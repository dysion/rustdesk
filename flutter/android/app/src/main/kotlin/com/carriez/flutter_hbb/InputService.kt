package com.carriez.flutter_hbb

/**
 * Handle remote input and dispatch android gesture
 *
 * Inspired by [droidVNC-NG] https://github.com/bk138/droidVNC-NG
 */

import android.accessibilityservice.AccessibilityService
import android.accessibilityservice.GestureDescription
import android.graphics.Path
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.util.Log
import android.widget.EditText
import android.view.accessibility.AccessibilityEvent
import android.view.ViewGroup.LayoutParams
import android.view.accessibility.AccessibilityNodeInfo
import android.view.KeyEvent as KeyEventAndroid
import android.view.ViewConfiguration
import android.graphics.Rect
import android.media.AudioManager
import android.accessibilityservice.AccessibilityServiceInfo
import android.accessibilityservice.AccessibilityServiceInfo.FLAG_INPUT_METHOD_EDITOR
import android.accessibilityservice.AccessibilityServiceInfo.FLAG_RETRIEVE_INTERACTIVE_WINDOWS
import android.view.inputmethod.EditorInfo
import androidx.annotation.RequiresApi
import java.util.*
import java.lang.Character
import kotlin.math.abs
import kotlin.math.max
import hbb.MessageOuterClass.KeyEvent
import hbb.MessageOuterClass.KeyboardMode
import hbb.KeyEventConverter

// const val BUTTON_UP = 2
// const val BUTTON_BACK = 0x08

const val LEFT_DOWN = 9
const val LEFT_MOVE = 8
const val LEFT_UP = 10
const val RIGHT_UP = 18
// (BUTTON_BACK << 3) | BUTTON_UP
const val BACK_UP = 66
const val WHEEL_BUTTON_DOWN = 33
const val WHEEL_BUTTON_UP = 34
const val WHEEL_DOWN = 523331
const val WHEEL_UP = 963

const val TOUCH_SCALE_START = 1
const val TOUCH_SCALE = 2
const val TOUCH_SCALE_END = 3
const val TOUCH_PAN_START = 4
const val TOUCH_PAN_UPDATE = 5
const val TOUCH_PAN_END = 6

const val WHEEL_STEP = 120
const val WHEEL_DURATION = 50L
const val LONG_TAP_DELAY = 200L

// ==================== MediaProjection auto-click (3-step state machine) ====================
// Real flow verified on Samsung A37 / Android 16:
//   Step 1: click the dropdown (Spinner) in the consent dialog
//   Step 2: click "Share entire screen" option in the popup list
//   Step 3: click the "Share screen" confirm button at bottom-right
const val AUTO_CLICK_MEDIA_PROJECTION_DELAY_MS = 5000L   // debug: wait 5s so tester can see the dialog
const val AUTO_CLICK_STEP_TIMEOUT_MS = 3000L             // max wait for next UI element to appear
const val AUTO_CLICK_STEP_POLL_MS = 300L                 // poll interval while waiting
const val AUTO_CLICK_BETWEEN_STEPS_DELAY_MS = 200L       // 0.2s wait after selecting the option
const val AUTO_CLICK_MAX_RETRY = 1                       // retry once per step on failure

enum class AutoClickStep {
    NONE,            // idle
    WAITING,         // dialog detected, waiting initial delay
    STEP1_DROPDOWN,  // clicking the dropdown
    STEP2_OPTION,    // selecting "Share entire screen"
    STEP3_CONFIRM,   // clicking "Share screen" button
    DONE
}

class InputService : AccessibilityService() {

    companion object {
        var ctx: InputService? = null
        val isOpen: Boolean
            get() = ctx != null
    }

    private val logTag = "input service"
    // ---- MediaProjection dialog auto-click state machine ----
    private val autoClickHandler = Handler(Looper.getMainLooper())
    private var autoClickStep = AutoClickStep.NONE
    private var autoClickRetryCount = 0
    private var autoClickPollCount = 0
    private var leftIsDown = false
    private var touchPath = Path()
    private var stroke: GestureDescription.StrokeDescription? = null
    private var lastTouchGestureStartTime = 0L
    private var mouseX = 0
    private var mouseY = 0
    private var timer = Timer()
    private var recentActionTask: TimerTask? = null
    // 100(tap timeout) + 400(long press timeout)
    private val longPressDuration = ViewConfiguration.getTapTimeout().toLong() + ViewConfiguration.getLongPressTimeout().toLong()

    private val wheelActionsQueue = LinkedList<GestureDescription>()
    private var isWheelActionsPolling = false
    private var isWaitingLongPress = false

    private var fakeEditTextForTextStateCalculation: EditText? = null

    private var lastX = 0
    private var lastY = 0

    private val volumeController: VolumeController by lazy { VolumeController(applicationContext.getSystemService(AUDIO_SERVICE) as AudioManager) }

    @RequiresApi(Build.VERSION_CODES.N)
    fun onMouseInput(mask: Int, _x: Int, _y: Int) {
        val x = max(0, _x)
        val y = max(0, _y)

        if (mask == 0 || mask == LEFT_MOVE) {
            val oldX = mouseX
            val oldY = mouseY
            mouseX = x * SCREEN_INFO.scale
            mouseY = y * SCREEN_INFO.scale
            if (isWaitingLongPress) {
                val delta = abs(oldX - mouseX) + abs(oldY - mouseY)
                Log.d(logTag,"delta:$delta")
                if (delta > 8) {
                    isWaitingLongPress = false
                }
            }
        }

        // left button down, was up
        if (mask == LEFT_DOWN) {
            isWaitingLongPress = true
            timer.schedule(object : TimerTask() {
                override fun run() {
                    if (isWaitingLongPress) {
                        isWaitingLongPress = false
                        continueGesture(mouseX, mouseY)
                    }
                }
            }, longPressDuration)

            leftIsDown = true
            startGesture(mouseX, mouseY)
            return
        }

        // left down, was down
        if (leftIsDown) {
            continueGesture(mouseX, mouseY)
        }

        // left up, was down
        if (mask == LEFT_UP) {
            if (leftIsDown) {
                leftIsDown = false
                isWaitingLongPress = false
                endGesture(mouseX, mouseY)
                return
            }
        }

        if (mask == RIGHT_UP) {
            longPress(mouseX, mouseY)
            return
        }

        if (mask == BACK_UP) {
            performGlobalAction(GLOBAL_ACTION_BACK)
            return
        }

        // long WHEEL_BUTTON_DOWN -> GLOBAL_ACTION_RECENTS
        if (mask == WHEEL_BUTTON_DOWN) {
            timer.purge()
            recentActionTask = object : TimerTask() {
                override fun run() {
                    performGlobalAction(GLOBAL_ACTION_RECENTS)
                    recentActionTask = null
                }
            }
            timer.schedule(recentActionTask, LONG_TAP_DELAY)
        }

        // wheel button up
        if (mask == WHEEL_BUTTON_UP) {
            if (recentActionTask != null) {
                recentActionTask!!.cancel()
                performGlobalAction(GLOBAL_ACTION_HOME)
            }
            return
        }

        if (mask == WHEEL_DOWN) {
            if (mouseY < WHEEL_STEP) {
                return
            }
            val path = Path()
            path.moveTo(mouseX.toFloat(), mouseY.toFloat())
            path.lineTo(mouseX.toFloat(), (mouseY - WHEEL_STEP).toFloat())
            val stroke = GestureDescription.StrokeDescription(
                path,
                0,
                WHEEL_DURATION
            )
            val builder = GestureDescription.Builder()
            builder.addStroke(stroke)
            wheelActionsQueue.offer(builder.build())
            consumeWheelActions()

        }

        if (mask == WHEEL_UP) {
            if (mouseY < WHEEL_STEP) {
                return
            }
            val path = Path()
            path.moveTo(mouseX.toFloat(), mouseY.toFloat())
            path.lineTo(mouseX.toFloat(), (mouseY + WHEEL_STEP).toFloat())
            val stroke = GestureDescription.StrokeDescription(
                path,
                0,
                WHEEL_DURATION
            )
            val builder = GestureDescription.Builder()
            builder.addStroke(stroke)
            wheelActionsQueue.offer(builder.build())
            consumeWheelActions()
        }
    }

    @RequiresApi(Build.VERSION_CODES.N)
    fun onTouchInput(mask: Int, _x: Int, _y: Int) {
        when (mask) {
            TOUCH_PAN_UPDATE -> {
                mouseX -= _x * SCREEN_INFO.scale
                mouseY -= _y * SCREEN_INFO.scale
                mouseX = max(0, mouseX);
                mouseY = max(0, mouseY);
                continueGesture(mouseX, mouseY)
            }
            TOUCH_PAN_START -> {
                mouseX = max(0, _x) * SCREEN_INFO.scale
                mouseY = max(0, _y) * SCREEN_INFO.scale
                startGesture(mouseX, mouseY)
            }
            TOUCH_PAN_END -> {
                endGesture(mouseX, mouseY)
                mouseX = max(0, _x) * SCREEN_INFO.scale
                mouseY = max(0, _y) * SCREEN_INFO.scale
            }
            else -> {}
        }
    }

    @RequiresApi(Build.VERSION_CODES.N)
    private fun consumeWheelActions() {
        if (isWheelActionsPolling) {
            return
        } else {
            isWheelActionsPolling = true
        }
        wheelActionsQueue.poll()?.let {
            dispatchGesture(it, null, null)
            timer.purge()
            timer.schedule(object : TimerTask() {
                override fun run() {
                    isWheelActionsPolling = false
                    consumeWheelActions()
                }
            }, WHEEL_DURATION + 10)
        } ?: let {
            isWheelActionsPolling = false
            return
        }
    }

    @RequiresApi(Build.VERSION_CODES.N)
    private fun performClick(x: Int, y: Int, duration: Long) {
        val path = Path()
        path.moveTo(x.toFloat(), y.toFloat())
        try {
            val longPressStroke = GestureDescription.StrokeDescription(path, 0, duration)
            val builder = GestureDescription.Builder()
            builder.addStroke(longPressStroke)
            Log.d(logTag, "performClick x:$x y:$y time:$duration")
            dispatchGesture(builder.build(), null, null)
        } catch (e: Exception) {
            Log.e(logTag, "performClick, error:$e")
        }
    }

    @RequiresApi(Build.VERSION_CODES.N)
    private fun longPress(x: Int, y: Int) {
        performClick(x, y, longPressDuration)
    }

    private fun startGesture(x: Int, y: Int) {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            touchPath.reset()
        } else {
            touchPath = Path()
        }
        touchPath.moveTo(x.toFloat(), y.toFloat())
        lastTouchGestureStartTime = System.currentTimeMillis()
        lastX = x
        lastY = y
    }

    @RequiresApi(Build.VERSION_CODES.N)
    private fun doDispatchGesture(x: Int, y: Int, willContinue: Boolean) {
        touchPath.lineTo(x.toFloat(), y.toFloat())
        var duration = System.currentTimeMillis() - lastTouchGestureStartTime
        if (duration <= 0) {
            duration = 1
        }
        try {
            if (stroke == null) {
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                    stroke = GestureDescription.StrokeDescription(
                        touchPath,
                        0,
                        duration,
                        willContinue
                    )
                } else {
                    stroke = GestureDescription.StrokeDescription(
                        touchPath,
                        0,
                        duration
                    )
                }
            } else {
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                    stroke = stroke?.continueStroke(touchPath, 0, duration, willContinue)
                } else {
                    stroke = null
                    stroke = GestureDescription.StrokeDescription(
                        touchPath,
                        0,
                        duration
                    )
                }
            }
            stroke?.let {
                val builder = GestureDescription.Builder()
                builder.addStroke(it)
                Log.d(logTag, "doDispatchGesture x:$x y:$y time:$duration")
                dispatchGesture(builder.build(), null, null)
            }
        } catch (e: Exception) {
            Log.e(logTag, "doDispatchGesture, willContinue:$willContinue, error:$e")
        }
    }

    @RequiresApi(Build.VERSION_CODES.N)
    private fun continueGesture(x: Int, y: Int) {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            doDispatchGesture(x, y, true)
            touchPath.reset()
            touchPath.moveTo(x.toFloat(), y.toFloat())
            lastTouchGestureStartTime = System.currentTimeMillis()
            lastX = x
            lastY = y
        } else {
            touchPath.lineTo(x.toFloat(), y.toFloat())
        }
    }

    @RequiresApi(Build.VERSION_CODES.N)
    private fun endGestureBelowO(x: Int, y: Int) {
        try {
            touchPath.lineTo(x.toFloat(), y.toFloat())
            var duration = System.currentTimeMillis() - lastTouchGestureStartTime
            if (duration <= 0) {
                duration = 1
            }
            val stroke = GestureDescription.StrokeDescription(
                touchPath,
                0,
                duration
            )
            val builder = GestureDescription.Builder()
            builder.addStroke(stroke)
            Log.d(logTag, "end gesture x:$x y:$y time:$duration")
            dispatchGesture(builder.build(), null, null)
        } catch (e: Exception) {
            Log.e(logTag, "endGesture error:$e")
        }
    }

    @RequiresApi(Build.VERSION_CODES.N)
    private fun endGesture(x: Int, y: Int) {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            doDispatchGesture(x, y, false)
            touchPath.reset()
            stroke = null
        } else {
            endGestureBelowO(x, y)
        }
    }

    @RequiresApi(Build.VERSION_CODES.N)
    fun onKeyEvent(data: ByteArray) {
        val keyEvent = KeyEvent.parseFrom(data)
        val keyboardMode = keyEvent.getMode()

        var textToCommit: String? = null

        // [down] indicates the key's state(down or up).
        // [press] indicates a click event(down and up).
        // https://github.com/rustdesk/rustdesk/blob/3a7594755341f023f56fa4b6a43b60d6b47df88d/flutter/lib/models/input_model.dart#L688
        if (keyEvent.hasSeq()) {
            textToCommit = keyEvent.getSeq()
        } else if (keyboardMode == KeyboardMode.Legacy) {
            if (keyEvent.hasChr() && (keyEvent.getDown() || keyEvent.getPress())) {
                val chr = keyEvent.getChr()
                if (chr != null) {
                    textToCommit = String(Character.toChars(chr))
                }
            }
        } else if (keyboardMode == KeyboardMode.Translate) {
        } else {
        }

        Log.d(logTag, "onKeyEvent $keyEvent textToCommit:$textToCommit")

        var ke: KeyEventAndroid? = null
        if (Build.VERSION.SDK_INT < 33 || textToCommit == null) {
            ke = KeyEventConverter.toAndroidKeyEvent(keyEvent)
        }
        ke?.let { event ->
            if (tryHandleVolumeKeyEvent(event)) {
                return
            } else if (tryHandlePowerKeyEvent(event)) {
                return
            }
        }

        if (Build.VERSION.SDK_INT >= 33) {
            getInputMethod()?.let { inputMethod ->
                inputMethod.getCurrentInputConnection()?.let { inputConnection ->
                    if (textToCommit != null) {
                        textToCommit?.let { text ->
                            inputConnection.commitText(text, 1, null)
                        }
                    } else {
                        ke?.let { event ->
                            inputConnection.sendKeyEvent(event)
                            if (keyEvent.getPress()) {
                                val actionUpEvent = KeyEventAndroid(KeyEventAndroid.ACTION_UP, event.keyCode)
                                inputConnection.sendKeyEvent(actionUpEvent)
                            }
                        }
                    }
                }
            }
        } else {
            val handler = Handler(Looper.getMainLooper())
            handler.post {
                ke?.let { event ->
                    val possibleNodes = possibleAccessibiltyNodes()
                    Log.d(logTag, "possibleNodes:$possibleNodes")
                    for (item in possibleNodes) {
                        val success = trySendKeyEvent(event, item, textToCommit)
                        if (success) {
                            if (keyEvent.getPress()) {
                                val actionUpEvent = KeyEventAndroid(KeyEventAndroid.ACTION_UP, event.keyCode)
                                trySendKeyEvent(actionUpEvent, item, textToCommit)
                            }
                            break
                        }
                    }
                }
            }
        }
    }

    private fun tryHandleVolumeKeyEvent(event: KeyEventAndroid): Boolean {
        when (event.keyCode) {
            KeyEventAndroid.KEYCODE_VOLUME_UP -> {
                if (event.action == KeyEventAndroid.ACTION_DOWN) {
                    volumeController.raiseVolume(null, true, AudioManager.STREAM_SYSTEM)
                }
                return true
            }
            KeyEventAndroid.KEYCODE_VOLUME_DOWN -> {
                if (event.action == KeyEventAndroid.ACTION_DOWN) {
                    volumeController.lowerVolume(null, true, AudioManager.STREAM_SYSTEM)
                }
                return true
            }
            KeyEventAndroid.KEYCODE_VOLUME_MUTE -> {
                if (event.action == KeyEventAndroid.ACTION_DOWN) {
                    volumeController.toggleMute(true, AudioManager.STREAM_SYSTEM)
                }
                return true
            }
            else -> {
                return false
            }
        }
    }

    private fun tryHandlePowerKeyEvent(event: KeyEventAndroid): Boolean {
        if (event.keyCode == KeyEventAndroid.KEYCODE_POWER) {
            // Perform power dialog action when action is up
            if (event.action == KeyEventAndroid.ACTION_UP) {
                performGlobalAction(GLOBAL_ACTION_POWER_DIALOG);
            }
            return true
        }
        return false
    }

    private fun insertAccessibilityNode(list: LinkedList<AccessibilityNodeInfo>, node: AccessibilityNodeInfo) {
        if (node == null) {
            return
        }
        if (list.contains(node)) {
            return
        }
        list.add(node)
    }

    private fun findChildNode(node: AccessibilityNodeInfo?): AccessibilityNodeInfo? {
        if (node == null) {
            return null
        }
        if (node.isEditable() && node.isFocusable()) {
            return node
        }
        val childCount = node.getChildCount()
        for (i in 0 until childCount) {
            val child = node.getChild(i)
            if (child != null) {
                if (child.isEditable() && child.isFocusable()) {
                    return child
                }
                if (Build.VERSION.SDK_INT < 33) {
                    child.recycle()
                }
            }
        }
        for (i in 0 until childCount) {
            val child = node.getChild(i)
            if (child != null) {
                val result = findChildNode(child)
                if (Build.VERSION.SDK_INT < 33) {
                    if (child != result) {
                        child.recycle()
                    }
                }
                if (result != null) {
                    return result
                }
            }
        }
        return null
    }

    private fun possibleAccessibiltyNodes(): LinkedList<AccessibilityNodeInfo> {
        val linkedList = LinkedList<AccessibilityNodeInfo>()
        val latestList = LinkedList<AccessibilityNodeInfo>()

        val focusInput = findFocus(AccessibilityNodeInfo.FOCUS_INPUT)
        var focusAccessibilityInput = findFocus(AccessibilityNodeInfo.FOCUS_ACCESSIBILITY)

        val rootInActiveWindow = getRootInActiveWindow()

        Log.d(logTag, "focusInput:$focusInput focusAccessibilityInput:$focusAccessibilityInput rootInActiveWindow:$rootInActiveWindow")

        if (focusInput != null) {
            if (focusInput.isFocusable() && focusInput.isEditable()) {
                insertAccessibilityNode(linkedList, focusInput)
            } else {
                insertAccessibilityNode(latestList, focusInput)
            }
        }

        if (focusAccessibilityInput != null) {
            if (focusAccessibilityInput.isFocusable() && focusAccessibilityInput.isEditable()) {
                insertAccessibilityNode(linkedList, focusAccessibilityInput)
            } else {
                insertAccessibilityNode(latestList, focusAccessibilityInput)
            }
        }

        val childFromFocusInput = findChildNode(focusInput)
        Log.d(logTag, "childFromFocusInput:$childFromFocusInput")

        if (childFromFocusInput != null) {
            insertAccessibilityNode(linkedList, childFromFocusInput)
        }

        val childFromFocusAccessibilityInput = findChildNode(focusAccessibilityInput)
        if (childFromFocusAccessibilityInput != null) {
            insertAccessibilityNode(linkedList, childFromFocusAccessibilityInput)
        }
        Log.d(logTag, "childFromFocusAccessibilityInput:$childFromFocusAccessibilityInput")

        if (rootInActiveWindow != null) {
            insertAccessibilityNode(linkedList, rootInActiveWindow)
        }

        for (item in latestList) {
            insertAccessibilityNode(linkedList, item)
        }

        return linkedList
    }

    private fun trySendKeyEvent(event: KeyEventAndroid, node: AccessibilityNodeInfo, textToCommit: String?): Boolean {
        node.refresh()
        this.fakeEditTextForTextStateCalculation?.setSelection(0,0)
        this.fakeEditTextForTextStateCalculation?.setText(null)

        val text = node.getText()
        var isShowingHint = false
        if (Build.VERSION.SDK_INT >= 26) {
            isShowingHint = node.isShowingHintText()
        }

        var textSelectionStart = node.textSelectionStart
        var textSelectionEnd = node.textSelectionEnd

        if (text != null) {
            if (textSelectionStart > text.length) {
                textSelectionStart = text.length
            }
            if (textSelectionEnd > text.length) {
                textSelectionEnd = text.length
            }
            if (textSelectionStart > textSelectionEnd) {
                textSelectionStart = textSelectionEnd
            }
        }

        var success = false

        Log.d(logTag, "existing text:$text textToCommit:$textToCommit textSelectionStart:$textSelectionStart textSelectionEnd:$textSelectionEnd")

        if (textToCommit != null) {
            if ((textSelectionStart == -1) || (textSelectionEnd == -1)) {
                val newText = textToCommit
                this.fakeEditTextForTextStateCalculation?.setText(newText)
                success = updateTextForAccessibilityNode(node)
            } else if (text != null) {
                this.fakeEditTextForTextStateCalculation?.setText(text)
                this.fakeEditTextForTextStateCalculation?.setSelection(
                    textSelectionStart,
                    textSelectionEnd
                )
                this.fakeEditTextForTextStateCalculation?.text?.insert(textSelectionStart, textToCommit)
                success = updateTextAndSelectionForAccessibiltyNode(node)
            }
        } else {
            if (isShowingHint) {
                this.fakeEditTextForTextStateCalculation?.setText(null)
            } else {
                this.fakeEditTextForTextStateCalculation?.setText(text)
            }
            if (textSelectionStart != -1 && textSelectionEnd != -1) {
                Log.d(logTag, "setting selection $textSelectionStart $textSelectionEnd")
                this.fakeEditTextForTextStateCalculation?.setSelection(
                    textSelectionStart,
                    textSelectionEnd
                )
            }

            this.fakeEditTextForTextStateCalculation?.let {
                // This is essiential to make sure layout object is created. OnKeyDown may not work if layout is not created.
                val rect = Rect()
                node.getBoundsInScreen(rect)

                it.layout(rect.left, rect.top, rect.right, rect.bottom)
                it.onPreDraw()
                if (event.action == KeyEventAndroid.ACTION_DOWN) {
                    val succ = it.onKeyDown(event.getKeyCode(), event)
                    Log.d(logTag, "onKeyDown $succ")
                } else if (event.action == KeyEventAndroid.ACTION_UP) {
                    val success = it.onKeyUp(event.getKeyCode(), event)
                    Log.d(logTag, "keyup $success")
                } else {}
            }

            success = updateTextAndSelectionForAccessibiltyNode(node)
        }
        return success
    }

    fun updateTextForAccessibilityNode(node: AccessibilityNodeInfo): Boolean {
        var success = false
        this.fakeEditTextForTextStateCalculation?.text?.let {
            val arguments = Bundle()
            arguments.putCharSequence(
                AccessibilityNodeInfo.ACTION_ARGUMENT_SET_TEXT_CHARSEQUENCE,
                it.toString()
            )
            success = node.performAction(AccessibilityNodeInfo.ACTION_SET_TEXT, arguments)
        }
        return success
    }

    fun updateTextAndSelectionForAccessibiltyNode(node: AccessibilityNodeInfo): Boolean {
        var success = updateTextForAccessibilityNode(node)

        if (success) {
            val selectionStart = this.fakeEditTextForTextStateCalculation?.selectionStart
            val selectionEnd = this.fakeEditTextForTextStateCalculation?.selectionEnd

            if (selectionStart != null && selectionEnd != null) {
                val arguments = Bundle()
                arguments.putInt(
                    AccessibilityNodeInfo.ACTION_ARGUMENT_SELECTION_START_INT,
                    selectionStart
                )
                arguments.putInt(
                    AccessibilityNodeInfo.ACTION_ARGUMENT_SELECTION_END_INT,
                    selectionEnd
                )
                success = node.performAction(AccessibilityNodeInfo.ACTION_SET_SELECTION, arguments)
                Log.d(logTag, "Update selection to $selectionStart $selectionEnd success:$success")
            }
        }

        return success
    }


    override fun onAccessibilityEvent(event: AccessibilityEvent) {
        // Detect MediaProjection authorization dialog and start the auto-click state machine.
        if (event.eventType == AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED) {
            val pkg = event.packageName?.toString() ?: ""
            val cls = event.className?.toString() ?: ""
            Log.d(logTag, "window state changed, package:$pkg class:$cls")

            // Only trigger when the machine is idle, so popup windows spawned by our own
            // clicks (the dropdown list) do not restart the flow.
            if (autoClickStep == AutoClickStep.NONE && isMediaProjectionDialog(pkg, cls)) {
                Log.w(logTag, "[AutoClick] MediaProjection dialog detected, starting in ${AUTO_CLICK_MEDIA_PROJECTION_DELAY_MS}ms")
                autoClickStep = AutoClickStep.WAITING
                autoClickRetryCount = 0
                autoClickPollCount = 0
                autoClickHandler.postDelayed({
                    if (autoClickStep == AutoClickStep.WAITING) {
                        autoClickStep = AutoClickStep.STEP1_DROPDOWN
                        executeStep1()
                    }
                }, AUTO_CLICK_MEDIA_PROJECTION_DELAY_MS)
            }
        }
    }

    /**
     * Heuristically detect whether the current window is the screen-capture
     * (MediaProjection) consent dialog.
     */
    private fun isMediaProjectionDialog(pkg: String, cls: String): Boolean {
        val p = pkg.lowercase()
        val c = cls.lowercase()
        // System UI / MediaProjection permission activity keywords
        val packageKeywords = listOf("mediaprojection", "mediaprojectionpermission", "systemui")
        val classKeywords = listOf(
            "mediaprojection", "mediaprojectionpermission",
            "mediaprojectionactivity", "launcherdialog"
        )
        if (packageKeywords.any { p.contains(it) }) return true
        if (classKeywords.any { c.contains(it) }) return true
        return false
    }

    // ==================================================================================
    // MediaProjection dialog auto-click: helpers
    // ==================================================================================

    /**
     * Loose text match: strip all whitespace and compare case-insensitively, so
     * "Share screen" / "Share  Screen" / "Sharescreen" all match keyword "share screen".
     */
    private fun looseMatch(text: String, keyword: String): Boolean {
        val t = text.lowercase().replace(" ", "").replace("\n", "").trim()
        val k = keyword.lowercase().replace(" ", "")
        return t.isNotEmpty() && t.contains(k)
    }

    /** Recursively dump the whole node tree with class / id / text / clickable / bounds. */
    private fun dumpNodeTree(node: AccessibilityNodeInfo, depth: Int) {
        val indent = "  ".repeat(depth)
        val rect = Rect()
        node.getBoundsInScreen(rect)
        Log.d(logTag, "[AutoClick][Dump] ${indent}[${node.className}] id=${node.viewIdResourceName} " +
            "text='${node.text}' clickable=${node.isClickable} bounds=$rect")
        for (i in 0 until node.childCount) {
            node.getChild(i)?.let { dumpNodeTree(it, depth + 1) }
        }
    }

    private fun dumpActiveWindow(tag: String) {
        val root = rootInActiveWindow
        if (root == null) {
            Log.d(logTag, "[AutoClick][Dump:$tag] no active window")
            return
        }
        Log.d(logTag, "[AutoClick][Dump:$tag] ==== active window ====")
        dumpNodeTree(root, 0)
    }

    private fun dumpAllWindows(tag: String) {
        Log.d(logTag, "[AutoClick][Dump:$tag] ==== all windows (${windows.size}) ====")
        for (w in windows) {
            // Note: AccessibilityWindowInfo.getPackageName() requires API 24 (minSdk is 22),
            // so read the package name from the window root node instead (API 16).
            val pkg = w.root?.packageName ?: "unknown"
            Log.d(logTag, "[AutoClick][Dump:$tag] -- window: $pkg active=${w.isActive} type=${w.type}")
            w.root?.let { dumpNodeTree(it, 1) }
        }
    }

    /** Generic depth-first search over a node tree. */
    private fun findNodeRecursive(
        root: AccessibilityNodeInfo?,
        predicate: (AccessibilityNodeInfo) -> Boolean
    ): AccessibilityNodeInfo? {
        if (root == null) return null
        if (predicate(root)) return root
        for (i in 0 until root.childCount) {
            val child = root.getChild(i) ?: continue
            val result = findNodeRecursive(child, predicate)
            if (result != null) return result
        }
        return null
    }

    /**
     * Search every window (including popup windows such as the dropdown list),
     * active window first.
     */
    private fun findInAllWindows(predicate: (AccessibilityNodeInfo) -> Boolean): AccessibilityNodeInfo? {
        rootInActiveWindow?.let { r ->
            findNodeRecursive(r, predicate)?.let { return it }
        }
        for (w in windows) {
            val r = w.root ?: continue
            findNodeRecursive(r, predicate)?.let { return it }
        }
        return null
    }

    /**
     * Click a node: prefer ACTION_CLICK on the node (or its clickable ancestor up to 5
     * levels), fall back to a coordinate gesture tap at the node center.
     */
    private fun clickNode(node: AccessibilityNodeInfo): Boolean {
        var n: AccessibilityNodeInfo? = node
        var depth = 0
        while (n != null && depth < 5) {
            if (n.isClickable && n.performAction(AccessibilityNodeInfo.ACTION_CLICK)) {
                Log.d(logTag, "[AutoClick] ACTION_CLICK success (depth=$depth)")
                return true
            }
            n = n.parent
            depth++
        }
        val rect = Rect()
        node.getBoundsInScreen(rect)
        if (rect.isEmpty) return false
        Log.d(logTag, "[AutoClick] fallback gesture click at (${rect.centerX()},${rect.centerY()})")
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.N) {
            Log.e(logTag, "[AutoClick] gesture click requires API 24+")
            return false
        }
        return try {
            performClick(rect.centerX(), rect.centerY(), 50)
            true
        } catch (e: Exception) {
            Log.e(logTag, "[AutoClick] gesture click error: $e")
            false
        }
    }

    private fun resetAutoClick() {
        autoClickStep = AutoClickStep.NONE
        autoClickRetryCount = 0
        autoClickPollCount = 0
    }

    /** Handle a step failure: retry once, otherwise give up and dump windows for debugging. */
    private fun onStepFailed(reason: String) {
        Log.e(logTag, "[AutoClick] FAILED: $reason (retry=$autoClickRetryCount/$AUTO_CLICK_MAX_RETRY)")
        if (autoClickRetryCount < AUTO_CLICK_MAX_RETRY) {
            autoClickRetryCount++
            Log.w(logTag, "[AutoClick] retrying current step in 500ms...")
            autoClickHandler.postDelayed({
                when (autoClickStep) {
                    AutoClickStep.STEP1_DROPDOWN -> executeStep1()
                    AutoClickStep.STEP2_OPTION -> { autoClickPollCount = 0; pollStep2() }
                    AutoClickStep.STEP3_CONFIRM -> executeStep3()
                    else -> { /* state changed meanwhile, ignore */ }
                }
            }, 500)
        } else {
            Log.e(logTag, "[AutoClick] giving up after retry, dumping all windows for debugging:")
            dumpAllWindows("giveup")
            resetAutoClick()
        }
    }

    // ==================================================================================
    // Step 1: click the dropdown (Spinner) in the consent dialog
    // ==================================================================================
    private fun executeStep1() {
        if (autoClickStep != AutoClickStep.STEP1_DROPDOWN) return
        Log.w(logTag, "[AutoClick] Step1: looking for dropdown in active window")
        dumpActiveWindow("Step1")

        val root = rootInActiveWindow
        if (root == null) {
            onStepFailed("Step1: no active window")
            return
        }

        // Priority: Spinner-like class/id > text 'Share one app' (default selection) >
        // first clickable non-button element in the dialog.
        val target = findNodeRecursive(root) { node ->
            val cls = node.className?.toString()?.lowercase() ?: ""
            val id = node.viewIdResourceName?.lowercase() ?: ""
            val text = node.text?.toString() ?: ""
            (cls.contains("spinner") && (node.isClickable || node.parent?.isClickable == true))
                || id.contains("spinner")
                || looseMatch(text, "share one app")
        } ?: findNodeRecursive(root) { node ->
            val cls = node.className?.toString()?.lowercase() ?: ""
            node.isClickable && !cls.contains("button")
        }

        if (target == null) {
            onStepFailed("Step1: dropdown not found")
            return
        }
        val rect = Rect()
        target.getBoundsInScreen(rect)
        Log.w(logTag, "[AutoClick] Step1: FOUND dropdown (class=${target.className} text='${target.text}') at $rect, clicking")
        if (clickNode(target)) {
            autoClickStep = AutoClickStep.STEP2_OPTION
            autoClickRetryCount = 0
            autoClickPollCount = 0
            autoClickHandler.postDelayed({ pollStep2() }, AUTO_CLICK_STEP_POLL_MS)
        } else {
            onStepFailed("Step1: click dispatch failed")
        }
    }

    // ==================================================================================
    // Step 2: wait for the popup list, then click "Share entire screen"
    // ==================================================================================
    private fun pollStep2() {
        if (autoClickStep != AutoClickStep.STEP2_OPTION) return

        val found = findInAllWindows { node ->
            val text = node.text?.toString() ?: ""
            looseMatch(text, "share entire screen")
        }
        if (found != null) {
            val rect = Rect()
            found.getBoundsInScreen(rect)
            Log.w(logTag, "[AutoClick] Step2: FOUND 'Share entire screen' at $rect, clicking")
            if (clickNode(found)) {
                autoClickStep = AutoClickStep.STEP3_CONFIRM
                autoClickRetryCount = 0
                autoClickHandler.postDelayed({ executeStep3() }, AUTO_CLICK_BETWEEN_STEPS_DELAY_MS)
            } else {
                onStepFailed("Step2: click dispatch failed")
            }
            return
        }

        autoClickPollCount++
        if (autoClickPollCount * AUTO_CLICK_STEP_POLL_MS >= AUTO_CLICK_STEP_TIMEOUT_MS) {
            dumpAllWindows("Step2-timeout")
            onStepFailed("Step2: option 'Share entire screen' not found within ${AUTO_CLICK_STEP_TIMEOUT_MS}ms")
            return
        }
        autoClickHandler.postDelayed({ pollStep2() }, AUTO_CLICK_STEP_POLL_MS)
    }

    // ==================================================================================
    // Step 3: click the "Share screen" confirm button (bottom-right)
    // ==================================================================================
    private fun executeStep3() {
        if (autoClickStep != AutoClickStep.STEP3_CONFIRM) return
        Log.w(logTag, "[AutoClick] Step3: looking for confirm button")
        dumpActiveWindow("Step3")

        val root = rootInActiveWindow
        if (root == null) {
            onStepFailed("Step3: no active window")
            return
        }

        val metrics = resources.displayMetrics
        // Priority: text 'Share screen' > clickable Button located in bottom-right quadrant.
        val target = findNodeRecursive(root) { node ->
            val text = node.text?.toString() ?: ""
            looseMatch(text, "share screen")
        } ?: findNodeRecursive(root) { node ->
            val cls = node.className?.toString()?.lowercase() ?: ""
            if (!cls.contains("button") || !node.isClickable) return@findNodeRecursive false
            val rect = Rect()
            node.getBoundsInScreen(rect)
            rect.centerX() > metrics.widthPixels / 2 && rect.centerY() > metrics.heightPixels / 2
        }

        if (target == null) {
            onStepFailed("Step3: confirm button not found")
            return
        }
        val rect = Rect()
        target.getBoundsInScreen(rect)
        Log.w(logTag, "[AutoClick] Step3: FOUND confirm (class=${target.className} text='${target.text}') at $rect, clicking")
        if (clickNode(target)) {
            Log.w(logTag, "[AutoClick] ALL STEPS DONE")
            resetAutoClick()
        } else {
            onStepFailed("Step3: click dispatch failed")
        }
    }

    override fun onServiceConnected() {
        super.onServiceConnected()
        ctx = this
        // Start from the XML-configured serviceInfo so eventTypes/feedbackType are
        // preserved; calling setServiceInfo with a fresh AccessibilityServiceInfo()
        // wipes eventTypes to 0 and the service stops receiving accessibility events
        // (which breaks the MediaProjection auto-click state machine).
        val info = this.serviceInfo
        info.flags = info.flags or FLAG_RETRIEVE_INTERACTIVE_WINDOWS
        if (Build.VERSION.SDK_INT >= 33) {
            info.flags = info.flags or FLAG_INPUT_METHOD_EDITOR
        }
        setServiceInfo(info)
        fakeEditTextForTextStateCalculation = EditText(this)
        // Size here doesn't matter, we won't show this view.
        fakeEditTextForTextStateCalculation?.layoutParams = LayoutParams(100, 100)
        fakeEditTextForTextStateCalculation?.onPreDraw()
        val layout = fakeEditTextForTextStateCalculation?.getLayout()
        Log.d(logTag, "fakeEditTextForTextStateCalculation layout:$layout")
        Log.d(logTag, "onServiceConnected!")
    }

    override fun onDestroy() {
        autoClickHandler.removeCallbacksAndMessages(null)
        resetAutoClick()
        ctx = null
        super.onDestroy()
    }

    override fun onInterrupt() {}
}
