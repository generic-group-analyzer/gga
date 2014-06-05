/// <reference path="ace.d.ts" />
/// <reference path="jquery.d.ts" />
var example = "(* DDH in G2 of asymmetric bilinear group *)\n\
isos G1 -> G2.\n\
maps G1 * G2 -> GT.\n\
input [ X, Y ] in G2.\n\
input_left [ X*Y ] in GT.\n\
input_right [ Z ] in GT.";

/* ******************************************************************/
/* Debug logging                                                    */
/* ******************************************************************/
var enable_debug = true;

function log(s) {
    if (enable_debug) {
        console.log(s);
    }
}

/* ******************************************************************/
/* Websocket connection                                             */
/* ******************************************************************/
var wsServer = window.location.hostname ? window.location.hostname : "127.0.0.1";
var webSocket = new WebSocket("ws://" + wsServer + ":9998/");
var firstConnect = true;

//webSocket.onclose = function(evt) {
//  log("reconnecting to server");
//  webSocket = new WebSocket("ws://" + wsServer + ":9999/");
//};
// send json request to zoocrypt websocket server
function sendZoocrypt(m) {
    if (webSocket) {
        webSocket.send(JSON.stringify(m));
    }
}

/* ******************************************************************/
/* Locking in proof editor                                          */
/* ******************************************************************/
// editorProof has been processed up to this character
var firstUnlocked = 0;

// the text from the timepoint when the locking was enabled
var originalLockedText = "";

// the last locking marker, used for removal
var lastMarker;

function lockedText() {
    return editorProof.getValue().substring(0, firstUnlocked);
}

function setFirstUnlocked(i) {
    firstUnlocked = i;
    originalLockedText = lockedText();
}

function insideComment(t, pos) {
    var cstart = t.lastIndexOf("(*", pos);
    var cend = t.lastIndexOf("*)", pos);

    // comment start and comment-start not followed by comment-end
    return (cstart !== -1 && cstart > cend);
}

function getNextDot(from) {
    var t = editorProof.getValue();
    var n = t.indexOf(".", from);
    if (n !== -1 && insideComment(t, n)) {
        return getNextDot(n + 1);
    }
    return n;
}

function getPrevDot(from) {
    var t = editorProof.getValue();
    var n = t.lastIndexOf(".", Math.max(0, from - 2));
    if (n !== -1 && insideComment(t, n)) {
        return getPrevDot(n - 1);
    }
    return n;
}

var emacs = ace.require("ace/keyboard/emacs").handler;

var editorProof = ace.edit("editor-proof");
editorProof.setTheme("ace/theme/eclipse");
editorProof.setHighlightActiveLine(false);
editorProof.focus();
editorProof.renderer.setShowGutter(false);
editorProof.setKeyboardHandler(emacs);
editorProof.getSession().setTabSize(2);
editorProof.getSession().setUseSoftTabs(true);
editorProof.getSession().setMode("ace/mode/zoocrypt");
editorProof.setValue(example);
editorProof.clearSelection();

editorProof.getSession().getDocument().on("change", function (ev) {
    var lt = lockedText();
    if (lt !== originalLockedText) {
        var pos = editorProof.getCursorPosition();
        setFirstUnlocked(-1);
        evalLocked();
        editorProof.moveCursorToPosition(pos);
    }
});

function markLocked(c) {
    var Range = ace.require('ace/range').Range;
    var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked, 0);
    if (lastMarker) {
        editorProof.getSession().removeMarker(lastMarker);
    }
    lastMarker = editorProof.getSession().addMarker(new Range(0, 0, pos.row, pos.column), c, 'word', false);
}

/* ******************************************************************/
/* Goal and message editor and resizing                             */
/* ******************************************************************/
//var editorGoal = ace.edit("editor-goal");
//editorGoal.setTheme("ace/theme/eclipse");
//editorGoal.setHighlightActiveLine(false);
//editorGoal.renderer.setShowGutter(false)
var editorMessage = ace.edit("editor-message");
editorMessage.setTheme("ace/theme/eclipse");
editorMessage.setHighlightActiveLine(false);
editorMessage.renderer.setShowGutter(false);
editorMessage.getSession().setTabSize(8);

// resize windows
function resizeAce() {
    var hpadding = 25;
    var vpadding = 75;
    var edit = $('#editor-proof');
    edit.height($(window).height() - vpadding + 13);
    edit.width($(window).width() / 2 - hpadding);

    edit = $('#editor-message');
    edit.height($(window).height() - vpadding + 13);
    edit.width($(window).width() / 2 - hpadding);
}

//listen for changes
$(window).resize(resizeAce);

//set initially
resizeAce();

/* ******************************************************************/
/* Websocket event handling                                         */
/* ******************************************************************/
// Request proof script
webSocket.onopen = function (evt) {
    firstConnect = false;
};

// handle websocket answers
webSocket.onmessage = function (evt) {
    log(evt.data);
    var m = JSON.parse(evt.data);

    if (m.cmd == 'setGoal') {
        setFirstUnlocked(-1);
        markLocked('locked');
        editorMessage.setValue(m.arg);
        editorMessage.clearSelection();
        var pos = editorMessage.getSession().getDocument().indexToPosition(0, 0);
        editorMessage.moveCursorToPosition(pos);
        if (m.err) {
            editorMessage.setValue(m.err);
        } else {
            editorMessage.setValue(m.msgs.length > 0 ? m.msgs[m.msgs.length - 1] : "No message received.");
        }
        editorMessage.clearSelection();
        // answer for load
    } else if (m.cmd == 'setProof') {
        editorProof.setValue(m.arg);
        editorProof.clearSelection();
        editorProof.scrollPageUp();
        editorMessage.setValue("Proofscript loaded.");
        editorMessage.clearSelection();
        var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked, 0);
        editorProof.moveCursorToPosition(pos);
    } else if (m.cmd == "saveOK") {
        editorMessage.setValue("Proofscript saved.");
        editorMessage.clearSelection();
    } else if (m.cmd == "saveFAILED") {
        editorMessage.setValue("Save of proofscript failed.");
        editorMessage.clearSelection();
    }
};

/* ******************************************************************/
/* Evaluate parts of buffer                                         */
/* ******************************************************************/
function evalLocked() {
    var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked, 0);
    editorProof.moveCursorToPosition(pos);
    editorProof.clearSelection();
    markLocked('processing');
    if (lockedText() !== "") {
        editorMessage.setValue("Processing input ...");
        editorMessage.clearSelection();
        sendZoocrypt({ 'cmd': 'eval', 'cmds': lockedText(), 'mode': $("#mode").val() });
    } else {
        editorMessage.setValue("");
    }
}

function evalEnd() {
    editorProof.navigateFileEnd();
    var pos = editorProof.getCursorPosition();
    var idx = editorProof.getSession().getDocument().positionToIndex(pos, 0);
    var prevDot = getPrevDot(idx + 1);
    if (prevDot == -1) {
        setFirstUnlocked(0);
    } else {
        setFirstUnlocked(prevDot + 1);
    }
    evalLocked();
}

/* ******************************************************************/
/* Add command bindings buffer                                      */
/* ******************************************************************/
editorProof.commands.addCommand({
    name: 'evalCursor',
    bindKey: {
        win: 'Ctrl-Enter',
        mac: 'Ctrl-Enter',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        evalEnd();
    }
});
//# sourceMappingURL=ggt.js.map
