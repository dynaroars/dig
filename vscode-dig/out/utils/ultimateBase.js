"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.UltimateBase = void 0;
const vscode = __importStar(require("vscode"));
const fs = __importStar(require("fs"));
class UltimateBase {
    results = [];
    error = null;
    settingsFilePath = vscode.Uri.file('');
    toolchainFilePath = vscode.Uri.file('');
    ultimateIsRunning = false;
    progressCancellationToken = null;
    logChannel;
    outputChannel;
    collection;
    extensionContext;
    constructor(context) {
        this.extensionContext = context;
        this.logChannel = this.createExtendedOutputChannel('Ultimate Log');
        this.outputChannel = vscode.window.createOutputChannel('Ultimate Results');
        this.collection = vscode.languages.createDiagnosticCollection('ultimate');
        this.initOutputChannel();
        this.initLogChannel();
    }
    createExtendedOutputChannel(name) {
        const channel = vscode.window.createOutputChannel(name);
        channel.error = (message) => channel.appendLine(`ERROR: ${message}`);
        channel.warning = (message) => channel.appendLine(`WARNING: ${message}`);
        channel.debug = (message) => channel.appendLine(`DEBUG: ${message}`);
        return channel;
    }
    initLogChannel() {
        this.extensionContext.subscriptions.push(this.logChannel);
        this.logChannel.appendLine('Ultimate activated');
        this.logChannel.show();
    }
    initOutputChannel() {
        this.extensionContext.subscriptions.push(this.outputChannel);
        this.outputChannel.appendLine('Ultimate activated');
    }
    setToolchainFile(path) {
        if (fs.existsSync(path.fsPath) && RegExp(/(.*\.xml$)/).exec(path.fsPath)) {
            this.toolchainFilePath = path;
        }
        else {
            console.log(`Toolchain file ${path} does not exist`);
        }
    }
    setSettingsFile(path) {
        if (fs.existsSync(path.fsPath) && RegExp(/(.*\.epf$)/).exec(path.fsPath)) {
            this.settingsFilePath = path;
        }
        else {
            console.log(`Settings file ${path} does not exist`);
        }
    }
    embedDiagnosticInfoInto(document) {
        if (document) {
            let diagnostics = this.prepareDiagnosticInfo(document);
            this.collection.set(document.uri, diagnostics);
        }
    }
    convertSeverity(logLvl) {
        switch (logLvl) {
            case 'error':
                return vscode.DiagnosticSeverity.Error;
            case 'warning':
                return vscode.DiagnosticSeverity.Warning;
            case 'debug':
                return vscode.DiagnosticSeverity.Hint;
            default:
                return vscode.DiagnosticSeverity.Information;
        }
    }
    showProgressInStatusBar(title) {
        vscode.window.withProgress({
            title: title,
            location: vscode.ProgressLocation.Window,
            cancellable: true,
        }, (progress, token) => {
            return new Promise((resolve) => {
                this.progressCancellationToken = new vscode.CancellationTokenSource();
                this.progressCancellationToken.token.onCancellationRequested(() => {
                    this.progressCancellationToken?.dispose();
                    this.progressCancellationToken = null;
                    resolve();
                });
                setTimeout(() => {
                    resolve();
                }, 300000);
            });
        });
    }
    stopShowingProgressInStatusBar() {
        this.progressCancellationToken?.cancel();
    }
    lockUltimate() {
        if (!this.ultimateIsRunning) {
            this.ultimateIsRunning = true;
            return true;
        }
        else {
            return false;
        }
    }
    freeUltimate() {
        this.ultimateIsRunning = false;
    }
    isLocked() {
        return this.ultimateIsRunning;
    }
    isDocument(obj) {
        return !!obj.languageId;
    }
}
exports.UltimateBase = UltimateBase;
//# sourceMappingURL=ultimateBase.js.map