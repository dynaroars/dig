"use strict";
/*import { exec } from 'child_process';
import * as path from 'path';
import * as vscode from 'vscode';

export function runUltimateAutomizer(context: vscode.ExtensionContext, filePath: string) {
    const ultimateRepoPath = path.join(context.globalStorageUri.fsPath, 'UltimateAtomizer');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'toolchains', 'AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'settings', 'default', 'automizer', 'svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${filePath}" -s "${settingsPath}"`;

    exec(ultimateCommand, (error, stdout, stderr) => {
        if (error) {
            console.error(`Error running Ultimate Automizer: ${stderr}`);
            return;
        }
        console.log(`Ultimate Automizer Output:\n${stdout}`);
    });
}
*/
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
exports.UltimateBase = exports.runUltimateAutomizer = void 0;
const vscode = __importStar(require("vscode"));
const child_process_1 = require("child_process");
const path = __importStar(require("path"));
const fs = __importStar(require("fs"));
function runUltimateAutomizer(filePath, context) {
    const ultimateRepoPath = path.join(context.globalStorageUri.fsPath, 'UltimateAtomizer');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'toolchains', 'AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'settings', 'svcomp2018', 'automizer', 'svcomp-Reach-64bit-Automizer_Bitvector.epf');
    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${filePath}" -s "${settingsPath}"`;
    (0, child_process_1.exec)(ultimateCommand, (error, stdout, stderr) => {
        if (error) {
            console.error(`Error running Ultimate Automizer: ${stderr}`);
            vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
            return;
        }
        console.log(`Ultimate Automizer Output:\n${stdout}`);
        vscode.window.showInformationMessage(`Ultimate Automizer executed successfully.`);
    });
}
exports.runUltimateAutomizer = runUltimateAutomizer;
class UltimateBase {
    results = [];
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
        this.logChannel = vscode.window.createOutputChannel('Ultimate Log', { log: true });
        this.outputChannel = vscode.window.createOutputChannel('Ultimate Results');
        this.collection = vscode.languages.createDiagnosticCollection('ultimate');
        this.initOutputChannel();
        this.initLogChannel();
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
    }
    setSettingsFile(path) {
        if (fs.existsSync(path.fsPath) && RegExp(/(.*\.epf$)/).exec(path.fsPath)) {
            this.settingsFilePath = path;
        }
    }
    getResultsOfLastRun() {
        return this.results;
    }
    dispose() {
        this.outputChannel.dispose();
    }
    log(message, severity) {
        switch (severity) {
            case vscode.DiagnosticSeverity.Error:
                this.logChannel.append(message);
                break;
            case vscode.DiagnosticSeverity.Warning:
                this.logChannel.append(message);
                break;
            case vscode.DiagnosticSeverity.Hint:
                this.logChannel.append(message);
                break;
            default:
                this.logChannel.append(message);
        }
    }
    embedDiagnosticInfoInto(document) {
        if (document) {
            let diagnostics = this.prepareDiagnosticInfo(document);
            this.collection.set(document.uri, diagnostics);
        }
    }
    prepareDiagnosticInfo(document) {
        // Implement the method to prepare diagnostic info
        return [];
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
        return true;
    }
}
exports.UltimateBase = UltimateBase;
//# sourceMappingURL=ultimate.js.map