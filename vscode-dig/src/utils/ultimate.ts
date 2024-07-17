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

import * as vscode from 'vscode';
import { exec } from 'child_process';
import * as path from 'path';
import * as fs from 'fs';

export function runUltimateAutomizer(filePath: string, context: vscode.ExtensionContext) {
    const ultimateRepoPath = path.join(context.globalStorageUri.fsPath, 'UltimateAtomizer');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'toolchains', 'AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'settings', 'svcomp2018', 'automizer', 'svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${filePath}" -s "${settingsPath}"`;

    exec(ultimateCommand, (error, stdout, stderr) => {
        if (error) {
            console.error(`Error running Ultimate Automizer: ${stderr}`);
            vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
            return;
        }
        console.log(`Ultimate Automizer Output:\n${stdout}`);
        vscode.window.showInformationMessage(`Ultimate Automizer executed successfully.`);
    });
}


export class UltimateBase {
    private results: any[] = [];
    protected settingsFilePath: vscode.Uri = vscode.Uri.file('');
    protected toolchainFilePath: vscode.Uri = vscode.Uri.file('');
    private ultimateIsRunning: boolean = false;
    private progressCancellationToken: vscode.CancellationTokenSource | null = null;
    private logChannel: vscode.OutputChannel;
    private outputChannel: vscode.OutputChannel;
    private collection: vscode.DiagnosticCollection;
    private extensionContext: vscode.ExtensionContext;

    constructor(context: vscode.ExtensionContext) {
        this.extensionContext = context;
        this.logChannel = vscode.window.createOutputChannel('Ultimate Log', { log: true });
        this.outputChannel = vscode.window.createOutputChannel('Ultimate Results');
        this.collection = vscode.languages.createDiagnosticCollection('ultimate');
        this.initOutputChannel();
        this.initLogChannel();
    }

    private initLogChannel() {
        this.extensionContext.subscriptions.push(this.logChannel);
        this.logChannel.appendLine('Ultimate activated');
        this.logChannel.show();
    }

    private initOutputChannel() {
        this.extensionContext.subscriptions.push(this.outputChannel);
        this.outputChannel.appendLine('Ultimate activated');
    }

    public setToolchainFile(path: vscode.Uri) {
        if (fs.existsSync(path.fsPath) && RegExp(/(.*\.xml$)/).exec(path.fsPath)) {
            this.toolchainFilePath = path;
        } 
    }

    public setSettingsFile(path: vscode.Uri) {
        if (fs.existsSync(path.fsPath) && RegExp(/(.*\.epf$)/).exec(path.fsPath)) {
            this.settingsFilePath = path;
        } 
    }

    public getResultsOfLastRun() {
        return this.results;
    }

    public dispose() {
        this.outputChannel.dispose();
    }

    public log(message: string, severity: vscode.DiagnosticSeverity) {
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

    public embedDiagnosticInfoInto(document: vscode.TextDocument) {
        if (document) {
            let diagnostics = this.prepareDiagnosticInfo(document);
            this.collection.set(document.uri, diagnostics);
        }
    }

    private prepareDiagnosticInfo(document: vscode.TextDocument): vscode.Diagnostic[] {
        // Implement the method to prepare diagnostic info
        return [];
    }

    public convertSeverity(logLvl: string): vscode.DiagnosticSeverity {
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

    public showProgressInStatusBar(title: string) {
        vscode.window.withProgress({
            title: title,
            location: vscode.ProgressLocation.Window,
            cancellable: true,
        }, (progress, token) => {
            return new Promise<void>((resolve) => {
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

    public stopShowingProgressInStatusBar() {
        this.progressCancellationToken?.cancel();
    }

    public lockUltimate(): boolean {
        if (!this.ultimateIsRunning) {
            this.ultimateIsRunning = true;
            return true;
        } else {
            return false;
        }
    }

    public freeUltimate() {
        this.ultimateIsRunning = false;
    }

    public isLocked(): boolean {
        return this.ultimateIsRunning;
    }

    public isDocument(obj: any): obj is vscode.TextDocument {
        return true;
    }
}
