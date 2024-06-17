import * as vscode from 'vscode';
import * as fs from 'fs';

interface ExtendedOutputChannel extends vscode.OutputChannel {
    error(message: string): void;
    warning(message: string): void;
    debug(message: string): void;
}

export abstract class UltimateBase {
    protected results: any[] = [];
    protected error: string | null = null;
    protected settingsFilePath: vscode.Uri = vscode.Uri.file('');
    protected toolchainFilePath: vscode.Uri = vscode.Uri.file('');
    protected ultimateIsRunning: boolean = false;
    protected progressCancellationToken: vscode.CancellationTokenSource | null = null;
    protected logChannel: ExtendedOutputChannel;
    protected outputChannel: vscode.OutputChannel;
    protected collection: vscode.DiagnosticCollection;
    protected extensionContext: vscode.ExtensionContext;

    constructor(context: vscode.ExtensionContext) {
        this.extensionContext = context;
        this.logChannel = this.createExtendedOutputChannel('Ultimate Log');
        this.outputChannel = vscode.window.createOutputChannel('Ultimate Results');
        this.collection = vscode.languages.createDiagnosticCollection('ultimate');
        this.initOutputChannel();
        this.initLogChannel();
    }

    private createExtendedOutputChannel(name: string): ExtendedOutputChannel {
        const channel = vscode.window.createOutputChannel(name) as ExtendedOutputChannel;
        channel.error = (message: string) => channel.appendLine(`ERROR: ${message}`);
        channel.warning = (message: string) => channel.appendLine(`WARNING: ${message}`);
        channel.debug = (message: string) => channel.appendLine(`DEBUG: ${message}`);
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

    setToolchainFile(path: vscode.Uri) {
        if (fs.existsSync(path.fsPath) && RegExp(/(.*\.xml$)/).exec(path.fsPath)) {
            this.toolchainFilePath = path;
        } else {
            console.log(`Toolchain file ${path} does not exist`);
        }
    }

    setSettingsFile(path: vscode.Uri) {
        if (fs.existsSync(path.fsPath) && RegExp(/(.*\.epf$)/).exec(path.fsPath)) {
            this.settingsFilePath = path;
        } else {
            console.log(`Settings file ${path} does not exist`);
        }
    }

   protected abstract runOn(input: vscode.TextDocument | string, language?: string): void;

    abstract log(message: string, severity: vscode.DiagnosticSeverity): void;

    embedDiagnosticInfoInto(document: vscode.TextDocument) {
        if (document) {
            let diagnostics = this.prepareDiagnosticInfo(document);
            this.collection.set(document.uri, diagnostics);
        }
    }

    convertSeverity(logLvl: string): vscode.DiagnosticSeverity {
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

    showProgressInStatusBar(title: string) {
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

    stopShowingProgressInStatusBar() {
        this.progressCancellationToken?.cancel();
    }

    lockUltimate() {
        if (!this.ultimateIsRunning) {
            this.ultimateIsRunning = true;
            return true;
        } else {
            return false;
        }
    }

    freeUltimate() {
        this.ultimateIsRunning = false;
    }

    isLocked() {
        return this.ultimateIsRunning;
    }

    isDocument(obj: any): obj is vscode.TextDocument {
        return !!obj.languageId;
    }

    abstract prepareDiagnosticInfo(document: vscode.TextDocument): vscode.Diagnostic[];
}
