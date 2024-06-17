/*import { exec } from 'child_process';
import path from 'path';
import * as vscode from 'vscode';

export function runUltimateByLog(filePath: string, context: vscode.ExtensionContext) {
    const ultimateRepoPath = context.globalStorageUri.fsPath;
    const ultimatePath = path.join(ultimateRepoPath, 'UltimateAtomizer', 'releaseScripts', 'log', 'Ultimate.py');
    const ultimateCommand = `python3 "${ultimatePath}" -i "${filePath}"`;

    exec(ultimateCommand, (error, stdout, stderr) => {
        if (error) {
            console.error(`Error running Ultimate By Log: ${stderr}`);
            return;
        }
        console.log(`Ultimate By Log Output:\n${stdout}`);
    });
}*/

/*good 2
import * as vscode from 'vscode';
import { exec } from 'child_process';
import * as path from 'path';

export function runUltimateByLog(filePath: string) {
    const ultimateRepoPath = vscode.workspace.getConfiguration().get<string>('ultimate.repoPath') || '';
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const ultimateCommand = `python3 "${ultimatePath}" "${filePath}"`;

    exec(ultimateCommand, (error, stdout, stderr) => {
        if (error) {
            console.error(`Error running Ultimate by Log: ${stderr}`);
            return;
        }
        console.log(`Ultimate by Log Output:\n${stdout}`);
    });
}

*/

/*
import * as vscode from 'vscode';
import { UltimateBase } from './ultimate';
import { exec } from 'child_process';

export class UltimateByLog extends UltimateBase {
    private executable: string;

    constructor(context: vscode.ExtensionContext, executable: string, settings: vscode.Uri, protected toolchainFilePath: vscode.Uri) {
        super(context);
        this.executable = executable;
    }

    run(filePath: string) {
        const ultimateCommand = `${this.executable} -tc "${this.toolchainFilePath.fsPath}" -i "${filePath}" -s "${this.settingsFilePath.fsPath}"`;

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
}*/


import { exec } from 'child_process';
import * as vscode from 'vscode';
import { UltimateBase } from './ultimateBase';

export class UltimateByLog extends UltimateBase {
    prepareDiagnosticInfo(document: vscode.TextDocument): vscode.Diagnostic[] {
        throw new Error('Method not implemented.');
    }

    private executable: string;

    constructor(context: vscode.ExtensionContext, executable: string, settings: vscode.Uri, toolchain: vscode.Uri) {
        super(context);
        this.executable = executable;
        this.setSettingsFile(settings);
        this.setToolchainFile(toolchain);
    }

    run(filePath: string) {
        this.runOn(filePath);
    }

    protected runOn(filePath: string) {
        const settingsPath = this.settingsFilePath.fsPath;
        //const toolchainPath = this.toolchainFilePath.fsPath;
        const propertyFile = this.settingsFilePath.fsPath;
        const ultimateCommand = `python3 "${this.executable}" "${propertyFile}" "${filePath}" 64bit simple`;
        
        exec(ultimateCommand, (error, stdout, stderr) => {
            if (error) {
                this.log(`Error running Ultimate Automizer: ${stderr}`, vscode.DiagnosticSeverity.Error);
                return;
            }
            this.log(`Ultimate Automizer Output:\n${stdout}`, vscode.DiagnosticSeverity.Information);
        });
    }

    log(message: string, severity: vscode.DiagnosticSeverity) {
        switch (severity) {
            case vscode.DiagnosticSeverity.Error:
                this.logChannel.appendLine(`Error: ${message}`);
                break;
            case vscode.DiagnosticSeverity.Warning:
                this.logChannel.appendLine(`Warning: ${message}`);
                break;
            case vscode.DiagnosticSeverity.Hint:
                this.logChannel.appendLine(`Hint: ${message}`);
                break;
            default:
                this.logChannel.appendLine(message);
        }
    }
}
