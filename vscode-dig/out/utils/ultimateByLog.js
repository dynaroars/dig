"use strict";
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
exports.UltimateByLog = void 0;
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
const child_process_1 = require("child_process");
const vscode = __importStar(require("vscode"));
const ultimateBase_1 = require("./ultimateBase");
class UltimateByLog extends ultimateBase_1.UltimateBase {
    prepareDiagnosticInfo(document) {
        throw new Error('Method not implemented.');
    }
    executable;
    constructor(context, executable, settings, toolchain) {
        super(context);
        this.executable = executable;
        this.setSettingsFile(settings);
        this.setToolchainFile(toolchain);
    }
    run(filePath) {
        this.runOn(filePath);
    }
    runOn(filePath) {
        const settingsPath = this.settingsFilePath.fsPath;
        //const toolchainPath = this.toolchainFilePath.fsPath;
        const propertyFile = this.settingsFilePath.fsPath;
        const ultimateCommand = `python3 "${this.executable}" "${propertyFile}" "${filePath}" 64bit simple`;
        (0, child_process_1.exec)(ultimateCommand, (error, stdout, stderr) => {
            if (error) {
                this.log(`Error running Ultimate Automizer: ${stderr}`, vscode.DiagnosticSeverity.Error);
                return;
            }
            this.log(`Ultimate Automizer Output:\n${stdout}`, vscode.DiagnosticSeverity.Information);
        });
    }
    log(message, severity) {
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
exports.UltimateByLog = UltimateByLog;
//# sourceMappingURL=ultimateByLog.js.map