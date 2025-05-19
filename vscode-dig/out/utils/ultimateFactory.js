"use strict";
/*import { runUltimateAutomizer } from './ultimate';
import { runUltimateByHttp } from './ultimateByHttp';
import { runUltimateByLog } from './ultimateByLog';
import * as vscode from 'vscode';

export function runUltimate(filePath: string, context: vscode.ExtensionContext, method: string = 'automizer') {
    switch (method) {
        case 'http':
            runUltimateByHttp(filePath, context);
            break;
        case 'log':
            runUltimateByLog(filePath, context);
            break;
        default:
            runUltimateAutomizer(context, filePath);
            break;
    }
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
exports.runUltimate = exports.UltimateFactory = void 0;
/*Good 2
import { runUltimateAutomizer } from './ultimate';
import { runUltimateByHttp } from './ultimateByHttp';
import { runUltimateByLog } from './ultimateByLog';
import * as vscode from 'vscode';

export function runUltimate(filePath: string, method: string = 'automizer', context: vscode.ExtensionContext) {
    switch (method) {
        case 'http':
            runUltimateByHttp(filePath);
            break;
        case 'log':
            runUltimateByLog(filePath);
            break;
        default:
            runUltimateAutomizer(filePath, context);
            break;
    }
}

*/
const ultimateByHttp_1 = require("./ultimateByHttp");
const ultimateByLog_1 = require("./ultimateByLog");
const ultimate_1 = require("./ultimate");
const vscode = __importStar(require("vscode"));
const publicKnownAPIs = [
    'https://ultimate.sopranium.de/api',
    'https://monteverdi.informatik.uni-freiburg.de',
];
class UltimateFactory {
    static createUltimateUsingLog(context, executable, settings, toolchain) {
        const newUltimateInstance = new ultimateByLog_1.UltimateByLog(context, executable, settings, toolchain);
        return newUltimateInstance;
    }
    static createUltimateUsingRestApi(context, apiUrl, settings, toolchain) {
        const newUltimateInstance = new ultimateByHttp_1.UltimateByHttp(context, settings, toolchain, apiUrl);
        let refreshTime = vscode.workspace.getConfiguration().get('ultimate.refreshRate') ?? 3000;
        if (publicKnownAPIs.includes(apiUrl)) {
            refreshTime = Math.min(3000, refreshTime);
        }
        newUltimateInstance.refreshTimeInMilliseconds = refreshTime;
        return newUltimateInstance;
    }
}
exports.UltimateFactory = UltimateFactory;
function runUltimate(filePath, method = 'automizer', context) {
    const ultimateBase = new ultimate_1.UltimateBase(context);
    const ultimateRepoPath = context.globalStorageUri.fsPath + '/UltimateAtomizer';
    const toolchainPath = vscode.Uri.file(`${ultimateRepoPath}/trunk/examples/toolchains/AutomizerC.xml`);
    const settingsPath = vscode.Uri.file(`${ultimateRepoPath}/trunk/examples/settings/svcomp2018/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf`);
    switch (method) {
        case 'http':
            const apiUrl = vscode.workspace.getConfiguration().get('ultimate.apiUrl') || 'https://ultimate.sopranium.de/api';
            UltimateFactory.createUltimateUsingRestApi(context, apiUrl, settingsPath, toolchainPath).runOn(filePath);
            break;
        case 'log':
            const executable = `${ultimateRepoPath}/releaseScripts/legacy/svcomp2015/Ultimate.py`;
            UltimateFactory.createUltimateUsingLog(context, executable, settingsPath, toolchainPath).run(filePath);
            break;
        default:
            const defaultExecutable = `${ultimateRepoPath}/releaseScripts/legacy/svcomp2015/Ultimate.py`;
            UltimateFactory.createUltimateUsingLog(context, defaultExecutable, settingsPath, toolchainPath).run(filePath);
            break;
    }
}
exports.runUltimate = runUltimate;
//# sourceMappingURL=ultimateFactory.js.map