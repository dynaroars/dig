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

import { UltimateByHttp } from './ultimateByHttp';
import { UltimateByLog } from './ultimateByLog';
import { UltimateBase } from './ultimate';
import * as vscode from 'vscode';


const publicKnownAPIs = [
    'https://ultimate.sopranium.de/api',
    'https://monteverdi.informatik.uni-freiburg.de',
];

export class UltimateFactory {
    static createUltimateUsingLog(context: vscode.ExtensionContext, executable: string, settings: vscode.Uri, toolchain: vscode.Uri): UltimateByLog {
        const newUltimateInstance = new UltimateByLog(context, executable, settings, toolchain);
        return newUltimateInstance;
    }

    static createUltimateUsingRestApi(context: vscode.ExtensionContext, apiUrl: string, settings: vscode.Uri, toolchain: vscode.Uri): UltimateByHttp {
        const newUltimateInstance = new UltimateByHttp(context, settings, toolchain, apiUrl);
        let refreshTime = vscode.workspace.getConfiguration().get<number>('ultimate.refreshRate') ?? 3000;
        if (publicKnownAPIs.includes(apiUrl)) {
            refreshTime = Math.min(3000, refreshTime);
        }
        newUltimateInstance.refreshTimeInMilliseconds = refreshTime;
        return newUltimateInstance;
    }
}

export function runUltimate(filePath: string, method: string = 'automizer', context: vscode.ExtensionContext) {
    const ultimateBase = new UltimateBase(context);
    const ultimateRepoPath = context.globalStorageUri.fsPath + '/UltimateAtomizer';
    const toolchainPath = vscode.Uri.file(`${ultimateRepoPath}/trunk/examples/toolchains/AutomizerC.xml`);
    const settingsPath = vscode.Uri.file(`${ultimateRepoPath}/trunk/examples/settings/svcomp2018/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf`);

    switch (method) {
        case 'http':
            const apiUrl = vscode.workspace.getConfiguration().get<string>('ultimate.apiUrl') || 'https://ultimate.sopranium.de/api';
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
