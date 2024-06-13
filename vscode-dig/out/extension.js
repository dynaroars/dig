"use strict";
/*GOOOD
import * as vscode from 'vscode';
import { insertAssertions } from './commands/insertAssertions';
import { testAssertions } from './commands/testAssertions';
import { insertCustomAssertions } from './commands/insertCustomAssertions';
import { buildDockerImage, cloneDIGRepository } from './utils/docker_utils';
import { checkIfImageExists } from './utils/docker_utils';
import { setContext } from './utils/context';
import { testWithUltimateAutomizer } from './commands/testAssertionsWithUltimateAutomizer';
import { cloneUltimateRepo } from './utils/ultimate_automizer_utils';
import path from 'path';
import fs from 'fs';

export async function activate(context: vscode.ExtensionContext) {
    // Check if the Docker image exists locally; build it if it does not.
    // TODO: If an updated image exists, the current image will be replaced with the updated one.
    const imageName = 'dig';
    

    // The target directory for cloning. This is the global storage path provided by VS Code.
    // This directory is meant to store data that doesn't need to be accessed by other applications
    // or by the user directly. Since the user doesn't need to interact with dig's source code directly,
    // this is a god place to clone.
    const targetDirectory = context.globalStorageUri.fsPath;

    setContext(context);

        try {
            const repoClonedKey = 'repoCloned';
            const repoCloned = context.globalState.get<boolean>(repoClonedKey, false);

            if (!repoCloned) {
                await cloneDIGRepository(targetDirectory);
                vscode.window.showInformationMessage('DIG repository successfully cloned and ready to use.');
    
                await context.globalState.update(repoClonedKey, true);
            } else {
                console.log('DIG repository already cloned. Skipping cloning.');
            }

        try {
            if (!(await checkIfImageExists('dig'))) {
                console.log('Building Docker image as it does not exist...');
                await buildDockerImage(targetDirectory);
            }

        } catch (error: any) {
            vscode.window.showErrorMessage(`Error initializing Docker environment: ${error.message}`);
        }

        
     // Clone Ultimate repository if not already cloned
     const ultimateRepoClonedKey = 'ultimateRepoCloned';
     const ultimateRepoCloned = context.globalState.get<boolean>(ultimateRepoClonedKey, false);
     const ultimateRepoPath = path.join("/Users/stefaniapiciorea/Documents/Github/dig/vscode-dig/UltimateAtomizer");
     
     if (!ultimateRepoCloned || !fs.existsSync(ultimateRepoPath)) {
         console.log('Cloning Ultimate Atomizer repository...');
         await cloneUltimateRepo();
         vscode.window.showInformationMessage('Ultimate repository successfully cloned and ready to use.');
         await context.globalState.update(ultimateRepoClonedKey, true);
     } else {
         console.log(`Ultimate repository already cloned. Skipping cloning. Path: ${ultimateRepoPath}`);
     }






    let disposable = vscode.commands.registerCommand('vscode-dig.insertAssertions', insertAssertions);
    context.subscriptions.push(disposable);

    let disposableTestAssertions = vscode.commands.registerCommand('vscode-dig.testAssertions', testAssertions);
    context.subscriptions.push(disposableTestAssertions);

    let disposableCustomAssertions = vscode.commands.registerCommand('vscode-dig.insertCustomAssertions', insertCustomAssertions);
    context.subscriptions.push(disposableCustomAssertions);

    let disposableTestAssertionsWithUltimateAutomizer = vscode.commands.registerCommand('vscode-dig.testAssertionsWithUltimateAutomizer', testWithUltimateAutomizer);
    context.subscriptions.push(disposableTestAssertionsWithUltimateAutomizer);


}catch (error: any) {
    vscode.window.showErrorMessage(`Error setting up DIG: ${error.message}`);
};

}

export function deactivate() {}

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
exports.deactivate = exports.activate = void 0;
/*
import * as vscode from 'vscode';
import { insertAssertions } from './commands/insertAssertions';
import { testAssertions } from './commands/testAssertions';
import { insertCustomAssertions } from './commands/insertCustomAssertions';
import { buildDockerImage, cloneDIGRepository } from './utils/docker_utils';
import { checkIfImageExists } from './utils/docker_utils';
import { setContext } from './utils/context';
import { testWithUltimateAutomizer } from './commands/testAssertionsWithUltimateAutomizer';
import { cloneUltimateRepo } from './utils/ultimate_automizer_utils';
import path from 'path';
import fs from 'fs';

export async function activate(context: vscode.ExtensionContext) {
    // Check if the Docker image exists locally; build it if it does not.
    // TODO: If an updated image exists, the current image will be replaced with the updated one.
    const imageName = 'dig';
    
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) {
        vscode.window.showErrorMessage('No workspace is open. Please open a workspace to use this extension.');
        return;
    }

    // The target directory for cloning DIG. This is the global storage path provided by VS Code.
    const targetDirectory = context.globalStorageUri.fsPath;

    setContext(context);

    try {
        const repoClonedKey = 'repoCloned';
        const repoCloned = context.globalState.get<boolean>(repoClonedKey, false);

        if (!repoCloned) {
            await cloneDIGRepository(targetDirectory);
            vscode.window.showInformationMessage('DIG repository successfully cloned and ready to use.');
            await context.globalState.update(repoClonedKey, true);
        } else {
            console.log('DIG repository already cloned. Skipping cloning.');
        }

        if (!(await checkIfImageExists('dig'))) {
            console.log('Building Docker image as it does not exist...');
            await buildDockerImage(targetDirectory);
        }

    } catch (error: any) {
        vscode.window.showErrorMessage(`Error initializing Docker environment: ${error.message}`);
    }

    // Clone Ultimate repository if not already cloned
    const ultimateRepoClonedKey = 'ultimateRepoCloned';
    const ultimateRepoCloned = context.globalState.get<boolean>(ultimateRepoClonedKey, false);
    const ultimateRepoPath = path.join(workspaceFolders[0].uri.fsPath, 'UltimateAtomizer');
    
    if (!ultimateRepoCloned || !fs.existsSync(ultimateRepoPath)) {
        console.log('Cloning Ultimate Atomizer repository...');
        await cloneUltimateRepo();
        vscode.window.showInformationMessage('Ultimate repository successfully cloned and ready to use.');
        await context.globalState.update(ultimateRepoClonedKey, true);
    } else {
        console.log(`Ultimate repository already cloned. Skipping cloning. Path: ${ultimateRepoPath}`);
    }

    // Register commands
    let disposable = vscode.commands.registerCommand('vscode-dig.insertAssertions', insertAssertions);
    context.subscriptions.push(disposable);

    let disposableTestAssertions = vscode.commands.registerCommand('vscode-dig.testAssertions', testAssertions);
    context.subscriptions.push(disposableTestAssertions);

    let disposableCustomAssertions = vscode.commands.registerCommand('vscode-dig.insertCustomAssertions', insertCustomAssertions);
    context.subscriptions.push(disposableCustomAssertions);

    let disposableTestAssertionsWithUltimateAutomizer = vscode.commands.registerCommand('vscode-dig.testAssertionsWithUltimateAutomizer', testWithUltimateAutomizer);
    context.subscriptions.push(disposableTestAssertionsWithUltimateAutomizer);
}

export function deactivate() {}
*/
/*
import * as vscode from 'vscode';
import { insertAssertions } from './commands/insertAssertions';
import { testAssertions } from './commands/testAssertions';
import { insertCustomAssertions } from './commands/insertCustomAssertions';
import { buildDockerImage, cloneDIGRepository } from './utils/docker_utils';
import { checkIfImageExists } from './utils/docker_utils';
import { setContext } from './utils/context';
import { testWithUltimateAutomizer } from './commands/testAssertionsWithUltimateAutomizer';
import { cloneUltimateRepo } from './utils/ultimate_automizer_utils';
import path from 'path';
import fs from 'fs';

export async function activate(context: vscode.ExtensionContext) {
    const imageName = 'dig';
    
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) {
        vscode.window.showErrorMessage('No workspace is open. Please open a workspace to use this extension.');
        return;
    }

    const targetDirectory = context.globalStorageUri.fsPath;

    setContext(context);

    try {
        const repoClonedKey = 'repoCloned';
        const repoCloned = context.globalState.get<boolean>(repoClonedKey, false);

        if (!repoCloned) {
            await cloneDIGRepository(targetDirectory);
            vscode.window.showInformationMessage('DIG repository successfully cloned and ready to use.');
            await context.globalState.update(repoClonedKey, true);
        } else {
            console.log('DIG repository already cloned. Skipping cloning.');
        }

        if (!(await checkIfImageExists('dig'))) {
            console.log('Building Docker image as it does not exist...');
            await buildDockerImage(targetDirectory);
        }

    } catch (error: any) {
        vscode.window.showErrorMessage(`Error initializing Docker environment: ${error.message}`);
    }

    // Clone Ultimate repository if not already cloned
    const ultimateRepoClonedKey = 'ultimateRepoCloned';
    const ultimateRepoCloned = context.globalState.get<boolean>(ultimateRepoClonedKey, false);
    const ultimateRepoPath = path.join(context.extensionPath, 'UltimateAtomizer');
    
    if (!ultimateRepoCloned || !fs.existsSync(ultimateRepoPath)) {
        console.log('Cloning Ultimate Atomizer repository...');
        await cloneUltimateRepo(context);
        vscode.window.showInformationMessage('Ultimate repository successfully cloned and ready to use.');
        await context.globalState.update(ultimateRepoClonedKey, true);
    } else {
        console.log(`Ultimate repository already cloned. Skipping cloning. Path: ${ultimateRepoPath}`);
    }

    // Register commands
    let disposable = vscode.commands.registerCommand('vscode-dig.insertAssertions', insertAssertions);
    context.subscriptions.push(disposable);

    let disposableTestAssertions = vscode.commands.registerCommand('vscode-dig.testAssertions', testAssertions);
    context.subscriptions.push(disposableTestAssertions);

    let disposableCustomAssertions = vscode.commands.registerCommand('vscode-dig.insertCustomAssertions', insertCustomAssertions);
    context.subscriptions.push(disposableCustomAssertions);

    let disposableTestAssertionsWithUltimateAutomizer = vscode.commands.registerCommand('vscode-dig.testAssertionsWithUltimateAutomizer', testWithUltimateAutomizer);
    context.subscriptions.push(disposableTestAssertionsWithUltimateAutomizer);

}

export function deactivate() {}
*/
/*
import * as vscode from 'vscode';
import { insertAssertions } from './commands/insertAssertions';
import { testAssertions } from './commands/testAssertions';
import { insertCustomAssertions } from './commands/insertCustomAssertions';
import { buildDockerImage, cloneDIGRepository } from './utils/docker_utils';
import { checkIfImageExists } from './utils/docker_utils';
import { setContext } from './utils/context';
import { cloneUltimateRepo } from './utils/ultimate_automizer_utils';
import { runUltimate } from './utils/ultimateFactory';
import path from 'path';
import fs from 'fs';

export async function activate(context: vscode.ExtensionContext) {
    const imageName = 'dig';

    const targetDirectory = context.globalStorageUri.fsPath;

    setContext(context);

    try {
        const repoClonedKey = 'repoCloned';
        const repoCloned = context.globalState.get<boolean>(repoClonedKey, false);

        if (!repoCloned) {
            await cloneDIGRepository(targetDirectory);
            vscode.window.showInformationMessage('DIG repository successfully cloned and ready to use.');
            await context.globalState.update(repoClonedKey, true);
        } else {
            console.log('DIG repository already cloned. Skipping cloning.');
        }

        try {
            if (!(await checkIfImageExists('dig'))) {
                console.log('Building Docker image as it does not exist...');
                await buildDockerImage(targetDirectory);
            }
        } catch (error: any) {
            vscode.window.showErrorMessage(`Error initializing Docker environment: ${error.message}`);
        }

        const ultimateRepoClonedKey = 'ultimateRepoCloned';
        const ultimateRepoCloned = context.globalState.get<boolean>(ultimateRepoClonedKey, false);
        const ultimateRepoPath = path.join(targetDirectory, 'UltimateAtomizer');
     
        if (!ultimateRepoCloned || !fs.existsSync(ultimateRepoPath)) {
            console.log('Cloning Ultimate Atomizer repository...');
            await cloneUltimateRepo();
            vscode.window.showInformationMessage('Ultimate repository successfully cloned and ready to use.');
            await context.globalState.update(ultimateRepoClonedKey, true);
        } else {
            console.log(`Ultimate repository already cloned. Skipping cloning. Path: ${ultimateRepoPath}`);
        }

        let disposable = vscode.commands.registerCommand('vscode-dig.insertAssertions', insertAssertions);
        context.subscriptions.push(disposable);

        let disposableTestAssertions = vscode.commands.registerCommand('vscode-dig.testAssertions', testAssertions);
        context.subscriptions.push(disposableTestAssertions);

        let disposableCustomAssertions = vscode.commands.registerCommand('vscode-dig.insertCustomAssertions', insertCustomAssertions);
        context.subscriptions.push(disposableCustomAssertions);

        let disposableTestAssertionsWithUltimateAutomizer = vscode.commands.registerCommand('vscode-dig.testAssertionsWithUltimateAutomizer', () => {
            const editor = vscode.window.activeTextEditor;
            if (editor) {
                const document = editor.document;
                runUltimate(document.fileName, context, 'automizer');
            }
        });
        context.subscriptions.push(disposableTestAssertionsWithUltimateAutomizer);

    } catch (error: any) {
        vscode.window.showErrorMessage(`Error setting up DIG: ${error.message}`);
    }
}

export function deactivate() {}
*/
/*good 2
import * as vscode from 'vscode';
import { insertAssertions } from './commands/insertAssertions';
import { testAssertions } from './commands/testAssertions';
import { insertCustomAssertions } from './commands/insertCustomAssertions';
import { buildDockerImage, cloneDIGRepository } from './utils/docker_utils';
import { checkIfImageExists } from './utils/docker_utils';
import { setContext } from './utils/context';
import { testWithUltimateAutomizer } from './commands/testAssertionsWithUltimateAutomizer';
import { cloneUltimateRepo } from './utils/ultimate_automizer_utils';
import { runUltimate } from './utils/ultimateFactory';
import path from 'path';
import fs from 'fs';
import { UltimateBase } from './utils/ultimate';

export async function activate(context: vscode.ExtensionContext) {
    const imageName = 'dig';
    const targetDirectory = context.globalStorageUri.fsPath;
    setContext(context);

    try {
        const repoClonedKey = 'repoCloned';
        const repoCloned = context.globalState.get<boolean>(repoClonedKey, false);

        if (!repoCloned) {
            await cloneDIGRepository(targetDirectory);
            vscode.window.showInformationMessage('DIG repository successfully cloned and ready to use.');
            await context.globalState.update(repoClonedKey, true);
        } else {
            console.log('DIG repository already cloned. Skipping cloning.');
        }

        try {
            if (!(await checkIfImageExists('dig'))) {
                console.log('Building Docker image as it does not exist...');
                await buildDockerImage(targetDirectory);
            }
        } catch (error: any) {
            vscode.window.showErrorMessage(`Error initializing Docker environment: ${error.message}`);
        }

        const ultimateRepoClonedKey = 'ultimateRepoCloned';
        const ultimateRepoCloned = context.globalState.get<boolean>(ultimateRepoClonedKey, false);
        const ultimateRepoPath = path.join(context.globalStorageUri.fsPath, 'UltimateAtomizer');

        if (!ultimateRepoCloned || !fs.existsSync(ultimateRepoPath)) {
            console.log('Cloning Ultimate Atomizer repository...');
            await cloneUltimateRepo();
            vscode.window.showInformationMessage('Ultimate repository successfully cloned and ready to use.');
            await context.globalState.update(ultimateRepoClonedKey, true);
        } else {
            console.log(`Ultimate repository already cloned. Skipping cloning. Path: ${ultimateRepoPath}`);
        }

        const ultimateBase = new UltimateBase(context);
        ultimateBase.setToolchainFile(vscode.Uri.file(path.join(ultimateRepoPath, 'trunk/examples/toolchains/AutomizerC.xml')));
        ultimateBase.setSettingsFile(vscode.Uri.file(path.join(ultimateRepoPath, 'trunk/examples/settings/svcomp2018/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf')));

        await vscode.workspace.getConfiguration().update('ultimate.context', targetDirectory, vscode.ConfigurationTarget.Global);

        let disposable = vscode.commands.registerCommand('vscode-dig.insertAssertions', insertAssertions);
        context.subscriptions.push(disposable);

        let disposableTestAssertions = vscode.commands.registerCommand('vscode-dig.testAssertions', testAssertions);
        context.subscriptions.push(disposableTestAssertions);

        let disposableCustomAssertions = vscode.commands.registerCommand('vscode-dig.insertCustomAssertions', insertCustomAssertions);
        context.subscriptions.push(disposableCustomAssertions);

        let disposableTestAssertionsWithUltimateAutomizer = vscode.commands.registerCommand('vscode-dig.testAssertionsWithUltimateAutomizer', testWithUltimateAutomizer);
        context.subscriptions.push(disposableTestAssertionsWithUltimateAutomizer);

    } catch (error: any) {
        vscode.window.showErrorMessage(`Error setting up DIG: ${error.message}`);
    }
}

export function deactivate() {}
*/
const vscode = __importStar(require("vscode"));
const insertAssertions_1 = require("./commands/insertAssertions");
const testAssertions_1 = require("./commands/testAssertions");
const insertCustomAssertions_1 = require("./commands/insertCustomAssertions");
const docker_utils_1 = require("./utils/docker_utils");
const docker_utils_2 = require("./utils/docker_utils");
const context_1 = require("./utils/context");
//import { UltimateBase } from './utils/ultimate';
async function activate(context) {
    const imageName = 'dig';
    const targetDirectory = context.globalStorageUri.fsPath;
    (0, context_1.setContext)(context);
    try {
        const repoClonedKey = 'repoCloned';
        const repoCloned = context.globalState.get(repoClonedKey, false);
        if (!repoCloned) {
            await (0, docker_utils_1.cloneDIGRepository)(targetDirectory);
            vscode.window.showInformationMessage('DIG repository successfully cloned and ready to use.');
            await context.globalState.update(repoClonedKey, true);
        }
        else {
            console.log('DIG repository already cloned. Skipping cloning.');
        }
        try {
            if (!(await (0, docker_utils_2.checkIfImageExists)('dig'))) {
                console.log('Building Docker image as it does not exist...');
                await (0, docker_utils_1.buildDockerImage)(targetDirectory);
            }
        }
        catch (error) {
            vscode.window.showErrorMessage(`Error initializing Docker environment: ${error.message}`);
        }
        /*const ultimateRepoClonedKey = 'ultimateRepoCloned';
        const ultimateRepoCloned = context.globalState.get<boolean>(ultimateRepoClonedKey, false);
        const ultimateRepoPath = path.join(targetDirectory, 'UltimateAtomizer');

        if (!ultimateRepoCloned || !fs.existsSync(ultimateRepoPath)) {
            console.log('Cloning Ultimate Atomizer repository...');
            await cloneUltimateRepo();
            vscode.window.showInformationMessage('Ultimate repository successfully cloned and ready to use.');
            await context.globalState.update(ultimateRepoClonedKey, true);
        } else {
            console.log(`Ultimate repository already cloned. Skipping cloning. Path: ${ultimateRepoPath}`);
        }*/
        /*const ultimateBase = new UltimateBase(context);
        ultimateBase.setToolchainFile(vscode.Uri.file(path.join(ultimateRepoPath, 'trunk/examples/toolchains/AutomizerC.xml')));
        ultimateBase.setSettingsFile(vscode.Uri.file(path.join(ultimateRepoPath, 'trunk/examples/settings/svcomp2018/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf')));

        await vscode.workspace.getConfiguration().update('ultimate.context', targetDirectory, vscode.ConfigurationTarget.Global);
        */
        let disposable = vscode.commands.registerCommand('vscode-dig.insertAssertions', insertAssertions_1.insertAssertions);
        context.subscriptions.push(disposable);
        let disposableTestAssertions = vscode.commands.registerCommand('vscode-dig.testAssertions', testAssertions_1.testAssertions);
        context.subscriptions.push(disposableTestAssertions);
        let disposableCustomAssertions = vscode.commands.registerCommand('vscode-dig.insertCustomAssertions', insertCustomAssertions_1.insertCustomAssertions);
        context.subscriptions.push(disposableCustomAssertions);
        /* let disposableTestAssertionsWithUltimateAutomizer = vscode.commands.registerCommand('vscode-dig.testAssertionsWithUltimateAutomizer', (filePath: string) => {
             runUltimate(filePath, 'automizer', context);
         });
         context.subscriptions.push(disposableTestAssertionsWithUltimateAutomizer);*/
    }
    catch (error) {
        vscode.window.showErrorMessage(`Error setting up DIG: ${error.message}`);
    }
}
exports.activate = activate;
function deactivate() { }
exports.deactivate = deactivate;
//# sourceMappingURL=extension.js.map