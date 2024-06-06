import * as vscode from 'vscode';
import { insertAssertions } from './commands/insertAssertions';
import { testAssertions } from './commands/testAssertions';
import { insertCustomAssertions } from './commands/insertCustomAssertions';
import { buildDockerImage, cloneDIGRepository } from './utils/docker_utils';
import { checkIfImageExists } from './utils/docker_utils';
import { setContext } from './utils/context';
import { testWithUltimateAtomizer } from './commands/testAssertionsWithUltimateAtomizer';
import { cloneUltimateRepo } from './utils/ultimate_atomizer_utils';
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

    let disposableTestAssertionsWithUltimateAtomizer = vscode.commands.registerCommand('vscode-dig.testAssertionsWithUltimateAtomizer', testWithUltimateAtomizer);
    context.subscriptions.push(disposableTestAssertionsWithUltimateAtomizer);



}catch (error: any) {
    vscode.window.showErrorMessage(`Error setting up DIG: ${error.message}`);
};

}

export function deactivate() {}

