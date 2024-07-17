
import * as vscode from 'vscode';
import { insertAssertions } from './commands/insertAssertions';
import { testAssertions } from './commands/testAssertions';
import { insertCustomAssertions } from './commands/insertCustomAssertions';
import { buildDockerImage, cloneDIGRepository } from './utils/docker_utils';
import { checkIfImageExists } from './utils/docker_utils';
import { setContext } from './utils/context';
import { cloneUltimateRepo } from './utils/ultimate_automizer_utils';
import path from 'path';
import fs from 'fs';
import { UltimateBase } from './utils/ultimate';

export async function activate(context: vscode.ExtensionContext) {
    const imageName = 'dig';
    const targetDirectory = path.join(context.globalStorageUri.fsPath, 'dig');
    setContext(context);

    try {
        const repoClonedKey = 'repoCloned';
        const repoCloned = context.globalState.get<boolean>(repoClonedKey, false);

         // Check if the DIG repository directory exists
         const digRepoPath = path.join(targetDirectory, 'dig');
      

            if (!repoCloned || !fs.existsSync(digRepoPath)) {
                await cloneDIGRepository(targetDirectory);
                vscode.window.showInformationMessage('DIG repository successfully cloned and ready to use.');
                await context.globalState.update(repoClonedKey, true);
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

    } catch (error: any) {
        vscode.window.showErrorMessage(`Error setting up DIG: ${error.message}`);
    }
}

export function deactivate() {}
