
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
import { exec } from 'child_process';

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
                //vscode.window.showInformationMessage('DIG repository successfully cloned and ready to use.');
                await context.globalState.update(repoClonedKey, true);
            } 

        const bundledDotSarlPath = vscode.Uri.joinPath(context.extensionUri, 'resources', 'dot_sarl').fsPath;    
        const digDotSarlPath = path.join(targetDirectory, 'EXTERNAL_FILES', 'dot_sarl');

        try {
            fs.copyFileSync(bundledDotSarlPath, digDotSarlPath);
            console.log('Successfully replaced dot_sarl in DIG repo.');
        
        } catch (err) {
            console.error('Failed to replace dot_sarl:', err);
            vscode.window.showWarningMessage('DIG was cloned, but dot_sarl could not be patched.');
        }

        const civlJarPath = path.join(targetDirectory, 'EXTERNAL_FILES', 'CIVL-1.22_5854', 'lib', 'civl-1.22_5854.jar');
        const civlTgzPath = path.join(targetDirectory, 'EXTERNAL_FILES', 'CIVL-1.22_5854.tgz');
        const civlExtractPath = path.join(targetDirectory, 'EXTERNAL_FILES');

        if (!fs.existsSync(civlJarPath)) {
        if (fs.existsSync(civlTgzPath)) {
        
        console.log('CIVL jar not found — extracting archive...');
        exec(`tar -xzf "${civlTgzPath}" -C "${civlExtractPath}"`, (error, stdout, stderr) => {
        if (error) {
            console.error(`Failed to extract CIVL: ${stderr}`);
        } else {
            console.log('CIVL archive extracted successfully.');
        }
            });
        } else {
        
        console.warn('CIVL archive not found — skipping extraction.');
        }
        }
        
        try {
            if (!(await checkIfImageExists('dig'))) {
                console.log('Building Docker image ...');
                await buildDockerImage(targetDirectory);
            }
        } catch (error: any) {
            vscode.window.showErrorMessage(`Error initializing Docker environment: ${error.message}`);
        }

        const ultimateRepoClonedKey = 'ultimateRepoCloned';
        const ultimateRepoCloned = context.globalState.get<boolean>(ultimateRepoClonedKey, false);
        const ultimateRepoPath = path.join(targetDirectory, 'UltimateAtomizer');

        if (!ultimateRepoCloned || !fs.existsSync(ultimateRepoPath)) {
            //console.log('Cloning Ultimate Atomizer repository...');
            await cloneUltimateRepo();
            //vscode.window.showInformationMessage('Ultimate repository successfully cloned and ready to use.');
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
