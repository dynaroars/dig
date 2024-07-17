
import { exec } from 'child_process';
import { getContext } from './context';
import * as fs from 'fs';
import * as path from 'path';

export async function cloneUltimateRepo(): Promise<void> {
    const context = getContext();
    const targetDirectory = path.join(context.globalStorageUri.fsPath, 'UltimateAtomizer');

    //console.log(`Target directory for Ultimate Atomizer repository: ${targetDirectory}`);

    // Check if the directory already exists
    if (fs.existsSync(targetDirectory)) {
        //console.log(`Directory already exists: ${targetDirectory}`);
        return;
    }

    return new Promise((resolve, reject) => {
        const command = `git clone --depth 1 https://github.com/ultimate-pa/ultimate.git "${targetDirectory}"`;
        //onsole.log(`Running command: ${command}`);

        exec(command, (error, stdout, stderr) => {
            if (error) {
                console.error(`Error cloning Ultimate Atomizer repository: ${error.message}`);
                console.error(stderr);
                reject(error);
                return;
            }
            //console.log(`Successfully cloned Ultimate Atomizer repository to ${targetDirectory}`);
            resolve();
        });
    });
}


///Users/stefaniapiciorea/Library/Application Support/Code/User/globalStorage/undefined_publisher.vscode-dig/UltimateAtomizer/releaseScripts/default/adds/Ultimate.py

//const ultimateScriptPath = path.join(context.globalStorageUri.fsPath, 'UltimateAtomizer/releaseScripts/default/adds/Ultimate.py');
