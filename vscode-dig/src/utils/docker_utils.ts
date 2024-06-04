import { exec } from 'child_process';
import * as vscode from 'vscode';
import * as fs from 'fs';

/** Clones the DIG repository if the repository is not already present on the user's local machine. 
 * 
 * @param {string} targetDirectory The path to the directory where the DIG repository should be cloned
 * @returns {Promise<void>} A promise that resolves when the repository had been successfully cloned or if it already exists
*/
export function cloneDIGRepository(targetDirectory: string): Promise<void> {
    return new Promise<void>((resolve, reject) => {
        // Checks if Git is available and prompts the user to intall it if it is not
        exec('git --version', (error) => {
            if (error) {
                vscode.window.showErrorMessage('Git is not installed on your system. Please install Git to use this extension.');
                return reject(new Error('Git not installed'));
            }

            // Check if the target directory exists and is not empty
            fs.readdir(targetDirectory, (err, files) => {
                if (err) {
                    // If the directory does not exist, proceed to clone
                    console.log('Target directory does not exist, proceeding to clone.');
                } else if (files.length > 0) {
                    // If the directory exists and is not empty, skip the cloning step

                    return resolve();
                }

                // Command to clone the repository
                const command = `git clone --depth 1 https://github.com/dynaroars/dig.git "${targetDirectory}"`;

                // Execute the command
                exec(command, (cloneError, stdout, stderr) => {
                    if (cloneError) {
                        console.error('Error cloning DIG repository:', stderr);
                        reject(cloneError);
                    } else {
                        console.log('DIG repository cloned successfully:', stdout);
                        resolve();
                    }
                });
            });
        });
    });
}

/** Checks if the 'dig' Docker image exists locally. 
 * 
 * @param {string} imageName The name of the Docker image to check
 * @returns {Promise<boolean>} A promise that resolves to true if the image exists; false otherwise
*/
/*export function checkIfImageExists(imageName: string): Promise<boolean> {
    return new Promise((resolve, reject) => {
        // Execute the Docker CLI command to inspect the image
        exec(`docker image inspect ${imageName}`, (error, stdout, stderr) => {
            if (error) {
                // If the command returns an error, it means the image doesn't exist
                if (error.code === 1) {
                    resolve(false); // Image doesn't exist
                } else {
                    reject(error); // Other error occurred
                }
            } else {
                // If the command succeeds, it means the image exists
                resolve(true);
            }
        });
    });

    
}*/

//Changed the way we check if the image exists. We now use the 'docker images -q' command to get the image ID instead of 'docker image inspect' which was
//generating an error whenever the image was not found
export async function checkIfImageExists(imageName: string): Promise<boolean> {
    return new Promise<boolean>((resolve) => {
        exec(`docker images -q ${imageName}`, (error, stdout) => {
            // Image exists if stdout is not empty
            resolve(stdout.trim() !== '');
        });
    });
}


/**  Function to build the Docker image if it doesn't exist or is outdated.
 * 
 * @returns {Promise<void>} A promise that resolves once the Docker image has been successfully built
 */
/*export async function buildDockerImage(): Promise<void> {
    try {
        // Check if the Docker image exists and get its creation date
        const { exists, creationDate } = await getDockerImageInfo('dig');

        if (!exists) {
            // Builds the image if it doesn't exist 
            console.log('Building Docker image...');
            await buildImage();
            console.log('Docker image built successfully.');
        }
    } catch (error) {
        console.error('Error building Docker image:', error);
        throw error;
    }
}*/

//Changed the way we build the image. The build command must be ran from inside the dig directory, so I am now passing that directory as a parameter
// to this function to make sure the command is ran from the correct location. This was also causing some issues with the previous implementation.

export async function buildDockerImage(targetDirectory:string): Promise<void> {
    const imageName = 'dig';
    try {
        const imageExists = await checkIfImageExists(imageName);
        if (!imageExists) {
            console.log('Docker image not found. Building now...');
            await buildImage(targetDirectory);
            console.log('Docker image built successfully.');
        } else {
            console.log('Docker image already exists. No need to build.');
        }
    } catch (error) {
        console.error('Error during Docker operation:', error);
        throw error;
    }
}

// NO LONGER NEEDED-- REMOVE LATER
/** Retrieves information about a Docker image.
 * 
 * @param {string} imageName The name of the Docker image to inspect
 * @returns {Promise<{exists: boolean, creationDate?: Date}>} A promise that resolves with the image's information
*/
/*async function getDockerImageInfo(imageName: string): Promise<{ exists: boolean; creationDate?: Date }> {
    return new Promise<{ exists: boolean; creationDate?: Date }>((resolve, reject) => {
        exec(`docker inspect --format='{{.Created}}' ${imageName}`, (error, stdout, stderr) => {
            if (error) {
                // If the image does not exist, docker inspect returns a non-zero exit code
                if (stderr.includes("No such image")) {
                    resolve({ exists: false });
                } else {
                    reject(error);
                }
            } else {
                const creationDateStr = stdout.trim();
                const creationDate = new Date(creationDateStr);
                resolve({ exists: true, creationDate });
            }
        });
    });
}*/


/** Executes the command to build the Docker image. 
 * 
 * @returns {Promise<void>} A promise that resolves once the Docker image has been built
*/
/*function buildImage(): Promise<void> {
    return new Promise<void>((resolve, reject) => {
        exec('docker build . -t dig', (error, stdout, stderr) => {
            if (error) {
                console.error('Error building Docker image:', error);
                reject(error);
            } else {
                console.log('Docker image built successfully:', stdout);
                resolve();
            }
        });
    });
}*/

//Changed the way we build the image. The build command must be ran from inside the dig directory, so I am now passing it as an argument here as well.

function buildImage(targetDirectory:string): Promise<void> {
    return new Promise<void>((resolve, reject) => {
        console.log(`Attempting to build Docker image from directory: ${targetDirectory}`);
        exec('docker build . -t dig', { cwd: targetDirectory }, (error: Error|null, stdout: string, stderr: string) => {
            if (error) {
                console.error('Error building Docker image:', error);
                console.error(stderr);
                reject(error);
            } else {
                console.log('Docker image built successfully:', stdout);
                resolve();
            }
        });
    });
}

