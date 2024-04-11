"use strict";
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
exports.buildDockerImage = exports.checkIfImageExists = exports.cloneDIGRepository = void 0;
const child_process_1 = require("child_process");
const vscode = __importStar(require("vscode"));
const fs = __importStar(require("fs"));
/** Clones the DIG repository if the repository is not already present on the user's local machine.
 *
 * @param {string} targetDirectory The path to the directory where the DIG repository should be cloned
 * @returns {Promise<void>} A promise that resolves when the repository had been successfully cloned or if it already exists
*/
function cloneDIGRepository(targetDirectory) {
    return new Promise((resolve, reject) => {
        // Checks if Git is available and prompts the user to intall it if it is not
        (0, child_process_1.exec)('git --version', (error) => {
            if (error) {
                vscode.window.showErrorMessage('Git is not installed on your system. Please install Git to use this extension.');
                return reject(new Error('Git not installed'));
            }
            // Check if the target directory exists and is not empty
            fs.readdir(targetDirectory, (err, files) => {
                if (err) {
                    // If the directory does not exist, proceed to clone
                    console.log('Target directory does not exist, proceeding to clone.');
                }
                else if (files.length > 0) {
                    // If the directory exists and is not empty, skip the cloning step
                    return resolve();
                }
                // Command to clone the repository
                const command = `git clone --depth 1 https://github.com/dynaroars/dig.git "${targetDirectory}"`;
                // Execute the command
                (0, child_process_1.exec)(command, (cloneError, stdout, stderr) => {
                    if (cloneError) {
                        console.error('Error cloning DIG repository:', stderr);
                        reject(cloneError);
                    }
                    else {
                        console.log('DIG repository cloned successfully:', stdout);
                        resolve();
                    }
                });
            });
        });
    });
}
exports.cloneDIGRepository = cloneDIGRepository;
/** Checks if the 'dig' Docker image exists locally.
 *
 * @param {string} imageName The name of the Docker image to check
 * @returns {Promise<boolean>} A promise that resolves to true if the image exists; false otherwise
*/
function checkIfImageExists(imageName) {
    return new Promise((resolve, reject) => {
        // Execute the Docker CLI command to inspect the image
        (0, child_process_1.exec)(`docker image inspect ${imageName}`, (error, stdout, stderr) => {
            if (error) {
                // If the command returns an error, it means the image doesn't exist
                if (error.code === 1) {
                    resolve(false); // Image doesn't exist
                }
                else {
                    reject(error); // Other error occurred
                }
            }
            else {
                // If the command succeeds, it means the image exists
                resolve(true);
            }
        });
    });
}
exports.checkIfImageExists = checkIfImageExists;
/**  Function to build the Docker image if it doesn't exist or is outdated.
 *
 * @returns {Promise<void>} A promise that resolves once the Docker image has been successfully built
 */
async function buildDockerImage() {
    try {
        // Check if the Docker image exists and get its creation date
        const { exists, creationDate } = await getDockerImageInfo('dig');
        if (!exists) {
            // Builds the image if it doesn't exist 
            console.log('Building Docker image...');
            await buildImage();
            console.log('Docker image built successfully.');
        }
    }
    catch (error) {
        console.error('Error building Docker image:', error);
        throw error;
    }
}
exports.buildDockerImage = buildDockerImage;
/** Retrieves information about a Docker image.
 *
 * @param {string} imageName The name of the Docker image to inspect
 * @returns {Promise<{exists: boolean, creationDate?: Date}>} A promise that resolves with the image's information
*/
async function getDockerImageInfo(imageName) {
    return new Promise((resolve, reject) => {
        (0, child_process_1.exec)(`docker inspect --format='{{.Created}}' ${imageName}`, (error, stdout, stderr) => {
            if (error) {
                // If the image does not exist, docker inspect returns a non-zero exit code
                if (stderr.includes("No such image")) {
                    resolve({ exists: false });
                }
                else {
                    reject(error);
                }
            }
            else {
                const creationDateStr = stdout.trim();
                const creationDate = new Date(creationDateStr);
                resolve({ exists: true, creationDate });
            }
        });
    });
}
/** Executes the command to build the Docker image.
 *
 * @returns {Promise<void>} A promise that resolves once the Docker image has been built
*/
function buildImage() {
    return new Promise((resolve, reject) => {
        (0, child_process_1.exec)('docker build . -t dig', (error, stdout, stderr) => {
            if (error) {
                console.error('Error building Docker image:', error);
                reject(error);
            }
            else {
                console.log('Docker image built successfully:', stdout);
                resolve();
            }
        });
    });
}
/*
// Function to periodically check for image updates and initiate background image building
export function checkForImageUpdates(): void {
    setInterval(async () => {
        try {
            // Check for updates to the Docker image
            const updateAvailable = await isImageUpdateAvailable();

            if (updateAvailable) {
                // Initiate background image building
                console.log('Updating Docker image in the background...');
                await buildDockerImage();
                console.log('Docker image updated successfully.');
            }
        } catch (error) {
            console.error('Error updating Docker image:', error);
        }
    }, 7 * 24 * 60 * 60 * 1000); // Checks at one week intervals
}


// Function to check if an update is available for the Docker image
async function isImageUpdateAvailable(): Promise<boolean> {
    // Compare the current image version with the version available in the Docker registry
}*/ 
//# sourceMappingURL=docker_utils.js.map