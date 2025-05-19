"use strict";
/*import * as vscode from 'vscode';
import { exec } from 'child_process';

export function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    // Collect necessary paths and options from the user or configuration
    const specPath = "/Users/stefaniapiciorea/Library/Application Support/Code/User/globalStorage/undefined_publisher.vscode-dig/UltimateAtomizer/releaseScripts/default/adds/props/Reach.prp";
    const architecture = "64bit"; // Replace with actual architecture (32bit or 64bit)
    const memoryModel = "precise"; // Replace with actual memory model (simple or precise)
    const cFilePath = editor.document.uri.fsPath; // Current file path
    const ultimatePath = "/Users/stefaniapiciorea/Library/Application Support/Code/User/globalStorage/undefined_publisher.vscode-dig/UltimateAtomizer/releaseScripts/legacy/svcomp2015/Ultimate.py";

    // Construct the command
    const ultimateCommand = `python3 "${ultimatePath}" "${specPath}" "${cFilePath}" ${architecture} ${memoryModel}`;

    // Log the command for debugging
    console.log(`Running command: ${ultimateCommand}`);

    // Execute the command with progress notification
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer...",
        cancellable: false
    }, (progress, token) => {
        return new Promise<void>((resolve, reject) => {
            exec(ultimateCommand, (error, stdout, stderr) => {
                console.log('Command executed');
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    reject();
                    return;
                }
                console.log('Command output:');
                console.log(stdout);
                console.error(stderr);

                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                processUltimateOutput(stdout, stderr);
                resolve();
            });
        });
    });
}

function processUltimateOutput(stdout: string, stderr: string) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);
    
    if (stdout) {
        vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    }
    
    if (stderr) {
        vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);
    }

    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";

    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }

    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
}
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
exports.testWithUltimateAutomizer = void 0;
/*
import * as vscode from 'vscode';
import { exec } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

export function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    const ultimateRepoPath = vscode.workspace.rootPath ? path.join(vscode.workspace.rootPath, 'ultimate') : '';
    const cFilePath = editor.document.uri.fsPath; // Current file path

    if (!fs.existsSync(ultimateRepoPath)) {
        vscode.window.showInformationMessage('Cloning Ultimate repository...');
        exec(`git clone https://github.com/ultimate-pa/ultimate.git ${ultimateRepoPath}`, (error, stdout, stderr) => {
            if (error) {
                vscode.window.showErrorMessage(`Error cloning Ultimate repository: ${stderr}`);
                console.error(`Error cloning Ultimate repository: ${stderr}`);
                return;
            }
            vscode.window.showInformationMessage('Ultimate repository cloned successfully.');
            buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
        });
    } else {
        buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
    }
}

function buildAndRunUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    vscode.window.showInformationMessage('Building Ultimate...');
    exec(`cd ${ultimateRepoPath}/releaseScripts/default && ./makeFresh.sh`, (error, stdout, stderr) => {
        if (error) {
            vscode.window.showErrorMessage(`Error building Ultimate: ${stderr}`);
            console.error(`Error building Ultimate: ${stderr}`);
            return;
        }
        vscode.window.showInformationMessage('Ultimate built successfully.');
        runUltimateAutomizer(ultimateRepoPath, cFilePath);
    });
}

function runUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    const specPath = path.join(ultimateRepoPath, 'releaseScripts/default/adds/props/Reach.prp');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts/legacy/svcomp2015/Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk/examples/toolchains/AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'releaseScripts/default/config/svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${cFilePath}" -s "${settingsPath}"`;

    console.log(`Running command: ${ultimateCommand}`);

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer",
        cancellable: false
    }, async (progress) => {
        progress.report({ increment: 0 });

        return new Promise<void>((resolve, reject) => {
            exec(ultimateCommand, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    reject();
                    return;
                }
                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                console.log('Ultimate Automizer Output:', stdout);
                processUltimateOutput(stdout, stderr);
                resolve();
            });

            // Simulate progress updates (you can modify or remove this as per your needs)
            let progressIncrement = 0;
            const interval = setInterval(() => {
                progressIncrement += 10;
                if (progressIncrement <= 100) {
                    progress.report({ increment: 10 });
                } else {
                    clearInterval(interval);
                }
            }, 1000);
        });
    });
}

function processUltimateOutput(stdout: string, stderr: string) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);

    vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);

    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";

    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }

    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
}
*/
/*
import * as vscode from 'vscode';
import { exec } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

export function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    const ultimateRepoPath = vscode.workspace.rootPath ? path.join(vscode.workspace.rootPath, 'ultimate') : '';
    const cFilePath = editor.document.uri.fsPath; // Current file path

    if (!fs.existsSync(ultimateRepoPath)) {
        vscode.window.showInformationMessage('Cloning Ultimate repository...');
        exec(`git clone https://github.com/ultimate-pa/ultimate.git ${ultimateRepoPath}`, (error, stdout, stderr) => {
            if (error) {
                vscode.window.showErrorMessage(`Error cloning Ultimate repository: ${stderr}`);
                console.error(`Error cloning Ultimate repository: ${stderr}`);
                return;
            }
            vscode.window.showInformationMessage('Ultimate repository cloned successfully.');
            console.log(stdout);
            buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
        });
    } else {
        buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
    }
}

function buildAndRunUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    vscode.window.showInformationMessage('Building Ultimate...');
    exec(`cd ${ultimateRepoPath}/releaseScripts/default && ./makeFresh.sh`, (error, stdout, stderr) => {
        if (error) {
            vscode.window.showErrorMessage(`Error building Ultimate: ${stderr}`);
            console.error(`Error building Ultimate: ${stderr}`);
            console.log(stdout);
            return;
        }
        vscode.window.showInformationMessage('Ultimate built successfully.');
        console.log(stdout);
        runUltimateAutomizer(ultimateRepoPath, cFilePath);
    });
}

function runUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    const specPath = path.join(ultimateRepoPath, 'releaseScripts/default/adds/props/Reach.prp');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts/legacy/svcomp2015/Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk/examples/toolchains/AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'releaseScripts/default/config/svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${cFilePath}" -s "${settingsPath}"`;

    console.log(`Running command: ${ultimateCommand}`);

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer",
        cancellable: false
    }, async (progress) => {
        progress.report({ increment: 0 });

        return new Promise<void>((resolve, reject) => {
            exec(ultimateCommand, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    console.log(stdout);
                    reject();
                    return;
                }
                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                console.log('Ultimate Automizer Output:', stdout);
                processUltimateOutput(stdout, stderr);
                resolve();
            });

            // Simulate progress updates (you can modify or remove this as per your needs)
            let progressIncrement = 0;
            const interval = setInterval(() => {
                progressIncrement += 10;
                if (progressIncrement <= 100) {
                    progress.report({ increment: 10 });
                } else {
                    clearInterval(interval);
                }
            }, 1000);
        });
    });
}

function processUltimateOutput(stdout: string, stderr: string) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);

    vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);

    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";

    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }

    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
}
*/
/*

import * as vscode from 'vscode';
import { exec, execSync } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

export function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    const ultimateRepoPath = vscode.workspace.rootPath ? path.join(vscode.workspace.rootPath, 'ultimate') : '';
    const cFilePath = editor.document.uri.fsPath; // Current file path

    if (!fs.existsSync(ultimateRepoPath)) {
        vscode.window.showInformationMessage('Cloning Ultimate repository...');
        exec(`git clone https://github.com/ultimate-pa/ultimate.git ${ultimateRepoPath}`, (error, stdout, stderr) => {
            if (error) {
                vscode.window.showErrorMessage(`Error cloning Ultimate repository: ${stderr}`);
                console.error(`Error cloning Ultimate repository: ${stderr}`);
                return;
            }
            vscode.window.showInformationMessage('Ultimate repository cloned successfully.');
            console.log(stdout);
            buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
        });
    } else {
        buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
    }
}
function buildAndRunUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    vscode.window.showInformationMessage('Building Ultimate...');

    // Find the JAVA_HOME path
    let javaHomePath: string;
    try {
        javaHomePath = execSync('/usr/libexec/java_home -v 11').toString().trim();
    } catch (error) {
        vscode.window.showErrorMessage('Failed to find JAVA_HOME. Make sure JDK 11 is installed.');
        console.error('Failed to find JAVA_HOME:', error);
        return;
    }

    const env = { ...process.env, JAVA_HOME: javaHomePath };

    exec(`cd ${ultimateRepoPath}/releaseScripts/default && ./makeFresh.sh -e -X`, { env }, (error, stdout, stderr) => {
        console.log(stdout); // Log the stdout output
        console.error(stderr); // Log the stderr output

        if (error) {
            vscode.window.showErrorMessage(`Error building Ultimate: ${stderr}`);
            console.error(`Error building Ultimate: ${stderr}`);
            return;
        }
        vscode.window.showInformationMessage('Ultimate built successfully.');
        runUltimateAutomizer(ultimateRepoPath, cFilePath, env);
    });
}


function runUltimateAutomizer(ultimateRepoPath: string, cFilePath: string, env: any) {
    const specPath = path.join(ultimateRepoPath, 'releaseScripts/default/adds/props/Reach.prp');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts/legacy/svcomp2015/Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk/examples/toolchains/AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'releaseScripts/default/config/svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${cFilePath}" -s "${settingsPath}"`;

    console.log(`Running command: ${ultimateCommand}`);

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer",
        cancellable: false
    }, async (progress) => {
        progress.report({ increment: 0 });

        return new Promise<void>((resolve, reject) => {
            exec(ultimateCommand, { env }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    console.log(stdout);
                    reject();
                    return;
                }
                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                console.log('Ultimate Automizer Output:', stdout);
                processUltimateOutput(stdout, stderr);
                resolve();
            });

            // Simulate progress updates (you can modify or remove this as per your needs)
            let progressIncrement = 0;
            const interval = setInterval(() => {
                progressIncrement += 10;
                if (progressIncrement <= 100) {
                    progress.report({ increment: 10 });
                } else {
                    clearInterval(interval);
                }
            }, 1000);
        });
    });
}

function processUltimateOutput(stdout: string, stderr: string) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);

    vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);

    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";

    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }

    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
} GOOD*/
/*
import * as vscode from 'vscode';
import { exec, execSync } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

export function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    const ultimateRepoPath = vscode.workspace.rootPath ? path.join(vscode.workspace.rootPath, 'ultimate') : '';
    const cFilePath = editor.document.uri.fsPath; // Current file path

    if (!fs.existsSync(ultimateRepoPath)) {
        vscode.window.showInformationMessage('Cloning Ultimate repository...');
        exec(`git clone https://github.com/ultimate-pa/ultimate.git ${ultimateRepoPath}`, (error, stdout, stderr) => {
            if (error) {
                vscode.window.showErrorMessage(`Error cloning Ultimate repository: ${stderr}`);
                console.error(`Error cloning Ultimate repository: ${stderr}`);
                return;
            }
            vscode.window.showInformationMessage('Ultimate repository cloned successfully.');
            console.log(stdout);
            buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
        });
    } else {
        buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
    }
}

function buildAndRunUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    vscode.window.showInformationMessage('Building Ultimate...');

    // Find the JAVA_HOME path
    let javaHomePath: string;
    try {
        javaHomePath = execSync('/usr/libexec/java_home -v 11').toString().trim();
    } catch (error) {
        vscode.window.showErrorMessage('Failed to find JAVA_HOME. Make sure JDK 11 is installed.');
        console.error('Failed to find JAVA_HOME:', error);
        return;
    }

    const env = { ...process.env, JAVA_HOME: javaHomePath };

    const buildCommand = `cd ${ultimateRepoPath}/releaseScripts/default && mvn clean install -Pmaterialize -Djava.home=${javaHomePath} -e -X`;

    exec(buildCommand, { env }, (error, stdout, stderr) => {
        // Write the logs to files
        fs.writeFileSync(path.join(ultimateRepoPath, 'build_stdout.log'), stdout);
        fs.writeFileSync(path.join(ultimateRepoPath, 'build_stderr.log'), stderr);

        console.log(stdout); // Log the stdout output
        console.error(stderr); // Log the stderr output

        if (error) {
            vscode.window.showErrorMessage(`Error building Ultimate. Check build_stderr.log for details.`);
            console.error(`Error building Ultimate: ${stderr}`);
            return;
        }
        vscode.window.showInformationMessage('Ultimate built successfully.');
        runUltimateAutomizer(ultimateRepoPath, cFilePath, env);
    });
}

function runUltimateAutomizer(ultimateRepoPath: string, cFilePath: string, env: any) {
    const specPath = path.join(ultimateRepoPath, 'releaseScripts/default/adds/props/Reach.prp');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts/legacy/svcomp2015/Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk/examples/toolchains/AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'releaseScripts/default/config/svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${cFilePath}" -s "${settingsPath}"`;

    console.log(`Running command: ${ultimateCommand}`);

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer",
        cancellable: false
    }, async (progress) => {
        progress.report({ increment: 0 });

        return new Promise<void>((resolve, reject) => {
            exec(ultimateCommand, { env }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    console.log(stdout);
                    reject();
                    return;
                }
                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                console.log('Ultimate Automizer Output:', stdout);
                processUltimateOutput(stdout, stderr);
                resolve();
            });

            // Simulate progress updates (you can modify or remove this as per your needs)
            let progressIncrement = 0;
            const interval = setInterval(() => {
                progressIncrement += 10;
                if (progressIncrement <= 100) {
                    progress.report({ increment: 10 });
                } else {
                    clearInterval(interval);
                }
            }, 1000);
        });
    });
}

function processUltimateOutput(stdout: string, stderr: string) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);

    vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);

    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";

    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }

    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
}
*/
/*
import * as vscode from 'vscode';
import { exec, execSync } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

export function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    const workspaceFolder = vscode.workspace.workspaceFolders ? vscode.workspace.workspaceFolders[0].uri.fsPath : '';
    const ultimateRepoPath = path.join(workspaceFolder, 'ultimate');
    const cFilePath = editor.document.uri.fsPath; // Current file path

    if (!fs.existsSync(ultimateRepoPath)) {
        vscode.window.showInformationMessage('Cloning Ultimate repository...');
        exec(`git clone https://github.com/ultimate-pa/ultimate.git ${ultimateRepoPath}`, (error, stdout, stderr) => {
            if (error) {
                vscode.window.showErrorMessage(`Error cloning Ultimate repository: ${stderr}`);
                console.error(`Error cloning Ultimate repository: ${stderr}`);
                return;
            }
            vscode.window.showInformationMessage('Ultimate repository cloned successfully.');
            console.log(stdout);
            buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
        });
    } else {
        buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
    }
}

function buildAndRunUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    vscode.window.showInformationMessage('Building Ultimate...');

    // Find the JAVA_HOME path
    let javaHomePath: string;
    try {
        javaHomePath = execSync('/usr/libexec/java_home -v 11').toString().trim();
    } catch (error) {
        vscode.window.showErrorMessage('Failed to find JAVA_HOME. Make sure JDK 11 is installed.');
        console.error('Failed to find JAVA_HOME:', error);
        return;
    }

    const env = { ...process.env, JAVA_HOME: javaHomePath };

    // Change the directory to trunk/source/UltimateTest
    const buildCommand = `cd ${ultimateRepoPath}/trunk/source/UltimateTest && mvn clean install -Pmaterialize -Dtycho.version=1.6.0 -Dtycho.target-platform=JavaSE-11 -e -X > build.log 2>&1`;

    exec(buildCommand, { env }, (error) => {
        // Read the logs from the file
        const buildLogPath = path.join(ultimateRepoPath, 'trunk', 'source', 'UltimateTest', 'build.log');
        const buildLog = fs.readFileSync(buildLogPath, 'utf8');

        console.log(buildLog); // Log the build output

        if (error) {
            vscode.window.showErrorMessage(`Error building Ultimate. Check build.log for details.`);
            console.error(`Error building Ultimate:`, error);
            return;
        }
        vscode.window.showInformationMessage('Ultimate built successfully.');
        runUltimateAutomizer(ultimateRepoPath, cFilePath, env);
    });
}

function runUltimateAutomizer(ultimateRepoPath: string, cFilePath: string, env: any) {
    const specPath = path.join(ultimateRepoPath, 'releaseScripts/default/adds/props/Reach.prp');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts/legacy/svcomp2015/Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk/examples/toolchains/AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'releaseScripts/default/config/svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${cFilePath}" -s "${settingsPath}"`;

    console.log(`Running command: ${ultimateCommand}`);

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer",
        cancellable: false
    }, async (progress) => {
        progress.report({ increment: 0 });

        return new Promise<void>((resolve, reject) => {
            exec(ultimateCommand, { env }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    console.log(stdout);
                    reject();
                    return;
                }
                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                console.log('Ultimate Automizer Output:', stdout);
                processUltimateOutput(stdout, stderr);
                resolve();
            });

            // Simulate progress updates (you can modify or remove this as per your needs)
            let progressIncrement = 0;
            const interval = setInterval(() => {
                progressIncrement += 10;
                if (progressIncrement <= 100) {
                    progress.report({ increment: 10 });
                } else {
                    clearInterval(interval);
                }
            }, 1000);
        });
    });
}

function processUltimateOutput(stdout: string, stderr: string) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);

    vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);

    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";

    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }

    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
}
*/
/*

import * as vscode from 'vscode';
import { exec } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

export function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders || workspaceFolders.length === 0) {
        vscode.window.showErrorMessage('Please open a workspace folder first.');
        return;
    }

    const workspacePath = workspaceFolders[0].uri.fsPath;
    const ultimateRepoPath = path.join(workspacePath, 'UltimateAtomizer');
    const cFilePath = editor.document.uri.fsPath; // Current file path

    if (!fs.existsSync(ultimateRepoPath)) {
        vscode.window.showInformationMessage('Cloning Ultimate repository...');
        exec(`git clone https://github.com/ultimate-pa/ultimate.git ${ultimateRepoPath}`, (error, stdout, stderr) => {
            if (error) {
                vscode.window.showErrorMessage(`Error cloning Ultimate repository: ${stderr}`);
                console.error(`Error cloning Ultimate repository: ${stderr}`);
                return;
            }
            vscode.window.showInformationMessage('Ultimate repository cloned successfully.');
            console.log(stdout);
            buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
        });
    } else {
        buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
    }
}

function buildAndRunUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    vscode.window.showInformationMessage('Building Ultimate...');

    const env = { ...process.env, JAVA_HOME: '/Users/stefaniapiciorea/Library/Java/JavaVirtualMachines/jdk-11.0.8.jdk/Contents/Home' }; // Replace with the actual path to the JDK
    const ultimateTestPath = path.join(ultimateRepoPath, 'trunk', 'source', 'UltimateTest');

    exec(`cd ${ultimateTestPath} && mvn clean install -Pmaterialize -Dtycho.version=1.6.0 -Dtycho.target-platform=JavaSE-11 -e -X > build.log 2>&1`, { env }, (error, stdout, stderr) => {
        if (error) {
            vscode.window.showErrorMessage('Error building Ultimate. Check the build.log for details.');
            console.error(`Error building Ultimate: ${stderr}`);
            console.log(stdout);
            const buildLogPath = path.join(ultimateTestPath, 'build.log');
            fs.readFile(buildLogPath, 'utf8', (err, data) => {
                if (err) {
                    console.error('Error reading build.log:', err);
                } else {
                    console.log('build.log contents:', data);
                }
            });
            return;
        }
        vscode.window.showInformationMessage('Ultimate built successfully.');
        runUltimateAutomizer(ultimateRepoPath, cFilePath, env);
    });
}

function runUltimateAutomizer(ultimateRepoPath: string, cFilePath: string, env: any) {
    const specPath = path.join(ultimateRepoPath, 'releaseScripts', 'default', 'adds', 'props', 'Reach.prp');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'toolchains', 'AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'releaseScripts', 'default', 'config', 'svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${cFilePath}" -s "${settingsPath}"`;

    console.log(`Running command: ${ultimateCommand}`);

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer",
        cancellable: false
    }, async (progress) => {
        progress.report({ increment: 0 });

        return new Promise<void>((resolve, reject) => {
            exec(ultimateCommand, { env }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    console.log(stdout);
                    reject();
                    return;
                }
                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                console.log('Ultimate Automizer Output:', stdout);
                processUltimateOutput(stdout, stderr);
                resolve();
            });

            // Simulate progress updates (you can modify or remove this as per your needs)
            let progressIncrement = 0;
            const interval = setInterval(() => {
                progressIncrement += 10;
                if (progressIncrement <= 100) {
                    progress.report({ increment: 10 });
                } else {
                    clearInterval(interval);
                }
            }, 1000);
        });
    });
}

function processUltimateOutput(stdout: string, stderr: string) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);

    vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);

    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";

    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }

    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
}
*/
/*
import * as vscode from 'vscode';
import { exec, execSync } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';
import { getContext } from '../utils/context';

export function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders || workspaceFolders.length === 0) {
        vscode.window.showErrorMessage('Please open a workspace folder first.');
        return;
    }

    const context = getContext();
    const ultimateRepoPath = path.join(context.extensionPath, 'UltimateAtomizer');
    const cFilePath = editor.document.uri.fsPath; // Current file path

    if (!fs.existsSync(ultimateRepoPath)) {
        vscode.window.showInformationMessage('Cloning Ultimate repository...');
        exec(`git clone https://github.com/ultimate-pa/ultimate.git ${ultimateRepoPath}`, (error, stdout, stderr) => {
            if (error) {
                vscode.window.showErrorMessage(`Error cloning Ultimate repository: ${stderr}`);
                console.error(`Error cloning Ultimate repository: ${stderr}`);
                return;
            }
            vscode.window.showInformationMessage('Ultimate repository cloned successfully.');
            console.log(stdout);
            buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
        });
    } else {
        buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
    }
}
function buildAndRunUltimateAutomizer(ultimateRepoPath: string, cFilePath: string) {
    vscode.window.showInformationMessage('Building Ultimate...');

    const javaHome = findJavaHome();
    if (!javaHome) {
        vscode.window.showErrorMessage('Could not find Java Home. Please ensure JDK is installed.');
        return;
    }

    const env = { ...process.env, JAVA_HOME: javaHome };
    const ultimateTestPath = path.join(ultimateRepoPath, 'trunk', 'source', 'UltimateTest');

    exec(`cd ${ultimateTestPath} && mvn clean install -Pmaterialize -Dtycho.version=1.6.0 -Dtycho.target-platform=JavaSE-11 -e -X > build.log 2>&1`, { env }, (error, stdout, stderr) => {
        if (error) {
            vscode.window.showErrorMessage('Error building Ultimate. Check the build.log for details.');
            console.error(`Error building Ultimate: ${stderr}`);
            console.log(stdout);
            const buildLogPath = path.join(ultimateTestPath, 'build.log');
            fs.readFile(buildLogPath, 'utf8', (err, data) => {
                if (err) {
                    console.error('Error reading build.log:', err);
                } else {
                    console.log('build.log contents:', data);
                }
            });
            return;
        }
        vscode.window.showInformationMessage('Ultimate built successfully.');
        runUltimateAutomizer(ultimateRepoPath, cFilePath, env);
    });
}

function runUltimateAutomizer(ultimateRepoPath: string, cFilePath: string, env: any) {
    const specPath = path.join(ultimateRepoPath, 'releaseScripts', 'default', 'adds', 'props', 'Reach.prp');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'toolchains', 'AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'releaseScripts', 'default', 'config', 'svcomp-Reach-64bit-Automizer_Bitvector.epf');

    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${cFilePath}" -s "${settingsPath}"`;

    console.log(`Running command: ${ultimateCommand}`);

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer",
        cancellable: false
    }, async (progress) => {
        progress.report({ increment: 0 });

        return new Promise<void>((resolve, reject) => {
            exec(ultimateCommand, { env }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    console.log(stdout);
                    reject();
                    return;
                }
                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                console.log('Ultimate Automizer Output:', stdout);
                processUltimateOutput(stdout, stderr);
                resolve();
            });

            let progressIncrement = 0;
            const interval = setInterval(() => {
                progressIncrement += 10;
                if (progressIncrement <= 100) {
                    progress.report({ increment: 10 });
                } else {
                    clearInterval(interval);
                }
            }, 1000);
        });
    });
}

function processUltimateOutput(stdout: string, stderr: string) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);

    vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);

    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";

    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }

    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
}


function findJavaHome(): string | null {
    const javaHome = process.env.JAVA_HOME;
    if (javaHome) {
        return javaHome;
    }

    if (process.platform === 'win32') {
        const possiblePaths = [
            'C:\\Program Files\\Java',
            'C:\\Program Files (x86)\\Java'
        ];

        for (const basePath of possiblePaths) {
            const paths = fs.readdirSync(basePath).map(dir => path.join(basePath, dir));
            for (const dirPath of paths) {
                if (fs.existsSync(path.join(dirPath, 'bin', 'java.exe'))) {
                    return dirPath;
                }
            }
        }
    } else {
        const result = execSync('/usr/libexec/java_home').toString().trim();
        if (result) {
            return result;
        }
    }

    return null;
}
*/
const vscode = __importStar(require("vscode"));
const child_process_1 = require("child_process");
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
function testWithUltimateAutomizer() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders || workspaceFolders.length === 0) {
        vscode.window.showErrorMessage('Please open a workspace folder first.');
        return;
    }
    const workspacePath = workspaceFolders[0].uri.fsPath;
    const ultimateRepoPath = path.join(workspacePath, 'UltimateAtomizer');
    const cFilePath = editor.document.uri.fsPath; // Current file path
    if (!fs.existsSync(ultimateRepoPath)) {
        vscode.window.showInformationMessage('Cloning Ultimate repository...');
        (0, child_process_1.exec)(`git clone https://github.com/ultimate-pa/ultimate.git ${ultimateRepoPath}`, (error, stdout, stderr) => {
            if (error) {
                vscode.window.showErrorMessage(`Error cloning Ultimate repository: ${stderr}`);
                console.error(`Error cloning Ultimate repository: ${stderr}`);
                return;
            }
            vscode.window.showInformationMessage('Ultimate repository cloned successfully.');
            //console.log(stdout);
            buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
        });
    }
    else {
        buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath);
    }
}
exports.testWithUltimateAutomizer = testWithUltimateAutomizer;
function buildAndRunUltimateAutomizer(ultimateRepoPath, cFilePath) {
    vscode.window.showInformationMessage('Building Ultimate...');
    // Find the JAVA_HOME path
    let javaHomePath;
    try {
        javaHomePath = (0, child_process_1.execSync)('/usr/libexec/java_home -v 11').toString().trim();
    }
    catch (error) {
        vscode.window.showErrorMessage('Failed to find JAVA_HOME. Make sure JDK 11 is installed.');
        console.error('Failed to find JAVA_HOME:', error);
        return;
    }
    const env = { ...process.env, JAVA_HOME: javaHomePath };
    const ultimateTestPath = path.join(ultimateRepoPath, 'trunk', 'source', 'UltimateTest');
    const debugLogPath = path.join(ultimateTestPath, 'debug.log');
    (0, child_process_1.exec)(`cd ${ultimateTestPath} && mvn clean install -Pmaterialize -Dtycho.version=1.6.0 -Dtycho.target-platform=JavaSE-11 -Dorg.osgi.framework.executionenvironment=JavaSE-11 -e -X > debug.log 2>&1`, { env }, (error, stdout, stderr) => {
        if (error) {
            vscode.window.showErrorMessage('Error building Ultimate. Check the debug.log for details.');
            console.error(`Error building Ultimate: ${stderr}`);
            console.log(stdout);
            // Check if debug.log exists and print its contents
            if (fs.existsSync(debugLogPath)) {
                readDebugLogFile(debugLogPath);
            }
            else {
                console.error('debug.log file not found.');
            }
            return;
        }
        vscode.window.showInformationMessage('Ultimate built successfully.');
        runUltimateAutomizer(ultimateRepoPath, cFilePath, env);
    });
}
function readDebugLogFile(logFilePath) {
    fs.readFile(logFilePath, 'utf8', (err, data) => {
        if (err) {
            console.error('Error reading debug.log:', err);
        }
        else {
            console.log('debug.log contents:', data);
        }
    });
}
function runUltimateAutomizer(ultimateRepoPath, cFilePath, env) {
    const specPath = path.join(ultimateRepoPath, 'releaseScripts', 'default', 'adds', 'props', 'Reach.prp');
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const toolchainPath = path.join(ultimateRepoPath, 'trunk', 'examples', 'toolchains', 'AutomizerC.xml');
    const settingsPath = path.join(ultimateRepoPath, 'releaseScripts', 'default', 'config', 'svcomp-Reach-64bit-Automizer_Bitvector.epf');
    const ultimateCommand = `python3 "${ultimatePath}" -tc "${toolchainPath}" -i "${cFilePath}" -s "${settingsPath}"`;
    console.log(`Running command: ${ultimateCommand}`);
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running Ultimate Automizer",
        cancellable: false
    }, async (progress) => {
        progress.report({ increment: 0 });
        return new Promise((resolve, reject) => {
            (0, child_process_1.exec)(ultimateCommand, { env }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
                    console.error(`Error running Ultimate Automizer: ${stderr}`);
                    console.log(stdout);
                    reject();
                    return;
                }
                vscode.window.showInformationMessage('Ultimate Automizer command executed successfully.');
                console.log('Ultimate Automizer Output:', stdout);
                processUltimateOutput(stdout, stderr);
                resolve();
            });
            let progressIncrement = 0;
            const interval = setInterval(() => {
                progressIncrement += 10;
                if (progressIncrement <= 100) {
                    progress.report({ increment: 10 });
                }
                else {
                    clearInterval(interval);
                }
            }, 1000);
        });
    });
}
/*function runUltimateAutomizer(filePath: string, method: string = 'automizer', context: vscode.ExtensionContext) {
    const ultimateRepoPath = context.globalStorageUri.fsPath + '/UltimateAutomizer';
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
}*/
function processUltimateOutput(stdout, stderr) {
    console.log('Ultimate Automizer Output:', stdout);
    console.error('Ultimate Automizer Error Output:', stderr);
    vscode.window.showInformationMessage(`Ultimate Automizer Output: ${stdout}`);
    vscode.window.showErrorMessage(`Ultimate Automizer Error Output: ${stderr}`);
    const lines = stdout.split('\n');
    let verificationResult = "Unknown";
    let counterexample = "";
    for (const line of lines) {
        if (line.includes("Verification Result")) {
            verificationResult = line;
        }
        if (line.includes("Counterexample")) {
            counterexample += line + '\n';
        }
    }
    vscode.window.showInformationMessage(`Ultimate Automizer Result: ${verificationResult}`);
    if (counterexample) {
        vscode.window.showErrorMessage(`Counterexample found:\n${counterexample}`);
    }
}
//# sourceMappingURL=testAssertionsWithUltimateAutomizer.js.map