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
exports.deactivate = exports.activate = void 0;
const vscode = __importStar(require("vscode"));
const insertAssertions_1 = require("./commands/insertAssertions");
const testAssertions_1 = require("./commands/testAssertions");
const insertCustomAssertions_1 = require("./commands/insertCustomAssertions");
const docker_utils_1 = require("./utils/docker_utils");
const docker_utils_2 = require("./utils/docker_utils");
const context_1 = require("./utils/context");
async function activate(context) {
    // Check if the Docker image exists locally; build it if it does not.
    // TODO: If an updated image exists, the current image will be replaced with the updated one.
    const imageName = 'dig';
    // The target directory for cloning. This is the global storage path provided by VS Code.
    // This directory is meant to store data that doesn't need to be accessed by other applications 
    // or by the user directly. Since the user doesn't need to interact with dig's source code directly,
    // this is a god place to clone.
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
        let disposable = vscode.commands.registerCommand('vscode-dig.insertAssertions', insertAssertions_1.insertAssertions);
        context.subscriptions.push(disposable);
        let disposableTestAssertions = vscode.commands.registerCommand('vscode-dig.testAssertions', testAssertions_1.testAssertions);
        context.subscriptions.push(disposableTestAssertions);
        let disposableCustomAssertions = vscode.commands.registerCommand('vscode-dig.insertCustomAssertions', insertCustomAssertions_1.insertCustomAssertions);
        context.subscriptions.push(disposableCustomAssertions);
    }
    catch (error) {
        vscode.window.showErrorMessage(`Error setting up DIG: ${error.message}`);
    }
    ;
}
exports.activate = activate;
function deactivate() { }
exports.deactivate = deactivate;
//# sourceMappingURL=extension.js.map