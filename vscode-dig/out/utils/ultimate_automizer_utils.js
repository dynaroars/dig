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
exports.cloneUltimateRepo = void 0;
const child_process_1 = require("child_process");
const context_1 = require("./context");
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
async function cloneUltimateRepo() {
    const context = (0, context_1.getContext)();
    const targetDirectory = path.join(context.globalStorageUri.fsPath, 'UltimateAtomizer');
    console.log(`Target directory for Ultimate Atomizer repository: ${targetDirectory}`);
    // Check if the directory already exists
    if (fs.existsSync(targetDirectory)) {
        console.log(`Directory already exists: ${targetDirectory}`);
        return;
    }
    return new Promise((resolve, reject) => {
        const command = `git clone --depth 1 https://github.com/ultimate-pa/ultimate.git "${targetDirectory}"`;
        console.log(`Running command: ${command}`);
        (0, child_process_1.exec)(command, (error, stdout, stderr) => {
            if (error) {
                console.error(`Error cloning Ultimate Atomizer repository: ${error.message}`);
                console.error(stderr);
                reject(error);
                return;
            }
            console.log(`Successfully cloned Ultimate Atomizer repository to ${targetDirectory}`);
            resolve();
        });
    });
}
exports.cloneUltimateRepo = cloneUltimateRepo;
///Users/stefaniapiciorea/Library/Application Support/Code/User/globalStorage/undefined_publisher.vscode-dig/UltimateAtomizer/releaseScripts/default/adds/Ultimate.py
//const ultimateScriptPath = path.join(context.globalStorageUri.fsPath, 'UltimateAtomizer/releaseScripts/default/adds/Ultimate.py');
//# sourceMappingURL=ultimate_automizer_utils.js.map