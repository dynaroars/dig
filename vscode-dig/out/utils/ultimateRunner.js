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
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.runUltimateAutomizer = void 0;
const child_process_1 = require("child_process");
const vscode = __importStar(require("vscode"));
const path_1 = __importDefault(require("path"));
function runUltimateAutomizer(ultimateRepoPath, cFilePath, context) {
    const ultimatePath = path_1.default.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const javaHome = vscode.workspace.getConfiguration().get('ultimate.javaHome') || '';
    const env = {
        JAVA_HOME: javaHome,
        PATH: process.env.PATH
    };
    const ultimateCommand = `python3 "${ultimatePath}" -tc "${ultimateRepoPath}/trunk/examples/toolchains/AutomizerC.xml" -i "${cFilePath}" -s "${ultimateRepoPath}/trunk/examples/settings/svcomp2018/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf"`;
    (0, child_process_1.exec)(ultimateCommand, { env }, (error, stdout, stderr) => {
        if (error) {
            console.error(`Error running Ultimate Automizer: ${stderr}`);
            vscode.window.showErrorMessage(`Error running Ultimate Automizer: ${stderr}`);
            return;
        }
        console.log(`Ultimate Automizer Output:\n${stdout}`);
        vscode.window.showInformationMessage(`Ultimate Automizer executed successfully.`);
    });
}
exports.runUltimateAutomizer = runUltimateAutomizer;
//# sourceMappingURL=ultimateRunner.js.map