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
exports.testAssertions = void 0;
const vscode = __importStar(require("vscode"));
const path = __importStar(require("path"));
const fs = __importStar(require("fs"));
const child_process_1 = require("child_process");
const context_1 = require("../utils/context");
/**
 * Tests assertions by creating temporary files, each containing only one assertion. Each temporary file is then converted
 * to a CIVL-compatible format and run through CIVL. The results are stored in a JSON file. When the user calls this command,
 * the selected assertion/s are tested. If there are any failed assertions, the user is prompted to remove them. All the valid
 * assertions are updated with a comment to indicate that they passed.
 */
async function testAssertions() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }
    const document = editor.document;
    const text = document.getText();
    //console.log("Document text length:", text.length);
    const assertionRegex = /assert\s*\(.*?\);/g;
    const matches = text.match(assertionRegex);
    //console.log("Matched assertions:", matches);
    if (!matches || matches.length === 0) {
        vscode.window.showInformationMessage('No assertions found to test.');
        return;
    }
    const selection = editor.selection;
    const selectedAssertions = matches.filter((match, index) => {
        const matchStartPos = document.positionAt(text.indexOf(match));
        const matchEndPos = matchStartPos.translate(0, match.length);
        return selection.intersection(new vscode.Range(matchStartPos, matchEndPos)) !== undefined;
    });
    const assertionsToTest = selectedAssertions.length > 0 ? selectedAssertions : matches;
    //console.log("Assertions to test:", assertionsToTest);
    const fileDirectory = path.dirname(editor.document.uri.fsPath);
    const context = (0, context_1.getContext)();
    const globalStoragePath = context.globalStorageUri.fsPath;
    const civlUtilsScriptPath = vscode.Uri.joinPath(context.extensionUri, 'src', 'utils', 'civl_utils.py').fsPath;
    const civlJarPath = path.join(globalStoragePath, "dig", "EXTERNAL_FILES", "CIVL-1.22_5854", "lib", "civl-1.22_5854.jar");
    const instrumentScriptPath = path.join(globalStoragePath, 'dig', 'src', 'c_instrument.py');
    const symexefileBase = path.join(fileDirectory, 'symexefile');
    const failedAssertions = [];
    const passedAssertions = [];
    const runConversionAndCivl = (tempFilePath, index) => {
        return new Promise((resolve, reject) => {
            const convertedFilePath = `${symexefileBase}_converted_${index}.c`;
            const traceFilePath = `${symexefileBase}_trace_${index}.c`;
            const conversionCommand = `python3 "${instrumentScriptPath}" "${tempFilePath}" "${convertedFilePath}" "${traceFilePath}"`;
            //console.log("Running conversion:", conversionCommand);
            (0, child_process_1.exec)(conversionCommand, (conversionError, conversionStdout, conversionStderr) => {
                if (conversionError) {
                    console.error(`Conversion Error: ${conversionError.message}`);
                    reject(`Error running the conversion script: ${conversionError.message}`);
                    return;
                }
                if (!fs.existsSync(convertedFilePath)) {
                    console.error(`Converted file does not exist: ${convertedFilePath}`);
                    reject('Converted file does not exist.');
                    return;
                }
                const civlCommand = `python3 "${civlUtilsScriptPath}" "${tempFilePath}" "${convertedFilePath}" --max_depth=10 --civl_jar="${civlJarPath}"`;
                const execOptions = {
                    cwd: fileDirectory,
                    env: {
                        ...process.env,
                        CIVL_HOME: path.join(globalStoragePath, 'dig', 'EXTERNAL_FILES', 'CIVL-1.22_5854'),
                        PATH: process.env.PATH + path.delimiter + path.join(globalStoragePath, 'dig', 'EXTERNAL_FILES', 'CIVL-1.22_5854', 'bin')
                    }
                };
                //console.log("Running CIVL command:", civlCommand);
                (0, child_process_1.exec)(civlCommand, execOptions, (civlError, civlStdout, civlStderr) => {
                    //console.log("CIVL STDOUT:", civlStdout);
                    //console.log("CIVL STDERR:", civlStderr);
                    if (civlError) {
                        console.error(`CIVL Error: ${civlError.message}`);
                        reject(`Error running CIVL: ${civlError.message}`);
                        return;
                    }
                    if (civlStderr) {
                        console.error(`CIVL Stderr: ${civlStderr}`);
                    }
                    let result;
                    try {
                        const output = JSON.parse(civlStdout);
                        result = {
                            file: tempFilePath,
                            violation: output.output.includes("Violation 0 encountered"),
                            output: output.output,
                            error: output.error,
                        };
                    }
                    catch (parseError) {
                        reject(`Parse Error: ${parseError.message}`);
                        return;
                    }
                    // Cleans up the temporary files
                    [tempFilePath, convertedFilePath, traceFilePath].forEach(file => {
                        if (fs.existsSync(file)) {
                            fs.unlinkSync(file);
                            //console.log(`Deleted file: ${file}`);
                        }
                    });
                    resolve(result);
                });
            });
        });
    };
    try {
        const resultsFilePath = path.join(fileDirectory, 'civl_results.json');
        const results = [];
        const newTextLines = text.split('\n');
        await ensureBeartypeInstalled();
        for (let i = 0; i < assertionsToTest.length; i++) {
            const tempFilePath = `${symexefileBase}_assert_${i}.c`;
            const tempFileContent = createTempFileContent(text, assertionsToTest[i]);
            fs.writeFileSync(tempFilePath, tempFileContent);
            //console.log("Created temp file:", tempFilePath);
            const result = await runConversionAndCivl(tempFilePath, i);
            results.push(result);
            const matchIndex = text.indexOf(assertionsToTest[i]);
            if (matchIndex === -1) {
                console.warn("Assertion not found in text:", assertionsToTest[i]);
                continue;
            }
            const startPos = document.positionAt(text.indexOf(assertionsToTest[i]));
            // If the assertion failed, add it to the failedAssertions array. Otherwise, add a "valid" comment to the assertion
            if (result.violation) {
                failedAssertions.push(`Line ${startPos.line + 1}: ${assertionsToTest[i]}`);
                //console.log(`Diagnostic added for assertion at line ${startPos.line}`);
            }
            else {
                const lineIndex = startPos.line;
                if (!newTextLines[lineIndex].includes('// valid')) {
                    newTextLines[lineIndex] = `${newTextLines[lineIndex]} // valid`;
                }
                passedAssertions.push({ line: lineIndex, text: assertionsToTest[i] });
            }
        }
        fs.writeFileSync(resultsFilePath, JSON.stringify(results, null, 2));
        //console.log("Wrote results to:", resultsFilePath);
        const newTextWithValidComments = newTextLines.join('\n');
        let edit = new vscode.WorkspaceEdit();
        let fullRange = new vscode.Range(new vscode.Position(0, 0), new vscode.Position(document.lineCount - 1, document.lineAt(document.lineCount - 1).text.length));
        edit.replace(editor.document.uri, fullRange, newTextWithValidComments);
        await vscode.workspace.applyEdit(edit);
        if (failedAssertions.length > 0) {
            const message = `The following assertions failed:\n\n${failedAssertions.join('\n')}\n\nWould you like to remove them?`;
            const removeButton = 'Remove';
            const result = await vscode.window.showInformationMessage(message, removeButton);
            if (result === removeButton) {
                const newTextAfterRemoval = newTextLines
                    .filter((line, index) => !failedAssertions.some(failed => failed.includes(`Line ${index + 1}`)))
                    .join('\n');
                edit = new vscode.WorkspaceEdit();
                edit.replace(editor.document.uri, fullRange, newTextAfterRemoval);
                await vscode.workspace.applyEdit(edit);
            }
        }
        if (fs.existsSync(resultsFilePath)) {
            fs.unlinkSync(resultsFilePath);
            //console.log("Deleted results file:", resultsFilePath);
        }
    }
    catch (error) {
        console.error("Top-level error:", error);
        vscode.window.showErrorMessage(`Error: ${error.message}`);
    }
}
exports.testAssertions = testAssertions;
/**
 * Creates the content for a temporary file containing only one assertion.
 */
function createTempFileContent(originalContent, assertion) {
    const lines = originalContent.split('\n');
    const filteredLines = lines.map(line => {
        if (line.includes('assert') && !line.includes(assertion) && !line.trim().startsWith('#include')) {
            return '';
        }
        return line;
    });
    return filteredLines.join('\n');
}
function ensureBeartypeInstalled() {
    return new Promise((resolve, reject) => {
        (0, child_process_1.exec)('python3 -c "import beartype"', (error) => {
            if (!error)
                return resolve();
            vscode.window.showErrorMessage('Python module "beartype" is not installed. It is required for DIG to work.', 'Install Now').then(selection => {
                if (selection === 'Install Now') {
                    vscode.window.withProgress({
                        location: vscode.ProgressLocation.Notification,
                        title: 'Installing Python module: beartype',
                        cancellable: false
                    }, () => {
                        return new Promise((resolveProgress, rejectProgress) => {
                            (0, child_process_1.exec)('pip3 install beartype', (installError, stdout, stderr) => {
                                if (installError) {
                                    vscode.window.showErrorMessage(`Failed to install beartype: ${stderr}`);
                                    return rejectProgress(installError);
                                }
                                resolveProgress();
                            });
                        });
                    }).then(resolve, reject);
                }
                else {
                    reject(new Error('User declined beartype installation.'));
                }
            });
        });
    });
}
//# sourceMappingURL=testAssertions.js.map