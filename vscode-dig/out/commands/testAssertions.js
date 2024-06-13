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
    // Get all the assertions in the file
    const document = editor.document;
    const text = document.getText();
    const assertionRegex = /assert\(.*\);/g;
    const matches = text.match(assertionRegex);
    // If there are no assertions, show a message and return
    if (!matches || matches.length === 0) {
        vscode.window.showInformationMessage('No assertions found to test.');
        return;
    }
    // If there are assertions, get the selected assertions or all the assertions if none are selected
    const selection = editor.selection;
    const selectedAssertions = matches.filter((match, index) => {
        const matchStartPos = document.positionAt(text.indexOf(match));
        const matchEndPos = matchStartPos.translate(0, match.length);
        return selection.intersection(new vscode.Range(matchStartPos, matchEndPos)) !== undefined;
    });
    const assertionsToTest = selectedAssertions.length > 0 ? selectedAssertions : matches;
    const fileDirectory = path.dirname(editor.document.uri.fsPath); // The directory of the file being tested
    const context = (0, context_1.getContext)(); // Get the context of the extension
    const globalStoragePath = context.globalStorageUri.fsPath; // The global storage path of the extension
    const civlUtilsScriptPath = vscode.Uri.joinPath(context.extensionUri, 'src', 'utils', 'civl_utils.py').fsPath;
    const instrumentScriptPath = path.join(globalStoragePath, 'src', 'c_instrument.py'); // The path to the C instrument script
    const symexefileBase = path.join(fileDirectory, 'symexefile'); // The base path for the temporary files
    const failedAssertions = []; // A list of failed assertions
    const passedAssertions = []; // A list of passed assertions
    /**
     * Runs the conversion script and CIVL on a given file.
     */
    const runConversionAndCivl = (tempFilePath, index) => {
        return new Promise((resolve, reject) => {
            const convertedFilePath = `${symexefileBase}_converted_${index}.c`; // The path to the converted file
            const traceFilePath = `${symexefileBase}_trace_${index}.c`; // The path to the trace file
            // The command to run the conversion script
            const conversionCommand = `python3 "${instrumentScriptPath}" "${tempFilePath}" "${convertedFilePath}" "${traceFilePath}"`;
            console.log(`Running conversion command: ${conversionCommand}`);
            // Runs the conversion script
            (0, child_process_1.exec)(conversionCommand, (conversionError, conversionStdout, conversionStderr) => {
                if (conversionError) {
                    console.error(`Conversion Error: ${conversionError.message}`);
                    reject(`Error running the conversion script: ${conversionError.message}`);
                    return;
                }
                if (conversionStderr) {
                    console.error(`Conversion Stderr: ${conversionStderr}`);
                }
                console.log(`Converted file created: ${convertedFilePath}`);
                if (fs.existsSync(convertedFilePath)) {
                    console.log(`Converted file exists: ${convertedFilePath}`);
                }
                else {
                    console.error(`Converted file does not exist: ${convertedFilePath}`);
                    reject('Converted file does not exist.');
                    return;
                }
                // The command to run CIVL
                const civlCommand = `python3 "${civlUtilsScriptPath}" "${tempFilePath}" "${convertedFilePath}" --max_depth=10`;
                console.log(`Running CIVL command: ${civlCommand}`);
                const execOptions = {
                    cwd: fileDirectory,
                };
                // Runs CIVL
                (0, child_process_1.exec)(civlCommand, execOptions, (civlError, civlStdout, civlStderr) => {
                    if (civlError) {
                        console.error(`CIVL Error: ${civlError.message}`);
                        reject(`Error running CIVL: ${civlError.message}`);
                        return;
                    }
                    if (civlStderr) {
                        console.error(`CIVL Stderr: ${civlStderr}`);
                    }
                    // Parses the output of CIVL
                    let result;
                    try {
                        const output = JSON.parse(civlStdout);
                        result = {
                            file: tempFilePath,
                            // If the output contains "Violation 0 encountered", the assertion failed
                            violation: output.output.includes("Violation 0 encountered"),
                            output: output.output,
                            error: output.error,
                        };
                    }
                    catch (parseError) {
                        reject(`Parse Error: ${parseError.message}`);
                        return;
                    }
                    // Cleans up temporary files
                    [tempFilePath, convertedFilePath, traceFilePath].forEach(file => {
                        if (fs.existsSync(file)) {
                            fs.unlinkSync(file);
                            console.log(`Deleted file: ${file}`);
                        }
                    });
                    resolve(result);
                });
            });
        });
    };
    try {
        const resultsFilePath = path.join(fileDirectory, 'civl_results.json'); // The path to the json file storing CIVLs output
        const results = []; // A list of results for each assertion
        const newTextLines = text.split('\n');
        // Loop that runs the conversion and CIVL for each temp file created
        for (let i = 0; i < assertionsToTest.length; i++) {
            const tempFilePath = `${symexefileBase}_assert_${i}.c`; // The path to the temporary file
            const tempFileContent = createTempFileContent(text, assertionsToTest[i]); // The content of the temporary file
            fs.writeFileSync(tempFilePath, tempFileContent);
            console.log(`Temporary file created at: ${tempFilePath}`);
            const result = await runConversionAndCivl(tempFilePath, i); // Run the conversion and CIVL scripts on the temp file
            results.push(result);
            // Get the position of the assertion in the document
            const startPos = document.positionAt(text.indexOf(assertionsToTest[i]));
            // If the assertion failed, add it to the failed assertions list. Else add it to the passed assertions list and update the document to display a valid comment next to it
            if (result.violation) {
                failedAssertions.push(`Line ${startPos.line + 1}: ${assertionsToTest[i]}`);
                console.log(`Diagnostic added for assertion at line ${startPos.line}`);
            }
            else {
                const lineIndex = startPos.line;
                if (!newTextLines[lineIndex].includes('// valid')) {
                    newTextLines[lineIndex] = `${newTextLines[lineIndex]} // valid`;
                }
                passedAssertions.push({ line: lineIndex, text: assertionsToTest[i] });
            }
        }
        // Save the results to a JSON file
        fs.writeFileSync(resultsFilePath, JSON.stringify(results, null, 2));
        console.log(`Results saved to ${resultsFilePath}`);
        const newTextWithValidComments = newTextLines.join('\n');
        let edit = new vscode.WorkspaceEdit();
        let fullRange = new vscode.Range(new vscode.Position(0, 0), new vscode.Position(document.lineCount - 1, document.lineAt(document.lineCount - 1).text.length));
        edit.replace(editor.document.uri, fullRange, newTextWithValidComments);
        await vscode.workspace.applyEdit(edit);
        // If there are failed assertions, display a message to the user and ask if they want to remove them
        if (failedAssertions.length > 0) {
            const message = `The following assertions failed:\n\n${failedAssertions.join('\n')}\n\nWould you like to remove them?`;
            const removeButton = 'Remove';
            const result = await vscode.window.showInformationMessage(message, removeButton);
            if (result === removeButton) {
                const newTextAfterRemoval = newTextLines
                    .filter((line, index) => !failedAssertions.some(failedAssertion => failedAssertion.includes(`Line ${index + 1}`)))
                    .join('\n');
                edit = new vscode.WorkspaceEdit();
                fullRange = new vscode.Range(new vscode.Position(0, 0), new vscode.Position(document.lineCount - 1, document.lineAt(document.lineCount - 1).text.length));
                edit.replace(editor.document.uri, fullRange, newTextAfterRemoval);
                await vscode.workspace.applyEdit(edit);
            }
        }
        // Remove the civl_results.json file
        if (fs.existsSync(resultsFilePath)) {
            fs.unlinkSync(resultsFilePath);
            console.log(`Deleted file: ${resultsFilePath}`);
        }
    }
    catch (error) {
        console.error('Error:', error);
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
//# sourceMappingURL=testAssertions.js.map