
import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { exec } from 'child_process';
import { getContext } from '../utils/context';

interface CivlResult {
    file: string;
    violation: boolean;
    output: string;
    error: string | null;
}

/**
 * Tests assertions by creating temporary files, each containing only one assertion. Each temporary file is then converted
 * to a CIVL-compatible format and run through CIVL. The results are stored in a JSON file. When the user calls this command,
 * the selected assertion/s are tested. If there are any failed assertions, the user is prompted to remove them. All the valid
 * assertions are updated with a comment to indicate that they passed.
 */

export async function testAssertions() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    const document = editor.document;
    const text = document.getText();
    const assertionRegex = /assert\(.*\);/g;
    const matches = text.match(assertionRegex);

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

    const fileDirectory = path.dirname(editor.document.uri.fsPath); //The directory of the file being edited
    const context = getContext(); //The context of the extension
    const globalStoragePath = context.globalStorageUri.fsPath; //The global storage path of the extension
    const civlUtilsScriptPath = vscode.Uri.joinPath(context.extensionUri, 'src', 'utils', 'civl_utils.py').fsPath;
    const instrumentScriptPath = path.join(globalStoragePath, 'dig', 'src', 'c_instrument.py'); //The path to the CIVL instrument script
    const symexefileBase = path.join(fileDirectory, 'symexefile'); //The base path for the temporary files
    
    const failedAssertions: string[] = [];
    const passedAssertions: { line: number; text: string }[] = [];

    /**
     * Runs the conversion script and CIVL on a given file.
     */

    const runConversionAndCivl = (tempFilePath: string, index: number): Promise<CivlResult> => {
        return new Promise((resolve, reject) => {
            const convertedFilePath = `${symexefileBase}_converted_${index}.c`; //The path to the converted file
            const traceFilePath = `${symexefileBase}_trace_${index}.c`; //The path to the trace file
            const conversionCommand = `python3 "${instrumentScriptPath}" "${tempFilePath}" "${convertedFilePath}" "${traceFilePath}"`;

            //console.log(`Running conversion command: ${conversionCommand}`);

            exec(conversionCommand, (conversionError, conversionStdout, conversionStderr) => {
                if (conversionError) {
                    console.error(`Conversion Error: ${conversionError.message}`);
                    reject(`Error running the conversion script: ${conversionError.message}`);
                    return;
                }
                if (conversionStderr) {
                    console.error(`Conversion Stderr: ${conversionStderr}`);
                }

                //console.log(`Converted file created: ${convertedFilePath}`);
                if (fs.existsSync(convertedFilePath)) {
                    console.log(`Converted file exists: ${convertedFilePath}`);
                } else {
                    console.error(`Converted file does not exist: ${convertedFilePath}`);
                    reject('Converted file does not exist.');
                    return;
                }

                const civlCommand = `python3 "${civlUtilsScriptPath}" "${tempFilePath}" "${convertedFilePath}" --max_depth=10`;
                //console.log(`Running CIVL command: ${civlCommand}`);

                const execOptions = {
                    cwd: fileDirectory,
                    env: {
                        ...process.env,
                        CIVL_HOME: path.join(globalStoragePath, 'dig', 'EXTERNAL_FILES', 'CIVL-1.22_5854'),
                        PATH: process.env.PATH + path.delimiter + path.join(globalStoragePath, 'dig', 'EXTERNAL_FILES', 'CIVL-1.22_5854', 'bin')
                    }
                };


                exec(civlCommand, execOptions, (civlError, civlStdout, civlStderr) => {
                    if (civlError) {
                        console.error(`CIVL Error: ${civlError.message}`);
                        reject(`Error running CIVL: ${civlError.message}`);
                        return;
                    }
                    if (civlStderr) {
                        console.error(`CIVL Stderr: ${civlStderr}`);
                    }

                    let result: CivlResult;
                    try {
                        const output = JSON.parse(civlStdout);
                        result = {
                            file: tempFilePath,
                            violation: output.output.includes("Violation 0 encountered"),
                            output: output.output,
                            error: output.error,
                        };
                    } catch (parseError: any) {
                        reject(`Parse Error: ${parseError.message}`);
                        return;
                    }

                    // Cleans up the temporary files
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
        const resultsFilePath = path.join(fileDirectory, 'civl_results.json'); //The path to the results file
        
        const results: CivlResult[] = [];
        const newTextLines = text.split('\n');

        // Runs the conversion script and civl command on each temporary file created
        for (let i = 0; i < assertionsToTest.length; i++) {
            const tempFilePath = `${symexefileBase}_assert_${i}.c`; // The path to the temporary file
            const tempFileContent = createTempFileContent(text, assertionsToTest[i]); // The content of the temporary file
            
            fs.writeFileSync(tempFilePath, tempFileContent);
            //console.log(`Temporary file created at: ${tempFilePath}`);

            const result = await runConversionAndCivl(tempFilePath, i);
            results.push(result);

            const startPos = document.positionAt(text.indexOf(assertionsToTest[i]));

            // If the assertion failed, add it to the failedAssertions array. Otherwise, add a "valid" comment to the assertion
            if (result.violation) {
                failedAssertions.push(`Line ${startPos.line + 1}: ${assertionsToTest[i]}`);
                //console.log(`Diagnostic added for assertion at line ${startPos.line}`);
            } else {
                const lineIndex = startPos.line;
                if (!newTextLines[lineIndex].includes('// valid')) {
                    newTextLines[lineIndex] = `${newTextLines[lineIndex]} // valid`;
                }
                passedAssertions.push({ line: lineIndex, text: assertionsToTest[i] });
            }
        }

        fs.writeFileSync(resultsFilePath, JSON.stringify(results, null, 2));
        //console.log(`Results saved to ${resultsFilePath}`);

        const newTextWithValidComments = newTextLines.join('\n');
        
        let edit = new vscode.WorkspaceEdit();
        let fullRange = new vscode.Range(
            new vscode.Position(0, 0),
            new vscode.Position(document.lineCount - 1, document.lineAt(document.lineCount - 1).text.length)
        );
        edit.replace(editor.document.uri, fullRange, newTextWithValidComments);
        await vscode.workspace.applyEdit(edit);

        // If there are any failed assertions dislpay a message to the user and ask if they wish to remove them
        if (failedAssertions.length > 0) {
            const message = `The following assertions failed:\n\n${failedAssertions.join('\n')}\n\nWould you like to remove them?`;
            const removeButton = 'Remove';
            const result = await vscode.window.showInformationMessage(message, removeButton);

            if (result === removeButton) {
                const newTextAfterRemoval = newTextLines
                    .filter((line, index) => !failedAssertions.some(failedAssertion => failedAssertion.includes(`Line ${index + 1}`)))
                    .join('\n');
                edit = new vscode.WorkspaceEdit();
                fullRange = new vscode.Range(
                    new vscode.Position(0, 0),
                    new vscode.Position(document.lineCount - 1, document.lineAt(document.lineCount - 1).text.length)
                );
                edit.replace(editor.document.uri, fullRange, newTextAfterRemoval);
                await vscode.workspace.applyEdit(edit);
            }
        }

        // Remove the civl_results.json file
        if (fs.existsSync(resultsFilePath)) {
            fs.unlinkSync(resultsFilePath);
            //console.log(`Deleted file: ${resultsFilePath}`);
        }

    } catch (error: any) {
        console.error('Error:', error);
        vscode.window.showErrorMessage(`Error: ${error.message}`);
    }
}

/**
 * Creates the cintent for a temporary file containing only one assertion.
 */
function createTempFileContent(originalContent: string, assertion: string): string {
    const lines = originalContent.split('\n');
    const filteredLines = lines.map(line => {
        if (line.includes('assert') && !line.includes(assertion) && !line.trim().startsWith('#include')) {
            return '';
        }
        return line;
    });
    return filteredLines.join('\n');
}

