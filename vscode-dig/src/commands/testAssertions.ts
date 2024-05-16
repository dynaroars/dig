import vscode from 'vscode';
import { ExecException, exec } from 'child_process';
import path from 'path';
import { getContext } from '../utils/context';

export async function testAssertions() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

     // Check if there is a multiline selection
     const selection = editor.selection;
     let linesToTest = [];
     
     if (!selection.isEmpty) {
         // User has selected multiple lines
         for (let i = selection.start.line; i <= selection.end.line; i++) {
             let lineText = editor.document.lineAt(i).text;
             if (lineText.includes('assert')) {
                 linesToTest.push(lineText);
             }
         }
     } else {
         // Single line where the cursor is located
         const currentLineText = editor.document.lineAt(selection.active.line).text;
         if (currentLineText.includes('assert')) {
             linesToTest.push(currentLineText);
         }
     }
 
     // No assertions found in the selection
     if (linesToTest.length === 0) {
         vscode.window.showInformationMessage('No assertions found to test.');
         return;
     }

    // Get the current file path
    const filePath = editor.document.uri.fsPath;

    // Get the directory of the currently open file
    const fileDirectory = path.dirname(editor.document.uri.fsPath);


    // Define the output files for the conversio
    const symexefile = path.join(path.dirname(filePath), 'symexefile.c');
    const tracefile = path.join(path.dirname(filePath), 'tracefile.c');

    // Conversion output file (DEBUGGING)
    const outputFile = path.join(fileDirectory, 'conversionOutput.txt');
    
    // Get the path to the cloned repository from the context
    const context = getContext();
    const globalStoragePath = context.globalStorageUri.fsPath;
    
    // Construct the path to the instrument.py script inside the cloned repository
    const instrumentScriptPath = path.join(globalStoragePath, 'src', 'c_instrument.py');

    // Construct the command to run the conversion script that converts C code into CIVL readable code
    const conversionCommand = `python3 "${instrumentScriptPath}" "${filePath}" "${symexefile}" "${tracefile}" > "${outputFile}"`;

    // Execute the conversion script
    exec(conversionCommand, (error: Error | null, stdout: string, stderr: string) => {
        if (error || stderr) {
            console.error(`Conversion Error: ${error ? error.message : stderr}`);
            vscode.window.showErrorMessage('Error running the conversion script.');
            return;
        }

// Construct the command to run CIVL
const maxDepth = '10';
const extensionPath = context.extensionPath;
const civlUtilsScriptPath = path.join(extensionPath, 'src', 'utils', 'civl_utils.py');
const civlCommand = `python3 "${civlUtilsScriptPath}" "${filePath}" "${symexefile}" --max_depth=${maxDepth}`;

// DEBUGGING. Logs the paths to c_instrument.py and civl_utils.py
console.log(`Instrument Script Path: ${instrumentScriptPath}`);
console.log(`CIVL Utils Script Path: ${civlUtilsScriptPath}`);

// Set up the execution options with the current working directory
const execOptions = {
    cwd: fileDirectory,
  };

// Execute teh CIVL command
exec(civlCommand, execOptions, (civlError: ExecException | null, civlStdout: string, civlStderr: string) => {
    if (civlError || civlStderr) {
        console.error(`CIVL Error: ${civlError ? civlError.message : civlStderr}`);
        vscode.window.showErrorMessage('Error running CIVL.');
        return;
    }
    
// Parses the CIVL output and displays a message to the user based on whether a violation message was found in CIVL's output or not
try {
    const result = JSON.parse(civlStdout);
    if (result.error) {
        vscode.window.showErrorMessage(`CIVL Error: ${result.error}`);
    } else {
        const civlOutput = result.output;
        if (civlOutput.includes("Violation")) {
            vscode.window.showErrorMessage('Assertion failed. The selected assertion is not valid.');
        } else {
            vscode.window.showInformationMessage('Assertion passed. The selected assertion is valid.');
        }
    }
} catch (parseError: any){
    console.error(`Parse Error: ${parseError.message}`);
    vscode.window.showErrorMessage('Error parsing CIVL output.');
}
    
});
    });

}



