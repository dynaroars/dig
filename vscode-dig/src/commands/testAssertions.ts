const vscode = require('vscode');
const { exec } = require('child_process');
const path = require('path');

export async function testAssertions() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to test assertions.');
        return;
    }

    // Get the current line of code where the cursor is located
    const currentPosition = editor.selection.active;
    const currentLine = editor.document.lineAt(currentPosition.line).text;

    if (!currentLine.includes('assert')) {
        vscode.window.showInformationMessage('No assertion on the current line.');
        return;
    }

    // Prompt the user to input the max depth
    const maxDepth = await vscode.window.showInputBox({
        prompt: 'Enter the max depth for CIVL verification:',
        placeHolder: 'e.g., 10',
    });

    if (!maxDepth) {
        vscode.window.showInformationMessage('CIVL verification cancelled.');
        return;
    }

    // Use the currentLine as the assertion to be tested
    const userAssertion = currentLine;

    // Get the current file path
    const filePath = editor.document.uri.fsPath;

    // Define the output files for the conversion
    const symexefile = path.join(path.dirname(filePath), 'symexefile.c');
    const tracefile = path.join(path.dirname(filePath), 'tracefile.c');

    // Construct the command to run the conversion script
    const conversionCommand = `python3  /Users/stefaniapiciorea/Documents/Github/dig/src/c_instrument.py ${filePath} ${symexefile} ${tracefile}`;

    // Execute the conversion script
    exec(conversionCommand, (error: Error, stdout: string, stderr: string) => {
        if (error || stderr) {
            console.error(`Conversion Error: ${error ? error.message : stderr}`);
            vscode.window.showErrorMessage('Error running the conversion script.');
            return;
        }

        // stdout will contain the types output from the instrument function
        console.log(`Conversion Output: ${stdout}`);

       // Construct the command to run CIVL with the user-specified max depth
const civlJarPath = '/opt/homebrew/Cellar/civl/1.22-5854/libexec/civl-1.22_5854.jar'; // Adjust this path as needed
const civlCommand = `civl verify -maxdepth=${maxDepth} ${symexefile}`;

// Get the directory of the currently open file
const fileDirectory = path.dirname(editor.document.uri.fsPath);

// Set up the execution options with the correct current working directory
const execOptions = {
    cwd: fileDirectory,
  };

// Execute CIVL
exec(civlCommand, execOptions, (civlError: Error, civlStdout: string, civlStderr: string) => {
    if (civlError || civlStderr) {
        console.error(`CIVL Error: ${civlError ? civlError.message : civlStderr}`);
        vscode.window.showErrorMessage('Error running CIVL.');
        return;
    }

    // Process and display the results from CIVL
    console.log(`CIVL Output: ${civlStdout}`);
    vscode.window.showInformationMessage(`CIVL Verification Result: ${civlStdout}`);
});
    });
}
