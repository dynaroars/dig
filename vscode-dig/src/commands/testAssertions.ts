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

    // Use the currentLine as the assertion to be tested
    const userAssertion = currentLine;

    // Get the current file path
    const filePath = editor.document.uri.fsPath;

    // Get the directory of the currently open file
    const fileDirectory = path.dirname(editor.document.uri.fsPath);


    // Define the output files for the conversio
    const symexefile = path.join(path.dirname(filePath), 'symexefile.c');
    const tracefile = path.join(path.dirname(filePath), 'tracefile.c');

    // Conversion output file (DEBUGGING)
    const outputFile = path.join(fileDirectory, 'conversionOutput.txt');

    // Construct the command to run the conversion script
    const conversionCommand = `python3  /Users/stefaniapiciorea/Documents/Github/dig/src/c_instrument.py ${filePath} ${symexefile} ${tracefile} > ${outputFile}`;

    // Execute the conversion script
    exec(conversionCommand, (error: Error, stdout: string, stderr: string) => {
        if (error || stderr) {
            console.error(`Conversion Error: ${error ? error.message : stderr}`);
            vscode.window.showErrorMessage('Error running the conversion script.');
            return;
        }

        

        // stdout will contain the types output from the instrument function
        console.log(`Conversion Output: ${stdout}`);


// Run CIVL with default maxDepth of 10
const civlCommand = `civl verify -maxdepth=10 ${symexefile}`;


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
