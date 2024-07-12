

import * as vscode from 'vscode';
import { exec } from 'child_process';
import { getAssertionsForLatestVtrace } from '../utils/dig_utils';
import * as path from 'path';

/**
 * Interface for command flags.
 * 
 * label: The flag as it appears in the command.
 * detail: Description of the flag for the user.
 * requiresArgument: Whether the flag requires an additional argument.
 */

interface Flag {
    label: string;
    detail: string;
    requiresArgument: boolean;
}

// Flags that can be used with the DIG command.
const flags: Flag[] = [
    { label: '--seed', detail: 'Specify seed for random number generator', requiresArgument: true },
    { label: '--maxdeg', detail: 'Specify maximum degree of polynomials', requiresArgument: true },
    { label: '--maxterm', detail: 'Specify maximum number of terms in invariants', requiresArgument: true },
    { label: '--nrandinps', detail: 'Specify number of random inputs to explore', requiresArgument: true },
    { label: '--inpMaxV', detail: 'Specify the maximum input value', requiresArgument: true},
    { label: '--se_mindepth', detail: 'Specify the minimum depth for symbolic execution', requiresArgument: true},
    { label: '--se_maxdepth', detail: 'Specify the maximum depth for symbolic execution', requiresArgument: true},
    { label: '--iupper', detail: 'Specify the maximum upper bound value for inequality analysis', requiresArgument: true},
    { label: '--ideg', detail: 'Specify the degree for inequalities (1 = linear, 2 = quadratic, etc.)', requiresArgument: true},
    { label: '--iterms', detail: 'Specify the number of terms in inequalities (2 = octogonal)', requiresArgument: true},
    { label: '--icoefs', detail: 'Specify the coefficients for inequalities (1 => coeffs are in [-1, 0, 1]', requiresArgument: true},
    { label: '--noss', detail: 'Disable state space exploration', requiresArgument: false },
    { label: '--noeqts', detail: 'Disable generation of equations', requiresArgument: false },
    { label: '--noieqs', detail: 'Disable generation of inequalities', requiresArgument: false },
    { label: '--nocongruences', detail: 'Disable the computation of congruence invariants', requiresArgument: false},
    { label: '--noarrays', detail: 'Disables the computation of relations among array elements', requiresArgument: false},
    { label: '--nominmaxplus', detail: 'Disables the computation of min/max-plus invariants', requiresArgument: false},
    { label: '--nopreposts', detail: 'Disables the computation of pre/post specifications', requiresArgument: false},
    { label: '--noincrdepth', detail: 'Disables incremental depth analysis', requiresArgument: false},
    { label: '--nofilter', detail: 'Disables fitering of inequality terms', requiresArgument: false},
    { label: '--nosimplify', detail: 'Disable simplification of generated invariants', requiresArgument: false },
    { label: '--nomp', detail: 'Disables multiprocessing', requiresArgument: false}
];

/**
 * Triggers a QuickPick UI to allow the user to select custom DIG command flags.
 */
export function insertCustomAssertions() {
    const editor = vscode.window.activeTextEditor!;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to insert assertions.');
        return;
    }

    // Create and configure QuickPick for flag selection.
    const quickPick = vscode.window.createQuickPick<Flag>();
    quickPick.items = flags;
    quickPick.canSelectMany = true;
    quickPick.title = 'Select Additional Flags';
    quickPick.placeholder = 'Select additional flags to customize DIG command';

    quickPick.onDidAccept(() => {
        handleFlagSelection(quickPick, editor);
    });

    quickPick.show();
}

/**
 * Handles the selection of flags from the QuickPick UI.
 * 
 * @param quickPick The QuickPick instance.
 * @param editor The active text editor.
 */
function handleFlagSelection(quickPick: vscode.QuickPick<Flag>, editor: vscode.TextEditor) {
    const selectedFlags = quickPick.selectedItems;
    if (selectedFlags.length === 0) {
        quickPick.dispose();
        return;
    }

    const argumentsMap = new Map<string, string>(); // Stores selected flags and their arguments.

    // Process each selected flag in sequence.
    processNextFlag(selectedFlags, argumentsMap, 0, () => {
        const additionalFlags = Array.from(argumentsMap.entries())
            .map(([label, argument]) => argument ? `${label} ${argument}` : label)
            .join(' ');
        const command = getCommand(editor.document.uri.fsPath, additionalFlags);
        execCommand(command, editor);
        quickPick.dispose();
    });
}

/**
 * Recursively processes each flag, asking for an argument if needed.
 * 
 * @param flags Array of selected flags.
 * @param argumentsMap Map storing flag arguments.
 * @param index Current index in the flags array.
 * @param callback Function to call after processing all flags.
 */
function processNextFlag(flags: readonly Flag[], argumentsMap: Map<string, string>, index: number, callback: () => void) {
    // Base case: all flags have been processed.
    if (index >= flags.length) {
        callback();
        return;
    }

    const flag = flags[index];
    if (flag.requiresArgument) {
        vscode.window.showInputBox({ prompt: `Enter argument for ${flag.label}` }).then(argument => {
            if (argument !== undefined) {
                argumentsMap.set(flag.label, argument);
            }
            processNextFlag(flags, argumentsMap, index + 1, callback);
        });
    } else {
        argumentsMap.set(flag.label, '');
        processNextFlag(flags, argumentsMap, index + 1, callback);
    }
}

/**
 * Constructs the command to execute DIG with the selected flags.
 * 
 * @param filePath The path to the current file in the editor.
 * @param additionalFlags Flags selected by the user.
 * @returns The constructed command.
 */
function getCommand(filePath: string, additionalFlags: string): string {
    const filename = path.basename(filePath);
    return `docker run --platform linux/amd64 -v "${filePath}:/dig/src/${filename}" -w /dig/src dig /bin/bash -c "/root/miniconda3/bin/python3 -O dig.py ${filename} -log 2 ${additionalFlags}"`;
}

/**
 * Handles errors from the DIG command execution.
 * 
 * @param error The error object.
 * @param stderr The standard error output.
 */
function handleDigError(error: Error, stderr: string) {
    vscode.window.showErrorMessage(`Error running DIG: ${stderr}`);
    console.error(`Execution Error: ${error}`);
}

/**
 * Processes standard error output from DIG.
 * 
 * @param stderr The standard error output.
 */
function processStdErr(stderr: string) {
    if (stderr.trim()) {
        console.error(`STDERR: ${stderr}`);
    }
}

/**
 * Processes standard output from DIG and inserts generated assertions.
 * 
 * @param stdout The standard output containing the invariants.
 * @param editor The active text editor.
 */
function processStdOut(stdout: string, editor: vscode.TextEditor) {
    if (!stdout.trim()) {
        vscode.window.showInformationMessage('No invariants generated by DIG.');
        return;
    }

    const lines = stdout.split('\n');
    const invariantLines = lines.filter(line => line.match(/^\d+\./));
    const currentLine = editor.document.lineAt(editor.selection.active.line);
    const currentLineIndentation = currentLine.text.substring(0, currentLine.firstNonWhitespaceCharacterIndex);
    /*const assertions = invariantLines.map(line => {
        const invariant = line.substring(line.indexOf(' ') + 1);
        return `${currentLineIndentation}assert(${invariant});`;
    }).join('\n');*/
    const initialPosition = editor.selection.active;
    const textUpToPosition = editor.document.getText(new vscode.Range(new vscode.Position(0,0), initialPosition));
    const formattedAssertions = getAssertionsForLatestVtrace(stdout, textUpToPosition, currentLineIndentation);
    const insertPosition = new vscode.Position(initialPosition.line + 1, 0);

    if (!formattedAssertions) {
        vscode.window.showInformationMessage('No invariants generated by DIG.');
        return;
    }

    /*editor.edit(editBuilder => {
        editBuilder.insert(initialPosition, `\n\n${assertions}\n`);
    });*/

    editor.edit(editBuilder => {
        //editBuilder.insert(initialPosition, `\n\n${assertions}\n`);
        editBuilder.insert(insertPosition, `\n${currentLineIndentation}${formattedAssertions}\n`);
    }); // Ensure the progress notification is closed
}
/**
 * Executes the constructed DIG command and handles the output.
 * 
 * @param command The command to execute.
 * @param editor The active text editor.
 */
function execCommand(command: string, editor: vscode.TextEditor) {
    console.log("Running command:", command);
  
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Running DIG...",
        cancellable: false
    }, async (progress) => {
        return new Promise<void>((resolve) => {
            exec(command, (error, stdout, stderr) => {
                console.log(`STDOUT: ${stdout}`);
                if (error) {
                    handleDigError(error, stderr);
                    // Resolve the promise to stop the process bar
                    resolve(); 
                    return;
                }

                processStdErr(stderr);
                processStdOut(stdout, editor);
                // Resolve the promise
                resolve(); 
            });
        });
    });
}


