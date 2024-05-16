import * as vscode from 'vscode';

// Context for the extension
let extensionContext: vscode.ExtensionContext;

// Set the context for the extension
export function setContext(context: vscode.ExtensionContext) {
    extensionContext = context;
}

// Get the context for the extension
export function getContext(): vscode.ExtensionContext {
    return extensionContext;
}
