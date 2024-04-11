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
exports.instrumentCode = void 0;
/*import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';

export async function instrumentCode() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to transform to CIVL.');
        return;
    }

    const document = editor.document;
    const documentText = document.getText();

    // Split the document text into lines
    let lines = documentText.split(/\r?\n/);

     // Determine the last include index
     let lastIncludeIndex = lines.map((line, index) => ({ line, index }))
     .filter(obj => obj.line.startsWith("#include"))
     .map(obj => obj.index)
     .pop();

// Default index to -1 if no includes found
lastIncludeIndex = (lastIncludeIndex === undefined) ? -1 : lastIncludeIndex;

// Prepare the includes, checking if they already exist
let civlcInclude = lines.find(line => line.includes('"civlc.cvh"')) ? '' : '#include "civlc.cvh"\n';
let assertInclude = lines.find(line => line.includes('<assert.h>')) ? '' : '#include <assert.h>\n';

// Add the CIVL and assert includes after the last existing include
lines.splice(lastIncludeIndex + 1, 0, civlcInclude + assertInclude);

// Remove empty lines that might be added due to splice operation
lines = lines.filter(line => line.trim() !== '');


    let transformedCode = documentText;
    const filePath = editor.document.uri.fsPath;
    const fileDirectory = path.dirname(filePath);



    // Rule 1: Headers
    transformedCode = '#include "civlc.cvh"\n#include <assert.h>\n' + transformedCode;

    // Rule 2: $input directives
    const mainQRegex = /void\s+mainQ\((.*?)\)/;
    const mainQMatch = mainQRegex.exec(transformedCode);
    if (mainQMatch) {
        const params = mainQMatch[1].split(',').map(param => param.trim());
        const inputDirectives = params.map(param => {
            const [type, name] = param.split(/\s+/);
            return `$input ${type} ${name};`;
        }).join('\n');
        transformedCode = inputDirectives + '\n' + transformedCode;
    }

    // Rule 3: Remove all vassume function declarations
    transformedCode = transformedCode.replace(/void\s+vassume\(.*?\);/g, '');

        // Rule 4: Convert all vtrace declarations
        transformedCode = transformedCode.replace(/void\s+vtrace(\d+)\((.*?)\)\s*{/g, (match: string, num: string, params: string) => {
            const paramNames = params.split(',').map(param => {
                const parts = param.trim().split(/\s+/);
                return parts.length === 2 ? parts[1] : param; // Ensure that we have both type and name
            });
            const printfParams = paramNames.join(', ');
            return `void vtrace${num}(${params}) {\n  printf("vtrace${num}: ${paramNames.map(name => `${name} = %d`).join('; ')}\\n", ${printfParams});\n  $pathCondition();\n}`;
        });

    // Rule 5: Keep mainQ header as is
    // No action needed as the header is unchanged

    // Rule 6: Convert all vassume calls
    transformedCode = transformedCode.replace(/vassume\((.*?)\);/g, (match, condition) => {
        return `$assume(${condition});`;
    });

    // Rule 7: Convert mainQ(atoi(argv[1]), atoi(argv[2]));
    transformedCode = transformedCode.replace(/mainQ\(atoi\(argv\[1]\)\),\s*atoi\(argv\[2]\)\);/g, 'mainQ(x, y);');


    let transformedCode = lines.join('\n');
    
    // Write transformed code to a new temp file
    const tempFilePath = path.join(fileDirectory, 'temp_' + path.basename(document.uri.fsPath));
    fs.writeFileSync(tempFilePath, transformedCode, 'utf8');

    // Notify user
    vscode.window.showInformationMessage('The code has been transformed and saved to a temporary file.');
}

// Call this function when the corresponding command is triggered
*/
/*
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';

export async function instrumentCode() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to transform to CIVL.');
        return;
    }

    const document = editor.document;
    const documentText = document.getText();

    // Split the document text into lines
    let lines = documentText.split(/\r?\n/);

    // Rule 1: Headers (ensuring they are only included once)
    const headerIncludes = ['<civlc.cvh>', '<assert.h>'];
    headerIncludes.forEach(header => {
        if (!lines.some(line => line.includes(header))) {
            lines.unshift(`#include ${header}`);
        }
    });
    

    // Determine the last include index
    const lastIncludeIndex = lines.findIndex(line => line.match(/#include/));
    let addCivlcInclude = !lines.some(line => line.includes('<civlc.cvh>'));
    let addAssertInclude = !lines.some(line => line.includes('<assert.h>'));

    // Prepare the includes, checking if they already exist
    let includesToAdd = [];
    if (addCivlcInclude) {includesToAdd.push('#include "civlc.cvh"');}
    if (addAssertInclude) {includesToAdd.push('#include <assert.h>');}

    // Add the CIVL and assert includes after the last existing include if not already present
    if (lastIncludeIndex >= 0 && includesToAdd.length > 0) {
        lines.splice(lastIncludeIndex + 1, 0, ...includesToAdd, "");
    } else if (includesToAdd.length > 0) {
        lines.unshift(...includesToAdd, "");
    }

     // Rule 2: $input directives
     const mainQRegex = /void\s+mainQ\((.*?)\)/;
     const mainQMatch = mainQRegex.exec(documentText);
     if (mainQMatch) {
         const params = mainQMatch[1].split(',').map(param => param.trim());
         const inputDirectives = params.map(param => {
             const [type, name] = param.split(/\s+/);
             return `$input ${type} ${name};`;
         }).join('\n');
         // Find the index immediately after the last #include
         //const lastIncludeIndex = lines.map((line, index) => line.startsWith('#include') ? index : -1).reduce((acc, val) => Math.max(acc, val), 0);
         lines.splice(lastIncludeIndex + 1, 0, inputDirectives);
     }

    // Join the lines back into a single string for further processing
    let transformedCode = lines.join('\n');

    // The rest of your transformation rules go here, applied to transformedCode
    // ...


    // Apply other transformation rules to transformedCode
    // ...

    // Write the fully transformed code to a new temp file
    const fileDirectory = path.dirname(document.uri.fsPath);
    const tempFilePath = path.join(fileDirectory, 'temp_' + path.basename(document.uri.fsPath));
    fs.writeFileSync(tempFilePath, transformedCode, 'utf8');

    // Notify user
    vscode.window.showInformationMessage('The code has been transformed and saved to a temporary file.');
}

// Call this function when the corresponding command is triggered
*/
/*
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';

export async function instrumentCode() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to transform to CIVL.');
        return;
    }

    const document = editor.document;
    const documentText = document.getText();

    // Split the document text into lines
    let lines = documentText.split(/\r?\n/);

    let includesAdded = false;

    // Find all include lines
    let includeLines = lines.filter(line => line.startsWith('#include'));

    // Check for existing includes
    let civlcIncluded = includeLines.some(line => line.includes('"civlc.cvh"'));
    let assertIncluded = includeLines.some(line => line.includes('<assert.h>'));

     // Add includes if not present
     if (!civlcIncluded) {
        lines.unshift('#include "civlc.cvh"');
        includesAdded = true;
    }
    if (!assertIncluded) {
        lines.unshift('#include <assert.h>');
        includesAdded = true;
    }

    // Find the mainQ function and extract its arguments for $input directives
    let inputLines = '';
    let mainQRegex = /void\s+mainQ\((int\s+\w+\s*,\s*int\s+\w+)\)/;
    let mainQMatch = mainQRegex.exec(documentText);
    if (mainQMatch) {
        inputLines = mainQMatch[1].split(',')
            .map(param => {
                const [type, name] = param.trim().split(/\s+/);
                return `$input ${type} ${name};`;
            })
            .join('\n');
    }
    console.log(`Input lines: ${inputLines}`);


    // Insert the $input lines after the last #include directive
    if (inputLines) {
        let lastIncludeIndex = lines.findIndex(line => line.startsWith('#include'));
        console.log(`Last Include Index: ${lastIncludeIndex}`);
        if (lastIncludeIndex !== -1) {
            // Adding 1 to insert after the last include
            lines.splice(lastIncludeIndex + 1, 0, inputLines);
        }
    }

    // Join the lines back into a single string for further processing
    let transformedCode = lines.join('\n');
    console.log(`Transformed Code:\n${transformedCode}`);

    // Rest of your transformation rules...
    // Make sure to apply them on `transformedCode`

    // Write the transformed code to a temp file
    const fileDirectory = path.dirname(document.uri.fsPath);
    const tempFilePath = path.join(fileDirectory, 'temp_' + path.basename(document.uri.fsPath));
    fs.writeFileSync(tempFilePath, transformedCode, 'utf8');

    vscode.window.showInformationMessage('The code has been transformed and saved to a temporary file.');
}*/
const vscode = __importStar(require("vscode"));
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
async function instrumentCode() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('Open a file to transform to CIVL.');
        return;
    }
    const document = editor.document;
    const documentText = document.getText();
    // Identify the part of the document where $input lines should be added
    // This assumes that mainQ definition is not the first thing in the file
    const mainQDefinitionRegex = /void\s+mainQ\(\s*([^)]*)\s*\)/;
    const match = mainQDefinitionRegex.exec(documentText);
    if (!match || match.index === undefined) {
        vscode.window.showErrorMessage('mainQ function not found.');
        return;
    }
    // Extract parameters from the mainQ function
    const paramsString = match[1];
    const params = paramsString.split(',').map(param => param.trim());
    const inputDirectives = params.map(param => {
        const [type, name] = param.split(/\s+/);
        return `$input ${type} ${name};`;
    }).join('\n');
    // Insert $input lines at the top of the document or after the last #include
    let insertPosition = 0; // Default to start of document
    const lastIncludeMatch = documentText.substring(0, match.index).lastIndexOf('#include');
    if (lastIncludeMatch !== -1) {
        // If there are #include lines, insert after the last one
        insertPosition = documentText.indexOf('\n', lastIncludeMatch) + 1;
    }
    const updatedDocumentText = [
        documentText.slice(0, insertPosition),
        inputDirectives,
        '\n\n',
        documentText.slice(insertPosition)
    ].join('');
    // Write the transformed code to a temp file
    const fileDirectory = path.dirname(document.uri.fsPath);
    const tempFilePath = path.join(fileDirectory, 'temp_' + path.basename(document.uri.fsPath));
    fs.writeFileSync(tempFilePath, updatedDocumentText, 'utf8');
    vscode.window.showInformationMessage('The code has been transformed and saved to a temporary file.');
}
exports.instrumentCode = instrumentCode;
//# sourceMappingURL=instrumentCode.js.map