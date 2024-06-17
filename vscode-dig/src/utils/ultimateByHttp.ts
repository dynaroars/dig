/*import { exec } from 'child_process';
import * as vscode from 'vscode';

export function runUltimateByHttp(filePath: string, context: vscode.ExtensionContext) {
    const ultimateRepoPath = context.globalStorageUri.fsPath;
    const ultimatePath = path.join(ultimateRepoPath, 'UltimateAtomizer', 'releaseScripts', 'http', 'Ultimate.py');
    const ultimateCommand = `python3 "${ultimatePath}" -i "${filePath}"`;

    exec(ultimateCommand, (error, stdout, stderr) => {
        if (error) {
            console.error(`Error running Ultimate By Http: ${stderr}`);
            return;
        }
        console.log(`Ultimate By Http Output:\n${stdout}`);
    });
}*/

/*good 2
import * as vscode from 'vscode';
import { exec } from 'child_process';
import * as path from 'path';

export function runUltimateByHttp(filePath: string) {
    const ultimateRepoPath = vscode.workspace.getConfiguration().get<string>('ultimate.repoPath') || '';
    const ultimatePath = path.join(ultimateRepoPath, 'releaseScripts', 'legacy', 'svcomp2015', 'Ultimate.py');
    const ultimateCommand = `python3 "${ultimatePath}" "${filePath}"`;

    exec(ultimateCommand, (error, stdout, stderr) => {
        if (error) {
            console.error(`Error running Ultimate by Http: ${stderr}`);
            return;
        }
        console.log(`Ultimate by Http Output:\n${stdout}`);
    });
}*/

import * as vscode from 'vscode';
import * as fs from 'fs';
import { UltimateBase } from './ultimateBase';
import { unifiedHttpsRequest } from './httpsRequest';
import * as querystring from 'querystring';

export class UltimateByHttp extends UltimateBase {
    private requestId: string = '';
    public refreshTimeInMilliseconds: number = 500;
    private apiUrl: URL;
    declare error: any;
    declare results: any;
    declare outputChannel: any;
    log: any;
    convertSeverity: any;
    declare settingsFilePath: any;
    declare toolchainFilePath: any;

    constructor(context: vscode.ExtensionContext, settings: vscode.Uri, toolchain: vscode.Uri, apiUrl: string) {
        super(context);
        this.apiUrl = new URL(apiUrl);
        this.setSettingsFile(settings);
        this.setToolchainFile(toolchain);
    }

    runOn(input: vscode.TextDocument | string, language: string = 'c') {
        let code = '';
        let fileExtension = language;
        let document: vscode.TextDocument | undefined;

        if (this.isDocument(input) && (input.languageId === 'c' || input.languageId === 'boogie')) {
            document = input;
            code = document.getText();
            fileExtension = vscode.window.activeTextEditor?.document.uri.fsPath.split('.').pop() ?? language;
        } else if (typeof input === 'string') {
            code = input;
        }

        if (!this.isLocked()) {
            this.lockUltimate();
            this.outputChannel.clear();
            this.showProgressInStatusBar('Fetching Ultimate results...');
            this.fetchResults(code.trim(), fileExtension)
                .then((response) => this.parseResponse(response))
                .then(() => this.pollResults())
                .then(() => this.outputChannel.show())
                .then(() => this.printResultsToOutput())
                .then(() => this.printResultsToLog())
                .then(() => {
                    if (document) this.embedDiagnosticInfoInto(document);
                })
                .then(() => this.stopShowingProgressInStatusBar())
                .then(() => this.freeUltimate())
                .catch((error) => {
                    console.log(error);
                    this.stopShowingProgressInStatusBar();
                    this.freeUltimate();
                });
        }
    }

    fetchResults(code: string, fileExtension: string): Promise<any> {
        const body = {
            action: 'execute',
            code: code,
            toolchain: JSON.stringify({
                id: 'cAutomizer',
            }),
            code_file_extension: '.' + fileExtension,
            user_settings: this.getSettingsFromFile(),
            ultimate_toolchain_xml: this.getToolchainFromFile(),
        };
    
        const defaultPort = this.apiUrl.protocol === 'http:' ? 80 : 443;
        const options = {
            protocol: this.apiUrl.protocol,
            hostname: this.apiUrl.hostname,
            port: parseInt(this.apiUrl.port) || defaultPort,
            path: this.apiUrl.pathname,
            method: 'POST',
            headers: {
                'Content-Type': 'application/x-www-form-urlencoded;charset=UTF-8',
                'Connection': 'keep-alive',
            },
        };
    
        return unifiedHttpsRequest(options, querystring.stringify(body));
    }
    
    getToolchainFromFile(): string {
        let toolchain = `<rundefinition>
                            <name>CAutomizerTC</name>
                            <toolchain>
                            <plugin id="de.uni_freiburg.informatik.ultimate.plugins.analysis.syntaxchecker"/>
                            <plugin id="de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator"/>
                            <plugin id="de.uni_freiburg.informatik.ultimate.boogie.preprocessor"/>
                            <plugin id="de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder"/>
                            <plugin id="de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction"/>
                            </toolchain>
                        </rundefinition>`;

        if (fs.existsSync(this.toolchainFilePath.fsPath) &&
            fs.lstatSync(this.settingsFilePath.fsPath).isFile()) {
            toolchain = fs.readFileSync(this.toolchainFilePath.fsPath, 'utf8');
        }

        return toolchain;
    }

    getSettingsFromFile(): string {
        let settings = '';
        if (fs.existsSync(this.settingsFilePath.fsPath) &&
            fs.lstatSync(this.settingsFilePath.fsPath).isFile()) {
            settings = fs.readFileSync(this.settingsFilePath.fsPath, 'utf8');
        }

        return settings;
    }

    parseResponse(httpResponse: any) {
        const response = JSON.parse(httpResponse.body);
        this.results = response.results ? response.results : [];
        this.requestId = response.requestId;
        this.error = response.error;
    }

    delay(ms: number): Promise<void> {
        return new Promise((resolve) => setTimeout(resolve, ms));
    }

    pollResults(): Promise<void> {
        const defaultPort = this.apiUrl.protocol === 'http:' ? 80 : 443;
        const options = {
            protocol: this.apiUrl.protocol,
            hostname: this.apiUrl.hostname,
            port: parseInt(this.apiUrl.port) || defaultPort,
            path: `${this.apiUrl.pathname}/job/get/${this.requestId}`,
            method: 'GET',
            headers: {
                Accept: '*/*',
                Connection: 'keep-alive',
            },
        };

        return unifiedHttpsRequest(options).then((httpResponse) => {
            const response = JSON.parse(httpResponse.body);
            switch (response.status.toLowerCase()) {
                case 'done':
                    this.results = response.results;
                    return Promise.resolve(response);
                case 'error':
                    return Promise.reject(response.error);
                default:
                    return this.delay(this.refreshTimeInMilliseconds).then(() => this.pollResults());
            }
        });
    }

    printResultsToOutput() {
        if (this.error) {
            this.outputChannel.appendLine(this.error);
        }
        this.results.forEach((result: { logLvl: any; shortDesc: any; longDesc: any; }) => {
            this.outputChannel.appendLine(`${result.logLvl}: ${result.shortDesc}`);
            this.outputChannel.appendLine(`${result.longDesc}`);
            this.outputChannel.appendLine('');
        });
    }

    printResultsToLog() {
        if (this.error) {
            this.log(this.error, vscode.DiagnosticSeverity.Error);
        }
        this.results.forEach((result: { shortDesc: any; longDesc: any; logLvl: any; }) => {
            const message = `${result.shortDesc}: ${result.longDesc}`;
            const severity = this.convertSeverity(result.logLvl);
            this.log(message, severity);
        });
    }

    prepareDiagnosticInfo(document: vscode.TextDocument): vscode.Diagnostic[] {
        const diagnostics: vscode.Diagnostic[] = [];
        this.results.forEach((result: { longDesc: string; shortDesc: any; logLvl: any; }) => {
            if (this.resultIsWorthEmbedding(result)) {
                const relatedInformation: vscode.DiagnosticRelatedInformation[] = [];
                const reasonInformation = RegExp(/Reason: (\D*)(\d*)(.*)\n/).exec(result.longDesc);
                if (reasonInformation) {
                    const relatedLine = Number(reasonInformation[2]);
                    const relatedInfoRange = document.lineAt(relatedLine - 1).range;
                    const relatedInfoLocation = new vscode.Location(document.uri, relatedInfoRange);
                    relatedInformation.push(new vscode.DiagnosticRelatedInformation(relatedInfoLocation, result.longDesc));
                }
                diagnostics.push({
                    code: '',
                    message: result.shortDesc,
                    range: this.getResultRange(result, document),
                    severity: this.convertSeverity(result.logLvl),
                    source: 'Ultimate Automizer',
                    relatedInformation: relatedInformation,
                });
            }
        });
        return diagnostics;
    }

    getResultRange(result: any, document: vscode.TextDocument): vscode.Range {
        const startLNr = result.startLNr > 0 ? result.startLNr - 1 : 0;
        const endLNr = result.endLNr > 0 ? result.endLNr - 1 : 0;
        let assertFinding: RegExpExecArray | null = null;
        let startCol = 0;
        let endCol = 0;
        if (startLNr > 0) {
            assertFinding = RegExp(/assert(.*);/).exec(document.lineAt(startLNr).text);
        }
        if (result.startCol >= 0 && result.endCol >= 0) {
            startCol = result.startCol;
            endCol = result.endCol;
        } else if (assertFinding) {
            startCol = assertFinding.index;
            endCol = startCol + assertFinding[0].length;
        }
        return new vscode.Range(startLNr, startCol, endLNr, endCol);
    }

    resultIsWorthEmbedding(result: any): boolean {
        return !(result.type === 'invariant' || result.type === 'syntaxError');
    }
}


