"use strict";
/*import * as https from 'https';

export function makeHttpsRequest(options: https.RequestOptions, postData?: string): Promise<string> {
    return new Promise((resolve, reject) => {
        const req = https.request(options, (res) => {
            let data = '';

            res.on('data', (chunk) => {
                data += chunk;
            });

            res.on('end', () => {
                resolve(data);
            });
        });

        req.on('error', (e) => {
            reject(e);
        });

        if (postData) {
            req.write(postData);
        }

        req.end();
    });
}
*/
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
exports.unifiedHttpsRequest = void 0;
const http = __importStar(require("http"));
const https = __importStar(require("https"));
const querystring = __importStar(require("querystring"));
function unifiedHttpsRequest(urlOptions, data = '') {
    return new Promise((resolve, reject) => {
        const httpModule = urlOptions.protocol === 'http:' ? http : https;
        const req = httpModule.request(urlOptions, (res) => {
            const chunks = [];
            res.on('data', (chunk) => chunks.push(chunk));
            res.on('error', reject);
            res.on('end', () => {
                const { statusCode, headers } = res;
                const validResponse = statusCode !== undefined && statusCode >= 200 && statusCode <= 299;
                const body = Buffer.concat(chunks).toString();
                if (validResponse) {
                    resolve({ statusCode, headers, body });
                }
                else {
                    reject(new Error(`Request failed. status: ${statusCode}, body: ${body}`));
                }
            });
        });
        req.on('error', reject);
        req.write(querystring.stringify({ data }), 'binary');
        req.end();
    });
}
exports.unifiedHttpsRequest = unifiedHttpsRequest;
//# sourceMappingURL=httpsRequest.js.map