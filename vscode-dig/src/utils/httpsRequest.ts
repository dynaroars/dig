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

import * as http from 'http';
import * as https from 'https';
import * as querystring from 'querystring';

interface UrlOptions {
    protocol: string;
    hostname: string;
    port?: number;
    path: string;
    method: string;
    headers?: http.OutgoingHttpHeaders;
}

interface HttpsResponse {
    statusCode: number;
    headers: http.IncomingHttpHeaders;
    body: string;
}

export function unifiedHttpsRequest(urlOptions: UrlOptions, data: string = ''): Promise<HttpsResponse> {
    return new Promise((resolve, reject) => {
        const httpModule = urlOptions.protocol === 'http:' ? http : https;
        const req = httpModule.request(urlOptions, (res) => {
            const chunks: Uint8Array[] = [];
            res.on('data', (chunk) => chunks.push(chunk));
            res.on('error', reject);
            res.on('end', () => {
                const { statusCode, headers } = res;
                const validResponse = statusCode !== undefined && statusCode >= 200 && statusCode <= 299;
                const body = Buffer.concat(chunks).toString();
                if (validResponse) {
                    resolve({ statusCode, headers, body });
                } else {
                    reject(new Error(`Request failed. status: ${statusCode}, body: ${body}`));
                }
            });
        });
        req.on('error', reject);
        req.write(querystring.stringify({ data }), 'binary');
        req.end();
    });
}
