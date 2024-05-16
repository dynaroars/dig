"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.getAssertionsForLatestVtrace = void 0;
function getAssertionsForLatestVtrace(digOutput, textUpToPosition, currentLineIndentation) {
    // Find the most recent vtrace call above the current line
    let matches = [...textUpToPosition.matchAll(/vtrace(\d+)/g)];
    // Get the last matched vtrace number
    let lastVtraceNum = matches[matches.length - 1]?.[1];
    if (!lastVtraceNum) {
        // No vtrace calls found
        return '';
    }
    // Extract invariants for the most recent vtrace call
    let vtracePattern = new RegExp(`vtrace${lastVtraceNum} \\((\\d+) invs\\):([\\s\\S]*?)(?=vtrace\\d+ \\(|$)`, 'g');
    let vtraceMatch = vtracePattern.exec(digOutput);
    if (vtraceMatch && vtraceMatch[2]) {
        // Format the extracted invariants as assertions
        return vtraceMatch[2].trim().split('\n')
            .filter(line => line.match(/^\d+\./))
            .map(line => `assert(${line.substring(line.indexOf(' ') + 1)});`)
            .join(`\n${currentLineIndentation}`);
    }
    // No invariants found for the most recent vtrace call
    return '';
}
exports.getAssertionsForLatestVtrace = getAssertionsForLatestVtrace;
//# sourceMappingURL=dig_utils.js.map