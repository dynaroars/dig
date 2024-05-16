"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.getContext = exports.setContext = void 0;
// Context for the extension
let extensionContext;
// Set the context for the extension
function setContext(context) {
    extensionContext = context;
}
exports.setContext = setContext;
// Get the context for the extension
function getContext() {
    return extensionContext;
}
exports.getContext = getContext;
//# sourceMappingURL=context.js.map