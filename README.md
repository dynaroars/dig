DIG (Dynamic Invariant Generator) for Visual Studio Code

**Overview**
The DIG (Dynamic Invariant Generator) is a tool designed to automatically generate and test program invariants, helping developers verify code correctness. This repository integrates DIG into Visual Studio Code, providing a user-friendly interface for developers to insert and validate invariants directly within their editor.

**Features**

  • Invariant Generation: Automatically generate invariants for supported data structures such as arrays and simple loops.

  •	Customizable Options: Control the depth of invariant generation, exclude certain expressions (equalities, inequalities, min/max), and more.

  •	Assertion Testing with CIVL: Validate assertions in your code using the CIVL verifier.

  •	VSCode Integration with LSP: Seamlessly integrates with Visual Studio Code using the Language Server Protocol (LSP) to provide real-time feedback, including syntax highlighting, error checking, and code completion.

  •	Automated Setup and Execution: DIG+ automates the setup, execution, and management of DIG and CIVL tools, simplifying installation and usage, especially for developers unfamiliar with command-line interfaces.

  •	Multiprocessing: Supports running multiple instances of CIVL in parallel to improve performance.

  •	Error Handling: Automatically remove invalid assertions to ensure code correctness.

**Usage**

Currently, the tool supports the analysis and generation of invariants exclusively for C programs.

1. Inserting Invariants
•	Right-click on the line where you want to insert an invariant and select Insert Invariant from the menu.
•	Customize the invariant generation by specifying the depth and constraints (optional).

2. Testing Invariants
•	Run the Test Invariants command to verify all the assertions in the current file.
•	Results are shown in the output panel, with options to automatically remove any invalid assertions.

**Target Users**

DIG+ is designed for industrial developers, academics, and researchers interested in formal verification and program specification through automated invariant generation and checking.

**Contact**

For questions or support, please create an issue in the GitHub repository or contact us directly.

