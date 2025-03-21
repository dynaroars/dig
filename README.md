
******* DIG+-- BRINGING INVARIANT ANALYSIS TO MODERN IDES *******
A VS Code extension that integrates DIG and CIVL for seamless program invariant generation and checking.

***** OVERVIEW *****
DIG+ is a Visual Studio Code extension designed to bring program invariant analysis directly into the development environment. By integrating the DIG (Dynamic Invariant Generator) and CIVL (Symbolic Execution Tool) using the Language Server Protocol (LSP), DIG+ allows developers to automatically infer, check, and refine program invariants in real time—without the need for complex command-line interactions.

DIG+ simplifies formal verification by making powerful program analysis techniques accessible to researchers, software engineers, and students alike. 

Currently, the tool supports the analysis and generation of invariants exclusively for C programs.

***** FEATURES *****

1)	Automated Invariant Generation-- Extract program invariants using DIG directly from your code.

2)	Assertion Checking with CIVL-- Validate program assertions using CIVL’s symbolic execution.

3)	VS Code Integration 

4)	Customizable Analysis-- Select DIG’s various flags using a QuickPick UI to get results tailored to your needs.

5)	Automated Setup and Execution-- DIG+ automates the setup, execution, and management of DIG and CIVL tools, simplifying installation and usage, especially for developers unfamiliar with command-line interfaces. Error Handling & Debugging Support-- Provides clear feedback when assertions fail.

6)	Multiprocessing-- Supports running multiple instances of CIVL in parallel to improve performance.

7)	Error Handling -- Automatically remove invalid assertions to ensure code correctness.

***** INSTALLATION *****

To install and use DIG+, follow these steps:
  
  1) Prerequisites
     Ensure the following dependencies are installed on your system:
        •	Visual Studio Code
        •	Docker (Required for DIG & CIVL execution)
        •	Git 

     Verify installations:
	      docker --version
	      git --version
	      code --version
       
  2) Clone This Repository
     Clone the DIG+ repository and open it in VS Code:
	      git clone https://github.com/dynaroars/dig-vscode.git
	      cd dig-vscode
	      code .

  3) Install the Extension Locally
     Inside VS Code: 
        1.	Open the Run & Debug panel (left sidebar or Ctrl + Shift + D).
        2.	Select "Launch Extension" from the dropdown.
        3.	Click "Start Debugging" (green play button).
        4.	This opens a new Extension Development Host window.
        5.	Open a C file in the new window.

***** HOW TO USE DIG+ *****

Generating Invariants
1.	Add a vtrace() function call to mark the program location for invariant generation.
2.	Right-click on the line containing the vtrace() call and select "Insert Assertions".
3.	DIG+ will infer and insert assertions as assert(...) statements at the marked location. Comments will be added to all the DIG generated assertions to avoid confusion with other existing ones.

Checking Assertions
1.	Select the assertions you want to check. You can select one assertion or multiple assertions at the same one to test.
2.	Right-click and select "Test Assertions".
3.	CIVL will validate the assertions and mark them as valid or invalid. The valid assertions will be marked with a (“valid”) comment while the invalid assertions will trigger a prompt asking the user if they wish to remove them.

Customizing Invariant Generation
DIG+ allows you to fine-tune invariant generation by selecting additional DIG flags:
1.	Right-click on a line where you wish to insert assertions (the line must contain a vtrace() call) and select “Insert Custom Assertions”.
2.	A QuickPick UI will appear, allowing you to select different DIG options.
3.	Choose desired flags (e.g., --maxdeg, --noeqts, --se_maxdepth).
4.	Confirm the selection, and DIG+ will generate assertions according to the selected flags.


