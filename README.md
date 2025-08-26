# MasterThesis_ZubairAhmed
The Git repository is for the Master Thesis 'A Machine Learning-Driven Approach to Optimizing Regression Test Binning: Enhancing Debugging Efficiency in Digital Front-end Verification'

## Git Structure

- The **`Bamboo`** folder highlights the tool integration into the Elmos's Regression System, titled 'Bamboo'. The  entirity of the code is written in `.sh` file, a shell script that the Unix shell like `bash`,`sh` or `zsh` can execute. 
**Why use a shell script?**
Instead of manually typing and rerunning the same commands over and over, the script automates the process. This makes the workflow faster, less error-prone, and easier to repeat.


- The **`RDA`** folder highlights the shell based deployment of the tool. The code here is written in `makefile`, it defines rules and dependencies for building or automating tasks and `.sh` file.
**Why use Makefile?**
Commonly used in software development for compiling code, but can also automate scripts, tests or even data processing. So instead of typing command manually, it is defined as **targets** in a `Makefile`.

- The **`python`** folder is all about the custom python framework developed using open source libraries available. In addition to the core framework files, it also includes Python scripts for data visualization and metrics calculation.
**Why python use for framework development?**
Python is one of the most widely used languages for building frameworks because it is simple, readable, and has a vast ecosystem of libraries. Its flexibility makes it ideal for automating workflows, processing data, and integrating with other tools. Moreover, Python’s strong community support and availability of open-source packages reduce development time and ensure maintainability.
