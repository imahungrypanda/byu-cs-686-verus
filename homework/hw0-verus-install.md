The [Verus overview](https://verus-lang.github.io/verus/guide/overview.html) is the starting point for the course. This homework is to complete [Getting Started](https://verus-lang.github.io/verus/guide/getting_started.html). The homework is complete when Verus is running on your system. 


## Problem 0: install verus

Follow [Getting Started on the command line](https://verus-lang.github.io/verus/guide/getting_started_cmd_line.html) to install `verus` for your system. Submit the following for this problem:

1. A screen shot showing step 2 complete for verified `getting_started.rs`
1. A screen shot showing step 2 complete for the modified `getting_started.rs` that doesn't verify
1. A screen shot showing step 3 complete

## Problem 1: configure verus and VSCode

Follow [Getting Started with VSCode](https://verus-lang.github.io/verus/guide/getting_started_vscode.html) to install `verus-analyzer` for your system. Submit a screenshot of the `main.rs` file showing the failing assertion.

## Docker

If you have [Docker](https://www.docker.com) installed on your system and the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) `vscode` extension also on your system, then this homework is most easily completed by opening a workspace with the provided containter definition found in `.devcontainer/devcontainer.json`.  You can do this be opening the `Command Pallette` with `View -> Command Pallette` and then typing in _Dev Containers: Reopen in Container_. In general, if you have the `Dev Containers` extension installed, then when you open the `byu-cs-686-verus` directory in `vscode` it will prompt you if you want to _Reopen in Container_. Choose yes.

Building the container takes a fair amount of time since it builds everything from source including [z3](https://github.com/Z3Prover/z3). Be patient. When the container is done, it has a last step to install the `verus-analyzer` extension. In a `vscode` terminal, run `bash .devcontainer/post-create.sh`. It should complete with no errors. At that point, `verus` should be available on the command line to complete problem 0, and the extensions should be active to complete problem 1.

## Notes on local install

Building everything from source was not without a few challenges starting with needing `glibc` 2.39. The `z3` and `verus` binaries where straightfortward. The `verus-analyzer` was less so. See the `.devcontainer/Dockerfile` and `.devcontainer/.devcontainer.json` files for details. the `Dockerfile` is the best starting point as it documents the whole build process. The `verus` and `verus-analyzer` documentation for building from source is always very helpful.
