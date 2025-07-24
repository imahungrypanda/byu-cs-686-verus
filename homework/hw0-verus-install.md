The [Verus overview](https://verus-lang.github.io/verus/guide/overview.html) is the starting point for the course. This homework is to complete [Getting Started](https://verus-lang.github.io/verus/guide/getting_started.html). The homework is complete when Verus is running on your system. 

## Problem 0: install verus

### Docker

If you have [Docker](https://www.docker.com) installed on your system and the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) `vscode` extension also on your system, then this homework is most easily completed by opening a workspace in the provided containter definition found in `.devcontainer/devcontainer.json`.  You can do this be opening the `Command Pallette` with `View -> Command Pallette` and then typing in _Dev Containers: Reopen in Container_. In generally, if you have the `Dev Containers` extension installed, then when you open the `byu-cs-686-verus` directory in `vscode` it will prompt you if you want to _Reopen in Container_. Choose yes.

### Notes on local install

Follow either command line or `vscode` install in [Getting Started](https://verus-lang.github.io/verus/guide/getting_started.html). These notes are from the `vscode` install while setting up the dev container.

* Requires newer version of `glibc`, 2.39, than what ships in `bullseye` or `bookworm` so defaulted to custom image based on `debian:sid` --- see `.devcontainer/dockerfile`.

