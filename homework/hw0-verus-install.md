# Homework 0

 The [Verus overview](https://verus-lang.github.io/verus/guide/overview.html) is the _text_ for the course. This homework covers [1. Getting Started](https://verus-lang.github.io/verus/guide/getting_started.html) and [2. Using Verus within Rust](https://verus-lang.github.io/verus/guide/verus_macro_intro.html).

## Problems

1. Install verus: follow [Getting Started on the command line](https://verus-lang.github.io/verus/guide/getting_started_cmd_line.html) to install `verus` for your system. Submit the following for this problem:

    1. A screen shot showing step 2 complete for verified `getting_started.rs`
    1. A screen shot showing step 2 complete for the modified `getting_started.rs` that doesn't verify
    1. A screen shot showing step 3 complete

1. Configure `verus-analyzer`: follow [Getting Started with VSCode](https://verus-lang.github.io/verus/guide/getting_started_vscode.html) to install `verus-analyzer` for your system. Submit a screenshot of the `main.rs` file showing the failing assertion.

## Docker Shortcut?

If you have [Docker](https://www.docker.com) installed on your system and the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) `vscode` extension also on your system, then this homework is most easily completed by opening a workspace with the provided container definition found in `.devcontainer/devcontainer.json`. "Most easily" assumes that _the container builds successfully_. Your mileage may vary as the container nukes and then clones `verus` and `verus-analyzer` both of which may introduce breaking changes. My last rebuild was August 12.

To use the Docker container, open `Command Pallette` with `View -> Command Pallette` and then type _Dev Containers: Reopen in Container_. In general, if you have the `Dev Containers` extension installed, then when you open the `byu-cs-686-verus` directory in `vscode` it will prompt if you want to _Reopen in Container_. Choose yes. And then wait because it takes a long time to build [z3](https://github.com/Z3Prover/z3). You can watch the log if you get bored. Be patient. You may run out of resources on Docker, and if that happens, then try `docker builder prune --all --force` to free up space.

When the container is done, it has a last step to install the `verus-analyzer` extension. In a `vscode` terminal, run `bash .devcontainer/post-create.sh`. It should complete with no errors. At that point, `verus` should be available on the command line to complete problem 0, and the extensions should be active to complete problem 1.

### Other Niceties from Docker

The container configures the project so that not only does `verus-analyzer` work out of the box but so does `cargo build`, `cargo test`, etc. **WARNING**: `cargo-verus` (also known as `cargo verus`) does not work as of August 13 in the custom build as it fails to find the builtin crate. Prefer using `verus` (i.e., `verus src/main`).

The project also includes a `verusfmt` binary to format `.rs` files: `verusfmt <file>`. I've added `verusfmt` to a `pre-commit` hook to keep the code clean. `pre-commit`is installed with the `post-create.sh` script.

## Local install

If you are not using the dev container, then with some luck the prebuilt binaries will work out of the box: no extra effort required. That should be the case, I think, for running native on Apple or Intel/AMD silicon in Windows or OSX. My install is in a Linux development container managed with Docker on Apple silicon. The pre-built binaries did not work in that environment, so I had to build **everything** from source.

Building everything from source is not without a few challenges in a dev container running on Apple silicon. The first issue is needing `glibc 2.39` so that meant I was not able to use any of the existing `vscode` dev container images from Microsoft. After that is resolved with a custom `Docker` file starting from a `Debian::sid` image, the `z3` and `verus` builds are straightforward (though the `z3` build takes a long time so be sure to cache that layer). The `verus-analyzer` build  was a nightmare for me. See the `.devcontainer/Dockerfile` and `.devcontainer/.devcontainer.json` files for details. These effectively document how to build from source. The `Dockerfile` is the best starting point as it documents the whole build process. The `.devcontainer/post-create.sh` script installs the `verus-analyzer` extension in `vscode`.

To be fair, I further complicated my life by insisting that the `cargo verus` integration work. That effort failed miserably, and I had to give up after wasting more time than I had sense trying to make it go -- I said some very bad things to the AI that was helping, and I'm not proud of that.

Final note, getting tools working is an important skill to practice. Tooling is a constant challenge in professional settings, and learning to get, and keep, tools working is just part of the trade. That learning only happens through experience (both bitter and sweet). Leverage AI, but also do not skip reading the docs. I have had really good experiences with AI in support of tooling and really bad experiences that could have been avoided by looking at the docs myself. Sometimes the AI is both wrong and out of date. And ofter rather than checking the web the AI just puts out something that is wholly, and completely, not even in the ballpark. I'd suggest having the AI first look at the docs and then suggest a solution.
