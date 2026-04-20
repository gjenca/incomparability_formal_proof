# Incomparability orthosets of finite posets

This is a repository containing formal proofs in Lean 4 of all the theorems from

 - G. Jenča, *N-free Posets and Orthomodularity*, Order **43**(11) (2026). [doi:10.1007/s11083-025-09723-y](https://doi.org/10.1007/s11083-025-09723-y)
 - G. Jenča, *Correction: N-free Posets and Orthomodularity*, preprint (2026). [arXiv:XXXX.XXXXX](https://arxiv.org/abs/XXXX.XXXXX)

## Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) with `elan` (the Lean version manager)
- Internet access to download the Mathlib build cache (~1 GB)

## Building

### Visual Studio Code

1. Install the [lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) in VS Code.
2. Clone this repository:
   ```
   git clone https://github.com/gjenca/incomparability_formal_proof.git
   cd incomparability_formal_proof
   ```
3. Open the folder in VS Code (`File → Open Folder`).
4. The extension will automatically install the correct Lean toolchain and download the Mathlib cache. This may take several minutes on the first run.
5. Open `IncomparabilityFormalProof/Basic.lean`. Definitions and theorems will be checked interactively; a spinning indicator in the status bar means elaboration is in progress.

### Command line

1. Clone this repository:
   ```
   git clone https://github.com/gjenca/incomparability_formal_proof.git
   cd incomparability_formal_proof
   ```
2. Install the correct Lean toolchain (done automatically by `elan` on first use):
   ```
   elan show
   ```
3. Download the Mathlib build cache and compile:
   ```
   lake exe cache get
   lake build
   ```
   `lake exe cache get` downloads precompiled Mathlib artifacts (~1 GB); without it `lake build` would compile Mathlib from source, which takes several hours.

4. A successful build ends with:
   ```
   Build completed successfully.
   ```

