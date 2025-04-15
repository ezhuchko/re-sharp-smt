# Lean Formalization of the Lookaround Normal Form (LNF)

This repo contains the Lean formalization files for the paper "Regex Decision Procedures in Extended RE#".

## Quick start
  1. Install VS Code and then install the `lean4` extension.
  2. Open this folder in VS Code.
  3. Open the `Regex.lean` file, which collects all modules of the formalization.

## Brief file overview

Listed below is a brief description of each file of the formalization.

- `EBA` : main definitions about Effective Boolean Algebras (EBA). The EBA is implemented in Lean as a type class. The assumption on the EBA is introduced at the beginning of the files with a variable command. 
- `Span` : main definitions and lemmas about spans. 
- `TTerm`: main definitions and lemmas about transition terms.

The main results are organized into three main directories, each corresponding to different classes of regular expressions:

### **1. `EREa/` – Extended Regular Expressions with Anchors**

This folder contains formalization results for the `EREa` class of regular expressions, which includes intersection, complement and start/end anchors.

Listed below is a brief description of each core file of the formalization.

- `EREa` : main definitions for the class `EREa`. 
- `Metrics` : metrics on regular expressions to show termination of theorems/definitions. 
- `Semantics` : classical matching semantics, defined on locations and spans.
- `Derivatives` : main definitions for derivative-based matching (includes both symbolic derivatives and classical). 
- `Equivalence` : proof of equivalence between the symbolic and classical derivative-based matching.
- `Correctness` : contains the equivalence theorem between the language-based semantics and the derivative-based matching.

### **2. `RESharp/` – The RE# Fragment**

This folder contains the formalization of the `RE` fragment which extends `RESharp` with unrestricted lookarounds.

We take the existing formalization from https://github.com/ezhuchko/extended-regexes and extend it with the following: 

- `Rewrites` : contains the formalization of the inference rules from Section 3.2 in the paper.

### **3. `EREwLookarounds/` – Regular Expressions with Lookarounds**

This folder contains the formalization of the `RESharp` fragment, which extends `EREa` with a restricted subset of lookarounds.

Listed below is a brief description of each file of the formalization.

- `RESharp` : main definitions for the class `RESharp`. 
- `Metrics` : metrics on regular expressions to show termination of theorems/definitions. 
- `Semantics`: classical matching semantics, defined on locations and spans.
- `Conversions`: contains the conversion theorems between match semantics of the three classes of regexes `EREa`, `RESharp` and `RE`.
- `LookaroundNormalForm`: contains the main correctness theorem `lnf_correct` for the lookaround normal form.

## Dependencies

The project dependencies are listed in `lakefile.toml`.

 - [Lean](https://lean-lang.org/) 4.14.0-rc2

The Lean version manager elan and the build tool lake will automatically download these dependency versions when you run `lake build`.

Lean has minimal platform requirements.  The instructions provided above will work on Ubuntu 24.04 (x86-64) with git and curl installed.  Other platforms, including Windows and macOS, are supported by Lean as well.  Please see the [Lean documentation](https://lean-lang.org/lean4/doc/setup.html) for more details on platform support.

## List of claims

- `RESharp.LookaroundNormalForm.lean` contains the main `lnf_correct` theorem which corresponds to Theorem 2 from Section 3.3 of the paper. 