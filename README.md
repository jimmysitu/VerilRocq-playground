# VerilRocq-playground

This repository serves as a playground for formally verifying open-source Verilog modules using the [VerilRocq](https://github.com/jimmysitu/VerilRocq) framework.

## Repository Structure

The repository is organized as follows:

*   **`VerilRocq/`**: The VerilRocq framework (included as a submodule).
*   **`modules/`**: Contains the target Verilog repositories (included as submodules).
    *   `verilog_arithmetic_module/`: A collection of arithmetic modules (Adder, Divider, Multiplier).
*   **`tools/`**: Helper scripts for the verification workflow.
    *   `verilog2rocq.py`: A script to automate the conversion of Verilog modules into VerilRocq-compatible Rocq definitions.
*   **`proofs/`**: The root directory for all formal proofs.
    *   `common/`: Common lemmas and tactics shared across different verification projects.
    *   `verilog_arithmetic_module_proof/`: Proofs specific to the `verilog_arithmetic_module` repository.
        *   Contains its own `_CoqProject` and `Makefile`.
        *   `Adder/HA/`: Example proof for the Half Adder module.

## Workflow

### 1. Initialization

Clone the repository and initialize the submodules:

```bash
git clone --recursive https://github.com/jimmysitu/VerilRocq-playground.git
cd VerilRocq-playground
# If you didn't clone with --recursive:
git submodule update --init --recursive
```

### 2. Generating Rocq Definitions

Use the provided Python script to convert a target Verilog file into a Rocq file containing the VerilRocq AST.

**Usage:**

```bash
python3 tools/verilog2rocq.py <input_verilog_file> <output_rocq_file>
```

**Example (Half Adder):**

```bash
# Create the destination directory
mkdir -p proofs/verilog_arithmetic_module_proof/Adder/HA

# Run the conversion
python3 tools/verilog2rocq.py \
    modules/verilog_arithmetic_module/Adder/00_HA/src/rtl/ha.v \
    proofs/verilog_arithmetic_module_proof/Adder/HA/ha_gen.v
```

### 3. Writing and Running Proofs

1.  Navigate to the relevant proof directory (e.g., `proofs/verilog_arithmetic_module_proof`).
2.  Write your proof file (e.g., `Adder/HA/ha_proof.v`), importing the generated module (`ha_gen.v`) and defining the correctness properties.
3.  Compile and verify the proofs using `make`.

```bash
cd proofs/verilog_arithmetic_module_proof
make
```

## Example: Half Adder (HA)

An example verification of a Half Adder module is provided in `proofs/verilog_arithmetic_module_proof/Adder/HA/`.

*   `ha_gen.v`: Auto-generated Rocq AST from the source Verilog.
*   `ha_proof.v`: The proof demonstrating that the Verilog implementation satisfies the specification `sum = a ^ b` and `carry = a & b`.

## Prerequisites

*   **Rocq**: The Rocq Proof Assistant 8.18.0 (compatible versions required by VerilRocq).
*   **Python 3**: For running the `verilog2rocq.py` conversion script.
