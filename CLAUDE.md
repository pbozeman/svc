# SVC - SystemVerilog Core Commands and Guidelines

## Build Commands
- `make quick`: Default target, runs tests and formal verification with success silencing
- `make full`: Full verification with linting, testbenches and formal verification
- `make tb`: Run all testbenches
- `make formal`: Run all formal verification
- `make lint`: Lint all code with Verilator
- `make format`: Format all code to match style guidelines

## Important Workflow Notes
- ALWAYS run `make format` after making any code changes
- Run `make lint` to check for linting issues before committing
- Add [🤖] emoji to commit message tags when commits are Claude-generated
- Add "✨🤖✨ vibe coded with claude" comment at the top of Claude-generated files

## Running Single Tests
- Single testbench: `make <module_name>_tb` (e.g., `make svc_arbiter_tb`)
- Single formal check: `make <module_name>_f` (e.g., `make svc_arbiter_f`)
- List available tests: `make list_tb` or `make list_f`

## Code Style Guidelines
- Naming: Module prefix `svc_`, test suffix `_tb`, formal suffix `_f`
- Signals: Lower snake_case without i_/o_ prefixes
- Types: Use `logic` instead of `wire`/`reg`
- Reset: Active-low `rst_n`
- Indentation: Spaces (no tabs)
- Structure: Parameters first, then ports in module declarations
- Next-cycle signals: Use `_next` suffix (e.g., `grant_valid_next`)