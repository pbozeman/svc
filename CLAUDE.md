# SVC - SystemVerilog Core Commands and Guidelines

## Documentation References

- **Style Guide**: See [docs/style.md](/docs/style.md) for comprehensive coding
  style guidelines
- **Testbench Guide**: See [docs/tb.md](/docs/tb.md) for detailed testbench
  development instructions

## Build Commands

- `make quick`: Default target, runs tests and formal verification with success
  silencing
- `make full`: Full verification with linting, testbenches and formal
  verification
- `make tb`: Run all testbenches
- `make formal`: Run all formal verification
- `make lint`: Lint all code with Verilator
- `make format`: Format all code to match style guidelines

## Running Single Tests

- Single testbench: `make <module_name>_tb` (e.g., `make svc_arbiter_tb`)
- Single formal check: `make <module_name>_f` (e.g., `make svc_arbiter_f`)
- List available tests: `make list_tb` or `make list_f`

## Important Workflow Notes

- ALWAYS run `make format` after making any code changes
- Run `make lint` to check for linting issues before committing
- Add [🤖] emoji to commit message tags when commits are Claude-generated
- Add "✨🤖✨ vibe coded with claude" comment at the top of Claude-generated files
- NEVER add Co-Authored-By blocks in commit messages - this policy is strictly
  enforced
