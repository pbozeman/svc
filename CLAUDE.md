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
- NEVER add Co-Authored-By blocks in commit messages - this policy is strictly enforced

## Running Single Tests
- Single testbench: `make <module_name>_tb` (e.g., `make svc_arbiter_tb`)
- Single formal check: `make <module_name>_f` (e.g., `make svc_arbiter_f`)
- List available tests: `make list_tb` or `make list_f`

## Code Style Guidelines
- Naming: Module prefix `svc_`, test suffix `_tb`, formal suffix `_f`
- Signals: Lower snake_case without i_/o_ prefixes
- Types: Use `logic` instead of `wire`/`reg`
- Reset: Active-low `rst_n` with synchronous reset
- Indentation: Spaces (no tabs)
- Structure: Parameters first, then ports in module declarations
- Next-cycle signals: Use `_next` suffix (e.g., `grant_valid_next`)
- NEVER use end-of-line comments - ALL comments must be placed on the line above the code
- Signal declarations: Each signal must be declared on a separate line, never group declarations
- Code organization: Add new lines between logical groupings of declarations and assignments
- Casting: Always use proper type casting instead of disabling lint warnings
- Sequential blocks: Use always_ff with non-blocking assignments (<=)
- Combinational blocks: Use always_comb with blocking assignments (=)
- Complex conditionals: Use if/else blocks instead of ternary operators for complex nested conditions

## Testbench Guidelines
- Each testbench should use the `svc_unit.sv` framework (`TEST_SUITE_BEGIN`/`TEST_SUITE_END`)
- Create individual test tasks for different test cases (e.g., `test_reset`, `test_basic_operation`)
- Always use `automatic` keyword with tasks and functions in testbenches
- Use `TEST_CASE(task_name)` to register each test task
- Include reset test as first test in every testbench
- Use `TICK(clk)` to advance simulation by one clock cycle
- Use `CHECK_*` macros for assertions (`CHECK_EQ`, `CHECK_TRUE`, etc.)
- Use `CHECK_WAIT_FOR(clk, condition, max_cycles)` for waiting on conditions
- Pipeline stages should use `_p1`, `_p2` suffixes for signal naming
- Verify proper behavior with backpressure in streaming interfaces
- Use explicit type casting in function calls when needed (`int'(x)`, etc.)
- When using testbench arrays, use fixed sizes (e.g., `[256][256]`) instead of parameterized sizes