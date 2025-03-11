# SystemVerilog Testbench Guide

This guide provides a comprehensive overview of how to write effective
testbenches for the SVC repository, following the established conventions and
patterns.

## Framework Overview

The SVC repository uses a custom lightweight testing framework implemented in
`svc_unit.sv`. This framework is designed to work with iverilog and provides a
structured approach for creating and organizing testbenches.

## Basic Testbench Structure

Every testbench should follow this basic structure:

```systemverilog
`include "svc_unit.sv"
`include "<module_under_test>.sv"

module <module_name>_tb;
  // 1. Clock and reset generation
  `TEST_CLK_NS(clk, 10);  // 10ns clock period
  `TEST_RST_N(clk, rst_n); // Reset signal generation
  
  // 2. Module instantiation
  <module_name> #(
    // Parameters
  ) uut (
    // Port connections
  );
  
  // 3. Signal initialization in reset block
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      // Initialize all inputs/outputs here
      input_signal_1 <= 1'b0;
      input_signal_2 <= 8'h00;
      // ...
    end
  end
  
  // 4. Individual test tasks
  task automatic test_reset();
    // Always include a reset test
    `CHECK_FALSE(uut_output_signal);
    // More assertions...
  endtask
  
  task automatic test_basic_operation();
    // Test basic functionality
    // ...
  endtask
  
  // 5. Test suite definition
  `TEST_SUITE_BEGIN(<module_name>_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_operation);
  // More test cases...
  `TEST_SUITE_END();
endmodule
```

## Key Macros and Features

### Test Framework Setup

- **`TEST_SUITE_BEGIN(module_name)`**: Initializes the test suite
- **`TEST_SUITE_END()`**: Finalizes the test suite
- **`TEST_CLK_NS(clk, period_ns)`**: Creates a clock with specified period
- **`TEST_RST_N(clk, rst_n, cycles=5)`**: Sets up reset signal, active for
  specified cycles

### Test Organization

- **`TEST_CASE(test_task)`**: Registers a test case to be run
- **`TICK(clk)`**: Advances simulation by one clock cycle

### Assertions

- **`CHECK_TRUE(condition)`**: Verifies condition is true
- **`CHECK_FALSE(condition)`**: Verifies condition is false
- **`CHECK_EQ(a, b)`**: Verifies a equals b
- **`CHECK_NEQ(a, b)`**: Verifies a doesn't equal b
- **`CHECK_LT(a, b)`**, **`CHECK_GT(a, b)`**, **`CHECK_LTE(a, b)`**,
  **`CHECK_GTE(a, b)`**: Comparison checks
- **`CHECK_WAIT_FOR(clk, condition, max_cycles=16)`**: Waits for condition to
  become true

## Best Practices

### General Guidelines

1. **Use `automatic` for all tasks**: This ensures local variables are properly
   scoped
1. **Follow naming conventions**: Module tests should be named with `_tb` suffix
1. **Always include a reset test**: Test proper behavior after reset
1. **Organize tests logically**: Simple tests first, complex tests later
1. **Use explicit typing**: Prefer explicit type declarations over inferred
   types

### Signal Initialization

1. **Use synchronous reset block**: Initialize all signals in an `always_ff`
   block with reset condition
1. **Complete initialization**: Ensure all inputs and outputs are properly
   initialized
1. **Use non-blocking assignments**: Always use `<=` for sequential logic in the
   reset block
1. **Follow module interface order**: Keep initialization in the same order as
   the module interface signals

### Test Organization

1. **One test per functionality**: Each test task should focus on a specific
   aspect
1. **Independent tests**: Tests should be independent of each other
1. **Comprehensive testing**: Cover normal operation, edge cases, and error
   conditions
1. **Test with backpressure**: For streaming interfaces, test behavior with
   backpressure

### Code Style

1. **Declare local variables at the top**: Place all variable declarations at
   the beginning of tasks
1. **Use consistent indentation**: Follow the code style in existing tests
1. **Align port connections**: For better readability
1. **Add sufficient comments**: Especially for complex test scenarios
1. **Use consistent color values**: For graphics testing (e.g., 12'hF00 for red)

### Streaming Interface Testing

When testing streaming interfaces (valid/ready), follow these patterns:

1. Test data transmission with no backpressure
1. Test with varying backpressure patterns
1. Verify correct handling of valid/ready handshake
1. Test edge cases (valid without ready, etc.)

### Pipeline Testing

For pipelined designs:

1. Use signal naming with `_p1`, `_p2` suffixes for pipeline stages
1. Test correct propagation through pipeline stages
1. Verify pipeline stalling behavior
1. Test pipeline flushing if applicable

## Running Tests

Tests can be run using the Makefile system:

- **`make <module_name>_tb`**: Runs a specific testbench
- **`make tb`**: Runs all testbenches
- **`make quick`**: Runs tests and formal verification with success silencing
- **`make full`**: Runs full verification including linting

To run a specific test case within a testbench:

```bash
make <module_name>_tb RUN=test_case_name
```

## Debugging

When a test fails, the framework provides:

1. Colored error messages with file and line information
1. Commands to re-run the specific test
1. VCD waveform generation for visual debugging

Use the automatically generated VCD file for waveform analysis:

```bash
gtkwave .build/<module_name>.vcd &
```

## Example Testbench

Here's a comprehensive example testbench for a simple module:

```systemverilog
`include "svc_unit.sv"
`include "svc_example_module.sv"

module svc_example_module_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);
  
  // Testbench signals
  logic       input_valid;
  logic       input_ready;
  logic [7:0] input_data;
  
  logic       output_valid;
  logic       output_ready;
  logic [7:0] output_data;
  
  // UUT instantiation
  svc_example_module uut (
    .clk       (clk),
    .rst_n     (rst_n),
    
    .in_valid  (input_valid),
    .in_ready  (input_ready),
    .in_data   (input_data),
    
    .out_valid (output_valid),
    .out_ready (output_ready),
    .out_data  (output_data)
  );
  
  // Initialize signals in reset
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      input_valid  <= 1'b0;
      input_data   <= 8'h00;
      output_ready <= 1'b1;
    end
  end
  
  // Test reset behavior
  task automatic test_reset();
    `CHECK_FALSE(output_valid);
    `CHECK_TRUE(input_ready);
  endtask
  
  // Test basic data flow
  task automatic test_basic_data_flow();
    // Send single data word
    input_valid = 1'b1;
    input_data  = 8'hA5;
    
    `TICK(clk);
    `CHECK_TRUE(input_ready);
    
    // Wait for output
    `CHECK_WAIT_FOR(clk, output_valid, 5);
    `CHECK_EQ(output_data, 8'hA5);
    
    // Complete transaction
    output_ready = 1'b1;
    input_valid  = 1'b0;
    
    `TICK(clk);
    `CHECK_FALSE(output_valid);
  endtask
  
  // Test backpressure
  task automatic test_backpressure();
    // Apply backpressure
    output_ready = 1'b0;
    
    // Send data
    input_valid = 1'b1;
    input_data  = 8'h42;
    
    `TICK(clk);
    
    // Check data is held
    `CHECK_WAIT_FOR(clk, output_valid, 5);
    output_ready = 1'b0;  // Keep backpressure
    
    repeat (3) `TICK(clk);
    
    // Verify data is still valid and unchanged
    `CHECK_TRUE(output_valid);
    `CHECK_EQ(output_data, 8'h42);
    
    // Release backpressure
    output_ready = 1'b1;
    
    `TICK(clk);
    `CHECK_FALSE(output_valid);
  endtask
  
  // Register and run all tests
  `TEST_SUITE_BEGIN(svc_example_module_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_data_flow);
  `TEST_CASE(test_backpressure);
  `TEST_SUITE_END();
endmodule
```

## Additional Signal Management

For complex testbenches, it's common to have additional logic for managing
signals beyond the reset initialization:

```systemverilog
// Clear valid signals after handshake
always_ff @(posedge clk) begin
  if (input_valid && input_ready) begin
    input_valid <= 1'b0;
  end
  
  if (output_valid && output_ready) begin
    output_valid <= 1'b0;
  end
end
```

## Formal Verification Integration

This repository also uses formal verification extensively. The testbenches are
complementary to formal verification:

- Use testbenches for directed testing and specific scenarios
- Use formal verification for exhaustive property checking

When a module has formal verification (in `tb/formal/`), focus testbench efforts
on:

1. Functional scenarios not easily expressed as formal properties
1. Complex interaction sequences
1. Performance and timing aspects

## Additional Resources

For more examples, refer to existing testbenches in the repository:

- Basic module testing: `svc_arbiter_tb.sv`
- Complex interface testing: `svc_axi_axil_adapter_tb.sv`
- Graphics module testing: `svc_gfx_vga_tb.sv`

Always run `make format` after writing new testbenches to ensure consistent code
style.
