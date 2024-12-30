`ifndef SVC_SKIDBUF_SV
`define SVC_SKIDBUF_SV

`include "svc.sv"

// Port of https://zipcpu.com/blog/2019/05/22/skidbuffer.html.
//
// Moved to the svc coding style and stripping out some of the extra
// complexity (e.g. options other than output registration).

module svc_skidbuf #(
    parameter DATA_WIDTH = 8,
    parameter OPT_OUTREG = 0
) (
    input logic clk,
    input logic rst_n,

    input  logic                  s_valid,
    output logic                  s_ready,
    input  logic [DATA_WIDTH-1:0] s_data,

    output logic                  m_valid,
    input  logic                  m_ready,
    output logic [DATA_WIDTH-1:0] m_data
);
  logic                  skid_s_valid;
  logic [DATA_WIDTH-1:0] skid_s_data;

  //
  // s side
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      skid_s_valid <= 0;
    end else begin
      if ((s_valid && s_ready) && (m_valid && !m_ready))
        // We have incoming data, but the output is stalled
        skid_s_valid <= 1;
      else if (m_ready) skid_s_valid <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if ((!OPT_OUTREG || s_valid) && s_ready) begin
      skid_s_data <= s_data;
    end
  end

  assign s_ready = !skid_s_valid;

  //
  // m side
  //
  if (!OPT_OUTREG) begin : gen_net_output
    assign m_valid = rst_n && (s_valid || skid_s_valid);

    always_comb begin
      if (skid_s_valid) begin
        m_data = skid_s_data;
      end else if (s_valid) begin
        m_data = s_data;
      end else begin
        m_data = 0;
      end
    end

  end else begin : gen_reg_output
    logic m_valid_reg;

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        m_valid_reg <= 0;
      end else if (!m_valid || m_ready) begin
        m_valid_reg <= (s_valid || skid_s_valid);
      end
    end

    assign m_valid = m_valid_reg;

    always_ff @(posedge clk) begin
      if (!m_valid || m_ready) begin
        if (skid_s_valid) begin
          m_data <= skid_s_data;
        end else if (s_valid) begin
          m_data <= s_data;
        end
      end
    end
  end
endmodule
`endif
