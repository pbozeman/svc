`ifndef SVC_STR_SV
`define SVC_STR_SV

parameter SVC_STR_MAX_LEN = 128;

// convert a literal to a packed string, msb first like a "normal" string
task automatic svc_str_init(output logic [8*SVC_STR_MAX_LEN-1:0] str,
                            input logic [8*SVC_STR_MAX_LEN-1:0] literal,
                            input int len);
  str = '0;
  for (int i = 0; i < SVC_STR_MAX_LEN; i++) begin
    if (i < len) begin
      str[8*i+:8] = literal[8*(len-1-i)+:8];
    end
  end
endtask

// helper macro to avoid having to specify the len
`define SVC_STR_INIT(out_str, str_literal) \
   svc_str_init(out_str, str_literal, $bits(str_literal)/8)

`endif
