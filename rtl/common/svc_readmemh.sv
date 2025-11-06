`ifndef SVC_READMEMH_SV
`define SVC_READMEMH_SV

`ifndef SYNTHESIS

//
// Utility function to count data words in a $readmemh-style file
//
// This prevents Icarus "Not enough words in the file" warnings by allowing
// you to only load up to the actual number of words present.
//
// The counting logic respects:
// - @<addr> address directives (skipped)
// - // comments (skipped)
// - All other tokens are counted as data words
//
// Usage:
//   int word_count;
//   word_count = svc_readmemh_count("firmware.hex");
//   $readmemh("firmware.hex", mem, 0, word_count - 1);
//
function automatic int svc_readmemh_count(input string filename);
  int    fd;
  int    count;
  string tok;
  int    scan_result;
  int    c;

  fd = $fopen(filename, "r");
  if (fd == 0) begin
    $error("svc_readmemh_count: could not open file '%s'", filename);
    return 0;
  end

  count       = 0;
  scan_result = $fscanf(fd, "%s", tok);
  while (scan_result == 1) begin
    if (tok.len() > 0) begin
      if (tok[0] == "@") begin
        //
        // Address directive: skip
        //
      end else if (tok[0] == "/") begin
        //
        // Line comment: skip rest of line
        //
        c = $fgetc(fd);
        while (c >= 0 && c != "\n") begin
          c = $fgetc(fd);
        end
      end else begin
        //
        // Data word
        //
        count++;
      end
    end
    scan_result = $fscanf(fd, "%s", tok);
  end
  $fclose(fd);

  return count;
endfunction

`endif
`endif
