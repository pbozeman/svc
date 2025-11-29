#!/usr/bin/env python3
"""
Convert byte-oriented Verilog hex (from objcopy -O verilog) to word-oriented hex.

objcopy outputs: @00000000
                 97 0F 00 00 93 8F CF 00 ...

$readmemh expects for 32-bit memory: @00000000
                                     00000F97
                                     00CF8F93
                                     ...
"""

import sys

def convert_hex(input_file, output_file):
    with open(input_file, 'r') as f:
        lines = f.readlines()

    with open(output_file, 'w') as f:
        byte_addr = 0
        bytes_buf = []

        for line in lines:
            line = line.strip()
            if not line:
                continue

            if line.startswith('@'):
                # Flush any pending bytes
                while len(bytes_buf) >= 4:
                    word = bytes_buf[0] | (bytes_buf[1] << 8) | (bytes_buf[2] << 16) | (bytes_buf[3] << 24)
                    f.write(f'{word:08x}\n')
                    bytes_buf = bytes_buf[4:]

                # Write new address (convert byte addr to word addr)
                byte_addr = int(line[1:], 16)
                word_addr = byte_addr // 4
                f.write(f'@{word_addr:08x}\n')
                bytes_buf = []
                continue

            # Parse space-separated bytes
            for byte_str in line.split():
                if byte_str.startswith('//'):
                    break
                try:
                    bytes_buf.append(int(byte_str, 16))
                except ValueError:
                    continue

                # When we have 4 bytes, write a word
                if len(bytes_buf) == 4:
                    word = bytes_buf[0] | (bytes_buf[1] << 8) | (bytes_buf[2] << 16) | (bytes_buf[3] << 24)
                    f.write(f'{word:08x}\n')
                    bytes_buf = []

        # Flush any remaining bytes (pad with zeros)
        if bytes_buf:
            while len(bytes_buf) < 4:
                bytes_buf.append(0)
            word = bytes_buf[0] | (bytes_buf[1] << 8) | (bytes_buf[2] << 16) | (bytes_buf[3] << 24)
            f.write(f'{word:08x}\n')

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print(f'Usage: {sys.argv[0]} <input.hex> <output.hex>')
        sys.exit(1)

    convert_hex(sys.argv[1], sys.argv[2])
