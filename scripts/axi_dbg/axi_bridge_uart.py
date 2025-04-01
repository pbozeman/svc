import serial
import struct

# Coordinate any changes with svc_axil_bridge_uart
MAGIC_CMD = 0xF0B0
MAGIC_RESP = 0xAB

OP_READ = 0x00
OP_WRITE = 0x01


class AxiBridgeUart:
    def __init__(self, port, baudrate=115200):
        self.ser = serial.Serial(port, baudrate, timeout=1)

    def _send(self, data):
        self.ser.write(data)

    def _recv_exact(self, n):
        buf = b""
        while len(buf) < n:
            chunk = self.ser.read(n - len(buf))
            if not chunk:
                raise TimeoutError("Timeout while waiting for response")
            buf += chunk
        return buf

    def write_word(self, addr, data):
        """Write a 32-bit word to a given AXI address."""
        # struct.pack format: <HBI
        # <     = little-endian
        # H     = 2-byte unsigned short (MAGIC_CMD)
        # B     = 1-byte unsigned char (OP_WRITE)
        # I     = 4-byte unsigned int (addr)
        payload = struct.pack("<HBI", MAGIC_CMD, OP_WRITE, addr)

        # Append 4-byte data word to payload
        payload += struct.pack("<I", data)

        self._send(payload)

        # Expect: 1 byte magic, 1 byte bresp
        resp = self._recv_exact(2)
        if resp[0] != MAGIC_RESP:
            raise ValueError(f"Invalid response magic: {resp[0]:02X}")
        bresp = resp[1]
        return bresp

    def read_word(self, addr):
        """Read a 32-bit word from a given AXI address."""
        # struct.pack format: <HBI
        # <     = little-endian
        # H     = 2-byte unsigned short (MAGIC_CMD)
        # B     = 1-byte unsigned char (OP_READ)
        # I     = 4-byte unsigned int (addr)
        payload = struct.pack("<HBI", MAGIC_CMD, OP_READ, addr)

        self._send(payload)

        # Expect: 1 byte magic, 1 byte rresp, 4 bytes data
        resp = self._recv_exact(6)
        if resp[0] != MAGIC_RESP:
            raise ValueError(f"Invalid response magic: {resp[0]:02X}")
        rresp = resp[1]
        data = struct.unpack("<I", resp[2:])[0]
        return rresp, data

    def close(self):
        """Close the UART connection."""
        self.ser.close()
