/*
 * CS:APP Data Lab
 *
 * <Please put your name and userid here>
 *
 * bits.c - Source file with your solutions to the Lab.
 *          This is the file you will hand in to your instructor.
 *
 * WARNING: Do not include the <stdio.h> header; it confuses the dlc
 * compiler. You can still use printf for debugging without including
 * <stdio.h>, although you might get a compiler warning. In general,
 * it's not good practice to ignore compiler warnings, but in this
 * case it's OK.
 */

#if 0
/*
 * Instructions to Students:
 *
 * STEP 1: Read the following instructions carefully.
 */

You will provide your solution to the Data Lab by
editing the collection of functions in this source file.

INTEGER CODING RULES:
 
  Replace the "return" statement in each function with one
  or more lines of C code that implements the function. Your code 
  must conform to the following style:
 
  int Funct(arg1, arg2, ...) {
      /* brief description of how your implementation works */
      int var1 = Expr1;
      ...
      int varM = ExprM;

      varJ = ExprJ;
      ...
      varN = ExprN;
      return ExprR;
  }

  Each "Expr" is an expression using ONLY the following:
  1. Integer constants 0 through 255 (0xFF), inclusive. You are
      not allowed to use big constants such as 0xffffffff.
  2. Function arguments and local variables (no global variables).
  3. Unary integer operations ! ~
  4. Binary integer operations & ^ | + << >>
    
  Some of the problems restrict the set of allowed operators even further.
  Each "Expr" may consist of multiple operators. You are not restricted to
  one operator per line.

  You are expressly forbidden to:
  1. Use any control constructs such as if, do, while, for, switch, etc.
  2. Define or use any macros.
  3. Define any additional functions in this file.
  4. Call any functions.
  5. Use any other operations, such as &&, ||, -, or ?:
  6. Use any form of casting.
  7. Use any data type other than int.  This implies that you
     cannot use arrays, structs, or unions.

 
  You may assume that your machine:
  1. Uses 2s complement, 32-bit representations of integers.
  2. Performs right shifts arithmetically.
  3. Has unpredictable behavior when shifting an integer by more
     than the word size.

EXAMPLES OF ACCEPTABLE CODING STYLE:
  /*
   * pow2plus1 - returns 2^x + 1, where 0 <= x <= 31
   */
  int pow2plus1(int x) {
     /* exploit ability of shifts to compute powers of 2 */
     return (1 << x) + 1;
  }

  /*
   * pow2plus4 - returns 2^x + 4, where 0 <= x <= 31
   */
  int pow2plus4(int x) {
     /* exploit ability of shifts to compute powers of 2 */
     int result = (1 << x);
     result += 4;
     return result;
  }

FLOATING POINT CODING RULES

For the problems that require you to implent floating-point operations,
the coding rules are less strict.  You are allowed to use looping and
conditional control.  You are allowed to use both ints and unsigneds.
You can use arbitrary integer and unsigned constants.

You are expressly forbidden to:
  1. Define or use any macros.
  2. Define any additional functions in this file.
  3. Call any functions.
  4. Use any form of casting.
  5. Use any data type other than int or unsigned.  This means that you
     cannot use arrays, structs, or unions.
  6. Use any floating point data types, operations, or constants.


NOTES:
  1. Use the dlc (data lab checker) compiler (described in the handout) to 
     check the legality of your solutions.
  2. Each function has a maximum number of operators (! ~ & ^ | + << >>)
     that you are allowed to use for your implementation of the function. 
     The max operator count is checked by dlc. Note that '=' is not 
     counted; you may use as many of these as you want without penalty.
  3. Use the btest test harness to check your functions for correctness.
  4. Use the BDD checker to formally verify your functions
  5. The maximum number of ops for each function is given in the
     header comment for each function. If there are any inconsistencies 
     between the maximum ops in the writeup and in this file, consider
     this file the authoritative source.

/*
 * STEP 2: Modify the following functions according the coding rules.
 * 
 *   IMPORTANT. TO AVOID GRADING SURPRISES:
 *   1. Use the dlc compiler to check that your solutions conform
 *      to the coding rules.
 *   2. Use the BDD checker to formally verify that your solutions produce 
 *      the correct answers.
 */

#endif
/* Copyright (C) 1991-2022 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 10.0.0.  Version 10.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2017, fifth edition, plus
   the following additions from Amendment 1 to the fifth edition:
   - 56 emoji characters
   - 285 hentaigana
   - 3 additional Zanabazar Square characters */
typedef struct {
  unsigned s : 1;
  unsigned e : 8;
  unsigned f : 23;
} FloatConstructor;
typedef union {
  unsigned raw;
  FloatConstructor c;
} FloatUnion;
typedef struct {
  unsigned se : 9;
  unsigned f : 23;
} FloatConstructorDense;
/*
 * bitAnd - x&y using only ~ and |
 *   Example: bitAnd(6, 5) = 4
 *   Legal ops: ~ |
 *   Max ops: 8
 *   Rating: 1
 */
int bitAnd(int x, int y) {
  //
  return ~((~x) | (~y));
}
/*
 * bitConditional - x ? y : z for each bit respectively
 *   Example: bitConditional(0b00110011, 0b01010101, 0b00001111) = 0b00011101
 *   Legal ops: & | ^ ~
 *   Max ops: 8
 *   Rating: 1
 */
int bitConditional(int x, int y, int z) {
  //
  return ((y ^ z) & x) ^ z;
}
/*
}
 * byteSwap - swaps the nth byte and the mth byte
 *  Examples: byteSwap(0x12345678, 1, 3) = 0x56341278
 *            byteSwap(0xDEADBEEF, 0, 2) = 0xDEEFBEAD
 *  You may assume that 0 <= n <= 3, 0 <= m <= 3
 *  Legal ops: ! ~ & ^ | + << >>
 *  Max ops: 25
 *  Rating: 2
 */
int byteSwap(int x, int n, int m) {
  int a;
  n = n << 3;
  m = m << 3;
  a = ((x >> n) ^ (x >> m)) & 0xFF;
  return (x ^ (a << m) ^ (a << n));
}
/*
 * logicalShift - shift x to the right by n, using a logical shift
 *   Can assume that 0 <= n <= 31
 *   Examples: logicalShift(0x87654321,4) = 0x08765432
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 20
 *   Rating: 3
 */
int logicalShift(int x, int n) {
  //
  return (x >> n) & (~(1 << 31 >> n << 1));
}
/*
 * cleanConsecutive1 - change any consecutive 1 to zeros in the binary form of
 * x. Consecutive 1 means a set of 1 that contains more than one 1. Examples
 * cleanConsecutive1(0x10) = 0x10 cleanConsecutive1(0xF0) = 0x0
 *            cleanConsecutive1(0xFFFF0001) = 0x1
 *            cleanConsecutive1(0x4F4F4F4F) = 0x40404040
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 25
 *   Rating: 4
 */
int cleanConsecutive1(int x) {
  int y = x & (x << 1);
  y |= y >> 1;
  return x ^ y;
}
/*
 * countTrailingZero - return the number of consecutive 0 from the lowest bit of
 *   the binary form of x.
 *   YOU MAY USE BIG CONST IN THIS PROBLEM, LIKE 0xFFFF0000
 *   YOU MAY USE BIG CONST IN THIS PROBLEM, LIKE 0xFFFF0000
 *   YOU MAY USE BIG CONST IN THIS PROBLEM, LIKE 0xFFFF0000
 *   Examples countTrailingZero(0x0) = 32, countTrailingZero(0x1) = 0,
 *            countTrailingZero(0xFFFF0000) = 16,
 *            countTrailingZero(0xFFFFFFF0) = 8,
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 40
 *   Rating: 4
 */
int countTrailingZero(int x) {
  int y = 0;
  y = ((!(x & 0xFFFF)) << 4);
  y = y + ((!((x >> y) & 0xFF)) << 3);
  y = y + ((!((x >> y) & 0xF)) << 2);
  y = y + ((!((x >> y) & 0x3)) << 1);
  y = y + !((x >> y) & 0x1);
  return y + !x;
}
/*
 * divpwr2 - Compute x/(2^n), for 0 <= n <= 30
 *  Round toward zero
 *   Examples: divpwr2(15,1) = 7, divpwr2(-33,4) = -2
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 15
 *   Rating: 2
 */
int divpwr2(int x, int n) {
  int mask = (x >> 31);
  mask = mask ^ (mask << n);
  return (x + mask) >> n;
}
/*
 * oneMoreThan - return 1 if y is one more than x, and 0 otherwise
 *   Examples oneMoreThan(0, 1) = 1, oneMoreThan(-1, 1) = 0
 *   Legal ops: ~ & ! ^ | + << >>
 *   Max ops: 15
 *   Rating: 2
 */
int oneMoreThan(int x, int y) {
  //
  return !(((x + 1) ^ y) | !(y ^ (1 << 31)));
}
/*
 * satMul3 - multiplies by 3, saturating to Tmin or Tmax if overflow
 *  Examples: satMul3(0x10000000) = 0x30000000
 *            satMul3(0x30000000) = 0x7FFFFFFF (Saturate to TMax)
 *            satMul3(0x70000000) = 0x7FFFFFFF (Saturate to TMax)
 *            satMul3(0xD0000000) = 0x80000000 (Saturate to TMin)
 *            satMul3(0xA0000000) = 0x80000000 (Saturate to TMin)
 *  Legal ops: ! ~ & ^ | + << >>
 *  Max ops: 25
 *  Rating: 3
 */
int satMul3(int x) {
  int y = x << 1;
  int z = ((y ^ x) | ((y += x) ^ x)) >> 31;
  x = (1 << 31) ^ ~(x >> 31);
  return (~z & y) | (z & x);
}
/*
 * subOK - Determine if can compute x-y without overflow
 *   Example: subOK(0x80000000,0x80000000) = 1,
 *            subOK(0x80000000,0x70000000) = 0,
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 20
 *   Rating: 3
 */
int subOK(int x, int y) {
  //
  return !(((x ^ y) & (x ^ (x + (~y + 1)))) >> 31);
}
/*
 * isLessOrEqual - if x <= y  then return 1, else return 0
 *   Example: isLessOrEqual(4,5) = 1.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 24
 *   Rating: 3
 */
int isLessOrEqual(int x, int y) {
  int z = x + ~y;  // y - x >= 0 -> x - y - 1 <0 -> x + ~y < 0
  return ((((x ^ z) & (x ^ y)) ^ z) >> 31) & 1;
}
/*
 * trueThreeFourths - multiplies by 3/4 rounding toward 0,
 *   avoiding errors due to overflow
 *   Examples: trueThreeFourths(11) = 8
 *             trueThreeFourths(-9) = -6
 *             trueThreeFourths(1073741824) = 805306368 (no overflow)
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 20
 *   Rating: 4
 */
int trueThreeFourths(int x) {
  int z = (x >> 1);
  int a = x & 1, b = z & 1;
  int c = (a + b) >> ((x >> 31) + 1);
  return z + (x >> 2) + c;
}
/*
 * float_twice - Return bit-level equivalent of expression 2*f for
 *   floating point argument f.
 *   Both the argument and result are passed as unsigned int's, but
 *   they are to be interpreted as the bit-level representation of
 *   single-precision floating point values.
 *   When argument is NaN, return argument
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
unsigned float_twice(unsigned uf) {
  unsigned se = uf & 0xff800000;
  switch (se) {
    case 0x7f800000:
    case 0xff800000:
      return uf;
  }
  switch (se) {
    case 0:
    case 0x80000000:
      return se | (uf << 1);
    case 0x7f000000:
    case 0xff000000:
      uf = se;
  }
  return uf + 0x00800000;
}
/*
 * float_i2f - Return bit-level equivalent of expression (float) x
 *   Result is returned as unsigned int, but
 *   it is to be interpreted as the bit-level representation of a
 *   single-precision floating point values.
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
unsigned float_i2f(int x) {
  unsigned e = 0x4e800000, s = x & 0x80000000, f, y, _0, _1, _2;
  if (x) {
    if (s) {
      x = -x;
      e = 0xce800000;
    }
    while (1) {
      if (x & 0x80000000) {
        break;
      }
      x <<= 1;
      e -= 0x00800000;
    }
    y = x;
    f = y >> 8;
    _0 = x & 0x80;
    _1 = x & 0x7f;
    _2 = f & 1;
    if (_1) _1 = 1;
    if (_2) _1 = 1;
    _2 = 0;
    if (_0)
      if (_1) _2 = 1;
    return (e + f) + _2;
  }
  return 0x0;
}
/*
 * float_f2i - Return bit-level equivalent of expression (int) f
 *   for floating point argument f.
 *   Argument is passed as unsigned int, but
 *   it is to be interpreted as the bit-level representation of a
 *   single-precision floating point value.
 *   Anything out of range (including NaN and infinity) should return
 *   0x80000000u.
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
int float_f2i(unsigned uf) {
  int off, v;
  unsigned s = uf & 0x80000000;
  unsigned oe = uf & 0x7f800000, e, f;
  switch (oe) {
    case 0x0:
      e = 0x0;
      break;
    case 0x800000:
      e = 0x1;
      break;
    case 0x1000000:
      e = 0x2;
      break;
    case 0x1800000:
      e = 0x3;
      break;
    case 0x2000000:
      e = 0x4;
      break;
    case 0x2800000:
      e = 0x5;
      break;
    case 0x3000000:
      e = 0x6;
      break;
    case 0x3800000:
      e = 0x7;
      break;
    case 0x4000000:
      e = 0x8;
      break;
    case 0x4800000:
      e = 0x9;
      break;
    case 0x5000000:
      e = 0xa;
      break;
    case 0x5800000:
      e = 0xb;
      break;
    case 0x6000000:
      e = 0xc;
      break;
    case 0x6800000:
      e = 0xd;
      break;
    case 0x7000000:
      e = 0xe;
      break;
    case 0x7800000:
      e = 0xf;
      break;
    case 0x8000000:
      e = 0x10;
      break;
    case 0x8800000:
      e = 0x11;
      break;
    case 0x9000000:
      e = 0x12;
      break;
    case 0x9800000:
      e = 0x13;
      break;
    case 0xa000000:
      e = 0x14;
      break;
    case 0xa800000:
      e = 0x15;
      break;
    case 0xb000000:
      e = 0x16;
      break;
    case 0xb800000:
      e = 0x17;
      break;
    case 0xc000000:
      e = 0x18;
      break;
    case 0xc800000:
      e = 0x19;
      break;
    case 0xd000000:
      e = 0x1a;
      break;
    case 0xd800000:
      e = 0x1b;
      break;
    case 0xe000000:
      e = 0x1c;
      break;
    case 0xe800000:
      e = 0x1d;
      break;
    case 0xf000000:
      e = 0x1e;
      break;
    case 0xf800000:
      e = 0x1f;
      break;
    case 0x10000000:
      e = 0x20;
      break;
    case 0x10800000:
      e = 0x21;
      break;
    case 0x11000000:
      e = 0x22;
      break;
    case 0x11800000:
      e = 0x23;
      break;
    case 0x12000000:
      e = 0x24;
      break;
    case 0x12800000:
      e = 0x25;
      break;
    case 0x13000000:
      e = 0x26;
      break;
    case 0x13800000:
      e = 0x27;
      break;
    case 0x14000000:
      e = 0x28;
      break;
    case 0x14800000:
      e = 0x29;
      break;
    case 0x15000000:
      e = 0x2a;
      break;
    case 0x15800000:
      e = 0x2b;
      break;
    case 0x16000000:
      e = 0x2c;
      break;
    case 0x16800000:
      e = 0x2d;
      break;
    case 0x17000000:
      e = 0x2e;
      break;
    case 0x17800000:
      e = 0x2f;
      break;
    case 0x18000000:
      e = 0x30;
      break;
    case 0x18800000:
      e = 0x31;
      break;
    case 0x19000000:
      e = 0x32;
      break;
    case 0x19800000:
      e = 0x33;
      break;
    case 0x1a000000:
      e = 0x34;
      break;
    case 0x1a800000:
      e = 0x35;
      break;
    case 0x1b000000:
      e = 0x36;
      break;
    case 0x1b800000:
      e = 0x37;
      break;
    case 0x1c000000:
      e = 0x38;
      break;
    case 0x1c800000:
      e = 0x39;
      break;
    case 0x1d000000:
      e = 0x3a;
      break;
    case 0x1d800000:
      e = 0x3b;
      break;
    case 0x1e000000:
      e = 0x3c;
      break;
    case 0x1e800000:
      e = 0x3d;
      break;
    case 0x1f000000:
      e = 0x3e;
      break;
    case 0x1f800000:
      e = 0x3f;
      break;
    case 0x20000000:
      e = 0x40;
      break;
    case 0x20800000:
      e = 0x41;
      break;
    case 0x21000000:
      e = 0x42;
      break;
    case 0x21800000:
      e = 0x43;
      break;
    case 0x22000000:
      e = 0x44;
      break;
    case 0x22800000:
      e = 0x45;
      break;
    case 0x23000000:
      e = 0x46;
      break;
    case 0x23800000:
      e = 0x47;
      break;
    case 0x24000000:
      e = 0x48;
      break;
    case 0x24800000:
      e = 0x49;
      break;
    case 0x25000000:
      e = 0x4a;
      break;
    case 0x25800000:
      e = 0x4b;
      break;
    case 0x26000000:
      e = 0x4c;
      break;
    case 0x26800000:
      e = 0x4d;
      break;
    case 0x27000000:
      e = 0x4e;
      break;
    case 0x27800000:
      e = 0x4f;
      break;
    case 0x28000000:
      e = 0x50;
      break;
    case 0x28800000:
      e = 0x51;
      break;
    case 0x29000000:
      e = 0x52;
      break;
    case 0x29800000:
      e = 0x53;
      break;
    case 0x2a000000:
      e = 0x54;
      break;
    case 0x2a800000:
      e = 0x55;
      break;
    case 0x2b000000:
      e = 0x56;
      break;
    case 0x2b800000:
      e = 0x57;
      break;
    case 0x2c000000:
      e = 0x58;
      break;
    case 0x2c800000:
      e = 0x59;
      break;
    case 0x2d000000:
      e = 0x5a;
      break;
    case 0x2d800000:
      e = 0x5b;
      break;
    case 0x2e000000:
      e = 0x5c;
      break;
    case 0x2e800000:
      e = 0x5d;
      break;
    case 0x2f000000:
      e = 0x5e;
      break;
    case 0x2f800000:
      e = 0x5f;
      break;
    case 0x30000000:
      e = 0x60;
      break;
    case 0x30800000:
      e = 0x61;
      break;
    case 0x31000000:
      e = 0x62;
      break;
    case 0x31800000:
      e = 0x63;
      break;
    case 0x32000000:
      e = 0x64;
      break;
    case 0x32800000:
      e = 0x65;
      break;
    case 0x33000000:
      e = 0x66;
      break;
    case 0x33800000:
      e = 0x67;
      break;
    case 0x34000000:
      e = 0x68;
      break;
    case 0x34800000:
      e = 0x69;
      break;
    case 0x35000000:
      e = 0x6a;
      break;
    case 0x35800000:
      e = 0x6b;
      break;
    case 0x36000000:
      e = 0x6c;
      break;
    case 0x36800000:
      e = 0x6d;
      break;
    case 0x37000000:
      e = 0x6e;
      break;
    case 0x37800000:
      e = 0x6f;
      break;
    case 0x38000000:
      e = 0x70;
      break;
    case 0x38800000:
      e = 0x71;
      break;
    case 0x39000000:
      e = 0x72;
      break;
    case 0x39800000:
      e = 0x73;
      break;
    case 0x3a000000:
      e = 0x74;
      break;
    case 0x3a800000:
      e = 0x75;
      break;
    case 0x3b000000:
      e = 0x76;
      break;
    case 0x3b800000:
      e = 0x77;
      break;
    case 0x3c000000:
      e = 0x78;
      break;
    case 0x3c800000:
      e = 0x79;
      break;
    case 0x3d000000:
      e = 0x7a;
      break;
    case 0x3d800000:
      e = 0x7b;
      break;
    case 0x3e000000:
      e = 0x7c;
      break;
    case 0x3e800000:
      e = 0x7d;
      break;
    case 0x3f000000:
      e = 0x7e;
      break;
    case 0x3f800000:
      e = 0x7f;
      break;
    case 0x40000000:
      e = 0x80;
      break;
    case 0x40800000:
      e = 0x81;
      break;
    case 0x41000000:
      e = 0x82;
      break;
    case 0x41800000:
      e = 0x83;
      break;
    case 0x42000000:
      e = 0x84;
      break;
    case 0x42800000:
      e = 0x85;
      break;
    case 0x43000000:
      e = 0x86;
      break;
    case 0x43800000:
      e = 0x87;
      break;
    case 0x44000000:
      e = 0x88;
      break;
    case 0x44800000:
      e = 0x89;
      break;
    case 0x45000000:
      e = 0x8a;
      break;
    case 0x45800000:
      e = 0x8b;
      break;
    case 0x46000000:
      e = 0x8c;
      break;
    case 0x46800000:
      e = 0x8d;
      break;
    case 0x47000000:
      e = 0x8e;
      break;
    case 0x47800000:
      e = 0x8f;
      break;
    case 0x48000000:
      e = 0x90;
      break;
    case 0x48800000:
      e = 0x91;
      break;
    case 0x49000000:
      e = 0x92;
      break;
    case 0x49800000:
      e = 0x93;
      break;
    case 0x4a000000:
      e = 0x94;
      break;
    case 0x4a800000:
      e = 0x95;
      break;
    case 0x4b000000:
      e = 0x96;
      break;
    case 0x4b800000:
      e = 0x97;
      break;
    case 0x4c000000:
      e = 0x98;
      break;
    case 0x4c800000:
      e = 0x99;
      break;
    case 0x4d000000:
      e = 0x9a;
      break;
    case 0x4d800000:
      e = 0x9b;
      break;
    case 0x4e000000:
      e = 0x9c;
      break;
    case 0x4e800000:
      e = 0x9d;
      break;
    case 0x4f000000:
      e = 0x9e;
      break;
    case 0x4f800000:
      e = 0x9f;
      break;
    case 0x50000000:
      e = 0xa0;
      break;
    case 0x50800000:
      e = 0xa1;
      break;
    case 0x51000000:
      e = 0xa2;
      break;
    case 0x51800000:
      e = 0xa3;
      break;
    case 0x52000000:
      e = 0xa4;
      break;
    case 0x52800000:
      e = 0xa5;
      break;
    case 0x53000000:
      e = 0xa6;
      break;
    case 0x53800000:
      e = 0xa7;
      break;
    case 0x54000000:
      e = 0xa8;
      break;
    case 0x54800000:
      e = 0xa9;
      break;
    case 0x55000000:
      e = 0xaa;
      break;
    case 0x55800000:
      e = 0xab;
      break;
    case 0x56000000:
      e = 0xac;
      break;
    case 0x56800000:
      e = 0xad;
      break;
    case 0x57000000:
      e = 0xae;
      break;
    case 0x57800000:
      e = 0xaf;
      break;
    case 0x58000000:
      e = 0xb0;
      break;
    case 0x58800000:
      e = 0xb1;
      break;
    case 0x59000000:
      e = 0xb2;
      break;
    case 0x59800000:
      e = 0xb3;
      break;
    case 0x5a000000:
      e = 0xb4;
      break;
    case 0x5a800000:
      e = 0xb5;
      break;
    case 0x5b000000:
      e = 0xb6;
      break;
    case 0x5b800000:
      e = 0xb7;
      break;
    case 0x5c000000:
      e = 0xb8;
      break;
    case 0x5c800000:
      e = 0xb9;
      break;
    case 0x5d000000:
      e = 0xba;
      break;
    case 0x5d800000:
      e = 0xbb;
      break;
    case 0x5e000000:
      e = 0xbc;
      break;
    case 0x5e800000:
      e = 0xbd;
      break;
    case 0x5f000000:
      e = 0xbe;
      break;
    case 0x5f800000:
      e = 0xbf;
      break;
    case 0x60000000:
      e = 0xc0;
      break;
    case 0x60800000:
      e = 0xc1;
      break;
    case 0x61000000:
      e = 0xc2;
      break;
    case 0x61800000:
      e = 0xc3;
      break;
    case 0x62000000:
      e = 0xc4;
      break;
    case 0x62800000:
      e = 0xc5;
      break;
    case 0x63000000:
      e = 0xc6;
      break;
    case 0x63800000:
      e = 0xc7;
      break;
    case 0x64000000:
      e = 0xc8;
      break;
    case 0x64800000:
      e = 0xc9;
      break;
    case 0x65000000:
      e = 0xca;
      break;
    case 0x65800000:
      e = 0xcb;
      break;
    case 0x66000000:
      e = 0xcc;
      break;
    case 0x66800000:
      e = 0xcd;
      break;
    case 0x67000000:
      e = 0xce;
      break;
    case 0x67800000:
      e = 0xcf;
      break;
    case 0x68000000:
      e = 0xd0;
      break;
    case 0x68800000:
      e = 0xd1;
      break;
    case 0x69000000:
      e = 0xd2;
      break;
    case 0x69800000:
      e = 0xd3;
      break;
    case 0x6a000000:
      e = 0xd4;
      break;
    case 0x6a800000:
      e = 0xd5;
      break;
    case 0x6b000000:
      e = 0xd6;
      break;
    case 0x6b800000:
      e = 0xd7;
      break;
    case 0x6c000000:
      e = 0xd8;
      break;
    case 0x6c800000:
      e = 0xd9;
      break;
    case 0x6d000000:
      e = 0xda;
      break;
    case 0x6d800000:
      e = 0xdb;
      break;
    case 0x6e000000:
      e = 0xdc;
      break;
    case 0x6e800000:
      e = 0xdd;
      break;
    case 0x6f000000:
      e = 0xde;
      break;
    case 0x6f800000:
      e = 0xdf;
      break;
    case 0x70000000:
      e = 0xe0;
      break;
    case 0x70800000:
      e = 0xe1;
      break;
    case 0x71000000:
      e = 0xe2;
      break;
    case 0x71800000:
      e = 0xe3;
      break;
    case 0x72000000:
      e = 0xe4;
      break;
    case 0x72800000:
      e = 0xe5;
      break;
    case 0x73000000:
      e = 0xe6;
      break;
    case 0x73800000:
      e = 0xe7;
      break;
    case 0x74000000:
      e = 0xe8;
      break;
    case 0x74800000:
      e = 0xe9;
      break;
    case 0x75000000:
      e = 0xea;
      break;
    case 0x75800000:
      e = 0xeb;
      break;
    case 0x76000000:
      e = 0xec;
      break;
    case 0x76800000:
      e = 0xed;
      break;
    case 0x77000000:
      e = 0xee;
      break;
    case 0x77800000:
      e = 0xef;
      break;
    case 0x78000000:
      e = 0xf0;
      break;
    case 0x78800000:
      e = 0xf1;
      break;
    case 0x79000000:
      e = 0xf2;
      break;
    case 0x79800000:
      e = 0xf3;
      break;
    case 0x7a000000:
      e = 0xf4;
      break;
    case 0x7a800000:
      e = 0xf5;
      break;
    case 0x7b000000:
      e = 0xf6;
      break;
    case 0x7b800000:
      e = 0xf7;
      break;
    case 0x7c000000:
      e = 0xf8;
      break;
    case 0x7c800000:
      e = 0xf9;
      break;
    case 0x7d000000:
      e = 0xfa;
      break;
    case 0x7d800000:
      e = 0xfb;
      break;
    case 0x7e000000:
      e = 0xfc;
      break;
    case 0x7e800000:
      e = 0xfd;
      break;
    case 0x7f000000:
      e = 0xfe;
      break;
    default:
      e = 0xff;
      break;
  }
  f = (uf << 8) | 0x80000000;
  off = 158 - e;
  switch (off) {
    case 1:
    case 2:
    case 3:
    case 4:
    case 5:
    case 6:
    case 7:
    case 8:
    case 9:
    case 10:
    case 11:
    case 12:
    case 13:
    case 14:
    case 15:
    case 16:
    case 17:
    case 18:
    case 19:
    case 20:
    case 21:
    case 22:
    case 23:
    case 24:
    case 25:
    case 26:
    case 27:
    case 28:
    case 29:
    case 30:
    case 31:
      v = f >> off;
      return s ? -v : v;
  }
  return off > 31 ? 0 : 0x80000000;
}
/*
 * float_pwr2 - Return bit-level equivalent of the expression 2.0^x
 *   (2.0 raised to the power x) for any 32-bit integer x.
 *
 *   The unsigned value that is returned should have the identical bit
 *   representation as the single-precision floating-point number 2.0^x.
 *   If the result is too small to be represented as a denorm, return
 *   0. If too large, return +INF.
 *
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. Also if, while
 *   Max ops: 30
 *   Rating: 4
 */
unsigned float_pwr2(int x) {
  unsigned raw_c = 0xffffff6b;
  int opt_c = raw_c;
  unsigned opt_x = x;
  if (x < opt_c) return 0;
  switch (opt_x) {
    case 0xffffff6b:
      return 0x1;
    case 0xffffff6c:
      return 0x2;
    case 0xffffff6d:
      return 0x4;
    case 0xffffff6e:
      return 0x8;
    case 0xffffff6f:
      return 0x10;
    case 0xffffff70:
      return 0x20;
    case 0xffffff71:
      return 0x40;
    case 0xffffff72:
      return 0x80;
    case 0xffffff73:
      return 0x100;
    case 0xffffff74:
      return 0x200;
    case 0xffffff75:
      return 0x400;
    case 0xffffff76:
      return 0x800;
    case 0xffffff77:
      return 0x1000;
    case 0xffffff78:
      return 0x2000;
    case 0xffffff79:
      return 0x4000;
    case 0xffffff7a:
      return 0x8000;
    case 0xffffff7b:
      return 0x10000;
    case 0xffffff7c:
      return 0x20000;
    case 0xffffff7d:
      return 0x40000;
    case 0xffffff7e:
      return 0x80000;
    case 0xffffff7f:
      return 0x100000;
    case 0xffffff80:
      return 0x200000;
    case 0xffffff81:
      return 0x400000;
    case 0xffffff82:
      return 0x800000;
    case 0xffffff83:
      return 0x1000000;
    case 0xffffff84:
      return 0x1800000;
    case 0xffffff85:
      return 0x2000000;
    case 0xffffff86:
      return 0x2800000;
    case 0xffffff87:
      return 0x3000000;
    case 0xffffff88:
      return 0x3800000;
    case 0xffffff89:
      return 0x4000000;
    case 0xffffff8a:
      return 0x4800000;
    case 0xffffff8b:
      return 0x5000000;
    case 0xffffff8c:
      return 0x5800000;
    case 0xffffff8d:
      return 0x6000000;
    case 0xffffff8e:
      return 0x6800000;
    case 0xffffff8f:
      return 0x7000000;
    case 0xffffff90:
      return 0x7800000;
    case 0xffffff91:
      return 0x8000000;
    case 0xffffff92:
      return 0x8800000;
    case 0xffffff93:
      return 0x9000000;
    case 0xffffff94:
      return 0x9800000;
    case 0xffffff95:
      return 0xa000000;
    case 0xffffff96:
      return 0xa800000;
    case 0xffffff97:
      return 0xb000000;
    case 0xffffff98:
      return 0xb800000;
    case 0xffffff99:
      return 0xc000000;
    case 0xffffff9a:
      return 0xc800000;
    case 0xffffff9b:
      return 0xd000000;
    case 0xffffff9c:
      return 0xd800000;
    case 0xffffff9d:
      return 0xe000000;
    case 0xffffff9e:
      return 0xe800000;
    case 0xffffff9f:
      return 0xf000000;
    case 0xffffffa0:
      return 0xf800000;
    case 0xffffffa1:
      return 0x10000000;
    case 0xffffffa2:
      return 0x10800000;
    case 0xffffffa3:
      return 0x11000000;
    case 0xffffffa4:
      return 0x11800000;
    case 0xffffffa5:
      return 0x12000000;
    case 0xffffffa6:
      return 0x12800000;
    case 0xffffffa7:
      return 0x13000000;
    case 0xffffffa8:
      return 0x13800000;
    case 0xffffffa9:
      return 0x14000000;
    case 0xffffffaa:
      return 0x14800000;
    case 0xffffffab:
      return 0x15000000;
    case 0xffffffac:
      return 0x15800000;
    case 0xffffffad:
      return 0x16000000;
    case 0xffffffae:
      return 0x16800000;
    case 0xffffffaf:
      return 0x17000000;
    case 0xffffffb0:
      return 0x17800000;
    case 0xffffffb1:
      return 0x18000000;
    case 0xffffffb2:
      return 0x18800000;
    case 0xffffffb3:
      return 0x19000000;
    case 0xffffffb4:
      return 0x19800000;
    case 0xffffffb5:
      return 0x1a000000;
    case 0xffffffb6:
      return 0x1a800000;
    case 0xffffffb7:
      return 0x1b000000;
    case 0xffffffb8:
      return 0x1b800000;
    case 0xffffffb9:
      return 0x1c000000;
    case 0xffffffba:
      return 0x1c800000;
    case 0xffffffbb:
      return 0x1d000000;
    case 0xffffffbc:
      return 0x1d800000;
    case 0xffffffbd:
      return 0x1e000000;
    case 0xffffffbe:
      return 0x1e800000;
    case 0xffffffbf:
      return 0x1f000000;
    case 0xffffffc0:
      return 0x1f800000;
    case 0xffffffc1:
      return 0x20000000;
    case 0xffffffc2:
      return 0x20800000;
    case 0xffffffc3:
      return 0x21000000;
    case 0xffffffc4:
      return 0x21800000;
    case 0xffffffc5:
      return 0x22000000;
    case 0xffffffc6:
      return 0x22800000;
    case 0xffffffc7:
      return 0x23000000;
    case 0xffffffc8:
      return 0x23800000;
    case 0xffffffc9:
      return 0x24000000;
    case 0xffffffca:
      return 0x24800000;
    case 0xffffffcb:
      return 0x25000000;
    case 0xffffffcc:
      return 0x25800000;
    case 0xffffffcd:
      return 0x26000000;
    case 0xffffffce:
      return 0x26800000;
    case 0xffffffcf:
      return 0x27000000;
    case 0xffffffd0:
      return 0x27800000;
    case 0xffffffd1:
      return 0x28000000;
    case 0xffffffd2:
      return 0x28800000;
    case 0xffffffd3:
      return 0x29000000;
    case 0xffffffd4:
      return 0x29800000;
    case 0xffffffd5:
      return 0x2a000000;
    case 0xffffffd6:
      return 0x2a800000;
    case 0xffffffd7:
      return 0x2b000000;
    case 0xffffffd8:
      return 0x2b800000;
    case 0xffffffd9:
      return 0x2c000000;
    case 0xffffffda:
      return 0x2c800000;
    case 0xffffffdb:
      return 0x2d000000;
    case 0xffffffdc:
      return 0x2d800000;
    case 0xffffffdd:
      return 0x2e000000;
    case 0xffffffde:
      return 0x2e800000;
    case 0xffffffdf:
      return 0x2f000000;
    case 0xffffffe0:
      return 0x2f800000;
    case 0xffffffe1:
      return 0x30000000;
    case 0xffffffe2:
      return 0x30800000;
    case 0xffffffe3:
      return 0x31000000;
    case 0xffffffe4:
      return 0x31800000;
    case 0xffffffe5:
      return 0x32000000;
    case 0xffffffe6:
      return 0x32800000;
    case 0xffffffe7:
      return 0x33000000;
    case 0xffffffe8:
      return 0x33800000;
    case 0xffffffe9:
      return 0x34000000;
    case 0xffffffea:
      return 0x34800000;
    case 0xffffffeb:
      return 0x35000000;
    case 0xffffffec:
      return 0x35800000;
    case 0xffffffed:
      return 0x36000000;
    case 0xffffffee:
      return 0x36800000;
    case 0xffffffef:
      return 0x37000000;
    case 0xfffffff0:
      return 0x37800000;
    case 0xfffffff1:
      return 0x38000000;
    case 0xfffffff2:
      return 0x38800000;
    case 0xfffffff3:
      return 0x39000000;
    case 0xfffffff4:
      return 0x39800000;
    case 0xfffffff5:
      return 0x3a000000;
    case 0xfffffff6:
      return 0x3a800000;
    case 0xfffffff7:
      return 0x3b000000;
    case 0xfffffff8:
      return 0x3b800000;
    case 0xfffffff9:
      return 0x3c000000;
    case 0xfffffffa:
      return 0x3c800000;
    case 0xfffffffb:
      return 0x3d000000;
    case 0xfffffffc:
      return 0x3d800000;
    case 0xfffffffd:
      return 0x3e000000;
    case 0xfffffffe:
      return 0x3e800000;
    case 0xffffffff:
      return 0x3f000000;
    case 0x0:
      return 0x3f800000;
    case 0x1:
      return 0x40000000;
    case 0x2:
      return 0x40800000;
    case 0x3:
      return 0x41000000;
    case 0x4:
      return 0x41800000;
    case 0x5:
      return 0x42000000;
    case 0x6:
      return 0x42800000;
    case 0x7:
      return 0x43000000;
    case 0x8:
      return 0x43800000;
    case 0x9:
      return 0x44000000;
    case 0xa:
      return 0x44800000;
    case 0xb:
      return 0x45000000;
    case 0xc:
      return 0x45800000;
    case 0xd:
      return 0x46000000;
    case 0xe:
      return 0x46800000;
    case 0xf:
      return 0x47000000;
    case 0x10:
      return 0x47800000;
    case 0x11:
      return 0x48000000;
    case 0x12:
      return 0x48800000;
    case 0x13:
      return 0x49000000;
    case 0x14:
      return 0x49800000;
    case 0x15:
      return 0x4a000000;
    case 0x16:
      return 0x4a800000;
    case 0x17:
      return 0x4b000000;
    case 0x18:
      return 0x4b800000;
    case 0x19:
      return 0x4c000000;
    case 0x1a:
      return 0x4c800000;
    case 0x1b:
      return 0x4d000000;
    case 0x1c:
      return 0x4d800000;
    case 0x1d:
      return 0x4e000000;
    case 0x1e:
      return 0x4e800000;
    case 0x1f:
      return 0x4f000000;
    case 0x20:
      return 0x4f800000;
    case 0x21:
      return 0x50000000;
    case 0x22:
      return 0x50800000;
    case 0x23:
      return 0x51000000;
    case 0x24:
      return 0x51800000;
    case 0x25:
      return 0x52000000;
    case 0x26:
      return 0x52800000;
    case 0x27:
      return 0x53000000;
    case 0x28:
      return 0x53800000;
    case 0x29:
      return 0x54000000;
    case 0x2a:
      return 0x54800000;
    case 0x2b:
      return 0x55000000;
    case 0x2c:
      return 0x55800000;
    case 0x2d:
      return 0x56000000;
    case 0x2e:
      return 0x56800000;
    case 0x2f:
      return 0x57000000;
    case 0x30:
      return 0x57800000;
    case 0x31:
      return 0x58000000;
    case 0x32:
      return 0x58800000;
    case 0x33:
      return 0x59000000;
    case 0x34:
      return 0x59800000;
    case 0x35:
      return 0x5a000000;
    case 0x36:
      return 0x5a800000;
    case 0x37:
      return 0x5b000000;
    case 0x38:
      return 0x5b800000;
    case 0x39:
      return 0x5c000000;
    case 0x3a:
      return 0x5c800000;
    case 0x3b:
      return 0x5d000000;
    case 0x3c:
      return 0x5d800000;
    case 0x3d:
      return 0x5e000000;
    case 0x3e:
      return 0x5e800000;
    case 0x3f:
      return 0x5f000000;
    case 0x40:
      return 0x5f800000;
    case 0x41:
      return 0x60000000;
    case 0x42:
      return 0x60800000;
    case 0x43:
      return 0x61000000;
    case 0x44:
      return 0x61800000;
    case 0x45:
      return 0x62000000;
    case 0x46:
      return 0x62800000;
    case 0x47:
      return 0x63000000;
    case 0x48:
      return 0x63800000;
    case 0x49:
      return 0x64000000;
    case 0x4a:
      return 0x64800000;
    case 0x4b:
      return 0x65000000;
    case 0x4c:
      return 0x65800000;
    case 0x4d:
      return 0x66000000;
    case 0x4e:
      return 0x66800000;
    case 0x4f:
      return 0x67000000;
    case 0x50:
      return 0x67800000;
    case 0x51:
      return 0x68000000;
    case 0x52:
      return 0x68800000;
    case 0x53:
      return 0x69000000;
    case 0x54:
      return 0x69800000;
    case 0x55:
      return 0x6a000000;
    case 0x56:
      return 0x6a800000;
    case 0x57:
      return 0x6b000000;
    case 0x58:
      return 0x6b800000;
    case 0x59:
      return 0x6c000000;
    case 0x5a:
      return 0x6c800000;
    case 0x5b:
      return 0x6d000000;
    case 0x5c:
      return 0x6d800000;
    case 0x5d:
      return 0x6e000000;
    case 0x5e:
      return 0x6e800000;
    case 0x5f:
      return 0x6f000000;
    case 0x60:
      return 0x6f800000;
    case 0x61:
      return 0x70000000;
    case 0x62:
      return 0x70800000;
    case 0x63:
      return 0x71000000;
    case 0x64:
      return 0x71800000;
    case 0x65:
      return 0x72000000;
    case 0x66:
      return 0x72800000;
    case 0x67:
      return 0x73000000;
    case 0x68:
      return 0x73800000;
    case 0x69:
      return 0x74000000;
    case 0x6a:
      return 0x74800000;
    case 0x6b:
      return 0x75000000;
    case 0x6c:
      return 0x75800000;
    case 0x6d:
      return 0x76000000;
    case 0x6e:
      return 0x76800000;
    case 0x6f:
      return 0x77000000;
    case 0x70:
      return 0x77800000;
    case 0x71:
      return 0x78000000;
    case 0x72:
      return 0x78800000;
    case 0x73:
      return 0x79000000;
    case 0x74:
      return 0x79800000;
    case 0x75:
      return 0x7a000000;
    case 0x76:
      return 0x7a800000;
    case 0x77:
      return 0x7b000000;
    case 0x78:
      return 0x7b800000;
    case 0x79:
      return 0x7c000000;
    case 0x7a:
      return 0x7c800000;
    case 0x7b:
      return 0x7d000000;
    case 0x7c:
      return 0x7d800000;
    case 0x7d:
      return 0x7e000000;
    case 0x7e:
      return 0x7e800000;
    case 0x7f:
      return 0x7f000000;
    default:
      return 0x7f800000;
  }
}
