/**
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 *
 * Zisu Zhang
 * 2100012732
 * MIT License
 */
#include <stdio.h>

#include "cachelab.h"
#include "contracts.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);
void trans_32_32(int M, int N, int A[N][M], int B[M][N]);
void trans_64_64(int M, int N, int A[N][M], int B[M][N]);
void trans_60_68(int M, int N, int A[N][M], int B[M][N]);

/*
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. The REQUIRES and ENSURES from 15-122 are included
 *     for your convenience. They can be removed if you like.
 */
char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N]) {
  if (M == 64 && N == 64) return trans_64_64(M, N, A, B);
  if (M == 60 && N == 68) return trans_60_68(M, N, A, B);
  return trans_32_32(M, N, A, B);
}

/*
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started.
 */

/**
 * trans_32_32 - This is the solution for 32x32 matrix transpose
 *   We use 8x8 block to transpose the matrix.
 *   First, copy the 8x8 block from A to B,
 *   then transpose the 8x8 block in B.
 */
void trans_32_32(int M, int N, int A[N][M], int B[M][N]) {
  int a0, a1, a2, a3, a4, a5, a6, a7;
  for (int bi = 0; bi < N; bi += 8) {
    for (int bj = 0; bj < M; bj += 8) {
      for (int oi = 0; oi < 8; oi++) {
        a0 = A[bi + oi][bj + 0];
        a1 = A[bi + oi][bj + 1];
        a2 = A[bi + oi][bj + 2];
        a3 = A[bi + oi][bj + 3];
        a4 = A[bi + oi][bj + 4];
        a5 = A[bi + oi][bj + 5];
        a6 = A[bi + oi][bj + 6];
        a7 = A[bi + oi][bj + 7];
        B[bj + oi][bi + 0] = a0;
        B[bj + oi][bi + 1] = a1;
        B[bj + oi][bi + 2] = a2;
        B[bj + oi][bi + 3] = a3;
        B[bj + oi][bi + 4] = a4;
        B[bj + oi][bi + 5] = a5;
        B[bj + oi][bi + 6] = a6;
        B[bj + oi][bi + 7] = a7;
      }
      for (int oi = 0; oi < 8; oi++) {
        for (int oj = 0; oj < oi; oj++) {
          a0 = B[bj + oi][bi + oj];
          B[bj + oi][bi + oj] = B[bj + oj][bi + oi];
          B[bj + oj][bi + oi] = a0;
        }
      }
    }
  }
}

/**
 * trans_64_64 - This is the solution for 64x64 matrix transpose
 *   We also use 8x8 block to transpose the matrix.
 *   However, instead of copying the 8x8 block from A to B and then transpose,
 *   we applied a more complicated algorithm, which divides the 8x8 block into
 *   four 4x4 sub-block and transpose within/between them separately.
 */
void trans_64_64(int M, int N, int A[N][M], int B[M][N]) {
  int a0, a1, a2, a3, a4, a5, a6, a7;
  int bi, bj, i, j;
  for (bi = 0; bi < N; bi += 8) {
    for (bj = 0; bj < M; bj += 8) {
      if (bi == bj) {
        for (i = 0; i < 4; i++) {
          a0 = A[bi + i][bj];
          a1 = A[bi + i][bj + 1];
          a2 = A[bi + i][bj + 2];
          a3 = A[bi + i][bj + 3];
          a4 = A[bi + i][bj + 4];
          a5 = A[bi + i][bj + 5];
          a6 = A[bi + i][bj + 6];
          a7 = A[bi + i][bj + 7];
          B[bj + i][bi] = a0;
          B[bj + i][bi + 1] = a1;
          B[bj + i][bi + 2] = a2;
          B[bj + i][bi + 3] = a3;
          B[bj + i][bi + 4] = a4;
          B[bj + i][bi + 5] = a5;
          B[bj + i][bi + 6] = a6;
          B[bj + i][bi + 7] = a7;
        }
        for (i = 0; i < 4; i++) {
          for (j = 0; j < i; j++) {
            a0 = B[bj + j][bi + i];
            B[bj + j][bi + i] = B[bj + i][bi + j];
            B[bj + i][bi + j] = a0;
          }
        }
        for (i = 4; i < 8; i++) {
          a0 = A[bi + i][bj];
          a1 = A[bi + i][bj + 1];
          a2 = A[bi + i][bj + 2];
          a3 = A[bi + i][bj + 3];
          a4 = A[bi + i][bj + 4];
          a5 = A[bi + i][bj + 5];
          a6 = A[bi + i][bj + 6];
          a7 = A[bi + i][bj + 7];
          B[bj + i][bi] = a0;
          B[bj + i][bi + 1] = a1;
          B[bj + i][bi + 2] = a2;
          B[bj + i][bi + 3] = a3;
          B[bj + i][bi + 4] = a4;
          B[bj + i][bi + 5] = a5;
          B[bj + i][bi + 6] = a6;
          B[bj + i][bi + 7] = a7;
        }
        for (i = 4; i < 8; i++) {
          for (j = 4; j < i; j++) {
            a0 = B[bj + j][bi + i];
            B[bj + j][bi + i] = B[bj + i][bi + j];
            B[bj + i][bi + j] = a0;
          }
        }
        a0 = B[bj + 4][bi];
        a1 = B[bj + 4][bi + 1];
        a2 = B[bj + 4][bi + 2];
        a3 = B[bj + 4][bi + 3];
        a4 = B[bj + 5][bi];
        a5 = B[bj + 5][bi + 1];
        a6 = B[bj + 5][bi + 2];
        a7 = B[bj + 5][bi + 3];
        i = B[bj][bi + 4];
        B[bj][bi + 4] = a0;
        a0 = i;
        i = B[bj + 1][bi + 4];
        B[bj + 1][bi + 4] = a1;
        a1 = i;
        i = B[bj + 2][bi + 4];
        B[bj + 2][bi + 4] = a2;
        a2 = i;
        i = B[bj + 3][bi + 4];
        B[bj + 3][bi + 4] = a3;
        a3 = i;
        i = B[bj][bi + 5];
        B[bj][bi + 5] = a4;
        a4 = i;
        i = B[bj + 1][bi + 5];
        B[bj + 1][bi + 5] = a5;
        a5 = i;
        i = B[bj + 2][bi + 5];
        B[bj + 2][bi + 5] = a6;
        a6 = i;
        i = B[bj + 3][bi + 5];
        B[bj + 3][bi + 5] = a7;
        a7 = i;
        B[bj + 4][bi] = a0;
        B[bj + 4][bi + 1] = a1;
        B[bj + 4][bi + 2] = a2;
        B[bj + 4][bi + 3] = a3;
        B[bj + 5][bi] = a4;
        B[bj + 5][bi + 1] = a5;
        B[bj + 5][bi + 2] = a6;
        B[bj + 5][bi + 3] = a7;
        a0 = B[bj + 6][bi];
        a1 = B[bj + 6][bi + 1];
        a2 = B[bj + 6][bi + 2];
        a3 = B[bj + 6][bi + 3];
        a4 = B[bj + 7][bi];
        a5 = B[bj + 7][bi + 1];
        a6 = B[bj + 7][bi + 2];
        a7 = B[bj + 7][bi + 3];
        i = B[bj][bi + 6];
        B[bj][bi + 6] = a0;
        a0 = i;
        i = B[bj + 1][bi + 6];
        B[bj + 1][bi + 6] = a1;
        a1 = i;
        i = B[bj + 2][bi + 6];
        B[bj + 2][bi + 6] = a2;
        a2 = i;
        i = B[bj + 3][bi + 6];
        B[bj + 3][bi + 6] = a3;
        a3 = i;
        i = B[bj][bi + 7];
        B[bj][bi + 7] = a4;
        a4 = i;
        i = B[bj + 1][bi + 7];
        B[bj + 1][bi + 7] = a5;
        a5 = i;
        i = B[bj + 2][bi + 7];
        B[bj + 2][bi + 7] = a6;
        a6 = i;
        i = B[bj + 3][bi + 7];
        B[bj + 3][bi + 7] = a7;
        a7 = i;
        B[bj + 6][bi] = a0;
        B[bj + 6][bi + 1] = a1;
        B[bj + 6][bi + 2] = a2;
        B[bj + 6][bi + 3] = a3;
        B[bj + 7][bi] = a4;
        B[bj + 7][bi + 1] = a5;
        B[bj + 7][bi + 2] = a6;
        B[bj + 7][bi + 3] = a7;
      } else {
        for (i = 0; i < 4; i++) {
          for (j = 0; j < 4; j++) {
            B[bj + j][bi + i] = A[bi + i][bj + j];
          }
        }
        a0 = A[bi][bj + 4];
        a1 = A[bi][bj + 5];
        a2 = A[bi][bj + 6];
        a3 = A[bi][bj + 7];
        a4 = A[bi + 1][bj + 4];
        a5 = A[bi + 1][bj + 5];
        a6 = A[bi + 1][bj + 6];
        a7 = A[bi + 1][bj + 7];
        for (i = 4; i < 8; i++) {
          for (j = 0; j < 4; j++) {
            B[bj + j][bi + i] = A[bi + i][bj + j];
          }
        }
        for (i = 4; i < 8; i++) {
          for (j = 4; j < 8; j++) {
            B[bj + j][bi + i] = A[bi + i][bj + j];
          }
        }
        for (i = 2; i < 4; i++) {
          for (j = 4; j < 8; j++) {
            B[bj + j][bi + i] = A[bi + i][bj + j];
          }
        }
        B[bj + 4][bi] = a0;
        B[bj + 5][bi] = a1;
        B[bj + 6][bi] = a2;
        B[bj + 7][bi] = a3;
        B[bj + 4][bi + 1] = a4;
        B[bj + 5][bi + 1] = a5;
        B[bj + 6][bi + 1] = a6;
        B[bj + 7][bi + 1] = a7;
      }
    }
  }
}

/**
 * trans_60_68 - This is the solution for 60x68 matrix transpose
 *   Kinda like trans_32_32, but we slowly transpose the rest cells
 *   that are not in the 56x64 block.
 */
void trans_60_68(int M, int N, int A[N][M], int B[M][N]) {
  int a0, a1, a2, a3, a4, a5, a6, a7;
  for (int bi = 0; bi < N; bi += 8) {
    for (int bj = 0; bj < M; bj += 8) {
      if (bi + 8 <= N && bj + 8 <= M) {
        for (int oi = 0; oi < 8; oi++) {
          a0 = A[bi + oi][bj + 0];
          a1 = A[bi + oi][bj + 1];
          a2 = A[bi + oi][bj + 2];
          a3 = A[bi + oi][bj + 3];
          a4 = A[bi + oi][bj + 4];
          a5 = A[bi + oi][bj + 5];
          a6 = A[bi + oi][bj + 6];
          a7 = A[bi + oi][bj + 7];
          B[bj + oi][bi + 0] = a0;
          B[bj + oi][bi + 1] = a1;
          B[bj + oi][bi + 2] = a2;
          B[bj + oi][bi + 3] = a3;
          B[bj + oi][bi + 4] = a4;
          B[bj + oi][bi + 5] = a5;
          B[bj + oi][bi + 6] = a6;
          B[bj + oi][bi + 7] = a7;
        }
        for (int oi = 0; oi < 8; oi++) {
          for (int oj = 0; oj < oi; oj++) {
            a0 = B[bj + oi][bi + oj];
            B[bj + oi][bi + oj] = B[bj + oj][bi + oi];
            B[bj + oj][bi + oi] = a0;
          }
        }
      } else {
        for (int i = bi; i < bi + 8 && i < N; i++) {
          for (int j = bj; j < bj + 8 && j < M; j++) {
            if (i == j) {
              a0 = A[i][i];
            } else {
              B[j][i] = A[i][j];
            }
          }
          if (bi == bj) {
            B[i][i] = a0;
          }
        }
      }
    }
  }
}

/*
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N]) {
  int i, j, tmp;

  REQUIRES(M > 0);
  REQUIRES(N > 0);

  for (i = 0; i < N; i++) {
    for (j = 0; j < M; j++) {
      tmp = A[i][j];
      B[j][i] = tmp;
    }
  }

  ENSURES(is_transpose(M, N, A, B));
}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions() {
  /* Register your solution function */
  registerTransFunction(transpose_submit, transpose_submit_desc);

  /* Register any additional transpose functions */
  registerTransFunction(trans, trans_desc);
}

/*
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N]) {
  int i, j;

  for (i = 0; i < N; i++) {
    for (j = 0; j < M; ++j) {
      if (A[i][j] != B[j][i]) {
        return 0;
      }
    }
  }
  return 1;
}
