// exact TM sim for 1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
// states A..F = 0..5 ; W[s][r], Dm[s][r] (+1 R,-1 L), N[s][r]; halt = -1
static const int W_[6][2]={{1,0},{0,1},{1,1},{1,0},{0,1},{0,0}};
static const int D_[6][2]={{1,0},{1,-1},{-1,-1},{1,1},{1,1},{-1,-1}};
static const int N_[6][2]={{1,-1},{2,5},{2,3},{4,0},{3,5},{3,5}};
