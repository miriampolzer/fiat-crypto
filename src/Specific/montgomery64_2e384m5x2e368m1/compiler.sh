#!/bin/sh
set -eu

gcc -fno-peephole2 `#GCC BUG 81300` -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Wno-incompatible-pointer-types -fno-strict-aliasing -Dlimb_weight_gaps_array='{64,64,64,64,64,64}' -Dq_mpz='(1_mpz<<384) - 5*(1_mpz<<368) - 1' -Dlimb_t=uint64_t -Dmodulus_bytes_val='48' -Dmodulus_limbs='6' -Da_minus_two_over_four_array='{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x30,0x39}' -Dmodulus_array='{0xff,0xfa,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff}' "$@"
