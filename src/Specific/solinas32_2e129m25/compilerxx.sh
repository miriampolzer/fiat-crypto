#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dlimb_weight_gaps_array='{22,21,22,21,22,21}' -Dq_mpz='(1_mpz<<129) - 25' -Dlimb_t=uint32_t -Dmodulus_bytes_val='17' -Dmodulus_limbs='6' -Da_minus_two_over_four_array='{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x30,0x39}' -Dmodulus_array='{0x01,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xe7}' "$@"
