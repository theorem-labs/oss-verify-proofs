(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *) (* Modified by Theorem Labs, 2026-10: Tfib_const_abs re-derived from libreac/fuzz_decode.asan-ubsan's own bytes: the 3 asan_globals descriptors at 0x9dbb0 (all 8 fields of each); the two cells that hold real_fopen and real_fclose are dropped (this image links neither), and so are the five zero cells 0x20e23..0x20e27, the padding after a global of cgif_file_fuzzer's own program, which here are plain image bytes no start-up or exit fact reads. TFIB_HASH and tfib_hash_buckets are recomputed with a Theorem Labs tool depot/depot.py over TFIB_TR0's moved pcs, and ts_junk's bounds are this image's page floor of .data.rel.ro (0x98000) and its page-rounded end (0x5f6000) *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0m.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Modified by Theorem Labs, 2026-10: generated for libreac/fuzz_decode image B (asan-ubsan) by af0m.py (frozen 1ea931109cf1) from a Theorem Labs lane base YF0m.v (ca2cdd36b2e); Tfib_owned_static re-derived from decode B own image (provenance/startup-gen/B/af0m, baseaudit.tsv); the 26 --add cells are image A's run_af0m.sh cells (a Theorem Labs lane 120a54c0ae1) mapped onto B by symbol / pointer-target key (adds.AtoB.tsv), less the six shadow bytes (image A carries those in Tfib_const_shadow or a Tfib_zero_shadow range) and less the two musl __atexit cells, which are not owned: target_run's post-main atexit registration rewrites slot 1 -> 2 inside the driver window (a Theorem Labs lane); 50 states (runs/B/pass2b.log), YB12, YB05, YCej universe. *)
(* Read from: fuzz_decode.asan-ubsan (libreac/fuzz_decode asan-ubsan) sha256 5d05689fd5b196976890b91e68c113953d385775b9d811ef98c712b2cac7d4a9; unstripped twin sha256 6744989bb2e66ffa4fb48e042ecedff4a3b4ba2301f43c1217e76fd1b090d0a4 *)
(* owned read-only static bytes pinned as const cells from the image: 60 bytes in 9 cells *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YF0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition TFIB_INST : Z := 0x9dcd8.      Definition TFIB_TP : Z := 0x5d42d8.       Definition TFIB_TSD : Z := 0x5f5680.
Definition TFIB_DEPOT : Z := 0x183218.     Definition TFIB_STORE : Z := 0x173208.
Definition TFIB_IAL_LO : Z := 0xa2540.    Definition TFIB_IAL_HI : Z := 0x123570.   Definition TFIB_IAL_W : Z := 0xe3300.
Definition TFIB_IAL_FLAG : Z := 0x130dc8.  Definition TFIB_OOM : Z := 0x1235a0.
Definition TFIB_MAIN : Z := 0x7fc10.      Definition TFIB_MAIN_RA : Z := 0x88700.  Definition TFIB_GP : Z := 0x10800.
Definition TFIB_ERRNO : Z := 0x5d4234.
Definition DRV_TRACES : list (list Z) :=
[[0x52250; 0x7fc64];
[0x52250; 0x7fcb8];
[0x520f0; 0x7fcdc];
[0x520f0; 0x7fe0c];
[0x52250; 0x7ff44];
[0x520f0; 0x7ffd8];
[0x520f0];
[0x52250]].
Definition Tfib_const_sym : list acell :=
[ c8 (AT 0) (AC 0); c8 (AT 8) (ATop 0); c8 (AT 16) (ATop (- kStackSpan)); z8 (AT 24) 0; z8 (AT 32) 0; z1 (AT 40) 0;
z8 (AT 48) 0x5d4a10; z8 (AT 56) 0x5d4aec; z8 (AT 64) 0x5d42e0; c8 (AT 72) (AF 0)    ;
z4 (AC 8) 0; c8 (AC 152) (AT 0);
c8 (ATsd 0) (AC 0); c8 (ATp 0) (AF 0); c8 (ATp (-88)) (ATsd 0); z8 (ATp (-8)) 0x5d42f8  ;
c8 (ATp 8) (AD 0); c8 (AD 24) (ATp 0)  ;
c8 (AInst o_space) (ASp 0); c8 (AInst o_rinfo) (ASp kRegionInfoOff); c8 (AInst o_sec_chunks) (AQ 0); c8 (AInst 80) (AQ 0) ].
Definition Tfib_const_abs : list acell :=
[
z8 (ANum 0x132e68) 0x1  ;
z8 (ANum 0x132e70) 0x0  ;
z8 (ANum 0x132e78) 0x0  ;
z8 (ANum 0x132e80) 0x13ef3  ;
z8 (ANum 0x132e88) 0x1e00010000  ;
z8 (ANum 0x132e90) 0x0  ;
z8 (ANum 0x132e98) 0x0  ;
z8 (ANum 0x132ea0) 0x0  ;
z8 (ANum 0x132ea8) 0x0  ;
z8 (ANum 0x132eb0) 0x10101000101  ;
z8 (ANum 0x132eb8) 0x100000000  ;
z8 (ANum 0x132ec0) 0x0  ;
z8 (ANum 0x132ec8) 0x0  ;
z8 (ANum 0x132ed0) 0x0  ;
z8 (ANum 0x132ed8) 0x10001  ;
z8 (ANum 0x132ee0) 18446744073709551615  ;
z8 (ANum 0x132ee8) 0x11827  ;
z8 (ANum 0x132ef0) 0x100  ;
z8 (ANum 0x132ef8) 0x0  ;
z8 (ANum 0x132f00) 0x0  ;
z8 (ANum 0x132f08) 0x0  ;
z8 (ANum 0x132f10) 0x0  ;
z8 (ANum 0x132f18) 0xffffffff00000000  ;
z8 (ANum 0x132f20) 0x1  ;
z8 (ANum 0x132f28) 0x1424f  ;
z8 (ANum 0x132f30) 0x13ef3  ;
z8 (ANum 0x132f38) 0x13ef3  ;
z8 (ANum 0x132f40) 0x10101000100  ;
z8 (ANum 0x132f48) 0x0  ;
z8 (ANum 0x132f50) 0x1d9e9  ;
z8 (ANum 0x132f58) 0x101000100000000  ;
z8 (ANum 0x132f60) 0x101010101010101  ;
z8 (ANum 0x132f68) 0x1010101  ;
z8 (ANum 0x132f70) 0x10100000001  ;
z8 (ANum 0x9eb38) 0x100ffffffff  ;
z8 (ANum 0x9eb40) 0x1000000400  ;
z8 (ANum 0x9eb48) 0x800  ;
z8 (ANum 0x9eb50) 0x101010000000001  ;
z8 (ANum 0x9eb58) 0x1400000010  ;
z8 (ANum 0x9eb60) 0x100000000000  ;
z8 (ANum 0x9eb68) 0xbe00000000  ;
z8 (ANum 0x9eb70) 0x100000055  ;
z8 (ANum 0x9eb78) 0x0  ;
z8 (ANum 0x9eb80) 0x1000100000000  ;
z8 (ANum 0x9eb88) 0x101010101000001  ;
z8 (ANum 0x9eb90) 0x1  ;
z8 (ANum 0x9eb98) 0x200000001  ;
z8 (ANum 0x9eba0) 0x13ef3  ;
z8 (ANum 0x9eba8) 0x10101  ;
z8 (ANum 0xa1338) 0x7fff8000  ;
z4 (ANum 0xa1340) 0x1  ;
z1 (ANum 0xa2018) 0x1  ;
z1 (ANum 0xa2019) 0x1  ;
z8 (ANum 0xa2020) 0x7fffffffffff  ;
z8 (ANum 0xa2028) 0x0  ;
z8 (ANum 0xa2030) 0x0  ;
z4 (ANum 0xa203c) 0x1e  ;
z1 (ANum 0xa0b9c) 0x1  ;
z1 (ANum 0xa0ba0) 0x1  ;
z4 (ANum 0xa0ba4) 0x0  ;
z1 (ANum 0x1235a1) 0x1  ;
z1 (ANum 0x1235a2) 0x0  ;
z8 (ANum 0x130de0) 0x1000  ;
z4 (ANum 0x132e5c) 0x0  ;
z8 (ANum 0x9b158) 0x9225c  ;
z8 (ANum 0x9b160) 0x92618  ;
z8 (ANum 0x9b168) 0x92a1c  ;
z8 (ANum 0x9b018) 0x925e8  ;
z8 (ANum 0x9b020) 0x92518  ;
z1 (ANum 0x132ef1) 0x1  ;
z4 (ANum 0x130dd8) 0x0  ;
z8 (ANum 0x99ff0) 0x8  ;
z8 (ANum 0x9b038) 0x97d1c  ;
z8 (ANum 0x9b040) 0x8ebcc  ;
z8 (ANum 0x9b110) 0x92ea4  ;
z8 (ANum 0x9b028) 0x9251c  ;
z1 (ANum 0x132f63) 0x1  ;
z1 (ANum 0x132ebc) 0x1  ;
z8 (ANum 0x9b058) 0x91f64  ;
z8 (ANum 0x9b060) 0x8ee54  ;
z8 (ANum 0x9b0a0) 0x9320c  ;
z8 (ANum 0x99e50) 0xa2019  ;
z8 (ANum 0x99f78) 0x9dbb0  ;
z8 (ANum 0x99f80) 0x9dc70  ;
z8 (ANum 0x9dc80) 0x1  ;
z8 (ANum 0x99fe0) 0x1  ;
z8 (ANum 0x99fe8) 0xfffffffffffff800  ;
z8 (ANum 0x173210) 0x800000  ;
z8 (ANum 0x9dce0) 0x2000011000  ;
z8 (ANum 0x9dce8) 0x16b30  ;
z8 (ANum 0x9dcf0) 0x0  ;
z8 (ANum 0x9dd00) 0xffffffff  ;
z8 (ANum 0x9dd10) 0x0  ;
z8 (ANum 0x9dd18) 0x1000  ;
z8 (ANum 0x9dd30) 0x800000  ;
z8 (ANum 0x9dd38) 0x1923c  ;
z8 (ANum 0x9dd40) 0x0  ;
z8 (ANum 0x9dff0) 0x10000000  ;
z8 (ANum 0x9dff8) 0xe666661  ;
z8 (ANum 0x9e000) 0x100000  ;
z8 (ANum 0x9eaf8) 0x10000000000  ;
z8 (ANum 0x9eb00) 0x108000010  ;
z8 (ANum 0x5d4280) 0x5f5680  ;
z8 (ANum 0x5d42d0) 0x5d42f8  ;
z8 (ANum 0x5d42f8) 0x1  ;
z8 (ANum 0x5d4300) 0x5d4ad8  ;
z8 (ANum 0x5d42e8) 0x0  ;
z8 (ANum 0x103d0) 0x218a392cd3d5dbf  ;
z8 (ANum 0x10330) 0xcc6e96b9cc6e96b9  ;
z8 (ANum 0x103b8) 0xafffff00000fffff  ;
z8 (ANum 0x102e8) 0xc6a4a7935bd1e995  ;
z8 (ANum 0x10308) 0x35253c9ade8f4ca8  ;
z8 (ANum 0x103b0) 0x9747b28c9747b28c  ;
z8 (ANum 0x99f40) 0x10  ;
z8 (ANum 0x10540) 0x13080d0307020100  ;
z8 (ANum 0x10548) 0x281422091c0e1904  ;
z8 (ANum 0x10550) 0x301d2e0f261a1105  ;
z8 (ANum 0x10558) 0x3929321536231f0a  ;
z8 (ANum 0x10560) 0x27211b18120c063f  ;
z8 (ANum 0x10568) 0x3831351e2f2d2510  ;
z8 (ANum 0x10570) 0x37342c2420170b3e  ;
z8 (ANum 0x10578) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x10440) 0x13080d0307020100  ;
z8 (ANum 0x10448) 0x281422091c0e1904  ;
z8 (ANum 0x10450) 0x301d2e0f261a1105  ;
z8 (ANum 0x10458) 0x3929321536231f0a  ;
z8 (ANum 0x10460) 0x27211b18120c063f  ;
z8 (ANum 0x10468) 0x3831351e2f2d2510  ;
z8 (ANum 0x10470) 0x37342c2420170b3e  ;
z8 (ANum 0x10478) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x132e00) 0x0  ;
z8 (ANum 0x132e08) 0x0  ;
z8 (ANum 0x132e10) 0x0  ;
z8 (ANum 0x132e18) 0x0  ;
z8 (ANum 0x132e20) 0x0  ;
z8 (ANum 0x132e28) 0x0  ;
z8 (ANum 0x132e30) 0x0  ;
z8 (ANum 0x132e38) 0x0  ;
z8 (ANum 0x132e40) 0x0  ;
z8 (ANum 0x132e48) 0x0  ;
z8 (ANum 0x992c8) 0x130de0  ;
z8 (ANum 0x992d0) 0x9b1a0  ;
z8 (ANum 0x992d8) 0x132e68  ;
z8 (ANum 0x992e0) 0x9eb38  ;
z8 (ANum 0x992e8) 0xa1338  ;
z8 (ANum 0x992f0) 0xa2028  ;
z8 (ANum 0x992f8) 0xa2030  ;
z8 (ANum 0x99300) 0xa2020  ;
z8 (ANum 0x99308) 0x9b168  ;
z8 (ANum 0x99310) 0x9b160  ;
z8 (ANum 0x99318) 0x9b198  ;
z8 (ANum 0x99320) 0x9b1b0  ;
z8 (ANum 0x99328) 0x1  ;
z8 (ANum 0x99330) 0x132e5c  ;
z8 (ANum 0x99338) 0x130dd8  ;
z8 (ANum 0x99340) 0xa1340  ;
z8 (ANum 0x9dbb0) 0x20d60  ;
z8 (ANum 0x9dbb8) 0xc  ;
z8 (ANum 0x9dbc0) 0x20  ;
z8 (ANum 0x9dbc8) 0x17ddb  ;
z8 (ANum 0x9dbd0) 0x20dc0  ;
z8 (ANum 0x9dbd8) 0x0  ;
z8 (ANum 0x9dbe0) 0x0  ;
z8 (ANum 0x9dbe8) 0x5d39c0  ;
z8 (ANum 0x9dbf0) 0x20d80  ;
z8 (ANum 0x9dbf8) 0xc  ;
z8 (ANum 0x9dc00) 0x20  ;
z8 (ANum 0x9dc08) 0x15897  ;
z8 (ANum 0x9dc10) 0x20dc0  ;
z8 (ANum 0x9dc18) 0x0  ;
z8 (ANum 0x9dc20) 0x0  ;
z8 (ANum 0x9dc28) 0x5d39c1  ;
z8 (ANum 0x9dc30) 0x20da0  ;
z8 (ANum 0x9dc38) 0xc  ;
z8 (ANum 0x9dc40) 0x20  ;
z8 (ANum 0x9dc48) 0x12d8c  ;
z8 (ANum 0x9dc50) 0x20dc0  ;
z8 (ANum 0x9dc58) 0x0  ;
z8 (ANum 0x9dc60) 0x0  ;
z8 (ANum 0x9dc68) 0x5d39c2  ;
z1 (ANum 0x1331e0) 0x0  ;
z8 (ANum 0x9ebf0) 0x0  ;
z2 (ANum 0x9e04a) 0x0  ;
z4 (ANum 0x9e04c) 0x0  ;
z1 (ANum 0x9df81) 0x0  ;
z2 (ANum 0x9df82) 0x0  ;
z4 (ANum 0x9df84) 0x0  ;
z8 (ANum 0x9b1a0) 0x1923c   ;
z8 (ANum 0x1ccb8) 0x612079726f6d656d  ;
z8 (ANum 0x1ccc0) 0x7365726464612074  ;
z4 (ANum 0x1ccc8) 0x70252073  ;
z1 (ANum 0x1cccc) 0x0  ;
z4 (ANum 0x20adc) 0x45c14  ;
z8 (ANum 0x99f88) 0x5f4318  ;
z8 (ANum 0x5f4598) 0x1000  ;
z1 (ANum 0x213a8) 0x04  ;
z1 (ANum 0x213a9) 0xff  ;
z4 (ANum 0x21344) 0x67088  ;
z1 (ANum 0x132f43) 0x1  ;
z1 (ANum 0x132f5c) 0x1  ;
z8 (ANum 0xa0b80) 0xa0b88  ;
z8 (ANum 0x9b0a8) 0x8e660  ;







z8 (ANum 0x9b010) 0x92b14
;
z8 (ANum 0x99f60) 0x20d60  ;
z8 (ANum 0x99f68) 0x20da0  ;
z8 (ANum 0x99f70) 0x20d80  ;
z8 (ANum 0x10338) 0xe38e38e38e38e38f  ;
z4 (ANum 0x9dd00) 0xffffffff  ;
z4 (ANum 0x132f1c) 0xffffffff  ;
z4 (ANum 0x132e8c) 0x1e
;
z4 (ANum 0x20d6c) 0x0  ;
z8 (ANum 0x20d70) 0x0  ;
z8 (ANum 0x20d78) 0x0  ;
z4 (ANum 0x20d8c) 0x0  ;
z8 (ANum 0x20d90) 0x0  ;
z8 (ANum 0x20d98) 0x0  ;
z4 (ANum 0x20dac) 0x0  ;
z8 (ANum 0x20db0) 0x0  ;
z8 (ANum 0x20db8) 0x0
].
Definition Tfib_const_shadow : list acell :=
[ z1 (ANum 0x7fffc1ad) 0x4  ;
z1 (ANum 0x7fffc1ae) 0xf9  ;
z1 (ANum 0x7fffc1af) 0xf9  ;
z1 (ANum 0x7fffc1b1) 0x4  ;
z1 (ANum 0x7fffc1b2) 0xf9  ;
z1 (ANum 0x7fffc1b3) 0xf9  ;
z1 (ANum 0x7fffc1b5) 0x4  ;
z1 (ANum 0x7fffc1b6) 0xf9  ;
z1 (ANum 0x7fffc1b7) 0xf9  ;
z1 (ANum 0x8000bb76) 0xf9  ;
z1 (ANum 0x8000bb77) 0xf9  ;
z1 (ANum 0x8000bb78) 0xf9  ;
z1 (ANum 0x8000bb79) 0xf9  ;
z1 (ANum 0x8000bb7a) 0xf9  ;
z1 (ANum 0x8000bb7b) 0xf9  ;
z1 (ANum 0x8000bb7c) 0xf9  ;
z1 (ANum 0x8000bb7d) 0xf9  ;
z1 (ANum 0x8000bb7e) 0xf9  ;
z1 (ANum 0x8000bb7f) 0xf9  ;
z1 (ANum 0x8000bb80) 0xf9  ;
z1 (ANum 0x8000bb81) 0xf9  ;
z1 (ANum 0x8000bb82) 0xf9  ;
z1 (ANum 0x8000bb83) 0xf9  ;
z1 (ANum 0x8000bb84) 0xf9  ;
z1 (ANum 0x8000bb85) 0xf9  ;
z1 (ANum 0x8000bb86) 0xf9  ;
z1 (ANum 0x8000bb87) 0xf9  ;
z1 (ANum 0x8000bb88) 0xf9  ;
z1 (ANum 0x8000bb89) 0xf9  ;
z1 (ANum 0x8000bb8a) 0xf9  ;
z1 (ANum 0x8000bb8b) 0xf9  ;
z1 (ANum 0x8000bb8c) 0xf9  ;
z1 (ANum 0x8000bb8d) 0xf9   ].
Definition Tfib_const (ly : alayout) : list acell := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow.
Definition Tfib_zero_shadow : list (Z * Z) :=
[ (0x10000, 0x20d68 - 0x10000); (0x20d80, 0x20d88 - 0x20d80); (0x20da0, 0x20da8 - 0x20da0); (0x20dc0, 0x9dbb0 - 0x20dc0); (0x9dc70, 0x5f6000 - 0x9dc70) ].
Definition Tfib_owned_static : list (Z * Z) :=
[ (0x9aff8, 0x2878); (0x9dbb0, 0xc0); (0x9dc80, 0x8); (0x9dcd8, 0x2eb0); (0xa0b90, 0x522e00)    ; (0x5d42d8, 0x3c)  ;
(0x992e8, 0x8); (0x99340, 0x8);
(0x102e8, 0x8); (0x10308, 0x8); (0x10330, 0x8); (0x103b0, 0x8); (0x103b8, 0x8); (0x103d0, 0x8); (0x10440, 0x40); (0x10540, 0x40);
(0x992c8, 0x20); (0x992f0, 0x18); (0x99308, 0x38); (0x99e50, 0x8); (0x99f40, 0x8); (0x99f78, 0x10); (0x99fe0, 0x10); (0x99ff0, 0x8)  ;
(0x20d6c, 0x14); (0x20d8c, 0x14); (0x20dac, 0x14); 
(0x5d4280, 0x8); (0x5d42d0, 0x8); (0x5d42e8, 0x8)  ; (0x5f5680, 0x8);
(0x1ccb8, 0x15); (0x20adc, 0x4); (0x21344, 0x4); (0x213a8, 0x2); (0x99f88, 0x8); (0x5f4598, 0x8); (0x5d39c0, 0x3) ;
(0x99f60, 8);
(0x99f68, 8);
(0x99f70, 8);
(0x10338, 8) ].
Definition TFIB_TR0 (h : nat) : list Z := match h with O => [0x3e1b4; 0x3f504] | _ => [0x3e1b4] end.
Definition TFIB_HASH (h : nat) : Z := match h with O => 9191398958145999013 | _ => 16849636616630543025 end.
Example tfib_hash_buckets : map (fun h => (TFIB_HASH h) mod d_tab_words) [0%nat; 1%nat] = [4261; 893617].
Proof. vm_compute. reflexivity. Qed.
Record TfibSyms (B : asyms) : Prop := {
ts_inst : as_inst B = TFIB_INST;
ts_tp : as_tp B = TFIB_TP;
ts_tsd : as_tsd B = TFIB_TSD;
ts_gp : as_gp B = TFIB_GP;
ts_code : as_code B = Tfib_code;
ts_errno : as_errno B = TFIB_ERRNO;
ts_depot : as_depot B = TFIB_DEPOT;
ts_store : as_store B = TFIB_STORE;
ts_ial_lo : as_ialloc_lo B = TFIB_IAL_LO;
ts_ial_hi : as_ialloc_hi B = TFIB_IAL_HI;
ts_ial_w : as_ialloc_w B = TFIB_IAL_W;
ts_ial_flag : as_ialloc_flag B = TFIB_IAL_FLAG;
ts_oom : as_oom_byte B = TFIB_OOM;
ts_ok : asyms_ok B;
ts_owned : as_owned_static B = Tfib_owned_static;
ts_const : forall ly, as_const B ly = Tfib_const ly;
ts_junk : forall ly r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 0x98000 <= z /\ z + snd r <= 0x5f6000;
ts_junk_comb : forall ly, In (ANum (TFIB_INST + o_comb_stats), 40) (as_junk B ly);
ts_junk_ly : forall ly ly', as_junk B ly' = as_junk B ly;
ts_zsh : as_zero_shadow B = Tfib_zero_shadow;
ts_universe : universe_ok (as_universe B);
ts_universe_drv : forall t, In t DRV_TRACES -> In t (as_universe B);
ts_hash : forall h, (h < 2)%nat -> (as_dhash B (TFIB_TR0 h)) mod 2 ^ 64 = TFIB_HASH h
}.
