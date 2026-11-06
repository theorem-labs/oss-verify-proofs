(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0m.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-10: regenerated for reac-pw/fuzz_qdisc image B by port-reply's af0m.py from fuzz_qdisc.asan-ubsan and its 50 collected hand-off states; base: cgif_file_fuzzer's YF0m.v (c8557374ad2e) through port_core 0e4e065eab9f's stage-out, with Tfib_owned_static relocated by object (h-small-q1) *)
(* Read from: fuzz_qdisc.asan-ubsan (reac-pw/fuzz_qdisc asan-ubsan) sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062; unstripped twin sha256 a8f38ed20eaa71da2be09efbc294ab6854786e94e1564acbf2a11cdbdf8585f1 *)
(* owned read-only static bytes pinned as const cells from the image: 247 bytes in 35 cells, from 13 ranges of Tfib_owned_static; counted from this file's own tables *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import YF0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition TFIB_INST : Z := 0x9a258.      Definition TFIB_TP : Z := 0x5d0850.       Definition TFIB_TSD : Z := 0x5f1bf8.
Definition TFIB_DEPOT : Z := 0x17f798.     Definition TFIB_STORE : Z := 0x16f788.
Definition TFIB_IAL_LO : Z := 0x9eac0.    Definition TFIB_IAL_HI : Z := 0x11faf0.   Definition TFIB_IAL_W : Z := 0xdf880.
Definition TFIB_IAL_FLAG : Z := 0x12d348.  Definition TFIB_OOM : Z := 0x11fb20.
Definition TFIB_MAIN : Z := 0x7e1f4.      Definition TFIB_MAIN_RA : Z := 0x84d1c.  Definition TFIB_GP : Z := 0x10800.
Definition TFIB_ERRNO : Z := 0x5d07ac.
Definition DRV_TRACES : list (list Z) :=
[[0x50dd0; 0x7e248]; [0x50dd0; 0x7e29c]; [0x50dd0; 0x7e528]; [0x50dd0];
[0x50c70; 0x7e2c0]; [0x50c70; 0x7e3f0]; [0x50c70; 0x7e5bc]; [0x50c70]].
Definition Tfib_const_sym : list acell :=
[ c8 (AT 0) (AC 0); c8 (AT 8) (ATop 0); c8 (AT 16) (ATop (- kStackSpan)); z8 (AT 24) 0; z8 (AT 32) 0; z1 (AT 40) 0;
z8 (AT 48) 0x5d0f88; z8 (AT 56) 0x5d1064; z8 (AT 64) 0x5d0858; c8 (AT 72) (AF 0)    ;
z4 (AC 8) 0; c8 (AC 152) (AT 0);
c8 (ATsd 0) (AC 0); c8 (ATp 0) (AF 0); c8 (ATp (-88)) (ATsd 0); z8 (ATp (-8)) 0x5d0870  ;
c8 (ATp 8) (AD 0); c8 (AD 24) (ATp 0)  ;
c8 (AInst o_space) (ASp 0); c8 (AInst o_rinfo) (ASp kRegionInfoOff); c8 (AInst o_sec_chunks) (AQ 0); c8 (AInst 80) (AQ 0) ].
(* Tfib_const_abs: 24 of its 215 rows are IN-PLACE FILLS (0-based rows 68, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 202, 203, 205, 206, 207, 208, 209): each repeats a neighbouring kept cell so that no later index moves; do not remove them *)
Definition Tfib_const_abs : list acell :=
[
z8 (ANum 0x12f3e8) 0x1  ;
z8 (ANum 0x12f3f0) 0x0  ;
z8 (ANum 0x12f3f8) 0x0  ;
z8 (ANum 0x12f400) 0x13e57  ;
z8 (ANum 0x12f408) 0x1e00010000  ;
z8 (ANum 0x12f410) 0x0  ;
z8 (ANum 0x12f418) 0x0  ;
z8 (ANum 0x12f420) 0x0  ;
z8 (ANum 0x12f428) 0x0  ;
z8 (ANum 0x12f430) 0x10101000101  ;
z8 (ANum 0x12f438) 0x100000000  ;
z8 (ANum 0x12f440) 0x0  ;
z8 (ANum 0x12f448) 0x0  ;
z8 (ANum 0x12f450) 0x0  ;
z8 (ANum 0x12f458) 0x10001  ;
z8 (ANum 0x12f460) 18446744073709551615  ;
z8 (ANum 0x12f468) 0x117ff  ;
z8 (ANum 0x12f470) 0x100  ;
z8 (ANum 0x12f478) 0x0  ;
z8 (ANum 0x12f480) 0x0  ;
z8 (ANum 0x12f488) 0x0  ;
z8 (ANum 0x12f490) 0x0  ;
z8 (ANum 0x12f498) 0xffffffff00000000  ;
z8 (ANum 0x12f4a0) 0x1  ;
z8 (ANum 0x12f4a8) 0x141b3  ;
z8 (ANum 0x12f4b0) 0x13e57  ;
z8 (ANum 0x12f4b8) 0x13e57  ;
z8 (ANum 0x12f4c0) 0x10101000100  ;
z8 (ANum 0x12f4c8) 0x0  ;
z8 (ANum 0x12f4d0) 0x1d91b  ;
z8 (ANum 0x12f4d8) 0x101000100000000  ;
z8 (ANum 0x12f4e0) 0x101010101010101  ;
z8 (ANum 0x12f4e8) 0x1010101  ;
z8 (ANum 0x12f4f0) 0x10100000001  ;
z8 (ANum 0x9b0b8) 0x100ffffffff  ;
z8 (ANum 0x9b0c0) 0x1000000400  ;
z8 (ANum 0x9b0c8) 0x800  ;
z8 (ANum 0x9b0d0) 0x101010000000001  ;
z8 (ANum 0x9b0d8) 0x1400000010  ;
z8 (ANum 0x9b0e0) 0x100000000000  ;
z8 (ANum 0x9b0e8) 0xbe00000000  ;
z8 (ANum 0x9b0f0) 0x100000055  ;
z8 (ANum 0x9b0f8) 0x0  ;
z8 (ANum 0x9b100) 0x1000100000000  ;
z8 (ANum 0x9b108) 0x101010101000001  ;
z8 (ANum 0x9b110) 0x1  ;
z8 (ANum 0x9b118) 0x200000001  ;
z8 (ANum 0x9b120) 0x13e57  ;
z8 (ANum 0x9b128) 0x10101  ;
z8 (ANum 0x9d8b8) 0x7fff8000  ;
z4 (ANum 0x9d8c0) 0x1  ;
z1 (ANum 0x9e598) 0x1  ;
z1 (ANum 0x9e599) 0x1  ;
z8 (ANum 0x9e5a0) 0x7fffffffffff  ;
z8 (ANum 0x9e5a8) 0x0  ;
z8 (ANum 0x9e5b0) 0x0  ;
z4 (ANum 0x9e5bc) 0x1e  ;
z1 (ANum 0x9d11c) 0x1  ;
z1 (ANum 0x9d120) 0x1  ;
z4 (ANum 0x9d124) 0x0  ;
z1 (ANum 0x11fb21) 0x1  ;
z1 (ANum 0x11fb22) 0x0  ;
z8 (ANum 0x12d360) 0x1000  ;
z4 (ANum 0x12f3dc) 0x0  ;
z8 (ANum 0x97750) 0x8e878  ;
z8 (ANum 0x97758) 0x8ec30  ;
z8 (ANum 0x97760) 0x8f034  ;
z8 (ANum 0x97618) 0x8ec00  ;
z8 (ANum 0x97618) 0x8ec00  (* FILL 68: duplicate of row 67 (0x97618/8), base row -: refused donor cell 0x9ff40 declared donor program data (--refused-drop) *) ;
z1 (ANum 0x12f471) 0x1  ;
z4 (ANum 0x12d358) 0x0  ;
z8 (ANum 0x965f0) 0x8  ;
z8 (ANum 0x97630) 0x94334  ;
z8 (ANum 0x97638) 0x8b1e8  ;
z8 (ANum 0x97708) 0x8f4bc  ;
z8 (ANum 0x97620) 0x8eb34  ;
z1 (ANum 0x12f4e3) 0x1  ;
z1 (ANum 0x12f43c) 0x1  ;
z8 (ANum 0x97650) 0x8e580  ;
z8 (ANum 0x97658) 0x8b470  ;
z8 (ANum 0x97698) 0x8f824  ;
z8 (ANum 0x96468) 0x9e599  ;
z8 (ANum 0x96578) 0x9a1b0  ;
z8 (ANum 0x96580) 0x9a1f0  ;
z8 (ANum 0x9a200) 0x1  ;
z8 (ANum 0x965e0) 0x1  ;
z8 (ANum 0x965e8) 0xfffffffffffff800  ;
z8 (ANum 0x16f790) 0x800000  ;
z8 (ANum 0x9a260) 0x2000011000  ;
z8 (ANum 0x9a268) 0x16a81  ;
z8 (ANum 0x9a270) 0x0  ;
z8 (ANum 0x9a280) 0xffffffff  ;
z8 (ANum 0x9a290) 0x0  ;
z8 (ANum 0x9a298) 0x1000  ;
z8 (ANum 0x9a2b0) 0x800000  ;
z8 (ANum 0x9a2b8) 0x1917e  ;
z8 (ANum 0x9a2c0) 0x0  ;
z8 (ANum 0x9a570) 0x10000000  ;
z8 (ANum 0x9a578) 0xe666661  ;
z8 (ANum 0x9a580) 0x100000  ;
z8 (ANum 0x9b078) 0x10000000000  ;
z8 (ANum 0x9b080) 0x108000010  ;
z8 (ANum 0x5d07f8) 0x5f1bf8  ;
z8 (ANum 0x5d0848) 0x5d0870  ;
z8 (ANum 0x5d0870) 0x1  ;
z8 (ANum 0x5d0878) 0x5d1050  ;
z8 (ANum 0x5d0860) 0x0  ;
z8 (ANum 0x103a8) 0x218a392cd3d5dbf  ;
z8 (ANum 0x10328) 0xcc6e96b9cc6e96b9  ;
z8 (ANum 0x10398) 0xafffff00000fffff  ;
z8 (ANum 0x102e8) 0xc6a4a7935bd1e995  ;
z8 (ANum 0x10308) 0x35253c9ade8f4ca8  ;
z8 (ANum 0x10390) 0x9747b28c9747b28c  ;
z8 (ANum 0x96558) 0x10  ;
z8 (ANum 0x10518) 0x13080d0307020100  ;
z8 (ANum 0x10520) 0x281422091c0e1904  ;
z8 (ANum 0x10528) 0x301d2e0f261a1105  ;
z8 (ANum 0x10530) 0x3929321536231f0a  ;
z8 (ANum 0x10538) 0x27211b18120c063f  ;
z8 (ANum 0x10540) 0x3831351e2f2d2510  ;
z8 (ANum 0x10548) 0x37342c2420170b3e  ;
z8 (ANum 0x10550) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x10418) 0x13080d0307020100  ;
z8 (ANum 0x10420) 0x281422091c0e1904  ;
z8 (ANum 0x10428) 0x301d2e0f261a1105  ;
z8 (ANum 0x10430) 0x3929321536231f0a  ;
z8 (ANum 0x10438) 0x27211b18120c063f  ;
z8 (ANum 0x10440) 0x3831351e2f2d2510  ;
z8 (ANum 0x10448) 0x37342c2420170b3e  ;
z8 (ANum 0x10450) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x12f380) 0x0  ;
z8 (ANum 0x12f388) 0x0  ;
z8 (ANum 0x12f390) 0x0  ;
z8 (ANum 0x12f398) 0x0  ;
z8 (ANum 0x12f3a0) 0x0  ;
z8 (ANum 0x12f3a8) 0x0  ;
z8 (ANum 0x12f3b0) 0x0  ;
z8 (ANum 0x12f3b8) 0x0  ;
z8 (ANum 0x12f3c0) 0x0  ;
z8 (ANum 0x12f3c8) 0x0  ;
z8 (ANum 0x958e0) 0x12d360  ;
z8 (ANum 0x958e8) 0x97798  ;
z8 (ANum 0x958f0) 0x12f3e8  ;
z8 (ANum 0x958f8) 0x9b0b8  ;
z8 (ANum 0x95900) 0x9d8b8  ;
z8 (ANum 0x95908) 0x9e5a8  ;
z8 (ANum 0x95910) 0x9e5b0  ;
z8 (ANum 0x95918) 0x9e5a0  ;
z8 (ANum 0x95920) 0x97760  ;
z8 (ANum 0x95928) 0x97758  ;
z8 (ANum 0x95930) 0x97790  ;
z8 (ANum 0x95938) 0x977a8  ;
z8 (ANum 0x95940) 0x1  ;
z8 (ANum 0x95948) 0x12f3dc  ;
z8 (ANum 0x95950) 0x12d358  ;
z8 (ANum 0x95958) 0x9d8c0  ;
z8 (ANum 0x9a1b0) 0x20c80  ;
z8 (ANum 0x9a1b8) 0x18  ;
z8 (ANum 0x9a1c0) 0x40  ;
z8 (ANum 0x9a1c8) 0x203fb  ;
z8 (ANum 0x9a1d0) 0x20cc0  ;
z8 (ANum 0x9a1d8) 0x0  ;
z8 (ANum 0x9a1e0) 0x0  ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 164: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b20 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 165: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b28 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 166: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b30 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 167: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b38 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 168: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b40 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 169: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b48 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 170: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b50 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 171: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b58 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 172: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b60 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 173: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b68 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 174: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b70 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 175: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b78 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 176: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b80 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 177: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b88 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 178: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b90 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1e8) 0xffffffffffffffff  (* FILL 179: duplicate of row 163 (0x9a1e8/8), base row -: refused donor descriptor word 0xa2b98 (this image has fewer descriptor words) *) ;
z1 (ANum 0x12f760) 0x0  ;
z8 (ANum 0x9b170) 0x0  ;
z2 (ANum 0x9a5ca) 0x0  ;
z4 (ANum 0x9a5cc) 0x0  ;
z1 (ANum 0x9a501) 0x0  ;
z2 (ANum 0x9a502) 0x0  ;
z4 (ANum 0x9a504) 0x0  ;
z8 (ANum 0x97798) 0x1917e   ;
z8 (ANum 0x1cbea) 0x612079726f6d656d  ;
z8 (ANum 0x1cbf2) 0x7365726464612074  ;
z4 (ANum 0x1cbfa) 0x70252073  ;
z1 (ANum 0x1cbfe) 0x0  ;
z4 (ANum 0x20a14) 0x442c0  ;
z8 (ANum 0x96588) 0x5f0890  ;
z8 (ANum 0x5f0b10) 0x1000  ;
z1 (ANum 0x212a8) 0x04  ;
z1 (ANum 0x212a9) 0xff  ;
z4 (ANum 0x21244) 0x637a4  ;
z1 (ANum 0x12f4c3) 0x1  ;
z1 (ANum 0x12f4dc) 0x1  ;
z8 (ANum 0x9d100) 0x9d108  ;
z8 (ANum 0x976a0) 0x8ac7c  ;
z8 (ANum 0x976a0) 0x8ac7c  (* FILL 202: duplicate of row 201 (0x976a0/8), base row -: refused donor cell 0x9ffd8 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x976a0) 0x8ac7c  (* FILL 203: duplicate of row 201 (0x976a0/8), base row -: refused donor cell 0x9ffc8 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x97610) 0x8f12c  ;
z8 (ANum 0x97610) 0x8f12c  (* FILL 205: duplicate of row 204 (0x97610/8), base row -: refused donor cell 0x20e23 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x97610) 0x8f12c  (* FILL 206: duplicate of row 204 (0x97610/8), base row -: refused donor cell 0x20e24 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x97610) 0x8f12c  (* FILL 207: duplicate of row 204 (0x97610/8), base row -: refused donor cell 0x20e25 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x97610) 0x8f12c  (* FILL 208: duplicate of row 204 (0x97610/8), base row -: refused donor cell 0x20e26 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x97610) 0x8f12c  (* FILL 209: duplicate of row 204 (0x97610/8), base row -: refused donor cell 0x20e27 declared donor program data (--refused-drop) *)
;
z8 (ANum 0x20c98) 0x0  ;
z8 (ANum 0x20ca0) 0x0  ;
z8 (ANum 0x20ca8) 0x0  ;
z8 (ANum 0x20cb0) 0x0  ;
z8 (ANum 0x20cb8) 0x0
].
(* Tfib_const_abs_filled: the 0-based rows of Tfib_const_abs that are IN-PLACE FILLS, each marked FILL in the list: a fill repeats a neighbouring kept cell so that no later index moves *)
Definition Tfib_const_abs_filled : list nat := [68%nat; 164%nat; 165%nat; 166%nat; 167%nat; 168%nat; 169%nat; 170%nat; 171%nat; 172%nat; 173%nat; 174%nat; 175%nat; 176%nat; 177%nat; 178%nat; 179%nat; 202%nat; 203%nat; 205%nat; 206%nat; 207%nat; 208%nat; 209%nat].

Definition Tfib_const_shadow : list acell :=
[ z1 (ANum 0x7fffc193) 0xf9  ;
z1 (ANum 0x7fffc194) 0xf9  ;
z1 (ANum 0x7fffc195) 0xf9  ;
z1 (ANum 0x7fffc196) 0xf9  ;
z1 (ANum 0x7fffc197) 0xf9  ;
z1 (ANum 0x8000b436) 0xf9  ;
z1 (ANum 0x8000b437) 0xf9  ;
z1 (ANum 0x8000b438) 0xf9  ;
z1 (ANum 0x8000b439) 0xf9  ;
z1 (ANum 0x8000b43a) 0xf9  ;
z1 (ANum 0x8000b43b) 0xf9  ;
z1 (ANum 0x8000b43c) 0xf9  ;
z1 (ANum 0x8000b43d) 0xf9   ].
Definition Tfib_const (ly : alayout) : list acell := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow.
Definition Tfib_zero_shadow : list (Z * Z) :=
[ (0x10000, 0x20c98 - 0x10000); (0x20cc0, 0x9a1b0 - 0x20cc0); (0x9a1f0, 0x5f3000 - 0x9a1f0) ].
Definition Tfib_owned_static : list (Z * Z) :=
[ (0x975f8, 0x99e68 - 0x975f8); (0x9a1b0, 0x40); (0x9a200, 8); (0x9a258, 0x9d108 - 0x9a258); (0x9d110, 0x5bff10 - 0x9d110)    ; (0x5d0850, 0x3c)  ;
(0x95900, 8); (0x95958, 8);
(0x102e8, 8); (0x10308, 8); (0x10328, 8); (0x10390, 8); (0x10398, 8); (0x103a8, 8); (0x10418, 64); (0x10518, 64);
(0x958e0, 0x20); (0x95908, 0x18); (0x95920, 0x38); (0x96468, 8); (0x96558, 8); (0x96578, 16); (0x965e0, 16); (0x965f0, 8)  ;
(0x20c98, 0x28);
(0x5d07f8, 8); (0x5d0848, 8); (0x5d0860, 8)  ; (0x5f1bf8, 8);
(0x1cbea, 21); (0x20a14, 4); (0x21244, 4); (0x212a8, 2); (0x96588, 8); (0x5f0b10, 8) ].
Definition TFIB_TR0 (h : nat) : list Z := match h with O => [0x3d4d4; 0x3e824] | _ => [0x3d4d4] end.
Definition TFIB_HASH (h : nat) : Z := match h with O => 4127892674883565242 | _ => 4174579939647801621 end.
Example tfib_hash_buckets : map (fun h => (TFIB_HASH h) mod d_tab_words) [0%nat; 1%nat] = [997050; 903445].
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
ts_junk : forall ly r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 0x95000 <= z /\ z + snd r <= 0x5f3000;
ts_junk_comb : forall ly, In (ANum (TFIB_INST + o_comb_stats), 40) (as_junk B ly);
ts_junk_ly : forall ly ly', as_junk B ly' = as_junk B ly;
ts_zsh : as_zero_shadow B = Tfib_zero_shadow;
ts_universe : universe_ok (as_universe B);
ts_universe_drv : forall t, In t DRV_TRACES -> In t (as_universe B);
ts_hash : forall h, (h < 2)%nat -> (as_dhash B (TFIB_TR0 h)) mod 2 ^ 64 = TFIB_HASH h
}.
