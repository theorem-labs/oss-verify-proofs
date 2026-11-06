(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0m.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-10: regenerated for reac-pw/fuzz_qdisc image A by port-reply's af0m.py from fuzz_qdisc.asan and its 50 collected hand-off states; base: cgif_file_fuzzer's A/AF0m.v (c8557374ad2e) through port_core 0e4e065eab9f's stage-out, with Tfib_owned_static relocated by object (h-small-a3) *)
(* Read from: fuzz_qdisc.asan (reac-pw/fuzz_qdisc asan) sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e; unstripped twin sha256 d77ead7cec5c42ebc28aff0443565f333cbb4dd08f5f1101d3deb805d5e34aac *)
(* owned read-only static bytes pinned as const cells from the image: 247 bytes in 35 cells, from 13 ranges of Tfib_owned_static; counted from this file's own tables *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AF0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition TFIB_INST : Z := 0x9a218.      Definition TFIB_TP : Z := 0x5d0810.       Definition TFIB_TSD : Z := 0x5f1bb8.
Definition TFIB_DEPOT : Z := 0x17f758.     Definition TFIB_STORE : Z := 0x16f748.
Definition TFIB_IAL_LO : Z := 0x9ea80.    Definition TFIB_IAL_HI : Z := 0x11fab0.   Definition TFIB_IAL_W : Z := 0xdf840.
Definition TFIB_IAL_FLAG : Z := 0x12d308.  Definition TFIB_OOM : Z := 0x11fae0.
Definition TFIB_MAIN : Z := 0x7e1ec.      Definition TFIB_MAIN_RA : Z := 0x84ce4.  Definition TFIB_GP : Z := 0x10800.
Definition TFIB_ERRNO : Z := 0x5d076c.
Definition DRV_TRACES : list (list Z) :=
[[0x50dc8; 0x7e240]; [0x50dc8; 0x7e294]; [0x50dc8; 0x7e520]; [0x50dc8];
[0x50c68; 0x7e2b8]; [0x50c68; 0x7e3e8]; [0x50c68; 0x7e5b4]; [0x50c68]].
Definition Tfib_const_sym : list acell :=
[ c8 (AT 0) (AC 0); c8 (AT 8) (ATop 0); c8 (AT 16) (ATop (- kStackSpan)); z8 (AT 24) 0; z8 (AT 32) 0; z1 (AT 40) 0;
z8 (AT 48) 0x5d0f48; z8 (AT 56) 0x5d1024; z8 (AT 64) 0x5d0818; c8 (AT 72) (AF 0)    ;
z4 (AC 8) 0; c8 (AC 152) (AT 0);
c8 (ATsd 0) (AC 0); c8 (ATp 0) (AF 0); c8 (ATp (-88)) (ATsd 0); z8 (ATp (-8)) 0x5d0830  ;
c8 (ATp 8) (AD 0); c8 (AD 24) (ATp 0)  ;
c8 (AInst o_space) (ASp 0); c8 (AInst o_rinfo) (ASp kRegionInfoOff); c8 (AInst o_sec_chunks) (AQ 0); c8 (AInst 80) (AQ 0) ].
(* Tfib_const_abs: 24 of its 215 rows are IN-PLACE FILLS (0-based rows 68, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 202, 203, 205, 206, 207, 208, 209): each repeats a neighbouring kept cell so that no later index moves; do not remove them *)
Definition Tfib_const_abs : list acell :=
[
z8 (ANum 0x12f3a8) 0x1  ;
z8 (ANum 0x12f3b0) 0x0  ;
z8 (ANum 0x12f3b8) 0x0  ;
z8 (ANum 0x12f3c0) 0x13e57  ;
z8 (ANum 0x12f3c8) 0x1e00010000  ;
z8 (ANum 0x12f3d0) 0x0  ;
z8 (ANum 0x12f3d8) 0x0  ;
z8 (ANum 0x12f3e0) 0x0  ;
z8 (ANum 0x12f3e8) 0x0  ;
z8 (ANum 0x12f3f0) 0x10101000101  ;
z8 (ANum 0x12f3f8) 0x100000000  ;
z8 (ANum 0x12f400) 0x0  ;
z8 (ANum 0x12f408) 0x0  ;
z8 (ANum 0x12f410) 0x0  ;
z8 (ANum 0x12f418) 0x10001  ;
z8 (ANum 0x12f420) 18446744073709551615  ;
z8 (ANum 0x12f428) 0x117ff  ;
z8 (ANum 0x12f430) 0x100  ;
z8 (ANum 0x12f438) 0x0  ;
z8 (ANum 0x12f440) 0x0  ;
z8 (ANum 0x12f448) 0x0  ;
z8 (ANum 0x12f450) 0x0  ;
z8 (ANum 0x12f458) 0xffffffff00000000  ;
z8 (ANum 0x12f460) 0x1  ;
z8 (ANum 0x12f468) 0x141b3  ;
z8 (ANum 0x12f470) 0x13e57  ;
z8 (ANum 0x12f478) 0x13e57  ;
z8 (ANum 0x12f480) 0x10101000100  ;
z8 (ANum 0x12f488) 0x0  ;
z8 (ANum 0x12f490) 0x1d91b  ;
z8 (ANum 0x12f498) 0x101000100000000  ;
z8 (ANum 0x12f4a0) 0x101010101010101  ;
z8 (ANum 0x12f4a8) 0x1010101  ;
z8 (ANum 0x12f4b0) 0x10100000001  ;
z8 (ANum 0x9b078) 0x100ffffffff  ;
z8 (ANum 0x9b080) 0x1000000400  ;
z8 (ANum 0x9b088) 0x800  ;
z8 (ANum 0x9b090) 0x101010000000001  ;
z8 (ANum 0x9b098) 0x1400000010  ;
z8 (ANum 0x9b0a0) 0x100000000000  ;
z8 (ANum 0x9b0a8) 0xbe00000000  ;
z8 (ANum 0x9b0b0) 0x100000055  ;
z8 (ANum 0x9b0b8) 0x0  ;
z8 (ANum 0x9b0c0) 0x1000100000000  ;
z8 (ANum 0x9b0c8) 0x101010101000001  ;
z8 (ANum 0x9b0d0) 0x1  ;
z8 (ANum 0x9b0d8) 0x200000001  ;
z8 (ANum 0x9b0e0) 0x13e57  ;
z8 (ANum 0x9b0e8) 0x10101  ;
z8 (ANum 0x9d878) 0x7fff8000  ;
z4 (ANum 0x9d880) 0x1  ;
z1 (ANum 0x9e558) 0x1  ;
z1 (ANum 0x9e559) 0x1  ;
z8 (ANum 0x9e560) 0x7fffffffffff  ;
z8 (ANum 0x9e568) 0x0  ;
z8 (ANum 0x9e570) 0x0  ;
z4 (ANum 0x9e57c) 0x1e  ;
z1 (ANum 0x9d0dc) 0x1  ;
z1 (ANum 0x9d0e0) 0x1  ;
z4 (ANum 0x9d0e4) 0x0  ;
z1 (ANum 0x11fae1) 0x1  ;
z1 (ANum 0x11fae2) 0x0  ;
z8 (ANum 0x12d320) 0x1000  ;
z4 (ANum 0x12f39c) 0x0  ;
z8 (ANum 0x97718) 0x8e840  ;
z8 (ANum 0x97720) 0x8ebf8  ;
z8 (ANum 0x97728) 0x8effc  ;
z8 (ANum 0x975e0) 0x8ebc8  ;
z8 (ANum 0x975e0) 0x8ebc8  (* FILL 68: duplicate of row 67 (0x975e0/8), base row -: refused donor cell 0x9fcd0 declared donor program data (--refused-drop) *) ;
z1 (ANum 0x12f431) 0x1  ;
z4 (ANum 0x12d318) 0x0  ;
z8 (ANum 0x965b8) 0x8  ;
z8 (ANum 0x975f8) 0x942fc  ;
z8 (ANum 0x97600) 0x8b1b0  ;
z8 (ANum 0x976d0) 0x8f484  ;
z8 (ANum 0x975e8) 0x8eafc  ;
z1 (ANum 0x12f4a3) 0x1  ;
z1 (ANum 0x12f3fc) 0x1  ;
z8 (ANum 0x97618) 0x8e548  ;
z8 (ANum 0x97620) 0x8b438  ;
z8 (ANum 0x97660) 0x8f7ec  ;
z8 (ANum 0x96430) 0x9e559  ;
z8 (ANum 0x96540) 0x9a170  ;
z8 (ANum 0x96548) 0x9a1b0  ;
z8 (ANum 0x9a1c0) 0x1  ;
z8 (ANum 0x965a8) 0x1  ;
z8 (ANum 0x965b0) 0xfffffffffffff800  ;
z8 (ANum 0x16f750) 0x800000  ;
z8 (ANum 0x9a220) 0x2000011000  ;
z8 (ANum 0x9a228) 0x16a81  ;
z8 (ANum 0x9a230) 0x0  ;
z8 (ANum 0x9a240) 0xffffffff  ;
z8 (ANum 0x9a250) 0x0  ;
z8 (ANum 0x9a258) 0x1000  ;
z8 (ANum 0x9a270) 0x800000  ;
z8 (ANum 0x9a278) 0x1917e  ;
z8 (ANum 0x9a280) 0x0  ;
z8 (ANum 0x9a530) 0x10000000  ;
z8 (ANum 0x9a538) 0xe666661  ;
z8 (ANum 0x9a540) 0x100000  ;
z8 (ANum 0x9b038) 0x10000000000  ;
z8 (ANum 0x9b040) 0x108000010  ;
z8 (ANum 0x5d07b8) 0x5f1bb8  ;
z8 (ANum 0x5d0808) 0x5d0830  ;
z8 (ANum 0x5d0830) 0x1  ;
z8 (ANum 0x5d0838) 0x5d1010  ;
z8 (ANum 0x5d0820) 0x0  ;
z8 (ANum 0x103a8) 0x218a392cd3d5dbf  ;
z8 (ANum 0x10328) 0xcc6e96b9cc6e96b9  ;
z8 (ANum 0x10398) 0xafffff00000fffff  ;
z8 (ANum 0x102e8) 0xc6a4a7935bd1e995  ;
z8 (ANum 0x10308) 0x35253c9ade8f4ca8  ;
z8 (ANum 0x10390) 0x9747b28c9747b28c  ;
z8 (ANum 0x96520) 0x10  ;
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
z8 (ANum 0x12f340) 0x0  ;
z8 (ANum 0x12f348) 0x0  ;
z8 (ANum 0x12f350) 0x0  ;
z8 (ANum 0x12f358) 0x0  ;
z8 (ANum 0x12f360) 0x0  ;
z8 (ANum 0x12f368) 0x0  ;
z8 (ANum 0x12f370) 0x0  ;
z8 (ANum 0x12f378) 0x0  ;
z8 (ANum 0x12f380) 0x0  ;
z8 (ANum 0x12f388) 0x0  ;
z8 (ANum 0x958a8) 0x12d320  ;
z8 (ANum 0x958b0) 0x97760  ;
z8 (ANum 0x958b8) 0x12f3a8  ;
z8 (ANum 0x958c0) 0x9b078  ;
z8 (ANum 0x958c8) 0x9d878  ;
z8 (ANum 0x958d0) 0x9e568  ;
z8 (ANum 0x958d8) 0x9e570  ;
z8 (ANum 0x958e0) 0x9e560  ;
z8 (ANum 0x958e8) 0x97728  ;
z8 (ANum 0x958f0) 0x97720  ;
z8 (ANum 0x958f8) 0x97758  ;
z8 (ANum 0x95900) 0x97770  ;
z8 (ANum 0x95908) 0x1  ;
z8 (ANum 0x95910) 0x12f39c  ;
z8 (ANum 0x95918) 0x12d318  ;
z8 (ANum 0x95920) 0x9d880  ;
z8 (ANum 0x9a170) 0x20c80  ;
z8 (ANum 0x9a178) 0x18  ;
z8 (ANum 0x9a180) 0x40  ;
z8 (ANum 0x9a188) 0x203fb  ;
z8 (ANum 0x9a190) 0x20cc0  ;
z8 (ANum 0x9a198) 0x0  ;
z8 (ANum 0x9a1a0) 0x0  ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 164: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28b0 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 165: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28b8 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 166: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28c0 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 167: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28c8 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 168: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28d0 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 169: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28d8 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 170: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28e0 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 171: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28e8 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 172: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28f0 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 173: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa28f8 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 174: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa2900 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 175: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa2908 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 176: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa2910 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 177: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa2918 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 178: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa2920 (this image has fewer descriptor words) *) ;
z8 (ANum 0x9a1a8) 0xffffffffffffffff  (* FILL 179: duplicate of row 163 (0x9a1a8/8), base row -: refused donor descriptor word 0xa2928 (this image has fewer descriptor words) *) ;
z1 (ANum 0x12f720) 0x0  ;
z8 (ANum 0x9b130) 0x0  ;
z2 (ANum 0x9a58a) 0x0  ;
z4 (ANum 0x9a58c) 0x0  ;
z1 (ANum 0x9a4c1) 0x0  ;
z2 (ANum 0x9a4c2) 0x0  ;
z4 (ANum 0x9a4c4) 0x0  ;
z8 (ANum 0x97760) 0x1917e   ;
z8 (ANum 0x1cbea) 0x612079726f6d656d  ;
z8 (ANum 0x1cbf2) 0x7365726464612074  ;
z4 (ANum 0x1cbfa) 0x70252073  ;
z1 (ANum 0x1cbfe) 0x0  ;
z4 (ANum 0x20a14) 0x442b8  ;
z8 (ANum 0x96550) 0x5f0850  ;
z8 (ANum 0x5f0ad0) 0x1000  ;
z1 (ANum 0x212a8) 0x04  ;
z1 (ANum 0x212a9) 0xff  ;
z4 (ANum 0x21244) 0x6376c  ;
z1 (ANum 0x12f483) 0x1  ;
z1 (ANum 0x12f49c) 0x1  ;
z8 (ANum 0x9d0c0) 0x9d0c8  ;
z8 (ANum 0x97668) 0x8ac44  ;
z8 (ANum 0x97668) 0x8ac44  (* FILL 202: duplicate of row 201 (0x97668/8), base row -: refused donor cell 0x9fd68 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x97668) 0x8ac44  (* FILL 203: duplicate of row 201 (0x97668/8), base row -: refused donor cell 0x9fd58 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x975d8) 0x8f0f4  ;
z8 (ANum 0x975d8) 0x8f0f4  (* FILL 205: duplicate of row 204 (0x975d8/8), base row -: refused donor cell 0x20e63 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x975d8) 0x8f0f4  (* FILL 206: duplicate of row 204 (0x975d8/8), base row -: refused donor cell 0x20e64 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x975d8) 0x8f0f4  (* FILL 207: duplicate of row 204 (0x975d8/8), base row -: refused donor cell 0x20e65 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x975d8) 0x8f0f4  (* FILL 208: duplicate of row 204 (0x975d8/8), base row -: refused donor cell 0x20e66 declared donor program data (--refused-drop) *) ;
z8 (ANum 0x975d8) 0x8f0f4  (* FILL 209: duplicate of row 204 (0x975d8/8), base row -: refused donor cell 0x20e67 declared donor program data (--refused-drop) *)
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
z1 (ANum 0x8000b42e) 0xf9  ;
z1 (ANum 0x8000b42f) 0xf9  ;
z1 (ANum 0x8000b430) 0xf9  ;
z1 (ANum 0x8000b431) 0xf9  ;
z1 (ANum 0x8000b432) 0xf9  ;
z1 (ANum 0x8000b433) 0xf9  ;
z1 (ANum 0x8000b434) 0xf9  ;
z1 (ANum 0x8000b435) 0xf9   ].
Definition Tfib_const (ly : alayout) : list acell := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow.
Definition Tfib_zero_shadow : list (Z * Z) :=
[ (0x10000, 0x20c98 - 0x10000); (0x20cc0, 0x9a170 - 0x20cc0); (0x9a1b0, 0x5f3000 - 0x9a1b0) ].
Definition Tfib_owned_static : list (Z * Z) :=
[ (0x975c0, 0x99e30 - 0x975c0); (0x9a170, 0x40); (0x9a1c0, 8); (0x9a218, 0x9d0c8 - 0x9a218); (0x9d0d0, 0x5bfed0 - 0x9d0d0)    ; (0x5d0810, 0x3c)  ;
(0x958c8, 8); (0x95920, 8);
(0x102e8, 8); (0x10308, 8); (0x10328, 8); (0x10390, 8); (0x10398, 8); (0x103a8, 8); (0x10418, 64); (0x10518, 64);
(0x958a8, 0x20); (0x958d0, 0x18); (0x958e8, 0x38); (0x96430, 8); (0x96520, 8); (0x96540, 16); (0x965a8, 16); (0x965b8, 8)  ;
(0x20c98, 0x28);
(0x5d07b8, 8); (0x5d0808, 8); (0x5d0820, 8)  ; (0x5f1bb8, 8);
(0x1cbea, 21); (0x20a14, 4); (0x21244, 4); (0x212a8, 2); (0x96550, 8); (0x5f0ad0, 8) ].
Definition TFIB_TR0 (h : nat) : list Z := match h with O => [0x3d4cc; 0x3e81c] | _ => [0x3d4cc] end.
Definition TFIB_HASH (h : nat) : Z := match h with O => 18169775612004528600 | _ => 12256442056595753099 end.
Example tfib_hash_buckets : map (fun h => (TFIB_HASH h) mod d_tab_words) [0%nat; 1%nat] = [389592; 805003].
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
