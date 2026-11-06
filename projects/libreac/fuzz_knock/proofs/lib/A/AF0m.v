(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0m.v, with its module paths changed and its constant tables regenerated from libreac/fuzz_knock's asan image: addresses relocated, the asan_globals descriptors, the global-redzone shadow and the cells of code knock does not link (real_bcmp, real_fopen, real_fclose) removed, the asan_globals GOT words and the registration flag set to 0, one zero-shadow range, and the start-up trace and hashes recomputed (a Theorem Labs lane). INTERIM copy for type-checks only, NOT acceptance: a Theorem Labs lane's start-up tool generates the final file; knock registers no globals, so its start-up depot is empty at main: TFIB_TR0, TFIB_HASH, tfib_hash_buckets and the TfibSyms field ts_hash (cgif's start-up trace from __asan_register_globals) are removed; the stackStore+8 cell (0x170410) is 0 on knock's pin (asan sha256 61768cf4739b..., all 50 start-up states, a Theorem Labs lane's generator), not cgif's 0x800000. *)
(* Modified by Theorem Labs, 2026-10: A/AF0m.v regenerated for fuzz_knock.asan by af0m.py from the image and the 50 collected hand-off states *)
(* Read from: fuzz_knock.asan (libreac/fuzz_knock asan) sha256 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118; unstripped twin sha256 fff563b309575a57ef583abcb12d652ce77bc65f8952edd8dd93464602cbea25 *)
(* owned read-only static bytes pinned as const cells from the image: 207 bytes in 30 cells, from 12 ranges of Tfib_owned_static; counted from this file's own tables *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AF0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition TFIB_INST : Z := 0x9aed8.      Definition TFIB_TP : Z := 0x5d14d0.       Definition TFIB_TSD : Z := 0x5f2878.
Definition TFIB_DEPOT : Z := 0x180418.     Definition TFIB_STORE : Z := 0x170408.
Definition TFIB_IAL_LO : Z := 0x9f740.    Definition TFIB_IAL_HI : Z := 0x120770.   Definition TFIB_IAL_W : Z := 0xe0500.
Definition TFIB_IAL_FLAG : Z := 0x12dfc8.  Definition TFIB_OOM : Z := 0x1207a0.
Definition TFIB_MAIN : Z := 0x7ea30.      Definition TFIB_MAIN_RA : Z := 0x859f4.  Definition TFIB_GP : Z := 0x10800.
Definition TFIB_ERRNO : Z := 0x5d142c.
Definition DRV_TRACES : list (list Z) :=
[[0x514ac; 0x7eafc];
[0x514ac; 0x7ec2c];
[0x5160c; 0x7ea84];
[0x5160c; 0x7ead8];
[0x514ac; 0x7edf8];
[0x5160c; 0x7ed64];
[0x514ac];
[0x5160c]].
Definition Tfib_const_sym : list acell :=
[ c8 (AT 0) (AC 0); c8 (AT 8) (ATop 0); c8 (AT 16) (ATop (- kStackSpan)); z8 (AT 24) 0; z8 (AT 32) 0; z1 (AT 40) 0;
z8 (AT 48) 0x5d1c08; z8 (AT 56) 0x5d1ce4; z8 (AT 64) 0x5d14d8; c8 (AT 72) (AF 0)    ;
z4 (AC 8) 0; c8 (AC 152) (AT 0);
c8 (ATsd 0) (AC 0); c8 (ATp 0) (AF 0); c8 (ATp (-88)) (ATsd 0); z8 (ATp (-8)) 0x5d14f0  ;
c8 (ATp 8) (AD 0); c8 (AD 24) (ATp 0)  ;
c8 (AInst o_space) (ASp 0); c8 (AInst o_rinfo) (ASp kRegionInfoOff); c8 (AInst o_sec_chunks) (AQ 0); c8 (AInst 80) (AQ 0) ].
Definition Tfib_const_abs : list acell :=
[
z8 (ANum 0x130068) 0x1  ;
z8 (ANum 0x130070) 0x0  ;
z8 (ANum 0x130078) 0x0  ;
z8 (ANum 0x130080) 0x13e4f  ;
z8 (ANum 0x130088) 0x1e00010000  ;
z8 (ANum 0x130090) 0x0  ;
z8 (ANum 0x130098) 0x0  ;
z8 (ANum 0x1300a0) 0x0  ;
z8 (ANum 0x1300a8) 0x0  ;
z8 (ANum 0x1300b0) 0x10101000101  ;
z8 (ANum 0x1300b8) 0x100000000  ;
z8 (ANum 0x1300c0) 0x0  ;
z8 (ANum 0x1300c8) 0x0  ;
z8 (ANum 0x1300d0) 0x0  ;
z8 (ANum 0x1300d8) 0x10001  ;
z8 (ANum 0x1300e0) 18446744073709551615  ;
z8 (ANum 0x1300e8) 0x117f7  ;
z8 (ANum 0x1300f0) 0x100  ;
z8 (ANum 0x1300f8) 0x0  ;
z8 (ANum 0x130100) 0x0  ;
z8 (ANum 0x130108) 0x0  ;
z8 (ANum 0x130110) 0x0  ;
z8 (ANum 0x130118) 0xffffffff00000000  ;
z8 (ANum 0x130120) 0x1  ;
z8 (ANum 0x130128) 0x141ab  ;
z8 (ANum 0x130130) 0x13e4f  ;
z8 (ANum 0x130138) 0x13e4f  ;
z8 (ANum 0x130140) 0x10101000100  ;
z8 (ANum 0x130148) 0x0  ;
z8 (ANum 0x130150) 0x1d913  ;
z8 (ANum 0x130158) 0x101000100000000  ;
z8 (ANum 0x130160) 0x101010101010101  ;
z8 (ANum 0x130168) 0x1010101  ;
z8 (ANum 0x130170) 0x10100000001  ;
z8 (ANum 0x9bd38) 0x100ffffffff  ;
z8 (ANum 0x9bd40) 0x1000000400  ;
z8 (ANum 0x9bd48) 0x800  ;
z8 (ANum 0x9bd50) 0x101010000000001  ;
z8 (ANum 0x9bd58) 0x1400000010  ;
z8 (ANum 0x9bd60) 0x100000000000  ;
z8 (ANum 0x9bd68) 0xbe00000000  ;
z8 (ANum 0x9bd70) 0x100000055  ;
z8 (ANum 0x9bd78) 0x0  ;
z8 (ANum 0x9bd80) 0x1000100000000  ;
z8 (ANum 0x9bd88) 0x101010101000001  ;
z8 (ANum 0x9bd90) 0x1  ;
z8 (ANum 0x9bd98) 0x200000001  ;
z8 (ANum 0x9bda0) 0x13e4f  ;
z8 (ANum 0x9bda8) 0x10101  ;
z8 (ANum 0x9e538) 0x7fff8000  ;
z4 (ANum 0x9e540) 0x1  ;
z1 (ANum 0x9f218) 0x1  ;
z1 (ANum 0x9f219) 0x1  ;
z8 (ANum 0x9f220) 0x7fffffffffff  ;
z8 (ANum 0x9f228) 0x0  ;
z8 (ANum 0x9f230) 0x0  ;
z4 (ANum 0x9f23c) 0x1e  ;
z1 (ANum 0x9dd9c) 0x1  ;
z1 (ANum 0x9dda0) 0x1  ;
z4 (ANum 0x9dda4) 0x0  ;
z1 (ANum 0x1207a1) 0x1  ;
z1 (ANum 0x1207a2) 0x0  ;
z8 (ANum 0x12dfe0) 0x1000  ;
z4 (ANum 0x13005c) 0x0  ;
z8 (ANum 0x98420) 0x8f550  ;
z8 (ANum 0x98428) 0x8f908  ;
z8 (ANum 0x98430) 0x8fd0c  ;
z8 (ANum 0x982e8) 0x8f8d8  ;
z1 (ANum 0x1300f1) 0x1  ;
z4 (ANum 0x12dfd8) 0x0  ;
z8 (ANum 0x972c0) 0x8  ;
z8 (ANum 0x98300) 0x9500c  ;
z8 (ANum 0x98308) 0x8bec0  ;
z8 (ANum 0x983d8) 0x90194  ;
z8 (ANum 0x982f0) 0x8f80c  ;
z1 (ANum 0x130163) 0x1  ;
z1 (ANum 0x1300bc) 0x1  ;
z8 (ANum 0x98320) 0x8f258  ;
z8 (ANum 0x98328) 0x8c148  ;
z8 (ANum 0x98368) 0x904fc  ;
z8 (ANum 0x97138) 0x9f219  ;
z8 (ANum 0x97248) 0x0  ;
z8 (ANum 0x97250) 0x0  ;
z8 (ANum 0x9ae80) 0x0  ;
z8 (ANum 0x972b0) 0x1  ;
z8 (ANum 0x972b8) 0xfffffffffffff800  ;
ACell (ANum 0x170410) 0 (AV (ANum 0))  ;
z8 (ANum 0x9aee0) 0x2000011000  ;
z8 (ANum 0x9aee8) 0x16a79  ;
z8 (ANum 0x9aef0) 0x0  ;
z8 (ANum 0x9af00) 0xffffffff  ;
z8 (ANum 0x9af10) 0x0  ;
z8 (ANum 0x9af18) 0x1000  ;
z8 (ANum 0x9af30) 0x800000  ;
z8 (ANum 0x9af38) 0x19176  ;
z8 (ANum 0x9af40) 0x0  ;
z8 (ANum 0x9b1f0) 0x10000000  ;
z8 (ANum 0x9b1f8) 0xe666661  ;
z8 (ANum 0x9b200) 0x100000  ;
z8 (ANum 0x9bcf8) 0x10000000000  ;
z8 (ANum 0x9bd00) 0x108000010  ;
z8 (ANum 0x5d1478) 0x5f2878  ;
z8 (ANum 0x5d14c8) 0x5d14f0  ;
z8 (ANum 0x5d14f0) 0x1  ;
z8 (ANum 0x5d14f8) 0x5d1cd0  ;
z8 (ANum 0x5d14e0) 0x0  ;
z8 (ANum 0x103a0) 0x218a392cd3d5dbf  ;
z8 (ANum 0x10318) 0xcc6e96b9cc6e96b9  ;
z8 (ANum 0x10390) 0xafffff00000fffff  ;
z8 (ANum 0x102d8) 0xc6a4a7935bd1e995  ;
z8 (ANum 0x102f8) 0x35253c9ade8f4ca8  ;
z8 (ANum 0x10388) 0x9747b28c9747b28c  ;
z8 (ANum 0x97228) 0x10  ;
z8 (ANum 0x10510) 0x13080d0307020100  ;
z8 (ANum 0x10518) 0x281422091c0e1904  ;
z8 (ANum 0x10520) 0x301d2e0f261a1105  ;
z8 (ANum 0x10528) 0x3929321536231f0a  ;
z8 (ANum 0x10530) 0x27211b18120c063f  ;
z8 (ANum 0x10538) 0x3831351e2f2d2510  ;
z8 (ANum 0x10540) 0x37342c2420170b3e  ;
z8 (ANum 0x10548) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x10410) 0x13080d0307020100  ;
z8 (ANum 0x10418) 0x281422091c0e1904  ;
z8 (ANum 0x10420) 0x301d2e0f261a1105  ;
z8 (ANum 0x10428) 0x3929321536231f0a  ;
z8 (ANum 0x10430) 0x27211b18120c063f  ;
z8 (ANum 0x10438) 0x3831351e2f2d2510  ;
z8 (ANum 0x10440) 0x37342c2420170b3e  ;
z8 (ANum 0x10448) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x130000) 0x0  ;
z8 (ANum 0x130008) 0x0  ;
z8 (ANum 0x130010) 0x0  ;
z8 (ANum 0x130018) 0x0  ;
z8 (ANum 0x130020) 0x0  ;
z8 (ANum 0x130028) 0x0  ;
z8 (ANum 0x130030) 0x0  ;
z8 (ANum 0x130038) 0x0  ;
z8 (ANum 0x130040) 0x0  ;
z8 (ANum 0x130048) 0x0  ;
z8 (ANum 0x965b0) 0x12dfe0  ;
z8 (ANum 0x965b8) 0x98468  ;
z8 (ANum 0x965c0) 0x130068  ;
z8 (ANum 0x965c8) 0x9bd38  ;
z8 (ANum 0x965d0) 0x9e538  ;
z8 (ANum 0x965d8) 0x9f228  ;
z8 (ANum 0x965e0) 0x9f230  ;
z8 (ANum 0x965e8) 0x9f220  ;
z8 (ANum 0x965f0) 0x98430  ;
z8 (ANum 0x965f8) 0x98428  ;
z8 (ANum 0x96600) 0x98460  ;
z8 (ANum 0x96608) 0x98478  ;
z8 (ANum 0x96610) 0x1  ;
z8 (ANum 0x96618) 0x13005c  ;
z8 (ANum 0x96620) 0x12dfd8  ;
z8 (ANum 0x96628) 0x9e540  ;
z1 (ANum 0x1303e0) 0x0  ;
z8 (ANum 0x9bdf0) 0x0  ;
z2 (ANum 0x9b24a) 0x0  ;
z4 (ANum 0x9b24c) 0x0  ;
z1 (ANum 0x9b181) 0x0  ;
z2 (ANum 0x9b182) 0x0  ;
z4 (ANum 0x9b184) 0x0  ;
z8 (ANum 0x98468) 0x19176   ;
z8 (ANum 0x1cbe2) 0x612079726f6d656d  ;
z8 (ANum 0x1cbea) 0x7365726464612074  ;
z4 (ANum 0x1cbf2) 0x70252073  ;
z1 (ANum 0x1cbf6) 0x0  ;
z4 (ANum 0x20a00) 0x44b10  ;
z8 (ANum 0x97258) 0x5f1510  ;
z8 (ANum 0x5f1790) 0x1000  ;
z1 (ANum 0x21240) 0x04  ;
z1 (ANum 0x21241) 0xff  ;
z4 (ANum 0x211dc) 0x644e4  ;
z1 (ANum 0x130143) 0x1  ;
z1 (ANum 0x13015c) 0x1  ;
z8 (ANum 0x9dd80) 0x9dd88  ;
z8 (ANum 0x98370) 0x8b954  ;
z8 (ANum 0x982e0) 0x8fe04
].
Definition Tfib_const_shadow : list acell :=
[    ].
Definition Tfib_const (ly : alayout) : list acell := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow.
Definition Tfib_zero_shadow : list (Z * Z) :=
[ (YImgTop.IMG_LO, YImgTop.IMG_TOP - YImgTop.IMG_LO) ].
Definition Tfib_owned_static : list (Z * Z) :=
[ (0x982c8, 0x9ab38 - 0x982c8); (0x9ae80, 8); (0x9aed8, 0x9dd88 - 0x9aed8); (0x9dd90, 0x5c0b90 - 0x9dd90)    ; (0x5d14d0, 0x3c)  ;
(0x965d0, 8); (0x96628, 8);
(0x102d8, 8); (0x102f8, 8); (0x10318, 8); (0x10388, 8); (0x10390, 8); (0x103a0, 8); (0x10410, 64); (0x10510, 64);
(0x965b0, 0x20); (0x965d8, 0x18); (0x965f0, 0x38); (0x97138, 8); (0x97228, 8); (0x97248, 16); (0x972b0, 16); (0x972c0, 8)  ;
(0x5d1478, 8); (0x5d14c8, 8); (0x5d14e0, 8)  ; (0x5f2878, 8);
(0x1cbe2, 21); (0x20a00, 4); (0x211dc, 4); (0x21240, 2); (0x97258, 8); (0x5f1790, 8) ].
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
ts_junk : forall ly r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 0x96000 <= z /\ z + snd r <= YImgTop.IMG_TOP;
ts_junk_comb : forall ly, In (ANum (TFIB_INST + o_comb_stats), 40) (as_junk B ly);
ts_junk_ly : forall ly ly', as_junk B ly' = as_junk B ly;
ts_zsh : as_zero_shadow B = Tfib_zero_shadow;
ts_universe : universe_ok (as_universe B);
ts_universe_drv : forall t, In t DRV_TRACES -> In t (as_universe B)
}.
