(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the start-up facts that lib/B/Prog/IdentEntryLink.v keeps open for
   libreac/fuzz_identity's ASan+UBSan build (image B): GM, IV, ZS_STEM, ZS_NAME, HUMM, HUMF and HUMB. The checks and
   their lemmas are fuzz_grant's (proofs/libreac/fuzz_grant/lib/A/Prog/GrantCloseChk.v :19-151 and GrantClose.v
   :200-287 at d110b9a519a: zfind, vscan, vscan_ok, is_shc, is_shv, le_byte1, in_zs_of_b, grant_shadow_cell,
   grant_zs_rd, grant_img_shadow_vis, grant_globs_marked, grant_zs_ROW), with module paths changed, the glob check
   relaxed (glob_chk_r below) and the universe checks (hum_chk, humb_chk) added. *)
(* No function is proved here: each lemma is a fact of the start-up data. The B core's record is ReusableB/YD2l.v:12
   IdentB (the AD2l twin); in this file, as in lib/B/IdentHimgOwned.v, the record is a Section Variable and each
   of its fields that a proof reads enters as a premise of the form that record meets by eq_refl:
     LAWS   : AR_laws SEGS IdentB                                    (the closer's AR_laws_ok)
     HZS    : as_zero_shadow IdentB = StartupB.Tfib_zero_shadow      (record: as_zero_shadow := Tfib_zero_shadow)
     HCONST : forall ly, as_const IdentB ly = StartupB.Tfib_const ly (record: as_const := Tfib_const; TfibSyms ts_const)
     HUNIV  : as_universe IdentB = StartupB.Tfib_universe            (record: as_universe := Tfib_universe)
     HMRA   : pc_malloc_ra0 (as_code IdentB) = 0x52eb0               (record: as_code := Tfib_code)
     HFRA   : pc_free_ra0 (as_code IdentB) = 0x52d50
   Each lemma takes only the premises its proof reads. Computation runs on closed terms only: vm_compute of a
   boolean check over the copied tables and the link's closed lists, then `reflexivity`. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the start-up tables of record, VERBATIM ------------------------------------------------------------------
   From the start-up branch of record (first copied from an earlier commit; the later one appends one row at the END of
   Tfib_const_abs, `z8 (ANum 0x9e390) 0x94f50`, real_strlen), the B start-up set at the release paths:
   - projects/libreac/fuzz_identity/proofs/lib/ReusableB/YF0m.v
     lines 29-1577 (byte-equal to the copy below; the file's header lines have changed since the copy): Tfib_const_sym,
     Tfib_const_abs, Tfib_const_shadow, Tfib_const and Tfib_zero_shadow;
   - projects/libreac/fuzz_identity/proofs/lib/ReusableB/YCej.v
     lines 223-249 (byte-equal to the copy below; the file's header lines have changed since the copy): Tfib_universe.
   Copied when neither file was in this tree (both are in it now). YF0m.v requires lib/ReusableB/YF0l.v, which the earlier commit does
   not carry. The names are kept. The copy sits in its own module, after only the Requires that YF0m.v makes itself,
   so each name in it resolves as it does there. The B core is in this tree: its record IdentB (ReusableB/YD2l.v:12)
   meets HZS, HCONST and HUNIV by eq_refl (IdentTopB.v:169-171), since these copies equal its tables (:32-36). *)
Module StartupB.
Definition Tfib_const_sym : list acell :=
[ c8 (AT 0) (AC 0); c8 (AT 8) (ATop 0); c8 (AT 16) (ATop (- kStackSpan)); z8 (AT 24) 0; z8 (AT 32) 0; z1 (AT 40) 0;
z8 (AT 48) 0x5d8988; z8 (AT 56) 0x5d8a64; z8 (AT 64) 0x5d8258; c8 (AT 72) (AF 0)    ;
z4 (AC 8) 0; c8 (AC 152) (AT 0);
c8 (ATsd 0) (AC 0); c8 (ATp 0) (AF 0); c8 (ATp (-88)) (ATsd 0); z8 (ATp (-8)) 0x5d8270  ;
c8 (ATp 8) (AD 0); c8 (AD 24) (ATp 0)  ;
c8 (AInst o_space) (ASp 0); c8 (AInst o_rinfo) (ASp kRegionInfoOff); c8 (AInst o_sec_chunks) (AQ 0); c8 (AInst 80) (AQ 0) ].
Definition Tfib_const_abs : list acell :=
[
z8 (ANum 0x136de8) 0x1  ;
z8 (ANum 0x136df0) 0x0  ;
z8 (ANum 0x136df8) 0x0  ;
z8 (ANum 0x136e00) 0x13fb9  ;
z8 (ANum 0x136e08) 0x1e00010000  ;
z8 (ANum 0x136e10) 0x0  ;
z8 (ANum 0x136e18) 0x0  ;
z8 (ANum 0x136e20) 0x0  ;
z8 (ANum 0x136e28) 0x0  ;
z8 (ANum 0x136e30) 0x10101000101  ;
z8 (ANum 0x136e38) 0x100000000  ;
z8 (ANum 0x136e40) 0x0  ;
z8 (ANum 0x136e48) 0x0  ;
z8 (ANum 0x136e50) 0x0  ;
z8 (ANum 0x136e58) 0x10001  ;
z8 (ANum 0x136e60) 18446744073709551615  ;
z8 (ANum 0x136e68) 0x11847  ;
z8 (ANum 0x136e70) 0x100  ;
z8 (ANum 0x136e78) 0x0  ;
z8 (ANum 0x136e80) 0x0  ;
z8 (ANum 0x136e88) 0x0  ;
z8 (ANum 0x136e90) 0x0  ;
z8 (ANum 0x136e98) 0xffffffff00000000  ;
z8 (ANum 0x136ea0) 0x1  ;
z8 (ANum 0x136ea8) 0x14315  ;
z8 (ANum 0x136eb0) 0x13fb9  ;
z8 (ANum 0x136eb8) 0x13fb9  ;
z8 (ANum 0x136ec0) 0x10101000100  ;
z8 (ANum 0x136ec8) 0x0  ;
z8 (ANum 0x136ed0) 0x1dbeb  ;
z8 (ANum 0x136ed8) 0x101000100000000  ;
z8 (ANum 0x136ee0) 0x101010101010101  ;
z8 (ANum 0x136ee8) 0x1010101  ;
z8 (ANum 0x136ef0) 0x10100000001  ;
z8 (ANum 0xa2ab8) 0x100ffffffff  ;
z8 (ANum 0xa2ac0) 0x1000000400  ;
z8 (ANum 0xa2ac8) 0x800  ;
z8 (ANum 0xa2ad0) 0x101010000000001  ;
z8 (ANum 0xa2ad8) 0x1400000010  ;
z8 (ANum 0xa2ae0) 0x100000000000  ;
z8 (ANum 0xa2ae8) 0xbe00000000  ;
z8 (ANum 0xa2af0) 0x100000055  ;
z8 (ANum 0xa2af8) 0x0  ;
z8 (ANum 0xa2b00) 0x1000100000000  ;
z8 (ANum 0xa2b08) 0x101010101000001  ;
z8 (ANum 0xa2b10) 0x1  ;
z8 (ANum 0xa2b18) 0x200000001  ;
z8 (ANum 0xa2b20) 0x13fb9  ;
z8 (ANum 0xa2b28) 0x10101  ;
z8 (ANum 0xa52b8) 0x7fff8000  ;
z4 (ANum 0xa52c0) 0x1  ;
z1 (ANum 0xa5f98) 0x1  ;
z1 (ANum 0xa5f99) 0x1  ;
z8 (ANum 0xa5fa0) 0x7fffffffffff  ;
z8 (ANum 0xa5fa8) 0x0  ;
z8 (ANum 0xa5fb0) 0x0  ;
z4 (ANum 0xa5fbc) 0x1e  ;
z1 (ANum 0xa4b1c) 0x1  ;
z1 (ANum 0xa4b20) 0x1  ;
z4 (ANum 0xa4b24) 0x0  ;
z1 (ANum 0x127521) 0x1  ;
z1 (ANum 0x127522) 0x0  ;
z8 (ANum 0x134d60) 0x1000  ;
z4 (ANum 0x136ddc) 0x0  ;
z8 (ANum 0x9e4e8) 0x94544  ;
z8 (ANum 0x9e4f0) 0x94900  ;
z8 (ANum 0x9e4f8) 0x94d04  ;
z8 (ANum 0x9e3a8) 0x948d0  ;
z8 (ANum 0x9e3b0) 0x94800  ;
z1 (ANum 0x136e71) 0x1  ;
z4 (ANum 0x134d58) 0x0  ;
z8 (ANum 0x9d380) 0x8  ;
z8 (ANum 0x9e3c8) 0x9a004  ;
z8 (ANum 0x9e3d0) 0x90eb4  ;
z8 (ANum 0x9e4a0) 0x9518c  ;
z8 (ANum 0x9e3b8) 0x94804  ;
z1 (ANum 0x136ee3) 0x1  ;
z1 (ANum 0x136e3c) 0x1  ;
z8 (ANum 0x9e3e8) 0x9424c  ;
z8 (ANum 0x9e3f0) 0x9113c  ;
z8 (ANum 0x9e430) 0x954f4  ;
z8 (ANum 0x9d1f8) 0xa5f99  ;
z8 (ANum 0x9d308) 0xa0f40  ;
z8 (ANum 0x9d310) 0xa1c00  ;
z8 (ANum 0xa1c00) 0x1  ;
z8 (ANum 0x9d370) 0x1  ;
z8 (ANum 0x9d378) 0xfffffffffffff800  ;
z8 (ANum 0x177190) 0x800000  ;
z8 (ANum 0xa1c60) 0x2000011000  ;
z8 (ANum 0xa1c68) 0x16c2e  ;
z8 (ANum 0xa1c70) 0x0  ;
z8 (ANum 0xa1c80) 0xffffffff  ;
z8 (ANum 0xa1c90) 0x0  ;
z8 (ANum 0xa1c98) 0x1000  ;
z8 (ANum 0xa1cb0) 0x800000  ;
z8 (ANum 0xa1cb8) 0x1938d  ;
z8 (ANum 0xa1cc0) 0x0  ;
z8 (ANum 0xa1f70) 0x10000000  ;
z8 (ANum 0xa1f78) 0xe666661  ;
z8 (ANum 0xa1f80) 0x100000  ;
z8 (ANum 0xa2a78) 0x10000000000  ;
z8 (ANum 0xa2a80) 0x108000010  ;
z8 (ANum 0x5d81f8) 0x5f95f8  ;
z8 (ANum 0x5d8248) 0x5d8270  ;
z8 (ANum 0x5d8270) 0x1  ;
z8 (ANum 0x5d8278) 0x5d8a50  ;
z8 (ANum 0x5d8260) 0x0  ;
z8 (ANum 0x103b8) 0x218a392cd3d5dbf  ;
z8 (ANum 0x10328) 0xcc6e96b9cc6e96b9  ;
z8 (ANum 0x103a8) 0xafffff00000fffff  ;
z8 (ANum 0x102e8) 0xc6a4a7935bd1e995  ;
z8 (ANum 0x10308) 0x35253c9ade8f4ca8  ;
z8 (ANum 0x103a0) 0x9747b28c9747b28c  ;
z8 (ANum 0x9d2e8) 0x10  ;
z8 (ANum 0x10528) 0x13080d0307020100  ;
z8 (ANum 0x10530) 0x281422091c0e1904  ;
z8 (ANum 0x10538) 0x301d2e0f261a1105  ;
z8 (ANum 0x10540) 0x3929321536231f0a  ;
z8 (ANum 0x10548) 0x27211b18120c063f  ;
z8 (ANum 0x10550) 0x3831351e2f2d2510  ;
z8 (ANum 0x10558) 0x37342c2420170b3e  ;
z8 (ANum 0x10560) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x10428) 0x13080d0307020100  ;
z8 (ANum 0x10430) 0x281422091c0e1904  ;
z8 (ANum 0x10438) 0x301d2e0f261a1105  ;
z8 (ANum 0x10440) 0x3929321536231f0a  ;
z8 (ANum 0x10448) 0x27211b18120c063f  ;
z8 (ANum 0x10450) 0x3831351e2f2d2510  ;
z8 (ANum 0x10458) 0x37342c2420170b3e  ;
z8 (ANum 0x10460) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x136d80) 0x0  ;
z8 (ANum 0x136d88) 0x0  ;
z8 (ANum 0x136d90) 0x0  ;
z8 (ANum 0x136d98) 0x0  ;
z8 (ANum 0x136da0) 0x0  ;
z8 (ANum 0x136da8) 0x0  ;
z8 (ANum 0x136db0) 0x0  ;
z8 (ANum 0x136db8) 0x0  ;
z8 (ANum 0x136dc0) 0x0  ;
z8 (ANum 0x136dc8) 0x0  ;
z8 (ANum 0x9c670) 0x134d60  ;
z8 (ANum 0x9c678) 0x9e530  ;
z8 (ANum 0x9c680) 0x136de8  ;
z8 (ANum 0x9c688) 0xa2ab8  ;
z8 (ANum 0x9c690) 0xa52b8  ;
z8 (ANum 0x9c698) 0xa5fa8  ;
z8 (ANum 0x9c6a0) 0xa5fb0  ;
z8 (ANum 0x9c6a8) 0xa5fa0  ;
z8 (ANum 0x9c6b0) 0x9e4f8  ;
z8 (ANum 0x9c6b8) 0x9e4f0  ;
z8 (ANum 0x9c6c0) 0x9e528  ;
z8 (ANum 0x9c6c8) 0x9e540  ;
z8 (ANum 0x9c6d0) 0x1  ;
z8 (ANum 0x9c6d8) 0x136ddc  ;
z8 (ANum 0x9c6e0) 0x134d58  ;
z8 (ANum 0x9c6e8) 0xa52c0  ;
z8 (ANum 0xa0f40) 0x20f80  ;
z8 (ANum 0xa0f48) 0x2  ;
z8 (ANum 0xa0f50) 0x20  ;
z8 (ANum 0xa0f58) 0x1c1e8  ;
z8 (ANum 0xa0f60) 0x210e0  ;
z8 (ANum 0xa0f68) 0x0  ;
z8 (ANum 0xa0f70) 0x0  ;
z8 (ANum 0xa0f78) 0xffffffffffffffff  ;
z8 (ANum 0xa0f80) 0x20fa0  ;
z8 (ANum 0xa0f88) 0x3  ;
z8 (ANum 0xa0f90) 0x20  ;
z8 (ANum 0xa0f98) 0x1e985  ;
z8 (ANum 0xa0fa0) 0x210e0  ;
z8 (ANum 0xa0fa8) 0x0  ;
z8 (ANum 0xa0fb0) 0x0  ;
z8 (ANum 0xa0fb8) 0xffffffffffffffff  ;
z8 (ANum 0xa0fc0) 0x20fc0  ;
z8 (ANum 0xa0fc8) 0x7  ;
z8 (ANum 0xa0fd0) 0x20  ;
z8 (ANum 0xa0fd8) 0x206e2  ;
z8 (ANum 0xa0fe0) 0x210e0  ;
z8 (ANum 0xa0fe8) 0x0  ;
z8 (ANum 0xa0ff0) 0x0  ;
z8 (ANum 0xa0ff8) 0xffffffffffffffff  ;
z1 (ANum 0x137160) 0x0  ;
z8 (ANum 0xa2b70) 0x0  ;
z2 (ANum 0xa1fca) 0x0  ;
z4 (ANum 0xa1fcc) 0x0  ;
z1 (ANum 0xa1f01) 0x0  ;
z2 (ANum 0xa1f02) 0x0  ;
z4 (ANum 0xa1f04) 0x0  ;
z8 (ANum 0x9e530) 0x1938d   ;
z8 (ANum 0x1ce7f) 0x612079726f6d656d  ;
z8 (ANum 0x1ce87) 0x7365726464612074  ;
z4 (ANum 0x1ce8f) 0x70252073  ;
z1 (ANum 0x1ce93) 0x0  ;
z4 (ANum 0x20d10) 0x460a4  ;
z8 (ANum 0x9d318) 0x5f8290  ;
z8 (ANum 0x5f8510) 0x1000  ;
z1 (ANum 0x21d68) 0x04  ;
z1 (ANum 0x21d69) 0xff  ;
z4 (ANum 0x21d04) 0x689b0  ;
z1 (ANum 0x136ec3) 0x1  ;
z1 (ANum 0x136edc) 0x1  ;
z8 (ANum 0xa4b00) 0xa4b08  ;
z8 (ANum 0x9e438) 0x90948  ;
z8 (ANum 0x9e448) 0x96f88  ;
z8 (ANum 0x9e438) 0x90948  ;
z8 (ANum 0x9e3a0) 0x94dfc  ;
z8 (ANum 0x9e3a0) 0x94dfc  ;
z8 (ANum 0x9e3a0) 0x94dfc  ;
z8 (ANum 0x9e3a0) 0x94dfc  ;
z8 (ANum 0x9e3a0) 0x94dfc  ;
z8 (ANum 0x9e3a0) 0x94dfc  ;
z8 (ANum 0xa1000) 0x20fe0  ;
z8 (ANum 0xa1008) 0x6  ;
z8 (ANum 0xa1010) 0x20  ;
z8 (ANum 0xa1018) 0x148c1  ;
z8 (ANum 0xa1020) 0x210e0  ;
z8 (ANum 0xa1028) 0x0  ;
z8 (ANum 0xa1030) 0x0  ;
z8 (ANum 0xa1038) 0xffffffffffffffff  ;
z8 (ANum 0xa1040) 0x21000  ;
z8 (ANum 0xa1048) 0x24  ;
z8 (ANum 0xa1050) 0x60  ;
z8 (ANum 0xa1058) 0x113ac  ;
z8 (ANum 0xa1060) 0x210e0  ;
z8 (ANum 0xa1068) 0x0  ;
z8 (ANum 0xa1070) 0x0  ;
z8 (ANum 0xa1078) 0xffffffffffffffff  ;
z8 (ANum 0xa1080) 0x21060  ;
z8 (ANum 0xa1088) 0x7  ;
z8 (ANum 0xa1090) 0x20  ;
z8 (ANum 0xa1098) 0x1d1a2  ;
z8 (ANum 0xa10a0) 0x210e0  ;
z8 (ANum 0xa10a8) 0x0  ;
z8 (ANum 0xa10b0) 0x0  ;
z8 (ANum 0xa10b8) 0xffffffffffffffff  ;
z8 (ANum 0xa10c0) 0x21080  ;
z8 (ANum 0xa10c8) 0x7  ;
z8 (ANum 0xa10d0) 0x20  ;
z8 (ANum 0xa10d8) 0x1890a  ;
z8 (ANum 0xa10e0) 0x210e0  ;
z8 (ANum 0xa10e8) 0x0  ;
z8 (ANum 0xa10f0) 0x0  ;
z8 (ANum 0xa10f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1100) 0x210a0  ;
z8 (ANum 0xa1108) 0x8  ;
z8 (ANum 0xa1110) 0x20  ;
z8 (ANum 0xa1118) 0x1a60b  ;
z8 (ANum 0xa1120) 0x210e0  ;
z8 (ANum 0xa1128) 0x0  ;
z8 (ANum 0xa1130) 0x0  ;
z8 (ANum 0xa1138) 0xffffffffffffffff  ;
z8 (ANum 0xa1140) 0x210c0  ;
z8 (ANum 0xa1148) 0x5  ;
z8 (ANum 0xa1150) 0x20  ;
z8 (ANum 0xa1158) 0x113b5  ;
z8 (ANum 0xa1160) 0x210e0  ;
z8 (ANum 0xa1168) 0x0  ;
z8 (ANum 0xa1170) 0x0  ;
z8 (ANum 0xa1178) 0xffffffffffffffff  ;
z8 (ANum 0xa1180) 0x21100  ;
z8 (ANum 0xa1188) 0x24  ;
z8 (ANum 0xa1190) 0x60  ;
z8 (ANum 0xa1198) 0x1d1a9  ;
z8 (ANum 0xa11a0) 0x21240  ;
z8 (ANum 0xa11a8) 0x0  ;
z8 (ANum 0xa11b0) 0x0  ;
z8 (ANum 0xa11b8) 0xffffffffffffffff  ;
z8 (ANum 0xa11c0) 0x21160  ;
z8 (ANum 0xa11c8) 0x7  ;
z8 (ANum 0xa11d0) 0x20  ;
z8 (ANum 0xa11d8) 0x1c1e8  ;
z8 (ANum 0xa11e0) 0x21240  ;
z8 (ANum 0xa11e8) 0x0  ;
z8 (ANum 0xa11f0) 0x0  ;
z8 (ANum 0xa11f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1200) 0x21180  ;
z8 (ANum 0xa1208) 0x7  ;
z8 (ANum 0xa1210) 0x20  ;
z8 (ANum 0xa1218) 0x1e985  ;
z8 (ANum 0xa1220) 0x21240  ;
z8 (ANum 0xa1228) 0x0  ;
z8 (ANum 0xa1230) 0x0  ;
z8 (ANum 0xa1238) 0xffffffffffffffff  ;
z8 (ANum 0xa1240) 0x211a0  ;
z8 (ANum 0xa1248) 0x8  ;
z8 (ANum 0xa1250) 0x20  ;
z8 (ANum 0xa1258) 0x206e2  ;
z8 (ANum 0xa1260) 0x21240  ;
z8 (ANum 0xa1268) 0x0  ;
z8 (ANum 0xa1270) 0x0  ;
z8 (ANum 0xa1278) 0xffffffffffffffff  ;
z8 (ANum 0xa1280) 0x211c0  ;
z8 (ANum 0xa1288) 0x5  ;
z8 (ANum 0xa1290) 0x20  ;
z8 (ANum 0xa1298) 0x148c1  ;
z8 (ANum 0xa12a0) 0x21240  ;
z8 (ANum 0xa12a8) 0x0  ;
z8 (ANum 0xa12b0) 0x0  ;
z8 (ANum 0xa12b8) 0xffffffffffffffff  ;
z8 (ANum 0xa12c0) 0x211e0  ;
z8 (ANum 0xa12c8) 0x3  ;
z8 (ANum 0xa12d0) 0x20  ;
z8 (ANum 0xa12d8) 0x1373c  ;
z8 (ANum 0xa12e0) 0x21240  ;
z8 (ANum 0xa12e8) 0x0  ;
z8 (ANum 0xa12f0) 0x0  ;
z8 (ANum 0xa12f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1300) 0x21200  ;
z8 (ANum 0xa1308) 0x7  ;
z8 (ANum 0xa1310) 0x20  ;
z8 (ANum 0xa1318) 0x1d1a2  ;
z8 (ANum 0xa1320) 0x21240  ;
z8 (ANum 0xa1328) 0x0  ;
z8 (ANum 0xa1330) 0x0  ;
z8 (ANum 0xa1338) 0xffffffffffffffff  ;
z8 (ANum 0xa1340) 0x21220  ;
z8 (ANum 0xa1348) 0x6  ;
z8 (ANum 0xa1350) 0x20  ;
z8 (ANum 0xa1358) 0x1890a  ;
z8 (ANum 0xa1360) 0x21240  ;
z8 (ANum 0xa1368) 0x0  ;
z8 (ANum 0xa1370) 0x0  ;
z8 (ANum 0xa1378) 0xffffffffffffffff  ;
z8 (ANum 0xa1380) 0x21260  ;
z8 (ANum 0xa1388) 0x6  ;
z8 (ANum 0xa1390) 0x20  ;
z8 (ANum 0xa1398) 0x148c8  ;
z8 (ANum 0xa13a0) 0x21780  ;
z8 (ANum 0xa13a8) 0x0  ;
z8 (ANum 0xa13b0) 0x0  ;
z8 (ANum 0xa13b8) 0xffffffffffffffff  ;
z8 (ANum 0xa13c0) 0x21280  ;
z8 (ANum 0xa13c8) 0x17  ;
z8 (ANum 0xa13d0) 0x40  ;
z8 (ANum 0xa13d8) 0x13e17  ;
z8 (ANum 0xa13e0) 0x21780  ;
z8 (ANum 0xa13e8) 0x0  ;
z8 (ANum 0xa13f0) 0x0  ;
z8 (ANum 0xa13f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1400) 0x212c0  ;
z8 (ANum 0xa1408) 0x6  ;
z8 (ANum 0xa1410) 0x20  ;
z8 (ANum 0xa1418) 0x13743  ;
z8 (ANum 0xa1420) 0x21780  ;
z8 (ANum 0xa1428) 0x0  ;
z8 (ANum 0xa1430) 0x0  ;
z8 (ANum 0xa1438) 0xffffffffffffffff  ;
z8 (ANum 0xa1440) 0x212e0  ;
z8 (ANum 0xa1448) 0x16  ;
z8 (ANum 0xa1450) 0x40  ;
z8 (ANum 0xa1458) 0x16fe5  ;
z8 (ANum 0xa1460) 0x21780  ;
z8 (ANum 0xa1468) 0x0  ;
z8 (ANum 0xa1470) 0x0  ;
z8 (ANum 0xa1478) 0xffffffffffffffff  ;
z8 (ANum 0xa1480) 0x21320  ;
z8 (ANum 0xa1488) 0x7  ;
z8 (ANum 0xa1490) 0x20  ;
z8 (ANum 0xa1498) 0x10ae5  ;
z8 (ANum 0xa14a0) 0x21780  ;
z8 (ANum 0xa14a8) 0x0  ;
z8 (ANum 0xa14b0) 0x0  ;
z8 (ANum 0xa14b8) 0xffffffffffffffff  ;
z8 (ANum 0xa14c0) 0x21340  ;
z8 (ANum 0xa14c8) 0x7  ;
z8 (ANum 0xa14d0) 0x20  ;
z8 (ANum 0xa14d8) 0x17f1c  ;
z8 (ANum 0xa14e0) 0x21780  ;
z8 (ANum 0xa14e8) 0x0  ;
z8 (ANum 0xa14f0) 0x0  ;
z8 (ANum 0xa14f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1500) 0x21360  ;
z8 (ANum 0xa1508) 0x1d  ;
z8 (ANum 0xa1510) 0x40  ;
z8 (ANum 0xa1518) 0x17703  ;
z8 (ANum 0xa1520) 0x21780  ;
z8 (ANum 0xa1528) 0x0  ;
z8 (ANum 0xa1530) 0x0  ;
z8 (ANum 0xa1538) 0xffffffffffffffff  ;
z8 (ANum 0xa1540) 0x213a0  ;
z8 (ANum 0xa1548) 0xc  ;
z8 (ANum 0xa1550) 0x20  ;
z8 (ANum 0xa1558) 0x10aed  ;
z8 (ANum 0xa1560) 0x21780  ;
z8 (ANum 0xa1568) 0x0  ;
z8 (ANum 0xa1570) 0x0  ;
z8 (ANum 0xa1578) 0xffffffffffffffff  ;
z8 (ANum 0xa1580) 0x213c0  ;
z8 (ANum 0xa1588) 0x1d  ;
z8 (ANum 0xa1590) 0x40  ;
z8 (ANum 0xa1598) 0x1374b  ;
z8 (ANum 0xa15a0) 0x21780  ;
z8 (ANum 0xa15a8) 0x0  ;
z8 (ANum 0xa15b0) 0x0  ;
z8 (ANum 0xa15b8) 0xffffffffffffffff  ;
z8 (ANum 0xa15c0) 0x21400  ;
z8 (ANum 0xa15c8) 0x6  ;
z8 (ANum 0xa15d0) 0x20  ;
z8 (ANum 0xa15d8) 0x113bc  ;
z8 (ANum 0xa15e0) 0x21780  ;
z8 (ANum 0xa15e8) 0x0  ;
z8 (ANum 0xa15f0) 0x0  ;
z8 (ANum 0xa15f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1600) 0x21420  ;
z8 (ANum 0xa1608) 0x17  ;
z8 (ANum 0xa1610) 0x40  ;
z8 (ANum 0xa1618) 0x123a8  ;
z8 (ANum 0xa1620) 0x21780  ;
z8 (ANum 0xa1628) 0x0  ;
z8 (ANum 0xa1630) 0x0  ;
z8 (ANum 0xa1638) 0xffffffffffffffff  ;
z8 (ANum 0xa1640) 0x21460  ;
z8 (ANum 0xa1648) 0x8  ;
z8 (ANum 0xa1650) 0x20  ;
z8 (ANum 0xa1658) 0x13e1f  ;
z8 (ANum 0xa1660) 0x21780  ;
z8 (ANum 0xa1668) 0x0  ;
z8 (ANum 0xa1670) 0x0  ;
z8 (ANum 0xa1678) 0xffffffffffffffff  ;
z8 (ANum 0xa1680) 0x21480  ;
z8 (ANum 0xa1688) 0x6  ;
z8 (ANum 0xa1690) 0x20  ;
z8 (ANum 0xa1698) 0x1df05  ;
z8 (ANum 0xa16a0) 0x21780  ;
z8 (ANum 0xa16a8) 0x0  ;
z8 (ANum 0xa16b0) 0x0  ;
z8 (ANum 0xa16b8) 0xffffffffffffffff  ;
z8 (ANum 0xa16c0) 0x214a0  ;
z8 (ANum 0xa16c8) 0x18  ;
z8 (ANum 0xa16d0) 0x40  ;
z8 (ANum 0xa16d8) 0x17f24  ;
z8 (ANum 0xa16e0) 0x21780  ;
z8 (ANum 0xa16e8) 0x0  ;
z8 (ANum 0xa16f0) 0x0  ;
z8 (ANum 0xa16f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1700) 0x214e0  ;
z8 (ANum 0xa1708) 0x8  ;
z8 (ANum 0xa1710) 0x20  ;
z8 (ANum 0xa1718) 0x1ba47  ;
z8 (ANum 0xa1720) 0x21780  ;
z8 (ANum 0xa1728) 0x0  ;
z8 (ANum 0xa1730) 0x0  ;
z8 (ANum 0xa1738) 0xffffffffffffffff  ;
z8 (ANum 0xa1740) 0x21500  ;
z8 (ANum 0xa1748) 0x7  ;
z8 (ANum 0xa1750) 0x20  ;
z8 (ANum 0xa1758) 0x1982c  ;
z8 (ANum 0xa1760) 0x21780  ;
z8 (ANum 0xa1768) 0x0  ;
z8 (ANum 0xa1770) 0x0  ;
z8 (ANum 0xa1778) 0xffffffffffffffff  ;
z8 (ANum 0xa1780) 0x21520  ;
z8 (ANum 0xa1788) 0x18  ;
z8 (ANum 0xa1790) 0x40  ;
z8 (ANum 0xa1798) 0x17f2c  ;
z8 (ANum 0xa17a0) 0x21780  ;
z8 (ANum 0xa17a8) 0x0  ;
z8 (ANum 0xa17b0) 0x0  ;
z8 (ANum 0xa17b8) 0xffffffffffffffff  ;
z8 (ANum 0xa17c0) 0x21560  ;
z8 (ANum 0xa17c8) 0x9  ;
z8 (ANum 0xa17d0) 0x20  ;
z8 (ANum 0xa17d8) 0x113c4  ;
z8 (ANum 0xa17e0) 0x21780  ;
z8 (ANum 0xa17e8) 0x0  ;
z8 (ANum 0xa17f0) 0x0  ;
z8 (ANum 0xa17f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1800) 0x21580  ;
z8 (ANum 0xa1808) 0x7  ;
z8 (ANum 0xa1810) 0x20  ;
z8 (ANum 0xa1818) 0x15061  ;
z8 (ANum 0xa1820) 0x21780  ;
z8 (ANum 0xa1828) 0x0  ;
z8 (ANum 0xa1830) 0x0  ;
z8 (ANum 0xa1838) 0xffffffffffffffff  ;
z8 (ANum 0xa1840) 0x215a0  ;
z8 (ANum 0xa1848) 0x18  ;
z8 (ANum 0xa1850) 0x40  ;
z8 (ANum 0xa1858) 0x19f7a  ;
z8 (ANum 0xa1860) 0x21780  ;
z8 (ANum 0xa1868) 0x0  ;
z8 (ANum 0xa1870) 0x0  ;
z8 (ANum 0xa1878) 0xffffffffffffffff  ;
z8 (ANum 0xa1880) 0x215e0  ;
z8 (ANum 0xa1888) 0x9  ;
z8 (ANum 0xa1890) 0x20  ;
z8 (ANum 0xa1898) 0x20704  ;
z8 (ANum 0xa18a0) 0x21780  ;
z8 (ANum 0xa18a8) 0x0  ;
z8 (ANum 0xa18b0) 0x0  ;
z8 (ANum 0xa18b8) 0xffffffffffffffff  ;
z8 (ANum 0xa18c0) 0x21600  ;
z8 (ANum 0xa18c8) 0x7  ;
z8 (ANum 0xa18d0) 0x20  ;
z8 (ANum 0xa18d8) 0x148d0  ;
z8 (ANum 0xa18e0) 0x21780  ;
z8 (ANum 0xa18e8) 0x0  ;
z8 (ANum 0xa18f0) 0x0  ;
z8 (ANum 0xa18f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1900) 0x21620  ;
z8 (ANum 0xa1908) 0x17  ;
z8 (ANum 0xa1910) 0x40  ;
z8 (ANum 0xa1918) 0x113cc  ;
z8 (ANum 0xa1920) 0x21780  ;
z8 (ANum 0xa1928) 0x0  ;
z8 (ANum 0xa1930) 0x0  ;
z8 (ANum 0xa1938) 0xffffffffffffffff  ;
z8 (ANum 0xa1940) 0x21660  ;
z8 (ANum 0xa1948) 0x8  ;
z8 (ANum 0xa1950) 0x20  ;
z8 (ANum 0xa1958) 0x16027  ;
z8 (ANum 0xa1960) 0x21780  ;
z8 (ANum 0xa1968) 0x0  ;
z8 (ANum 0xa1970) 0x0  ;
z8 (ANum 0xa1978) 0xffffffffffffffff  ;
z8 (ANum 0xa1980) 0x21680  ;
z8 (ANum 0xa1988) 0x7  ;
z8 (ANum 0xa1990) 0x20  ;
z8 (ANum 0xa1998) 0x1d1d5  ;
z8 (ANum 0xa19a0) 0x21780  ;
z8 (ANum 0xa19a8) 0x0  ;
z8 (ANum 0xa19b0) 0x0  ;
z8 (ANum 0xa19b8) 0xffffffffffffffff  ;
z8 (ANum 0xa19c0) 0x216a0  ;
z8 (ANum 0xa19c8) 0x17  ;
z8 (ANum 0xa19d0) 0x40  ;
z8 (ANum 0xa19d8) 0x19834  ;
z8 (ANum 0xa19e0) 0x21780  ;
z8 (ANum 0xa19e8) 0x0  ;
z8 (ANum 0xa19f0) 0x0  ;
z8 (ANum 0xa19f8) 0xffffffffffffffff  ;
z8 (ANum 0xa1a00) 0x216e0  ;
z8 (ANum 0xa1a08) 0x8  ;
z8 (ANum 0xa1a10) 0x20  ;
z8 (ANum 0xa1a18) 0x201f3  ;
z8 (ANum 0xa1a20) 0x21780  ;
z8 (ANum 0xa1a28) 0x0  ;
z8 (ANum 0xa1a30) 0x0  ;
z8 (ANum 0xa1a38) 0xffffffffffffffff  ;
z8 (ANum 0xa1a40) 0x21700  ;
z8 (ANum 0xa1a48) 0x7  ;
z8 (ANum 0xa1a50) 0x20  ;
z8 (ANum 0xa1a58) 0x1ba4f  ;
z8 (ANum 0xa1a60) 0x21780  ;
z8 (ANum 0xa1a68) 0x0  ;
z8 (ANum 0xa1a70) 0x0  ;
z8 (ANum 0xa1a78) 0xffffffffffffffff  ;
z8 (ANum 0xa1a80) 0x21720  ;
z8 (ANum 0xa1a88) 0x18  ;
z8 (ANum 0xa1a90) 0x40  ;
z8 (ANum 0xa1a98) 0x1cb24  ;
z8 (ANum 0xa1aa0) 0x21780  ;
z8 (ANum 0xa1aa8) 0x0  ;
z8 (ANum 0xa1ab0) 0x0  ;
z8 (ANum 0xa1ab8) 0xffffffffffffffff  ;
z8 (ANum 0xa1ac0) 0x21760  ;
z8 (ANum 0xa1ac8) 0x8  ;
z8 (ANum 0xa1ad0) 0x20  ;
z8 (ANum 0xa1ad8) 0x2070c  ;
z8 (ANum 0xa1ae0) 0x21780  ;
z8 (ANum 0xa1ae8) 0x0  ;
z8 (ANum 0xa1af0) 0x0  ;
z8 (ANum 0xa1af8) 0xffffffffffffffff  ;
z8 (ANum 0xa1b00) 0x9b460  ;
z8 (ANum 0xa1b08) 0x18  ;
z8 (ANum 0xa1b10) 0x40  ;
z8 (ANum 0xa1b18) 0x16fc1  ;
z8 (ANum 0xa1b20) 0x210e0  ;
z8 (ANum 0xa1b28) 0x0  ;
z8 (ANum 0xa1b30) 0x0  ;
z8 (ANum 0xa1b38) 0xffffffffffffffff  ;
z8 (ANum 0xa1b40) 0x9b4a0  ;
z8 (ANum 0xa1b48) 0x18  ;
z8 (ANum 0xa1b50) 0x40  ;
z8 (ANum 0xa1b58) 0x1d1b3  ;
z8 (ANum 0xa1b60) 0x21240  ;
z8 (ANum 0xa1b68) 0x0  ;
z8 (ANum 0xa1b70) 0x0  ;
z8 (ANum 0xa1b78) 0xffffffffffffffff  ;
z8 (ANum 0xa1b80) 0x9b4e0  ;
z8 (ANum 0xa1b88) 0x18  ;
z8 (ANum 0xa1b90) 0x40  ;
z8 (ANum 0xa1b98) 0x206e9  ;
z8 (ANum 0xa1ba0) 0x21240  ;
z8 (ANum 0xa1ba8) 0x0  ;
z8 (ANum 0xa1bb0) 0x0  ;
z8 (ANum 0xa1bb8) 0xffffffffffffffff  ;
z8 (ANum 0xa1bc0) 0x9b520  ;
z8 (ANum 0xa1bc8) 0xcb8  ;
z8 (ANum 0xa1bd0) 0xfe0  ;
z8 (ANum 0xa1bd8) 0x1c1ed  ;
z8 (ANum 0xa1be0) 0x21780  ;
z8 (ANum 0xa1be8) 0x0  ;
z8 (ANum 0xa1bf0) 0x0  ;
z8 (ANum 0xa1bf8) 0xffffffffffffffff
;
z2 (ANum 0x20f82) 0x0  ;
z4 (ANum 0x20f84) 0x0  ;
z8 (ANum 0x20f88) 0x0  ;
z8 (ANum 0x20f90) 0x0  ;
z8 (ANum 0x20f98) 0x0  ;
z1 (ANum 0x20fa3) 0x0  ;
z4 (ANum 0x20fa4) 0x0  ;
z8 (ANum 0x20fa8) 0x0  ;
z8 (ANum 0x20fb0) 0x0  ;
z8 (ANum 0x20fb8) 0x0  ;
z1 (ANum 0x20fc7) 0x0  ;
z8 (ANum 0x20fc8) 0x0  ;
z8 (ANum 0x20fd0) 0x0  ;
z8 (ANum 0x20fd8) 0x0  ;
z2 (ANum 0x20fe6) 0x0  ;
z8 (ANum 0x20fe8) 0x0  ;
z8 (ANum 0x20ff0) 0x0  ;
z8 (ANum 0x20ff8) 0x0  ;
z4 (ANum 0x21024) 0x0  ;
z8 (ANum 0x21028) 0x0  ;
z8 (ANum 0x21030) 0x0  ;
z8 (ANum 0x21038) 0x0  ;
z8 (ANum 0x21040) 0x0  ;
z8 (ANum 0x21048) 0x0  ;
z8 (ANum 0x21050) 0x0  ;
z8 (ANum 0x21058) 0x0  ;
z1 (ANum 0x21067) 0x0  ;
z8 (ANum 0x21068) 0x0  ;
z8 (ANum 0x21070) 0x0  ;
z8 (ANum 0x21078) 0x0  ;
z1 (ANum 0x21087) 0x0  ;
z8 (ANum 0x21088) 0x0  ;
z8 (ANum 0x21090) 0x0  ;
z8 (ANum 0x21098) 0x0  ;
z8 (ANum 0x210a8) 0x0  ;
z8 (ANum 0x210b0) 0x0  ;
z8 (ANum 0x210b8) 0x0  ;
z1 (ANum 0x210c5) 0x0  ;
z2 (ANum 0x210c6) 0x0  ;
z8 (ANum 0x210c8) 0x0  ;
z8 (ANum 0x210d0) 0x0  ;
z8 (ANum 0x210d8) 0x0  ;
z4 (ANum 0x21124) 0x0  ;
z8 (ANum 0x21128) 0x0  ;
z8 (ANum 0x21130) 0x0  ;
z8 (ANum 0x21138) 0x0  ;
z8 (ANum 0x21140) 0x0  ;
z8 (ANum 0x21148) 0x0  ;
z8 (ANum 0x21150) 0x0  ;
z8 (ANum 0x21158) 0x0  ;
z1 (ANum 0x21167) 0x0  ;
z8 (ANum 0x21168) 0x0  ;
z8 (ANum 0x21170) 0x0  ;
z8 (ANum 0x21178) 0x0  ;
z1 (ANum 0x21187) 0x0  ;
z8 (ANum 0x21188) 0x0  ;
z8 (ANum 0x21190) 0x0  ;
z8 (ANum 0x21198) 0x0  ;
z8 (ANum 0x211a8) 0x0  ;
z8 (ANum 0x211b0) 0x0  ;
z8 (ANum 0x211b8) 0x0  ;
z1 (ANum 0x211c5) 0x0  ;
z2 (ANum 0x211c6) 0x0  ;
z8 (ANum 0x211c8) 0x0  ;
z8 (ANum 0x211d0) 0x0  ;
z8 (ANum 0x211d8) 0x0  ;
z1 (ANum 0x211e3) 0x0  ;
z4 (ANum 0x211e4) 0x0  ;
z8 (ANum 0x211e8) 0x0  ;
z8 (ANum 0x211f0) 0x0  ;
z8 (ANum 0x211f8) 0x0  ;
z1 (ANum 0x21207) 0x0  ;
z8 (ANum 0x21208) 0x0  ;
z8 (ANum 0x21210) 0x0  ;
z8 (ANum 0x21218) 0x0  ;
z2 (ANum 0x21226) 0x0  ;
z8 (ANum 0x21228) 0x0  ;
z8 (ANum 0x21230) 0x0  ;
z8 (ANum 0x21238) 0x0  ;
z2 (ANum 0x21266) 0x0  ;
z8 (ANum 0x21268) 0x0  ;
z8 (ANum 0x21270) 0x0  ;
z8 (ANum 0x21278) 0x0  ;
z1 (ANum 0x21297) 0x0  ;
z8 (ANum 0x21298) 0x0  ;
z8 (ANum 0x212a0) 0x0  ;
z8 (ANum 0x212a8) 0x0  ;
z8 (ANum 0x212b0) 0x0  ;
z8 (ANum 0x212b8) 0x0  ;
z2 (ANum 0x212c6) 0x0  ;
z8 (ANum 0x212c8) 0x0  ;
z8 (ANum 0x212d0) 0x0  ;
z8 (ANum 0x212d8) 0x0  ;
z2 (ANum 0x212f6) 0x0  ;
z8 (ANum 0x212f8) 0x0  ;
z8 (ANum 0x21300) 0x0  ;
z8 (ANum 0x21308) 0x0  ;
z8 (ANum 0x21310) 0x0  ;
z8 (ANum 0x21318) 0x0  ;
z1 (ANum 0x21327) 0x0  ;
z8 (ANum 0x21328) 0x0  ;
z8 (ANum 0x21330) 0x0  ;
z8 (ANum 0x21338) 0x0  ;
z1 (ANum 0x21347) 0x0  ;
z8 (ANum 0x21348) 0x0  ;
z8 (ANum 0x21350) 0x0  ;
z8 (ANum 0x21358) 0x0  ;
z1 (ANum 0x2137d) 0x0  ;
z2 (ANum 0x2137e) 0x0  ;
z8 (ANum 0x21380) 0x0  ;
z8 (ANum 0x21388) 0x0  ;
z8 (ANum 0x21390) 0x0  ;
z8 (ANum 0x21398) 0x0  ;
z4 (ANum 0x213ac) 0x0  ;
z8 (ANum 0x213b0) 0x0  ;
z8 (ANum 0x213b8) 0x0  ;
z1 (ANum 0x213dd) 0x0  ;
z2 (ANum 0x213de) 0x0  ;
z8 (ANum 0x213e0) 0x0  ;
z8 (ANum 0x213e8) 0x0  ;
z8 (ANum 0x213f0) 0x0  ;
z8 (ANum 0x213f8) 0x0  ;
z2 (ANum 0x21406) 0x0  ;
z8 (ANum 0x21408) 0x0  ;
z8 (ANum 0x21410) 0x0  ;
z8 (ANum 0x21418) 0x0  ;
z1 (ANum 0x21437) 0x0  ;
z8 (ANum 0x21438) 0x0  ;
z8 (ANum 0x21440) 0x0  ;
z8 (ANum 0x21448) 0x0  ;
z8 (ANum 0x21450) 0x0  ;
z8 (ANum 0x21458) 0x0  ;
z8 (ANum 0x21468) 0x0  ;
z8 (ANum 0x21470) 0x0  ;
z8 (ANum 0x21478) 0x0  ;
z2 (ANum 0x21486) 0x0  ;
z8 (ANum 0x21488) 0x0  ;
z8 (ANum 0x21490) 0x0  ;
z8 (ANum 0x21498) 0x0  ;
z8 (ANum 0x214b8) 0x0  ;
z8 (ANum 0x214c0) 0x0  ;
z8 (ANum 0x214c8) 0x0  ;
z8 (ANum 0x214d0) 0x0  ;
z8 (ANum 0x214d8) 0x0  ;
z8 (ANum 0x214e8) 0x0  ;
z8 (ANum 0x214f0) 0x0  ;
z8 (ANum 0x214f8) 0x0  ;
z1 (ANum 0x21507) 0x0  ;
z8 (ANum 0x21508) 0x0  ;
z8 (ANum 0x21510) 0x0  ;
z8 (ANum 0x21518) 0x0  ;
z8 (ANum 0x21538) 0x0  ;
z8 (ANum 0x21540) 0x0  ;
z8 (ANum 0x21548) 0x0  ;
z8 (ANum 0x21550) 0x0  ;
z8 (ANum 0x21558) 0x0  ;
z1 (ANum 0x21569) 0x0  ;
z2 (ANum 0x2156a) 0x0  ;
z4 (ANum 0x2156c) 0x0  ;
z8 (ANum 0x21570) 0x0  ;
z8 (ANum 0x21578) 0x0  ;
z1 (ANum 0x21587) 0x0  ;
z8 (ANum 0x21588) 0x0  ;
z8 (ANum 0x21590) 0x0  ;
z8 (ANum 0x21598) 0x0  ;
z8 (ANum 0x215b8) 0x0  ;
z8 (ANum 0x215c0) 0x0  ;
z8 (ANum 0x215c8) 0x0  ;
z8 (ANum 0x215d0) 0x0  ;
z8 (ANum 0x215d8) 0x0  ;
z1 (ANum 0x215e9) 0x0  ;
z2 (ANum 0x215ea) 0x0  ;
z4 (ANum 0x215ec) 0x0  ;
z8 (ANum 0x215f0) 0x0  ;
z8 (ANum 0x215f8) 0x0  ;
z1 (ANum 0x21607) 0x0  ;
z8 (ANum 0x21608) 0x0  ;
z8 (ANum 0x21610) 0x0  ;
z8 (ANum 0x21618) 0x0  ;
z1 (ANum 0x21637) 0x0  ;
z8 (ANum 0x21638) 0x0  ;
z8 (ANum 0x21640) 0x0  ;
z8 (ANum 0x21648) 0x0  ;
z8 (ANum 0x21650) 0x0  ;
z8 (ANum 0x21658) 0x0  ;
z8 (ANum 0x21668) 0x0  ;
z8 (ANum 0x21670) 0x0  ;
z8 (ANum 0x21678) 0x0  ;
z1 (ANum 0x21687) 0x0  ;
z8 (ANum 0x21688) 0x0  ;
z8 (ANum 0x21690) 0x0  ;
z8 (ANum 0x21698) 0x0  ;
z1 (ANum 0x216b7) 0x0  ;
z8 (ANum 0x216b8) 0x0  ;
z8 (ANum 0x216c0) 0x0  ;
z8 (ANum 0x216c8) 0x0  ;
z8 (ANum 0x216d0) 0x0  ;
z8 (ANum 0x216d8) 0x0  ;
z8 (ANum 0x216e8) 0x0  ;
z8 (ANum 0x216f0) 0x0  ;
z8 (ANum 0x216f8) 0x0  ;
z1 (ANum 0x21707) 0x0  ;
z8 (ANum 0x21708) 0x0  ;
z8 (ANum 0x21710) 0x0  ;
z8 (ANum 0x21718) 0x0  ;
z8 (ANum 0x21738) 0x0  ;
z8 (ANum 0x21740) 0x0  ;
z8 (ANum 0x21748) 0x0  ;
z8 (ANum 0x21750) 0x0  ;
z8 (ANum 0x21758) 0x0  ;
z8 (ANum 0x21768) 0x0  ;
z8 (ANum 0x21770) 0x0  ;
z8 (ANum 0x21778) 0x0 ;
z8 (ANum 0xa2b70) 0x0  ;
z8 (ANum 0x9e390) 0x94f50  ].
Definition Tfib_const_shadow : list acell :=
[ z1 (ANum 0x7fffc1f0) 0x2  ;
z1 (ANum 0x7fffc1f1) 0xf9  ;
z1 (ANum 0x7fffc1f2) 0xf9  ;
z1 (ANum 0x7fffc1f3) 0xf9  ;
z1 (ANum 0x7fffc1f4) 0x3  ;
z1 (ANum 0x7fffc1f5) 0xf9  ;
z1 (ANum 0x7fffc1f6) 0xf9  ;
z1 (ANum 0x7fffc1f7) 0xf9  ;
z1 (ANum 0x7fffc1f8) 0x7  ;
z1 (ANum 0x7fffc1f9) 0xf9  ;
z1 (ANum 0x7fffc1fa) 0xf9  ;
z1 (ANum 0x7fffc1fb) 0xf9  ;
z1 (ANum 0x7fffc1fc) 0x6  ;
z1 (ANum 0x7fffc1fd) 0xf9  ;
z1 (ANum 0x7fffc1fe) 0xf9  ;
z1 (ANum 0x7fffc1ff) 0xf9  ;
z1 (ANum 0x7fffc204) 0x4  ;
z1 (ANum 0x7fffc205) 0xf9  ;
z1 (ANum 0x7fffc206) 0xf9  ;
z1 (ANum 0x7fffc207) 0xf9  ;
z1 (ANum 0x7fffc208) 0xf9  ;
z1 (ANum 0x7fffc209) 0xf9  ;
z1 (ANum 0x7fffc20a) 0xf9  ;
z1 (ANum 0x7fffc20b) 0xf9  ;
z1 (ANum 0x7fffc20c) 0x7  ;
z1 (ANum 0x7fffc20d) 0xf9  ;
z1 (ANum 0x7fffc20e) 0xf9  ;
z1 (ANum 0x7fffc20f) 0xf9  ;
z1 (ANum 0x7fffc210) 0x7  ;
z1 (ANum 0x7fffc211) 0xf9  ;
z1 (ANum 0x7fffc212) 0xf9  ;
z1 (ANum 0x7fffc213) 0xf9  ;
z1 (ANum 0x7fffc215) 0xf9  ;
z1 (ANum 0x7fffc216) 0xf9  ;
z1 (ANum 0x7fffc217) 0xf9  ;
z1 (ANum 0x7fffc218) 0x5  ;
z1 (ANum 0x7fffc219) 0xf9  ;
z1 (ANum 0x7fffc21a) 0xf9  ;
z1 (ANum 0x7fffc21b) 0xf9  ;
z1 (ANum 0x7fffc224) 0x4  ;
z1 (ANum 0x7fffc225) 0xf9  ;
z1 (ANum 0x7fffc226) 0xf9  ;
z1 (ANum 0x7fffc227) 0xf9  ;
z1 (ANum 0x7fffc228) 0xf9  ;
z1 (ANum 0x7fffc229) 0xf9  ;
z1 (ANum 0x7fffc22a) 0xf9  ;
z1 (ANum 0x7fffc22b) 0xf9  ;
z1 (ANum 0x7fffc22c) 0x7  ;
z1 (ANum 0x7fffc22d) 0xf9  ;
z1 (ANum 0x7fffc22e) 0xf9  ;
z1 (ANum 0x7fffc22f) 0xf9  ;
z1 (ANum 0x7fffc230) 0x7  ;
z1 (ANum 0x7fffc231) 0xf9  ;
z1 (ANum 0x7fffc232) 0xf9  ;
z1 (ANum 0x7fffc233) 0xf9  ;
z1 (ANum 0x7fffc235) 0xf9  ;
z1 (ANum 0x7fffc236) 0xf9  ;
z1 (ANum 0x7fffc237) 0xf9  ;
z1 (ANum 0x7fffc238) 0x5  ;
z1 (ANum 0x7fffc239) 0xf9  ;
z1 (ANum 0x7fffc23a) 0xf9  ;
z1 (ANum 0x7fffc23b) 0xf9  ;
z1 (ANum 0x7fffc23c) 0x3  ;
z1 (ANum 0x7fffc23d) 0xf9  ;
z1 (ANum 0x7fffc23e) 0xf9  ;
z1 (ANum 0x7fffc23f) 0xf9  ;
z1 (ANum 0x7fffc240) 0x7  ;
z1 (ANum 0x7fffc241) 0xf9  ;
z1 (ANum 0x7fffc242) 0xf9  ;
z1 (ANum 0x7fffc243) 0xf9  ;
z1 (ANum 0x7fffc244) 0x6  ;
z1 (ANum 0x7fffc245) 0xf9  ;
z1 (ANum 0x7fffc246) 0xf9  ;
z1 (ANum 0x7fffc247) 0xf9  ;
z1 (ANum 0x7fffc24c) 0x6  ;
z1 (ANum 0x7fffc24d) 0xf9  ;
z1 (ANum 0x7fffc24e) 0xf9  ;
z1 (ANum 0x7fffc24f) 0xf9  ;
z1 (ANum 0x7fffc252) 0x7  ;
z1 (ANum 0x7fffc253) 0xf9  ;
z1 (ANum 0x7fffc254) 0xf9  ;
z1 (ANum 0x7fffc255) 0xf9  ;
z1 (ANum 0x7fffc256) 0xf9  ;
z1 (ANum 0x7fffc257) 0xf9  ;
z1 (ANum 0x7fffc258) 0x6  ;
z1 (ANum 0x7fffc259) 0xf9  ;
z1 (ANum 0x7fffc25a) 0xf9  ;
z1 (ANum 0x7fffc25b) 0xf9  ;
z1 (ANum 0x7fffc25e) 0x6  ;
z1 (ANum 0x7fffc25f) 0xf9  ;
z1 (ANum 0x7fffc260) 0xf9  ;
z1 (ANum 0x7fffc261) 0xf9  ;
z1 (ANum 0x7fffc262) 0xf9  ;
z1 (ANum 0x7fffc263) 0xf9  ;
z1 (ANum 0x7fffc264) 0x7  ;
z1 (ANum 0x7fffc265) 0xf9  ;
z1 (ANum 0x7fffc266) 0xf9  ;
z1 (ANum 0x7fffc267) 0xf9  ;
z1 (ANum 0x7fffc268) 0x7  ;
z1 (ANum 0x7fffc269) 0xf9  ;
z1 (ANum 0x7fffc26a) 0xf9  ;
z1 (ANum 0x7fffc26b) 0xf9  ;
z1 (ANum 0x7fffc26f) 0x5  ;
z1 (ANum 0x7fffc270) 0xf9  ;
z1 (ANum 0x7fffc271) 0xf9  ;
z1 (ANum 0x7fffc272) 0xf9  ;
z1 (ANum 0x7fffc273) 0xf9  ;
z1 (ANum 0x7fffc275) 0x4  ;
z1 (ANum 0x7fffc276) 0xf9  ;
z1 (ANum 0x7fffc277) 0xf9  ;
z1 (ANum 0x7fffc27b) 0x5  ;
z1 (ANum 0x7fffc27c) 0xf9  ;
z1 (ANum 0x7fffc27d) 0xf9  ;
z1 (ANum 0x7fffc27e) 0xf9  ;
z1 (ANum 0x7fffc27f) 0xf9  ;
z1 (ANum 0x7fffc280) 0x6  ;
z1 (ANum 0x7fffc281) 0xf9  ;
z1 (ANum 0x7fffc282) 0xf9  ;
z1 (ANum 0x7fffc283) 0xf9  ;
z1 (ANum 0x7fffc286) 0x7  ;
z1 (ANum 0x7fffc287) 0xf9  ;
z1 (ANum 0x7fffc288) 0xf9  ;
z1 (ANum 0x7fffc289) 0xf9  ;
z1 (ANum 0x7fffc28a) 0xf9  ;
z1 (ANum 0x7fffc28b) 0xf9  ;
z1 (ANum 0x7fffc28d) 0xf9  ;
z1 (ANum 0x7fffc28e) 0xf9  ;
z1 (ANum 0x7fffc28f) 0xf9  ;
z1 (ANum 0x7fffc290) 0x6  ;
z1 (ANum 0x7fffc291) 0xf9  ;
z1 (ANum 0x7fffc292) 0xf9  ;
z1 (ANum 0x7fffc293) 0xf9  ;
z1 (ANum 0x7fffc297) 0xf9  ;
z1 (ANum 0x7fffc298) 0xf9  ;
z1 (ANum 0x7fffc299) 0xf9  ;
z1 (ANum 0x7fffc29a) 0xf9  ;
z1 (ANum 0x7fffc29b) 0xf9  ;
z1 (ANum 0x7fffc29d) 0xf9  ;
z1 (ANum 0x7fffc29e) 0xf9  ;
z1 (ANum 0x7fffc29f) 0xf9  ;
z1 (ANum 0x7fffc2a0) 0x7  ;
z1 (ANum 0x7fffc2a1) 0xf9  ;
z1 (ANum 0x7fffc2a2) 0xf9  ;
z1 (ANum 0x7fffc2a3) 0xf9  ;
z1 (ANum 0x7fffc2a7) 0xf9  ;
z1 (ANum 0x7fffc2a8) 0xf9  ;
z1 (ANum 0x7fffc2a9) 0xf9  ;
z1 (ANum 0x7fffc2aa) 0xf9  ;
z1 (ANum 0x7fffc2ab) 0xf9  ;
z1 (ANum 0x7fffc2ad) 0x1  ;
z1 (ANum 0x7fffc2ae) 0xf9  ;
z1 (ANum 0x7fffc2af) 0xf9  ;
z1 (ANum 0x7fffc2b0) 0x7  ;
z1 (ANum 0x7fffc2b1) 0xf9  ;
z1 (ANum 0x7fffc2b2) 0xf9  ;
z1 (ANum 0x7fffc2b3) 0xf9  ;
z1 (ANum 0x7fffc2b7) 0xf9  ;
z1 (ANum 0x7fffc2b8) 0xf9  ;
z1 (ANum 0x7fffc2b9) 0xf9  ;
z1 (ANum 0x7fffc2ba) 0xf9  ;
z1 (ANum 0x7fffc2bb) 0xf9  ;
z1 (ANum 0x7fffc2bd) 0x1  ;
z1 (ANum 0x7fffc2be) 0xf9  ;
z1 (ANum 0x7fffc2bf) 0xf9  ;
z1 (ANum 0x7fffc2c0) 0x7  ;
z1 (ANum 0x7fffc2c1) 0xf9  ;
z1 (ANum 0x7fffc2c2) 0xf9  ;
z1 (ANum 0x7fffc2c3) 0xf9  ;
z1 (ANum 0x7fffc2c6) 0x7  ;
z1 (ANum 0x7fffc2c7) 0xf9  ;
z1 (ANum 0x7fffc2c8) 0xf9  ;
z1 (ANum 0x7fffc2c9) 0xf9  ;
z1 (ANum 0x7fffc2ca) 0xf9  ;
z1 (ANum 0x7fffc2cb) 0xf9  ;
z1 (ANum 0x7fffc2cd) 0xf9  ;
z1 (ANum 0x7fffc2ce) 0xf9  ;
z1 (ANum 0x7fffc2cf) 0xf9  ;
z1 (ANum 0x7fffc2d0) 0x7  ;
z1 (ANum 0x7fffc2d1) 0xf9  ;
z1 (ANum 0x7fffc2d2) 0xf9  ;
z1 (ANum 0x7fffc2d3) 0xf9  ;
z1 (ANum 0x7fffc2d6) 0x7  ;
z1 (ANum 0x7fffc2d7) 0xf9  ;
z1 (ANum 0x7fffc2d8) 0xf9  ;
z1 (ANum 0x7fffc2d9) 0xf9  ;
z1 (ANum 0x7fffc2da) 0xf9  ;
z1 (ANum 0x7fffc2db) 0xf9  ;
z1 (ANum 0x7fffc2dd) 0xf9  ;
z1 (ANum 0x7fffc2de) 0xf9  ;
z1 (ANum 0x7fffc2df) 0xf9  ;
z1 (ANum 0x7fffc2e0) 0x7  ;
z1 (ANum 0x7fffc2e1) 0xf9  ;
z1 (ANum 0x7fffc2e2) 0xf9  ;
z1 (ANum 0x7fffc2e3) 0xf9  ;
z1 (ANum 0x7fffc2e7) 0xf9  ;
z1 (ANum 0x7fffc2e8) 0xf9  ;
z1 (ANum 0x7fffc2e9) 0xf9  ;
z1 (ANum 0x7fffc2ea) 0xf9  ;
z1 (ANum 0x7fffc2eb) 0xf9  ;
z1 (ANum 0x7fffc2ed) 0xf9  ;
z1 (ANum 0x7fffc2ee) 0xf9  ;
z1 (ANum 0x7fffc2ef) 0xf9  ;
z1 (ANum 0x8000b68f) 0xf9  ;
z1 (ANum 0x8000b690) 0xf9  ;
z1 (ANum 0x8000b691) 0xf9  ;
z1 (ANum 0x8000b692) 0xf9  ;
z1 (ANum 0x8000b693) 0xf9  ;
z1 (ANum 0x8000b697) 0xf9  ;
z1 (ANum 0x8000b698) 0xf9  ;
z1 (ANum 0x8000b699) 0xf9  ;
z1 (ANum 0x8000b69a) 0xf9  ;
z1 (ANum 0x8000b69b) 0xf9  ;
z1 (ANum 0x8000b69f) 0xf9  ;
z1 (ANum 0x8000b6a0) 0xf9  ;
z1 (ANum 0x8000b6a1) 0xf9  ;
z1 (ANum 0x8000b6a2) 0xf9  ;
z1 (ANum 0x8000b6a3) 0xf9  ;
z1 (ANum 0x8000b83b) 0xf9  ;
z1 (ANum 0x8000b83c) 0xf9  ;
z1 (ANum 0x8000b83d) 0xf9  ;
z1 (ANum 0x8000b83e) 0xf9  ;
z1 (ANum 0x8000b83f) 0xf9  ;
z1 (ANum 0x8000b840) 0xf9  ;
z1 (ANum 0x8000b841) 0xf9  ;
z1 (ANum 0x8000b842) 0xf9  ;
z1 (ANum 0x8000b843) 0xf9  ;
z1 (ANum 0x8000b844) 0xf9  ;
z1 (ANum 0x8000b845) 0xf9  ;
z1 (ANum 0x8000b846) 0xf9  ;
z1 (ANum 0x8000b847) 0xf9  ;
z1 (ANum 0x8000b848) 0xf9  ;
z1 (ANum 0x8000b849) 0xf9  ;
z1 (ANum 0x8000b84a) 0xf9  ;
z1 (ANum 0x8000b84b) 0xf9  ;
z1 (ANum 0x8000b84c) 0xf9  ;
z1 (ANum 0x8000b84d) 0xf9  ;
z1 (ANum 0x8000b84e) 0xf9  ;
z1 (ANum 0x8000b84f) 0xf9  ;
z1 (ANum 0x8000b850) 0xf9  ;
z1 (ANum 0x8000b851) 0xf9  ;
z1 (ANum 0x8000b852) 0xf9  ;
z1 (ANum 0x8000b853) 0xf9  ;
z1 (ANum 0x8000b854) 0xf9  ;
z1 (ANum 0x8000b855) 0xf9  ;
z1 (ANum 0x8000b856) 0xf9  ;
z1 (ANum 0x8000b857) 0xf9  ;
z1 (ANum 0x8000b858) 0xf9  ;
z1 (ANum 0x8000b859) 0xf9  ;
z1 (ANum 0x8000b85a) 0xf9  ;
z1 (ANum 0x8000b85b) 0xf9  ;
z1 (ANum 0x8000b85c) 0xf9  ;
z1 (ANum 0x8000b85d) 0xf9  ;
z1 (ANum 0x8000b85e) 0xf9  ;
z1 (ANum 0x8000b85f) 0xf9  ;
z1 (ANum 0x8000b860) 0xf9  ;
z1 (ANum 0x8000b861) 0xf9  ;
z1 (ANum 0x8000b862) 0xf9  ;
z1 (ANum 0x8000b863) 0xf9  ;
z1 (ANum 0x8000b864) 0xf9  ;
z1 (ANum 0x8000b865) 0xf9  ;
z1 (ANum 0x8000b866) 0xf9  ;
z1 (ANum 0x8000b867) 0xf9  ;
z1 (ANum 0x8000b868) 0xf9  ;
z1 (ANum 0x8000b869) 0xf9  ;
z1 (ANum 0x8000b86a) 0xf9  ;
z1 (ANum 0x8000b86b) 0xf9  ;
z1 (ANum 0x8000b86c) 0xf9  ;
z1 (ANum 0x8000b86d) 0xf9  ;
z1 (ANum 0x8000b86e) 0xf9  ;
z1 (ANum 0x8000b86f) 0xf9  ;
z1 (ANum 0x8000b870) 0xf9  ;
z1 (ANum 0x8000b871) 0xf9  ;
z1 (ANum 0x8000b872) 0xf9  ;
z1 (ANum 0x8000b873) 0xf9  ;
z1 (ANum 0x8000b874) 0xf9  ;
z1 (ANum 0x8000b875) 0xf9  ;
z1 (ANum 0x8000b876) 0xf9  ;
z1 (ANum 0x8000b877) 0xf9  ;
z1 (ANum 0x8000b878) 0xf9  ;
z1 (ANum 0x8000b879) 0xf9  ;
z1 (ANum 0x8000b87a) 0xf9  ;
z1 (ANum 0x8000b87b) 0xf9  ;
z1 (ANum 0x8000b87c) 0xf9  ;
z1 (ANum 0x8000b87d) 0xf9  ;
z1 (ANum 0x8000b87e) 0xf9  ;
z1 (ANum 0x8000b87f) 0xf9  ;
z1 (ANum 0x8000b880) 0xf9  ;
z1 (ANum 0x8000b881) 0xf9  ;
z1 (ANum 0x8000b882) 0xf9  ;
z1 (ANum 0x8000b883) 0xf9  ;
z1 (ANum 0x8000b884) 0xf9  ;
z1 (ANum 0x8000b885) 0xf9  ;
z1 (ANum 0x8000b886) 0xf9  ;
z1 (ANum 0x8000b887) 0xf9  ;
z1 (ANum 0x8000b888) 0xf9  ;
z1 (ANum 0x8000b889) 0xf9  ;
z1 (ANum 0x8000b88a) 0xf9  ;
z1 (ANum 0x8000b88b) 0xf9  ;
z1 (ANum 0x8000b88c) 0xf9  ;
z1 (ANum 0x8000b88d) 0xf9  ;
z1 (ANum 0x8000b88e) 0xf9  ;
z1 (ANum 0x8000b88f) 0xf9  ;
z1 (ANum 0x8000b890) 0xf9  ;
z1 (ANum 0x8000b891) 0xf9  ;
z1 (ANum 0x8000b892) 0xf9  ;
z1 (ANum 0x8000b893) 0xf9  ;
z1 (ANum 0x8000b894) 0xf9  ;
z1 (ANum 0x8000b895) 0xf9  ;
z1 (ANum 0x8000b896) 0xf9  ;
z1 (ANum 0x8000b897) 0xf9  ;
z1 (ANum 0x8000b898) 0xf9  ;
z1 (ANum 0x8000b899) 0xf9  ;
z1 (ANum 0x8000b89a) 0xf9  ;
z1 (ANum 0x8000b89b) 0xf9  ;
z1 (ANum 0x8000b89c) 0xf9  ;
z1 (ANum 0x8000b89d) 0xf9  ;
z1 (ANum 0x8000b89e) 0xf9  ;
z1 (ANum 0x8000b89f) 0xf9  ;
z1 (ANum 0x8000c1e8) 0xf9  ;
z1 (ANum 0x8000c1e9) 0xf9  ;
z1 (ANum 0x8000c1ea) 0xf9  ;
z1 (ANum 0x8000c1eb) 0xf9  ;
z1 (ANum 0x8000c1ec) 0xf9  ;
z1 (ANum 0x8000c1ed) 0xf9  ;
z1 (ANum 0x8000c1ee) 0xf9  ;
z1 (ANum 0x8000c1ef) 0xf9  ;
z1 (ANum 0x8000c1f0) 0xf9  ;
z1 (ANum 0x8000c1f1) 0xf9  ;
z1 (ANum 0x8000c1f2) 0xf9  ;
z1 (ANum 0x8000c1f3) 0xf9  ;
z1 (ANum 0x8000c1f4) 0xf9  ;
z1 (ANum 0x8000c1f5) 0xf9  ;
z1 (ANum 0x8000c1f6) 0xf9  ;
z1 (ANum 0x8000c1f7) 0xf9  ;
z1 (ANum 0x8000c1f8) 0xf9  ;
z1 (ANum 0x8000c1f9) 0xf9  ;
z1 (ANum 0x8000c1fa) 0xf9  ;
z1 (ANum 0x8000c1fb) 0xf9  ;
z1 (ANum 0x8000c1fc) 0xf9  ;
z1 (ANum 0x8000c1fd) 0xf9  ;
z1 (ANum 0x8000c1fe) 0xf9  ;
z1 (ANum 0x8000c1ff) 0xf9  ;
z1 (ANum 0x8000c200) 0xf9  ;
z1 (ANum 0x8000c201) 0xf9  ;
z1 (ANum 0x8000c202) 0xf9  ;
z1 (ANum 0x8000c203) 0xf9  ;
z1 (ANum 0x8000c204) 0xf9  ;
z1 (ANum 0x8000c205) 0xf9  ;
z1 (ANum 0x8000c206) 0xf9  ;
z1 (ANum 0x8000c207) 0xf9  ;
z1 (ANum 0x8000c208) 0xf9  ;
z1 (ANum 0x8000c209) 0xf9  ;
z1 (ANum 0x8000c20a) 0xf9  ;
z1 (ANum 0x8000c20b) 0xf9  ;
z1 (ANum 0x8000c20c) 0xf9  ;
z1 (ANum 0x8000c20d) 0xf9  ;
z1 (ANum 0x8000c20e) 0xf9  ;
z1 (ANum 0x8000c20f) 0xf9  ;
z1 (ANum 0x8000c210) 0xf9  ;
z1 (ANum 0x8000c211) 0xf9  ;
z1 (ANum 0x8000c212) 0xf9  ;
z1 (ANum 0x8000c213) 0xf9  ;
z1 (ANum 0x8000c214) 0xf9  ;
z1 (ANum 0x8000c215) 0xf9  ;
z1 (ANum 0x8000c216) 0xf9  ;
z1 (ANum 0x8000c217) 0xf9  ;
z1 (ANum 0x8000c218) 0xf9  ;
z1 (ANum 0x8000c219) 0xf9  ;
z1 (ANum 0x8000c21a) 0xf9  ;
z1 (ANum 0x8000c21b) 0xf9  ;
z1 (ANum 0x8000c21c) 0xf9  ;
z1 (ANum 0x8000c21d) 0xf9  ;
z1 (ANum 0x8000c21e) 0xf9  ;
z1 (ANum 0x8000c21f) 0xf9  ;
z1 (ANum 0x8000c220) 0xf9  ;
z1 (ANum 0x8000c221) 0xf9  ;
z1 (ANum 0x8000c222) 0xf9  ;
z1 (ANum 0x8000c223) 0xf9  ;
z1 (ANum 0x8000c224) 0xf9  ;
z1 (ANum 0x8000c225) 0xf9  ;
z1 (ANum 0x8000c226) 0xf9  ;
z1 (ANum 0x8000c227) 0xf9  ;
z1 (ANum 0x8000c228) 0xf9  ;
z1 (ANum 0x8000c229) 0xf9  ;
z1 (ANum 0x8000c22a) 0xf9  ;
z1 (ANum 0x8000c22b) 0xf9  ;
z1 (ANum 0x8000c22c) 0xf9  ;
z1 (ANum 0x8000c22d) 0xf9  ;
z1 (ANum 0x8000c22e) 0xf9  ;
z1 (ANum 0x8000c22f) 0xf9  ;
z1 (ANum 0x8000c230) 0xf9  ;
z1 (ANum 0x8000c231) 0xf9  ;
z1 (ANum 0x8000c232) 0xf9  ;
z1 (ANum 0x8000c233) 0xf9  ;
z1 (ANum 0x8000c234) 0xf9  ;
z1 (ANum 0x8000c235) 0xf9  ;
z1 (ANum 0x8000c236) 0xf9  ;
z1 (ANum 0x8000c237) 0xf9  ;
z1 (ANum 0x8000c238) 0xf9  ;
z1 (ANum 0x8000c239) 0xf9  ;
z1 (ANum 0x8000c23a) 0xf9  ;
z1 (ANum 0x8000c23b) 0xf9  ;
z1 (ANum 0x8000c23c) 0xf9  ;
z1 (ANum 0x8000c23d) 0xf9  ;
z1 (ANum 0x8000c23e) 0xf9  ;
z1 (ANum 0x8000c23f) 0xf9  ;
z1 (ANum 0x8000c240) 0xf9  ;
z1 (ANum 0x8000c241) 0xf9  ;
z1 (ANum 0x8000c242) 0xf9  ;
z1 (ANum 0x8000c243) 0xf9  ;
z1 (ANum 0x8000c244) 0xf9  ;
z1 (ANum 0x8000c245) 0xf9  ;
z1 (ANum 0x8000c246) 0xf9  ;
z1 (ANum 0x8000c247) 0xf9  ;
z1 (ANum 0x8000c248) 0xf9  ;
z1 (ANum 0x8000c249) 0xf9  ;
z1 (ANum 0x8000c24a) 0xf9  ;
z1 (ANum 0x8000c24b) 0xf9  ;
z1 (ANum 0x8000c24c) 0xf9  ;
z1 (ANum 0x8000c24d) 0xf9  ;
z1 (ANum 0x8000c24e) 0xf9  ;
z1 (ANum 0x8000c24f) 0xf9  ;
z1 (ANum 0x8000c250) 0xf9  ;
z1 (ANum 0x8000c251) 0xf9  ;
z1 (ANum 0x8000c252) 0xf9  ;
z1 (ANum 0x8000c253) 0xf9  ;
z1 (ANum 0x8000c254) 0xf9  ;
z1 (ANum 0x8000c255) 0xf9  ;
z1 (ANum 0x8000c256) 0xf9  ;
z1 (ANum 0x8000c257) 0xf9  ;
z1 (ANum 0x8000c258) 0xf9  ;
z1 (ANum 0x8000c259) 0xf9  ;
z1 (ANum 0x8000c25a) 0xf9  ;
z1 (ANum 0x8000c25b) 0xf9  ;
z1 (ANum 0x8000c25c) 0xf9  ;
z1 (ANum 0x8000c25d) 0xf9  ;
z1 (ANum 0x8000c25e) 0xf9  ;
z1 (ANum 0x8000c25f) 0xf9  ;
z1 (ANum 0x8000c260) 0xf9  ;
z1 (ANum 0x8000c261) 0xf9  ;
z1 (ANum 0x8000c262) 0xf9  ;
z1 (ANum 0x8000c263) 0xf9  ;
z1 (ANum 0x8000c264) 0xf9  ;
z1 (ANum 0x8000c265) 0xf9  ;
z1 (ANum 0x8000c266) 0xf9  ;
z1 (ANum 0x8000c267) 0xf9  ;
z1 (ANum 0x8000c268) 0xf9  ;
z1 (ANum 0x8000c269) 0xf9  ;
z1 (ANum 0x8000c26a) 0xf9  ;
z1 (ANum 0x8000c26b) 0xf9  ;
z1 (ANum 0x8000c26c) 0xf9  ;
z1 (ANum 0x8000c26d) 0xf9  ;
z1 (ANum 0x8000c26e) 0xf9  ;
z1 (ANum 0x8000c26f) 0xf9  ;
z1 (ANum 0x8000c270) 0xf9  ;
z1 (ANum 0x8000c271) 0xf9  ;
z1 (ANum 0x8000c272) 0xf9  ;
z1 (ANum 0x8000c273) 0xf9  ;
z1 (ANum 0x8000c274) 0xf9  ;
z1 (ANum 0x8000c275) 0xf9  ;
z1 (ANum 0x8000c276) 0xf9  ;
z1 (ANum 0x8000c277) 0xf9  ;
z1 (ANum 0x8000c278) 0xf9  ;
z1 (ANum 0x8000c279) 0xf9  ;
z1 (ANum 0x8000c27a) 0xf9  ;
z1 (ANum 0x8000c27b) 0xf9  ;
z1 (ANum 0x8000c27c) 0xf9  ;
z1 (ANum 0x8000c27d) 0xf9  ;
z1 (ANum 0x8000c27e) 0xf9  ;
z1 (ANum 0x8000c27f) 0xf9  ;
z1 (ANum 0x8000c280) 0xf9  ;
z1 (ANum 0x8000c281) 0xf9  ;
z1 (ANum 0x8000c282) 0xf9  ;
z1 (ANum 0x8000c283) 0xf9  ;
z1 (ANum 0x8000c284) 0xf9  ;
z1 (ANum 0x8000c285) 0xf9  ;
z1 (ANum 0x8000c286) 0xf9  ;
z1 (ANum 0x8000c287) 0xf9  ;
z1 (ANum 0x8000c288) 0xf9  ;
z1 (ANum 0x8000c289) 0xf9  ;
z1 (ANum 0x8000c28a) 0xf9  ;
z1 (ANum 0x8000c28b) 0xf9  ;
z1 (ANum 0x8000c28c) 0xf9  ;
z1 (ANum 0x8000c28d) 0xf9  ;
z1 (ANum 0x8000c28e) 0xf9  ;
z1 (ANum 0x8000c28f) 0xf9  ;
z1 (ANum 0x8000c290) 0xf9  ;
z1 (ANum 0x8000c291) 0xf9  ;
z1 (ANum 0x8000c292) 0xf9  ;
z1 (ANum 0x8000c293) 0xf9  ;
z1 (ANum 0x8000c294) 0xf9  ;
z1 (ANum 0x8000c295) 0xf9  ;
z1 (ANum 0x8000c296) 0xf9  ;
z1 (ANum 0x8000c297) 0xf9  ;
z1 (ANum 0x8000c298) 0xf9  ;
z1 (ANum 0x8000c299) 0xf9  ;
z1 (ANum 0x8000c29a) 0xf9  ;
z1 (ANum 0x8000c29b) 0xf9  ;
z1 (ANum 0x8000c29c) 0xf9  ;
z1 (ANum 0x8000c29d) 0xf9  ;
z1 (ANum 0x8000c29e) 0xf9  ;
z1 (ANum 0x8000c29f) 0xf9  ;
z1 (ANum 0x8000c2a0) 0xf9  ;
z1 (ANum 0x8000c2a1) 0xf9  ;
z1 (ANum 0x8000c2a2) 0xf9  ;
z1 (ANum 0x8000c2a3) 0xf9  ;
z1 (ANum 0x8000c2a4) 0xf9  ;
z1 (ANum 0x8000c2a5) 0xf9  ;
z1 (ANum 0x8000c2a6) 0xf9  ;
z1 (ANum 0x8000c2a7) 0xf9  ;
z1 (ANum 0x8000c2a8) 0xf9  ;
z1 (ANum 0x8000c2a9) 0xf9  ;
z1 (ANum 0x8000c2aa) 0xf9  ;
z1 (ANum 0x8000c2ab) 0xf9  ;
z1 (ANum 0x8000c2ac) 0xf9  ;
z1 (ANum 0x8000c2ad) 0xf9  ;
z1 (ANum 0x8000c2ae) 0xf9  ;
z1 (ANum 0x8000c2af) 0xf9  ;
z1 (ANum 0x8000c2b0) 0xf9  ;
z1 (ANum 0x8000c2b1) 0xf9  ;
z1 (ANum 0x8000c2b2) 0xf9  ;
z1 (ANum 0x8000c2b3) 0xf9  ;
z1 (ANum 0x8000c2b4) 0xf9  ;
z1 (ANum 0x8000c2b5) 0xf9  ;
z1 (ANum 0x8000c2b6) 0xf9  ;
z1 (ANum 0x8000c2b7) 0xf9  ;
z1 (ANum 0x8000c2b8) 0xf9  ;
z1 (ANum 0x8000c2b9) 0xf9  ;
z1 (ANum 0x8000c2ba) 0xf9  ;
z1 (ANum 0x8000c2bb) 0xf9  ;
z1 (ANum 0x8000c2bc) 0xf9  ;
z1 (ANum 0x8000c2bd) 0xf9  ;
z1 (ANum 0x8000c2be) 0xf9  ;
z1 (ANum 0x8000c2bf) 0xf9  ;
z1 (ANum 0x8000c2c0) 0xf9  ;
z1 (ANum 0x8000c2c1) 0xf9  ;
z1 (ANum 0x8000c2c2) 0xf9  ;
z1 (ANum 0x8000c2c3) 0xf9  ;
z1 (ANum 0x8000c2c4) 0xf9  ;
z1 (ANum 0x8000c2c5) 0xf9  ;
z1 (ANum 0x8000c2c6) 0xf9  ;
z1 (ANum 0x8000c2c7) 0xf9  ;
z1 (ANum 0x8000c2c8) 0xf9  ;
z1 (ANum 0x8000c2c9) 0xf9  ;
z1 (ANum 0x8000c2ca) 0xf9  ;
z1 (ANum 0x8000c2cb) 0xf9  ;
z1 (ANum 0x8000c2cc) 0xf9  ;
z1 (ANum 0x8000c2cd) 0xf9  ;
z1 (ANum 0x8000c2ce) 0xf9  ;
z1 (ANum 0x8000c2cf) 0xf9  ;
z1 (ANum 0x8000c2d0) 0xf9  ;
z1 (ANum 0x8000c2d1) 0xf9  ;
z1 (ANum 0x8000c2d2) 0xf9  ;
z1 (ANum 0x8000c2d3) 0xf9  ;
z1 (ANum 0x8000c2d4) 0xf9  ;
z1 (ANum 0x8000c2d5) 0xf9  ;
z1 (ANum 0x8000c2d6) 0xf9  ;
z1 (ANum 0x8000c2d7) 0xf9  ;
z1 (ANum 0x8000c2d8) 0xf9  ;
z1 (ANum 0x8000c2d9) 0xf9  ;
z1 (ANum 0x8000c2da) 0xf9  ;
z1 (ANum 0x8000c2db) 0xf9  ;
z1 (ANum 0x8000c2dc) 0xf9  ;
z1 (ANum 0x8000c2dd) 0xf9  ;
z1 (ANum 0x8000c2de) 0xf9  ;
z1 (ANum 0x8000c2df) 0xf9  ;
z1 (ANum 0x8000c2e0) 0xf9  ;
z1 (ANum 0x8000c2e1) 0xf9  ;
z1 (ANum 0x8000c2e2) 0xf9  ;
z1 (ANum 0x8000c2e3) 0xf9  ;
z1 (ANum 0x8000c2e4) 0xf9  ;
z1 (ANum 0x8000c2e5) 0xf9  ;
z1 (ANum 0x8000c2e6) 0xf9  ;
z1 (ANum 0x8000c2e7) 0xf9  ;
z1 (ANum 0x8000c2e8) 0xf9  ;
z1 (ANum 0x8000c2e9) 0xf9  ;
z1 (ANum 0x8000c2ea) 0xf9  ;
z1 (ANum 0x8000c2eb) 0xf9  ;
z1 (ANum 0x8000c2ec) 0xf9  ;
z1 (ANum 0x8000c2ed) 0xf9  ;
z1 (ANum 0x8000c2ee) 0xf9  ;
z1 (ANum 0x8000c2ef) 0xf9  ;
z1 (ANum 0x8000c2f0) 0xf9  ;
z1 (ANum 0x8000c2f1) 0xf9  ;
z1 (ANum 0x8000c2f2) 0xf9  ;
z1 (ANum 0x8000c2f3) 0xf9  ;
z1 (ANum 0x8000c2f4) 0xf9  ;
z1 (ANum 0x8000c2f5) 0xf9  ;
z1 (ANum 0x8000c2f6) 0xf9  ;
z1 (ANum 0x8000c2f7) 0xf9  ;
z1 (ANum 0x8000c2f8) 0xf9  ;
z1 (ANum 0x8000c2f9) 0xf9  ;
z1 (ANum 0x8000c2fa) 0xf9  ;
z1 (ANum 0x8000c2fb) 0xf9  ;
z1 (ANum 0x8000c2fc) 0xf9  ;
z1 (ANum 0x8000c2fd) 0xf9  ;
z1 (ANum 0x8000c2fe) 0xf9  ;
z1 (ANum 0x8000c2ff) 0xf9  ;
z1 (ANum 0x8000c300) 0xf9  ;
z1 (ANum 0x8000c301) 0xf9  ;
z1 (ANum 0x8000c302) 0xf9  ;
z1 (ANum 0x8000c303) 0xf9  ;
z1 (ANum 0x8000c304) 0xf9  ;
z1 (ANum 0x8000c305) 0xf9  ;
z1 (ANum 0x8000c306) 0xf9  ;
z1 (ANum 0x8000c307) 0xf9  ;
z1 (ANum 0x8000c308) 0xf9  ;
z1 (ANum 0x8000c309) 0xf9  ;
z1 (ANum 0x8000c30a) 0xf9  ;
z1 (ANum 0x8000c30b) 0xf9  ;
z1 (ANum 0x8000c30c) 0xf9  ;
z1 (ANum 0x8000c30d) 0xf9  ;
z1 (ANum 0x8000c30e) 0xf9  ;
z1 (ANum 0x8000c30f) 0xf9  ;
z1 (ANum 0x8000c310) 0xf9  ;
z1 (ANum 0x8000c311) 0xf9  ;
z1 (ANum 0x8000c312) 0xf9  ;
z1 (ANum 0x8000c313) 0xf9  ;
z1 (ANum 0x8000c314) 0xf9  ;
z1 (ANum 0x8000c315) 0xf9  ;
z1 (ANum 0x8000c316) 0xf9  ;
z1 (ANum 0x8000c317) 0xf9  ;
z1 (ANum 0x8000c318) 0xf9  ;
z1 (ANum 0x8000c319) 0xf9  ;
z1 (ANum 0x8000c31a) 0xf9  ;
z1 (ANum 0x8000c31b) 0xf9  ;
z1 (ANum 0x8000c31c) 0xf9  ;
z1 (ANum 0x8000c31d) 0xf9  ;
z1 (ANum 0x8000c31e) 0xf9  ;
z1 (ANum 0x8000c31f) 0xf9  ;
z1 (ANum 0x8000c320) 0xf9  ;
z1 (ANum 0x8000c321) 0xf9  ;
z1 (ANum 0x8000c322) 0xf9  ;
z1 (ANum 0x8000c323) 0xf9  ;
z1 (ANum 0x8000c324) 0xf9  ;
z1 (ANum 0x8000c325) 0xf9  ;
z1 (ANum 0x8000c326) 0xf9  ;
z1 (ANum 0x8000c327) 0xf9  ;
z1 (ANum 0x8000c328) 0xf9  ;
z1 (ANum 0x8000c329) 0xf9  ;
z1 (ANum 0x8000c32a) 0xf9  ;
z1 (ANum 0x8000c32b) 0xf9  ;
z1 (ANum 0x8000c32c) 0xf9  ;
z1 (ANum 0x8000c32d) 0xf9  ;
z1 (ANum 0x8000c32e) 0xf9  ;
z1 (ANum 0x8000c32f) 0xf9  ;
z1 (ANum 0x8000c330) 0xf9  ;
z1 (ANum 0x8000c331) 0xf9  ;
z1 (ANum 0x8000c332) 0xf9  ;
z1 (ANum 0x8000c333) 0xf9  ;
z1 (ANum 0x8000c334) 0xf9  ;
z1 (ANum 0x8000c335) 0xf9  ;
z1 (ANum 0x8000c336) 0xf9  ;
z1 (ANum 0x8000c337) 0xf9  ;
z1 (ANum 0x8000c338) 0xf9  ;
z1 (ANum 0x8000c339) 0xf9  ;
z1 (ANum 0x8000c33a) 0xf9  ;
z1 (ANum 0x8000c33b) 0xf9  ;
z1 (ANum 0x8000c33c) 0xf9  ;
z1 (ANum 0x8000c33d) 0xf9  ;
z1 (ANum 0x8000c33e) 0xf9  ;
z1 (ANum 0x8000c33f) 0xf9  ;
z1 (ANum 0x8000c340) 0xf9  ;
z1 (ANum 0x8000c341) 0xf9  ;
z1 (ANum 0x8000c342) 0xf9  ;
z1 (ANum 0x8000c343) 0xf9  ;
z1 (ANum 0x8000c344) 0xf9  ;
z1 (ANum 0x8000c345) 0xf9  ;
z1 (ANum 0x8000c346) 0xf9  ;
z1 (ANum 0x8000c347) 0xf9  ;
z1 (ANum 0x8000c348) 0xf9  ;
z1 (ANum 0x8000c349) 0xf9  ;
z1 (ANum 0x8000c34a) 0xf9  ;
z1 (ANum 0x8000c34b) 0xf9  ;
z1 (ANum 0x8000c34c) 0xf9  ;
z1 (ANum 0x8000c34d) 0xf9  ;
z1 (ANum 0x8000c34e) 0xf9  ;
z1 (ANum 0x8000c34f) 0xf9  ;
z1 (ANum 0x8000c350) 0xf9  ;
z1 (ANum 0x8000c351) 0xf9  ;
z1 (ANum 0x8000c352) 0xf9  ;
z1 (ANum 0x8000c353) 0xf9  ;
z1 (ANum 0x8000c354) 0xf9  ;
z1 (ANum 0x8000c355) 0xf9  ;
z1 (ANum 0x8000c356) 0xf9  ;
z1 (ANum 0x8000c357) 0xf9  ;
z1 (ANum 0x8000c358) 0xf9  ;
z1 (ANum 0x8000c359) 0xf9  ;
z1 (ANum 0x8000c35a) 0xf9  ;
z1 (ANum 0x8000c35b) 0xf9  ;
z1 (ANum 0x8000c35c) 0xf9  ;
z1 (ANum 0x8000c35d) 0xf9  ;
z1 (ANum 0x8000c35e) 0xf9  ;
z1 (ANum 0x8000c35f) 0xf9  ;
z1 (ANum 0x8000c360) 0xf9  ;
z1 (ANum 0x8000c361) 0xf9  ;
z1 (ANum 0x8000c362) 0xf9  ;
z1 (ANum 0x8000c363) 0xf9  ;
z1 (ANum 0x8000c364) 0xf9  ;
z1 (ANum 0x8000c365) 0xf9  ;
z1 (ANum 0x8000c366) 0xf9  ;
z1 (ANum 0x8000c367) 0xf9  ;
z1 (ANum 0x8000c368) 0xf9  ;
z1 (ANum 0x8000c369) 0xf9  ;
z1 (ANum 0x8000c36a) 0xf9  ;
z1 (ANum 0x8000c36b) 0xf9  ;
z1 (ANum 0x8000c36c) 0xf9  ;
z1 (ANum 0x8000c36d) 0xf9  ;
z1 (ANum 0x8000c36e) 0xf9  ;
z1 (ANum 0x8000c36f) 0xf9  ;
z1 (ANum 0x8000c370) 0xf9  ;
z1 (ANum 0x8000c371) 0xf9  ;
z1 (ANum 0x8000c372) 0xf9  ;
z1 (ANum 0x8000c373) 0xf9  ;
z1 (ANum 0x8000c374) 0xf9  ;
z1 (ANum 0x8000c375) 0xf9  ;
z1 (ANum 0x8000c376) 0xf9  ;
z1 (ANum 0x8000c377) 0xf9  ;
z1 (ANum 0x8000c378) 0xf9  ;
z1 (ANum 0x8000c379) 0xf9  ;
z1 (ANum 0x8000c37a) 0xf9  ;
z1 (ANum 0x8000c37b) 0xf9  ;
z1 (ANum 0x8000c37c) 0xf9  ;
z1 (ANum 0x8000c37d) 0xf9  ;
z1 (ANum 0x8000c37e) 0xf9  ;
z1 (ANum 0x8000c37f) 0xf9   ].
Definition Tfib_const (ly : alayout) : list acell := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow.
Definition Tfib_zero_shadow : list (Z * Z) :=
[ (0x10000, 0x20f80 - 0x10000); (0x21000, 0x21020 - 0x21000); (0x210a0, 0x210a8 - 0x210a0); (0x210e0, 0x21120 - 0x210e0); (0x211a0, 0x211a8 - 0x211a0); (0x21240, 0x21260 - 0x21240); (0x21280, 0x21290 - 0x21280); (0x212e0, 0x212f0 - 0x212e0); (0x21360, 0x21378 - 0x21360); (0x213a0, 0x213a8 - 0x213a0); (0x213c0, 0x213d8 - 0x213c0); (0x21420, 0x21430 - 0x21420); (0x21460, 0x21468 - 0x21460); (0x214a0, 0x214b8 - 0x214a0); (0x214e0, 0x214e8 - 0x214e0); (0x21520, 0x21538 - 0x21520); (0x21560, 0x21568 - 0x21560); (0x215a0, 0x215b8 - 0x215a0); (0x215e0, 0x215e8 - 0x215e0); (0x21620, 0x21630 - 0x21620); (0x21660, 0x21668 - 0x21660); (0x216a0, 0x216b0 - 0x216a0); (0x216e0, 0x216e8 - 0x216e0); (0x21720, 0x21738 - 0x21720); (0x21760, 0x21768 - 0x21760); (0x21780, 0x9b478 - 0x21780); (0x9b4a0, 0x9b4b8 - 0x9b4a0); (0x9b4e0, 0x9b4f8 - 0x9b4e0); (0x9b520, 0x9c1d8 - 0x9b520); (0x9c500, 0xa0f40 - 0x9c500); (0xa1c00, YImgTop.IMG_TOP - 0xa1c00) ].
Definition Tfib_universe : list (list Z) :=
[[0x52d50];
[0x52d50; 0x803a0];
[0x52d50; 0x804d0];
[0x52d50; 0x8069c];
[0x52d50; 0x80da4];
[0x52d50; 0x80da4; 0x80670];
[0x52d50; 0x815d8];
[0x52d50; 0x815d8; 0x80670];
[0x52d50; 0x818ec];
[0x52d50; 0x818ec; 0x80670];
[0x52d50; 0x81928];
[0x52d50; 0x81928; 0x80670];
[0x52d50; 0x82368];
[0x52d50; 0x82368; 0x80670];
[0x52d50; 0x82370];
[0x52d50; 0x82370; 0x80670];
[0x52d50; 0x82378];
[0x52d50; 0x82378; 0x80670];
[0x52eb0];
[0x52eb0; 0x80328];
[0x52eb0; 0x8037c];
[0x52eb0; 0x80608];
[0x52eb0; 0x80c94];
[0x52eb0; 0x80c94; 0x80670];
[0x52eb0; 0x82814];
[0x52eb0; 0x82814; 0x80670]].
End StartupB.

(* The allocator's return addresses (HMRA, HFRA). The start-up of record carries no B Tfib_code
   (the earlier commit lacks lib/ReusableB/YF0l.v), so no table is copied for them. The values are the B core's code
   table as staged: a dry run's AF0l.v:9-10 (sha256 11196f2664c2428a...) and
   the B stage's lib/ReusableB/YF0l.v:10-11 (the file in this tree; only its header lines differ from the staged copy), both
   pc_malloc_ra0 := 0x52eb0 and pc_free_ra0 := 0x52d50. The start-up tables agree: the traces [0x52eb0] and
   [0x52d50] are YF0m.v:26-28 DRV_TRACES (TfibSyms ts_universe_drv) and are in Tfib_universe above. *)

From Stdlib Require Import NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable IdentRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa IdentBImg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput buf_of IdentEntryLink.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the checks (GrantCloseChk.v :38-62, with glob_chk relaxed) ------------------------------------------------ *)
(* The shadow byte at s is one of the start-up certificate's one-byte cells. *)
Definition is_shc (s : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum _)) => Z.eqb s' s | _ => false end.
Definition is_shv (s v : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum v')) => (Z.eqb s' s && Z.eqb v' v)%bool | _ => false end.

(* The end (in granules) of the zero-shadow range that holds granule k, if one does. *)
Fixpoint zfind (k : Z) (zs : list (Z * Z)) : option Z :=
  match zs with
  | [] => None
  | (q, m) :: r => if ((q / 8 <=? k) && (k <? (q + m) / 8))%bool then Some ((q + m) / 8) else zfind k r
  end.

(* Every granule of [k, hi) is in a range of zs or has a cell in cells. *)
Fixpoint vscan (zs : list (Z * Z)) (cells : list acell) (fuel : nat) (k hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? k then true else
      match zfind k zs with
      | Some e => vscan zs cells f e hi
      | None => (existsb (is_shc (SHADOW_OFF + k)) cells && vscan zs cells f (k + 1) hi)%bool
      end
  end.

(* A registered global (q, sz): q is granule-aligned, its full part [q, q + sz / 8 * 8) lies in one range of zs,
   and, when sz mod 8 <> 0, its last, partial granule has the cell `sz mod 8` in cells. RELAXED from fuzz_grant's
   glob_chk (GrantCloseChk.v:64), which asks for the zs range even when the full part is empty (sz < 8) and so
   rejects the 22 globals of fuzz_identity.asan-ubsan smaller than 8 bytes: here an empty full part
   (sz / 8 = 0) needs no range. Nothing else changes; glob_chk_r_sound below is the soundness lemma. *)
Definition glob_chk_r (zs : list (Z * Z)) (cells : list acell) (g : Z * Z) : bool :=
  ((fst g mod 8 =? 0) && (0 <=? snd g) &&
   ((snd g / 8 =? 0) || existsb (fun r => (fst r <=? fst g) && (fst g + snd g / 8 * 8 <=? fst r + snd r)) zs) &&
   ((snd g mod 8 =? 0) || existsb (is_shv (SHADOW_OFF + fst g / 8 + snd g / 8) (snd g mod 8)) cells))%bool.

(* [a, a + n) lies in one range of zs. *)
Definition zs_cov_b (zs : list (Z * Z)) (a n : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a + n <=? fst r + snd r))%bool zs.

(* The allocator's universe holds the call trace of each context (amalloc04_rule / afree04_rule's
   `call_trace0 pc0 regs ch`, rewritten to the link's text): HUMM / HUMF at the contexts c, HUMB at buf_of's
   contexts ra :: c, whose trace has buf_of's malloc return address in place of ra. *)
Definition lz_in (t : list Z) (U : list (list Z)) : bool :=
  existsb (fun u => if list_eq_dec Z.eq_dec u t then true else false) U.
Definition hum_tr (ra0 : Z) (c : list Z) : list Z :=
  firstn kUnwindMax (ra0 :: flat_map (fun r => if r =? ra0 then [] else [r]) c).
Definition hum_chk (ra0 : Z) (ctx U : list (list Z)) : bool :=
  forallb (fun c => lz_in (hum_tr ra0 c) U) ctx.
Definition humb_chk (ra0 rab : Z) (ctx U : list (list Z)) : bool :=
  forallb (fun x => match x with [] => true | _ :: c => lz_in (hum_tr ra0 (rab :: c)) U end) ctx.

(* ---- what the checks say ------------------------------------------------------------------------------------- *)
Lemma le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.

Lemma is_shc_eq : forall s c, is_shc s c = true -> exists v, c = z1 (ANum s) v.
Proof.
intros s [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply Z.eqb_eq in H. subst. eexists. reflexivity.
Qed.

Lemma is_shv_eq : forall s v c, is_shv s v c = true -> c = z1 (ANum s) v.
Proof.
intros s v [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma zfind_some : forall k zs e, zfind k zs = Some e ->
  exists q m, In (q, m) zs /\ q / 8 <= k < (q + m) / 8 /\ e = (q + m) / 8.
Proof.
intros k zs. induction zs as [|[q m] r IH]; intros e H; cbn [zfind] in H; [discriminate|].
destruct ((q / 8 <=? k) && (k <? (q + m) / 8))%bool eqn:Hb.
- injection H as <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists q, m. split; [left; reflexivity|]. split; [lia | reflexivity].
- destruct (IH e H) as (q' & m' & Hin & Hk & He). exists q', m'. split; [right; exact Hin|]. split; [exact Hk | exact He].
Qed.

Lemma vscan_ok : forall zs cells fuel k hi, vscan zs cells fuel k hi = true -> forall j, k <= j < hi ->
  (exists q m, In (q, m) zs /\ q / 8 <= j < (q + m) / 8) \/
  existsb (is_shc (SHADOW_OFF + j)) cells = true.
Proof.
intros zs cells. induction fuel as [|f IH]; intros k hi H j Hj; cbn [vscan] in H; [discriminate|].
destruct (hi <=? k) eqn:E; [apply Z.leb_le in E; exfalso; lia|].
destruct (zfind k zs) as [e|] eqn:Ez.
- destruct (zfind_some _ _ _ Ez) as (q & m & Hin & Hk & ->).
  destruct (Z_lt_le_dec j ((q + m) / 8)) as [Hlt|Hge].
  + left. exists q, m. split; [exact Hin | lia].
  + exact (IH _ _ H j (conj Hge (proj2 Hj))).
- apply andb_prop in H as [Hc H]. destruct (Z.eq_dec j k) as [->|Hne]; [right; exact Hc|].
  apply (IH _ _ H). lia.
Qed.

(* The image's shadow is mapped wherever the zero-shadow ranges and the one-byte cells say so (the argument of
   GrantClose.v:228 grant_img_shadow_vis, over any reader that holds the two tables). *)
Lemma vscan_vis : forall (rd : reader) zs cells fuel,
  (forall q m, In (q, m) zs -> q mod 8 = 0 /\ m mod 8 = 0 /\ zero_shadow rd SHADOW_OFF q m) ->
  (forall s v, In (z1 (ANum s) v) cells -> rd s = Some (YG0f.le_byte v 1 0)) ->
  vscan zs cells fuel (IMG_LO / 8) (IMG_TOP / 8) = true ->
  forall a, IMG_LO <= a < IMG_TOP -> rd (shadow_addr a) <> None.
Proof.
intros rd zs cells fuel HZ HC Hv a Ha. unfold shadow_addr.
assert (E8 : 8 * (IMG_TOP / 8) = IMG_TOP) by (vm_compute; reflexivity).
assert (Hj : IMG_LO / 8 <= a / 8 < IMG_TOP / 8).
{ split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]. }
destruct (vscan_ok _ _ _ _ _ Hv (a / 8) Hj) as [(q & m & Hin & Hq) | Hc].
- destruct (HZ q m Hin) as (Hq8 & Hm8 & Hz).
  assert (E : (q + m) / 8 = q / 8 + m / 8).
  { pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
    replace (q + m) with (m + q / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
  replace (SHADOW_OFF + a / 8) with (shadow_of_addr SHADOW_OFF q + (a / 8 - q / 8)) by (unfold shadow_of_addr; lia).
  rewrite (Hz (a / 8 - q / 8) ltac:(lia)). discriminate.
- apply existsb_exists in Hc as (c & Hin & Hb). destruct (is_shc_eq _ _ Hb) as [v ->].
  rewrite (HC _ v Hin). discriminate.
Qed.

(* Soundness of the relaxed glob check: a global the check accepts is marked as the runtime marks it, its full
   granules 0 and, when sz mod 8 <> 0 (every global of size sz < 8 among them), its partial last granule
   `sz mod 8`. The full-granule case needs a range only when sz / 8 > 0, which is when it is used. *)
Lemma glob_chk_r_sound : forall (rd : reader) zs cells q sz,
  (forall r0 m0, In (r0, m0) zs -> r0 mod 8 = 0 /\ m0 mod 8 = 0 /\ zero_shadow rd SHADOW_OFF r0 m0) ->
  (forall s v, In (z1 (ANum s) v) cells -> rd s = Some (YG0f.le_byte v 1 0)) ->
  glob_chk_r zs cells (q, sz) = true ->
  block_shadow rd SHADOW_OFF q sz.
Proof.
intros rd zs cells q sz HZ HC Hb. unfold glob_chk_r in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Bs.
pose proof (Z.div_mod (sz + 7) 8 ltac:(lia)) as Ds7. pose proof (Z.mod_pos_bound (sz + 7) 8 ltac:(lia)) as Bs7.
destruct (i <? sz / 8) eqn:Hlt.
- (* a full granule: sz / 8 > 0, so the range clause holds *)
  apply Z.ltb_lt in Hlt.
  apply orb_true_iff in Hfull as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
  apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
  destruct (HZ r0 m0 Hr) as (Hr8 & Hm8 & Hz).
  pose proof (Z.div_mod r0 8 ltac:(lia)) as Dr. pose proof (Z.div_mod m0 8 ltac:(lia)) as Dm.
  unfold shadow_of_addr.
  replace (SHADOW_OFF + q / 8 + i) with (shadow_of_addr SHADOW_OFF r0 + (q / 8 + i - r0 / 8))
    by (unfold shadow_of_addr; lia).
  apply Hz. lia.
- (* the partial last granule: its cell holds sz mod 8 *)
  apply Z.ltb_ge in Hlt.
  assert (Hi' : i = sz / 8) by lia.
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply is_shv_eq in Hcb. subst c. subst i.
  unfold shadow_of_addr. rewrite (HC _ _ Hc). rewrite le_byte1 by lia. reflexivity.
Qed.

Lemma in_zs_of_b : forall B a n, zs_cov_b (as_zero_shadow B) a n = true -> in_zs B a n.
Proof.
intros B a n H. apply existsb_exists in H as ([q m] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists q, m. split; [exact Hin|]. lia.
Qed.

Lemma lz_in_ok : forall t U, lz_in t U = true -> In t U.
Proof.
intros t U H. apply existsb_exists in H as (u & Hu & Hb).
destruct (list_eq_dec Z.eq_dec u t) as [<-|]; [exact Hu | discriminate].
Qed.

Lemma hum_chk_ok : forall ra0 ctx U, hum_chk ra0 ctx U = true -> forall c, In c ctx ->
  In (firstn kUnwindMax (ra0 :: flat_map (fun r => if r =? ra0 then [] else [r]) c)) U.
Proof. intros ra0 ctx U H c Hc. apply lz_in_ok. exact (proj1 (forallb_forall _ _) H c Hc). Qed.

Lemma humb_chk_ok : forall ra0 rab ctx U, humb_chk ra0 rab ctx U = true -> forall ra c, In (ra :: c) ctx ->
  In (firstn kUnwindMax (ra0 :: flat_map (fun r => if r =? ra0 then [] else [r]) (rab :: c))) U.
Proof. intros ra0 rab ctx U H ra c Hc. apply lz_in_ok. exact (proj1 (forallb_forall _ _) H (ra :: c) Hc). Qed.

(* ---- the checks, by computation on the copied tables (closed terms) ------------------------------------------ *)
(* IV: every granule of [IMG_LO, IMG_TOP) is in a zero-shadow range or has a one-byte cell. *)
Lemma identb_vscan :
  vscan StartupB.Tfib_zero_shadow StartupB.Tfib_const_shadow (Pos.to_nat 4096) (IMG_LO / 8) (IMG_TOP / 8) = true.
Proof. vm_compute. reflexivity. Qed.

(* GM: all 51 registered globals of the link's IDENTB_GLOBS pass the relaxed check; none is dropped. *)
Lemma identb_globs_chk :
  forallb (glob_chk_r StartupB.Tfib_zero_shadow StartupB.Tfib_const_shadow) IdentEntryLink.IDENTB_GLOBS = true.
Proof. vm_compute. reflexivity. Qed.

(* ZS_STEM / ZS_NAME: objects 18 and 22 (0x9b4a0, 0x9b4e0), 24 bytes each, lie in one zero-shadow range. *)
Lemma identb_zs_stem_chk : zs_cov_b StartupB.Tfib_zero_shadow (identb_val (A_OBJ 18)) 24 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma identb_zs_name_chk : zs_cov_b StartupB.Tfib_zero_shadow (identb_val (A_OBJ 22)) 24 = true.
Proof. vm_compute. reflexivity. Qed.

(* HUMM / HUMF / HUMB: the link's contexts with BASE = identb_val A_TEXT (pa_val of PI_identb), closed. *)
Lemma identb_humm_chk :
  hum_chk 0x52eb0
    (map (fun o => [identb_val A_TEXT + o; IdentEntryLink.RA_LLVMF]) LLVMFuzzerTestOneInput.LLVMF_MALLOC_RAS ++
     map (fun o => [identb_val A_TEXT + o]) LLVMFuzzerTestOneInput.LLVMF_MALLOC_RAS)
    StartupB.Tfib_universe = true.
Proof. vm_compute. reflexivity. Qed.
Lemma identb_humf_chk :
  hum_chk 0x52d50
    (map (fun o => [identb_val A_TEXT + o; IdentEntryLink.RA_LLVMF]) LLVMFuzzerTestOneInput.LLVMF_FREE_RAS ++
     map (fun o => [identb_val A_TEXT + o]) LLVMFuzzerTestOneInput.LLVMF_FREE_RAS)
    StartupB.Tfib_universe = true.
Proof. vm_compute. reflexivity. Qed.
Lemma identb_humb_chk :
  humb_chk 0x52eb0 (identb_val A_TEXT + AF_buf_of + 0x14)
    (map (fun o => [identb_val A_TEXT + o; IdentEntryLink.RA_LLVMF]) LLVMFuzzerTestOneInput.BUF_OF_RAS ++
     map (fun o => [identb_val A_TEXT + o]) LLVMFuzzerTestOneInput.BUF_OF_RAS)
    StartupB.Tfib_universe = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- the link's binders, at the B record ---------------------------------------------------------------------- *)
(* The context is IdentEntryLink.v's Section L (:176-182): the same Context and notations, so each conclusion below
   is the text of the link's Hypothesis line (cited per lemma). *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation PI := (@PI_identb rc).
Local Notation SEGS := (@pa_segs _ identb_listing PI).
Local Notation VAL := (@pa_val _ identb_listing PI).
Variable IdentB : asyms.
Hypothesis LAWS : AR_laws SEGS IdentB.
Hypothesis HZS : as_zero_shadow IdentB = StartupB.Tfib_zero_shadow.
Hypothesis HCONST : forall ly, as_const IdentB ly = StartupB.Tfib_const ly.
Hypothesis HUNIV : as_universe IdentB = StartupB.Tfib_universe.
Hypothesis HMRA : pc_malloc_ra0 (as_code IdentB) = 0x52eb0.
Hypothesis HFRA : pc_free_ra0 (as_code IdentB) = 0x52d50.

(* A one-byte cell of the start-up certificate holds its byte in every state (GrantClose.v:201). *)
Lemma identb_shadow_cell : forall ly S W mem md, AR SEGS IdentB ly S W mem md ->
  forall s v, In (z1 (ANum s) v) StartupB.Tfib_const_shadow -> aview SEGS (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros ly S W mem md HAR s v Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
assert (Hin' : In (z1 (ANum s) v) (as_const IdentB ly)).
{ rewrite HCONST. unfold StartupB.Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
specialize (HC _ Hin'). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

(* A zero-shadow range of the certificate is granule-aligned and reads 0 in every state (IdentRo.v zs_range,
   zs_zero: aso_zshadow and the AR law al_zshadow). *)
Lemma identb_zs_facts : forall ly S W mem md, AR SEGS IdentB ly S W mem md ->
  forall q m, In (q, m) StartupB.Tfib_zero_shadow ->
  q mod 8 = 0 /\ m mod 8 = 0 /\ zero_shadow (aview SEGS (w_H W) mem) SHADOW_OFF q m.
Proof.
intros ly S W mem md HAR q m Hin. rewrite <- HZS in Hin.
destruct (zs_range SEGS IdentB q m Hin ly S W mem md HAR) as (_ & _ & Hq & Hm & _).
split; [exact Hq|]. split; [exact Hm|].
exact (zs_zero SEGS IdentB LAWS q m Hin ly S W mem md HAR).
Qed.

(* IdentEntryLink.v:256 GM (G := IDENTB_GLOBS). *)
Lemma identb_GM : globs_marked SEGS IdentB IdentEntryLink.IDENTB_GLOBS.
Proof.
intros ly S W mem md q sz Hin HAR.
exact (glob_chk_r_sound (aview SEGS (w_H W) mem) _ _ q sz (identb_zs_facts ly S W mem md HAR)
  (identb_shadow_cell ly S W mem md HAR) (proj1 (forallb_forall _ _) identb_globs_chk (q, sz) Hin)).
Qed.

(* IdentEntryLink.v:257 IV. *)
Lemma identb_IV : img_shadow_vis SEGS IdentB.
Proof.
intros ly S W mem md a HAR Ha.
exact (vscan_vis (aview SEGS (w_H W) mem) _ _ _ (identb_zs_facts ly S W mem md HAR)
  (identb_shadow_cell ly S W mem md HAR) identb_vscan a Ha).
Qed.

(* IdentEntryLink.v:347 ZS_STEM. *)
Lemma identb_ZS_STEM : in_zs IdentB (VAL (A_OBJ 18)) 24.
Proof. apply in_zs_of_b. rewrite HZS. exact identb_zs_stem_chk. Qed.

(* IdentEntryLink.v:348 ZS_NAME. *)
Lemma identb_ZS_NAME : in_zs IdentB (VAL (A_OBJ 22)) 24.
Proof. apply in_zs_of_b. rewrite HZS. exact identb_zs_name_chk. Qed.

(* IdentEntryLink.v:698-700 HUMM. *)
Lemma identb_HUMM : forall c, In c (LLVMFuzzerTestOneInput.LLVMF_MALLOC_CTX IdentEntryLink.RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code IdentB)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code IdentB) then [] else [r]) c)) (as_universe IdentB).
Proof. intros c Hc. rewrite HMRA, HUNIV. exact (hum_chk_ok _ _ _ identb_humm_chk c Hc). Qed.

(* IdentEntryLink.v:701-703 HUMF. *)
Lemma identb_HUMF : forall c, In c (LLVMFuzzerTestOneInput.LLVMF_FREE_CTX IdentEntryLink.RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code IdentB)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code IdentB) then [] else [r]) c)) (as_universe IdentB).
Proof. intros c Hc. rewrite HFRA, HUNIV. exact (hum_chk_ok _ _ _ identb_humf_chk c Hc). Qed.

(* IdentEntryLink.v:245-248 HUMB (buf_of's universe fact at CTX_BUF_OF). *)
Lemma identb_HUMB : forall ra c, In (ra :: c) (@LLVMFuzzerTestOneInput.CTX_BUF_OF rc PI IdentEntryLink.RA_LLVMF) ->
  In (firstn kUnwindMax (pc_malloc_ra0 (as_code IdentB)
        :: flat_map (fun r => if r =? pc_malloc_ra0 (as_code IdentB) then [] else [r]) (@buf_of.RA_buf_of_malloc rc PI :: c)))
     (as_universe IdentB).
Proof. intros ra c Hc. rewrite HMRA, HUNIV. exact (humb_chk_ok _ _ _ _ identb_humb_chk ra c Hc). Qed.
End b.
