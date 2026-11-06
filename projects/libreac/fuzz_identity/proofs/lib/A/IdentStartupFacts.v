(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the start-up facts of libreac/fuzz_identity's ASan build (image A) that
   lib/A/Prog/IdentEntryLink.v (Section L) takes as the Hypotheses GM (:250), IV (:251), ZS_STEM (:340), ZS_NAME (:341),
   HUMM (:680) and HUMF (:683), each proved here with that Hypothesis's text as its conclusion. The checks and their
   lemmas are ported from fuzz_grant's closer (a working branch d110b9a519a, proofs/libreac/fuzz_grant/lib/A/Prog/
   GrantCloseChk.v:38-145 and GrantClose.v:200-287); the universe check is cgif's ACee.v:80 pattern (c8557374ad2e) in
   the start-up AD2l.v's In_of_existsb form. One change in substance: the glob check is RELAXED (see glob_chk_relaxed). *)
(* The record: premises, not the core. The core's record (IdentB, TfibB before the rename) is lib/A/AD2l.v:15, and
   lib/A/IdentTop.v:152-157 discharges the premises below from it; the start-up file lib/A/AF0m.v of a working branch 1ddc6a57e5d does not build on that branch
   (AF0m.v requires AF0l.v, which that branch does not carry). That branch's lib/A/ACej.v needs only Stdlib and lib/Reusable/YG00.v, YG01.v and YG0a.v, all on that branch; whether it builds was not measured. So, as lib/A/IdentHimgOwned.v does, the facts are stated
   in a Section over `Variable IdentB : asyms` with one premise per record field the proofs read, against verbatim
   copies of the start-up tables below:
     HZS    : as_zero_shadow IdentB = TFIB_ZERO_SHADOW_A                           (GM, IV, ZS_STEM, ZS_NAME)
     HCONST : forall ly, exists pre, as_const IdentB ly = pre ++ TFIB_CONST_SHADOW_A (GM, IV)
     HUNIV  : as_universe IdentB = TFIB_UNIVERSE_A                                 (HUMM, HUMF)
     HRA0M  : pc_malloc_ra0 (as_code IdentB) = 0x52e48                              (HUMM)
     HRA0F  : pc_free_ra0 (as_code IdentB) = 0x52ce8                                (HUMF)
   HCONST asks only that the copied shadow cells are the tail of the record's const list, because the proofs read no
   other const cell: AF0m.v:1548 has Tfib_const ly := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow. No AR law
   is a premise: the zero-shadow ranges and the const cells are fields of AR's first conjunct ARm (am_zshadow,
   am_const: Reusable/YG0n.v:211, :218), so LAWS (AR_laws) is not needed.
   The core's record meets the premises once it carries the start-up branch's AF0m.v and ACej.v.
   With the staged lib/A/AD2l.v:15-38 record (as_code := Tfib_code, as_const :=
   Tfib_const, as_zero_shadow := Tfib_zero_shadow, as_universe := Tfib_universe):
     HZS, HUNIV, HRA0M, HRA0F by eq_refl;
     HCONST by fun ly => ex_intro _ (Tfib_const_sym ++ Tfib_const_abs) (app_assoc Tfib_const_sym Tfib_const_abs Tfib_const_shadow).
   Sources of the copies (each body below is the source's text, line for line):
     TFIB_ZERO_SHADOW_A  = Tfib_zero_shadow,  lib/A/AF0m.v:1547-1548 @ a working branch 1ddc6a57e5d
     TFIB_CONST_SHADOW_A = Tfib_const_shadow, lib/A/AF0m.v:831-1545  @ the same commit (714 one-byte cells)
       (AF0m.v sha256 894ced30947c45acc73a7d40a6084da4e413f8a618308d38a44f3769b9a37840)
     TFIB_UNIVERSE_A     = Tfib_universe,     lib/A/ACej.v:170-206   @ the same commit (36 traces)
       (ACej.v sha256 db588a816896295b3992d364981615d5da509c5a50c82d50a601813113616590)
     0x52e48 / 0x52ce8   = pc_malloc_ra0 / pc_free_ra0 of Tfib_code, lib/A/AF0l.v:10-11;
       the same two values head the start-up
       record's driver traces, AF0m.v:24-26 DRV_TRACES
       @ the same commit. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO09 YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaTable PaSym IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentImg IdentFrame IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_A
check_str put_dec reac_box_catalogue reac_box_catalogue_defect reac_box_family_of reac_box_family_stem
reac_box_name reac_box_name_walk reac_identity_fw_str reac_identity_init reac_identity_ingest IngestWalk
reac_identity_reac_ver_str write_uint sb_dec sb_decWalk.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require
LLVMFuzzerTestOneInput_B LLVMFuzzerTestOneInput_C LLVMFuzzerTestOneInput_D1 LLVMFuzzerTestOneInput_D2 LLVMFuzzerTestOneInput_D3 LLVMFuzzerTestOneInput_D4
LLVMFuzzerTestOneInput_D5 LLVMFuzzerTestOneInput_D6 LLVMFuzzerTestOneInput_Loop LLVMFuzzerTestOneInput_E LLVMFuzzerTestOneInput_F
LLVMFuzzerTestOneInput_G LLVMFuzzerTestOneInput_H LLVMFuzzerTestOneInput_I LLVMFuzzerTestOneInput_J LLVMFuzzerTestOneInput_K LLVMFuzzerTestOneInput_L.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentEntryLink.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the start-up tables, verbatim (sources in the header) ------------------------------------------------- *)
Definition TFIB_ZERO_SHADOW_A : list (Z * Z) :=
[ (0x10000, 0x20f80 - 0x10000); (0x20fe0, 0x21000 - 0x20fe0); (0x21080, 0x21088 - 0x21080); (0x210c0, 0x21100 - 0x210c0); (0x21180, 0x21188 - 0x21180); (0x21220, 0x21240 - 0x21220); (0x21260, 0x21270 - 0x21260); (0x212c0, 0x212d0 - 0x212c0); (0x21340, 0x21358 - 0x21340); (0x21380, 0x21388 - 0x21380); (0x213a0, 0x213b8 - 0x213a0); (0x21400, 0x21410 - 0x21400); (0x21440, 0x21448 - 0x21440); (0x21480, 0x21498 - 0x21480); (0x214c0, 0x214c8 - 0x214c0); (0x21500, 0x21518 - 0x21500); (0x21540, 0x21548 - 0x21540); (0x21580, 0x21598 - 0x21580); (0x215c0, 0x215c8 - 0x215c0); (0x21600, 0x21610 - 0x21600); (0x21640, 0x21648 - 0x21640); (0x21680, 0x21690 - 0x21680); (0x216c0, 0x216c8 - 0x216c0); (0x21700, 0x21718 - 0x21700); (0x21740, 0x21748 - 0x21740); (0x21760, 0x9b198 - 0x21760); (0x9b1c0, 0x9b1d8 - 0x9b1c0); (0x9b200, 0x9b218 - 0x9b200); (0x9b240, 0x9bef8 - 0x9b240); (0x9c220, 0xa0c60 - 0x9c220); (0xa18e0, 0x5fa000 - 0xa18e0) ].
Definition TFIB_CONST_SHADOW_A : list acell :=
[ z1 (ANum 0x7fffc1f0) 0x2  ;
z1 (ANum 0x7fffc1f1) 0xf9  ;
z1 (ANum 0x7fffc1f2) 0xf9  ;
z1 (ANum 0x7fffc1f3) 0xf9  ;
z1 (ANum 0x7fffc1f4) 0x7  ;
z1 (ANum 0x7fffc1f5) 0xf9  ;
z1 (ANum 0x7fffc1f6) 0xf9  ;
z1 (ANum 0x7fffc1f7) 0xf9  ;
z1 (ANum 0x7fffc1f8) 0x6  ;
z1 (ANum 0x7fffc1f9) 0xf9  ;
z1 (ANum 0x7fffc1fa) 0xf9  ;
z1 (ANum 0x7fffc1fb) 0xf9  ;
z1 (ANum 0x7fffc200) 0x4  ;
z1 (ANum 0x7fffc201) 0xf9  ;
z1 (ANum 0x7fffc202) 0xf9  ;
z1 (ANum 0x7fffc203) 0xf9  ;
z1 (ANum 0x7fffc204) 0xf9  ;
z1 (ANum 0x7fffc205) 0xf9  ;
z1 (ANum 0x7fffc206) 0xf9  ;
z1 (ANum 0x7fffc207) 0xf9  ;
z1 (ANum 0x7fffc208) 0x7  ;
z1 (ANum 0x7fffc209) 0xf9  ;
z1 (ANum 0x7fffc20a) 0xf9  ;
z1 (ANum 0x7fffc20b) 0xf9  ;
z1 (ANum 0x7fffc20c) 0x7  ;
z1 (ANum 0x7fffc20d) 0xf9  ;
z1 (ANum 0x7fffc20e) 0xf9  ;
z1 (ANum 0x7fffc20f) 0xf9  ;
z1 (ANum 0x7fffc211) 0xf9  ;
z1 (ANum 0x7fffc212) 0xf9  ;
z1 (ANum 0x7fffc213) 0xf9  ;
z1 (ANum 0x7fffc214) 0x5  ;
z1 (ANum 0x7fffc215) 0xf9  ;
z1 (ANum 0x7fffc216) 0xf9  ;
z1 (ANum 0x7fffc217) 0xf9  ;
z1 (ANum 0x7fffc220) 0x4  ;
z1 (ANum 0x7fffc221) 0xf9  ;
z1 (ANum 0x7fffc222) 0xf9  ;
z1 (ANum 0x7fffc223) 0xf9  ;
z1 (ANum 0x7fffc224) 0xf9  ;
z1 (ANum 0x7fffc225) 0xf9  ;
z1 (ANum 0x7fffc226) 0xf9  ;
z1 (ANum 0x7fffc227) 0xf9  ;
z1 (ANum 0x7fffc228) 0x7  ;
z1 (ANum 0x7fffc229) 0xf9  ;
z1 (ANum 0x7fffc22a) 0xf9  ;
z1 (ANum 0x7fffc22b) 0xf9  ;
z1 (ANum 0x7fffc22c) 0x7  ;
z1 (ANum 0x7fffc22d) 0xf9  ;
z1 (ANum 0x7fffc22e) 0xf9  ;
z1 (ANum 0x7fffc22f) 0xf9  ;
z1 (ANum 0x7fffc231) 0xf9  ;
z1 (ANum 0x7fffc232) 0xf9  ;
z1 (ANum 0x7fffc233) 0xf9  ;
z1 (ANum 0x7fffc234) 0x5  ;
z1 (ANum 0x7fffc235) 0xf9  ;
z1 (ANum 0x7fffc236) 0xf9  ;
z1 (ANum 0x7fffc237) 0xf9  ;
z1 (ANum 0x7fffc238) 0x3  ;
z1 (ANum 0x7fffc239) 0xf9  ;
z1 (ANum 0x7fffc23a) 0xf9  ;
z1 (ANum 0x7fffc23b) 0xf9  ;
z1 (ANum 0x7fffc23c) 0x7  ;
z1 (ANum 0x7fffc23d) 0xf9  ;
z1 (ANum 0x7fffc23e) 0xf9  ;
z1 (ANum 0x7fffc23f) 0xf9  ;
z1 (ANum 0x7fffc240) 0x6  ;
z1 (ANum 0x7fffc241) 0xf9  ;
z1 (ANum 0x7fffc242) 0xf9  ;
z1 (ANum 0x7fffc243) 0xf9  ;
z1 (ANum 0x7fffc248) 0x6  ;
z1 (ANum 0x7fffc249) 0xf9  ;
z1 (ANum 0x7fffc24a) 0xf9  ;
z1 (ANum 0x7fffc24b) 0xf9  ;
z1 (ANum 0x7fffc24e) 0x7  ;
z1 (ANum 0x7fffc24f) 0xf9  ;
z1 (ANum 0x7fffc250) 0xf9  ;
z1 (ANum 0x7fffc251) 0xf9  ;
z1 (ANum 0x7fffc252) 0xf9  ;
z1 (ANum 0x7fffc253) 0xf9  ;
z1 (ANum 0x7fffc254) 0x6  ;
z1 (ANum 0x7fffc255) 0xf9  ;
z1 (ANum 0x7fffc256) 0xf9  ;
z1 (ANum 0x7fffc257) 0xf9  ;
z1 (ANum 0x7fffc25a) 0x6  ;
z1 (ANum 0x7fffc25b) 0xf9  ;
z1 (ANum 0x7fffc25c) 0xf9  ;
z1 (ANum 0x7fffc25d) 0xf9  ;
z1 (ANum 0x7fffc25e) 0xf9  ;
z1 (ANum 0x7fffc25f) 0xf9  ;
z1 (ANum 0x7fffc260) 0x7  ;
z1 (ANum 0x7fffc261) 0xf9  ;
z1 (ANum 0x7fffc262) 0xf9  ;
z1 (ANum 0x7fffc263) 0xf9  ;
z1 (ANum 0x7fffc264) 0x7  ;
z1 (ANum 0x7fffc265) 0xf9  ;
z1 (ANum 0x7fffc266) 0xf9  ;
z1 (ANum 0x7fffc267) 0xf9  ;
z1 (ANum 0x7fffc26b) 0x5  ;
z1 (ANum 0x7fffc26c) 0xf9  ;
z1 (ANum 0x7fffc26d) 0xf9  ;
z1 (ANum 0x7fffc26e) 0xf9  ;
z1 (ANum 0x7fffc26f) 0xf9  ;
z1 (ANum 0x7fffc271) 0x4  ;
z1 (ANum 0x7fffc272) 0xf9  ;
z1 (ANum 0x7fffc273) 0xf9  ;
z1 (ANum 0x7fffc277) 0x5  ;
z1 (ANum 0x7fffc278) 0xf9  ;
z1 (ANum 0x7fffc279) 0xf9  ;
z1 (ANum 0x7fffc27a) 0xf9  ;
z1 (ANum 0x7fffc27b) 0xf9  ;
z1 (ANum 0x7fffc27c) 0x6  ;
z1 (ANum 0x7fffc27d) 0xf9  ;
z1 (ANum 0x7fffc27e) 0xf9  ;
z1 (ANum 0x7fffc27f) 0xf9  ;
z1 (ANum 0x7fffc282) 0x7  ;
z1 (ANum 0x7fffc283) 0xf9  ;
z1 (ANum 0x7fffc284) 0xf9  ;
z1 (ANum 0x7fffc285) 0xf9  ;
z1 (ANum 0x7fffc286) 0xf9  ;
z1 (ANum 0x7fffc287) 0xf9  ;
z1 (ANum 0x7fffc289) 0xf9  ;
z1 (ANum 0x7fffc28a) 0xf9  ;
z1 (ANum 0x7fffc28b) 0xf9  ;
z1 (ANum 0x7fffc28c) 0x6  ;
z1 (ANum 0x7fffc28d) 0xf9  ;
z1 (ANum 0x7fffc28e) 0xf9  ;
z1 (ANum 0x7fffc28f) 0xf9  ;
z1 (ANum 0x7fffc293) 0xf9  ;
z1 (ANum 0x7fffc294) 0xf9  ;
z1 (ANum 0x7fffc295) 0xf9  ;
z1 (ANum 0x7fffc296) 0xf9  ;
z1 (ANum 0x7fffc297) 0xf9  ;
z1 (ANum 0x7fffc299) 0xf9  ;
z1 (ANum 0x7fffc29a) 0xf9  ;
z1 (ANum 0x7fffc29b) 0xf9  ;
z1 (ANum 0x7fffc29c) 0x7  ;
z1 (ANum 0x7fffc29d) 0xf9  ;
z1 (ANum 0x7fffc29e) 0xf9  ;
z1 (ANum 0x7fffc29f) 0xf9  ;
z1 (ANum 0x7fffc2a3) 0xf9  ;
z1 (ANum 0x7fffc2a4) 0xf9  ;
z1 (ANum 0x7fffc2a5) 0xf9  ;
z1 (ANum 0x7fffc2a6) 0xf9  ;
z1 (ANum 0x7fffc2a7) 0xf9  ;
z1 (ANum 0x7fffc2a9) 0x1  ;
z1 (ANum 0x7fffc2aa) 0xf9  ;
z1 (ANum 0x7fffc2ab) 0xf9  ;
z1 (ANum 0x7fffc2ac) 0x7  ;
z1 (ANum 0x7fffc2ad) 0xf9  ;
z1 (ANum 0x7fffc2ae) 0xf9  ;
z1 (ANum 0x7fffc2af) 0xf9  ;
z1 (ANum 0x7fffc2b3) 0xf9  ;
z1 (ANum 0x7fffc2b4) 0xf9  ;
z1 (ANum 0x7fffc2b5) 0xf9  ;
z1 (ANum 0x7fffc2b6) 0xf9  ;
z1 (ANum 0x7fffc2b7) 0xf9  ;
z1 (ANum 0x7fffc2b9) 0x1  ;
z1 (ANum 0x7fffc2ba) 0xf9  ;
z1 (ANum 0x7fffc2bb) 0xf9  ;
z1 (ANum 0x7fffc2bc) 0x7  ;
z1 (ANum 0x7fffc2bd) 0xf9  ;
z1 (ANum 0x7fffc2be) 0xf9  ;
z1 (ANum 0x7fffc2bf) 0xf9  ;
z1 (ANum 0x7fffc2c2) 0x7  ;
z1 (ANum 0x7fffc2c3) 0xf9  ;
z1 (ANum 0x7fffc2c4) 0xf9  ;
z1 (ANum 0x7fffc2c5) 0xf9  ;
z1 (ANum 0x7fffc2c6) 0xf9  ;
z1 (ANum 0x7fffc2c7) 0xf9  ;
z1 (ANum 0x7fffc2c9) 0xf9  ;
z1 (ANum 0x7fffc2ca) 0xf9  ;
z1 (ANum 0x7fffc2cb) 0xf9  ;
z1 (ANum 0x7fffc2cc) 0x7  ;
z1 (ANum 0x7fffc2cd) 0xf9  ;
z1 (ANum 0x7fffc2ce) 0xf9  ;
z1 (ANum 0x7fffc2cf) 0xf9  ;
z1 (ANum 0x7fffc2d2) 0x7  ;
z1 (ANum 0x7fffc2d3) 0xf9  ;
z1 (ANum 0x7fffc2d4) 0xf9  ;
z1 (ANum 0x7fffc2d5) 0xf9  ;
z1 (ANum 0x7fffc2d6) 0xf9  ;
z1 (ANum 0x7fffc2d7) 0xf9  ;
z1 (ANum 0x7fffc2d9) 0xf9  ;
z1 (ANum 0x7fffc2da) 0xf9  ;
z1 (ANum 0x7fffc2db) 0xf9  ;
z1 (ANum 0x7fffc2dc) 0x7  ;
z1 (ANum 0x7fffc2dd) 0xf9  ;
z1 (ANum 0x7fffc2de) 0xf9  ;
z1 (ANum 0x7fffc2df) 0xf9  ;
z1 (ANum 0x7fffc2e3) 0xf9  ;
z1 (ANum 0x7fffc2e4) 0xf9  ;
z1 (ANum 0x7fffc2e5) 0xf9  ;
z1 (ANum 0x7fffc2e6) 0xf9  ;
z1 (ANum 0x7fffc2e7) 0xf9  ;
z1 (ANum 0x7fffc2e9) 0xf9  ;
z1 (ANum 0x7fffc2ea) 0xf9  ;
z1 (ANum 0x7fffc2eb) 0xf9  ;
z1 (ANum 0x8000b633) 0xf9  ;
z1 (ANum 0x8000b634) 0xf9  ;
z1 (ANum 0x8000b635) 0xf9  ;
z1 (ANum 0x8000b636) 0xf9  ;
z1 (ANum 0x8000b637) 0xf9  ;
z1 (ANum 0x8000b63b) 0xf9  ;
z1 (ANum 0x8000b63c) 0xf9  ;
z1 (ANum 0x8000b63d) 0xf9  ;
z1 (ANum 0x8000b63e) 0xf9  ;
z1 (ANum 0x8000b63f) 0xf9  ;
z1 (ANum 0x8000b643) 0xf9  ;
z1 (ANum 0x8000b644) 0xf9  ;
z1 (ANum 0x8000b645) 0xf9  ;
z1 (ANum 0x8000b646) 0xf9  ;
z1 (ANum 0x8000b647) 0xf9  ;
z1 (ANum 0x8000b7df) 0xf9  ;
z1 (ANum 0x8000b7e0) 0xf9  ;
z1 (ANum 0x8000b7e1) 0xf9  ;
z1 (ANum 0x8000b7e2) 0xf9  ;
z1 (ANum 0x8000b7e3) 0xf9  ;
z1 (ANum 0x8000b7e4) 0xf9  ;
z1 (ANum 0x8000b7e5) 0xf9  ;
z1 (ANum 0x8000b7e6) 0xf9  ;
z1 (ANum 0x8000b7e7) 0xf9  ;
z1 (ANum 0x8000b7e8) 0xf9  ;
z1 (ANum 0x8000b7e9) 0xf9  ;
z1 (ANum 0x8000b7ea) 0xf9  ;
z1 (ANum 0x8000b7eb) 0xf9  ;
z1 (ANum 0x8000b7ec) 0xf9  ;
z1 (ANum 0x8000b7ed) 0xf9  ;
z1 (ANum 0x8000b7ee) 0xf9  ;
z1 (ANum 0x8000b7ef) 0xf9  ;
z1 (ANum 0x8000b7f0) 0xf9  ;
z1 (ANum 0x8000b7f1) 0xf9  ;
z1 (ANum 0x8000b7f2) 0xf9  ;
z1 (ANum 0x8000b7f3) 0xf9  ;
z1 (ANum 0x8000b7f4) 0xf9  ;
z1 (ANum 0x8000b7f5) 0xf9  ;
z1 (ANum 0x8000b7f6) 0xf9  ;
z1 (ANum 0x8000b7f7) 0xf9  ;
z1 (ANum 0x8000b7f8) 0xf9  ;
z1 (ANum 0x8000b7f9) 0xf9  ;
z1 (ANum 0x8000b7fa) 0xf9  ;
z1 (ANum 0x8000b7fb) 0xf9  ;
z1 (ANum 0x8000b7fc) 0xf9  ;
z1 (ANum 0x8000b7fd) 0xf9  ;
z1 (ANum 0x8000b7fe) 0xf9  ;
z1 (ANum 0x8000b7ff) 0xf9  ;
z1 (ANum 0x8000b800) 0xf9  ;
z1 (ANum 0x8000b801) 0xf9  ;
z1 (ANum 0x8000b802) 0xf9  ;
z1 (ANum 0x8000b803) 0xf9  ;
z1 (ANum 0x8000b804) 0xf9  ;
z1 (ANum 0x8000b805) 0xf9  ;
z1 (ANum 0x8000b806) 0xf9  ;
z1 (ANum 0x8000b807) 0xf9  ;
z1 (ANum 0x8000b808) 0xf9  ;
z1 (ANum 0x8000b809) 0xf9  ;
z1 (ANum 0x8000b80a) 0xf9  ;
z1 (ANum 0x8000b80b) 0xf9  ;
z1 (ANum 0x8000b80c) 0xf9  ;
z1 (ANum 0x8000b80d) 0xf9  ;
z1 (ANum 0x8000b80e) 0xf9  ;
z1 (ANum 0x8000b80f) 0xf9  ;
z1 (ANum 0x8000b810) 0xf9  ;
z1 (ANum 0x8000b811) 0xf9  ;
z1 (ANum 0x8000b812) 0xf9  ;
z1 (ANum 0x8000b813) 0xf9  ;
z1 (ANum 0x8000b814) 0xf9  ;
z1 (ANum 0x8000b815) 0xf9  ;
z1 (ANum 0x8000b816) 0xf9  ;
z1 (ANum 0x8000b817) 0xf9  ;
z1 (ANum 0x8000b818) 0xf9  ;
z1 (ANum 0x8000b819) 0xf9  ;
z1 (ANum 0x8000b81a) 0xf9  ;
z1 (ANum 0x8000b81b) 0xf9  ;
z1 (ANum 0x8000b81c) 0xf9  ;
z1 (ANum 0x8000b81d) 0xf9  ;
z1 (ANum 0x8000b81e) 0xf9  ;
z1 (ANum 0x8000b81f) 0xf9  ;
z1 (ANum 0x8000b820) 0xf9  ;
z1 (ANum 0x8000b821) 0xf9  ;
z1 (ANum 0x8000b822) 0xf9  ;
z1 (ANum 0x8000b823) 0xf9  ;
z1 (ANum 0x8000b824) 0xf9  ;
z1 (ANum 0x8000b825) 0xf9  ;
z1 (ANum 0x8000b826) 0xf9  ;
z1 (ANum 0x8000b827) 0xf9  ;
z1 (ANum 0x8000b828) 0xf9  ;
z1 (ANum 0x8000b829) 0xf9  ;
z1 (ANum 0x8000b82a) 0xf9  ;
z1 (ANum 0x8000b82b) 0xf9  ;
z1 (ANum 0x8000b82c) 0xf9  ;
z1 (ANum 0x8000b82d) 0xf9  ;
z1 (ANum 0x8000b82e) 0xf9  ;
z1 (ANum 0x8000b82f) 0xf9  ;
z1 (ANum 0x8000b830) 0xf9  ;
z1 (ANum 0x8000b831) 0xf9  ;
z1 (ANum 0x8000b832) 0xf9  ;
z1 (ANum 0x8000b833) 0xf9  ;
z1 (ANum 0x8000b834) 0xf9  ;
z1 (ANum 0x8000b835) 0xf9  ;
z1 (ANum 0x8000b836) 0xf9  ;
z1 (ANum 0x8000b837) 0xf9  ;
z1 (ANum 0x8000b838) 0xf9  ;
z1 (ANum 0x8000b839) 0xf9  ;
z1 (ANum 0x8000b83a) 0xf9  ;
z1 (ANum 0x8000b83b) 0xf9  ;
z1 (ANum 0x8000b83c) 0xf9  ;
z1 (ANum 0x8000b83d) 0xf9  ;
z1 (ANum 0x8000b83e) 0xf9  ;
z1 (ANum 0x8000b83f) 0xf9  ;
z1 (ANum 0x8000b840) 0xf9  ;
z1 (ANum 0x8000b841) 0xf9  ;
z1 (ANum 0x8000b842) 0xf9  ;
z1 (ANum 0x8000b843) 0xf9  ;
z1 (ANum 0x8000c18c) 0xf9  ;
z1 (ANum 0x8000c18d) 0xf9  ;
z1 (ANum 0x8000c18e) 0xf9  ;
z1 (ANum 0x8000c18f) 0xf9  ;
z1 (ANum 0x8000c190) 0xf9  ;
z1 (ANum 0x8000c191) 0xf9  ;
z1 (ANum 0x8000c192) 0xf9  ;
z1 (ANum 0x8000c193) 0xf9  ;
z1 (ANum 0x8000c194) 0xf9  ;
z1 (ANum 0x8000c195) 0xf9  ;
z1 (ANum 0x8000c196) 0xf9  ;
z1 (ANum 0x8000c197) 0xf9  ;
z1 (ANum 0x8000c198) 0xf9  ;
z1 (ANum 0x8000c199) 0xf9  ;
z1 (ANum 0x8000c19a) 0xf9  ;
z1 (ANum 0x8000c19b) 0xf9  ;
z1 (ANum 0x8000c19c) 0xf9  ;
z1 (ANum 0x8000c19d) 0xf9  ;
z1 (ANum 0x8000c19e) 0xf9  ;
z1 (ANum 0x8000c19f) 0xf9  ;
z1 (ANum 0x8000c1a0) 0xf9  ;
z1 (ANum 0x8000c1a1) 0xf9  ;
z1 (ANum 0x8000c1a2) 0xf9  ;
z1 (ANum 0x8000c1a3) 0xf9  ;
z1 (ANum 0x8000c1a4) 0xf9  ;
z1 (ANum 0x8000c1a5) 0xf9  ;
z1 (ANum 0x8000c1a6) 0xf9  ;
z1 (ANum 0x8000c1a7) 0xf9  ;
z1 (ANum 0x8000c1a8) 0xf9  ;
z1 (ANum 0x8000c1a9) 0xf9  ;
z1 (ANum 0x8000c1aa) 0xf9  ;
z1 (ANum 0x8000c1ab) 0xf9  ;
z1 (ANum 0x8000c1ac) 0xf9  ;
z1 (ANum 0x8000c1ad) 0xf9  ;
z1 (ANum 0x8000c1ae) 0xf9  ;
z1 (ANum 0x8000c1af) 0xf9  ;
z1 (ANum 0x8000c1b0) 0xf9  ;
z1 (ANum 0x8000c1b1) 0xf9  ;
z1 (ANum 0x8000c1b2) 0xf9  ;
z1 (ANum 0x8000c1b3) 0xf9  ;
z1 (ANum 0x8000c1b4) 0xf9  ;
z1 (ANum 0x8000c1b5) 0xf9  ;
z1 (ANum 0x8000c1b6) 0xf9  ;
z1 (ANum 0x8000c1b7) 0xf9  ;
z1 (ANum 0x8000c1b8) 0xf9  ;
z1 (ANum 0x8000c1b9) 0xf9  ;
z1 (ANum 0x8000c1ba) 0xf9  ;
z1 (ANum 0x8000c1bb) 0xf9  ;
z1 (ANum 0x8000c1bc) 0xf9  ;
z1 (ANum 0x8000c1bd) 0xf9  ;
z1 (ANum 0x8000c1be) 0xf9  ;
z1 (ANum 0x8000c1bf) 0xf9  ;
z1 (ANum 0x8000c1c0) 0xf9  ;
z1 (ANum 0x8000c1c1) 0xf9  ;
z1 (ANum 0x8000c1c2) 0xf9  ;
z1 (ANum 0x8000c1c3) 0xf9  ;
z1 (ANum 0x8000c1c4) 0xf9  ;
z1 (ANum 0x8000c1c5) 0xf9  ;
z1 (ANum 0x8000c1c6) 0xf9  ;
z1 (ANum 0x8000c1c7) 0xf9  ;
z1 (ANum 0x8000c1c8) 0xf9  ;
z1 (ANum 0x8000c1c9) 0xf9  ;
z1 (ANum 0x8000c1ca) 0xf9  ;
z1 (ANum 0x8000c1cb) 0xf9  ;
z1 (ANum 0x8000c1cc) 0xf9  ;
z1 (ANum 0x8000c1cd) 0xf9  ;
z1 (ANum 0x8000c1ce) 0xf9  ;
z1 (ANum 0x8000c1cf) 0xf9  ;
z1 (ANum 0x8000c1d0) 0xf9  ;
z1 (ANum 0x8000c1d1) 0xf9  ;
z1 (ANum 0x8000c1d2) 0xf9  ;
z1 (ANum 0x8000c1d3) 0xf9  ;
z1 (ANum 0x8000c1d4) 0xf9  ;
z1 (ANum 0x8000c1d5) 0xf9  ;
z1 (ANum 0x8000c1d6) 0xf9  ;
z1 (ANum 0x8000c1d7) 0xf9  ;
z1 (ANum 0x8000c1d8) 0xf9  ;
z1 (ANum 0x8000c1d9) 0xf9  ;
z1 (ANum 0x8000c1da) 0xf9  ;
z1 (ANum 0x8000c1db) 0xf9  ;
z1 (ANum 0x8000c1dc) 0xf9  ;
z1 (ANum 0x8000c1dd) 0xf9  ;
z1 (ANum 0x8000c1de) 0xf9  ;
z1 (ANum 0x8000c1df) 0xf9  ;
z1 (ANum 0x8000c1e0) 0xf9  ;
z1 (ANum 0x8000c1e1) 0xf9  ;
z1 (ANum 0x8000c1e2) 0xf9  ;
z1 (ANum 0x8000c1e3) 0xf9  ;
z1 (ANum 0x8000c1e4) 0xf9  ;
z1 (ANum 0x8000c1e5) 0xf9  ;
z1 (ANum 0x8000c1e6) 0xf9  ;
z1 (ANum 0x8000c1e7) 0xf9  ;
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
z1 (ANum 0x8000c31b) 0xf9   ].
Definition TFIB_UNIVERSE_A : list (list Z) :=
[[0x52ce8];
[0x52ce8; 0x80338];
[0x52ce8; 0x80468];
[0x52ce8; 0x80634];
[0x52ce8; 0x80cd8];
[0x52ce8; 0x80cd8; 0x80608];
[0x52ce8; 0x813f4];
[0x52ce8; 0x813f4; 0x80608];
[0x52ce8; 0x8173c];
[0x52ce8; 0x8173c; 0x80608];
[0x52ce8; 0x81784];
[0x52ce8; 0x81784; 0x80608];
[0x52ce8; 0x82098];
[0x52ce8; 0x82098; 0x80608];
[0x52ce8; 0x820a0];
[0x52ce8; 0x820a0; 0x80608];
[0x52ce8; 0x820a8];
[0x52ce8; 0x820a8; 0x80608];
[0x52e48];
[0x52e48; 0x802c0];
[0x52e48; 0x80314];
[0x52e48; 0x805a0];
[0x52e48; 0x80bcc];
[0x52e48; 0x80bcc; 0x80608];
[0x52e48; 0x80c44];
[0x52e48; 0x80c44; 0x80608];
[0x52e48; 0x816e8];
[0x52e48; 0x816e8; 0x80608];
[0x52e48; 0x81748];
[0x52e48; 0x81748; 0x80608];
[0x52e48; 0x818bc];
[0x52e48; 0x818bc; 0x80608];
[0x52e48; 0x818d4];
[0x52e48; 0x818d4; 0x80608];
[0x52e48; 0x818ec];
[0x52e48; 0x818ec; 0x80608]].

(* ---- the closed checks ------------------------------------------------------------------------------------- *)
(* The shadow byte at s is one of the certificate's one-byte cells (GrantCloseChk.v:38-41). *)
Definition sf_is_shc (s : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum _)) => Z.eqb s' s | _ => false end.
Definition sf_is_shv (s v : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum v')) => (Z.eqb s' s && Z.eqb v' v)%bool | _ => false end.

(* The end (in granules) of the zero-shadow range that holds granule k, if one does (GrantCloseChk.v:44-48). *)
Fixpoint sf_zfind (k : Z) (zs : list (Z * Z)) : option Z :=
  match zs with
  | [] => None
  | (q, m) :: r => if ((q / 8 <=? k) && (k <? (q + m) / 8))%bool then Some ((q + m) / 8) else sf_zfind k r
  end.

(* Every granule of [k, hi) is in a range of zs or has a cell in cells (GrantCloseChk.v:51-60). *)
Fixpoint sf_vscan (zs : list (Z * Z)) (cells : list acell) (fuel : nat) (k hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? k then true else
      match sf_zfind k zs with
      | Some e => sf_vscan zs cells f e hi
      | None => (existsb (sf_is_shc (SHADOW_OFF + k)) cells && sf_vscan zs cells f (k + 1) hi)%bool
      end
  end.

(* The RELAXED glob check. fuzz_grant's glob_chk (GrantCloseChk.v:64-67) asks every global (q, sz) for a zero-shadow
   range over its full granules [q, q + sz / 8 * 8), also when it has none: a global of fewer than 8 bytes then
   needs a range that holds q, which identity's start-up table has not (its zero-shadow ranges stop at each global),
   so grant's check rejects 21 of the 50 registered globals. Here that clause is asked
   only when sz / 8 > 0. Every global is still checked byte for byte: a global whose size is not a multiple of 8 has
   a partial last granule whose shadow byte must be the cell `sz mod 8` (glob_chk_relaxed_sound). *)
Definition glob_chk_relaxed (zs : list (Z * Z)) (cells : list acell) (g : Z * Z) : bool :=
  ((fst g mod 8 =? 0) && (0 <=? snd g) &&
   ((snd g / 8 =? 0) || existsb (fun r => (fst r <=? fst g) && (fst g + snd g / 8 * 8 <=? fst r + snd r)) zs) &&
   ((snd g mod 8 =? 0) || existsb (sf_is_shv (SHADOW_OFF + fst g / 8 + snd g / 8) (snd g mod 8)) cells))%bool.

(* ---- what the checks say ------------------------------------------------------------------------------------- *)
Lemma sf_le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.

Lemma sf_is_shc_eq : forall s c, sf_is_shc s c = true -> exists v, c = z1 (ANum s) v.
Proof.
intros s [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply Z.eqb_eq in H. subst. eexists. reflexivity.
Qed.

Lemma sf_is_shv_eq : forall s v c, sf_is_shv s v c = true -> c = z1 (ANum s) v.
Proof.
intros s v [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma sf_zfind_some : forall k zs e, sf_zfind k zs = Some e ->
  exists q m, In (q, m) zs /\ q / 8 <= k < (q + m) / 8 /\ e = (q + m) / 8.
Proof.
intros k zs. induction zs as [|[q m] r IH]; intros e H; cbn [sf_zfind] in H; [discriminate|].
destruct ((q / 8 <=? k) && (k <? (q + m) / 8))%bool eqn:Hb.
- injection H as <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists q, m. split; [left; reflexivity|]. split; [lia | reflexivity].
- destruct (IH e H) as (q' & m' & Hin & Hk & He). exists q', m'. split; [right; exact Hin|]. split; [exact Hk | exact He].
Qed.

(* [a, a + n) lies in one range of l (GrantCloseChk.v:139, over the list rather than the record). *)
Lemma sf_in_zs_of_b : forall (l : list (Z * Z)) a n,
  existsb (fun r => (fst r <=? a) && (a + n <=? fst r + snd r))%bool l = true ->
  exists q m, In (q, m) l /\ q <= a /\ a + n <= q + m.
Proof.
intros l a n H. apply existsb_exists in H as ([q m] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists q, m. split; [exact Hin|]. lia.
Qed.

(* A trace the check finds in U is in U (the start-up AD2l.v's In_of_existsb). *)
Lemma sf_In_of_existsb : forall (t : list Z) (U : list (list Z)),
  existsb (fun u => if list_eq_dec Z.eq_dec u t then true else false) U = true -> In t U.
Proof.
intros t U H. apply existsb_exists in H as (u & Hu & Hb). destruct (list_eq_dec Z.eq_dec u t) as [<-|]; [exact Hu | discriminate].
Qed.

(* The trace an allocator call records at each context of ctx is in U (the shape of HUMM / HUMF). *)
Lemma sf_hum_of_b : forall (ra0 : Z) (ctx U : list (list Z)),
  forallb (fun c => existsb (fun u => if list_eq_dec Z.eq_dec u
      (firstn kUnwindMax (ra0 :: flat_map (fun r => if r =? ra0 then [] else [r]) c)) then true else false) U) ctx = true ->
  forall c, In c ctx -> In (firstn kUnwindMax (ra0 :: flat_map (fun r => if r =? ra0 then [] else [r]) c)) U.
Proof.
intros ra0 ctx U H c Hc. apply sf_In_of_existsb. exact (proj1 (forallb_forall _ _) H c Hc).
Qed.

(* Over any reader rd that holds zero at the shadow of each (8-aligned) range of zs and each one-byte cell of cells. *)
Section sound.
Variable rd : YG0f.reader.
Variable zs : list (Z * Z).
Variable cells : list acell.
Hypothesis ZAL : forall q m, In (q, m) zs -> q mod 8 = 0.
Hypothesis ZRD : Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) zs.
Hypothesis CRD : forall s v, In (z1 (ANum s) v) cells -> rd s = Some (YG0f.le_byte v 1 0).

(* A granule of a zero-shadow range has shadow byte 0 (GrantClose.v:214). *)
Lemma sf_zs_rd : forall q m j, In (q, m) zs -> q / 8 <= j < (q + m) / 8 -> rd (SHADOW_OFF + j) = Some 0.
Proof.
intros q m j Hin Hj.
pose proof (proj1 (Forall_forall _ _) ZRD (q, m) Hin) as Hz. cbn [fst snd] in Hz. unfold zero_shadow in Hz.
pose proof (ZAL q m Hin) as Hq. pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
assert (E : (q + m) / 8 = m / 8 + q / 8).
{ replace (q + m) with (m + q / 8 * 8) by lia. apply Z.div_add. lia. }
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

(* The relaxed check is sound: it gives block_shadow, the fact globs_marked asks of each global. *)
Lemma glob_chk_relaxed_sound : forall q sz, glob_chk_relaxed zs cells (q, sz) = true ->
  block_shadow rd SHADOW_OFF q sz.
Proof.
intros q sz Hb. unfold glob_chk_relaxed in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Bs.
pose proof (Z.div_mod (sz + 7) 8 ltac:(lia)) as Ds7. pose proof (Z.mod_pos_bound (sz + 7) 8 ltac:(lia)) as Bs7.
unfold shadow_of_addr.
destruct (i <? sz / 8) eqn:Hlt.
- (* a full granule: sz / 8 > 0, so the check found a zero-shadow range over all of them *)
  apply Z.ltb_lt in Hlt.
  apply orb_true_iff in Hfull as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
  apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
  pose proof (ZAL r0 m0 Hr) as Hr8. pose proof (Z.div_mod r0 8 ltac:(lia)) as Dr.
  pose proof (Z.div_mod (r0 + m0) 8 ltac:(lia)) as Drm. pose proof (Z.mod_pos_bound (r0 + m0) 8 ltac:(lia)) as Brm.
  replace (SHADOW_OFF + q / 8 + i) with (SHADOW_OFF + (q / 8 + i)) by lia.
  apply (sf_zs_rd r0 m0); [exact Hr | lia].
- (* the partial last granule: i = sz / 8 and sz mod 8 <> 0, so the check found its cell `sz mod 8` *)
  apply Z.ltb_ge in Hlt.
  assert (Hi' : i = sz / 8) by lia.
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply sf_is_shv_eq in Hcb. subst c. subst i.
  rewrite (CRD _ _ Hc). rewrite sf_le_byte1 by lia. reflexivity.
Qed.

(* Every granule of [k, hi) that the scan accepts has a mapped shadow byte (GrantCloseChk.v:124, GrantClose.v:228). *)
Lemma sf_vscan_sound : forall fuel k hi, sf_vscan zs cells fuel k hi = true ->
  forall j, k <= j < hi -> rd (SHADOW_OFF + j) <> None.
Proof.
induction fuel as [|f IH]; intros k hi H j Hj; cbn [sf_vscan] in H; [discriminate|].
destruct (hi <=? k) eqn:E; [apply Z.leb_le in E; exfalso; lia|].
destruct (sf_zfind k zs) as [e|] eqn:Ez.
- destruct (sf_zfind_some _ _ _ Ez) as (q & m & Hin & Hk & ->).
  destruct (Z_lt_le_dec j ((q + m) / 8)) as [Hlt|Hge].
  + rewrite (sf_zs_rd q m j Hin ltac:(lia)). discriminate.
  + exact (IH _ _ H j (conj Hge (proj2 Hj))).
- apply andb_prop in H as [Hc H]. destruct (Z.eq_dec j k) as [->|Hne].
  + apply existsb_exists in Hc as (c & Hin & Hb). destruct (sf_is_shc_eq _ _ Hb) as [v ->].
    rewrite (CRD _ _ Hin). discriminate.
  + apply (IH _ _ H). lia.
Qed.
End sound.

(* ---- the checks, by computation on the copied tables (closed terms) -------------------------------------- *)
Lemma sf_zs_al : forall q m, In (q, m) TFIB_ZERO_SHADOW_A -> q mod 8 = 0.
Proof.
intros q m Hin.
assert (H : forallb (fun r => fst r mod 8 =? 0) TFIB_ZERO_SHADOW_A = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) H (q, m) Hin) as Hb. cbn [fst] in Hb. apply Z.eqb_eq in Hb. exact Hb.
Qed.

(* All 50 registered globals of IDENT_GLOBS pass the relaxed check (none dropped). *)
Lemma ident_globs_chk : forallb (glob_chk_relaxed TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A) IDENT_GLOBS = true.
Proof. vm_compute. reflexivity. Qed.

(* Every granule of the image's read range [IMG_LO, IMG_TOP) is in a zero-shadow range or has a one-byte cell
   (745 scan steps). *)
Lemma ident_vscan : sf_vscan TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A (Pos.to_nat 4096) (IMG_LO / 8) (IMG_TOP / 8) = true.
Proof. vm_compute. reflexivity. Qed.

(* LLVMF_MALLOC_CTX / LLVMF_FREE_CTX at BASE = 0x8070c (A_LLVMF), as closed lists; equal to the link's terms by
   conversion (sf_malloc_ctx / sf_free_ctx below). *)
Definition IDENT_MALLOC_CTX_C : list (list Z) :=
map (fun o => [0x8070c + o; RA_LLVMF]) LLVMFuzzerTestOneInput.LLVMF_MALLOC_RAS ++
map (fun o => [0x8070c + o]) LLVMFuzzerTestOneInput.LLVMF_MALLOC_RAS.
Definition IDENT_FREE_CTX_C : list (list Z) :=
map (fun o => [0x8070c + o; RA_LLVMF]) LLVMFuzzerTestOneInput.LLVMF_FREE_RAS ++
map (fun o => [0x8070c + o]) LLVMFuzzerTestOneInput.LLVMF_FREE_RAS.

(* ---- the facts, at the link's names ---------------------------------------------------------------------------- *)
Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation PI := (@PI_ident rc).
Local Notation SEGS := (@pa_segs _ ident_listing PI).
Local Notation VAL := (@pa_val _ ident_listing PI).
Variable IdentB : asyms.
Hypothesis HZS : as_zero_shadow IdentB = TFIB_ZERO_SHADOW_A.
Hypothesis HCONST : forall ly, exists pre, as_const IdentB ly = pre ++ TFIB_CONST_SHADOW_A.
Hypothesis HUNIV : as_universe IdentB = TFIB_UNIVERSE_A.
Hypothesis HRA0M : pc_malloc_ra0 (as_code IdentB) = 0x52e48.
Hypothesis HRA0F : pc_free_ra0 (as_code IdentB) = 0x52ce8.

(* In every AR state, the shadow of each range of the copied zero-shadow table reads zero (ARm's am_zshadow) ... *)
Lemma sf_ar_zrd : forall ly S (W : world SEGS) mem md, AR SEGS IdentB ly S W mem md ->
  Forall (fun r => zero_shadow (aview SEGS (w_H W) mem) SHADOW_OFF (fst r) (snd r)) TFIB_ZERO_SHADOW_A.
Proof.
intros ly S W mem md HAR. pose proof (am_zshadow _ _ _ _ (proj1 HAR)) as Hz.
unfold zshadow_ok, zero_shadow_ranges in Hz. rewrite HZS in Hz. exact (Forall_inv_tail Hz).
Qed.

(* ... and each copied one-byte shadow cell holds its byte (ARm's am_const; GrantClose.v:201). *)
Lemma sf_ar_crd : forall ly S (W : world SEGS) mem md, AR SEGS IdentB ly S W mem md ->
  forall s v, In (z1 (ANum s) v) TFIB_CONST_SHADOW_A -> aview SEGS (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros ly S W mem md HAR s v Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
destruct (HCONST ly) as [pre Hpre].
assert (Hin' : In (z1 (ANum s) v) (as_const IdentB ly)) by (rewrite Hpre; apply in_or_app; right; exact Hin).
specialize (HC _ Hin'). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

(* GM (IdentEntryLink.v:250). *)
Lemma ident_GM : globs_marked SEGS IdentB IDENT_GLOBS.
Proof.
intros ly S W mem md q sz Hin HAR.
exact (glob_chk_relaxed_sound (aview SEGS (w_H W) mem) TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A sf_zs_al
  (sf_ar_zrd ly S W mem md HAR) (sf_ar_crd ly S W mem md HAR) q sz
  (proj1 (forallb_forall _ _) ident_globs_chk (q, sz) Hin)).
Qed.

(* IV (IdentEntryLink.v:251). *)
Lemma ident_IV : img_shadow_vis SEGS IdentB.
Proof.
intros ly S W mem md a HAR Ha. unfold shadow_addr. unfold IdentRo.IMG_HI in Ha.
assert (E8 : 8 * (IMG_TOP / 8) = IMG_TOP) by (vm_compute; reflexivity).
assert (Hj : IMG_LO / 8 <= a / 8 < IMG_TOP / 8).
{ split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]. }
exact (sf_vscan_sound (aview SEGS (w_H W) mem) TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A sf_zs_al
  (sf_ar_zrd ly S W mem md HAR) (sf_ar_crd ly S W mem md HAR) _ _ _ ident_vscan (a / 8) Hj).
Qed.

(* ZS_STEM (IdentEntryLink.v:340): object 17 is [0x9b1c0, +24), the range (0x9b1c0, 0x18) of the table. *)
Lemma ident_ZS_STEM : in_zs IdentB (VAL (A_OBJ 17)) 24.
Proof.
change (VAL (A_OBJ 17)) with 0x9b1c0. unfold in_zs. rewrite HZS.
apply sf_in_zs_of_b. vm_compute. reflexivity.
Qed.

(* ZS_NAME (IdentEntryLink.v:341): object 21 is [0x9b200, +24), the range (0x9b200, 0x18) of the table. *)
Lemma ident_ZS_NAME : in_zs IdentB (VAL (A_OBJ 21)) 24.
Proof.
change (VAL (A_OBJ 21)) with 0x9b200. unfold in_zs. rewrite HZS.
apply sf_in_zs_of_b. vm_compute. reflexivity.
Qed.

Lemma sf_malloc_ctx : LLVMFuzzerTestOneInput.LLVMF_MALLOC_CTX RA_LLVMF = IDENT_MALLOC_CTX_C.
Proof. reflexivity. Qed.
Lemma sf_free_ctx : LLVMFuzzerTestOneInput.LLVMF_FREE_CTX RA_LLVMF = IDENT_FREE_CTX_C.
Proof. reflexivity. Qed.

(* HUMM (IdentEntryLink.v:680): the 14 malloc traces are in the universe. *)
Lemma ident_HUMM : forall c, In c (LLVMFuzzerTestOneInput.LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code IdentB)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code IdentB) then [] else [r]) c)) (as_universe IdentB).
Proof.
rewrite HRA0M, HUNIV, sf_malloc_ctx. apply sf_hum_of_b. vm_compute. reflexivity.
Qed.

(* HUMF (IdentEntryLink.v:683): the 14 free traces are in the universe. *)
Lemma ident_HUMF : forall c, In c (LLVMFuzzerTestOneInput.LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code IdentB)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code IdentB) then [] else [r]) c)) (as_universe IdentB).
Proof.
rewrite HRA0F, HUNIV, sf_free_ctx. apply sf_hum_of_b. vm_compute. reflexivity.
Qed.
End L.
