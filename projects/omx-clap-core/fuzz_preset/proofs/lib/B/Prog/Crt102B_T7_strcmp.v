(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 996 of its 1069 lines of code are new or changed and 441 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Crt102B_T7.v; 33 of its 93 lines of code are new or changed and 1009 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Crt102B_T7_top.v; 28 of its 88 lines of code are new or changed and 33 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T7 = CRT-B-CEXIT: THE ROW AT THE
   B' STRCMP ROW OF RECORD.

   rule 24: proves function check_round_trip (image B' of fuzz_preset; reuse search CONFIRMED by name: the R24 confirmation
   note R24-CONFIRM.md (sha256 b58eb5e2e5e3; internal record): released proofs plain/ubsan only, its address runs no evidence; no released walk, no walk held outside this tree, and no walk on an internal branch of these B' segments).

   crtB_T7_strcmp: Crt102B_T7_top.crtB_T7 at B := YD2l.TfibB (TS := YD2l.TfibB_syms), ARx := ARcf, with STRCMP
   discharged by the libc row's lib/AU/PSstrRo.v ps_strcmp_xrom_B (astrcmp_realizes_xrom at YB1v.tfibsegs, ARcf, any
   rlo / rhi, pc CfImgB's cf_pc_strcmp; the base carries lib/Reusable/YF0m.v blob f82202ebccdf with YGcfStrRo.v /
   PSstrlen.v / PSstrcmp.v) and BOK by YD2l.TfibB_ok. The segs: YB1v.tfibsegs and PI_prog_B's pa_segs (lib/B/Img0.v
   rsegs) are both AsanUbsan.M.loaded_segments, by conversion; the pc: CfImgB's cf_pc_strcmp and PI_prog_B's pa_sigma
   AS___wrap_strcmp are the same entry, by vm_compute (as read_members_Bp3.rmB3_pc). Every other premise is crtB_T7's
   own Section hypothesis, at this instance; crtB_T7 and its STRCMP hypothesis are unchanged.
   On the Step-1 contract texts (the re-hiding move): YG0ncf.ARcf takes {ci : CfImg} on
   the Step-1 base, so ARc names ci := CfImgB.CfImg_B (the CfImg form of AU/CfApiPresetB.v), and ps_strcmp_xrom_B is
   cited at the same ci; crtB_T7's new Section hypothesis HOS4 : (length rp_os <= 4)%nat is this corollary's too.

   A LEAF: nothing imports this file. Requiring lib/AU/PSstrRo.v loads lib/K/Lib/LiaTuning.v and
   lib/K5/Lib/LiaTuning.v, whose GLOBAL `Ltac lia ::=` changes later proofs in any file that loads them (measured by
   the T5 / T6 rows), so the row's own files do not Require it.

   NUMERALS: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102B_T7_bd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102B_T7_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

Section t7strcmp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation TB := (YD2l.TfibB).
#[local] Notation ARc := (YG0ncf.ARcf (ci := CfImgB.CfImg_B) (rc := rc) (cp := CfParams_preset) SEGS TB).

Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt ran most : Z)
  (CTX0 : list (list Z)).

(* crtB_T7's Section hypotheses (Crt102B_T7_top.v; owners in the stretch files), at B := TfibB, ARx := ARcf; BOK and
   STRCMP are discharged below *)
Hypothesis LAWS : AR_laws_x SEGS TB ARc cf_head.
Hypothesis HPRE : fpre TB ARc STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HRAN : ran = 0.
Hypothesis HCL : prh_univ_closure TB CTX0.
Hypothesis HCTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).
Hypothesis HKMA : @kept_img _ B_prog_listing PA TB (@CRT_MOD_AT_B _ PA) (Z.of_nat (length ck_MOD_AT) + 1).
Hypothesis HKST : @kept_img _ B_prog_listing PA TB (@CRT_STAMP_B _ PA) (Z.of_nat (length ck_STAMP) + 1).
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARc ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis FFREE : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_free_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA TB ARc SK.
Hypothesis PJFREE : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_free_specX fxk rc ci CfParams_preset prh_img_B RL B_prog_listing PA TB ARc SK CTX0 DOC_D.
(* crtB_T7's length bound (check_round_trip's text premise, PRH_FnCheck.v:2363) *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

Corollary crtB_T7_strcmp :
  CRT_B_SEG_T7 (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
    (CRT_PC := CRT_PC_B) (CRT_X_OFF := CRT_X_OFF_B) (CRT_C_OFF := CRT_C_OFF_B) (B := TB) (ARx := ARc)
    (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
    (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
    (cnt := cnt) (ran := ran) (most := most).
Proof.
assert (STRCMP : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS TB ARc RLO RHI (SIGMA AS___wrap_strcmp)).
{ intros fxk.
  pose proof (PSstrRo.ps_strcmp_xrom_B (fx := fxk) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CfParams_preset) TB
    YD2l.TfibB_syms RLO RHI) as ASC.
  replace (SIGMA AS___wrap_strcmp) with (@cf_pc_strcmp CfImgB.CfImg_B)
    by (cbn [pa_sigma PI_prog_B]; vm_compute; reflexivity).
  exact ASC. }
exact (Crt102B_T7_top.crtB_T7 TB ARc rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D Lam peak cnt ran
  most CTX0 LAWS HPRE HTREE HRAN HCL HCTX HKMA HKST YD2l.TfibB_ok IMGVIS FFREE PJFREE STRCMP HOS4).
Qed.

End t7strcmp.

(* the axioms the corollary rests on, printed into the build log (the Section hypotheses are its premises) *)
Print Assumptions crtB_T7_strcmp.
