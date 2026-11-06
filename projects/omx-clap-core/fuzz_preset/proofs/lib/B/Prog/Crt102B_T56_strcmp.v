(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 104 of its 139 lines of code are new or changed and 479 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Crt102B_T5.v, with its module names changed; 60 of its 103 lines of code are new or changed and 96 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): statements unchanged in text
   (CRT_B_SEG_T5 / CRT_B_SEG_T6 now at YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf); Step 1's YG0ncf.ARcf takes {ci : CfImg},
   named here at the fixed image, ci := CfImgB.CfImg_B. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b): rows T5 (CRT-B-L012, Crt102B_T5.v crtB_T5) and T6 (CRT-B-L3, Crt102B_T6.v
   crtB_T6) with their callee text ASTRCMP DISCHARGED.

   proves no function (kind: corollaries of the segment lemmas crtB_T5 / crtB_T6).

   THE INSTANCE. B := YD2l.TfibB (the B' asyms of record) and ARx := YG0ncf.ARcf SEGS TfibB, the ARc that
   the libc B' strcmp row asks. ASTRCMP (both rows' Section hypothesis, unchanged in their files) is given by
   PSstrRo.ps_strcmp_xrom_B (lib/AU/PSstrRo.v:67, blob 45e63604063e: astrcmp_realizes_xrom at YB1v.tfibsegs, ARc, any
   rlo / rhi, pc CfImgB's cf_pc_strcmp) at TS := YD2l.TfibB_syms and rlo / rhi := PI_prog_B's relro bounds. Two facts
   carry that row to ASTRCMP's text: the pc (crt56_pc_strcmp: CfImgB's cf_pc_strcmp IS PI_prog_B's pa_sigma
   AS___wrap_strcmp, both __wrap_strcmp, by vm_compute) and the segs (YB1v.tfibsegs and PI_prog_B's pa_segs are both
   AsanUbsan.M.loaded_segments: by conversion, at the `exact`). Each corollary's premises are its row theorem's own
   premises at this instance, ASTRCMP removed; none is added.

   WHY A SEPARATE FILE, not the end of Crt102B_T5.v / Crt102B_T6.v: lib/AU/PSstrRo.v's closure loads
   lib/K/Lib/LiaTuning.v and lib/K5/Lib/LiaTuning.v, whose GLOBAL `Ltac lia ::=` replaces the lia (CJ/Lib/LiaTuning.v's)
   of every file that loads them after. Measured in a build that Requires it: Required from Crt102B_T6.v, it adds HMN to
   crtB_T6's arguments and to Crt102B_T5_bd.v ct5_live_run / ct5_pre_run / ct5_core_run's, so Crt102B_T5_L2.v:372
   fails. No file loads this one, so no other file's lia changes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck PRH_FnEx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB Crt102B_T6 Crt102B_T5.
(* the instance (B := YD2l.TfibB, ARx := ARcf) and the libc B' strcmp row *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

Section t56s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
(* Step 1's engine: YG0ncf.ARcf takes {ci : CfImg}. The image is fixed, so ci is named,
   CfImgB.CfImg_B (the form in lib/AU/CfApiPresetB.v) *)
#[local] Notation ARI := (YG0ncf.ARcf (ci := CfImgB.CfImg_B) (rc := rc) (cp := CfParams_preset) SEGS TB).

(* the pc: the row's trampoline entry is the listing's __wrap_strcmp *)
Lemma crt56_pc_strcmp : @cf_pc_strcmp CfImgB.CfImg_B = SIGMA AS___wrap_strcmp.
Proof. cbn [pa_sigma PI_prog_B]. vm_compute. reflexivity. Qed.

(* ASTRCMP's text at this instance, from the libc strcmp row *)
Lemma crt56_astrcmp_TfibB : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS TB ARI RLO RHI (SIGMA AS___wrap_strcmp).
Proof.
intros fxk.
pose proof (PSstrRo.ps_strcmp_xrom_B (fx := fxk) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CfParams_preset) TB
  YD2l.TfibB_syms RLO RHI) as H.
rewrite crt56_pc_strcmp in H. exact H.
Qed.

Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z).

(* ROW T6 (CRT-B-L3) at the instance: crtB_T6's premises LAWS, HPRE, HTREE, HREAD, SAME at B := TfibB, ARx := ARcf *)
Corollary crtB_T6_TfibB :
  AR_laws_x SEGS TB ARI cf_head ->
  fpre TB ARI STKC ly S Hp W regs mem md ch ->
  ck_tree_ok ly S Lam W mem doc t D ->
  ck_read x = Some t ->
  (forall fxk : YK11.FPState, @tsame_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA TB ARI SK DOC_D) ->
  CRT_B_SEG_T6 (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (CRT_PC := CRT_PC_B) (CRT_C_OFF := CRT_C_OFF_B) (CRT_L3_OFF := CRT_L3_OFF_B) (B := TB) (ARx := ARI)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt)
  (ran := ran) (most := most).
Proof.
intros LAWS HPRE HTREE HREAD SAME.
exact (crtB_T6 TB ARI LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HTREE HREAD crt56_astrcmp_TfibB SAME).
Qed.

(* ROW T5 (CRT-B-L012) at the instance: crtB_T5's premises LAWS, HPRE, HTREE, HMN, HREAD, HLENX, HWL0, HWL1, HCNT,
   HLED0, HRQA, HKMA, BOK, IMGVIS at B := TfibB, ARx := ARcf *)
Corollary crtB_T5_TfibB :
  AR_laws_x SEGS TB ARI cf_head ->
  fpre TB ARI STKC ly S Hp W regs mem md ch ->
  ck_tree_ok ly S Lam W mem doc t D ->
  YAkMemnorm.memnorm SEGS mem ->
  ck_read x = Some t ->
  Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x) ->
  PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54 ->
  cnt < 2 ^ 62 - 2 ^ 30 ->
  prh_ledger TB ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 ->
  RQA_crt t <= most ->
  @kept_img _ B_prog_listing PA TB (@CRT_MOD_AT_B _ PA) (Z.of_nat (length ck_MOD_AT) + 1) ->
  asyms_ok TB ->
  (forall ly S Hp (W : world SEGS) mem md a,
     ARI ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
     aview SEGS (w_H W) mem (shadow_addr a) <> None) ->
  CRT_B_SEG_T5 (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (CRT_PC := CRT_PC_B) (CRT_C_OFF := CRT_C_OFF_B) (CRT_L3_OFF := CRT_L3_OFF_B) (CRT_L0_OFF := CRT_L0_OFF_B)
  (B := TB) (ARx := ARI) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly)
  (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam)
  (peak := peak) (cnt := cnt) (ran := ran) (most := most).
Proof.
intros LAWS HPRE HTREE HMN HREAD HLENX HWL0 HWL1 HCNT HLED0 HRQA HKMA BOK IMGVIS.
exact (crtB_T5 TB ARI LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HTREE HMN HREAD HLENX HWL0 HWL1 HCNT HLED0 HRQA HKMA BOK IMGVIS crt56_astrcmp_TfibB).
Qed.
End t56s.

Print Assumptions crtB_T5.
Print Assumptions crtB_T6.
Print Assumptions crtB_T5_TfibB.
Print Assumptions crtB_T6_TfibB.
