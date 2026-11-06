(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA PRH_Base PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Ent102CutsA Ent102FdA Ent102PosA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Ent102CallA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section L5d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variable ec_ccut : ecx -> nat -> Z.
Variable ec_lcut : ecx -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
(* the cuts of this lane are after check_no_overread's frees: ec_inv at wle' (Ent102CutsA.v ec_invR) *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).

Lemma l5d_fetch : fetch_word SEGS (Z_to_bv 64 (BASE + 0x320)) = Some (Z_to_bv 32 0xe9dff06f).
Proof.
exact (pa_fetch_pw (L := A_prog_listing) (PL := PL_102_A) (PI := PA) 0x320 0xe9dff06f ltac:(vm_compute; reflexivity)).
Qed.

Lemma l5d_dec : decode_any (Z_to_bv 32 0xe9dff06f) = Some (Jal 0 (Z_to_bv 21 (-356)), 4%Z).
Proof. vm_compute. f_equal. f_equal. f_equal. all: apply bv_eq; reflexivity. Qed.

Lemma l5d_j : forall (fy : YK11.FPState) (W : world SEGS) regs mem md Q,
  (forall X, SRr SEGS W (@cfg_at fy SEGS (BASE + 0x1bc) regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cfg_at fy SEGS (BASE + 0x320) regs mem md) Q.
Proof.
intros fy W regs mem md Q HK.
unfold cfg_at, YG0d.w64.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  exact (step_jal_x0 SEGS regs _ (mrestrict (w_H W) mem) (seg_rom SEGS) _ _ l5d_fetch
    (not_ecall_of_decode _ _ _ l5d_dec ltac:(discriminate)) l5d_dec).
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  rewrite YCbn.btgt_lit.
  replace (bv_signed (Z_to_bv 21 (-356))) with (-356) by (vm_compute; reflexivity).
  replace (BASE + 0x320 + -356) with (BASE + 0x1bc) by lia.
  exact (HK (m_vm_materialized model')).
Qed.

Theorem seg_L5d_A :
  @seg_L5d_stmt fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L5d_stmt, ec_laneR.
intros E fk t D HYP W c Hcut.
pose proof HYP as HCC. apply ech_ccut_ok in HCC.
pose proof HYP as HLC. apply ech_lcut_ok in HLC.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & Lam & peak & cnt & k & trp & Hat & Hinv & Hro & Hcc & Hlc
  & Hrkd & Hfrm & Hrd & HP & HN & Hpjf & Hnm).
pose proof Hinv as Hpre. apply ec_inv_preR in Hpre.
assert (Hsm : e_sm E = ReaderRes.jr_strtod) by (unfold ec_pre in Hpre; ec_conj_pick Hpre).
pose proof (proj2 (HCC E 9%nat 10%nat) ltac:(lia)) as Hc10.
pose proof (proj2 (HLC E 9%nat 10%nat) ltac:(lia)) as Hl10.
destruct Hat as (fy & Hfz & Hkept & ->).
(* a no-call lane: the plain SRr proof lifts to SRr' (YA0nH.SRr_SRr') *)
apply (SRr_SRr' SEGS (@YGcfRehidePost.RZ_cf rc)).
unfold EC_AR_CRS1, EC_BASE.
apply l5d_j. intros X.
apply SRr_ret.
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).
exists ly, S, Hp, regs, mem, (with_vm_backing (m_vm_lazy md) X md), own, Lam, peak, cnt, k, D, trp, t.
split; [exists fy; split; [exact Hfz|]; split; [exact Hkept | reflexivity]|].
split.
{ (* the `j` is a no-call stretch: the budgeted journal with the model materialized, at the same spent wild budget
     (ec_wk_free is ec_wk_crs1) *)
  destruct Hinv as ((WS & HJ & HWB) & Hrest). split; [|exact Hrest].
  exact (ec_inv_wk_growR B SK WLE' LAWS E own ly S Hp W mem md k WS ec_wk_crs1 ec_wk_free X HJ HWB (le_n _)). }
split; [exact Hro|].
split; [lia|].
split; [lia|].
split; [exact Hrkd|].
split; [exact Hfrm|].
split; [exact HP|].
split; [exact (ec_read_fd SEGS _ _ (e_x E) t (ec_doc fk) D Hrd HN)|].
split; [exact Hpjf|].
split; [exact Hnm|].
rewrite (ec_rd_ck_read _ _ _ E Hsm). exact Hrd.
Qed.

End L5d.

Check seg_L5d_A.
Print Assumptions seg_L5d_A.
