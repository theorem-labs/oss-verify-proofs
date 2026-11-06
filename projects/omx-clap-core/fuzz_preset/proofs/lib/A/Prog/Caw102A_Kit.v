(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Disp_word.v, with its module paths and module names changed; 116 of its 154 lines of code are new or changed and 465 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A': the segments' SHARED STATE KIT (lane CawA102).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma kit).
   A segment proof rebuilds its symbolic state at its cut from the cut's facts: the function's frame [sp0 - 80, sp0)
   with the words a stage reads as atoms 33, 34, .. (atom 32 is the shadow base), every register its own atom.
   PORTED from origin/cold/h-hpreset-7-walk-H2H5 1934271f1f4 lib/A/Prog/H2CawBase.v (blob f20e6e557cb1, Section bld
   :94-256), the old walk of check_as_written on the old pin, to the PARAMETRIC image {PA : PAImg A_prog_listing}: the
   only change is PI_prog_A -> the section's PA. Inputs as Caw102A_Base.v's header.
   Numerals: 80 (LENGTH: the frame), 32 / 33 / 200 (DERIVED: the engine's atom numbering), 2 (WORD: sp), 8 (LENGTH:
   a word), 2 ^ 64 (word range). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Caw102A_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- a stage's symbolic state: the frame region with chunk atoms 33, 34, .. ---- *)
Fixpoint caw_fchunks (k : nat) (offs : list (Z * N)) : list YP09.chunk :=
  match offs with
  | [] => []
  | (o, w) :: r => YP09.mkChunk o (CVal w (SOff k 0)) :: caw_fchunks (S k) r
  end.
(* the frame BELOW the entry sp sp0 (atom 2 holds sp0, sp is the term SOff 2 (-80)): the journal from entry is at sp0,
   so the call rules (`ew E 2 = spw`, `bv_unsigned spw = sp0`) and the frame's stores apply as at the entry *)
Definition caw_fregion_e (offs : list (Z * N)) (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (- CAW_FRAME) 0 wlo whi (caw_fchunks 33 offs).
Definition caw_sr80 : list sv := sr_set sr_atoms 2%bv (SOff 2 (- CAW_FRAME)).

Section bld. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGSz := (@pa_segs _ A_prog_listing PA).
#[local] Notation VALz := (@pa_val _ A_prog_listing PA).
#[local] Notation BASEz := (@pa_val _ A_prog_listing PA A_TEXT).
Fixpoint caw_vals_ok (m : word -> option byte) (sp : Z) (offs : list (Z * N)) (vals : list Z) : Prop :=
  match offs, vals with
  | [], [] => True
  | (o, w) :: r, v :: vs =>
      val_mem SEGSz m (sp + o) (N.to_nat w) v /\ 0 <= v < 2 ^ (8 * Z.of_N w) /\ Z.of_N w <= 8 /\
      caw_vals_ok m sp r vs
  | _, _ => False
  end.
Definition caw_Ee (regs : bvmap 5 word) (sp0 : Z) (vals : list Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))).
Lemma caw_fchunks_ok : forall E m sp offs vals k,
  (forall i, (i < length offs)%nat -> ew E (k + i) = Z_to_bv 64 (nth i vals 0)) ->
  caw_vals_ok m sp offs vals -> Forall (YP09.chunk_ok SEGSz E m sp) (caw_fchunks k offs).
Proof.
intros E m sp offs. induction offs as [|[o w] r IH]; intros vals k He Hv; [constructor|].
destruct vals as [|v vs]; [destruct Hv|]. destruct Hv as (Hm & Hr & Hw & Hv).
constructor.
- apply (chunk_ok_val SEGSz E m sp o w (SOff k 0) v); [| exact Hr | exact Hw | exact Hm].
  cbn [sv_denot]. specialize (He 0%nat ltac:(cbn; lia)). rewrite Nat.add_0_r in He. rewrite He.
  cbn [nth]. rewrite Z.add_0_r, unsigned_lit_small by (split; [lia|]; apply (Z.lt_le_trans _ _ _ (proj2 Hr)); apply Z.pow_le_mono_r; lia).
  reflexivity.
- apply (IH vs (S k)); [| exact Hv].
  intros i Hi. specialize (He (S i) ltac:(cbn; lia)). rewrite <- Nat.add_succ_comm in He. exact He.
Qed.
Lemma caw_getr_upd_other : forall regs (r r' : bv 5) w, r' <> r -> getr (regupd regs r w) r' = getr regs r'.
Proof.
intros regs r r' w Hne. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other by (intros Heq; apply Hne; symmetry; exact Heq). reflexivity.
Qed.
Lemma caw_getr_upd_same : forall regs (r : bv 5) w, bv_eqb r 0 = false -> getr (regupd regs r w) r = w.
Proof. intros regs r w H. unfold getr, regupd. rewrite H. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma caw_Ee_reg : forall regs sp0 vals n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv ->
  ew (caw_Ee regs sp0 vals) n = getr regs r.
Proof.
intros regs sp0 vals n r Hn Hr. pose proof (u5_range r) as Hu. unfold caw_Ee.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat _ _ n r Hn).
apply caw_getr_upd_other. exact Hr.
Qed.
Lemma caw_Ee_sp : forall regs sp0 vals, ew (caw_Ee regs sp0 vals) 2 = Z_to_bv 64 sp0.
Proof.
intros regs sp0 vals. unfold caw_Ee. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). apply caw_getr_upd_same. reflexivity.
Qed.
Lemma caw_Ee_val : forall regs sp0 vals i, (i < 200)%nat -> ew (caw_Ee regs sp0 vals) (33 + i) = Z_to_bv 64 (nth i vals 0).
Proof.
intros regs sp0 vals i Hi. unfold caw_Ee. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (33 + i)%nat with (32 + S i)%nat by lia. rewrite ew_Ereg_extra.
change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth. reflexivity.
Qed.
Lemma caw_Ee_sh : forall regs sp0 vals, ew (caw_Ee regs sp0 vals) 32 = Z_to_bv 64 SHADOW_OFF.
Proof.
intros regs sp0 vals. unfold caw_Ee. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 0).
Qed.
(* regs_ok at sp = SOff 2 (-80) over the env whose atom 2 is sp0 *)
Lemma caw_regs_ok_e : forall regs sp0 vals, spZ regs = sp0 - CAW_FRAME -> CAW_FRAME <= sp0 < 2 ^ 64 ->
  regs_ok (caw_Ee regs sp0 vals) caw_sr80 regs.
Proof.
intros regs sp0 vals Hsp Hsp0 r'.
pose proof (regs_ok_Eimg_Ereg (L := A_prog_listing) (PI := PA) (regupd regs 2%bv (Z_to_bv 64 sp0))
  (map (Z_to_bv 64) (SHADOW_OFF :: vals)) r') as H.
fold (caw_Ee regs sp0 vals) in H.
unfold caw_sr80, sr_set. change (bv_eqb 2%bv 0%bv) with false. cbv iota.
unfold getr, regupd, sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact H|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx 2%bv)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'.
  cbn [sv_denot]. rewrite caw_Ee_sp. unfold spZ in Hsp. unfold CAW_FRAME in *.
  rewrite unsigned_lit_small by lia.
  unfold getr in Hsp. change (bv_eqb 2%bv 0%bv) with false in Hsp. cbv iota in Hsp.
  apply bv_eq. rewrite unsigned_lit_small by lia. lia.
- apply Nat.eqb_neq in Hi.
  unfold reg_get in *. rewrite bvmap_get_set_other in H by (intros Heq; apply Hi; rewrite Heq; reflexivity).
  exact H.
Qed.
(* the frame state of a cut at listing offset pc: the frame region below sp0, facts G *)
Lemma caw_st_ok_e : forall (W : world SEGSz) regs mem pc sp0 offs vals wlo whi G,
  regions_wf [caw_fregion_e offs wlo whi] = true -> (length offs <= 100)%nat ->
  spZ regs = sp0 - CAW_FRAME -> CAW_FRAME <= sp0 < 2 ^ 64 ->
  (forall o, wlo <= o < whi -> writable_at SEGSz (mrestrict (w_H W) mem) (sp0 + o)) ->
  caw_vals_ok (mrestrict (w_H W) mem) sp0 offs vals ->
  facts_ok (caw_Ee regs sp0 vals) G ->
  st_ok_pi SEGSz VALz (caw_Ee regs sp0 vals) (mkSS pc caw_sr80 [caw_fregion_e offs wlo whi] None G)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASEz + pc)) mem (YK11.seg_rom SEGSz))).
Proof.
intros W regs mem pc sp0 offs vals wlo whi G Hwf Hlen Hsp Hsp0 Hwr Hvals HG.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact (caw_regs_ok_e regs sp0 vals Hsp Hsp0).
- exact Hwf.
- assert (Hb : base_val (caw_Ee regs sp0 vals) (Some 2%nat) = sp0)
    by (cbn [base_val]; rewrite caw_Ee_sp; apply unsigned_lit_small; unfold CAW_FRAME in *; lia).
  constructor; [|constructor]. unfold region_ok, caw_fregion_e.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
  split; [unfold CAW_FRAME in *; lia|]. split; [lia|]. split; [exact Hwr|].
  apply (caw_fchunks_ok _ _ _ offs vals 33); [| exact Hvals].
  intros i Hi. apply caw_Ee_val. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.
(* the frame env's agreement with the register file below atom 32, kept by every later havoc above it *)
Lemma caw_Ee_agree : forall regs sp0 vals,
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) (caw_Ee regs sp0 vals).
Proof. intros regs sp0 vals. unfold caw_Ee. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* reading a stage's machine registers off its symbolic state *)
Lemma caw_reg_st : forall (H : word -> bool) E ss ms (r : bv 5) n v,
  st_ok_pi SEGSz VALz E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = v ->
  getr (ms_regs ms) r = v.
Proof.
intros H E ss ms r n v HS Hsr Hv.
rewrite (st_ok_pi_restrict_reg (L := A_prog_listing) (PI := PA) H E ss ms r HS), Hsr.
cbn [sv_denot]. rewrite Hv, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma caw_sp_st : forall (H : word -> bool) E ss ms sp0,
  st_ok_pi SEGSz VALz E ss (restrict H ms) -> sr_get (ss_regs ss) 2%bv = SOff 2 (- CAW_FRAME) ->
  ew E 2 = Z_to_bv 64 sp0 -> CAW_FRAME <= sp0 < 2 ^ 64 -> spZ (ms_regs ms) = sp0 - CAW_FRAME.
Proof.
intros H E ss ms sp0 HS Hsr E2 Hsp. unfold spZ.
rewrite (st_ok_pi_restrict_reg (L := A_prog_listing) (PI := PA) H E ss ms 2%bv HS), Hsr.
change (bv_unsigned (sv_denot E (SOff 2 (- CAW_FRAME)))) with (U E (SOff 2 (- CAW_FRAME))).
unfold CAW_FRAME in *. rewrite U_SOff, E2, unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
End bld.
