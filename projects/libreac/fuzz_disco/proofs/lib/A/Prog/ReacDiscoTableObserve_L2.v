(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 167 of its 204 lines of code are new or changed and 32 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X ReacDiscoTableObserve_L.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma tobs_reg_same_pi : forall c regs1 Tc r E' ss ms H (q : bv 5),
  st_ok_pi SEGS VAL E' ss (restrict H ms) -> regs_ok (tobs_env c regs1 Tc r) tobs_sr regs1 ->
  sr_get (ss_regs ss) q = sr_get tobs_sr q -> sv_atoms_lt 32 (sr_get tobs_sr q) = true ->
  env_agree 32 (tobs_env c regs1 Tc r) E' ->
  YK11.getr (ms_regs ms) q = YK11.getr regs1 q.
Proof.
intros c regs1 Tc r E' ss ms H q HS HR Hq Hat HA.
rewrite (st_ok_pi_restrict_reg H E' ss ms q HS), Hq, (sv_denot_agree 32 _ _ _ HA Hat).
symmetry. exact (HR q).
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Ltac tobs_regq HS HR0 :=
  eapply (tobs_reg_same_pi _ _ _ _ _ _ _ _ _ HS HR0);
  [ vm_compute; reflexivity | vm_compute; reflexivity
  | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity] ].
Lemma loop_tail : forall c j, SegNone B c -> SegLoopAt B c (j + 1) ->
  forall regs1 m1 md1, tpre B c -> tobs_m B c regs1 m1 md1 (tT c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 23 = w64 (DTC.n_of (tT c)) ->
  YK11.getr regs1 25 = w64 (48 * (j + 1)) -> YK11.getr regs1 26 = w64 (48 * DTC.n_of (tT c)) ->
  0 <= j < DTC.n_of (tT c) -> (forall j', 0 <= j' <= j -> DTC.mac_of (tT c) j' <> DTC.s_mac (tG c)) ->
  SRr SEGS (tW c) (cfgB 0x5144 regs1 m1 md1) (tpost B c).
Proof.
intros c j HNo HL regs1 m1 md1 HP HM H18 H23 H25 H26 Hj Hmis.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63. pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
assert (B8 : base_val (tobs_env c regs1 (tT c) 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 (tT c) 0 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  apply unsigned_lit_small. lia. }
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (tobs_env c regs1 (tT c) 0) n = YK11.getr regs1 x)
  by (intros n x Hnx; apply tobs_env_reg; exact Hnx).
pose proof (tobs_regs_ok c regs1 (tT c) 0 (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM)
  (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
pose proof (tobs_env_img c regs1 (tT c) 0) as HEI.
destruct (tobs_enter B c regs1 m1 md1 (tT c) 0x5144 false 0 0 HP HM ltac:(left; reflexivity)
  ltac:(rewrite H18; f_equal; lia) ltac:(discriminate)) as [HS SHOK].
unfold cfgB.
assert (U26 : U (tobs_env c regs1 (tT c) 0) (SOff 26 0) = 48 * DTC.n_of (tT c))
  by (apply U_atom; [rewrite (EE 26%nat 26%bv eq_refl); exact H26 | lia]).
assert (U25 : U (tobs_env c regs1 (tT c) 0) (SOff 25 0) = 48 * (j + 1))
  by (apply U_atom; [rewrite (EE 25%nat 25%bv eq_refl); exact H25 | lia]).
psrr_branch_tok RUN BR HS SHOK TBspan.
- rewrite branch_eq_U, U26, U25 in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x53c4.
  { exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
    assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (tT c))
  end.
  { apply (tobs_exit_nostore B LAWS c regs1 m1 md1 (tT c) 0 _ (ms_mem ms) _ (ms_regs ms) HP HM ltac:(left; reflexivity) HFr HG HJ Hreg B8 eq_refl).
    intros q Hq. cbn in Hq.
    repeat (destruct Hq as [<- | Hq]; [tobs_regq HS HR0 |]).
    destruct Hq. }
  assert (S18 : YK11.getr (ms_regs ms) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq HS HR0).
  assert (S23 : YK11.getr (ms_regs ms) 23 = w64 (DTC.n_of (tT c))) by (rewrite <- H23; tobs_regq HS HR0).
  assert (S26 : YK11.getr (ms_regs ms) 26 = w64 (48 * DTC.n_of (tT c))) by (rewrite <- H26; tobs_regq HS HR0).
  pmkst HS.
  apply (HNo _ _ _ HP HM2 S18 S23).
  intros j' Hj' Heq. apply (Hmis j' ltac:(lia) Heq).
- rewrite branch_eq_U, U26, U25 in Hc. apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5128.
  { exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
    assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (tT c))
  end.
  { apply (tobs_exit_nostore B LAWS c regs1 m1 md1 (tT c) 0 _ (ms_mem ms) _ (ms_regs ms) HP HM ltac:(left; reflexivity) HFr HG HJ Hreg B8 eq_refl).
    intros q Hq. cbn in Hq.
    repeat (destruct Hq as [<- | Hq]; [tobs_regq HS HR0 |]).
    destruct Hq. }
  assert (S18 : YK11.getr (ms_regs ms) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq HS HR0).
  assert (S23 : YK11.getr (ms_regs ms) 23 = w64 (DTC.n_of (tT c))) by (rewrite <- H23; tobs_regq HS HR0).
  assert (S26 : YK11.getr (ms_regs ms) 26 = w64 (48 * DTC.n_of (tT c))) by (rewrite <- H26; tobs_regq HS HR0).
  pmkst HS.
  assert (S25 : YK11.getr (ms_regs ms) 25 = w64 (48 * (j + 1))) by (rewrite <- H25; tobs_regq HS HR0).
  apply (HL _ _ _ HP HM2 S18 S23 S25 S26 ltac:(lia)).
  intros j' Hj' Heq. apply (Hmis j' ltac:(lia) Heq).
Qed.
Lemma loop_after : forall c j, SegFound B c -> SegNone B c -> SegLoopAt B c (j + 1) -> SegLoop2At B c j.
Proof.
intros c j HFd HNo HL regs1 m1 md1 v HP HM H18 H19 H23 H25 H26 H10 Hcmp Hj Hmis.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63. pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
assert (B8 : base_val (tobs_env c regs1 (tT c) 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 (tT c) 0 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  apply unsigned_lit_small. lia. }
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (tobs_env c regs1 (tT c) 0) n = YK11.getr regs1 x)
  by (intros n x Hnx; apply tobs_env_reg; exact Hnx).
pose proof (tobs_regs_ok c regs1 (tT c) 0 (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM)
  (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
pose proof (tobs_env_img c regs1 (tT c) 0) as HEI.
assert (Hmb := TM.mac_bytes (tT c) (tG c) j HTl HGl ltac:(lia)).
destruct (tobs_enter B c regs1 m1 md1 (tT c) 0x513c false 0 0 HP HM ltac:(left; reflexivity)
  ltac:(rewrite H18; f_equal; lia) ltac:(discriminate)) as [HS SHOK].
unfold cfgB.
assert (U10 : U (tobs_env c regs1 (tT c) 0) (SOff 10 0) = bv_unsigned v).
{ apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), H10; symmetry; apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range]. }
assert (U0 : U (tobs_env c regs1 (tT c) 0) (SLit 0) = 0) by (apply U_lit; lia).
psrr_branch_tok RUN BR HS SHOK TBspan.
- rewrite branch_eq_U, U10, U0 in Hc. apply Z.eqb_eq in Hc.
  assert (Hv : v = w64 0) by (apply bv_eq; rewrite Hc; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  pose proof (proj2 Hmb (proj1 Hcmp Hv)) as Hfd.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x514c.
  { exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
    assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (tT c))
  end.
  { apply (tobs_exit_nostore B LAWS c regs1 m1 md1 (tT c) 0 _ (ms_mem ms) _ (ms_regs ms) HP HM ltac:(left; reflexivity) HFr HG HJ Hreg B8 eq_refl).
    intros q Hq. cbn in Hq.
    repeat (destruct Hq as [<- | Hq]; [tobs_regq HS HR0 |]).
    destruct Hq. }
  assert (S18 : YK11.getr (ms_regs ms) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq HS HR0).
  assert (S23 : YK11.getr (ms_regs ms) 23 = w64 (DTC.n_of (tT c))) by (rewrite <- H23; tobs_regq HS HR0).
  assert (S26 : YK11.getr (ms_regs ms) 26 = w64 (48 * DTC.n_of (tT c))) by (rewrite <- H26; tobs_regq HS HR0).
  pmkst HS.
  assert (S19 : YK11.getr (ms_regs ms) 19 = w64 (tt c + 48 * j)) by (rewrite <- H19; tobs_regq HS HR0).
  apply (HFd _ _ _ j HP HM2 S18 S19).
  split; [lia | split; [exact Hfd | exact Hmis]].
- rewrite branch_eq_U, U10, U0 in Hc. apply Z.eqb_neq in Hc.
  assert (Hnf : DTC.mac_of (tT c) j <> DTC.s_mac (tG c)).
  { intros Heq. apply Hc. rewrite (proj2 Hcmp (proj1 Hmb Heq)). unfold w64. apply unsigned_lit_small. lia. }
  paj_run_tok RUN HS HJ SHOK TBspan.
  { exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
    assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (tT c))
  end.
  { apply (tobs_exit_nostore B LAWS c regs1 m1 md1 (tT c) 0 _ (ms_mem ms) _ (ms_regs ms) HP HM ltac:(left; reflexivity) HFr HG HJ Hreg B8 eq_refl).
    intros q Hq. cbn in Hq.
    repeat (destruct Hq as [<- | Hq]; [tobs_regq HS HR0 |]).
    destruct Hq. }
  assert (S18 : YK11.getr (ms_regs ms) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq HS HR0).
  assert (S23 : YK11.getr (ms_regs ms) 23 = w64 (DTC.n_of (tT c))) by (rewrite <- H23; tobs_regq HS HR0).
  assert (S26 : YK11.getr (ms_regs ms) 26 = w64 (48 * DTC.n_of (tT c))) by (rewrite <- H26; tobs_regq HS HR0).
  pmkst HS.
  prreg HS (25%bv : bv 5) P25.
  rewrite (EE 25%nat 25%bv eq_refl), H25 in P25.
  assert (S25 : YK11.getr (ms_regs ms) 25 = w64 (48 * (j + 1))).
  { rewrite P25. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  apply (loop_tail c j HNo HL _ _ _ HP HM2 S18 S23 S25 S26 Hj).
  intros j' Hj' Heq. destruct (Z.eq_dec j' j) as [-> | Hne]; [exact (Hnf Heq) | apply (Hmis j' ltac:(lia) Heq)].
Qed.
Lemma seg_loop_full : forall c, SegFound B c -> SegNone B c -> SegLoop B c.
Proof.
intros c HFd HNo. eapply seg_loop;
first [ exact LAWS | exact TL | exact ABCMP | intros j HL; exact (loop_after c j HFd HNo HL) ].
Qed.
End h.
End f.
End d.
