(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa1), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySetGa1.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySetGa1.v, ported from a working branch
   7c8c67da870 (blob 6343983ade5; the image-A file carries no licence lines, so none are copied).

   The set loop of LLVMFuzzerTestOneInput on image B: the piece GA1 → G78 | the call of
   reac_headamp_tx_effective (the slots 0x80f9c .. 0x810b0, fuzz/fuzz_grant.c:201-224).

   At 0x80f9c the turn's cell had one byte left: reac_headamp_tx_set was called with the channel in s2 and
   parameter and value 0 (gcell_cases), and a0 holds its answer. The code keeps it in s10, sets a2 (the bytes
   left) to 0 and tests the channel (`bgeu s2,48` at 0x80fa8):
   - below 48: s9 := s8 := 0, s7 := s11 (0x8104c), a0 := (0 < 3 && 0 < 2) - 1 = 0 and s6 := 1 (0x81050 ..
     0x81060); the set accepted (legalb 0 0), so the check at 0x81064 (`bne s10,a0` into the abort 0x81d98)
     falls through, `bnez s10` at 0x8109c too, and the piece ends at the call of reac_headamp_tx_effective
     at 0x810b0;
   - 48 or more: s6 := s8 := s9 := 0, a0 := -1, s7 := s11 (0x81084 .. 0x81094); the set refused, so the check
     at 0x81098 (`bne s10,a0` into 0x81d98) falls through and `bnez s10` at 0x8109c goes to the end of the
     turn at 0x81140 (G78).
   The run writes no memory. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* The state at 0x80f9c: s10's source a0 pinned to the set's answer z, the channel atom
   (s2) in [lo, hi]; no memory. *)
Definition F_ga1 (lo hi : Z) : facts := mkFacts [(18%nat, mkAF lo hi 0)] [] [].
Definition ss_ga1a (lo hi : Z) : sstate := mkSS 0x560 sr_atoms [] None (F_ga1 lo hi).
Definition ss_ga1 (z lo hi : Z) : sstate := mkSS 0x560 (sr_set sr_atoms 10%bv (SLit z)) [] None (F_ga1 lo hi).

Section ga1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
(* The call of reac_headamp_tx_effective at 0x810b0 after an accepted set. *)
Hypothesis CALLE2 : call_e2_stmt B MT.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* The memory after runs whose frames are empty is the memory before them. *)
Ltac memeq ms0 :=
  let a := fresh "a" in intros a; cbn [ms_mem mkst];
  repeat match goal with
  | |- aview _ _ (ms_mem ms0) _ = _ => reflexivity
  | H : frame_of _ _ (ms_mem ?m1) (ms_mem ?m2) |- aview _ _ (ms_mem ?m2) _ = _ =>
      rewrite (frame_nil_eq _ _ _ _ _ eq_refl H a)
  end.
(* A register whose value the cut's atoms give. *)
Ltac vgoal HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let X := fresh "X" in prreg HS r X; rewrite X;
    first [ reflexivity | assumption | (unfold w64; f_equal; lia) ] end.

(* The state at 0x80f9c holds, for an answer z of the set and a channel in [lo, hi]. *)
Lemma ga1_entry : forall (W3 : world SEGS) ms3 E z lo hi c,
  E = Eimg (Ereg (ms_regs ms3) []) ->
  getr (ms_regs ms3) 18 = w64 c -> getr (ms_regs ms3) 10 = Z_to_bv 64 z ->
  0 <= lo -> lo <= c <= hi -> hi < 2 ^ 64 ->
  st_ok_pi SEGS VAL E (ss_ga1 z lo hi)
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + 0x560)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
  intros W3 ms3 E z lo hi c HE R18 R10 Hlo Hc Hhi.
  assert (ER : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr (ms_regs ms3) r)
    by (intros n0 r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (E18 : ew E 18 = w64 c) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  apply (st_ok_pi_set_reg E (ss_ga1a lo hi) _ (10%bv : bv 5) (SLit z));
    [| discriminate | cbn [ms_regs restrict mkst sv_denot]; exact R10].
  rewrite restrict_mkst_fx. unfold ss_ga1a. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - unfold F_ga1. split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18. unfold w64. rewrite !unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. splits; first [exact I | lia].
Qed.

Lemma ge_set_ga1 : seg_ga1_stmt B MT.
Proof.
  intros POST n i HN HE2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & HLEN & HM & R10 & R18 & R27).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  (* One byte was left: the cell is (that byte, 0, 0) and the cursor moves past it. *)
  pose proof (gcell_cases (c_pl cx) i) as Hcc. cbv zeta in Hcc.
  destruct Hcc as [(H3 & _) | [(H2 & _) | [(H1 & Ecell & Epos) | (H0 & _)]]]; [lia | lia | | lia].
  assert (Eq0 : gq (c_pl cx) i = 0) by (unfold gq; rewrite Ecell; reflexivity).
  assert (Ev0 : gv (c_pl cx) i = 0) by (unfold gv; rewrite Ecell; reflexivity).
  (* So the set is accepted exactly when the channel is below 48 (legalb 0 0 = true). *)
  assert (Eacc : gacc (c_pl cx) i = (gc (c_pl cx) i <? 48))
    by (unfold gacc; rewrite Eq0, Ev0; change (legalb 0 0) with true; apply andb_true_r).
  assert (Ecn : c_n cx = Z.of_nat (length (c_pl cx))) by reflexivity.
  assert (Hv0 : c_n cx - Z.of_nat (gpos (c_pl cx) (S i)) = 0) by (rewrite Ecn, HLEN, Epos; lia).
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & _ & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr (ms_regs ms3) r)
    by (intros n0 r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); exact G2).
  assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); exact G3).
  assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); exact G4).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (ER 8%nat 8%bv eq_refl); exact G8).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
  assert (E18 : ew E 18 = w64 (gc (c_pl cx) i)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E19 : ew E 19 = w64 (gSH cx fp)) by (rewrite (ER 19%nat 19%bv eq_refl); exact H19).
  assert (E20 : ew E 20 = w64 t) by (rewrite (ER 20%nat 20%bv eq_refl); exact H20).
  assert (E21 : ew E 21 = w64 (Z.of_nat (S n))) by (rewrite (ER 21%nat 21%bv eq_refl); exact H21).
  assert (E27 : ew E 27 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i)))) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  rewrite (gmach_mkst cx ms3 _ HMA).
  destruct (Z.ltb_spec (gc (c_pl cx) i) 48) as [Hc48 | Hc48].
  - (* The channel is below 48: the set accepted (a0 = 0); on to the call of
       reac_headamp_tx_effective at 0x810b0. *)
    pose proof Eacc as HA. rewrite HA in R10.
    pose proof (ga1_entry W3 ms3 E 0 0 47 (gc (c_pl cx) i) HE R18 R10 ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
    paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_nil |].
    pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
    apply (CALLE2 POST n i cx fp k acc ly3 S3 W3 _ _ _ t HE2 HB HJ HFR HMO Hk Hacc Hbl Ht0 Hn Hns HA).
    all: first [ vgoal HS | (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM]) ].
  - (* The channel is 48 or more: the set refused (a0 = -1); on to the end of the turn
       at 0x81140. *)
    pose proof Eacc as HA. rewrite HA in R10.
    pose proof (ga1_entry W3 ms3 E (-1) 48 255 (gc (c_pl cx) i) HE R18 R10 ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x704; [apply awr_ok_nil |].
    let m := lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => m end in rename m into msA.
    apply (HN cx fp k acc ly3 S3 W3 msA _ HB HJ HFR HMO).
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    destruct (gtables_S (c_pl cx) i) as (_ & EW & ES). rewrite HA in EW, ES.
    exists t. split; [|split; [|split]].
    + unfold gcore, gmach, gregs. splits; try assumption; vgoal HS.
    + rewrite EW, ES. apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM].
    + vgoal HS.
    + vgoal HS.
Qed.

End ga1.
