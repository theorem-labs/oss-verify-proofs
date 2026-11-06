(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa0), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySetGa0.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySetGa0.v, ported from a working branch
   7c8c67da870 (blob d23210e6857; the image-A file carries no licence lines, so none are copied).

   The set loop of LLVMFuzzerTestOneInput on image B: the piece of a turn that starts at GA0
   (LLVMFEntrySetDefs.v), slots 0x80f70 .. 0x810b0.

   At GA0 the cell had no byte left, and reac_headamp_tx_set was called at 0x80f6c with the cell (0, 0, 0)
   (fuzz/fuzz_grant.c:201-230 reads 0 for each byte past the end). The code keeps the set's answer in s10,
   sets a2 (the bytes left), s9, s2 and s8 (value, channel, parameter) to 0 and jumps to 0x81050, which
   computes the answer the set must give, (s8 < 3 && s9 < 2) - 1, which is 0, and sets s6 := 1. The check at
   0x81064 (`bne s10,a0` into the abort block at 0x81d98) compares the two: the channel 0 is below 48 and the
   value 0 is legal for the parameter 0 (legalb 0 0, lib/Prog/HeadampModel.v:58), so the set accepted the
   cell, s10 is 0 and the branch is not taken. Nor is the one at 0x8109c (`bnez s10`) to the refused end of
   the turn at 0x81140. a2 is saved in s10 (0x810a0) and the piece ends at the call of
   reac_headamp_tx_effective at 0x810b0, which call_e2_stmt carries on to GE2. The run writes no memory, so
   unlike image A's piece (which stored slot 120) it carries no region. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* The state at 0x80f70: a0 pinned to 0, the answer of an accepted set; no memory. *)
Definition ss_ga0 : sstate := mkSS 0x534 (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []).
Definition ss_ga0a : sstate := mkSS 0x534 sr_atoms [] None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
(* The call of reac_headamp_tx_effective at 0x810b0 after an accepted set lands in GE2. *)
Hypothesis CALLE2 : call_e2_stmt B MT.

Let RUN := paj_run B LAWS.

Ltac curms HS := lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?m) => m
  | st_ok _ _ _ (restrict _ ?m) => m
  end.
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

Lemma ge_set_ga0 : seg_ga0_stmt B MT.
Proof.
  intros POST n i HN HE2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & Hlen & HM & R10 & R23).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  (* The cell: no byte is left, so it reads (0, 0, 0) (gcell_cases, from
     SegSetModel.cell_rd_0), and the set accepts it: 0 < 48 and legalb 0 0. *)
  pose proof (gcell_cases (c_pl cx) i) as HCC. cbv zeta in HCC.
  destruct HCC as [(Hc3 & _) | [(Hc2 & _) | [(Hc1 & _) | (_ & Ecell & EposS)]]]; [lia | lia | lia |].
  assert (Ec : gc (c_pl cx) i = 0) by (unfold gc; rewrite Ecell; reflexivity).
  assert (Eq : gq (c_pl cx) i = 0) by (unfold gq; rewrite Ecell; reflexivity).
  assert (Ev : gv (c_pl cx) i = 0) by (unfold gv; rewrite Ecell; reflexivity).
  assert (HA : gacc (c_pl cx) i = true) by (unfold gacc; rewrite Ec, Eq, Ev; reflexivity).
  rewrite HA in R10. cbv beta iota in R10.
  assert (Ecn : c_n cx = Z.of_nat (length (c_pl cx))) by reflexivity.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r)
    by (intros n0 r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); subst regs; exact G2).
  assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); subst regs; exact G3).
  assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); subst regs; exact G4).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (ER 8%nat 8%bv eq_refl); subst regs; exact G8).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); subst regs; exact G9).
  assert (E19 : ew E 19 = w64 (gSH cx fp)) by (rewrite (ER 19%nat 19%bv eq_refl); subst regs; exact H19).
  assert (E20 : ew E 20 = w64 t) by (rewrite (ER 20%nat 20%bv eq_refl); subst regs; exact H20).
  assert (E21 : ew E 21 = w64 (Z.of_nat (S n))) by (rewrite (ER 21%nat 21%bv eq_refl); subst regs; exact H21).
  assert (E23 : ew E 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))))
    by (rewrite (ER 23%nat 23%bv eq_refl); subst regs; rewrite EposS; exact R23).
  assert (HS0 : st_ok_pi SEGS VAL E ss_ga0a (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x534)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_ga0a. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  (* a0 holds the set's answer, 0 (R10). *)
  assert (HS : st_ok_pi SEGS VAL E ss_ga0 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x534)) mem (seg_rom SEGS)))).
  { apply (st_ok_pi_set_reg E ss_ga0a _ (10%bv : bv 5) (SLit 0) HS0); [discriminate|].
    cbn [ms_regs restrict mkst]. subst regs. rewrite R10. reflexivity. }
  clear HS0.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) mem)) by constructor.
  subst mem.
  (* 0x80f70 .. 0x810b0: s10 = a0 = 0, the computed answer (s8 < 3 && s9 < 2) - 1 = 0,
     so neither the branch at 0x81064 to the abort block 0x81d98 nor the one at 0x8109c
     to 0x81140 is taken; the run stops at the call of reac_headamp_tx_effective. *)
  paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_nil |].
  pmkst HS.
  rewrite pa_sigma_reac_headamp_tx_effective.
  apply (CALLE2 POST n i cx fp k acc ly3 S3 W3 _ _ _ t HE2 HB HJ HFR HMO Hk Hacc Hbl Ht0 Hn Hns HA).
  all: first [ vgoal HS
             | (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM]) ].
Qed.

End c.
End b.
End a.
