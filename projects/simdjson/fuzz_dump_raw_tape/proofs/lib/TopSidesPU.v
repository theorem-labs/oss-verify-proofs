(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Import TopLevel Obligations ProofBase TopPlain TopE.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prog ModelInv ModelInvN MallocSome Canon CanonNoKill ProgDetIface ProgDet ProgNoEnomem.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Unforced.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Plain.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition Tc (inp : ProcInput) : list event -> Prop := canonT (argv_Z (in_argv inp)) (in_fs inp).

Lemma Tc_nokill : T_nokill Tc.
Proof. intros inp tr sig fs H. exact (canonT_nokill _ _ tr sig fs H). Qed.

Theorem P_side : impl_P_stmt ->
  side_canon Tc (mkImage psegs Plain.M.init_pc Plain.M.phdrs) source_alloc_limit.
Proof. intros HP en inp He Hi. exact (P_canon HP prog_no_enomem_P en inp He Hi). Qed.

Theorem P_side_lim : forall lim, Unforced.KLIM + Unforced.SMALLREQ <= lim -> impl_P_stmt ->
  side_canon Tc (mkImage psegs Plain.M.init_pc Plain.M.phdrs) lim.
Proof.
  intros lim Hlim HP en inp He Hi.
  exact (P_canon_lim lim HP (prog_no_enomem_any psegs pstage _ _ lim segs_pu_P Hlim) en inp He Hi).
Qed.

Theorem P_side_san : impl_P_stmt ->
  side_canon Tc (mkImage psegs Plain.M.init_pc Plain.M.phdrs) SanitizerBudgets.lim_source.
Proof. apply P_side_lim. unfold Unforced.KLIM, Unforced.SMALLREQ, SanitizerBudgets.lim_source, sanitizer_source_limit. lia. Qed.

Theorem U_side : impl_U_stmt ->
  side_canon Tc (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) target_alloc_limit.
Proof.
  intros HU en inp He Hi.
  destruct (prog_model_ok_U (CE__:=run_ceiling en) (raw_malloc_some (CE__:=run_ceiling en)) en inp He Hi
              (run_ceiling_eqA _ _ _ _ _ (vie_va_size _ Hi) He) (prog_no_enomem_U en inp He Hi)) as [Hl Hs].
  destruct (run_of_tree usegs Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit
              (the_prog usegs ustage inp en) (epost the_post) en inp (HU en inp He Hi) Hl
              (tsafe_conj nstep nsafe unforced _ _ Hs
                 (tsafe_mono nstep no_enomem unforced _ _ no_enomem_unforced (prog_no_enomem_U en inp He Hi))))
    as (t' & Hres & Htr & Herr & _).
  split; [| exact Herr].
  intros tr. rewrite (Htr tr). exact (prog_det_U prog_no_enomem_U en inp He Hi t' Hres tr).
Qed.

Section Bases.
  Hypothesis HP : impl_P_stmt.

  Section Ubsan.
    Hypothesis HU : impl_U_stmt.
    Theorem ubsan_off : strong_universal_error_free_T_scfg ACFG
      (mkImage psegs Plain.M.init_pc Plain.M.phdrs) (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs).
    Proof. exact (glue_off Tc _ _ (P_side HP) (U_side HU)). Qed.
    Theorem ubsan_base : strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage psegs Plain.M.init_pc Plain.M.phdrs) (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs).
    Proof. exact (glue_budgets_abort Tc _ _ (P_side HP) (U_side HU) Tc_nokill). Qed.
  End Ubsan.

End Bases.
