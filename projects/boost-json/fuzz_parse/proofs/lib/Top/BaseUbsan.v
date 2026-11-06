(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OSSVerify.boost_json.fuzz_parse.images.Plain.
Require OSSVerify.boost_json.fuzz_parse.images.Ubsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg ShapeAlg ShapeEF ShapeEFA HeapCeil HeapSecret Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require MallocMF.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJIface BJIfaceStr BJIfaceEsc BJIfaceTop.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require EhGlue.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require PlainTop PlainClosed UbsanClosed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition CFG : SpuriousCfg := Run.mkSpuriousCfg false true true true true true.

Definition SRCI : Image :=
  mkImage OSSVerify.boost_json.fuzz_parse.images.Plain.M.loaded_segments
          OSSVerify.boost_json.fuzz_parse.images.Plain.M.init_pc
          OSSVerify.boost_json.fuzz_parse.images.Plain.M.phdrs.

Definition UBSI : Image :=
  mkImage OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.loaded_segments
          OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.init_pc
          OSSVerify.boost_json.fuzz_parse.images.Ubsan.M.phdrs.

Section Open.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem ubsan_base_scfg : strong_universal_error_free_T_scfg CFG SRCI UBSI.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _).
    change CFG with (@the_scfg hunspell_scfg).
    assert (Hr : 2 ^ 34 <= source_alloc_limit) by (unfold source_alloc_limit; cbn; lia).
    assert (Ha : 2 ^ 34 <= target_alloc_limit) by (unfold target_alloc_limit; cbn; lia).
    apply (shape_strong_equiv_ef_scfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - exact (PlainClosed.plain_realizes_closed rsp rbrk rmb rrnd _ inp Hrsp Hrbrk Hr Hrfit Hargv Henvp Hfs).
    - exact (UbsanClosed.ubsan_realizes_closed asp abrk amb arnd _ inp Hasp Habrk Ha Hafit Hargv Henvp Hfs).
  Qed.

  (* [comment removed for export] *)
  Theorem ubsan_base :
    strong_universal_error_free_T_scfg_budgets_abort CFG ShippedBudgets.lim_source ShippedBudgets.lim_target SRCI UBSI.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _).
    change CFG with (@the_scfg hunspell_scfg).
    assert (Hr : 2 ^ 34 <= ShippedBudgets.lim_source) by (unfold ShippedBudgets.lim_source, source_alloc_limit; cbn; lia).
    assert (Ha : 2 ^ 34 <= ShippedBudgets.lim_target) by (unfold ShippedBudgets.lim_target, target_alloc_limit; cbn; lia).
    apply (shape_strong_equiv_ef_abort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - exact (PlainClosed.plain_realizes_closed rsp rbrk rmb rrnd _ inp Hrsp Hrbrk Hr Hrfit Hargv Henvp Hfs).
    - exact (UbsanClosed.ubsan_realizes_closed asp abrk amb arnd _ inp Hasp Habrk Ha Hafit Hargv Henvp Hfs).
    - apply PlainTop.spec_kill_free.
  Qed.
End Open.
