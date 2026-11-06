(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec Scfg ShapeAlg SpinAlg ShapeEFA ShapeEFAS HeapCeil Spec AsanInit AsPlanImages AsMainState.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.LimSim Require Import LimSimRz.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsIface Fuzz_stmt AsInstanceMain AS_InstFree AS_InstanceKit AS_InstanceClosed.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require Import PlainTop PlainClosed AsanClosed.
Import ListNotations.
Open Scope Z_scope.

Local Existing Instance fx0.

Definition CFG : SpuriousCfg := Run.mkSpuriousCfg false true true true true true.

Definition SRCI : Image :=
  mkImage OSSVerify.boost_json.fuzz_parse.images.Plain.M.loaded_segments
          OSSVerify.boost_json.fuzz_parse.images.Plain.M.init_pc
          OSSVerify.boost_json.fuzz_parse.images.Plain.M.phdrs.

Definition ASANI : Image :=
  mkImage OSSVerify.boost_json.fuzz_parse.images.Asan.M.loaded_segments
          OSSVerify.boost_json.fuzz_parse.images.Asan.M.init_pc
          OSSVerify.boost_json.fuzz_parse.images.Asan.M.phdrs.

Section Open.

  (* [comment removed for export] *)
  Theorem asan_base :
    strong_universal_error_free_T_scfg_budgets_abort CFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target SRCI ASANI.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid SWB.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    change CFG with (@the_scfg hunspell_scfg) in SWB |- *.
    assert (Ha : SanitizerBudgets.lim_target = target_alloc_limit) by reflexivity.
    apply (shape_strong_equiv_ef_abort_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - (* [comment removed for export] *)
      apply (realizes_init_relim _ _ _ _ _ _ _ (2 ^ 34) SanitizerBudgets.lim_source inp _
               ltac:(unfold SanitizerBudgets.lim_source, sanitizer_source_limit; cbn; lia) SWB).
      exact (PlainClosed.plain_realizes_closed rsp rbrk rmb rrnd _ inp Hrsp Hrbrk (Z.le_refl _) Hrfit Hargv Henvp Hfs).
    - (* [comment removed for export] *)
      rewrite Ha. exact (AsanClosed.as_realizes_closed asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw).
    - apply PlainTop.spec_kill_free.
  Qed.

  (* [comment removed for export] *)
  Theorem asan_base_scfg : strong_universal_error_free_T_scfg CFG SRCI ASANI.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    change CFG with (@the_scfg hunspell_scfg).
    assert (Hr : 2 ^ 34 <= source_alloc_limit) by (unfold source_alloc_limit; cbn; lia).
    apply (shape_strong_equiv_ef_scfg_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - exact (PlainClosed.plain_realizes_closed rsp rbrk rmb rrnd _ inp Hrsp Hrbrk Hr Hrfit Hargv Henvp Hfs).
    - exact (AsanClosed.as_realizes_closed asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw).
  Qed.
End Open.
