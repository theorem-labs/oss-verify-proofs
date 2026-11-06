(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OSSVerify.openssl.echconfiglist_parser.images.Plain.
Require OSSVerify.openssl.echconfiglist_parser.images.Ubsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg ShapeEF Spec HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require RefTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require UbTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

Definition CFG : SpuriousCfg := Run.mkSpuriousCfg false true true true true true.

Section WithLib.
  (* [comment removed for export] *)
  Hypothesis FZ_p : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
      @OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_Iface.fuzz_stmt HCEIL (@OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.MallocSR.HS HCEIL HSEC).
  Hypothesis FZ_u : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
      @OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.ECH_Iface.fuzz_stmt HCEIL (@OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.MallocSR.HS HCEIL HSEC).

  (* [comment removed for export] *)
  Theorem ubsan_base_scfg :
    strong_universal_error_free_T_scfg CFG
      (mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments
               OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc
               OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs)
      (mkImage OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.loaded_segments
               OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.init_pc
               OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.phdrs).
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    change CFG with (@the_scfg hunspell_scfg).
    apply (shape_strong_equiv_ef_scfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - exact (RefTop.ref_realizes_spec FZ_p rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs).
    - exact (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.UbTop.ub_realizes_spec FZ_u asp abrk amb arnd inp Hasp Habrk Hafit Hargv Henvp Hfs).
  Qed.

  (* [comment removed for export] *)
  Theorem ubsan_base :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
      CFG
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs)
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.phdrs).
  Proof.
    intros en_source en_target inp Hens Hent Hvalid _.
    unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
    exact (ubsan_base_scfg en_source en_target inp Hens Hent Hvalid).
  Qed.
End WithLib.
