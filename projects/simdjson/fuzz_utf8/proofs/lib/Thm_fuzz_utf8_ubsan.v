(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec ShapeAlg SpinAlg. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ShapeEFS Spec SpecNoKill. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanInit. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ImgParams MainDefs MainTree MainAsm Img_src13 Img_utf8_ubsan Main_src13 Main_utf8_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Section Top.
  Variable CS : certs IP_src13.
  Variable CU : certs IP_utf8_ubsan.

  #[local] Notation SRC := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
  #[local] Notation TGT := (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).

  (* [comment removed for export] *)
  Lemma thm_either : forall en_s en_t inp,
    valid_entry SRC en_s inp -> valid_entry TGT en_t inp -> valid_input_either inp ->
    error_free_unkilled (run_scfg ACFG SRC source_alloc_limit en_s inp)
    /\ error_free_unkilled (run_scfg ACFG TGT target_alloc_limit en_t inp)
    /\ trace_equiv (bh_traces (run_scfg ACFG SRC source_alloc_limit en_s inp))
                   (bh_traces (run_scfg ACFG TGT target_alloc_limit en_t inp)).
  Proof.
    intros [rsp rbrk rmb rdr] [asp abrk amb adr] inp Hens Hent Hv.
    (* [comment removed for export] *)
    assert (Hsv48 : in_va_size inp = Sv48) by (destruct Hv as (_ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    destruct Hv as [Hargv [Henvp [Hfs [_ [[Huid Hgid] [Hnof [Hsig [Hhw _]]]]]]]].
    destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw abt va urnd tmp].
    cbn [in_va_size in_argv in_envp in_fs in_uid in_gid in_nofile in_hwcap] in *. subst va.
    apply (shape_strong_equiv_ss_unkilled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec argv (fs_seed_tmp fs tmp)) _ (spec_nokill argv (fs_seed_tmp fs tmp))).
    - exact (realizes_spec_src13 rsp rdr rbrk rmb argv envp (fs_seed_tmp fs tmp) stdin uid gid hw groups net nofile sigmask abt urnd
               Hrsp Hrbrk Hargv Henvp Hrfit Huid Hhw CS).
    - exact (realizes_spec_utf8_ubsan asp adr abrk amb argv envp (fs_seed_tmp fs tmp) stdin uid gid hw groups net nofile sigmask abt urnd
               Hasp Habrk Hargv Henvp Hafit Huid Hhw CU).
  Qed.

  (* [comment removed for export] *)
  Theorem thm :
    strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true) ShippedBudgets.lim_source ShippedBudgets.lim_target SRC TGT.
  Proof.
    intros en_s en_t inp Hens Hent Hv _.
    exact (thm_either en_s en_t inp Hens Hent (valid_input_either_of_valid_input_abort _ Hv)).
  Qed.

  (* [comment removed for export] *)
  Theorem thm_plain : strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true) SRC TGT.
  Proof.
    intros en_s en_t inp Hens Hent Hv.
    destruct (thm_either en_s en_t inp Hens Hent (valid_input_either_of_valid_input _ Hv)) as [[A _] [[B _] C]].
    exact (conj A (conj B C)).
  Qed.
End Top.
