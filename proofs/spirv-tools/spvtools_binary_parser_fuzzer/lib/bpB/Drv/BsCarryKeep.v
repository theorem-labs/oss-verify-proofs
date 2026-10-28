(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BLibKnowFrame BazyRestrict BazySR BazyFdNodes BazySym.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsLazyRun BsPrintfFirst.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import SX2. Import SX2S.

Fixpoint carry_keep (keep : kentry -> bool) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry_keep keep older kn hints in
      let '(kn2, scs2, hs2) := prune kn1 a w kn1 hs1 in
      ((if keep (KWord a w v) then KWord a w v :: kn2 else kn2), scs1 ++ scs2, hs2)
  end.

Lemma carry_keep_sound : forall segs keep E (anybase : word -> option byte) base log kn hints kn' scs hs',
  carry_keep keep log kn hints = (kn', scs, hs') ->
  log_flat E log -> know_ok segs E base kn -> scs_denot segs anybase E scs ->
  know_ok segs E (mem_denot E base log) kn'.
Proof.
  intros segs keep E anyb base log. induction log as [|[a w v] older IH]; intros kn hints kn' scs hs' Hc Hlf Hkn Hscs.
  - cbn in Hc. injection Hc as <- <- <-. exact Hkn.
  - cbn [carry_keep] in Hc. cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf').
    destruct (carry_keep keep older kn hints) as [[kn1 scs1] hs1] eqn:Hco.
    destruct (prune kn1 a w kn1 hs1) as [[kn2 scs2] hs2] eqn:Hpr.
    injection Hc as <- <- <-.
    apply scs_denot_app in Hscs as [Hs1 Hs2].
    cbn [mem_denot].
    assert (HP : know_ok segs E (wbytes (mem_denot E base older) (adenot E a) (word_to_le_bytes w (edenot E v))) kn2)
      by (eapply prune_sound; eauto).
    destruct (keep (KWord a w v)); [| exact HP].
    constructor; [| exact HP].
    cbn [kentry_ok]. split; [exact Hw8|]. split; [exact Hfa|].
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v)) (mem_denot E base older) (adenot E a)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. rewrite (flat_u E _ _ Hfa).
    destruct Hfa as (?&?&?&?). lia.
Qed.

