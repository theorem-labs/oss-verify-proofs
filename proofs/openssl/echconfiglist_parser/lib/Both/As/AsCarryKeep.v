(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymRun SymDrive LibKnowFrame
  LazyRestrict LazySR LazyFdNodes LazySym SymCarrySkip.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsLazyRun AsPrintfFirst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

(* [comment removed for export] *)
Theorem rz_run_lf_lazy_keep : forall keep segs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R msF mo T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry_keep keep (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst R (Z_to_bv 64 pc) M rom ->
  (forall R' M' msF' mo', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom ->
     realizes segs (mkCfg msF' mo') T) ->
  realizes segs (mkCfg msF mo) T.
Proof.
  intros keep segs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF mo T
         Hex Hc HR HK Hsc Hsc2 Hok Hr Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply (rz_msteps_lazy_mkst segs L S Zr); [exact Hok | exact Hr | exact Hms |].
  intros msF' mo' Hok' Hsb Hhs Hr'.
  apply (Hcont R' (mem_denot E M (s_log ss')) msF' mo' HR'); [| reflexivity | exact Hlf | exact Hok' | exact Hsb | exact Hhs | exact Hr'].
  eapply carry_keep_sound; eassumption.
Qed.

(* [comment removed for export] *)
Theorem rz_run_lf_lazy_skip : forall lo hi segs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R msF mo T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry_skip lo hi (s_log ss') kn [] = (kn', scs2, hs2) ->
  (0 <= lo)%Z -> (lo <= hi)%Z -> (lo < 2 ^ 64)%Z -> (hi <= 2 ^ 64)%Z ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst R (Z_to_bv 64 pc) M rom ->
  (forall R' M' msF' mo', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom ->
     realizes segs (mkCfg msF' mo') T) ->
  realizes segs (mkCfg msF mo) T.
Proof.
  intros lo hi segs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF mo T
         Hex Hc Hlo Hlh Hlo64 Hhi HR HK Hsc Hsc2 Hok Hr Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply (rz_msteps_lazy_mkst segs L S Zr); [exact Hok | exact Hr | exact Hms |].
  intros msF' mo' Hok' Hsb Hhs Hr'.
  apply (Hcont R' (mem_denot E M (s_log ss')) msF' mo' HR'); [| reflexivity | exact Hlf | exact Hok' | exact Hsb | exact Hhs | exact Hr'].
  eapply carry_skip_sound; eassumption.
Qed.
