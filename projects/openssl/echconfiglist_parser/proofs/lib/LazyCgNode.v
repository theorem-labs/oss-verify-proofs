(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time Require Import PosixTimers.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import CgNode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  Scfg SimInv ExitSim PropExec CatExec CatSim MmapSim AllocSim FileSim RelSpec
  ShapeAlg Nodes AgentLib AgentNodes Gap04 RefNodes RefNodesDir Hoare LibWritev SReach
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR LazyNodes LazyFdNodes.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg} {AF : AllocForced SC}.

(* [comment removed for export] *)
Lemma wr_at_restrictL : forall L S mF a n,
  lazy_ranges_okb segs L = true ->
  wr_at segs (restrict_mem L S mF) a n ->
  wr_at segs mF a n /\ (forall i, (0 <= i < n)%Z -> hiddenb L S (wa (a + i)) = false).
Proof.
  intros L S mF a n HL (H0 & Hn & W).
  assert (X : forall i, (0 <= i < n)%Z -> hiddenb L S (wa (a + i)) = false /\ wview segs mF (wa (a + i)) <> None).
  { intros i Hi. specialize (W i Hi). unfold restrict_mem in W.
    rewrite (wview_restrict segs (hiddenb L S) (lazy_ranges_ok_avoids segs L S HL)) in W.
    destruct (hiddenb L S (wa (a + i))); [exfalso; apply W; reflexivity| auto]. }
  split; [| intros i Hi; apply (X i Hi)].
  split; [exact H0|]. split; [exact Hn|]. intros i Hi. apply (X i Hi).
Qed.

(* [comment removed for export] *)
Lemma cg_at_node_restrictL : forall L S msF tp,
  lazy_ranges_okb segs L = true ->
  cg_at_node segs (CGRealtime tp) (restrict L S msF) ->
  cg_at_node segs (CGRealtime tp) msF /\ (forall i, (0 <= i < 16)%Z -> hiddenb L S (wa (tp + i)) = false).
Proof.
  intros L S msF tp HL (SV & A0 & A1 & ROM & WR).
  rewrite ms_mem_restrict in WR. destruct (wr_at_restrictL L S (ms_mem msF) tp 16 HL WR) as [WRF VIS].
  split; [| exact VIS].
  destruct msF as [rg fr pcv svc rv fc mm rom].
  unfold cg_at_node, OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.Nodes.areg, restrict, restrict_by, with_mem in *.
  cbn in SV, A0, A1, ROM, WRF |- *. exact (conj SV (conj A0 (conj A1 (conj ROM WRF)))).
Qed.

(* [comment removed for export] *)
Theorem sreach_cg_lazy : forall L S Zr msF1 mo ms (ts : Z) (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF1 mo) ->
  restrict L S msF1 = ms ->
  cg_at_node segs (CGRealtime ts) ms ->
  (forall bs msF' mo', realtime_ok_b bs = true -> length bs = 16%nat ->
      lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
      restrict L S msF' = sysret ms (Z_to_bv 64 0) (write_to_mem (ms_mem ms) (Z_to_bv 64 ts) bs) ->
      hid_same L S msF1 msF' ->
      sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF1 mo).
Proof.
  intros L S Zr msF1 mo ms ts Q Hok Hr AT Hk.
  pose proof (lzok_ranges Hok) as HL.
  rewrite <- Hr in AT. destruct (cg_at_node_restrictL L S msF1 ts HL AT) as [ATF VIS16].
  pose proof ATF as (SV & A0 & A1 & ROM & WR). destruct WR as (T0 & T16 & _).
  destruct (cg_input segs ts msF1 (Z_to_bv 64 113) mo ATF SV) as (NO & _ & _ & _ & SP).
  assert (Emem : restrict_mem L S (ms_mem msF1) = ms_mem ms) by (rewrite <- Hr; symmetry; apply ms_mem_restrict).
  set (eff := fun bs : list byte => mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 ts, bs)] []).
  assert (VISb : forall bs : list byte, length bs = 16%nat -> range_visible (hiddenb L S) (Z_to_bv 64 ts) (length bs)).
  { intros bs Lb i Hi. rewrite Lb in Hi. rewrite wa_add_nat. rewrite u64_lit by lia. apply VIS16. lia. }
  assert (ACC : forall bs, syscall_effect_accesses (eff bs) = [(Z_to_bv 64 ts, length bs)]).
  { intros bs. reflexivity. }
  assert (RV : forall bs, length bs = 16%nat -> ranges_visible (hiddenb L S) (syscall_effect_accesses (eff bs))).
  { intros bs Lb. rewrite ACC. intros a n Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. exact (VISb bs Lb). }
  assert (HID : forall bs, length bs = 16%nat -> forall a, hiddenb L S a = true -> ms_mem (apply_effect msF1 (eff bs)) a = ms_mem msF1 a).
  { intros bs Lb a Ha. unfold eff. rewrite apply_effect_write1_mem.
    apply (write_to_mem_hidden (hiddenb L S)); [exact (VISb bs Lb) | exact Ha]. }
  assert (AFTER : forall bs, realtime_ok_b bs = true ->
    exists mo', materialize_model_accesses mo (syscall_effect_accesses (eff bs)) = Some mo'
      /\ same_but_materialized mo mo'
      /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 (eff bs))) mo')
      /\ hid_same L S msF1 (advance_past_svc (apply_effect msF1 (eff bs)))).
  { intros bs Hbs. pose proof (realtime_ok_length bs Hbs) as Lb.
    exact (lzok_after_fd_op segs L S Zr msF1 mo mo (eff bs) Hok eq_refl (lzok_halted Hok) (RV bs Lb) (HID bs Lb)). }
  set (I := { bs : list byte | realtime_ok_b bs = true }).
  set (MAT := fun i : I => match materialize_model_accesses mo (syscall_effect_accesses (eff (proj1_sig i))) with Some m => m | None => mo end).
  assert (NODE : node_ok segs (mkCfg msF1 mo) I (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect msF1 (eff (proj1_sig i)))) (MAT i))).
  { apply (node_family_mat segs msF1 mo (Z_to_bv 64 113) I (fun i => eff (proj1_sig i)) (fun _ => mo) MAT (fun _ => [])
             (fun o => exists bs, realtime_ok_b bs = true /\ o = Ok (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 ts, bs)] []) mo [])
             (lzok_halted Hok) SV SP).
    - intros [bs Hbs]. exists bs. split; [exact Hbs| reflexivity].
    - intros [bs Hbs]. apply cg_not_spurious. exact NO.
    - intros o (bs & Hbs & ->). exists (exist _ bs Hbs). reflexivity.
    - intros _. exact (lzok_halted Hok).
    - intros [bs Hbs]. unfold MAT. cbn [proj1_sig]. destruct (AFTER bs Hbs) as (mo' & E & _). rewrite E. reflexivity. }
  apply (sreach_node segs (mkCfg msF1 mo) I _ (exist _ (repeat (Z_to_bv 8 0) 16) realtime_ok_zeros) Q NODE).
  intros [bs Hbs]. cbn [proj1_sig].
  destruct (AFTER bs Hbs) as (mo' & E & SBM & OK' & HS).
  unfold MAT. cbn [proj1_sig]. rewrite E.
  apply (Hk bs _ mo' Hbs (realtime_ok_length bs Hbs) OK' SBM); [| exact HS].
  rewrite (restrict_sysret L S L S msF1 (eff bs)), Hr. unfold eff. cbn [eff_ret].
  rewrite apply_effect_write1_mem. f_equal.
  unfold restrict_mem in Emem |- *.
  rewrite <- (write_to_mem_restrict (hiddenb L S) bs (ms_mem msF1) (Z_to_bv 64 ts) (VISb bs (realtime_ok_length bs Hbs))).
  rewrite Emem. reflexivity.
Qed.
End WithSegs.
