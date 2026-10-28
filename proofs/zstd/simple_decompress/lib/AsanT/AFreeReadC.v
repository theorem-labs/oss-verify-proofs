(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes AQConst ARep ARepQ ARepQP ARepFrame ARepKit ALayout AHeapP
     AModelFacts AFreeModel AFreeRep AFreeGeo F_afree_tail F_afree_icpt.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AFreeRead F_afreeC_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section VariantC.
Variables (H : aholes) (L : alayout) (st : astate) (X : aconc) (Q : qconc) (m : amem) (RNG : footprint)
          (s0 : bstate) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Hypothesis ALO : alayout_ok L.
Hypothesis ARNG : arng L RNG st.
Hypothesis AR : AREP H L st X m.
Hypothesis AQ : AQUAR_at L st X Q m.
Hypothesis XB : x_busy X = l1 ++ bany s0 c k n b1 ctx :: l2.
Hypothesis NBT : s0 <> BBatch.
Hypothesis N1 : 1 <= n.

Lemma WF : awf L st X. Proof. exact (proj1 AR). Qed.
Lemma CP : qcoupled L st X Q. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 AQ))))). Qed.
Lemma HCKR : 1 <= c < K_NUM_CLASSES /\ 0 <= k < ndist st c. Proof. exact (AFreeRead.HCKR H L st X m s0 c k n b1 ctx l1 l2 AR XB). Qed.
Lemma other_key : forall y, In y (x_busy X) -> xb_st y <> s0 -> c <> xb_class y \/ k <> xb_slot y.
Proof. exact (AFreeRead.other_key H L st X m s0 c k n b1 ctx l1 l2 AR XB). Qed.
Lemma freed_vs_slot24 : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> c <> K_BATCH_CLASS \/ k <> kk ->
  fhm L c k n + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= fhm L c k n.
Proof. exact (AFreeRead.freed_vs_slot24 H L st X m s0 c k n b1 ctx l1 l2 ALO AR XB NBT). Qed.
Lemma qfirst_cases : forall qs, qfirst L qs = 0 \/ (exists q, In q qs /\ qfirst L qs = abatch_addr L (qb_slot q)). Proof. exact (AFreeRead.qfirst_cases L). Qed.
Lemma qlast_cases : forall qs, qlast L qs = 0 \/ (exists q, In q qs /\ qlast L qs = abatch_addr L (qb_slot q)). Proof. exact (AFreeRead.qlast_cases L). Qed.

Lemma read_dkC : forall (eb delta : Z) (ek : enq_kind),
  0 <= delta -> delta <= Q_MAX + 8192 ->
  (eb = qlast L (q_loc Q) \/ exists kk, eb = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))) ->
  Q_CACHE < a_qloc_bytes st + delta -> Q_MAX < a_qglob_bytes st + (a_qloc_bytes st + delta) ->
  ek_b ek (qlast L (q_loc Q)) = eb ->
  let g := g_of L st Q delta in
     dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + delta) m
  /\ dk_seps g L (fhm L c k n)
  /\ g_lst g = qlast L (q_glob Q) /\ dk_glst g (qlast L (q_loc Q)) = qlast L (q_glob Q) /\ g_drain g = true.
Proof.
  intros eb delta ek D0 DMAX EB REC1 REC2 EKB g. subst g. unfold g_of. cbv beta iota zeta delta [dk_preC dk_seps g_drain g_full g_nb g_fst g_lst g_qb g_nx dk_glst].
  destruct HCKR as [HC KR]. pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GC ABG] & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  apply Forall_app in NF. destruct NF as [NFl NFg].
  pose proof (batches_bytes_lb _ NFg) as GLB0. rewrite <- NB2 in GLB0.
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1 & _). atop_facts. lia. }
  assert (GF64 : 0 <= qfirst L (q_glob Q) < 2^64).
  { destruct (qfirst_cases (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  assert (GL64 : 0 <= qlast L (q_glob Q) < 2^64).
  { destruct (qlast_cases (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (GFULL : a_qglob st <> [] ->
      0 < Z.of_nat (length (a_qglob st))
   /\ rw_cells bsegs m (qlast L (q_glob Q)) [C8 (Z_to_bv 64 0)]
   /\ 0x10007fff8000 <= qlast L (q_glob Q) /\ qlast L (q_glob Q) + 8192 <= ATOP
   /\ (al_t L + 4096 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_t L)
   /\ (fhm L c k n + 24 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= fhm L c k n)
   /\ (qlast L (q_loc Q) + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= qlast L (q_loc Q))
   /\ (eb + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= eb)
   /\ (al_nodes L + 1048576 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_nodes L)
   /\ (al_store L + 8388608 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_store L)
   /\ rng RNG (qlast L (q_glob Q)) 8192).
  { intros GNE.
    assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
    assert (LQ : (0 < length (q_glob Q))%nat) by (rewrite LN2; destruct (a_qglob st); [congruence| cbn; lia]).
    assert (QQ : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_glob Q); [cbn in LQ; lia| discriminate]. }
    set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
    set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
    assert (LNg : length qg = length lg) by (rewrite QQ, QG, !length_app in LN2; cbn in LN2; lia).
    unfold abatches in ABG. rewrite QG, QQ in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [_ ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & _) _].
    assert (QLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQ; apply qlast_app1). rewrite QLST.
    assert (INz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WF CP qgz INz) as KZ.
    pose proof (bslot_geo L st X ALO WF (qb_slot qgz) KZ) as (B0 & B1 & BAL & BT & BN & BSR & BR).
    destruct (bslot_busy L st X Q CP qgz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (freed_vs_slot24 (qb_slot qgz) KZ ltac:(rewrite <- Cyz, <- Kyz; apply other_key; [exact Hyz| rewrite Syz; intros EE; exact (NBT (eq_sym EE))])) as DH.
    (* [comment removed for export] *)
    assert (DL : qlast L (q_loc Q) + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= qlast L (q_loc Q)).
    { destruct (qlast_cases (q_loc Q)) as [E0 |(q & Hq & Eq)]; [rewrite E0; left; lia| rewrite Eq].
      assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
      pose proof (bslot_range L st X Q WF CP q INq) as KQ.
      assert (NEq : qb_slot q <> qb_slot qgz).
      { apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ qg) qgz []). rewrite EQl, QQ. rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
      pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q) (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    assert (DE : eb + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= eb).
    { destruct EB as [-> |(kk & -> & KK & NIK)]; [exact DL|].
      assert (NEq : kk <> qb_slot qgz) by (intros ->; apply NIK; apply in_map; exact INz).
      pose proof (slots_disjoint L K_BATCH_CLASS kk (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    split; [rewrite QG, length_app; cbn; lia|].
    split; [pose proof Z1 as Z1'; rw_split Z1' 1%nat ZN ZR; exact ZN|].
    split; [exact B0|]. split; [exact B1|]. split; [exact BT|]. split; [exact DH|]. split; [exact DL|]. split; [exact DE|].
    split; [exact BN|]. split; [exact BSR|]. apply BR. exact ARNG. }
  (* [comment removed for export] *)
  unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES in *.
  assert (GDT : (1048576 <? a_qloc_bytes st + delta) = true) by (apply Z.ltb_lt; exact REC1).
  rewrite GDT.
  split; [| split; [| split; [reflexivity| split; reflexivity]]].
  - split; [reflexivity|]. split; [exact MX|]. split; [exact GC|].
    split; [lia|]. split; [lia|]. split; [exact GF64|]. split; [exact GL64|].
    split; [exact REC1|]. split; [exact REC2|]. split; [lia|].
    destruct (a_qglob st) as [|bg lg0] eqn:QG0.
    + split; [reflexivity|]. assert (QQ0 : q_glob Q = []) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). rewrite QQ0. reflexivity.
    + rewrite <- QG0 in *. destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      rewrite EKB. unfold fhm in *.
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [generalize F6; clear; intros; lia|].
      split; [exact F7|]. split; [exact F8|]. exact F11.
  - intros _ FU. destruct (a_qglob st) as [|bg lg0] eqn:QG0; [discriminate|]. rewrite <- QG0 in *.
    destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    unfold fhm in *. split; [generalize F6; clear; intros; lia|]. split; [exact F9| exact F10].
Qed.
End VariantC.
End CANSEC1.
