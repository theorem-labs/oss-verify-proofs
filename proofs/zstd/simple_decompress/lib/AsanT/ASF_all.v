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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP
     ASec AFreeModel AFreeModelR AFreeRep AFreeRead ARefill_iface ARefillP F_afree_arep
     ASF_kit ASF_fast ASF_store ASF_refill ASF_mid ASF_storeR ASF_big.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6443008 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6443008 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xcc970 \/ 0xcca30 <= fst iv)
                                  /\ (snd iv <= 0xd0f00 \/ 0x151f30 <= fst iv)
                                  /\ (snd iv <= 0x15f788 \/ 0x15f78c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Lemma REFILLS : forall cs Q1, refill_stmt (AHSm DI AFK cs Q1).
Proof. intros cs Q1. exact (arefillP (AHSm DI AFK cs Q1) (AHSm_laws DI AFK HL cs Q1)). Qed.

Definition afree_sec_refillP :=
  afree_sec_refill DI AFK HL CI CI_OK CI_OK2 (mid_kitS DI AFK HL CI CI_OK) (store_freeRS DI AFK HL CI CI_OK) REFILLS.

(* [comment removed for export] *)
Theorem afree_sec_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply (afree_sec_fastP DI AFK HL CI CI_OK); try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply (afree_sec_fastP DI AFK HL CI CI_OK); try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
        destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
      eapply afree_sec_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as (_ & G1 & G2 & _ & _ & L2 & _).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.

(* [comment removed for export] *)
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Theorem afree_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (n <= Q_MAX -> Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE st1 st2 NOREC. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - eapply afree_sec_norecycle; try eassumption. exact (NOREC LE).
  - eapply (afree_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.
End S.
End CANSEC1.
