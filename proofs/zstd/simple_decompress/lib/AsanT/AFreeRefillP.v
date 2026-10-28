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
     AFreeModel AFreeModelR AFreeRep AFreeRead ARefill_iface ARefillP F_afree_arep AFreeStore F_afree_arepR AFreeMid AFreeStoreR.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xcc970 \/ 0xcca30 <= fst iv)
                                  /\ (snd iv <= 0xd0f00 \/ 0x151f30 <= fst iv)
                                  /\ (snd iv <= 0x15f788 \/ 0x15f78c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Lemma REFILL : forall Q1, refill_stmt (AHQm DI ASEC AFK Q1).
Proof. intros Q1. exact (arefillP (AHQm DI ASEC AFK Q1) (AHQm_laws DI ASEC AFK HL Q1)). Qed.

Definition afree_refillP :=
  afree_refill DI ASEC AFK HL CI CI_OK CI_OK2 (mid_kit DI ASEC AFK HL CI CI_OK) (store_freeR DI ASEC AFK HL CI CI_OK) REFILL.

Theorem afree_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until c. intros LIVE N1 st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply (afree_fastP DI ASEC AFK HL CI CI_OK); try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply (afree_fastP DI ASEC AFK HL CI CI_OK); try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
      change (enq_app st1 (CPrim c n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
        destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
      eapply afree_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CPrim c n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CPrim c n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      pose proof (enq_new_core (CPrim c n) (set_live (delete p (a_live st)) st)) as (_ & G1 & G2 & _ & _ & L2 & _).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.
End S.
End CANSEC1.
