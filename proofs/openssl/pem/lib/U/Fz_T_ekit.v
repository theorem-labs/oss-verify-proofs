(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Tactic Notation "tcalle" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut;
      [ eapply SPEC; th_strip_ulit; try eassumption
      | let ms' := fresh "ms'" in let PO := fresh "POST" in
        intros ms' PO; hnf in PO; th_strip_ulit_in PO; revert ms' PO; post_call segs m ]
  end.

(* [comment removed for export] *)
Tactic Notation "tcallr" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut;
      [ eapply SPEC; th_strip_ulit; try first [eassumption | reflexivity]
      | let ms' := fresh "ms'" in let PO := fresh "POST" in
        intros ms' PO; hnf in PO; th_strip_ulit_in PO; revert ms' PO; post_call segs m ]
  end.

(* [comment removed for export] *)
Ltac cst_static CFR H Hn :=
  assert (Hn := cfr_cells_static _ _ _ _ _ _ _ _ CFR H);
  cbn [cells_size csize Nat.add] in Hn;
  specialize (Hn ltac:(lia) ltac:(lia));
  specialize (Hn ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS;
                        cbn [rin_ivs fst snd]; lia)).

(* [comment removed for export] *)
Lemma t_le_bytes_app : forall n k z, Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z.
  - cbn [Nat.add Z_to_le_bytes app]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. rewrite IH. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. f_equal. lia.
Qed.
Lemma t_le8_of_halves : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> le8 (Z_to_bv 64 (a + 2 ^ 32 * b)) = le4 (Z_to_bv 64 a) ++ le4 (Z_to_bv 64 b).
Proof.
  intros a b Ha Hb. rewrite <- store_bytes_8'. unfold le4. rewrite !unsigned_lit by lia.
  change 8%nat with (4 + 4)%nat. rewrite t_le_bytes_app. change (8 * Z.of_nat 4) with 32. rewrite Z.shiftr_div_pow2 by lia. f_equal.
  - rewrite <- (Z_to_le_bytes_mod 4 (a + 2 ^ 32 * b) 32) by (cbn; lia). f_equal. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - f_equal. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma t_cells_halves : forall segs m A a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  rw_cells segs m A [C4 (Z_to_bv 64 a); C4 (Z_to_bv 64 b)] <-> rw_cells segs m A [C8 (Z_to_bv 64 (a + 2 ^ 32 * b))].
Proof.
  intros segs m A a b Ha Hb. split; intros H.
  - apply (th_cells_congr segs m A _ [C8 (Z_to_bv 64 (a + 2 ^ 32 * b))]) in H; [exact H| | reflexivity | cbn; tauto].
    cbn [cells_bytes cbytes app]. rewrite t_le8_of_halves by lia. rewrite <- app_assoc. reflexivity.
  - apply (th_cells_congr segs m A _ [C4 (Z_to_bv 64 a); C4 (Z_to_bv 64 b)]) in H; [exact H| | reflexivity | cbn; tauto].
    cbn [cells_bytes cbytes app]. rewrite t_le8_of_halves by lia. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma t_nodup_prefix : forall {A B : Type} (g : A -> B) (pre l : list A) (b : A), List.NoDup (map g (pre ++ l)) -> In b pre -> ~ In (g b) (map g l).
Proof.
  intros A B g pre l b. induction pre as [|x pre IH]; intros ND Hb; [destruct Hb|].
  cbn [app map] in ND. inversion ND as [|hd tl NI ND']; subst. destruct Hb as [->|Hb]; [| exact (IH ND' Hb)].
  intros X. apply NI. rewrite map_app. apply in_or_app. right. exact X.
Qed.
Lemma t_fresh_notin : forall (T : bptr -> Prop) (LB0 : list block) (b : block), ~ In (blk_id b) (map blk_id LB0) ->
  forall b0, In b0 LB0 -> ~ T (blk_id b0) -> blk_id b0 <> blk_id b.
Proof. intros T LB0 b NI b0 H0 _ E. apply NI. rewrite <- E. apply in_map. exact H0. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma cstate_apart : forall s LBall LB L m sp tp lo B p A n q A' n',
  cstate s LBall LB L m sp tp lo B -> In (p, A, n) LBall -> In (q, A', n') LBall -> p <> q -> A + n <= A' \/ A' + n' <= A.
Proof.
  intros s LBall LB L m sp tp lo B p A n q A' n' (HP & _) H1 H2 NE.
  pose proof (RHEAP_blocks_disjoint_proof _ _ _ (p, A, n) (q, A', n') HP H1 H2) as D.
  unfold blk_id, blk_addr, blk_size in D. cbn [fst snd] in D. exact (D NE).
Qed.

(* [comment removed for export] *)
Lemma cstate_head_fresh : forall s p A n LBall LB L m sp tp lo B q A' n',
  cstate s ((p, A, n) :: LBall) LB L m sp tp lo B -> In (q, A', n') LBall -> q <> p.
Proof.
  intros s p A n LBall LB L m sp tp lo B q A' n' CST H E. destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [ND _].
  cbn [map] in ND. inversion ND as [|hd tl NI _]; subst. apply NI. change (blk_id (p, A, n)) with p.
  change p with (blk_id (p, A', n')). apply in_map. exact H.
Qed.

(* [comment removed for export] *)
Lemma cpost_rebase_gen : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s sc : PState) (LBall LB LBc : list block) (L Lc : @clist bptr) (f fc' : nat) (m mc : mem) (lo B : Z) T W T' W' EV EV' da db dbig da' db' dbig' R f' L' s' ms',
  cframe T W (bv_unsigned sp) s LBall L m sc LBc Lc mc ->
  (forall a, rin_ivs W' a -> rin_ivs W a) -> (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ T q -> ~ T' q) ->
  (f - EV <= fc')%nat -> cgrow L Lc da db dbig ->
  cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sc LBc LB Lc fc' mc lo B T' W' EV' da' db' dbig' R f' L' s' ms' ->
  cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B T W (EV + EV') (da + da') (db + db') (dbig + dbig') R f' L' s' ms'.
Proof.
  intros until ms'. intros FR0 HW HT HF GR0 (v & m2 & LB1 & RET & FU & GR & CST1 & FRM1 & RES).
  exists v, m2, LB1. split; [exact RET|]. split; [lia|]. split; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR0 GR)|]. split; [exact CST1|]. split; [| exact RES].
  eapply cframe_call; [exact FR0| exact FRM1| lia| exact HW| exact HT].
Qed.
End WithCeiling0.
