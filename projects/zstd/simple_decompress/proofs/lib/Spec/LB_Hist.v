(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad MSafe Malloc KStep MI_Inv MI_Cnt PState Prog
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_PCaps.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bc (n : Z) : Z := if n =? 24 then 1 else n / 4 - 1.
Definition BC (Y : list (bptr * Z)) : Z := zsum (map (fun b => bc (snd b)) Y).
Definition YW (Y : list (bptr * Z)) : Prop := Forall (fun b => snd b = 24 \/ exists l, 0 <= l /\ snd b = 4 * (l + 1)) Y.
Definition N24 (Y : list (bptr * Z)) : Z := zcount (fun b => snd b =? 24) Y.
Definition N4 (Y : list (bptr * Z)) : Z := zcount (fun b => snd b =? 4) Y.

Lemma BC_cons p n Y : BC ((p, n) :: Y) = bc n + BC Y. Proof. reflexivity. Qed.
Lemma BC_app Y1 Y2 : BC (Y1 ++ Y2) = BC Y1 + BC Y2. Proof. unfold BC. rewrite map_app, zsum_app. reflexivity. Qed.
Lemma N24_cons p n Y : N24 ((p, n) :: Y) = (if n =? 24 then 1 else 0) + N24 Y. Proof. unfold N24. rewrite zcount_cons. reflexivity. Qed.
Lemma N4_cons p n Y : N4 ((p, n) :: Y) = (if n =? 4 then 1 else 0) + N4 Y. Proof. unfold N4. rewrite zcount_cons. reflexivity. Qed.
Lemma N24_app Y1 Y2 : N24 (Y1 ++ Y2) = N24 Y1 + N24 Y2. Proof. unfold N24. apply zcount_app. Qed.
Lemma N4_app Y1 Y2 : N4 (Y1 ++ Y2) = N4 Y1 + N4 Y2. Proof. unfold N4. apply zcount_app. Qed.
Lemma LRX_cons p n X c : LRX ((p, n) :: X) c = (if negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c) then 1 else 0) + LRX X c.
Proof. unfold LRX. rewrite zcount_cons. reflexivity. Qed.
Lemma LRX_app X1 X2 c : LRX (X1 ++ X2) c = LRX X1 c + LRX X2 c. Proof. unfold LRX. apply zcount_app. Qed.
Lemma n63X_cons p n X : n63X ((p, n) :: X) = (if MMAP_THRESHOLD <=? n then 1 else 0) + n63X X.
Proof. unfold n63X. rewrite zcount_cons. reflexivity. Qed.
Lemma n63X_app X1 X2 : n63X (X1 ++ X2) = n63X X1 + n63X X2. Proof. unfold n63X. apply zcount_app. Qed.
Lemma R63X_app X1 X2 : R63X (X1 ++ X2) = R63X X1 + R63X X2. Proof. unfold R63X. rewrite map_app, zsum_app. reflexivity. Qed.
Lemma LRX_nonneg X c : 0 <= LRX X c. Proof. unfold LRX. apply zcount_nonneg. Qed.
Lemma n63X_nonneg X : 0 <= n63X X. Proof. unfold n63X. apply zcount_nonneg. Qed.
Lemma N24_nonneg Y : 0 <= N24 Y. Proof. unfold N24. apply zcount_nonneg. Qed.
Lemma N4_nonneg Y : 0 <= N4 Y. Proof. unfold N4. apply zcount_nonneg. Qed.

Lemma bc_kv l : 0 <= l -> bc (4 * (l + 1)) = (if l =? 5 then 1 else l).
Proof.
  intros Hl. unfold bc. destruct (Z.eqb_spec (4 * (l + 1)) 24); destruct (Z.eqb_spec l 5); lia.
Qed.

Lemma bigb_kv_le l : 0 <= l -> bigb (4 * (l + 1)) <= 5 * (if l =? 5 then 1 else l).
Proof.
  intros Hl. unfold bigb, MMAP_THRESHOLD, IB, UNIT. destruct (Z.leb_spec 131052 (4 * (l + 1))); [|destruct (l =? 5); lia].
  destruct (Z.eqb_spec l 5); [lia|]. rewrite round_up_pg_eq. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (4 * (l + 1) + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (4 * (l + 1) + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
Lemma hist_Y : forall Y, YW Y ->
  0 <= BC Y /\ N24 Y <= BC Y
  /\ LRX Y 0 <= N4 Y + BC Y
  /\ LRX Y 1 <= BC Y
  /\ (forall c, 2 <= c < 48 -> LRX Y c * lmin c <= BC Y)
  /\ n63X Y * 32762 <= BC Y
  /\ R63X Y <= 5 * BC Y.
Proof.
  induction Y as [|[p n] Y IH]; intros HW.
  - unfold BC, N24, N4, LRX, n63X, R63X, zcount, zlen. cbn. splits; intros; lia.
  - apply Forall_cons_iff in HW as [Hn HW]. cbn [snd] in Hn. specialize (IH HW). destruct IH as (I0 & I1 & I2 & I3 & I4 & I5 & I6).
    rewrite BC_cons, N24_cons, N4_cons, !LRX_cons, n63X_cons, R63X_cons.
    destruct Hn as [-> | (l & Hl & ->)].
    + (* [comment removed for export] *) change (bc 24) with 1. change (size_to_class 24) with 1. change (MMAP_THRESHOLD <=? 24) with false.
      change (24 =? 24) with true. change (24 =? 4) with false. change (bigb 24) with 0. change (1 =? 0) with false. change (1 =? 1) with true. cbn [negb andb].
      splits; try lia. intros c Hc. rewrite LRX_cons. change (size_to_class 24) with 1. change (MMAP_THRESHOLD <=? 24) with false. cbn [negb andb].
      replace (1 =? c) with false by (symmetry; apply Z.eqb_neq; lia). specialize (I4 c Hc). lia.
    + rewrite bc_kv by lia. pose proof (bigb_kv_le l Hl) as HB.
      replace (4 * (l + 1) =? 24) with (l =? 5) by (destruct (Z.eqb_spec l 5); destruct (Z.eqb_spec (4*(l+1)) 24); try reflexivity; lia).
      replace (4 * (l + 1) =? 4) with (l =? 0) by (destruct (Z.eqb_spec l 0); destruct (Z.eqb_spec (4*(l+1)) 4); try reflexivity; lia).
      destruct (Z.leb_spec MMAP_THRESHOLD (4 * (l + 1))) as [Hbig|Hsmall]; cbn [negb andb].
      * (* [comment removed for export] *) unfold MMAP_THRESHOLD in Hbig. destruct (Z.eqb_spec l 5); [lia|]. destruct (Z.eqb_spec l 0); [lia|].
        splits; try lia. intros c Hc. rewrite LRX_cons. replace (MMAP_THRESHOLD <=? 4 * (l + 1)) with true by (symmetry; apply Z.leb_le; unfold MMAP_THRESHOLD; lia). cbn [negb andb]. specialize (I4 c Hc). pose proof (lmin_pos c ltac:(lia)). nia.
      * pose proof (kv_class_len l Hl Hsmall) as [Rc Lc]. set (c0 := size_to_class (4 * (l + 1))) in *.
        replace (MMAP_THRESHOLD <=? 4 * (l + 1)) with false in * by (symmetry; apply Z.leb_gt; lia).
        assert (U : 4 * (l + 1) + IB <= UNIT * size_class c0) by (pose proof (size_to_class_ok (4 * (l + 1)) ltac:(lia)) as [_ U]; exact U).
        assert (HBIG : bigb (4 * (l + 1)) = 0). { unfold bigb. replace (MMAP_THRESHOLD <=? 4 * (l + 1)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        rewrite HBIG.
        assert (GEN : forall c, 2 <= c < 48 -> LRX ((p, 4 * (l + 1)) :: Y) c * lmin c <= (if l =? 5 then 1 else l) + BC Y).
        { intros c Hc. rewrite LRX_cons. replace (MMAP_THRESHOLD <=? 4 * (l + 1)) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb andb]. fold c0.
          specialize (I4 c Hc). pose proof (lmin_pos c ltac:(lia)). destruct (Z.eqb_spec c0 c) as [<-|NE]; [|destruct (l =? 5); lia].
          destruct (Z.eqb_spec l 5) as [->|N5]; [exfalso; subst c0; change (size_to_class (4 * (5 + 1))) with 1 in Hc; lia| nia]. }
        destruct (Z.eqb_spec l 5) as [E5|N5].
        -- (* [comment removed for export] *) assert (E1 : c0 = 1) by (subst l c0; reflexivity). rewrite E1 in *.
           change (1 =? 0) with false. change (1 =? 1) with true. subst l. change (5 =? 5) with true in *. change (5 =? 0) with false. cbn [negb andb]. splits; try lia. exact GEN.
        -- replace (l =? 5) with false in * by (symmetry; apply Z.eqb_neq; lia).
           destruct (Z.eqb_spec l 0) as [E0|N0].
           ++ (* [comment removed for export] *) assert (Ec : c0 = 0) by (subst l c0; reflexivity). rewrite Ec in *. subst l.
              change (0 =? 0) with true in *. change (0 =? 1) with false. cbn [negb andb]. splits; try lia. exact GEN.
           ++ assert (B1 : (c0 =? 1) = true -> 3 <= l).
              { intros E. apply Z.eqb_eq in E. rewrite E in Lc. change (lmin 1) with 3 in Lc. exact Lc. }
              replace (l =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. splits; try lia.
              ** destruct (c0 =? 0); lia.
              ** destruct (c0 =? 1) eqn:E1; [specialize (B1 eq_refl)|]; lia.
              ** exact GEN.
Qed.

(* [comment removed for export] *)
Definition AMBZ (Z0 : list (bptr * Z)) : Prop := (length Z0 <= 3)%nat /\ Forall (fun b => 0 <= snd b <= 2^26 + 64) Z0.

Lemma amb_counts : forall Z0, AMBZ Z0 -> (forall c, LRX Z0 c <= 3) /\ n63X Z0 <= 3 /\ R63X Z0 <= 3 * (2^26 + 8192).
Proof.
  intros Z0 [Hl HF]. 
  assert (G : forall Z1, Forall (fun b => 0 <= snd b <= 2^26 + 64) Z1 -> (forall c, LRX Z1 c <= Z.of_nat (length Z1)) /\ n63X Z1 <= Z.of_nat (length Z1) /\ R63X Z1 <= Z.of_nat (length Z1) * (2^26 + 8192)).
  { induction Z1 as [|[p n] Z1 IH]; intros HF1.
    - unfold LRX, n63X, R63X, zcount, zlen. cbn. splits; intros; lia.
    - apply Forall_cons_iff in HF1 as [Hn HF1]. cbn [snd] in Hn. destruct (IH HF1) as (A1 & A2 & A3). cbn [length]. rewrite Nat2Z.inj_succ.
      splits.
      + intros c. rewrite LRX_cons. specialize (A1 c). destruct (_ && _); lia.
      + rewrite n63X_cons. destruct (_ <=? _); lia.
      + rewrite R63X_cons. assert (bigb n <= 2^26 + 8192); [|lia]. unfold bigb. destruct (_ <=? _); [|lia].
        rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
        pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia. }
  destruct (G Z0 HF) as (A1 & A2 & A3). splits; [intros c; specialize (A1 c); lia| lia| nia].
Qed.

Lemma AMBZ_cons p n Z0 : AMBZ Z0 -> (length Z0 <= 2)%nat -> 0 <= n <= 2^26 + 64 -> AMBZ ((p, n) :: Z0).
Proof. intros [Hl HF] Hl2 Hn. split; [cbn; lia| constructor; [exact Hn| exact HF]]. Qed.
Lemma AMBZ_nil : AMBZ []. Proof. split; [cbn; lia| constructor]. Qed.

