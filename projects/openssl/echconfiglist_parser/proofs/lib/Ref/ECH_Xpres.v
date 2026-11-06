(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc MallocCtrl Monad Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition xclient (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop :=
  rclient_addr LB SP a /\ ~ rin_ivs X a.

Definition xpres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> xclient LB SP X a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma xpres_refl : forall LB SP X m, xpres LB SP X m m.
Proof. intros LB SP X m a _ _. auto. Qed.

Lemma xpres_trans : forall LB SP X m1 m2 m3, xpres LB SP X m1 m2 -> xpres LB SP X m2 m3 -> xpres LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma xpres_weaken : forall LB LB' SP SP' X X' m m',
  xpres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
  xpres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX a Ha [Hc Hx]. apply H; [exact Ha|]. split; [| intros K; apply Hx, HX, K].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma xpres_of_heap_pres : forall LB SP X m m', rheap_pres LB SP m m' -> xpres LB SP X m m'.
Proof. intros LB SP X m m' H a Ha [Hc _]. apply H; assumption. Qed.

Lemma rin_ivs_app : forall X1 X2 a, rin_ivs (X1 ++ X2) a <-> rin_ivs X1 a \/ rin_ivs X2 a.
Proof. induction X1 as [|iv X1 IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Lemma xpres_of_munch : forall LB SP X W m m',
  munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv : Z * Z => (hceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
  (forall b, In b LB -> blk_addr b + blk_size b <= hceil) ->
  xpres LB SP X m m'.
Proof.
  intros LB SP X W m m' MU WM FW HB a Ha [Hc Hx].
  assert (OUT : outside W a).
  { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as H1. cbn in H1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct H1 as [[H1 H2]|H1].
    - destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [lia| hcb; lia|]. pose proof (HB b Hb). lia.
    - intros R. apply Hx. apply H1. exact R. }
  split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
  - intros Hw. apply WM. exact Hw.
Qed.

(* [comment removed for export] *)
Definition xclient_range (LB : list block) (SP : Z) (X : list (Z * Z)) (A n : Z) : Prop :=
  rclient_range LB SP A n /\ Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X.

Lemma xclient_range_addr : forall LB SP X A n a, xclient_range LB SP X A n -> A <= a < A + n -> xclient LB SP X a.
Proof.
  intros LB SP X A n a [HR HX] Ha. split; [eapply rclient_range_addr; eauto|].
  induction X as [|iv X IH]; cbn; [tauto|]. pose proof (Forall_inv HX) as H1. cbn in H1. pose proof (Forall_inv_tail HX) as H2.
  intros [K|K]; [lia| exact (IH H2 K)].
Qed.

Lemma xpres_bytes_at : forall LB SP X m m' A bs,
  xpres LB SP X m m' -> bytes_at rsegs m A bs -> xclient_range LB SP X A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
  intros LB SP X m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma xpres_wr_at : forall LB SP X m m' A n,
  xpres LB SP X m m' -> wr_at rsegs m A n -> xclient_range LB SP X A n -> wr_at rsegs m' A n.
Proof.
  intros LB SP X m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma xpres_rw_cells : forall LB SP X m m' A cs,
  xpres LB SP X m m' -> rw_cells rsegs m A cs -> xclient_range LB SP X A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
  intros LB SP X m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply xpres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply xpres_wr_at; eauto.
Qed.

Lemma xpres_stk : forall LB SP X m m' lo hi,
  xpres LB SP X m m' -> stk rsegs m lo hi -> SP <= lo -> Forall (fun iv : Z * Z => hi <= fst iv \/ snd iv <= lo) X ->
  stk rsegs m' lo hi.
Proof.
  intros LB SP X m m' lo hi HP ST HS HX. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi.
  assert (XC : xclient LB SP X i).
  { split; [left; lia|]. clear HP HW. induction X as [|iv X IH]; cbn; [tauto|].
    pose proof (Forall_inv HX) as K1. cbn in K1. pose proof (Forall_inv_tail HX) as K2. intros [K|K]; [lia| exact (IH K2 K)]. }
  destruct (HP i ltac:(lia) XC) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma disjoint_from_mono : forall W a n n', disjoint_from W a n -> n' <= n -> disjoint_from W a n'.
Proof. induction W as [|[lo hi] W IH]; cbn; intros a n n' H Hn; [exact I|]. destruct H as [H1 H2]. split; [lia| eauto]. Qed.

End HCW.
