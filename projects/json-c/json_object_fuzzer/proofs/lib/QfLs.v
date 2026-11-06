(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE QbVh QWxq_c1 QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QZDE QbVh QWxq_c1.
Import QCcH.
Import ListNotations.
Open Scope Z_scope.

Definition pe_arg_ok (segs : list Segment) (m : word -> option byte) (LBc : list blk) (SP sb len lenr : Z)
(payload slack : list byte) : Prop :=
(lenr = len /\ (len = 0 \/ SP <= sb \/ exists b, In b LBc /\ blk_addr b <= sb /\ sb + len <= blk_addr b + blk_size b))
\/ (lenr = 2^64 - 1 /\ SP <= sb /\ (exists str0, payload = str0 ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str0)
/\ bytes_at segs m (sb + len) slack /\ (- (sb + len)) mod 8 <= Z.of_nat (length slack)).

Lemma pe_arg_ok_explicit : forall segs m LBc SP sb len payload,
(len = 0 \/ In (sb, len) LBc) -> pe_arg_ok segs m LBc SP sb len len payload [].
Proof.
intros segs m LBc SP sb len payload [L0 | IN]; left; (split; [reflexivity|]); [left; exact L0 | right; right].
exists (sb, len). cbn. split; [exact IN | lia].
Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Facts.
Variable L : heap_layout.
Notation segs := (hl_segs L).

Definition client_range (LB : list blk) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (forall a, A <= a < A + n -> hl_client_static L a)
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

#[using="Type"] Lemma client_range_addr : forall LB SP A n a,
client_range LB SP A n -> A <= a < A + n -> client_addr L LB SP a.
Proof.
intros LB SP A n a HR Ha. unfold client_range, client_addr, in_block in *.
destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; apply H; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

#[using="Type"] Lemma client_range_block : forall LB SP A n a k,
In (a, k) LB -> a <= A -> A + n <= a + k -> client_range LB SP A n.
Proof. intros. right; right. exists (a, k). cbn. auto. Qed.

#[using="Type"] Lemma client_range_above : forall LB SP A n, SP <= A -> client_range LB SP A n.
Proof. intros. left. assumption. Qed.

#[using="Type"] Lemma heap_pres_refl : forall LB SP m, heap_pres L LB SP m m.
Proof. intros LB SP m a _ _. auto. Qed.

#[using="Type"] Lemma heap_pres_trans : forall LB SP m1 m2 m3,
heap_pres L LB SP m1 m2 -> heap_pres L LB SP m2 m3 -> heap_pres L LB SP m1 m3.
Proof.
intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
split; [congruence| auto].
Qed.

#[using="Type"] Lemma heap_pres_weaken : forall LB LB' SP SP' m m',
heap_pres L LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> heap_pres L LB' SP' m m'.
Proof.
intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
unfold client_addr, in_block in *.
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

#[using="Type"] Lemma heap_pres_bytes_at : forall LB SP m m' A bs,
heap_pres L LB SP m m' -> bytes_at segs m A bs -> client_range LB SP A (Z.of_nat (length bs)) ->
bytes_at segs m' A bs.
Proof.
intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply client_range_addr; [exact HR|lia])) as [E _].
rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma heap_pres_wr_at : forall LB SP m m' A n,
heap_pres L LB SP m m' -> wr_at segs m A n -> client_range LB SP A n -> wr_at segs m' A n.
Proof.
intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply client_range_addr; [exact HR|lia])) as [_ W].
apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma heap_pres_rw_cells : forall LB SP m m' A cs,
heap_pres L LB SP m m' -> rw_cells segs m A cs -> client_range LB SP A (Z.of_nat (cells_size cs)) ->
rw_cells segs m' A cs.
Proof.
intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply heap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply heap_pres_wr_at; eauto.
Qed.

#[using="Type"] Lemma heap_pres_u8arr : forall LB SP m m' A xs,
heap_pres L LB SP m m' -> u8arr segs m A xs -> client_range LB SP A (Z.of_nat (length xs)) ->
u8arr segs m' A xs.
Proof.
intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells segs m' A (length xs)).
eapply heap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

#[using="Type"] Lemma heap_pres_stk : forall LB SP m m' lo hi,
heap_pres L LB SP m m' -> stk segs m lo hi -> SP <= lo -> stk segs m' lo hi.
Proof.
intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Definition client_addrx (X : Z -> Prop) (LB : list blk) (SP : Z) (a : Z) : Prop :=
SP <= a \/ (hl_client_static L a /\ ~ X a) \/ in_block LB a.

#[using="Type"] Lemma client_addrx_addr : forall X LB SP a, client_addrx X LB SP a -> client_addr L LB SP a.
Proof. intros X LB SP a [H|[[H _]|H]]; [left | right; left | right; right]; exact H. Qed.

Definition heap_presx (X : Z -> Prop) (LB : list blk) (SP : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> client_addrx X LB SP a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Definition client_rangex (X : Z -> Prop) (LB : list blk) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (forall a, A <= a < A + n -> hl_client_static L a /\ ~ X a)
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

#[using="Type"] Lemma client_rangex_addr : forall X LB SP A n a,
client_rangex X LB SP A n -> A <= a < A + n -> client_addrx X LB SP a.
Proof.
intros X LB SP A n a HR Ha. unfold client_rangex, client_addrx, in_block in *.
destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; apply H; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

#[using="Type"] Lemma client_rangex_block : forall X LB SP A n a k,
In (a, k) LB -> a <= A -> A + n <= a + k -> client_rangex X LB SP A n.
Proof. intros. right; right. exists (a, k). cbn. auto. Qed.

#[using="Type"] Lemma client_rangex_above : forall X LB SP A n, SP <= A -> client_rangex X LB SP A n.
Proof. intros. left. assumption. Qed.

#[using="Type"] Lemma heap_pres_presx : forall X LB SP m m', heap_pres L LB SP m m' -> heap_presx X LB SP m m'.
Proof. intros X LB SP m m' H a Ha Hc. apply H; [exact Ha | exact (client_addrx_addr _ _ _ _ Hc)]. Qed.

#[using="Type"] Lemma heap_presx_refl : forall X LB SP m, heap_presx X LB SP m m.
Proof. intros X LB SP m a _ _. auto. Qed.

#[using="Type"] Lemma heap_presx_trans : forall X LB SP m1 m2 m3,
heap_presx X LB SP m1 m2 -> heap_presx X LB SP m2 m3 -> heap_presx X LB SP m1 m3.
Proof.
intros X LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
split; [congruence| auto].
Qed.

#[using="Type"] Lemma heap_presx_weaken : forall X X' LB LB' SP SP' m m',
heap_presx X LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, X a -> X' a) -> heap_presx X' LB' SP' m m'.
Proof.
intros X X' LB LB' SP SP' m m' H HS HL HX a Ha Hc. apply H; [exact Ha|].
unfold client_addrx, in_block in *.
destruct Hc as [Hc|[[Hc Hx]|(b & Hb & Hr)]]; [left; lia| right; left; split; [exact Hc | intros Xa; exact (Hx (HX _ Xa))] | right; right].
exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

#[using="Type"] Lemma heap_presx_bytes_at : forall X LB SP m m' A bs,
heap_presx X LB SP m m' -> bytes_at segs m A bs -> client_rangex X LB SP A (Z.of_nat (length bs)) ->
bytes_at segs m' A bs.
Proof.
intros X LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply client_rangex_addr; [exact HR|lia])) as [E _].
rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma heap_presx_wr_at : forall X LB SP m m' A n,
heap_presx X LB SP m m' -> wr_at segs m A n -> client_rangex X LB SP A n -> wr_at segs m' A n.
Proof.
intros X LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply client_rangex_addr; [exact HR|lia])) as [_ W].
apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma heap_presx_rw_cells : forall X LB SP m m' A cs,
heap_presx X LB SP m m' -> rw_cells segs m A cs -> client_rangex X LB SP A (Z.of_nat (cells_size cs)) ->
rw_cells segs m' A cs.
Proof.
intros X LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply heap_presx_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply heap_presx_wr_at; eauto.
Qed.

#[using="Type"] Lemma heap_presx_stk : forall X LB SP m m' lo hi,
heap_presx X LB SP m m' -> stk segs m lo hi -> SP <= lo -> stk segs m' lo hi.
Proof.
intros X LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

#[using="Type"] Lemma lb_remove_head : forall p n LB, lb_remove p ((p, n) :: LB) = LB.
Proof. intros. cbn. rewrite Z.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma lb_remove_other : forall p b LB, blk_addr b <> p -> lb_remove p (b :: LB) = b :: lb_remove p LB.
Proof. intros p [a n] LB H. cbn in *. destruct (Z.eqb_spec a p); [congruence| reflexivity]. Qed.

#[using="Type"] Lemma in_lb_remove : forall p b LB, In b (lb_remove p LB) -> In b LB.
Proof.
intros p b LB. induction LB as [|[a n] LB IH]; cbn; [tauto|].
destruct (Z.eqb a p); cbn; intuition.
Qed.

End Facts.

Section Facts2.
Variable L : heap_layout.
Notation segs := (hl_segs L).

#[using="Type"] Lemma heap_pres_of_munch : forall LB SP W m m',
munch W m m' -> wmono segs m m' ->
(forall a, 0 <= a < 2^64 -> client_addr L LB SP a -> outside W a) ->
heap_pres L LB SP m m'.
Proof.
intros LB SP W m m' MU WM HW a Ha Hc. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
- apply WM.
Qed.

#[using="Type"] Lemma heap_presx_of_munch : forall X LB SP W m m',
munch W m m' -> wmono segs m m' ->
(forall a, 0 <= a < 2^64 -> client_addr L LB SP a -> outside W a) ->
heap_presx L X LB SP m m'.
Proof.
intros X LB SP W m m' MU WM HW a Ha Hc. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; [assumption | exact (client_addrx_addr L _ _ _ _ Hc)].
- apply WM.
Qed.
End Facts2.

End RC__1.
