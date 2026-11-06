(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section WithSegs.
Variable segs : list Segment.
Notation rw_cells := (rw_cells segs).
Notation u8arr := (u8arr segs).
Notation bytes_at := (bytes_at segs).
Notation wr_at := (wr_at segs).

(* [comment removed for export] *)

Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at m a (n1 + n2) <-> wr_at m a n1 /\ wr_at m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold Mem.wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma u8arr_app : forall m A l1 l2,
  u8arr m A (l1 ++ l2) <-> u8arr m A l1 /\ u8arr m (A + Z.of_nat (length l1)) l2.
Proof.
  intros m A l1 l2. unfold Arr.u8arr. rewrite length_app, Nat2Z.inj_add.
  rewrite bytes_at_app. rewrite wr_at_app by lia. tauto.
Qed.

(* [comment removed for export] *)
Lemma u8arr_of_CB2 : forall m A n1 b1 n2 b2,
  rw_cells m A [CB n1 b1; CB n2 b2] -> u8arr m A (b1 ++ b2) /\ length b1 = n1 /\ length b2 = n2.
Proof.
  intros m A n1 b1 n2 b2 [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  split; [| auto]. split; [exact Hb|]. rewrite length_app, L1, L2. exact Hw.
Qed.

Lemma CB2_of_u8arr : forall m A b1 b2 n1 n2,
  u8arr m A (b1 ++ b2) -> length b1 = n1 -> length b2 = n2 -> rw_cells m A [CB n1 b1; CB n2 b2].
Proof.
  intros m A b1 b2 n1 n2 [Hb Hw] L1 L2. split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, <- L1, <- L2, <- length_app. exact Hw.
Qed.

Lemma u8arr_of_CB : forall m A n b, rw_cells m A [CB n b] -> u8arr m A b /\ length b = n.
Proof.
  intros m A n b H. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [L _].
  split; [eapply u8arr_of_rw_cells; exact H| exact L].
Qed.

Lemma CB_of_u8arr : forall m A b n, u8arr m A b -> length b = n -> rw_cells m A [CB n b].
Proof. intros m A b n H <-. apply rw_cells_of_u8arr. exact H. Qed.

(* [comment removed for export] *)
Lemma u8arr_of_CB3 : forall m A n1 b1 c n2 b2,
  rw_cells m A [CB n1 b1; C1 c; CB n2 b2] -> u8arr m A (b1 ++ [c] ++ b2) /\ length b1 = n1 /\ length b2 = n2.
Proof.
  intros m A n1 b1 c n2 b2 [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as (L1 & _ & L2 & _).
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  split; [| auto]. split.
  - revert Hb. cbn [app]. intros Hb. exact Hb.
  - rewrite !length_app, L1, L2. cbn [length]. exact Hw.
Qed.

Lemma CB3_of_u8arr : forall m A b1 c b2 n1 n2,
  u8arr m A (b1 ++ [c] ++ b2) -> length b1 = n1 -> length b2 = n2 -> rw_cells m A [CB n1 b1; C1 c; CB n2 b2].
Proof.
  intros m A b1 c b2 n1 n2 [Hb Hw] L1 L2. split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. revert Hb. cbn [app]. intros Hb. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, <- L1, <- L2.
    revert Hw. rewrite !length_app. cbn [length]. intros Hw. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma upd_app_last : forall {X} (l1 : list X) (x y : X) (l2 : list X),
  upd (l1 ++ x :: l2) (length l1) y = l1 ++ y :: l2.
Proof. intros X l1. induction l1 as [|z l1 IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma upd_app_len : forall {X} (l1 : list X) (x y : X) (l2 : list X) n,
  n = length l1 -> upd (l1 ++ x :: l2) n y = l1 ++ y :: l2.
Proof. intros X l1 x y l2 n ->. apply upd_app_last. Qed.

(* [comment removed for export] *)
Lemma u8arr_store_ok_at : forall m A bs (i : Z),
  u8arr m A bs -> 0 <= i < Z.of_nat (length bs) -> store_ok segs m (wa (A + i)) 1 = true.
Proof. intros. eapply u8arr_store_ok; eauto. Qed.

End WithSegs.

(* [comment removed for export] *)
Definition yhide (P : Prop) : Prop := P.
End RC__1.
Ltac yhide H := lazymatch type of H with ?P => change P with (yhide P) in H end.
Ltac yshow H := unfold yhide in H.
Ltac yreveal H MU WM :=
  unfold yhide in H;
  lazymatch type of H with
  | rw_cells ?segs _ _ _ =>
      eapply (rw_cells_transport segs) in H; [ | exact MU | exact WM | cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; try lia ]
  | Arr.u8arr ?segs _ _ _ =>
      eapply (u8arr_transport segs) in H; [ | exact MU | exact WM | cbv [disjoint_from fst snd]; try lia ]
  | bytes_at ?segs _ _ _ =>
      eapply (bytes_at_transport segs) in H; [ | exact MU | cbv [disjoint_from fst snd]; try lia ]
  | stk ?segs _ _ _ =>
      eapply (stk_transport_disjoint segs) in H; [ | exact MU | exact WM | cbv [disjoint_from fst snd]; try lia ]
  end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma le1_wz : forall c, (0 <= c < 2^64)%Z -> le1 (wz c) = [Z_to_bv 8 c].
Proof. intros c Hc. unfold le1, wz. rewrite unsigned_lit by lia. reflexivity. Qed.
End RC__2.
