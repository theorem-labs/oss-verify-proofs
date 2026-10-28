(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatCellEx_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_vis (H : word -> bool) (a n : Z) : Prop := forall x : word, a <= U x < a + n -> H x = false.

Lemma art_vis_sub : forall H a n a' n', art_vis H a n -> a <= a' -> a' + n' <= a + n -> art_vis H a' n'.
Proof. intros H a n a' n' V L1 L2 x Hx. apply V. lia. Qed.

Lemma art_vis_avoids : forall H a (n : nat), 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> art_vis H a (Z.of_nat n) -> range_avoids H (Z_to_bv 64 a) n.
Proof.
  intros H a n Ha Hn V k Hk. apply V. unfold woff. rewrite (art_u_lit a) by lia. rewrite art_u_lit by lia. lia.
Qed.

Lemma art_cell_vis : forall H (M : word -> option byte) a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> art_vis H a (Z.of_nat n) ->
  (cellA (mrestrict H M) a n v <-> cellA M a n v).
Proof.
  intros H M a n v Ha Hn V. unfold cell. rewrite (rdn_mrestrict_eq ASEGS H n M (Z_to_bv 64 a) (art_vis_avoids H a n Ha Hn V)). tauto.
Qed.

Lemma art_byte_vis : forall H (M : word -> option byte) (x : word), H x = false -> mrestrict H M x = M x.
Proof. intros H M x E. unfold mrestrict. rewrite E. reflexivity. Qed.

Lemma art_wr_vis : forall H (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 -> art_vis H a n -> (wrA (mrestrict H M) a n <-> wrA M a n).
Proof.
  intros H M a n Ha Hn V. split; intros W; apply art_wr_of_wview; try lia; intros x Hx.
  - rewrite <- (wview_mrestrict_eq ASEGS H M x (V x Hx)). apply (art_wr_wview ASEGS _ a n Ha Hn W x Hx).
  - rewrite (wview_mrestrict_eq ASEGS H M x (V x Hx)). apply (art_wr_wview ASEGS _ a n Ha Hn W x Hx).
Qed.

(* [comment removed for export] *)
Lemma art_vis_of_wr : forall H (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 -> (a + n <= 0x10000 \/ 0x696000 <= a) ->
  wrA (mrestrict H M) a n -> art_vis H a n.
Proof.
  intros H M a n Ha Hn Off W x Hx. pose proof (art_wr_wview ASEGS _ a n Ha Hn W x Hx) as D.
  rewrite art_wview_off in D by lia. unfold mrestrict in D. destruct (H x); [exfalso; apply D; reflexivity|reflexivity].
Qed.

(* [comment removed for export] *)
Section Lift.
Context {fx : PropExec.FPState}.
Variables (A0 A1 : list (Z * Z)) (M0 M1 : word -> option byte) (model0 model1 : Model) (log0 log1 : list aev).
Let H0 := bhid A0 model0.
Let H1 := bhid A1 model1.
Hypothesis BH : bhist A0 M0 model0 log0 log1 A1 M1 model1.

#[using="M0 M1 log0 log1 BH"] Lemma art_lift_vis : forall a n, art_vis H0 a n -> art_vis H1 a n.
Proof.
  intros a n V x Hx. destruct BH as (sfx & _ & _ & B2 & _). destruct (H1 x) eqn:E; [|reflexivity].
  destruct (B2 x E) as [E0 _]. fold H0 in E0. rewrite (V x Hx) in E0. discriminate E0.
Qed.

#[using="BH"] Lemma art_lift_frame : forall (FP : Z -> Prop),
  (forall x : word, ~ FP (U x) -> mrestrict H1 M1 x = mrestrict H0 M0 x) ->
  (forall sfx, log1 = log0 ++ sfx -> forall z, in_ev_ranges sfx z -> FP z) ->
  forall x : word, ~ FP (U x) -> M1 x = M0 x.
Proof.
  intros FP FR EVR x N. destruct BH as (sfx & El & _ & B2 & B3 & _).
  destruct (H1 x) eqn:E1.
  - exact (proj2 (B2 x E1)).
  - destruct (H0 x) eqn:E0.
    + exfalso. apply N. apply (EVR sfx El). apply B3; assumption.
    + pose proof (FR x N) as F. unfold mrestrict in F. fold H1 H0 in F. rewrite E1, E0 in F. exact F.
Qed.
End Lift.
