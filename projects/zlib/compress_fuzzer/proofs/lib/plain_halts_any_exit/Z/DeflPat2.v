(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeLF RefDeflSafeI1 BoundFw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record PATG2 (s : deflate_state) : Prop := {
  pg2_mode : dmode s = 0 \/ dmode s = 3 \/ dmode s = 4;
  pg2_strat : ds_strategy s = 0 \/ ds_strategy s = 1;
  pg2_wrap : ds_wrap s = 1 \/ (ds_wrap s = -1 /\ ds_status s = FINISH_STATE);
  pg2_st : ds_status s = INIT_STATE \/ ds_status s = BUSY_STATE \/ ds_status s = FINISH_STATE }.

Lemma CF4_proj : forall a b, CF4 b = CF4 a ->
  ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_wrap b = ds_wrap a /\ ds_status b = ds_status a.
Proof. intros a b E. unfold CF4 in E. injection E as E1 E2 E3 E4. auto. Qed.

Lemma CF4_dmode : forall a b, CF4 b = CF4 a -> dmode b = dmode a.
Proof. intros a b E. destruct (CF4_proj a b E) as (E1 & E2 & _). unfold dmode. rewrite E1, E2. reflexivity. Qed.

Lemma CF_CF4 : forall a b, CF b = CF a -> CF4 b = CF4 a.
Proof. intros a b E. destruct (CF_fields a b E) as (E1 & E2 & E3 & E4 & _). unfold CF4. rewrite E1, E2, E3, E4. reflexivity. Qed.

Lemma PATG2_CF4 : forall a b, CF4 b = CF4 a -> PATG2 a -> PATG2 b.
Proof.
  intros a b E [P1 P2 P3 P4]. destruct (CF4_proj a b E) as (E1 & E2 & E3 & E4).
  constructor; rewrite ?(CF4_dmode a b E), ?E2, ?E3, ?E4; assumption.
Qed.

Lemma PATG2_CF : forall a b, CF b = CF a -> PATG2 a -> PATG2 b.
Proof. intros a b E P. exact (PATG2_CF4 a b (CF_CF4 a b E) P). Qed.

Lemma PATG2_slf : forall s v, PATG2 s -> PATG2 (set_last_flush s v).
Proof. intros s v [P1 P2 P3 P4]. constructor; assumption. Qed.
Lemma PATG2_set_strm : forall s c, PATG2 s -> PATG2 (set_strm s c).
Proof. intros s c [P1 P2 P3 P4]. constructor; assumption. Qed.
Lemma PATG2_err : forall s e, PATG2 s -> PATG2 (fst (err_return s e)).
Proof. intros s e P. rewrite err_return_fst. apply PATG2_set_strm. exact P. Qed.
Lemma PATG2_busy : forall s, PATG2 s -> ds_status s = INIT_STATE -> PATG2 (set_status s BUSY_STATE).
Proof.
  intros s [P1 P2 P3 P4] E.
  assert (W : ds_wrap s = 1) by (destruct P3 as [W|[_ F]]; [exact W | rewrite E in F; discriminate F]).
  constructor; try assumption. - left. exact W. - right. left. reflexivity.
Qed.
Lemma PATG2_finish : forall s, PATG2 s -> ds_status s <> FINISH_STATE -> PATG2 (set_status s FINISH_STATE).
Proof.
  intros s [P1 P2 P3 P4] N.
  assert (W : ds_wrap s = 1) by (destruct P3 as [W|[_ F]]; [exact W | contradiction]).
  constructor; try assumption. - left. exact W. - right. right. reflexivity.
Qed.
Lemma PATG2_wrapneg : forall s, PATG2 s -> ds_status s = FINISH_STATE -> PATG2 (set_wrap s (-1)).
Proof. intros s [P1 P2 P3 P4] F. constructor; try assumption. right. split; [reflexivity | exact F]. Qed.

Lemma PATG2_PF : forall a b, PF b = PF a -> PATG2 a -> PATG2 b.
Proof.
  intros a b E P.
  pose proof (PF_fields _ _ E) as ((_ & _ & _ & _ & El & Es) & (_ & _ & _ & _ & _ & _ & _ & Ew) & (Est & _) & _).
  apply (PATG2_CF4 a b); [| exact P]. unfold CF4. rewrite El, Es, Ew, Est. reflexivity.
Qed.

Lemma PATG2_cases : forall s, dwf s -> PATG2 s ->
  (dmode s = 0 /\ ds_level s = 0) \/ (dmode s = 3 /\ 1 <= ds_level s <= 3) \/ (dmode s = 4 /\ 4 <= ds_level s <= 9).
Proof.
  intros s D P. pose proof (df_level _ D) as L. destruct (pg2_mode _ P) as [M|[M|M]]; pose proof M as M'; unfold dmode in M.
  - destruct (Z.eqb_spec (ds_level s) 0) as [E|E]; [left; split; [exact M'| exact E]|].
    exfalso. destruct (ds_strategy s =? Z_HUFFMAN_ONLY); [discriminate M|]. destruct (ds_strategy s =? Z_RLE); [discriminate M|].
    destruct (ds_level s <=? 3); discriminate M.
  - destruct (Z.eqb_spec (ds_level s) 0) as [E|E]; [discriminate M|].
    destruct (ds_strategy s =? Z_HUFFMAN_ONLY); [discriminate M|]. destruct (ds_strategy s =? Z_RLE); [discriminate M|].
    destruct (Z.leb_spec (ds_level s) 3) as [E3|E3]; [| discriminate M]. right. left. split; [exact M'| lia].
  - destruct (Z.eqb_spec (ds_level s) 0) as [E|E]; [discriminate M|].
    destruct (ds_strategy s =? Z_HUFFMAN_ONLY); [discriminate M|]. destruct (ds_strategy s =? Z_RLE); [discriminate M|].
    destruct (Z.leb_spec (ds_level s) 3) as [E3|E3]; [discriminate M|]. right. right. split; [exact M'| lia].
Qed.

Lemma PATG2_level : forall s, dwf s -> PATG2 s -> 0 <= ds_level s <= 9.
Proof. intros s D _. exact (df_level _ D). Qed.

Lemma PATG2_strategy : forall s, PATG2 s -> 0 <= ds_strategy s <= 1.
Proof. intros s P. destruct (pg2_strat _ P) as [E|E]; rewrite E; lia. Qed.

Lemma PATG2_wrap2 : forall s, PATG2 s -> ds_wrap s <> 2.
Proof. intros s P. destruct (pg2_wrap _ P) as [W|[W _]]; rewrite W; discriminate. Qed.
