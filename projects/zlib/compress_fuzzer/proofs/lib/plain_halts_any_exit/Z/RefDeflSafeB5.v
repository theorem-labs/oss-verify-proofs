(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record bt_pre (s : deflate_state) (t : tree_id) : Prop := {
  bp_tl : tree_lens s;
  bp_fc : forall i, 0 <= arr_get (tree_fc s t) i < 65536;
  bp_dl : forall i, 0 <= arr_get (tree_dl s t) i < 65536;
  bp_depth : forall i, 0 <= arr_get (ds_depth s) i < 256;
  bp_ol : 0 <= ds_opt_len s < 2 ^ 64;
  bp_sl : 0 <= ds_static_len s < 2 ^ 64 }.

Lemma gen_codes_typed : forall f s0 t a nc mc n,
  arr_len a = tsize t -> (forall i, 0 <= arr_get a i < 65536) ->
  exists a', gen_codes_loop2 f (set_tree_fc s0 t a) t nc mc n = set_tree_fc s0 t a'
             /\ arr_len a' = tsize t /\ (forall i, 0 <= arr_get a' i < 65536).
Proof.
  induction f as [|f IH]; intros s0 t a nc mc n Ha Ra.
  - exists a. split; [reflexivity|]. split; [exact Ha | exact Ra].
  - rewrite loop2_S. destruct (n <=? mc); [| exists a; split; [reflexivity|]; split; [exact Ha | exact Ra]]. cbv zeta.
    destruct (Len s0 t n =? 0); [apply IH; assumption|].
    apply IH; [rewrite arr_len_set; exact Ha|].
    intros i. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply Ra].
Qed.

Section BT.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Hypothesis HP : bt_pre s t.

Let TL : tree_lens s := bp_tl _ _ HP.
Let LFC : arr_len (tree_fc s t) = tsize t := tree_lens_fc s t TL.
Let LDL : arr_len (tree_dl s t) = tsize t := tree_lens_dl s t TL.
Lemma LHP : arr_len (ds_heap s) = 573. Proof. pose proof TL as X. unfold tree_lens in X. tauto. Qed.
Lemma LDP : arr_len (ds_depth s) = 573. Proof. pose proof TL as X. unfold tree_lens in X. tauto. Qed.
Lemma LBC : arr_len (ds_bl_count s) = 16. Proof. pose proof TL as X. unfold tree_lens in X. tauto. Qed.

Lemma heap_phase_s :
  let FC := tree_fc s t in
  let s0 := set_heap_max (set_heap_len s 0) HEAP_SIZE in
  let '(s1, mc1) := build_tree_loop1 (Z.to_nat E) s0 t E 0 (-1) in
  let '(s2, mc) := build_tree_loop2 2%nat s1 t mc1 in
  let s3 := set_max_code s2 t mc in
  let s4 := build_tree_loop3 (Z.to_nat (ds_heap_len s3 / 2)) s3 t (ds_heap_len s3 / 2) in
  let s5 := build_tree_loop4 573%nat s4 t E in
  let s6 := set_heap_max s5 (ds_heap_max s5 - 1) in
  let s7 := heap_set s6 (ds_heap_max s6) (heap_get s6 SMALLEST) in
  exists Fl DL2 HP2 DP2 L FCf DLf HPf DPf,
    let FC2 := fc_forced Fl FC in
    s3 = bt_upd s t FC2 DL2 HP2 L 573 DP2 (ds_bl_count s) (ol_forced Fl (ds_opt_len s)) (sl_forced t Fl (ds_static_len s)) mc
    /\ s7 = bt_upd s t FCf DLf HPf 1 (574 - 2 * L) DPf (ds_bl_count s) (ol_forced Fl (ds_opt_len s)) (sl_forced t Fl (ds_static_len s)) mc
    /\ heap_result t FC2 DL2 L mc FCf DLf HPf DPf
    /\ zone_ok HP2 L 573 (Vscan FC2 E) /\ arr_len HP2 = 573 /\ arr_len DP2 = 573 /\ arr_len DL2 = tsize t
    /\ (forall i, 0 <= arr_get DP2 i < 256) /\ (forall i, 0 <= arr_get FC2 i < 65536) /\ (forall i, 0 <= arr_get DL2 i < 65536)
    /\ (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f < E /\ arr_get FC f = 0 /\ f <= 2)
    /\ (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get FC i)
    /\ (forall i, arr_get DL2 i = if (0 <=? i) && (i <? E) && (arr_get FC i =? 0) then 0 else arr_get (tree_dl s t) i).
Proof.
  pose proof (heap_phase s t (tree_fc s t) (tree_dl s t) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_bl_count s)
                (ds_opt_len s) (ds_static_len s) (max_code s t) LFC LDL LHP LDP (bp_fc _ _ HP) (bp_dl _ _ HP) (bp_depth _ _ HP)) as H.
  rewrite bt_upd_self in H. exact H.
Qed.

Lemma let_pair_elim : forall {A B : Type} (X : A * B) (P : A -> B -> Prop),
  (let '(a, b) := X in P a b) -> P (fst X) (snd X).
Proof. intros A B X P. destruct X; exact (fun h => h). Qed.
Lemma let_pair_intro : forall {A B : Type} (X : A * B) (P : A -> B -> Prop),
  P (fst X) (snd X) -> (let '(a, b) := X in P a b).
Proof. intros A B X P. destruct X; exact (fun h => h). Qed.

Lemma DLI_leaf_len : forall FC2 DL2 L mc FCf DLf HPf DPf DL' i,
  heap_result t FC2 DL2 L mc FCf DLf HPf DPf -> DLI t FC2 L HPf DL' -> 0 <= i < E ->
  0 <= arr_get DL' i <= ML.
Proof.
  intros FC2 DL2 L mc FCf DLf HPf DPf DL' i HR HD Hi. pose proof (ML_range t _ _ _ _ _ _ _ _ HR).
  destruct (Z.eq_dec (arr_get FC2 i) 0) as [Z0|NZ].
  - rewrite (dli_zero _ _ _ _ _ HD i Hi Z0). lia.
  - destruct (hr_cov _ _ _ _ _ _ _ _ _ HR i ltac:(unfold Vj, V0, Vscan; left; lia)) as (p & Hp & Ep).
    pose proof (hr_L _ _ _ _ _ _ _ _ _ HR).
    assert (Np : p <> 574 - 2 * L) by (intros ->; rewrite (hr_root _ _ _ _ _ _ _ _ _ HR) in Ep; lia).
    pose proof (dli_leaf _ _ _ _ _ HD p ltac:(unfold RefDeflSafeB3.HM; lia) ltac:(unfold RefDeflSafeB3.leafb, RefDeflSafeB3.nd; apply Z.ltb_lt; rewrite Ep; lia)) as X.
    unfold RefDeflSafeB3.nd in X. rewrite Ep in X. lia.
Qed.

Theorem bt_safe_intro : bt_safe s t.
Proof.
  pose proof (elems_range t) as RE. pose proof LBC as LBC'.
  unfold bt_safe.
  split; [intros i _; apply (bp_fc _ _ HP)|]. split; [apply (bp_ol _ _ HP)|]. split; [apply (bp_sl _ _ HP)|].
  pose proof heap_phase_s as H. cbv zeta in H.
  apply let_pair_elim in H. apply let_pair_elim in H.
  apply let_pair_intro. apply let_pair_intro.
  destruct H as (Fl & DL2 & HP2 & DP2 & L & FCf & DLf & HPf & DPf & E3 & E7 & HR & Z2 & LHP2 & LDP2 & LDL2 & RDP2 & RFC2 & RDL2 & LF & ND & FF & FCE & DLE).
  rewrite E7. rewrite E3. autorewrite with btupd.
  pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML.
  split.
  { intros i Hi. unfold heap_get. rewrite bt_heap. pose proof (zone_ok_mem _ _ _ _ i Z2 ltac:(left; lia)) as M. unfold Vscan in M. lia. }
  split.
  { intros i Hi. unfold depth_get. rewrite bt_depth. apply RDP2. }
  split.
  { intros i Hi. rewrite bt_Freq. apply RFC2. }
  split.
  { intros h Hh. unfold heap_get. rewrite bt_heap. unfold HEAP_SIZE in Hh.
    pose proof (hr_tail _ _ _ _ _ _ _ _ _ HR h ltac:(lia)) as M. unfold Vj, V0, Vscan in M. lia. }
  split.
  { intros i Hi. apply (hr_dlr _ _ _ _ _ _ _ _ _ HR). }
  assert (ROL : 0 <= ol_forced Fl (ds_opt_len s) < 2 ^ 64).
  { unfold ol_forced. destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_ol _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  assert (RSL : 0 <= sl_forced t Fl (ds_static_len s) < 2 ^ 64).
  { unfold sl_forced. destruct (stree_has t); [| apply (bp_sl _ _ HP)].
    destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_sl _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  destruct (gen_bitlen_run t _ _ _ _ _ _ _ _ HR s (ds_bl_count s) (ol_forced Fl (ds_opt_len s)) (sl_forced t Fl (ds_static_len s)) LBC' ROL RSL)
    as ((DL' & BC' & OL' & SL' & EG & HD & RO & RS & LB) & G1 & G23).
  change (RefDeflSafeB3.HM L) with (574 - 2 * L) in EG, G1, G23.
  autorewrite with btupd in G1. autorewrite with btupd in G23. autorewrite with btupd.
  split; [| split; [exact G23 |]].
  - exact G1.
  - intros i Hi. rewrite EG. unfold Len. rewrite bt_tree_dl.
    pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR).
    pose proof (DLI_leaf_len _ _ _ _ _ _ _ _ DL' i HR HD ltac:(lia)). lia.
Qed.
End BT.
