(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition qslot (gs : gif_st) (k : nat) : option frame :=
match k with 0%nat => s_q0 gs | 1%nat => s_q1 gs | _ => s_q2 gs end.
Lemma qslot_get : forall gs k, (k < 3)%nat -> q_get gs (Z.of_nat k) = qslot gs k.
Proof. intros gs [|[|[|k]]] Hk; cbn; try reflexivity. lia. Qed.
Lemma qslot_set : forall gs i o k, (k < 3)%nat -> (i < 3)%nat ->
qslot (q_set gs (Z.of_nat i) o) k = if (k =? i)%nat then o else qslot gs k.
Proof. intros gs [|[|[|i]]] o [|[|[|k]]] Hk Hi; cbn; try reflexivity; lia. Qed.
Lemma qslot_with_cur : forall gs c k, qslot (with_cur gs c) k = qslot gs k.
Proof. intros gs c [|[|k]]; reflexivity. Qed.
Lemma qslot_mkS : forall a b c ih cu rc ou k, qslot (mkS a b c ih cu rc ou) k = match k with 0%nat => a | 1%nat => b | _ => c end.
Proof. intros a b c ih cu rc ou [|[|k]]; reflexivity. Qed.
Lemma q_set_fields : forall gs i o, s_cur (q_set gs i o) = s_cur gs /\ s_rcur (q_set gs i o) = s_rcur gs /\ s_out (q_set gs i o) = s_out gs /\ s_ihead (q_set gs i o) = s_ihead gs.
Proof. intros gs i o. unfold q_set. destruct (i =? 0); [| destruct (i =? 1)]; cbn; repeat split; reflexivity. Qed.
Section AF.
Variables (g : gcfg) (attr gen delay ctrans nlp : Z) (lpal img : list Z).
Definition af_hasAlpha : bool := flag (g_attr g) 8 || flag attr 2.
Definition af_hasSet : bool := flag attr 4.
Definition af_err : bool := (af_hasAlpha && af_hasSet) || (flag (g_attr g) 8 && flag attr 2) || (negb (flag attr 1) && flag (g_attr g) 4).
Definition af_nf : frame := new_frame g attr gen delay ctrans nlp lpal img.
Definition af_same (hd : frame) : bool :=
if negb (flag attr 1) && negb (flag (f_attr hd) 1) && negb (flag attr 4) && negb (flag (f_attr hd) 4)
then list_eqb img (f_img hd)
else forallb (fun pq => negb (cmp_pixel g af_nf hd (fst pq) (snd pq))) (combine img (f_img hd)).
Definition af_merged (s : gif_st) : option gif_st :=
match q_get s (s_ihead s) with
| Some hd =>
let fd := delay + f_delay hd in
if (fd <=? 65535) && negb (flag (g_gen g) 1) then if af_same hd then Some (q_set s (s_ihead s) (Some (set_delay hd fd))) else None else None
| None => None
end.
Definition af_i0 (s : gif_st) : Z :=
if match q_get s (s_ihead s) with None => true | Some _ => false end then s_ihead s
else if (s_ihead s <? 2) && match s_q2 s with None => true | Some _ => false end then 2 else 3.
Definition af_flushstep (s : gif_st) : gif_st * Z * bool :=
if af_i0 s =? 3 then
match s_q1 s with
| Some f1 =>
let '(r, bytes) := flush_frame g (s_rcur s) f1 (s_q0 s) in
let s' := mkS (s_q0 s) (s_q1 s) (s_q2 s) (s_ihead s) (s_cur s) (if negb (s_rcur s =? R_OK) && negb (s_rcur s =? R_PENDING) then s_rcur s else r) (if r =? C_OK then s_out s ++ [bytes] else s_out s) in
if r =? C_OK then (mkS (s_q1 s') (s_q2 s') None (s_ihead s') (s_cur s') (s_rcur s') (s_out s'), 2, false)
else (mkS None (s_q1 s') (s_q2 s') (s_ihead s') r (s_rcur s') (s_out s'), 2, true)
| None => (s, 2, false)
end
else (s, af_i0 s, false).
Definition af_tail (s1 : gif_st) (i : Z) : gif_st :=
let s2 := q_set s1 i (Some af_nf) in
let s3 := mkS (s_q0 s2) (s_q1 s2) (s_q2 s2) i (s_cur s2) (s_rcur s2) (s_out s2) in
let s4 := if flag (g_attr g) 8 then q_set s3 (i - 1) (omap (fun f => set_disp (set_gen f (clr (f_gen f) 3)) 8) (q_get s3 (i - 1))) else s3 in
let s5 := if flag attr 2 then q_set s4 (i - 1) (omap (fun f => set_disp (set_gen f (clr (f_gen f) 2)) 8) (q_get s4 (i - 1))) else s4 in
with_cur s5 C_OK.
Definition af_s3 (s1 : gif_st) (i : Z) : gif_st :=
let s2 := q_set s1 i (Some af_nf) in mkS (s_q0 s2) (s_q1 s2) (s_q2 s2) i (s_cur s2) (s_rcur s2) (s_out s2).
Definition af_s4 (s1 : gif_st) (i : Z) : gif_st :=
let s3 := af_s3 s1 i in
if flag (g_attr g) 8 then q_set s3 (i - 1) (omap (fun f => set_disp (set_gen f (clr (f_gen f) 3)) 8) (q_get s3 (i - 1))) else s3.
Definition af_s5 (s1 : gif_st) (i : Z) : gif_st :=
let s4 := af_s4 s1 i in
if flag attr 2 then q_set s4 (i - 1) (omap (fun f => set_disp (set_gen f (clr (f_gen f) 2)) 8) (q_get s4 (i - 1))) else s4.
Lemma af_tail_eq : forall s1 i, af_tail s1 i = with_cur (af_s5 s1 i) C_OK.
Proof. intros. reflexivity. Qed.
Definition af_rest (s : gif_st) : gif_st :=
let '(s1, i, failed) := af_flushstep s in if failed then s1 else af_tail s1 i.
Lemma af_rest_free : forall s, af_i0 s <> 3 -> af_rest s = af_tail s (af_i0 s).
Proof. intros s H. unfold af_rest, af_flushstep. destruct (Z.eqb_spec (af_i0 s) 3); [exfalso; exact (H ltac:(assumption)) | reflexivity]. Qed.
Lemma af_rest_full : forall s f1, af_i0 s = 3 -> s_q1 s = Some f1 ->
af_rest s = (let '(r, bytes) := flush_frame g (s_rcur s) f1 (s_q0 s) in
let rc' := if negb (s_rcur s =? R_OK) && negb (s_rcur s =? R_PENDING) then s_rcur s else r in
if r =? C_OK then af_tail (mkS (s_q1 s) (s_q2 s) None (s_ihead s) (s_cur s) rc' (s_out s ++ [bytes])) 2
else mkS None (s_q1 s) (s_q2 s) (s_ihead s) r rc' (s_out s)).
Proof.
intros s f1 H3 Hq1. unfold af_rest, af_flushstep. rewrite H3, Hq1. cbn [Z.eqb Pos.eqb].
destruct (flush_frame g (s_rcur s) f1 (s_q0 s)) as [r bytes]. destruct (r =? C_OK) eqn:E; cbn; rewrite ?E; reflexivity.
Qed.
Definition af_from_merge (s : gif_st) : gif_st :=
match af_merged s with Some s' => s' | None => af_rest s end.
Lemma af_tail_facts : forall s1 (i : nat), (i = 1%nat \/ i = 2%nat) ->
let sF := af_tail s1 (Z.of_nat i) in
s_cur sF = C_OK /\ s_rcur sF = s_rcur s1 /\ s_out sF = s_out s1 /\ s_ihead sF = Z.of_nat i /\
qslot sF i = Some af_nf /\
qslot sF (i - 1)%nat = (if flag attr 2 then omap (fun f => set_disp (set_gen f (clr (f_gen f) 2)) 8)
(if flag (g_attr g) 8 then omap (fun f => set_disp (set_gen f (clr (f_gen f) 3)) 8) (qslot s1 (i - 1)%nat) else qslot s1 (i - 1)%nat)
else (if flag (g_attr g) 8 then omap (fun f => set_disp (set_gen f (clr (f_gen f) 3)) 8) (qslot s1 (i - 1)%nat) else qslot s1 (i - 1)%nat)) /\
(forall k, (k < 3)%nat -> k <> i -> k <> (i - 1)%nat -> qslot sF k = qslot s1 k).
Proof.
intros s1 i Hi. destruct Hi as [-> | ->]; cbv zeta; unfold af_tail, with_cur, q_set, q_get; cbn;
destruct (flag (g_attr g) 8), (flag attr 2); cbn;
(repeat split; try reflexivity; intros [|[|[|k]]] Hk H1 H2; cbn; try reflexivity; lia).
Qed.
Lemma flush_frame_dead : forall rcur cur bef,
negb (rcur =? R_OK) && negb (rcur =? R_PENDING) = true -> flush_frame g rcur cur bef = (rcur, []).
Proof.
intros rcur cur bef H. unfold flush_frame. destruct bef as [b|].
- cbv zeta. match goal with |- context [match ?d with pair _ _ => _ end] => destruct d as [[[w h] t] l] end.
unfold raw_addframe. rewrite H. reflexivity.
- unfold raw_addframe. rewrite H. reflexivity.
Qed.
Lemma af_rcur_step : forall rcur cur bef,
(if negb (rcur =? R_OK) && negb (rcur =? R_PENDING) then rcur else fst (flush_frame g rcur cur bef)) = fst (flush_frame g rcur cur bef).
Proof.
intros rcur cur bef. destruct (negb (rcur =? R_OK) && negb (rcur =? R_PENDING)) eqn:E; [| reflexivity].
rewrite (flush_frame_dead rcur cur bef E). reflexivity.
Qed.
Lemma raw_addframe_code_live : forall ganim sizeGCT rcur img rfattr width height top lf delay sizeLCT lct disposal transIndex code bytes,
raw_addframe ganim sizeGCT rcur img rfattr width height top lf delay sizeLCT lct disposal transIndex = (code, bytes) ->
negb (rcur =? R_OK) && negb (rcur =? R_PENDING) = false -> code = R_ERROR \/ code = R_EINDEX \/ code = R_OK.
Proof.
intros until code. intros bytes H E. unfold raw_addframe in H. rewrite E in H.
destruct (256 <? sizeLCT); [injection H as <- _; left; reflexivity|]. cbv zeta in H.
match type of H with context [match ?m with Some _ => _ | None => _ end] => destruct m end;
injection H as <- _; [right; right | right; left]; reflexivity.
Qed.
Lemma flush_frame_code_live : forall rcur cur bef code bytes,
flush_frame g rcur cur bef = (code, bytes) -> negb (rcur =? R_OK) && negb (rcur =? R_PENDING) = false ->
code = R_ERROR \/ code = R_EINDEX \/ code = R_OK.
Proof.
intros rcur cur bef code bytes H E. unfold flush_frame in H. destruct bef as [b|].
- cbv zeta in H. match type of H with context [match ?d with pair _ _ => _ end] => destruct d as [[[w h] t] l] end.
eapply raw_addframe_code_live; [exact H | exact E].
- eapply raw_addframe_code_live; [exact H | exact E].
Qed.
Definition af_set_trans (f : frame) (t : Z) : frame := mkFr (f_attr f) (f_gen f) (f_delay f) (f_nlp f) (f_lpal f) (f_img f) (f_ctrans f) (f_disp f) t.
Lemma add_frame_split : forall s,
add_frame g s attr gen delay ctrans nlp lpal img =
if negb (s_cur s =? C_OK) && negb (s_cur s =? C_PENDING) then s
else if af_err then with_cur s C_ERROR else af_from_merge s.
Proof. intros s. reflexivity. Qed.
End AF.
