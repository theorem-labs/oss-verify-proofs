(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Fixpoint nw (nbs : list blk) : Z := match nbs with [] => 0 | b :: r => key_w (snd b) + nw r end.
Lemma nw_nonneg : forall nbs, 0 <= nw nbs.
Proof. induction nbs as [|b r IH]; cbn [nw]; [lia | pose proof (key_w_nonneg (snd b)); lia]. Qed.

Definition vw (cs : option jshape) (cbs : list blk) : option Z :=
match cs with
| Some s => match jtx s cbs with Some (w, []) => Some w | _ => None end
| None => Some 0
end.
Lemma vw_nonneg : forall cs cbs w, vw cs cbs = Some w -> 0 <= w.
Proof.
intros [s|] cbs w H; cbn [vw] in H.
- destruct (jtx s cbs) as [[w0 [|? ?]]|] eqn:E; try discriminate H. injection H as <-. exact (jtx_nonneg _ _ _ _ E).
- injection H as <-. lia.
Qed.
Lemma vw_fresh : forall s BS w, jfresh s BS w -> vw (Some s) BS = Some w.
Proof. intros s BS w H. unfold jfresh in H. cbn [vw]. rewrite H. reflexivity. Qed.
Lemma vw_opt : forall os obs wv, jtx_opt os obs = Some (wv, []) -> exists v, vw os obs = Some v /\ wv <= v + NULL_W.
Proof.
intros [s|] obs wv H; cbn [jtx_opt vw] in *.
- rewrite H. exists wv. split; [reflexivity | unfold NULL_W; lia].
- injection H as <- _. exists 0. split; [reflexivity | lia].
Qed.

Definition lw (l : tlevel) : option Z :=
match vw (tl_cs l) (tl_cbs l) with Some w => Some (w + nw (tl_nbs l)) | None => None end.
Lemma lw_nonneg : forall l w, lw l = Some w -> 0 <= w.
Proof. intros l w H. unfold lw in H. destruct (vw _ _) as [w0|] eqn:E; [| discriminate H]. injection H as <-. pose proof (vw_nonneg _ _ _ E). pose proof (nw_nonneg (tl_nbs l)). lia. Qed.

Fixpoint jwl (levels : list tlevel) (n : nat) : option Z :=
match n, levels with
| O, _ => Some 0
| S n', l :: rest => match lw l, jwl rest n' with Some a, Some b => Some (a + b) | _, _ => None end
| S _, [] => Some 0
end.

Definition ow (st : Z) (os : option jshape) (obs : list blk) : option Z := if zin st [ST_array_add; ST_ovadd] then vw os obs else Some 0.

Definition jw (ts : tstate) : option Z :=
match jwl (t_levels ts) (S (t_depth ts)), ow (cur_st ts) (t_objs ts) (t_objbs ts) with Some a, Some b => Some (a + b) | _, _ => None end.

Lemma jwl_nonneg : forall levels n W, jwl levels n = Some W -> 0 <= W.
Proof.
induction levels as [|h t IH]; intros n W H; destruct n as [|n]; cbn [jwl] in H; try (injection H as <-; lia).
destruct (lw h) as [a|] eqn:E1; [| discriminate H]. destruct (jwl t n) as [b|] eqn:E2; [| discriminate H]. injection H as <-.
pose proof (lw_nonneg _ _ E1). pose proof (IH _ _ E2). lia.
Qed.
Lemma jw_nonneg : forall ts W, jw ts = Some W -> 0 <= W.
Proof.
intros ts W H. unfold jw in H. destruct (jwl _ _) as [a|] eqn:E1; [| discriminate H]. destruct (ow _ _ _) as [b|] eqn:E2; [| discriminate H]. injection H as <-.
pose proof (jwl_nonneg _ _ _ E1). assert (0 <= b) by (unfold ow in E2; destruct (zin _ _); [exact (vw_nonneg _ _ _ E2) | injection E2 as <-; lia]). lia.
Qed.

Lemma jwl_nth : forall levels n i l W, jwl levels n = Some W -> nth_error levels i = Some l -> (i < n)%nat -> exists a, lw l = Some a.
Proof.
induction levels as [|h t IH]; intros n i l W H Hn Hi; [destruct i; discriminate Hn|].
destruct n as [|n]; [lia|]. cbn [jwl] in H. destruct (lw h) as [a|] eqn:E1; [| discriminate H]. destruct (jwl t n) as [b|] eqn:E2; [| discriminate H].
destruct i as [|i]; cbn [nth_error] in Hn; [injection Hn as <-; exists a; exact E1 | exact (IH n i l b E2 Hn ltac:(lia))].
Qed.
Lemma jwl_lupd : forall levels n i l l' a a' W,
nth_error levels i = Some l -> (i < n)%nat -> lw l = Some a -> lw l' = Some a' -> jwl levels n = Some W -> jwl (lupd levels i l') n = Some (W - a + a').
Proof.
induction levels as [|h t IH]; intros n i l l' a a' W Hn Hi La La' H; [destruct i; discriminate Hn|].
destruct n as [|n]; [lia|]. cbn [jwl] in H. destruct (lw h) as [ah|] eqn:E1; [| discriminate H]. destruct (jwl t n) as [b|] eqn:E2; [| discriminate H]. injection H as <-.
destruct i as [|i]; cbn [nth_error] in Hn.
- injection Hn as ->. cbn [lupd jwl]. rewrite La', E2. rewrite La in E1. injection E1 as <-. f_equal. lia.
- cbn [lupd jwl]. rewrite E1, (IH n i l l' a a' b Hn ltac:(lia) La La' E2). f_equal. lia.
Qed.
Lemma jwl_lupd_out : forall levels n i l', (n <= i)%nat -> jwl (lupd levels i l') n = jwl levels n.
Proof.
induction levels as [|h t IH]; intros n i l' Hi; [destruct i; reflexivity|].
destruct n as [|n]; [destruct i; reflexivity|]. destruct i as [|i]; [lia|]. cbn [lupd jwl]. rewrite (IH n i l' ltac:(lia)). reflexivity.
Qed.
Lemma jwl_S : forall levels n l, nth_error levels n = Some l ->
jwl levels (S n) = match jwl levels n, lw l with Some a, Some b => Some (a + b) | _, _ => None end.
Proof.
induction levels as [|h t IH]; intros n l Hn; [destruct n; discriminate Hn|].
destruct n as [|n]; cbn [nth_error] in Hn.
- injection Hn as ->. cbn [jwl]. destruct (lw l) as [a|]; [| reflexivity]. destruct t; f_equal; lia.
- change (jwl (h :: t) (S (S n))) with (match lw h, jwl t (S n) with Some a, Some b => Some (a + b) | _, _ => None end).
rewrite (IH n l Hn). cbn [jwl]. destruct (lw h) as [a|]; [| reflexivity]. destruct (jwl t n) as [b|]; [| reflexivity]. destruct (lw l) as [c|]; [| reflexivity]. f_equal. lia.
Qed.

Definition jlive (st : Z) : bool := zin st [ST_string; ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u; ST_ofield].
Definition jpi0 (st : Z) : Z :=
if zin st [ST_array_sep; ST_osep; ST_ofend] then 0
else if zin st [ST_finish; ST_array_add; ST_ovadd] then 6
else if zin st [ST_esc_need_escape; ST_esc_need_u] then 48
else if zin st [ST_string; ST_string_escape; ST_escape_unicode; ST_ofield] then 30
else 26.
Definition jpi (st ss : Z) : Z := if st =? ST_eatws then jpi0 ss else jpi0 st.
Lemma jpi0_range : forall st, 0 <= jpi0 st <= 48. Proof. intros st. unfold jpi0. repeat (destruct (zin _ _)); lia. Qed.
Lemma jpi_range : forall st ss, 0 <= jpi st ss <= 48. Proof. intros st ss. unfold jpi. destruct (st =? ST_eatws); apply jpi0_range. Qed.

Definition JC1 : Z := 26.
Definition JC0 : Z := 64.
Definition jtext (st g : Z) : Z := if jlive st then 6 * g else 0.

Definition JL (ts : tstate) (g a : Z) : Prop :=
exists W, jw ts = Some W /\ W + jtext (cur_st ts) g + jpi (cur_st ts) (cur_ss ts) <= JC1 * a + JC0.

Lemma JL_step : forall ts ts' g g' a a' W,
JL ts g a -> jw ts = Some W ->
(exists W', jw ts' = Some W' /\
W' + jtext (cur_st ts') g' + jpi (cur_st ts') (cur_ss ts') <= W + jtext (cur_st ts) g + jpi (cur_st ts) (cur_ss ts) + JC1 * (a' - a)) ->
JL ts' g' a'.
Proof. intros ts ts' g g' a a' W (W0 & E0 & H) E (W' & E' & H'). rewrite E in E0. injection E0 as <-. exists W'. split; [exact E' | lia]. Qed.
Lemma JL_jw : forall ts g a, JL ts g a -> exists W, jw ts = Some W. Proof. intros ts g a (W & E & _). exists W. exact E. Qed.

Definition JOUT (len : Z) (ts : tstate) : Prop :=
bv_unsigned (sx32 (ts_err (t_x ts))) = 0 -> exists W, jw ts = Some W /\ W <= JC1 * len + JC0.

Lemma cur_st_updJ : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l -> cur_st (TST depth (lupd levels depth l') co pb pbs x o os obs) = tl_st l'.
Proof. intros. unfold cur_st; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; congruence). reflexivity. Qed.
Lemma cur_ss_updJ : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l -> cur_ss (TST depth (lupd levels depth l') co pb pbs x o os obs) = tl_ss l'.
Proof. intros. unfold cur_ss; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; congruence). reflexivity. Qed.
Lemma cur_st_ofJ : forall depth levels l co pb pbs x o os obs, nth_error levels depth = Some l -> cur_st (TST depth levels co pb pbs x o os obs) = tl_st l.
Proof. intros. unfold cur_st; cbn [t_levels t_depth]. rewrite H. reflexivity. Qed.
Lemma cur_ss_ofJ : forall depth levels l co pb pbs x o os obs, nth_error levels depth = Some l -> cur_ss (TST depth levels co pb pbs x o os obs) = tl_ss l.
Proof. intros. unfold cur_ss; cbn [t_levels t_depth]. rewrite H. reflexivity. Qed.

Lemma jw_same : forall ts ts', t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts ->
(zin (cur_st ts) [ST_array_add; ST_ovadd] = true -> t_objs ts' = t_objs ts /\ t_objbs ts' = t_objbs ts) -> jw ts' = jw ts.
Proof.
intros ts ts' E1 E2 E3. unfold jw. assert (Ec : cur_st ts' = cur_st ts) by (unfold cur_st; rewrite E1, E2; reflexivity).
rewrite E1, E2, Ec. unfold ow. destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]) eqn:Z; [destruct (E3 eq_refl) as [-> ->]; reflexivity | reflexivity].
Qed.

Lemma jw_upd : forall depth levels l l' co pb pbs x o os obs co' pb' pbs' x' W a',
nth_error levels depth = Some l -> jw (TST depth levels co pb pbs x o os obs) = Some W -> lw l' = Some a' ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
exists a0, lw l = Some a0 /\ jw (TST depth (lupd levels depth l') co' pb' pbs' x' o os obs) = Some (W - a0 + a').
Proof.
intros depth levels l l' co pb pbs x o os obs co' pb' pbs' x' W a' Hl HW La' Hz.
unfold jw in HW |- *. cbn [t_levels t_depth t_objs t_objbs] in HW |- *.
rewrite (cur_st_ofJ _ _ l) in HW by exact Hl. rewrite (cur_st_updJ _ _ l) by exact Hl. unfold ow in HW |- *. rewrite Hz.
destruct (jwl levels (S depth)) as [A|] eqn:EA; [| discriminate HW].
destruct (if zin (tl_st l) [ST_array_add; ST_ovadd] then vw os obs else Some 0) as [Bv|] eqn:EB; [| discriminate HW]. injection HW as <-.
destruct (jwl_nth levels (S depth) depth l A EA Hl ltac:(lia)) as (a0 & La0). exists a0. split; [exact La0|].
rewrite (jwl_lupd levels (S depth) depth l l' a0 a' A Hl ltac:(lia) La0 La' EA). f_equal. lia.
Qed.

Lemma jw_upd_add : forall depth levels l l' co pb pbs x o os obs co' pb' pbs' x' o' os' obs' W a',
nth_error levels depth = Some l -> jw (TST depth levels co pb pbs x o os obs) = Some W -> lw l' = Some a' ->
zin (tl_st l) [ST_array_add; ST_ovadd] = true -> zin (tl_st l') [ST_array_add; ST_ovadd] = false ->
exists a0 b, lw l = Some a0 /\ vw os obs = Some b /\ jw (TST depth (lupd levels depth l') co' pb' pbs' x' o' os' obs') = Some (W - a0 - b + a').
Proof.
intros depth levels l l' co pb pbs x o os obs co' pb' pbs' x' o' os' obs' W a' Hl HW La' Hz Hz'.
unfold jw in HW |- *. cbn [t_levels t_depth t_objs t_objbs] in HW |- *.
rewrite (cur_st_ofJ _ _ l) in HW by exact Hl. rewrite (cur_st_updJ _ _ l) by exact Hl. unfold ow in HW |- *. rewrite Hz in HW. rewrite Hz'.
destruct (jwl levels (S depth)) as [A|] eqn:EA; [| discriminate HW]. destruct (vw os obs) as [Bv|] eqn:EB; [| discriminate HW]. injection HW as <-.
destruct (jwl_nth levels (S depth) depth l A EA Hl ltac:(lia)) as (a0 & La0). exists a0, Bv. split; [exact La0|]. split; [reflexivity|].
rewrite (jwl_lupd levels (S depth) depth l l' a0 a' A Hl ltac:(lia) La0 La' EA). f_equal. lia.
Qed.

Lemma jw_push : forall depth levels l lp co pb pbs x o os obs W,
nth_error levels depth = Some l -> (S depth < length levels)%nat -> jw (TST depth levels co pb pbs x o os obs) = Some W -> lw lp = lw l ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
jw (TST (S depth) (lupd (lupd levels depth lp) (S depth) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x o os obs) = Some W.
Proof.
intros depth levels l lp co pb pbs x o os obs W Hl Hlen HW Elw Hz.
unfold jw in HW |- *. cbn [t_levels t_depth t_objs t_objbs] in HW |- *.
rewrite (cur_st_ofJ _ _ l) in HW by exact Hl. unfold ow in HW. rewrite Hz in HW.
destruct (jwl levels (S depth)) as [A|] eqn:EA; [| discriminate HW]. injection HW as <-.
assert (Ec : cur_st (TST (S depth) (lupd (lupd levels depth lp) (S depth) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x o os obs) = ST_eatws).
{ unfold cur_st; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (rewrite lupd_length; exact Hlen). reflexivity. }
rewrite Ec. unfold ow. change (zin ST_eatws [ST_array_add; ST_ovadd]) with false.
destruct (jwl_nth levels (S depth) depth l A EA Hl ltac:(lia)) as (a0 & La0).
rewrite (jwl_S _ (S depth) (TL ST_eatws ST_start 0 None [] 0 [])) by (apply nth_error_lupd_eq; rewrite lupd_length; exact Hlen).
rewrite jwl_lupd_out by lia.
rewrite (jwl_lupd levels (S depth) depth l lp a0 a0 A Hl ltac:(lia) La0 ltac:(rewrite Elw; exact La0) EA).
change (lw (TL ST_eatws ST_start 0 None [] 0 [])) with (Some 0). f_equal. lia.
Qed.

Lemma jw_pop : forall dp levels l lp co pb pbs x o os obs W,
nth_error levels (S dp) = Some l -> nth_error levels dp = Some lp ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false -> zin (tl_st lp) [ST_array_add; ST_ovadd] = true ->
jw (TST (S dp) levels co pb pbs x o os obs) = Some W ->
exists W', jw (TST dp (lupd levels (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x (tl_cur l) (tl_cs l) (tl_cbs l)) = Some W' /\ W' <= W.
Proof.
intros dp levels l lp co pb pbs x o os obs W Hl Hlp Hz Hzp HW.
unfold jw in HW |- *. cbn [t_levels t_depth t_objs t_objbs] in HW |- *.
rewrite (cur_st_ofJ _ _ l) in HW by exact Hl. unfold ow in HW. rewrite Hz in HW.
destruct (jwl levels (S (S dp))) as [A|] eqn:EA; [| discriminate HW]. injection HW as <-.
rewrite (jwl_S levels (S dp) l Hl) in EA. destruct (jwl levels (S dp)) as [A0|] eqn:EA0; [| discriminate EA]. destruct (lw l) as [al|] eqn:El; [| discriminate EA]. injection EA as <-.
assert (Ec : cur_st (TST dp (lupd levels (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x (tl_cur l) (tl_cs l) (tl_cbs l)) = tl_st lp).
{ unfold cur_st; cbn [t_levels t_depth]. rewrite nth_error_lupd_neq by lia. rewrite Hlp. reflexivity. }
rewrite Ec. unfold ow. rewrite Hzp. rewrite jwl_lupd_out by lia. rewrite EA0.
unfold lw in El. destruct (vw (tl_cs l) (tl_cbs l)) as [v|] eqn:Ev; [| discriminate El]. injection El as <-.
exists (A0 + v). split; [reflexivity|]. pose proof (nw_nonneg (tl_nbs l)). lia.
Qed.

Lemma lw_restate : forall l l', tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l -> lw l' = lw l.
Proof. intros l l' E1 E2 E3. unfold lw. rewrite E1, E2, E3. reflexivity. Qed.

Lemma JL_dead : forall ts g g' a, jlive (cur_st ts) = false -> JL ts g a -> JL ts g' a.
Proof. intros ts g g' a H (W & E & L). exists W. split; [exact E|]. unfold jtext in *. rewrite H in *. exact L. Qed.
Lemma JL_mono : forall ts g g' a a', g' <= g -> a <= a' -> JL ts g a -> JL ts g' a'.
Proof. intros ts g g' a a' Hg Ha (W & E & L). exists W. split; [exact E|]. unfold jtext, JC1 in *. destruct (jlive (cur_st ts)); lia. Qed.
Lemma JL_same : forall ts ts' g a, t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts ->
(zin (cur_st ts) [ST_array_add; ST_ovadd] = true -> t_objs ts' = t_objs ts /\ t_objbs ts' = t_objbs ts) -> JL ts g a -> JL ts' g a.
Proof.
intros ts ts' g a E1 E2 E3 (W & E & L). exists W. rewrite (jw_same ts ts' E1 E2 E3).
assert (Ec : cur_st ts' = cur_st ts) by (unfold cur_st; rewrite E1, E2; reflexivity). assert (Es : cur_ss ts' = cur_ss ts) by (unfold cur_ss; rewrite E1, E2; reflexivity).
rewrite Ec, Es. split; [exact E | exact L].
Qed.

Lemma JL_upd : forall depth levels l l' co pb pbs x o os obs co' pb' pbs' x' g g' a a' w',
nth_error levels depth = Some l -> lw l' = Some w' ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL (TST depth levels co pb pbs x o os obs) g a ->
(forall w0, lw l = Some w0 -> 0 <= w0 ->
w' + jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= w0 + jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a)) ->
JL (TST depth (lupd levels depth l') co' pb' pbs' x' o os obs) g' a'.
Proof.
intros depth levels l l' co pb pbs x o os obs co' pb' pbs' x' g g' a a' w' Hl Lw' Hz (W & E & L) H.
destruct (jw_upd depth levels l l' co pb pbs x o os obs co' pb' pbs' x' W w' Hl E Lw' Hz) as (w0 & Lw0 & E').
exists (W - w0 + w'). split; [exact E'|].
rewrite (cur_st_updJ _ _ l), (cur_ss_updJ _ _ l) by exact Hl. rewrite (cur_st_ofJ _ _ l), (cur_ss_ofJ _ _ l) in L by exact Hl.
specialize (H w0 Lw0 (lw_nonneg _ _ Lw0)). lia.
Qed.

Lemma JOUT_of_JL : forall len ts ts' g a, JL ts g a -> 0 <= g -> a <= len -> jw ts' = jw ts -> JOUT len ts'.
Proof.
intros len ts ts' g a (W & E & L) Hg Ha Ej _. exists W. rewrite Ej. split; [exact E|].
pose proof (jpi_range (cur_st ts) (cur_ss ts)).
unfold jtext, JC1, JC0 in *. destruct (jlive (cur_st ts)); lia.
Qed.
Lemma JOUT_err : forall len ts, bv_unsigned (sx32 (ts_err (t_x ts))) <> 0 -> JOUT len ts.
Proof. intros len ts H E. exfalso. exact (H E). Qed.

Lemma JOUT_set_err : forall len ts e, 0 < e < 2^31 -> JOUT len (ts_set_err ts (Z_to_bv 64 e)).
Proof.
intros len ts e He. apply JOUT_err. destruct ts as [d lv co pb pbs x o os obs]. destruct x as [isd sp ch er uc hi qu]. unfold ts_set_err. cbn [t_x ts_err].
rewrite sx32_small by lia. rewrite unsigned_lit by lia. lia.
Qed.
Lemma JOUT_same : forall len ts ts', jw ts' = jw ts -> ts_err (t_x ts') = ts_err (t_x ts) -> JOUT len ts -> JOUT len ts'.
Proof. intros len ts ts' Ej Ee H E. rewrite Ee in E. rewrite Ej. exact (H E). Qed.

End RC__1.
