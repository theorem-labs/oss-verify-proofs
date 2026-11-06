(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QCcH Q0Ek Qtgi QjDH Qsw7 QkMG QG8z Qdyh QLbz QlKV QrQv Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import QlKV.Mq2 QrQv.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Pins.
Variable segs : list Segment.
Variable fn : fnaddrs.
Lemma jfresh_scalar48 : forall s m BS p rc, jval segs fn s m BS p rc -> length BS = 1%nat -> (s = Sbool /\ jfresh s BS 8) \/ (s = Sdouble false /\ jfresh s BS 9) \/ (s <> Sbool /\ s <> Sdouble false).
Proof.
intros s m BS p rc J L. destruct s as [|ud| |h|k|k]; try (right; right; split; discriminate).
- left. split; [reflexivity|]. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (b & junk & -> & _)). subst BS.
destruct PBS as [|x PBS]; [reflexivity | cbn in L; lia].
- destruct ud; [right; right; split; discriminate|]. right; left. split; [reflexivity|].
cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (bits & -> & _)). subst BS.
destruct PBS as [|x PBS]; [reflexivity | cbn in L; lia].
Qed.
Lemma jfresh_bool : forall m BS p rc, jval segs fn Sbool m BS p rc -> length BS = 1%nat -> jfresh Sbool BS 8.
Proof. intros m BS p rc J L. destruct (jfresh_scalar48 _ _ _ _ _ J L) as [[_ H] | [[E _] | [E _]]]; [exact H | discriminate E | exfalso; apply E; reflexivity]. Qed.
Lemma jfresh_dbl : forall m BS p rc, jval segs fn (Sdouble false) m BS p rc -> length BS = 1%nat -> jfresh (Sdouble false) BS 9.
Proof. intros m BS p rc J L. destruct (jfresh_scalar48 _ _ _ _ _ J L) as [[E _] | [[_ H] | [_ E]]]; [discriminate E | exact H | exfalso; apply E; reflexivity]. Qed.
Lemma jfresh_int : forall m BS p rc, jval segs fn Sint m BS p rc -> length BS = 1%nat -> jfresh Sint BS 20.
Proof.
intros m BS p rc J L. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (cty & v & junk & -> & _)). subst BS.
destruct PBS as [|x PBS]; [reflexivity | cbn in L; lia].
Qed.

Lemma jfresh_dbls : forall p ud n, 0 <= n -> jfresh (Sdouble true) [(p, 48); (ud, n + 1)] (16 + n).
Proof. intros p ud n H. replace (16 + n) with (16 + Z.max 0 (n + 1 - 1)) by lia. apply jtx_dbl_ud. Qed.
End Pins.

End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import QlKV.Mq2 QrQv.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
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

End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV QfLs QJjn QRUw Q8tj QbFI Qhd4 Qwm6 QsKa Qiiq Q4v2 QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 QJjn QRUw.Mq0 QkMG. Import QG8z QLbz Qdyh.Mq0. Import Q8tj.
Import QbFI. Import Qhd4. Import Qwm6.Mq4 QsKa.Mqd Qiiq Q4v2 QSHS QrQv.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition K_ev (pf : pe_fix) : Z := 1.
Lemma K_ev_pos : forall pf, 1 <= K_ev pf. Proof. intros pf. unfold K_ev. lia. Qed.

Definition lvl_closed (l : tlevel) : bool := (tl_ss l =? ST_finish) && negb (zin (tl_st l) [ST_array_add; ST_ovadd]).
Definition phi_open (l : tlevel) : Z := if lvl_closed l then 0 else phi_level l.

Lemma lvl_closed_open_ss : forall l, tl_ss l <> ST_finish -> lvl_closed l = false.
Proof. intros l H. unfold lvl_closed. replace (tl_ss l =? ST_finish) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.
Lemma lvl_closed_open_st : forall l, zin (tl_st l) [ST_array_add; ST_ovadd] = true -> lvl_closed l = false.
Proof. intros l H. unfold lvl_closed. rewrite H. apply andb_false_r. Qed.

Lemma lvl_closed_keep : forall l st' c cs cbs nm nbs, zin st' [ST_array_add; ST_ovadd] = false -> lvl_closed l = true -> lvl_closed (TL st' (tl_ss l) c cs cbs nm nbs) = true.
Proof. intros l st' c cs cbs nm nbs Hz H. unfold lvl_closed in *. cbn [tl_ss tl_st]. apply andb_true_iff in H as [H _]. rewrite H, Hz. reflexivity. Qed.
Lemma lvl_closed_fin : forall st' c cs cbs nm nbs, zin st' [ST_array_add; ST_ovadd] = false -> lvl_closed (TL st' ST_finish c cs cbs nm nbs) = true.
Proof. intros st' c cs cbs nm nbs Hz. unfold lvl_closed. cbn [tl_ss tl_st]. rewrite Hz. reflexivity. Qed.

Fixpoint ledger_open (levels : list tlevel) (n : nat) : Z :=
match n, levels with
| O, _ => 0
| S n', l :: rest => phi_open l + ledger_open rest n'
| S _, [] => 0
end.

Definition lvl_disc (pf : pe_fix) (l : tlevel) : Prop :=
0 <= phi_open l /\
(lvl_closed l = false -> forall kids, tl_cs l = Some (Sarr kids) -> arr_inv (arr_capA (tl_cbs l)) (Z.of_nat (length kids))) /\

(lvl_closed l = false -> forall kids, tl_cs l = Some (Sobj kids) -> In (obj_capA (tl_cbs l)) lf_sizes) /\

Forall (fun b : blk => snd b <= Z.max 0 (pf_len pf) + 1) (tl_nbs l).

Definition bneed (pf : pe_fix) (pa : pe_fixA) (ts : tstate) (n : nat) : Z :=
K_ev pf * Z.of_nat n + ledger_open (t_levels ts) (S (t_depth ts)) + PhiPB (pf_len pf) (pb_capA (t_pbs ts))
+ K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa.

Definition BOK (pf : pe_fix) (pa : pe_fixA) (ts : tstate) (B : bud) (n : nat) : Prop :=
bneed pf pa ts n <= bB B /\ Z.of_nat n + pa_dslack pa <= bD B /\
0 <= PhiPB (pf_len pf) (pb_capA (t_pbs ts)) /\ pb_inv (pb_capA (t_pbs ts)) (t_co ts) /\
(forall i l, (i <= t_depth ts)%nat -> nth_error (t_levels ts) i = Some l -> lvl_disc pf l).

Lemma ledger_open_nonneg : forall levels n, (forall i l, (i < n)%nat -> nth_error levels i = Some l -> 0 <= phi_open l) -> 0 <= ledger_open levels n.
Proof.
induction levels as [|h t IH]; intros n H; [destruct n; cbn; lia|].
destruct n as [|n]; cbn; [lia|].
pose proof (H 0%nat h ltac:(lia) eq_refl). pose proof (IH n ltac:(intros i l Hi Hn; apply (H (S i) l); [lia | exact Hn])). lia.
Qed.

Lemma ledger_open_lupd : forall levels n i l l',
nth_error levels i = Some l -> (i < n)%nat -> ledger_open (lupd levels i l') n = ledger_open levels n - phi_open l + phi_open l'.
Proof.
induction levels as [|h t IH]; intros n i l l' Hn Hi; [destruct i; discriminate|].
destruct i as [|i]; cbn in Hn.
- injection Hn as ->. destruct n as [|n]; [lia|]. cbn. lia.
- destruct n as [|n]; [lia|]. cbn. rewrite (IH n i l l' Hn ltac:(lia)). lia.
Qed.

Lemma ledger_open_lupd_out : forall levels n i l', (n <= i)%nat -> ledger_open (lupd levels i l') n = ledger_open levels n.
Proof.
induction levels as [|h t IH]; intros n i l' Hi; [destruct i; reflexivity|].
destruct n as [|n]; [destruct i; reflexivity|]. destruct i as [|i]; [lia|]. cbn. rewrite (IH n i l' ltac:(lia)). reflexivity.
Qed.

Lemma BOK_ledger_nonneg : forall pf pa ts B n, BOK pf pa ts B n -> 0 <= ledger_open (t_levels ts) (S (t_depth ts)).
Proof. intros pf pa ts B n (_ & _ & _ & _ & D). apply ledger_open_nonneg. intros i l Hi Hn. exact (proj1 (D i l ltac:(lia) Hn)). Qed.

Lemma BOK_weaken : forall pf pa ts B n n', (n' <= n)%nat -> BOK pf pa ts B n -> BOK pf pa ts B n'.
Proof.
intros pf pa ts B n n' Hn (H1 & H2 & H3). pose proof (K_ev_pos pf).
pose proof (Z.mul_le_mono_nonneg_l (Z.of_nat n') (Z.of_nat n) (K_ev pf) ltac:(lia) ltac:(lia)).
unfold BOK, bneed in *. split; [lia|]. split; [lia | exact H3].
Qed.

Lemma BOK_mono : forall pf pa ts B B' n, bB B <= bB B' -> bD B <= bD B' -> BOK pf pa ts B n -> BOK pf pa ts B' n.
Proof. intros pf pa ts B B' n HB HD (H1 & H2 & H3). unfold BOK in *. split; [lia|]. split; [lia | exact H3]. Qed.

Lemma BOK_pay : forall pf pa ts B B' n c {C}, BOK pf pa ts B (S (Z.to_nat C + n)) -> c <= C -> bB B - c <= bB B' -> bD B - 1 <= bD B' -> BOK pf pa ts B' n.
Proof.
intros pf pa ts B B' n c C (H1 & H2 & H3) Hc HB HD. unfold BOK, bneed, K_ev in *. split; [lia|]. split; [lia | exact H3].
Qed.

Lemma BOK_drop : forall pf pa ts B n C, BOK pf pa ts B (S (Z.to_nat C + n)) -> BOK pf pa ts B n.
Proof. intros pf pa ts B n C H. eapply BOK_weaken; [| exact H]. lia. Qed.

Lemma BOK_weak : forall pf pa ts B n, BOK pf pa ts B n -> PE_BUD pf pa ts B.
Proof.
intros pf pa ts B n H. pose proof (BOK_ledger_nonneg _ _ _ _ _ H) as L0. destruct H as (H1 & H2 & H3 & _).
pose proof (K_ev_pos pf). pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)). unfold bneed in H1. split; [lia | lia].
Qed.

Lemma BOK_set_co : forall pf pa ts B n co', t_co ts <= co' -> BOK pf pa ts B n -> BOK pf pa (ts_set_co ts co') B n.
Proof.
intros pf pa ts B n co' Hco (H1 & H2 & H3 & H4 & H5). unfold ts_set_co.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [eapply pb_inv_mono; [exact H4 | cbn [t_co]; lia] | exact H5].
Qed.

Lemma BOK_lvl_restate : forall pf pa ts B n l st' ss',
nth_error (t_levels ts) (t_depth ts) = Some l ->
(lvl_closed l = true -> lvl_closed (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) = true) ->
BOK pf pa ts B n ->
BOK pf pa (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B n.
Proof.
intros pf pa ts B n l st' ss' Hl Hcl (H1 & H2 & H3 & H4 & H5).
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & OI & NI).
assert (Hphi : 0 <= phi_open l' <= phi_open l).
{ unfold phi_open in *. fold l' in Hcl. change (phi_level l') with (phi_level l).
destruct (lvl_closed l') eqn:E1; destruct (lvl_closed l) eqn:E2; try lia; specialize (Hcl eq_refl); discriminate Hcl. }
assert (Hblk : tstate_blocks (ts_lvl ts l') = tstate_blocks ts).
{ unfold tstate_blocks, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth]. rewrite (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) l' l Hl eq_refl). reflexivity. }
split.
{ unfold bneed in *. rewrite Hblk. unfold ts_lvl; cbn [t_levels t_depth t_pbs]. rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)). lia. }
split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [lia|].
assert (Hopl : lvl_closed l' = false -> lvl_closed l = false) by (intros Hop; destruct (lvl_closed l) eqn:E; [| reflexivity]; fold l' in Hcl; rewrite (Hcl eq_refl) in Hop; discriminate Hop).
split; [intros Hop kids Hcs; apply AI; [exact (Hopl Hop) | exact Hcs]|]. split; [intros Hop kids Hcs; apply (OI (Hopl Hop) kids); exact Hcs | exact NI].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma BOK_memappend : forall pf pa ts B k pb buf cap bpos n,
BOK pf pa ts B k -> t_pbs ts = [(pb, PB_SZ); (buf, cap)] -> 0 <= pa_bslack pa ->
0 <= bpos -> 0 <= n -> bpos + n <= t_co ts + 1 -> 0 <= t_co ts <= pf_len pf -> pf_len pf < 2^26 ->
memappend_costX cap bpos n <= bB B /\
(forall buf' B', bB B - memappend_costX2 cap bpos n <= bB B' -> bD B <= bD B' ->
BOK pf pa (ts_pbs ts [(pb, PB_SZ); (buf', memappend_cap2 cap bpos n)]) B' k).
Proof.
intros pf pa ts B k pb buf cap bpos n H E BSL Hb Hn Hbn Hco Hlen.
pose proof (BOK_ledger_nonneg _ _ _ _ _ H) as L0. destruct H as (H1 & H2 & H4 & H5 & H6).
unfold bneed in H1. rewrite E in H1, H4, H5. unfold pb_capA in H1, H4, H5. cbn [nth snd] in H1, H4, H5.
destruct (potential_step_memappend2 (pf_len pf) cap bpos n (t_co ts) H5 Hb Hn Hbn ltac:(lia) Hlen) as (P1 & P2 & P3 & P4).
pose proof (Zle_0_nat (length (tstate_blocks ts))) as Hnb. pose proof (K_ev_pos pf) as KE.
pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat k) ltac:(lia) ltac:(lia)) as KN. unfold K_free, K_exit in *.
split; [lia|]. intros buf' B' HB HD.
assert (Hblk : length (tstate_blocks (ts_pbs ts [(pb, PB_SZ); (buf', memappend_cap2 cap bpos n)])) = length (tstate_blocks ts)).
{ unfold tstate_blocks, ts_pbs; cbn [t_pbs t_objbs t_levels]. rewrite E. rewrite !length_app. reflexivity. }
unfold BOK, bneed. rewrite Hblk. unfold ts_pbs; cbn [t_levels t_depth t_pbs t_co]. unfold pb_capA. cbn [nth snd].
split; [unfold K_free, K_exit; lia|]. split; [lia|]. split; [exact P3|]. split; [exact P2 | exact H6].
Qed.

Lemma BOK_memappend_fail : forall pf pa ts B B' k pb buf cap bpos n,
BOK pf pa ts B k -> t_pbs ts = [(pb, PB_SZ); (buf, cap)] ->
0 <= bpos -> 0 <= n -> bpos + n <= t_co ts + 1 -> 0 <= t_co ts <= pf_len pf -> pf_len pf < 2^26 ->
bB B - memappend_costX2 cap bpos n <= bB B' -> bD B <= bD B' ->
PE_BUD pf pa ts B'.
Proof.
intros pf pa ts B B' k pb buf cap bpos n H E Hb Hn Hbn Hco Hlen HB HD.
pose proof (BOK_ledger_nonneg _ _ _ _ _ H) as L0. destruct H as (H1 & H2 & H4 & H5 & H6).
unfold bneed in H1. rewrite E in H1, H4, H5. unfold pb_capA in H1, H4, H5. cbn [nth snd] in H1, H4, H5.
destruct (potential_step_memappend2 (pf_len pf) cap bpos n (t_co ts) H5 Hb Hn Hbn ltac:(lia) Hlen) as (P1 & P2 & P3 & P4).
pose proof (memappend_costX2_le cap bpos n ltac:(destruct H5; lia)) as LE.
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat k) ltac:(lia) ltac:(lia)) as KN.
split; lia.
Qed.

Lemma tstate_blocks_lvl_length : forall ts l l',
nth_error (t_levels ts) (t_depth ts) = Some l ->
Z.of_nat (length (tstate_blocks (ts_lvl ts l'))) = Z.of_nat (length (tstate_blocks ts)) - Z.of_nat (length (lvl_blocks l)) + Z.of_nat (length (lvl_blocks l')).
Proof.
intros ts l l' Hl. unfold tstate_blocks, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (lupd_split _ _ _ l' Hl), (concat_split _ _ _ Hl). rewrite !length_app. lia.
Qed.

Lemma ledger_open_ge : forall levels n i l,
nth_error levels i = Some l -> (i < n)%nat -> (forall j lj, (j < n)%nat -> nth_error levels j = Some lj -> 0 <= phi_open lj) ->
phi_open l <= ledger_open levels n.
Proof.
intros levels n i l Hn Hi H.
pose proof (ledger_open_lupd levels n i l lvl_reset Hn Hi) as E. change (phi_open lvl_reset) with 0 in E.
assert (0 <= ledger_open (lupd levels i lvl_reset) n).
{ apply ledger_open_nonneg. intros j lj Hj Hnj. destruct (PeanoNat.Nat.eq_dec j i) as [-> | NE].
- rewrite nth_error_lupd_eq in Hnj by (apply nth_error_Some; rewrite Hn; discriminate). injection Hnj as <-. cbn. lia.
- rewrite nth_error_lupd_neq in Hnj by congruence. exact (H j lj Hj Hnj). }
lia.
Qed.

Lemma BOK_arr_close : forall pf pa ts B n l kids,
BOK pf pa ts B n -> 0 <= pa_bslack pa ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some (Sarr kids) -> lvl_closed l = false ->
arr_shrink_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B /\
(forall B' cbs2 st', zin st' [ST_array_add; ST_ovadd] = false -> length cbs2 = length (tl_cbs l) ->
bB B - arr_shrink_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
BOK pf pa (ts_lvl ts (TL st' ST_finish (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l))) B' n).
Proof.
intros pf pa ts B n l kids H BSL Hl Hcs Hop.
pose proof H as (H1 & H2 & H3 & H4 & H5).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & _ & NI). specialize (AI Hop kids Hcs).
assert (Ephi : phi_open l = PhiA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) + RA).
{ unfold phi_open. rewrite Hop. unfold phi_level. rewrite Hcs. reflexivity. }
pose proof (potential_step_arr_close _ _ AI) as STEP.
pose proof (ledger_open_ge (t_levels ts) (S (t_depth ts)) (t_depth ts) l Hl (Nat.lt_succ_diag_r _)
ltac:(intros j lj Hj Hnj; exact (proj1 (H5 j lj ltac:(lia) Hnj)))) as GE.
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)) as KN.
pose proof (Zle_0_nat (length (tstate_blocks ts))) as Hnb.
unfold bneed in H1. unfold K_free, K_exit in *.
split; [lia|]. intros B' cbs2 st' Hz' Hlen HB HD.
set (l' := TL st' ST_finish (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l)).
assert (Hcl' : lvl_closed l' = true) by (apply lvl_closed_fin; exact Hz').
assert (Hphi' : phi_open l' = 0) by (unfold phi_open; rewrite Hcl'; reflexivity).
pose proof (tstate_blocks_lvl_length ts l l' Hl) as Hblk.
assert (Hlb : length (lvl_blocks l') = length (lvl_blocks l)) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite !length_app, Hlen; reflexivity).
rewrite Hlb in Hblk.
unfold BOK, bneed. rewrite Hblk. unfold ts_lvl; cbn [t_levels t_depth t_pbs t_co].
rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)), Hphi'.
split; [unfold K_free, K_exit; lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|].
intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [rewrite Hphi'; lia|].
split; [intros Hss; rewrite Hcl' in Hss; discriminate Hss|]. split; [intros Hss; rewrite Hcl' in Hss; discriminate Hss | exact NI].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma tstate_blocks_lvl_obj_length : forall ts l l' o os obs,
nth_error (t_levels ts) (t_depth ts) = Some l ->
Z.of_nat (length (tstate_blocks (ts_lvl_obj ts l' o os obs))) =
Z.of_nat (length (tstate_blocks ts)) - Z.of_nat (length (lvl_blocks l)) - Z.of_nat (length (t_objbs ts)) + Z.of_nat (length (lvl_blocks l')) + Z.of_nat (length obs).
Proof.
intros ts l l' o os obs Hl. unfold tstate_blocks, ts_lvl_obj; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (lupd_split _ _ _ l' Hl), (concat_split _ _ _ Hl). rewrite !length_app. lia.
Qed.

Lemma PhiA_nonneg : forall cap len, arr_inv cap len -> 0 <= PhiA cap len.
Proof. intros cap len (H32 & Hl & Hc). unfold PhiA. lia. Qed.

Lemma BOK_arr_add : forall pf pa ts B n l kids,
BOK pf pa ts B (S (Z.to_nat 1280 + n)) -> 0 <= pa_bslack pa ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some (Sarr kids) -> lvl_closed l = false ->
arr_add_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B /\
(forall B', bB B - arr_add_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' -> PE_BUD pf pa ts B') /\
(forall B' cbs2 st' ss' obj' objs', ss' <> ST_finish -> length cbs2 = (length (tl_cbs l) + length (t_objbs ts))%nat ->
arr_grownA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) (arr_capA cbs2) ->
bB B - arr_add_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B' n).
Proof.
intros pf pa ts B n l kids H BSL Hl Hcs Hop.
pose proof H as (H1 & H2 & H3 & H4 & H5).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & _ & NI). specialize (AI Hop kids Hcs).
assert (Ephi : phi_open l = PhiA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) + RA).
{ unfold phi_open. rewrite Hop. unfold phi_level. rewrite Hcs. reflexivity. }
pose proof (ledger_open_ge (t_levels ts) (S (t_depth ts)) (t_depth ts) l Hl (Nat.lt_succ_diag_r _)
ltac:(intros j lj Hj Hnj; exact (proj1 (H5 j lj ltac:(lia) Hnj)))) as GE.
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)) as KN.
pose proof (Zle_0_nat (length (tstate_blocks ts))) as Hnb.
unfold bneed in H1. assert (KU : K_ev pf * Z.of_nat (S (Z.to_nat 1280 + n)) = K_ev pf * Z.of_nat n + 1281) by (unfold K_ev; lia). rewrite KU in H1. clear KU.
assert (COSTB : arr_add_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= PhiA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) + RA + K_arr).
{ destruct AI as (A32 & Alen & Acap). unfold arr_add_costA, PhiA, RA, K_arr. destruct (Z.of_nat (length kids) + 1 <? arr_capA (tl_cbs l)) eqn:E; [lia|]. apply Z.ltb_ge in E. lia. }
unfold K_arr in COSTB. unfold K_free, K_exit in *.
split; [lia|]. split.
{ intros B' HB HD. split; [unfold K_free, K_exit; lia | lia]. }
intros B' cbs2 st' ss' obj' objs' Hss' Hlen GR HB HD.
set (l' := TL st' ss' (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)).
destruct (potential_step_arr_add _ _ _ AI GR) as [STEP AI'].
assert (Elen : Z.of_nat (length (kids ++ [t_objs ts])) = Z.of_nat (length kids) + 1) by (rewrite length_app; cbn [length]; lia).
assert (Hphi' : phi_open l' = PhiA (arr_capA cbs2) (Z.of_nat (length kids) + 1) + RA).
{ unfold phi_open. rewrite (lvl_closed_open_ss l' Hss'). unfold phi_level, l'. cbn [tl_cs tl_cbs]. rewrite Elen. reflexivity. }
pose proof (PhiA_nonneg _ _ AI') as PN.
pose proof (tstate_blocks_lvl_obj_length ts l l' obj' objs' [] Hl) as Hblk.
assert (Hlb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length (lvl_blocks l)) + Z.of_nat (length (t_objbs ts))).
{ unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite !length_app, Hlen. lia. }
cbn [length] in Hblk.
unfold BOK, bneed. rewrite Hblk. unfold ts_lvl_obj; cbn [t_levels t_depth t_pbs t_co].
rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)), Hphi'.
unfold RA, K_arr in *.
split; [unfold K_free, K_exit; lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|].
intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [rewrite Hphi'; unfold RA; lia|].
split; [intros _ kids2 Hk2; unfold l' in Hk2 |- *; cbn [tl_cs tl_cbs] in Hk2 |- *; injection Hk2 as <-; rewrite Elen; exact AI'|].
split; [intros _ kids2 Hk2; unfold l' in Hk2; cbn [tl_cs] in Hk2; discriminate Hk2 | exact NI].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma map_lupd_eq : forall {X Y} (f : X -> Y) (l : list X) i x y, f x = f y -> map f (lupd l i x) = map f (lupd l i y).
Proof. induction l as [|h t IH]; intros [|i] x y E; cbn; try reflexivity; [rewrite E; reflexivity | f_equal; apply IH; exact E]. Qed.

Lemma PE_BUD_lvl_obj_irrel : forall pf pa ts l1 l2 o os o' os' obs B,
lvl_blocks l1 = lvl_blocks l2 -> PE_BUD pf pa (ts_lvl_obj ts l1 o os obs) B -> PE_BUD pf pa (ts_lvl_obj ts l2 o' os' obs) B.
Proof.
intros pf pa ts l1 l2 o os o' os' obs B E H. unfold PE_BUD, tstate_blocks, ts_lvl_obj in *. cbn [t_pbs t_objbs t_levels t_depth] in *.
rewrite (map_lupd_eq lvl_blocks (t_levels ts) (t_depth ts) l2 l1 (eq_sym E)). exact H.
Qed.
Lemma PE_BUD_lvl_irrel : forall pf pa ts l1 l2 B,
lvl_blocks l1 = lvl_blocks l2 -> PE_BUD pf pa (ts_lvl ts l1) B -> PE_BUD pf pa (ts_lvl ts l2) B.
Proof.
intros pf pa ts l1 l2 B E H. unfold PE_BUD, tstate_blocks, ts_lvl in *. cbn [t_pbs t_objbs t_levels t_depth] in *.
rewrite (map_lupd_eq lvl_blocks (t_levels ts) (t_depth ts) l2 l1 (eq_sym E)). exact H.
Qed.

Lemma ledger_open_S : forall levels n l, nth_error levels n = Some l -> ledger_open levels (S n) = ledger_open levels n + phi_open l.
Proof.
induction levels as [|h t IH]; intros n l H; [destruct n; discriminate|].
assert (Z0 : forall ls, ledger_open ls 0 = 0) by (intros [|? ?]; reflexivity).
destruct n as [|n]; cbn in H; [injection H as ->; change (ledger_open (l :: t) 1) with (phi_open l + ledger_open t 0); rewrite !Z0; lia|].
change (ledger_open (h :: t) (S (S n))) with (phi_open h + ledger_open t (S n)). rewrite (IH n l H).
change (ledger_open (h :: t) (S n)) with (phi_open h + ledger_open t n). lia.
Qed.

Lemma BOK_push : forall pf pa ts B n l stp,
nth_error (t_levels ts) (t_depth ts) = Some l ->
(S (t_depth ts) < length (t_levels ts))%nat ->
(forall l1, nth_error (t_levels ts) (S (t_depth ts)) = Some l1 -> lvl_blocks l1 = []) ->
lvl_closed l = false -> zin stp [ST_array_add; ST_ovadd] = true ->
BOK pf pa ts B n ->
BOK pf pa (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B n.
Proof.
intros pf pa ts B n l stp Hl Hd1 Hcl1 Hop Hz (H1 & H2 & H3 & H4 & H5).
set (lp := TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
set (ln := TL ST_eatws ST_start 0 None [] 0 []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (nth_error (t_levels ts) (S (t_depth ts))) as [l1|] eqn:Hl1; [| apply nth_error_None in Hl1; lia].
specialize (Hcl1 l1 eq_refl).
assert (Eblk : map lvl_blocks (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln) = map lvl_blocks (t_levels ts)).
{ rewrite (map_lupd_same lvl_blocks (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln l1);
[| rewrite nth_error_lupd_neq by lia; exact Hl1 | rewrite Hcl1; reflexivity].
apply (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) lp l Hl). reflexivity. }
assert (Hblk : tstate_blocks (ts_push ts lp) = tstate_blocks ts).
{ unfold tstate_blocks, ts_push; cbn [t_pbs t_objbs t_levels t_depth]. fold ln. rewrite Eblk. reflexivity. }
assert (Eln : phi_open ln = 0) by reflexivity.
assert (Clp : lvl_closed lp = false) by (apply lvl_closed_open_st; exact Hz).
assert (Elp : phi_open lp = phi_open l) by (unfold phi_open; rewrite Clp, Hop; reflexivity).
assert (Eled : ledger_open (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln) (S (S (t_depth ts))) = ledger_open (t_levels ts) (S (t_depth ts))).
{ rewrite (ledger_open_S _ (S (t_depth ts)) ln) by (apply nth_error_lupd_eq; rewrite lupd_length; exact Hd1).
rewrite ledger_open_lupd_out by lia.
rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l lp Hl (Nat.lt_succ_diag_r _)). lia. }
split.
{ unfold bneed in *. rewrite Hblk. unfold ts_push; cbn [t_levels t_depth t_pbs]. fold ln. rewrite Eled. exact H1. }
split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
unfold ts_push; cbn [t_levels t_depth]. fold ln. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (S (t_depth ts))) as [-> | N1].
- rewrite nth_error_lupd_eq in Hn by (rewrite lupd_length; exact Hd1). injection Hn as <-. split; [rewrite Eln; lia|]. split; [intros _ kids Hk; discriminate Hk|]. split; [intros _ kids Hk; discriminate Hk | apply Forall_nil].
- rewrite nth_error_lupd_neq in Hn by congruence.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | N0].
+ rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & OI & NI).
split; [rewrite Elp; exact P0|]. split; [intros _ kids Hk; exact (AI Hop kids Hk)|]. split; [intros _ kids Hk; exact (OI Hop kids Hk) | exact NI].
+ rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li ltac:(lia) Hn).
Qed.

Lemma BOK_set_x : forall pf pa ts B n co' x', t_co ts <= co' -> BOK pf pa ts B n -> BOK pf pa (ts_set_x ts co' x') B n.
Proof.
intros pf pa ts B n co' x' Hco (H1 & H2 & H3 & H4 & H5). unfold ts_set_x.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [eapply pb_inv_mono; [exact H4 | cbn [t_co]; lia] | exact H5].
Qed.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import QlKV.Mq2. Import QrQv.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Pins.
Variable segs : list Segment.
Variable fn : fnaddrs.
Lemma jfresh_scalar48 : forall s m BS p rc, jval segs fn s m BS p rc -> length BS = 1%nat -> (s = Sbool /\ jfresh s BS 8) \/ (s = Sdouble false /\ jfresh s BS 9) \/ (s <> Sbool /\ s <> Sdouble false).
Proof.
intros s m BS p rc J L. destruct s as [|ud| |h|k|k]; try (right; right; split; discriminate).
- left. split; [reflexivity|]. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (b & junk & -> & _)). subst BS.
destruct PBS as [|x PBS]; [reflexivity | cbn in L; lia].
- destruct ud; [right; right; split; discriminate|]. right; left. split; [reflexivity|].
cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (bits & -> & _)). subst BS.
destruct PBS as [|x PBS]; [reflexivity | cbn in L; lia].
Qed.
Lemma jfresh_bool : forall m BS p rc, jval segs fn Sbool m BS p rc -> length BS = 1%nat -> jfresh Sbool BS 8.
Proof. intros m BS p rc J L. destruct (jfresh_scalar48 _ _ _ _ _ J L) as [[_ H] | [[E _] | [E _]]]; [exact H | discriminate E | exfalso; apply E; reflexivity]. Qed.
Lemma jfresh_dbl : forall m BS p rc, jval segs fn (Sdouble false) m BS p rc -> length BS = 1%nat -> jfresh (Sdouble false) BS 9.
Proof. intros m BS p rc J L. destruct (jfresh_scalar48 _ _ _ _ _ J L) as [[E _] | [[_ H] | [_ E]]]; [discriminate E | exact H | exfalso; apply E; reflexivity]. Qed.
Lemma jfresh_int : forall m BS p rc, jval segs fn Sint m BS p rc -> length BS = 1%nat -> jfresh Sint BS 20.
Proof.
intros m BS p rc J L. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (cty & v & junk & -> & _)). subst BS.
destruct PBS as [|x PBS]; [reflexivity | cbn in L; lia].
Qed.

Lemma jfresh_dbls : forall p ud n, 0 <= n -> jfresh (Sdouble true) [(p, 48); (ud, n + 1)] (16 + n).
Proof. intros p ud n H. replace (16 + n) with (16 + Z.max 0 (n + 1 - 1)) by lia. apply jtx_dbl_ud. Qed.
End Pins.

End RC__1.
End Mq3.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition K_ev (pf : pe_fix) : Z := 1.
Lemma K_ev_pos : forall pf, 1 <= K_ev pf. Proof. intros pf. unfold K_ev. lia. Qed.

Definition lvl_closed (l : tlevel) : bool := (tl_ss l =? ST_finish) && negb (zin (tl_st l) [ST_array_add; ST_ovadd]).
Definition phi_open (l : tlevel) : Z := if lvl_closed l then 0 else phi_level l.

Lemma lvl_closed_open_ss : forall l, tl_ss l <> ST_finish -> lvl_closed l = false.
Proof. intros l H. unfold lvl_closed. replace (tl_ss l =? ST_finish) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.
Lemma lvl_closed_open_st : forall l, zin (tl_st l) [ST_array_add; ST_ovadd] = true -> lvl_closed l = false.
Proof. intros l H. unfold lvl_closed. rewrite H. apply andb_false_r. Qed.

Lemma lvl_closed_keep : forall l st' c cs cbs nm nbs, zin st' [ST_array_add; ST_ovadd] = false -> lvl_closed l = true -> lvl_closed (TL st' (tl_ss l) c cs cbs nm nbs) = true.
Proof. intros l st' c cs cbs nm nbs Hz H. unfold lvl_closed in *. cbn [tl_ss tl_st]. apply andb_true_iff in H as [H _]. rewrite H, Hz. reflexivity. Qed.
Lemma lvl_closed_fin : forall st' c cs cbs nm nbs, zin st' [ST_array_add; ST_ovadd] = false -> lvl_closed (TL st' ST_finish c cs cbs nm nbs) = true.
Proof. intros st' c cs cbs nm nbs Hz. unfold lvl_closed. cbn [tl_ss tl_st]. rewrite Hz. reflexivity. Qed.

Fixpoint ledger_open (levels : list tlevel) (n : nat) : Z :=
match n, levels with
| O, _ => 0
| S n', l :: rest => phi_open l + ledger_open rest n'
| S _, [] => 0
end.

Definition lvl_disc (pf : pe_fix) (l : tlevel) : Prop :=
0 <= phi_open l /\
(lvl_closed l = false -> forall kids, tl_cs l = Some (Sarr kids) -> arr_inv (arr_capA (tl_cbs l)) (Z.of_nat (length kids))) /\

(lvl_closed l = false -> forall kids, tl_cs l = Some (Sobj kids) -> In (obj_capA (tl_cbs l)) lf_sizes) /\

Forall (fun b : blk => snd b <= Z.max 0 (pf_len pf) + 1) (tl_nbs l).

Definition bneed (pf : pe_fix) (pa : pe_fixA) (ts : tstate) (n : nat) : Z :=
K_ev pf * Z.of_nat n + ledger_open (t_levels ts) (S (t_depth ts)) + PhiPB (pf_len pf) (pb_capA (t_pbs ts))
+ K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa.

Definition BOK (pf : pe_fix) (pa : pe_fixA) (ts : tstate) (B : bud) (n : nat) : Prop :=
bneed pf pa ts n <= bB B /\ Z.of_nat n + pa_dslack pa <= bD B /\
0 <= PhiPB (pf_len pf) (pb_capA (t_pbs ts)) /\ pb_inv (pb_capA (t_pbs ts)) (t_co ts) /\
(forall i l, (i <= t_depth ts)%nat -> nth_error (t_levels ts) i = Some l -> lvl_disc pf l).

Lemma ledger_open_nonneg : forall levels n, (forall i l, (i < n)%nat -> nth_error levels i = Some l -> 0 <= phi_open l) -> 0 <= ledger_open levels n.
Proof.
induction levels as [|h t IH]; intros n H; [destruct n; cbn; lia|].
destruct n as [|n]; cbn; [lia|].
pose proof (H 0%nat h ltac:(lia) eq_refl). pose proof (IH n ltac:(intros i l Hi Hn; apply (H (S i) l); [lia | exact Hn])). lia.
Qed.

Lemma ledger_open_lupd : forall levels n i l l',
nth_error levels i = Some l -> (i < n)%nat -> ledger_open (lupd levels i l') n = ledger_open levels n - phi_open l + phi_open l'.
Proof.
induction levels as [|h t IH]; intros n i l l' Hn Hi; [destruct i; discriminate|].
destruct i as [|i]; cbn in Hn.
- injection Hn as ->. destruct n as [|n]; [lia|]. cbn. lia.
- destruct n as [|n]; [lia|]. cbn. rewrite (IH n i l l' Hn ltac:(lia)). lia.
Qed.

Lemma ledger_open_lupd_out : forall levels n i l', (n <= i)%nat -> ledger_open (lupd levels i l') n = ledger_open levels n.
Proof.
induction levels as [|h t IH]; intros n i l' Hi; [destruct i; reflexivity|].
destruct n as [|n]; [destruct i; reflexivity|]. destruct i as [|i]; [lia|]. cbn. rewrite (IH n i l' ltac:(lia)). reflexivity.
Qed.

Lemma BOK_ledger_nonneg : forall pf pa ts B n, BOK pf pa ts B n -> 0 <= ledger_open (t_levels ts) (S (t_depth ts)).
Proof. intros pf pa ts B n (_ & _ & _ & _ & D). apply ledger_open_nonneg. intros i l Hi Hn. exact (proj1 (D i l ltac:(lia) Hn)). Qed.

Lemma BOK_weaken : forall pf pa ts B n n', (n' <= n)%nat -> BOK pf pa ts B n -> BOK pf pa ts B n'.
Proof.
intros pf pa ts B n n' Hn (H1 & H2 & H3). pose proof (K_ev_pos pf).
pose proof (Z.mul_le_mono_nonneg_l (Z.of_nat n') (Z.of_nat n) (K_ev pf) ltac:(lia) ltac:(lia)).
unfold BOK, bneed in *. split; [lia|]. split; [lia | exact H3].
Qed.

Lemma BOK_mono : forall pf pa ts B B' n, bB B <= bB B' -> bD B <= bD B' -> BOK pf pa ts B n -> BOK pf pa ts B' n.
Proof. intros pf pa ts B B' n HB HD (H1 & H2 & H3). unfold BOK in *. split; [lia|]. split; [lia | exact H3]. Qed.

Lemma BOK_pay : forall pf pa ts B B' n c {C}, BOK pf pa ts B (S (Z.to_nat C + n)) -> c <= C -> bB B - c <= bB B' -> bD B - 1 <= bD B' -> BOK pf pa ts B' n.
Proof.
intros pf pa ts B B' n c C (H1 & H2 & H3) Hc HB HD. unfold BOK, bneed, K_ev in *. split; [lia|]. split; [lia | exact H3].
Qed.

Lemma BOK_drop : forall pf pa ts B n C, BOK pf pa ts B (S (Z.to_nat C + n)) -> BOK pf pa ts B n.
Proof. intros pf pa ts B n C H. eapply BOK_weaken; [| exact H]. lia. Qed.

Lemma BOK_weak : forall pf pa ts B n, BOK pf pa ts B n -> PE_BUD pf pa ts B.
Proof.
intros pf pa ts B n H. pose proof (BOK_ledger_nonneg _ _ _ _ _ H) as L0. destruct H as (H1 & H2 & H3 & _).
pose proof (K_ev_pos pf). pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)). unfold bneed in H1. split; [lia | lia].
Qed.

Lemma BOK_set_co : forall pf pa ts B n co', t_co ts <= co' -> BOK pf pa ts B n -> BOK pf pa (ts_set_co ts co') B n.
Proof.
intros pf pa ts B n co' Hco (H1 & H2 & H3 & H4 & H5). unfold ts_set_co.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [eapply pb_inv_mono; [exact H4 | cbn [t_co]; lia] | exact H5].
Qed.

Lemma BOK_lvl_restate : forall pf pa ts B n l st' ss',
nth_error (t_levels ts) (t_depth ts) = Some l ->
(lvl_closed l = true -> lvl_closed (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) = true) ->
BOK pf pa ts B n ->
BOK pf pa (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B n.
Proof.
intros pf pa ts B n l st' ss' Hl Hcl (H1 & H2 & H3 & H4 & H5).
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & OI & NI).
assert (Hphi : 0 <= phi_open l' <= phi_open l).
{ unfold phi_open in *. fold l' in Hcl. change (phi_level l') with (phi_level l).
destruct (lvl_closed l') eqn:E1; destruct (lvl_closed l) eqn:E2; try lia; specialize (Hcl eq_refl); discriminate Hcl. }
assert (Hblk : tstate_blocks (ts_lvl ts l') = tstate_blocks ts).
{ unfold tstate_blocks, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth]. rewrite (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) l' l Hl eq_refl). reflexivity. }
split.
{ unfold bneed in *. rewrite Hblk. unfold ts_lvl; cbn [t_levels t_depth t_pbs]. rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)). lia. }
split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [lia|].
assert (Hopl : lvl_closed l' = false -> lvl_closed l = false) by (intros Hop; destruct (lvl_closed l) eqn:E; [| reflexivity]; fold l' in Hcl; rewrite (Hcl eq_refl) in Hop; discriminate Hop).
split; [intros Hop kids Hcs; apply AI; [exact (Hopl Hop) | exact Hcs]|]. split; [intros Hop kids Hcs; apply (OI (Hopl Hop) kids); exact Hcs | exact NI].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma BOK_memappend : forall pf pa ts B k pb buf cap bpos n,
BOK pf pa ts B k -> t_pbs ts = [(pb, PB_SZ); (buf, cap)] -> 0 <= pa_bslack pa ->
0 <= bpos -> 0 <= n -> bpos + n <= t_co ts + 1 -> 0 <= t_co ts <= pf_len pf -> pf_len pf < 2^26 ->
memappend_costX cap bpos n <= bB B /\
(forall buf' B', bB B - memappend_costX2 cap bpos n <= bB B' -> bD B <= bD B' ->
BOK pf pa (ts_pbs ts [(pb, PB_SZ); (buf', memappend_cap2 cap bpos n)]) B' k).
Proof.
intros pf pa ts B k pb buf cap bpos n H E BSL Hb Hn Hbn Hco Hlen.
pose proof (BOK_ledger_nonneg _ _ _ _ _ H) as L0. destruct H as (H1 & H2 & H4 & H5 & H6).
unfold bneed in H1. rewrite E in H1, H4, H5. unfold pb_capA in H1, H4, H5. cbn [nth snd] in H1, H4, H5.
destruct (potential_step_memappend2 (pf_len pf) cap bpos n (t_co ts) H5 Hb Hn Hbn ltac:(lia) Hlen) as (P1 & P2 & P3 & P4).
pose proof (Zle_0_nat (length (tstate_blocks ts))) as Hnb. pose proof (K_ev_pos pf) as KE.
pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat k) ltac:(lia) ltac:(lia)) as KN. unfold K_free, K_exit in *.
split; [lia|]. intros buf' B' HB HD.
assert (Hblk : length (tstate_blocks (ts_pbs ts [(pb, PB_SZ); (buf', memappend_cap2 cap bpos n)])) = length (tstate_blocks ts)).
{ unfold tstate_blocks, ts_pbs; cbn [t_pbs t_objbs t_levels]. rewrite E. rewrite !length_app. reflexivity. }
unfold BOK, bneed. rewrite Hblk. unfold ts_pbs; cbn [t_levels t_depth t_pbs t_co]. unfold pb_capA. cbn [nth snd].
split; [unfold K_free, K_exit; lia|]. split; [lia|]. split; [exact P3|]. split; [exact P2 | exact H6].
Qed.

Lemma BOK_memappend_fail : forall pf pa ts B B' k pb buf cap bpos n,
BOK pf pa ts B k -> t_pbs ts = [(pb, PB_SZ); (buf, cap)] ->
0 <= bpos -> 0 <= n -> bpos + n <= t_co ts + 1 -> 0 <= t_co ts <= pf_len pf -> pf_len pf < 2^26 ->
bB B - memappend_costX2 cap bpos n <= bB B' -> bD B <= bD B' ->
PE_BUD pf pa ts B'.
Proof.
intros pf pa ts B B' k pb buf cap bpos n H E Hb Hn Hbn Hco Hlen HB HD.
pose proof (BOK_ledger_nonneg _ _ _ _ _ H) as L0. destruct H as (H1 & H2 & H4 & H5 & H6).
unfold bneed in H1. rewrite E in H1, H4, H5. unfold pb_capA in H1, H4, H5. cbn [nth snd] in H1, H4, H5.
destruct (potential_step_memappend2 (pf_len pf) cap bpos n (t_co ts) H5 Hb Hn Hbn ltac:(lia) Hlen) as (P1 & P2 & P3 & P4).
pose proof (memappend_costX2_le cap bpos n ltac:(destruct H5; lia)) as LE.
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat k) ltac:(lia) ltac:(lia)) as KN.
split; lia.
Qed.

Lemma tstate_blocks_lvl_length : forall ts l l',
nth_error (t_levels ts) (t_depth ts) = Some l ->
Z.of_nat (length (tstate_blocks (ts_lvl ts l'))) = Z.of_nat (length (tstate_blocks ts)) - Z.of_nat (length (lvl_blocks l)) + Z.of_nat (length (lvl_blocks l')).
Proof.
intros ts l l' Hl. unfold tstate_blocks, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (lupd_split _ _ _ l' Hl), (concat_split _ _ _ Hl). rewrite !length_app. lia.
Qed.

Lemma ledger_open_ge : forall levels n i l,
nth_error levels i = Some l -> (i < n)%nat -> (forall j lj, (j < n)%nat -> nth_error levels j = Some lj -> 0 <= phi_open lj) ->
phi_open l <= ledger_open levels n.
Proof.
intros levels n i l Hn Hi H.
pose proof (ledger_open_lupd levels n i l lvl_reset Hn Hi) as E. change (phi_open lvl_reset) with 0 in E.
assert (0 <= ledger_open (lupd levels i lvl_reset) n).
{ apply ledger_open_nonneg. intros j lj Hj Hnj. destruct (PeanoNat.Nat.eq_dec j i) as [-> | NE].
- rewrite nth_error_lupd_eq in Hnj by (apply nth_error_Some; rewrite Hn; discriminate). injection Hnj as <-. cbn. lia.
- rewrite nth_error_lupd_neq in Hnj by congruence. exact (H j lj Hj Hnj). }
lia.
Qed.

Lemma BOK_arr_close : forall pf pa ts B n l kids,
BOK pf pa ts B n -> 0 <= pa_bslack pa ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some (Sarr kids) -> lvl_closed l = false ->
arr_shrink_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B /\
(forall B' cbs2 st', zin st' [ST_array_add; ST_ovadd] = false -> length cbs2 = length (tl_cbs l) ->
bB B - arr_shrink_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
BOK pf pa (ts_lvl ts (TL st' ST_finish (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l))) B' n).
Proof.
intros pf pa ts B n l kids H BSL Hl Hcs Hop.
pose proof H as (H1 & H2 & H3 & H4 & H5).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & _ & NI). specialize (AI Hop kids Hcs).
assert (Ephi : phi_open l = PhiA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) + RA).
{ unfold phi_open. rewrite Hop. unfold phi_level. rewrite Hcs. reflexivity. }
pose proof (potential_step_arr_close _ _ AI) as STEP.
pose proof (ledger_open_ge (t_levels ts) (S (t_depth ts)) (t_depth ts) l Hl (Nat.lt_succ_diag_r _)
ltac:(intros j lj Hj Hnj; exact (proj1 (H5 j lj ltac:(lia) Hnj)))) as GE.
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)) as KN.
pose proof (Zle_0_nat (length (tstate_blocks ts))) as Hnb.
unfold bneed in H1. unfold K_free, K_exit in *.
split; [lia|]. intros B' cbs2 st' Hz' Hlen HB HD.
set (l' := TL st' ST_finish (tl_cur l) (tl_cs l) cbs2 (tl_name l) (tl_nbs l)).
assert (Hcl' : lvl_closed l' = true) by (apply lvl_closed_fin; exact Hz').
assert (Hphi' : phi_open l' = 0) by (unfold phi_open; rewrite Hcl'; reflexivity).
pose proof (tstate_blocks_lvl_length ts l l' Hl) as Hblk.
assert (Hlb : length (lvl_blocks l') = length (lvl_blocks l)) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite !length_app, Hlen; reflexivity).
rewrite Hlb in Hblk.
unfold BOK, bneed. rewrite Hblk. unfold ts_lvl; cbn [t_levels t_depth t_pbs t_co].
rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)), Hphi'.
split; [unfold K_free, K_exit; lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|].
intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [rewrite Hphi'; lia|].
split; [intros Hss; rewrite Hcl' in Hss; discriminate Hss|]. split; [intros Hss; rewrite Hcl' in Hss; discriminate Hss | exact NI].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma tstate_blocks_lvl_obj_length : forall ts l l' o os obs,
nth_error (t_levels ts) (t_depth ts) = Some l ->
Z.of_nat (length (tstate_blocks (ts_lvl_obj ts l' o os obs))) =
Z.of_nat (length (tstate_blocks ts)) - Z.of_nat (length (lvl_blocks l)) - Z.of_nat (length (t_objbs ts)) + Z.of_nat (length (lvl_blocks l')) + Z.of_nat (length obs).
Proof.
intros ts l l' o os obs Hl. unfold tstate_blocks, ts_lvl_obj; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (lupd_split _ _ _ l' Hl), (concat_split _ _ _ Hl). rewrite !length_app. lia.
Qed.

Lemma PhiA_nonneg : forall cap len, arr_inv cap len -> 0 <= PhiA cap len.
Proof. intros cap len (H32 & Hl & Hc). unfold PhiA. lia. Qed.

Lemma BOK_arr_add : forall pf pa ts B n l kids,
BOK pf pa ts B (S (Z.to_nat 1280 + n)) -> 0 <= pa_bslack pa ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some (Sarr kids) -> lvl_closed l = false ->
arr_add_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B /\
(forall B', bB B - arr_add_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' -> PE_BUD pf pa ts B') /\
(forall B' cbs2 st' ss' obj' objs', ss' <> ST_finish -> length cbs2 = (length (tl_cbs l) + length (t_objbs ts))%nat ->
arr_grownA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) (arr_capA cbs2) ->
bB B - arr_add_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B' n).
Proof.
intros pf pa ts B n l kids H BSL Hl Hcs Hop.
pose proof H as (H1 & H2 & H3 & H4 & H5).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & _ & NI). specialize (AI Hop kids Hcs).
assert (Ephi : phi_open l = PhiA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) + RA).
{ unfold phi_open. rewrite Hop. unfold phi_level. rewrite Hcs. reflexivity. }
pose proof (ledger_open_ge (t_levels ts) (S (t_depth ts)) (t_depth ts) l Hl (Nat.lt_succ_diag_r _)
ltac:(intros j lj Hj Hnj; exact (proj1 (H5 j lj ltac:(lia) Hnj)))) as GE.
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)) as KN.
pose proof (Zle_0_nat (length (tstate_blocks ts))) as Hnb.
unfold bneed in H1. assert (KU : K_ev pf * Z.of_nat (S (Z.to_nat 1280 + n)) = K_ev pf * Z.of_nat n + 1281) by (unfold K_ev; lia). rewrite KU in H1. clear KU.
assert (COSTB : arr_add_costA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) <= PhiA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) + RA + K_arr).
{ destruct AI as (A32 & Alen & Acap). unfold arr_add_costA, PhiA, RA, K_arr. destruct (Z.of_nat (length kids) + 1 <? arr_capA (tl_cbs l)) eqn:E; [lia|]. apply Z.ltb_ge in E. lia. }
unfold K_arr in COSTB. unfold K_free, K_exit in *.
split; [lia|]. split.
{ intros B' HB HD. split; [unfold K_free, K_exit; lia | lia]. }
intros B' cbs2 st' ss' obj' objs' Hss' Hlen GR HB HD.
set (l' := TL st' ss' (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs2 (tl_name l) (tl_nbs l)).
destruct (potential_step_arr_add _ _ _ AI GR) as [STEP AI'].
assert (Elen : Z.of_nat (length (kids ++ [t_objs ts])) = Z.of_nat (length kids) + 1) by (rewrite length_app; cbn [length]; lia).
assert (Hphi' : phi_open l' = PhiA (arr_capA cbs2) (Z.of_nat (length kids) + 1) + RA).
{ unfold phi_open. rewrite (lvl_closed_open_ss l' Hss'). unfold phi_level, l'. cbn [tl_cs tl_cbs]. rewrite Elen. reflexivity. }
pose proof (PhiA_nonneg _ _ AI') as PN.
pose proof (tstate_blocks_lvl_obj_length ts l l' obj' objs' [] Hl) as Hblk.
assert (Hlb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length (lvl_blocks l)) + Z.of_nat (length (t_objbs ts))).
{ unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite !length_app, Hlen. lia. }
cbn [length] in Hblk.
unfold BOK, bneed. rewrite Hblk. unfold ts_lvl_obj; cbn [t_levels t_depth t_pbs t_co].
rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)), Hphi'.
unfold RA, K_arr in *.
split; [unfold K_free, K_exit; lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|].
intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [rewrite Hphi'; unfold RA; lia|].
split; [intros _ kids2 Hk2; unfold l' in Hk2 |- *; cbn [tl_cs tl_cbs] in Hk2 |- *; injection Hk2 as <-; rewrite Elen; exact AI'|].
split; [intros _ kids2 Hk2; unfold l' in Hk2; cbn [tl_cs] in Hk2; discriminate Hk2 | exact NI].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma map_lupd_eq : forall {X Y} (f : X -> Y) (l : list X) i x y, f x = f y -> map f (lupd l i x) = map f (lupd l i y).
Proof. induction l as [|h t IH]; intros [|i] x y E; cbn; try reflexivity; [rewrite E; reflexivity | f_equal; apply IH; exact E]. Qed.

Lemma PE_BUD_lvl_obj_irrel : forall pf pa ts l1 l2 o os o' os' obs B,
lvl_blocks l1 = lvl_blocks l2 -> PE_BUD pf pa (ts_lvl_obj ts l1 o os obs) B -> PE_BUD pf pa (ts_lvl_obj ts l2 o' os' obs) B.
Proof.
intros pf pa ts l1 l2 o os o' os' obs B E H. unfold PE_BUD, tstate_blocks, ts_lvl_obj in *. cbn [t_pbs t_objbs t_levels t_depth] in *.
rewrite (map_lupd_eq lvl_blocks (t_levels ts) (t_depth ts) l2 l1 (eq_sym E)). exact H.
Qed.
Lemma PE_BUD_lvl_irrel : forall pf pa ts l1 l2 B,
lvl_blocks l1 = lvl_blocks l2 -> PE_BUD pf pa (ts_lvl ts l1) B -> PE_BUD pf pa (ts_lvl ts l2) B.
Proof.
intros pf pa ts l1 l2 B E H. unfold PE_BUD, tstate_blocks, ts_lvl in *. cbn [t_pbs t_objbs t_levels t_depth] in *.
rewrite (map_lupd_eq lvl_blocks (t_levels ts) (t_depth ts) l2 l1 (eq_sym E)). exact H.
Qed.

Lemma ledger_open_S : forall levels n l, nth_error levels n = Some l -> ledger_open levels (S n) = ledger_open levels n + phi_open l.
Proof.
induction levels as [|h t IH]; intros n l H; [destruct n; discriminate|].
assert (Z0 : forall ls, ledger_open ls 0 = 0) by (intros [|? ?]; reflexivity).
destruct n as [|n]; cbn in H; [injection H as ->; change (ledger_open (l :: t) 1) with (phi_open l + ledger_open t 0); rewrite !Z0; lia|].
change (ledger_open (h :: t) (S (S n))) with (phi_open h + ledger_open t (S n)). rewrite (IH n l H).
change (ledger_open (h :: t) (S n)) with (phi_open h + ledger_open t n). lia.
Qed.

Lemma BOK_push : forall pf pa ts B n l stp,
nth_error (t_levels ts) (t_depth ts) = Some l ->
(S (t_depth ts) < length (t_levels ts))%nat ->
(forall l1, nth_error (t_levels ts) (S (t_depth ts)) = Some l1 -> lvl_blocks l1 = []) ->
lvl_closed l = false -> zin stp [ST_array_add; ST_ovadd] = true ->
BOK pf pa ts B n ->
BOK pf pa (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B n.
Proof.
intros pf pa ts B n l stp Hl Hd1 Hcl1 Hop Hz (H1 & H2 & H3 & H4 & H5).
set (lp := TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
set (ln := TL ST_eatws ST_start 0 None [] 0 []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (nth_error (t_levels ts) (S (t_depth ts))) as [l1|] eqn:Hl1; [| apply nth_error_None in Hl1; lia].
specialize (Hcl1 l1 eq_refl).
assert (Eblk : map lvl_blocks (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln) = map lvl_blocks (t_levels ts)).
{ rewrite (map_lupd_same lvl_blocks (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln l1);
[| rewrite nth_error_lupd_neq by lia; exact Hl1 | rewrite Hcl1; reflexivity].
apply (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) lp l Hl). reflexivity. }
assert (Hblk : tstate_blocks (ts_push ts lp) = tstate_blocks ts).
{ unfold tstate_blocks, ts_push; cbn [t_pbs t_objbs t_levels t_depth]. fold ln. rewrite Eblk. reflexivity. }
assert (Eln : phi_open ln = 0) by reflexivity.
assert (Clp : lvl_closed lp = false) by (apply lvl_closed_open_st; exact Hz).
assert (Elp : phi_open lp = phi_open l) by (unfold phi_open; rewrite Clp, Hop; reflexivity).
assert (Eled : ledger_open (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln) (S (S (t_depth ts))) = ledger_open (t_levels ts) (S (t_depth ts))).
{ rewrite (ledger_open_S _ (S (t_depth ts)) ln) by (apply nth_error_lupd_eq; rewrite lupd_length; exact Hd1).
rewrite ledger_open_lupd_out by lia.
rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l lp Hl (Nat.lt_succ_diag_r _)). lia. }
split.
{ unfold bneed in *. rewrite Hblk. unfold ts_push; cbn [t_levels t_depth t_pbs]. fold ln. rewrite Eled. exact H1. }
split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
unfold ts_push; cbn [t_levels t_depth]. fold ln. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (S (t_depth ts))) as [-> | N1].
- rewrite nth_error_lupd_eq in Hn by (rewrite lupd_length; exact Hd1). injection Hn as <-. split; [rewrite Eln; lia|]. split; [intros _ kids Hk; discriminate Hk|]. split; [intros _ kids Hk; discriminate Hk | apply Forall_nil].
- rewrite nth_error_lupd_neq in Hn by congruence.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | N0].
+ rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & OI & NI).
split; [rewrite Elp; exact P0|]. split; [intros _ kids Hk; exact (AI Hop kids Hk)|]. split; [intros _ kids Hk; exact (OI Hop kids Hk) | exact NI].
+ rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li ltac:(lia) Hn).
Qed.

Lemma BOK_set_x : forall pf pa ts B n co' x', t_co ts <= co' -> BOK pf pa ts B n -> BOK pf pa (ts_set_x ts co' x') B n.
Proof.
intros pf pa ts B n co' x' Hco (H1 & H2 & H3 & H4 & H5). unfold ts_set_x.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [eapply pb_inv_mono; [exact H4 | cbn [t_co]; lia] | exact H5].
Qed.

End RC__1.
