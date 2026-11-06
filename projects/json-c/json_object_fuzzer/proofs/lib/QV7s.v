(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QCcH Q0Ek Qtgi QjDH Qsw7 QRUw QkMG QG8z Qdyh QLbz Q7UD QlKV QrQv QEUF QdGy Q63E Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QRUw.Mq0 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import Q7UD QlKV.Mq2 QrQv.Mq2 QEUF.Mq1 QdGy.Mq3 Q63E.Mq1 QdGy.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma jtext_nonneg : forall st g, 0 <= g -> 0 <= jtext st g. Proof. intros st g H. unfold jtext. destruct (jlive st); lia. Qed.
Lemma jtext_dead : forall st g, jlive st = false -> jtext st g = 0. Proof. intros st g H. unfold jtext. rewrite H. reflexivity. Qed.
Lemma jpi_eatws : forall ss, jpi ST_eatws ss = jpi0 ss. Proof. reflexivity. Qed.
Lemma jpi_self : forall ss, jpi ss ss = jpi0 ss. Proof. intros ss. unfold jpi. destruct (ss =? ST_eatws); reflexivity. Qed.
Lemma PBJ_open : forall m ts k a, PBJ m ts k a -> exists g, 0 <= g /\ PBOKat m ts g /\ g <= t_co ts + k /\ JL ts g a.
Proof. intros m ts k a (g & P & Hg & J). exists g. split; [exact (PBOKat_nonneg _ _ _ P)|]. split; [exact P|]. split; [exact Hg | exact J]. Qed.

Lemma PBJ_restate_g : forall m' ts ts' l l' g k' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a -> PBOK m' ts' k' -> k' <= kk ->
jtext (tl_st l') (t_co ts' + k') + jpi (tl_st l') (tl_ss l') <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m' ts ts' l l' g k' kk a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J P Hk H. exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
exact (JL_lvl_restate ts ts' l l' g _ a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J H).
Qed.

Lemma PBJ_restate : forall m m' ts ts' l l' k k' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive (tl_st l') = false ->
jpi (tl_st l') (tl_ss l') <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l l' k k' kk a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz PJ P Hk Hd H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
eapply (PBJ_restate_g m' ts ts' l l' g k' kk a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J P Hk).
rewrite (jtext_dead _ _ Hd). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_attach : forall m m' ts ts' l st' ss' r sh BS nm k k' kk a a' w,
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) (TL st' ss' r (Some sh) BS nm []) -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive st' = false -> jfresh sh BS w ->
w + jpi st' ss' <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l st' ss' r sh BS nm k k' kk a a' w Hl E1 E2 E3 E4 Hz PJ P Hk Hd JF H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
eapply (JL_lvl ts ts' l _ g _ a a' w Hl E1 E2 E3 E4 (lw_attach st' ss' r sh BS nm w JF) Hz J).
intros w0 _ W0. cbn [tl_st tl_ss]. rewrite (jtext_dead _ _ Hd). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_revalue : forall m m' ts ts' l l' k k' kk a a' dw,
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive (tl_st l') = false ->
(forall w0, lw l = Some w0 -> exists w', lw l' = Some w' /\ w' <= w0 + dw) ->
dw + jpi (tl_st l') (tl_ss l') <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l l' k k' kk a a' dw Hl E1 E2 E3 E4 Hz PJ P Hk Hd HW H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
destruct (JL_jw _ _ _ J) as (W & EW).
assert (Lw : exists w0, lw l = Some w0).
{ destruct ts as [d lv co pb pbs x o os obs]. cbn [t_levels t_depth] in Hl. unfold jw in EW. cbn [t_levels t_depth] in EW.
destruct (jwl lv (S d)) as [A|] eqn:EA; [| discriminate EW]. exact (jwl_nth lv (S d) d l A EA Hl ltac:(lia)). }
destruct Lw as (w0 & Lw0). destruct (HW w0 Lw0) as (w' & Lw' & LE).
eapply (JL_lvl ts ts' l l' g _ a a' w' Hl E1 E2 E3 E4 Lw' Hz J).
intros w1 Lw1 _. rewrite Lw0 in Lw1. injection Lw1 as <-. rewrite (jtext_dead _ _ Hd). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma lw_recbs : forall l st' ss' cbs' s w0, tl_cs l = Some s -> lw l = Some w0 ->
(forall w, jtx s (tl_cbs l) = Some (w, []) -> jtx s cbs' = Some (w, [])) ->
lw (TL st' ss' (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l)) = Some w0.
Proof.
intros l st' ss' cbs' s w0 Hcs Lw JX. unfold lw in *. cbn [tl_cs tl_cbs tl_nbs]. rewrite Hcs in *. cbn [vw] in *.
destruct (jtx s (tl_cbs l)) as [[w [|? ?]]|] eqn:J; try discriminate Lw. rewrite (JX w eq_refl). exact Lw.
Qed.

Lemma lw_aadd : forall l kids os obs cbs' st' ss' w0 b, tl_cs l = Some (Sarr kids) -> lw l = Some w0 -> vw os obs = Some b -> (os = None -> obs = []) ->
(forall w wv, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx_opt os obs = Some (wv, []) -> jtx (Sarr (kids ++ [os])) cbs' = Some (w + (2 + wv), [])) ->
exists w', lw (TL st' ss' (tl_cur l) (Some (Sarr (kids ++ [os]))) cbs' (tl_name l) (tl_nbs l)) = Some w' /\ w' <= w0 + b + 6.
Proof.
intros l kids os obs cbs' st' ss' w0 b Hcs Lw Vb Hn JX. destruct (lw_arr l kids Hcs w0 Lw) as (w & Jw & ->). destruct (vw_kid os obs b Vb Hn) as (wv & Jv & Lv).
exists (w + (2 + wv) + nw (tl_nbs l)). split; [exact (lw_container _ _ _ _ _ _ _ _ (JX w wv Jw Jv)) | unfold NULL_W in Lv; lia].
Qed.

Lemma lw_oadd : forall l kids kids' os obs cbs' st' ss' nm nn w0 b, tl_cs l = Some (Sobj kids) -> lw l = Some w0 -> vw os obs = Some b -> (os = None -> obs = []) ->
tl_nbs l = [(nm, nn)] ->
(forall w wv nm0 nn0, tl_nbs l = [(nm0, nn0)] -> jtx (Sobj kids) (tl_cbs l) = Some (w, []) -> jtx_opt os obs = Some (wv, []) ->
exists w', jtx (Sobj kids') cbs' = Some (w', []) /\ w' <= w + key_w nn0 + wv) ->
exists w', lw (TL st' ss' (tl_cur l) (Some (Sobj kids')) cbs' 0 []) = Some w' /\ w' <= w0 + b + 4.
Proof.
intros l kids kids' os obs cbs' st' ss' nm nn w0 b Hcs Lw Vb Hn Hnbs JX. destruct (lw_obj l kids Hcs w0 Lw) as (w & Jw & ->). destruct (vw_kid os obs b Vb Hn) as (wv & Jv & Lv).
destruct (JX w wv nm nn Hnbs Jw Jv) as (w' & Jw' & Lw'). exists (w' + nw []). split; [exact (lw_container _ _ _ _ _ _ _ _ Jw')|].
rewrite Hnbs. cbn [nw snd]. unfold NULL_W in Lv. lia.
Qed.

Lemma PBJ_add : forall m m' ts ts' l l' k k' kk a a' dw,
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts ->
zin (tl_st l) [ST_array_add; ST_ovadd] = true -> zin (tl_st l') [ST_array_add; ST_ovadd] = false ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive (tl_st l') = false ->
(forall w0 b, lw l = Some w0 -> vw (t_objs ts) (t_objbs ts) = Some b -> exists w', lw l' = Some w' /\ w' <= w0 + b + dw) ->
dw + jpi (tl_st l') (tl_ss l') <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l l' k k' kk a a' dw Hl E1 E2 Hz Hz' PJ P Hk Hd HW H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
destruct J as (W & EW & LW).
assert (X : exists w0 b, lw l = Some w0 /\ vw (t_objs ts) (t_objbs ts) = Some b).
{ destruct ts as [d lv co pb pbs x o os obs]. cbn [t_levels t_depth t_objs t_objbs] in *. unfold jw in EW. cbn [t_levels t_depth t_objs t_objbs] in EW.
rewrite (cur_st_ofJ _ _ l) in EW by exact Hl. unfold ow in EW. rewrite Hz in EW.
destruct (jwl lv (S d)) as [A|] eqn:EA; [| discriminate EW]. destruct (vw os obs) as [b|] eqn:Eb; [| discriminate EW].
destruct (jwl_nth lv (S d) d l A EA Hl ltac:(lia)) as (w0 & Lw0). exists w0, b. split; [exact Lw0 | reflexivity]. }
destruct X as (w0 & b & Lw0 & Eb). destruct (HW w0 b Lw0 Eb) as (w' & Lw' & LE).
eapply (JL_add ts ts' l l' g _ a a' w' Hl E1 E2 Lw' Hz Hz'); [exists W; split; [exact EW | exact LW] |].
intros w1 b1 Lw1 Eb1. rewrite Lw0 in Lw1. injection Lw1 as <-. rewrite Eb in Eb1. injection Eb1 as <-.
rewrite (jtext_dead _ _ Hd). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_restate_at : forall m m' ts ts' l l' k g' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PBJ m ts k a -> PBOKat m' ts' g' -> g' <= t_co ts' + kk ->
jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l l' k g' kk a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz PJ P Hg H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists g'. split; [exact P|]. split; [exact Hg|].
eapply (JL_lvl_restate ts ts' l l' g g' a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_push : forall m m' ts l lp k k' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l -> (S (t_depth ts) < length (t_levels ts))%nat ->
tl_cs lp = tl_cs l -> tl_cbs lp = tl_cbs l -> tl_nbs lp = tl_nbs l ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
PBJ m ts k a -> PBOK m' (ts_push ts lp) k' -> k' <= kk ->
26 <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' (ts_push ts lp) kk a'.
Proof.
intros m m' ts l lp k k' kk a a' Hl Hlen C1 C2 C3 Hz PJ P Hk H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co (ts_push ts lp) + k'). split; [exact P|]. split; [lia|].
eapply (JL_push ts l lp g _ a a' Hl Hlen C1 C2 C3 Hz J). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_pop : forall m m' ts dp l lp k k' kk a,
t_depth ts = S dp -> nth_error (t_levels ts) (S dp) = Some l -> nth_error (t_levels ts) dp = Some lp ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false -> zin (tl_st lp) [ST_array_add; ST_ovadd] = true ->
PBJ m ts k a ->
PBOK m' (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) k' -> k' <= kk ->
jpi (tl_st lp) (tl_ss lp) <= jpi (tl_st l) (tl_ss l) ->
PBJ m' (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) kk a.
Proof.
intros m m' ts dp l lp k k' kk a Hd Hl Hlp Hz Hzp PJ P Hk H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts + k'). split; [unfold PBOK in P; cbn [t_co] in P; exact P|]. split; [cbn [t_co]; lia|].
assert (JP := JL_pop ts dp l lp g a Hd Hl Hlp Hz Hzp J ltac:(pose proof (jtext_nonneg (tl_st l) g G0); lia)).
eapply JL_dead; [| exact JP].
assert (Ec : cur_st (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) = tl_st lp)
by (unfold cur_st; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
rewrite Ec. unfold jlive. cbn [zin existsb] in Hzp |- *. apply orb_prop in Hzp. destruct Hzp as [Hq | Hq]; [| apply orb_prop in Hq; destruct Hq as [Hq | Hq]; [| discriminate Hq]];
apply Z.eqb_eq in Hq; rewrite Hq; reflexivity.
Qed.

Lemma esc_ss_pi : forall st ss c hn, zin st [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = true -> 0 <= ss <= 26 ->
lvl_mode st ss = Some (c, hn) -> jpi0 ss <= 30.
Proof.
intros st ss c hn Hst R Hm.
assert (C : st = ST_string_escape \/ st = ST_escape_unicode \/ st = ST_esc_need_escape \/ st = ST_esc_need_u).
{ cbn [zin existsb] in Hst. repeat (apply orb_prop in Hst as [Hst | Hst]; [apply Z.eqb_eq in Hst; auto |]). discriminate Hst. }
assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
destruct C as [-> | [-> | [-> | ->]]]; do 27 (destruct k as [|k]; [vm_compute in Hm; first [discriminate Hm | vm_compute; discriminate] |]); lia.
Qed.

Lemma eatws_ss_dead : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_eatws ss = Some (c, hn) -> jlive ss = false.
Proof.
intros ss c hn R Hm.
assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in Hm; first [discriminate Hm | reflexivity] |]); lia.
Qed.

Lemma PBOK_of_at : forall m ts b, PBOKat m ts b -> PBOK m ts (b - t_co ts).
Proof. intros m ts b H. unfold PBOK. replace (t_co ts + (b - t_co ts)) with b by lia. exact H. Qed.

Lemma PBJ_keep : forall m m' ts ts' k k' kk a a',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive (cur_st ts) = false -> a <= a' -> PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' k k' kk a a' E1 E2 E3 E4 PJ P Hk Hd Ha. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
assert (Ec : cur_st ts' = cur_st ts) by (unfold cur_st; rewrite E1, E2; reflexivity).
eapply JL_dead; [rewrite Ec; exact Hd|]. eapply (JL_keep ts ts' g g a a' E1 E2 E3 E4 (Z.le_refl _) Ha J).
Qed.

Lemma PBJ_attach_g : forall m' ts ts' l st' ss' r sh BS nm g k' kk a a' w,
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) (TL st' ss' r (Some sh) BS nm []) -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a -> PBOK m' ts' k' -> k' <= kk -> jlive st' = false -> jfresh sh BS w ->
w + jpi st' ss' <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m' ts ts' l st' ss' r sh BS nm g k' kk a a' w Hl E1 E2 E3 E4 Hz J P Hk Hd JF H.
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
eapply (JL_lvl ts ts' l _ g _ a a' w Hl E1 E2 E3 E4 (lw_attach st' ss' r sh BS nm w JF) Hz J).
intros w0 _ W0. cbn [tl_st tl_ss]. rewrite (jtext_dead _ _ Hd). lia.
Qed.

Lemma PBJ_name_g : forall m' ts ts' l st' ss' r nn g k' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)]) -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a -> PBOK m' ts' k' -> k' <= kk -> jlive st' = false ->
key_w nn + jpi st' ss' <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m' ts ts' l st' ss' r nn g k' kk a a' Hl E1 E2 E3 E4 Hz J P Hk Hd H.
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
destruct (JL_jw _ _ _ J) as (W & EW).
assert (Lw : exists w0, lw l = Some w0).
{ destruct ts as [d lv co pb pbs x o os obs]. cbn [t_levels t_depth] in Hl. unfold jw in EW. cbn [t_levels t_depth] in EW.
destruct (jwl lv (S d)) as [A|] eqn:EA; [| discriminate EW]. exact (jwl_nth lv (S d) d l A EA Hl ltac:(lia)). }
destruct (lw_value l Lw) as (v & Ev & Lw0).
eapply (JL_lvl ts ts' l _ g _ a a' _ Hl E1 E2 E3 E4 (lw_rename l st' ss' r [(r, nn)] v Ev) Hz J).
intros w1 Lw1 _. rewrite Lw0 in Lw1. injection Lw1 as <-. cbn [tl_st tl_ss nw snd]. rewrite (jtext_dead _ _ Hd). pose proof (nw_nonneg (tl_nbs l)). lia.
Qed.

End RC__1.

Ltac jl_c :=
repeat match goal with
| |- context [jlive ?s] => let v := eval vm_compute in (jlive s) in (first [constr_eq v true | constr_eq v false]; change (jlive s) with v)
| |- context [jpi ?a ?b] => let v := eval vm_compute in (jpi a b) in (lazymatch v with Z0 => idtac | Zpos _ => idtac end; change (jpi a b) with v)
end.

Ltac jl_zin Hst := rewrite ?Hst; cbn [tl_st]; first [reflexivity | etransitivity; [eassumption | reflexivity]].
Ltac jl_unf := repeat match goal with x := _ : tlevel |- _ => subst x end; unfold ts_lvl, ts_pbs, ts_set_co, ts_set_x, ts_lvl_obj, ts_push; cbn [tl_st tl_ss t_co].
Ltac jl_rng := repeat match goal with |- context [jpi0 ?x] => lazymatch goal with H : 0 <= jpi0 x <= 48 |- _ => fail | _ => pose proof (jpi0_range x) end end.
Ltac jl_arith := jl_unf; unfold jtext, JC1; jl_c; cbv iota; rewrite ?jpi_eatws, ?jpi_self; repeat match goal with |- context [if jlive ?s then _ else _] => destruct (jlive s) end; jl_rng; lia.
Ltac jl_dead := jl_unf; first [jl_c; reflexivity | eassumption].

Ltac pbj_rs TS l PBK PBK' Hl Hst :=
eapply (PBJ_restate _ _ TS _ l _ _ _ _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst
| exact PBK | exact PBK' | lia | rewrite ?Hst; jl_dead | rewrite ?Hst; jl_arith].

Ltac pbj_rsg TS l g JLg PBK' Hl Hst :=
eapply (PBJ_restate_g _ TS _ l _ g _ _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst
| exact JLg | exact PBK' | lia | rewrite ?Hst; jl_arith].
End Mq0.
From Stdlib Require Permutation.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QfLs QJjn QmZZ QPZI Qhd4 Qwm6 QsKa Qiiq Q4v2 Qvmy Qawr QJZd QW22 Q1Ey Ql4f Qeia QWrz Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 Qvmy.Mq0 Qawr.Mq0 QJZd.Mq2 QJZd.Mq3 QW22.Mq0 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QdGy.Mq6 Qeia.Mq1 QWrz.Mq2 Qw5U.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma a4_static_in_img : forall a, hl_client_static A4L a -> hl_img_lo A4H <= a < hl_img_hi A4H.
Proof. intros a H. cbn [hl_client_static hl_img_lo hl_img_hi hla_base A4L A4H] in *. unfold a4_client_static in H. lia. Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma presD_own_pres : forall A LBall LM FRS B m md F R SP m' (Lo : list blk),
HEAPA A4L HIx A LBall LM ((F, 2) :: FRS) B m md ->
heap_presD R (LBall ++ LM ++ fr_ivs A4L ((F, 2) :: FRS)) SP m m' ->
F <= R -> R + 8 <= F + 248 -> alloc_ceiling <= SP ->
(forall a n, In (a, n) Lo -> F <= a /\ a + n <= F + 248 /\ (a + n <= R \/ R + 8 <= a)) ->
heap_pres A4H ((LBall ++ LM ++ (shad A4L F, 32) :: fr_ivs A4L FRS) ++ Lo) SP m m'.
Proof.
intros A LBall LM FRS B m md F R SP m' Lo HP HPD HR1 HR2 HSP HLo a Ha Hc.
assert (INF : In (F, 2) ((F, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & HF0 & HFc & HFimg & _). rewrite fr_size_2 in HFc, HFimg.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp. rewrite fr_size_2 in HFapp. cbn [hl_sb A4L] in HFapp.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg. change ((2 ^ 47 - 1) / 8) with 17592186044415 in HFapp. unfold A_SB in HFapp.
apply (HPD a Ha).
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; exact Hc | right; left; exact Hc | right; right].
apply in_app_or in Hb as [Hb | Hb].
+ apply in_app_or in Hb as [Hb | Hb]; [exists b; split; [apply in_or_app; left; exact Hb | exact Hr]|].
apply in_app_or in Hb as [Hb | Hb]; [exists b; split; [apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hr]|].
destruct Hb as [<- | Hb].
* exists (shad A4L F, 32). split; [| exact Hr]. apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. apply fr_ivs_shadow. exact INF.
* exists b. split; [| exact Hr]. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
+ destruct b as [ba bn]. destruct (HLo ba bn Hb) as (H1 & H2 & _). cbn [blk_addr blk_size fst snd] in Hr.
exists (F, fr_size 2 - 8). split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF|]. cbn [blk_addr blk_size fst snd]. rewrite fr_size_2. lia.
- intros HD. destruct Hc as [Hc | [Hc | (b & Hb & Hr)]].
+ lia.
+ pose proof (a4_static_in_img a Hc) as Hi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
+ apply in_app_or in Hb as [Hb | Hb].
* apply in_app_or in Hb as [Hb | Hb].
{ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_introl Hb))) as Hd. rewrite fr_size_2 in Hd. lia. }
apply in_app_or in Hb as [Hb | Hb].
{ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_intror Hb))) as Hd. rewrite fr_size_2 in Hd. lia. }
destruct Hb as [<- | Hb].
{ cbn [blk_addr blk_size fst snd] in Hr. unfold shad in Hr. cbn [hl_sb A4L] in Hr. unfold A_SB in *. Z.div_mod_to_equations. lia. }
destruct (in_fr_ivs _ _ Hb) as (F' & k' & HF' & [-> | ->]); cbn [blk_addr blk_size fst snd] in Hr.
{ assert (NE : F <> F') by (intros E; exact (own_frame_ne HIx _ _ _ _ _ _ _ _ _ _ HP HF' (eq_sym E))).
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ F 2 F' k' HP INF (or_intror HF') NE) as Hd. rewrite fr_size_2 in Hd. lia. }
{ pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HF')) as (Hk' & _ & HF'0 & HF'c & _).
pose proof (fr_shadow_len_bnd k' Hk') as SLB. pose proof alloc_ceiling_range as ACR. pose proof (fr_size_pos k' ltac:(lia)) as FSP.
unfold shad in Hr. cbn [hl_sb A4L] in Hr. unfold A_SB in *. Z.div_mod_to_equations. lia. }
* destruct b as [ba bn]. destruct (HLo ba bn Hb) as (_ & _ & H3). cbn [blk_addr blk_size fst snd] in Hr. lia.
Qed.

Lemma pe_frameAX_presD : forall pf pa (L : list blk) SP m m' nb pj sv ffa ffb shc (rj v : word) R,
heap_pres A4H L SP m m' -> SP <= pf_spf pf -> pe_geomA pf pa ->
In (shA (pa_F pa), 32) L -> In (pa_F pa, R - pa_F pa) L -> In (R + 8, pa_F pa + 248 - (R + 8)) L ->
R = pa_F pa + Z.of_nat (cells_size ffa) ->
Z.of_nat (cells_size ffa) + 8 + Z.of_nat (cells_size ffb) = 248 -> Z.of_nat (cells_size shc) <= 32 ->
pe_frameAX m pf pa nb pj sv (ffa ++ [C8 rj] ++ ffb) shc ->
rw_cells asegs m' R [C8 v] ->
pe_frameAX m' pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc.
Proof.
intros pf pa L SP m m' nb pj sv ffa ffb shc rj v R HPR HSP GEO InS InA InB ER SZ SZS (SL & GP & SV & FF & FSH) RC.
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF as [FFa FFm]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFm as [_ FFb].
cbn [cells_size csize Nat.add] in FFb.
split; [| split; [| split; [| split]]].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SL | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact GP | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SV | left; lia].
- apply (proj2 (rw_cells_app asegs _ _ _ _)). split.
+ eapply (heap_pres_rw_cells A4H); [exact HPR | exact FFa | right; right]. exists (pa_F pa, R - pa_F pa). split; [exact InA | cbn [blk_addr blk_size fst snd]; lia].
+ apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [rewrite <- ER; exact RC|]. cbn [cells_size csize Nat.add].
eapply (heap_pres_rw_cells A4H); [exact HPR | exact FFb | right; right]. exists (R + 8, pa_F pa + 248 - (R + 8)). split; [exact InB | cbn [blk_addr blk_size fst snd]; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FSH | right; right]. exists (shA (pa_F pa), 32). split; [exact InS | cbn [blk_addr blk_size fst snd]; lia].
Qed.

Lemma disjoint_from_below : forall (W : list (Z * Z)) (a n c : Z), 0 <= n -> Forall (fun iv => snd iv <= c) W -> c <= a -> disjoint_from W a n.
Proof.
intros W a n c Hn HW Hc. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [disjoint_from fst snd] in *. split; [lia | apply IH; exact HW].
Qed.
Lemma pe_frameAX_writeG : forall pf pa nb pj sv ffc shc ffc' shc' m mc lo (W : list (Z * Z)),
PE_STATIC_A HIx pf pa lo -> pe_frameAX m pf pa nb pj sv ffc shc -> munch W m mc -> wmono asegs m mc ->
Forall (fun iv => snd iv <= alloc_ceiling) W ->
rw_cells asegs mc (pa_F pa) ffc' -> rw_cells asegs mc (shA (pa_F pa)) shc' ->
pe_frameAX mc pf pa nb pj sv ffc' shc'.
Proof.
intros pf pa nb pj sv ffc shc ffc' shc' m mc lo W STC (SLOTS & GAP & SAVED & _ & _) MU WM HW FFc FSHc.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
split; [| split; [| split; [| split; [exact FFc | exact FSHc]]]].
- eapply rw_cells_transport; [exact SLOTS | exact MU | exact WM |]. eapply disjoint_from_below; [lia | exact HW | lia].
- eapply rw_cells_transport; [exact GAP | exact MU | exact WM |]. eapply disjoint_from_below; [lia | exact HW | lia].
- eapply rw_cells_transport; [exact SAVED | exact MU | exact WM |]. eapply disjoint_from_below; [lia | exact HW | lia].
Qed.

Lemma payload_locA_presL : forall pf pa LB0 FRS A LB LM FR B m0 md (L : list blk) SP m m',
HEAPA A4L HIx A LB LM FR B m0 md -> incl FRS FR -> incl (fr_ivs A4L FRS) L ->
heap_pres A4H L SP m m' ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) -> (pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m').
Proof.
intros pf pa LB0 FRS A LB LM FR B m0 md L SP m m' HP HinclF HinclL HPR [L0 | PL]; [left; exact L0 | right].
destruct PL as [BL | (Fh & kh & HFh & HF1 & HF2 & UPS)]; [left; exact BL | right].
exists Fh, kh. split; [exact HFh|]. split; [exact HF1|]. split; [exact HF2|].
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (HinclF _ HFh)) as (Hks & HFal & HF0 & HFc & _).
pose proof UPS as (Hn & _).
assert (HF8 : Fh mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kh)); [| apply Z.mod_divide; [pose proof (fr_size_pos kh ltac:(lia)); lia | exact HFal]].
exists (2 ^ kh). unfold fr_size. lia. }
eapply unpoisoned_pres_heap; [exact UPS | exact HPR | apply HinclL; apply fr_ivs_shadow; exact HFh | |].
- unfold shadow_span_lo, shad. cbn [hl_sb A4L]. unfold A_SB. Z.div_mod_to_equations. lia.
- unfold shadow_span_hi, shad. cbn [hl_sb A4L]. unfold A_SB. rewrite (fr_size_shadow kh) in HF2 by lia.
unfold fr_shadow_len in *. Z.div_mod_to_equations. lia.
Qed.

Lemma PE_REST_A_callL : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 (L : list blk),
PE_STATIC_A HIx pf pa lo ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B ts errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H L (pf_spf pf) m1 m2 ->
incl LB0 L -> incl LM L -> incl (fr_ivs A4L FRS) L ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
(forall i l, nth_error (t_levels ts2) i = Some l -> lvl_cur asegs A4F m2 (t_depth ts2) i l) ->
(if zin (cur_st ts2) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts2) m2 (t_objbs ts2) (t_obj ts2) else t_objbs ts2 = []) ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BUD pf pa ts2 B2 ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 L STC
(HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD) VM12 HPRc Hincl HinclM HinclF HP2 LV2 OBJ2 ST2 ERR2 BUD2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
split; [exact HP2|]. split; [exact LV2|]. split; [exact OBJ2|]. split; [exact ST2|]. split; [exact ERR2|].
assert (SBin2 := payload_locA_presL pf pa LB0 FRS _ _ _ _ _ _ _ L _ _ _ HP (incl_tl _ (incl_refl _)) HinclF HPRc SBin).
split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split; [| split; [| exact BUD2]]]]]].
- eapply payload_presA; [exact HPRc | exact Hincl | exact HinclF | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply Hincl; exact Hb|].
apply in_app_or in Hb as [Hb | Hb]; [apply HinclM; exact Hb | apply HinclF; exact Hb].
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_pres; [exact HPRc | exact G].
Qed.

Lemma pe_parse_i64_cX :
forall (entry : Z), parse_i64_A_stmt HIx entry ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP buf cap R : Z) (rj : word) (ffa ffb shc : list cell)
(ra gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv (pe_frameAX m pf pa nb pj sv (ffa ++ [C8 rj] ++ ffb) shc) ->
PBOKat m ts kP ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
R = pa_F pa + Z.of_nat (cells_size ffa) -> Z.of_nat (cells_size ffa) + 8 + Z.of_nat (cells_size ffb) = 248 -> Z.of_nat (cells_size shc) = 32 ->
R mod 8 = 0 -> unpoisoned asegs m A_SB R 8 ->
Z.of_nat (length FRS) + 1 < 4096 ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 errv2 (rv : Z) (v w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
(rv = 0 \/ rv = 1) ->
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B ts errv2 (pe_frameAX m2 pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc) ->
PBOKat m2 ts kP ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 rv) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Proof.
intros entry PI64. intros until fc. intros STC INV PBK Epbs ER SZ SZS R8 UNPR NFR RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _ & _ & _ & _ & _ & _ & BUD1).
pose proof PBK as (buf' & bpos & cap' & pre & post & Epbs' & Lpre & CORE1 & Hbp).
rewrite Epbs in Epbs'. injection Epbs' as <- <-.
destruct CORE1 as (Hbp0 & Hcap & Hlen & _ & BUFC).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
destruct (first_nul_splitA pre post) as (str & rest & Econt & NONUL & Lstr).
rewrite Econt in BUFB. change (str ++ QgoP.b0 :: rest) with (str ++ [QgoP.b0] ++ rest) in BUFB. rewrite app_assoc in BUFB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in BUFB as [SRC _].
assert (LenC : Z.of_nat (length str) + 1 <= cap).
{ rewrite <- Hlen, Econt, !length_app. cbn [length]. lia. }
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INbuf : In (buf, cap) RB) by (unfold RB, pe_blocksA, tstate_blocks; rewrite Epbs; apply in_or_app; left; cbn [app]; right; left; reflexivity).
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (SPF : lo <= pf_spf pf - PI64_STK_A /\ pf_spf pf mod 32 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ unfold PI64_STK_A. clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [exact Gspf|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
pose proof FR1 as (_ & _ & _ & FF1 & _).
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [_ FFm]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFm as [RC1 _]. rewrite <- ER in RC1.
eapply (PI64 ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B str buf R lo rj errv);
[ exact HP1 | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1 | rewrite unsigned_lit by lia; exact SPF2
| rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity | exact SRC | exact NONUL
| exists buf, cap; split; [exact INbuf | lia]
| eapply (unpoisoned_of_blk HIx); [exact HP1 | exact INbuf | lia | lia | lia]
| exists (pa_F pa), 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| exact RC1 | exact UNPR | exact R8 | cbn [length]; lia | ].
intros ms2 md2 m2 A2 rv v errv2 RS2 VM2 ST2 HPD2 Hrv RC2 ERR2 HP2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & ->).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPD2 by lia.
set (Lo := [(pa_F pa, R - pa_F pa); (R + 8, pa_F pa + 248 - (R + 8))]).
assert (HPR2 : heap_pres A4H ((RB ++ LM ++ (shad A4L (pa_F pa), 32) :: fr_ivs A4L FRS) ++ Lo) (pf_spf pf) m m2).
{ eapply (presD_own_pres A RB LM FRS B m md (pa_F pa) R (pf_spf pf) m2 Lo); [exact HP1 | exact HPD2 | lia | lia | lia |].
intros a n [E | [E | []]]; injection E as <- <-; lia. }
set (LL := (RB ++ LM ++ (shad A4L (pa_F pa), 32) :: fr_ivs A4L FRS) ++ Lo) in *.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc).
{ eapply (pe_frameAX_presD pf pa LL (pf_spf pf) m m2 nb pj sv ffa ffb shc rj v R); [exact HPR2 | lia | exact GEO | | | | exact ER | exact SZ | lia | exact FR1 | exact RC2].
- unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. left. reflexivity.
- unfold LL, Lo. apply in_or_app; right. left. reflexivity.
- unfold LL, Lo. apply in_or_app; right. right. left. reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl INq))))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOKat m2 ts kP).
{ eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B ts errv2).
{ eapply (PE_REST_A_callL pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B ts ts errv errv2 LL); [exact STC | exact REST1 | exact VM2 | exact HPR2 | | | | exact HP2 | | | exact ST2 | exact ERR2 | exact BUD1].
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; left. apply LB0R. exact Hb.
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb.
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. right. exact Hb.
- intros i li Hli. eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ1].
eapply (jopt_agree asegs A4F); [exact OBJ1 | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
eapply (K m2 md2 A2 errv2 rv v); [exact Hrv | | exact PBKa].
split; [| exact REST2]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOKat_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2].
Qed.

Definition STRTOD_STK_A : Z := 12288.
Definition strtod_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(str : list byte) (SA R lo : Z) (rj errv : word),
HEAPA A4L HIx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - STRTOD_STK_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 R ->
bytes_at asegs m SA (str ++ [QgoP.b0]) -> ~ In QgoP.b0 str ->
Z.of_nat (length str) < 2^31 ->
(exists a n, In (a, n) LB /\ a <= SA /\ SA + Z.of_nat (length str) + 1 <= a + n) ->
(exists Fc kc, In (Fc, kc) FRS /\ Fc <= R /\ R + 8 <= Fc + fr_size kc - 8) ->
rw_cells asegs m R [C8 rj] -> R mod 8 = 0 ->
frm0 fc ->
(forall ms' m' (a0' v e' : word),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m' ms' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_presD R (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' R [C8 v] -> rw_cells asegs m' A_ERRNO [C4 e'] ->
HEAPA A4L HIx A LB LM FRS B m' md ->
AJ5 A4L HIx A T md ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xda5f4) fc None m (seg_rom asegs)).

Lemma pe_strtod_cX :
strtod_A_stmt ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP buf cap R : Z) (rj : word) (ffa ffb shc : list cell)
(ra gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv (pe_frameAX m pf pa nb pj sv (ffa ++ [C8 rj] ++ ffb) shc) ->
PBOKat m ts kP ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
R = pa_F pa + Z.of_nat (cells_size ffa) -> Z.of_nat (cells_size ffa) + 8 + Z.of_nat (cells_size ffb) = 248 -> Z.of_nat (cells_size shc) = 32 ->
R mod 8 = 0 -> frm0 fc ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 errv2 (a0' v w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts errv2 (pe_frameAX m2 pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc) ->
PBOKat m2 ts kP ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0' w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xda5f4) fc None m (seg_rom asegs)).
Proof.
intros PI64. intros until fc. intros STC INV PBK Epbs ER SZ SZS R8 FRM RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _ & _ & _ & _ & _ & _ & BUD1).
pose proof PBK as (buf' & bpos & cap' & pre & post & Epbs' & Lpre & CORE1 & Hbp).
rewrite Epbs in Epbs'. injection Epbs' as <- <-.
destruct CORE1 as (Hbp0 & Hcap & Hlen & _ & BUFC).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
destruct (first_nul_splitA pre post) as (str & rest & Econt & NONUL & Lstr).
rewrite Econt in BUFB. change (str ++ QgoP.b0 :: rest) with (str ++ [QgoP.b0] ++ rest) in BUFB. rewrite app_assoc in BUFB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in BUFB as [SRC _].
assert (LenC : Z.of_nat (length str) + 1 <= cap).
{ rewrite <- Hlen, Econt, !length_app. cbn [length]. lia. }
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INbuf : In (buf, cap) RB) by (unfold RB, pe_blocksA, tstate_blocks; rewrite Epbs; apply in_or_app; left; cbn [app]; right; left; reflexivity).
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (SPF : lo <= pf_spf pf - STRTOD_STK_A /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ unfold STRTOD_STK_A. clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
pose proof FR1 as (_ & _ & _ & FF1 & _).
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [_ FFm]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFm as [RC1 _]. rewrite <- ER in RC1.
eapply (PI64 ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B str buf R lo rj errv);
[ exact HP1 | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1 | rewrite unsigned_lit by lia; exact SPF2
| rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity | exact SRC | exact NONUL | lia
| exists buf, cap; split; [exact INbuf | lia]
| exists (pa_F pa), 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| exact RC1 | exact R8 | exact FRM | ].
intros ms2 m2 a0' v errv2 RS2 ST2 HPD2 RC2 ERR2 HP2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
pose proof (model_vm_only_refl (cfg_model md)) as VM2. set (md2 := md) in *. set (A2 := A) in *.
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPD2 by lia.
set (Lo := [(pa_F pa, R - pa_F pa); (R + 8, pa_F pa + 248 - (R + 8))]).
assert (HPR2 : heap_pres A4H ((RB ++ LM ++ (shad A4L (pa_F pa), 32) :: fr_ivs A4L FRS) ++ Lo) (pf_spf pf) m m2).
{ eapply (presD_own_pres A RB LM FRS B m md (pa_F pa) R (pf_spf pf) m2 Lo); [exact HP1 | exact HPD2 | lia | lia | lia |].
intros a n [E | [E | []]]; injection E as <- <-; lia. }
set (LL := (RB ++ LM ++ (shad A4L (pa_F pa), 32) :: fr_ivs A4L FRS) ++ Lo) in *.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc).
{ eapply (pe_frameAX_presD pf pa LL (pf_spf pf) m m2 nb pj sv ffa ffb shc rj v R); [exact HPR2 | lia | exact GEO | | | | exact ER | exact SZ | lia | exact FR1 | exact RC2].
- unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. left. reflexivity.
- unfold LL, Lo. apply in_or_app; right. left. reflexivity.
- unfold LL, Lo. apply in_or_app; right. right. left. reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl INq))))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOKat m2 ts kP).
{ eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B ts errv2).
{ eapply (PE_REST_A_callL pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B ts ts errv errv2 LL); [exact STC | exact REST1 | exact VM2 | exact HPR2 | | | | exact HP2 | | | exact ST2 | exact ERR2 | exact BUD1].
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; left. apply LB0R. exact Hb.
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb.
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. right. exact Hb.
- intros i li Hli. eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ1].
eapply (jopt_agree asegs A4F); [exact OBJ1 | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
eapply (K m2 errv2 a0' v); [| exact PBKa | exact FS2 | exact FRM2].
split; [| exact REST2]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOKat_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2].
Qed.

Lemma jval_int_blocks : forall m BS p rc, jval asegs A4F Sint m BS p rc -> In (p, 56) BS /\ (length BS <= 3)%nat.
Proof.
intros m BS p rc J. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (cty & v & junk & -> & _)). subst BS.
split; [left; reflexivity|].
destruct OP as [[_ ->] | [_ (buf & bpos & size & content & -> & _)]]; cbn; lia.
Qed.

Lemma jval_dbls_blocks : forall m BS p rc, jval asegs A4F (Sdouble true) m BS p rc -> In (p, 48) BS /\ (length BS <= 4)%nat.
Proof.
intros m BS p rc J. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (bits & ud & udn & uds & -> & _)). subst BS.
split; [left; reflexivity|].
destruct OP as [[_ ->] | [_ (buf & bpos & size & content & -> & _)]]; cbn; lia.
Qed.

Definition jo_new_int_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPA A4L HIx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newint_costB <= bB B -> 1 <= bD B ->
(forall ms' md' A', QJZd.Mq2.new_obj_A_post HIx Sint ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma pe_new_int_wX :
forall (entry : Z), jo_new_int_A_stmt entry ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (ffc shc : list cell)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 errv (pe_frameAX m pf pa nb pj sv ffc shc) ->
Z.of_nat (cells_size ffc) <= 248 -> Z.of_nat (cells_size shc) <= 32 ->
PBOKat m ts kP -> newint_costB <= bB B -> 1 <= bD B ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc)) \/
(r <> 0 /\ exists BS, (length BS <= 3)%nat /\ jfresh Sint BS 20 /\ 0 < r < 2^62 /\
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some Sint) BS 1 errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc))) ->
PBOKat m2 ts kP -> bB B - newint_costB <= bB B2 -> bD B - 1 <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Proof.
intros entry NEWINT. intros until fc. intros STC WIN SZF SZS PBK COST COSTD RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 32 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
eapply (NEWINT ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B lo errv);
[ exact HP1 | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| exact COST | exact COSTD | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv ffc shc).
{ eapply pe_frameAX_pres; [exact HPRc | lia | exact GEO | | | exact SZF | exact SZS | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
eapply (K m2 md2 A2 B2 errv2 r); [| | exact HB2 | exact HD2 | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & HP2 & PIN)].
+ left. split; [reflexivity|].
eapply (PE_WINX_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity | exact FR2].
+ right. split; [exact Hr|]. exists BS.
destruct (jval_int_blocks _ _ _ _ J2) as [INr LEN3].
split; [exact LEN3|]. split; [exact (jfresh_int asegs A4F _ _ _ _ J2 PIN)|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 56 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WINX_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some Sint) BS 1 errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]] | exact FR2].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Lemma pe_new_double_s_wX :
new_double_s_A_stmt HIx ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP buf cap v2 ra2 : Z) (ffc shc : list cell)
(ra gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 errv (pe_frameAX m pf pa nb pj sv ffc shc) ->
Z.of_nat (cells_size ffc) <= 248 -> Z.of_nat (cells_size shc) <= 32 ->
PBOKat m ts kP -> t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
newdbls_costB kP <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc)) \/
(r <> 0 /\ exists BS, (length BS <= 4)%nat /\ (exists w, jfresh (Sdouble true) BS w /\ w <= kP + 16) /\ 0 < r < 2^62 /\
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sdouble true)) BS 1 errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc))) ->
PBOKat m2 ts kP -> bB B - newdbls_costB kP <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 json_object_new_double_s_A_entry) fc None m (seg_rom asegs)).
Proof.
intros NEWDBLS. intros until fc. intros STC WIN SZF SZS PBK Epbs COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 80 - 16 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof PBK as (buf' & bpos & cap' & pre & post & Epbs' & Lpre & CORE1 & Hbp).
rewrite Epbs in Epbs'. injection Epbs' as <- <-.
destruct CORE1 as (Hbp0 & Hcap & Hlen & _ & BUFC).
destruct (first_nul_splitA pre post) as (str & rest & Econt & NONUL & Lstr).
assert (LenC : Z.of_nat (length str) + 1 <= cap).
{ rewrite <- Hlen, Econt, !length_app. cbn [length]. lia. }
assert (INbuf : In (buf, cap) RB) by (unfold RB, pe_blocksA, tstate_blocks; rewrite Epbs; apply in_or_app; left; cbn [app]; right; left; reflexivity).
assert (SIB : str_in_block A4H m buf cap (pre ++ [Z_to_bv 8 0] ++ post) buf str).
{ split; [exact BUFC|]. split; [lia|]. split; [lia|]. split; [| exact NONUL].
rewrite Z.sub_diag. change (Z.to_nat 0) with 0%nat. rewrite skipn_O. rewrite Econt. change (str ++ QgoP.b0 :: rest) with (str ++ [QgoP.b0] ++ rest). rewrite app_assoc.
rewrite firstn_app. rewrite length_app. cbn [length]. replace (length str + 1 - (length str + 1))%nat with 0%nat by lia.
rewrite firstn_all2 by (rewrite length_app; cbn [length]; lia). cbn [firstn]. apply app_nil_r. }
pose proof (pe_uw_atX HIx pf pa lo m nb pj sv v2 ra2 ffc shc STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
assert (COST' : newdbls_costB (Z.of_nat (length str)) <= bB B) by (unfold newdbls_costB in *; lia).
eapply (NEWDBLS ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B buf lo buf cap str (pre ++ [Z_to_bv 8 0] ++ post) errv (UWfp ra2 v2));
[ exact HP1 | rewrite !unsigned_lit by lia; exact UWA | exact UWK | exact INbuf | exact SIB | lia
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| exact COST' | cbn [uw_cost]; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | reflexivity | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & _ & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv ffc shc).
{ eapply pe_frameAX_pres; [exact HPRc | lia | exact GEO | | | exact SZF | exact SZS | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
eapply (K m2 md2 A2 B2 errv2 r); [| | unfold newdbls_costB in *; lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & HP2 & PIN)].
+ left. split; [reflexivity|].
eapply (PE_WINX_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity | exact FR2].
+ right. split; [exact Hr|]. exists BS.
destruct (jval_dbls_blocks _ _ _ _ J2) as [INr LEN4].
split; [exact LEN4|]. split; [destruct PIN as (ud & ->); exists (16 + Z.of_nat (length str)); split; [apply jfresh_dbls; lia | lia]|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WINX_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sdouble true)) BS 1 errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]] | exact FR2].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End WithIface.
End RC__1.
End Mq1.
From Stdlib Require NArith.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QZDE Qc3B QKQo Q8tj Qu4M QSL3 Q3jZ Qmd7 Q22i Qvbw Qg1M Q30W QkXq Q1Y6 QvPk Qoif Qkxa QjKS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QRUw QKQo Q8tj. Import Qu4M.Mq0.
Import QSL3. Import Q3jZ Qmd7 Q22i.
Import Qvbw. Import Qg1M.
Import Q7UD Qhd4 Qwm6.
Import QsKa.Mq0.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QlKV.Mq7 QsKa.Mq5 Q30W.Mq3 QkXq.Mq2 Q1Y6.Mq0 Q30W.Mq1 QvPk QsKa.Mq4 Qiiq.Mq0 QlKV.Mq5 Qoif.Mq0 QlKV.Mq2 Qkxa QjKS.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MJoObjAddMain.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB VBS PBS LM : list blk) (FRS : list frame) (B0 : bud) (KBS : list (list blk)).
Variables (lo p v k kn pb t tbl size : Z) (es : list lent) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - (64 + 96 + 4096 + 128 + HD).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis INK : In (k, kn) LB.
Hypothesis KN : kn <= 2^31.
Hypothesis FRM : frm0 fc.
Hypothesis FRN : Z.of_nat (length FRS) < 4096.
Hypothesis LK1 : length es = length kids.
Hypothesis LK2 : length KBS = length kids.
Hypothesis BB0 : oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B0.
Hypothesis BR0 : 512 * (3 + Z.of_nat (length es) + Z.of_nat (length (concat KBS)) + Z.of_nat (length PBS)) <= bB B0.
Hypothesis BD0 : 0 <= bD B0.
Notation OBS := (OBS PBS KBS p t tbl size es).
Notation OHDR := (OHDR pb t).
Hypothesis Kont : forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_framexA ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
lh_globA m' -> bD B0 <= bD B' ->
((r = 0 /\ exists OBS' kids', jval asegs A4F (Sobj kids') m' OBS' p 1 /\ HEAPAx A' (OBS' ++ LB) LM FRS B' m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)
/\ ( ( Z.of_nat (length kids') = Z.of_nat (length kids) + 1
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length OBS') = Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1
/\ obj_grownA size (Z.of_nat (length kids)) (obj_capA OBS')
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj kids') OBS' = Some (w + (key_w (Z.of_nat (length ks) + 1) + wv), [])))
\/ ( Z.of_nat (length kids') = Z.of_nat (length kids)
/\ bB B0 - 512 * (Z.of_nat (length OBS) + Z.of_nat (length VBS) - Z.of_nat (length OBS')) <= bB B'
/\ Z.of_nat (length OBS') <= Z.of_nat (length OBS) + Z.of_nat (length VBS)
/\ obj_capA OBS' = size
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj kids') OBS' = Some (w', []) /\ w' <= w + wv)))) \/
(r = 2^64 - 1 /\ exists REM, jval asegs A4F (Sobj kids) m' OBS p 1 /\ jopt asegs A4F vs m' VBS v
/\ HEAPAx A' (OBS ++ VBS ++ REM ++ LB) LM FRS B' m' md'
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B')) ->
AJ5 A4L HIx A' T md' ms'.

Lemma oadd_mainA :
forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word) (svs : list slotv),
HEAPAx A (OBS ++ VBS ++ LB) LM FRS B0 m0 md0 ->
rw_cells asegs m0 p OHDR ->
lh_open asegs A4F m0 t tbl size es svs ->
okids asegs A4F m0 kids (map kv es) KBS -> opt_pbuf asegs m0 PBS pb -> jopt asegs A4F vs m0 VBS v ->
cstr asegs m0 k kn ks -> lh_globA m0 ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
stk asegs m0 lo (bv_unsigned sp) ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 k) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_object_add_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until svs. intros HP HDR OPEN KIDS OPB JOB CS G ERR ST.
pose proof HDR as HDR0. unfold Qkxa.OHDR in HDR. cbn [fn_obj_to_json_string A4F] in HDR.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL. pose proof alloc_ceiling_ge as ACG. pose proof alloc_ceiling_range as ACR.
destruct (oadd_factsX HIx LM FRS p t tbl size es _ _ _ _ _ (concat KBS ++ PBS ++ VBS ++ LB) HP ltac:(unfold Qkxa.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pvX HIx VBS LM FRS p v vs _ _ _ _ _ (lh_blocks t tbl size es ++ concat KBS ++ PBS ++ LB) HP ltac:(unfold Qkxa.OBS; perm) JOB) as (Hpv & V0 & V1).
assert (INK' : In (k, kn) (OBS ++ VBS ++ LB)) by (apply in_or_app; right; apply in_or_app; right; exact INK).
destruct (oadd_keyX HIx LM FRS k kn ks _ _ _ _ _ HP INK' CS) as (STR & NN & KL & KPOS & KHI & KAL).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m0) as MU.
assert (INp : In (p, 48) (OBS ++ VBS ++ LB)) by (unfold Qkxa.OBS; cbn; left; reflexivity).
assert (INt : In (t, 56) (OBS ++ VBS ++ LB)) by (unfold Qkxa.OBS, lh_blocks; cbn; right; left; reflexivity).
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INp) as SHp. unfold shad in SHp. apply shadow_ro_cells in SHp.
change (shadow_cells 48) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHp.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP INt) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (proj1 OPEN) as THDR. unfold lh_hdr, lh_hdrf in THDR. cbn [fn_lh_char_hash fn_lh_char_equal fn_lh_entry_free A4F] in THDR.
a4l.
stash OPEN. stash KIDS. stash OPB. stash JOB. stash CS. stash G. stash KF. stash STR. stash HDR0.
stash Hpimg. stash Htimg. stash Hbimg. stash SEP. stash D1. stash D2.
unfold json_object_object_add_A_entry.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 9 step.
step. step. step. step.
step. step.
asan_chkA.
step. step. step.
asan_chkA.
step. step. step.

unstash CS. unstash G.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
assert (HP1 : HEAPAx A (OBS ++ VBS ++ LB) LM FRS B0 mA md0) by (match goal with MIc : mem_inv asegs mA |- _ => heap_nowA A4L HIx HP MU WM MIc end).
assert (HPR1 : heap_pres A4H ((OBS ++ VBS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mA).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP]. }
assert (AG1 : agree_on asegs (OBS ++ VBS ++ LB) m0 mA).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR1 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
pose proof (cstr_agree asegs _ _ _ _ _ _ CS AG1 INK' ltac:(lia)) as CS1.
pose proof (lh_globA_client _ _ _ _ HPR1 G) as G1.
evt_done5.
eapply HASH with (LB := OBS ++ VBS ++ LB) (lo := lo) (kp := k) (kn := kn) (ks := ks);
[ exact HP1 | exact INK' | exact CS1 | exact G1 | rewrite unsigned_lit by lia; eassumption | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| unfold A_ERRNO, A_TP; eassumption | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRM | exact FRN | reflexivity | ].
intros ms2 md2 A2 (mB & h & e2 & RS2 & Hh & VM2 & ST2 & HPR2 & ERR2 & G2 & HP2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
unstash OPEN. unstash KIDS. unstash OPB. unstash JOB. unstash HDR0.
assert (AG2 : agree_on asegs (OBS ++ VBS ++ LB) m0 mB).
{ eapply agree_on_trans; [exact AG1|]. eapply (agree_of_heap_presx asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
assert (HPRa : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mB).
{ eapply heap_presx_trans; [apply heap_pres_presx; eapply heap_pres_weaken; [exact HPR1 | lia |] |].
- intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb].
- eapply heap_presx_weaken; [exact HPR2 | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb]. }
lazymatch goal with FRc : rw_cells asegs mA (bv_unsigned sp + -64) _ |- _ => rename FRc into FR end.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR.
apply (rw_cells_agree asegs _ _ _ _ _ HDR0) in AG2 as HDR2; [| exists p, 48; split; [exact INp | cbn; lia]].
pose proof HDR2 as HDR2'. unfold Qkxa.OHDR in HDR2. cbn [fn_obj_to_json_string A4F] in HDR2.
pose proof (lh_open_agree asegs A4F _ _ _ _ _ _ _ _ OPEN AG2 ltac:(unfold Qkxa.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb)) as OPEN2.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ KIDS AG2 ltac:(unfold Qkxa.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS2.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB AG2 ltac:(unfold Qkxa.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB2.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB AG2 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB2.
pose proof (cstr_agree asegs _ _ _ _ _ _ CS AG2 INK' ltac:(lia)) as CS2.
clear HP MU WM MI HDR THDR OPEN KIDS OPB JOB CS G HP1 HPR1 AG1 CS1 G1 AG2 SHp SHt GOT CELL.
destruct (oadd_keyX HIx LM FRS k kn ks _ _ _ _ _ HP2 INK' CS2) as (KB2 & _).
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP2) as [GOT CELL].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP2 INp) as SHp. unfold shad in SHp. apply shadow_ro_cells in SHp.
change (shadow_cells 48) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHp.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs mB) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -64)] mB) as MU.
a4l.
stash KIDS2. stash OPB2. stash JOB2. stash CS2. stash G2. stash HDR2'. stash OPEN2.
reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. step. step. step.

unstash OPEN2. unstash KF.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He) as (_ & _ & K2 & _). lia. }
stash KF.
eapply evt_cut.
{ eapply (lh_lookup_A_spec HIx OBL_ISTRCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 t tbl size k lo es svs ks mB md2 A2 (OBS ++ VBS ++ LB) LM FRS B0 k kn HP2) with (h := h);
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
first [ exact MI | exact OPEN2 | exact BELOW | exact KB2 | exact NN | exact ST2 | exact LO | exact INK' | reflexivity | exact Hh | lia
| (clear - SPA; Z.div_mod_to_equations; lia)
| (unfold Qkxa.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb) ]. }
intros ms3 (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & r & mC & -> & MU3 & WM3 & MI3 & ST3 & OPEN3 & KB3 & RES).
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in MU3, ST3 by lia.
unstash KIDS2. unstash OPB2. unstash JOB2. unstash CS2. unstash G2. unstash HDR2'. unstash KF.
assert (HP3 : HEAPAx A2 (OBS ++ VBS ++ LB) LM FRS B0 mC md2) by heap_nowA A4L HIx HP2 MU3 WM3 MI3.
assert (AG3 : agree_on asegs (OBS ++ VBS ++ LB) mB mC).
{ eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |]. intros a n Ha. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP2 ltac:(apply in_or_app; left; exact Ha)) as (? & _ & _ & ? & _). lia. }
assert (HPRb : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mC).
{ eapply heap_presx_trans; [exact HPRa|]. eapply (heap_presx_of_munch A4H); [exact MU3 | exact WM3 |].
eapply (client_outsideA A4L HIx); [exact HP2 | | clia | solve_clientWA A4L HIx HP2].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb]. }
pose proof (rw_cells_agree asegs _ _ _ _ _ HDR2' AG3 ltac:(exists p, 48; split; [exact INp | cbn; lia])) as HDR3.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ KIDS2 AG3 ltac:(unfold Qkxa.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS3.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB2 AG3 ltac:(unfold Qkxa.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB3.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB2 AG3 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB3.
pose proof (cstr_agree asegs _ _ _ _ _ _ CS2 AG3 INK' ltac:(lia)) as CS3.
pose proof (lh_globA_frame _ _ _ G2 MU3 WM3 ltac:(apply Forall_cons; [unfold GHASHA, GSEEDA; cbn [fst snd]; lia | apply Forall_nil])) as G3.
lazymatch type of MU3 with munch _ ?mq _ =>
transport_after_call asegs mq mC MU3 WM3; try match goal with H : mem_inv asegs mq |- _ => clear H end end.
replace (ret_pc (Z_to_bv 64 0x9bef4)) with (Z_to_bv 64 0x9bef4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step.
if_falsex. step.
lazymatch goal with FRc : rw_cells asegs mC (bv_unsigned sp + -64) _ |- _ => rename FRc into FR3 end.
lazymatch goal with E : rw_cells asegs mC 6434236 _ |- _ => rename E into ERR3 | E : rw_cells asegs mC (6434400 - 164) _ |- _ => rename E into ERR3 end.
destruct RES as [-> | (j & e & Hj & -> & Hks)].
-
if_true.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; reflexivity).
replace (p / 8 + 2147450885) with (p / 8 + 5 + 2147450880) by lia.
evt_done5.
eapply (oadd_insA HIx LF OBL_AMEMSET HD HD_ge HASH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB VBS PBS LM FRS B0 KBS lo p v k kn pb t tbl size es ks kids vs T
LO LOS SPA HT RA INK KN FRN LK1 LK2 BB0 BD0 Kont);
first [exact HP3 | exact HDR3 | exact OPEN3 | exact KIDS3 | exact OPB3 | exact JOB3 | exact CS3 | exact G3 | exact ERR3 | exact ST3 | exact FR3
| exact VM2 | exact HPRb | exact FS2 | exact (FRM2 FRM) | exact Hh].
-
destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ _ _ OPEN3 Hj) as (sl & _ & Hix & _).
pose proof OPEN3 as (_ & _ & _ & _ & Hsz3 & _ & Hlen). pose proof (lf_size_range size Hsz3) as HSR.
unfold ent_addr. if_falsex. fold (ent_addr tbl (le_ix e)).
replace (p / 8 + 2147450885) with (p / 8 + 5 + 2147450880) by lia.
evt_done5.
eapply (oadd_dupA HIx PUT HD HD_ge ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB VBS PBS LM FRS B0 KBS lo p v k pb t tbl size es ks kids vs T
LO LOS SPA HT LK1 LK2 BR0 Kont);
first [exact HP3 | exact HDR3 | exact OPEN3 | exact Hj | exact KIDS3 | exact OPB3 | exact JOB3 | exact G3 | exact ERR3 | exact ST3 | exact FR3
| exact VM2 | exact HPRb | exact FS2 | exact FRM2].
Qed.
End MJoObjAddMain.

Section MJoObjAddCps.
Variable HIx : heap_iface_A A4L.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.

Theorem json_object_object_add_A_cps : jo_object_add_A HIx HD.
Proof.
unfold jo_object_add_A, jo_object_add_A_stmt. intros until errv. intros PRE G J JOB INK CS KN FRM FRN A0 A1 A2 BB BR BD K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
destruct (sobj_open asegs A4F _ _ _ _ _ J) as (pb & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR & TAB & L1 & L2 & KIDS).
destruct TAB as (tbl & size & es & svs & Hkvs & ETBS & OPEN). subst OBS TBS kvs a0 a1 a2 tp.
rewrite length_map in L1.
pose proof OPEN as (_ & _ & _ & _ & Hsz & _). pose proof (lf_size_range size Hsz) as HSR.
lazymatch type of BB with context [obj_capA ?L] => assert (CAP : obj_capA L = size) by (apply obj_capA_lh; lia) end.
rewrite CAP in BB, K.
eapply (oadd_mainA HIx PUT LF OBL_AMEMSET OBL_ISTRCMP HD HD_ge HASH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB VBS PBS LM FRS B KBS lo p v k kn pb t tbl size es ks kids vs T
LO LOS SPA HT RA INK KN FRM FRN L1 L2 BB).
- revert BR. unfold lh_blocks. cbn [app length]. rewrite !length_app, length_map. cbn [length]. intros BR2. rewrite !Nat2Z.inj_succ, !Nat2Z.inj_add in BR2. unfold Z.succ in BR2.

lazymatch goal with |- 512 * (3 + ?a + ?b + ?c) <= _ => replace (3 + a + b + c) with (a + b + c + 1 + 1 + 1) by ring end. exact BR2.
- exact BD.
- intros ms' md' m' r A' B' PO G' BD' OUT. exact (K ms' md' m' r A' B' PO G' BD' OUT).
- exact HP.
- exact HDR.
- exact OPEN.
- exact KIDS.
- exact OPB.
- exact JOB.
- exact CS.
- exact G.
- exact ERR.
- exact ST.
Qed.
End MJoObjAddCps.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr QbFI QSHS Qc5u QAzu Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mqe.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import Q2EX QdGy.Mqc.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition tsX (ts : tstate) (LK : list blk) : tstate :=
TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts ++ LK).

Lemma perm_blocks_tsX : forall pf q LB0 ts LK, Permutation (pe_blocksA pf q LB0 (tsX ts LK)) (pe_blocksA pf q LB0 ts ++ LK).
Proof.
intros pf q LB0 ts LK. unfold pe_blocksA, tstate_blocks, tsX; cbn [t_pbs t_objbs t_levels].
set (P := t_pbs ts). set (O := t_objbs ts). set (C := concat (map lvl_blocks (t_levels ts))). set (R := (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0).
rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.

Lemma PE_INVW_A_tokw1 : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts LK cb nb pj sv errv co' x',
PE_STATIC_A HIx pf pa lo ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts LK cb nb pj sv errv ->
munch [(pf_tk pf, pf_tk pf + 72)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x ts co' x') LK cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts LK cb nb pj sv errv co' x' STC (CORE & BASE & LVW & BUDW) MU WM MI TOKc Hco Hch.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (HW : Forall (pe_wtfA pf pa) [(pf_tk pf, pf_tk pf + 72)]) by (apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]).
assert (BASEx : PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 (tsX ts LK)) errv).
{ destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | apply Permutation_sym; apply perm_blocks_tsX | apply Permutation_refl | apply Permutation_refl]. }
destruct (PE_BASE_A_private_write HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m mc md A B (tsX ts LK) errv _ STC BASEx MU WM MI (pe_wtfA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsX in AG; cbn [t_objbs t_levels] in AG.
split; [| split; [| split]].
- unfold PE_CORE_A, ts_set_x; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco|]. split; [exact Hch|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split]].
+ eapply (pbuf_wtfA HIx) with (ts := tsX ts LK); [exact STC | exact (proj1 BASEx) | exact PB | exact MU | exact WM | exact HW].
+ eapply (tstack_wtfA HIx) with (ts := tsX ts LK); [exact STC | exact (proj1 BASEx) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
+ eapply (pe_frameA_blkwrite HIx) with (ts := tsX ts LK); [exact STC | exact (proj1 BASEx) | | exact FR | exact MU | exact WM].
apply Forall_cons; [exists (pf_tk pf), 72; cbn [fst snd]; split; [apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity | lia] | apply Forall_nil].
- destruct BASEc as (HPc & BASEc'). split; [| exact BASEc'].
eapply (heapA_perm A4L HIx); [exact HPc | | apply Permutation_refl | apply Permutation_refl].
change (pe_blocksA pf q LB0 (ts_set_x ts co' x')) with (pe_blocksA pf q LB0 ts). apply perm_blocks_tsX.
- unfold ts_set_x; cbn [t_levels t_depth]. intros i li Hli. destruct (LVW i li Hli) as (R12 & JO & NM & CL).
assert (INli : incl (lvl_blocks li) ((t_objbs ts ++ LK) ++ concat (map lvl_blocks (t_levels ts)))).
{ intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [apply in_map; eapply nth_error_In; exact Hli | exact Hb]. }
split; [exact R12|]. split; [| split; [| exact CL]].
+ eapply (jopt_agree asegs A4F); [exact JO | exact AG |]. intros b Hb. apply INli. unfold lvl_blocks. apply in_or_app; left. exact Hb.
+ destruct NM as [NM | NM]; [left | right]; (eapply (name_ok_agree asegs); [exact NM | exact AG |]; intros b Hb; apply INli; unfold lvl_blocks; apply in_or_app; right; exact Hb).
- exact BUDW.
Qed.

Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Notation KOUTx := (KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation KERR2x := (KERR2_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Hypothesis KO : KOUTx.

Lemma tdepth_ok_set_err : forall ts e, tdepth_ok ts -> tdepth_ok (ts_set_err ts e).
Proof. intros ts e TD. eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. Qed.

Local Ltac open_w STCx INVW :=
pose proof STCx as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
pose proof INVW as (CORE & BASE & _ & _);
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & _ & _ & _ & FR);
pose proof (proj1 BASE) as HP; clear BASE.

Lemma kerr2_of_kout_x :
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 < e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (Q1Y6.Mq4.pe_msE pf pa APE_ERR2 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros ts LK e m md A B cb nb pj errv gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc INVW TD He FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 e)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold Q1Y6.Mq4.pe_msE, pe_msO, APE_ERR2. cbn [pf_tk pf_spf pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 e) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

Lemma kerr2_of_kout : KERR2x.
Proof. unfold KERR2_S. intros. eapply kerr2_of_kout_x; eassumption. Qed.

Lemma kerr3_of_kout :
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 < e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msX asegs pf pa APE_ERR3 x1 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros ts LK e m md A B cb nb pj errv x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc INVW TD He FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 e)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msX, pe_msO, APE_ERR3. cbn [pf_tk pf_spf pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 e) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

Lemma kerrmem_of_kout :
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_ERRMEM gp t0 t1 t2 (Z_to_bv 64 (pf_tk pf + 36)) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros ts LK m md A B cb nb pj errv gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc INVW TD FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 16)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msO, APE_ERRMEM. cbn [pf_tk pf_spf pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 16) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

Lemma kerrmem2_of_kout :
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_ERRMEM2 gp t0 t1 t2 a0 a1 (Z_to_bv 64 (pf_tk pf + 36)) a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros ts LK m md A B cb nb pj errv gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc INVW TD FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 16)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msO, APE_ERRMEM2. cbn [pf_tk pf_spf pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 16) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

End WithIface.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QRUw.Mq0 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import QbFI. Import QlKV.Mq2. Import QrQv.Mq4 Q2EX QdGy.Mqa Q63E.Mqb QdGy.Mqc.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma jtext_nonneg : forall st g, 0 <= g -> 0 <= jtext st g. Proof. intros st g H. unfold jtext. destruct (jlive st); lia. Qed.
Lemma jtext_dead : forall st g, jlive st = false -> jtext st g = 0. Proof. intros st g H. unfold jtext. rewrite H. reflexivity. Qed.
Lemma jpi_eatws : forall ss, jpi ST_eatws ss = jpi0 ss. Proof. reflexivity. Qed.
Lemma jpi_self : forall ss, jpi ss ss = jpi0 ss. Proof. intros ss. unfold jpi. destruct (ss =? ST_eatws); reflexivity. Qed.
Lemma PBJ_open : forall m ts k a, PBJ m ts k a -> exists g, 0 <= g /\ PBOKat m ts g /\ g <= t_co ts + k /\ JL ts g a.
Proof. intros m ts k a (g & P & Hg & J). exists g. split; [exact (PBOKat_nonneg _ _ _ P)|]. split; [exact P|]. split; [exact Hg | exact J]. Qed.

Lemma PBJ_restate_g : forall m' ts ts' l l' g k' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a -> PBOK m' ts' k' -> k' <= kk ->
jtext (tl_st l') (t_co ts' + k') + jpi (tl_st l') (tl_ss l') <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m' ts ts' l l' g k' kk a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J P Hk H. exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
exact (JL_lvl_restate ts ts' l l' g _ a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J H).
Qed.

Lemma PBJ_restate : forall m m' ts ts' l l' k k' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive (tl_st l') = false ->
jpi (tl_st l') (tl_ss l') <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l l' k k' kk a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz PJ P Hk Hd H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
eapply (PBJ_restate_g m' ts ts' l l' g k' kk a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J P Hk).
rewrite (jtext_dead _ _ Hd). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_attach : forall m m' ts ts' l st' ss' r sh BS nm k k' kk a a' w,
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) (TL st' ss' r (Some sh) BS nm []) -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive st' = false -> jfresh sh BS w ->
w + jpi st' ss' <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l st' ss' r sh BS nm k k' kk a a' w Hl E1 E2 E3 E4 Hz PJ P Hk Hd JF H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
eapply (JL_lvl ts ts' l _ g _ a a' w Hl E1 E2 E3 E4 (lw_attach st' ss' r sh BS nm w JF) Hz J).
intros w0 _ W0. cbn [tl_st tl_ss]. rewrite (jtext_dead _ _ Hd). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_revalue : forall m m' ts ts' l l' k k' kk a a' dw,
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive (tl_st l') = false ->
(forall w0, lw l = Some w0 -> exists w', lw l' = Some w' /\ w' <= w0 + dw) ->
dw + jpi (tl_st l') (tl_ss l') <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l l' k k' kk a a' dw Hl E1 E2 E3 E4 Hz PJ P Hk Hd HW H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
destruct (JL_jw _ _ _ J) as (W & EW).
assert (Lw : exists w0, lw l = Some w0).
{ destruct ts as [d lv co pb pbs x o os obs]. cbn [t_levels t_depth] in Hl. unfold jw in EW. cbn [t_levels t_depth] in EW.
destruct (jwl lv (S d)) as [A|] eqn:EA; [| discriminate EW]. exact (jwl_nth lv (S d) d l A EA Hl ltac:(lia)). }
destruct Lw as (w0 & Lw0). destruct (HW w0 Lw0) as (w' & Lw' & LE).
eapply (JL_lvl ts ts' l l' g _ a a' w' Hl E1 E2 E3 E4 Lw' Hz J).
intros w1 Lw1 _. rewrite Lw0 in Lw1. injection Lw1 as <-. rewrite (jtext_dead _ _ Hd). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma lw_recbs : forall l st' ss' cbs' s w0, tl_cs l = Some s -> lw l = Some w0 ->
(forall w, jtx s (tl_cbs l) = Some (w, []) -> jtx s cbs' = Some (w, [])) ->
lw (TL st' ss' (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l)) = Some w0.
Proof.
intros l st' ss' cbs' s w0 Hcs Lw JX. unfold lw in *. cbn [tl_cs tl_cbs tl_nbs]. rewrite Hcs in *. cbn [vw] in *.
destruct (jtx s (tl_cbs l)) as [[w [|? ?]]|] eqn:J; try discriminate Lw. rewrite (JX w eq_refl). exact Lw.
Qed.

Lemma lw_aadd : forall l kids os obs cbs' st' ss' w0 b, tl_cs l = Some (Sarr kids) -> lw l = Some w0 -> vw os obs = Some b -> (os = None -> obs = []) ->
(forall w wv, jtx (Sarr kids) (tl_cbs l) = Some (w, []) -> jtx_opt os obs = Some (wv, []) -> jtx (Sarr (kids ++ [os])) cbs' = Some (w + (2 + wv), [])) ->
exists w', lw (TL st' ss' (tl_cur l) (Some (Sarr (kids ++ [os]))) cbs' (tl_name l) (tl_nbs l)) = Some w' /\ w' <= w0 + b + 6.
Proof.
intros l kids os obs cbs' st' ss' w0 b Hcs Lw Vb Hn JX. destruct (lw_arr l kids Hcs w0 Lw) as (w & Jw & ->). destruct (vw_kid os obs b Vb Hn) as (wv & Jv & Lv).
exists (w + (2 + wv) + nw (tl_nbs l)). split; [exact (lw_container _ _ _ _ _ _ _ _ (JX w wv Jw Jv)) | unfold NULL_W in Lv; lia].
Qed.

Lemma lw_oadd : forall l kids kids' os obs cbs' st' ss' nm nn w0 b, tl_cs l = Some (Sobj kids) -> lw l = Some w0 -> vw os obs = Some b -> (os = None -> obs = []) ->
tl_nbs l = [(nm, nn)] ->
(forall w wv nm0 nn0, tl_nbs l = [(nm0, nn0)] -> jtx (Sobj kids) (tl_cbs l) = Some (w, []) -> jtx_opt os obs = Some (wv, []) ->
exists w', jtx (Sobj kids') cbs' = Some (w', []) /\ w' <= w + key_w nn0 + wv) ->
exists w', lw (TL st' ss' (tl_cur l) (Some (Sobj kids')) cbs' 0 []) = Some w' /\ w' <= w0 + b + 4.
Proof.
intros l kids kids' os obs cbs' st' ss' nm nn w0 b Hcs Lw Vb Hn Hnbs JX. destruct (lw_obj l kids Hcs w0 Lw) as (w & Jw & ->). destruct (vw_kid os obs b Vb Hn) as (wv & Jv & Lv).
destruct (JX w wv nm nn Hnbs Jw Jv) as (w' & Jw' & Lw'). exists (w' + nw []). split; [exact (lw_container _ _ _ _ _ _ _ _ Jw')|].
rewrite Hnbs. cbn [nw snd]. unfold NULL_W in Lv. lia.
Qed.

Lemma PBJ_add : forall m m' ts ts' l l' k k' kk a a' dw,
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts ->
zin (tl_st l) [ST_array_add; ST_ovadd] = true -> zin (tl_st l') [ST_array_add; ST_ovadd] = false ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive (tl_st l') = false ->
(forall w0 b, lw l = Some w0 -> vw (t_objs ts) (t_objbs ts) = Some b -> exists w', lw l' = Some w' /\ w' <= w0 + b + dw) ->
dw + jpi (tl_st l') (tl_ss l') <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l l' k k' kk a a' dw Hl E1 E2 Hz Hz' PJ P Hk Hd HW H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
destruct J as (W & EW & LW).
assert (X : exists w0 b, lw l = Some w0 /\ vw (t_objs ts) (t_objbs ts) = Some b).
{ destruct ts as [d lv co pb pbs x o os obs]. cbn [t_levels t_depth t_objs t_objbs] in *. unfold jw in EW. cbn [t_levels t_depth t_objs t_objbs] in EW.
rewrite (cur_st_ofJ _ _ l) in EW by exact Hl. unfold ow in EW. rewrite Hz in EW.
destruct (jwl lv (S d)) as [A|] eqn:EA; [| discriminate EW]. destruct (vw os obs) as [b|] eqn:Eb; [| discriminate EW].
destruct (jwl_nth lv (S d) d l A EA Hl ltac:(lia)) as (w0 & Lw0). exists w0, b. split; [exact Lw0 | reflexivity]. }
destruct X as (w0 & b & Lw0 & Eb). destruct (HW w0 b Lw0 Eb) as (w' & Lw' & LE).
eapply (JL_add ts ts' l l' g _ a a' w' Hl E1 E2 Lw' Hz Hz'); [exists W; split; [exact EW | exact LW] |].
intros w1 b1 Lw1 Eb1. rewrite Lw0 in Lw1. injection Lw1 as <-. rewrite Eb in Eb1. injection Eb1 as <-.
rewrite (jtext_dead _ _ Hd). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_restate_at : forall m m' ts ts' l l' k g' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PBJ m ts k a -> PBOKat m' ts' g' -> g' <= t_co ts' + kk ->
jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' l l' k g' kk a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz PJ P Hg H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists g'. split; [exact P|]. split; [exact Hg|].
eapply (JL_lvl_restate ts ts' l l' g g' a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_push : forall m m' ts l lp k k' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l -> (S (t_depth ts) < length (t_levels ts))%nat ->
tl_cs lp = tl_cs l -> tl_cbs lp = tl_cbs l -> tl_nbs lp = tl_nbs l ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
PBJ m ts k a -> PBOK m' (ts_push ts lp) k' -> k' <= kk ->
26 <= jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' (ts_push ts lp) kk a'.
Proof.
intros m m' ts l lp k k' kk a a' Hl Hlen C1 C2 C3 Hz PJ P Hk H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co (ts_push ts lp) + k'). split; [exact P|]. split; [lia|].
eapply (JL_push ts l lp g _ a a' Hl Hlen C1 C2 C3 Hz J). pose proof (jtext_nonneg (tl_st l) g G0). lia.
Qed.

Lemma PBJ_pop : forall m m' ts dp l lp k k' kk a,
t_depth ts = S dp -> nth_error (t_levels ts) (S dp) = Some l -> nth_error (t_levels ts) dp = Some lp ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false -> zin (tl_st lp) [ST_array_add; ST_ovadd] = true ->
PBJ m ts k a ->
PBOK m' (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) k' -> k' <= kk ->
jpi (tl_st lp) (tl_ss lp) <= jpi (tl_st l) (tl_ss l) ->
PBJ m' (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) kk a.
Proof.
intros m m' ts dp l lp k k' kk a Hd Hl Hlp Hz Hzp PJ P Hk H. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts + k'). split; [unfold PBOK in P; cbn [t_co] in P; exact P|]. split; [cbn [t_co]; lia|].
assert (JP := JL_pop ts dp l lp g a Hd Hl Hlp Hz Hzp J ltac:(pose proof (jtext_nonneg (tl_st l) g G0); lia)).
eapply JL_dead; [| exact JP].
assert (Ec : cur_st (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) = tl_st lp)
by (unfold cur_st; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
rewrite Ec. unfold jlive. cbn [zin existsb] in Hzp |- *. apply orb_prop in Hzp. destruct Hzp as [Hq | Hq]; [| apply orb_prop in Hq; destruct Hq as [Hq | Hq]; [| discriminate Hq]];
apply Z.eqb_eq in Hq; rewrite Hq; reflexivity.
Qed.

Lemma esc_ss_pi : forall st ss c hn, zin st [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = true -> 0 <= ss <= 26 ->
lvl_mode st ss = Some (c, hn) -> jpi0 ss <= 30.
Proof.
intros st ss c hn Hst R Hm.
assert (C : st = ST_string_escape \/ st = ST_escape_unicode \/ st = ST_esc_need_escape \/ st = ST_esc_need_u).
{ cbn [zin existsb] in Hst. repeat (apply orb_prop in Hst as [Hst | Hst]; [apply Z.eqb_eq in Hst; auto |]). discriminate Hst. }
assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
destruct C as [-> | [-> | [-> | ->]]]; do 27 (destruct k as [|k]; [vm_compute in Hm; first [discriminate Hm | vm_compute; discriminate] |]); lia.
Qed.

Lemma eatws_ss_dead : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_eatws ss = Some (c, hn) -> jlive ss = false.
Proof.
intros ss c hn R Hm.
assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in Hm; first [discriminate Hm | reflexivity] |]); lia.
Qed.

Lemma PBOK_of_at : forall m ts b, PBOKat m ts b -> PBOK m ts (b - t_co ts).
Proof. intros m ts b H. unfold PBOK. replace (t_co ts + (b - t_co ts)) with b by lia. exact H. Qed.

Lemma PBJ_keep : forall m m' ts ts' k k' kk a a',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
PBJ m ts k a -> PBOK m' ts' k' -> k' <= kk -> jlive (cur_st ts) = false -> a <= a' -> PBJ m' ts' kk a'.
Proof.
intros m m' ts ts' k k' kk a a' E1 E2 E3 E4 PJ P Hk Hd Ha. destruct (PBJ_open _ _ _ _ PJ) as (g & G0 & _ & _ & J).
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
assert (Ec : cur_st ts' = cur_st ts) by (unfold cur_st; rewrite E1, E2; reflexivity).
eapply JL_dead; [rewrite Ec; exact Hd|]. eapply (JL_keep ts ts' g g a a' E1 E2 E3 E4 (Z.le_refl _) Ha J).
Qed.

Lemma PBJ_attach_g : forall m' ts ts' l st' ss' r sh BS nm g k' kk a a' w,
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) (TL st' ss' r (Some sh) BS nm []) -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a -> PBOK m' ts' k' -> k' <= kk -> jlive st' = false -> jfresh sh BS w ->
w + jpi st' ss' <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m' ts ts' l st' ss' r sh BS nm g k' kk a a' w Hl E1 E2 E3 E4 Hz J P Hk Hd JF H.
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
eapply (JL_lvl ts ts' l _ g _ a a' w Hl E1 E2 E3 E4 (lw_attach st' ss' r sh BS nm w JF) Hz J).
intros w0 _ W0. cbn [tl_st tl_ss]. rewrite (jtext_dead _ _ Hd). lia.
Qed.

Lemma PBJ_name_g : forall m' ts ts' l st' ss' r nn g k' kk a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) r [(r, nn)]) -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a -> PBOK m' ts' k' -> k' <= kk -> jlive st' = false ->
key_w nn + jpi st' ss' <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
PBJ m' ts' kk a'.
Proof.
intros m' ts ts' l st' ss' r nn g k' kk a a' Hl E1 E2 E3 E4 Hz J P Hk Hd H.
exists (t_co ts' + k'). split; [exact P|]. split; [lia|].
destruct (JL_jw _ _ _ J) as (W & EW).
assert (Lw : exists w0, lw l = Some w0).
{ destruct ts as [d lv co pb pbs x o os obs]. cbn [t_levels t_depth] in Hl. unfold jw in EW. cbn [t_levels t_depth] in EW.
destruct (jwl lv (S d)) as [A|] eqn:EA; [| discriminate EW]. exact (jwl_nth lv (S d) d l A EA Hl ltac:(lia)). }
destruct (lw_value l Lw) as (v & Ev & Lw0).
eapply (JL_lvl ts ts' l _ g _ a a' _ Hl E1 E2 E3 E4 (lw_rename l st' ss' r [(r, nn)] v Ev) Hz J).
intros w1 Lw1 _. rewrite Lw0 in Lw1. injection Lw1 as <-. cbn [tl_st tl_ss nw snd]. rewrite (jtext_dead _ _ Hd). pose proof (nw_nonneg (tl_nbs l)). lia.
Qed.

End RC__1.

Ltac jl_c :=
repeat match goal with
| |- context [jlive ?s] => let v := eval vm_compute in (jlive s) in (first [constr_eq v true | constr_eq v false]; change (jlive s) with v)
| |- context [jpi ?a ?b] => let v := eval vm_compute in (jpi a b) in (lazymatch v with Z0 => idtac | Zpos _ => idtac end; change (jpi a b) with v)
end.

Ltac jl_zin Hst := rewrite ?Hst; cbn [tl_st]; first [reflexivity | etransitivity; [eassumption | reflexivity]].
Ltac jl_unf := repeat match goal with x := _ : tlevel |- _ => subst x end; unfold ts_lvl, ts_pbs, ts_set_co, ts_set_x, ts_lvl_obj, ts_push; cbn [tl_st tl_ss t_co].
Ltac jl_rng := repeat match goal with |- context [jpi0 ?x] => lazymatch goal with H : 0 <= jpi0 x <= 48 |- _ => fail | _ => pose proof (jpi0_range x) end end.
Ltac jl_arith := jl_unf; unfold jtext, JC1; jl_c; cbv iota; rewrite ?jpi_eatws, ?jpi_self; repeat match goal with |- context [if jlive ?s then _ else _] => destruct (jlive s) end; jl_rng; lia.
Ltac jl_dead := jl_unf; first [jl_c; reflexivity | eassumption].

Ltac pbj_rs TS l PBK PBK' Hl Hst :=
eapply (PBJ_restate _ _ TS _ l _ _ _ _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst
| exact PBK | exact PBK' | lia | rewrite ?Hst; jl_dead | rewrite ?Hst; jl_arith].

Ltac pbj_rsg TS l g JLg PBK' Hl Hst :=
eapply (PBJ_restate_g _ TS _ l _ g _ _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst
| exact JLg | exact PBK' | lia | rewrite ?Hst; jl_arith].
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqh Qvmy Qawr QJZd.Mqb QJZd.Mqc QW22.Mq4 QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mqe Qeia.Mq7 QWrz.Mq6 Qw5U.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import QEUF.Mq3.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma a4_static_in_img : forall a, hl_client_static A4L a -> hl_img_lo A4H <= a < hl_img_hi A4H.
Proof. intros a H. cbn [hl_client_static hl_img_lo hl_img_hi hla_base A4L A4H] in *. unfold a4_client_static in H. lia. Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma presD_own_pres : forall A LBall LM FRS B m md F R SP m' (Lo : list blk),
HEAPA A4L HIx A LBall LM ((F, 2) :: FRS) B m md ->
heap_presD R (LBall ++ LM ++ fr_ivs A4L ((F, 2) :: FRS)) SP m m' ->
F <= R -> R + 8 <= F + 248 -> alloc_ceiling <= SP ->
(forall a n, In (a, n) Lo -> F <= a /\ a + n <= F + 248 /\ (a + n <= R \/ R + 8 <= a)) ->
heap_pres A4H ((LBall ++ LM ++ (shad A4L F, 32) :: fr_ivs A4L FRS) ++ Lo) SP m m'.
Proof.
intros A LBall LM FRS B m md F R SP m' Lo HP HPD HR1 HR2 HSP HLo a Ha Hc.
assert (INF : In (F, 2) ((F, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & HF0 & HFc & HFimg & _). rewrite fr_size_2 in HFc, HFimg.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp. rewrite fr_size_2 in HFapp. cbn [hl_sb A4L] in HFapp.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg. change ((2 ^ 47 - 1) / 8) with 17592186044415 in HFapp. unfold A_SB in HFapp.
apply (HPD a Ha).
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; exact Hc | right; left; exact Hc | right; right].
apply in_app_or in Hb as [Hb | Hb].
+ apply in_app_or in Hb as [Hb | Hb]; [exists b; split; [apply in_or_app; left; exact Hb | exact Hr]|].
apply in_app_or in Hb as [Hb | Hb]; [exists b; split; [apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hr]|].
destruct Hb as [<- | Hb].
* exists (shad A4L F, 32). split; [| exact Hr]. apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. apply fr_ivs_shadow. exact INF.
* exists b. split; [| exact Hr]. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
+ destruct b as [ba bn]. destruct (HLo ba bn Hb) as (H1 & H2 & _). cbn [blk_addr blk_size fst snd] in Hr.
exists (F, fr_size 2 - 8). split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF|]. cbn [blk_addr blk_size fst snd]. rewrite fr_size_2. lia.
- intros HD. destruct Hc as [Hc | [Hc | (b & Hb & Hr)]].
+ lia.
+ pose proof (a4_static_in_img a Hc) as Hi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
+ apply in_app_or in Hb as [Hb | Hb].
* apply in_app_or in Hb as [Hb | Hb].
{ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_introl Hb))) as Hd. rewrite fr_size_2 in Hd. lia. }
apply in_app_or in Hb as [Hb | Hb].
{ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_intror Hb))) as Hd. rewrite fr_size_2 in Hd. lia. }
destruct Hb as [<- | Hb].
{ cbn [blk_addr blk_size fst snd] in Hr. unfold shad in Hr. cbn [hl_sb A4L] in Hr. unfold A_SB in *. Z.div_mod_to_equations. lia. }
destruct (in_fr_ivs _ _ Hb) as (F' & k' & HF' & [-> | ->]); cbn [blk_addr blk_size fst snd] in Hr.
{ assert (NE : F <> F') by (intros E; exact (own_frame_ne HIx _ _ _ _ _ _ _ _ _ _ HP HF' (eq_sym E))).
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ F 2 F' k' HP INF (or_intror HF') NE) as Hd. rewrite fr_size_2 in Hd. lia. }
{ pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HF')) as (Hk' & _ & HF'0 & HF'c & _).
pose proof (fr_shadow_len_bnd k' Hk') as SLB. pose proof alloc_ceiling_range as ACR. pose proof (fr_size_pos k' ltac:(lia)) as FSP.
unfold shad in Hr. cbn [hl_sb A4L] in Hr. unfold A_SB in *. Z.div_mod_to_equations. lia. }
* destruct b as [ba bn]. destruct (HLo ba bn Hb) as (_ & _ & H3). cbn [blk_addr blk_size fst snd] in Hr. lia.
Qed.

Lemma pe_frameAX_presD : forall pf pa (L : list blk) SP m m' nb pj sv ffa ffb shc (rj v : word) R,
heap_pres A4H L SP m m' -> SP <= pf_spf pf -> pe_geomA pf pa ->
In (shA (pa_F pa), 32) L -> In (pa_F pa, R - pa_F pa) L -> In (R + 8, pa_F pa + 248 - (R + 8)) L ->
R = pa_F pa + Z.of_nat (cells_size ffa) ->
Z.of_nat (cells_size ffa) + 8 + Z.of_nat (cells_size ffb) = 248 -> Z.of_nat (cells_size shc) <= 32 ->
pe_frameAX m pf pa nb pj sv (ffa ++ [C8 rj] ++ ffb) shc ->
rw_cells asegs m' R [C8 v] ->
pe_frameAX m' pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc.
Proof.
intros pf pa L SP m m' nb pj sv ffa ffb shc rj v R HPR HSP GEO InS InA InB ER SZ SZS (SL & GP & SV & FF & FSH) RC.
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF as [FFa FFm]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFm as [_ FFb].
cbn [cells_size csize Nat.add] in FFb.
split; [| split; [| split; [| split]]].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SL | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact GP | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SV | left; lia].
- apply (proj2 (rw_cells_app asegs _ _ _ _)). split.
+ eapply (heap_pres_rw_cells A4H); [exact HPR | exact FFa | right; right]. exists (pa_F pa, R - pa_F pa). split; [exact InA | cbn [blk_addr blk_size fst snd]; lia].
+ apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [rewrite <- ER; exact RC|]. cbn [cells_size csize Nat.add].
eapply (heap_pres_rw_cells A4H); [exact HPR | exact FFb | right; right]. exists (R + 8, pa_F pa + 248 - (R + 8)). split; [exact InB | cbn [blk_addr blk_size fst snd]; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FSH | right; right]. exists (shA (pa_F pa), 32). split; [exact InS | cbn [blk_addr blk_size fst snd]; lia].
Qed.

Lemma disjoint_from_below : forall (W : list (Z * Z)) (a n c : Z), 0 <= n -> Forall (fun iv => snd iv <= c) W -> c <= a -> disjoint_from W a n.
Proof.
intros W a n c Hn HW Hc. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [disjoint_from fst snd] in *. split; [lia | apply IH; exact HW].
Qed.
Lemma pe_frameAX_writeG : forall pf pa nb pj sv ffc shc ffc' shc' m mc lo (W : list (Z * Z)),
PE_STATIC_A HIx pf pa lo -> pe_frameAX m pf pa nb pj sv ffc shc -> munch W m mc -> wmono asegs m mc ->
Forall (fun iv => snd iv <= alloc_ceiling) W ->
rw_cells asegs mc (pa_F pa) ffc' -> rw_cells asegs mc (shA (pa_F pa)) shc' ->
pe_frameAX mc pf pa nb pj sv ffc' shc'.
Proof.
intros pf pa nb pj sv ffc shc ffc' shc' m mc lo W STC (SLOTS & GAP & SAVED & _ & _) MU WM HW FFc FSHc.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
split; [| split; [| split; [| split; [exact FFc | exact FSHc]]]].
- eapply rw_cells_transport; [exact SLOTS | exact MU | exact WM |]. eapply disjoint_from_below; [lia | exact HW | lia].
- eapply rw_cells_transport; [exact GAP | exact MU | exact WM |]. eapply disjoint_from_below; [lia | exact HW | lia].
- eapply rw_cells_transport; [exact SAVED | exact MU | exact WM |]. eapply disjoint_from_below; [lia | exact HW | lia].
Qed.

Lemma payload_locA_presL : forall pf pa LB0 FRS A LB LM FR B m0 md (L : list blk) SP m m',
HEAPA A4L HIx A LB LM FR B m0 md -> incl FRS FR -> incl (fr_ivs A4L FRS) L ->
heap_pres A4H L SP m m' ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) -> (pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m').
Proof.
intros pf pa LB0 FRS A LB LM FR B m0 md L SP m m' HP HinclF HinclL HPR [L0 | PL]; [left; exact L0 | right].
destruct PL as [BL | (Fh & kh & HFh & HF1 & HF2 & UPS)]; [left; exact BL | right].
exists Fh, kh. split; [exact HFh|]. split; [exact HF1|]. split; [exact HF2|].
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (HinclF _ HFh)) as (Hks & HFal & HF0 & HFc & _).
pose proof UPS as (Hn & _).
assert (HF8 : Fh mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kh)); [| apply Z.mod_divide; [pose proof (fr_size_pos kh ltac:(lia)); lia | exact HFal]].
exists (2 ^ kh). unfold fr_size. lia. }
eapply unpoisoned_pres_heap; [exact UPS | exact HPR | apply HinclL; apply fr_ivs_shadow; exact HFh | |].
- unfold shadow_span_lo, shad. cbn [hl_sb A4L]. unfold A_SB. Z.div_mod_to_equations. lia.
- unfold shadow_span_hi, shad. cbn [hl_sb A4L]. unfold A_SB. rewrite (fr_size_shadow kh) in HF2 by lia.
unfold fr_shadow_len in *. Z.div_mod_to_equations. lia.
Qed.

Lemma PE_REST_A_callL : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 (L : list blk),
PE_STATIC_A HIx pf pa lo ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B ts errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H L (pf_spf pf) m1 m2 ->
incl LB0 L -> incl LM L -> incl (fr_ivs A4L FRS) L ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
(forall i l, nth_error (t_levels ts2) i = Some l -> lvl_cur asegs A4F m2 (t_depth ts2) i l) ->
(if zin (cur_st ts2) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts2) m2 (t_objbs ts2) (t_obj ts2) else t_objbs ts2 = []) ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BUD pf pa ts2 B2 ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 L STC
(HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD) VM12 HPRc Hincl HinclM HinclF HP2 LV2 OBJ2 ST2 ERR2 BUD2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
split; [exact HP2|]. split; [exact LV2|]. split; [exact OBJ2|]. split; [exact ST2|]. split; [exact ERR2|].
assert (SBin2 := payload_locA_presL pf pa LB0 FRS _ _ _ _ _ _ _ L _ _ _ HP (incl_tl _ (incl_refl _)) HinclF HPRc SBin).
split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split; [| split; [| exact BUD2]]]]]].
- eapply payload_presA; [exact HPRc | exact Hincl | exact HinclF | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply Hincl; exact Hb|].
apply in_app_or in Hb as [Hb | Hb]; [apply HinclM; exact Hb | apply HinclF; exact Hb].
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_pres; [exact HPRc | exact G].
Qed.

Lemma pe_parse_i64_cX :
forall (entry : Z), parse_i64_A_stmt HIx entry ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP buf cap R : Z) (rj : word) (ffa ffb shc : list cell)
(ra gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv (pe_frameAX m pf pa nb pj sv (ffa ++ [C8 rj] ++ ffb) shc) ->
PBOKat m ts kP ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
R = pa_F pa + Z.of_nat (cells_size ffa) -> Z.of_nat (cells_size ffa) + 8 + Z.of_nat (cells_size ffb) = 248 -> Z.of_nat (cells_size shc) = 32 ->
R mod 8 = 0 -> unpoisoned asegs m A_SB R 8 ->
Z.of_nat (length FRS) + 1 < 4096 ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 errv2 (rv : Z) (v w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
(rv = 0 \/ rv = 1) ->
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B ts errv2 (pe_frameAX m2 pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc) ->
PBOKat m2 ts kP ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 rv) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Proof.
intros entry PI64. intros until fc. intros STC INV PBK Epbs ER SZ SZS R8 UNPR NFR RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _ & _ & _ & _ & _ & _ & BUD1).
pose proof PBK as (buf' & bpos & cap' & pre & post & Epbs' & Lpre & CORE1 & Hbp).
rewrite Epbs in Epbs'. injection Epbs' as <- <-.
destruct CORE1 as (Hbp0 & Hcap & Hlen & _ & BUFC).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
destruct (first_nul_splitA pre post) as (str & rest & Econt & NONUL & Lstr).
rewrite Econt in BUFB. change (str ++ QgoP.b0 :: rest) with (str ++ [QgoP.b0] ++ rest) in BUFB. rewrite app_assoc in BUFB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in BUFB as [SRC _].
assert (LenC : Z.of_nat (length str) + 1 <= cap).
{ rewrite <- Hlen, Econt, !length_app. cbn [length]. lia. }
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INbuf : In (buf, cap) RB) by (unfold RB, pe_blocksA, tstate_blocks; rewrite Epbs; apply in_or_app; left; cbn [app]; right; left; reflexivity).
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (SPF : lo <= pf_spf pf - PI64_STK_A /\ pf_spf pf mod 32 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ unfold PI64_STK_A. clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [exact Gspf|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
pose proof FR1 as (_ & _ & _ & FF1 & _).
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [_ FFm]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFm as [RC1 _]. rewrite <- ER in RC1.
eapply (PI64 ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B str buf R lo rj errv);
[ exact HP1 | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1 | rewrite unsigned_lit by lia; exact SPF2
| rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity | exact SRC | exact NONUL
| exists buf, cap; split; [exact INbuf | lia]
| eapply (unpoisoned_of_blk HIx); [exact HP1 | exact INbuf | lia | lia | lia]
| exists (pa_F pa), 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| exact RC1 | exact UNPR | exact R8 | cbn [length]; lia | ].
intros ms2 md2 m2 A2 rv v errv2 RS2 VM2 ST2 HPD2 Hrv RC2 ERR2 HP2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & ->).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPD2 by lia.
set (Lo := [(pa_F pa, R - pa_F pa); (R + 8, pa_F pa + 248 - (R + 8))]).
assert (HPR2 : heap_pres A4H ((RB ++ LM ++ (shad A4L (pa_F pa), 32) :: fr_ivs A4L FRS) ++ Lo) (pf_spf pf) m m2).
{ eapply (presD_own_pres A RB LM FRS B m md (pa_F pa) R (pf_spf pf) m2 Lo); [exact HP1 | exact HPD2 | lia | lia | lia |].
intros a n [E | [E | []]]; injection E as <- <-; lia. }
set (LL := (RB ++ LM ++ (shad A4L (pa_F pa), 32) :: fr_ivs A4L FRS) ++ Lo) in *.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc).
{ eapply (pe_frameAX_presD pf pa LL (pf_spf pf) m m2 nb pj sv ffa ffb shc rj v R); [exact HPR2 | lia | exact GEO | | | | exact ER | exact SZ | lia | exact FR1 | exact RC2].
- unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. left. reflexivity.
- unfold LL, Lo. apply in_or_app; right. left. reflexivity.
- unfold LL, Lo. apply in_or_app; right. right. left. reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl INq))))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOKat m2 ts kP).
{ eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B ts errv2).
{ eapply (PE_REST_A_callL pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B ts ts errv errv2 LL); [exact STC | exact REST1 | exact VM2 | exact HPR2 | | | | exact HP2 | | | exact ST2 | exact ERR2 | exact BUD1].
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; left. apply LB0R. exact Hb.
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb.
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. right. exact Hb.
- intros i li Hli. eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ1].
eapply (jopt_agree asegs A4F); [exact OBJ1 | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
eapply (K m2 md2 A2 errv2 rv v); [exact Hrv | | exact PBKa].
split; [| exact REST2]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOKat_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2].
Qed.

Definition STRTOD_STK_A : Z := 12288.
Definition strtod_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(str : list byte) (SA R lo : Z) (rj errv : word),
HEAPA A4L HIx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - STRTOD_STK_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 R ->
bytes_at asegs m SA (str ++ [QgoP.b0]) -> ~ In QgoP.b0 str ->
Z.of_nat (length str) < 2^31 ->
(exists a n, In (a, n) LB /\ a <= SA /\ SA + Z.of_nat (length str) + 1 <= a + n) ->
(exists Fc kc, In (Fc, kc) FRS /\ Fc <= R /\ R + 8 <= Fc + fr_size kc - 8) ->
rw_cells asegs m R [C8 rj] -> R mod 8 = 0 ->
frm0 fc ->
(forall ms' m' (a0' v e' : word),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m' ms' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_presD R (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' R [C8 v] -> rw_cells asegs m' A_ERRNO [C4 e'] ->
HEAPA A4L HIx A LB LM FRS B m' md ->
AJ5 A4L HIx A T md ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdccb8) fc None m (seg_rom asegs)).

Lemma pe_strtod_cX :
strtod_A_stmt ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP buf cap R : Z) (rj : word) (ffa ffb shc : list cell)
(ra gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv (pe_frameAX m pf pa nb pj sv (ffa ++ [C8 rj] ++ ffb) shc) ->
PBOKat m ts kP ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
R = pa_F pa + Z.of_nat (cells_size ffa) -> Z.of_nat (cells_size ffa) + 8 + Z.of_nat (cells_size ffb) = 248 -> Z.of_nat (cells_size shc) = 32 ->
R mod 8 = 0 -> frm0 fc ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 errv2 (a0' v w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_AX HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts errv2 (pe_frameAX m2 pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc) ->
PBOKat m2 ts kP ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0' w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xdccb8) fc None m (seg_rom asegs)).
Proof.
intros PI64. intros until fc. intros STC INV PBK Epbs ER SZ SZS R8 FRM RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _ & _ & _ & _ & _ & _ & BUD1).
pose proof PBK as (buf' & bpos & cap' & pre & post & Epbs' & Lpre & CORE1 & Hbp).
rewrite Epbs in Epbs'. injection Epbs' as <- <-.
destruct CORE1 as (Hbp0 & Hcap & Hlen & _ & BUFC).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
destruct (first_nul_splitA pre post) as (str & rest & Econt & NONUL & Lstr).
rewrite Econt in BUFB. change (str ++ QgoP.b0 :: rest) with (str ++ [QgoP.b0] ++ rest) in BUFB. rewrite app_assoc in BUFB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in BUFB as [SRC _].
assert (LenC : Z.of_nat (length str) + 1 <= cap).
{ rewrite <- Hlen, Econt, !length_app. cbn [length]. lia. }
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INbuf : In (buf, cap) RB) by (unfold RB, pe_blocksA, tstate_blocks; rewrite Epbs; apply in_or_app; left; cbn [app]; right; left; reflexivity).
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (SPF : lo <= pf_spf pf - STRTOD_STK_A /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ unfold STRTOD_STK_A. clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
pose proof FR1 as (_ & _ & _ & FF1 & _).
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [_ FFm]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFm as [RC1 _]. rewrite <- ER in RC1.
eapply (PI64 ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B str buf R lo rj errv);
[ exact HP1 | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1 | rewrite unsigned_lit by lia; exact SPF2
| rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity | exact SRC | exact NONUL | lia
| exists buf, cap; split; [exact INbuf | lia]
| exists (pa_F pa), 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| exact RC1 | exact R8 | exact FRM | ].
intros ms2 m2 a0' v errv2 RS2 ST2 HPD2 RC2 ERR2 HP2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
pose proof (model_vm_only_refl (cfg_model md)) as VM2. set (md2 := md) in *. set (A2 := A) in *.
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPD2 by lia.
set (Lo := [(pa_F pa, R - pa_F pa); (R + 8, pa_F pa + 248 - (R + 8))]).
assert (HPR2 : heap_pres A4H ((RB ++ LM ++ (shad A4L (pa_F pa), 32) :: fr_ivs A4L FRS) ++ Lo) (pf_spf pf) m m2).
{ eapply (presD_own_pres A RB LM FRS B m md (pa_F pa) R (pf_spf pf) m2 Lo); [exact HP1 | exact HPD2 | lia | lia | lia |].
intros a n [E | [E | []]]; injection E as <- <-; lia. }
set (LL := (RB ++ LM ++ (shad A4L (pa_F pa), 32) :: fr_ivs A4L FRS) ++ Lo) in *.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv (ffa ++ [C8 v] ++ ffb) shc).
{ eapply (pe_frameAX_presD pf pa LL (pf_spf pf) m m2 nb pj sv ffa ffb shc rj v R); [exact HPR2 | lia | exact GEO | | | | exact ER | exact SZ | lia | exact FR1 | exact RC2].
- unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. left. reflexivity.
- unfold LL, Lo. apply in_or_app; right. left. reflexivity.
- unfold LL, Lo. apply in_or_app; right. right. left. reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl INq))))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOKat m2 ts kP).
{ eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B ts errv2).
{ eapply (PE_REST_A_callL pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B ts ts errv errv2 LL); [exact STC | exact REST1 | exact VM2 | exact HPR2 | | | | exact HP2 | | | exact ST2 | exact ERR2 | exact BUD1].
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; left. apply LB0R. exact Hb.
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb.
- intros b Hb. unfold LL. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. right. exact Hb.
- intros i li Hli. eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ1].
eapply (jopt_agree asegs A4F); [exact OBJ1 | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
eapply (K m2 errv2 a0' v); [| exact PBKa | exact FS2 | exact FRM2].
split; [| exact REST2]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOKat_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2].
Qed.

Lemma jval_int_blocks : forall m BS p rc, jval asegs A4F Sint m BS p rc -> In (p, 56) BS /\ (length BS <= 3)%nat.
Proof.
intros m BS p rc J. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (cty & v & junk & -> & _)). subst BS.
split; [left; reflexivity|].
destruct OP as [[_ ->] | [_ (buf & bpos & size & content & -> & _)]]; cbn; lia.
Qed.

Lemma jval_dbls_blocks : forall m BS p rc, jval asegs A4F (Sdouble true) m BS p rc -> In (p, 48) BS /\ (length BS <= 4)%nat.
Proof.
intros m BS p rc J. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (bits & ud & udn & uds & -> & _)). subst BS.
split; [left; reflexivity|].
destruct OP as [[_ ->] | [_ (buf & bpos & size & content & -> & _)]]; cbn; lia.
Qed.

Definition jo_new_int_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPA A4L HIx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newint_costB <= bB B -> 1 <= bD B ->
(forall ms' md' A', QJZd.Mqb.new_obj_A_post HIx Sint ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma pe_new_int_wX :
forall (entry : Z), jo_new_int_A_stmt entry ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (ffc shc : list cell)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 errv (pe_frameAX m pf pa nb pj sv ffc shc) ->
Z.of_nat (cells_size ffc) <= 248 -> Z.of_nat (cells_size shc) <= 32 ->
PBOKat m ts kP -> newint_costB <= bB B -> 1 <= bD B ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc)) \/
(r <> 0 /\ exists BS, (length BS <= 3)%nat /\ jfresh Sint BS 20 /\ 0 < r < 2^62 /\
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some Sint) BS 1 errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc))) ->
PBOKat m2 ts kP -> bB B - newint_costB <= bB B2 -> bD B - 1 <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Proof.
intros entry NEWINT. intros until fc. intros STC WIN SZF SZS PBK COST COSTD RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 32 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
eapply (NEWINT ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B lo errv);
[ exact HP1 | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| exact COST | exact COSTD | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv ffc shc).
{ eapply pe_frameAX_pres; [exact HPRc | lia | exact GEO | | | exact SZF | exact SZS | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
eapply (K m2 md2 A2 B2 errv2 r); [| | exact HB2 | exact HD2 | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & HP2 & PIN)].
+ left. split; [reflexivity|].
eapply (PE_WINX_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity | exact FR2].
+ right. split; [exact Hr|]. exists BS.
destruct (jval_int_blocks _ _ _ _ J2) as [INr LEN3].
split; [exact LEN3|]. split; [exact (jfresh_int asegs A4F _ _ _ _ J2 PIN)|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 56 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WINX_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some Sint) BS 1 errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]] | exact FR2].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Lemma pe_new_double_s_wX :
new_double_s_A_stmt HIx ->
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP buf cap v2 ra2 : Z) (ffc shc : list cell)
(ra gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 errv (pe_frameAX m pf pa nb pj sv ffc shc) ->
Z.of_nat (cells_size ffc) <= 248 -> Z.of_nat (cells_size shc) <= 32 ->
PBOKat m ts kP -> t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] ->
newdbls_costB kP <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f57c) (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc)) \/
(r <> 0 /\ exists BS, (length BS <= 4)%nat /\ (exists w, jfresh (Sdouble true) BS w /\ w <= kP + 16) /\ 0 < r < 2^62 /\
PE_WINX HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sdouble true)) BS 1 errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc))) ->
PBOKat m2 ts kP -> bB B - newdbls_costB kP <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 json_object_new_double_s_A_entry) fc None m (seg_rom asegs)).
Proof.
intros NEWDBLS. intros until fc. intros STC WIN SZF SZS PBK Epbs COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 112 - 16 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof PBK as (buf' & bpos & cap' & pre & post & Epbs' & Lpre & CORE1 & Hbp).
rewrite Epbs in Epbs'. injection Epbs' as <- <-.
destruct CORE1 as (Hbp0 & Hcap & Hlen & _ & BUFC).
destruct (first_nul_splitA pre post) as (str & rest & Econt & NONUL & Lstr).
assert (LenC : Z.of_nat (length str) + 1 <= cap).
{ rewrite <- Hlen, Econt, !length_app. cbn [length]. lia. }
assert (INbuf : In (buf, cap) RB) by (unfold RB, pe_blocksA, tstate_blocks; rewrite Epbs; apply in_or_app; left; cbn [app]; right; left; reflexivity).
assert (SIB : str_in_block A4H m buf cap (pre ++ [Z_to_bv 8 0] ++ post) buf str).
{ split; [exact BUFC|]. split; [lia|]. split; [lia|]. split; [| exact NONUL].
rewrite Z.sub_diag. change (Z.to_nat 0) with 0%nat. rewrite skipn_O. rewrite Econt. change (str ++ QgoP.b0 :: rest) with (str ++ [QgoP.b0] ++ rest). rewrite app_assoc.
rewrite firstn_app. rewrite length_app. cbn [length]. replace (length str + 1 - (length str + 1))%nat with 0%nat by lia.
rewrite firstn_all2 by (rewrite length_app; cbn [length]; lia). cbn [firstn]. apply app_nil_r. }
pose proof (pe_uw_atX HIx pf pa lo m nb pj sv v2 ra2 ffc shc STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
assert (COST' : newdbls_costB (Z.of_nat (length str)) <= bB B) by (unfold newdbls_costB in *; lia).
eapply (NEWDBLS ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B buf lo buf cap str (pre ++ [Z_to_bv 8 0] ++ post) errv (UWfp ra2 v2));
[ exact HP1 | rewrite !unsigned_lit by lia; exact UWA | exact UWK | exact INbuf | exact SIB | lia
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| exact COST' | cbn [uw_cost]; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | reflexivity | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & _ & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv ffc shc).
{ eapply pe_frameAX_pres; [exact HPRc | lia | exact GEO | | | exact SZF | exact SZS | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
eapply (K m2 md2 A2 B2 errv2 r); [| | unfold newdbls_costB in *; lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & HP2 & PIN)].
+ left. split; [reflexivity|].
eapply (PE_WINX_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity | exact FR2].
+ right. split; [exact Hr|]. exists BS.
destruct (jval_dbls_blocks _ _ _ _ J2) as [INr LEN4].
split; [exact LEN4|]. split; [destruct PIN as (ud & ->); exists (16 + Z.of_nat (length str)); split; [apply jfresh_dbls; lia | lia]|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WINX_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sdouble true)) BS 1 errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]] | exact FR2].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End WithIface.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl Qm5W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QRUw QKQo Q8tj. Import Qu4M.Mq0.
Import QSL3. Import Q3jZ Qmd7 Q22i.
Import Qvbw. Import Qg1M.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import QsKa.Mq9.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QlKV.Mqh QsKa.Mqe Q30W.Mq6 QkXq.Mq6 Q1Y6.Mq3 Q30W QvPk.Mq0 QsKa.Mqd Qiiq QlKV.Mqf Qoif.Mq4. Import QlKV.Mq2. Import Qm5W QjKS.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MJoObjAddMain.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB VBS PBS LM : list blk) (FRS : list frame) (B0 : bud) (KBS : list (list blk)).
Variables (lo p v k kn pb t tbl size : Z) (es : list lent) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - (80 + 96 + 4096 + 144 + HD).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis INK : In (k, kn) LB.
Hypothesis KN : kn <= 2^31.
Hypothesis FRM : frm0 fc.
Hypothesis FRN : Z.of_nat (length FRS) < 4096.
Hypothesis LK1 : length es = length kids.
Hypothesis LK2 : length KBS = length kids.
Hypothesis BB0 : oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B0.
Hypothesis BR0 : 512 * (3 + Z.of_nat (length es) + Z.of_nat (length (concat KBS)) + Z.of_nat (length PBS)) <= bB B0.
Hypothesis BD0 : 0 <= bD B0.
Notation OBS := (OBS PBS KBS p t tbl size es).
Notation OHDR := (OHDR pb t).
Hypothesis Kont : forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_framexA ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
lh_globA m' -> bD B0 <= bD B' ->
((r = 0 /\ exists OBS' kids', jval asegs A4F (Sobj kids') m' OBS' p 1 /\ HEAPAx A' (OBS' ++ LB) LM FRS B' m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)
/\ ( ( Z.of_nat (length kids') = Z.of_nat (length kids) + 1
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length OBS') = Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1
/\ obj_grownA size (Z.of_nat (length kids)) (obj_capA OBS')
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj kids') OBS' = Some (w + (key_w (Z.of_nat (length ks) + 1) + wv), [])))
\/ ( Z.of_nat (length kids') = Z.of_nat (length kids)
/\ bB B0 - 512 * (Z.of_nat (length OBS) + Z.of_nat (length VBS) - Z.of_nat (length OBS')) <= bB B'
/\ Z.of_nat (length OBS') <= Z.of_nat (length OBS) + Z.of_nat (length VBS)
/\ obj_capA OBS' = size
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj kids') OBS' = Some (w', []) /\ w' <= w + wv)))) \/
(r = 2^64 - 1 /\ exists REM, jval asegs A4F (Sobj kids) m' OBS p 1 /\ jopt asegs A4F vs m' VBS v
/\ HEAPAx A' (OBS ++ VBS ++ REM ++ LB) LM FRS B' m' md'
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B')) ->
AJ5 A4L HIx A' T md' ms'.

Lemma oadd_mainA :
forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word) (svs : list slotv),
HEAPAx A (OBS ++ VBS ++ LB) LM FRS B0 m0 md0 ->
rw_cells asegs m0 p OHDR ->
lh_open asegs A4F m0 t tbl size es svs ->
okids asegs A4F m0 kids (map kv es) KBS -> opt_pbuf asegs m0 PBS pb -> jopt asegs A4F vs m0 VBS v ->
cstr asegs m0 k kn ks -> lh_globA m0 ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
stk asegs m0 lo (bv_unsigned sp) ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d664) fc None m0 (seg_rom asegs)).
Proof.
intros until svs. intros HP HDR OPEN KIDS OPB JOB CS G ERR ST.
pose proof HDR as HDR0. unfold Qm5W.OHDR in HDR. cbn [fn_obj_to_json_string A4F] in HDR.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL. pose proof alloc_ceiling_ge as ACG. pose proof alloc_ceiling_range as ACR.
destruct (oadd_factsX HIx LM FRS p t tbl size es _ _ _ _ _ (concat KBS ++ PBS ++ VBS ++ LB) HP ltac:(unfold Qm5W.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pvX HIx VBS LM FRS p v vs _ _ _ _ _ (lh_blocks t tbl size es ++ concat KBS ++ PBS ++ LB) HP ltac:(unfold Qm5W.OBS; perm) JOB) as (Hpv & V0 & V1).
assert (INK' : In (k, kn) (OBS ++ VBS ++ LB)) by (apply in_or_app; right; apply in_or_app; right; exact INK).
destruct (oadd_keyX HIx LM FRS k kn ks _ _ _ _ _ HP INK' CS) as (STR & NN & KL & KPOS & KHI & KAL).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m0) as MU.
assert (INp : In (p, 48) (OBS ++ VBS ++ LB)) by (unfold Qm5W.OBS; cbn; left; reflexivity).
assert (INt : In (t, 56) (OBS ++ VBS ++ LB)) by (unfold Qm5W.OBS, lh_blocks; cbn; right; left; reflexivity).
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INp) as SHp. unfold shad in SHp. apply shadow_ro_cells in SHp.
change (shadow_cells 48) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHp.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP INt) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (proj1 OPEN) as THDR. unfold lh_hdr, lh_hdrf in THDR. cbn [fn_lh_char_hash fn_lh_char_equal fn_lh_entry_free A4F] in THDR.
a4l.
stash OPEN. stash KIDS. stash OPB. stash JOB. stash CS. stash G. stash KF. stash STR. stash HDR0.
stash Hpimg. stash Htimg. stash Hbimg. stash SEP. stash D1. stash D2.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 80%nat ST.
do 10 step.
step. if_falsex.
step.
step. rewrite (unsigned_lit p) by lia. rewrite (ub_land7 p) by (clear -Hpal; Z.div_mod_to_equations; lia). step. if_false.
do 3 step.
step. asan_chkA.
step.
step. if_falsex.
step.
step. rewrite (unsigned_lit t) by lia. rewrite (ub_land7 t) by (clear -Htal; Z.div_mod_to_equations; lia). step. if_false.
step. asan_chkA.
step. step.
step. step. step.

unstash CS. unstash G.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
assert (HP1 : HEAPAx A (OBS ++ VBS ++ LB) LM FRS B0 mA md0) by (match goal with MIc : mem_inv asegs mA |- _ => heap_nowA A4L HIx HP MU WM MIc end).
assert (HPR1 : heap_pres A4H ((OBS ++ VBS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mA).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP]. }
assert (AG1 : agree_on asegs (OBS ++ VBS ++ LB) m0 mA).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR1 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
pose proof (cstr_agree asegs _ _ _ _ _ _ CS AG1 INK' ltac:(lia)) as CS1.
pose proof (lh_globA_client _ _ _ _ HPR1 G) as G1.
evt_done5.
eapply HASH with (LB := OBS ++ VBS ++ LB) (lo := lo) (kp := k) (kn := kn) (ks := ks);
[ exact HP1 | exact INK' | exact CS1 | exact G1 | rewrite unsigned_lit by lia; eassumption | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| unfold A_ERRNO, A_TP; eassumption | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRM | exact FRN | reflexivity | ].
intros ms2 md2 A2 (mB & h & e2 & RS2 & Hh & VM2 & ST2 & HPR2 & ERR2 & G2 & HP2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR2 by lia.
unstash OPEN. unstash KIDS. unstash OPB. unstash JOB. unstash HDR0.
assert (AG2 : agree_on asegs (OBS ++ VBS ++ LB) m0 mB).
{ eapply agree_on_trans; [exact AG1|]. eapply (agree_of_heap_presx asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
assert (HPRa : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mB).
{ eapply heap_presx_trans; [apply heap_pres_presx; eapply heap_pres_weaken; [exact HPR1 | lia |] |].
- intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb].
- eapply heap_presx_weaken; [exact HPR2 | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb]. }
lazymatch goal with FRc : rw_cells asegs mA (bv_unsigned sp + -80) _ |- _ => rename FRc into FR end.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR.
apply (rw_cells_agree asegs _ _ _ _ _ HDR0) in AG2 as HDR2; [| exists p, 48; split; [exact INp | cbn; lia]].
pose proof HDR2 as HDR2'. unfold Qm5W.OHDR in HDR2. cbn [fn_obj_to_json_string A4F] in HDR2.
pose proof (lh_open_agree asegs A4F _ _ _ _ _ _ _ _ OPEN AG2 ltac:(unfold Qm5W.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb)) as OPEN2.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ KIDS AG2 ltac:(unfold Qm5W.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS2.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB AG2 ltac:(unfold Qm5W.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB2.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB AG2 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB2.
pose proof (cstr_agree asegs _ _ _ _ _ _ CS AG2 INK' ltac:(lia)) as CS2.
clear HP MU WM MI HDR THDR OPEN KIDS OPB JOB CS G HP1 HPR1 AG1 CS1 G1 AG2 SHp SHt GOT CELL.
destruct (oadd_keyX HIx LM FRS k kn ks _ _ _ _ _ HP2 INK' CS2) as (KB2 & _).
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP2) as [GOT CELL].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP2 INp) as SHp. unfold shad in SHp. apply shadow_ro_cells in SHp.
change (shadow_cells 48) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHp.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs mB) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mB) as MU.
a4l.
stash KIDS2. stash OPB2. stash JOB2. stash CS2. stash G2. stash HDR2'. stash OPEN2.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. step. if_false.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. step. step.

unstash OPEN2. unstash KF.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He) as (_ & _ & K2 & _). lia. }
stash KF.
eapply evt_cut.
{ eapply (lh_lookup_A_spec HIx OBL_ISTRCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 t tbl size k lo es svs ks mB md2 A2 (OBS ++ VBS ++ LB) LM FRS B0 k kn HP2) with (h := h);
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by lia;
first [ exact MI | exact OPEN2 | exact BELOW | exact KB2 | exact NN | exact ST2 | exact LO | exact INK' | reflexivity | exact Hh | lia
| (clear - SPA; Z.div_mod_to_equations; lia)
| (unfold Qm5W.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb) ]. }
intros ms3 (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & r & mC & -> & MU3 & WM3 & MI3 & ST3 & OPEN3 & KB3 & RES).
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in MU3, ST3 by lia.
unstash KIDS2. unstash OPB2. unstash JOB2. unstash CS2. unstash G2. unstash HDR2'. unstash KF.
assert (HP3 : HEAPAx A2 (OBS ++ VBS ++ LB) LM FRS B0 mC md2) by heap_nowA A4L HIx HP2 MU3 WM3 MI3.
assert (AG3 : agree_on asegs (OBS ++ VBS ++ LB) mB mC).
{ eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |]. intros a n Ha. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP2 ltac:(apply in_or_app; left; exact Ha)) as (? & _ & _ & ? & _). lia. }
assert (HPRb : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mC).
{ eapply heap_presx_trans; [exact HPRa|]. eapply (heap_presx_of_munch A4H); [exact MU3 | exact WM3 |].
eapply (client_outsideA A4L HIx); [exact HP2 | | clia | solve_clientWA A4L HIx HP2].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb]. }
pose proof (rw_cells_agree asegs _ _ _ _ _ HDR2' AG3 ltac:(exists p, 48; split; [exact INp | cbn; lia])) as HDR3.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ KIDS2 AG3 ltac:(unfold Qm5W.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS3.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB2 AG3 ltac:(unfold Qm5W.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB3.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB2 AG3 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB3.
pose proof (cstr_agree asegs _ _ _ _ _ _ CS2 AG3 INK' ltac:(lia)) as CS3.
pose proof (lh_globA_frame _ _ _ G2 MU3 WM3 ltac:(apply Forall_cons; [unfold GHASHA, GSEEDA; cbn [fst snd]; lia | apply Forall_nil])) as G3.
lazymatch type of MU3 with munch _ ?mq _ =>
transport_after_call asegs mq mC MU3 WM3; try match goal with H : mem_inv asegs mq |- _ => clear H end end.
replace (ret_pc (Z_to_bv 64 0x9d71c)) with (Z_to_bv 64 0x9d71c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. if_falsex.
step.
lazymatch goal with FRc : rw_cells asegs mC (bv_unsigned sp + -80) _ |- _ => rename FRc into FR3 end.
lazymatch goal with E : rw_cells asegs mC 6444156 _ |- _ => rename E into ERR3 | E : rw_cells asegs mC (6444320 - 164) _ |- _ => rename E into ERR3 end.
destruct RES as [-> | (j & e & Hj & -> & Hks)].
-
if_true.
replace (p / 8 + 2147450885) with (p / 8 + 5 + 2147450880) by lia.
evt_done5.
eapply (oadd_insA HIx LF OBL_AMEMSET HD HD_ge HASH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB VBS PBS LM FRS B0 KBS lo p v k kn pb t tbl size es ks kids vs T
LO LOS SPA HT RA INK KN FRN LK1 LK2 BB0 BD0 Kont);
first [exact HP3 | exact HDR3 | exact OPEN3 | exact KIDS3 | exact OPB3 | exact JOB3 | exact CS3 | exact G3 | exact ERR3 | exact ST3 | exact FR3
| exact VM2 | exact HPRb | exact FS2 | exact (FRM2 FRM) | exact Hh].
-
destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ _ _ OPEN3 Hj) as (sl & _ & Hix & _).
pose proof OPEN3 as (_ & _ & _ & _ & Hsz3 & _ & Hlen). pose proof (lf_size_range size Hsz3) as HSR.
unfold ent_addr. if_falsex. fold (ent_addr tbl (le_ix e)).
replace (p / 8 + 2147450885) with (p / 8 + 5 + 2147450880) by lia.
evt_done5.
eapply (oadd_dupA HIx PUT HD HD_ge ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB VBS PBS LM FRS B0 KBS lo p v k pb t tbl size es ks kids vs T
LO LOS SPA HT LK1 LK2 BR0 Kont);
first [exact HP3 | exact HDR3 | exact OPEN3 | exact Hj | exact KIDS3 | exact OPB3 | exact JOB3 | exact G3 | exact ERR3 | exact ST3 | exact FR3
| exact VM2 | exact HPRb | exact FS2 | exact FRM2].
Qed.
End MJoObjAddMain.

Section MJoObjAddCps.
Variable HIx : heap_iface_A A4L.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.

Theorem json_object_object_add_A_cps : jo_object_add_A HIx HD.
Proof.
unfold jo_object_add_A, jo_object_add_A_stmt. intros until errv. intros PRE G J JOB INK CS KN FRM FRN A0 A1 A2 BB BR BD K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
destruct (sobj_open asegs A4F _ _ _ _ _ J) as (pb & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR & TAB & L1 & L2 & KIDS).
destruct TAB as (tbl & size & es & svs & Hkvs & ETBS & OPEN). subst OBS TBS kvs a0 a1 a2 tp.
rewrite length_map in L1.
pose proof OPEN as (_ & _ & _ & _ & Hsz & _). pose proof (lf_size_range size Hsz) as HSR.
lazymatch type of BB with context [obj_capA ?L] => assert (CAP : obj_capA L = size) by (apply obj_capA_lh; lia) end.
rewrite CAP in BB, K.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
unfold json_object_object_add_A_entry. reenterA asegs A4L HIx asegs_wx HP. step. step. evt_done5. clear MI WM MU.
eapply (oadd_mainA HIx PUT LF OBL_AMEMSET OBL_ISTRCMP HD HD_ge HASH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB VBS PBS LM FRS B KBS lo p v k kn pb t tbl size es ks kids vs T
LO LOS SPA HT RA INK KN FRM FRN L1 L2 BB).
- revert BR. unfold lh_blocks. cbn [app length]. rewrite !length_app, length_map. cbn [length]. intros BR2. rewrite !Nat2Z.inj_succ, !Nat2Z.inj_add in BR2. unfold Z.succ in BR2.

lazymatch goal with |- 512 * (3 + ?a + ?b + ?c) <= _ => replace (3 + a + b + c) with (a + b + c + 1 + 1 + 1) by ring end. exact BR2.
- exact BD.
- intros ms' md' m' r A' B' PO G' BD' OUT. exact (K ms' md' m' r A' B' PO G' BD' OUT).
- exact HP.
- exact HDR.
- exact OPEN.
- exact KIDS.
- exact OPB.
- exact JOB.
- exact CS.
- exact G.
- exact ERR.
- exact ST.
Qed.

Definition jo_object_add_ex0_A_stmt (stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB OBS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v k kn : Z) (ks : list byte)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA HIx A (OBS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> lh_globA m ->
jval asegs A4F (Sobj kids) m OBS p 1 -> jopt asegs A4F vs m VBS v ->
In (k, kn) LB -> cstr asegs m k kn ks -> kn <= 2^31 ->
frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 0 ->
oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B ->
512 * Z.of_nat (length OBS) <= bB B ->
0 <= bD B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_framexA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
lh_globA m' -> bD B <= bD B' ->
((r = 0 /\ exists OBS' kids', jval asegs A4F (Sobj kids') m' OBS' p 1 /\ (HEAPA A4L HIx) A' (OBS' ++ LB) LM FRS B' m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)
/\ ( (
Z.of_nat (length kids') = Z.of_nat (length kids) + 1
/\ bB B - oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length OBS') = Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1
/\ obj_grownA (obj_capA OBS) (Z.of_nat (length kids)) (obj_capA OBS')
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj kids') OBS' = Some (w + (key_w (Z.of_nat (length ks) + 1) + wv), [])))
\/ (
Z.of_nat (length kids') = Z.of_nat (length kids)
/\ bB B - 512 * (Z.of_nat (length OBS) + Z.of_nat (length VBS) - Z.of_nat (length OBS')) <= bB B'
/\ Z.of_nat (length OBS') <= Z.of_nat (length OBS) + Z.of_nat (length VBS)
/\ obj_capA OBS' = obj_capA OBS
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj kids') OBS' = Some (w', []) /\ w' <= w + wv)))) \/
(r = 2^64 - 1 /\ exists REM, jval asegs A4F (Sobj kids) m' OBS p 1 /\ jopt asegs A4F vs m' VBS v
/\ (HEAPA A4L HIx) A' (OBS ++ VBS ++ REM ++ LB) LM FRS B' m' md'
/\ bB B - oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d664) fc None m (seg_rom asegs)).
Theorem json_object_object_add_ex0_A_cps : jo_object_add_ex0_A_stmt (80 + 96 + 4096 + 144 + HD).
Proof.
unfold jo_object_add_ex0_A_stmt. intros until errv. intros PRE G J JOB INK CS KN FRM FRN A0 A1 A2 A3 BB BR BD K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
destruct (sobj_open asegs A4F _ _ _ _ _ J) as (pb & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR & TAB & L1 & L2 & KIDS).
destruct TAB as (tbl & size & es & svs & Hkvs & ETBS & OPEN). subst OBS TBS kvs a0 a1 a2 a3 tp.
rewrite length_map in L1.
pose proof OPEN as (_ & _ & _ & _ & Hsz & _). pose proof (lf_size_range size Hsz) as HSR.
lazymatch type of BB with context [obj_capA ?L] => assert (CAP : obj_capA L = size) by (apply obj_capA_lh; lia) end.
rewrite CAP in BB, K.
eapply (oadd_mainA HIx PUT LF OBL_AMEMSET OBL_ISTRCMP HD HD_ge HASH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB VBS PBS LM FRS B KBS lo p v k kn pb t tbl size es ks kids vs T
LO LOS SPA HT RA INK KN FRM FRN L1 L2 BB).
- revert BR. unfold lh_blocks. cbn [app length]. rewrite !length_app, length_map. cbn [length]. intros BR2. rewrite !Nat2Z.inj_succ, !Nat2Z.inj_add in BR2. unfold Z.succ in BR2.

lazymatch goal with |- 512 * (3 + ?a + ?b + ?c) <= _ => replace (3 + a + b + c) with (a + b + c + 1 + 1 + 1) by ring end. exact BR2.
- exact BD.
- intros ms' md' m' r A' B' PO G' BD' OUT. exact (K ms' md' m' r A' B' PO G' BD' OUT).
- exact HP.
- exact HDR.
- exact OPEN.
- exact KIDS.
- exact OPB.
- exact JOB.
- exact CS.
- exact G.
- exact ERR.
- exact ST.
Qed.
End MJoObjAddCps.
End RC__1.
End Mq6.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMmN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMmN.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition tsX (ts : tstate) (LK : list blk) : tstate :=
TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts ++ LK).

Lemma perm_blocks_tsX : forall pf q LB0 ts LK, Permutation (pe_blocksA pf q LB0 (tsX ts LK)) (pe_blocksA pf q LB0 ts ++ LK).
Proof.
intros pf q LB0 ts LK. unfold pe_blocksA, tstate_blocks, tsX; cbn [t_pbs t_objbs t_levels].
set (P := t_pbs ts). set (O := t_objbs ts). set (C := concat (map lvl_blocks (t_levels ts))). set (R := (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0).
rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.

Lemma PE_INVW_A_tokw1 : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts LK cb nb pj sv errv co' x',
PE_STATIC_A HIx pf pa lo ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts LK cb nb pj sv errv ->
munch [(pf_tk pf, pf_tk pf + 72)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x ts co' x') LK cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts LK cb nb pj sv errv co' x' STC (CORE & BASE & LVW & BUDW) MU WM MI TOKc Hco Hch.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (HW : Forall (pe_wtfA pf pa) [(pf_tk pf, pf_tk pf + 72)]) by (apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]).
assert (BASEx : PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 (tsX ts LK)) errv).
{ destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | apply Permutation_sym; apply perm_blocks_tsX | apply Permutation_refl | apply Permutation_refl]. }
destruct (PE_BASE_A_private_write HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m mc md A B (tsX ts LK) errv _ STC BASEx MU WM MI (pe_wtfA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsX in AG; cbn [t_objbs t_levels] in AG.
split; [| split; [| split]].
- unfold PE_CORE_A, ts_set_x; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco|]. split; [exact Hch|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split]].
+ eapply (pbuf_wtfA HIx) with (ts := tsX ts LK); [exact STC | exact (proj1 BASEx) | exact PB | exact MU | exact WM | exact HW].
+ eapply (tstack_wtfA HIx) with (ts := tsX ts LK); [exact STC | exact (proj1 BASEx) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
+ eapply (pe_frameA_blkwrite HIx) with (ts := tsX ts LK); [exact STC | exact (proj1 BASEx) | | exact FR | exact MU | exact WM].
apply Forall_cons; [exists (pf_tk pf), 72; cbn [fst snd]; split; [apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity | lia] | apply Forall_nil].
- destruct BASEc as (HPc & BASEc'). split; [| exact BASEc'].
eapply (heapA_perm A4L HIx); [exact HPc | | apply Permutation_refl | apply Permutation_refl].
change (pe_blocksA pf q LB0 (ts_set_x ts co' x')) with (pe_blocksA pf q LB0 ts). apply perm_blocks_tsX.
- unfold ts_set_x; cbn [t_levels t_depth]. intros i li Hli. destruct (LVW i li Hli) as (R12 & JO & NM & CL).
assert (INli : incl (lvl_blocks li) ((t_objbs ts ++ LK) ++ concat (map lvl_blocks (t_levels ts)))).
{ intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [apply in_map; eapply nth_error_In; exact Hli | exact Hb]. }
split; [exact R12|]. split; [| split; [| exact CL]].
+ eapply (jopt_agree asegs A4F); [exact JO | exact AG |]. intros b Hb. apply INli. unfold lvl_blocks. apply in_or_app; left. exact Hb.
+ destruct NM as [NM | NM]; [left | right]; (eapply (name_ok_agree asegs); [exact NM | exact AG |]; intros b Hb; apply INli; unfold lvl_blocks; apply in_or_app; right; exact Hb).
- exact BUDW.
Qed.

Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Notation KOUTx := (KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Notation KERR2x := (KERR2_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Hypothesis KO : KOUTx.

Lemma tdepth_ok_set_err : forall ts e, tdepth_ok ts -> tdepth_ok (ts_set_err ts e).
Proof. intros ts e TD. eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. Qed.

Local Ltac open_w STCx INVW :=
pose proof STCx as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
pose proof INVW as (CORE & BASE & _ & _);
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & _ & _ & _ & FR);
pose proof (proj1 BASE) as HP; clear BASE.

Lemma kerr2_of_kout : KERR2x.
Proof.
intros ts LK e m md A B cb nb pj errv x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc INVW TD He FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 e)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msE, APE_ERR2. cbn [pf_tk pf_spf pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
do 6 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 e) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

Lemma kerrst_of_kout :
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s10 t4 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 < e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_ERRST (t_co ts) gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s5 s10 t4 F fc m).
Proof.
intros ts LK e m md A B cb nb pj errv gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s10 t4 F fc INVW TD He FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 e)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msA, pe_msO, pe_msE, APE_ERRST. cbn [pf_tk pf_spf pf_sb pf_lenr pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 e) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

Lemma kerrmem_of_kout :
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_ERRMEM x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 (Z_to_bv 64 (pf_tk pf + 56)) s11 t4 t6 F fc m).
Proof.
intros ts LK m md A B cb nb pj errv x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s11 t4 t6 F fc INVW TD FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 16)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msA, pe_msO, pe_msE, APE_ERRMEM. cbn [pf_tk pf_spf pf_sb pf_lenr pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 16) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

Lemma kerrmemb_of_kout :
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa APE_ERRMEMB x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5 (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6 F fc m).
Proof.
intros ts LK m md A B cb nb pj errv x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s11 t3 t4 t5 t6 F fc INVW TD FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 16)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msA, pe_msO, pe_msE, APE_ERRMEMB. cbn [pf_tk pf_spf pf_sb pf_lenr pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 16) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

Lemma kerrmemc_of_kout :
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa APE_ERRMEMC x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
s3 (Z_to_bv 64 (pf_tk pf + 20)) s5 (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6 F fc m).
Proof.
intros ts LK m md A B cb nb pj errv x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s11 t3 t4 t5 t6 F fc INVW TD FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 16)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msA, pe_msO, pe_msE, APE_ERRMEMC. cbn [pf_tk pf_spf pf_sb pf_lenr pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 16) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.
End WithIface.
End RC__1.
