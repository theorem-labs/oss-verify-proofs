(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH Qsw7 QJjn Q7UD Qhd4 Qwm6 QlKV QsKa Q9O6 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import Q7UD Qhd4.
Import Qwm6.Mq0 QlKV.Mq2 QsKa Q9O6.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Lemma skipn_nth_cons : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
intros X l. induction l as [|y l IH]; intros i x H; [destruct i; discriminate H|].
destruct i as [|i]; cbn in H |- *; [injection H as ->; reflexivity | apply IH; exact H].
Qed.
Lemma skipn_all_nil : forall {X} (l : list X) i, (length l <= i)%nat -> skipn i l = [].
Proof. intros X l i H. apply skipn_all2. exact H. Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation rw_cells := (rw_cells segs).
Notation jnode := (jnode segs fn).

Lemma jnode_hdr : forall s m REST p rc pb0, jnode s m REST p rc pb0 ->
exists n ty udel ud cs rest, REST = (p, n) :: rest /\ 48 <= n /\
rw_cells m p ([C4 (wz ty); C4 (wz rc); C8 (wz (fn_ofF fn s)); C8 (wz pb0); C8 (wz udel); C8 (wz ud)] ++ cs).
Proof.
intros s m REST p rc pb0 J. destruct s as [|[|]| |[|]|kids|kids]; cbn in J.
- destruct J as (b & junk & -> & H). exists 48, JT_BOOLEAN, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & ud & udn & uds & -> & _ & H & _). exists 48, JT_DOUBLE, (fn_free_userdata fn), ud. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & -> & _ & H). exists 48, JT_DOUBLE, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (cty & v & junk & -> & _ & H). exists 56, JT_INT, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & pd & pdn & str & junk2 & -> & _ & _ & _ & H & _). exists 56, JT_STRING, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & str & junk & -> & Hl & _ & H). exists (str_objsize len), JT_STRING, 0, 0. eexists. exists []. split; [reflexivity|]. split; [unfold str_objsize; lia|]. exact H.
- destruct J as (t & TBS & kvs & KBS & -> & H & _). exists 48, JT_OBJECT, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (a & ABS & ps & KBS & -> & H & _). exists 48, JT_ARRAY, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
Qed.

Lemma kids_okp_nth : forall m kids ps KBS i k,
kids_okp segs fn m kids ps KBS -> nth_error kids i = Some k ->
exists v bs, nth_error ps i = Some v /\ nth_error KBS i = Some bs /\
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jval segs fn s' m bs v 1 end.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros ps KBS i k KOK Hn; [destruct i; discriminate Hn|].
destruct ps as [|v0 ps]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
destruct KOK as [H0 KOK].
destruct i as [|i]; cbn in Hn |- *.
- injection Hn as ->. exists v0, bs0. auto.
- eapply IH; eassumption.
Qed.
Lemma kids_okp_len : forall m kids ps KBS, kids_okp segs fn m kids ps KBS -> length ps = length kids /\ length KBS = length kids.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros ps KBS KOK.
- destruct ps; [|destruct KOK]. destruct KBS; [|destruct KOK]. split; reflexivity.
- destruct ps as [|v0 ps]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
destruct KOK as [_ KOK]. destruct (IH _ _ KOK) as [L1 L2]. cbn. lia.
Qed.
Lemma kids_okv_nth : forall m kids kvs KBS i k,
kids_okv segs fn m kids kvs KBS -> nth_error kids i = Some k ->
exists kk v bs, nth_error kvs i = Some (kk, v) /\ nth_error KBS i = Some bs /\
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jval segs fn s' m bs v 1 end.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros kvs KBS i k KOK Hn; [destruct i; discriminate Hn|].
destruct kvs as [|[kk0 v0] kvs]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
destruct KOK as [H0 KOK].
destruct i as [|i]; cbn in Hn |- *.
- injection Hn as ->. exists kk0, v0, bs0. auto.
- eapply IH; eassumption.
Qed.
Lemma kids_okv_len : forall m kids kvs KBS, kids_okv segs fn m kids kvs KBS -> length kvs = length kids /\ length KBS = length kids.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros kvs KBS KOK.
- destruct kvs; [|destruct KOK]. destruct KBS; [|destruct KOK]. split; reflexivity.
- destruct kvs as [|[kk0 v0] kvs]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
destruct KOK as [_ KOK]. destruct (IH _ _ KOK) as [L1 L2]. cbn. lia.
Qed.

Lemma kids_okp_agree : forall m m' BS kids ps KBS,
kids_okp segs fn m kids ps KBS -> agree_on segs BS m m' -> incl (concat KBS) BS -> kids_okp segs fn m' kids ps KBS.
Proof.
intros m m' BS kids. induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS AG HiK; try exact KIDS.
cbn in HiK. destruct KIDS as [K1 K2]. split.
- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply (jval_agree segs fn); [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
- apply IH; [exact K2 | exact AG | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
Qed.
Lemma kids_okv_agree : forall m m' BS kids kvs KBS,
kids_okv segs fn m kids kvs KBS -> agree_on segs BS m m' -> incl (concat KBS) BS -> kids_okv segs fn m' kids kvs KBS.
Proof.
intros m m' BS kids. induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS AG HiK; try exact KIDS.
cbn in HiK. destruct KIDS as [K1 K2]. split.
- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply (jval_agree segs fn); [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
- apply IH; [exact K2 | exact AG | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
Qed.

Lemma jtxk_arr_step_some : forall m kids ps KBS i s' v bs P Y acc w R,
kids_okp segs fn m kids ps KBS -> nth_error kids i = Some (Some s') -> nth_error ps i = Some v -> nth_error KBS i = Some bs -> pbtail P ->
jtxk_arr (skipn i kids) (P ++ concat (skipn i KBS) ++ Y) acc = Some (w, R) ->
v <> 0 /\ jval segs fn s' m bs v 1 /\
exists pbk PBSk RESTk wi P', bs = RESTk ++ PBSk /\ jnode s' m RESTk v 1 pbk /\ 0 <= wi /\ acc + (2 + wi) <= w /\
jtx s' (RESTk ++ (PBSk ++ concat (skipn (S i) KBS) ++ Y)) = Some (wi, P' ++ concat (skipn (S i) KBS) ++ Y) /\ pbtail P' /\
jtxk_arr (skipn (S i) kids) (P' ++ concat (skipn (S i) KBS) ++ Y) (acc + (2 + wi)) = Some (w, R).
Proof.
intros m kids ps KBS i s' v bs P Y acc w R KOK Hk Hp Hb HP H.
destruct (kids_okp_nth _ _ _ _ _ _ KOK Hk) as (v' & bs' & Hp' & Hb' & Hv & JV).
rewrite Hp in Hp'. injection Hp' as <-. rewrite Hb in Hb'. injection Hb' as <-.
split; [exact Hv|]. split; [exact JV|].
rewrite (skipn_nth_cons _ _ _ Hk), (skipn_nth_cons _ _ _ Hb) in H. cbn [jtxk_arr concat] in H.
destruct (jtx s' (P ++ (bs ++ concat (skipn (S i) KBS)) ++ Y)) as [[wi R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (jval_jtx_node segs fn _ _ _ _ _ _ _ _ JV E) as (pbk & PBSk & RESTk & EB & OP & JN & E').
destruct (jtx_val_tail segs fn _ _ _ _ _ JV _ _ _ E) as (P' & -> & HP').
exists pbk, PBSk, RESTk, wi, P'. split; [exact EB|]. split; [exact JN|].
split; [exact (jtx_nonneg _ _ _ _ E)|].
split; [eapply (jtxk_arr_acc (fun _ => True)); [intros s0 _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact H]|].
split; [exact E'|]. split; [exact HP' | exact H].
Qed.
Lemma jtxk_arr_step_none : forall m kids ps KBS i P Y acc w R,
kids_okp segs fn m kids ps KBS -> nth_error kids i = Some None -> pbtail P ->
jtxk_arr (skipn i kids) (P ++ concat (skipn i KBS) ++ Y) acc = Some (w, R) ->
nth_error ps i = Some 0 /\ acc + 6 <= w /\
jtxk_arr (skipn (S i) kids) (P ++ concat (skipn (S i) KBS) ++ Y) (acc + 6) = Some (w, R).
Proof.
intros m kids ps KBS i P Y acc w R KOK Hk HP H.
destruct (kids_okp_nth _ _ _ _ _ _ KOK Hk) as (v' & bs' & Hp' & Hb' & -> & ->).
split; [exact Hp'|].
rewrite (skipn_nth_cons _ _ _ Hk), (skipn_nth_cons _ _ _ Hb') in H. cbn [jtxk_arr concat app] in H. unfold NULL_W in H. change (2 + 4) with 6 in H.
split; [eapply (jtxk_arr_acc (fun _ => True)); [intros s0 _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact H] | exact H].
Qed.
Lemma jtxk_arr_done : forall kids i bs acc w R, (length kids <= i)%nat -> jtxk_arr (skipn i kids) bs acc = Some (w, R) -> w = acc.
Proof. intros kids i bs acc w R Hi H. rewrite (skipn_all_nil _ _ Hi) in H. cbn in H. injection H as <- _. reflexivity. Qed.

Lemma jtxk_obj_step_some : forall m kids kvs KBS keys i s' kk v bs kb P Y acc w R,
kids_okv segs fn m kids kvs KBS -> nth_error kids i = Some (Some s') -> nth_error kvs i = Some (kk, v) -> nth_error KBS i = Some bs ->
nth_error keys i = Some kb -> pbtail P ->
jtxk_obj (skipn i kids) (skipn i keys) (P ++ concat (skipn i KBS) ++ Y) acc = Some (w, R) ->
v <> 0 /\ jval segs fn s' m bs v 1 /\
exists pbk PBSk RESTk wi P', bs = RESTk ++ PBSk /\ jnode s' m RESTk v 1 pbk /\ 0 <= wi /\ acc + (key_w (snd kb) + wi) <= w /\
jtx s' (RESTk ++ (PBSk ++ concat (skipn (S i) KBS) ++ Y)) = Some (wi, P' ++ concat (skipn (S i) KBS) ++ Y) /\ pbtail P' /\
jtxk_obj (skipn (S i) kids) (skipn (S i) keys) (P' ++ concat (skipn (S i) KBS) ++ Y) (acc + (key_w (snd kb) + wi)) = Some (w, R).
Proof.
intros m kids kvs KBS keys i s' kk v bs [k kn] P Y acc w R KOK Hk Hp Hb Hkb HP H.
destruct (kids_okv_nth _ _ _ _ _ _ KOK Hk) as (kk' & v' & bs' & Hp' & Hb' & Hv & JV).
rewrite Hp in Hp'. injection Hp' as <- <-. rewrite Hb in Hb'. injection Hb' as <-.
split; [exact Hv|]. split; [exact JV|].
rewrite (skipn_nth_cons _ _ _ Hk), (skipn_nth_cons _ _ _ Hb), (skipn_nth_cons _ _ _ Hkb) in H. cbn [jtxk_obj concat] in H.
destruct (jtx s' (P ++ (bs ++ concat (skipn (S i) KBS)) ++ Y)) as [[wi R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (jval_jtx_node segs fn _ _ _ _ _ _ _ _ JV E) as (pbk & PBSk & RESTk & EB & OP & JN & E').
destruct (jtx_val_tail segs fn _ _ _ _ _ JV _ _ _ E) as (P' & -> & HP').
exists pbk, PBSk, RESTk, wi, P'. split; [exact EB|]. split; [exact JN|].
split; [exact (jtx_nonneg _ _ _ _ E)|]. cbn [snd].
split; [eapply jtxk_obj_acc; [intros s0 _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact H]|].
split; [exact E'|]. split; [exact HP' | exact H].
Qed.
Lemma jtxk_obj_step_none : forall m kids kvs KBS keys i kb P Y acc w R,
kids_okv segs fn m kids kvs KBS -> nth_error kids i = Some None -> nth_error keys i = Some kb -> pbtail P ->
jtxk_obj (skipn i kids) (skipn i keys) (P ++ concat (skipn i KBS) ++ Y) acc = Some (w, R) ->
(exists kk, nth_error kvs i = Some (kk, 0)) /\ acc + (key_w (snd kb) + 4) <= w /\
jtxk_obj (skipn (S i) kids) (skipn (S i) keys) (P ++ concat (skipn (S i) KBS) ++ Y) (acc + (key_w (snd kb) + 4)) = Some (w, R).
Proof.
intros m kids kvs KBS keys i [k kn] P Y acc w R KOK Hk Hkb HP H.
destruct (kids_okv_nth _ _ _ _ _ _ KOK Hk) as (kk' & v' & bs' & Hp' & Hb' & -> & ->).
split; [exists kk'; exact Hp'|].
rewrite (skipn_nth_cons _ _ _ Hk), (skipn_nth_cons _ _ _ Hb'), (skipn_nth_cons _ _ _ Hkb) in H. cbn [jtxk_obj concat app] in H. unfold NULL_W in H. cbn [snd].
split; [eapply jtxk_obj_acc; [intros s0 _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact H] | exact H].
Qed.
Lemma jtxk_obj_done : forall kids i keys bs acc w R, (length kids <= i)%nat -> jtxk_obj (skipn i kids) keys bs acc = Some (w, R) -> w = acc.
Proof. intros kids i keys bs acc w R Hi H. rewrite (skipn_all_nil _ _ Hi) in H. cbn in H. injection H as <- _. reflexivity. Qed.
End WithSegs.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3 Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QCcH Q0Ek QjDH.Mq0.
Import QSL3.
Import Qvbw.
Import QlKV.Mq2 QsKa Q9O6.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Local Ltac flia := Qo9G.term_slim ltac:(Zify.zify; xlia zchecker).

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation jvalx := (jval segs fn).

Definition jindep (s : jshape) (bs : list blk) : Prop :=
forall X w R, jtx s (bs ++ X) = Some (w, R) -> exists P, R = P ++ X /\ pbtail P /\ forall X', jtx s (bs ++ X') = Some (w, P ++ X').

Lemma jtxk_arr_indep : forall m kids, (forall s, In (Some s) kids -> forall bs p rc, jvalx s m bs p rc -> jindep s bs) ->
forall ps KBS, kids_okp segs fn m kids ps KBS -> forall P0 Y acc w R, pbtail P0 ->
jtxk_arr kids (P0 ++ concat KBS ++ Y) acc = Some (w, R) ->
exists P, R = P ++ Y /\ pbtail P /\ forall Y', jtxk_arr kids (P0 ++ concat KBS ++ Y') acc = Some (w, P ++ Y').
Proof.
induction kids as [|[s'|] kids IH]; intros HK ps KBS OK P0 Y acc w R HP0 H.
- destruct ps; [|destruct OK]. destruct KBS; [|destruct OK]. cbn [jtxk_arr concat app] in H. injection H as <- <-. exists P0. split; [reflexivity|]. split; [exact HP0|]. intros Y'. reflexivity.
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [jtxk_arr concat] in H. destruct (jtx s' (P0 ++ (bs1 ++ concat KBS) ++ Y)) as [[w1 R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP0 E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (HK s' (or_introl eq_refl) _ _ _ JV _ _ _ E) as (P1 & -> & HP1 & IND1).
destruct (IH (fun s Hs => HK s (or_intror Hs)) ps KBS OK P1 Y _ _ _ HP1 H) as (P & -> & HP & INDr).
exists P. split; [reflexivity|]. split; [exact HP|]. intros Y'. cbn [jtxk_arr concat app]. rewrite <- app_assoc, (IND1 (concat KBS ++ Y')). exact (INDr Y').
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [jtxk_arr concat app] in H. destruct (IH (fun s Hs => HK s (or_intror Hs)) ps KBS OK P0 Y _ _ _ HP0 H) as (P & -> & HP & INDr).
exists P. split; [reflexivity|]. split; [exact HP|]. intros Y'. cbn [jtxk_arr concat app]. exact (INDr Y').
Qed.

Lemma jtxk_obj_indep : forall m kids, (forall s, In (Some s) kids -> forall bs p rc, jvalx s m bs p rc -> jindep s bs) ->
forall kvs KBS, kids_okv segs fn m kids kvs KBS -> forall keys P0 Y acc w R, pbtail P0 ->
jtxk_obj kids keys (P0 ++ concat KBS ++ Y) acc = Some (w, R) ->
exists P, R = P ++ Y /\ pbtail P /\ forall Y', jtxk_obj kids keys (P0 ++ concat KBS ++ Y') acc = Some (w, P ++ Y').
Proof.
induction kids as [|[s'|] kids IH]; intros HK kvs KBS OK keys P0 Y acc w R HP0 H.
- destruct kvs; [|destruct OK]. destruct KBS; [|destruct OK]. cbn [jtxk_obj concat app] in H. injection H as <- <-. exists P0. split; [reflexivity|]. split; [exact HP0|]. intros Y'. reflexivity.
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [jtxk_obj concat] in H. destruct keys as [|[k kn] keys]; [discriminate|].
destruct (jtx s' (P0 ++ (bs1 ++ concat KBS) ++ Y)) as [[w1 R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP0 E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (HK s' (or_introl eq_refl) _ _ _ JV _ _ _ E) as (P1 & -> & HP1 & IND1).
destruct (IH (fun s Hs => HK s (or_intror Hs)) kvs KBS OK keys P1 Y _ _ _ HP1 H) as (P & -> & HP & INDr).
exists P. split; [reflexivity|]. split; [exact HP|]. intros Y'. cbn [jtxk_obj concat app]. rewrite <- app_assoc, (IND1 (concat KBS ++ Y')). exact (INDr Y').
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [jtxk_obj concat app] in H. destruct keys as [|[k kn] keys]; [discriminate|].
destruct (IH (fun s Hs => HK s (or_intror Hs)) kvs KBS OK keys P0 Y _ _ _ HP0 H) as (P & -> & HP & INDr).
exists P. split; [reflexivity|]. split; [exact HP|]. intros Y'. cbn [jtxk_obj concat app]. exact (INDr Y').
Qed.

Theorem jtx_val_indep : forall s m bs p rc, jvalx s m bs p rc -> jindep s bs.
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; intros m bs p rc JV X w R H.
- destruct JV as (pb & PBS & REST & -> & OP & b & junk & -> & _). cbn in H. injection H as <- <-. exists PBS.
split; [reflexivity|]. split; [eapply opt_pbuf_pbtail; exact OP|]. intros X'. reflexivity.
- destruct u.
+ destruct JV as (pb & PBS & REST & -> & OP & bits & ud & udn & uds & -> & _). cbn in H. injection H as <- <-. exists PBS.
split; [reflexivity|]. split; [eapply opt_pbuf_pbtail; exact OP|]. intros X'. reflexivity.
+ destruct JV as (pb & PBS & REST & -> & OP & bits & -> & _). cbn in H. injection H as <- <-. exists PBS.
split; [reflexivity|]. split; [eapply opt_pbuf_pbtail; exact OP|]. intros X'. reflexivity.
- destruct JV as (pb & PBS & REST & -> & OP & cty & v & junk & -> & _). cbn in H. injection H as <- <-. exists PBS.
split; [reflexivity|]. split; [eapply opt_pbuf_pbtail; exact OP|]. intros X'. reflexivity.
- destruct h.
+ destruct JV as (pb & PBS & REST & -> & OP & len & pd & pdn & str & junk2 & -> & _). cbn in H. injection H as <- <-. exists PBS.
split; [reflexivity|]. split; [eapply opt_pbuf_pbtail; exact OP|]. intros X'. reflexivity.
+ destruct JV as (pb & PBS & REST & -> & OP & len & str & junk & -> & Hl & _). cbn [app jtx] in H |- *. unfold str_objsize in H |- *.
replace (57 <=? 49 + Z.max len 8) with true in H by (symmetry; apply Z.leb_le; lia). injection H as <- <-. exists PBS.
split; [reflexivity|]. split; [eapply opt_pbuf_pbtail; exact OP|]. intros X'. cbn [app jtx]. unfold str_objsize.
replace (57 <=? 49 + Z.max len 8) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- destruct JV as (pb & PBS & REST & -> & OP & t & TBS & kvs & KBS & -> & _ & (tbl & size & es & svs & Ekvs & -> & _) & L1 & L2 & OK).
unfold lh_blocks in H. cbn [app] in H. rewrite <- !app_assoc in H. rewrite jtx_obj_eq in H. cbn [snd] in H.
assert (LKe : length es = length kids) by (rewrite Ekvs, length_map in L1; exact L1).
assert (LK : length (map (fun e => (le_k e, le_kn e) : blk) es) = length kids) by (rewrite length_map; exact LKe).
change (48 =? 48) with true in H. change (56 =? 56) with true in H. cbn [andb] in H.
match type of H with context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app, length_map in GT; clear - GT LKe; flia] end.
rewrite (firstn_app_exact _ _ _ LK), (skipn_app_exact _ _ _ LK) in H.
destruct (jtxk_obj_indep m kids (fun s Hs bs0 p0 rc0 JV0 => IHk s Hs m bs0 p0 rc0 JV0) kvs KBS OK _ [] (PBS ++ X) _ w R pbtail_nil H) as (P & -> & HP & IND).
exists (P ++ PBS). split; [rewrite app_assoc; reflexivity|]. split; [apply pbtail_app; [exact HP | eapply opt_pbuf_pbtail; exact OP]|].
intros X'. unfold lh_blocks. cbn [app]. rewrite <- !app_assoc. rewrite jtx_obj_eq. cbn [snd].
change (48 =? 48) with true. change (56 =? 56) with true. cbn [andb].
match goal with |- context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app, length_map in GT; clear - GT LKe; flia] end.
rewrite (firstn_app_exact _ _ _ LK), (skipn_app_exact _ _ _ LK). exact (IND (PBS ++ X')).
- destruct JV as (pb & PBS & REST & -> & OP & a & ABS & ps & KBS & -> & _ & (arr & size & junk & -> & _) & L1 & L2 & OK).
cbn [app] in H. rewrite <- !app_assoc in H. rewrite jtx_arr_eq in H. cbn [snd] in H.
change (48 =? 48) with true in H. change (32 =? 32) with true in H. cbn [andb] in H.
destruct (jtxk_arr_indep m kids (fun s Hs bs0 p0 rc0 JV0 => IHk s Hs m bs0 p0 rc0 JV0) ps KBS OK [] (PBS ++ X) _ w R pbtail_nil H) as (P & -> & HP & IND).
exists (P ++ PBS). split; [rewrite app_assoc; reflexivity|]. split; [apply pbtail_app; [exact HP | eapply opt_pbuf_pbtail; exact OP]|].
intros X'. cbn [app]. rewrite <- !app_assoc. rewrite jtx_arr_eq. cbn [snd].
change (48 =? 48) with true. change (32 =? 32) with true. cbn [andb]. exact (IND (PBS ++ X')).
Qed.

Lemma jtxk_obj_shift : forall ks keys bs acc w r d,
jtxk_obj ks keys bs acc = Some (w, r) -> jtxk_obj ks keys bs (acc + d) = Some (w + d, r).
Proof.
induction ks as [|[s'|] ks IH]; intros keys bs acc w r d H; cbn [jtxk_obj] in H |- *.
- injection H as <- <-. reflexivity.
- destruct keys as [|[k kn] keys]; [discriminate|]. destruct (jtx s' bs) as [[w' bs']|]; [|discriminate].
replace (acc + d + (key_w kn + w')) with (acc + (key_w kn + w') + d) by lia. apply IH. exact H.
- destruct keys as [|[k kn] keys]; [discriminate|].
replace (acc + d + (key_w kn + NULL_W)) with (acc + (key_w kn + NULL_W) + d) by lia. apply IH. exact H.
Qed.

Lemma jtxk_obj_P0_nil : forall m kids kvs KBS, kids_okv segs fn m kids kvs KBS -> forall keys P0 Y acc w, pbtail P0 ->
jtxk_obj kids keys (P0 ++ concat KBS ++ Y) acc = Some (w, []) -> P0 = [].
Proof.
induction kids as [|[s'|] kids IH]; intros kvs KBS OK keys P0 Y acc w HP0 H.
- destruct kvs; [|destruct OK]. destruct KBS; [|destruct OK]. cbn [jtxk_obj concat app] in H. injection H as _ H. apply app_eq_nil in H as [-> _]. reflexivity.
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|].
cbn [jtxk_obj] in H. destruct keys as [|[k kn] keys]; [discriminate|].
destruct (jtx s' (P0 ++ concat (bs1 :: KBS) ++ Y)) as [[w1 R1]|] eqn:E; [|discriminate].
exact (jtx_pbtail_nil _ _ _ _ _ HP0 E).
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [jtxk_obj concat app] in H. destruct keys as [|[k kn] keys]; [discriminate|].
exact (IH kvs KBS OK keys P0 Y _ _ HP0 H).
Qed.

Lemma kids_okv_split : forall m kids1 K2 kvs KBS1 B2, kids_okv segs fn m (kids1 ++ K2) kvs (KBS1 ++ B2) -> length KBS1 = length kids1 ->
exists kvs1 kvs2, kvs = kvs1 ++ kvs2 /\ kids_okv segs fn m kids1 kvs1 KBS1 /\ kids_okv segs fn m K2 kvs2 B2.
Proof.
induction kids1 as [|k kids1 IH]; intros K2 kvs KBS1 B2 OK L.
- destruct KBS1; [|discriminate]. exists [], kvs. split; [reflexivity|]. split; [exact I | exact OK].
- destruct KBS1 as [|bs1 KBS1]; [discriminate|]. destruct kvs as [|[kk v] kvs]; [destruct OK|].
cbn [app] in OK. destruct OK as [OK1 OK].
destruct (IH K2 kvs KBS1 B2 OK ltac:(cbn in L; lia)) as (kvs1 & kvs2 & -> & O1 & O2).
exists ((kk, v) :: kvs1), kvs2. split; [reflexivity|]. split; [split; [exact OK1 | exact O1] | exact O2].
Qed.

Lemma obj_set_jtx : forall m kids1 kj kids2 kvs KBS1 bsj KBS2 PBS (b0 b1 b2 b2' : blk) (keys : list blk) vs VBS w wv,
okids segs fn m (kids1 ++ kj :: kids2) kvs (KBS1 ++ bsj :: KBS2) -> length KBS1 = length kids1 ->
length keys = length (kids1 ++ kj :: kids2) ->
jtx (Sobj (kids1 ++ kj :: kids2)) ((b0 :: (b1 :: b2 :: keys) ++ concat (KBS1 ++ bsj :: KBS2)) ++ PBS) = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj (kids1 ++ vs :: kids2)) ((b0 :: (b1 :: b2' :: keys) ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS) = Some (w', []) /\ w' <= w + wv.
Proof.
intros m kids1 kj kids2 kvs KBS1 bsj KBS2 PBS b0 b1 b2 b2' keys vs VBS w wv KIDS LB1 LK Hw Hwv.
destruct (kids_okv_split m kids1 (kj :: kids2) kvs KBS1 (bsj :: KBS2) (okids_okv _ _ _ _ _ _ KIDS) LB1) as (kvs1 & kvs2 & -> & OK1 & OK2).
destruct kvs2 as [|[kkj vj] kvs2]; [destruct OK2|]. destruct OK2 as [OKj OK2].

set (n := length kids1).
assert (EK : keys = firstn n keys ++ skipn n keys) by (symmetry; apply firstn_skipn).
assert (LK1 : length (firstn n keys) = n) by (apply firstn_length_le; rewrite LK, length_app; cbn [length]; unfold n; lia).
destruct (skipn n keys) as [|[k kn] keys2] eqn:ES.
{ exfalso. apply (f_equal (@length _)) in EK. rewrite length_app, LK1, LK, length_app in EK. cbn [length] in EK. unfold n in EK. lia. }
set (keys1 := firstn n keys) in *.
assert (LKS : length (kids1 ++ kj :: kids2) = length (kids1 ++ vs :: kids2)) by (rewrite !length_app; reflexivity).

cbn [app] in Hw. rewrite <- ?app_assoc in Hw. rewrite jtx_obj_eq in Hw.
destruct ((snd b0 =? 48) && (snd b1 =? 56)) eqn:E01; [| discriminate]. cbn [andb] in Hw.
match type of Hw with context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| discriminate] end.
rewrite (firstn_app_exact _ _ _ LK), (skipn_app_exact _ _ _ LK) in Hw.
rewrite concat_app in Hw. cbn [concat] in Hw. rewrite <- ?app_assoc in Hw.
rewrite EK in Hw. rewrite (jtxk_obj_app kids1 (kj :: kids2) keys1 ((k, kn) :: keys2)) in Hw by exact LK1.
destruct (jtxk_obj kids1 keys1 (concat KBS1 ++ bsj ++ concat KBS2 ++ PBS) 24) as [[w1 R1]|] eqn:E1; [| discriminate].
destruct (jtxk_obj_indep m kids1 (fun s _ bs0 p0 rc0 JV0 => jtx_val_indep s m bs0 p0 rc0 JV0) kvs1 KBS1 OK1 keys1 [] (bsj ++ concat KBS2 ++ PBS) _ w1 R1 pbtail_nil E1) as (P1 & -> & HP1 & IND1).

assert (OLD : exists wj, 0 <= wj /\ P1 = [] /\ jtxk_obj kids2 keys2 (concat KBS2 ++ PBS) (w1 + (key_w kn + wj)) = Some (w, [])).
{ destruct kj as [sj|]; cbn [jtxk_obj] in Hw.
- destruct OKj as [_ JVj].
destruct (jtx sj (P1 ++ bsj ++ concat KBS2 ++ PBS)) as [[wj Rj]|] eqn:Ej; [| discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP1 Ej) as ->. cbn [app] in Ej.
destruct (jtx_val_indep sj m bsj vj 1 JVj _ _ _ Ej) as (Pj & -> & HPj & _).
pose proof (jtxk_obj_P0_nil m kids2 kvs2 KBS2 OK2 keys2 Pj PBS _ _ HPj Hw) as ->.
exists wj. split; [eapply jtx_nonneg; exact Ej|]. split; [reflexivity | exact Hw].
- destruct OKj as [_ ->]. cbn [app] in Hw.
pose proof (jtxk_obj_P0_nil m kids2 kvs2 KBS2 OK2 keys2 P1 PBS _ _ HP1 Hw) as ->.
exists NULL_W. split; [unfold NULL_W; lia|]. split; [reflexivity | exact Hw]. }
destruct OLD as (wj & Hwj & -> & Hw2).

exists (w + (wv - wj)). split; [| lia].
cbn [app]. rewrite <- ?app_assoc. rewrite jtx_obj_eq, E01. cbn [andb].
match goal with |- context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT2]; [| exfalso; rewrite <- LKS, <- LK in GT2; rewrite length_app in GT2; flia] end.
rewrite <- LKS. rewrite (firstn_app_exact _ _ _ LK), (skipn_app_exact _ _ _ LK).
rewrite concat_app. cbn [concat]. rewrite <- ?app_assoc.
rewrite EK. rewrite (jtxk_obj_app kids1 (vs :: kids2) keys1 ((k, kn) :: keys2)) by exact LK1.
pose proof (IND1 (VBS ++ concat KBS2 ++ PBS)) as E1'. cbn [app] in E1'. rewrite E1'.
replace (w1 + (key_w kn + wj)) with (w1 + (key_w kn + wv) + (wj - wv)) in Hw2 by lia.
destruct vs as [sv|]; cbn [jtx_opt] in Hwv; cbn [jtxk_obj].
- rewrite (jtx_frame sv VBS wv [] (concat KBS2 ++ PBS) Hwv). cbn [app].
pose proof (jtxk_obj_shift kids2 keys2 (concat KBS2 ++ PBS) _ _ _ (wv - wj) Hw2) as S.
replace (w1 + (key_w kn + wv) + (wj - wv) + (wv - wj)) with (w1 + (key_w kn + wv)) in S by lia. exact S.
- injection Hwv as <- ->. cbn [app].
pose proof (jtxk_obj_shift kids2 keys2 (concat KBS2 ++ PBS) _ _ _ (NULL_W - wj) Hw2) as S.
replace (w1 + (key_w kn + NULL_W) + (wj - NULL_W) + (NULL_W - wj)) with (w1 + (key_w kn + NULL_W)) in S by lia. exact S.
Qed.
End WithSegs.
End Mq1.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 QytA Qy5Y Q4J3 Q8zf QEoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1.
Import QytA Qy5Y.Mq4 Q4J3.Mq3.
Import Q6q3.
Import QlKV.Mq9 Q8zf QEoy Q9O6.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Open Scope Z_scope.

Section B. Context {RC__ : RunConsts}.
Variables (sec : Z) (resv : list (Z * Z)) (a1 a2 a3 a4 a5 : Z).
Hypothesis H1 : brk0_answer_ok a1 = true.
Hypothesis Hb : round_up_pg a1 = a1.
Hypothesis H2 : brk_answer_ok a1 (a1 + 2 * PGSZ) a2 = true.
Hypothesis H3 : (a2 =? a1 + 2 * PGSZ) = false.
Hypothesis H4 : mmap_answer_ok (resv ++ []) (2 * PGSZ) a3 = true.
Hypothesis H5 : is_err a3 = false.
Hypothesis H6 : mprotect_answer_ok a4 = true.
Hypothesis H7 : ((a4 =? 0) || (a4 =? TWO64 - ENOSYS)) = true.
Hypothesis H8 : mmap_answer_ok (resv ++ [(a3, 8192)]) 4096 a5 = true.
Hypothesis H9 : is_err a5 = false.

Lemma crun_B_gen : follow (cmalloc (strip (minit sec resv)) 40) [a1; a2; a3; a4; a5] = Some (strip (ST0_B sec resv a3 a5), Some (1%N, 64)).
Proof using H1 Hb H2 H3 H4 H5 H6 H7 H8 H9.
apply follow_of_eruns0.
mgo. mchk H1. rewrite Hb.
mgo. mchk H2.
mgo. mchk H3.
mgo. mchk H4.
mgo. mchk H5.
mgo. mchk H6.
mgo. mchk H7.
mgo. mchk H8.
mgo. mchk H9.
mgo.
lazymatch goal with |- follow (eruns ?s ?u ?o (SRet ?x)) [] = ?r => let x' := flat x in change_no_check (Some (o, x') = r) end.
reflexivity.
Qed.
End B.

Theorem startup_cmalloc40_mmap {RC__ : RunConsts} (sec : Z) (resv : list (Z * Z)) (brk0 mb grp : Z) :
brk0_answer_ok brk0 = true ->
mmap_answer_ok (resv ++ []) (2 * PGSZ) mb = true ->
is_err mb = false ->
mmap_answer_ok (resv ++ [(mb, 8192)]) 4096 grp = true ->
is_err grp = false ->
follow (cmalloc (strip (minit sec resv)) 40) [brk0; brk0; mb; 0; grp] = Some (strip (ST0_B sec resv mb grp), Some (1%N, 64)).
Proof.
intros H1 H4 H5 H8 H9.
apply crun_B_gen; try assumption; try reflexivity.
- unfold brk0_answer_ok in H1. apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1a H1b].
apply round_up_pg_aligned; [apply Z.ltb_lt in H1a; lia | apply Z.eqb_eq in H1b; exact H1b].
- unfold brk_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
- apply Z.eqb_neq. unfold PGSZ. lia.
Qed.

Definition BLK0_B (sec : Z) (resv : list (Z * Z)) (mb grp : Z) : block :=
(((1%N, 64), fresh_off (strip (ST0_B sec resv mb grp)) (1%N, 64) 40), grp + 64, 40).

Theorem areach_main_B {RC__ : RunConsts} (sec : Z) (resv : list (Z * Z)) (brk0 mb grp : Z) :
0 <= sec < 2^64 ->
brk0_answer_ok brk0 = true ->
mmap_answer_ok (resv ++ []) (2 * PGSZ) mb = true ->
is_err mb = false ->
mmap_answer_ok (resv ++ [(mb, 8192)]) 4096 grp = true ->
is_err grp = false ->
AREACH_from resv sec (ST0_B sec resv mb grp) [BLK0_B sec resv mb grp].
Proof.
intros Hs H1 H4 H5 H8 H9.
pose proof (startup_malloc40_mmap sec resv brk0 mb grp H1 H4 H5 H8 H9) as RUN.
pose proof (startup_cmalloc40_mmap sec resv brk0 mb grp H1 H4 H5 H8 H9) as CRUN.
pose proof (areach_malloc_some (minit sec resv) [] 40 o0 o0 _ _ (1%N, 64) _ (1%N, 64) (areach_init Hs) ltac:(lia) RUN CRUN) as AR.
exact AR.
Qed.

Lemma brk_link_main_B {RC__ : RunConsts} (sec : Z) (resv : list (Z * Z)) (mb grp : Z) (pbrk : Z) :
brk_link (ST0_B sec resv mb grp) pbrk.
Proof. exact I. Qed.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw QZsi Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QZsi.Mq0.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Export QsKa.Mq7.
Import Qw5U.Mq4.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MuslAMemset.

Lemma amemset_sound_U : amemset_spec_U.
Proof.
unfold amemset_spec_U.
intros until Q. intros UP0 RT Hd0 Hd47 Hdlo Ha0 Ha1 Ha2 Hc Hn Hsz DST ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.

pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RTC. cbn [app] in RTC.
apply Forall_cons_iff in RTC as [GOTF RTC]. apply Forall_cons_iff in RTC as [FLAG RTC]. apply Forall_cons_iff in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [REALM RTC]. cbn [fst snd] in GOTF, FLAG, REALM.
do 57 (apply Forall_cons_iff in RTC as [_ RTC]).
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in GOTF. apply ro_C8_of_bytes_at in REALM. apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (FLAGc : ro_cells asegs m 0xf07d9 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact FLAG]). clear FLAG.
pose proof (munch_refl [(d, d + n); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
unfold A_MEMSET_U. carve_frame 56%nat ST.
do 10 step.

assert (TAILG : forall (xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 z3 z4 z5 z6 : word) (oldz : list byte) mz,
munch [(d, d + n); (lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -56) ->
rw_cells asegs mz (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mz d [CB (Z.to_nat n) oldz] ->
ro_cells asegs mz 0xe7db0 [C8 (Z_to_bv 64 0xdb750)] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x0 x1 x2 sp w1 (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 w2 w3 (Z_to_bv 64 (bv_unsigned sp + -2128)) w5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 0x61c70) fc None mz (seg_rom asegs))).
{ intros xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 z3 z4 z5 z6 oldz mz MUz WMz MIz STz FRz DSTz REALMz.
clear GOTF REALM GOT CELL FLAGc MU WM MU0 ST FR DST MI.
step. step. step.
(call amemset_real_specZ); [lia | lia | lia | exact DSTz | assumption |].
do 10 step.
eapply K;
[ match goal with H : munch _ m ?mf |- munch _ m ?mf => exact H end
| match goal with H : wmono _ m ?mf |- wmono _ m ?mf => exact H end
| assumption
| match goal with H : rw_cells _ ?mf d [CB _ (repeat _ _)] |- rw_cells _ ?mf d _ =>
rewrite unsigned_lit in H by lia; rewrite Z.mod_small in H by lia; exact H end
| release_frame FRz STz (bv_unsigned sp); exact STz ]. }
do 4 step. if_false.
step. step. step.
step.
rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. step.
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
{
rewrite Hn0. change (0 + -65) with (-65). if_true.
step. if_false.
step.
rewrite <- Hn0. eapply TAILG; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact REALM]. }
destruct (Z.lt_ge_cases 64 n) as [Hbig | Hsmall].
{
if_truex.
step. if_truex.
do 4 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2128) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply region_is_poisoned_sound_U with (s := d) (n := n) (lo := lo);
[ eapply unpoisoned_transport; [exact (UP0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]
| eapply asan_rt_ok_transport; [exact RT | exact MU0 | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]]
| destruct Hsz as [?|?]; [lia | assumption]
| lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 ST1' UP2 RT2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x61dc8)) with (Z_to_bv 64 0x61dc8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
eapply TAILG; [exact MU | exact WM | exact MI2 | eapply stk_merge; [exact ST1' | exact ST2 | lia] | exact FR | exact DST | exact REALM]. }

pose proof (UP0 ltac:(lia)) as UP.
rewrite (size_test_n n) by lia. cbv iota.
assert (Hg : d / 8 <= (d + n - 1) / 8 <= d / 8 + 8) by (Z.div_mod_to_equations; lia).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UP1 : unpoisoned asegs mc A_SB d n)
by (eapply unpoisoned_transport; [exact UP | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia])
end.
clear MU0.
destruct (unpoisoned_word asegs _ _ _ _ (d / 8 + A_SB) UP1 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((d + n - 1) / 8 + A_SB) UP1 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
unfold A_SB in W1c, W2c.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GR0 : forall j, 0 <= j -> d / 8 + j < (d + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (d / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0])
end.
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (d / 8 + 2147450880 + j) with ((d / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UP1). lia. }
do 4 step.
do 3 step.
do 2 step.
do 2 step.
sh_norm.
replace (d + n + -1) with (d + n - 1) by lia.
replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia.
replace (2147450880 + (d + n - 1) / 8) with ((d + n - 1) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (d / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((d + n - 1) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 s2 s3 (Z_to_bv 64 (bv_unsigned sp + -2128)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61c70) fc None mc (seg_rom asegs)))
by (intros x3 x4 x5 x6 x7; eapply TAILG; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact REALM])
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((d + n - 1) / 8 - d / 8 - i) = Kn -> 0 <= i -> d / 8 + i < (d + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n)
(Z_to_bv 64 (d / 8 + 2147450880 + i)) (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 s3 (Z_to_bv 64 (bv_unsigned sp + -2128)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61d9c) fc None mc (seg_rom asegs)))
end.
{ induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|].
pose proof (GR0 i Hi Hig) as HR.
step. rewrite ?zxb_zero.
clear HR.
step. step.
rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (d / 8 + i + 1) ((d + n - 1) / 8)) as [Heq|Hne].
- if_falsex.
step. step. if_true. apply TAIL.
- if_truex.
replace (d / 8 + 2147450880 + i + 1) with (d / 8 + 2147450880 + (i + 1)) by lia.
apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRL : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (d + n - 1) mod 8 < v)))
end.
{ destruct (unpoisoned_last asegs _ _ _ _ UP1) as (v & Hro & Hv). exists v. split; [| exact Hv].
apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
destruct HRL as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step. rewrite (sxb_small v) by lia. clear HR.
step.
rewrite (unsigned_lit (d + n - 1)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.

destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.

step.
destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex.
replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia.
apply (LOOP (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((d + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.

step.
destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex.
replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia.
apply (LOOP (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia.
Qed.
End MuslAMemset.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import QbFI. Import Qhd4.
Import Qwm6.Mq4. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Lemma skipn_nth_cons : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
intros X l. induction l as [|y l IH]; intros i x H; [destruct i; discriminate H|].
destruct i as [|i]; cbn in H |- *; [injection H as ->; reflexivity | apply IH; exact H].
Qed.
Lemma skipn_all_nil : forall {X} (l : list X) i, (length l <= i)%nat -> skipn i l = [].
Proof. intros X l i H. apply skipn_all2. exact H. Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation rw_cells := (rw_cells segs).
Notation jnode := (jnode segs fn).

Lemma jnode_hdr : forall s m REST p rc pb0, jnode s m REST p rc pb0 ->
exists n ty udel ud cs rest, REST = (p, n) :: rest /\ 48 <= n /\
rw_cells m p ([C4 (wz ty); C4 (wz rc); C8 (wz (fn_ofF fn s)); C8 (wz pb0); C8 (wz udel); C8 (wz ud)] ++ cs).
Proof.
intros s m REST p rc pb0 J. destruct s as [|[|]| |[|]|kids|kids]; cbn in J.
- destruct J as (b & junk & -> & H). exists 48, JT_BOOLEAN, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & ud & udn & uds & -> & _ & H & _). exists 48, JT_DOUBLE, (fn_free_userdata fn), ud. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & -> & _ & H). exists 48, JT_DOUBLE, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (cty & v & junk & -> & _ & H). exists 56, JT_INT, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & pd & pdn & str & junk2 & -> & _ & _ & _ & H & _). exists 56, JT_STRING, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & str & junk & -> & Hl & _ & H). exists (str_objsize len), JT_STRING, 0, 0. eexists. exists []. split; [reflexivity|]. split; [unfold str_objsize; lia|]. exact H.
- destruct J as (t & TBS & kvs & KBS & -> & H & _). exists 48, JT_OBJECT, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (a & ABS & ps & KBS & -> & H & _). exists 48, JT_ARRAY, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
Qed.

Lemma kids_okp_nth : forall m kids ps KBS i k,
kids_okp segs fn m kids ps KBS -> nth_error kids i = Some k ->
exists v bs, nth_error ps i = Some v /\ nth_error KBS i = Some bs /\
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jval segs fn s' m bs v 1 end.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros ps KBS i k KOK Hn; [destruct i; discriminate Hn|].
destruct ps as [|v0 ps]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
destruct KOK as [H0 KOK].
destruct i as [|i]; cbn in Hn |- *.
- injection Hn as ->. exists v0, bs0. auto.
- eapply IH; eassumption.
Qed.
Lemma kids_okp_len : forall m kids ps KBS, kids_okp segs fn m kids ps KBS -> length ps = length kids /\ length KBS = length kids.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros ps KBS KOK.
- destruct ps; [|destruct KOK]. destruct KBS; [|destruct KOK]. split; reflexivity.
- destruct ps as [|v0 ps]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
destruct KOK as [_ KOK]. destruct (IH _ _ KOK) as [L1 L2]. cbn. lia.
Qed.
Lemma kids_okv_nth : forall m kids kvs KBS i k,
kids_okv segs fn m kids kvs KBS -> nth_error kids i = Some k ->
exists kk v bs, nth_error kvs i = Some (kk, v) /\ nth_error KBS i = Some bs /\
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jval segs fn s' m bs v 1 end.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros kvs KBS i k KOK Hn; [destruct i; discriminate Hn|].
destruct kvs as [|[kk0 v0] kvs]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
destruct KOK as [H0 KOK].
destruct i as [|i]; cbn in Hn |- *.
- injection Hn as ->. exists kk0, v0, bs0. auto.
- eapply IH; eassumption.
Qed.
Lemma kids_okv_len : forall m kids kvs KBS, kids_okv segs fn m kids kvs KBS -> length kvs = length kids /\ length KBS = length kids.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros kvs KBS KOK.
- destruct kvs; [|destruct KOK]. destruct KBS; [|destruct KOK]. split; reflexivity.
- destruct kvs as [|[kk0 v0] kvs]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
destruct KOK as [_ KOK]. destruct (IH _ _ KOK) as [L1 L2]. cbn. lia.
Qed.

Lemma kids_okp_agree : forall m m' BS kids ps KBS,
kids_okp segs fn m kids ps KBS -> agree_on segs BS m m' -> incl (concat KBS) BS -> kids_okp segs fn m' kids ps KBS.
Proof.
intros m m' BS kids. induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS AG HiK; try exact KIDS.
cbn in HiK. destruct KIDS as [K1 K2]. split.
- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply (jval_agree segs fn); [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
- apply IH; [exact K2 | exact AG | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
Qed.
Lemma kids_okv_agree : forall m m' BS kids kvs KBS,
kids_okv segs fn m kids kvs KBS -> agree_on segs BS m m' -> incl (concat KBS) BS -> kids_okv segs fn m' kids kvs KBS.
Proof.
intros m m' BS kids. induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS AG HiK; try exact KIDS.
cbn in HiK. destruct KIDS as [K1 K2]. split.
- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply (jval_agree segs fn); [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
- apply IH; [exact K2 | exact AG | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
Qed.

Lemma jtxk_arr_step_some : forall m kids ps KBS i s' v bs P Y acc w R,
kids_okp segs fn m kids ps KBS -> nth_error kids i = Some (Some s') -> nth_error ps i = Some v -> nth_error KBS i = Some bs -> pbtail P ->
jtxk_arr (skipn i kids) (P ++ concat (skipn i KBS) ++ Y) acc = Some (w, R) ->
v <> 0 /\ jval segs fn s' m bs v 1 /\
exists pbk PBSk RESTk wi P', bs = RESTk ++ PBSk /\ jnode s' m RESTk v 1 pbk /\ 0 <= wi /\ acc + (2 + wi) <= w /\
jtx s' (RESTk ++ (PBSk ++ concat (skipn (S i) KBS) ++ Y)) = Some (wi, P' ++ concat (skipn (S i) KBS) ++ Y) /\ pbtail P' /\
jtxk_arr (skipn (S i) kids) (P' ++ concat (skipn (S i) KBS) ++ Y) (acc + (2 + wi)) = Some (w, R).
Proof.
intros m kids ps KBS i s' v bs P Y acc w R KOK Hk Hp Hb HP H.
destruct (kids_okp_nth _ _ _ _ _ _ KOK Hk) as (v' & bs' & Hp' & Hb' & Hv & JV).
rewrite Hp in Hp'. injection Hp' as <-. rewrite Hb in Hb'. injection Hb' as <-.
split; [exact Hv|]. split; [exact JV|].
rewrite (skipn_nth_cons _ _ _ Hk), (skipn_nth_cons _ _ _ Hb) in H. cbn [jtxk_arr concat] in H.
destruct (jtx s' (P ++ (bs ++ concat (skipn (S i) KBS)) ++ Y)) as [[wi R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (jval_jtx_node segs fn _ _ _ _ _ _ _ _ JV E) as (pbk & PBSk & RESTk & EB & OP & JN & E').
destruct (jtx_val_tail segs fn _ _ _ _ _ JV _ _ _ E) as (P' & -> & HP').
exists pbk, PBSk, RESTk, wi, P'. split; [exact EB|]. split; [exact JN|].
split; [exact (jtx_nonneg _ _ _ _ E)|].
split; [eapply (jtxk_arr_acc (fun _ => True)); [intros s0 _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact H]|].
split; [exact E'|]. split; [exact HP' | exact H].
Qed.
Lemma jtxk_arr_step_none : forall m kids ps KBS i P Y acc w R,
kids_okp segs fn m kids ps KBS -> nth_error kids i = Some None -> pbtail P ->
jtxk_arr (skipn i kids) (P ++ concat (skipn i KBS) ++ Y) acc = Some (w, R) ->
nth_error ps i = Some 0 /\ acc + 6 <= w /\
jtxk_arr (skipn (S i) kids) (P ++ concat (skipn (S i) KBS) ++ Y) (acc + 6) = Some (w, R).
Proof.
intros m kids ps KBS i P Y acc w R KOK Hk HP H.
destruct (kids_okp_nth _ _ _ _ _ _ KOK Hk) as (v' & bs' & Hp' & Hb' & -> & ->).
split; [exact Hp'|].
rewrite (skipn_nth_cons _ _ _ Hk), (skipn_nth_cons _ _ _ Hb') in H. cbn [jtxk_arr concat app] in H. unfold NULL_W in H. change (2 + 4) with 6 in H.
split; [eapply (jtxk_arr_acc (fun _ => True)); [intros s0 _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact H] | exact H].
Qed.
Lemma jtxk_arr_done : forall kids i bs acc w R, (length kids <= i)%nat -> jtxk_arr (skipn i kids) bs acc = Some (w, R) -> w = acc.
Proof. intros kids i bs acc w R Hi H. rewrite (skipn_all_nil _ _ Hi) in H. cbn in H. injection H as <- _. reflexivity. Qed.

Lemma jtxk_obj_step_some : forall m kids kvs KBS keys i s' kk v bs kb P Y acc w R,
kids_okv segs fn m kids kvs KBS -> nth_error kids i = Some (Some s') -> nth_error kvs i = Some (kk, v) -> nth_error KBS i = Some bs ->
nth_error keys i = Some kb -> pbtail P ->
jtxk_obj (skipn i kids) (skipn i keys) (P ++ concat (skipn i KBS) ++ Y) acc = Some (w, R) ->
v <> 0 /\ jval segs fn s' m bs v 1 /\
exists pbk PBSk RESTk wi P', bs = RESTk ++ PBSk /\ jnode s' m RESTk v 1 pbk /\ 0 <= wi /\ acc + (key_w (snd kb) + wi) <= w /\
jtx s' (RESTk ++ (PBSk ++ concat (skipn (S i) KBS) ++ Y)) = Some (wi, P' ++ concat (skipn (S i) KBS) ++ Y) /\ pbtail P' /\
jtxk_obj (skipn (S i) kids) (skipn (S i) keys) (P' ++ concat (skipn (S i) KBS) ++ Y) (acc + (key_w (snd kb) + wi)) = Some (w, R).
Proof.
intros m kids kvs KBS keys i s' kk v bs [k kn] P Y acc w R KOK Hk Hp Hb Hkb HP H.
destruct (kids_okv_nth _ _ _ _ _ _ KOK Hk) as (kk' & v' & bs' & Hp' & Hb' & Hv & JV).
rewrite Hp in Hp'. injection Hp' as <- <-. rewrite Hb in Hb'. injection Hb' as <-.
split; [exact Hv|]. split; [exact JV|].
rewrite (skipn_nth_cons _ _ _ Hk), (skipn_nth_cons _ _ _ Hb), (skipn_nth_cons _ _ _ Hkb) in H. cbn [jtxk_obj concat] in H.
destruct (jtx s' (P ++ (bs ++ concat (skipn (S i) KBS)) ++ Y)) as [[wi R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (jval_jtx_node segs fn _ _ _ _ _ _ _ _ JV E) as (pbk & PBSk & RESTk & EB & OP & JN & E').
destruct (jtx_val_tail segs fn _ _ _ _ _ JV _ _ _ E) as (P' & -> & HP').
exists pbk, PBSk, RESTk, wi, P'. split; [exact EB|]. split; [exact JN|].
split; [exact (jtx_nonneg _ _ _ _ E)|]. cbn [snd].
split; [eapply jtxk_obj_acc; [intros s0 _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact H]|].
split; [exact E'|]. split; [exact HP' | exact H].
Qed.
Lemma jtxk_obj_step_none : forall m kids kvs KBS keys i kb P Y acc w R,
kids_okv segs fn m kids kvs KBS -> nth_error kids i = Some None -> nth_error keys i = Some kb -> pbtail P ->
jtxk_obj (skipn i kids) (skipn i keys) (P ++ concat (skipn i KBS) ++ Y) acc = Some (w, R) ->
(exists kk, nth_error kvs i = Some (kk, 0)) /\ acc + (key_w (snd kb) + 4) <= w /\
jtxk_obj (skipn (S i) kids) (skipn (S i) keys) (P ++ concat (skipn (S i) KBS) ++ Y) (acc + (key_w (snd kb) + 4)) = Some (w, R).
Proof.
intros m kids kvs KBS keys i [k kn] P Y acc w R KOK Hk Hkb HP H.
destruct (kids_okv_nth _ _ _ _ _ _ KOK Hk) as (kk' & v' & bs' & Hp' & Hb' & -> & ->).
split; [exists kk'; exact Hp'|].
rewrite (skipn_nth_cons _ _ _ Hk), (skipn_nth_cons _ _ _ Hb'), (skipn_nth_cons _ _ _ Hkb) in H. cbn [jtxk_obj concat app] in H. unfold NULL_W in H. cbn [snd].
split; [eapply jtxk_obj_acc; [intros s0 _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact H] | exact H].
Qed.
Lemma jtxk_obj_done : forall kids i keys bs acc w R, (length kids <= i)%nat -> jtxk_obj (skipn i kids) keys bs acc = Some (w, R) -> w = acc.
Proof. intros kids i keys bs acc w R Hi H. rewrite (skipn_all_nil _ _ Hi) in H. cbn in H. injection H as <- _. reflexivity. Qed.
End WithSegs.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QZsi.Mq1.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Export QsKa.Mqg.
Import Qw5U.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MuslAMemset.

Lemma amemset_sound_U : amemset_spec_U.
Proof.
unfold amemset_spec_U.
intros until Q. intros UP0 RT Hd0 Hd47 Hdlo Ha0 Ha1 Ha2 Hc Hn Hsz DST ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.

pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RTC. cbn [app] in RTC.
apply Forall_cons_iff in RTC as [GOTF RTC]. apply Forall_cons_iff in RTC as [FLAG RTC]. apply Forall_cons_iff in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [REALM RTC]. cbn [fst snd] in GOTF, FLAG, REALM.
do 60 (apply Forall_cons_iff in RTC as [_ RTC]).
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in GOTF. apply ro_C8_of_bytes_at in REALM. apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (FLAGc : ro_cells asegs m 0xf2e99 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact FLAG]). clear FLAG.
pose proof (munch_refl [(d, d + n); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
unfold A_MEMSET_U. carve_frame 56%nat ST.
do 10 step.

assert (TAILG : forall (xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 z3 z4 z5 z6 : word) (oldz : list byte) mz,
munch [(d, d + n); (lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -56) ->
rw_cells asegs mz (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mz d [CB (Z.to_nat n) oldz] ->
ro_cells asegs mz 0xea1d0 [C8 (Z_to_bv 64 0xdde14)] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x0 x1 x2 sp w1 (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 w2 w3 (Z_to_bv 64 (bv_unsigned sp + -2128)) w5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 0x62048) fc None mz (seg_rom asegs))).
{ intros xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 z3 z4 z5 z6 oldz mz MUz WMz MIz STz FRz DSTz REALMz.
clear GOTF REALM GOT CELL FLAGc MU WM MU0 ST FR DST MI.
step. step. step.
(call amemset_real_specZ); [lia | lia | lia | exact DSTz | assumption |].
do 10 step.
eapply K;
[ match goal with H : munch _ m ?mf |- munch _ m ?mf => exact H end
| match goal with H : wmono _ m ?mf |- wmono _ m ?mf => exact H end
| assumption
| match goal with H : rw_cells _ ?mf d [CB _ (repeat _ _)] |- rw_cells _ ?mf d _ =>
rewrite unsigned_lit in H by lia; rewrite Z.mod_small in H by lia; exact H end
| release_frame FRz STz (bv_unsigned sp); exact STz ]. }
do 4 step. if_false.
step. step. step.
step.
rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. step.
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
{
rewrite Hn0. change (0 + -65) with (-65). if_true.
step. if_false.
step.
rewrite <- Hn0. eapply TAILG; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact REALM]. }
destruct (Z.lt_ge_cases 64 n) as [Hbig | Hsmall].
{
if_truex.
step. if_truex.
do 4 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2128) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply region_is_poisoned_sound_U with (s := d) (n := n) (lo := lo);
[ eapply unpoisoned_transport; [exact (UP0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]
| eapply asan_rt_ok_transport; [exact RT | exact MU0 | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]]
| destruct Hsz as [?|?]; [lia | assumption]
| lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 ST1' UP2 RT2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x621a0)) with (Z_to_bv 64 0x621a0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
eapply TAILG; [exact MU | exact WM | exact MI2 | eapply stk_merge; [exact ST1' | exact ST2 | lia] | exact FR | exact DST | exact REALM]. }

pose proof (UP0 ltac:(lia)) as UP.
rewrite (size_test_n n) by lia. cbv iota.
assert (Hg : d / 8 <= (d + n - 1) / 8 <= d / 8 + 8) by (Z.div_mod_to_equations; lia).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UP1 : unpoisoned asegs mc A_SB d n)
by (eapply unpoisoned_transport; [exact UP | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia])
end.
clear MU0.
destruct (unpoisoned_word asegs _ _ _ _ (d / 8 + A_SB) UP1 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((d + n - 1) / 8 + A_SB) UP1 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
unfold A_SB in W1c, W2c.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GR0 : forall j, 0 <= j -> d / 8 + j < (d + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (d / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0])
end.
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (d / 8 + 2147450880 + j) with ((d / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UP1). lia. }
do 4 step.
do 3 step.
do 2 step.
do 2 step.
sh_norm.
replace (d + n + -1) with (d + n - 1) by lia.
replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia.
replace (2147450880 + (d + n - 1) / 8) with ((d + n - 1) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (d / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((d + n - 1) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 s2 s3 (Z_to_bv 64 (bv_unsigned sp + -2128)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x62048) fc None mc (seg_rom asegs)))
by (intros x3 x4 x5 x6 x7; eapply TAILG; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact REALM])
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((d + n - 1) / 8 - d / 8 - i) = Kn -> 0 <= i -> d / 8 + i < (d + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n)
(Z_to_bv 64 (d / 8 + 2147450880 + i)) (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 s3 (Z_to_bv 64 (bv_unsigned sp + -2128)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x62174) fc None mc (seg_rom asegs)))
end.
{ induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|].
pose proof (GR0 i Hi Hig) as HR.
step. rewrite ?zxb_zero.
clear HR.
step. step.
rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (d / 8 + i + 1) ((d + n - 1) / 8)) as [Heq|Hne].
- if_falsex.
step. step. if_true. apply TAIL.
- if_truex.
replace (d / 8 + 2147450880 + i + 1) with (d / 8 + 2147450880 + (i + 1)) by lia.
apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRL : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (d + n - 1) mod 8 < v)))
end.
{ destruct (unpoisoned_last asegs _ _ _ _ UP1) as (v & Hro & Hv). exists v. split; [| exact Hv].
apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
destruct HRL as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step. rewrite (sxb_small v) by lia. clear HR.
step.
rewrite (unsigned_lit (d + n - 1)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.

destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.

step.
destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex.
replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia.
apply (LOOP (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((d + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.

step.
destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex.
replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia.
apply (LOOP (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia.
Qed.
End MuslAMemset.
End RC__1.
End Mq5.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Fixpoint zlb_remove (p : Z) (LB : list (Z * Z)) : list (Z * Z) :=
match LB with
| [] => []
| b :: LB' => if Z.eqb (fst b) p then LB' else b :: zlb_remove p LB'
end.

Lemma zlb_remove_perm : forall LB p n,
List.NoDup (map fst LB) -> In (p, n) LB -> Permutation LB ((p, n) :: zlb_remove p LB).
Proof.
induction LB as [|b LB IH]; intros p n ND Hin; [destruct Hin|].
cbn [map] in ND. inversion ND as [|x l Hni ND']; subst. cbn [zlb_remove].
destruct Hin as [->|Hin].
- cbn [fst]. rewrite Z.eqb_refl. apply Permutation_refl.
- destruct (Z.eqb_spec (fst b) p) as [E|NE].
+ exfalso. apply Hni. rewrite E. apply in_map_iff. exists (p, n). split; [reflexivity| exact Hin].
+ eapply Permutation_trans; [apply perm_skip; apply (IH p n ND' Hin)| apply perm_swap].
Qed.

Lemma bptr_eqb_true_iff p q : bptr_eqb p q = true <-> p = q.
Proof.
unfold bptr_eqb. rewrite andb_true_iff, QSfG.Mq2.aptr_eqb_eq, Z.eqb_eq. destruct p, q; cbn; split; [intros [-> ->]; reflexivity| intros E; injection E; auto].
Qed.

Lemma lb_remove_split : forall (b0 : block) LB0,
In b0 LB0 -> List.NoDup (map blk_id LB0) ->
exists l1 l2, LB0 = l1 ++ b0 :: l2 /\ lb_remove (blk_id b0) LB0 = l1 ++ l2.
Proof.
intros b0 LB0. induction LB0 as [|b LB IH]; intros Hin ND; [destruct Hin|].
cbn [map] in ND. inversion ND as [|x l Hni ND']; subst. unfold lb_remove. rewrite filter_cons.
destruct Hin as [->|Hin].
- destruct (decide _) as [D|D].
{ exfalso. revert D. rewrite (proj2 (bptr_eqb_true_iff _ _) eq_refl). cbn. exact (fun x => x). }
exists [], LB. split; [reflexivity|]. cbn [app].
clear IH ND D. induction LB as [|b LB IH]; [reflexivity|].
cbn [map] in Hni, ND'. inversion ND'; subst. rewrite filter_cons.
destruct (decide _) as [D|D].
+ f_equal. apply IH; [intros H'; apply Hni; right; exact H'| assumption].
+ exfalso. apply Hni. left. destruct (bptr_eqb (blk_id b) (blk_id b0)) eqn:E; [| exfalso; apply D; exact I].
apply bptr_eqb_true_iff in E. exact E.
- destruct (IH Hin ND') as (l1 & l2 & E1 & E2).
destruct (decide _) as [D|D].
+ exists (b :: l1), l2. rewrite E1 at 1. split; [reflexivity|]. cbn [app]. f_equal. unfold lb_remove in E2. exact E2.
+ exfalso. apply Hni. destruct (bptr_eqb (blk_id b) (blk_id b0)) eqn:E; [| exfalso; apply D; exact I].
apply bptr_eqb_true_iff in E. rewrite E. apply in_map. exact Hin.
Qed.

Lemma ap_remove_perm : forall c l, In c l -> Permutation l (c :: ap_remove c l).
Proof.
induction l as [|y l IH]; intros Hin; [destruct Hin|]. cbn [ap_remove].
destruct (QSfG.Mq2.aptr_eqb_spec y c) as [->|NE]; [apply Permutation_refl|].
destruct Hin as [->|Hin]; [congruence|].
eapply Permutation_trans; [apply perm_skip; apply IH; exact Hin| apply perm_swap].
Qed.

Lemma ap_remove_sub : forall c l x, In x (ap_remove c l) -> In x l.
Proof.
induction l as [|y l IH]; intros x Hin; [destruct Hin|]. cbn [ap_remove] in Hin.
destruct (aptr_eqb y c); [right; exact Hin|]. destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; exact Hin].
Qed.

Lemma ap_remove_nodup : forall c l, List.NoDup l -> List.NoDup (ap_remove c l).
Proof.
induction l as [|y l IH]; intros ND; [constructor|]. inversion ND; subst. cbn [ap_remove].
destruct (aptr_eqb y c); [assumption|]. constructor; [| apply IH; assumption].
intros Hin. apply H1. apply (ap_remove_sub c). exact Hin.
Qed.

Lemma blk_addr_nodup : forall (LB0 : list block),
List.NoDup (map blk_id LB0) ->
(forall b1 b2, In b1 LB0 -> In b2 LB0 -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1) ->
Forall (fun b => 1 <= blk_size b) LB0 ->
List.NoDup (map blk_addr LB0).
Proof.
induction LB0 as [|b LB IH]; intros ND DJ SZ; [constructor|].
cbn [map] in ND |- *. inversion ND as [|x l Hni ND']; subst. inversion SZ as [|y l' SZb SZ']; subst.
constructor.
- intros Hin. apply in_map_iff in Hin as (b' & Ea & Hin').
assert (NE : blk_id b <> blk_id b') by (intros E; apply Hni; rewrite E; apply in_map; exact Hin').
pose proof (DJ b b' (or_introl eq_refl) (or_intror Hin') NE) as D.
pose proof (proj1 (List.Forall_forall _ _) SZ' b' Hin') as S'. cbn beta in S', SZb. rewrite Ea in D. lia.
- apply IH; [exact ND'| intros b1 b2 H1 H2; apply DJ; right; assumption| exact SZ'].
Qed.

