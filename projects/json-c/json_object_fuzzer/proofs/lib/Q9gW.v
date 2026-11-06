(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkfD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUnM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZbm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZbm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QF0G.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QF0G.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Notation mem := (word -> option byte) (only parsing).

Section Hide.
Context {BAND : Band}.
Variable F : word -> bool.

Lemma agree_hide : forall (P : Z -> Prop) (m : mem), (forall x, 0 <= x < 2^64 -> P x -> F (wa x) = false) ->
agree_on asegs P m (mrestrict F m).
Proof.
intros P m HP a Ha Pa. pose proof (HP a Ha Pa) as Fa. unfold wview, mrestrict. rewrite Fa. split; [reflexivity| exact (fun H => H)].
Qed.

Definition hzone (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (x : Z) : Prop :=
fp_RTconst RE X x \/ fp_RStats RE X x \/ fp_RPrim G RE X x \/ fp_RChunks a LB0 G RE X x \/ fp_RSec a RE X x
\/ fp_RQuar a LB0 G RE X x \/ fp_RDepot RE X x \/ fp_RFake FS0 RE X x
\/ in_live_used LB0 x \/ in_iv (ae_fs_base RE, A_FS_MAP_SIZE) x \/ in_sh (ae_fs_base RE, A_FS_MAP_SIZE) x.

Theorem run_hide : forall a LB0 FS0 G RE X (m : mem),
(forall x, 0 <= x < 2^64 -> hzone a LB0 FS0 G RE X x -> F (wa x) = false) ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RChunks a LB0 G RE X m -> RSec a LB0 RE X m -> RQuar a LB0 G RE X m ->
RDepot RE X m -> RFake FS0 RE X m ->
RTconst RE X (mrestrict F m) /\ RStats RE X (mrestrict F m) /\ RPrim a G RE X (mrestrict F m) /\ RChunks a LB0 G RE X (mrestrict F m)
/\ RSec a LB0 RE X (mrestrict F m) /\ RQuar a LB0 G RE X (mrestrict F m) /\ RDepot RE X (mrestrict F m) /\ RFake FS0 RE X (mrestrict F m).
Proof.
intros a LB0 FS0 G RE X m HZ R1 R2 R3 R4 R5 R6 R7 R8. unfold hzone in HZ.
split; [apply (RTconst_frame_nw RE X m _ R1); apply agree_hide; intros x Hx P; apply (HZ x Hx); tauto|].
split; [apply (RStats_frame_nw RE X m _ R2); apply agree_hide; intros x Hx P; apply (HZ x Hx); tauto|].
split; [apply (RPrim_frame_nw a G RE X m _ R3); apply agree_hide; intros x Hx P; apply (HZ x Hx); tauto|].
split; [apply (RChunks_frame_nw a LB0 G RE X m _ R4); apply agree_hide; intros x Hx P; apply (HZ x Hx); tauto|].
split; [apply (RSec_frame_nw a LB0 RE X m _ R5); apply agree_hide; intros x Hx P; apply (HZ x Hx); tauto|].
split; [apply (RQuar_frame_nw a LB0 G RE X m _ R6); apply agree_hide; intros x Hx P; apply (HZ x Hx); tauto|].
split; [apply (RDepot_frame_nw RE X m _ R7); apply agree_hide; intros x Hx P; apply (HZ x Hx); tauto|].
apply (RFake_frame_nw RE X FS0 m _ R8); apply agree_hide; intros x Hx P; apply (HZ x Hx); tauto.
Qed.
End Hide.

Section Coarse.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.

Definition ivsh (o : Z * Z) (x : Z) : Prop := in_iv o x \/ in_sh o x.

Definition rzone (x : Z) : Prop :=
0x10000 <= x < 0x645000
\/ (exists o, In o (rlay_objs RE X) /\ ivsh o x)
\/ ivsh (prim_lo RE, 2^37 + 0x1000) x
\/ ivsh (ptrarr_lo RE, 0x800000) x
\/ (exists e, In e (as_reg a) /\ ivsh (se_beg e, se_size e) x)
\/ in_live_used LB0 x.

Lemma in_sh_sub : forall lo len lo' len' x, lo' mod 8 = 0 -> lo' <= lo -> lo + len <= lo' + len' -> 0 <= len ->
in_sh (lo, len) x -> in_sh (lo', len') x.
Proof.
intros lo len lo' len' x A8 L1 L2 L0 [H1 H2]. unfold in_sh in *. cbn [fst snd] in *. rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
Qed.

Local Ltac in_obj o Ho := right; left; exists o; split; [exact Ho|].
Local Ltac in_prim := right; right; left.
Local Ltac in_sec e He := do 4 right; left; exists e; split; [exact He|].

Lemma prim8 : prim_lo RE mod 8 = 0.
Proof. pose proof (rl_prim a LB0 FS0 G RE X GC) as (P0 & _). Z.div_mod_to_equations. lia. Qed.

Lemma slot_in_prim : forall c i t x, tag_at G c i = Some t -> in_iv (slot_beg RE c i, class_size c) x -> rzone x.
Proof.
intros c i t x Ht [H1 H2]. cbn [fst snd] in *. pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & P2 & _).
in_prim. left. unfold prim_hi, prim_lo in *. split; cbn [fst snd]; lia.
Qed.
Lemma slot_sh_in_prim : forall c i t x, tag_at G c i = Some t -> in_sh (slot_beg RE c i, class_size c) x -> rzone x.
Proof.
intros c i t x Ht H. pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & P2 & _ & _ & _ & _ & _ & S1 & _).
in_prim. right. apply (in_sh_sub (slot_beg RE c i) (class_size c)); [exact prim8| exact P1| unfold prim_hi, prim_lo in *; lia| lia| exact H].
Qed.
Lemma sec8 : forall e, In e (as_reg a) -> se_beg e mod 8 = 0 /\ kPage <= se_size e.
Proof.
intros e He. pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (E1 & _ & _ & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1, M2. pose proof kconsts as (_ & _ & _ & _ & KP & _).
split; [Z.div_mod_to_equations; lia| lia].
Qed.

Theorem hzone_coarse : forall x, hzone a LB0 FS0 G RE X x -> rzone x.
Proof.
intros x HZ. pose proof kconsts as (_ & KO & KS & K32 & KP & _).
destruct HZ as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]].
-  destruct H as [H|[H|[H|H]]].
+ left. exact (proj1 (rtconst_img_ok x H)).
+ in_obj (rl_T X, 0x1000) (T_obj RE X). left. destruct H; split; cbn [fst snd] in *; lia.
+ in_obj (rl_ctx X, 0x10000) (ctx_obj RE X). left. destruct H; split; cbn [fst snd] in *; lia.
+ in_obj (rl_dtls X, 0x1000) (dtls_obj RE X). left. exact H.
-  destruct H as [H|[H|H]].
+ in_obj (rl_T X, 0x1000) (T_obj RE X). left. destruct H; split; cbn [fst snd] in *; lia.
+ left. destruct H as [H1 H2]. unfold A_ERRNO in *. cbn [fst snd] in *. lia.
+ left. lia.
-  destruct H as [H|[H|[H|[H|[[H _]|[H _]]]]]].
+ in_prim. left. destruct H as [H1 H2]. unfold region_info, prim_lo in *. split; cbn [fst snd] in *; lia.
+ in_obj (rl_T X, 0x1000) (T_obj RE X). left. destruct H; split; cbn [fst snd] in *; lia.
+ destruct H as (c & Hc & Hx). rewrite K32 in Hc. pose proof (region_in_prim RE c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
in_prim. left. split; cbn [fst snd]; lia.
+ destruct H as (c & Hc & Hx). rewrite K32 in Hc. pose proof (region_in_prim RE c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
in_prim. right. apply (in_sh_sub (fa_beg (ae_L RE) c) kFreeArraySize); [exact prim8| lia| lia| rewrite KS; lia| exact Hx].
+ destruct H as (c & Hc & Hx). rewrite K32 in Hc. pose proof (region_in_prim RE c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
in_prim. left. rewrite KO, KS in *. split; cbn [fst snd]; lia.
+ destruct H as (c & Hc & Hx). rewrite K32 in Hc. pose proof (region_in_prim RE c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
in_prim. right. apply (in_sh_sub (reg_beg (ae_L RE) c) kFreeArrayOffset); [exact prim8| lia| rewrite KO, KS in *; lia| rewrite KO; lia| exact Hx].
-  destruct H as [[[H|H] _]|[H|H]].
+ destruct H as (c & i & t & Ht & _ & Hx). exact (slot_in_prim c i t x Ht Hx).
+ destruct H as (e & He & _ & Hx). in_sec e He. left. split; cbn [fst snd]; lia.
+ destruct H as (c & i & t & Ht & _ & Hx). exact (slot_sh_in_prim c i t x Ht Hx).
+ destruct H as (e & He & _ & Hx). destruct (sec8 e He) as [S8 SK]. in_sec e He. right.
apply (in_sh_sub (se_beg e + kPage) (se_size e - kPage)); [exact S8| lia| lia| lia| exact Hx].
-  destruct H as [H|[H|[H|H]]].
+ left. destruct H as [H1 H2]. unfold A_INSTANCE in *. cbn [fst snd] in *. lia.
+ do 3 right; left. left. exact H.
+ destruct H as (e & He & Hx). destruct (sec8 e He) as [S8 SK]. in_sec e He. left. split; cbn [fst snd]; lia.
+ destruct H as (e & He & Hx). destruct (sec8 e He) as [S8 SK]. in_sec e He. right.
apply (in_sh_sub (se_beg e) kPage); [exact S8| lia| lia| lia| exact Hx].
-  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
+ in_obj (rl_T X, 0x1000) (T_obj RE X). left. destruct H; split; cbn [fst snd] in *; lia.
+ left. destruct H as [H1 H2]. unfold A_INSTANCE in *. cbn [fst snd] in *. lia.
+ left. destruct H as [H1 H2]. unfold A_INSTANCE in *. cbn [fst snd] in *. lia.
+ left. destruct H as [H1 H2]. cbn [fst snd] in *. lia.
+ left. destruct H as [H1 H2]. cbn [fst snd] in *. lia.
+ destruct H as (c & i & t & Ht & _ & Hx). exact (slot_in_prim c i t x Ht Hx).
+ destruct H as (c & i & t & Ht & _ & Hx). exact (slot_sh_in_prim c i t x Ht Hx).
+ destruct H as (e & He & _ & Hx). in_sec e He. left. split; cbn [fst snd]; lia.
+ destruct H as (e & He & _ & Hx). destruct (sec8 e He) as [S8 SK]. in_sec e He. right.
apply (in_sh_sub (se_beg e + kPage) (se_size e - kPage)); [exact S8| lia| lia| lia| exact Hx].
-  destruct H as [H|[H|[H|H]]].
+ left. destruct H as [H1 H2]. cbn [fst snd] in *. lia.
+ in_obj (rl_dn X, 0x100000) (dn_obj RE X). left. exact H.
+ in_obj (rl_ssb X, 0x800000) (ssb_obj RE X). left. exact H.
+ in_obj (rl_T X, 0x1000) (T_obj RE X). left. split; cbn [fst snd]; lia.
-  in_obj (ae_fs_base RE, A_FS_MAP_SIZE) (fs_obj RE X). destruct H as [[H _]|[H _]]; [left| right]; exact H.
-  do 5 right. exact H.
- in_obj (ae_fs_base RE, A_FS_MAP_SIZE) (fs_obj RE X). left. exact H.
- in_obj (ae_fs_base RE, A_FS_MAP_SIZE) (fs_obj RE X). right. exact H.
Qed.
End Coarse.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuLP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5bV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.

Module DI := QCrt.
Module DA := QuLP.

Section HiddenJo.
Context {RC__ : Q6q3.RunConsts}.
Variable guard : word.
#[local] Instance BANDj : Band := DA.Band_RC guard.

Theorem dc_run_hidden_jo : forall (LV : Qsn5.lvp) (F : word -> bool)
(s : PStateA) (LB0 : list ablock) (FS0 : list fframe) (RE : DI.aentry) (X : rlay) (G : ghost) (m : mem),
gcons (ps_a s) LB0 FS0 G (DA.toRA RE) X ->
RTconst (DA.toRA RE) X m -> RStats (DA.toRA RE) X m -> RPrim (ps_a s) G (DA.toRA RE) X m -> RChunks (ps_a s) LB0 G (DA.toRA RE) X m ->
RSec (ps_a s) LB0 (DA.toRA RE) X m -> RQuar (ps_a s) LB0 G (DA.toRA RE) X m -> RDepot (DA.toRA RE) X m -> RFake FS0 (DA.toRA RE) X m ->
(forall x, 0 <= x < 2^64 -> hzone (ps_a s) LB0 FS0 G (DA.toRA RE) X x -> F (wa x) = false) ->
DI.dc_run _ _ _ _ (DA.DCo_jo guard LV) s LB0 FS0 RE (mrestrict F m).
Proof.
intros LV F s LB0 FS0 RE X G m GC R1 R2 R3 R4 R5 R6 R7 R8 HZ.
destruct (run_hide F (ps_a s) LB0 FS0 G (DA.toRA RE) X m HZ R1 R2 R3 R4 R5 R6 R7 R8) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
exists X, G, LB0, FS0. split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
split; [exact GC|]. repeat (split; [assumption|]). assumption.
Qed.
End HiddenJo.

Section HiddenJoCoarse.
Context {RC__ : Q6q3.RunConsts}.
Variable guard : word.
#[local] Instance BANDjc : Band := DA.Band_RC guard.

Theorem dc_run_hidden_jo_coarse : forall (LV : Qsn5.lvp) (F : word -> bool)
(s : PStateA) (LB0 : list ablock) (FS0 : list fframe) (RE : DI.aentry) (X : rlay) (G : ghost) (m : mem),
gcons (ps_a s) LB0 FS0 G (DA.toRA RE) X ->
RTconst (DA.toRA RE) X m -> RStats (DA.toRA RE) X m -> RPrim (ps_a s) G (DA.toRA RE) X m -> RChunks (ps_a s) LB0 G (DA.toRA RE) X m ->
RSec (ps_a s) LB0 (DA.toRA RE) X m -> RQuar (ps_a s) LB0 G (DA.toRA RE) X m -> RDepot (DA.toRA RE) X m -> RFake FS0 (DA.toRA RE) X m ->
(forall x, 0 <= x < 2^64 -> rzone (ps_a s) LB0 (DA.toRA RE) X x -> F (wa x) = false) ->
DI.dc_run _ _ _ _ (DA.DCo_jo guard LV) s LB0 FS0 RE (mrestrict F m).
Proof.
intros LV F s LB0 FS0 RE X G m GC R1 R2 R3 R4 R5 R6 R7 R8 HZ.
apply (dc_run_hidden_jo guard LV F s LB0 FS0 RE X G m GC R1 R2 R3 R4 R5 R6 R7 R8).
intros x Hx HZx. apply (HZ x Hx). exact (hzone_coarse (ps_a s) LB0 FS0 G (DA.toRA RE) X GC x HZx).
Qed.
End HiddenJoCoarse.
