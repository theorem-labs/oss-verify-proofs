(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 QCcH Q7UD Qwm6 QZsi QYZ0 Qsn5 Q2ui QCUT QlES QQIi Q6sh QzgH Q7z8 QKTr QgTJ QCrt QU91 QuLP QrOY QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QCoy QLPb QY73 Q72M QDRB Qo4M QrQA QLJz QFop Q5o6 Q0Cb Q92D Qb5q QVyC QkIR QvG1 Qp4j QDw3 QNwL QUil Q7lu Qx84.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.

Import Qsn5 Q2ui.

Import QlES.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QCoy QLPb QY73 Q72M QDRB.
Import Qo4M QrQA QLJz QFop Q5o6 Q0Cb Q92D Qb5q.

Import QUil Q7lu Qx84.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma find_segment_none_below : forall segs a n bot,
(forall seg, In seg segs -> bot <= Z.of_N (seg_base seg)) -> a < bot -> find_segment segs a n = None.
Proof.
induction segs as [|s rest IH]; intros a n bot H Ha; [reflexivity|]. cbn [find_segment].
pose proof (H s (or_introl eq_refl)) as Hs.
destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
- apply andb_true_iff in E as [E _]. apply Z.leb_le in E. lia.
- apply (IH a n bot); [intros seg Hin; apply H; right; exact Hin | exact Ha].
Qed.
Lemma JO6SEGS_bot : forall seg, In seg JO6SEGS -> 0x10000 <= Z.of_N (seg_base seg).
Proof. intros seg H. unfold JO6SEGS, Asan.M.loaded_segments, Asan.Asan_loaded_segments in H. cbn [In] in H. repeat (destruct H as [<-|H]; [vm_compute; discriminate|]). destruct H. Qed.
Lemma off_hull_no_segment : forall z, 0 <= z -> (z + 1 <= 0x10000 \/ 0x645000 <= z) -> find_segment JO6SEGS z 1 = None.
Proof.
intros z Hz [H|H].
- apply (find_segment_none_below JO6SEGS z 1 0x10000 JO6SEGS_bot). lia.
- apply (find_segment_none_above JO6SEGS z 1 0x645000 JO6SEGS_top). lia.
Qed.

Section Static.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
#[local] Notation LV := (LV_J E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Instance BANDS : Band := QuLP.Band_RC Q6q3.rc_canary.
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCEIL) (only parsing).

Definition MTBJ : Z := pg E (fst (META_O w)).
Definition FR0J : list (Z * Z) := [(MTBJ, MTBJ + 8192)].
Definition BOTJ : Z := QkIR.BSTAR sp E.
Definition TOPJ : Z := usp - 32.
Definition BAUXJ : Z := usp + 32.
#[local] Notation REJ := (REJ sp E w).

Lemma META_in : In (META_O w) (OBJS_W w).  Proof. destruct w; cbn; tauto. Qed.
Lemma meta_facts : MTBJ mod 4096 = 0 /\ 0 < MTBJ /\ (MTBJ + 8192 <= 0x7fff7000 \/ 0x10007fff8000 <= MTBJ)
/\ (MTBJ + 8192 <= 0x10000 \/ 0x645000 <= MTBJ) /\ MTBJ + 8192 <= atopE E.
Proof.
pose proof ((LA obj_facts) (META_O w) META_in) as (F1 & F2 & _ & F4 & F5 & F6).
assert (SZ : snd (META_O w) = 8192) by (destruct w; reflexivity). rewrite SZ in *. unfold MTBJ, pg. tauto.
Qed.

Lemma Fof_FR0 : forall x, QgTJ.Mq1.Fof LV FR0J x = true ->
MTBJ <= bv_unsigned x < MTBJ + 8192 \/ 0x7fff8000 + MTBJ / 8 <= bv_unsigned x < 0x7fff8000 + (MTBJ + 8191) / 8 + 1.
Proof.
intros x H. unfold QgTJ.Mq1.Fof, FR0J in H. cbn [existsb] in H. rewrite orb_false_r in H. unfold QgTJ.Mq1.fr_in in H.
apply orb_true_iff in H as [H|H]; unfold zin in H; cbn [fst snd] in H; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2.
- left. lia.
- right. unfold sh_iv, shz in H1, H2. cbn [fst snd] in H1, H2. change (lv_shoff LV) with 0x7fff8000 in H1, H2.
replace (MTBJ + 8192 - 1) with (MTBJ + 8191) in H2 by lia. lia.
Qed.

Lemma Fof_FR0_facts : forall x, QgTJ.Mq1.Fof LV FR0J x = true ->
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x) /\ bv_unsigned x < atopE E.
Proof.
intros x H. destruct meta_facts as (M1 & M2 & M3 & M4 & M5). pose proof (MA main_atop_bounds) as AB.
destruct (Fof_FR0 x H) as [Hx|Hx]; [split; lia|].
split; [right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

Theorem HS_main : QU91.Mq0.handoff_static Qwm6.Mq0.A4L (LA_main w E) LV (PERM0_J E w) QVyC.TMAX_J QVyC.NMAX_J REJ FR0J.
Proof.
destruct meta_facts as (M1 & M2 & M3 & M4 & M5). pose proof (MA main_atop_bounds) as AB.
unfold QU91.Mq0.handoff_static.
split; [exact (MA ll_ok_main_J)|].
split; [exact JO6SEGS_wx_nowrap|].
split; [exact (L_main_jo6_segs_in_base (atopE E))|].
split; [exact (L_main_jo6_shoff_ok (atopE E))|].
split; [exact (L_main_jo6_bands_excl (atopE E))|].
split; [exact (L_main_jo6_bands_cover (atopE E))|].
split. { intros iv Hiv. cbn in Hiv. destruct Hiv as [<-|[<-|[]]]; cbn [fst snd]; lia. }
split. { intros y Hy. apply JO6SEGS_low. unfold QzgH.kLowEnd in *. lia. }
split.
{
apply Forall_cons; [|apply Forall_nil]. unfold QgTJ.Mq1.fr_ok. cbn [fst snd].
split; [lia|]. split; [unfold QzgH.kLowEnd, QzgH.KHI, Qqcs.Mq0.kHighMemBeg in *; lia|].
exists (wiv2z (obj_e E (META_O w))).
pose proof ((MA u_obj_base) _ META_in) as UB. pose proof ((MA u_obj_len) _ META_in) as UL.
assert (SZ : snd (META_O w) = 8192) by (destruct w; reflexivity).
split; [exact (MV4 meta_perm)|]. unfold wiv2z. rewrite UB, UL, SZ. cbn [fst snd]. fold (pg E (fst (META_O w))). fold MTBJ.
split; [lia|]. split; [lia|].
pose proof (LA sb_facts) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10). destruct (MA sb_layout) as (_ & _ & S11).
pose proof ((LA obj_disj) (META_O w) _ META_in (PRES_O_in w) ltac:(destruct w; discriminate)) as D1.
pose proof ((LA obj_disj) (META_O w) _ META_in (PARR_O_in w) ltac:(destruct w; discriminate)) as D2.
rewrite SZ in D1, D2. cbn [fst snd] in D1, D2. fold (pg E (fst (META_O w))) in D1, D2. fold MTBJ in D1, D2.
change (Q6sh.al_space_beg (LA_main w E)) with (SB E). change (Q6sh.al_ptrarr (LA_main w E)) with (PARR E).
unfold QzgH.zdisj. cbn [fst snd]. unfold PRES, PARR in *. split; lia. }
split. { intros a Ha. destruct (Fof_FR0_facts a Ha) as [OH _]. apply off_hull_no_segment; [pose proof (u64_range a); lia| exact OH]. }
split. { intros x Hx. destruct (Fof_FR0_facts x Hx) as [_ LT]. unfold Q6q3.alloc_ceiling. rewrite HCEIL. exact LT. }
reflexivity.
Qed.

Lemma r1_main : exists iv, In iv (lv_base LV) /\ fst iv <= QCcH.hl_img_lo (QZsi.hla_base Qwm6.Mq0.A4L) /\ QCcH.hl_img_hi (QZsi.hla_base Qwm6.Mq0.A4L) <= snd iv.
Proof. exists (0x10000, 0x645000). split; [cbn; tauto|]. cbn. lia. Qed.
Lemma r2_main : exists iv, In iv (lv_base LV) /\ fst iv <= BOTJ /\ 2^47 <= snd iv.
Proof. exists (atopE E, 0x800000000000). split; [cbn; tauto|]. pose proof (MV4 QkIR.BSTAR_facts) as ((B1 & _) & _). unfold BOTJ. cbn [fst snd]. lia. Qed.
Lemma r3_main : forall x, QgTJ.Mq1.Fof LV FR0J x = true ->
~ (QYZ0.mg_data_lo QrOY.Mq0.MJ.S_AJ <= bv_unsigned x < QYZ0.mg_img_hi QrOY.Mq0.MJ.S_AJ).
Proof.
intros x Hx [H1 H2]. destruct (Fof_FR0_facts x Hx) as [OH _].
cbn [QrOY.Mq0.MJ.S_AJ QYZ0.mg_data_lo QYZ0.mg_img_hi] in H1, H2.
unfold QrOY.Mq0.MJ.AJ_DATA_LO, QrOY.Mq0.MJ.AJ_IMG_HI in H1, H2. lia.
Qed.
Lemma r4_main : Q6q3.alloc_ceiling <= BOTJ /\ BOTJ mod 8 = 0 /\ BOTJ <= TOPJ.
Proof.
pose proof (MV4 QkIR.BSTAR_facts) as ((B1 & B2) & B3 & _).
unfold Q6q3.alloc_ceiling, BOTJ, TOPJ. rewrite HCEIL. pose proof (MV4 atop_val) as AV.
split; [lia|]. split; [exact B3|lia].
Qed.
Lemma botj_cap : BOTJ <= 0x7fffff800000 /\ atopE E <= BOTJ <= atopE E + 3935.
Proof. pose proof (MV4 QkIR.BSTAR_facts) as (B12 & _ & B4 & _). unfold BOTJ. split; [exact B4| exact B12]. Qed.
Lemma r5_main : Q6q3.alloc_ceiling < TOPJ /\ TOPJ <= 2^47.
Proof.
unfold Q6q3.alloc_ceiling, TOPJ. rewrite HCEIL. pose proof (MV4 atop_val) as AV. destruct Hsp as (S1 & S2 & _). unfold sp_window_hi in S2. lia.
Qed.
Lemma r6_main : TOPJ + 64 <= BAUXJ.
Proof. unfold TOPJ, BAUXJ. lia. Qed.
Lemma r7_main : TOPJ + 64 <= QCrt.ae_stack_top REJ + 4096.
Proof. pose proof (LA st_main_facts) as (T1 & _). unfold TOPJ. cbn [QCrt.ae_stack_top Qx84.REJ]. lia. Qed.
End Static.
End Mq0.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QBzu QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QNDM Q7DP QHqi Qi08 QZzg Q61C QWRO QFQR QWwJ Q4I1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5 Q2ui.

Import QlES.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QHqi Qb5q.Mq2.

Import QWwJ Q4I1 Qx84.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma find_segment_none_below : forall segs a n bot,
(forall seg, In seg segs -> bot <= Z.of_N (seg_base seg)) -> a < bot -> find_segment segs a n = None.
Proof.
induction segs as [|s rest IH]; intros a n bot H Ha; [reflexivity|]. cbn [find_segment].
pose proof (H s (or_introl eq_refl)) as Hs.
destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
- apply andb_true_iff in E as [E _]. apply Z.leb_le in E. lia.
- apply (IH a n bot); [intros seg Hin; apply H; right; exact Hin | exact Ha].
Qed.
Lemma JOB6SEGS_bot : forall seg, In seg JOB6SEGS -> 0x10000 <= Z.of_N (seg_base seg).
Proof. intros seg H. unfold JOB6SEGS, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments in H. cbn [In] in H. repeat (destruct H as [<-|H]; [vm_compute; discriminate|]). destruct H. Qed.
Lemma off_hull_no_segment : forall z, 0 <= z -> (z + 1 <= 0x10000 \/ 0x647000 <= z) -> find_segment JOB6SEGS z 1 = None.
Proof.
intros z Hz [H|H].
- apply (find_segment_none_below JOB6SEGS z 1 0x10000 JOB6SEGS_bot). lia.
- apply (find_segment_none_above JOB6SEGS z 1 0x647000 JOB6SEGS_top). lia.
Qed.

Section Static.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
#[local] Notation LV := (LV_J E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Instance BANDS : Band := QBzu.Band_RC Q6q3.rc_canary.
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCEIL) (only parsing).

Definition MTBJ : Z := pg E (fst (META_O w)).
Definition FR0J : list (Z * Z) := [(MTBJ, MTBJ + 8192)].
Definition BOTJ : Z := QkIR.Mq0.BSTAR sp E.
Definition TOPJ : Z := usp - 32.
Definition BAUXJ : Z := usp + 32.
#[local] Notation REJ := (REJ sp E w).

Lemma META_in : In (META_O w) (OBJS_W w).  Proof. destruct w; cbn; tauto. Qed.
Lemma meta_facts : MTBJ mod 4096 = 0 /\ 0 < MTBJ /\ (MTBJ + 8192 <= 0x7fff7000 \/ 0x10007fff8000 <= MTBJ)
/\ (MTBJ + 8192 <= 0x10000 \/ 0x647000 <= MTBJ) /\ MTBJ + 8192 <= atopE E.
Proof.
pose proof ((LA obj_facts) (META_O w) META_in) as (F1 & F2 & _ & F4 & F5 & F6).
assert (SZ : snd (META_O w) = 8192) by (destruct w; reflexivity). rewrite SZ in *. unfold MTBJ, pg. tauto.
Qed.

Lemma Fof_FR0 : forall x, QgTJ.Mq1.Fof LV FR0J x = true ->
MTBJ <= bv_unsigned x < MTBJ + 8192 \/ 0x7fff8000 + MTBJ / 8 <= bv_unsigned x < 0x7fff8000 + (MTBJ + 8191) / 8 + 1.
Proof.
intros x H. unfold QgTJ.Mq1.Fof, FR0J in H. cbn [existsb] in H. rewrite orb_false_r in H. unfold QgTJ.Mq1.fr_in in H.
apply orb_true_iff in H as [H|H]; unfold zin in H; cbn [fst snd] in H; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2.
- left. lia.
- right. unfold sh_iv, shz in H1, H2. cbn [fst snd] in H1, H2. change (lv_shoff LV) with 0x7fff8000 in H1, H2.
replace (MTBJ + 8192 - 1) with (MTBJ + 8191) in H2 by lia. lia.
Qed.

Lemma Fof_FR0_facts : forall x, QgTJ.Mq1.Fof LV FR0J x = true ->
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x) /\ bv_unsigned x < atopE E.
Proof.
intros x H. destruct meta_facts as (M1 & M2 & M3 & M4 & M5). pose proof (MA main_atop_bounds) as AB.
destruct (Fof_FR0 x H) as [Hx|Hx]; [split; lia|].
split; [right; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

Theorem HS_main : QU91.Mq0.handoff_static Qwm6.Mq4.A4L (LA_main w E) LV (PERM0_J E w) Qi08.TMAX_J Qi08.NMAX_J REJ FR0J.
Proof.
destruct meta_facts as (M1 & M2 & M3 & M4 & M5). pose proof (MA main_atop_bounds) as AB.
unfold QU91.Mq0.handoff_static.
split; [exact (MA ll_ok_main_J)|].
split; [exact JOB6SEGS_wx_nowrap|].
split; [exact (L_main_job6_segs_in_base (atopE E))|].
split; [exact (L_main_job6_shoff_ok (atopE E))|].
split; [exact (L_main_job6_bands_excl (atopE E))|].
split; [exact (L_main_job6_bands_cover (atopE E))|].
split. { intros iv Hiv. cbn in Hiv. destruct Hiv as [<-|[<-|[]]]; cbn [fst snd]; lia. }
split. { intros y Hy. apply JOB6SEGS_low. unfold QzgH.kLowEnd in *. lia. }
split.
{
apply Forall_cons; [|apply Forall_nil]. unfold QgTJ.Mq1.fr_ok. cbn [fst snd].
split; [lia|]. split; [unfold QzgH.kLowEnd, QzgH.KHI, Qqcs.Mq0.kHighMemBeg in *; lia|].
exists (wiv2z (obj_e E (META_O w))).
pose proof ((MA u_obj_base) _ META_in) as UB. pose proof ((MA u_obj_len) _ META_in) as UL.
assert (SZ : snd (META_O w) = 8192) by (destruct w; reflexivity).
split; [exact (MV4 meta_perm)|]. unfold wiv2z. rewrite UB, UL, SZ. cbn [fst snd]. fold (pg E (fst (META_O w))). fold MTBJ.
split; [lia|]. split; [lia|].
pose proof (LA sb_facts) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10). destruct (MA sb_layout) as (_ & _ & S11).
pose proof ((LA obj_disj) (META_O w) _ META_in (PRES_O_in w) ltac:(destruct w; discriminate)) as D1.
pose proof ((LA obj_disj) (META_O w) _ META_in (PARR_O_in w) ltac:(destruct w; discriminate)) as D2.
rewrite SZ in D1, D2. cbn [fst snd] in D1, D2. fold (pg E (fst (META_O w))) in D1, D2. fold MTBJ in D1, D2.
change (Q6sh.al_space_beg (LA_main w E)) with (SB E). change (Q6sh.al_ptrarr (LA_main w E)) with (PARR E).
unfold QzgH.zdisj. cbn [fst snd]. unfold PRES, PARR in *. split; lia. }
split. { intros a Ha. destruct (Fof_FR0_facts a Ha) as [OH _]. apply off_hull_no_segment; [pose proof (u64_range a); lia| exact OH]. }
split. { intros x Hx. destruct (Fof_FR0_facts x Hx) as [_ LT]. unfold Q6q3.alloc_ceiling. rewrite HCEIL. exact LT. }
reflexivity.
Qed.

Lemma r1_main : exists iv, In iv (lv_base LV) /\ fst iv <= QCcH.hl_img_lo (QZsi.hla_base Qwm6.Mq4.A4L) /\ QCcH.hl_img_hi (QZsi.hla_base Qwm6.Mq4.A4L) <= snd iv.
Proof. exists (0x10000, 0x647000). split; [cbn; tauto|]. cbn. lia. Qed.
Lemma r2_main : exists iv, In iv (lv_base LV) /\ fst iv <= BOTJ /\ 2^47 <= snd iv.
Proof. exists (atopE E, 0x800000000000). split; [cbn; tauto|]. pose proof (MV4 QkIR.Mq0.BSTAR_facts) as ((B1 & _) & _). unfold BOTJ. cbn [fst snd]. lia. Qed.
Lemma r3_main : forall x, QgTJ.Mq1.Fof LV FR0J x = true ->
~ (QYZ0.mg_data_lo QrOY.MJ.S_AJU <= bv_unsigned x < QYZ0.mg_img_hi QrOY.MJ.S_AJU).
Proof.
intros x Hx [H1 H2]. destruct (Fof_FR0_facts x Hx) as [OH _].
cbn [QrOY.MJ.S_AJU QYZ0.mg_data_lo QYZ0.mg_img_hi] in H1, H2.
unfold QrOY.MJ.AJU_DATA_LO, QrOY.MJ.AJU_IMG_HI in H1, H2. lia.
Qed.
Lemma r4_main : Q6q3.alloc_ceiling <= BOTJ /\ BOTJ mod 8 = 0 /\ BOTJ <= TOPJ.
Proof.
pose proof (MV4 QkIR.Mq0.BSTAR_facts) as ((B1 & B2) & B3 & _).
unfold Q6q3.alloc_ceiling, BOTJ, TOPJ. rewrite HCEIL. pose proof (MV4 atop_val) as AV.
split; [lia|]. split; [exact B3|lia].
Qed.
Lemma botj_cap : BOTJ <= 0x7fffff800000 /\ atopE E <= BOTJ <= atopE E + 3935.
Proof. pose proof (MV4 QkIR.Mq0.BSTAR_facts) as (B12 & _ & B4 & _). unfold BOTJ. split; [exact B4| exact B12]. Qed.
Lemma r5_main : Q6q3.alloc_ceiling < TOPJ /\ TOPJ <= 2^47.
Proof.
unfold Q6q3.alloc_ceiling, TOPJ. rewrite HCEIL. pose proof (MV4 atop_val) as AV. destruct Hsp as (S1 & S2 & _). unfold sp_window_hi in S2. lia.
Qed.
Lemma r6_main : TOPJ + 64 <= BAUXJ.
Proof. unfold TOPJ, BAUXJ. lia. Qed.
Lemma r7_main : TOPJ + 64 <= QCrt.ae_stack_top REJ + 4096.
Proof. pose proof (LA st_main_facts) as (T1 & _). unfold TOPJ. cbn [QCrt.ae_stack_top Qx84.Mq0.REJ]. lia. Qed.
End Static.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcGV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtIP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuLP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition gtab (g0 : Z) : list byte := map (fun i => Z_to_bv 8 (QZsi.img_shadow_val QGcC.Mq0.tokA_reg_globals (g0 + Z.of_nat i))) (seq 0 8).
Lemma GTAB1 : gtab 0x46d0 = QXE1.Mq0.GSHW1.  Proof. vm_compute. reflexivity. Qed.
Lemma GTAB2 : gtab 0x46e0 = QXE1.Mq0.GSHW2.  Proof. vm_compute. reflexivity. Qed.

Lemma bytes_at_octet : forall (m : word -> option byte) (g0 : Z),
0 <= g0 -> g0 + 0x7fff8000 + 8 <= 2^64 ->
(forall i, (i < 8)%nat -> QCUT.bytes_at QvG1.asegs m (g0 + Z.of_nat i + 0x7fff8000) [Z_to_bv 8 (QZsi.img_shadow_val QGcC.Mq0.tokA_reg_globals (g0 + Z.of_nat i))]) ->
QCUT.bytes_at QvG1.asegs m (g0 + 0x7fff8000) (gtab g0).
Proof.
intros m g0 H0 H1 H. split; [lia|]. split; [unfold gtab; rewrite length_map, length_seq; lia|].
intros i Hi. unfold gtab in Hi. rewrite length_map, length_seq in Hi.
destruct (H i Hi) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in HB. rewrite Z.add_0_r in HB.
replace (g0 + 0x7fff8000 + Z.of_nat i) with (g0 + Z.of_nat i + 0x7fff8000) by lia. rewrite HB.
unfold gtab. rewrite nth_error_map, nth_error_seq. replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add]. reflexivity.
Qed.

Section Pfrt.
Context {RC__ : Q6q3.RunConsts}.
Variable LA : Q6sh.ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : QCrt.aentry.
Variable FR0 : list (Z * Z).
Variables BAUX BOTJ TOPJ : Z.
Variable HS : QU91.Mq0.handoff_static Qwm6.Mq0.A4L LA LV PERM0 TMAX NMAX RE FR0.
Hypothesis RUN_botj : Q6q3.alloc_ceiling <= BOTJ.
Hypothesis BOT_cap : BOTJ <= 0x7fffff800000.

Notation BANDP := (QJny.Mq0.BANDP BOTJ RUN_botj BOT_cap).
Notation DLj := (@QuLP.DL_AR (QuLP.Band_RC Q6q3.rc_canary)).
Notation DCoj := (QuLP.DCo_jo Q6q3.rc_canary LV).
Notation H63 := (QU91.HEAPA63 Qwm6.Mq0.A4L LV PERM0 TMAX NMAX DLj RE DCoj FR0 QrOY.Mq0.MJ.S_AJ BAUX (QPUe.STAT_A Qwm6.Mq0.A4L BOTJ TOPJ QrOY.Mq0.jo_STATC)).

Theorem ishG_of_heapA63 : forall A LB LM FR B m c, H63 A LB LM FR B m c -> @QXE1.Mq0.ISH BANDP m.
Proof.
intros A LB LM FR B m c HP.
apply QXE1.Mq0.ISH_of_AR; [exact (QJny.Mq0.ish_of_heapA63 LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS RUN_botj BOT_cap A LB LM FR B m c HP)|].
destruct HP as ((g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & KL & HP) & _).
do 14 (destruct HP as [_ HP]). destruct HP as (SC & SS & SI).
change (QtIP.JH.hl_sb Qwm6.Mq0.A4L) with 0x7fff8000 in SI.
change (QtIP.JH.hl_reg_globals Qwm6.Mq0.A4L) with QGcC.Mq0.tokA_reg_globals in SI.
change (QtIP.HI.hl_img_lo (QtIP.JH.hla_base Qwm6.Mq0.A4L)) with 0x10000 in SI. change (QtIP.HI.hl_img_hi (QtIP.JH.hla_base Qwm6.Mq0.A4L)) with 0x645000 in SI.
unfold QXE1.Mq0.gsh. rewrite <- GTAB1, <- GTAB2. split.
- change 0x7fffc6d0 with (0x46d0 + 0x7fff8000). apply bytes_at_octet; [lia | lia |]. intros i Hi. apply SI; lia.
- change 0x7fffc6e0 with (0x46e0 + 0x7fff8000). apply bytes_at_octet; [lia | lia |]. intros i Hi. apply SI; lia.
Qed.
End Pfrt.
