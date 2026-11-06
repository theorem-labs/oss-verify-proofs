(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QbrW Q6q3 QWxq_c1 QCcH QZsi QYZ0 Qwm6 QW7x.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi QdTb Q1lV Qc27 Qcrs QUcd QCUT QMow QHig QwAs Qc6I QJFf QVsB Qsn5 Qknc QBrp Q2ui Q1KO Q6sh QzgH QNqr QgTJ QCrt QRGF QcGV QNLn QtIP QU91 QuLP QZrD QPUe QCVR QdSl QM2q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import QQIi QdTb Q1lV.
Import Qc27 Qcrs QUcd QCUT QMow QHig QwAs.Mq0 Qc6I QJFf QVsB Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import Q6sh QzgH.
Import QNqr QgTJ.Mq1 QCrt.
Import QRGF QcGV QNLn.Mq0 QtIP QU91.Mq0 QU91 QuLP QZrD QPUe.

Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module AY := Qwm6.Mq0.
Module MJ := QdSl.Mq0.
Module RG := QW7x.Mq0.

Section Jo.
Context {RC__ : RC.RunConsts}.
Notation L := AY.A4L.
Notation HL := (JH.hla_base L).
Notation segs := (HI.hl_segs HL).
Notation S := MJ.S_AJ.
Notation DL := (@DL_AR (Band_RC RC.rc_canary)).

Lemma jo_L_malloc2 : HI.hl_malloc2 HL = MGI.mg_malloc S. Proof. reflexivity. Qed.
Lemma jo_L_free2 : HI.hl_free2 HL = MGI.mg_free S. Proof. reflexivity. Qed.
Lemma jo_L_tp2 : HI.hl_tp HL = MGI.mg_tp S. Proof. reflexivity. Qed.
Lemma jo_L_stack2 : MGI.mg_stack S <= HI.hl_stack HL. Proof. cbn. lia. Qed.
Lemma jo_IMG_low : MGI.mg_img_hi S <= kLowEnd. Proof. cbn. unfold MJ.AJ_IMG_HI, kLowEnd. lia. Qed.
Lemma jo_L_img : HI.hl_img_lo HL = dl_img_lo DL /\ HI.hl_img_hi HL = dl_img_hi DL. Proof. split; reflexivity. Qed.
Lemma jo_L_errno : dl_errno DL = HI.hl_tp HL - 164. Proof. reflexivity. Qed.
Lemma jo_L_malloc : HI.hl_malloc HL = dl_malloc DL. Proof. reflexivity. Qed.
Lemma jo_L_free : HI.hl_free HL = dl_free DL. Proof. reflexivity. Qed.
Lemma jo_L_calloc : HI.hl_calloc HL = dl_calloc DL. Proof. reflexivity. Qed.
Lemma jo_L_tp : HI.hl_tp HL = dl_tp DL. Proof. reflexivity. Qed.
Lemma jo_L_gp : JH.hl_gp L = dl_gp DL. Proof. reflexivity. Qed.

Lemma jo_L_stack : dl_malloc_stack DL <= JH.hl_stack_A L /\ dl_free_stack DL <= JH.hl_stack_A L /\ dl_calloc_stack DL <= JH.hl_stack_A L.
Proof. cbn. lia. Qed.

Lemma jo_L_stackA : 64 <= JH.hl_stack_A L. Proof. cbn. lia. Qed.

Lemma jo_L_dpn : 0 <= dl_depot_n DL /\ dl_depot_n DL + 4 <= RC.alloc_ceiling.
Proof. pose proof (@RC.alloc_ceiling_range RC__). cbn. unfold RA.DP_N. lia. Qed.
Lemma jo_L_dpn_hull : dl_img_lo DL <= dl_depot_n DL /\ dl_depot_n DL + 4 <= dl_img_hi DL.
Proof. cbn. unfold RA.DP_N. lia. Qed.
Lemma jo_L_sb : JH.hl_sb L = kShadowOffset. Proof. reflexivity. Qed.
Lemma jo_L_hull_eq : HI.hl_img_lo HL = MGI.mg_img_lo S /\ HI.hl_img_hi HL = MGI.mg_img_hi S. Proof. split; reflexivity. Qed.

Lemma jo_seg_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x645000 <= z) -> find_segment segs z n = None.
Proof. exact RG.ref_find_segment_none. Qed.

Lemma jo_IMG_seg_G : forall z, z + 1 <= MGI.mg_img_lo S \/ MGI.mg_img_hi S <= z -> find_segment segs z 1 = None.
Proof. intros z Hz. apply jo_seg_none; [lia|]. cbn in Hz. unfold MJ.AJ_IMG_HI in Hz. lia. Qed.

Lemma jo_seg_some : forall y, find_segment segs y 1 <> None -> 0x10000 <= y < 0x645000.
Proof.
intros y Hy. destruct (Z.lt_ge_cases y 0x10000) as [H1|H1]; [exfalso; apply Hy; apply jo_seg_none; lia|].
destruct (Z.lt_ge_cases y 0x645000) as [H2|H2]; [lia| exfalso; apply Hy; apply jo_seg_none; lia].
Qed.

Lemma jo_IMG_hull : HI.hl_img_lo HL <= MGI.mg_data_lo S /\ MGI.mg_img_hi S <= HI.hl_img_hi HL /\
forall y, find_segment segs y 1 <> None -> HI.hl_img_lo HL <= y < HI.hl_img_hi HL.
Proof. cbn. unfold MJ.AJ_DATA_LO, MJ.AJ_IMG_HI. split; [lia|]. split; [lia|]. exact jo_seg_some. Qed.

Lemma jo_seg_ro : forall z, 0x10000 <= z < 0xe2000 -> exists seg, find_segment segs z 1 = Some seg /\ seg_writable seg = false.
Proof.
intros z Hz. cbn [HI.hl_segs JH.hla_base AY.A4L AY.A4H].
unfold Q7UD.asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Asan.Asan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_000)) with 0x2d000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_001)) with 0x3d000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_001)) with 0xa5000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + 1) (0x10000 + 0x2d000)); cbn [andb]; try lia.
- eexists. split; [reflexivity| vm_compute; reflexivity].
- destruct (Z.leb_spec0 0x3d000 z); destruct (Z.leb_spec0 (z + 1) (0x3d000 + 0xa5000)); cbn [andb]; try lia.
eexists. split; [reflexivity| vm_compute; reflexivity].
Qed.

Lemma jo_IMG_rw : forall y : word, find_segment segs (bv_unsigned y) 1 <> None -> ro_addr segs y = false ->
MGI.mg_data_lo S <= bv_unsigned y < MGI.mg_img_hi S.
Proof.
intros y Hf Hro. pose proof (jo_seg_some _ Hf) as Hr. cbn [MJ.S_AJ MGI.mg_data_lo MGI.mg_img_hi]. unfold MJ.AJ_DATA_LO, MJ.AJ_IMG_HI.
destruct (Z.lt_ge_cases (bv_unsigned y) 0xe2000) as [Hlt|Hge]; [exfalso| lia].
destruct (jo_seg_ro (bv_unsigned y) ltac:(lia)) as (seg & E & W). unfold ro_addr in Hro. rewrite E, W in Hro. discriminate.
Qed.

Fixpoint img_w_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| Datatypes.S n' => match wview segs (fun _ => None) (wa A) with Some _ => img_w_b (A + 1) n' | None => false end
end.
Lemma img_w_b_sound : forall n A (m : word -> option byte), img_w_b A n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 -> wr_at segs m A (Z.of_nat n).
Proof.
intros n A m Hb HA Hhi. split; [exact HA|]. split; [exact Hhi|]. revert A Hb HA Hhi.
induction n as [|n IH]; intros A Hb HA Hhi i Hi; [lia|]. cbn [img_w_b] in Hb.
destruct (wview segs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite Z.add_0_r. unfold wview in *. destruct (m (wa A)); [discriminate|]. cbn beta in Ew. rewrite Ew. discriminate.
- replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) Hb); lia.
Qed.

Lemma jo_L_rtc : incl (MGI.mg_rtc S) (dl_rtc DL).
Proof. intros c [<-|[<-|[<-|[]]]]; [left| right; left| right; right; left]; reflexivity. Qed.

Lemma jo_IMG_rtc_wr : forall m : word -> option byte, Forall (fun c => wr_at segs m (fst c) (Z.of_nat (length (snd c)))) (MGI.mg_rtc S).
Proof.
intros m. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd];
(apply img_w_b_sound; [vm_compute; reflexivity| vm_compute; discriminate| vm_compute; discriminate]).
Qed.

Lemma jo_wstat : forall a, MGI.in_ivs (MGI.mg_wstat S) a <-> (0x6431e8 <= a < 0x643588 \/ 0x622dbc <= a < 0x622dc0).
Proof.
intros a. unfold MGI.in_ivs, MGI.mg_wstat. cbn [MJ.S_AJ MGI.mg_ctx MGI.mg_tp]. unfold RG.RCTX, RG.RATP. split.
- intros (iv & [<-|[<-|[]]] & Hr); cbn [fst snd] in Hr; lia.
- intros [Hr|Hr]; [exists (0x6431e8, 0x6431e8 + 928)| exists (0x622e60 + -164, 0x622e60 + -164 + 4)]; (split; [cbn; auto| cbn [fst snd]; lia]).
Qed.

Lemma jo_L_static2 : forall a, HI.hl_client_static HL a ->
MGI.mg_data_lo S <= a < MGI.mg_img_hi S /\ ~ MGI.in_ivs (MGI.mg_wstat S) a.
Proof.
intros a Ha. rewrite jo_wstat. cbn [MJ.S_AJ MGI.mg_data_lo MGI.mg_img_hi]. unfold MJ.AJ_DATA_LO, MJ.AJ_IMG_HI.
cbn [HI.hl_client_static JH.hla_base AY.A4L AY.A4H] in Ha. unfold AY.a4_client_static in Ha. lia.
Qed.

Lemma jo_rstat : forall a, mng_static S a <->
(0x6431e8 <= a < 0x643588 \/ 0x6431e0 <= a < 0x6431e4 \/ 0x6446f8 <= a < 0x6446fc \/ 0x6430f3 <= a < 0x6430f4
\/ 0x643120 <= a < 0x643128 \/ 0xe6b80 <= a < 0xe6b88 \/ 0x642ea0 <= a < 0x642ea8).
Proof.
intros a. unfold mng_static, MGI.in_ivs. cbn [MJ.S_AJ MGI.mg_rstat]. unfold MJ.aj_rstat, RG.RCTX, RG.RMLOCK, RG.RVMLOCK, RG.RNEED_LOCKS, RG.RPAGE_SIZE, RG.RGOT_SSP, RG.RSSP_GUARD. split.
- intros (iv & Hin & Hr). cbn [In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
- intros H.
destruct H as [H|[H|[H|[H|[H|[H|H]]]]]];
[exists (0x6431e8, 0x6431e8 + 928)| exists (0x6431e0, 0x6431e0 + 4)| exists (0x6446f8, 0x6446f8 + 4)| exists (0x6430f3, 0x6430f3 + 1)
| exists (0x643120, 0x643120 + 8)| exists (0xe6b80, 0xe6b80 + 8)| exists (0x642ea0, 0x642ea0 + 8)];
(split; [cbn [In]; tauto| cbn [fst snd]; lia]).
Qed.

Lemma jo_in_rtc : forall a, (0x643120 <= a < 0x643128 \/ 0xe6b80 <= a < 0xe6b88 \/ 0x642ea0 <= a < 0x642ea8) -> in_rtc S a.
Proof.
intros a H. unfold in_rtc. cbn [MJ.S_AJ MGI.mg_rtc]. unfold RG.RPAGE_SIZE, RG.RGOT_SSP, RG.RSSP_GUARD.
destruct H as [H|[H|H]]; [eexists; split; [left; reflexivity|]| eexists; split; [right; left; reflexivity|]| eexists; split; [right; right; left; reflexivity|]];
cbn [fst snd]; change (Z.of_nat (length _)) with 8; lia.
Qed.

Lemma jo_OBL_R1P : forall a, (mng_static S a /\ ~ in_rtc S a) \/ fst (MGI.mg_ctx S) <= a < snd (MGI.mg_ctx S) -> dl_client_data DL a.
Proof.
intros a H. unfold DL_AR; cbn [dl_client_data]; unfold RA.a_client_data.
destruct H as [[Hs Hn]|Hc].
- apply jo_rstat in Hs. assert (Hn' : ~ (0x643120 <= a < 0x643128 \/ 0xe6b80 <= a < 0xe6b88 \/ 0x642ea0 <= a < 0x642ea8)) by (intros X; exact (Hn (jo_in_rtc a X))). lia.
- cbn [MJ.S_AJ MGI.mg_ctx fst snd] in Hc. unfold RG.RCTX in Hc. lia.
Qed.

Definition jo_SIVS : list (Z * Z) :=
[(0xea500, 0xec420); (0xec448, 0xec498); (0x181998, 0x1819a8); (0x612140, 0x622dbc); (0x622dc0, 0x622e08); (0x622e10, 0x622e58); (0x622e98, 0x642ea0);
(0x642ea8, 0x643120); (0x643128, 0x644280)].
Lemma jo_L_sivs_data : forall iv a, In iv jo_SIVS -> fst iv <= a < snd iv -> dl_client_data DL a.
Proof.
intros iv a Hin Hr. unfold DL_AR; cbn [dl_client_data]; unfold RA.a_client_data. unfold jo_SIVS in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.

Lemma jo_L_rstat_priv : forall a, mng_static S a -> ~ HI.hl_client_static HL a /\ ~ HI.hl_scratch HL a.
Proof.
intros a Hs. apply jo_rstat in Hs. cbn [HI.hl_client_static HI.hl_scratch JH.hla_base AY.A4L AY.A4H]. unfold AY.a4_client_static, AY.A_TP. lia.
Qed.

Lemma jo_L_scratch_data : forall a, HI.hl_scratch HL a -> MGI.mg_data_lo S <= a < MGI.mg_img_hi S.
Proof.
intros a Hs. cbn [HI.hl_scratch JH.hla_base AY.A4L AY.A4H] in Hs. unfold AY.A_TP in Hs.
cbn [MJ.S_AJ MGI.mg_data_lo MGI.mg_img_hi]. unfold MJ.AJ_DATA_LO, MJ.AJ_IMG_HI. lia.
Qed.

Lemma jo_L_scratch : forall a, HI.hl_scratch HL a -> HI.hl_tp HL - 164 <= a < HI.hl_tp HL - 160.
Proof. intros a Hs. exact Hs. Qed.

Fixpoint img_r_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| Datatypes.S n' => match seg_rom segs (wa A) with Some _ => img_r_b (A + 1) n' | None => false end
end.
Lemma img_r_b_sound : forall n A (m : word -> option byte), img_r_b A n = true ->
exists bs, length bs = n /\ forall i, (i < n)%nat -> mrd segs m (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
induction n as [|n IH]; intros A m Hb; [exists []; split; [reflexivity| intros i Hi; lia]|].
cbn [img_r_b] in Hb. destruct (seg_rom segs (wa A)) as [b0|] eqn:Er; [|discriminate].
destruct (IH (A + 1) m Hb) as (bs & Hl & Hbs).
exists ((match m (wa A) with Some b => b | None => b0 end) :: bs). split; [cbn [length]; rewrite Hl; reflexivity|].
intros [|i] Hi; cbn [nth_error].
- rewrite Z.add_0_r. unfold mrd. destruct (m (wa A)); [reflexivity| exact Er].
- replace (A + Z.of_nat (Datatypes.S i)) with (A + 1 + Z.of_nat i) by lia. apply Hbs. lia.
Qed.

Lemma jo_IMG_errno_any : forall m : word -> option byte, exists v : word, rw_cells segs m (HI.hl_tp HL - 164) [C4 v].
Proof.
intros m. cbn [HI.hl_tp JH.hla_base AY.A4L AY.A4H]. unfold AY.A_TP.
destruct (img_r_b_sound 4 (0x622e60 - 164) m ltac:(vm_compute; reflexivity)) as (bs & Hl & Hbs).
exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [split; [cbn; auto|]|].
- cbn [cells_bytes cbytes]. rewrite app_nil_r, (le4_of_bytes bs Hl). split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. apply Hbs. lia.
- cbn [cells_size csize Nat.add]. apply (img_w_b_sound 4); [vm_compute; reflexivity| lia| lia].
Qed.

Definition jo_STATC : list (Z * list byte) :=
[ (0x6446f8, le4 (Z_to_bv 64 0));
(HI.hl_tp HL - 16, le8 RC.rc_canary);
(HI.hl_libc HL + 3, [Z_to_bv 8 0]) ].

Definition byte_eqb (a b : byte) : bool := Z.eqb (bv_unsigned a) (bv_unsigned b).
Fixpoint bytes_eqb (x y : list byte) : bool :=
match x, y with [], [] => true | a :: x', b :: y' => byte_eqb a b && bytes_eqb x' y' | _, _ => false end.
Lemma bytes_eqb_eq : forall x y, bytes_eqb x y = true -> x = y.
Proof.
induction x as [|a x IH]; intros [|b y] H; cbn [bytes_eqb] in H; try discriminate; [reflexivity|].
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b. f_equal. exact (IH y H2).
Qed.
Definition cell_mem (c : Z * list byte) (l : list (Z * list byte)) : bool :=
existsb (fun d => Z.eqb (fst c) (fst d) && bytes_eqb (snd c) (snd d)) l.
Lemma cell_mem_In : forall c l, cell_mem c l = true -> In c l.
Proof.
intros [a x] l H. unfold cell_mem in H. apply existsb_exists in H as ([b y] & Hin & E). cbn [fst snd] in E.
apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. apply bytes_eqb_eq in E2. subst b y. exact Hin.
Qed.

Lemma jo_L_rtc_all : forall c, In c (JH.hl_rt_consts L) -> In c (dl_rtc DL) \/ In c jo_STATC.
Proof.
assert (HF : forallb (fun c => cell_mem c (skipn 3 (@rtc_AR (Band_RC RC.rc_canary))) || Z.eqb (fst c) 0x6446f8) (JH.hl_rt_consts L) = true) by (vm_compute; reflexivity).
intros c Hc. rewrite forallb_forall in HF. specialize (HF c Hc). apply orb_true_iff in HF as [HF|HF].
- left. unfold DL_AR; cbn [dl_rtc]. apply cell_mem_In in HF. clear - HF. unfold rtc_AR in *. cbn [skipn] in HF. right; right; right. exact HF.
- right. apply Z.eqb_eq in HF. cbn [JH.hl_rt_consts AY.A4L] in Hc. unfold AY.a4_rt_consts in Hc. cbn [In] in Hc.
repeat (destruct Hc as [<-|Hc]; [first [left; reflexivity | cbn [fst] in HF; discriminate HF]|]). destruct Hc.
Qed.

Lemma jo_L_sb_cells :
In (JH.hl_got_sb L, le8 (Z_to_bv 64 (JH.hl_sb_cell L))) (dl_rtc DL) /\ In (JH.hl_sb_cell L, le8 (Z_to_bv 64 (JH.hl_sb L))) (dl_rtc DL) /\
In (JH.hl_got_uar L, le8 (Z_to_bv 64 (JH.hl_uar_cell L))) (dl_rtc DL) /\ In (JH.hl_uar_cell L, le4 (Z_to_bv 64 1)) (dl_rtc DL).
Proof.
unfold DL_AR; cbn [dl_rtc JH.hl_got_sb JH.hl_sb_cell JH.hl_sb JH.hl_got_uar JH.hl_uar_cell AY.A4L]. unfold rtc_AR. cbn [In].
repeat split; repeat (first [left; reflexivity | right]).
Qed.

Lemma jo_L_statc_data : forall c x, In c jo_STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) -> dl_client_data DL x.
Proof.
intros c x Hc Hx. unfold DL_AR; cbn [dl_client_data]; unfold RA.a_client_data. unfold jo_STATC in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; cbn [HI.hl_tp HI.hl_libc JH.hla_base AY.A4L AY.A4H] in Hx; unfold AY.A_TP in Hx;
[change (Z.of_nat (length _)) with 4 in Hx| change (Z.of_nat (length _)) with 8 in Hx| change (Z.of_nat (length _)) with 1 in Hx]; lia.
Qed.
Lemma jo_L_statc_range : forall c x, In c jo_STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) -> 0 <= x < 2^64.
Proof.
intros c x Hc Hx. unfold jo_STATC in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; cbn [HI.hl_tp HI.hl_libc JH.hla_base AY.A4L AY.A4H] in Hx; unfold AY.A_TP in Hx;
[change (Z.of_nat (length _)) with 4 in Hx| change (Z.of_nat (length _)) with 8 in Hx| change (Z.of_nat (length _)) with 1 in Hx]; lia.
Qed.
Lemma jo_L_imgsh_data : forall g, HI.hl_img_lo HL <= 8 * g -> 8 * g + 8 <= HI.hl_img_hi HL -> dl_client_data DL (g + JH.hl_sb L).
Proof.
intros g G1 G2. cbn [HI.hl_img_lo HI.hl_img_hi JH.hl_sb JH.hla_base AY.A4L AY.A4H] in *. unfold AY.A_SB.
unfold DL_AR; cbn [dl_client_data]; unfold RA.a_client_data. lia.
Qed.
Lemma jo_L_img_range : 0 <= HI.hl_img_lo HL /\ HI.hl_img_hi HL <= 2^47. Proof. cbn. lia. Qed.
Lemma jo_L_can_got : In (HI.hl_got_guard HL, le8 (Z_to_bv 64 (HI.hl_guard HL))) (dl_rtc DL). Proof. right; left; reflexivity. Qed.
Lemma jo_L_can_guard : In (HI.hl_guard HL, le8 RC.rc_canary) (dl_rtc DL). Proof. right; right; left; reflexivity. Qed.
Lemma jo_L_can_copy : In (HI.hl_tp HL - 16, le8 RC.rc_canary) jo_STATC. Proof. right; left; reflexivity. Qed.
Lemma jo_L_need_locks : In (HI.hl_libc HL + 3, [Z_to_bv 8 0]) jo_STATC. Proof. right; right; left; reflexivity. Qed.

Lemma jo_L_statc_hull : forall c x, In c jo_STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) ->
MGI.mg_data_lo S <= x < MGI.mg_img_hi S /\ ~ MGI.in_ivs (MGI.mg_wstat S) x.
Proof.
intros c x Hc Hx. rewrite jo_wstat. cbn [MJ.S_AJ MGI.mg_data_lo MGI.mg_img_hi]. unfold MJ.AJ_DATA_LO, MJ.AJ_IMG_HI. unfold jo_STATC in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; cbn [HI.hl_tp HI.hl_libc JH.hla_base AY.A4L AY.A4H] in Hx; unfold AY.A_TP in Hx;
[change (Z.of_nat (length _)) with 4 in Hx| change (Z.of_nat (length _)) with 8 in Hx| change (Z.of_nat (length _)) with 1 in Hx]; lia.
Qed.

Lemma jo_L_statc_priv : forall c x, In c jo_STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) ->
HI.hl_img_lo HL <= x < HI.hl_img_hi HL /\ ~ HI.hl_client_static HL x /\ ~ HI.hl_scratch HL x.
Proof.
intros c x Hc Hx. cbn [HI.hl_img_lo HI.hl_img_hi HI.hl_client_static HI.hl_scratch JH.hla_base AY.A4L AY.A4H]. unfold AY.a4_client_static, AY.A_TP.
unfold jo_STATC in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; cbn [HI.hl_tp HI.hl_libc JH.hla_base AY.A4L AY.A4H] in Hx; unfold AY.A_TP in Hx;
[change (Z.of_nat (length _)) with 4 in Hx| change (Z.of_nat (length _)) with 8 in Hx| change (Z.of_nat (length _)) with 1 in Hx]; lia.
Qed.

Lemma jo_L_sivs_cover : forall a, HI.hl_client_static HL a -> exists iv, In iv jo_SIVS /\ fst iv <= a < snd iv.
Proof.
intros a Hs. cbn [HI.hl_client_static JH.hla_base AY.A4L AY.A4H] in Hs. unfold AY.a4_client_static in Hs.
assert (C : (0xea500 <= a < 0xec420) \/ (0xec448 <= a < 0xec498) \/ (0x181998 <= a < 0x1819a8) \/ (0x612140 <= a < 0x622dbc) \/ (0x622dc0 <= a < 0x622e08)
\/ (0x622e10 <= a < 0x622e58) \/ (0x622e98 <= a < 0x642ea0) \/ (0x642ea8 <= a < 0x643120) \/ (0x643128 <= a < 0x644280)) by lia.
unfold jo_SIVS.
destruct C as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]];
[exists (0xea500, 0xec420)| exists (0xec448, 0xec498)| exists (0x181998, 0x1819a8)| exists (0x612140, 0x622dbc)| exists (0x622dc0, 0x622e08)| exists (0x622e10, 0x622e58)
| exists (0x622e98, 0x642ea0)| exists (0x642ea8, 0x643120)| exists (0x643128, 0x644280)]; (split; [cbn [In]; tauto| cbn [fst snd]; lia]).
Qed.

Lemma jo_L_static : forall a, HI.hl_client_static HL a -> dl_client_data DL a.
Proof.
intros a Hs. destruct (jo_L_sivs_cover a Hs) as (iv & Hin & Hr). exact (jo_L_sivs_data iv a Hin Hr).
Qed.

Variable LA : ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : aentry.
Variable FR0 : list (Z * Z).
Variable BAUX : Z.

Variables BOTJ TOPJ : Z.

Notation STAT := (STAT_A L BOTJ TOPJ jo_STATC).
Notation DCo := (DCo_jo RC.rc_canary LV).

Hypothesis HS : handoff_static L LA LV PERM0 TMAX NMAX RE FR0.
Hypothesis RUN_base_img : exists iv, In iv (lv_base LV) /\ fst iv <= HI.hl_img_lo HL /\ HI.hl_img_hi HL <= snd iv.
Hypothesis RUN_base_stack : exists iv, In iv (lv_base LV) /\ fst iv <= BOTJ /\ 2^47 <= snd iv.
Lemma RUN_img_base : exists iv, In iv (lv_base LV) /\ fst iv <= MGI.mg_data_lo S /\ MGI.mg_img_hi S <= snd iv.
Proof. destruct RUN_base_img as (iv & Hiv & B1 & B2). exists iv. split; [exact Hiv|]. cbn in *. unfold MJ.AJ_DATA_LO, MJ.AJ_IMG_HI. lia. Qed.
Hypothesis RUN_FR0_off_data : forall x, Fof LV FR0 x = true -> ~ (MGI.mg_data_lo S <= bv_unsigned x < MGI.mg_img_hi S).
Hypothesis RUN_botj : RC.alloc_ceiling <= BOTJ /\ BOTJ mod 8 = 0 /\ BOTJ <= TOPJ.
Hypothesis RUN_topj : RC.alloc_ceiling < TOPJ /\ TOPJ <= 2^47.
Hypothesis RUN_baux : TOPJ + 64 <= BAUX.
Hypothesis RUN_top_re : TOPJ + 64 <= ae_stack_top RE + 4096.
Lemma RUN_bot8 : BOTJ mod 8 = 0. Proof. exact (proj1 (proj2 RUN_botj)). Qed.
Lemma RUN_bot : RC.alloc_ceiling <= BOTJ. Proof. exact (proj1 RUN_botj). Qed.
Lemma jo_top_re : TOPJ + 64 <= ae_stack_top RE + JH.hl_stack_A L. Proof. exact RUN_top_re. Qed.

Let hs_LL0 := proj1 HS.
Let hs_wx := proj1 (proj2 HS).
Let hs_segs := proj1 (proj2 (proj2 HS)).
Let hs_sh := proj1 (proj2 (proj2 (proj2 HS))).
Let hs_bx := proj1 (proj2 (proj2 (proj2 (proj2 HS)))).
Let hs_bc := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))).
Let hs_b47 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))).
Let hs_low := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))))).
Let hs_frok := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))).
Let hs_froff := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))))))).
Let hs_frlow := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))))).
Let hs_rel := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))))).

Lemma jo_free2_null : JH.hiA_free2_null_ty L (aj_base_vj segs LV hs_wx hs_segs) unit (HEAPA63 L LV PERM0 TMAX NMAX DL RE DCo FR0 S BAUX STAT) TOPJ.
Proof.
apply QM2q.Mq0.free2_null_A.
intros A LB LM FR B m c a n (HP & _) Hin.
exact (proj1 (proj2 (proj2 (heapA1_blk L LV PERM0 TMAX NMAX DL RE DCo FR0 S BAUX STAT _ LB LM FR B m c a n HP (in_or_app _ _ _ (or_intror Hin)))))).
Qed.

Definition jo_SM (k : Z) : Z := if k =? 0 then 0x4a790 else if k =? 1 then 0x4a904 else if k =? 2 then 0x4aa94 else 0.
Lemma jo_L_sm : forall k, 0 <= k <= 3 -> JH.hl_stack_malloc L k = jo_SM k. Proof. intros k _. reflexivity. Qed.
Lemma jo_L_sm_stack : 4096 <= JH.hl_stack_A L. Proof. cbn. lia. Qed.

Lemma jo_L_strdup : JH.hl_strdup L = jo_SD. Proof. reflexivity. Qed.
Lemma jo_L_realloc : HI.hl_realloc HL = jo_RL. Proof. reflexivity. Qed.
Lemma jo_L_t2_stack : jo_SD_stack <= JH.hl_stack_A L /\ jo_RL_stack <= JH.hl_stack_A L. Proof. cbn. unfold jo_SD_stack, jo_RL_stack. lia. Qed.

Lemma jo_L_dpn_wstat : Forall (fun iv : Z * Z => snd iv <= dl_depot_n DL \/ dl_depot_n DL + 4 <= fst iv) (MGI.mg_wstat S).
Proof.
unfold MGI.mg_wstat. cbn [MJ.S_AJ MGI.mg_ctx MGI.mg_tp dl_depot_n DL_AR]. unfold RA.DP_N.
repeat (apply Forall_cons; [cbn [fst snd]; unfold QW7x.Mq0.RCTX, QW7x.Mq0.RATP; lia|]). apply Forall_nil.
Qed.
Lemma jo_L_dpn_priv : forall x, dl_depot_n DL <= x < dl_depot_n DL + 4 -> ~ HI.hl_client_static HL x /\ ~ HI.hl_scratch HL x.
Proof.
intros x Hx. cbn [dl_depot_n DL_AR] in Hx. unfold RA.DP_N in Hx.
cbn [HI.hl_client_static HI.hl_scratch JH.hla_base AY.A4L AY.A4H]. unfold AY.a4_client_static, AY.A_TP. lia.
Qed.

Lemma jo_L_img_lo_small : HI.hl_img_lo HL <= 0xb09000.
Proof. cbn. lia. Qed.

Definition hiA_jo :=
@hiA_v63 RC__ L LA LV PERM0 TMAX NMAX hs_LL0 hs_wx hs_segs hs_sh hs_bx hs_bc hs_b47 hs_low DL RE hs_rel DCo FR0 hs_frok hs_froff hs_frlow S BAUX STAT
MJ.aj_laws jo_L_malloc2 jo_L_free2 jo_L_tp2 jo_L_stack2 jo_IMG_low jo_IMG_seg_G jo_IMG_rw RUN_img_base jo_L_img jo_IMG_hull jo_L_static2 jo_OBL_R1P
jo_L_rtc jo_IMG_rtc_wr jo_L_errno RUN_FR0_off_data jo_L_dpn jo_L_dpn_hull jo_L_dpn_wstat jo_L_dpn_priv
(fun Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI _ _ Hlo _ PRES _ ST =>
stat_mng L BOTJ TOPJ jo_STATC jo_L_sb RUN_bot jo_L_statc_range jo_L_img_range LA LV PERM0 TMAX NMAX hs_LL0 hs_low FR0 S hs_frok
jo_IMG_low jo_L_statc_hull RUN_bot8 RUN_base_stack RUN_base_img Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI Hlo PRES ST)
(fun Lg g c H m m' Bc Tc Nc sp LBall _ _ Hcd _ ST => stat_asan L BOTJ TOPJ jo_STATC DL jo_L_sb RUN_bot jo_L_statc_data jo_L_imgsh_data jo_L_statc_range jo_L_img_range m m' Hcd ST)
jo_L_malloc jo_L_free jo_L_calloc jo_L_tp jo_L_gp jo_L_stack jo_L_static BOTJ RUN_bot jo_L_stackA jo_L_sb jo_L_hull_eq
jo_SM 4096 (DFs_jo RC.rc_canary LV) jo_L_sm jo_L_sm_stack
jo_SIVS jo_L_sivs_cover jo_L_sivs_data jo_L_scratch jo_IMG_errno_any jo_L_rstat_priv jo_L_scratch_data
(stat_client L BOTJ TOPJ jo_STATC jo_L_statc_priv)
jo_SD jo_SD_stack jo_RL jo_RL_stack (DT2_jo_closed RC.rc_canary LV) jo_L_strdup jo_L_realloc jo_L_t2_stack
TOPJ RUN_topj RUN_baux jo_top_re jo_STATC (stat_cells L BOTJ TOPJ jo_STATC) jo_L_rtc_all jo_L_sb_cells
(stat_static L BOTJ TOPJ jo_STATC DL jo_L_sb RUN_bot LA LV PERM0 TMAX NMAX hs_LL0 hs_segs hs_low RE DCo FR0 hs_froff S BAUX RC.rc_canary eq_refl eq_refl jo_L_can_got jo_L_can_guard jo_L_can_copy jo_L_need_locks)
jo_free2_null (proj2 RUN_botj) jo_L_img_lo_small.

Definition loop_rule_jo : QCVR.heap_loop_rule6 L hiA_jo :=
@heap_loop_rule_v63 RC__ L LA LV PERM0 TMAX NMAX hs_LL0 hs_wx hs_segs hs_sh hs_bx hs_bc hs_b47 hs_low DL RE hs_rel DCo FR0 hs_frok hs_froff hs_frlow S BAUX STAT
MJ.aj_laws jo_L_malloc2 jo_L_free2 jo_L_tp2 jo_L_stack2 jo_IMG_low jo_IMG_seg_G jo_IMG_rw RUN_img_base jo_L_img jo_IMG_hull jo_L_static2 jo_OBL_R1P
jo_L_rtc jo_IMG_rtc_wr jo_L_errno RUN_FR0_off_data jo_L_dpn jo_L_dpn_hull jo_L_dpn_wstat jo_L_dpn_priv
(fun Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI _ _ Hlo _ PRES _ ST =>
stat_mng L BOTJ TOPJ jo_STATC jo_L_sb RUN_bot jo_L_statc_range jo_L_img_range LA LV PERM0 TMAX NMAX hs_LL0 hs_low FR0 S hs_frok
jo_IMG_low jo_L_statc_hull RUN_bot8 RUN_base_stack RUN_base_img Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI Hlo PRES ST)
(fun Lg g c H m m' Bc Tc Nc sp LBall _ _ Hcd _ ST => stat_asan L BOTJ TOPJ jo_STATC DL jo_L_sb RUN_bot jo_L_statc_data jo_L_imgsh_data jo_L_statc_range jo_L_img_range m m' Hcd ST)
jo_L_malloc jo_L_free jo_L_calloc jo_L_tp jo_L_gp jo_L_stack jo_L_static BOTJ RUN_bot jo_L_stackA jo_L_sb jo_L_hull_eq
jo_SM 4096 (DFs_jo RC.rc_canary LV) jo_L_sm jo_L_sm_stack
jo_SIVS jo_L_sivs_cover jo_L_sivs_data jo_L_scratch jo_IMG_errno_any jo_L_rstat_priv jo_L_scratch_data
(stat_client L BOTJ TOPJ jo_STATC jo_L_statc_priv)
jo_SD jo_SD_stack jo_RL jo_RL_stack (DT2_jo_closed RC.rc_canary LV) jo_L_strdup jo_L_realloc jo_L_t2_stack
TOPJ RUN_topj RUN_baux jo_top_re jo_STATC (stat_cells L BOTJ TOPJ jo_STATC) jo_L_rtc_all jo_L_sb_cells
(stat_static L BOTJ TOPJ jo_STATC DL jo_L_sb RUN_bot LA LV PERM0 TMAX NMAX hs_LL0 hs_segs hs_low RE DCo FR0 hs_froff S BAUX RC.rc_canary eq_refl eq_refl jo_L_can_got jo_L_can_guard jo_L_can_copy jo_L_need_locks)
jo_free2_null (proj2 RUN_botj) jo_L_img_lo_small.

End Jo.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXEH.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMow. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcGV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcGV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNLn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtIP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtIP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU91.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBzu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZrD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZrD.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPUe.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCVR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdSl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM2q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module AY := Qwm6.Mq4.
Module MJ := QdSl.
Module RG := QXEH.

Section Jo.
Context {RC__ : RC.RunConsts}.
Notation L := AY.A4L.
Notation HL := (JH.hla_base L).
Notation segs := (HI.hl_segs HL).
Notation S := MJ.S_AJU.
Notation DL := (@DL_AR (Band_RC RC.rc_canary)).

Lemma jo_L_malloc2 : HI.hl_malloc2 HL = MGI.mg_malloc S. Proof. reflexivity. Qed.
Lemma jo_L_free2 : HI.hl_free2 HL = MGI.mg_free S. Proof. reflexivity. Qed.
Lemma jo_L_tp2 : HI.hl_tp HL = MGI.mg_tp S. Proof. reflexivity. Qed.
Lemma jo_L_stack2 : MGI.mg_stack S <= HI.hl_stack HL. Proof. cbn. lia. Qed.
Lemma jo_IMG_low : MGI.mg_img_hi S <= kLowEnd. Proof. cbn. unfold MJ.AJU_IMG_HI, kLowEnd. lia. Qed.
Lemma jo_L_img : HI.hl_img_lo HL = dl_img_lo DL /\ HI.hl_img_hi HL = dl_img_hi DL. Proof. split; reflexivity. Qed.
Lemma jo_L_errno : dl_errno DL = HI.hl_tp HL - 164. Proof. reflexivity. Qed.
Lemma jo_L_malloc : HI.hl_malloc HL = dl_malloc DL. Proof. reflexivity. Qed.
Lemma jo_L_free : HI.hl_free HL = dl_free DL. Proof. reflexivity. Qed.
Lemma jo_L_calloc : HI.hl_calloc HL = dl_calloc DL. Proof. reflexivity. Qed.
Lemma jo_L_tp : HI.hl_tp HL = dl_tp DL. Proof. reflexivity. Qed.
Lemma jo_L_gp : JH.hl_gp L = dl_gp DL. Proof. reflexivity. Qed.

Lemma jo_L_stack : dl_malloc_stack DL <= JH.hl_stack_A L /\ dl_free_stack DL <= JH.hl_stack_A L /\ dl_calloc_stack DL <= JH.hl_stack_A L.
Proof. cbn. lia. Qed.

Lemma jo_L_stackA : 64 <= JH.hl_stack_A L. Proof. cbn. lia. Qed.

Lemma jo_L_dpn : 0 <= dl_depot_n DL /\ dl_depot_n DL + 4 <= RC.alloc_ceiling.
Proof. pose proof (@RC.alloc_ceiling_range RC__). cbn. unfold RA.DP_N. lia. Qed.
Lemma jo_L_dpn_hull : dl_img_lo DL <= dl_depot_n DL /\ dl_depot_n DL + 4 <= dl_img_hi DL.
Proof. cbn. unfold RA.DP_N. lia. Qed.
Lemma jo_L_sb : JH.hl_sb L = kShadowOffset. Proof. reflexivity. Qed.
Lemma jo_L_hull_eq : HI.hl_img_lo HL = MGI.mg_img_lo S /\ HI.hl_img_hi HL = MGI.mg_img_hi S. Proof. split; reflexivity. Qed.

Lemma jo_seg_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x647000 <= z) -> find_segment segs z n = None.
Proof. exact RG.ref_find_segment_none. Qed.

Lemma jo_IMG_seg_G : forall z, z + 1 <= MGI.mg_img_lo S \/ MGI.mg_img_hi S <= z -> find_segment segs z 1 = None.
Proof. intros z Hz. apply jo_seg_none; [lia|]. cbn in Hz. unfold MJ.AJU_IMG_HI in Hz. lia. Qed.

Lemma jo_seg_some : forall y, find_segment segs y 1 <> None -> 0x10000 <= y < 0x647000.
Proof.
intros y Hy. destruct (Z.lt_ge_cases y 0x10000) as [H1|H1]; [exfalso; apply Hy; apply jo_seg_none; lia|].
destruct (Z.lt_ge_cases y 0x647000) as [H2|H2]; [lia| exfalso; apply Hy; apply jo_seg_none; lia].
Qed.

Lemma jo_IMG_hull : HI.hl_img_lo HL <= MGI.mg_data_lo S /\ MGI.mg_img_hi S <= HI.hl_img_hi HL /\
forall y, find_segment segs y 1 <> None -> HI.hl_img_lo HL <= y < HI.hl_img_hi HL.
Proof. cbn. unfold MJ.AJU_DATA_LO, MJ.AJU_IMG_HI. split; [lia|]. split; [lia|]. exact jo_seg_some. Qed.

Lemma jo_seg_ro : forall z, 0x10000 <= z < 0xe4000 -> exists seg, find_segment segs z 1 = Some seg /\ seg_writable seg = false.
Proof.
intros z Hz. cbn [HI.hl_segs JH.hla_base AY.A4L AY.A4H].
unfold QbFI.asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x2e000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x3e000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0xa6000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + 1) (0x10000 + 0x2e000)); cbn [andb]; try lia.
- eexists. split; [reflexivity| vm_compute; reflexivity].
- destruct (Z.leb_spec0 0x3e000 z); destruct (Z.leb_spec0 (z + 1) (0x3e000 + 0xa6000)); cbn [andb]; try lia.
eexists. split; [reflexivity| vm_compute; reflexivity].
Qed.

Lemma jo_IMG_rw : forall y : word, find_segment segs (bv_unsigned y) 1 <> None -> ro_addr segs y = false ->
MGI.mg_data_lo S <= bv_unsigned y < MGI.mg_img_hi S.
Proof.
intros y Hf Hro. pose proof (jo_seg_some _ Hf) as Hr. cbn [MJ.S_AJU MGI.mg_data_lo MGI.mg_img_hi]. unfold MJ.AJU_DATA_LO, MJ.AJU_IMG_HI.
destruct (Z.lt_ge_cases (bv_unsigned y) 0xe4000) as [Hlt|Hge]; [exfalso| lia].
destruct (jo_seg_ro (bv_unsigned y) ltac:(lia)) as (seg & E & W). unfold ro_addr in Hro. rewrite E, W in Hro. discriminate.
Qed.

Fixpoint img_w_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| Datatypes.S n' => match wview segs (fun _ => None) (wa A) with Some _ => img_w_b (A + 1) n' | None => false end
end.
Lemma img_w_b_sound : forall n A (m : word -> option byte), img_w_b A n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 -> wr_at segs m A (Z.of_nat n).
Proof.
intros n A m Hb HA Hhi. split; [exact HA|]. split; [exact Hhi|]. revert A Hb HA Hhi.
induction n as [|n IH]; intros A Hb HA Hhi i Hi; [lia|]. cbn [img_w_b] in Hb.
destruct (wview segs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite Z.add_0_r. unfold wview in *. destruct (m (wa A)); [discriminate|]. cbn beta in Ew. rewrite Ew. discriminate.
- replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) Hb); lia.
Qed.

Lemma jo_L_rtc : incl (MGI.mg_rtc S) (dl_rtc DL).
Proof. intros c [<-|[<-|[<-|[]]]]; [left| right; left| right; right; left]; reflexivity. Qed.

Lemma jo_IMG_rtc_wr : forall m : word -> option byte, Forall (fun c => wr_at segs m (fst c) (Z.of_nat (length (snd c)))) (MGI.mg_rtc S).
Proof.
intros m. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd];
(apply img_w_b_sound; [vm_compute; reflexivity| vm_compute; discriminate| vm_compute; discriminate]).
Qed.

Lemma jo_wstat : forall a, MGI.in_ivs (MGI.mg_wstat S) a <-> (0x6458a8 <= a < 0x645c48 \/ 0x62547c <= a < 0x625480).
Proof.
intros a. unfold MGI.in_ivs, MGI.mg_wstat. cbn [MJ.S_AJU MGI.mg_ctx MGI.mg_tp]. unfold RG.RCTX, RG.RATP. split.
- intros (iv & [<-|[<-|[]]] & Hr); cbn [fst snd] in Hr; lia.
- intros [Hr|Hr]; [exists (0x6458a8, 0x6458a8 + 928)| exists (0x625520 + -164, 0x625520 + -164 + 4)]; (split; [cbn; auto| cbn [fst snd]; lia]).
Qed.

Lemma jo_L_static2 : forall a, HI.hl_client_static HL a ->
MGI.mg_data_lo S <= a < MGI.mg_img_hi S /\ ~ MGI.in_ivs (MGI.mg_wstat S) a.
Proof.
intros a Ha. rewrite jo_wstat. cbn [MJ.S_AJU MGI.mg_data_lo MGI.mg_img_hi]. unfold MJ.AJU_DATA_LO, MJ.AJU_IMG_HI.
cbn [HI.hl_client_static JH.hla_base AY.A4L AY.A4H] in Ha. unfold AY.a4_client_static in Ha. lia.
Qed.

Lemma jo_rstat : forall a, mng_static S a <->
(0x6458a8 <= a < 0x645c48 \/ 0x6458a0 <= a < 0x6458a4 \/ 0x646db8 <= a < 0x646dbc \/ 0x6457b3 <= a < 0x6457b4
\/ 0x6457e0 <= a < 0x6457e8 \/ 0xe8f90 <= a < 0xe8f98 \/ 0x645560 <= a < 0x645568).
Proof.
intros a. unfold mng_static, MGI.in_ivs. cbn [MJ.S_AJU MGI.mg_rstat]. unfold MJ.aju_rstat, RG.RCTX, RG.RMLOCK, RG.RVMLOCK, RG.RNEED_LOCKS, RG.RPAGE_SIZE, RG.RGOT_SSP, RG.RSSP_GUARD. split.
- intros (iv & Hin & Hr). cbn [In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
- intros H.
destruct H as [H|[H|[H|[H|[H|[H|H]]]]]];
[exists (0x6458a8, 0x6458a8 + 928)| exists (0x6458a0, 0x6458a0 + 4)| exists (0x646db8, 0x646db8 + 4)| exists (0x6457b3, 0x6457b3 + 1)
| exists (0x6457e0, 0x6457e0 + 8)| exists (0xe8f90, 0xe8f90 + 8)| exists (0x645560, 0x645560 + 8)];
(split; [cbn [In]; tauto| cbn [fst snd]; lia]).
Qed.

Lemma jo_in_rtc : forall a, (0x6457e0 <= a < 0x6457e8 \/ 0xe8f90 <= a < 0xe8f98 \/ 0x645560 <= a < 0x645568) -> in_rtc S a.
Proof.
intros a H. unfold in_rtc. cbn [MJ.S_AJU MGI.mg_rtc]. unfold RG.RPAGE_SIZE, RG.RGOT_SSP, RG.RSSP_GUARD.
destruct H as [H|[H|H]]; [eexists; split; [left; reflexivity|]| eexists; split; [right; left; reflexivity|]| eexists; split; [right; right; left; reflexivity|]];
cbn [fst snd]; change (Z.of_nat (length _)) with 8; lia.
Qed.

Lemma jo_OBL_R1P : forall a, (mng_static S a /\ ~ in_rtc S a) \/ fst (MGI.mg_ctx S) <= a < snd (MGI.mg_ctx S) -> dl_client_data DL a.
Proof.
intros a H. unfold DL_AR; cbn [dl_client_data]; unfold RA.a_client_data.
destruct H as [[Hs Hn]|Hc].
- apply jo_rstat in Hs. assert (Hn' : ~ (0x6457e0 <= a < 0x6457e8 \/ 0xe8f90 <= a < 0xe8f98 \/ 0x645560 <= a < 0x645568)) by (intros X; exact (Hn (jo_in_rtc a X))). lia.
- cbn [MJ.S_AJU MGI.mg_ctx fst snd] in Hc. unfold RG.RCTX in Hc. lia.
Qed.

Definition jo_SIVS : list (Z * Z) :=
[(0xec920, 0xeeb00); (0xeeb08, 0xeeb58); (0x184058, 0x184068); (0x614800, 0x62547c); (0x625480, 0x6254c8); (0x6254d0, 0x625518); (0x625558, 0x645560);
(0x645568, 0x6457e0); (0x6457e8, 0x646940)].
Lemma jo_L_sivs_data : forall iv a, In iv jo_SIVS -> fst iv <= a < snd iv -> dl_client_data DL a.
Proof.
intros iv a Hin Hr. unfold DL_AR; cbn [dl_client_data]; unfold RA.a_client_data. unfold jo_SIVS in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.

Lemma jo_L_rstat_priv : forall a, mng_static S a -> ~ HI.hl_client_static HL a /\ ~ HI.hl_scratch HL a.
Proof.
intros a Hs. apply jo_rstat in Hs. cbn [HI.hl_client_static HI.hl_scratch JH.hla_base AY.A4L AY.A4H]. unfold AY.a4_client_static, AY.A_TP. lia.
Qed.

Lemma jo_L_scratch_data : forall a, HI.hl_scratch HL a -> MGI.mg_data_lo S <= a < MGI.mg_img_hi S.
Proof.
intros a Hs. cbn [HI.hl_scratch JH.hla_base AY.A4L AY.A4H] in Hs. unfold AY.A_TP in Hs.
cbn [MJ.S_AJU MGI.mg_data_lo MGI.mg_img_hi]. unfold MJ.AJU_DATA_LO, MJ.AJU_IMG_HI. lia.
Qed.

Lemma jo_L_scratch : forall a, HI.hl_scratch HL a -> HI.hl_tp HL - 164 <= a < HI.hl_tp HL - 160.
Proof. intros a Hs. exact Hs. Qed.

Fixpoint img_r_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| Datatypes.S n' => match seg_rom segs (wa A) with Some _ => img_r_b (A + 1) n' | None => false end
end.
Lemma img_r_b_sound : forall n A (m : word -> option byte), img_r_b A n = true ->
exists bs, length bs = n /\ forall i, (i < n)%nat -> mrd segs m (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
induction n as [|n IH]; intros A m Hb; [exists []; split; [reflexivity| intros i Hi; lia]|].
cbn [img_r_b] in Hb. destruct (seg_rom segs (wa A)) as [b0|] eqn:Er; [|discriminate].
destruct (IH (A + 1) m Hb) as (bs & Hl & Hbs).
exists ((match m (wa A) with Some b => b | None => b0 end) :: bs). split; [cbn [length]; rewrite Hl; reflexivity|].
intros [|i] Hi; cbn [nth_error].
- rewrite Z.add_0_r. unfold mrd. destruct (m (wa A)); [reflexivity| exact Er].
- replace (A + Z.of_nat (Datatypes.S i)) with (A + 1 + Z.of_nat i) by lia. apply Hbs. lia.
Qed.

Lemma jo_IMG_errno_any : forall m : word -> option byte, exists v : word, rw_cells segs m (HI.hl_tp HL - 164) [C4 v].
Proof.
intros m. cbn [HI.hl_tp JH.hla_base AY.A4L AY.A4H]. unfold AY.A_TP.
destruct (img_r_b_sound 4 (0x625520 - 164) m ltac:(vm_compute; reflexivity)) as (bs & Hl & Hbs).
exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [split; [cbn; auto|]|].
- cbn [cells_bytes cbytes]. rewrite app_nil_r, (le4_of_bytes bs Hl). split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. apply Hbs. lia.
- cbn [cells_size csize Nat.add]. apply (img_w_b_sound 4); [vm_compute; reflexivity| lia| lia].
Qed.

Definition jo_STATC : list (Z * list byte) :=
[ (0x646db8, le4 (Z_to_bv 64 0));
(HI.hl_tp HL - 16, le8 RC.rc_canary);
(HI.hl_libc HL + 3, [Z_to_bv 8 0]) ].

Definition byte_eqb (a b : byte) : bool := Z.eqb (bv_unsigned a) (bv_unsigned b).
Fixpoint bytes_eqb (x y : list byte) : bool :=
match x, y with [], [] => true | a :: x', b :: y' => byte_eqb a b && bytes_eqb x' y' | _, _ => false end.
Lemma bytes_eqb_eq : forall x y, bytes_eqb x y = true -> x = y.
Proof.
induction x as [|a x IH]; intros [|b y] H; cbn [bytes_eqb] in H; try discriminate; [reflexivity|].
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b. f_equal. exact (IH y H2).
Qed.
Definition cell_mem (c : Z * list byte) (l : list (Z * list byte)) : bool :=
existsb (fun d => Z.eqb (fst c) (fst d) && bytes_eqb (snd c) (snd d)) l.
Lemma cell_mem_In : forall c l, cell_mem c l = true -> In c l.
Proof.
intros [a x] l H. unfold cell_mem in H. apply existsb_exists in H as ([b y] & Hin & E). cbn [fst snd] in E.
apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. apply bytes_eqb_eq in E2. subst b y. exact Hin.
Qed.

Lemma jo_L_rtc_all : forall c, In c (JH.hl_rt_consts L) -> In c (dl_rtc DL) \/ In c jo_STATC.
Proof.
assert (HF : forallb (fun c => cell_mem c (skipn 3 (@rtc_AR (Band_RC RC.rc_canary))) || Z.eqb (fst c) 0x646db8) (JH.hl_rt_consts L) = true) by (vm_compute; reflexivity).
intros c Hc. rewrite forallb_forall in HF. specialize (HF c Hc). apply orb_true_iff in HF as [HF|HF].
- left. unfold DL_AR; cbn [dl_rtc]. apply cell_mem_In in HF. clear - HF. unfold rtc_AR in *. cbn [skipn] in HF. right; right; right. exact HF.
- right. apply Z.eqb_eq in HF. cbn [JH.hl_rt_consts AY.A4L] in Hc. unfold AY.a4_rt_consts in Hc. cbn [In] in Hc.
repeat (destruct Hc as [<-|Hc]; [first [left; reflexivity | cbn [fst] in HF; discriminate HF]|]). destruct Hc.
Qed.

Lemma jo_L_sb_cells :
In (JH.hl_got_sb L, le8 (Z_to_bv 64 (JH.hl_sb_cell L))) (dl_rtc DL) /\ In (JH.hl_sb_cell L, le8 (Z_to_bv 64 (JH.hl_sb L))) (dl_rtc DL) /\
In (JH.hl_got_uar L, le8 (Z_to_bv 64 (JH.hl_uar_cell L))) (dl_rtc DL) /\ In (JH.hl_uar_cell L, le4 (Z_to_bv 64 1)) (dl_rtc DL).
Proof.
unfold DL_AR; cbn [dl_rtc JH.hl_got_sb JH.hl_sb_cell JH.hl_sb JH.hl_got_uar JH.hl_uar_cell AY.A4L]. unfold rtc_AR. cbn [In].
repeat split; repeat (first [left; reflexivity | right]).
Qed.

Lemma jo_L_statc_data : forall c x, In c jo_STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) -> dl_client_data DL x.
Proof.
intros c x Hc Hx. unfold DL_AR; cbn [dl_client_data]; unfold RA.a_client_data. unfold jo_STATC in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; cbn [HI.hl_tp HI.hl_libc JH.hla_base AY.A4L AY.A4H] in Hx; unfold AY.A_TP in Hx;
[change (Z.of_nat (length _)) with 4 in Hx| change (Z.of_nat (length _)) with 8 in Hx| change (Z.of_nat (length _)) with 1 in Hx]; lia.
Qed.
Lemma jo_L_statc_range : forall c x, In c jo_STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) -> 0 <= x < 2^64.
Proof.
intros c x Hc Hx. unfold jo_STATC in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; cbn [HI.hl_tp HI.hl_libc JH.hla_base AY.A4L AY.A4H] in Hx; unfold AY.A_TP in Hx;
[change (Z.of_nat (length _)) with 4 in Hx| change (Z.of_nat (length _)) with 8 in Hx| change (Z.of_nat (length _)) with 1 in Hx]; lia.
Qed.
Lemma jo_L_imgsh_data : forall g, HI.hl_img_lo HL <= 8 * g -> 8 * g + 8 <= HI.hl_img_hi HL -> dl_client_data DL (g + JH.hl_sb L).
Proof.
intros g G1 G2. cbn [HI.hl_img_lo HI.hl_img_hi JH.hl_sb JH.hla_base AY.A4L AY.A4H] in *. unfold AY.A_SB.
unfold DL_AR; cbn [dl_client_data]; unfold RA.a_client_data. lia.
Qed.
Lemma jo_L_img_range : 0 <= HI.hl_img_lo HL /\ HI.hl_img_hi HL <= 2^47. Proof. cbn. lia. Qed.
Lemma jo_L_can_got : In (HI.hl_got_guard HL, le8 (Z_to_bv 64 (HI.hl_guard HL))) (dl_rtc DL). Proof. right; left; reflexivity. Qed.
Lemma jo_L_can_guard : In (HI.hl_guard HL, le8 RC.rc_canary) (dl_rtc DL). Proof. right; right; left; reflexivity. Qed.
Lemma jo_L_can_copy : In (HI.hl_tp HL - 16, le8 RC.rc_canary) jo_STATC. Proof. right; left; reflexivity. Qed.
Lemma jo_L_need_locks : In (HI.hl_libc HL + 3, [Z_to_bv 8 0]) jo_STATC. Proof. right; right; left; reflexivity. Qed.

Lemma jo_L_statc_hull : forall c x, In c jo_STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) ->
MGI.mg_data_lo S <= x < MGI.mg_img_hi S /\ ~ MGI.in_ivs (MGI.mg_wstat S) x.
Proof.
intros c x Hc Hx. rewrite jo_wstat. cbn [MJ.S_AJU MGI.mg_data_lo MGI.mg_img_hi]. unfold MJ.AJU_DATA_LO, MJ.AJU_IMG_HI. unfold jo_STATC in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; cbn [HI.hl_tp HI.hl_libc JH.hla_base AY.A4L AY.A4H] in Hx; unfold AY.A_TP in Hx;
[change (Z.of_nat (length _)) with 4 in Hx| change (Z.of_nat (length _)) with 8 in Hx| change (Z.of_nat (length _)) with 1 in Hx]; lia.
Qed.

Lemma jo_L_statc_priv : forall c x, In c jo_STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) ->
HI.hl_img_lo HL <= x < HI.hl_img_hi HL /\ ~ HI.hl_client_static HL x /\ ~ HI.hl_scratch HL x.
Proof.
intros c x Hc Hx. cbn [HI.hl_img_lo HI.hl_img_hi HI.hl_client_static HI.hl_scratch JH.hla_base AY.A4L AY.A4H]. unfold AY.a4_client_static, AY.A_TP.
unfold jo_STATC in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; cbn [HI.hl_tp HI.hl_libc JH.hla_base AY.A4L AY.A4H] in Hx; unfold AY.A_TP in Hx;
[change (Z.of_nat (length _)) with 4 in Hx| change (Z.of_nat (length _)) with 8 in Hx| change (Z.of_nat (length _)) with 1 in Hx]; lia.
Qed.

Lemma jo_L_sivs_cover : forall a, HI.hl_client_static HL a -> exists iv, In iv jo_SIVS /\ fst iv <= a < snd iv.
Proof.
intros a Hs. cbn [HI.hl_client_static JH.hla_base AY.A4L AY.A4H] in Hs. unfold AY.a4_client_static in Hs.
assert (C : (0xec920 <= a < 0xeeb00) \/ (0xeeb08 <= a < 0xeeb58) \/ (0x184058 <= a < 0x184068) \/ (0x614800 <= a < 0x62547c) \/ (0x625480 <= a < 0x6254c8)
\/ (0x6254d0 <= a < 0x625518) \/ (0x625558 <= a < 0x645560) \/ (0x645568 <= a < 0x6457e0) \/ (0x6457e8 <= a < 0x646940)) by lia.
unfold jo_SIVS.
destruct C as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]];
[exists (0xec920, 0xeeb00)| exists (0xeeb08, 0xeeb58)| exists (0x184058, 0x184068)| exists (0x614800, 0x62547c)| exists (0x625480, 0x6254c8)| exists (0x6254d0, 0x625518)
| exists (0x625558, 0x645560)| exists (0x645568, 0x6457e0)| exists (0x6457e8, 0x646940)]; (split; [cbn [In]; tauto| cbn [fst snd]; lia]).
Qed.

Lemma jo_L_static : forall a, HI.hl_client_static HL a -> dl_client_data DL a.
Proof.
intros a Hs. destruct (jo_L_sivs_cover a Hs) as (iv & Hin & Hr). exact (jo_L_sivs_data iv a Hin Hr).
Qed.

Variable LA : ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : aentry.
Variable FR0 : list (Z * Z).
Variable BAUX : Z.

Variables BOTJ TOPJ : Z.

Notation STAT := (STAT_A L BOTJ TOPJ jo_STATC).
Notation DCo := (DCo_jo RC.rc_canary LV).

Hypothesis HS : handoff_static L LA LV PERM0 TMAX NMAX RE FR0.
Hypothesis RUN_base_img : exists iv, In iv (lv_base LV) /\ fst iv <= HI.hl_img_lo HL /\ HI.hl_img_hi HL <= snd iv.
Hypothesis RUN_base_stack : exists iv, In iv (lv_base LV) /\ fst iv <= BOTJ /\ 2^47 <= snd iv.
Lemma RUN_img_base : exists iv, In iv (lv_base LV) /\ fst iv <= MGI.mg_data_lo S /\ MGI.mg_img_hi S <= snd iv.
Proof. destruct RUN_base_img as (iv & Hiv & B1 & B2). exists iv. split; [exact Hiv|]. cbn in *. unfold MJ.AJU_DATA_LO, MJ.AJU_IMG_HI. lia. Qed.
Hypothesis RUN_FR0_off_data : forall x, Fof LV FR0 x = true -> ~ (MGI.mg_data_lo S <= bv_unsigned x < MGI.mg_img_hi S).
Hypothesis RUN_botj : RC.alloc_ceiling <= BOTJ /\ BOTJ mod 8 = 0 /\ BOTJ <= TOPJ.
Hypothesis RUN_topj : RC.alloc_ceiling < TOPJ /\ TOPJ <= 2^47.
Hypothesis RUN_baux : TOPJ + 64 <= BAUX.
Hypothesis RUN_top_re : TOPJ + 64 <= ae_stack_top RE + 4096.
Lemma RUN_bot8 : BOTJ mod 8 = 0. Proof. exact (proj1 (proj2 RUN_botj)). Qed.
Lemma RUN_bot : RC.alloc_ceiling <= BOTJ. Proof. exact (proj1 RUN_botj). Qed.
Lemma jo_top_re : TOPJ + 64 <= ae_stack_top RE + JH.hl_stack_A L. Proof. exact RUN_top_re. Qed.

Let hs_LL0 := proj1 HS.
Let hs_wx := proj1 (proj2 HS).
Let hs_segs := proj1 (proj2 (proj2 HS)).
Let hs_sh := proj1 (proj2 (proj2 (proj2 HS))).
Let hs_bx := proj1 (proj2 (proj2 (proj2 (proj2 HS)))).
Let hs_bc := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))).
Let hs_b47 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))).
Let hs_low := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))))).
Let hs_frok := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))).
Let hs_froff := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))))))).
Let hs_frlow := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))))).
Let hs_rel := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))))).

Lemma jo_free2_null : JH.hiA_free2_null_ty L (aj_base_vj segs LV hs_wx hs_segs) unit (HEAPA63 L LV PERM0 TMAX NMAX DL RE DCo FR0 S BAUX STAT) TOPJ.
Proof.
apply QM2q.free2_null_A.
intros A LB LM FR B m c a n (HP & _) Hin.
exact (proj1 (proj2 (proj2 (heapA1_blk L LV PERM0 TMAX NMAX DL RE DCo FR0 S BAUX STAT _ LB LM FR B m c a n HP (in_or_app _ _ _ (or_intror Hin)))))).
Qed.

Definition jo_SM (k : Z) : Z := if k =? 0 then 0x4a9bc else if k =? 1 then 0x4ab30 else if k =? 2 then 0x4acc0 else if k =? 3 then 0x4ae5c else 0.
Lemma jo_L_sm : forall k, 0 <= k <= 3 -> JH.hl_stack_malloc L k = jo_SM k. Proof. intros k _. reflexivity. Qed.
Lemma jo_L_sm_stack : 4096 <= JH.hl_stack_A L. Proof. cbn. lia. Qed.

Lemma jo_L_strdup : JH.hl_strdup L = jo_SD. Proof. reflexivity. Qed.
Lemma jo_L_realloc : HI.hl_realloc HL = jo_RL. Proof. reflexivity. Qed.
Lemma jo_L_t2_stack : jo_SD_stack <= JH.hl_stack_A L /\ jo_RL_stack <= JH.hl_stack_A L. Proof. cbn. unfold jo_SD_stack, jo_RL_stack. lia. Qed.

Lemma jo_L_dpn_wstat : Forall (fun iv : Z * Z => snd iv <= dl_depot_n DL \/ dl_depot_n DL + 4 <= fst iv) (MGI.mg_wstat S).
Proof.
unfold MGI.mg_wstat. cbn [MJ.S_AJU MGI.mg_ctx MGI.mg_tp dl_depot_n DL_AR]. unfold RA.DP_N.
repeat (apply Forall_cons; [cbn [fst snd]; unfold QXEH.RCTX, QXEH.RATP; lia|]). apply Forall_nil.
Qed.
Lemma jo_L_dpn_priv : forall x, dl_depot_n DL <= x < dl_depot_n DL + 4 -> ~ HI.hl_client_static HL x /\ ~ HI.hl_scratch HL x.
Proof.
intros x Hx. cbn [dl_depot_n DL_AR] in Hx. unfold RA.DP_N in Hx.
cbn [HI.hl_client_static HI.hl_scratch JH.hla_base AY.A4L AY.A4H]. unfold AY.a4_client_static, AY.A_TP. lia.
Qed.

Lemma jo_L_img_lo_small : HI.hl_img_lo HL <= 0xb09000.
Proof. cbn. lia. Qed.

Definition hiA_jo :=
@hiA_v63 RC__ L LA LV PERM0 TMAX NMAX hs_LL0 hs_wx hs_segs hs_sh hs_bx hs_bc hs_b47 hs_low DL RE hs_rel DCo FR0 hs_frok hs_froff hs_frlow S BAUX STAT
MJ.aju_laws jo_L_malloc2 jo_L_free2 jo_L_tp2 jo_L_stack2 jo_IMG_low jo_IMG_seg_G jo_IMG_rw RUN_img_base jo_L_img jo_IMG_hull jo_L_static2 jo_OBL_R1P
jo_L_rtc jo_IMG_rtc_wr jo_L_errno RUN_FR0_off_data jo_L_dpn jo_L_dpn_hull jo_L_dpn_wstat jo_L_dpn_priv
(fun Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI _ _ Hlo _ PRES _ ST =>
stat_mng L BOTJ TOPJ jo_STATC jo_L_sb RUN_bot jo_L_statc_range jo_L_img_range LA LV PERM0 TMAX NMAX hs_LL0 hs_low FR0 S hs_frok
jo_IMG_low jo_L_statc_hull RUN_bot8 RUN_base_stack RUN_base_img Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI Hlo PRES ST)
(fun Lg g c H m m' Bc Tc Nc sp LBall _ _ Hcd _ ST => stat_asan L BOTJ TOPJ jo_STATC DL jo_L_sb RUN_bot jo_L_statc_data jo_L_imgsh_data jo_L_statc_range jo_L_img_range m m' Hcd ST)
jo_L_malloc jo_L_free jo_L_calloc jo_L_tp jo_L_gp jo_L_stack jo_L_static BOTJ RUN_bot jo_L_stackA jo_L_sb jo_L_hull_eq
jo_SM 4096 (DFs_jo RC.rc_canary LV) jo_L_sm jo_L_sm_stack
jo_SIVS jo_L_sivs_cover jo_L_sivs_data jo_L_scratch jo_IMG_errno_any jo_L_rstat_priv jo_L_scratch_data
(stat_client L BOTJ TOPJ jo_STATC jo_L_statc_priv)
jo_SD jo_SD_stack jo_RL jo_RL_stack (DT2_jo_closed RC.rc_canary LV) jo_L_strdup jo_L_realloc jo_L_t2_stack
TOPJ RUN_topj RUN_baux jo_top_re jo_STATC (stat_cells L BOTJ TOPJ jo_STATC) jo_L_rtc_all jo_L_sb_cells
(stat_static L BOTJ TOPJ jo_STATC DL jo_L_sb RUN_bot LA LV PERM0 TMAX NMAX hs_LL0 hs_segs hs_low RE DCo FR0 hs_froff S BAUX RC.rc_canary eq_refl eq_refl jo_L_can_got jo_L_can_guard jo_L_can_copy jo_L_need_locks)
jo_free2_null (proj2 RUN_botj) jo_L_img_lo_small.

Definition loop_rule_jo : QCVR.heap_loop_rule6 L hiA_jo :=
@heap_loop_rule_v63 RC__ L LA LV PERM0 TMAX NMAX hs_LL0 hs_wx hs_segs hs_sh hs_bx hs_bc hs_b47 hs_low DL RE hs_rel DCo FR0 hs_frok hs_froff hs_frlow S BAUX STAT
MJ.aju_laws jo_L_malloc2 jo_L_free2 jo_L_tp2 jo_L_stack2 jo_IMG_low jo_IMG_seg_G jo_IMG_rw RUN_img_base jo_L_img jo_IMG_hull jo_L_static2 jo_OBL_R1P
jo_L_rtc jo_IMG_rtc_wr jo_L_errno RUN_FR0_off_data jo_L_dpn jo_L_dpn_hull jo_L_dpn_wstat jo_L_dpn_priv
(fun Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI _ _ Hlo _ PRES _ ST =>
stat_mng L BOTJ TOPJ jo_STATC jo_L_sb RUN_bot jo_L_statc_range jo_L_img_range LA LV PERM0 TMAX NMAX hs_LL0 hs_low FR0 S hs_frok
jo_IMG_low jo_L_statc_hull RUN_bot8 RUN_base_stack RUN_base_img Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI Hlo PRES ST)
(fun Lg g c H m m' Bc Tc Nc sp LBall _ _ Hcd _ ST => stat_asan L BOTJ TOPJ jo_STATC DL jo_L_sb RUN_bot jo_L_statc_data jo_L_imgsh_data jo_L_statc_range jo_L_img_range m m' Hcd ST)
jo_L_malloc jo_L_free jo_L_calloc jo_L_tp jo_L_gp jo_L_stack jo_L_static BOTJ RUN_bot jo_L_stackA jo_L_sb jo_L_hull_eq
jo_SM 4096 (DFs_jo RC.rc_canary LV) jo_L_sm jo_L_sm_stack
jo_SIVS jo_L_sivs_cover jo_L_sivs_data jo_L_scratch jo_IMG_errno_any jo_L_rstat_priv jo_L_scratch_data
(stat_client L BOTJ TOPJ jo_STATC jo_L_statc_priv)
jo_SD jo_SD_stack jo_RL jo_RL_stack (DT2_jo_closed RC.rc_canary LV) jo_L_strdup jo_L_realloc jo_L_t2_stack
TOPJ RUN_topj RUN_baux jo_top_re jo_STATC (stat_cells L BOTJ TOPJ jo_STATC) jo_L_rtc_all jo_L_sb_cells
(stat_static L BOTJ TOPJ jo_STATC DL jo_L_sb RUN_bot LA LV PERM0 TMAX NMAX hs_LL0 hs_segs hs_low RE DCo FR0 hs_froff S BAUX RC.rc_canary eq_refl eq_refl jo_L_can_got jo_L_can_guard jo_L_can_copy jo_L_need_locks)
jo_free2_null (proj2 RUN_botj) jo_L_img_lo_small.

End Jo.
