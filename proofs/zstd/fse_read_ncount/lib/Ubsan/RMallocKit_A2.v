(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free MallocTree MallocKit_A MallocKit_AB.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Export MallocKit_A2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require KStep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMalloc_fp.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.
#[using="Hconc"] Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.
#[using="Hmetas"] Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.
#[using="P HP Hconc"] Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.
#[using="P HP Hconc Hctx"] Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof.
intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
assert (E1 : rctx_head_cells st' = rctx_head_cells st).
{ unfold rctx_head_cells, rsecw. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
{ unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.
#[using="P HP Hconc Hmetas"] Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof.
intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
destruct (H9 a ar Ha) as [Pa Pn].
unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.
#[using="P HP Hconc"] Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof.
intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.
#[using="Type"] Lemma rbytes_at_agree m m' A bs : bytes_at usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at usegs m' A bs.
Proof.
intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold mrd. Local Ltac2 Set LiaHints.tbl := fun () => "0010>23517522163.11000004S2Hi".
rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rwr_at_agree m m' A n : wr_at usegs m A n -> agree_on m m' A n -> wr_at usegs m' A n.
Proof.
intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold wview. Local Ltac2 Set LiaHints.tbl := fun () => "0010>51696475855.11000004S2Hi".
rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rrw_cells_agree m m' A cs : rw_cells usegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells usegs m' A cs.
Proof.
intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply rwr_at_agree; eauto.
Qed.
#[using="Type"] Lemma ru64arr_agree m m' A ws : u64arr usegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr usegs m' A ws.
Proof.
intros [HB HW] AG. split.
- eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. Local Ltac2 Set LiaHints.tbl := fun () => "0010=47196626702.8000001S".
replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply rwr_at_agree; [exact HW|]. exact AG.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ru8arr_agree m m' A bs : u8arr usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr usegs m' A bs.
Proof. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.
#[using="Type"] Lemma rmrep_agree : forall st m m',
rmrep st m ->
agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x418 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 ->
(forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
rmrep st m'.
Proof.
intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGA AGG AGR.
split; [exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold RLIBC, RCTX in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact C1|]. Local Ltac2 Set LiaHints.tbl := fun () => "00N0>11975433144.2112818127403.3014226938624.2415695071912.2118486167351.2120380452209.2620884180337.262308380449.24 24239863711.2427403712881.2628207167223.2130609631268.3031421950360.2633996841880.264134277774.26 42002724356.2442661237559.2144459413361.2644964381608.2145013491368.2145272792472.2645665994261.2649911400209.2651851436650.2652153901149.26657468072.21  6831527281.26 7029766762.26 720406327.21  8509455175.21 00000100500600700800E00R00S00T00a00b00f01301@01M01N01O01\01]01^01k01o02<02I02M02N02[02h02i02jSS2HoSSSS2L12L22L32L4S2L12L22L32L4SSS2L12L22L32L4SS2HoS2L12L22L32L4S2L12L22L32L4S2L12L22L32L4SSS2L12L22L32L4SSS2L12L22L32L4S2HkS2L12L22L32L4S2L12L22L32L4S2HkSS2L12L22L32L4S2L12L22L32L4SS".
eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
split; [|split; [|split; [|split]]].
+ eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
- intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
split; [|split].
+ eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
+ intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
+ eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).
Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= ATOP.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).
#[using="Type"] Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite rnr_regions. apply lookup_insert_eq. Qed.
#[using="r0"] Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
intros H. destruct (N.eq_dec q rid) as [->|NE].
- left. rewrite rnr_lookup_new in H. inversion H. auto.
- right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
#[using="r0"] Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
#[using="rc st m' rid L ZF"] Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0020>26406869192.23623840791.23  000001002SS".
destruct k; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc rid RF"] Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>10651169430.2850715972057.28000003006S1HS1H".
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="m m' rid L r0 MR PT X0 XA LEN XC RF ZF"] Lemma rnr_regions_wf : rregions_wf st'.
Proof.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RFimg : ranges_free ref_reserved x L = true).
{ apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite (rstatics_reserved _ RS). exact HI. }
split; [exact RS|]. split; [|split; [|split]].
- intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+ unfold r0. cbn. fold L. Local Ltac2 Set LiaHints.tbl := fun () => "0070>10719459035.3117080226137.3918033365813.3118773509442.3149526293456.3956095916220.3162207566392.3100000400:00;00@00F00J00NS2XAS1H2H0FS3LENS1H2H0S2X0S2XC".
repeat split; try lia. exact RFimg.
+ exact (WR q r H).
- intros q1 r1 q2 r2 H1 H2 NE.
destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists r. rewrite rnr_lookup_old by exact Pa. auto.
- intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="m rid L r0 MR PT FRs X0 XA LEN XC RF AG ZF"] Lemma rmrep_new_region : rmrep st' m'.
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
{ intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite (rstatics_reserved _ RS). exact HI. }
pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
pose proof (round_up_pg_ge len) as LG. fold L in LG. atop_facts.
assert (MR1 : rmrep st m').
{ eapply rmrep_agree; [exact MR| | | | | | |].
- intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "00@0>12061084937.522363779058.49 2363779058.55 2363779058.56 2438520923.51 25398462548.534409511471.48 47011428444.5150384998011.4156093675997.4856765667309.4157019993822.5165438330304.4965438330304.5565438330304.568992053401.50 00000400E00c01A01H01L01V01c01o02302702802B02W02h02lS2HoS5ATOPR3Ha02B02BCS5ATOPR3Ha02Cb3Sb03Sb13RB03RBCS5ATOPR3Ha02Ca3Sa03Sa13RB03RBCS2X02HoS2HiS2XC5ATOPRS2XC5ATOPR2HoS3RI32Ha3RI2S2X0S2HaSS3Ha01H2H0S3Ha02Cb3Sb03Sb11H2H0S3Ha02Ca3Sa11H2H0S2Hi".
apply AG; unfold RMLOCK in *; lia.
- intros a Ha. apply AG; unfold RLIBC in *; lia.
- intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
- intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
- intros a ar Ha a0 Ha0.
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
atop_facts. apply AG; lia.
- intros b gh Hb a0 Ha0.
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). atop_facts. apply AG; lia.
- intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). atop_facts.
pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
- eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
- intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
- intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
- intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+
cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
split.
* split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
* intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
+ eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End NEWREGION.
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
(RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x418 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
\/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
m' (wa a) = m (wa a).
#[using="Type"] Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
- rewrite lookup_delete_eq in H. discriminate.
- rewrite lookup_delete_ne in H by congruence. auto.
Qed.
#[using="Type"] Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="m r MR Hr PT AG"] Lemma rmrep_drop_region : rmrep st' m'.
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). atop_facts.
assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
split; [|split; [|split; [|split; [|split]]]].
-
split; [exact RS|]. split; [|split; [|split]].
+ intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
+ intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
+ intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists ra. rewrite rdr_lookup_old by exact Pa. auto.
+ intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists rb. rewrite rdr_lookup_old by exact Pb. auto.
-
eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x1d000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x1d000 \/ 0x50000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ Local Ltac2 Set LiaHints.tbl := fun () => "00Z0>1141365109.38 1141365109.43 1350490947.36 1350490947.41 13810226248.4914226941244.5120382645184.4220886074304.422308385053.51 2361675378.42 2361675378.49 2361675378.50 24239851939.5125928405048.4225928405048.4925928405048.502736392884.36 2736392884.41 27401390016.4227682316668.502810811353.38 2810811353.43 31420028713.4233998888233.4237856360665.384132400191.42 42002712632.514323575805.53 43295456921.4944457505216.4245270467369.4249097616537.3849909135776.4251853483227.4252155998208.5353660854600.4956765667309.3856765667309.4360743538393.3861553444585.426829616064.42 7031932123.42 00000:00P00S00b00f00g01401A01B01T02202P02Q02\02m03B03K03`03m04@04D04H04U04b04f05305405905G05T05a05e06206?06D06H06L06P06T06\06i076S2H02DD2HaS2L12L22L32L42H02DD2HaS1eS2L12L22L32L41eS2HoSS2L12L22L32L4S2L12L22L32L4SS5ATOPR2Bq3BCq3Ha0S5ATOPR2Ca3Sa03Sa13RB03RBC3Ha0S5ATOPR2Cb3Sb03Sb13RB03RBC3Ha0SS2H02H23Ha0S2Ca3Sa11H2H03Ha0S2Cb3Sb03Sb11H2H13Ha0S3RL01H1nS3RL02L12L22L32L41H1nS2L12L22L32L4S2Cb3Sb03Sb12H13Ha0S2HaS2HaS2L12L22L32L4S2L12L22L32L4S2HaS2L12L22L32L4SS3Hk0S2Ca3Sa11H3Ha0S2L12L22L32L4S2L12L22L32L4S2HaS2L12L22L32L4S2L12L22L32L4S3Hk0S2HoS2HaS2HaS2HaS2H23Ha0S2L12L22L32L4S2L12L22L32L4".
destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
assert (AGC : agree_on m m' RLIBC 0x418).
{ intros a Ha. unfold RLIBC in Ha. apply AG; [lia| lia| right; left; unfold RLIBC; lia]. }
unfold RLIBC, RCTX in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x1d000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x1d000 \/ 0x50000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
split; [|split; [|split; [|split]]].
+ eapply rrw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; lia].
+ eapply rrw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
+ eapply rrw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
- intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). atop_facts.
assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
assert (AGA : agree_on m m' (conc st a) 4096).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
+ eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
+ intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
+ eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
- intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). atop_facts.
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
- intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
destruct (WR q rq H) as (Bq & _ & _ & BCq & _). atop_facts.
pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
destruct (SH q rq H Hk) as [HWr HB]. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof.
intros [T1 T2]. split.
- intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
- intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.
#[using="Type"] Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
rmrep st m -> (s_groups st) !! b = None ->
(s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
rw_cells usegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
rmrep (put_group b (Some g) ai st) m.
Proof.
intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
pose proof WF as (RS & WR & DJ & WA & WG).
split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
- split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
+ rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
- intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
+ rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.
#[using="Type"] Lemma rmrep_set_mmap_counter : forall st m v,
rmrep st m -> 0 <= v < 2^32 ->
rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof.
intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le4 (wz v)) as L4.
Local Ltac2 Set LiaHints.tbl := fun () => "0090>11805580453.1312714926104.1614161391384.1622952405272.1636105752344.1638523358648.1340791864600.1643091896157.1668058738381.1300000400500600700800<00=00>00BS2L4SSSSS2L4SSS2L4".
pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
pose proof (wmono_write usegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl usegs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
- left.
pose proof (rw_cells_write usegs m RCTX (rctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
unfold rctx_head_cells, rsecw, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
