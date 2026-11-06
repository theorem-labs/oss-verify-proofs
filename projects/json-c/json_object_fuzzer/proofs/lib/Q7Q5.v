(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mremap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbrW QlEo_c1 Q5Rg QWxq_c1 QRjH Qn1e QiVh QSpR Qnhz QuJV QZAi QUZl Q7S0 Qfya QYTG Ql2m QGeV QeZD QkRc QqWy QyuL QvVk QOnw Q6q3 EdEvNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap.
Import QsjA QEpW QZDE QbrW QlEo_c1.Mq0 Q5Rg.Mq0.

Import QRjH.
Import Qn1e.Mq1.
Import QiVh.
Import QSpR.Mq2.
Import Qnhz.Mq1.
Import QuJV.Mq1.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QYTG.Mq0 Ql2m.Mq3 QGeV.
Import QeZD QkRc QqWy.Mq0 QyuL.Mq0 QvVk.Mq0 QOnw.
Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Ltac lia ::= klia. Ltac mkr__lia_0 := klia.
Ltac nia ::= knia. Ltac mkr__nia_1 := knia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma m_vmmaps_mremap_next : forall mo old on dst nn,
m_vmmaps (mremap_model_next mo old on dst nn) = mremap_maps_next (m_vmmaps mo) old dst nn.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma m_halted_mremap_next : forall mo old on dst nn, m_halted (mremap_model_next mo old on dst nn) = m_halted mo.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma m_vm_lazy_mremap_next : forall mo old on dst nn,
m_vm_lazy mo = [] -> m_vm_lazy (mremap_model_next mo old on dst nn) = [].
Proof.
intros mo old on dst nn H. unfold mremap_model_next, mremap_source_lazy_b, vm_resize_backing, with_vm_backing.
rewrite with_vmmaps_lazy', H. unfold m_vm_lazy. cbn [m_vm vmst_lazy map_contains existsb]. rewrite !maps_subtract_nil. reflexivity.
Qed.
#[using="Type"] Lemma vm_only_mremap_next : forall mo old on dst nn, vm_only mo (mremap_model_next mo old on dst nn).
Proof.
intros. unfold mremap_model_next, vm_resize_backing.
eapply vm_only_trans; [| apply vm_only_with_vm_backing]; apply vm_only_with_vmmaps; reflexivity.
Qed.

#[using="Type"] Lemma ranges_free_except_sub : forall a l lo len lo' len',
ranges_free_except a l lo len = true -> lo <= lo' -> lo' + len' <= lo + len -> 0 <= len' ->
ranges_free_except a l lo' len' = true.
Proof.
intros a l lo len lo' len' H H1 H2 H3. unfold ranges_free_except in *.
apply forallb_forall. intros [b m] Hin. pose proof (proj1 (forallb_forall _ _) H _ Hin) as X. cbn [fst snd] in *.
destruct (b =? a); [reflexivity|]. cbn [orb] in *. unfold iv_disjoint in *.
apply orb_true_iff in X. apply orb_true_iff. destruct X as [X|X]; apply Z.leb_le in X; [left| right]; apply Z.leb_le; lia.
Qed.

#[using="Type"] Lemma ranges_free_except_of_free : forall a l lo len,
ranges_free l lo len = true -> ranges_free_except a l lo len = true.
Proof.
intros a l lo len H. unfold ranges_free, ranges_free_except in *.
apply forallb_forall. intros bm Hin. pose proof (proj1 (forallb_forall _ _) H _ Hin) as X. rewrite X. apply orb_true_r.
Qed.

#[using="Type"] Lemma maps_entry_at : forall L pbrk mo a l0 e,
KL L pbrk mo -> In (a, l0) (ld_groups L) -> In e (vm_maps (m_vmmaps mo)) ->
fst e = wz a -> e = went a (mmap_len l0).
Proof.
intros L pbrk mo a l0 e HK Hin He Efst.
pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He B4) as [E|D]; [exact E|].
pose proof (proj1 (kl_wf _ _ _ HK) e He) as W. unfold edisj in D. rewrite B5, B6 in D.
unfold elo, ehi in D, W. rewrite Efst in D, W. rewrite unsigned_wz in D, W by lia. lia.
Qed.

#[using="Type"] Lemma KL_mremap_new : forall L pbrk mo mo' a l0 dst nl,
KL L pbrk mo -> brk_quiet L -> In (a, l0) (ld_groups L) ->
0 < nl < LEN_MAX -> nl mod PGSZ = 0 ->
0 < dst -> dst mod PGSZ = 0 -> dst + nl <= alloc_ceiling ->
let h := m_vmmaps mo in
region_free (vm_reserved h ++ map_remove (vm_maps h) (wz a)) (wz dst) (wz nl) = true ->
m_halted mo' = None -> m_vm_lazy mo' = [] ->
m_vmmaps mo' = mremap_maps_next h (wz a) (wz dst) (wz nl) ->
KL (set_groups ((dst, nl) :: g_remove a (ld_groups L)) L) pbrk mo'
/\ ranges_free_except a (lranges L) dst nl = true.
Proof.
intros L pbrk mo mo' a l0 dst nl HK Hq Hin Hnl Hnal Hd0 Hdal Hdc h Hrf Hh' Hl' Evm.
pose proof alloc_ceiling_lt as Hcl.
pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
set (n := mmap_len l0) in *.
assert (Hnn : mmap_len nl = nl) by (apply mmap_len_of_aligned; [lia| unfold PGSZ in Hnal; exact Hnal]).
assert (Ua : bv_unsigned (wz a) = a) by (apply unsigned_wz; lia).
assert (Ud : bv_unsigned (wz dst) = dst) by (apply unsigned_wz; lia).
assert (Unl : bv_unsigned (wz nl) = nl) by (apply unsigned_wz; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm. pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
pose proof (fun b0 l1 H => went_In_bounds _ _ _ b0 l1 HK H) as WB.

pose proof (kl_distinct _ _ _ HK) as Kd.
destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
{ intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
{ intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }

assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> wz a).
{ intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
assert (Dgm : forall b0 l1, (In (b0, l1) (ld_groups L) \/ exists k, In (b0, l1, k) (ld_metas L)) -> b0 <> a ->
In (went b0 (mmap_len l1)) (map_remove (vm_maps h) (wz a)) /\ (dst + nl <= b0 \/ b0 + mmap_len l1 <= dst)).
{ intros b0 l1 H Hne. pose proof (WB b0 l1 H) as (C1 & C2 & C3 & C4 & C5 & C6).
assert (HinR : In (went b0 (mmap_len l1)) (map_remove (vm_maps h) (wz a))) by (apply In_map_remove; split; [exact C4| apply Kfst; lia]).
split; [exact HinR|]. pose proof (region_free_disj _ _ _ _ Hrfm HinR) as D. rewrite C5, C6, Ud, Unl in D. exact D. }

assert (Kne : forall e, In e (vm_maps h) -> e <> went a n -> In e (map_remove (vm_maps h) (wz a))).
{ intros e He Hne. apply In_map_remove. split; [exact He|]. intros Efst. apply Hne. exact (maps_entry_at _ _ _ _ _ _ HK Hin He Efst). }
assert (Rcov' : forall b0 l1, ld_brkreg L = Some (b0, l1) -> wcov (map_remove (vm_maps h) (wz a)) (b0 + PGSZ) (b0 + l1)).
{ intros b0 l1 E z Hz. pose proof (kl_brkreg _ _ _ HK b0 l1 E) as (R1 & R2 & R3 & R4 & R5 & Rcov). destruct (Rcov z Hz) as (e & He & Hr).
exists e. split; [| exact Hr]. apply (Kne _ He). intros ->. rewrite B5, B6 in Hr. pose proof (A6 b0 l1 E). lia. }
assert (Dbrk : forall b0 l1, ld_brkreg L = Some (b0, l1) -> dst + nl <= b0 + PGSZ \/ b0 + l1 <= dst).
{ intros b0 l1 E. pose proof (kl_brkreg _ _ _ HK b0 l1 E) as (R1 & R2 & R3 & R4 & R5 & _).
pose proof (wcov_rf_disj _ _ _ _ _ (Rcov' b0 l1 E) Hrfm ltac:(rewrite Unl; lia) ltac:(clear -R3; lia)) as D. rewrite Ud, Unl in D. exact D. }
assert (Dna : forall e, In e (vm_noaccess h) -> dst + nl <= elo e \/ ehi e <= dst).
{ intros e He. destruct (kl_na _ _ _ HK e He) as (W & [(b0 & l1 & k & Hin0 & X1 & X2) | (b0 & l1 & E & X1 & X2 & X3)]).
- pose proof (Dgm b0 l1 (or_intror (ex_intro _ k Hin0)) (Hm' _ _ _ Hin0)) as [_ D]. lia.
- pose proof (kl_brkreg _ _ _ HK b0 l1 E) as (R1 & R2 & R3 & _).
assert (HinR : In (went b0 (2 * PGSZ)) (map_remove (vm_maps h) (wz a))).
{ apply (Kne _ X3). intros EG. pose proof (f_equal elo EG) as E1. pose proof (f_equal ehi EG) as E2.
rewrite B5, elo_went in E1 by lia. rewrite B6, ehi_went in E2 by lia. pose proof (A6 b0 l1 E). lia. }
pose proof (region_free_disj _ _ _ _ Hrfm HinR) as D. rewrite Ud, Unl in D. rewrite elo_went, ehi_went in D by lia. lia. }
split.
2:{ unfold ranges_free_except. apply forallb_forall. intros [b0 m0] Hin0. cbn [fst snd].
destruct (Z.eqb_spec b0 a) as [|Hne]; [reflexivity|]. cbn [orb]. unfold iv_disjoint.
enough (dst + nl <= b0 \/ b0 + m0 <= dst) as D.
{ destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
apply In_lranges in Hin0 as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
- rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
pose proof (region_free_In _ _ _ _ _ Hrfr H) as D. unfold iv_overlap in D. rewrite Ud, Unl in D.
destruct (Z.ltb_spec dst (bv_unsigned e + bv_unsigned sz)); destruct (Z.ltb_spec (bv_unsigned e) (dst + nl)); cbn in D; try discriminate; lia.
- injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l1). exact (proj2 (Dgm b1 l1 (or_introl H) Hne)).
- injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l1). exact (proj2 (Dgm b1 l1 (or_intror (ex_intro _ k H)) (Hm' _ _ _ H))).
- injection E as -> ->. pose proof (kl_brkreg _ _ _ HK b1 l1 H) as (R1 & R2 & R3 & R4 & R5 & _).
rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b1 l1 H). unfold PGSZ in *. lia. }
assert (Hnotin : ~ In dst (map fst (g_remove a (ld_groups L)) ++ map (fun m => fst (fst m)) (ld_metas L))).
{ intros HinD. apply in_app_or in HinD as [HinD|HinD].
- apply in_map_iff in HinD as ([b0 l1] & E & HinD). cbn in E. subst b0. destruct (Hg' _ _ HinD) as [Hin1 Hne].
pose proof (WB dst l1 (or_introl Hin1)) as (C1 & C2 & _). pose proof (Dgm dst l1 (or_introl Hin1) Hne) as [_ D]. lia.
- apply in_map_iff in HinD as ([[b0 l1] k] & E & HinD). cbn in E. subst b0.
pose proof (WB dst l1 (or_intror (ex_intro _ k HinD))) as (C1 & C2 & _). pose proof (Dgm dst l1 (or_intror (ex_intro _ k HinD)) (Hm' _ _ _ HinD)) as [_ D]. lia. }
pose proof HK as HK0. kl_open HK. clear Kstart.
set (L' := set_groups ((dst, nl) :: g_remove a (ld_groups L)) L).
assert (Hph' : phase_inv (ld_brk L') L' pbrk mo').
{ eapply phase_quiet; [exact HK0| exact Hq| reflexivity| reflexivity| |]; rewrite Evm; reflexivity. }
subst L'. constructor; try exact Hph'; rewrite ?Evm; unfold mremap_maps_next;
cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
- apply vmwf_cons; [apply vmwf_remove; exact Kwf| rewrite Ud, Unl; lia| exact Hrfm].
- pose proof (kl_start _ _ _ HK0). tauto.
- intros b0 l1 [E|Hin0].
+ injection E as <- <-. rewrite Hnn. unfold brk_disj; cbn [ld_brkreg set_groups]. splits; try lia; try (left; reflexivity); try exact Dbrk.
apply region_free_intro. intros e He. rewrite Ud, Unl. apply Dna. exact He.
+ destruct (Hg' _ _ Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7).
unfold brk_disj in *; cbn [ld_brkreg set_groups]. splits; auto. right. exact (proj1 (Dgm b0 l1 (or_introl Hin1) Hne)).
- intros b0 l1 [E|Hin0]; [| apply Kgrr; exact (proj1 (Hg' _ _ Hin0))]. injection E as <- <-. rewrite Hnn. exact Hrfr.
- intros b0 l1 k Hin0. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold brk_disj in *; cbn [ld_brkreg set_groups]. splits; auto. right. exact (proj1 (Dgm b0 l1 (or_intror (ex_intro _ k Hin0)) (Hm' _ _ _ Hin0))).
- cbn [map fst app]. constructor; [exact Hnotin| rewrite Ezz, map_app, <- app_assoc; exact Kd1].
- intros e He. destruct (Kna e He) as (W & [(b0 & l1 & k & Hin0 & X) | (b0 & l1 & E & X1 & X2 & X3)]); split; try exact W.
+ left. exists b0, l1, k. auto.
+ right. exists b0, l1. splits; auto. right. apply (Kne _ X3). intros EG.
pose proof (f_equal elo EG) as E1. pose proof (f_equal ehi EG) as E2. pose proof (Kreg b0 l1 E) as (R1 & R2 & R3 & _).
rewrite B5, elo_went in E1 by lia. rewrite B6, ehi_went in E2 by lia. pose proof (A6 b0 l1 E). lia.
- intros b0 l1 E. specialize (Kreg b0 l1 E) as KR. destruct KR as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
eapply wcov_mono; [| exact (Rcov' b0 l1 E)]. intros e He; right; exact He.
Qed.

#[using="Type"] Lemma wz_add : forall x y, 0 <= x -> 0 <= y -> x + y < 2^64 -> (wz x + wz y)%bv = wz (x + y).
Proof. intros. unfold wz. apply lit_add_lit. Qed.

#[using="Type"] Lemma page_align_is0_false : forall x, 0 < x -> x mod 4096 = 0 -> x < 2^64 -> page_align_is0_b (wz x) = false.
Proof.
intros x Hx Hal Hlt. unfold page_align_is0_b, w_is0. rewrite unsigned_wz by lia. fold (mmap_len x). rewrite mmap_len_of_aligned by lia.
replace (bv_eqb (wz x) (Z_to_bv 64 0)) with false.
2:{ symmetry. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite unsigned_wz in E by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
cbn [orb]. apply Z.leb_gt. unfold two_pow_64. lia.
Qed.

#[using="Type"] Lemma region_free_incl : forall maps maps' a n,
(forall e, In e maps' -> In e maps) -> region_free maps a n = true -> region_free maps' a n = true.
Proof. intros maps maps' a n Hs H. apply region_free_intro. intros e He. eapply region_free_disj; [exact H| apply Hs; exact He]. Qed.

Section Ev.
Variable segs : list Segment.

#[using="Type"] Lemma ev1_mremap : forall L pbrk md ms1 (J : config -> Prop) a l0 ol nl fl,
NClosed segs J -> KL L pbrk md -> brk_quiet L -> fl = MREMAP_MAYMOVE -> 0 < nl < TWO64 -> nl mod PGSZ = 0 ->
In (a, l0) (ld_groups L) -> ol = round_up_pg l0 -> nl <> ol ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMremap a ol nl fl) ms1 ->
(forall rsp z md',
ev_dec (EMremap a ol nl fl) pbrk rsp = Some z -> answer_ok L (EMremap a ol nl fl) z = true ->
KL (event_post L (EMremap a ol nl fl) z) (ps_brk (ev_post_state (EMremap a ol nl fl) rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Proof.
intros L pbrk md ms1 J a l0 ol nl fl HJ HK Hq -> Hnl Hnal Hin Hol Hne Hat HC.
destruct Hat as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3).
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy. pose proof alloc_ceiling_lt as Hcl.
rewrite round_up_pg_eq in Hol. fold (mmap_len l0) in Hol. subst ol.
pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
pose proof (kl_gresv _ _ _ HK a l0 Hin) as A8.
pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
pose proof (mmap_len_aligned l0) as Hnal0. linearize_mods.
set (n := mmap_len l0) in *.
assert (Hn1 : l0 <= n < l0 + 4096) by (apply mmap_len_ge; lia).
assert (Hnn : mmap_len n = n) by (apply mmap_len_of_aligned; lia).
assert (Hnln : mmap_len nl = nl) by (apply mmap_len_of_aligned; lia).
assert (Ua : bv_unsigned (wz a) = a) by (apply unsigned_wz; lia).
assert (Un : bv_unsigned (wz n) = n) by (apply unsigned_wz; lia).
assert (Unl : bv_unsigned (wz nl) = nl) by (apply unsigned_wz; lia).
set (h := m_vmmaps md) in *.

set (i := sys_input segs ms1 (Z_to_bv 64 216)).
assert (E0 : in_arg i 0 = wz a) by (transitivity (ms_gpr ms1 0); [reflexivity|]; rewrite ms_gpr_areg0; exact Ha0).
assert (E1 : in_arg i 1 = wz n) by (transitivity (ms_gpr ms1 1); [reflexivity|]; rewrite ms_gpr_areg1; exact Ha1).
assert (E2 : in_arg i 2 = wz nl) by (transitivity (ms_gpr ms1 2); [reflexivity|]; rewrite ms_gpr_areg2; exact Ha2).
assert (E3 : in_arg i 3 = wz MREMAP_MAYMOVE) by (transitivity (ms_gpr ms1 3); [reflexivity|]; rewrite ms_gpr_areg3; exact Ha3).
assert (Hflags : bv_unsigned (wz MREMAP_MAYMOVE) = Uapi.MREMAP_MAYMOVE) by reflexivity.
assert (Hal : bv_unsigned (wz a) mod page_size = 0) by (rewrite Ua, page_size_eq; lia).
assert (Hnew : page_align_is0_b (wz nl) = false) by (apply page_align_is0_false; lia).
assert (Hold : page_align_is0_b (wz n) = false) by (apply page_align_is0_false; lia).
assert (Ron : page_round_up_Z (bv_unsigned (wz n)) = n) by (rewrite Un; exact Hnn).
assert (Rnl : page_round_up_Z (bv_unsigned (wz nl)) = nl) by (rewrite Unl; exact Hnln).
assert (Hsrc : mremap_source_b h (wz a) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (wz n)))) (page_round_up_Z (bv_unsigned (wz n))) = true).
{ rewrite Ron. unfold mremap_source_b. unfold h at 1. rewrite Ua, (kl_ceil _ _ _ HK), (proj2 (Z.leb_le _ _) A4). fold (wz n).
change (region_free (vm_reserved h) (wz a) (wz n)) with (region_free (vm_reserved h) (wz a) (wz (mmap_len l0))). rewrite A8.
rewrite (map_has_intro _ _ _ A5).
change (region_free (vm_noaccess h) (wz a) (wz n)) with (region_free (vm_noaccess h) (wz a) (wz (mmap_len l0))). rewrite A7. reflexivity. }
assert (Hunif : mremap_backing_uniform_b md (wz a) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (wz n)))) = true).
{ unfold mremap_backing_uniform_b. unfold h in Hlazy. rewrite Hlazy. reflexivity. }
assert (SPEC : forall o, Specs.syscall_spec i md o <-> mremap_spec (wz a) (wz n) (wz nl) (wz MREMAP_MAYMOVE) i md o).
{ intros o. unfold i. rewrite (syscall_spec_216 _ md o) by reflexivity. fold i. rewrite E0, E1, E2, E3. reflexivity. }

assert (DECerr : forall e, e = 12 ->
ev_dec (EMremap a n nl MREMAP_MAYMOVE) pbrk (mkEffect (errno_ret e) [] []) = Some (neg_errno e)).
{ intros e He. cbn -[errno_of neg_errno errno_ret]. rewrite errno_of_errno_ret by lia. rewrite He. reflexivity. }
assert (ERR : forall e, In e mremap_errnos -> J (mkCfg (nret ms1 (mkEffect (errno_ret e) [] [])) md)).
{ intros e He. assert (E12 : e = 12) by (destruct He as [<-|[]]; reflexivity). assert (Her : 1 <= e <= 4095) by lia.
apply (HC (mkEffect (errno_ret e) [] []) (neg_errno e) md).
- apply DECerr. exact E12.
- cbn [answer_ok]. unfold mremap_answer_ok. rewrite is_errno_form_neg by lia. reflexivity.
- cbn [ev_post_state ps_brk event_post]. rewrite is_errno_form_neg by lia. exact HK.
- apply vm_only_refl. }
assert (NEa : is_errno_form a = false).
{ unfold is_errno_form, TWO64. apply Bool.andb_false_iff. left. apply Z.leb_gt. lia. }
destruct (Z.lt_ge_cases nl n) as [Hlt|Hge].
-
pose (I := ({e : Z | In e mremap_errnos} + unit)%type).
pose (effs := fun x : I => match x with
| inl (exist _ e _) => mkEffect (errno_ret e) [] []
| inr _ => mkEffectU (wz a) [] [] [((wz a + wz nl)%bv, Z_to_bv 64 (n - nl))] [] [] end).
pose (ms' := fun x : I => match x with inl _ => md | inr _ => mremap_model_next md (wz a) (wz n) (wz a) (wz nl) end).
apply (EdEvNode.ncl_spec_family segs J ms1 md (Z_to_bv 64 216) I effs ms' (inr tt) HJ Hh Hsvc).
+ intros o. fold i. rewrite SPEC, (mremap_shrink_outcome (wz a) (wz n) (wz nl) (wz MREMAP_MAYMOVE) i md Hflags Hal Hnew Hold Hsrc Hunif o)
by (rewrite Ron, Rnl; exact Hlt).
unfold mremap_err_out. rewrite Ron, Rnl. fold (wz n) (wz nl). split.
* intros [(e & He & ->) | ->]; [exists (inl (exist _ e He))| exists (inr tt)]; reflexivity.
* intros [[[e He]|[]] ->]; [left; exists e; auto| right; reflexivity].
+ intros [[e He]|[]]; cbn [ms']; [exact Hh| rewrite m_halted_mremap_next; exact Hh].
+ intros [[e He]|[]]; cbn [ms']; [exact Hlazy| apply m_vm_lazy_mremap_next; exact Hlazy].
+ intros [[e He]|[]]; cbn [effs ms']; [apply ERR; exact He|].
assert (Hrf : region_free (vm_reserved h ++ map_remove (vm_maps h) (wz a)) (wz a) (wz nl) = true).
{ apply region_free_intro. intros e He. rewrite Ua, Unl. apply in_app_or in He as [He|He].
- pose proof (region_free_disj _ _ _ _ A8 He) as D. rewrite Ua, unsigned_wz in D by lia. lia.
- apply In_map_remove in He as [He Hfe].
destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [E|D]; [exfalso; apply Hfe; rewrite E; reflexivity|].
unfold edisj in D. rewrite B5, B6 in D. lia. }
destruct (KL_mremap_new L pbrk md (mremap_model_next md (wz a) (wz n) (wz a) (wz nl)) a l0 a nl HK Hq Hin ltac:(lia)
ltac:(unfold PGSZ; lia) ltac:(lia) ltac:(unfold PGSZ; lia) ltac:(lia) Hrf
ltac:(rewrite m_halted_mremap_next; exact Hh) ltac:(apply m_vm_lazy_mremap_next; exact Hlazy)
ltac:(rewrite m_vmmaps_mremap_next; reflexivity)) as [HK' _].
apply (HC _ a).
* cbn [ev_dec]. unfold dec_mremap. cbn [errno_of].
rewrite (errno_of_small (wz a)) by (rewrite Ua; lia).
rewrite bv_eqb_refl. rewrite (proj2 (Z.ltb_lt _ _) Hlt). rewrite wz_add by lia. unfold wa. fold (wz (a + nl)). rewrite !bv_eqb_refl. reflexivity.
* cbn [answer_ok]. unfold mremap_answer_ok. rewrite NEa, Z.eqb_refl. rewrite !round_up_pg_eq. fold (mmap_len nl) (mmap_len n). rewrite Hnln, Hnn.
rewrite (proj2 (Z.leb_le nl n)) by lia. reflexivity.
* cbn [ev_post_state ps_brk event_post]. rewrite NEa. exact HK'.
* apply vm_only_mremap_next.
-
assert (Hlt : n < nl) by lia.
pose (I := ({e : Z | In e mremap_errnos}
+ ({u : unit | mremap_inplace_grow_b md (wz a) (wz n) (wz nl) n nl = true}
+ {dst : word | mremap_fresh_b md n nl (wz a) (wz n) dst (wz nl) = true}))%type).
pose (effs := fun x : I => match x with
| inl (exist _ e _) => mkEffect (errno_ret e) [] []
| inr (inl _) => mkEffect (wz a) [] [((wz a + wz n)%bv, Z_to_bv 64 (nl - n))]
| inr (inr (exist _ dst _)) =>
mkEffectU dst [] [((dst + wz n)%bv, Z_to_bv 64 (nl - n))] [(wz a, wz n)] [mkCopy (wz a) dst (wz n)] [] end).
pose (ms' := fun x : I => match x with
| inl _ => md
| inr (inl _) => mremap_model_next md (wz a) (wz n) (wz a) (wz nl)
| inr (inr (exist _ dst _)) => mremap_model_next md (wz a) (wz n) dst (wz nl) end).
apply (EdEvNode.ncl_spec_family segs J ms1 md (Z_to_bv 64 216) I effs ms' (inl (exist _ ENOMEM ENOMEM_in_mremap_errnos)) HJ Hh Hsvc).
+ intros o. fold i. rewrite SPEC, (mremap_grow_outcome (wz a) (wz n) (wz nl) (wz MREMAP_MAYMOVE) i md Hflags Hal Hnew Hold Hsrc Hunif o)
by (rewrite Ron, Rnl; exact Hlt).
unfold mremap_grow_out, mremap_err_out. rewrite Ron, Rnl. fold (wz n) (wz nl). fold h. split.
* intros [(e & He & ->) | [(Hok & ->) | (dst & Hd & ->)]];
[exists (inl (exist _ e He))| exists (inr (inl (exist _ tt Hok)))| exists (inr (inr (exist _ dst Hd)))]; reflexivity.
* intros [[[e He]|[[u Hu]|[dst Hd]]] ->]; [left; exists e; auto| right; left; auto| right; right; exists dst; auto].
+ intros [[e He]|[[u Hu]|[dst Hd]]]; cbn [ms']; [exact Hh| rewrite m_halted_mremap_next; exact Hh| rewrite m_halted_mremap_next; exact Hh].
+ intros [[e He]|[[u Hu]|[dst Hd]]]; cbn [ms']; [exact Hlazy| apply m_vm_lazy_mremap_next; exact Hlazy| apply m_vm_lazy_mremap_next; exact Hlazy].
+ intros [[e He]|[[u Hu]|[dst Hd]]]; cbn [effs ms']; [apply ERR; exact He| |].
*
unfold mremap_inplace_grow_b in Hu. fold h in Hu. apply andb_prop in Hu as [Hu _]. apply andb_prop in Hu as [G1 Hrf].
apply Z.leb_le in G1. rewrite Ua in G1. unfold h in G1. rewrite (kl_ceil _ _ _ HK) in G1.
destruct (KL_mremap_new L pbrk md (mremap_model_next md (wz a) (wz n) (wz a) (wz nl)) a l0 a nl HK Hq Hin ltac:(lia)
ltac:(unfold PGSZ; lia) ltac:(lia) ltac:(unfold PGSZ; lia) G1 Hrf
ltac:(rewrite m_halted_mremap_next; exact Hh) ltac:(apply m_vm_lazy_mremap_next; exact Hlazy)
ltac:(rewrite m_vmmaps_mremap_next; reflexivity)) as [HK' RFE].
apply (HC _ a).
-- cbn [ev_dec]. unfold dec_mremap. rewrite (errno_of_small (wz a)) by (rewrite Ua; lia).
rewrite bv_eqb_refl. rewrite (proj2 (Z.ltb_lt _ _) Hlt). rewrite wz_add by lia. unfold wa. fold (wz (a + n)). rewrite !bv_eqb_refl. reflexivity.
-- cbn [answer_ok]. unfold mremap_answer_ok. rewrite NEa, Z.eqb_refl. rewrite !round_up_pg_eq. fold (mmap_len nl) (mmap_len n). rewrite Hnln, Hnn.
rewrite (proj2 (Z.leb_gt nl n)) by lia. rewrite (proj2 (Z.leb_le (a + nl) alloc_ceiling)) by lia.
rewrite (ranges_free_except_sub a (lranges L) a nl (a + n) (nl - n) RFE) by lia. reflexivity.
-- cbn [ev_post_state ps_brk event_post]. rewrite NEa. exact HK'.
-- apply vm_only_mremap_next.
*
unfold mremap_fresh_b in Hd. fold h in Hd.
apply andb_prop in Hd as [Hd _]. apply andb_prop in Hd as [Hd Hrf].
apply andb_prop in Hd as [Hd G3]. apply andb_prop in Hd as [Hd G2]. apply andb_prop in Hd as [G0 G1].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. rewrite page_size_eq in G1. unfold h in G3. rewrite (kl_ceil _ _ _ HK) in G3.
apply Bool.negb_true_iff in G0.
pose proof (bv_unsigned_in_range 64 dst) as Rd. unfold bv_modulus in Rd.
set (d := bv_unsigned dst) in *.
assert (Ed : dst = wz d) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (Hda : d <> a).
{ intros E. enough (bv_eqb dst (wz a) = true) by congruence. rewrite Ed, E. apply bv_eqb_refl. }
rewrite Ed in Hrf.
assert (Hrf' : region_free (vm_reserved h ++ map_remove (vm_maps h) (wz a)) (wz d) (wz nl) = true).
{ eapply region_free_incl; [| exact Hrf]. intros e He. apply in_app_or in He as [He|He]; apply in_or_app; [left; exact He| right].
apply In_map_remove in He. tauto. }
destruct (KL_mremap_new L pbrk md (mremap_model_next md (wz a) (wz n) dst (wz nl)) a l0 d nl HK Hq Hin ltac:(lia)
ltac:(unfold PGSZ; lia) ltac:(lia) ltac:(unfold PGSZ; lia) G3 Hrf'
ltac:(rewrite m_halted_mremap_next; exact Hh) ltac:(apply m_vm_lazy_mremap_next; exact Hlazy)
ltac:(rewrite m_vmmaps_mremap_next, Ed; reflexivity)) as [HK' _].
assert (NEd : is_errno_form d = false).
{ unfold is_errno_form, TWO64. apply Bool.andb_false_iff. left. apply Z.leb_gt. lia. }
apply (HC _ d).
-- cbn [ev_dec]. unfold dec_mremap. rewrite Ed. rewrite (errno_of_small (wz d)) by (rewrite unsigned_wz; lia).
replace (bv_eqb (wz d) (Z_to_bv 64 a)) with false by (symmetry; apply bv_eqb_neq; intros E; apply Hda; apply (f_equal bv_unsigned) in E; rewrite unsigned_wz, unsigned_lit in E by lia; exact E).
rewrite (proj2 (Z.ltb_lt _ _) Hlt). rewrite unsigned_wz by lia. rewrite !wz_add by lia. unfold wa. fold (wz (d + n)) (wz a) (wz n).
cbn [copy_src copy_dst copy_len]. rewrite !bv_eqb_refl.
rewrite G1, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt 0 d)) by lia. rewrite (proj2 (Z.leb_le _ _) G3). reflexivity.
-- cbn [answer_ok]. unfold mremap_answer_ok. rewrite NEd. rewrite !round_up_pg_eq. fold (mmap_len nl) (mmap_len n). rewrite Hnln, Hnn.
replace (d =? a) with false by (symmetry; apply Z.eqb_neq; exact Hda). cbn [andb orb negb].
rewrite (proj2 (Z.ltb_lt n nl)) by lia. rewrite (proj2 (Z.ltb_lt 0 d)) by lia. unfold PGSZ at 1. rewrite G1, Z.eqb_refl.
rewrite (proj2 (Z.leb_le (d + nl) alloc_ceiling)) by lia. cbn [andb].
eapply KL_ranges_free; [exact HK| lia| lia| exact G3| exact Hrf].
-- cbn [ev_post_state ps_brk event_post]. rewrite NEd. exact HK'.
-- apply vm_only_mremap_next.
Qed.
End Ev.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require EdEvNode EdEvArm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwNp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwNp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkRc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkRc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qh1B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qh1B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyuL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyuL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOnw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOnw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Ltac lia ::= klia. Ltac mkr__lia_0 := klia.
Ltac nia ::= knia. Ltac mkr__nia_1 := knia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ev.
Variable segs : list Segment.

Notation EVND := (EVND segs KL vm_only FEAS (fun e => ACC (ecost e))).

#[using="Type"] Lemma evn_brk0 : forall L pbrk md ms1,
KL L pbrk md -> ld_brk L = BPUntried -> QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NBrk 0) ms1 ->
EVND (EBrk 0) L pbrk md ms1.
Proof.
intros L pbrk md ms1 HK Hph [Hsvc Ha0].
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
assert (H0 : ms_gpr ms1 0 = Z_to_bv 64 0) by (rewrite ms_gpr_areg0; exact Ha0).
set (b := vm_brk (m_vmmaps md)).
assert (Hcases : forall r, brk_resolution_ok md (ms_gpr ms1 0) r <-> r = b).
{ intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
assert (Hq : brk_resolution_ok md (ms_gpr ms1 0) b) by (apply Hcases; reflexivity).
pose proof (EdEvNode.Mb.node_brk_query segs ms1 md (Z_to_bv 64 214) Hh Hlazy Hsvc u214 H0) as NODE.
unfold EVND.
exists {r : word | brk_resolution_ok md (ms_gpr ms1 0) r},
(fun i => mkEffectU (proj1_sig i) [] (Mmap.brk_zeros (ms_gpr ms1 0) (proj1_sig i) (vm_brk (m_vmmaps md)))
(Mmap.brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps md))) [] []),
(fun i => brk_model (ms_gpr ms1 0) (proj1_sig i) md),
(fun i => bv_unsigned (proj1_sig i)),
(exist _ b Hq).
split; [exact NODE|]. split; [| intros E; discriminate E].
intros [r Hr]. cbn [proj1_sig].
pose proof (proj1 (Hcases r) Hr) as Er. subst r.
rewrite H0, brk_zeros_query, brk_unmaps_keep.
rewrite (brk_model_query _ md eq_refl), vmmaps_eta, with_vmmaps_eta.
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
splits.
- reflexivity.
-
cbn [answer_ok Z.eqb]. unfold brk0_answer_ok. subst b. rewrite Ebrk.
pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps md))) as R. unfold bv_modulus in R.
unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- cbn [ev_post_state Z.eqb dec_brk0 set_brk_ps ps_brk event_post].
eapply KL_rephase; [exact HK|]. cbn [phase_inv]. subst b. rewrite Ebrk. splits; auto.
- apply vm_only_refl.
- apply ACC_refl. cbn. lia.
Qed.

#[using="Type"] Lemma brk_grow_evnd : forall md ms1 (pbrk d : Z) (P : resp -> Z -> Model -> Prop),
m_halted md = None -> m_vm_lazy md = [] ->
bv_unsigned (vm_brk (m_vmmaps md)) = pbrk -> 0 < pbrk -> pbrk mod PGSZ = 0 -> 0 < d -> d mod PGSZ = 0 -> pbrk + d < 2^63 ->
bv_unsigned (vm_start_brk (m_vmmaps md)) <= pbrk + d ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NBrk (pbrk + d)) ms1 ->
P (mkEffectU (vm_brk (m_vmmaps md)) [] [] [] [] []) pbrk md ->
(Mmap.brk_grow_ok md (Z_to_bv 64 (pbrk + d)) (Z_to_bv 64 (pbrk + d)) = true ->
P (mkEffectU (Z_to_bv 64 (pbrk + d)) [] [(vm_brk (m_vmmaps md), Z_to_bv 64 d)] [] [] []) (pbrk + d)
(with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps md)) ((vm_brk (m_vmmaps md), Z_to_bv 64 d) :: vm_maps (m_vmmaps md))
(vm_noaccess (m_vmmaps md)) (vm_start_brk (m_vmmaps md))
(Z_to_bv 64 (pbrk + d)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))) md)) ->
exists (I : Type) (rspf : I -> resp) (mdf : I -> Model) (zf : I -> Z) (i0 : I),
node_ok segs (mkCfg ms1 md) I (fun _ => []) (fun i => mkCfg (nret ms1 (rspf i)) (mdf i))
/\ (forall i, P (rspf i) (zf i) (mdf i)).
Proof.
intros md ms1 pbrk d P Hh Hlazy Ub Hp0 Hpal Hd Hdal Hnw Hs [Hsvc Ha0] HA HB. linearize_mods.
set (h := m_vmmaps md) in *. set (b := vm_brk h) in *.
set (req := Z_to_bv 64 (pbrk + d)) in *.
assert (Hureq : bv_unsigned req = pbrk + d) by (unfold req; apply unsigned_lit; lia).
assert (H0 : ms_gpr ms1 0 = req) by (rewrite ms_gpr_areg0; exact Ha0).
assert (Hcases : forall r, brk_resolution_ok md (ms_gpr ms1 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok md req req = true))).
{ intros r. rewrite H0. pose proof (brk_r_ok_grow_cases md req r) as X. cbv zeta in X. fold h b in X.
apply X; rewrite ?Hureq, ?Ub; lia. }
pose proof (EdEvNode.Mb.node_brk_ekept segs ms1 md (Z_to_bv 64 214) Hh Hlazy Hsvc u214) as NODE.
destruct (EdEvNode.Mb.ebrk_idx_inh segs ms1 md (Z_to_bv 64 214) u214) as (r0 & Hr0 & Hns0).
exists (EdEvNode.Mb.ebrk_idx segs ms1 md (Z_to_bv 64 214)),
(fun i => EdEvNode.Mb.ebrk_eff ms1 md (proj1_sig i)),
(fun i => brk_model (ms_gpr ms1 0) (proj1_sig i) md),
(fun i => if bv_eqb (proj1_sig i) b then pbrk else pbrk + d),
(exist _ r0 (conj Hr0 Hns0)).
split; [exact NODE|].
intros [r [Hr Hns]]. cbn [proj1_sig]. unfold EdEvNode.Mb.ebrk_eff. fold h b.
destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
- rewrite bv_eqb_refl, brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep. exact HA.
- assert (Hlt : bv_unsigned b < bv_unsigned req) by (rewrite Hureq; lia).
assert (Hneq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
assert (Ebq : bv_eqb req b = false).
{ apply bv_eqb_neq. intros E. rewrite E in Hlt. lia. }
rewrite Ebq.
rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hneq0 ltac:(lia) Hlt), (brk_unmaps_grow req b) by lia.
unfold Mmap.brk_page_range.
rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (rewrite Ub; unfold page_size; lia).
rewrite (page_round_up_Z_aligned (bv_unsigned req))
by (rewrite Hureq; unfold page_size; lia).
rewrite (proj2 (Z.ltb_lt _ _) Hlt).
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
rewrite Hureq, Ub. replace (pbrk + d - pbrk) with d by lia.
unfold req. replace (pbrk + d) with (bv_unsigned b + d) by lia.
pose proof (brk_model_grow_eq md d Hd) as E. cbv zeta in E. fold h b in E.
rewrite E by (rewrite ?Ub; first [lia | exact Hpal | exact Hdal]).
rewrite Ub. apply HB. unfold req in Hg. exact Hg.
Qed.

Definition FACTS (e : ev) (L : mled) (pbrk : Z) (md : Model) : resp -> Z -> Model -> Prop :=
fun rsp z md' =>
ev_dec e pbrk rsp = Some z /\ answer_ok L e z = true
/\ KL (event_post L e z) (ps_brk (ev_post_state e rsp (mkPS (minit 0 []) pbrk tt tt))) md'
/\ vm_only md md' /\ ACC (ecost e) md md'.

#[using="Type"] Lemma evnd_of_facts e L pbrk md ms1 (I : Type) rspf mdf zf (i0 : I) :
node_ok segs (mkCfg ms1 md) I (fun _ => []) (fun i => mkCfg (nret ms1 (rspf i)) (mdf i)) ->
(forall i, FACTS e L pbrk md (rspf i) (zf i) (mdf i)) ->
egrant e = false ->
EVND e L pbrk md ms1.
Proof.
intros NODE HF EG. unfold EVND. exists I, rspf, mdf, zf, i0. splits; [exact NODE| exact HF| rewrite EG; intros X; discriminate X].
Qed.

#[using="Type"] Lemma evn_brk_grow1 : forall L pbrk md ms1 cur req,
KL L pbrk md -> ld_brk L = BPQueried cur ->
req = round_up_pg cur + 2 * PGSZ ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NBrk req) ms1 ->
EVND (EBrk req) L pbrk md ms1.
Proof.
intros L pbrk md ms1 cur req HK Hph Hreq Hat. pose proof alloc_ceiling_lt as Hcl.
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
subst pbrk. rename cur into pbrk.
assert (Hpal : pbrk mod PGSZ = 0) by (rewrite Ecur; exact S2). linearize_mods.
assert (Hrc : round_up_pg pbrk = pbrk) by (apply round_up_pg_aligned; lia).
assert (Ereq : req = pbrk + 2 * PGSZ) by (rewrite Hreq, Hrc; lia).
clear Hreq. subst req.
assert (Hne : pbrk + 2 * PGSZ =? 0 = false) by (apply Z.eqb_neq; unfold PGSZ; lia).
destruct (brk_grow_evnd md ms1 pbrk (2 * PGSZ) (FACTS (EBrk (pbrk + 2 * PGSZ)) L pbrk md) Hh Hlazy Ebrk ltac:(lia) Hpal
ltac:(unfold PGSZ; lia) eq_refl ltac:(unfold PGSZ in *; lia) ltac:(lia) Hat) as (I & rspf & mdf & zf & i0 & NODE & HF).
3:{ eapply (evnd_of_facts _ L pbrk md ms1 I rspf mdf zf i0 NODE HF). reflexivity. }
-
unfold FACTS. splits.
+ cbn [ev_dec]. rewrite Hne. unfold dec_brk. rewrite Ebrk, Z.eqb_refl. reflexivity.
+ cbn [answer_ok]. rewrite Hne, Hph. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r.
replace (pbrk =? pbrk + 2 * PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). reflexivity.
+ cbn [ev_post_state ps_brk]. rewrite Hne. unfold dec_brk. rewrite Ebrk, Z.eqb_refl. cbn [andb ps_brk event_post].
rewrite Hne. replace (pbrk =? pbrk + 2 * PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia).
eapply KL_dead. exact HK.
+ apply vm_only_refl.
+ apply ACC_refl. cbn. rewrite Hne. lia.
-
intros Hg.
destruct (brk_grow_ok_facts md pbrk (2 * PGSZ) Ebrk ltac:(lia) Hpal ltac:(unfold PGSZ; lia) eq_refl ltac:(unfold PGSZ in *; lia) Hg (kl_ceil _ _ _ HK)) as (Hceil & Hrf & Hrf2).
set (b := vm_brk (m_vmmaps md)) in *.
assert (Eb : b = Z_to_bv 64 pbrk) by (symmetry; apply Z_to_bv_u_eq'; symmetry; exact Ebrk).
unfold FACTS. splits.
+ cbn [ev_dec]. rewrite Hne. unfold dec_brk. rewrite unsigned_lit by (unfold PGSZ in *; lia).
replace (pbrk + 2 * PGSZ =? pbrk) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [andb].
rewrite Z.eqb_refl. unfold brk_new_pages. rewrite <- !round_up_pg_eq.
rewrite (round_up_pg_aligned pbrk) by lia.
rewrite (round_up_pg_aligned (pbrk + 2 * PGSZ)) by (unfold PGSZ; lia).
rewrite (proj2 (Z.ltb_lt _ _)) by (unfold PGSZ; lia). cbn [zeros_of].
replace (pbrk + 2 * PGSZ - pbrk) with (2 * PGSZ) by lia. unfold wa. rewrite <- Eb. rewrite listNN_eqb_refl. reflexivity.
+ cbn [answer_ok]. rewrite Hne, Hph. unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [andb orb negb].
rewrite Hrc. eapply KL_lbrk_pages_ok; [exact HK| lia| unfold PGSZ; lia| exact Hceil| exact Hrf].
+ cbn [ev_post_state ps_brk]. rewrite Hne. unfold dec_brk. rewrite unsigned_lit by (unfold PGSZ in *; lia).
replace (pbrk + 2 * PGSZ =? pbrk) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [andb].
rewrite Z.eqb_refl. unfold brk_new_pages. rewrite <- !round_up_pg_eq.
rewrite (round_up_pg_aligned pbrk) by lia.
rewrite (round_up_pg_aligned (pbrk + 2 * PGSZ)) by (unfold PGSZ; lia).
rewrite (proj2 (Z.ltb_lt _ _)) by (unfold PGSZ; lia). cbn [zeros_of].
replace (pbrk + 2 * PGSZ - pbrk) with (2 * PGSZ) by lia. unfold wa. rewrite <- Eb. rewrite listNN_eqb_refl. cbn [andb ps_brk set_brk_ps].
cbn [event_post]. rewrite Hne, Z.eqb_refl, Hph.

assert (Upb : bv_unsigned (Z_to_bv 64 pbrk) = pbrk) by (apply unsigned_lit; lia).
assert (Ud : bv_unsigned (Z_to_bv 64 (2 * PGSZ)) = 2 * PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
b0 + mmap_len l0 <= pbrk \/ pbrk + 2 * PGSZ <= b0).
{ intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Upb, Ud in D. lia. }
kl_open HK. clear Kstart. constructor; mproj; auto.
* apply vmwf_cons; [exact Kwf| rewrite Eb, Upb, Ud; unfold PGSZ in *; lia| rewrite Eb; exact Hrfm].
* rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; [exact S1| exact S2| lia| exact S4].
* intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
* intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold brk_disj in *; cbn. splits; auto with datatypes.
* intros e He. destruct (Kna e He) as (W & [Hm | (b0 & l0 & E & _)]); [split; [exact W| left; exact Hm]|].
rewrite Ereg in E. discriminate.
* intros b0 l0 E. rewrite Ereg in E. discriminate.
* rewrite unsigned_lit by (unfold PGSZ in *; lia). splits.
-- exact Ecur.
-- reflexivity.
-- reflexivity.
-- exact Ereg.
-- exact Hceil.
-- left; rewrite Eb; reflexivity.
-- intros b0 l0 Hin; apply Dgm; left; exact Hin.
-- intros b0 l0 k Hin; apply Dgm; right; exists k; exact Hin.
+ apply vm_only_with_vmmaps; reflexivity.
+ cbn [ecost]. rewrite Hne. apply ACC_brk_grow; [| unfold PGSZ; lia]. rewrite unsigned_lit by (unfold PGSZ; lia). lia.
Qed.

#[using="Type"] Lemma evn_brk_grow2 : forall L pbrk md ms1 b0 l0 req,
KL L pbrk md -> ld_brk L = BPLive -> ld_brkreg L = Some (b0, l0) ->
req = b0 + l0 + PGSZ ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NBrk req) ms1 ->
EVND (EBrk req) L pbrk md ms1.
Proof.
intros L pbrk md ms1 b0 l0 req HK Hph Hreg Hreq Hat. pose proof alloc_ceiling_small as Hcl.
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (b0' & l0' & Hreg' & Ebrk & Epbrk).
rewrite Hreg in Hreg'. injection Hreg' as <- <-.
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
pose proof (kl_brkreg _ _ _ HK b0 l0 Hreg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
subst pbrk.
assert (Ereq : req = b0 + l0 + PGSZ) by exact Hreq. clear Hreq. subst req.
assert (Hne : b0 + l0 + PGSZ =? 0 = false) by (apply Z.eqb_neq; unfold PGSZ; lia).
linearize_mods.
assert (Hal : (b0 + l0) mod PGSZ = 0) by (unfold PGSZ; lia).
assert (Hal' : hidden ((b0 + l0) mod PGSZ = 0)) by exact Hal. clear Hal. rename Hal' into Hal.
destruct (brk_grow_evnd md ms1 (b0 + l0) PGSZ (FACTS (EBrk (b0 + l0 + PGSZ)) L (b0 + l0) md) Hh Hlazy Ebrk ltac:(lia) Hal
ltac:(unfold PGSZ; lia) eq_refl ltac:(unfold PGSZ in *; lia) ltac:(lia) Hat) as (I & rspf & mdf & zf & i0 & NODE & HF).
3:{ eapply (evnd_of_facts _ L (b0 + l0) md ms1 I rspf mdf zf i0 NODE HF). reflexivity. }
-
unfold FACTS. splits.
+ cbn [ev_dec]. rewrite Hne. unfold dec_brk. rewrite Ebrk, Z.eqb_refl. reflexivity.
+ cbn [answer_ok]. rewrite Hne, Hph, Hreg. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r.
replace (b0 + l0 =? b0 + l0 + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). reflexivity.
+ cbn [ev_post_state ps_brk]. rewrite Hne. unfold dec_brk. rewrite Ebrk, Z.eqb_refl. cbn [andb ps_brk event_post].
rewrite Hne. replace (b0 + l0 =? b0 + l0 + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia).
eapply KL_dead. exact HK.
+ apply vm_only_refl.
+ apply ACC_refl. cbn. rewrite Hne. lia.
-
intros Hg.
destruct (brk_grow_ok_facts md (b0 + l0) PGSZ Ebrk ltac:(lia) Hal ltac:(unfold PGSZ; lia) eq_refl ltac:(unfold PGSZ in *; lia) Hg (kl_ceil _ _ _ HK)) as (Hceil & Hrf & Hrf2).
set (b := vm_brk (m_vmmaps md)) in *.
assert (Eb : b = Z_to_bv 64 (b0 + l0)) by (symmetry; apply Z_to_bv_u_eq'; symmetry; exact Ebrk).
unfold FACTS. splits.
+ cbn [ev_dec]. rewrite Hne. unfold dec_brk. rewrite unsigned_lit by (unfold PGSZ in *; lia).
replace (b0 + l0 + PGSZ =? b0 + l0) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [andb].
rewrite Z.eqb_refl. unfold brk_new_pages. rewrite <- !round_up_pg_eq.
rewrite (round_up_pg_aligned (b0 + l0)) by (unfold PGSZ; lia).
rewrite (round_up_pg_aligned (b0 + l0 + PGSZ)) by (unfold PGSZ; lia).
rewrite (proj2 (Z.ltb_lt _ _)) by (unfold PGSZ; lia). cbn [zeros_of].
replace (b0 + l0 + PGSZ - (b0 + l0)) with PGSZ by lia. unfold wa. rewrite <- Eb. rewrite listNN_eqb_refl. reflexivity.
+ cbn [answer_ok]. rewrite Hne, Hph, Hreg. unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [andb orb negb].
eapply KL_lbrk_pages_ok; [exact HK| lia| unfold PGSZ; lia| exact Hceil| exact Hrf].
+ cbn [ev_post_state ps_brk]. rewrite Hne. unfold dec_brk. rewrite unsigned_lit by (unfold PGSZ in *; lia).
replace (b0 + l0 + PGSZ =? b0 + l0) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [andb].
rewrite Z.eqb_refl. unfold brk_new_pages. rewrite <- !round_up_pg_eq.
rewrite (round_up_pg_aligned (b0 + l0)) by (unfold PGSZ; lia).
rewrite (round_up_pg_aligned (b0 + l0 + PGSZ)) by (unfold PGSZ; lia).
rewrite (proj2 (Z.ltb_lt _ _)) by (unfold PGSZ; lia). cbn [zeros_of].
replace (b0 + l0 + PGSZ - (b0 + l0)) with PGSZ by lia. unfold wa. rewrite <- Eb. rewrite listNN_eqb_refl. cbn [andb ps_brk set_brk_ps].
cbn [event_post]. rewrite Hne, Z.eqb_refl, Hph, Hreg.

assert (Upb : bv_unsigned (Z_to_bv 64 (b0 + l0)) = b0 + l0) by (apply unsigned_lit; lia).
assert (Ud : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
pose proof (fun b1 l1 H => went_In_bounds _ _ _ b1 l1 HK H) as WB.
assert (Dgm : forall b1 l1, (In (b1, l1) (ld_groups L) \/ exists k, In (b1, l1, k) (ld_metas L)) ->
b1 + mmap_len l1 <= b0 + l0 \/ b0 + l0 + PGSZ <= b1).
{ intros b1 l1 H. pose proof (WB b1 l1 H) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Upb, Ud in D. lia. }
kl_open HK. clear Kstart. constructor; mproj; auto.
* apply vmwf_cons; [exact Kwf| rewrite Eb, Upb, Ud; unfold PGSZ in *; lia| rewrite Eb; exact Hrfm].
* rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; [exact S1| exact S2| lia| exact S4].
* intros b1 l1 Hin. pose proof (Dgm b1 l1 (or_introl Hin)) as D. specialize (Kgr b1 l1 Hin).
destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). splits; auto with datatypes.
unfold brk_disj in *; cbn. intros b2 l2 E. injection E as <- <-. specialize (G6 b0 l0 Hreg).
pose proof (mmap_len_ge l1 ltac:(lia)). lia.
* intros b1 l1 k Hin. pose proof (Dgm b1 l1 (or_intror (ex_intro _ k Hin))) as D. specialize (Kme b1 l1 k Hin).
destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; auto with datatypes.
unfold brk_disj in *; cbn. intros b2 l2 E. injection E as <- <-. specialize (G8 b0 l0 Hreg).
pose proof (mmap_len_ge l1 ltac:(lia)). lia.
* intros e He. destruct (Kna e He) as (W & [Hm | (b2 & l2 & E & X1 & X2 & X3)]); [split; [exact W| left; exact Hm]|].
split; [exact W|]. right. rewrite Hreg in E. injection E as <- <-. exists b0, (l0 + PGSZ). splits; auto with datatypes.
* intros b2 l2 E. injection E as <- <-. splits; [exact R1| exact R2| lia| | lia|].
{ unfold PGSZ. lia. }
intros x Hx. destruct (Z.lt_ge_cases x (b0 + l0)) as [Hlt|Hge].
-- destruct (Rcov x ltac:(lia)) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
-- exists (b, Z_to_bv 64 PGSZ). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Eb, Upb, Ud. lia.
* rewrite Hph. exists b0, (l0 + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; [reflexivity| lia| lia].
+ apply vm_only_with_vmmaps; reflexivity.
+ cbn [ecost]. rewrite Hne. apply ACC_brk_grow; [| unfold PGSZ; lia]. rewrite unsigned_lit by (unfold PGSZ; lia). unfold PGSZ; lia.
Qed.

#[using="Type"] Lemma evn_mmap_anon : forall L pbrk md ms1 len prot,
KL L pbrk md -> brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMmap 0 len prot MAPF) ms1 ->
EVND (EMmap 0 len prot MAPF) L pbrk md ms1.
Proof.
intros L pbrk md ms1 len prot HK Hq Hprot Hlen Hat.
destruct Hat as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & _).
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
pose proof (mmap_len_ge len ltac:(lia)) as Hn1.
assert (U1 : bv_unsigned (ms_gpr ms1 1) = len) by (rewrite ms_gpr_areg1, Ha1; apply unsigned_lit; lia).
assert (Hpr : page_round_up (ms_gpr ms1 1) = Z_to_bv 64 (mmap_len len)) by (unfold page_round_up, mmap_len; rewrite U1; reflexivity).
assert (H0 : ms_gpr ms1 0 = Z_to_bv 64 0) by (rewrite ms_gpr_areg0; exact Ha0).
assert (Hne1 : ms_gpr ms1 1 <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite U1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }

assert (Hfix : negb (Z.land MAPF MAP_FIXED_Z =? 0) = false) by reflexivity.
assert (Hfix' : (Z.land MAPF MAP_FIXED =? 0) = true) by reflexivity.
assert (Hisf : is_fixed MAPF = false) by reflexivity.
assert (Hcost : ecost (EMmap 0 len prot MAPF) = mmap_len len) by (cbn [ecost]; rewrite Hisf; apply round_up_pg_eq).
assert (Un : bv_unsigned (Z_to_bv 64 (mmap_len len)) = mmap_len len) by (apply unsigned_lit; lia).
unfold EVND. destruct Hprot as [-> | ->].
-
assert (Hargs : mmap_noaccess_args_ok ms1).
{ unfold mmap_noaccess_args_ok. rewrite ms_gpr_areg2, ms_gpr_areg3, ms_gpr_areg4, ms_gpr_areg5. auto 10. }

pose (IDX := ({e : Z | In e mmap_errnos /\ mmap_reserve_refusable md (mmap_len len) = true}
+ {a : word | grant_ok_na (ms_gpr ms1 0) md a (mmap_len len) = true})%type).
pose (effs := fun i : IDX =>
match i with
| inl (exist _ e _) => mkEffect (errno_ret e) [] []
| inr (exist _ a _) => mkEffectU a [] [] [(a, Z_to_bv 64 (mmap_len len))] [] [] end).
pose (ms' := fun i : IDX =>
match i with inl _ => md | inr (exist _ a _) => noaccess_model a (Z_to_bv 64 (mmap_len len)) md end).
pose (zf := fun i : IDX =>
match i with inl (exist _ e _) => neg_errno e | inr (exist _ a _) => bv_unsigned a end).
assert (Hi0 : exists i0 : IDX, True).
{ destruct (Bool.bool_dec (mmap_reserve_refusable md (mmap_len len)) true) as [HR|HR]; [| apply Bool.not_true_is_false in HR].
- exists (inl (exist _ ENOMEM (conj ENOMEM_in_mmap_errnos HR))). exact I.
- destruct (not_refusable_grant_ok_na (ms_gpr ms1 0) md (mmap_len len) HR) as [a Ha]. exists (inr (exist _ a Ha)). exact I. }
destruct Hi0 as [i0 _].
unshelve epose proof (EdEvNode.node_ekept segs ms1 md (Z_to_bv 64 222) _ effs ms' Hh Hsvc (EdEvArm.Ms.mmap_noaccess_outcome_live segs ms1 (Z_to_bv 64 222) md eq_refl Hargs Hh) _ _ _) as NODE.
+ intros o. rewrite (EdEvArm.Ms.mmap_noaccess_outcome_ekept segs ms1 (Z_to_bv 64 222) md eq_refl Hargs o). unfold mmap_len in IDX, effs, ms'. rewrite U1. split.
* intros [(HR & e & He & ->) | (a & Ha & ->)]; [exists (inl (exist _ e (conj He HR)))| exists (inr (exist _ a Ha))]; reflexivity.
* intros [[[e [He HR]]|[a Ha]] ->]; [left; split; [exact HR| exists e; auto]| right; exists a; auto].
+ intros [[e [He HR]]|[a Ha]]; cbn [ms']; [exact Hh| rewrite <- Hh; reflexivity].
+ intros [[e [He HR]]|[a Ha]]; cbn [ms']; [exact Hlazy| rewrite <- Hlazy; reflexivity].
+ exists _, effs, ms', zf, i0. split; [exact NODE|]. split.
* intros [[e [He HR]]|[a Ha]]; cbn [effs ms' zf].
--
pose proof (mmap_errno_range e He) as Her. assert (E12 : e = 12) by (destruct He as [<-|[]]; reflexivity). splits.
++ cbn [ev_dec]. rewrite Hfix. change (PROT_NONE =? 0) with true. cbv iota.
cbn -[errno_of neg_errno errno_ret]. rewrite errno_of_errno_ret by lia. rewrite E12. reflexivity.
++ cbn [answer_ok]. rewrite Hfix'. unfold mmap_answer_ok. rewrite is_errno_form_neg by lia. reflexivity.
++ cbn [ev_post_state ps_brk event_post]. rewrite Hfix', is_err_neg by lia. exact HK.
++ apply vm_only_refl.
++ apply ACC_refl. rewrite Hcost. lia.
--
set (n := mmap_len len) in *.
pose proof Ha as Ha'. unfold grant_ok_na in Ha.
apply andb_prop in Ha as [Ha Hrf]. apply andb_prop in Ha as [Ha G3]. apply andb_prop in Ha as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. rewrite page_size_eq in G1. rewrite (kl_ceil _ _ _ HK) in G3.
pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
assert (Ea : a = Z_to_bv 64 (bv_unsigned a)) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (Hok : mmap_addr_ok len [] (bv_unsigned a) = true).
{ unfold mmap_addr_ok. fold n. rewrite page_size_eq, G1, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _) G2).
rewrite (proj2 (Z.leb_le _ _) G3). reflexivity. }
rewrite Ea in Hrf.
destruct (KL_mmap_new L pbrk md (noaccess_model a (Z_to_bv 64 n) md) (bv_unsigned a) len true HK Hq Hlen Hok Hrf
ltac:(rewrite <- Hh; reflexivity) ltac:(rewrite <- Hlazy; reflexivity)
ltac:(rewrite <- Ea; reflexivity)) as (HK' & Hans & Herr).
splits.
++ cbn [ev_dec]. rewrite Hfix. change (PROT_NONE =? 0) with true. cbv iota.
unfold dec_mmap_none. fold n. rewrite !bv_eqb_refl, Hok. reflexivity.
++ cbn [answer_ok]. rewrite Hfix'. exact Hans.
++ cbn [ev_post_state ps_brk event_post]. rewrite Hfix', Herr. change (PROT_NONE =? PROT_NONE) with true. cbv iota. exact HK'.
++ apply vm_only_with_vmmaps; reflexivity.
++ rewrite Hcost. apply ACC_noaccess_model. exact Un.
*
intros _ HF [[e [He HR]]|[x Hx]]; cbn [zf eclass]; rewrite Hisf.
-- exfalso. destruct (HF (kl_ceil _ _ _ HK) (ms_gpr ms1 0)) as [y Hy].
rewrite (grant_ok_na_not_refusable _ _ _ _ (grant_ok_na_of_ok _ _ _ _ Hy)) in HR. discriminate HR.
-- unfold grant_ok_na in Hx. apply andb_prop in Hx as [Hx _].
apply andb_prop in Hx as [Hx G3]. apply andb_prop in Hx as [G1 G2]. apply Z.leb_le in G3. rewrite (kl_ceil _ _ _ HK) in G3.
unfold is_err. pose proof alloc_ceiling_small. pose proof (mmap_len_ge len ltac:(lia)).
destruct (Z.ltb_spec (TWO64 - 4096) (bv_unsigned x)); [exfalso; lia| reflexivity].
-
assert (Hargs : mmap_args_ok ms1).
{ unfold mmap_args_ok. rewrite ms_gpr_areg2, ms_gpr_areg3, ms_gpr_areg4, ms_gpr_areg5. auto 10. }

assert (H3 : ms_gpr ms1 3 = Z_to_bv 64 MAPF) by (rewrite ms_gpr_areg3; exact Ha3).
pose (IDX := ({e : Z | In e mmap_errnos /\ mmap_grant_refusable (ms_gpr ms1 3) md (mmap_len len) = true}
+ {a : word | grant_ok (ms_gpr ms1 0) md a (mmap_len len) = true})%type).
pose (effs := fun i : IDX =>
match i with
| inl (exist _ e _) => mkEffect (errno_ret e) [] []
| inr (exist _ a _) => mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))] end).
pose (ms' := fun i : IDX =>
match i with inl _ => md | inr (exist _ a _) => mmap_model a (Z_to_bv 64 (mmap_len len)) md end).
pose (zf := fun i : IDX =>
match i with inl (exist _ e _) => neg_errno e | inr (exist _ a _) => bv_unsigned a end).
assert (Hi0 : exists i0 : IDX, True).
{ destruct (Bool.bool_dec (mmap_grant_refusable (ms_gpr ms1 3) md (mmap_len len)) true) as [HR|HR]; [| apply Bool.not_true_is_false in HR].
- exists (inl (exist _ ENOMEM (conj ENOMEM_in_mmap_errnos HR))). exact I.
- rewrite H3 in HR. destruct (not_refusable_grant_ok (ms_gpr ms1 0) md (mmap_len len) HR) as [a Ha]. exists (inr (exist _ a Ha)). exact I. }
destruct Hi0 as [i0 _].
unshelve epose proof (EdEvNode.node_ekept segs ms1 md (Z_to_bv 64 222) _ effs ms' Hh Hsvc (EdEvArm.Mm.mmap_outcome_live segs ms1 (Z_to_bv 64 222) md eq_refl Hargs Hh) _ _ _) as NODE.
+ intros o. rewrite (EdEvArm.Mm.mmap_outcome_ekept segs ms1 (Z_to_bv 64 222) md o eq_refl Hargs). rewrite Hpr. unfold mmap_len in IDX, effs, ms' |- *. rewrite U1. split.
* intros [(HR & e & He & ->) | (a & Ha & ->)]; [exists (inl (exist _ e (conj He HR)))| exists (inr (exist _ a Ha))]; reflexivity.
* intros [[[e [He HR]]|[a Ha]] ->]; [left; split; [exact HR| exists e; auto]| right; exists a; auto].
+ intros [[e [He HR]]|[a Ha]]; cbn [ms']; [exact Hh| rewrite <- Hh; reflexivity].
+ intros [[e [He HR]]|[a Ha]]; cbn [ms']; [exact Hlazy| rewrite <- Hlazy; reflexivity].
+ exists _, effs, ms', zf, i0. split; [exact NODE|]. split.
* intros [[e [He HR]]|[a Ha]]; cbn [effs ms' zf].
--
pose proof (mmap_errno_range e He) as Her. assert (E12 : e = 12) by (destruct He as [<-|[]]; reflexivity). splits.
++ cbn [ev_dec]. rewrite Hfix. change (PROT_RW =? 0) with false. cbv iota.
cbn -[errno_of neg_errno errno_ret]. rewrite errno_of_errno_ret by lia. rewrite E12. reflexivity.
++ cbn [answer_ok]. rewrite Hfix'. unfold mmap_answer_ok. rewrite is_errno_form_neg by lia. reflexivity.
++ cbn [ev_post_state ps_brk event_post]. rewrite Hfix', is_err_neg by lia. exact HK.
++ apply vm_only_refl.
++ apply ACC_refl. rewrite Hcost. lia.
--
set (n := mmap_len len) in *.
unfold grant_ok in Ha.
apply andb_prop in Ha as [Ha _]. apply andb_prop in Ha as [Ha Hrf]. apply andb_prop in Ha as [Ha G3]. apply andb_prop in Ha as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. rewrite page_size_eq in G1. rewrite (kl_ceil _ _ _ HK) in G3.
pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
assert (Ea : a = Z_to_bv 64 (bv_unsigned a)) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (Hok : mmap_addr_ok len [] (bv_unsigned a) = true).
{ unfold mmap_addr_ok. fold n. rewrite page_size_eq, G1, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _) G2).
rewrite (proj2 (Z.leb_le _ _) G3). reflexivity. }
rewrite Ea in Hrf.
destruct (KL_mmap_new L pbrk md (mmap_model a (Z_to_bv 64 n) md) (bv_unsigned a) len false HK Hq Hlen Hok Hrf
ltac:(rewrite <- Hh; reflexivity) ltac:(rewrite <- Hlazy; reflexivity)
ltac:(rewrite <- Ea; reflexivity)) as (HK' & Hans & Herr).
splits.
++ cbn [ev_dec]. rewrite Hfix. change (PROT_RW =? 0) with false. cbv iota.
unfold dec_mmap. fold n. rewrite !bv_eqb_refl, Hok. reflexivity.
++ cbn [answer_ok]. rewrite Hfix'. exact Hans.
++ cbn [ev_post_state ps_brk event_post]. rewrite Hfix', Herr. change (PROT_RW =? PROT_NONE) with false. cbv iota. exact HK'.
++ apply vm_only_with_vmmaps; reflexivity.
++ rewrite Hcost. apply ACC_mmap_model. exact Un.
*
intros _ HF [[e [He HR]]|[x Hx]]; cbn [zf eclass]; rewrite Hisf.
-- exfalso. destruct (HF (kl_ceil _ _ _ HK) (ms_gpr ms1 0)) as [y Hy].
rewrite (grant_ok_not_refusable _ _ _ _ (ms_gpr ms1 3) Hy) in HR. discriminate HR.
-- unfold grant_ok in Hx. apply andb_prop in Hx as [Hx _]. apply andb_prop in Hx as [Hx _].
apply andb_prop in Hx as [Hx G3]. apply andb_prop in Hx as [G1 G2]. apply Z.leb_le in G3. rewrite (kl_ceil _ _ _ HK) in G3.
unfold is_err. pose proof alloc_ceiling_small. pose proof (mmap_len_ge len ltac:(lia)).
destruct (Z.ltb_spec (TWO64 - 4096) (bv_unsigned x)); [exfalso; lia| reflexivity].
Qed.

#[using="Type"] Lemma evn_mmap_fixed : forall L pbrk md ms1 cur a,
KL L pbrk md -> ld_brk L = BPGuard cur -> a = round_up_pg cur ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMmap a PGSZ PROT_NONE MAPFX) ms1 ->
EVND (EMmap a PGSZ PROT_NONE MAPFX) L pbrk md ms1.
Proof.
intros L pbrk md ms1 cur a HK Hph Ha Hat.
destruct Hat as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & _).
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & Hgin & Dg & Dm).
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
assert (Hcal : cur mod PGSZ = 0) by (rewrite Ecur; exact S2). linearize_mods.
assert (Ea : a = cur) by (rewrite Ha; apply round_up_pg_aligned; lia). clear Ha. subst a.
assert (Ua : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; lia).
assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; lia).
assert (H0 : ms_gpr ms1 0 = (Z_to_bv 64 cur)) by (rewrite ms_gpr_areg0; exact Ha0).
assert (H1 : ms_gpr ms1 1 = Z_to_bv 64 PGSZ) by (rewrite ms_gpr_areg1; exact Ha1).
assert (Hargs : mmap_fixed_args_ok ms1).
{ unfold mmap_fixed_args_ok. rewrite H1, ms_gpr_areg2, ms_gpr_areg3, ms_gpr_areg4, ms_gpr_areg5. splits; auto.
all: intros E; apply (f_equal bv_unsigned) in E; rewrite unsigned_lit in E by lia; change (bv_unsigned (Z_to_bv 64 0)) with 0 in E; lia. }
assert (Hrf : region_free (vm_reserved (m_vmmaps md)) (Z_to_bv 64 cur) (Z_to_bv 64 PGSZ) = true).
{ apply region_free_intro. intros e He. rewrite Ua, Un.
pose proof (kl_resv_top _ _ _ HK e He). lia. }
assert (Hmc : map_contains (vm_maps (m_vmmaps md)) (Z_to_bv 64 cur) (Z_to_bv 64 PGSZ) = true).
{ eapply map_contains_intro; [exact Hgin| rewrite elo_went, Ua by lia; lia| rewrite ehi_went, Ua, Un by lia; lia]. }
assert (Hpn : Z_to_bv 64 (page_round_up_Z PGSZ) = (Z_to_bv 64 PGSZ)) by reflexivity.
pose proof (EdEvArm.Ms.mmap_fixed_outcome_ekept segs ms1 (Z_to_bv 64 222) md (Z_to_bv 64 cur) PGSZ eq_refl Hargs H0 ltac:(rewrite Ua; unfold page_size; lia) ltac:(lia)
H1 ltac:(lia) ltac:(rewrite Ua; change (page_round_up_Z PGSZ) with PGSZ; rewrite alloc_ceiling_State; lia)
(kl_ceil _ _ _ HK)
ltac:(rewrite Hpn; exact Hrf) ltac:(rewrite Hpn; exact Hmc) Hh) as [Hchk Hlive].
cbv zeta in Hchk. rewrite Hpn in Hchk.

pose (effs := fun _ : unit => mkEffectU (Z_to_bv 64 cur) [] [] [((Z_to_bv 64 cur), (Z_to_bv 64 PGSZ))] [] []).
pose (ms' := fun _ : unit => fixed_noaccess_model (Z_to_bv 64 cur) (Z_to_bv 64 PGSZ) md).
pose (zf := fun _ : unit => cur).
unshelve epose proof (EdEvNode.node_ekept segs ms1 md (Z_to_bv 64 222) unit effs ms' Hh Hsvc Hlive _ _ _) as NODE.
{ intros o. rewrite (Hchk o). split.
- intros ->. exists tt. reflexivity.
- intros [[] ->]. reflexivity. }
{ intros []; cbn [ms']; unfold fixed_noaccess_model; mproj; exact Hh. }
{ intros []; cbn [ms']; unfold fixed_noaccess_model; mproj; rewrite ?Hlazy; reflexivity. }

set (L' := set_brkph BPLive (set_brkreg (Some (cur, 2 * PGSZ)) L)).
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
b0 + mmap_len l0 <= cur \/ cur + 2 * PGSZ <= b0).
{ intros b0 l0 [H|[k H]]; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
assert (NAold : forall e, In e (vm_noaccess (m_vmmaps md)) ->
elo e < ehi e <= 2^64 /\ exists b l k, In (b, l, k) (ld_metas L) /\ b <= elo e /\ ehi e <= b + mmap_len l).
{ intros e He. destruct (kl_na _ _ _ HK e He) as (W & [X | (b0 & l0 & E & _)]); [auto|]. rewrite Ereg in E. discriminate. }
assert (KLnew : forall mo' maps' noacc',
m_halted mo' = None -> m_vm_lazy mo' = [] ->
vmwf maps' ->
(forall e, In e (vm_maps (m_vmmaps md)) -> (ehi e <= cur \/ cur + PGSZ <= elo e) -> In e maps') ->
(forall e', In e' noacc' ->
(e' = ((Z_to_bv 64 cur), (Z_to_bv 64 PGSZ)) /\ In (went cur (2 * PGSZ)) maps')
\/ exists e, In e (vm_noaccess (m_vmmaps md)) /\ elo e <= elo e' /\ ehi e' <= ehi e /\ elo e' < ehi e') ->
(forall e x y, In e (vm_noaccess (m_vmmaps md)) -> elo e <= x -> x < y -> y <= ehi e -> (y <= cur \/ cur + PGSZ <= x) ->
exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
(exists e', In e' maps' /\ elo e' <= cur + PGSZ /\ cur + 2 * PGSZ <= ehi e') ->
m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps md)) maps' noacc' (vm_start_brk (m_vmmaps md)) (vm_brk (m_vmmaps md)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md)) ->
KL L' pbrk mo').
{ intros mo' maps' noacc' Hh' Hl' Hwf' Hkeep Hback Hna Hcov' Evm. subst L'.
pose proof HK as HK0. kl_open HK. clear Kstart.
constructor; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
- intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). splits; try assumption.
+ apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. lia.
+ unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. lia.
+ apply region_free_intro. intros e' He'. rewrite !unsigned_wz by lia.
destruct (Hback e' He') as [[-> _] | (e & He & X1 & X2 & X3)].
* rewrite elo_pair, ehi_pair, Ua, Un. clear -D B2. lia.
* pose proof (region_free_disj _ _ _ _ G7 He) as D2. rewrite !unsigned_wz in D2 by lia. clear -D2 X1 X2 X3. lia.
- intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
+ apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. lia.
+ unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. lia.
+ intros q' Hq1 Hq2. destruct (G9 q' Hq1 Hq2) as (e & He & Hel & Heh).
apply (Hna e (b0 + q' * PGSZ) (b0 + q' * PGSZ + PGSZ) He Hel ltac:(lia) Heh). clear -D Hq1 Hq2 G5. nia.
- intros e' He'. destruct (Hback e' He') as [[-> Hg'] | (e & He & X1 & X2 & X3)].
+ rewrite elo_pair, ehi_pair, Ua, Un. split; [lia|]. right. exists cur, (2 * PGSZ). splits; [reflexivity| lia| lia| exact Hg'].
+ destruct (NAold e He) as (W & b & l & k & Hin & Y1 & Y2). split; [lia|]. left. exists b, l, k. splits; [exact Hin| lia| lia].
- intros b1 l1 E. injection E as <- <-. splits; try lia.
intros z Hz. destruct Hcov' as (e' & He' & X1 & X2). exists e'. split; [exact He'|]. lia.
- exists cur, (2 * PGSZ). splits; [reflexivity| lia| lia]. }
assert (Hlohi : 0 <= bv_unsigned (Z_to_bv 64 cur) < bv_unsigned (Z_to_bv 64 cur) + bv_unsigned (Z_to_bv 64 PGSZ)) by (rewrite Ua, Un; lia).
assert (Hhi : bv_unsigned (Z_to_bv 64 cur) + bv_unsigned (Z_to_bv 64 PGSZ) < 2^64) by (rewrite Ua, Un; lia).
assert (Hfix : negb (Z.land MAPFX MAP_FIXED_Z =? 0) = true) by reflexivity.
assert (Hfix' : (Z.land MAPFX MAP_FIXED =? 0) = false) by reflexivity.
assert (NAwf : forall e, In e (vm_noaccess (m_vmmaps md)) -> elo e < ehi e <= 2^64) by (intros e He; exact (proj1 (NAold e He))).
assert (Hisf : is_fixed MAPFX = true) by reflexivity.
assert (Hcost : ecost (EMmap cur PGSZ PROT_NONE MAPFX) = PGSZ) by (cbn [ecost]; rewrite Hisf; reflexivity).
apply (evnd_of_facts _ L pbrk md ms1 unit effs ms' zf tt NODE); [| cbn [egrant]; rewrite Hisf; reflexivity].
intros []; unfold effs, ms', zf; unfold FACTS.

splits.
- cbn [ev_dec]. rewrite Hfix. unfold dec_mmap_fixed. change (mmap_len PGSZ) with PGSZ.
rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by lia. reflexivity.
- cbn [answer_ok]. rewrite Hfix'. unfold mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
- cbn [ev_post_state ps_brk event_post]. rewrite Hfix'. fold L'.
apply (KLnew _ (vm_maps (m_vmmaps md)) (((Z_to_bv 64 cur), (Z_to_bv 64 PGSZ)) :: maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned (Z_to_bv 64 cur)) (bv_unsigned (Z_to_bv 64 cur) + bv_unsigned (Z_to_bv 64 PGSZ)))).
+ unfold fixed_noaccess_model. mproj. exact Hh.
+ unfold fixed_noaccess_model. mproj. rewrite Hlazy. reflexivity.
+ exact (kl_wf _ _ _ HK).
+ auto.
+ intros e' [<-|He']; [left; split; [reflexivity| exact Hgin]| right].
exact (maps_subtract_inside _ (bv_unsigned (Z_to_bv 64 cur)) _ _ NAwf ltac:(lia) Hhi He').
+ intros e x y He X1 X2 X3 X4. pose proof (NAwf e He).
destruct (iv_subtract_contains (fst e) (snd e) (bv_unsigned (Z_to_bv 64 cur)) (bv_unsigned (Z_to_bv 64 cur) + bv_unsigned (Z_to_bv 64 PGSZ)) x y
ltac:(lia) Hhi ltac:(unfold ehi in *; lia) X1 X2 X3 ltac:(rewrite Ua, Un; exact X4)) as (e' & He' & Hr).
exists e'. split; [right; eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
+ exists (went cur (2 * PGSZ)). split; [exact Hgin|]. rewrite elo_went, ehi_went by lia. lia.
+ unfold fixed_noaccess_model. mproj. reflexivity.
- unfold fixed_noaccess_model. eapply vm_only_trans; [| apply vm_only_forget]; apply vm_only_with_vmmaps; reflexivity.
- rewrite Hcost. apply ACC_fixed_noaccess_model. lia.
Qed.

#[using="Type"] Lemma evn_munmap : forall L pbrk md ms1 a l0 len,
KL L pbrk md -> brk_quiet L -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMunmap a len) ms1 ->
EVND (EMunmap a len) L pbrk md ms1.
Proof.
intros L pbrk md ms1 a l0 len HK Hq Hin Hlen Hat.
destruct Hat as (Hsvc & Ha0 & Ha1).
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7). linearize_mods.
pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
set (n := mmap_len l0) in *.
assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
{ destruct Hlen as [-> | ->]; [split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
destruct Hlen3 as [Hlen1 Hlen2].
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
assert (H0 : ms_gpr ms1 0 = Z_to_bv 64 a) by (rewrite ms_gpr_areg0; exact Ha0).
assert (H1 : ms_gpr ms1 1 = Z_to_bv 64 len) by (rewrite ms_gpr_areg1; exact Ha1).
assert (Hpr : page_round_up (ms_gpr ms1 1) = Z_to_bv 64 n).
{ unfold page_round_up. rewrite H1, unsigned_lit by lia. fold (mmap_len len). rewrite Hlen2. reflexivity. }
assert (Hhas : map_has (vm_maps (m_vmmaps md)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true) by (apply map_has_intro; exact A5).
assert (Hargs : munmap_args_ok ms1 md).
{ unfold munmap_args_ok. rewrite Hpr, H0, H1, Ua, unsigned_lit by lia. fold (mmap_len len). rewrite Hlen2. splits.
- unfold page_size; lia.
- intros E. apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia.
- unfold TASK_SIZE; lia.
- exact Hhas. }
unshelve epose proof (node_det segs ms1 md (Z_to_bv 64 215) (munmap_eff ms1) (munmap_model (Z_to_bv 64 a) (Z_to_bv 64 n) md) [] Hh Hsvc _ _ _) as NODE.
{ intros o. rewrite (munmap_outcome_si segs ms1 (Z_to_bv 64 215) md o eq_refl Hargs). rewrite Hpr, H0. reflexivity. }
{ unfold munmap_model, Mmap.with_mmap_destroyed. mproj. exact Hh. }
{ unfold munmap_model, Mmap.with_mmap_destroyed. mproj. rewrite Hlazy. reflexivity. }
unfold munmap_eff in NODE. rewrite Hpr, H0 in NODE.
apply (evnd_of_facts _ L pbrk md ms1 unit (fun _ => mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 a, Z_to_bv 64 n)] [] [])
(fun _ => munmap_model (Z_to_bv 64 a) (Z_to_bv 64 n) md) (fun _ => 0) tt NODE); [| reflexivity].
intros _. unfold FACTS. splits.
- cbn [ev_dec]. unfold dec_munmap. rewrite Hlen2, !bv_eqb_refl. reflexivity.
- reflexivity.
- cbn [ev_post_state ps_brk event_post].

set (L' := set_groups (g_remove a (ld_groups L)) L).
pose proof (kl_distinct _ _ _ HK) as Kd.
destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
{ intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
{ intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }

assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
b + mmap_len l <= a \/ a + n <= b).
{ intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
- exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
- unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
assert (NAwf : forall e, In e (vm_noaccess (m_vmmaps md)) -> elo e < ehi e <= 2^64) by (intros e He; exact (proj1 (kl_na _ _ _ HK e He))).
assert (Hhi : a + n < 2^64) by lia.
assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> Z_to_bv 64 a).
{ intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }

assert (Kne : forall e, In e (vm_maps (m_vmmaps md)) -> e <> went a n -> fst e <> Z_to_bv 64 a).
{ intros e He Hne Efst. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [E|D]; [exact (Hne E)|].
pose proof (proj1 (kl_wf _ _ _ HK) e He) as W. unfold edisj in D. rewrite B5, B6 in D.
unfold elo, ehi in D, W. rewrite Efst, Ua in D, W. lia. }
pose proof HK as HK0. kl_open HK. clear Kstart.
assert (Hph' : phase_inv (ld_brk L') L' pbrk (munmap_model (Z_to_bv 64 a) (Z_to_bv 64 n) md)).
{ eapply phase_quiet; [exact HK0| exact Hq| reflexivity| reflexivity| |]; unfold munmap_model, Mmap.with_mmap_destroyed; mproj; reflexivity. }
subst L'. constructor; try exact Hph'; unfold munmap_model, Mmap.with_mmap_destroyed; mproj; rewrite ?Ua, ?Un; auto.
+ rewrite Klazy. reflexivity.
+ apply vmwf_remove. exact Kwf.
+ pose proof (kl_start _ _ _ HK0). tauto.
+ intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. pose proof (Dother b0 l1 (or_introl Hin1) Hne) as D.
specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). splits; try assumption.
* apply In_map_remove. split; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
* apply region_free_subtract; auto; lia.
+ intros b0 l1 Hin0. apply Kgrr. exact (proj1 (Hg' b0 l1 Hin0)).
+ intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
* apply In_map_remove. split; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
* intros q' Hq1 Hq2. destruct (G9 q' Hq1 Hq2) as (e & He & Hel & Heh). pose proof (NAwf e He).
destruct (iv_subtract_contains (fst e) (snd e) a (a + n) (b0 + q' * PGSZ) (b0 + q' * PGSZ + PGSZ)
ltac:(lia) Hhi ltac:(unfold ehi in *; lia) Hel ltac:(lia) Heh ltac:(clear -D Hq1 Hq2 G5; nia)) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
+ rewrite Ezz, map_app, <- app_assoc. exact Kd1.
+ intros e' He'. destruct (maps_subtract_inside _ a (a + n) e' NAwf ltac:(lia) Hhi He') as (e & He & X1 & X2 & X3).
destruct (Kna e He) as (W & [(b0 & l1 & k & Hin0 & Y1 & Y2) | (b0 & l1 & E & Y1 & Y2 & Y3)]); split; try lia.
* left. exists b0, l1, k. splits; [exact Hin0| lia| lia].
* right. exists b0, l1. splits; [exact E| lia| lia|]. apply In_map_remove. split; [exact Y3|].
apply (Kne _ Y3). intros EG. pose proof (A6 b0 l1 E) as D6. pose proof (Kreg b0 l1 E) as (R1 & R2 & R3 & _).
pose proof (f_equal elo EG) as E1. pose proof (f_equal ehi EG) as E2.
rewrite B5, elo_went in E1 by lia. rewrite B6, ehi_went in E2 by lia. lia.
+ intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply In_map_remove. split; [exact He|].
apply (Kne _ He). intros ->. rewrite B5, B6 in Hr. pose proof (A6 b0 l1 E) as D6. lia.
- unfold munmap_model, Mmap.with_mmap_destroyed. eapply vm_only_trans; [| apply vm_only_forget]; apply vm_only_with_vmmaps; reflexivity.
- apply ACC_munmap_model. cbn. lia.
Qed.

#[using="Type"] Lemma evn_mprotect : forall L pbrk md ms1 b l k a,
KL L pbrk md -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
a = b + (1 + k) * PGSZ -> (2 + k) * PGSZ <= round_up_pg l ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMprotect a PGSZ PROT_RW) ms1 ->
EVND (EMprotect a PGSZ PROT_RW) L pbrk md ms1.
Proof.
intros L pbrk md ms1 b l k a HK Hq Hin Ha Hk2 Hat.
destruct Hat as (Hsvc & Ha0 & Ha1 & Ha2).
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana). linearize_mods.
pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
set (nb := mmap_len l) in *.
assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; nia).
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; lia).
assert (Hamod : a mod 4096 = 0) by (subst a; lia).
assert (H0 : ms_gpr ms1 0 = Z_to_bv 64 a) by (rewrite ms_gpr_areg0; exact Ha0).
assert (H1 : ms_gpr ms1 1 = Z_to_bv 64 PGSZ) by (rewrite ms_gpr_areg1; exact Ha1).
assert (H2 : ms_gpr ms1 2 = Z_to_bv 64 3) by (rewrite ms_gpr_areg2; exact Ha2).
assert (Hpn : Z_to_bv 64 (page_round_up_Z PGSZ) = Z_to_bv 64 PGSZ) by reflexivity.
assert (Hcn : map_contains (vm_noaccess (m_vmmaps md)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true).
{ destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh).
eapply map_contains_intro; [exact He| rewrite Ua; subst a; lia| rewrite Ua, Un; subst a; lia]. }
assert (Hcm : map_contains (vm_maps (m_vmmaps md)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true).
{ eapply map_contains_intro; [exact A5| rewrite B5, Ua; lia| rewrite B6, Ua, Un; lia]. }
pose proof (EdEvArm.Ms.mprotect_outcome_ekept segs ms1 (Z_to_bv 64 226) md (Z_to_bv 64 a) PGSZ eq_refl H0 ltac:(rewrite Ua; unfold page_size; exact Hamod)
H1 ltac:(lia) ltac:(rewrite Ua; change (page_round_up_Z PGSZ) with PGSZ; unfold two_pow_64; lia) H2
ltac:(rewrite Hpn; exact Hcn) ltac:(rewrite Hpn; exact Hcm) Hh) as [Hchk Hlive].
cbv zeta in Hchk. rewrite Hpn in Hchk.
set (ok := mprotect_budget_ok md (Z_to_bv 64 a) (Z_to_bv 64 PGSZ)) in *.

pose (IDX := ({e : Z | In e mprotect_errnos /\ mprotect_refusable md (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true} + {u : unit | ok = true})%type).
pose (effs := fun i : IDX =>
match i with
| inl (exist _ e _) => mkEffect (errno_ret e) [] []
| inr _ => mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 a, Z_to_bv 64 PGSZ)] end).
pose (ms' := fun i : IDX =>
match i with inl _ => md | inr _ => mprotect_model (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) md end).
pose (zf := fun i : IDX =>
match i with inl (exist _ e _) => neg_errno e | inr _ => 0 end).
assert (HinE : In ENOMEM mprotect_errnos) by (left; reflexivity).
assert (Herr : forall e, In e mprotect_errnos -> e = ENOMEM) by (intros e [<-|[]]; reflexivity).
assert (Hi0 : exists i0 : IDX, True).
{ destruct (Bool.bool_dec ok true) as [HR|HR]; [| apply Bool.not_true_is_false in HR].
- exists (inr (exist _ tt HR)). exact I.
- unshelve eexists (inl (exist _ ENOMEM (conj HinE _))); [| exact I].
rewrite mprotect_refusable_budget. fold ok. rewrite HR. reflexivity. }
destruct Hi0 as [i0 _].
unshelve epose proof (EdEvNode.node_ekept segs ms1 md (Z_to_bv 64 226) _ effs ms' Hh Hsvc Hlive _ _ _) as NODE.
{ intros o. rewrite (Hchk o). split.
- intros [(HR & e & He & ->) | (Hok & ->)]; [exists (inl (exist _ e (conj He HR)))| exists (inr (exist _ tt Hok))]; reflexivity.
- intros [[[e [He HR]]|[u Hok]] ->]; cbn [effs ms']; [left; split; [exact HR| exists e; auto]| right; auto]. }
{ intros [[e [He HR]]|[u Hok]]; cbn [ms']; unfold mprotect_model; mproj; exact Hh. }
{ intros [[e [He HR]]|[u Hok]]; cbn [ms']; unfold mprotect_model; mproj; exact Hlazy. }
unfold EVND. exists _, effs, ms', zf, i0. split; [exact NODE|]. split.
2:{
intros _ HF [[e [He HR]]|[u Hok]]; cbn [zf eclass]; [| reflexivity].
exfalso. rewrite mprotect_refusable_budget, (HF _ _) in HR. discriminate HR. }
intros [[e [He HR]]|[u Hok]]; cbn [effs ms' zf].
-
pose proof (Herr e He) as Ee. subst e. splits.
+ cbn [ev_dec]. unfold dec_mprotect_rw. cbn -[errno_of neg_errno errno_ret Z.eqb ENOSYS].
rewrite errno_of_errno_ret by (unfold ENOMEM; lia). change (ENOMEM =? ENOSYS) with false. reflexivity.
+ cbn [answer_ok]. unfold mprotect_answer_ok. rewrite is_errno_form_neg by (unfold ENOMEM; lia). apply orb_true_r.
+ cbn [ev_post_state ps_brk event_post].
replace ((neg_errno ENOMEM =? 0) || (neg_errno ENOMEM =? TWO64 - ENOSYS)) with false by reflexivity. exact HK.
+ apply vm_only_refl.
+ apply ACC_refl. cbn. lia.
-
splits.
+ cbn [ev_dec]. unfold dec_mprotect_rw, dec_mprotect. cbn -[bv_eqb Z_to_bv mmap_len Z.eqb bv_unsigned errno_of].
change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl. change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. reflexivity.
+ reflexivity.
+ cbn [ev_post_state ps_brk event_post]. change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true. cbv iota.
set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
pose proof (kl_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
b0 + mmap_len l0 <= b \/ b + nb <= b0).
{ intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
- exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
- unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
assert (NAwf : forall e, In e (vm_noaccess (m_vmmaps md)) -> elo e < ehi e <= 2^64) by (intros e He; exact (proj1 (kl_na _ _ _ HK e He))).
assert (Hhi : a + PGSZ < 2^64) by lia.
pose proof HK as HK0. kl_open HK. clear Kstart.
assert (Hph' : phase_inv (ld_brk L') L' pbrk (mprotect_model (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) md)).
{ eapply phase_quiet; [exact HK0| exact Hq| reflexivity| reflexivity| |]; unfold mprotect_model; mproj; reflexivity. }
subst L'. constructor; try exact Hph'; unfold mprotect_model; mproj; rewrite ?Ua, ?Un; auto.
* pose proof (kl_start _ _ _ HK0). tauto.
* intros b0 l0 Hin0. specialize (Kgr b0 l0 Hin0). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). splits; try assumption.
apply region_free_subtract; auto; lia.
* intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
specialize (Kme b1 l1 k0 Hin1). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Eqa|Na]; injection Eb as -> -> <-.
--
assert (Eb0 : b0 = b).
{ destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Eqa Hab G5 G6 H. nia. }
subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
splits; try assumption; try lia.
intros q' Hq1 Hq2. destruct (G9 q' ltac:(lia) Hq2) as (e & He & Hel & Heh). pose proof (NAwf e He).
destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b + q' * PGSZ) (b + q' * PGSZ + PGSZ)
ltac:(lia) Hhi ltac:(unfold ehi in *; lia) Hel ltac:(lia) Heh ltac:(right; subst a; clear -Hq1; nia)) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
-- splits; try assumption.
intros q' Hq1 Hq2. destruct (G9 q' Hq1 Hq2) as (e & He & Hel & Heh). pose proof (NAwf e He).
assert (D : b0 + mmap_len l0 <= b \/ b + nb <= b0).
{ destruct (Z.eq_dec b0 b) as [->|Hne].
{ pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. symmetry. exact Ha. }
exact (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne). }
destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q' * PGSZ) (b0 + q' * PGSZ + PGSZ)
ltac:(lia) Hhi ltac:(unfold ehi in *; lia) Hel ltac:(lia) Heh ltac:(clear -D Hab Hq1 Hq2 G5; nia)) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
* rewrite map_base_bump. exact Kdis.
* intros e' He'. destruct (maps_subtract_inside _ a (a + PGSZ) e' NAwf ltac:(lia) Hhi He') as (e & He & X1 & X2 & X3).
destruct (Kna e He) as (W & [(b0 & l1 & k1 & Hin0 & Y1 & Y2) | (b0 & l1 & E & Y1 & Y2 & Y3)]); split; try lia.
-- left. pose proof (in_map (bump_meta a) _ _ Hin0) as Hin0'. unfold bump_meta in Hin0'.
destruct (b0 + (1 + k1) * PGSZ =? a); [exists b0, l1, (k1 + 1)| exists b0, l1, k1]; splits; try exact Hin0'; lia.
-- right. exists b0, l1. splits; [exact E| lia| lia| exact Y3].
+ apply vm_only_with_vmmaps; reflexivity.
+ apply ACC_mprotect_model. cbn. lia.
Qed.

End Ev.

End RC__1.
