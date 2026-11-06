(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV.Mq1.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkRc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyuL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyuL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Ltac lia ::= klia. Ltac mkr__lia_0 := klia.
Ltac nia ::= knia. Ltac mkr__nia_1 := knia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma g_remove_split : forall a l0 (l : list (Z * Z)) (M : list Z), In (a, l0) l -> List.NoDup (map fst l ++ M) ->
exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
destruct (Z.eqb_spec x1 a) as [->|Hne].
- destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
- destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

#[using="Type"] Lemma phase_quiet : forall L L' pbrk mo mo',
KL L pbrk mo -> brk_quiet L -> ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) -> vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
phase_inv (ld_brk L') L' pbrk mo'.
Proof.
intros L L' pbrk mo mo' HK Hq E1 E2 E3 E4. pose proof (kl_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv.
rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

#[using="Type"] Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
- exfalso. apply H1. rewrite E. apply in_map. exact Hy.
- exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

#[using="Type"] Lemma map_base_bump : forall a ms, map (fun m : Z * Z * Z => fst (fst m)) (map (bump_meta a) ms) = map (fun m => fst (fst m)) ms.
Proof.
intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

Section Ev.
Variable segs : list Segment.

#[using="Type"] Lemma ev1_munmap : forall L pbrk md ms1 (J : config -> Prop) a l0 len,
NClosed segs J -> KL L pbrk md -> brk_quiet L -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMunmap a len) ms1 ->
(forall rsp z md',
ev_dec (EMunmap a len) pbrk rsp = Some z -> answer_ok L (EMunmap a len) z = true ->
KL (event_post L (EMunmap a len) z) (ps_brk (ev_post_state (EMunmap a len) rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Proof.
intros L pbrk md ms1 J a l0 len HJ HK Hq Hin Hlen Hat HC.
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
apply (ncl_det segs J ms1 md (Z_to_bv 64 215) (munmap_eff ms1) (munmap_model (Z_to_bv 64 a) (Z_to_bv 64 n) md) HJ Hh Hsvc).
{ intros o. rewrite (munmap_outcome_si segs ms1 (Z_to_bv 64 215) md o eq_refl Hargs). rewrite Hpr, H0. reflexivity. }
{ unfold munmap_model, with_mmap_destroyed. mproj. exact Hh. }
{ unfold munmap_model, with_mmap_destroyed. mproj. rewrite Hlazy. reflexivity. }
unfold munmap_eff. rewrite Hpr, H0.
apply (HC (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 a, Z_to_bv 64 n)] [] []) 0).
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
{ eapply phase_quiet; [exact HK0| exact Hq| reflexivity| reflexivity| |]; unfold munmap_model, with_mmap_destroyed; mproj; reflexivity. }
subst L'. constructor; try exact Hph'; unfold munmap_model, with_mmap_destroyed; mproj; rewrite ?Ua, ?Un; auto.
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
- unfold munmap_model, with_mmap_destroyed. eapply vm_only_trans; [| apply vm_only_forget]; apply vm_only_with_vmmaps; reflexivity.
Qed.

#[using="Type"] Lemma ev1_mprotect : forall L pbrk md ms1 (J : config -> Prop) b l k a,
NClosed segs J -> KL L pbrk md -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
a = b + (1 + k) * PGSZ -> (2 + k) * PGSZ <= round_up_pg l ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMprotect a PGSZ PROT_RW) ms1 ->
(forall rsp z md',
ev_dec (EMprotect a PGSZ PROT_RW) pbrk rsp = Some z -> answer_ok L (EMprotect a PGSZ PROT_RW) z = true ->
KL (event_post L (EMprotect a PGSZ PROT_RW) z) (ps_brk (ev_post_state (EMprotect a PGSZ PROT_RW) rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Proof.
intros L pbrk md ms1 J b l k a HJ HK Hq Hin Ha Hk2 Hat HC.
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
assert (HinE : In ENOMEM mprotect_errnos) by (left; reflexivity).
assert (Herr : forall e, In e mprotect_errnos -> e = ENOMEM) by (intros e [<-|[]]; reflexivity).
assert (Hi0 : exists i0 : IDX, True).
{ destruct (Bool.bool_dec ok true) as [HR|HR]; [| apply Bool.not_true_is_false in HR].
- exists (inr (exist _ tt HR)). exact I.
- unshelve eexists (inl (exist _ ENOMEM (conj HinE _))); [| exact I].
rewrite mprotect_refusable_budget. fold ok. rewrite HR. reflexivity. }
destruct Hi0 as [i0 _].
apply (EdEvNode.ncl_ekept segs J ms1 md (Z_to_bv 64 226) _ effs ms' i0 HJ Hh Hsvc Hlive).
{ intros o. rewrite (Hchk o). split.
- intros [(HR & e & He & ->) | (Hok & ->)]; [exists (inl (exist _ e (conj He HR)))| exists (inr (exist _ tt Hok))]; reflexivity.
- intros [[[e [He HR]]|[u Hok]] ->]; cbn [effs ms']; [left; split; [exact HR| exists e; auto]| right; auto]. }
{ intros [[e [He HR]]|[u Hok]]; cbn [ms']; unfold mprotect_model; mproj; exact Hh. }
{ intros [[e [He HR]]|[u Hok]]; cbn [ms']; unfold mprotect_model; mproj; exact Hlazy. }
intros [[e [He HR]]|[u Hok]]; cbn [effs ms'].
-
rewrite (Herr e He).
apply (HC (mkEffect (errno_ret ENOMEM) [] []) (neg_errno ENOMEM) md).
+ cbn [ev_dec]. unfold dec_mprotect_rw. cbn -[errno_of neg_errno errno_ret Z.eqb ENOSYS].
rewrite errno_of_errno_ret by (unfold ENOMEM; lia). change (ENOMEM =? ENOSYS) with false. reflexivity.
+ cbn [answer_ok]. unfold mprotect_answer_ok. rewrite is_errno_form_neg by (unfold ENOMEM; lia). apply orb_true_r.
+ cbn [ev_post_state ps_brk event_post].
replace ((neg_errno ENOMEM =? 0) || (neg_errno ENOMEM =? TWO64 - ENOSYS)) with false by reflexivity. exact HK.
+ apply vm_only_refl.
-
apply (HC (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 a, Z_to_bv 64 PGSZ)]) 0).
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
Qed.

End Ev.

End RC__1.
