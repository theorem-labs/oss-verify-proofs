(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbrW QlEo_c1 Q5Rg QWxq_c1 QRjH Qn1e QiVh QSpR QuJV QZAi QUZl Q7S0 Qfya QYTG Ql2m QGeV QeZD QkRc QqWy Q6q3 EdEvNode EdEvArm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import QsjA QEpW QZDE QbrW QlEo_c1.Mq0 Q5Rg.Mq0.

Import QRjH.
Import Qn1e.Mq1.
Import QiVh.
Import QSpR.Mq2.
Import QuJV.Mq1.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QYTG.Mq0 Ql2m.Mq3 QGeV.
Import QeZD QkRc QqWy.Mq0.
Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Ltac lia ::= klia. Ltac mkr__lia_0 := klia.
Ltac nia ::= knia. Ltac mkr__nia_1 := knia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma wcov_rf_disj : forall maps lo hi aw nw,
wcov maps lo hi -> region_free maps aw nw = true -> 0 < bv_unsigned nw -> lo < hi ->
bv_unsigned aw + bv_unsigned nw <= lo \/ hi <= bv_unsigned aw.
Proof.
intros maps lo hi aw nw Hc Hrf Hn Hlh.
destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
destruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr).
pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.

#[using="Type"] Lemma is_errno_form_neg : forall e, 1 <= e <= 4095 -> is_errno_form (neg_errno e) = true.
Proof. intros e He. unfold is_errno_form, neg_errno, TWO64. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
#[using="Type"] Lemma is_err_neg : forall e, 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof. intros e He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.
#[using="Type"] Lemma errno_ret_neg : forall e, errno_ret e = Z_to_bv 64 (neg_errno e).
Proof.
intros e. unfold errno_ret, neg_errno. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
rewrite <- (Z.mod_add (-e) 1 (2^64)) by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma KL_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
KL L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
let h := m_vmmaps mo in let n := mmap_len len in
mmap_addr_ok len [] a = true ->
region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
m_halted mo' = None -> m_vm_lazy mo' = [] ->
m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
(if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
/\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false.
Proof.
intros L pbrk mo mo' a len isnone HK Hq Hlen h n Hok Hrf Hh' Hl' Evm.
apply mmap_addr_ok_true in Hok as [(A1 & A2 & A3) _]. rewrite page_size_eq in A1. rewrite alloc_ceiling_State in A3. fold n in A3.
pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).

assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
a + n <= b0 \/ b0 + mmap_len l0 <= a).
{ intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
{ intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; lia)) as D. rewrite Ua, Un in D. exact D. }

assert (Dna : forall e, In e (vm_noaccess h) -> a + n <= elo e \/ ehi e <= a).
{ intros e He. destruct (kl_na _ _ _ HK e He) as (W & [(b0 & l0 & k & Hin & X1 & X2) | (b0 & l0 & E & X1 & X2 & X3)]).
- pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))). lia.
- pose proof (region_free_disj _ _ _ _ Hrfm X3) as D. rewrite Ua, Un in D.
pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & _).
rewrite elo_went, ehi_went in D by lia. lia. }
split; [|split].
2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
eapply KL_ranges_free; [exact HK| lia| lia| exact A3| exact Hrf]. }
2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
{ intros Hin. apply in_app_or in Hin as [Hin|Hin].
- apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
- apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
pose proof HK as HK0. kl_open HK.
assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
match ld_brk L' with
| BPUntried => vm_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo') /\ ld_brkreg L' = None
| BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo')) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur /\ pbrk = cur /\ ld_brkreg L' = None
| BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo'))
/\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
/\ ld_brkreg L' = None /\ cur + 2 * PGSZ <= alloc_ceiling
/\ In (went cur (2 * PGSZ)) (vm_maps (m_vmmaps mo'))
/\ (forall b l, In (b, l) (ld_groups L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
/\ (forall b l k, In (b, l, k) (ld_metas L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
| BPLive => exists b l, ld_brkreg L' = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = b + l /\ pbrk = b + l
| BPDead => True
end).
{ intros L' E1 E2. rewrite E1, E2, Evm. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
destruct (ld_brk L); try contradiction; auto. }
destruct isnone; constructor;
first [ apply (Hph' (set_metas _ L)); reflexivity
| apply (Hph' (set_groups _ L)); reflexivity
| rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
- apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
- intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7).
unfold brk_disj in *; cbn. splits; auto with datatypes.
cbn [region_free]. change (vm_noaccess h) with (vm_noaccess (m_vmmaps mo)). rewrite G7, andb_true_r. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (Dgm b0 l0 (or_introl Hin)) as D. unfold iv_overlap. unfold went, wz in B5, B6. rewrite elo_pair in B5. rewrite ehi_pair in B6.
rewrite Ua, Un. apply Bool.negb_true_iff. apply Bool.andb_false_iff. unfold wz. rewrite B6, B5.
destruct D as [D|D]; [left| right]; apply (proj2 (Z.ltb_ge _ _)); lia.
- intros b0 l0 k [E|Hin].
+ injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia; try (left; reflexivity); try exact Dbrk.
intros q Hq1 Hq2. exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n in Hq2. lia.
+ specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
- cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
- intros e [<-|He].
+ split; [rewrite elo_pair, ehi_pair, Ua, Un; lia|]. left. exists a, len, 0. split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n. lia.
+ destruct (Kna e He) as (W & [(b0 & l0 & k & Hin & X) | (b0 & l0 & E & X1 & X2 & X3)]); split; try exact W.
* left. exists b0, l0, k. split; [right; exact Hin| exact X].
* right. exists b0, l0. splits; auto with datatypes.
- intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
- apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
- intros b0 l0 [E|Hin].
+ injection E as <- <-. unfold brk_disj; cbn. splits; try lia; try (left; reflexivity); try exact Dbrk.
apply region_free_intro. intros e He. unfold wz. fold n. rewrite Ua, Un. apply Dna. exact He.
+ specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
- intros b0 l0 [E|Hin]; [| apply Kgrr; exact Hin]. injection E as <- <-. unfold wz. fold n. exact (region_free_app_l _ _ _ _ Hrf).
- intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
- cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
- intros e He. destruct (Kna e He) as (W & [(b0 & l0 & k & Hin & X) | (b0 & l0 & E & X1 & X2 & X3)]); split; try exact W.
+ left. exists b0, l0, k. auto.
+ right. exists b0, l0. splits; auto with datatypes.
- intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
Qed.

Section Ev.
Variable segs : list Segment.

#[using="Type"] Lemma ev1_mmap_anon : forall L pbrk md ms1 (J : config -> Prop) len prot,
NClosed segs J -> KL L pbrk md -> brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMmap 0 len prot MAPF) ms1 ->
(forall rsp z md',
ev_dec (EMmap 0 len prot MAPF) pbrk rsp = Some z -> answer_ok L (EMmap 0 len prot MAPF) z = true ->
KL (event_post L (EMmap 0 len prot MAPF) z) (ps_brk (ev_post_state (EMmap 0 len prot MAPF) rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Proof.
intros L pbrk md ms1 J len prot HJ HK Hq Hprot Hlen Hat HC.
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
destruct Hprot as [-> | ->].
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
assert (Hi0 : exists i0 : IDX, True).
{ destruct (Bool.bool_dec (mmap_reserve_refusable md (mmap_len len)) true) as [HR|HR]; [| apply Bool.not_true_is_false in HR].
- exists (inl (exist _ ENOMEM (conj ENOMEM_in_mmap_errnos HR))). exact I.
- destruct (not_refusable_grant_ok_na (ms_gpr ms1 0) md (mmap_len len) HR) as [a Ha]. exists (inr (exist _ a Ha)). exact I. }
destruct Hi0 as [i0 _].
apply (EdEvNode.ncl_ekept segs J ms1 md (Z_to_bv 64 222) _ effs ms' i0 HJ Hh Hsvc (EdEvArm.Ms.mmap_noaccess_outcome_live segs ms1 (Z_to_bv 64 222) md eq_refl Hargs Hh)).
+ intros o. rewrite (EdEvArm.Ms.mmap_noaccess_outcome_ekept segs ms1 (Z_to_bv 64 222) md eq_refl Hargs o). unfold mmap_len in IDX, effs, ms'. rewrite U1. split.
* intros [(HR & e & He & ->) | (a & Ha & ->)]; [exists (inl (exist _ e (conj He HR)))| exists (inr (exist _ a Ha))]; reflexivity.
* intros [[[e [He HR]]|[a Ha]] ->]; [left; split; [exact HR| exists e; auto]| right; exists a; auto].
+ intros [[e [He HR]]|[a Ha]]; cbn [ms']; [exact Hh| rewrite <- Hh; reflexivity].
+ intros [[e [He HR]]|[a Ha]]; cbn [ms']; [exact Hlazy| rewrite <- Hlazy; reflexivity].
+ intros [[e [He HR]]|[a Ha]]; cbn [effs ms'].
*
pose proof (mmap_errno_range e He) as Her. assert (E12 : e = 12) by (destruct He as [<-|[]]; reflexivity).
apply (HC (mkEffect (errno_ret e) [] []) (neg_errno e) md).
-- cbn [ev_dec]. rewrite Hfix. change (PROT_NONE =? 0) with true. cbv iota.
cbn -[errno_of neg_errno errno_ret]. rewrite errno_of_errno_ret by lia. rewrite E12. reflexivity.
-- cbn [answer_ok]. rewrite Hfix'. unfold mmap_answer_ok. rewrite is_errno_form_neg by lia. reflexivity.
-- cbn [ev_post_state ps_brk event_post]. rewrite Hfix', is_err_neg by lia. exact HK.
-- apply vm_only_refl.
*
set (n := mmap_len len) in *.
unfold grant_ok_na in Ha.
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
apply (HC (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []) (bv_unsigned a)).
-- cbn [ev_dec]. rewrite Hfix. change (PROT_NONE =? 0) with true. cbv iota.
unfold dec_mmap_none. fold n. rewrite !bv_eqb_refl, Hok. reflexivity.
-- cbn [answer_ok]. rewrite Hfix'. exact Hans.
-- cbn [ev_post_state ps_brk event_post]. rewrite Hfix', Herr. change (PROT_NONE =? PROT_NONE) with true. cbv iota. exact HK'.
-- apply vm_only_with_vmmaps; reflexivity.
-
assert (Hargs : mmap_args_ok ms1).
{ unfold mmap_args_ok. rewrite ms_gpr_areg2, ms_gpr_areg3, ms_gpr_areg4, ms_gpr_areg5. auto 10. }

assert (H3 : ms_gpr ms1 3 = Z_to_bv 64 34) by (rewrite ms_gpr_areg3; exact Ha3).
pose (IDX := ({e : Z | In e mmap_errnos /\ mmap_grant_refusable (ms_gpr ms1 3) md (mmap_len len) = true}
+ {a : word | grant_ok (ms_gpr ms1 0) md a (mmap_len len) = true})%type).
pose (effs := fun i : IDX =>
match i with
| inl (exist _ e _) => mkEffect (errno_ret e) [] []
| inr (exist _ a _) => mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))] end).
pose (ms' := fun i : IDX =>
match i with inl _ => md | inr (exist _ a _) => mmap_model a (Z_to_bv 64 (mmap_len len)) md end).
assert (Hi0 : exists i0 : IDX, True).
{ destruct (Bool.bool_dec (mmap_grant_refusable (ms_gpr ms1 3) md (mmap_len len)) true) as [HR|HR]; [| apply Bool.not_true_is_false in HR].
- exists (inl (exist _ ENOMEM (conj ENOMEM_in_mmap_errnos HR))). exact I.
- rewrite H3 in HR. destruct (not_refusable_grant_ok (ms_gpr ms1 0) md (mmap_len len) HR) as [a Ha]. exists (inr (exist _ a Ha)). exact I. }
destruct Hi0 as [i0 _].
apply (EdEvNode.ncl_ekept segs J ms1 md (Z_to_bv 64 222) _ effs ms' i0 HJ Hh Hsvc (EdEvArm.Mm.mmap_outcome_live segs ms1 (Z_to_bv 64 222) md eq_refl Hargs Hh)).
+ intros o. rewrite (EdEvArm.Mm.mmap_outcome_ekept segs ms1 (Z_to_bv 64 222) md o eq_refl Hargs). rewrite Hpr. unfold mmap_len in IDX, effs, ms' |- *. rewrite U1. split.
* intros [(HR & e & He & ->) | (a & Ha & ->)]; [exists (inl (exist _ e (conj He HR)))| exists (inr (exist _ a Ha))]; reflexivity.
* intros [[[e [He HR]]|[a Ha]] ->]; [left; split; [exact HR| exists e; auto]| right; exists a; auto].
+ intros [[e [He HR]]|[a Ha]]; cbn [ms']; [exact Hh| rewrite <- Hh; reflexivity].
+ intros [[e [He HR]]|[a Ha]]; cbn [ms']; [exact Hlazy| rewrite <- Hlazy; reflexivity].
+ intros [[e [He HR]]|[a Ha]]; cbn [effs ms'].
*
pose proof (mmap_errno_range e He) as Her. assert (E12 : e = 12) by (destruct He as [<-|[]]; reflexivity).
apply (HC (mkEffect (errno_ret e) [] []) (neg_errno e) md).
-- cbn [ev_dec]. rewrite Hfix. change (PROT_RW =? 0) with false. cbv iota.
cbn -[errno_of neg_errno errno_ret]. rewrite errno_of_errno_ret by lia. rewrite E12. reflexivity.
-- cbn [answer_ok]. rewrite Hfix'. unfold mmap_answer_ok. rewrite is_errno_form_neg by lia. reflexivity.
-- cbn [ev_post_state ps_brk event_post]. rewrite Hfix', is_err_neg by lia. exact HK.
-- apply vm_only_refl.
*
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
apply (HC (mkEffect a [] [(a, Z_to_bv 64 n)]) (bv_unsigned a)).
-- cbn [ev_dec]. rewrite Hfix. change (PROT_RW =? 0) with false. cbv iota.
unfold dec_mmap. fold n. rewrite !bv_eqb_refl, Hok. reflexivity.
-- cbn [answer_ok]. rewrite Hfix'. exact Hans.
-- cbn [ev_post_state ps_brk event_post]. rewrite Hfix', Herr. change (PROT_RW =? PROT_NONE) with false. cbv iota. exact HK'.
-- apply vm_only_with_vmmaps; reflexivity.
Qed.

End Ev.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section TargetStmt.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable ENTRY : Z.

Variable G : (word -> option byte) -> Prop.
Notation segs := (hl_segs L).
Notation HEAPx := (HEAP L HIx).

Definition T_LOCCELL : Z := hl_tp L - 48.
Definition T_GLOBLOC : Z := hl_libc L + 56.
Definition T_LOCALE_LOCK : Z := hl_libc L + 0xd8.

Definition TGT_STACK : Z := 0x100000.

Definition xtgt (a : Z) : Prop := hl_volatile L a \/ (T_LOCCELL <= a < T_LOCCELL + 8).

Definition target_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB : list blk) (data size lo : Z) (payload : list byte) (errv : word),
HEAPx A LB m md ->

bytes_at segs m data payload -> Z.of_nat (length payload) = size ->
0 <= size < 2^26 -> 0 < data -> data + size < 2^63 ->
data + size <= alloc_ceiling ->
(size = 0 \/ In (data, size) LB) ->

rw_cells segs m T_LOCCELL [C8 (Z_to_bv 64 T_GLOBLOC)] ->
rw_cells segs m T_LOCALE_LOCK [C4 (Z_to_bv 64 0)] ->
G m ->

stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - TGT_STACK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top L HIx -> hi_top L HIx < 2^62 ->
rw_cells segs m (hl_tp L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned ra mod 2 = 0 ->
frm0 fc ->
a0 = Z_to_bv 64 data -> a1 = Z_to_bv 64 size ->
(forall ms' m' md' (A' : AS L HIx) (errv' : word) (gp' : word) (LK : list blk),
ret_statew L ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_presx L xtgt LB (bv_unsigned sp) m m' ->
rw_cells segs m' T_LOCCELL [C8 (Z_to_bv 64 T_GLOBLOC)] ->
rw_cells segs m' (hl_tp L - 164) [C4 errv'] ->
G m' ->
HEAPx A' (LB ++ LK) m' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) md) T.
End TargetStmt.
End RC__1.
