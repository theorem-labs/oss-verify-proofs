(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbrW QlEo_c1 Q5Rg QWxq_c1 QRjH QiVh QSpR QZAi QUZl Q7S0 Qfya QYTG Ql2m QGeV QeZD QkRc Q6q3 EdEvNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.
Import QsjA QEpW QZDE QbrW QlEo_c1.Mq0 Q5Rg.Mq0.

Import QRjH.
Import QiVh.
Import QSpR.Mq2.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QYTG.Mq0 Ql2m.Mq3 QGeV.
Import QeZD QkRc.
Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Ltac lia ::= klia. Ltac mkr__lia_0 := klia.
Ltac nia ::= knia. Ltac mkr__nia_1 := knia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ms_gpr_areg0 : forall ms, ms_gpr ms 0 = QWxq_c1.Mq1.areg ms 10. Proof. reflexivity. Qed.
#[using="Type"] Lemma ms_gpr_areg1 : forall ms, ms_gpr ms 1 = QWxq_c1.Mq1.areg ms 11. Proof. reflexivity. Qed.
#[using="Type"] Lemma ms_gpr_areg2 : forall ms, ms_gpr ms 2 = QWxq_c1.Mq1.areg ms 12. Proof. reflexivity. Qed.
#[using="Type"] Lemma ms_gpr_areg3 : forall ms, ms_gpr ms 3 = QWxq_c1.Mq1.areg ms 13. Proof. reflexivity. Qed.
#[using="Type"] Lemma ms_gpr_areg4 : forall ms, ms_gpr ms 4 = QWxq_c1.Mq1.areg ms 14. Proof. reflexivity. Qed.
#[using="Type"] Lemma ms_gpr_areg5 : forall ms, ms_gpr ms 5 = QWxq_c1.Mq1.areg ms 15. Proof. reflexivity. Qed.

#[using="Type"] Lemma u214 : bv_unsigned (Z_to_bv 64 214) = 214. Proof. reflexivity. Qed.

Section Ev.
Variable segs : list Segment.

Definition EV1 (e : ev) : Prop :=
forall L pbrk md ms1 (J : config -> Prop),
NClosed segs J -> KL L pbrk md -> event_pre L e -> ev_at segs e ms1 ->
(forall rsp z md',
ev_dec e pbrk rsp = Some z -> answer_ok L e z = true ->
KL (event_post L e z) (ps_brk (ev_post_state e rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).

#[using="Type"] Lemma ev1_brk0 : forall L pbrk md ms1 (J : config -> Prop),
NClosed segs J -> KL L pbrk md -> ld_brk L = BPUntried -> QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NBrk 0) ms1 ->
(forall rsp z md',
ev_dec (EBrk 0) pbrk rsp = Some z -> answer_ok L (EBrk 0) z = true ->
KL (event_post L (EBrk 0) z) (ps_brk (ev_post_state (EBrk 0) rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Proof.
intros L pbrk md ms1 J HJ HK Hph [Hsvc Ha0] HC.
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
assert (H0 : ms_gpr ms1 0 = Z_to_bv 64 0) by (rewrite ms_gpr_areg0; exact Ha0).
set (b := vm_brk (m_vmmaps md)).
assert (Hcases : forall r, brk_resolution_ok md (ms_gpr ms1 0) r <-> r = b).
{ intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
apply (EdEvNode.Mb.ncl_brk segs J ms1 md (Z_to_bv 64 214) HJ Hh Hlazy Hsvc u214).
intros [r Hr]. cbn [proj1_sig].
pose proof (proj1 (Hcases r) Hr) as Er. subst r.
rewrite H0, brk_zeros_query, brk_unmaps_keep.
rewrite (brk_model_query _ md eq_refl), vmmaps_eta, with_vmmaps_eta.
apply (HC (mkEffectU b [] [] [] [] []) (bv_unsigned b) md).
- reflexivity.
-
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk _].
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
cbn [answer_ok Z.eqb]. unfold brk0_answer_ok. subst b. rewrite Ebrk.
pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps md))) as R. unfold bv_modulus in R.
unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- cbn [ev_post_state Z.eqb dec_brk0 set_brk_ps ps_brk event_post].
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
eapply KL_rephase; [exact HK|]. cbn [phase_inv]. subst b. rewrite Ebrk. splits; auto.
- apply vm_only_refl.
Qed.

#[using="Type"] Lemma listNN_eqb_refl : forall l, listNN_eqb l l = true.
Proof. intros l. apply (proj2 (listNN_eqb_eq l l)). reflexivity. Qed.

#[using="Type"] Lemma brk_grow_node : forall md ms1 (J : config -> Prop) (pbrk d : Z),
NClosed segs J -> m_halted md = None -> m_vm_lazy md = [] ->
bv_unsigned (vm_brk (m_vmmaps md)) = pbrk -> 0 < pbrk -> pbrk mod PGSZ = 0 -> 0 < d -> d mod PGSZ = 0 -> pbrk + d < 2^63 ->
bv_unsigned (vm_start_brk (m_vmmaps md)) <= pbrk + d ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NBrk (pbrk + d)) ms1 ->
J (mkCfg (nret ms1 (mkEffectU (vm_brk (m_vmmaps md)) [] [] [] [] [])) md) ->
(Mmap.brk_grow_ok md (Z_to_bv 64 (pbrk + d)) (Z_to_bv 64 (pbrk + d)) = true ->
J (mkCfg (nret ms1 (mkEffectU (Z_to_bv 64 (pbrk + d)) [] [(vm_brk (m_vmmaps md), Z_to_bv 64 d)] [] [] []))
(with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps md)) ((vm_brk (m_vmmaps md), Z_to_bv 64 d) :: vm_maps (m_vmmaps md))
(vm_noaccess (m_vmmaps md)) (vm_start_brk (m_vmmaps md))
(Z_to_bv 64 (pbrk + d)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))) md))) ->
J (mkCfg ms1 md).
Proof.
intros md ms1 J pbrk d HJ Hh Hlazy Ub Hp0 Hpal Hd Hdal Hnw Hs [Hsvc Ha0] HA HB. linearize_mods.
set (h := m_vmmaps md) in *. set (b := vm_brk h) in *.
set (req := Z_to_bv 64 (pbrk + d)) in *.
assert (Hureq : bv_unsigned req = pbrk + d) by (unfold req; apply unsigned_lit; lia).
assert (H0 : ms_gpr ms1 0 = req) by (rewrite ms_gpr_areg0; exact Ha0).
assert (Hcases : forall r, brk_resolution_ok md (ms_gpr ms1 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok md req req = true))).
{ intros r. rewrite H0. pose proof (brk_r_ok_grow_cases md req r) as X. cbv zeta in X. fold h b in X.
apply X; rewrite ?Hureq, ?Ub; lia. }
apply (EdEvNode.Mb.ncl_brk segs J ms1 md (Z_to_bv 64 214) HJ Hh Hlazy Hsvc u214).
intros [r Hr]. cbn [proj1_sig]. fold h b.
destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
- rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep. exact HA.
- assert (Hlt : bv_unsigned b < bv_unsigned req) by (rewrite Hureq; lia).
assert (Hneq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hneq0 ltac:(lia) Hlt), (brk_unmaps_grow req b) by lia.
unfold brk_page_range.
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

#[using="Type"] Lemma brk_grow_ok_facts : forall md pbrk d,
let h := m_vmmaps md in
bv_unsigned (vm_brk h) = pbrk -> 0 < pbrk -> pbrk mod PGSZ = 0 -> 0 < d -> d mod PGSZ = 0 -> pbrk + d < 2^63 ->
Mmap.brk_grow_ok md (Z_to_bv 64 (pbrk + d)) (Z_to_bv 64 (pbrk + d)) = true ->
alloc_top h = alloc_ceiling ->
pbrk + d <= alloc_ceiling /\
region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 pbrk) (Z_to_bv 64 d) = true /\
region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 pbrk) (Z_to_bv 64 (d + PGSZ)) = true.
Proof.
intros md pbrk d h Ub Hp0 Hpal Hd Hdal Hnw Hg Hceil. linearize_mods.
unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in Hg. cbv zeta in Hg. fold h in Hg. rewrite Ub in Hg.
rewrite (unsigned_lit (pbrk + d)) in Hg by lia.
rewrite (proj2 (Z.ltb_lt 0 pbrk) Hp0), (proj2 (Z.ltb_lt pbrk (pbrk + d))) in Hg by lia. cbn [andb] in Hg.
rewrite (page_round_up_Z_aligned pbrk) in Hg by (unfold page_size; lia).
rewrite (page_round_up_Z_aligned (pbrk + d)) in Hg by (unfold page_size; lia).
rewrite (proj2 (Z.ltb_lt pbrk (pbrk + d))) in Hg by lia.
apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [H1 H2].
apply Z.leb_le in H1. rewrite Hceil in H1. replace (pbrk + d + page_size - pbrk) with (d + PGSZ) in H2 by (unfold page_size; lia).
pose proof alloc_ceiling_lt as Hcl.
split; [exact H1|]. split; [| exact H2].
apply (region_free_shrink _ _ _ _ H2). rewrite !unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma ev1_brk_grow1 : forall L pbrk md ms1 (J : config -> Prop) cur req,
NClosed segs J -> KL L pbrk md -> ld_brk L = BPQueried cur ->
req = round_up_pg cur + 2 * PGSZ ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NBrk req) ms1 ->
(forall rsp z md',
ev_dec (EBrk req) pbrk rsp = Some z -> answer_ok L (EBrk req) z = true ->
KL (event_post L (EBrk req) z) (ps_brk (ev_post_state (EBrk req) rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Proof.
intros L pbrk md ms1 J cur req HJ HK Hph Hreq Hat HC. pose proof alloc_ceiling_lt as Hcl.
pose proof (kl_halt _ _ _ HK) as Hh. pose proof (kl_lazy _ _ _ HK) as Hlazy.
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
subst pbrk. rename cur into pbrk.
assert (Hpal : pbrk mod PGSZ = 0) by (rewrite Ecur; exact S2). linearize_mods.
assert (Hrc : round_up_pg pbrk = pbrk) by (apply round_up_pg_aligned; lia).
assert (Ereq : req = pbrk + 2 * PGSZ) by (rewrite Hreq, Hrc; lia).
clear Hreq. subst req.
assert (Hne : pbrk + 2 * PGSZ =? 0 = false) by (apply Z.eqb_neq; unfold PGSZ; lia).
eapply (brk_grow_node md ms1 J pbrk (2 * PGSZ) HJ Hh Hlazy); try exact Hat.
- exact Ebrk.
- lia.
- exact Hpal.
- unfold PGSZ; lia.
- reflexivity.
- unfold PGSZ in *; lia.
- lia.
-
apply (HC (mkEffectU (vm_brk (m_vmmaps md)) [] [] [] [] []) pbrk md).
+ cbn [ev_dec]. rewrite Hne. unfold dec_brk. rewrite Ebrk, Z.eqb_refl. reflexivity.
+ cbn [answer_ok]. rewrite Hne, Hph. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r.
replace (pbrk =? pbrk + 2 * PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). reflexivity.
+ cbn [ev_post_state ps_brk]. rewrite Hne. unfold dec_brk. rewrite Ebrk, Z.eqb_refl. cbn [andb ps_brk event_post].
rewrite Hne. replace (pbrk =? pbrk + 2 * PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia).
eapply KL_dead. exact HK.
+ apply vm_only_refl.
-
intros Hg.
destruct (brk_grow_ok_facts md pbrk (2 * PGSZ) Ebrk ltac:(lia) Hpal ltac:(unfold PGSZ; lia) eq_refl ltac:(unfold PGSZ in *; lia) Hg (kl_ceil _ _ _ HK)) as (Hceil & Hrf & Hrf2).
set (b := vm_brk (m_vmmaps md)) in *.
assert (Eb : b = Z_to_bv 64 pbrk) by (symmetry; apply Z_to_bv_u_eq'; symmetry; exact Ebrk).
apply (HC (mkEffectU (Z_to_bv 64 (pbrk + 2 * PGSZ)) [] [(b, Z_to_bv 64 (2 * PGSZ))] [] [] []) (pbrk + 2 * PGSZ)).
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
Qed.

#[using="Type"] Lemma ev1_brk_grow2 : forall L pbrk md ms1 (J : config -> Prop) b0 l0 req,
NClosed segs J -> KL L pbrk md -> ld_brk L = BPLive -> ld_brkreg L = Some (b0, l0) ->
req = b0 + l0 + PGSZ ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NBrk req) ms1 ->
(forall rsp z md',
ev_dec (EBrk req) pbrk rsp = Some z -> answer_ok L (EBrk req) z = true ->
KL (event_post L (EBrk req) z) (ps_brk (ev_post_state (EBrk req) rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Proof.
intros L pbrk md ms1 J b0 l0 req HJ HK Hph Hreg Hreq Hat HC. pose proof alloc_ceiling_small as Hcl.
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
eapply (brk_grow_node md ms1 J (b0 + l0) PGSZ HJ Hh Hlazy); try exact Hat.
- exact Ebrk.
- lia.
- exact Hal.
- unfold PGSZ; lia.
- reflexivity.
- unfold PGSZ in *; lia.
- lia.
-
apply (HC (mkEffectU (vm_brk (m_vmmaps md)) [] [] [] [] []) (b0 + l0) md).
+ cbn [ev_dec]. rewrite Hne. unfold dec_brk. rewrite Ebrk, Z.eqb_refl. reflexivity.
+ cbn [answer_ok]. rewrite Hne, Hph, Hreg. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r.
replace (b0 + l0 =? b0 + l0 + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). reflexivity.
+ cbn [ev_post_state ps_brk]. rewrite Hne. unfold dec_brk. rewrite Ebrk, Z.eqb_refl. cbn [andb ps_brk event_post].
rewrite Hne. replace (b0 + l0 =? b0 + l0 + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia).
eapply KL_dead. exact HK.
+ apply vm_only_refl.
-
intros Hg.
destruct (brk_grow_ok_facts md (b0 + l0) PGSZ Ebrk ltac:(lia) Hal ltac:(unfold PGSZ; lia) eq_refl ltac:(unfold PGSZ in *; lia) Hg (kl_ceil _ _ _ HK)) as (Hceil & Hrf & Hrf2).
set (b := vm_brk (m_vmmaps md)) in *.
assert (Eb : b = Z_to_bv 64 (b0 + l0)) by (symmetry; apply Z_to_bv_u_eq'; symmetry; exact Ebrk).
apply (HC (mkEffectU (Z_to_bv 64 (b0 + l0 + PGSZ)) [] [(b, Z_to_bv 64 PGSZ)] [] [] []) (b0 + l0 + PGSZ)).
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
Qed.

End Ev.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Ltac lia ::= klia. Ltac mkr__lia_0 := klia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition mints (md : Model) : list (word * word) := vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md).
Definition szok (l : list (word * word)) : Prop := Forall (fun p => bv_unsigned (snd p) <= 2^30) l.
Definition MAXINT : Z := 40000.

Definition BUD (md : Model) (W : Z) (D : nat) : Prop :=
m_vm_lazy md = [] /\ m_vm_materialized md = [] /\ 0 <= W /\
vm_live_bytes (m_vmmaps md) + W <= vm_limit (m_vmmaps md) /\
Z.of_nat (length (mints md)) + Z.of_nat D <= MAXINT /\
szok (mints md).

Record ACC (c : Z) (md md' : Model) : Prop := mkACC {
acc_lazy : m_vm_lazy md = [] -> m_vm_lazy md' = [];
acc_mat : m_vm_materialized md = [] -> m_vm_materialized md' = [];
acc_live : vm_live_bytes (m_vmmaps md') <= vm_live_bytes (m_vmmaps md) + c;
acc_limit : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md);
acc_len : (length (mints md') <= S (length (mints md)))%nat;
acc_sz : szok (mints md) -> c <= 2^30 -> szok (mints md') }.

Definition FEAS (e : ev) (md : Model) : Prop :=
match e with
| EMmap a len prot flags =>

alloc_top (m_vmmaps md) = alloc_ceiling ->
forall hint, exists x, grant_ok hint md x (mmap_len len) = true
| EMprotect a len prot => forall addr n, Mprotect.mprotect_budget_ok md addr n = true
| _ => True
end.

#[using="Type"] Lemma length_map_remove_le l a : (length (map_remove l a) <= length l)%nat.
Proof. unfold map_remove. induction l as [|x l IH]; cbn; [lia|]. destruct (negb _); cbn; lia. Qed.

#[using="Type"] Lemma length_iv_subtract_le2 a sz lo hi : (length (iv_subtract a sz lo hi) <= 2)%nat.
Proof. unfold iv_subtract. destruct (_ <? _), (_ <? _); cbn; lia. Qed.

#[using="Type"] Lemma length_iv_subtract_le1 a sz lo hi :
~ (bv_unsigned a < lo /\ hi < bv_unsigned a + bv_unsigned sz) -> (length (iv_subtract a sz lo hi) <= 1)%nat.
Proof.
intros H. unfold iv_subtract. destruct (Z.ltb_spec (bv_unsigned a) lo), (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn; lia.
Qed.

#[using="Type"] Lemma length_maps_subtract_noholes l lo hi :
(forall e, In e l -> ~ (elo e < lo /\ hi < ehi e)) -> (length (maps_subtract l lo hi) <= length l)%nat.
Proof.
induction l as [|[a sz] l IH]; intros H; cbn; [lia|]. rewrite length_app.
pose proof (length_iv_subtract_le1 a sz lo hi (H (a, sz) (or_introl eq_refl))).
assert (length (maps_subtract l lo hi) <= length l)%nat by (apply IH; intros e He; apply H; right; exact He). lia.
Qed.

#[using="Type"] Lemma length_maps_subtract_le l lo hi : pwdisj l -> lo < hi -> (length (maps_subtract l lo hi) <= S (length l))%nat.
Proof.
intros PW LT. induction PW as [| e l Hd PW IH]; cbn; [lia|]. destruct e as [a sz]. rewrite length_app.
destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)).
-
pose proof (length_iv_subtract_le2 a sz lo hi).
assert (length (maps_subtract l lo hi) <= length l)%nat; [| lia].
apply length_maps_subtract_noholes. intros e' He' [X1 X2]. specialize (Hd e' He'). unfold edisj, elo, ehi in *. cbn [fst snd] in Hd. lia.
- pose proof (length_iv_subtract_le1 a sz lo hi ltac:(lia)). lia.
- pose proof (length_iv_subtract_le1 a sz lo hi ltac:(lia)). lia.
- pose proof (length_iv_subtract_le1 a sz lo hi ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma szok_app l1 l2 : szok (l1 ++ l2) <-> szok l1 /\ szok l2.
Proof. unfold szok. apply Forall_app. Qed.
#[using="Type"] Lemma szok_cons e l : szok (e :: l) <-> bv_unsigned (snd e) <= 2^30 /\ szok l.
Proof. unfold szok. split; [intros H; inversion H; auto| intros [A B]; constructor; auto]. Qed.
#[using="Type"] Lemma szok_map_remove l a : szok l -> szok (map_remove l a).
Proof. unfold szok, map_remove. intros H. apply List.incl_Forall with (l1 := l); [| exact H]. intros x Hx. apply filter_In in Hx. tauto. Qed.
#[using="Type"] Lemma szok_maps_subtract l lo hi : 0 <= lo -> hi < 2^64 -> szok l -> szok (maps_subtract l lo hi).
Proof. intros. apply maps_subtract_sizes; auto. Qed.

#[using="Type"] Lemma m_vm_materialized_with_vmmaps h mo : m_vm_materialized (with_vmmaps h mo) = m_vm_materialized mo. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vm_materialized_forget lo hi mo : m_vm_materialized (vm_forget_range lo hi mo) = List.filter (page_outside_range lo hi) (m_vm_materialized mo). Proof. reflexivity. Qed.
End RC__1.
Ltac macc := unfold mints; rewrite ?m_vm_materialized_forget, ?m_vm_materialized_with_vmmaps in *; mproj.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ACC_refl c md : 0 <= c -> ACC c md md.
Proof. intros Hc. constructor; auto; try lia. Qed.

#[using="Type"] Lemma ACC_mono c c' md md' : ACC c md md' -> c <= c' -> c' <= 2^30 \/ c = c' -> ACC c' md md'.
Proof.
intros [A1 A2 A3 A4 A5 A6] LE OR. constructor; auto; try lia. intros SZ Hc'. apply A6; auto. lia.
Qed.

#[using="Type"] Lemma ACC_with_vmmaps_cons c md e (na : list (word * word)) brk :
bv_unsigned (snd e) = c ->
ACC c md (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps md)) (e :: vm_maps (m_vmmaps md)) na
(vm_start_brk (m_vmmaps md)) brk (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))) md).
Proof.
intros Hc. destruct e as [a n]. cbn [snd] in Hc. constructor; macc; auto.
- unfold vm_live_bytes. cbn [vm_maps]. rewrite live_bytes_cons. lia.
- rewrite !length_app. cbn. lia.
- intros SZ LE. apply szok_app in SZ as [S1 S2]. apply szok_app. split; [exact S1|]. apply szok_cons. cbn [snd]. split; [lia| exact S2].
Qed.

#[using="Type"] Lemma ACC_mmap_model c md a n : bv_unsigned n = c -> ACC c md (mmap_model a n md).
Proof. intros Hc. unfold mmap_model. apply (ACC_with_vmmaps_cons c md (a, n)). exact Hc. Qed.

#[using="Type"] Lemma ACC_noaccess_model c md a n : bv_unsigned n = c -> ACC c md (noaccess_model a n md).
Proof. intros Hc. unfold noaccess_model. apply (ACC_with_vmmaps_cons c md (a, n)). exact Hc. Qed.

#[using="Type"] Lemma ACC_brk_grow c md b d brk : bv_unsigned d <= c -> c <= 2^30 ->
ACC c md (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps md)) ((b, d) :: vm_maps (m_vmmaps md)) (vm_noaccess (m_vmmaps md))
(vm_start_brk (m_vmmaps md)) brk (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))) md).
Proof.
intros Hd Hc. eapply ACC_mono; [apply (ACC_with_vmmaps_cons (bv_unsigned d) md (b, d)); reflexivity| exact Hd| left; exact Hc].
Qed.

#[using="Type"] Lemma ACC_mprotect_model c md a n : 0 <= c -> ACC c md (mprotect_model a n md).
Proof. intros Hc. unfold mprotect_model. constructor; macc; auto. unfold vm_live_bytes. cbn. lia. Qed.

#[using="Type"] Lemma ACC_fixed_noaccess_model c md a n : 0 <= c -> ACC c md (fixed_noaccess_model a n md).
Proof.
intros Hc. unfold fixed_noaccess_model. constructor; macc; auto.
- intros ->. reflexivity.
- intros ->. reflexivity.
- unfold vm_live_bytes. cbn. lia.
Qed.

#[using="Type"] Lemma ACC_fixed_destroyed_model c md a n : 0 <= c -> pwdisj (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned n ->
bv_unsigned a + bv_unsigned n < 2^64 ->
ACC c md (fixed_destroyed_model a n md).
Proof.
intros Hc PW Hn Hhi. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
unfold fixed_destroyed_model. constructor; macc; auto.
- intros ->. reflexivity.
- intros ->. reflexivity.
- unfold vm_live_bytes. cbn. pose proof (live_bytes_maps_subtract_le (vm_maps (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n)). lia.
- rewrite !length_app. pose proof (length_maps_subtract_le (vm_maps (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) PW ltac:(lia)). lia.
- intros SZ LE. apply szok_app in SZ as [S1 S2]. apply szok_app. split; [exact S1|].
unfold szok. apply maps_subtract_sizes; auto. lia.
Qed.

#[using="Type"] Lemma ACC_munmap_model c md a n : 0 <= c -> ACC c md (munmap_model a n md).
Proof.
intros Hc. unfold munmap_model, Mmap.with_mmap_destroyed. constructor; macc; auto.
- intros ->. reflexivity.
- intros ->. reflexivity.
- unfold vm_live_bytes. cbn. pose proof (live_bytes_map_remove_le (vm_maps (m_vmmaps md)) a). lia.
- rewrite !length_app. pose proof (length_map_remove_le (vm_maps (m_vmmaps md)) a). lia.
- intros SZ LE. apply szok_app in SZ as [S1 S2]. apply szok_app. split; [exact S1| apply szok_map_remove; exact S2].
Qed.

#[using="Type"] Lemma ecost_le e : esz_ok e -> ecost e <= 2^30.
Proof. destruct e; cbn; intros H; try lia; [destruct (addr =? 0); lia|]. destruct (is_fixed flags); [lia| exact (proj2 (H eq_refl))]. Qed.

#[using="Type"] Theorem BUD_step : forall md md' e W D,
BUD md (W + ecost e) (S D) -> eks e = true -> esz_ok e -> 0 <= W -> ACC (ecost e) md md' -> BUD md' W D.
Proof.
intros md md' e W D (B1 & B2 & B3 & B4 & B5 & B6) EK SZ HW [A1 A2 A3 A4 A5 A6]. unfold BUD.
rewrite A4. splits; auto; try lia. apply A6; [exact B6| apply ecost_le; exact SZ].
Qed.

#[using="Type"] Theorem BUD_mono : forall md W D W' D', BUD md W D -> 0 <= W' <= W -> (D' <= D)%nat -> BUD md W' D'.
Proof. intros md W D W' D' (B1 & B2 & B3 & B4 & B5 & B6) HW HD. unfold BUD. splits; auto; lia. Qed.

#[using="Type"] Lemma grant_ok_na_of_ok hint md x n : grant_ok hint md x n = true -> grant_ok_na hint md x n = true.
Proof. apply grant_ok_grant_ok_na. Qed.

#[using="Type"] Theorem BUD_feas : forall md e W D,
BUD md (W + ecost e) (S D) -> eks e = true -> esz_ok e -> 0 <= W -> egrant e = true -> FEAS e md.
Proof.
intros md e W D (B1 & B2 & B3 & B4 & B5 & B6) EK SZ HW EG. destruct e; cbn in EG |- *; try discriminate; auto.
-
cbn in SZ. unfold ecost in B4, B3. destruct (is_fixed flags); [discriminate|]. destruct (SZ eq_refl) as [SZ0 SZ1].
rewrite round_up_pg_eq in SZ1, B4, B3. fold (mmap_len len) in SZ1, B4, B3.
intros Hceil hint. apply grant_exists.
+ pose proof (round_up_pg_ge len). rewrite round_up_pg_eq in H. fold (mmap_len len) in H. split; [lia| exact SZ1].
+ exact B6.
+ unfold MAXINT in B5. unfold mints in B5. lia.
+ exact Hceil.
+ pose proof (vm_backing_used_le_live md B1 B2). lia.
-
intros a n. apply mprotect_budget_ok_intro; auto. unfold ecost in B4. lia.
Qed.

#[using="Type"] Lemma BUD_frame md md' W D :
BUD md W D -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md ->
BUD md' W D.
Proof. intros (B1 & B2 & B3 & B4 & B5 & B6) E1 E2 E3. unfold BUD, mints in *. rewrite E1, E2, E3. splits; auto. Qed.

#[using="Type"] Lemma BUD_init md W D :
m_vm_lazy md = [] -> m_vm_materialized md = [] -> vm_maps (m_vmmaps md) = [] ->
0 <= W <= vm_limit (m_vmmaps md) ->
Z.of_nat (length (vm_reserved (m_vmmaps md))) + Z.of_nat D <= MAXINT ->
Forall (fun p => bv_unsigned (snd p) <= 2^30) (vm_reserved (m_vmmaps md)) ->
BUD md W D.
Proof.
intros L M E HW HC HS. unfold BUD, mints, szok. rewrite E, app_nil_r. unfold vm_live_bytes. rewrite E. cbn [live_bytes fold_right].
splits; auto; try lia.
Qed.

End RC__2.
