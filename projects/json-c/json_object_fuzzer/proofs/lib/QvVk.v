(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbrW QlEo_c1 Q5Rg QWxq_c1 QRjH Qn1e QiVh QSpR QuJV QZAi QUZl Q7S0 Qfya QYTG Ql2m QGeV QeZD QkRc QqWy QyuL Q6q3 EdEvNode EdEvArm.
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
Import QeZD QkRc QqWy.Mq0 QyuL.Mq0.
Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Ltac lia ::= klia. Ltac mkr__lia_0 := klia.
Ltac nia ::= knia. Ltac mkr__nia_1 := knia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma maps_subtract_inside : forall na lo hi e',
(forall e, In e na -> elo e < ehi e <= 2^64) -> 0 <= lo -> hi < 2^64 ->
In e' (maps_subtract na lo hi) ->
exists e, In e na /\ elo e <= elo e' /\ ehi e' <= ehi e /\ elo e' < ehi e'.
Proof.
intros na lo hi e' Hwf Hlo Hhi Hin.
destruct (maps_subtract_In _ _ _ _ Hin) as ([a sz] & He & Hsub).
pose proof (Hwf _ He) as W. rewrite elo_pair, ehi_pair in W.
pose proof (iv_subtract_sub a sz lo hi e' ltac:(lia) ltac:(lia) Hlo Hhi Hsub) as (S1 & S2 & S3).
exists (a, sz). rewrite elo_pair, ehi_pair. auto.
Qed.

#[using="Type"] Lemma region_free_subtract : forall na lo hi x m,
(forall e, In e na -> elo e < ehi e <= 2^64) -> 0 <= lo -> hi < 2^64 ->
region_free na x m = true -> region_free (maps_subtract na lo hi) x m = true.
Proof.
intros na lo hi x m Hwf Hlo Hhi Hrf. apply region_free_intro. intros e' He'.
destruct (maps_subtract_inside na lo hi e' Hwf Hlo Hhi He') as (e & He & S1 & S2 & S3).
pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.

Section Ev.
Variable segs : list Segment.

#[using="Type"] Lemma ev1_mmap_fixed : forall L pbrk md ms1 (J : config -> Prop) cur a,
NClosed segs J -> KL L pbrk md -> ld_brk L = BPGuard cur -> a = round_up_pg cur ->
QWxq_c1.Mq1.at_node segs (QWxq_c1.Mq1.NMmap a PGSZ PROT_NONE MAPFX) ms1 ->
(forall rsp z md',
ev_dec (EMmap a PGSZ PROT_NONE MAPFX) pbrk rsp = Some z -> answer_ok L (EMmap a PGSZ PROT_NONE MAPFX) z = true ->
KL (event_post L (EMmap a PGSZ PROT_NONE MAPFX) z) (ps_brk (ev_post_state (EMmap a PGSZ PROT_NONE MAPFX) rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Proof.
intros L pbrk md ms1 J cur a HJ HK Hph Ha Hat HC.
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
apply (EdEvNode.ncl_ekept segs J ms1 md (Z_to_bv 64 222) unit effs ms' tt HJ Hh Hsvc Hlive).
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
intros []; cbn [effs ms'].

apply (HC (mkEffectU (Z_to_bv 64 cur) [] [] [((Z_to_bv 64 cur), (Z_to_bv 64 PGSZ))] [] []) cur).
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
Qed.

End Ev.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhfJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhfJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition AMW (SH : Z) : Z := (2 + 2 ^ (SH + 1)) * PGSZ.
Definition AMD : nat := 4%nat.

Section AMK.
Context {T : Type} (isS : T -> bool) (P : T -> Prop) (Wf : Z) (Df : nat).
Variables (BL : list blk) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled) (κn κs : kind) (W : Z) (D : nat) (SH : Z).
Hypothesis HW : Wf <= W.
Hypothesis HSH : 0 <= SH <= 16.
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 ->
c_meta_alloc_shift (s_ctx st1) <= SH + 1 -> KSUM isS P Wf Df L1 (k st1 None) κn W D.

Definition AMQ (st1 : mstate) : Prop :=
(c_meta_alloc_shift (s_ctx st1) = c_meta_alloc_shift (s_ctx st0) /\ c_avail_meta_count (s_ctx st0) - 1 <= c_avail_meta_count (s_ctx st1))
\/ (c_avail_meta_count (s_ctx st1) = NSLOTS - 1 /\ c_avail_meta_count (s_ctx st0) = 0
/\ c_meta_alloc_shift (s_ctx st1) <= c_meta_alloc_shift (s_ctx st0) + 1).
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 ->
c_meta_alloc_shift (s_ctx st1) <= SH + 1 -> AMQ st1 -> KSUM isS P Wf Df L1 (k st1 (Some m)) κs W D.

Definition amk (κ : kind) : Prop := κ = κs.

#[using="HSH"] Lemma pow_SH : 1 <= 2 ^ (SH + 1) <= 2 ^ 17.
Proof.
split.
- change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia.
- apply Z.pow_le_mono_r; lia.
Qed.

Notation SHF st := (c_meta_alloc_shift (s_ctx st)).
Notation CNT st := (c_avail_meta_count (s_ctx st)).

#[using="Type"] Lemma am_take_ok' Y st L LS : INVL Y st L BL LS -> 0 < c_avail_meta_count (s_ctx st) ->
exists m st2, (forall (kk : mstate -> optr -> M T) bb, am_take st kk bb = kk st2 (Some m))
/\ INVL (xidle Y (m :: x_idle Y)) st2 L BL LS /\ AM_frame st st2 /\ ~ In m (x_idle Y) /\ SHF st2 = SHF st /\ CNT st2 = CNT st - 1.
Proof.
intros INV HC.
destruct (am_take_ok Y st L BL LS INV HC (fun s m => SRet (s, m) : M (mstate * optr)) (SRet (st, None))) as (m & st2 & E & INV2 & AF2 & NI).
unfold am_take in E |- *. destruct (c_avail_meta (ctx st)) as [a|] eqn:EA; [| discriminate E].
injection E as E1 E2. rewrite <- E1 in *. rewrite <- E2 in *. exists a. eexists. split; [intros; reflexivity|]. split; [exact INV2|]. split; [exact AF2|]. split; [exact NI| split; reflexivity].
Qed.

#[using="KS"] Lemma am_take_ks st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
0 < c_avail_meta_count (s_ctx st) -> SHF st <= SH + 1 ->
(SHF st = SHF st0 /\ CNT st = CNT st0) \/ (CNT st = NSLOTS /\ CNT st0 = 0 /\ SHF st <= SHF st0 + 1) ->
KSUM isS P Wf Df L (am_take st k bail) κs W D.
Proof.
intros INV AF LF HC SHC REL. destruct (am_take_ok' X st L LS INV HC) as (m & st2 & E & INV2 & AF2 & NI & SE & CE). rewrite E.
eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| exact LF| rewrite SE; exact SHC|].
unfold AMQ. rewrite CE, SE. destruct REL as [[A B]|(A & B & C)]; [left| right]; lia.
Qed.

#[using="KS"] Lemma am_carve_ks s p L LS : INVL X s L BL LS ->
c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
AM_frame st0 s -> L_frame L0 L -> SHF s <= SH + 1 -> CNT st0 = 0 -> SHF s <= SHF st0 + 1 ->
KSUM isS P Wf Df L (am_take (carve_rest s p) k bail) κs W D.
Proof.
intros INV H1 H2 H3 H4 H5 H6 AF LF SHC C0 SR. destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
assert (SHc : SHF (carve_rest s p) = SHF s) by (unfold carve_rest; cbn; destruct (c_meta_area_tail _); cbn; reflexivity).
eapply am_take_ks; [exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC| rewrite SHc; exact SHC |].
right. split; [| split; [exact C0| rewrite SHc; exact SR]]. unfold carve_rest. cbn -[NSLOTS]. destruct (c_meta_area_tail (ctx s)); cbn -[NSLOTS]; reflexivity.
Qed.

#[using="HW KN KS"] Lemma am_finish_ks st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 -> SHF st <= SH + 1 -> CNT st0 = 0 -> SHF st <= SHF st0 + 1 ->
KSUM isS P Wf Df L (am_finish st true k bail) κs W (S D).
Proof.
intros INV AF LF HC HI SHC C0 SR.
destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
eapply (ks_ev' isS P Wf Df L _ _ κn κs); [reflexivity| exact I| exact HW| cbn; lia| | | intros E; discriminate E| reflexivity].
- intros a Ha Ca. cbn in Ha. rewrite Ha. cbn [negb]. cbn [eclass] in Ca.
change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
assert (E : (a =? 0) || (a =? TWO64 - ENOSYS) = false).
{ apply negb_false_iff in Ca. apply andb_prop in Ca as [C1' C2']. apply negb_true_iff in C2'. rewrite C2'.
unfold is_err in C1'. apply Z.ltb_lt in C1'. replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; unfold TWO64 in C1'; lia). reflexivity. }
cbn [event_post]. rewrite E. eapply KN; [exact INV| exact AF| exact LF| exact SHC].
- intros a Ha Ca. cbn in Ha. rewrite Ha. cbn [negb]. cbn [eclass] in Ca.
change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
assert (E : (a =? 0) || (a =? TWO64 - ENOSYS) = true).
{ apply negb_true_iff in Ca. apply andb_false_iff in Ca as [C1'|C2'].
- unfold is_err in C1'. apply Z.ltb_ge in C1'. unfold mprotect_answer_ok in Ha.
apply orb_prop in Ha as [Ha|Ha]; [rewrite Ha; reflexivity|]. unfold is_errno_form in Ha. apply andb_prop in Ha as [Ha _]. apply Z.leb_le in Ha. unfold TWO64 in *. lia.
- apply negb_false_iff in C2'. rewrite C2'. apply orb_true_r. }
cbn [event_post]. rewrite E. rewrite am_carve_eq.
destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
eapply am_carve_ks; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')| | cbn; exact SHC| exact C0| cbn; exact SR].
destruct LF; constructor; assumption.
Qed.

Definition nres (st : mstate) : Z := Z.shiftl 2 (SHF st).

#[using="Type"] Lemma nres_eq st : 0 <= SHF st -> nres st = 2 ^ (SHF st + 1).
Proof. intros H. unfold nres. rewrite Z.shiftl_mul_pow2 by exact H. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia. Qed.

#[using="Type"] Lemma nres_bound st : 0 <= SHF st <= SH -> 2 <= nres st <= 2 ^ (SH + 1).
Proof.
intros H. rewrite nres_eq by lia. split.
- change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia.
- apply Z.pow_le_mono_r; lia.
Qed.

#[using="HW HSH KN KS"] Lemma am_after_brk0_ks st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
c_init_done (s_ctx st) = 1 -> c_avail_meta_area_count (s_ctx st) = 0 -> SHF st <= SH -> CNT st0 = 0 -> SHF st = SHF st0 ->
KSUM isS P Wf Df L (am_after_brk st true k bail) κs (W + 2 ^ (SH + 1) * PGSZ) (S (S D)).
Proof.
intros INV AF LF HI HC SHC C0 SR. unfold am_after_brk. unfold ctx. rewrite HC. cbn [Z.eqb].
pose proof (proj1 (ir_shift _ _ _ (proj1 INV))) as S0.
pose proof (nres_bound st ltac:(lia)) as NB. pose proof pow_SH as PS. fold (nres st).
assert (AL : (nres st * PGSZ) mod PGSZ = 0) by (apply Z_mod_mult).
assert (RU : round_up_pg (nres st * PGSZ) = nres st * PGSZ) by (apply round_up_pg_id; exact AL).
eapply KSUM_mono; [| | apply le_n_S, Nat.le_refl].
1: eapply (ks_ev' isS P Wf Df L _ _ κn κs _ W (S D)); [reflexivity| | exact HW| reflexivity| | | intros E; discriminate E|].
- cbn. intros _. rewrite RU. unfold PGSZ. nia.
- intros a Ha Ca. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. rewrite Ha. cbn [negb]. cbn [eclass is_fixed] in Ca.
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ca. cbn [negb] in Ca. apply negb_false_iff in Ca. rewrite Ca.
unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. rewrite Ca. cbn [andb].
eapply KSUM_mono; [eapply KN; [exact INV| exact AF| exact LF| lia]| lia| lia].
- intros a Ha Ca. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. rewrite Ha. cbn [negb]. cbn [eclass is_fixed] in Ca.
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ca. cbn [negb] in Ca. apply negb_true_iff in Ca. rewrite Ca.
unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. rewrite Ca. cbn [andb].
destruct (INVL_new_meta X st L BL LS a INV HC Ha Ca) as (INV' & HC' & HI' & AF').
eapply am_finish_ks; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI| cbn; lia| exact C0| cbn; lia].
- cbn [egrant is_fixed]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. cbn. destruct κn as [[|] [|]], κs as [[|] [|]]; reflexivity.
- cbn [ecost]. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false. cbv iota. rewrite RU. unfold PGSZ in *. nia.
Qed.

#[using="HW HSH KN KS"] Lemma am_after_brk_ks st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
c_init_done (s_ctx st) = 1 -> SHF st <= SH -> CNT st0 = 0 -> SHF st = SHF st0 ->
KSUM isS P Wf Df L (am_after_brk st true k bail) κs (W + 2 ^ (SH + 1) * PGSZ) (S (S D)).
Proof.
intros INV AF LF HI SHC C0 SR. pose proof pow_SH as PS.
destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
- apply (am_after_brk0_ks st L LS); auto.
- unfold am_after_brk. apply Z.eqb_neq in HC. rewrite HC.
eapply KSUM_mono; [eapply am_finish_ks; [exact INV| exact AF| exact LF| apply Z.eqb_neq in HC; pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI| lia| exact C0| lia]| unfold PGSZ; nia| lia].
Qed.

Definition am_quick (st : mstate) : bool :=
match c_free_meta_head (s_ctx st) with Some _ => true | None => negb (c_avail_meta_count (s_ctx st) =? 0) end.

Definition am_kind (st : mstate) : kind := let _ := κn in let _ := am_quick st in κs.

#[using="Type"] Lemma am_quick_init st : am_quick (am_init st) = am_quick st.
Proof. unfold am_init. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.

#[using="HW HSH KN KS"] Theorem alloc_meta_ks st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> SHF st <= SH ->
SHF st = SHF st0 /\ CNT st = CNT st0 ->
KSUM isS P Wf Df L (alloc_meta st k bail) (am_kind st) (W + AMW SH) (D + AMD)%nat.
Proof.
intros INV0 AF0 LF SHC0 E00. pose proof pow_SH as PS. unfold AMW, AMD. unfold am_kind.
assert (E0 : SHF (am_init st) = SHF st0 /\ CNT (am_init st) = CNT st0) by (unfold am_init; destruct (c_init_done (ctx st) =? 0); cbn; exact E00).
clear E00.
destruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
pose proof (amf_trans _ _ _ AF0 AFi) as AF.
assert (SHC : SHF (am_init st) <= SH) by (unfold am_init; destruct (c_init_done (ctx st) =? 0); cbn; exact SHC0).
clear AF0 AFi INV0 SHC0.
unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (proj1 (ir_shift _ _ _ IR)) as SH0.
unfold am_quick. unfold ctx.

destruct (c_free_meta_head (s_ctx s)) as [m|] eqn:EFH.
{
pose proof (il_head _ _ IL LFree) as HH. cbn in HH. rewrite EFH in HH.
destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
eapply (KSUM_mono isS P Wf Df _ _ _ W D); [| unfold PGSZ; nia| lia].
eapply KS; [exact INV1| | | exact LF| |].
{ intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
{ eapply amf_trans; [exact AF|]. pose proof FC as FC'. destruct FC'. constructor; auto; try congruence.
all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
all: try (intros rid r H _; rewrite F1; exact H).
all: try (rewrite ?F3; lia).
exact (dequeue_free_hmetas BL _ s L LS m rest INV ELS). }
{ change (SHF (dequeue LFree m s)) with (c_meta_alloc_shift (s_ctx (dequeue LFree m s))). rewrite (cb_shift _ _ FC). lia. }
{ unfold AMQ. left. rewrite (cb_shift _ _ FC), (cb_amc _ _ FC). destruct E0 as [A B]. cbn in A, B |- *. rewrite A, B. lia. } }

destruct (Z.eqb_spec (c_avail_meta_count (s_ctx s)) 0) as [HAC|HAC]; cbn [negb].
2:{ eapply (KSUM_mono isS P Wf Df _ _ _ W D); [| unfold PGSZ; nia| lia].
eapply am_take_ks; [exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); lia| lia| left; exact E0]. }

assert (C0 : CNT st0 = 0) by (destruct E0 as [_ B]; cbn in B; rewrite <- B; exact HAC).
assert (SR : SHF s = SHF st0) by (destruct E0 as [A _]; exact A).
destruct (Z.eqb_spec (c_avail_meta_area_count (s_ctx s)) 0) as [HC|HC]; cbn [andb].
2:{ eapply KSUM_mono; [exact (am_after_brk_ks s L LS INV AF LF HI SHC C0 SR)| unfold PGSZ; nia| lia]. }
pose proof (ir_brk _ _ _ IR) as IBK. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
-
destruct IBK as [BP NB].
replace (D + 4)%nat with (S (S (S (S D)))) by lia.
eapply (ks_ev' isS P Wf Df L (EBrk 0) _ κs κs _ (W + (2 + 2 ^ (SH + 1)) * PGSZ) (S (S (S D))));
[reflexivity| exact I| unfold PGSZ; nia| cbn [ecost Z.eqb]; lia| | intros cur Hc C; cbn in C; discriminate C| intros _; reflexivity| reflexivity].
intros cur Hc _. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
set (L1 := Qfya.set_brkph (BPQueried cur) L).
set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
assert (NZ : (new =? 0) = false).
{ apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
eapply (ks_ev' isS P Wf Df L1 (EBrk new) _ κs κs _ (W + 2 ^ (SH + 1) * PGSZ) (S (S D)));
[reflexivity| exact I| unfold PGSZ; nia| cbn [ecost]; rewrite NZ; lia| | | intros _; reflexivity| cbn [egrant]; reflexivity].
+
intros r Hr Cr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [Qfya.ld_brk Qfya.set_brkph] in Hr.
apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb]. cbn [eclass] in Cr. rewrite NZ in Cr. rewrite Cr. cbn [negb].
unfold event_post. rewrite NZ. unfold L1. cbn [Qfya.ld_brk Qfya.set_brkph]. rewrite Cr.
destruct (INVL_brk_dead X s L (Qfya.set_brkph BPDead (Qfya.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
eapply am_after_brk0_ks; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| cbn; exact HC| cbn; exact SHC| exact C0| cbn; exact SR].
+
intros r Hr Cr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [Qfya.ld_brk Qfya.set_brkph] in Hr.
apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb]. cbn [eclass] in Cr. rewrite NZ in Cr. rewrite Cr. cbn [negb].
apply Z.eqb_eq in Cr. subst r. rewrite Z.eqb_refl in Hp. cbn [negb orb] in Hp.
unfold event_post. rewrite NZ. unfold L1. cbn [Qfya.ld_brk Qfya.set_brkph]. rewrite Z.eqb_refl.
rewrite (lbrk_pages_ok_ext (Qfya.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
eapply (KSUM_mono isS P Wf Df _ _ _ (W + PGSZ) (S D)); [| unfold PGSZ; nia| lia].
eapply (ks_ev' isS P Wf Df _ _ _ κs κs _ W D); [reflexivity| cbn; intros E; discriminate E| exact HW| | | intros rg Hg C; cbn in C; discriminate C| intros _; reflexivity| reflexivity].
{ cbn [ecost]. change (is_fixed (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) with true. reflexivity. }
intros rg Hg _. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
subst rid s1.
unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
rewrite am_carve_eq.
destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (Qfya.set_brkph (BPGuard cur) (Qfya.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
eapply am_carve_ks; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| | | exact C0|].
{ destruct LF; constructor; assumption. }
{ unfold adv. cbn. change (c_meta_alloc_shift (s_ctx (fst (new_region RKBrk base (2 * PGSZ) s)))) with (SHF s). lia. }
{ unfold adv. cbn. change (c_meta_alloc_shift (s_ctx (fst (new_region RKBrk base (2 * PGSZ) s)))) with (SHF s). lia. }
-
eapply KSUM_mono; [exact (am_after_brk_ks s L LS INV AF LF HI SHC C0 SR)| unfold PGSZ; nia| lia].
-
destruct IBK as [BP (r & Hr & K & Elen)].
set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
assert (NZ : (new =? 0) = false).
{ apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
assert (BR : ld_brkreg L = Some (r_base r, off)).
{ apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
eapply (KSUM_mono isS P Wf Df _ _ _ (W + 2 ^ (SH + 1) * PGSZ + 2 * PGSZ) (S (S (S D)))); [| unfold PGSZ; nia| lia].
eapply (ks_ev' isS P Wf Df L (EBrk new) _ κs κs _ (W + 2 ^ (SH + 1) * PGSZ) (S (S D)));
[reflexivity| exact I| unfold PGSZ; nia| cbn [ecost]; rewrite NZ; reflexivity| | | intros _; reflexivity| cbn [egrant]; reflexivity].
+
intros z Hz Cz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb]. cbn [eclass] in Cz. rewrite NZ in Cz. rewrite Cz. cbn [negb].
unfold event_post. rewrite NZ, BP, BR, Cz.
destruct (INVL_brk_dead X s L (Qfya.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
eapply am_after_brk0_ks; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| cbn; exact HC| cbn; exact SHC| exact C0| cbn; exact SR].
+
intros z Hz Cz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb]. cbn [eclass] in Cz. rewrite NZ in Cz. rewrite Cz. cbn [negb].
apply Z.eqb_eq in Cz. subst z. rewrite Z.eqb_refl in Hp. cbn [negb orb] in Hp.
unfold event_post. rewrite NZ, BP, BR, Z.eqb_refl.
rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
rewrite am_carve_eq.
destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
eapply (KSUM_mono isS P Wf Df _ _ _ W D); [| unfold PGSZ; nia| lia].
eapply am_carve_ks; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| | | exact C0|].
{ destruct LF; constructor; assumption. }
{ unfold adv, upd_region. cbn. destruct (get_region s rid); cbn; change (c_meta_alloc_shift (s_ctx s)) with (SHF s); lia. }
{ unfold adv, upd_region. cbn. destruct (get_region s rid); cbn; change (c_meta_alloc_shift (s_ctx s)) with (SHF s); lia. }
Qed.

End AMK.

End RC__1.
