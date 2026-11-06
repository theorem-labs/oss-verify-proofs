(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKY2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXDj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXDj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q45h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q25t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q25t. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNDM.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Set Default Proof Using "All".

Section Vis.
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
#[local] Notation h := (m_vmmaps mo).
#[local] Notation LV := (LV_J E).
#[local] Notation argH := (argH0 JOB6PH sp rdraw argv envp uid hw).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
#[local] Notation HID := (hid BJO6 usp argH E ch mo).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).

Definition GLO : Z := 0x7fff8000 + (TOPP usp - 8388608) / 8.
Definition GHI : Z := 0x7fff8000 + atopE E / 8.
Definition gapb (a : word) : bool := ((GLO <=? bv_unsigned a) && (bv_unsigned a <? GHI))%bool.

Lemma atop_val : atopE E = usp - 8388608.
Proof. unfold atopE. rewrite (MA main_sp0). reflexivity. Qed.

Lemma gap_bounds : GHI <= GLO + 20 /\ GLO <= GHI + 492 /\ 0x10006fef8000 <= GLO /\ GHI <= 0x10007fef8000.
Proof.
pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (T1 & T2 & T3 & T4). unfold STACK_MAX, CEIL in T4.
destruct Hsp as (S1 & S2 & S3). unfold sp_window_lo, sp_window_hi in S1, S2.
unfold GLO, GHI. rewrite atop_val.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma topp_val : TOPP usp = 32768 * bv_unsigned (ev E 0) + 4096 * bv_unsigned (ev E 10)
/\ 4294901760 <= bv_unsigned (ev E 0) <= 4294967295 /\ 0 <= bv_unsigned (ev E 10) <= 8.
Proof.
pose proof (P co_know) as K. unfold know_ok in K. rewrite Forall_forall in K.
destruct (HS2_facts w ch HCL) as (_ & _ & I0 & I10 & _).
pose proof (K _ I0) as K0. pose proof (K _ I10) as K10. unfold Q25t.F0, Q25t.F10 in K0, K10. cbn [kentry_ok edenot] in K0, K10.
pose proof (proj2 (P co_sp0)) as Htop. unfold uE in Htop. rewrite e_top_eq in Htop. cbn [edenot] in Htop.
rewrite u_add64, !u_mul64, !u64_lit in Htop by lia.
split; [|split; assumption].
rewrite <- Htop. rewrite (Z.mod_small (32768 * _)), (Z.mod_small (4096 * _)), Z.mod_small by lia. reflexivity.
Qed.

Lemma estart_GB : estart E (SA GB GK) = GLO.
Proof.
destruct topp_val as (HT & K0 & K10). unfold estart, GB, GK, GLO. cbn [a_base a_off edenot].
rewrite u_add64, !u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)), (Z.mod_small (512 * _)), Z.mod_small by lia.
rewrite HT. replace (32768 * bv_unsigned (ev E 0) + 4096 * bv_unsigned (ev E 10) - 8388608)
with ((4096 * bv_unsigned (ev E 0) + 512 * bv_unsigned (ev E 10) - 1048576) * 8) by lia.
rewrite Z.div_mul by lia. lia.
Qed.

Lemma band_sh : sh_lo BJO6 E (e_stacklo, e_stacklen) = GLO /\ sh_hi BJO6 E (e_stacklo, e_stacklen) = 0x7fff8000 + 2 ^ 44.
Proof.
destruct (MA u_stack) as [U1 U2]. unfold sh_lo, sh_hi. cbn [fst snd shadow_off BJO6]. rewrite U1, U2. split; [reflexivity|].
replace (TOPP usp - 8388608 + (2 ^ 47 + 8388608 - TOPP usp)) with (2 ^ 44 * 8) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma allowed_base : forall z, (0x10000 <= z < 0x647000 \/ atopE E <= z < 2^47) -> allowed_byte LV mo z = true.
Proof.
intros z Hz. unfold allowed_byte. apply orb_true_iff. left. unfold Qsn5.in_zivs, appvis. rewrite existsb_app. apply orb_true_iff. left.
unfold LV_J, L_main_job6. cbn [lv_base existsb]. unfold Qsn5.zin. cbn [fst snd].
destruct Hz as [[A B]|[A B]].
- apply orb_true_iff; left. apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
- apply orb_true_iff; right. apply orb_true_iff; left. apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

Lemma allowed_stack_shadow : forall z, GHI <= z < 0x7fff8000 + 2 ^ 44 -> allowed_byte LV mo z = true.
Proof.
intros z Hz. pose proof (MA main_atop_bounds) as AB.
unfold allowed_byte. apply orb_true_iff. right. unfold Qsn5.in_zivs, shivs. apply existsb_exists.
exists (sh_iv LV (atopE E, 0x800000000000)). split.
- apply in_map. apply filter_In. split; [unfold appvis; apply in_app_iff; left; cbn; tauto|]. unfold Qsn5.nonempty. apply Z.ltb_lt. cbn [fst snd]. lia.
- unfold Qsn5.zin, sh_iv, shz, LV_J, L_main_job6. cbn [lv_shoff fst snd]. unfold GHI in Hz.
replace ((0x800000000000 - 1) / 8) with (2 ^ 44 - 1) by reflexivity.
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma entry_allowed0 : forall e z, In e (vm_maps h) -> excl_entry LV e = false ->
bv_unsigned (fst e) <= z < bv_unsigned (fst e) + bv_unsigned (snd e) -> allowed_byte LV mo z = true.
Proof.
intros e z Hin Hex Hz. unfold allowed_byte. apply orb_true_iff. left. unfold Qsn5.in_zivs, appvis. rewrite existsb_app. apply orb_true_iff. right.
apply existsb_exists. exists (wiv2z e). split.
- apply in_map. apply filter_In. split; [exact Hin| rewrite Hex; reflexivity].
- unfold Qsn5.zin, wiv2z. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma in_allow_allowed : forall z, z < 0x10007fff8000 -> in_allow BJO6 E ch z = true -> allowed_byte LV mo z = true \/ GLO <= z < GHI.
Proof.
intros z Hzt Hal.
assert (Hp : exists p, In p (a_vis ch) /\
((uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)) || (sh_lo BJO6 E p <=? z) && (z <? sh_hi BJO6 E p))%bool = true).
{ unfold in_allow, in_vis, in_sh in Hal. apply orb_true_iff in Hal as [Hal|Hal]; apply existsb_exists in Hal as (p & Hp & Hz);
exists p; (split; [exact Hp|]); rewrite Hz; [reflexivity | apply orb_true_r]. }
destruct Hp as (p & Hp & Hz). destruct ((MA vis_cases) p Hp) as [Hin | ->].
- left. exact ((MA inside_allowed) p z Hin Hz).
- destruct band_sh as [B1 B2]. rewrite B1, B2 in Hz.
apply orb_true_iff in Hz as [Hz|Hz]; apply andb_prop in Hz as [Z1 Z2]; apply Z.leb_le in Z1; apply Z.ltb_lt in Z2.
+ exfalso. cbn [fst snd] in Z1. rewrite (proj1 (MA u_stack)) in Z1.
pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (_ & _ & _ & T4). unfold STACK_MAX, CEIL in T4. lia.
+ destruct (Z.lt_ge_cases z GHI) as [Hg|Hg]; [right; lia | left; apply allowed_stack_shadow; lia].
Qed.

Lemma gap_amap_in : In {| am_base := ELit 2415882240; am_len := ELit 2199023255552; am_kind := KNONELAZY |} (a_maps ch).
Proof. rewrite (MAPS_W_eq w ch HCL). destruct w; vm_compute; tauto. Qed.
Lemma low_amap_in : In {| am_base := ELit 2147446784; am_len := ELit 268435456; am_kind := KRWLAZY |} (a_maps ch).
Proof. rewrite (MAPS_W_eq w ch HCL). destruct w; vm_compute; tauto. Qed.
Lemma high_amap_in : In {| am_base := ELit 2201439137792; am_len := ELit 15392894357504; am_kind := KRWLAZY |} (a_maps ch).
Proof. rewrite (MAPS_W_eq w ch HCL). destruct w; vm_compute; tauto. Qed.

Theorem hidL_hid_gap : forall a : word, bv_unsigned a < 2^47 -> hidden LV mo a = true -> HID a = true \/ gapb a = true.
Proof.
intros a Ha Hh. unfold hidden in Hh. apply negb_true_iff in Hh.
unfold hid. destruct (argH E a); [left; reflexivity|]. cbn [orb]. unfold vis.
destruct (in_hull BJO6 (bv_unsigned a)) eqn:Hhull.
{ exfalso. unfold in_hull in Hhull. cbn [img_lo img_hi BJO6] in Hhull. apply andb_prop in Hhull as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite (allowed_base (bv_unsigned a)) in Hh; [discriminate| lia]. }
destruct (ATOP usp <=? bv_unsigned a) eqn:Htop.
{ exfalso. apply Z.leb_le in Htop. unfold ATOP, STACK_MAX in Htop. rewrite <- atop_val in Htop. rewrite (allowed_base (bv_unsigned a)) in Hh; [discriminate| lia]. }
cbn [orb].
destruct (in_ivs (bv_unsigned a) (vm_maps h)) eqn:Hm; [|left; reflexivity].
destruct (in_ivs (bv_unsigned a) (vm_noaccess h)) eqn:Hna; [left; reflexivity|]. cbn [andb negb].
apply in_ivs_true in Hm as (iv & Hin & Hz).
destruct (excl_entry LV iv) eqn:Hex.
2:{ exfalso. rewrite (entry_allowed0 iv (bv_unsigned a) Hin Hex Hz) in Hh. discriminate. }
pose proof (P co_kinds) as KD. rewrite Forall_forall in KD.
destruct ((MA excl_cases) iv Hin Hex) as [ -> | [ -> | -> ] ].
-
destruct (KD _ low_amap_in eq_refl a Hz) as [_ ->]. cbn [negb orb].
destruct (in_allow BJO6 E ch (bv_unsigned a)) eqn:Hal; [|left; reflexivity].
unfold e_low in Hz. cbn [fst snd] in Hz. rewrite !(u_litE E) in Hz by lia.
destruct (in_allow_allowed (bv_unsigned a) ltac:(lia) Hal) as [X|X]; [rewrite X in Hh; discriminate|].
right. unfold gapb. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
-
exfalso. pose proof (P co_none) as NO. rewrite Forall_forall in NO.
specialize (NO _ gap_amap_in (or_intror eq_refl)). unfold amap_den in NO. cbn [am_base am_len] in NO.
assert (X : in_ivs (bv_unsigned a) (vm_noaccess h) = true).
{ apply in_ivs_true. exists (e_gap E). split; [exact NO| exact Hz]. }
rewrite X in Hna. discriminate.
-
destruct (KD _ high_amap_in eq_refl a Hz) as [_ ->]. cbn [negb orb].
destruct (in_allow BJO6 E ch (bv_unsigned a)) eqn:Hal; [|left; reflexivity].
unfold e_high in Hz. cbn [fst snd] in Hz. rewrite !(u_litE E) in Hz by lia.
destruct (in_allow_allowed (bv_unsigned a) ltac:(lia) Hal) as [X|X]; [rewrite X in Hh; discriminate|].
right. unfold gapb. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Definition H1g (a : word) : bool := (HID a || gapb a)%bool.

Lemma HID_off : H_off_segments JOB6SEGS HID.
Proof. exact (H_off_segments_cs JOB6SEGS BJO6 usp asan_in_hull asan_hull_ok argH (argH0_high JOB6PH sp rdraw argv envp uid hw Hsp Hva) E ch mo). Qed.

Lemma H1g_off : H_off_segments JOB6SEGS H1g.
Proof.
intros a Ha. unfold H1g in Ha. apply orb_true_iff in Ha as [Ha|Ha]; [exact (HID_off a Ha)|].
unfold gapb in Ha. apply andb_prop in Ha as [G1 _]. apply Z.leb_le in G1. destruct gap_bounds as (_ & _ & B3 & _).
apply (find_segment_none_above JOB6SEGS (bv_unsigned a) 1 0x647000); [exact JOB6SEGS_top | lia].
Qed.

Lemma hid_hull : forall a : word, 65536 <= bv_unsigned a < 6582272 -> HID a = false.
Proof.
intros a Ha. unfold hid, vis, in_hull. cbn [img_lo img_hi BJO6].
replace (argH E a) with false.
2:{ symmetry. destruct (argH E a) eqn:Hg; [|reflexivity]. exfalso.
pose proof (argH0_high JOB6PH sp rdraw argv envp uid hw Hsp Hva E a Hg). unfold CEIL in *. lia. }
cbn [orb negb]. replace ((65536 <=? bv_unsigned a) && (bv_unsigned a <? 6582272))%bool with true; [reflexivity|].
symmetry. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma H1g_hull : forall a : word, 65536 <= bv_unsigned a < 6582272 -> H1g a = false.
Proof.
intros a Ha. unfold H1g. rewrite (hid_hull a Ha). cbn [orb]. unfold gapb. destruct gap_bounds as (_ & _ & B3 & _).
apply andb_false_iff. left. apply Z.leb_gt. lia.
Qed.

Lemma mrestrict_H1g : mrestrict H1g FULL = mrestrict gapb (mrestrict HID FULL).
Proof. apply functional_extensionality. intros a. unfold mrestrict, H1g. destruct (HID a), (gapb a); reflexivity. Qed.

Lemma gap_apart_avoids : forall M K, know_ok JOB6SEGS E M (kn ch) -> kentry_ok JOB6SEGS E M K -> gap_apart (kn ch) K = true -> fact_avoids gapb E K.
Proof.
intros M K HK Hk Hg. destruct gap_bounds as (B1 & _).
assert (AV : forall b off n, ranges_apart_x (kn ch) b off n GB GK (ELit 20) = true ->
forall i, 0 <= i < elenZ E n -> 0 <= estart E (SA b off) -> estart E (SA b off) + elenZ E n <= 2 ^ 64 ->
gapb (Z_to_bv 64 (estart E (SA b off) + i)) = false).
{ intros b off n Hr i Hi F1 F4. destruct (ranges_apart_x_sound JOB6SEGS E M (kn ch) b off n GB GK (ELit 20) HK Hr) as [A|A];
rewrite estart_GB in A; unfold gapb; rewrite u64_lit by lia.
- apply andb_false_iff. left. apply Z.leb_gt. lia.
- unfold elenZ in A at 1. cbn [edenot] in A. rewrite u64_lit in A by lia. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
destruct K; cbn [gap_apart fact_avoids kentry_ok] in *; try exact I.
- destruct a as [b off]. destruct Hk as (Hw & (F1 & F2 & F3 & F4) & _). intros i Hi.
apply (AV _ _ _ Hg i); unfold elenZ; cbn [edenot]; rewrite ?u64_lit by lia; lia.
- destruct a as [b off]. destruct Hk as ((F1 & F2 & F3 & F4) & _). intros i Hi. apply (AV b off n Hg i Hi); lia.
- destruct a as [b off]. destruct Hk as ((F1 & F2 & F3 & F4) & _). intros i Hi. apply (AV b off n Hg i Hi); lia.
- destruct a as [b off]. destruct Hk as ((F1 & F2 & F3 & F4) & _). intros i Hi. apply (AV b off n Hg i Hi); lia.
- destruct a as [b off]. destruct Hk as ((F1 & F2 & F3 & F4) & _). intros i Hi. apply (AV b off n Hg i Hi); lia.
- destruct a as [b off]. destruct Hk as ((F1 & F2 & F3 & F4) & _). intros i Hi. apply (AV b off n Hg i Hi); lia.
Qed.

Lemma kn_rest_In : forall K, In K (kn_rest ch) -> In K (kn ch).
Proof. intros K HK. unfold kn_rest in HK. apply filter_In in HK. exact (proj1 HK). Qed.

Lemma know_gap : know_ok JOB6SEGS E (mrestrict H1g FULL) (kn_rest ch).
Proof.
pose proof (P co_know) as KR. unfold Mr in KR.
pose proof (GAP_APART w ch HCL) as GA. rewrite forallb_forall in GA.
rewrite mrestrict_H1g. unfold know_ok. apply Forall_forall. intros K HK.
pose proof (proj1 (Forall_forall _ _) KR K (kn_rest_In K HK)) as Hk.
apply kentry_ok_hide; [exact Hk|]. exact (gap_apart_avoids _ K KR Hk (GA K HK)).
Qed.

Lemma know_full : know_ok JOB6SEGS E FULL (kn ch).
Proof.
pose proof (P co_know) as KR. unfold Mr in KR.
apply (know_ok_full JOB6SEGS HID HID_off (img_lo BJO6) (img_hi BJO6)); [| exact (HS2_kimg w ch HCL) | exact KR].
intros a Ha. cbn [img_lo img_hi BJO6] in Ha. apply hid_hull. lia.
Qed.

Lemma u_auxv : bv_unsigned (edenot E E_AUXV) = usp + 8 * argc + 8 * envc.
Proof.
pose proof (proj1 (P co_sinv)) as Senv.
rewrite (edenot_ev_agree NX0 E (E0 JOB6PH sp rdraw brk0 argv envp uid hw) E_AUXV Senv eq_refl eq_refl).
pose proof (QpvH.u_e_auxv JOB6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U.
pose proof (split_lit_denot (E0 JOB6PH sp rdraw brk0 argv envp uid hw) e_auxv E_AUXV 24 split_auxv) as S.
unfold uE in U. rewrite S, u_lit64a in U.
pose proof (u64_range (edenot (E0 JOB6PH sp rdraw brk0 argv envp uid hw) E_AUXV)). pose proof (u64_range sp).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma stack_fact_avoids : forall K, stack_fact K = true -> fact_avoids (hidden LV mo) E K.
Proof.
intros K Hs.
pose proof (QpvH.usp_fit JOB6PH sp rdraw argv envp uid hw Hfit) as Ufit.
pose proof (QpvH.bsb_ge JOB6PH sp rdraw argv envp uid hw) as [G _].
pose proof (MA main_atop_bounds) as AB. rewrite atop_val in AB.
destruct K; cbn [stack_fact] in Hs; try discriminate Hs. destruct a as [b off]. cbn [fact_avoids].
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply expr_eqb_eq in H1. subst b.
apply Z.leb_le in H2. apply Z.leb_le in H3. intros i Hi. unfold estart. cbn [a_base a_off]. rewrite u_auxv.
unfold hidden. apply negb_false_iff. rewrite u64_lit by lia. apply allowed_base. right. rewrite atop_val. lia.
Qed.

Lemma H21 : forall a : word, bv_unsigned a < 2^47 -> hidden LV mo a = true -> H1g a = true.
Proof. intros a Ha Hh. unfold H1g. destruct (hidL_hid_gap a Ha Hh) as [-> | ->]; [reflexivity | apply orb_true_r]. Qed.

Lemma know_rest_view : know_ok JOB6SEGS E (view LV mo FULL) (kn_rest ch).
Proof.
pose proof know_gap as KG. pose proof know_full as KF.
pose proof (FACTS_CLASSIFIED w ch HCL) as Hcl. pose proof (HS2_kimg w ch HCL) as Hki. cbn [img_lo img_hi BJO6] in Hki.
unfold know_ok. apply Forall_forall. intros K HK.
unfold facts_classified in Hcl. rewrite forallb_forall in Hcl. pose proof (Hcl K HK) as HC. apply orb_prop in HC as [Hb|Hs].
- unfold view.
apply (kentry_ok_mono JOB6SEGS H1g (hidden LV mo) H1g_off (2^47) H21 65536 6582272 H1g_hull E FULL (kn_rest ch) K KG).
+ unfold kimg_inside in Hki. rewrite forallb_forall in Hki. specialize (Hki K (kn_rest_In K HK)).
destruct K; try exact I. apply andb_prop in Hki as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
+ exact Hb.
+ unfold know_ok in KG. rewrite Forall_forall in KG. exact (KG K HK).
- unfold view. apply kentry_ok_hide; [| exact (stack_fact_avoids K Hs)].
unfold know_ok in KF. rewrite Forall_forall in KF. exact (KF K (kn_rest_In K HK)).
Qed.

Lemma usp_val : usp = 32768 * bv_unsigned (ev E 0) + 16 * bv_unsigned (ev E 6) /\ 0 <= bv_unsigned (ev E 6) <= 2047.
Proof.
pose proof (P co_know) as K. unfold know_ok in K. rewrite Forall_forall in K.
destruct (HS2_band_facts w ch HCL) as (_ & I6). pose proof (K _ I6) as K6. unfold F6 in K6. cbn [kentry_ok edenot] in K6.
destruct topp_val as (_ & K0 & _).
pose proof (proj1 (P co_sp0)) as Hsp0. unfold uE in Hsp0.
change e_sp0 with (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) in Hsp0. cbn [edenot] in Hsp0.
rewrite u_add64, !u_mul64, !u64_lit in Hsp0 by lia.
split; [|exact K6]. rewrite <- Hsp0. rewrite (Z.mod_small (32768 * _)), (Z.mod_small (16 * _)), Z.mod_small by lia. reflexivity.
Qed.

Lemma neg_scale2 : forall c1 c2 V0 V1, 0 < c1 -> 0 < c2 -> 0 <= V0 -> 0 <= V1 -> 0 < c1 * V0 + c2 * V1 < 2 ^ 64 ->
(((- c1) mod 2 ^ 64 * V0) mod 2 ^ 64 + ((- c2) mod 2 ^ 64 * V1) mod 2 ^ 64) mod 2 ^ 64 = 2 ^ 64 - c1 * V0 - c2 * V1.
Proof.
intros c1 c2 V0 V1 H1 H2 H3 H4 H5.
rewrite !Z.mul_mod_idemp_l by lia. rewrite <- Zplus_mod.
replace (- c1 * V0 + - c2 * V1) with ((2 ^ 64 - c1 * V0 - c2 * V1) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma estart_VB : estart E (SA VB VK) = GHI + 512 /\ elenZ E VLEN = 0x7fff8000 + 2 ^ 44 - (GHI + 512).
Proof.
destruct usp_val as (HU & K6). destruct topp_val as (_ & K0 & _).
assert (HG : GHI = 4096 * bv_unsigned (ev E 0) + 2 * bv_unsigned (ev E 6) + 2146402304).
{ unfold GHI. rewrite atop_val, HU.
replace (32768 * bv_unsigned (ev E 0) + 16 * bv_unsigned (ev E 6) - 8388608)
with ((4096 * bv_unsigned (ev E 0) + 2 * bv_unsigned (ev E 6) - 1048576) * 8) by lia.
rewrite Z.div_mul by lia. lia. }
split.
- unfold estart, VB, VK. cbn [a_base a_off edenot]. rewrite u_add64, !u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)), (Z.mod_small (2 * _)), Z.mod_small by lia. lia.
- unfold elenZ, VLEN. cbn [edenot]. rewrite !u_add64, !u_mul64. rewrite (u64_lit 0x1000000ffe00) by lia. rewrite !u_lit64a.
rewrite (neg_scale2 4096 2) by lia.
replace (2 ^ 64 - 4096 * bv_unsigned (ev E 0) - 2 * bv_unsigned (ev E 6) + 17592187092480)
with (17592187092480 - 4096 * bv_unsigned (ev E 0) - 2 * bv_unsigned (ev E 6) + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma elen_GLEN : elenZ E GLEN = 0x7fff8000 + 2 ^ 44 - GLO.
Proof.
destruct topp_val as (HT & K0 & K10). rewrite <- estart_GB.
unfold elenZ, GLEN, estart, GB, GK. cbn [a_base a_off edenot]. rewrite !u_add64, !u_mul64.
rewrite (u64_lit 0x100000100000), (u64_lit 4096), (u64_lit 512) by lia. rewrite !u_lit64a.
rewrite (neg_scale2 4096 512) by lia.
rewrite (Z.mod_small (4096 * _)), (Z.mod_small (512 * _)), (Z.mod_small (4096 * _ + 512 * _)) by lia.
replace (2 ^ 64 - 4096 * bv_unsigned (ev E 0) - 512 * bv_unsigned (ev E 10) + 17592187092992)
with (17592187092992 - 4096 * bv_unsigned (ev E 0) - 512 * bv_unsigned (ev E 10) + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma view_stack_shadow : forall z, GHI <= z < 0x7fff8000 + 2 ^ 44 -> hidden LV mo (Z_to_bv 64 z) = false.
Proof.
intros z Hz. destruct gap_bounds as (_ & B2 & B3 & B4). unfold hidden. apply negb_false_iff.
rewrite u64_lit by lia. apply allowed_stack_shadow. exact Hz.
Qed.

Lemma kz_band_view : kentry_ok JOB6SEGS E (view LV mo FULL) KZ_BAND_V.
Proof.
destruct estart_VB as (ES & EL). destruct gap_bounds as (B1 & B2 & B3 & B4). destruct band_sh as (S1 & S2).
unfold KZ_BAND_V. cbn [kentry_ok]. split.
- unfold flat. rewrite ES, EL. lia.
- intros i Hi. rewrite ES. rewrite EL in Hi. unfold view, QQIi.mrestrict. rewrite view_stack_shadow by lia.
apply (MA stack_shadow_zero). rewrite S1, S2. rewrite u64_lit by lia. lia.
Qed.

Lemma kw_band_view : kentry_ok JOB6SEGS E (view LV mo FULL) KW_BAND_V.
Proof.
destruct estart_VB as (ES & EL). destruct gap_bounds as (B1 & B2 & B3 & B4).
pose proof (P co_know) as K. unfold know_ok in K. rewrite Forall_forall in K.
destruct (HS2_band_facts w ch HCL) as (IW & _). pose proof (K _ IW) as KW0. unfold KW_BAND in KW0. cbn [kentry_ok] in KW0. destruct KW0 as [_ KW].
rewrite estart_GB, elen_GLEN in KW.
unfold KW_BAND_V. cbn [kentry_ok]. split.
- unfold flat. rewrite ES, EL. lia.
- intros d m Hd Hm. rewrite ES. rewrite EL in Hm.
specialize (KW (GHI + 512 - GLO + d) m ltac:(lia) ltac:(lia)).
replace (GLO + (GHI + 512 - GLO + d)) with (GHI + 512 + d) in KW by lia.
unfold Mr in KW. destruct (store_ok_restrict JOB6SEGS HID HID_off m FULL _ KW) as [Hf _].
unfold view. rewrite (store_ok_mrestrict_eq JOB6SEGS (hidden LV mo)); [exact Hf|].
intros kk Hkk. unfold woff. rewrite u64_lit by lia.
replace (GHI + 512 + d + Z.of_nat kk) with (GHI + (512 + d + Z.of_nat kk)) by lia. apply view_stack_shadow. lia.
Qed.

Theorem main_know_view : know_ok JOB6SEGS E (view LV mo FULL) (kn_view ch).
Proof.
unfold kn_view, know_ok. apply Forall_cons; [exact kz_band_view|]. apply Forall_cons; [exact kw_band_view|]. exact know_rest_view.
Qed.
End Vis.
