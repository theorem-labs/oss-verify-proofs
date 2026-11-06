(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF61 YE1n YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition STRNLEN_STK : Z := ESTACK + 32.
Definition A_strnlen_ret {imgk : img} : Z := (0x9bd40 + D_10ec).
Definition ss_strnlen {imgk : img} : sstate :=
mkSS tfx_A_musl_strnlen sr_atoms [YQ0b.mkRegion (Some 2%nat) (-32) 0 (-32) 0 []] None (mkFacts [] [] []).
Section S. Context {imgk : img}.
Variable B : asyms.
Hypothesis TL : TfxSyms B.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis AMEMCHR : amemchr0_realizesM B (pc_wrap_memchr (as_code B)).
Let HBcode := ts_code B TL.
Lemma strnlen_entry : forall (W : world tfxsegs) regs mem,
32 <= spZ regs -> spZ regs <= 2 ^ 64 ->
(forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok tfxsegs (Ereg regs []) ss_strnlen
(restrict (w_H W) (mkst regs (Z_to_bv 64 tfx_A_musl_strnlen) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem Hsp Hsp2 Hpres. rewrite restrict_mkst_fx. unfold ss_strnlen.
img_apply (entry_st_ok tfxsegs).
- img_case; vm_compute. all: img_refl.
- constructor; [|img_try (constructor)].
img_apply (region_ok_stack tfxsegs (Ereg regs []) _ 2 (spZ regs) (-32)).
+ rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). img_refl.
+ img_lia. + img_lia.
+ intros a Ha. img_apply apresent_writable. img_apply Hpres. img_lia.
- cbn [pairwise_disjoint all_disjoint]. split; img_exact I.
- constructor.
Qed.
Lemma apresent_of_writable : forall (H : word -> bool) (m : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ in_img tfxsegs a ->
writable_at tfxsegs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hn Hw. unfold apresent. unfold writable_at, wview, mrestrict in Hw.
rewrite unsigned_lit_small in Hw by img_lia. rewrite (find_segment_none a Hn) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [img_try (exfalso; img_apply Hw; img_refl)|].
split; [img_refl|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl)|].
try rewrite Eb in Hw. exfalso. img_apply Hw. img_refl.
Qed.
Lemma tfx_segs_low : forall a, in_img tfxsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
revert Hin Hr. img_case; intros Hin Hr.
all: unfold tfxsegs, tfx_loaded_segments in Hin; cbn in Hin.
all: destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.
Lemma high_not_img : forall a, kLowMemEnd <= a -> ~ in_img tfxsegs a.
Proof. intros a Ha Hin. pose proof (tfx_segs_low a Hin). img_lia. Qed.
Theorem tfx_strnlen_at : forall ly S (W : world tfxsegs) regs mem md x n k,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + STRNLEN_STK <= spZ regs ->
(forall a, spZ regs - STRNLEN_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 ->
0 < x -> 0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= kHighMemEnd ->
first_byte tfxsegs W mem x n 0 k ->
(forall a, x <= a < x + (k + 1) ->
aview tfxsegs (w_H W) mem a <> None /\ ~ (spZ regs - STRNLEN_STK <= a < spZ regs)) ->
amem_range x (k + 1) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfxsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
SRr tfxsegs W (cfg_at tfxsegs tfx_A_musl_strnlen regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STRNLEN_STK <= a < spZ regs) ->
aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md x n k HPRE Hstk Hpres Ha0 Ha1 Hn Hx0 Hk0 Hk8 Hk32 Hxhi Hfb Hsrc Ham Hra_s Hhull Htail Hrom.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Hstop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx.
assert (HES : ESTACK = 4096) by img_refl. assert (HSTK : STRNLEN_STK = 4096 + 32) by img_refl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold cfg_at. img_change (w64 tfx_A_musl_strnlen) with (Z_to_bv 64 tfx_A_musl_strnlen).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (strnlen_entry W regs mem ltac:(img_lia) ltac:(img_lia) ltac:(img_try (intros a Ha; img_apply Hpres; img_lia))) as HS.
remember (Ereg regs []) as E eqn:HE.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (img_try (intros i r Hi; (subst E; cbv beta); img_exact (ew_Ereg_nat regs [] i r Hi))).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E1. pose proof (EE 2%nat (2%bv : bv 5) eq_refl) as E2.
pose proof (EE 3%nat (3%bv : bv 5) eq_refl) as E3. pose proof (EE 4%nat (4%bv : bv 5) eq_refl) as E4.
pose proof (EE 8%nat (8%bv : bv 5) eq_refl) as E8. pose proof (EE 9%nat (9%bv : bv 5) eq_refl) as E9.
pose proof (EE 10%nat (10%bv : bv 5) eq_refl) as E10. pose proof (EE 11%nat (11%bv : bv 5) eq_refl) as E11.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (img_try (rewrite E2; img_refl)).
srr_run_with tfxmusl_tbl_ok HS.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
rewrite Hshape.
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11. rreg HS (12%bv : bv 5) R12.
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
set (md1 := with_vm_backing (m_vm_lazy md) mat md).
assert (WIN : forall a, in_wrange E (ss_mem ss_strnlen) a -> spZ regs + -32 <= a < spZ regs + 0).
{ intros a Ha. eapply (in_wrange_single E _ a 2%nat (-32) 0 (spZ regs)); [| img_try (img_exact Usp) | img_try (img_exact Ha)].
intros t Ht. cbn in Ht. destruct Ht as [<- | []]. left. img_refl. }
assert (OUT1 : forall y : word, ~ (spZ regs - 32 <= bv_unsigned y < spZ regs) -> mem1 y = mem y).
{ intros y Hy. img_apply HF. intros Hin. img_apply Hy. pose proof (WIN _ Hin). img_lia. }
assert (OUT1r : forall y : word, ~ (spZ regs - 32 <= bv_unsigned y < spZ regs) ->
mrestrict (w_H W) mem1 y = mrestrict (w_H W) mem y).
{ intros y Hy. img_apply HFr. intros Hin. img_apply Hy. pose proof (WIN _ Hin). img_lia. }
clear HF HFr.
assert (AV1 : forall a, ~ (spZ regs - 32 <= a < spZ regs) -> 0 <= a < 2 ^ 64 ->
aview tfxsegs (w_H W) mem1 a = aview tfxsegs (w_H W) mem a).
{ intros a Ha Hr. img_apply aview_eq_of. img_apply OUT1r. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (PRES1w : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem1 a).
{ intros a Ha. img_apply (apresent_of_writable (w_H W) mem1 a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _).
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw. rewrite Usp in Hw.
cbn [restrict ms_mem] in Hw. unfold mem1.
replace a with (spZ regs + (a - spZ regs)) by img_lia. img_apply Hw. img_lia. }
assert (Hsp1 : spZ regs1 = spZ regs - 32).
{ img_change (spZ regs1) with (bv_unsigned (getr regs1 2)). rewrite R2, Usp, unsigned_lit_small by img_lia. img_lia. }
pose proof (same_but_materialized_frame md md1 (with_vm_backing_same md mat)) as MF.
assert (HPRE1 : ecall_pre tfxsegs B ly S W regs1 mem1 md1).
{ split; [|img_try (split; [|split; [|split; [|split; [|split; [|split]]]]])].
- img_apply (al_frame _ _ LAWS ly S W mem md mem1 md1 HAR).
+ intros a Ha Hown. img_apply AV1; [|img_try (img_exact Ha)]. intros Hw'. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_lia) Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfxsegs (w_H W) mem a <> None -> aview tfxsegs (w_H W) mem1 a <> None).
{ intros a Hr Hv. destruct (Z_le_dec (spZ regs - 32) a); [img_try (destruct (Z_lt_dec a (spZ regs)))|].
* img_apply aview_some_of_apresent. img_apply PRES1w. img_lia.
* rewrite AV1; [img_try (img_exact Hv) | img_lia | img_try (img_exact Hr)].
* rewrite AV1; [img_try (img_exact Hv) | img_lia | img_try (img_exact Hr)]. }
intros a Hv. rewrite (aview_mod _ mem1 a). img_apply PV; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (rewrite <- aview_mod; img_exact Hv)].
+ img_apply MF. + img_apply MF. + img_apply MF.
+ img_exact (hs_kept_win _ _ _ _ _ _ _ _ OUT1 Hpres ltac:(img_lia) ltac:(img_lia)).
- rewrite R1. img_case; vm_compute. all: img_refl.
- rewrite Hsp1. replace (spZ regs - 32) with (spZ regs + (-2) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal16.
- img_lia.
- img_lia.
- intros a Ha. rewrite Hsp1 in Ha. destruct (Hpres a ltac:(img_lia)) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b.
unfold mem1. rewrite OUT1; [img_try (img_exact Hb)|]. rewrite unsigned_lit_small by img_lia. img_lia.
- rewrite R3, E3. img_exact Hgp.
- rewrite R4, E4. img_exact Htp. }
assert (SRNG : forall a, x <= a < x + (k + 1) -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 32 <= a < spZ regs)).
{ intros a Ha. destruct (Hsrc a Ha) as [_ Hns]. split; [img_lia | img_lia]. }
assert (SHA : forall y, 0 <= y < kHighMemEnd -> 0 <= shadow_addr y < 2 ^ 64 /\ ~ (spZ regs - 32 <= shadow_addr y < spZ regs)
/\ shadow_addr y / 8 * 8 + 8 <= spZ regs - 32).
{ intros y Hy. pose proof (shadow_addr_bounds y Hy) as [B1 B2]. split; [img_lia|]. split; [img_lia|]. img_lia. }
pose proof AMEMCHR as AM. unfold amemchr0_realizesM, cfg_at in AM. rewrite HBcode in AM. cbn [pc_wrap_memchr Tfx_code] in AM.
eapply SRr_bind.
{ img_apply (AM ly S W regs1 mem1 md1 x n k HPRE1).
- rewrite R10, E10. img_exact Ha0.
- rewrite R11. img_refl.
- rewrite R12, E11. img_exact Ha1.
- img_exact Hn.
- img_lia.
- img_exact Hk0.
- img_exact Hk8.
- img_exact Hk32.
- unfold kHighMemEnd in Hxhi. img_lia.
-   destruct Hfb as (Hk & Hbef & Hlast). split; [img_try (img_exact Hk)|]. split.
+ intros i Hi. rewrite AV1; [img_try (img_apply Hbef; img_exact Hi) | |]; img_apply (SRNG (x + i)); img_lia.
+ intros Hkn. rewrite AV1; [img_try (img_apply Hlast; img_exact Hkn) | |]; img_apply (SRNG (x + k)); img_lia.
-   intros a Ha. destruct (Hsrc a Ha) as [Hv Hns]. split; [img_try (rewrite AV1; [img_exact Hv | img_lia | img_lia]) | img_try (rewrite Hsp1; img_lia)].
- img_exact Ham.
- eapply range_addressable_agree; [|img_try (img_exact Hra_s)]. intros y Hy. img_change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
pose proof (SHA y ltac:(img_lia)) as (S1 & S2 & S3). img_apply AV1; [img_try (img_exact S2) | img_try (img_exact S1)].
-   intros s Hs. rewrite AV1; [img_try (img_exact (Hhull s Hs)) | |];
pose proof (SHA x ltac:(img_lia)) as (S1 & S2 & S3); pose proof (SHA (x + (k + 1) - 1) ltac:(img_lia)) as (T1 & T2 & T3); img_lia.
-
intros a Ha. pose proof (Z.mod_pos_bound (x + k) 8 ltac:(img_lia)). pose proof (proj2 (Hsrc (x + k) ltac:(img_lia))) as Hnk. unfold STRNLEN_STK in Hnk.
rewrite AV1; [img_try (img_apply Htail; img_exact Ha) | img_lia | img_try (unfold kHighMemEnd in Hxhi; img_lia)].
-
intros a Ha. pose proof mc_bounds as [MB1 MB2]. rewrite AV1; [img_try (img_exact (Hrom a Ha)) | img_lia | img_lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsbm2 & Hres & Hfr2 & Hpres2).
assert (Hra1 : w64 (raZ regs1) = Z_to_bv 64 A_strnlen_ret) by (img_try (unfold raZ, w64; rewrite R1, unsigned_lit_small by img_lia; img_refl)).
rewrite Hra1.
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STRNLEN_STK <= a < spZ regs - 32) ->
aview tfxsegs (w_H W) mem2 a = aview tfxsegs (w_H W) mem1 a).
{ intros a Hr Ha. img_apply Hfr2; [img_try (img_exact Hr)|]. rewrite Hsp1. img_lia. }
assert (PRES2w : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem2 a).
{ intros a Ha. img_apply Hpres2. img_apply PRES1w. img_exact Ha. }
jafter_call HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|img_try (specialize (HS2 HRK); clear HRK)] end.
{ cbn [ms_mem restrict]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Usp; intros a Ha.
- img_apply mbyte_of_aview. unfold mem1. img_apply AV2; img_lia.
- intros _. img_apply apresent_writable. img_apply PRES2w. img_lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as Eb eqn:HEb.
assert (OLD : forall i, (i < 32)%nat -> ew Eb i = ew E i) by (img_try (intros i Hi; rewrite HEb; img_apply ew_havoc_old; img_exact Hi)).
assert (F36 : ew Eb 36 = w64 (x + k)).
{ rewrite HEb. img_change 36%nat with (32 + 4)%nat. rewrite (ew_havoc_new E 32 _ 4 (Z_to_bv 64 0)) by (img_try (cbn; img_lia)). cbn. img_exact Hres. }
assert (HAEb : env_agree 32 (Ereg regs []) Eb) by (img_try (rewrite HEb, HE; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (split; [intros i Hi; img_refl | img_refl])])).
pose proof Hfb as (Hk & _ & _).
assert (TAIL : forall ss3 ms3 mat3,
st_ok tfxsegs Eb ss3 (restrict (w_H W) ms3) -> ss_resv ss3 = None ->
clookup tfxmusl_tbl (ss_pc ss3) = Some RET_WORD_r ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss3) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
sr_get (ss_regs ss3) 1 = SOff 1 0 ->
getr (ms_regs ms3) 10 = w64 k ->
(exists cs, ss_mem ss3 = [YQ0b.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs]) ->
frame_of Eb (ss_mem ss3) mem2 (ms_mem ms3) ->
frame_of Eb (ss_mem ss3) (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms3)) ->
SRr tfxsegs W (mkCfg ms3 (with_vm_backing (m_vm_lazy md2) mat3 md2))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (w64 (raZ regs)) mem' (seg_rom tfxsegs)) md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STRNLEN_STK <= a < spZ regs) ->
aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros ss3 ms3 mat3 HS3 Hrv3 Hpc3 Hcs3 Hsr1 Ha0' [cs Hm3] HF3 HFr3.
eapply (SRr_ret_at tfxsegs tfxmusl_tbl tfxmusl_tbl_ok Hwx W Eb); [img_try (img_exact HS3) | img_try (img_exact Hrv3) | img_try (img_exact Hpc3) |].
intros mat4. split; [img_refl|].
set (mem3 := ms_mem ms3). set (regs3 := ms_regs ms3).
assert (Usp' : bv_unsigned (ew Eb 2) = spZ regs) by (img_try (rewrite OLD by ((img_case; cbv); img_lia); img_exact Usp)).
assert (WIN3 : forall a, in_wrange Eb (ss_mem ss3) a -> spZ regs + -32 <= a < spZ regs + 0).
{ intros a Ha. eapply (in_wrange_single Eb _ a 2%nat (-32) 0 (spZ regs)); [| img_try (img_exact Usp') | img_try (img_exact Ha)].
intros t Ht. rewrite Hm3 in Ht. cbn in Ht. destruct Ht as [<- | []]. left. img_refl. }
assert (OUT3 : forall y : word, ~ (spZ regs - 32 <= bv_unsigned y < spZ regs) -> mem3 y = mem2 y).
{ intros y Hy. img_apply HF3. intros Hin. img_apply Hy. pose proof (WIN3 _ Hin). img_lia. }
assert (AV3 : forall a, ~ (spZ regs - 32 <= a < spZ regs) -> 0 <= a < 2 ^ 64 ->
aview tfxsegs (w_H W) mem3 a = aview tfxsegs (w_H W) mem2 a).
{ intros a Ha Hr. img_apply aview_eq_of. img_apply HFr3. intros Hin. pose proof (WIN3 _ Hin).
rewrite unsigned_lit_small in H by img_lia. img_lia. }
assert (PRES3w : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem3 a).
{ intros a Ha. img_apply (apresent_of_writable (w_H W) mem3 a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS3 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _). rewrite Hm3 in Hrs.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _).
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw. rewrite Usp' in Hw.
cbn [restrict ms_mem] in Hw. unfold mem3.
replace a with (spZ regs + (a - spZ regs)) by img_lia. img_apply Hw. img_lia. }
pose proof (same_but_materialized_frame md2 _ (with_vm_backing_same md2 mat4)) as MF3.
exists regs3, mem3, (with_vm_backing (m_vm_lazy md2) mat4 md2).
split; [|img_try (split; [|split; [|split; [|split; [img_exact Ha0'|split]]]])].
-
unfold regs3. rewrite (st_ok_restrict_reg tfxsegs (w_H W) Eb _ _ 1 HS3), Hsr1. cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, OLD by (img_try ((img_case; cbv); img_lia)). rewrite E1.
unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. rewrite Hra. img_refl.
-
img_apply (al_frame _ _ LAWS ly S W mem2 md2 mem3 _ HAR2).
+ intros a Ha Hown. img_apply AV3; [|img_try (img_exact Ha)]. intros Hw'. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_lia) Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfxsegs (w_H W) mem2 a <> None -> aview tfxsegs (w_H W) mem3 a <> None).
{ intros a Hr Hv. destruct (Z_le_dec (spZ regs - 32) a); [img_try (destruct (Z_lt_dec a (spZ regs)))|].
* img_apply aview_some_of_apresent. img_apply PRES3w. img_lia.
* rewrite AV3; [img_try (img_exact Hv) | img_lia | img_try (img_exact Hr)].
* rewrite AV3; [img_try (img_exact Hv) | img_lia | img_try (img_exact Hr)]. }
intros a Hv. rewrite (aview_mod _ mem3 a). img_apply PV; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (rewrite <- aview_mod; img_exact Hv)].
+ img_apply MF3. + img_apply MF3. + img_apply MF3.
+ img_exact (hs_kept_win _ _ _ _ _ _ _ _ OUT3 PRES3w ltac:(img_lia) ltac:(img_lia)).
-
eapply aregs_preserved_trans; [| img_try (img_exact (aregs_preserved_of_st_ok _ Eb _ _ regs [] HS3 HAEb Hcs3))].
intros r Hr. img_refl.
-
eapply same_but_materialized_trans; [| img_try (img_apply with_vm_backing_same)].
eapply same_but_materialized_trans; [img_try (img_apply with_vm_backing_same) | img_try (img_exact Hsbm2)].
-
intros a Hr Ha. rewrite AV3 by img_lia. rewrite AV2 by img_lia. img_apply AV1; img_lia.
-
assert (PVp : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem a -> apresent (w_H W) mem3 a).
{ intros a Hr Hp.
assert (CASE : (spZ regs - 32 <= a < spZ regs) \/ ~ (spZ regs - 32 <= a < spZ regs)) by img_lia.
destruct CASE as [Hin | Hout]; [img_try (img_apply PRES3w; img_exact Hin)|].
assert (Hp2 : apresent (w_H W) mem2 a).
{ img_apply Hpres2. destruct Hp as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. unfold mem1.
rewrite OUT1; [img_try (img_exact Hb)|]. rewrite unsigned_lit_small by img_lia. img_exact Hout. }
destruct Hp2 as [Hh2 [b2 Hb2]]. split; [img_try (img_exact Hh2)|]. exists b2. unfold mem3.
rewrite OUT3; [img_try (img_exact Hb2)|]. rewrite unsigned_lit_small by img_lia. img_exact Hout. }
intros a Hp. rewrite apresent_mod. img_apply PVp; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (rewrite <- apresent_mod; img_exact Hp)]. }
srr_branch_with tfxmusl_tbl_ok HS.
+
exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite U_lit in Hc by img_lia.
unfold kHighMemEnd in Hxhi. rewrite (U_atom Eb 36 (x + k) F36) in Hc by img_lia. img_lia.
+
assert (Hkn : k < n) by img_lia.
srr_run_with tfxmusl_tbl_ok HS.
lazymatch type of HS with st_ok _ _ ?ss3 (restrict _ ?ms3) =>
img_apply (TAIL ss3 ms3 _ HS eq_refl); [img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | img_refl | | img_try (eexists; img_refl) | img_try (img_exact HF) | img_try (img_exact HFr)] end.
rreg HS (10%bv : bv 5) Q10. rewrite Q10, F36, OLD by (img_try ((img_case; cbv); img_lia)). rewrite E10, Ha0.
img_apply bv_eq. unfold alu64, alu, mul_div, w64.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. rewrite (Z.mod_small x) by img_lia. rewrite (Z.mod_small (x + k)) by img_lia.
replace (x * (18446744073709551615 mod 2 ^ 64) + (x + k)) with (k + x * 2 ^ 64) by (img_try (img_change (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1); img_lia)).
rewrite Z_mod_plus_full. img_refl.
Qed.
End S.
End c.
