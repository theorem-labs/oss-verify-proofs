(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3a AE39 AE20 AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition STRNLEN_STK : Z := ESTACK + 32.
Definition A_strnlen_ret : Z := 0x97b44.
Definition ss_strnlen : sstate :=
mkSS tfib_A_musl_strnlen sr_atoms [YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 []] None (mkFacts [] [] []).
Section S.
Variable B : asyms.
Hypothesis TL : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCHR : amemchr0_realizesM B (pc_wrap_memchr (as_code B)).
Let HBcode := ts_code B TL.
Lemma strnlen_entry : forall (W : world tfibsegs) regs mem,
32 <= spZ regs -> spZ regs <= 2 ^ 64 ->
(forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok tfibsegs (Ereg regs []) ss_strnlen
(restrict (w_H W) (mkst regs (Z_to_bv 64 tfib_A_musl_strnlen) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem Hsp Hsp2 Hpres. rewrite restrict_mkst_fx. unfold ss_strnlen.
apply (entry_st_ok tfibsegs).
- vm_compute. reflexivity.
- constructor; [|constructor].
apply (region_ok_stack tfibsegs (Ereg regs []) _ 2 (spZ regs) (-32)).
+ rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). reflexivity.
+ lia. + lia.
+ intros a Ha. apply apresent_writable. apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- constructor.
Qed.
Lemma apresent_of_writable : forall (H : word -> bool) (m : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
writable_at tfibsegs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hn Hw. unfold apresent. unfold writable_at, wview, mrestrict in Hw.
rewrite unsigned_lit_small in Hw by lia. rewrite (find_segment_none a Hn) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|].
try rewrite Eb in Hw. exfalso. apply Hw. reflexivity.
Qed.
Lemma tfib_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
unfold tfibsegs, Asan.M.loaded_segments in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.
Lemma high_not_img : forall a, kLowMemEnd <= a -> ~ in_img tfibsegs a.
Proof. intros a Ha Hin. pose proof (tfib_segs_low a Hin). lia. Qed.
Theorem tfib_strnlen_at : forall ly S (W : world tfibsegs) regs mem md x n k,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + STRNLEN_STK <= spZ regs ->
(forall a, spZ regs - STRNLEN_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 ->
0 < x -> 0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= kHighMemEnd ->
first_byte tfibsegs W mem x n 0 k ->
(forall a, x <= a < x + (k + 1) ->
aview tfibsegs (w_H W) mem a <> None /\ ~ (spZ regs - STRNLEN_STK <= a < spZ regs)) ->
amem_range x (k + 1) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
SRr tfibsegs W (cfg_at tfibsegs tfib_A_musl_strnlen regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STRNLEN_STK <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md x n k HPRE Hstk Hpres Ha0 Ha1 Hn Hx0 Hk0 Hk8 Hk32 Hxhi Hfb Hsrc Ham Hra_s Hhull Htail Hrom.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Hstop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx.
assert (HES : ESTACK = 4096) by reflexivity. assert (HSTK : STRNLEN_STK = 4096 + 32) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold cfg_at. change (w64 tfib_A_musl_strnlen) with (Z_to_bv 64 tfib_A_musl_strnlen).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (strnlen_entry W regs mem ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hpres; lia)) as HS.
remember (Ereg regs []) as E eqn:HE.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (intros i r Hi; subst E; exact (ew_Ereg_nat regs [] i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E1. pose proof (EE 2%nat (2%bv : bv 5) eq_refl) as E2.
pose proof (EE 3%nat (3%bv : bv 5) eq_refl) as E3. pose proof (EE 4%nat (4%bv : bv 5) eq_refl) as E4.
pose proof (EE 8%nat (8%bv : bv 5) eq_refl) as E8. pose proof (EE 9%nat (9%bv : bv 5) eq_refl) as E9.
pose proof (EE 10%nat (10%bv : bv 5) eq_refl) as E10. pose proof (EE 11%nat (11%bv : bv 5) eq_refl) as E11.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
srr_run_with tfibmusl_tbl_ok HS.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
rewrite Hshape.
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11. rreg HS (12%bv : bv 5) R12.
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
set (md1 := with_vm_backing (m_vm_lazy md) mat md).
assert (WIN : forall a, in_wrange E (ss_mem ss_strnlen) a -> spZ regs + -32 <= a < spZ regs + 0).
{ intros a Ha. eapply (in_wrange_single E _ a 2%nat (-32) 0 (spZ regs)); [| exact Usp | exact Ha].
intros t Ht. cbn in Ht. destruct Ht as [<- | []]. left. reflexivity. }
assert (OUT1 : forall y : word, ~ (spZ regs - 32 <= bv_unsigned y < spZ regs) -> mem1 y = mem y).
{ intros y Hy. apply HF. intros Hin. apply Hy. pose proof (WIN _ Hin). lia. }
assert (OUT1r : forall y : word, ~ (spZ regs - 32 <= bv_unsigned y < spZ regs) ->
mrestrict (w_H W) mem1 y = mrestrict (w_H W) mem y).
{ intros y Hy. apply HFr. intros Hin. apply Hy. pose proof (WIN _ Hin). lia. }
clear HF HFr.
assert (AV1 : forall a, ~ (spZ regs - 32 <= a < spZ regs) -> 0 <= a < 2 ^ 64 ->
aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hr. apply aview_eq_of. apply OUT1r. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRES1w : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem1 a).
{ intros a Ha. apply (apresent_of_writable (w_H W) mem1 a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite Usp in Hw.
cbn [restrict ms_mem] in Hw. unfold mem1.
replace a with (spZ regs + (a - spZ regs)) by lia. apply Hw. lia. }
assert (Hsp1 : spZ regs1 = spZ regs - 32).
{ change (spZ regs1) with (bv_unsigned (getr regs1 2)). rewrite R2, Usp, unsigned_lit_small by lia. lia. }
pose proof (same_but_materialized_frame md md1 (with_vm_backing_same md mat)) as MF.
assert (HPRE1 : ecall_pre tfibsegs B ly S W regs1 mem1 md1).
{ split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- apply (al_frame _ _ LAWS ly S W mem md mem1 md1 HAR).
+ intros a Ha Hown. apply AV1; [|exact Ha]. intros Hw'. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem1 a <> None).
{ intros a Hr Hv. destruct (Z_le_dec (spZ regs - 32) a); [destruct (Z_lt_dec a (spZ regs))|].
* apply aview_some_of_apresent. apply PRES1w. lia.
* rewrite AV1; [exact Hv | lia | exact Hr].
* rewrite AV1; [exact Hv | lia | exact Hr]. }
intros a Hv. rewrite (aview_mod _ mem1 a). apply PV; [apply Z.mod_pos_bound; lia | rewrite <- aview_mod; exact Hv].
+ apply MF. + apply MF. + apply MF.
+ exact (hs_kept_win _ _ _ _ _ _ _ _ OUT1 Hpres ltac:(lia) ltac:(lia)).
- rewrite R1. vm_compute. reflexivity.
- rewrite Hsp1. replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- lia.
- lia.
- intros a Ha. rewrite Hsp1 in Ha. destruct (Hpres a ltac:(lia)) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
unfold mem1. rewrite OUT1; [exact Hb|]. rewrite unsigned_lit_small by lia. lia.
- rewrite R3, E3. exact Hgp.
- rewrite R4, E4. exact Htp. }
assert (SRNG : forall a, x <= a < x + (k + 1) -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 32 <= a < spZ regs)).
{ intros a Ha. destruct (Hsrc a Ha) as [_ Hns]. split; [lia | lia]. }
assert (SHA : forall y, 0 <= y < kHighMemEnd -> 0 <= shadow_addr y < 2 ^ 64 /\ ~ (spZ regs - 32 <= shadow_addr y < spZ regs)
/\ shadow_addr y / 8 * 8 + 8 <= spZ regs - 32).
{ intros y Hy. pose proof (shadow_addr_bounds y Hy) as [B1 B2]. split; [lia|]. split; [lia|]. lia. }
pose proof AMEMCHR as AM. unfold amemchr0_realizesM, cfg_at in AM. rewrite HBcode in AM. cbn [pc_wrap_memchr Tfib_code] in AM.
eapply SRr_bind.
{ apply (AM ly S W regs1 mem1 md1 x n k HPRE1).
- rewrite R10, E10. exact Ha0.
- rewrite R11. reflexivity.
- rewrite R12, E11. exact Ha1.
- exact Hn.
- lia.
- exact Hk0.
- exact Hk8.
- exact Hk32.
- unfold kHighMemEnd in Hxhi. lia.
-   destruct Hfb as (Hk & Hbef & Hlast). split; [exact Hk|]. split.
+ intros i Hi. rewrite AV1; [apply Hbef; exact Hi | |]; apply (SRNG (x + i)); lia.
+ intros Hkn. rewrite AV1; [apply Hlast; exact Hkn | |]; apply (SRNG (x + k)); lia.
-   intros a Ha. destruct (Hsrc a Ha) as [Hv Hns]. split; [rewrite AV1; [exact Hv | lia | lia] | rewrite Hsp1; lia].
- exact Ham.
- eapply range_addressable_agree; [|exact Hra_s]. intros y Hy. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
pose proof (SHA y ltac:(lia)) as (S1 & S2 & S3). apply AV1; [exact S2 | exact S1].
-   intros s Hs. rewrite AV1; [exact (Hhull s Hs) | |];
pose proof (SHA x ltac:(lia)) as (S1 & S2 & S3); pose proof (SHA (x + (k + 1) - 1) ltac:(lia)) as (T1 & T2 & T3); lia.
-
intros a Ha. pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)). pose proof (proj2 (Hsrc (x + k) ltac:(lia))) as Hnk. unfold STRNLEN_STK in Hnk.
rewrite AV1; [apply Htail; exact Ha | lia | unfold kHighMemEnd in Hxhi; lia].
-
intros a Ha. pose proof mc_bounds as [MB1 MB2]. rewrite AV1; [exact (Hrom a Ha) | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsbm2 & Hres & Hfr2 & Hpres2).
assert (Hra1 : w64 (raZ regs1) = Z_to_bv 64 A_strnlen_ret) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
rewrite Hra1.
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STRNLEN_STK <= a < spZ regs - 32) ->
aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem1 a).
{ intros a Hr Ha. apply Hfr2; [exact Hr|]. rewrite Hsp1. lia. }
assert (PRES2w : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem2 a).
{ intros a Ha. apply Hpres2. apply PRES1w. exact Ha. }
jafter_call HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
- apply mbyte_of_aview. unfold mem1. apply AV2; lia.
- intros _. apply apresent_writable. apply PRES2w. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as Eb eqn:HEb.
assert (OLD : forall i, (i < 32)%nat -> ew Eb i = ew E i) by (intros i Hi; rewrite HEb; apply ew_havoc_old; exact Hi).
assert (F36 : ew Eb 36 = w64 (x + k)).
{ rewrite HEb. change 36%nat with (32 + 4)%nat. rewrite (ew_havoc_new E 32 _ 4 (Z_to_bv 64 0)) by (cbn; lia). cbn. exact Hres. }
assert (HAEb : env_agree 32 (Ereg regs []) Eb) by (rewrite HEb, HE; apply env_agree_havoc_ge; [cbv; lia | split; [intros i Hi; reflexivity | reflexivity]]).
pose proof Hfb as (Hk & _ & _).
assert (TAIL : forall ss3 ms3 mat3,
st_ok tfibsegs Eb ss3 (restrict (w_H W) ms3) -> ss_resv ss3 = None ->
clookup tfibmusl_tbl (ss_pc ss3) = Some RET_WORD_r ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss3) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
sr_get (ss_regs ss3) 1 = SOff 1 0 ->
getr (ms_regs ms3) 10 = w64 k ->
(exists cs, ss_mem ss3 = [YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs]) ->
frame_of Eb (ss_mem ss3) mem2 (ms_mem ms3) ->
frame_of Eb (ss_mem ss3) (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms3)) ->
SRr tfibsegs W (mkCfg ms3 (with_vm_backing (m_vm_lazy md2) mat3 md2))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (w64 (raZ regs)) mem' (seg_rom tfibsegs)) md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STRNLEN_STK <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros ss3 ms3 mat3 HS3 Hrv3 Hpc3 Hcs3 Hsr1 Ha0' [cs Hm3] HF3 HFr3.
eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W Eb); [exact HS3 | exact Hrv3 | exact Hpc3 |].
intros mat4. split; [reflexivity|].
set (mem3 := ms_mem ms3). set (regs3 := ms_regs ms3).
assert (Usp' : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLD by (cbv; lia); exact Usp).
assert (WIN3 : forall a, in_wrange Eb (ss_mem ss3) a -> spZ regs + -32 <= a < spZ regs + 0).
{ intros a Ha. eapply (in_wrange_single Eb _ a 2%nat (-32) 0 (spZ regs)); [| exact Usp' | exact Ha].
intros t Ht. rewrite Hm3 in Ht. cbn in Ht. destruct Ht as [<- | []]. left. reflexivity. }
assert (OUT3 : forall y : word, ~ (spZ regs - 32 <= bv_unsigned y < spZ regs) -> mem3 y = mem2 y).
{ intros y Hy. apply HF3. intros Hin. apply Hy. pose proof (WIN3 _ Hin). lia. }
assert (AV3 : forall a, ~ (spZ regs - 32 <= a < spZ regs) -> 0 <= a < 2 ^ 64 ->
aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem2 a).
{ intros a Ha Hr. apply aview_eq_of. apply HFr3. intros Hin. pose proof (WIN3 _ Hin).
rewrite unsigned_lit_small in H by lia. lia. }
assert (PRES3w : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem3 a).
{ intros a Ha. apply (apresent_of_writable (w_H W) mem3 a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS3 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _). rewrite Hm3 in Hrs.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite Usp' in Hw.
cbn [restrict ms_mem] in Hw. unfold mem3.
replace a with (spZ regs + (a - spZ regs)) by lia. apply Hw. lia. }
pose proof (same_but_materialized_frame md2 _ (with_vm_backing_same md2 mat4)) as MF3.
exists regs3, mem3, (with_vm_backing (m_vm_lazy md2) mat4 md2).
split; [|split; [|split; [|split; [|split; [exact Ha0'|split]]]]].
-
unfold regs3. rewrite (st_ok_restrict_reg tfibsegs (w_H W) Eb _ _ 1 HS3), Hsr1. cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, OLD by (cbv; lia). rewrite E1.
unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. rewrite Hra. reflexivity.
-
apply (al_frame _ _ LAWS ly S W mem2 md2 mem3 _ HAR2).
+ intros a Ha Hown. apply AV3; [|exact Ha]. intros Hw'. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem2 a <> None -> aview tfibsegs (w_H W) mem3 a <> None).
{ intros a Hr Hv. destruct (Z_le_dec (spZ regs - 32) a); [destruct (Z_lt_dec a (spZ regs))|].
* apply aview_some_of_apresent. apply PRES3w. lia.
* rewrite AV3; [exact Hv | lia | exact Hr].
* rewrite AV3; [exact Hv | lia | exact Hr]. }
intros a Hv. rewrite (aview_mod _ mem3 a). apply PV; [apply Z.mod_pos_bound; lia | rewrite <- aview_mod; exact Hv].
+ apply MF3. + apply MF3. + apply MF3.
+ exact (hs_kept_win _ _ _ _ _ _ _ _ OUT3 PRES3w ltac:(lia) ltac:(lia)).
-
eapply aregs_preserved_trans; [| exact (aregs_preserved_of_st_ok _ Eb _ _ regs [] HS3 HAEb Hcs3)].
intros r Hr. reflexivity.
-
eapply same_but_materialized_trans; [| apply with_vm_backing_same].
eapply same_but_materialized_trans; [apply with_vm_backing_same | exact Hsbm2].
-
intros a Hr Ha. rewrite AV3 by lia. rewrite AV2 by lia. apply AV1; lia.
-
assert (PVp : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem a -> apresent (w_H W) mem3 a).
{ intros a Hr Hp.
assert (CASE : (spZ regs - 32 <= a < spZ regs) \/ ~ (spZ regs - 32 <= a < spZ regs)) by lia.
destruct CASE as [Hin | Hout]; [apply PRES3w; exact Hin|].
assert (Hp2 : apresent (w_H W) mem2 a).
{ apply Hpres2. destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mem1.
rewrite OUT1; [exact Hb|]. rewrite unsigned_lit_small by lia. exact Hout. }
destruct Hp2 as [Hh2 [b2 Hb2]]. split; [exact Hh2|]. exists b2. unfold mem3.
rewrite OUT3; [exact Hb2|]. rewrite unsigned_lit_small by lia. exact Hout. }
intros a Hp. rewrite apresent_mod. apply PVp; [apply Z.mod_pos_bound; lia | rewrite <- apresent_mod; exact Hp]. }
srr_branch_with tfibmusl_tbl_ok HS.
+
exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite U_lit in Hc by lia.
unfold kHighMemEnd in Hxhi. rewrite (U_atom Eb 36 (x + k) F36) in Hc by lia. lia.
+
assert (Hkn : k < n) by lia.
srr_run_with tfibmusl_tbl_ok HS.
lazymatch type of HS with st_ok _ _ ?ss3 (restrict _ ?ms3) =>
apply (TAIL ss3 ms3 _ HS eq_refl); [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | | eexists; reflexivity | exact HF | exact HFr] end.
rreg HS (10%bv : bv 5) Q10. rewrite Q10, F36, OLD by (cbv; lia). rewrite E10, Ha0.
apply bv_eq. unfold alu64, alu, mul_div, w64.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small (x + k)) by lia.
replace (x * (18446744073709551615 mod 2 ^ 64) + (x + k)) with (k + x * 2 ^ 64) by (change (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1); lia).
rewrite Z_mod_plus_full. reflexivity.
Qed.
End S.
End c.
