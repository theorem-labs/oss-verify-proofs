(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (asan-ubsan) walk of fuzz_reply's has_prefix, ported from
   lib/A/W_has_prefix.v (a working branch), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and lib/A/ACbk.v (entry and return). *)
(* Image B's has_prefix (0x86618) is image A's (0x86020) instruction for instruction: UBSan adds no check here, only
   the pc-relative operands move (the strlen / bcmp trampolines, 0x421e4 / 0x42204 in B).  The two return addresses
   below are B's: BASE + AF_fr_has_prefix + 0x28 / + 0x44. *)
(* has_prefix(s, n, p) at 0x86618 measures the NUL-terminated string at p with the strlen interceptor
   and, when its length fits in n, compares the two with the bcmp interceptor.  Both calls are taken as
   Section hypotheses in the donor's site-contract form: ASTRLEN (W_contract.v astrlen_realizes, the
   shape of Reusable/YG0d.v astrnlen_realizes) and ABCMP (Reusable/YG0d.v abcmp_realizes). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_has_prefix : Z := AF_fr_has_prefix.
Definition A_has_prefixP : Z := BASE + A_has_prefix.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bx : sv := SOff 32 0.
Definition HP_FRAME : Z := 32.
Definition hp_regions : smem := [ stack_region HP_FRAME ].
Definition hp_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_hp : sstate := mkSS A_has_prefix sr_atoms hp_regions None hp_facts.
Definition hp_SH : list shent := [].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition hp_extra : list word := map (Z_to_bv 64) [SB].
Lemma hp_entry : forall W ly S regs mem md ch,
afn_pre SEGS B HP_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs hp_extra)) ss_hp
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_has_prefixP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx hp_SH (Eimg (Ereg regs hp_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : HP_STK = 8224) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs hp_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_hp, A_has_prefixP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold hp_regions, stack_region, HP_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
+ apply pairwise_disjoint_of_extents. unfold hp_regions, stack_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; [exact I | exact I]].
cbn [hp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, hp_SH. constructor.
Qed.
Theorem pb_has_prefix : hp_spec B A_has_prefixP.
Proof.
intros W ly S regs mem md ch s n p lp HPRE H10 H11 H12 Rn Rlp0 Rlp32 Rp0 Rpk Rs0 Rsl
HFB HVIS HOFF HMR HM8 HRA HHV HTAIL HROM HCMP.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (hp_entry W ly S regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_init SEGS B HP_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : HP_STK = 8224) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs hp_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs hp_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_has_prefixP) with (Z_to_bv 64 A_has_prefixP).
unfold A_has_prefixP, A_has_prefix.
(* prologue, then the call to strlen *)
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the prologue wrote only inside the 32-byte frame, so every byte the interceptor needs is the
   byte the caller gave us *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha).
intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
unfold stack_region, HP_FRAME in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
rewrite Usp in Hr. lia. }
assert (KEEPLO : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KEEP; lia. }
assert (Usp2 : spZ (ms_regs ms) = spZ regs - 32).
{ unfold spZ. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (OFF32 : forall a, p <= a < p + (lp + 8) -> ~ (spZ regs - 32 <= a < spZ regs)).
{ intros a Ha [HA HB]. apply (HOFF a Ha). split; unfold HP_STK, ESTACK in *; lia. }
eapply SRr_bind.
{ eapply (aj_strlen_at B LAWS _ ASTRLEN W (ms_regs ms) (ms_mem ms) HP_STK (spZ regs) ([] : list (Z * Z))
ly S W mem md ([] : list (Z * Z)) ly S _ 0 p lp (-32) (Z_to_bv 64 (BASE + 17148)) HJ).
- rewrite Q10, E12. reflexivity.
- exact Rp0.
- exact Rlp0.
- exact Rlp32.
- exact Rpk.
- lia.
- reflexivity.
- lia.
- unfold HP_STK, ESTACK. lia.
- rewrite Q3, E3. exact Hgp.
- rewrite Q4, E4. exact Htp.
- exact Q1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- destruct HFB as (Hk1 & Hk2 & Hk3). split; [exact Hk1|]. split.
  + intros i Hi. destruct (Hk2 i Hi) as (b & Hb & Hbz). exists b. split; [|exact Hbz].
    rewrite KEEP by (first [lia | apply OFF32; lia]). exact Hb.
  + intros Hlt. rewrite KEEP by (first [lia | apply OFF32; lia]). exact (Hk3 Hlt).
- intros a Ha. split.
  + rewrite KEEP by (first [lia | apply OFF32; lia]). apply HVIS. lia.
  + intros [HA HB]. apply (HOFF a ltac:(lia)). split; unfold HP_STK, ESTACK in *; lia.
- intros a Ha [HA HB]. apply (HOFF a ltac:(lia)). split; unfold HP_STK, ESTACK in *; lia.
- exact HMR.
- exact HM8.
- intros y Hy. destruct (HRA y Hy) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite <- Hsv. apply KEEPLO.
  assert (HY : 0 <= y < kHighMemEnd)
  by (destruct HMR as [HM | [HM1 HM2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  pose proof (shadow_addr_bounds y HY) as [L1 H1].
  unfold shadow_of_addr, shadow_addr, kLowMemEnd, kHighShadowEnd in *. lia.
- intros sa Hsa. rewrite KEEPLO; [apply HHV; exact Hsa|].
  assert (HY1 : 0 <= p < kHighMemEnd)
  by (destruct HMR as [HM | [HM1 HM2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (HY2 : 0 <= p + (lp + 1) - 1 < kHighMemEnd)
  by (destruct HMR as [HM | [HM1 HM2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  pose proof (shadow_addr_bounds p HY1) as [L1 H1].
  pose proof (shadow_addr_bounds (p + (lp + 1) - 1) HY2) as [L2 H2].
  unfold kLowMemEnd in L1, L2. unfold kHighShadowEnd in H1, H2.
  pose proof (Z.div_pos (shadow_addr p) 8 ltac:(lia) ltac:(lia)) as D1.
  assert (D2 : shadow_addr (p + (lp + 1) - 1) / 8 * 8 <= shadow_addr (p + (lp + 1) - 1))
  by (pose proof (Z.mul_div_le (shadow_addr (p + (lp + 1) - 1)) 8 ltac:(lia)); lia).
  assert (D3 : shadow_addr p / 8 * 8 <= shadow_addr p)
  by (pose proof (Z.mul_div_le (shadow_addr p) 8 ltac:(lia)); lia).
  lia.
- intros a Ha. rewrite KEEP by (first [lia | apply OFF32; lia]). apply HTAIL. exact Ha.
- intros a Hin. rewrite KEEPLO; [apply HROM; exact Hin|].
  destruct Hin as (sg & Hsg & _ & Hr). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr])) as HI. lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hlen & Hfr2 & Hpres2).
(* back in has_prefix with a0 = lp *)
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
unfold stack_region, HP_FRAME. split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
- intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2; unfold ESTACK in *; lia.
- intros a Ha _. apply (apresent_writable SEGS). pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
apply HPR2. unfold HP_STK, ESTACK in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEI2 : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall m, (m < 33)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAE2 : env_agree 32 (Ereg regs hp_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (F10 : ew Ea 10 = Z_to_bv 64 s) by (rewrite OLD2 by (cbv; lia); exact E10).
assert (F11 : ew Ea 11 = Z_to_bv 64 n) by (rewrite OLD2 by (cbv; lia); exact E11).
assert (F12 : ew Ea 12 = Z_to_bv 64 p) by (rewrite OLD2 by (cbv; lia); exact E12).
assert (F2 : ew Ea 2 = getr regs 2) by (rewrite OLD2 by (cbv; lia); exact E2).
assert (Usp3 : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite F2; reflexivity).
assert (SHOK2 : sh_ok SEGS Bx hp_SH Ea (mrestrict (w_H W) mem2)) by (unfold sh_ok, hp_SH; constructor).
prreg HS (10%bv : bv 5) R10b.
assert (F37 : ew Ea 37 = w64 lp) by (rewrite <- R10b; exact Hlen).
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - HP_STK <= a < spZ regs) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. rewrite (Hfr2 a Ha ltac:(unfold HP_STK, ESTACK in *; intros [HA HB]; apply Hno; split; lia)).
apply KEEP; [exact Ha | unfold HP_STK in Hno; intros [HA HB]; apply Hno; split; unfold ESTACK; lia]. }
assert (KEEPLO2 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KEEP2; [lia | intros [HA HB]; unfold HP_STK, ESTACK in HA; lia]. }
paj_run_tok RUN HS HJ2 SHOK2 Bspan. { awr_ok_tac. exact Usp3. }
psrr_branch_tok RUN BR HS SHOK2 Bspan.
-
(* n >= lp: compare the two with bcmp *)
assert (Hge : lp <= n).
{ rewrite branch_geu_U, (U_atom Ea 11 n F11), (U_atom Ea 37 lp ltac:(rewrite F37; reflexivity)) in Hc by lia.
apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc. exact Hc. }
destruct (HCMP Hge) as (HVs & HOFFs & HMRs & HRAs & HHVs & HRAp & HHVp).
paj_run_tok RUN HS HJ2 SHOK2 Bspan. { awr_ok_tac. exact Usp3. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - HP_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
assert (HQ1 : aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) (ms_mem ms0) a).
{ lazymatch type of HFr1 with frame_of ?Ev ?rs _ _ =>
apply (aview_kept_out Ev rs (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha) end.
intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp3 in Hr.
apply Hno. unfold HP_STK, ESTACK. split; lia. }
assert (HQ0 : aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
{ lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ =>
apply (aview_kept_out Ev rs (w_H W) mem2 (ms_mem ms0) HFr0 a Ha) end.
intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp3 in Hr.
apply Hno. unfold HP_STK, ESTACK. split; lia. }
rewrite HQ1, HQ0. apply KEEP2; assumption. }
assert (HLO : alloc_ceiling <= spZ regs - HP_STK) by lia.
assert (MRY : forall x m y, amem_range x m -> 0 <= x -> x <= y -> y <= x + m -> 0 <= y < kHighMemEnd)
by exact amem_range_in.
assert (SHOUT : forall y, 0 <= y < kHighMemEnd ->
0 <= shadow_addr y < 2 ^ 64 /\ ~ (spZ regs - HP_STK <= shadow_addr y < spZ regs))
by (intros y HY; exact (shadow_below_stack _ _ y HLO HY)).
assert (SHOUT2 : forall x m sa, 0 <= x < kHighMemEnd -> 0 <= x + m - 1 < kHighMemEnd ->
shadow_addr x / 8 * 8 <= sa < shadow_addr (x + m - 1) / 8 * 8 + 8 ->
0 <= sa < 2 ^ 64 /\ ~ (spZ regs - HP_STK <= sa < spZ regs))
by (intros x m sa H1 H2 Hsa; exact (shadow_hull_below_stack _ _ x m sa HLO H1 H2 Hsa)).
assert (Usp4 : spZ (ms_regs ms1) = spZ regs - 32).
{ unfold spZ. rewrite P2, Usp3. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA WS_bcmp) ABCMP W (ms_regs ms1) (ms_mem ms1) HP_STK (spZ regs)
([] : list (Z * Z)) ly S W mem md ([] : list (Z * Z)) ly S _ 0 s p lp (-32) (Z_to_bv 64 (BASE + 17176)) HJ2).
- rewrite P10, F10. reflexivity.
- rewrite P11, F12. reflexivity.
- rewrite P12, F37. reflexivity.
- lia.
- exact Rs0.
- lia.
- lia.
- lia.
- lia.
- reflexivity.
- lia.
- unfold HP_STK, ESTACK. lia.
- rewrite P3. rewrite OLD2 by (cbv; lia). exact (eq_trans E3 Hgp).
- rewrite P4. rewrite OLD2 by (cbv; lia). exact (eq_trans E4 Htp).
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
  + rewrite KEEP3 by (first [lia | intros [HA HB]; apply (HOFFs a ltac:(lia)); split; lia]). apply HVs. lia.
  + intros [HA HB]. apply (HOFFs a ltac:(lia)). split; unfold HP_STK, ESTACK in *; lia.
- intros a Ha. split.
  + rewrite KEEP3 by (first [lia | intros [HA HB]; apply (HOFF a ltac:(lia)); split; lia]). apply HVIS. lia.
  + intros [HA HB]. apply (HOFF a ltac:(lia)). split; unfold HP_STK, ESTACK in *; lia.
- intros a Ha [HA HB]. apply (HOFFs a ltac:(lia)). split; unfold HP_STK, ESTACK in *; lia.
- intros a Ha [HA HB]. apply (HOFF a ltac:(lia)). split; unfold HP_STK, ESTACK in *; lia.
- exact HMRs.
- unfold amem_range in HMR |- *. lia.
- intros y Hy. destruct (HRAs y Hy) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  destruct (SHOUT y (MRY s lp y HMRs Rs0 ltac:(lia) ltac:(lia))) as [SA SB].
  rewrite <- Hsv. unfold shadow_of_addr. change (SHADOW_OFF + y / 8) with (shadow_addr y).
  apply KEEP3; assumption.
- intros Hpos sa Hsa.
  destruct (SHOUT2 s lp sa (MRY s lp s HMRs Rs0 ltac:(lia) ltac:(lia))
  (MRY s lp (s + lp - 1) HMRs Rs0 ltac:(lia) ltac:(lia)) Hsa) as [SA SB].
  rewrite KEEP3 by assumption. apply (HHVs Hpos). exact Hsa.
- intros y Hy. destruct (HRAp y Hy) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  destruct (SHOUT y (MRY p (lp + 1) y HMR ltac:(lia) ltac:(lia) ltac:(lia))) as [SA SB].
  rewrite <- Hsv. unfold shadow_of_addr. change (SHADOW_OFF + y / 8) with (shadow_addr y).
  apply KEEP3; assumption.
- intros Hpos sa Hsa.
  destruct (SHOUT2 p lp sa (MRY p (lp + 1) p HMR ltac:(lia) ltac:(lia) ltac:(lia))
  (MRY p (lp + 1) (p + lp - 1) HMR ltac:(lia) ltac:(lia) ltac:(lia)) Hsa) as [SA SB].
  rewrite KEEP3 by assumption. apply (HHVp Hpos). exact Hsa. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
jafter_call_keep_pi HS 49%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp3.
- intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK in *; lia.
- intros a Ha _. apply (apresent_writable SEGS).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR3 & _).
apply HPR3. unfold HP_STK, ESTACK in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 49 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIz : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLDz : forall m, (m < 49)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEz : env_agree 32 (Ereg regs hp_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HEb.
assert (G2 : ew Eb 2 = getr regs 2) by (rewrite OLDz by (cbv; lia); exact F2).
assert (Usp5 : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite G2; reflexivity).
assert (SHOK3 : sh_ok SEGS Bx hp_SH Eb (mrestrict (w_H W) mem3)) by (unfold sh_ok, hp_SH; constructor).
prreg HS (10%bv : bv 5) R10z.
paj_run_tok RUN HS HJ3 SHOK3 Bspan. { awr_ok_tac. exact Usp5. }
prreg HS (10%bv : bv 5) R10d. prreg HS (1%bv : bv 5) R1d.
assert (Hval : getr (ms_regs ms2) 10 = if bv_ltu v (Z_to_bv 64 1) then Z_to_bv 64 1 else Z_to_bv 64 0).
{ rewrite R10d, <- R10z, Hv. cbn [alu64 alu]. reflexivity. }
assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - HP_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
assert (Qf2 : aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem3 a).
{ lazymatch type of HFr2 with frame_of ?Ev ?rs _ _ =>
apply (aview_kept_out Ev rs (w_H W) mem3 (ms_mem ms2) HFr2 a Ha) end.
intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp5 in Hr.
apply Hno. unfold HP_STK, ESTACK. split; lia. }
assert (Qf3 : aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) (ms_mem ms1) a).
{ apply Hfr3; [exact Ha | unfold HP_STK, ESTACK in Hno; intros [HA HB]; apply Hno; split; lia]. }
rewrite Qf2, Qf3. apply KEEP3; assumption. }
assert (SAMEs : forall i, 0 <= i < lp -> aview SEGS (w_H W) (ms_mem ms1) (s + i) = aview SEGS (w_H W) mem (s + i)).
{ intros i Hi. apply KEEP3; [lia | apply (HOFFs (s + i)); lia]. }
assert (SAMEp : forall i, 0 <= i < lp -> aview SEGS (w_H W) (ms_mem ms1) (p + i) = aview SEGS (w_H W) mem (p + i)).
{ intros i Hi. apply KEEP3; [lia | apply (HOFF (p + i)); lia]. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat3. unfold hp_post.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1d; rewrite OLDz by (cbv; lia); rewrite OLD2 by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ3.
+ eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs hp_extra HS); [exact HAEz | vm_compute; reflexivity].
+ intros a Ha. cbn [ms_mem]. pres_chain.
+ intros a Ha Hno. cbn [ms_mem]. apply KEEP4; assumption.
+ cbn [ms_regs]. rewrite Hval. unfold bv_ltu. rewrite (unsigned_lit_small 1) by lia.
destruct (Z.eq_dec (bv_unsigned v) 0) as [Hv0 | Hv0].
* assert (Hvz : v = w64 0) by (apply bv_eq; rewrite Hv0; reflexivity).
left. split; [exact Hge|]. split.
-- intros i Hi. rewrite <- (SAMEs i Hi), <- (SAMEp i Hi). exact (proj1 Hcmp Hvz i Hi).
-- rewrite Hv0. reflexivity.
* right. split.
-- intros _ Hpre. apply Hv0.
assert (Hvz : v = w64 0).
{ apply (proj2 Hcmp). intros i Hi. rewrite (SAMEs i Hi), (SAMEp i Hi). exact (Hpre i Hi). }
rewrite Hvz. reflexivity.
-- pose proof (bv_unsigned_in_range 64 v) as RV. change (bv_modulus 64) with (2 ^ 64) in RV.
destruct (Z.ltb_spec (bv_unsigned v) 1); [lia | reflexivity].
-
(* n < lp: the prefix cannot fit, so has_prefix returns 0 *)
assert (Hlt : n < lp).
{ rewrite branch_geu_U, (U_atom Ea 11 n F11), (U_atom Ea 37 lp ltac:(rewrite F37; reflexivity)) in Hc by lia.
apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc. exact Hc. }
paj_run_tok RUN HS HJ2 SHOK2 Bspan. { awr_ok_tac. exact Usp3. }
prreg HS (10%bv : bv 5) R10c. prreg HS (1%bv : bv 5) R1c.
assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - HP_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
assert (Qg1 : aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) (ms_mem ms0) a).
{ lazymatch type of HFr1 with frame_of ?Ev ?rs _ _ =>
apply (aview_kept_out Ev rs (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha) end.
intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp3 in Hr.
apply Hno. unfold HP_STK, ESTACK. split; lia. }
assert (Qg0 : aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
{ lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ =>
apply (aview_kept_out Ev rs (w_H W) mem2 (ms_mem ms0) HFr0 a Ha) end.
intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp3 in Hr.
apply Hno. unfold HP_STK, ESTACK. split; lia. }
rewrite Qg1, Qg0. apply KEEP2; assumption. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. unfold hp_post.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1c; rewrite OLD2 by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ2.
+ eapply (aregs_preserved_of_st_ok SEGS _ Ea _ _ regs hp_extra HS); [exact HAE2 | vm_compute; reflexivity].
+ intros a Ha. cbn [ms_mem]. pres_chain.
+ intros a Ha Hno. cbn [ms_mem]. apply KEEP5; assumption.
+ right. split; [intros Hle; exfalso; lia|]. cbn [ms_regs]. rewrite R10c. reflexivity.
Qed.
End c.
End b.
End a.
