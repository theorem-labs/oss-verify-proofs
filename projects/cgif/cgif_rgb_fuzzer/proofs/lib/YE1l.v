(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YE1p YE09 YE1s YE1r YE1w YE08 YF8r YE04 YE0v YE1q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Notation tbl13 := tbl_x213 (only parsing).
Notation tbl13_ok := tbl_x213_ok (only parsing).
Definition ss_x1 {imgk : img} : sstate := mkSS X1_PC sr_atoms [cellr (0x13c060 + D_10c0) 1 (SLit 0) false] None (mkFacts [] [] []).
Definition x1_st {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tbl13 FUEL ss_x1)))).
Lemma x1_run {imgk : img} : sym_runN tfxsegs tbl13 FUEL ss_x1 = (x1_st, RS_stopped (SR_jalr (SOff 1 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition ss_x3 {imgk : img} : sstate := mkSS X3_PC sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [];
cellr (0xa6b50 + D_10c0) 1 (SOff 32 0) true;
YQ0b.mkRegion None (0xa2130 + D_10f0) (0xa2140 + D_10f0) (0xa2130 + D_10f0) (0xa2130 + D_10f0) [YQ0b.mkChunk (0xa2130 + D_10f0) (CVal 8 (SLit (0x916e4 + D_104c))); YQ0b.mkChunk (0xa2138 + D_10f0) (CVal 8 (SLit 0))];
cellr (0xa3e80 + D_10f0) 8 (SOff 33 0) false ] None (mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] []).
Definition x3_a : sv := SAlu ALU_AND (SExt false 8 (SOff 32 0)) (SLit 1).
Definition x3_st1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tbl13 FUEL ss_x3)))).
Definition x3_st2t {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tbl13 FUEL (YQ09.add_cond x3_st1 (mkAC BC_EQ x3_a (SLit 0))))))).
Definition x3_st2f {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tbl13 FUEL (YQ09.add_cond x3_st1 (mkAC BC_NE x3_a (SLit 0))))))).
Lemma x3_run1 {imgk : img} : sym_runN tfxsegs tbl13 FUEL ss_x3 = (x3_st1, RS_stopped (SR_branch BC_EQ x3_a (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma x3_run2t {imgk : img} : sym_runN tfxsegs tbl13 FUEL (YQ09.add_cond x3_st1 (mkAC BC_EQ x3_a (SLit 0))) = (x3_st2t, RS_stopped (SR_jalr (SOff 1 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma x3_run2f {imgk : img} : sym_runN tfxsegs tbl13 FUEL (YQ09.add_cond x3_st1 (mkAC BC_NE x3_a (SLit 0))) = (x3_st2f, RS_stopped (SR_jalr (SOff 1 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma x_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) ->
sym_runN tfxsegs tbl13 FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tbl13 tbl13_ok Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|].
split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Lemma img_aview_some {imgk : img} : forall (H : word -> bool) (m : word -> option byte) a,
img_byte_ok tfxsegs a = true -> exists v, aview tfxsegs H m a = Some v /\ 0 <= v < 256.
Proof.
intros H m a Hi. unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)) as [b|].
- exists (bv_unsigned b). split; [img_refl|]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. img_lia.
- unfold img_byte_ok, img_byte in Hi. destruct (seg_rom tfxsegs (Z_to_bv 64 a)) as [b|]; [|img_try (discriminate)].
exists (bv_unsigned b). split; [img_refl|]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. img_lia.
Qed.
Lemma val_mem1_of_aview {imgk : img} : forall (H : word -> bool) (m : word -> option byte) a v,
aview tfxsegs H m a = Some v -> val_mem tfxsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by img_lia. rewrite Z.add_0_r.
destruct (YE0v.aview_byte_ex H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal. img_apply bv_eq.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (img_try (cbn; img_lia)). cbn [Nat.mul Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
rewrite unsigned_lit8_small by img_lia. img_refl.
Qed.
Lemma rdword_img_some {imgk : img} : forall (H : word -> bool) (m : word -> option byte) a,
zallb (img_byte_ok tfxsegs) a 8%nat = true -> exists v, rdword (aview tfxsegs H m) a = Some v /\ 0 <= v < 2 ^ 64.
Proof.
intros H m a Hz.
assert (B : forall k, 0 <= k < 8 -> exists v, aview tfxsegs H m (a + k) = Some v /\ 0 <= v < 256).
{ intros k Hk. img_apply img_aview_some. img_exact (zallb_sound _ _ _ (a + k) Hz ltac:(img_lia)). }
destruct (B 0 ltac:(img_lia)) as (v0 & E0 & R0). destruct (B 1 ltac:(img_lia)) as (v1 & E1 & R1).
destruct (B 2 ltac:(img_lia)) as (v2 & E2 & R2). destruct (B 3 ltac:(img_lia)) as (v3 & E3 & R3).
destruct (B 4 ltac:(img_lia)) as (v4 & E4 & R4). destruct (B 5 ltac:(img_lia)) as (v5 & E5 & R5).
destruct (B 6 ltac:(img_lia)) as (v6 & E6 & R6). destruct (B 7 ltac:(img_lia)) as (v7 & E7 & R7).
rewrite Z.add_0_r in E0. unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. split; [img_refl|]. img_lia.
Qed.
Lemma no_window_false {imgk : img} : forall E a, in_wrange E (ss_mem ss_x1) a -> False.
Proof.
intros E a Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
cbn in Ht. destruct Ht as [Hq|[]]. injection Hq as <- <- <-. cbn [base_val] in Hr. img_lia.
Qed.
Lemma x3_windows {imgk : img} : forall E (rs : smem) a, windows rs = windows (ss_mem ss_x3) -> in_wrange E rs a ->
(bv_unsigned (ew E 2) - 16 <= a < bv_unsigned (ew E 2)) \/ a = (0xa6b50 + D_10c0).
Proof.
intros E rs a Hw Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr). rewrite Hw in Ht.
cbn in Ht. destruct Ht as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as <- <- <-; cbn [base_val] in Hr; img_lia.
Qed.
Lemma zi_14b320 {imgk : img} : zallb (img_byte_ok tfxsegs) (0xa3e80 + D_10f0) 8%nat = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma zi_14ea50 {imgk : img} : img_byte_ok tfxsegs (0xa6b50 + D_10c0) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma wz_14ea50 {imgk : img} : wseg_ok tfxsegs (Z_to_bv 64 (0xa6b50 + D_10c0)) (Z.to_nat 1) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Section S. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis COV0 : forall ly S (W : world tfxsegs) mem md, AR tfxsegs B ly S W mem md -> aview tfxsegs (w_H W) mem (0x13c060 + D_10c0) = Some 0.
Hypothesis COMPLETED_free : forall ly S (W : world tfxsegs) mem md, AR tfxsegs B ly S W mem md -> ~ aowned B ly S (0xa6b50 + D_10c0).
Theorem x1_realizes : xret_realizes tfxsegs B X1_PC XW1 XTRUE.
Proof.
intros ly S W regs mem md HPRE _. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx.
unfold cfg_at. img_change (w64 X1_PC) with (Z_to_bv 64 X1_PC).
set (E := Ereg regs (@nil word)).
assert (HS0 : st_ok tfxsegs E ss_x1 (restrict (w_H W) (mkst regs (Z_to_bv 64 X1_PC) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x1. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 1 _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_apply val_mem1_of_aview. img_exact (COV0 ly S W mem md HAR).
- img_apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [img_try (cbn; img_exact I) | img_try (split; img_exact I)]. }
eapply SRr_bind; [img_try (img_apply (x_phase W E ss_x1 x1_st _ _ md HS0 x1_run))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
eapply (SRr_ret_at tfxsegs tbl13 tbl13_ok Hwx W E); [img_try (img_exact HS1) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb.
assert (MEQ : forall x, ms_mem ms1 x = mem x) by (img_try (intros x; img_apply HF1; intros Hin; img_exact (no_window_false E _ Hin))).
assert (MEQr : forall x, mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x) by (img_try (intros x; img_apply HFr1; intros Hin; img_exact (no_window_false E _ Hin))).
assert (AV : forall a, aview tfxsegs (w_H W) (ms_mem ms1) a = aview tfxsegs (w_H W) mem a) by (img_try (intros a; img_apply aview_eq_of; img_apply MEQr)).
rreg HS1 (1%bv : bv 5) Q1. replace (ew E 1) with (getr regs 1) in Q1 by (img_try (symmetry; img_exact (ew_Ereg_nat regs [] 1 1%bv eq_refl))).
replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
split; [img_refl|]. exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [img_refl|].
split; [|img_try (split; [|split; [|split]])].
- img_apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR); [img_try (intros a _ _; img_apply AV) | img_try (intros a Hv; rewrite AV; img_exact Hv) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_exact (YE0v.hs_kept_eq _ _ _ MEQ))].
- img_exact (aregs_preserved_of_st_ok _ E _ _ regs [] HS1 ltac:(img_try (split; [img_try (intros i Hi; img_refl) | img_refl])) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
- img_apply with_vm_backing_same.
- intros a _ _ _ _. img_apply AV.
- intros a _ _ [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite MEQ. img_exact Hb.
Qed.
Theorem x3_realizes : xret_realizes tfxsegs B X3_PC XW3 X3PRE.
Proof.
intros ly S W regs mem md HPRE [HG1 HG2]. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold cfg_at. img_change (w64 X3_PC) with (Z_to_bv 64 X3_PC).
set (sp0 := spZ regs) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by img_lia.
destruct (img_aview_some (w_H W) mem (0xa6b50 + D_10c0) zi_14ea50) as (v0 & Hv0 & Rv0).
destruct (rdword_img_some (w_H W) mem (0xa3e80 + D_10f0) zi_14b320) as (v1 & Hv1 & Rv1).
set (E := Ereg regs [Z_to_bv 64 v0; Z_to_bv 64 v1]).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); img_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 v0) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (E33 : ew E 33 = Z_to_bv 64 v1) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 1))).
assert (HS0 : st_ok tfxsegs E ss_x3 (restrict (w_H W) (mkst regs (Z_to_bv 64 X3_PC) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x3. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 v0; Z_to_bv 64 v1]) with E.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 sp0 (-16)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply HpresE. img_lia.
+ unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; img_apply (wseg_writable _ (0xa6b50 + D_10c0) 1); [img_exact wz_14ea50 | img_lia | img_lia | img_lia | img_lia]) |].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 1 _ v0); [img_try (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_apply val_mem1_of_aview. img_exact Hv0.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil; (eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; assumption)]).
+ unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ v1); [img_try (cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_apply val_mem_of_rdword. img_exact Hv1.
- img_apply pairwise_disjoint_of_extents. unfold cellr, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
img_change (2 ^ 4) with 16. repeat split; img_lia. }
eapply SRr_bind; [img_try (img_apply (x_phase W E ss_x3 x3_st1 _ _ md HS0 x3_run1))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (TAIL : forall ss2 c (Hrun : sym_runN tfxsegs tbl13 FUEL (YQ09.add_cond x3_st1 (mkAC c x3_a (SLit 0))) = (ss2, RS_stopped (SR_jalr (SOff 1 0)))),
(ss2 = x3_st2t \/ ss2 = x3_st2f) ->
st_ok tfxsegs E (YQ09.add_cond x3_st1 (mkAC c x3_a (SLit 0))) (restrict (w_H W) ms1) ->
SRr tfxsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (w64 (raZ regs)) mem' (seg_rom tfxsegs)) md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ aowned B ly S a -> ~ XW3 a ->
aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ XW3 a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros ss2 c Hrun Hss2 HSc.
eapply SRr_bind; [img_try (img_apply (x_phase W E _ ss2 _ _ _ HSc Hrun))|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfxsegs tbl13 tbl13_ok Hwx W E); [img_try (img_exact HS2) | img_try (destruct Hss2 as [-> | ->]; img_refl) | img_try (destruct Hss2 as [-> | ->]; (try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb.
assert (W1 : forall x : word, ~ ((sp0 - 16 <= bv_unsigned x < sp0) \/ bv_unsigned x = (0xa6b50 + D_10c0)) -> ms_mem ms2 x = mem x).
{ intros x Hx. assert (WEQ : windows (ss_mem (YQ09.add_cond x3_st1 (mkAC c x3_a (SLit 0)))) = windows (ss_mem ss_x3)) by (img_try ((try img_inst; img_case; vm_compute); img_refl)).
rewrite (HF2 x) by (img_try (intros Hin; img_apply Hx; destruct (x3_windows E _ _ WEQ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [img_try (left; img_exact Hw) | img_try (right; img_exact Hw)])).
img_apply HF1. intros Hin. img_apply Hx. destruct (x3_windows E _ _ eq_refl Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [img_try (left; img_exact Hw) | img_try (right; img_exact Hw)]. }
assert (W1r : forall x : word, ~ ((sp0 - 16 <= bv_unsigned x < sp0) \/ bv_unsigned x = (0xa6b50 + D_10c0)) -> mrestrict (w_H W) (ms_mem ms2) x = mrestrict (w_H W) mem x).
{ intros x Hx. assert (WEQ : windows (ss_mem (YQ09.add_cond x3_st1 (mkAC c x3_a (SLit 0)))) = windows (ss_mem ss_x3)) by (img_try ((try img_inst; img_case; vm_compute); img_refl)).
rewrite (HFr2 x) by (img_try (intros Hin; img_apply Hx; destruct (x3_windows E _ _ WEQ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [img_try (left; img_exact Hw) | img_try (right; img_exact Hw)])).
img_apply HFr1. intros Hin. img_apply Hx. destruct (x3_windows E _ _ eq_refl Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [img_try (left; img_exact Hw) | img_try (right; img_exact Hw)]. }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 16 <= a < sp0) -> a <> (0xa6b50 + D_10c0) -> aview tfxsegs (w_H W) (ms_mem ms2) a = aview tfxsegs (w_H W) mem a).
{ intros a Hr H1 H2. img_apply aview_eq_of. img_apply W1r. rewrite unsigned_lit_small by img_lia. img_lia. }
assert (PRS : forall a, sp0 - 16 <= a < sp0 -> apresent (w_H W) (ms_mem ms2) a).
{ intros a Ha. img_apply (apresent_of_writable (w_H W) (ms_mem ms2) a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS2 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
assert (Hr0 : region_ok tfxsegs E (mrestrict (w_H W) (ms_mem ms2)) (YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 (YQ0b.r_chunks (hd (YQ0b.mkRegion None 0 0 0 0 []) (ss_mem ss2))))).
{ destruct Hss2 as [-> | ->]; img_exact (Forall_inv Hrs). }
destruct Hr0 as (_ & _ & Hw & _). cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw. rewrite E2 in Hw.
replace a with (sp0 + (a - sp0)) by img_lia. img_apply Hw. img_lia. }
assert (Q1' : getr (ms_regs ms2) 1 = getr regs 1).
{ destruct Hss2 as [-> | ->]; (rreg HS2 (1%bv : bv 5) Q1; rewrite Q1; symmetry; img_exact (ew_Ereg_nat regs [Z_to_bv 64 v0; Z_to_bv 64 v1] 1 1%bv eq_refl)). }
replace (v_jalr (getr (ms_regs ms2) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite Q1'; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
split; [img_refl|]. exists (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [img_refl|].
split; [|img_try (split; [|split; [|split]])].
- img_apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms2) _ HAR).
+ intros a Hr Hown. img_apply AV; [img_try (img_exact Hr) | img_try (intros Hs; img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_lia) Hown)) | img_try (intros ->; img_exact (COMPLETED_free ly S W mem md HAR Hown))].
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfxsegs (w_H W) mem a <> None -> aview tfxsegs (w_H W) (ms_mem ms2) a <> None).
{ intros a Hr Hv. destruct (Z.eq_dec a (0xa6b50 + D_10c0)) as [->|Hne].
{ destruct (img_aview_some (w_H W) (ms_mem ms2) (0xa6b50 + D_10c0) zi_14ea50) as (v & Hv' & _). rewrite Hv'. discriminate. }
destruct (Z_lt_le_dec a (sp0 - 16)) as [L1|L1]; [img_try (rewrite AV by img_lia; img_exact Hv)|].
destruct (Z_lt_le_dec a sp0) as [L2|L2]; [img_try (img_apply aview_some_of_apresent; img_apply PRS; img_lia)|].
rewrite AV by img_lia. img_exact Hv. }
intros a Hv. rewrite (aview_mod _ (ms_mem ms2) a). img_apply PV; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (rewrite <- aview_mod; img_exact Hv)].
+ img_apply MF. + img_apply MF. + img_apply MF.
+
intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.
assert (CASE : (sp0 - 16 <= a < sp0) \/ ~ (sp0 - 16 <= a < sp0)) by img_lia.
destruct CASE as [Hin|Hout]; [img_try (exfalso; destruct (HpresE a ltac:(unfold ESTACK; img_lia)) as [Hf _]; rewrite Hf in Hh; discriminate Hh)|].
rewrite W1; [img_refl|]. rewrite unsigned_lit_small by (img_try (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)).
intros [Hx|Hx]; [img_try (img_exact (Hout Hx)) | img_try (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)].
- destruct Hss2 as [-> | ->];
img_exact (aregs_preserved_of_st_ok _ E _ _ regs [Z_to_bv 64 v0; Z_to_bv 64 v1] HS2 ltac:(img_try (split; [img_try (intros i Hi; img_refl) | img_refl])) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
- img_apply with_vm_backing_same.
- intros a Hr Hs Ho Hx. img_apply AV; [img_try (img_exact Hr) | img_try (unfold sp0 in *; img_lia) | img_try (intros ->; img_apply Hx; img_refl)].
- intros a Hr Hx Hp. unfold XW3 in Hx.
destruct (Z_lt_le_dec a (sp0 - 16)) as [L1|L1]; [| img_try (destruct (Z_lt_le_dec a sp0) as [L2|L2]; [img_apply PRS; img_lia|])].
all: destruct Hp as [Hh [b Hb]]; split; [img_try (img_exact Hh)|]; exists b; rewrite W1; [img_try (img_exact Hb)|]; rewrite unsigned_lit_small by img_lia; img_lia. }
destruct (branch_taken BC_EQ (sv_denot E x3_a) (sv_denot E (SLit 0))) eqn:Hbt.
- img_apply (TAIL x3_st2t BC_EQ x3_run2t (or_introl eq_refl)). img_apply st_ok_add_cond; [img_try (img_exact HS1) | img_try (img_exact Hbt)].
- img_apply (TAIL x3_st2f BC_NE x3_run2f (or_intror eq_refl)).
img_change BC_NE with (neg_bc BC_EQ). img_apply st_ok_add_cond_neg; [img_try (img_exact HS1) | img_try (img_exact Hbt)].
Qed.
End S.
End d.
