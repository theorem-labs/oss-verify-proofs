(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AE3g AE2p AE3i AE3h AE3m AE23 AF0x AE20 AE2y AE7f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation tbl13 := tbl_x213 (only parsing).
Notation tbl13_ok := tbl_x213_ok (only parsing).
Definition ss_x1 : sstate := mkSS X1_PC sr_atoms [cellr 0x137ea0 1 (SLit 0) false] None (mkFacts [] [] []).
Definition x1_st : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl13 FUEL ss_x1).
Lemma x1_run : sym_runN tfibsegs tbl13 FUEL ss_x1 = (x1_st, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition ss_x3 : sstate := mkSS X3_PC sr_atoms
[ YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [];
cellr 0xa2990 1 (SOff 32 0) true;
YP09.mkRegion None 0x9df68 0x9df78 0x9df68 0x9df68 [YP09.mkChunk 0x9df68 (CVal 8 (SLit 0x8d4e8)); YP09.mkChunk 0x9df70 (CVal 8 (SLit 0))];
cellr 0x9fca8 8 (SOff 33 0) false ] None (mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] []).
Definition x3_a : sv := SAlu ALU_AND (SExt false 8 (SOff 32 0)) (SLit 1).
Definition x3_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl13 FUEL ss_x3).
Definition x3_st2t : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl13 FUEL (YP06.add_cond x3_st1 (mkAC BC_EQ x3_a (SLit 0)))).
Definition x3_st2f : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl13 FUEL (YP06.add_cond x3_st1 (mkAC BC_NE x3_a (SLit 0)))).
Lemma x3_run1 : sym_runN tfibsegs tbl13 FUEL ss_x3 = (x3_st1, RS_stopped (SR_branch BC_EQ x3_a (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Lemma x3_run2t : sym_runN tfibsegs tbl13 FUEL (YP06.add_cond x3_st1 (mkAC BC_EQ x3_a (SLit 0))) = (x3_st2t, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Lemma x3_run2f : sym_runN tfibsegs tbl13 FUEL (YP06.add_cond x3_st1 (mkAC BC_NE x3_a (SLit 0))) = (x3_st2f, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Lemma x_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl13 FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl13 tbl13_ok Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma img_aview_some : forall (H : word -> bool) (m : word -> option byte) a,
img_byte_ok tfibsegs a = true -> exists v, aview tfibsegs H m a = Some v /\ 0 <= v < 256.
Proof.
intros H m a Hi. unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)) as [b|].
- exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
- unfold img_byte_ok, img_byte in Hi. destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; [|discriminate].
exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Lemma val_mem1_of_aview : forall (H : word -> bool) (m : word -> option byte) a v,
aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
destruct (AE2y.aview_byte_ex H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal. apply bv_eq.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn; lia). cbn [Nat.mul Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
rewrite unsigned_lit8_small by lia. reflexivity.
Qed.
Lemma rdword_img_some : forall (H : word -> bool) (m : word -> option byte) a,
zallb (img_byte_ok tfibsegs) a 8%nat = true -> exists v, rdword (aview tfibsegs H m) a = Some v /\ 0 <= v < 2 ^ 64.
Proof.
intros H m a Hz.
assert (B : forall k, 0 <= k < 8 -> exists v, aview tfibsegs H m (a + k) = Some v /\ 0 <= v < 256).
{ intros k Hk. apply img_aview_some. exact (zallb_sound _ _ _ (a + k) Hz ltac:(lia)). }
destruct (B 0 ltac:(lia)) as (v0 & E0 & R0). destruct (B 1 ltac:(lia)) as (v1 & E1 & R1).
destruct (B 2 ltac:(lia)) as (v2 & E2 & R2). destruct (B 3 ltac:(lia)) as (v3 & E3 & R3).
destruct (B 4 ltac:(lia)) as (v4 & E4 & R4). destruct (B 5 ltac:(lia)) as (v5 & E5 & R5).
destruct (B 6 ltac:(lia)) as (v6 & E6 & R6). destruct (B 7 ltac:(lia)) as (v7 & E7 & R7).
rewrite Z.add_0_r in E0. unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. split; [reflexivity|]. lia.
Qed.
Lemma no_window_false : forall E a, in_wrange E (ss_mem ss_x1) a -> False.
Proof.
intros E a Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
cbn in Ht. destruct Ht as [Hq|[]]. injection Hq as <- <- <-. cbn [base_val] in Hr. lia.
Qed.
Lemma x3_windows : forall E (rs : smem) a, windows rs = windows (ss_mem ss_x3) -> in_wrange E rs a ->
(bv_unsigned (ew E 2) - 16 <= a < bv_unsigned (ew E 2)) \/ a = 0xa2990.
Proof.
intros E rs a Hw Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr). rewrite Hw in Ht.
cbn in Ht. destruct Ht as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as <- <- <-; cbn [base_val] in Hr; lia.
Qed.
Lemma zi_14b320 : zallb (img_byte_ok tfibsegs) 0x9fca8 8%nat = true. Proof. vm_compute. reflexivity. Qed.
Lemma zi_14ea50 : img_byte_ok tfibsegs 0xa2990 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wz_14ea50 : wseg_ok tfibsegs (Z_to_bv 64 0xa2990) (Z.to_nat 1) = true. Proof. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis COV0 : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md -> aview tfibsegs (w_H W) mem 0x137ea0 = Some 0.
Hypothesis COMPLETED_free : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md -> ~ aowned B ly S 0xa2990.
Theorem x1_realizes : xret_realizes tfibsegs B X1_PC XW1 XTRUE.
Proof.
intros ly S W regs mem md HPRE _. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx.
unfold cfg_at. change (w64 X1_PC) with (Z_to_bv 64 X1_PC).
set (E := Ereg regs (@nil word)).
assert (HS0 : st_ok tfibsegs E ss_x1 (restrict (w_H W) (mkst regs (Z_to_bv 64 X1_PC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x1. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 1 _ 0); [reflexivity | zside | zside |].
rewrite Z.add_0_l. apply val_mem1_of_aview. exact (COV0 ly S W mem md HAR).
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [cbn; exact I | split; exact I]. }
eapply SRr_bind; [apply (x_phase W E ss_x1 x1_st _ _ md HS0 x1_run)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
eapply (SRr_ret_at tfibsegs tbl13 tbl13_ok Hwx W E); [exact HS1 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ : forall x, ms_mem ms1 x = mem x) by (intros x; apply HF1; intros Hin; exact (no_window_false E _ Hin)).
assert (MEQr : forall x, mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x) by (intros x; apply HFr1; intros Hin; exact (no_window_false E _ Hin)).
assert (AV : forall a, aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a) by (intros a; apply aview_eq_of; apply MEQr).
rreg HS1 (1%bv : bv 5) Q1. replace (ew E 1) with (getr regs 1) in Q1 by (symmetry; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
split; [|split; [|split; [|split]]].
- apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR); [intros a _ _; apply AV | intros a Hv; rewrite AV; exact Hv | apply MF | apply MF | apply MF | exact (AE2y.hs_kept_eq _ _ _ MEQ)].
- exact (aregs_preserved_of_st_ok _ E _ _ regs [] HS1 ltac:(split; [intros i Hi; reflexivity | reflexivity]) ltac:(vm_compute; reflexivity)).
- apply with_vm_backing_same.
- intros a _ _ _ _. apply AV.
- intros a _ _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite MEQ. exact Hb.
Qed.
Theorem x3_realizes : xret_realizes tfibsegs B X3_PC XW3 X3PRE.
Proof.
intros ly S W regs mem md HPRE [HG1 HG2]. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold cfg_at. change (w64 X3_PC) with (Z_to_bv 64 X3_PC).
set (sp0 := spZ regs) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
destruct (img_aview_some (w_H W) mem 0xa2990 zi_14ea50) as (v0 & Hv0 & Rv0).
destruct (rdword_img_some (w_H W) mem 0x9fca8 zi_14b320) as (v1 & Hv1 & Rv1).
set (E := Ereg regs [Z_to_bv 64 v0; Z_to_bv 64 v1]).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 v0) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 v1) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (HS0 : st_ok tfibsegs E ss_x3 (restrict (w_H W) (mkst regs (Z_to_bv 64 X3_PC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x3. apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 v0; Z_to_bv 64 v1]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 sp0 (-16)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply HpresE. lia.
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa2990 1); [exact wz_14ea50 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 1 _ v0); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_l. apply val_mem1_of_aview. exact Hv0.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil; (eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; assumption]).
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ v1); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_l. apply val_mem_of_rdword. exact Hv1.
- apply pairwise_disjoint_of_extents. unfold cellr, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
change (2 ^ 4) with 16. repeat split; lia. }
eapply SRr_bind; [apply (x_phase W E ss_x3 x3_st1 _ _ md HS0 x3_run1)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (TAIL : forall ss2 c (Hrun : sym_runN tfibsegs tbl13 FUEL (YP06.add_cond x3_st1 (mkAC c x3_a (SLit 0))) = (ss2, RS_stopped (SR_jalr (SOff 1 0)))),
(ss2 = x3_st2t \/ ss2 = x3_st2f) ->
st_ok tfibsegs E (YP06.add_cond x3_st1 (mkAC c x3_a (SLit 0))) (restrict (w_H W) ms1) ->
SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (w64 (raZ regs)) mem' (seg_rom tfibsegs)) md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ aowned B ly S a -> ~ XW3 a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ XW3 a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros ss2 c Hrun Hss2 HSc.
eapply SRr_bind; [apply (x_phase W E _ ss2 _ _ _ HSc Hrun)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl13 tbl13_ok Hwx W E); [exact HS2 | destruct Hss2 as [-> | ->]; reflexivity | destruct Hss2 as [-> | ->]; vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (W1 : forall x : word, ~ ((sp0 - 16 <= bv_unsigned x < sp0) \/ bv_unsigned x = 0xa2990) -> ms_mem ms2 x = mem x).
{ intros x Hx. assert (WEQ : windows (ss_mem (YP06.add_cond x3_st1 (mkAC c x3_a (SLit 0)))) = windows (ss_mem ss_x3)) by (vm_compute; reflexivity).
rewrite (HF2 x) by (intros Hin; apply Hx; destruct (x3_windows E _ _ WEQ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]).
apply HF1. intros Hin. apply Hx. destruct (x3_windows E _ _ eq_refl Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]. }
assert (W1r : forall x : word, ~ ((sp0 - 16 <= bv_unsigned x < sp0) \/ bv_unsigned x = 0xa2990) -> mrestrict (w_H W) (ms_mem ms2) x = mrestrict (w_H W) mem x).
{ intros x Hx. assert (WEQ : windows (ss_mem (YP06.add_cond x3_st1 (mkAC c x3_a (SLit 0)))) = windows (ss_mem ss_x3)) by (vm_compute; reflexivity).
rewrite (HFr2 x) by (intros Hin; apply Hx; destruct (x3_windows E _ _ WEQ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]).
apply HFr1. intros Hin. apply Hx. destruct (x3_windows E _ _ eq_refl Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]. }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 16 <= a < sp0) -> a <> 0xa2990 -> aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) mem a).
{ intros a Hr H1 H2. apply aview_eq_of. apply W1r. rewrite unsigned_lit_small by lia. lia. }
assert (PRS : forall a, sp0 - 16 <= a < sp0 -> apresent (w_H W) (ms_mem ms2) a).
{ intros a Ha. apply (apresent_of_writable (w_H W) (ms_mem ms2) a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS2 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
assert (Hr0 : region_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms2)) (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 (YP09.r_chunks (hd (YP09.mkRegion None 0 0 0 0 []) (ss_mem ss2))))).
{ destruct Hss2 as [-> | ->]; exact (Forall_inv Hrs). }
destruct Hr0 as (_ & _ & Hw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite E2 in Hw.
replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia. }
assert (Q1' : getr (ms_regs ms2) 1 = getr regs 1).
{ destruct Hss2 as [-> | ->]; (rreg HS2 (1%bv : bv 5) Q1; rewrite Q1; symmetry; exact (ew_Ereg_nat regs [Z_to_bv 64 v0; Z_to_bv 64 v1] 1 1%bv eq_refl)). }
replace (v_jalr (getr (ms_regs ms2) 1) 0) with (w64 (raZ regs)) by (rewrite Q1'; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
split; [|split; [|split; [|split]]].
- apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms2) _ HAR).
+ intros a Hr Hown. apply AV; [exact Hr | intros Hs; exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown) | intros ->; exact (COMPLETED_free ly S W mem md HAR Hown)].
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) (ms_mem ms2) a <> None).
{ intros a Hr Hv. destruct (Z.eq_dec a 0xa2990) as [->|Hne].
{ destruct (img_aview_some (w_H W) (ms_mem ms2) 0xa2990 zi_14ea50) as (v & Hv' & _). rewrite Hv'. discriminate. }
destruct (Z_lt_le_dec a (sp0 - 16)) as [L1|L1]; [rewrite AV by lia; exact Hv|].
destruct (Z_lt_le_dec a sp0) as [L2|L2]; [apply aview_some_of_apresent; apply PRS; lia|].
rewrite AV by lia. exact Hv. }
intros a Hv. rewrite (aview_mod _ (ms_mem ms2) a). apply PV; [apply Z.mod_pos_bound; lia | rewrite <- aview_mod; exact Hv].
+ apply MF. + apply MF. + apply MF.
+
intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.
assert (CASE : (sp0 - 16 <= a < sp0) \/ ~ (sp0 - 16 <= a < sp0)) by lia.
destruct CASE as [Hin|Hout]; [exfalso; destruct (HpresE a ltac:(unfold ESTACK; lia)) as [Hf _]; rewrite Hf in Hh; discriminate Hh|].
rewrite W1; [reflexivity|]. rewrite unsigned_lit_small by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
intros [Hx|Hx]; [exact (Hout Hx) | unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia].
- destruct Hss2 as [-> | ->];
exact (aregs_preserved_of_st_ok _ E _ _ regs [Z_to_bv 64 v0; Z_to_bv 64 v1] HS2 ltac:(split; [intros i Hi; reflexivity | reflexivity]) ltac:(vm_compute; reflexivity)).
- apply with_vm_backing_same.
- intros a Hr Hs Ho Hx. apply AV; [exact Hr | unfold sp0 in *; lia | intros ->; apply Hx; reflexivity].
- intros a Hr Hx Hp. unfold XW3 in Hx.
destruct (Z_lt_le_dec a (sp0 - 16)) as [L1|L1]; [| destruct (Z_lt_le_dec a sp0) as [L2|L2]; [apply PRS; lia|]].
all: destruct Hp as [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite W1; [exact Hb|]; rewrite unsigned_lit_small by lia; lia. }
destruct (branch_taken BC_EQ (sv_denot E x3_a) (sv_denot E (SLit 0))) eqn:Hbt.
- apply (TAIL x3_st2t BC_EQ x3_run2t (or_introl eq_refl)). apply st_ok_add_cond; [exact HS1 | exact Hbt].
- apply (TAIL x3_st2f BC_NE x3_run2f (or_intror eq_refl)).
change BC_NE with (neg_bc BC_EQ). apply st_ok_add_cond_neg; [exact HS1 | exact Hbt].
Qed.
End S.
End d.
