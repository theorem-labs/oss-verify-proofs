(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma alu_sll1w : forall i, 0 <= i <= 17 -> alu64 ALU_SLL (Z_to_bv 64 1) (Z_to_bv 64 i) = Z_to_bv 64 (2 ^ i).
Proof.
intros i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17) by lia.
destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma denot_sll1w : forall E n1 n i, ew E n1 = Z_to_bv 64 1 -> ew E n = Z_to_bv 64 i -> 0 <= i <= 17 ->
sv_denot E (SAlu ALU_SLL (SOff n1 0) (SOff n 0)) = Z_to_bv 64 (2 ^ i).
Proof.
intros E n1 n i H1 Hn Hi. cbn [sv_denot]. rewrite H1, Hn, !unsigned_lit_small, !Z.add_0_r by lia. apply alu_sll1w. exact Hi.
Qed.
Lemma addiw1_small : forall i, 0 <= i <= 17 -> sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 i)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (i + 1).
Proof.
intros i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17) by lia.
destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma denot_addiw1 : forall E n i, ew E n = Z_to_bv 64 i -> 0 <= i <= 17 ->
sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (i + 1).
Proof.
intros E n i Hn Hi. cbn [sv_denot]. rewrite Hn, !unsigned_lit_small, !Z.add_0_r by lia. apply addiw1_small. exact Hi.
Qed.
Definition FPOW_CLOB : list (bv 5) := [10; 12; 13]%bv.
Definition FPOW_KEPT : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma fpow_clob_kept : forall r : bv 5, reg_in r FPOW_CLOB = false -> r = 0%bv \/ In r FPOW_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Section L.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma fl_pow2 : forall (m : nat) (i np : Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
Z.of_nat m = 17 - i ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 np ->
0 <= i <= 17 -> 0 <= np <= 65535 -> (2 ^ i < 2 * np \/ i = 0) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x20c8)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' K,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x20d8)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 12 = Z_to_bv 64 K /\ getr regs' 10 = Z_to_bv 64 (K + 1) /\ getr regs' 13 = Z_to_bv 64 (2 ^ K) /\
i <= K <= 16 /\ np <= 2 ^ K /\ (2 ^ K < 2 * np \/ K = 0) /\
(forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall r : bv 5, reg_in r FPOW_CLOB = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros i np W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Hm HJ H10 H11 H14 Hi Hnp Hpow.
{ exfalso. assert (i = 17) by lia. subst i. change (2 ^ 17) with 131072 in Hpow. lia. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Hp2i : 0 < 2 ^ i <= 131072) by (split; [apply Z.pow_pos_nonneg; lia | change 131072 with (2 ^ 17); apply Z.pow_le_mono_r; lia]).
assert (E10 : ew (Eimg (Ereg regs [])) 10 = Z_to_bv 64 i) by (eimg_low; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (E11 : ew (Eimg (Ereg regs [])) 11 = Z_to_bv 64 1) by (eimg_low; rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H11).
assert (E14 : ew (Eimg (Ereg regs [])) 14 = Z_to_bv 64 np) by (eimg_low; rewrite (ew_Ereg_nat regs [] 14 14%bv eq_refl); exact H14).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS 0x20c8 sr_atoms [] None
(mkFacts [(10%nat, mkAF 0 17 0); (11%nat, mkAF 1 1 0); (14%nat, mkAF 0 65535 0)] [] [])) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x20c8)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
exact (rn_st_ok_any (Eimg (Ereg regs [])) (BASE + 0x20c8) sr_atoms regs [] (mkFacts [(10%nat, mkAF 0 17 0); (11%nat, mkAF 1 1 0); (14%nat, mkAF 0 65535 0)] [] []) (mrestrict (w_H W) memc)
(regs_ok_Eimg_Ereg regs []) eq_refl ltac:(apply Forall_nil) I
ltac:(split; [|split; exact I]; cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite E10, E11, E14, !unsigned_lit_small by lia; rewrite !Z.pow_0_r, !Z.mod_1_r; lia)). }
pose proof HS as HS0.
remember (Eimg (Ereg regs [])) as E eqn:HEdef. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HEdef; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]). clear HEdef.
paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1w E 11 10 i E11 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
paj_run_to_shc RUNTOP HS HJ 0x20c8; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
prreg HS (10%bv : bv 5) Qr10. prreg HS (11%bv : bv 5) Qr11. prreg HS (14%bv : bv 5) Qr14.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply SRr_mono;
[ eapply (IH (i + 1) np W (ms_regs msX) (ms_mem msX) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k ltac:(lia) HJ);
[ rewrite Qr10, E10, unsigned_lit_small by lia; reflexivity
| rewrite Qr11, E11; reflexivity
| rewrite Qr14, E14; reflexivity
| lia | lia | left; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia ]
| ] end.
cbv beta. intros W' c' _ (-> & regs'' & mem'' & md'' & K & -> & HJ'' & HK12 & HK10 & HK13 & HK1 & HK2 & HK3 & Hav & Hpr & Hrg).
split; [reflexivity|]. exists regs'', mem'', md'', K.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact HK12|]. split; [exact HK10|]. split; [exact HK13|].
split; [lia|]. split; [exact HK2|]. split; [exact HK3|].
split; [intros a; rewrite (Hav a); cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; apply Hpr; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. rewrite (Hrg r Hr). cbn [ms_regs].
destruct (fpow_clob_kept r Hr) as [-> | Hin].
+ rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok SEGS E _ _ regs [] FPOW_KEPT HS HAE ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1w E 11 10 i E11 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ 0x20d8; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
prreg HS (10%bv : bv 5) Qr10. prreg HS (12%bv : bv 5) Qr12. prreg HS (13%bv : bv 5) Qr13.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkst (ms_regs ?msX) _ _ _] => exists (ms_regs msX), (ms_mem msX) end. eexists. exists i.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite Qr12, E10; reflexivity|].
split; [rewrite Qr10, E10, unsigned_lit_small by lia; reflexivity|].
split; [rewrite Qr13, E11, E10; apply alu_sll1w; exact Hi|].
assert (Hi16 : i <= 16) by (destruct (Z_le_gt_dec i 16); [lia|]; assert (i = 17) by lia; subst i; change (2 ^ 17) with 131072 in Hpow; lia).
split; [lia|]. split; [lia|]. split; [exact Hpow|].
split; [intros a; cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. cbn [ms_regs].
destruct (fpow_clob_kept r Hr) as [-> | Hin].
+ rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok SEGS E _ _ regs [] FPOW_KEPT HS HAE ltac:(vm_compute; reflexivity) r Hin).
Qed.
End L.
End c.
End b.
