(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition POW_CLOB_RA : list (bv 5) := [10; 13]%bv.
Definition POW_KEPT_RA : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pow_clob_kept_RA : forall r : bv 5, reg_in r POW_CLOB_RA = false -> r = 0%bv \/ In r POW_KEPT_RA.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Definition POW_CLOB_D : list (bv 5) := [10; 15]%bv.
Definition POW_KEPT_D : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pow_clob_kept_D : forall r : bv 5, reg_in r POW_CLOB_D = false -> r = 0%bv \/ In r POW_KEPT_D.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Section L.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Lemma ra_pow2a : forall (m : nat) (i sg : Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
Z.of_nat m = 9 - i ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 64 -> getr regs 14 = Z_to_bv 64 sg ->
0 <= i <= 9 -> 1 <= sg <= 256 -> 2 ^ i < 2 * sg ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 0x897c0) memc (seg_rom trbsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' K,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x897d4) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 10 = Z_to_bv 64 K /\ getr regs' 13 = Z_to_bv 64 (2 ^ K) /\
i <= K <= 8 /\ sg <= 2 ^ K /\ 2 ^ K < 2 * sg /\
(forall a, aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall r : bv 5, reg_in r POW_CLOB_RA = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros i sg W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Hm HJ H10 H11 H12 H14 Hi Hsg Hpow.
{ exfalso. assert (i = 9) by lia. subst i. change (2 ^ 9) with 512 in Hpow. lia. }
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
assert (Hp2i : 0 < 2 ^ i <= 512) by (split; [apply Z.pow_pos_nonneg; lia | change 512 with (2 ^ 9); apply Z.pow_le_mono_r; lia]).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (E11 : ew (Ereg regs []) 11 = Z_to_bv 64 1) by (rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H11).
assert (E12 : ew (Ereg regs []) 12 = Z_to_bv 64 64) by (rewrite (ew_Ereg_nat regs [] 12 12%bv eq_refl); exact H12).
assert (E14 : ew (Ereg regs []) 14 = Z_to_bv 64 sg) by (rewrite (ew_Ereg_nat regs [] 14 14%bv eq_refl); exact H14).
assert (HS : st_ok trbsegs (Ereg regs []) (mkSS 0x897c0 sr_atoms [] None
(mkFacts [(10%nat, mkAF 0 9 0); (11%nat, mkAF 1 1 0); (12%nat, mkAF 64 64 0); (14%nat, mkAF 1 256 0)] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 0x897c0) memc (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx.
exact (rn_st_ok_any (Ereg regs []) 0x897c0 sr_atoms regs [] (mkFacts [(10%nat, mkAF 0 9 0); (11%nat, mkAF 1 1 0); (12%nat, mkAF 64 64 0); (14%nat, mkAF 1 256 0)] [] []) (mrestrict (w_H W) memc)
(regs_ok_Ereg regs []) eq_refl ltac:(apply Forall_nil) I
ltac:(split; [|split; exact I]; cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite E10, E11, E12, E14, !unsigned_lit_small by lia; rewrite !Z.pow_0_r, !Z.mod_1_r; lia)). }
pose proof HS as HS0.
remember (Ereg regs []) as E eqn:HEdef.
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HEdef; apply env_agree_refl). clear HEdef.
aj_run trbtbl_lib_ok HS HJ; [apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
srr_branch_with trbtbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1 E 11 10 i E11 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia.
apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc.
aj_run_to trbtbl_lib_ok HS HJ 0x897d4; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (10%bv : bv 5) Qr10. rreg HS (13%bv : bv 5) Qr13.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkst (ms_regs ?msX) _ _ _] => exists (ms_regs msX), (ms_mem msX) end. eexists. exists i.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite Qr10, E10; reflexivity|].
split; [rewrite Qr13, E11, E10; apply alu_sll1; exact Hi|].
assert (Hi8 : i <= 8) by (destruct (Z_le_gt_dec i 8); [lia|]; assert (i = 9) by lia; subst i; change (2 ^ 9) with 512 in Hpow; lia).
split; [lia|]. split; [lia|]. split; [exact Hpow|].
split; [intros a; cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. cbn [ms_regs].
destruct (pow_clob_kept_RA r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trbsegs E _ _ regs [] POW_KEPT_RA HS HAE ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1 E 11 10 i E11 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia.
apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc.
aj_run_to trbtbl_lib_ok HS HJ 0x897c0; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (10%bv : bv 5) Qr10. rreg HS (11%bv : bv 5) Qr11. rreg HS (12%bv : bv 5) Qr12. rreg HS (14%bv : bv 5) Qr14.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply SRr_mono;
[ eapply (IH (i + 1) sg W (ms_regs msX) (ms_mem msX) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k ltac:(lia) HJ);
[ rewrite Qr10, E10, unsigned_lit_small by lia; reflexivity
| rewrite Qr11, E11; reflexivity
| rewrite Qr12, E12; reflexivity
| rewrite Qr14, E14; reflexivity
| lia | lia | rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia ]
| ] end.
cbv beta. intros W' c' _ (-> & regs'' & mem'' & md'' & K & -> & HJ'' & HK10 & HK13 & HK1 & HK2 & HK3 & Hav & Hpr & Hrg).
split; [reflexivity|]. exists regs'', mem'', md'', K.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact HK10|]. split; [exact HK13|].
split; [lia|]. split; [exact HK2|]. split; [exact HK3|].
split; [intros a; rewrite (Hav a); cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; apply Hpr; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. rewrite (Hrg r Hr). cbn [ms_regs].
destruct (pow_clob_kept_RA r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trbsegs E _ _ regs [] POW_KEPT_RA HS HAE ltac:(vm_compute; reflexivity) r Hin).
Qed.
Lemma ra_pow2b : forall (m : nat) (i sg : Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
Z.of_nat m = 9 - i ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 64 -> getr regs 12 = Z_to_bv 64 sg ->
0 <= i <= 9 -> 0 <= sg <= 256 -> (2 ^ i < 2 * sg \/ i = 0) ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 0x898cc) memc (seg_rom trbsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' K,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x898e0) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 10 = Z_to_bv 64 K /\ getr regs' 15 = Z_to_bv 64 (2 ^ K) /\
i <= K <= 8 /\ sg <= 2 ^ K /\ (2 ^ K < 2 * sg \/ K = 0) /\
(forall a, aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall r : bv 5, reg_in r POW_CLOB_D = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros i sg W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Hm HJ H10 H13 H14 H12 Hi Hsg Hpow.
{ exfalso. assert (i = 9) by lia. subst i. change (2 ^ 9) with 512 in Hpow. lia. }
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
assert (Hp2i : 0 < 2 ^ i <= 512) by (split; [apply Z.pow_pos_nonneg; lia | change 512 with (2 ^ 9); apply Z.pow_le_mono_r; lia]).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (E13 : ew (Ereg regs []) 13 = Z_to_bv 64 1) by (rewrite (ew_Ereg_nat regs [] 13 13%bv eq_refl); exact H13).
assert (E14 : ew (Ereg regs []) 14 = Z_to_bv 64 64) by (rewrite (ew_Ereg_nat regs [] 14 14%bv eq_refl); exact H14).
assert (E12 : ew (Ereg regs []) 12 = Z_to_bv 64 sg) by (rewrite (ew_Ereg_nat regs [] 12 12%bv eq_refl); exact H12).
assert (HS : st_ok trbsegs (Ereg regs []) (mkSS 0x898cc sr_atoms [] None
(mkFacts [(10%nat, mkAF 0 9 0); (13%nat, mkAF 1 1 0); (14%nat, mkAF 64 64 0); (12%nat, mkAF 0 256 0)] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 0x898cc) memc (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx.
exact (rn_st_ok_any (Ereg regs []) 0x898cc sr_atoms regs [] (mkFacts [(10%nat, mkAF 0 9 0); (13%nat, mkAF 1 1 0); (14%nat, mkAF 64 64 0); (12%nat, mkAF 0 256 0)] [] []) (mrestrict (w_H W) memc)
(regs_ok_Ereg regs []) eq_refl ltac:(apply Forall_nil) I
ltac:(split; [|split; exact I]; cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite E10, E13, E14, E12, !unsigned_lit_small by lia; rewrite !Z.pow_0_r, !Z.mod_1_r; lia)). }
pose proof HS as HS0.
remember (Ereg regs []) as E eqn:HEdef.
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HEdef; apply env_agree_refl). clear HEdef.
aj_run trbtbl_lib_ok HS HJ; [apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
srr_branch_with trbtbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1 E 13 10 i E13 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia.
apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc.
aj_run_to trbtbl_lib_ok HS HJ 0x898e0; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (10%bv : bv 5) Qr10. rreg HS (15%bv : bv 5) Qr15.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkst (ms_regs ?msX) _ _ _] => exists (ms_regs msX), (ms_mem msX) end. eexists. exists i.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite Qr10, E10; reflexivity|].
split; [rewrite Qr15, E13, E10; apply alu_sll1; exact Hi|].
assert (Hi8 : i <= 8) by (destruct (Z_le_gt_dec i 8); [lia|]; assert (i = 9) by lia; subst i; change (2 ^ 9) with 512 in Hpow; lia).
split; [lia|]. split; [lia|]. split; [exact Hpow|].
split; [intros a; cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. cbn [ms_regs].
destruct (pow_clob_kept_D r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trbsegs E _ _ regs [] POW_KEPT_D HS HAE ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1 E 13 10 i E13 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia.
apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc.
aj_run_to trbtbl_lib_ok HS HJ 0x898cc; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (10%bv : bv 5) Qr10. rreg HS (13%bv : bv 5) Qr13. rreg HS (14%bv : bv 5) Qr14. rreg HS (12%bv : bv 5) Qr12.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply SRr_mono;
[ eapply (IH (i + 1) sg W (ms_regs msX) (ms_mem msX) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k ltac:(lia) HJ);
[ rewrite Qr10, E10, unsigned_lit_small by lia; reflexivity
| rewrite Qr13, E13; reflexivity
| rewrite Qr14, E14; reflexivity
| rewrite Qr12, E12; reflexivity
| lia | lia | left; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia ]
| ] end.
cbv beta. intros W' c' _ (-> & regs'' & mem'' & md'' & K & -> & HJ'' & HK10 & HK13 & HK1 & HK2 & HK3 & Hav & Hpr & Hrg).
split; [reflexivity|]. exists regs'', mem'', md'', K.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact HK10|]. split; [exact HK13|].
split; [lia|]. split; [exact HK2|]. split; [exact HK3|].
split; [intros a; rewrite (Hav a); cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; apply Hpr; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. rewrite (Hrg r Hr). cbn [ms_regs].
destruct (pow_clob_kept_D r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trbsegs E _ _ regs [] POW_KEPT_D HS HAE ltac:(vm_compute; reflexivity) r Hin).
Qed.
End L.
End b.
