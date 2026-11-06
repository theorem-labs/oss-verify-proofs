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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC1z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
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
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section L.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Lemma fl_pow2 : forall (m : nat) (i np : Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
Z.of_nat m = 17 - i ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 np ->
0 <= i <= 17 -> 0 <= np <= 65535 -> (2 ^ i < 2 * np \/ i = 0) ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x87698) memc (seg_rom trasegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' K,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x876a8) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 12 = Z_to_bv 64 K /\ getr regs' 10 = Z_to_bv 64 (K + 1) /\ getr regs' 13 = Z_to_bv 64 (2 ^ K) /\
i <= K <= 16 /\ np <= 2 ^ K /\ (2 ^ K < 2 * np \/ K = 0) /\
(forall a, aview trasegs (w_H W) mem' a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall r : bv 5, reg_in r POW_CLOB_A = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros i np W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Hm HJ H10 H11 H14 Hi Hnp Hpow.
{ exfalso. assert (i = 17) by lia. subst i. change (2 ^ 17) with 131072 in Hpow. lia. }
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
assert (Hp2i : 0 < 2 ^ i <= 131072) by (split; [apply Z.pow_pos_nonneg; lia | change 131072 with (2 ^ 17); apply Z.pow_le_mono_r; lia]).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (E11 : ew (Ereg regs []) 11 = Z_to_bv 64 1) by (rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H11).
assert (E14 : ew (Ereg regs []) 14 = Z_to_bv 64 np) by (rewrite (ew_Ereg_nat regs [] 14 14%bv eq_refl); exact H14).
assert (HS : st_ok trasegs (Ereg regs []) (mkSS 0x87698 sr_atoms [] None
(mkFacts [(10%nat, mkAF 0 17 0); (11%nat, mkAF 1 1 0); (14%nat, mkAF 0 65535 0)] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 0x87698) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx.
exact (rn_st_ok_any (Ereg regs []) 0x87698 sr_atoms regs [] (mkFacts [(10%nat, mkAF 0 17 0); (11%nat, mkAF 1 1 0); (14%nat, mkAF 0 65535 0)] [] []) (mrestrict (w_H W) memc)
(regs_ok_Ereg regs []) eq_refl ltac:(apply Forall_nil) I
ltac:(split; [|split; exact I]; cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite E10, E11, E14, !unsigned_lit_small by lia; rewrite !Z.pow_0_r, !Z.mod_1_r; lia)). }
pose proof HS as HS0.
remember (Ereg regs []) as E eqn:HEdef.
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HEdef; apply env_agree_refl). clear HEdef.
aj_run tratbl_lib_ok HS HJ; [apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
srr_branch_with tratbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1w E 11 10 i E11 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
aj_run_to tratbl_lib_ok HS HJ 0x87698; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (10%bv : bv 5) Qr10. rreg HS (11%bv : bv 5) Qr11. rreg HS (14%bv : bv 5) Qr14.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
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
destruct (pow_clob_kept_A r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trasegs E _ _ regs [] POW_KEPT_A HS HAE ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1w E 11 10 i E11 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
aj_run_to tratbl_lib_ok HS HJ 0x876a8; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (10%bv : bv 5) Qr10. rreg HS (12%bv : bv 5) Qr12. rreg HS (13%bv : bv 5) Qr13.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
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
destruct (pow_clob_kept_A r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trasegs E _ _ regs [] POW_KEPT_A HS HAE ltac:(vm_compute; reflexivity) r Hin).
Qed.
End L.
End b.
