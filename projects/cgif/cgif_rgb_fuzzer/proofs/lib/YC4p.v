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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rn_st_ok_any : forall E pc sr (regsM : bvmap 5 word) (rs : smem) (G : facts) mem,
regs_ok E sr regsM -> regions_wf rs = true -> Forall (region_ok trasegs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok trasegs E (mkSS pc sr rs None G) (mkst regsM (Z_to_bv 64 pc) mem (seg_rom trasegs)).
Proof.
intros E pc sr regsM rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma alu_sll1 : forall i, 0 <= i <= 9 -> alu64 ALU_SLL (Z_to_bv 64 1) (Z_to_bv 64 i) = Z_to_bv 64 (2 ^ i).
Proof.
intros i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma denot_sll1 : forall E n1 n i, ew E n1 = Z_to_bv 64 1 -> ew E n = Z_to_bv 64 i -> 0 <= i <= 9 ->
sv_denot E (SAlu ALU_SLL (SOff n1 0) (SOff n 0)) = Z_to_bv 64 (2 ^ i).
Proof.
intros E n1 n i H1 Hn Hi. cbn [sv_denot]. rewrite H1, Hn, !unsigned_lit_small, !Z.add_0_r by lia. apply alu_sll1. exact Hi.
Qed.
Lemma aview_wrap : forall H (m : word -> option byte) a, aview trasegs H m a = aview trasegs H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma aview_kept_nil : forall E H (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview trasegs H m' a = aview trasegs H m a.
Proof.
intros E H m m' HF a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
apply (aview_kept_frame E [] H m m' 0 HF ltac:(lia)); [| apply Z.mod_pos_bound; lia].
intros x Hx (r & Hin & _). exact Hin.
Qed.
Lemma regions_kept_all : forall E H (m m2 : word -> option byte) rs,
(forall a, aview trasegs H m2 a = aview trasegs H m a) -> (forall a, apresent H m a -> apresent H m2 a) ->
Forall (region_kept trasegs E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 rs Hav Hpr. apply Forall_forall. intros r _. split; intros a Ha.
- apply (mbyte_of_aview trasegs). apply Hav.
- apply writable_kept. apply Hpr.
Qed.
Lemma regions_kept_out : forall E H (m m2 : word -> option byte) lo hi rs,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview trasegs H m2 a = aview trasegs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
Forall (fun r => 0 <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= lo \/ hi <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r)) rs ->
Forall (region_kept trasegs E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 lo hi rs Hav Hpr Hrs. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (H1 & H2 & H3). split; intros a Ha.
- apply (mbyte_of_aview trasegs). apply Hav; lia.
- apply writable_kept. apply Hpr.
Qed.
Lemma aview_kept_out : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview trasegs H m' a = aview trasegs H m a.
Proof.
intros E rs H m m' HF a Ha Hno. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hno.
Qed.
Definition POW_CLOB_A : list (bv 5) := [11; 13; 14]%bv.
Definition POW_KEPT_A : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pow_clob_kept_A : forall r : bv 5, reg_in r POW_CLOB_A = false -> r = 0%bv \/ In r POW_KEPT_A.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Section L.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Lemma rn_pow2a : forall (m : nat) (i sg : Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
Z.of_nat m = 9 - i ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 sg ->
0 <= i <= 9 -> 1 <= sg <= 256 -> 2 ^ i < 2 * sg ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x885a0) memc (seg_rom trasegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' K,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x885b0) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 13 = Z_to_bv 64 K /\ getr regs' 11 = Z_to_bv 64 (K + 1) /\ getr regs' 14 = Z_to_bv 64 (2 ^ K) /\
i <= K <= 8 /\ sg <= 2 ^ K /\ 2 ^ K < 2 * sg /\
(forall a, aview trasegs (w_H W) mem' a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall r : bv 5, reg_in r POW_CLOB_A = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros i sg W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Hm HJ H10 H11 H19 Hi Hsg Hpow.
{ exfalso. assert (i = 9) by lia. subst i. change (2 ^ 9) with 512 in Hpow. lia. }
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
assert (E10 : ew (Ereg regs []) 11 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H10).
assert (E11 : ew (Ereg regs []) 12 = Z_to_bv 64 1) by (rewrite (ew_Ereg_nat regs [] 12 12%bv eq_refl); exact H11).
assert (E19 : ew (Ereg regs []) 10 = Z_to_bv 64 sg) by (rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H19).
assert (HS : st_ok trasegs (Ereg regs []) (mkSS 0x885a0 sr_atoms [] None
(mkFacts [(11%nat, mkAF 0 9 0); (12%nat, mkAF 1 1 0); (10%nat, mkAF 1 256 0)] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 0x885a0) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx.
exact (rn_st_ok_any (Ereg regs []) 0x885a0 sr_atoms regs [] (mkFacts [(11%nat, mkAF 0 9 0); (12%nat, mkAF 1 1 0); (10%nat, mkAF 1 256 0)] [] []) (mrestrict (w_H W) memc)
(regs_ok_Ereg regs []) eq_refl ltac:(apply Forall_nil) I
ltac:(split; [|split; exact I]; cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite E10, E11, E19, !unsigned_lit_small by lia; rewrite !Z.pow_0_r, !Z.mod_1_r; lia)). }
pose proof HS as HS0.
remember (Ereg regs []) as E eqn:HEdef.
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HEdef; apply env_agree_refl). clear HEdef.
aj_run tratbl_lib_ok HS HJ; [apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
srr_branch_with tratbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1 E 12 11 i E11 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
aj_run_to tratbl_lib_ok HS HJ 0x885a0; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (11%bv : bv 5) Qr10. rreg HS (12%bv : bv 5) Qr11. rreg HS (10%bv : bv 5) Qr19.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply SRr_mono;
[ eapply (IH (i + 1) sg W (ms_regs msX) (ms_mem msX) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k ltac:(lia) HJ);
[ rewrite Qr10, E10, unsigned_lit_small by lia; reflexivity
| rewrite Qr11, E11; reflexivity
| rewrite Qr19, E19; reflexivity
| lia | lia | rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia ]
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
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1 E 12 11 i E11 E10 Hi) in Hc. cbn [sv_denot] in Hc.
rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
aj_run_to tratbl_lib_ok HS HJ 0x885b0; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (11%bv : bv 5) Qr10. rreg HS (13%bv : bv 5) Qr12. rreg HS (14%bv : bv 5) Qr13.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkst (ms_regs ?msX) _ _ _] => exists (ms_regs msX), (ms_mem msX) end. eexists. exists i.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite Qr12, E10; reflexivity|].
split; [rewrite Qr10, E10, unsigned_lit_small by lia; reflexivity|].
split; [rewrite Qr13, E11, E10; apply alu_sll1; exact Hi|].
assert (Hi8 : i <= 8) by (destruct (Z_le_gt_dec i 8); [lia|]; assert (i = 9) by lia; subst i; change (2 ^ 9) with 512 in Hpow; lia).
split; [lia|]. split; [lia|]. split; [exact Hpow|].
split; [intros a; cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. cbn [ms_regs].
destruct (pow_clob_kept_A r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trasegs E _ _ regs [] POW_KEPT_A HS HAE ltac:(vm_compute; reflexivity) r Hin).
Qed.
Definition POW_CLOB_B : list (bv 5) := [11; 12; 14]%bv.
Definition POW_KEPT_B : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pow_clob_kept_B : forall r : bv 5, reg_in r POW_CLOB_B = false -> r = 0%bv \/ In r POW_KEPT_B.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Lemma rn_pow2b : forall (m : nat) (i sg : Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
Z.of_nat m = 9 - i ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 12 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 sg ->
0 <= i <= 9 -> 1 <= sg <= 256 -> 2 ^ i < 2 * sg ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x88680) memc (seg_rom trasegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' K,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x88690) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 11 = Z_to_bv 64 K /\ getr regs' 12 = Z_to_bv 64 (K + 1) /\ getr regs' 14 = Z_to_bv 64 (2 ^ K) /\
i <= K <= 8 /\ sg <= 2 ^ K /\ 2 ^ K < 2 * sg /\
(forall a, aview trasegs (w_H W) mem' a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall r : bv 5, reg_in r POW_CLOB_B = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros i sg W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Hm HJ Hri Hrone Hrsg Hi Hsg Hpow.
{ exfalso. assert (i = 9) by lia. subst i. change (2 ^ 9) with 512 in Hpow. lia. }
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
assert (Ei : ew (Ereg regs []) 12 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs [] 12 12%bv eq_refl); exact Hri).
assert (Eone : ew (Ereg regs []) 13 = Z_to_bv 64 1) by (rewrite (ew_Ereg_nat regs [] 13 13%bv eq_refl); exact Hrone).
assert (Esg : ew (Ereg regs []) 15 = Z_to_bv 64 sg) by (rewrite (ew_Ereg_nat regs [] 15 15%bv eq_refl); exact Hrsg).
assert (HS : st_ok trasegs (Ereg regs []) (mkSS 0x88680 sr_atoms [] None
(mkFacts [(12%nat, mkAF 0 9 0); (13%nat, mkAF 1 1 0); (15%nat, mkAF 1 256 0)] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 0x88680) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx.
exact (rn_st_ok_any (Ereg regs []) 0x88680 sr_atoms regs [] (mkFacts [(12%nat, mkAF 0 9 0); (13%nat, mkAF 1 1 0); (15%nat, mkAF 1 256 0)] [] []) (mrestrict (w_H W) memc)
(regs_ok_Ereg regs []) eq_refl ltac:(apply Forall_nil) I
ltac:(split; [|split; exact I]; cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite Ei, Eone, Esg, !unsigned_lit_small by lia; rewrite !Z.pow_0_r, !Z.mod_1_r; lia)). }
pose proof HS as HS0.
remember (Ereg regs []) as E eqn:HEdef.
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HEdef; apply env_agree_refl). clear HEdef.
aj_run tratbl_lib_ok HS HJ; [apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
srr_branch_with tratbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1 E 13 12 i Eone Ei Hi) in Hc. cbn [sv_denot] in Hc.
rewrite Esg, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
aj_run_to tratbl_lib_ok HS HJ 0x88680; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (12%bv : bv 5) Qi. rreg HS (13%bv : bv 5) Qone. rreg HS (15%bv : bv 5) Qsg.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply SRr_mono;
[ eapply (IH (i + 1) sg W (ms_regs msX) (ms_mem msX) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k ltac:(lia) HJ);
[ rewrite Qi, Ei, unsigned_lit_small by lia; reflexivity
| rewrite Qone, Eone; reflexivity
| rewrite Qsg, Esg; reflexivity
| lia | lia | rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia ]
| ] end.
cbv beta. intros W' c' _ (-> & regs'' & mem'' & md'' & K & -> & HJ'' & HKK & HKi & HKpow & HK1 & HK2 & HK3 & Hav & Hpr & Hrg).
split; [reflexivity|]. exists regs'', mem'', md'', K.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact HKK|]. split; [exact HKi|]. split; [exact HKpow|].
split; [lia|]. split; [exact HK2|]. split; [exact HK3|].
split; [intros a; rewrite (Hav a); cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; apply Hpr; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. rewrite (Hrg r Hr). cbn [ms_regs].
destruct (pow_clob_kept_B r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trasegs E _ _ regs [] POW_KEPT_B HS HAE ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned, (denot_sll1 E 13 12 i Eone Ei Hi) in Hc. cbn [sv_denot] in Hc.
rewrite Esg, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
aj_run_to tratbl_lib_ok HS HJ 0x88690; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (12%bv : bv 5) Qi. rreg HS (11%bv : bv 5) QK. rreg HS (14%bv : bv 5) Qpow.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkst (ms_regs ?msX) _ _ _] => exists (ms_regs msX), (ms_mem msX) end. eexists. exists i.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite QK, Ei; reflexivity|].
split; [rewrite Qi, Ei, unsigned_lit_small by lia; reflexivity|].
split; [rewrite Qpow, Eone, Ei; apply alu_sll1; exact Hi|].
assert (Hi8 : i <= 8) by (destruct (Z_le_gt_dec i 8); [lia|]; assert (i = 9) by lia; subst i; change (2 ^ 9) with 512 in Hpow; lia).
split; [lia|]. split; [lia|]. split; [exact Hpow|].
split; [intros a; cbn [ms_mem]; rewrite (aview_kept_nil E _ _ _ HFr2 a); exact (aview_kept_nil E _ _ _ HFr1 a)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. cbn [ms_regs].
destruct (pow_clob_kept_B r Hr) as [-> | Hin].
+ rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok trasegs E _ _ regs [] POW_KEPT_B HS HAE ltac:(vm_compute; reflexivity) r Hin).
Qed.
Definition WDB_CLOB : list (bv 5) := [1; 6; 10; 11; 12; 13; 14; 15; 19; 21]%bv.
Definition WDB_KEPT : list (bv 5) := [2; 3; 4; 5; 7; 8; 9; 16; 17; 18; 20; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma wdb_clob_kept : forall r : bv 5, reg_in r WDB_CLOB = false -> r = 0%bv \/ r = 22%bv \/ In r WDB_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Definition wdb_regions : smem :=
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 []; got_region; bcell_region 24;
YQ0b.mkRegion (Some 25%nat) 0 CGIF_SIZE 0 0
[YQ0b.mkChunk 56 (CVal 8 (SLit A_writecb)); YQ0b.mkChunk 64 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 80 (CVal 8 (SLit 0))] ].
Definition wdb_facts : facts :=
mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4); (19%nat, mkAF 1 765 0); (24%nat, mkAF SB SB 0); (25%nat, HPTR 4);
(32%nat, mkAF 0 18446744073709551615 0) ] [] [].
Definition ss_wdb : sstate :=
mkSS 0x88700 (sr_set (sr_set sr_atoms 22%bv (SLit A_cgif_writecb)) 21%bv (SLit 0)) wdb_regions None wdb_facts.
Lemma rn_wdb : forall (m : nat) (n : Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k sp1 g ctx,
Z.of_nat m = n ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 2 = Z_to_bv 64 sp1 -> sp1 mod 16 = 0 -> sp0 - STK <= sp1 - 16 -> sp1 <= sp0 -> 70368744177664 + 16 <= sp1 -> sp0 <= 2 ^ 47 ->
getr regs 19 = Z_to_bv 64 n -> 1 <= n <= 765 ->
getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 A_cgif_writecb -> getr regs 24 = Z_to_bv 64 SB -> getr regs 25 = Z_to_bv 64 g ->
In (g, CGIF_SIZE) (ablocks B lyc Sc) ->
val_mem trasegs (mrestrict (w_H W) memc) (g + 56) 8 A_writecb -> val_mem trasegs (mrestrict (w_H W) memc) (g + 80) 8 0 ->
val_mem trasegs (mrestrict (w_H W) memc) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x88700) memc (seg_rom trasegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 0x8871c) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 16 <= a < sp1) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall r : bv 5, reg_in r WDB_CLOB = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros n W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k sp1 g ctx
Hm HJ H2 Hal16 Hlo Hhi H46 H47 H18 Hn H19 H21 H24 H25 Hing M56 M80 M64 Hctx; [lia|].
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (proj1 HJ) as HAR. pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgpres, Hgh_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (tl_got_shadow _ TL), (tl_shadow_cell _ TL) in Kgot. rewrite (tl_shadow_cell _ TL) in Kcell.
assert (E2 : ew (Ereg regs []) 2 = Z_to_bv 64 sp1) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); exact H2).
assert (E18 : ew (Ereg regs []) 19 = Z_to_bv 64 n) by (rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact H18).
assert (E24 : ew (Ereg regs []) 24 = Z_to_bv 64 SB) by (rewrite (ew_Ereg_nat regs [] 24 24%bv eq_refl); exact H24).
assert (E25 : ew (Ereg regs []) 25 = Z_to_bv 64 g) by (rewrite (ew_Ereg_nat regs [] 25 25%bv eq_refl); exact H25).
assert (E32 : ew (Ereg regs [Z_to_bv 64 ctx]) 32 = Z_to_bv 64 ctx) by (exact (ew_Ereg_extra regs _ 0)).
assert (XE : forall n : nat, (n < 32)%nat -> ew (Ereg regs [Z_to_bv 64 ctx]) n = ew (Ereg regs []) n).
{ intros nn Hnn. unfold Ereg. cbn [ew]. destruct (nn <? 32)%nat eqn:Q; [reflexivity|]. apply Nat.ltb_ge in Q. lia. }
rewrite <- (XE 2%nat ltac:(lia)) in E2. rewrite <- (XE 19%nat ltac:(lia)) in E18. rewrite <- (XE 24%nat ltac:(lia)) in E24. rewrite <- (XE 25%nat ltac:(lia)) in E25.
clear XE.
assert (HS : st_ok trasegs (Ereg regs [Z_to_bv 64 ctx]) ss_wdb (restrict (w_H W) (mkst regs (Z_to_bv 64 0x88700) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_wdb.
eapply (st_ok_pin_reg' trasegs _ (mkSS 0x88700 (sr_set sr_atoms 22%bv (SLit A_cgif_writecb)) wdb_regions None wdb_facts) _ 21%bv 0); [| exact H19 | reflexivity].
eapply (st_ok_pin_reg' trasegs _ (mkSS 0x88700 sr_atoms wdb_regions None wdb_facts) _ 22%bv A_cgif_writecb); [| exact H21 | reflexivity].
apply (rn_st_ok_any (Ereg regs [Z_to_bv 64 ctx]) 0x88700 sr_atoms regs wdb_regions wdb_facts (mrestrict (w_H W) memc) (regs_ok_Ereg regs _) eq_refl).
- unfold wdb_regions, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
+ rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply HJpres. lia.
+ unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. rewrite <- (Z.add_0_l 663904) at 1.
apply (chunk_ok_val trasegs _ _ 0 663904 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) memc _ _ Kgot).
+ unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. rewrite <- (Z.add_0_l 696760) at 1.
apply (chunk_ok_val trasegs _ _ 0 696760 8 (SOff 24 0) SB);
[cbn [sv_denot]; rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) memc _ _ Kcell).
+ rewrite E25, unsigned_lit_small by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs _ _ g 56 8 _ A_writecb); [reflexivity | unfold A_writecb; zside | zside | exact M56]|].
apply Forall_cons; [apply (chunk_ok_val trasegs _ _ g 64 8 _ ctx); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M64]|].
apply Forall_cons; [apply (chunk_ok_val trasegs _ _ g 80 8 _ 0); [reflexivity | zside | zside | exact M80]|].
apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold wdb_regions, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E2, E25, !unsigned_lit_small by lia.
unfold A_GOT_shadow, A_shadow_glob, CGIF_SIZE. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
repeat split; zone_lia.
- split; [|split; exact I]. cbn [wdb_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2, E18, E24, E25, E32, !unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia. }
pose proof HS as HS0.
remember (Ereg regs [Z_to_bv 64 ctx]) as E eqn:HEdef.
assert (HAE : env_agree 32 (Ereg regs []) E).
{ rewrite HEdef. split; [|reflexivity]. intros nn Hnn. unfold Ereg. cbn [ew]. destruct (nn <? 32)%nat eqn:Q; [reflexivity|]. apply Nat.ltb_ge in Q. lia. }
clear HEdef.
shok_auto SHOK (SOff 24 0) E (mrestrict (w_H W) memc).
aj_run_tok tratbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (obl_blk HJ E25 E24 Hing).
1: { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1 - sp0)); [reflexivity | cbn [ew]; rewrite E2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_ok_tac. }
rename HFr into HFr1. rename HG into HG1. clear HF.
assert (NW : forall Ex rs a, (forall r, In r rs -> YQ0b.r_whi r <= YQ0b.r_wlo r \/ (YQ0b.r_base r = Some 2%nat /\ YQ0b.r_wlo r = -16 /\ YQ0b.r_whi r = 0)) ->
bv_unsigned (ew Ex 2) = sp1 -> ~ (sp1 - 16 <= a < sp1) -> ~ in_wrange Ex rs a).
{ intros Ex rs a Hrs Hsp Hna (r & Hin & Hr). destruct (Hrs r Hin) as [Hro | (Hb & Hwlo & Hwhi)]; [lia|].
rewrite Hb, Hwlo, Hwhi in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. lia. }
srr_branch_tok tratbl_lib_ok HS SHOK (SB, SB + 2 ^ 44 - 1).
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub negb] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E18 in Hc. replace (bv_unsigned (Z_to_bv 64 n)) with n in Hc by (symmetry; apply unsigned_lit_small; lia).
rewrite !unsigned_lit_small in Hc by lia.
destruct (Z.eqb_spec (n + -1) 0) as [Hz | Hnz]; [discriminate Hc|]. clear Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0x88700.
1: { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1 - sp0));
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_ok_tac. }
rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (2%bv : bv 5) Q2. rreg HS (19%bv : bv 5) Q18. rreg HS (21%bv : bv 5) Q19. rreg HS (22%bv : bv 5) Q21. rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 16 <= a < sp1) -> aview trasegs (w_H W) (ms_mem msX) a = aview trasegs (w_H W) memc a);
[ intros a Ha Hna;
rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha ltac:(apply NW; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; first [left; lia | right; repeat split; reflexivity] |]); destruct Hr | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E2; apply unsigned_lit_small; lia | exact Hna]));
cbn [ms_mem];
exact (aview_kept_out _ _ _ _ _ HFr1 a Ha ltac:(apply NW; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; first [left; lia | right; repeat split; reflexivity] |]); destruct Hr | rewrite E2; apply unsigned_lit_small; lia | exact Hna]))
| ] end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply SRr_mono;
[ eapply (IH (n - 1) W (ms_regs msX) (ms_mem msX) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k sp1 g ctx ltac:(lia) HJ);
[ rewrite Q2; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E2
| exact Hal16 | exact Hlo | exact Hhi | exact H46 | exact H47
| rewrite Q18; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E18, unsigned_lit_small by lia; f_equal; lia
| lia
| exact Q19 | exact Q21
| rewrite Q24; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24
| rewrite Q25; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E25
| exact Hing
| eapply val_mem_kept; [|exact M56]; intros q Hq; apply Hav; lia
| eapply val_mem_kept; [|exact M80]; intros q Hq; apply Hav; lia
| eapply val_mem_kept; [|exact M64]; intros q Hq; apply Hav; lia
| exact Hctx ]
| ] end.
cbv beta. intros W' c' _ (-> & regs'' & mem'' & md'' & -> & HJ'' & HK18 & HK19 & Hav2 & Hpr2 & Hrg2).
split; [reflexivity|]. exists regs'', mem'', md''.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact HK18|]. split; [exact HK19|].
split; [intros a Ha Hna; rewrite (Hav2 a Ha Hna); apply Hav; [exact Ha | exact Hna]|].
split; [intros a Ha; apply Hpr2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. rewrite (Hrg2 r Hr). cbn [ms_regs].
destruct (wdb_clob_kept r Hr) as [-> | [-> | Hin]].
+ rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0). reflexivity.
+ rewrite Q21, H21. reflexivity.
+ exact (regs_kept_of_st_ok trasegs _ _ _ regs [] WDB_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub negb] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E18 in Hc. replace (bv_unsigned (Z_to_bv 64 n)) with n in Hc by (symmetry; apply unsigned_lit_small; lia).
rewrite !unsigned_lit_small in Hc by lia.
destruct (Z.eqb_spec (n + -1) 0) as [Hz | Hnz]; [|discriminate Hc]. clear Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0x8871c.
1: { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1 - sp0));
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_ok_tac. }
rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (19%bv : bv 5) Q18. rreg HS (21%bv : bv 5) Q19. rreg HS (22%bv : bv 5) Q21.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkst (ms_regs ?msX) _ _ _] => exists (ms_regs msX), (ms_mem msX) end. eexists.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite Q18; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E18, unsigned_lit_small by lia; f_equal; lia|].
split; [exact Q19|].
split.
{ intros a Ha Hna. cbn [ms_mem].
rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha ltac:(apply NW; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; first [left; lia | right; repeat split; reflexivity] |]); destruct Hr | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E2; apply unsigned_lit_small; lia | exact Hna])).
exact (aview_kept_out _ _ _ _ _ HFr1 a Ha ltac:(apply NW; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; first [left; lia | right; repeat split; reflexivity] |]); destruct Hr | rewrite E2; apply unsigned_lit_small; lia | exact Hna])). }
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. cbn [ms_regs].
destruct (wdb_clob_kept r Hr) as [-> | [-> | Hin]].
+ rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0). reflexivity.
+ rewrite Q21, H21. reflexivity.
+ exact (regs_kept_of_st_ok trasegs _ _ _ regs [] WDB_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) r Hin).
Qed.
End L.
End b.
