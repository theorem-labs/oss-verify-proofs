(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCey.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YI08 YI0c YI0g YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji YCjo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition TEPI_HEAD : Z := 0x844b4.
Definition TEPI_EXIT : Z := 0x844c0.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Hypothesis HSTK : 576 <= STK.
Definition te_Bx : sv := SOff 25 0.
Definition te_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition te_mem : smem := [ YQ0b.mkRegion (Some 2%nat) 448 472 0 0
[YQ0b.mkChunk 448 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 456 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 464 (CVal 8 (SOff 34 0))] ].
Definition ss_TEPI : sstate := mkSS TEPI_HEAD sr_atoms te_mem None (mkFacts [ (2%nat, mkAF (2^46) (2^47) 0) ] [] []).
Definition TEPI_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma te_present8 : forall (H : word -> bool) (mem : word -> option byte) a,
(forall i, 0 <= i < 8 -> apresent H mem (a + i)) -> exists v, 0 <= v < 2 ^ 64 /\ val_mem trbsegs (mrestrict H mem) a 8 v.
Proof.
intros H mem a HP. apply val_mem_of_present8. intros i Hi. destruct (HP i Hi) as [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
Qed.
Lemma trb_epi_fld : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k -> frm_zero (@fp_csr fy) ->
getr regs 2 = w64 (sp0 - 576) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 TEPI_HEAD) mem (seg_rom trbsegs)) md)
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 TEPI_EXIT) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\ frm_zero (@fp_csr fy') /\
(forall r : bv 5, In r TEPI_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md HJ Hfrm G2.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (Rs : 2 ^ 46 <= sp0 - 576 /\ sp0 <= 2 ^ 47) by lia.
destruct (te_present8 (w_H W) mem (sp0 - 576 + 448) ltac:(intros i Hi; apply Hpres; clear - Hi HSTK; lia)) as (v0 & Hv0 & V0).
destruct (te_present8 (w_H W) mem (sp0 - 576 + 456) ltac:(intros i Hi; apply Hpres; clear - Hi HSTK; lia)) as (v1 & Hv1 & V1).
destruct (te_present8 (w_H W) mem (sp0 - 576 + 464) ltac:(intros i Hi; apply Hpres; clear - Hi HSTK; lia)) as (v2 & Hv2 & V2).
set (E0 := Ereg regs (map (Z_to_bv 64) [v0; v1; v2] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [v0; v1; v2] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (U2 : bv_unsigned (ew E0 2) = sp0 + -576) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; rewrite unsigned_lit_small by (clear - Rs; lia); clear; lia).
assert (A32 : bv_unsigned (ew E0 32) = v0) by (pose proof (HV 0%nat v0 eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hv0).
assert (A33 : bv_unsigned (ew E0 33) = v1) by (pose proof (HV 1%nat v1 eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hv1).
assert (A34 : bv_unsigned (ew E0 34) = v2) by (pose proof (HV 2%nat v2 eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hv2).
replace (sp0 - 576 + 448) with (sp0 + -576 + 448) in V0 by (clear; lia).
replace (sp0 - 576 + 456) with (sp0 + -576 + 456) in V1 by (clear; lia).
replace (sp0 - 576 + 464) with (sp0 + -576 + 464) in V2 by (clear; lia).
assert (HS0 : @st_ok trbsegs fy E0 ss_TEPI (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 TEPI_HEAD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_TEPI. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold te_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U2.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val trbsegs E0 _ (sp0 + -576) 448 8 _ v0); [cbn [sv_denot]; rewrite A32, Z.add_0_r; reflexivity | zside | zside | exact V0].
+ apply (chunk_ok_val trbsegs E0 _ (sp0 + -576) 456 8 _ v1); [cbn [sv_denot]; rewrite A33, Z.add_0_r; reflexivity | zside | zside | exact V1].
+ apply (chunk_ok_val trbsegs E0 _ (sp0 + -576) 464 8 _ v2); [cbn [sv_denot]; rewrite A34, Z.add_0_r; reflexivity | zside | zside | exact V2].
- apply pairwise_disjoint_of_extents. unfold te_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0. rewrite U2.
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs. repeat match goal with |- _ /\ _ => split end; lia. }
pose proof (st_ok_enterF trbsegs fy 64 E0 ss_TEPI _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 64 (@fp_regs fy)) in HS.
assert (SHOK : sh_ok trbsegs te_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 TEPI_HEAD) mem (seg_rom trbsegs))) in HJ, SHOK.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_TEPI] in HS.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK te_Bspan TEPI_EXIT.
{ cbn [ss_mem]. unfold te_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
pose proof HAEx as [EA ED].
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [v0; v1; v2] ++ [])) _)
by (split; [intros j Hj; transitivity (ew E j); [apply EA; lia | apply HEE; lia] | transitivity (ed E); [exact ED | reflexivity]]).
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ TEPI_KEEP HSL HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|].
lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz, (ms_regs ms), (ms_mem ms) end. eexists. split; [reflexivity|].
split; [exact HJ|]. split; [exact Hfrm'|]. split; [exact HKR|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. unfold te_mem in Hin. cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YQ0b.r_wlo YQ0b.r_whi]. lia.
Qed.
End c.
