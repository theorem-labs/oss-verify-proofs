(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCey.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YI08 YI0c YI0g YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji YCjo YM01 YM02.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition QF_DI0 : Z := 0x83ee4.
Definition QF_DI1 : Z := 0x83f0c.
Definition QF_DI2 : Z := 0x83f14.
Definition QF_ND0 : Z := 0x84500.
Definition QF_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition QF_FK8 : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition QF_FK9 : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition QF_FK18 : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section b.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Definition qf_Bx : sv := SOff 27 0.
Definition qf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ss_QF (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition QF_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (rd : bv 5) (v : word) (FK : list (bv 5)) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\ frm_zero (@fp_csr fy') /\
reg_get (@fp_regs fy') rd = v /\ (forall r : bv 5, In r FK -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall r : bv 5, In r QF_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma q_fmv_di0 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k -> frm_zero (@fp_csr fy) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 QF_DI0) mem (seg_rom trbsegs)) md)
(QF_post fy regs mem 0x83ee8 (8%bv : bv 5) (nan_box (Z_to_bv 32 0)) QF_FK8).
Proof.
intros fy regs mem md HJ Hfrm.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
set (E0 := Ereg regs ([] : list word)).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HS0 : @st_ok trbsegs fy E0 (ss_QF QF_DI0) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 QF_DI0) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_QF. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_enterF trbsegs fy 64 E0 (ss_QF QF_DI0) _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 64 (@fp_regs fy)) in HS.
assert (SHOK : sh_ok trbsegs qf_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 QF_DI0) mem (seg_rom trbsegs))) in HJ, SHOK.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_QF] in HS.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK qf_Bspan 0x83ee8.
{ cbn [ss_mem]. apply awr_ok_nil. }
assert (HEf : forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'.
lazymatch type of HS with st_okF _ ?Ex ?ssx (restrict ?Hh ?msF) =>
pose proof (st_okF_freg trbsegs Ex ssx (restrict Hh msF) (8%bv : bv 5) HS) as HFV;
pose proof (st_okF_fregs_kept trbsegs Ex ssx (restrict Hh msF) 64 _ QF_FK8 HS HEf ltac:(vm_compute; reflexivity)) as HFK end.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL.
pose proof HAEx as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs ([] : list word)) _)
by (split; [intros j Hj; transitivity (ew E j); [apply EA; lia | apply HEE; lia] | transitivity (ed E); [exact ED | reflexivity]]).
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ QF_KEEP HSL HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|].
lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz, (ms_regs ms), (ms_mem ms) end. eexists. split; [reflexivity|].
split; [exact HJ|]. split; [exact Hfrm'|].
split.
{ cbn [fp_regs fp_of]. rewrite HFV.
match goal with |- sv_denot _ ?sv0 = _ => let v' := eval vm_compute in sv0 in change sv0 with v' end.
cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity. }
split; [exact HFK|]. split; [exact HKR|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. destruct Hin.
Qed.
Lemma q_fmv_di1 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k -> frm_zero (@fp_csr fy) ->
getr regs 13 = Z_to_bv 64 S255 ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 QF_DI1) mem (seg_rom trbsegs)) md)
(QF_post fy regs mem 0x83f10 (9%bv : bv 5) (nan_box (Z_to_bv 32 S255)) QF_FK9).
Proof.
intros fy regs mem md HJ Hfrm GR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
set (E0 := Ereg regs ([] : list word)).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HS0 : @st_ok trbsegs fy E0 (ss_QF QF_DI1) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 QF_DI1) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_QF. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_enterF trbsegs fy 64 E0 (ss_QF QF_DI1) _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 64 (@fp_regs fy)) in HS.
assert (SHOK : sh_ok trbsegs qf_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 QF_DI1) mem (seg_rom trbsegs))) in HJ, SHOK.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_QF] in HS.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK qf_Bspan 0x83f10.
{ cbn [ss_mem]. apply awr_ok_nil. }
assert (HEf : forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'.
lazymatch type of HS with st_okF _ ?Ex ?ssx (restrict ?Hh ?msF) =>
pose proof (st_okF_freg trbsegs Ex ssx (restrict Hh msF) (9%bv : bv 5) HS) as HFV;
pose proof (st_okF_fregs_kept trbsegs Ex ssx (restrict Hh msF) 64 _ QF_FK9 HS HEf ltac:(vm_compute; reflexivity)) as HFK end.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL.
pose proof HAEx as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs ([] : list word)) _)
by (split; [intros j Hj; transitivity (ew E j); [apply EA; lia | apply HEE; lia] | transitivity (ed E); [exact ED | reflexivity]]).
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ QF_KEEP HSL HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|].
lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz, (ms_regs ms), (ms_mem ms) end. eexists. split; [reflexivity|].
split; [exact HJ|]. split; [exact Hfrm'|].
split.
{ cbn [fp_regs fp_of]. rewrite HFV.
match goal with |- sv_denot _ ?sv0 = _ => let v' := eval vm_compute in sv0 in change sv0 with v' end.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (HEE 13%nat ltac:(lia)), (HE0 13%nat 13%bv eq_refl), GR.
apply bv_eq. vm_compute. reflexivity.
}
split; [exact HFK|]. split; [exact HKR|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. destruct Hin.
Qed.
Lemma q_fmv_di2 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k -> frm_zero (@fp_csr fy) ->
getr regs 14 = Z_to_bv 64 Shi ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 QF_DI2) mem (seg_rom trbsegs)) md)
(QF_post fy regs mem 0x83f18 (18%bv : bv 5) (nan_box (Z_to_bv 32 Shi)) QF_FK18).
Proof.
intros fy regs mem md HJ Hfrm GR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
set (E0 := Ereg regs ([] : list word)).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HS0 : @st_ok trbsegs fy E0 (ss_QF QF_DI2) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 QF_DI2) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_QF. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_enterF trbsegs fy 64 E0 (ss_QF QF_DI2) _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 64 (@fp_regs fy)) in HS.
assert (SHOK : sh_ok trbsegs qf_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 QF_DI2) mem (seg_rom trbsegs))) in HJ, SHOK.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_QF] in HS.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK qf_Bspan 0x83f18.
{ cbn [ss_mem]. apply awr_ok_nil. }
assert (HEf : forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'.
lazymatch type of HS with st_okF _ ?Ex ?ssx (restrict ?Hh ?msF) =>
pose proof (st_okF_freg trbsegs Ex ssx (restrict Hh msF) (18%bv : bv 5) HS) as HFV;
pose proof (st_okF_fregs_kept trbsegs Ex ssx (restrict Hh msF) 64 _ QF_FK18 HS HEf ltac:(vm_compute; reflexivity)) as HFK end.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL.
pose proof HAEx as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs ([] : list word)) _)
by (split; [intros j Hj; transitivity (ew E j); [apply EA; lia | apply HEE; lia] | transitivity (ed E); [exact ED | reflexivity]]).
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ QF_KEEP HSL HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|].
lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz, (ms_regs ms), (ms_mem ms) end. eexists. split; [reflexivity|].
split; [exact HJ|]. split; [exact Hfrm'|].
split.
{ cbn [fp_regs fp_of]. rewrite HFV.
match goal with |- sv_denot _ ?sv0 = _ => let v' := eval vm_compute in sv0 in change sv0 with v' end.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (HEE 14%nat ltac:(lia)), (HE0 14%nat 14%bv eq_refl), GR.
apply bv_eq. vm_compute. reflexivity.
}
split; [exact HFK|]. split; [exact HKR|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. destruct Hin.
Qed.
Lemma q_fmv_nd0 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k -> frm_zero (@fp_csr fy) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 QF_ND0) mem (seg_rom trbsegs)) md)
(QF_post fy regs mem 0x84504 (8%bv : bv 5) (nan_box (Z_to_bv 32 0)) QF_FK8).
Proof.
intros fy regs mem md HJ Hfrm.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
set (E0 := Ereg regs ([] : list word)).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HS0 : @st_ok trbsegs fy E0 (ss_QF QF_ND0) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 QF_ND0) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_QF. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_enterF trbsegs fy 64 E0 (ss_QF QF_ND0) _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 64 (@fp_regs fy)) in HS.
assert (SHOK : sh_ok trbsegs qf_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 QF_ND0) mem (seg_rom trbsegs))) in HJ, SHOK.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_QF] in HS.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK qf_Bspan 0x84504.
{ cbn [ss_mem]. apply awr_ok_nil. }
assert (HEf : forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'.
lazymatch type of HS with st_okF _ ?Ex ?ssx (restrict ?Hh ?msF) =>
pose proof (st_okF_freg trbsegs Ex ssx (restrict Hh msF) (8%bv : bv 5) HS) as HFV;
pose proof (st_okF_fregs_kept trbsegs Ex ssx (restrict Hh msF) 64 _ QF_FK8 HS HEf ltac:(vm_compute; reflexivity)) as HFK end.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL.
pose proof HAEx as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs ([] : list word)) _)
by (split; [intros j Hj; transitivity (ew E j); [apply EA; lia | apply HEE; lia] | transitivity (ed E); [exact ED | reflexivity]]).
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ QF_KEEP HSL HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|].
lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz, (ms_regs ms), (ms_mem ms) end. eexists. split; [reflexivity|].
split; [exact HJ|]. split; [exact Hfrm'|].
split.
{ cbn [fp_regs fp_of]. rewrite HFV.
match goal with |- sv_denot _ ?sv0 = _ => let v' := eval vm_compute in sv0 in change sv0 with v' end.
cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity. }
split; [exact HFK|]. split; [exact HKR|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. destruct Hin.
Qed.
End b.
