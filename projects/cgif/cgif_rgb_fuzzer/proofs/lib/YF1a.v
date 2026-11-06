(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF08 YF19.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, TFX_IMG_END, IAL_STK, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG in *.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ialloc_inited {imgk : img} : forall (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
YK0s.ret_ok (getr regs 1) ->
sp mod 16 = 0 -> TFX_IMG_END <= sp - IAL_STK -> sp < 2 ^ 64 -> (forall a, sp - IAL_STK <= a < sp -> apresent H mem a) ->
val_mem tfxsegs m TFX_IAL_FLAG 1 1 -> val_mem tfxsegs m (TFX_IAL_FLAG + 1) 1 0 ->
val_mem tfxsegs m TFX_IAL_W 8 4096 -> val_mem tfxsegs m (TFX_IAL_W + 8) 8 (TFX_IAL_W + 16) ->
(forall a, TFX_IAL_LO <= a < TFX_IAL_W \/ TFX_IAL_W + 16 <= a < TFX_IAL_HI -> mbyte tfxsegs m a = Some (Z_to_bv 8 0)) ->
SRr tfxsegs W (mkCfg (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfxsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 TFX_IAL_LO /\
(forall x : word, ~ (sp - IAL_STK <= bv_unsigned x < sp) -> ~ (TFX_IAL_LO <= bv_unsigned x < TFX_IAL_HI) ->
~ (TFX_IAL_FLAG <= bv_unsigned x < TFX_IAL_FLAG + 4) -> mem' x = mem x) /\
(forall a, TFX_IMG_END <= a < 2 ^ 64 -> apresent H mem a -> apresent H mem' a) /\
let m' := mrestrict H mem' in
val_mem tfxsegs m' TFX_IAL_FLAG 1 1 /\ val_mem tfxsegs m' (TFX_IAL_FLAG + 1) 1 0 /\
val_mem tfxsegs m' TFX_IAL_W 8 4096 /\ val_mem tfxsegs m' (TFX_IAL_W + 8) 8 (TFX_IAL_W + 16) /\
(forall a, TFX_IAL_LO <= a < TFX_IAL_W \/ TFX_IAL_W + 16 <= a < TFX_IAL_HI -> mbyte tfxsegs m' a = Some (Z_to_bv 8 0))).
Proof.
intros W regs mem md. cbv zeta. intros Hra Hal Hsp Hsp64 HPRES HF1 HF2 HW1 HW2 HZ. pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
set (E0 := Ereg regs [Z_to_bv 64 0]).
assert (E2 : ew E0 2 = getr regs 2) by (img_try (img_exact (ew_Ereg_nat regs [Z_to_bv 64 0] 2 2%bv eq_refl))).
assert (E1 : ew E0 1 = getr regs 1) by (img_try (img_exact (ew_Ereg_nat regs [Z_to_bv 64 0] 1 1%bv eq_refl))).
assert (HS : st_ok tfxsegs E0 SS_T (restrict (w_H W) (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfxsegs)))).
{ unfold SS_T, A_ialloc. rewrite restrict_mkst_fx. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. unfold rSTK, rFLAG1. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
+ img_apply (region_ok_stack tfxsegs E0 _ 2 sp (- IAL_STK)); [img_try (rewrite E2; img_refl) | img_try (numconst; img_lia) | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (numconst; img_lia) | img_try (img_apply HPRES; img_exact Ha)].
+ reg_intro. unfold TFX_IAL_FLAG. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. eapply chunk_ok_val; [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact HF1)].
- img_apply pairwise_disjoint_of_extents. unfold rSTK, rFLAG1, extent_of_region. cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite (ew_Ereg_nat regs [Z_to_bv 64 0] 2 2%bv eq_refl). fold sp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [IFF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ew_Ereg_nat regs [Z_to_bv 64 0] 2 2%bv eq_refl). fold sp.
replace (ew (Ereg regs [Z_to_bv 64 0]) aFW) with (Z_to_bv 64 0) by img_refl. rewrite (unsigned_lit_small 0) by img_lia.
numconst. repeat split; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
srr_run_to_sh tfxtbl_rtF_ok HS (0x5eac8 + D_2c4).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
assert (FR : forall x : word, ~ (sp - IAL_STK <= bv_unsigned x < sp) -> ms_mem msR x = mem x).
{ intros x Hx. img_apply (frame_of_outside E0 _ _ _ x HF). intros r Hr. cbn [ss_mem SS_T In] in Hr.
destruct Hr as [<-|[<-|[]]]; unfold rSTK, rFLAG1; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; [img_try (right; rewrite E2; fold sp; clear - Hx; img_lia) | img_try (left; img_lia)]. }
eapply (SRr_ret_at tfxsegs tfxtbl_rtF tfxtbl_rtF_ok Hwx W E0); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|].
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { img_apply (regs_preserved_of_st_ok tfxsegs E0 _ _ regs [Z_to_bv 64 0] HS); [img_try (img_apply env_agree_refl) | img_try ((img_case; vm_compute); img_refl)]. }
split. { rreg HS (10%bv : bv 5) R10. rewrite R10. img_refl. }
split. { intros x H1 _ _. img_apply FR. img_exact H1. }
split. { intros a Ha HP.
assert (D : (sp - IAL_STK <= a < sp) \/ ~ (sp - IAL_STK <= a < sp)) by img_lia. destruct D as [D|D].
- eapply (st_ok_window_apresent (w_H W) E0 _ _ 0 _ _ HS); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite E2; fold sp; clear - D; unfold IAL_STK in *; img_lia) | img_try (clear - Ha; img_lia)].
- img_apply (apresent_same (w_H W) mem); [img_try (img_apply FR; rewrite unsigned_lit_small by (clear - Ha; numconst; img_lia); img_exact D) | img_try (img_exact HP)]. }
assert (FRz : forall a, 0 <= a < TFX_IMG_END -> ms_mem msR (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. img_apply FR. rewrite unsigned_lit_small by (img_try (clear - Ha; numconst; img_lia)). clear - Ha Hsp; numconst; img_lia. }
split. { img_apply (val_mem_frame (w_H W) mem); [img_try (intros k Hk; img_apply FRz; clear - Hk; numconst; img_lia) | img_try (img_exact HF1)]. }
split. { img_apply (val_mem_frame (w_H W) mem); [img_try (intros k Hk; img_apply FRz; clear - Hk; numconst; img_lia) | img_try (img_exact HF2)]. }
split. { img_apply (val_mem_frame (w_H W) mem); [img_try (intros k Hk; img_apply FRz; clear - Hk; numconst; img_lia) | img_try (img_exact HW1)]. }
split. { img_apply (val_mem_frame (w_H W) mem); [img_try (intros k Hk; img_apply FRz; clear - Hk; numconst; img_lia) | img_try (img_exact HW2)]. }
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) mem (ms_mem msR) a); [img_try (img_apply HZ; img_exact Ha) | img_try (img_apply FRz; clear - Ha; numconst; img_lia)].
Qed.
Definition OUT {imgk : img} (sp ux : Z) : Prop :=
~ (sp - IAL_STK <= ux < sp) /\ ~ (TFX_IAL_LO <= ux < TFX_IAL_HI) /\ ~ (TFX_IAL_FLAG <= ux < TFX_IAL_FLAG + 4).
Definition GAP {imgk : img} (ux : Z) : Prop := (0xeb3c8 + D_10c0) <= ux < (0xeb400 + D_10c0).
Definition UNCH {imgk : img} (sp ux : Z) : Prop := OUT sp ux \/ GAP ux.
Definition KEEPW {imgk : img} (sp ux : Z) : Prop :=
~ (sp - IAL_STK <= ux < sp) /\ ~ (TFX_IAL_FLAG <= ux < TFX_IAL_FLAG + 4) /\ ~ (TFX_IAL_LO <= ux < TFX_IAL_LO + 8) /\ ~ (TFX_IAL_W <= ux < TFX_IAL_W + 16).
Definition INZ1 {imgk : img} (ux : Z) : Prop := (0x12c3c8 + D_10c0) <= ux < (0x12c3f0 + D_10c0).
Definition INZ2 {imgk : img} (ux : Z) : Prop := INZ1 ux \/ (0xab3c8 + D_10c0) <= ux < (0xeb3c8 + D_10c0).
Definition INZ3 {imgk : img} (ux : Z) : Prop := INZ2 ux \/ (0xeb400 + D_10c0) <= ux < (0xec180 + D_10c0).
Definition INZ4 {imgk : img} (ux : Z) : Prop := INZ3 ux \/ (0xec190 + D_10c0) <= ux < (0x12c3c8 + D_10c0).
Ltac frame_keep HF sp BV2 Hsp KW :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
assert (KW : forall x : word, KEEPW sp (bv_unsigned x) -> m' x = m x)
by (img_try (let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
intros x Hx; img_apply (frame_of_outside E rs m m' x HF); intros r Hr;
cbn [ss_mem SS_F2 ss_after_stretch In] in Hr; unfold rSTK, rFLAGW, rPSP, rPS, rLO, flit8 in Hr; unfold KEEPW in Hx;
repeat (destruct Hr as [<-|Hr]; [img_try (cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; try rewrite BV2; clear - Hx Hsp; numconst; img_lia)|]);
destruct Hr));
clear HF
end.
Lemma ialloc_fresh {imgk : img} : forall (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
YK0s.ret_ok (getr regs 1) ->
sp mod 16 = 0 -> TFX_IMG_END <= sp - IAL_STK -> sp < 2 ^ 64 -> (forall a, sp - IAL_STK <= a < sp -> apresent H mem a) ->
val_mem tfxsegs m TFX_IAL_FLAG 1 0 -> val_mem tfxsegs m (TFX_IAL_FLAG + 1) 1 0 ->
val_mem tfxsegs m (0xa2140 + D_10f0) 8 (0x139c60 + D_10c0) -> val_mem tfxsegs m (0x139c60 + D_10c0) 8 4096 ->
(forall a, TFX_IAL_LO <= a < TFX_IAL_W \/ TFX_IAL_W + 16 <= a < TFX_IAL_HI -> mbyte tfxsegs m a = Some (Z_to_bv 8 0)) ->
SRr tfxsegs W (mkCfg (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfxsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 TFX_IAL_LO /\
(forall x : word, ~ (sp - IAL_STK <= bv_unsigned x < sp) -> ~ (TFX_IAL_LO <= bv_unsigned x < TFX_IAL_HI) ->
~ (TFX_IAL_FLAG <= bv_unsigned x < TFX_IAL_FLAG + 4) -> mem' x = mem x) /\
(forall a, TFX_IMG_END <= a < 2 ^ 64 -> apresent H mem a -> apresent H mem' a) /\
let m' := mrestrict H mem' in
val_mem tfxsegs m' TFX_IAL_FLAG 1 1 /\ val_mem tfxsegs m' (TFX_IAL_FLAG + 1) 1 0 /\
val_mem tfxsegs m' TFX_IAL_W 8 4096 /\ val_mem tfxsegs m' (TFX_IAL_W + 8) 8 (TFX_IAL_W + 16) /\
(forall a, TFX_IAL_LO <= a < TFX_IAL_W \/ TFX_IAL_W + 16 <= a < TFX_IAL_HI -> mbyte tfxsegs m' a = Some (Z_to_bv 8 0))).
Proof.
intros W regs mem md. cbv zeta. intros Hra Hal Hsp Hsp64 HPRES HF1 HF2 HPSP HPS HZ. pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
destruct (rw_mbyte W mem (TFX_IAL_FLAG + 2) ltac:(img_try (numconst; img_lia))) as [b2 Hb2].
destruct (rw_mbyte W mem (TFX_IAL_FLAG + 3) ltac:(img_try (numconst; img_lia))) as [b3 Hb3].
pose proof (bv_unsigned_in_range _ b2) as R2. pose proof (bv_unsigned_in_range _ b3) as R3.
unfold bv_modulus in R2, R3. change (2 ^ Z.of_N 8) with 256 in R2, R3.
set (h := bv_unsigned b2 + 256 * bv_unsigned b3). set (FW := 65536 * h).
pose proof (flagword_val _ _ b2 b3 HF1 HF2 Hb2 Hb3) as HFW. fold h in HFW. fold FW in HFW.
set (E0 := Ereg regs [Z_to_bv 64 FW]).
assert (E2 : ew E0 2 = getr regs 2) by (img_try (img_exact (ew_Ereg_nat regs [Z_to_bv 64 FW] 2 2%bv eq_refl))).
assert (E1 : ew E0 1 = getr regs 1) by (img_try (img_exact (ew_Ereg_nat regs [Z_to_bv 64 FW] 1 1%bv eq_refl))).
assert (E32 : ew E0 aFW = Z_to_bv 64 FW) by img_refl.
assert (HS : st_ok tfxsegs E0 SS_F2 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfxsegs)))).
{ unfold SS_F2, A_ialloc. rewrite restrict_mkst_fx. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. unfold rSTK, rFLAGW, rPSP, rPS, rLO, flit8.
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]]])].
+ img_apply (region_ok_stack tfxsegs E0 _ 2 sp (- IAL_STK)); [img_try (rewrite E2; img_refl) | img_try (numconst; img_lia) | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (numconst; img_lia) | img_try (img_apply HPRES; img_exact Ha)].
+ reg_intro. unfold TFX_IAL_FLAG. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_apply rw_writable; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. eapply (chunk_ok_val tfxsegs E0 _ _ _ _ _ FW); [img_try (cbn [sv_denot]; rewrite E32, (unsigned_lit_small FW), Z.add_0_r by ((subst FW h; cbv beta); img_lia); img_refl) | img_try (cbn; (subst FW h; cbv beta); img_lia) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact HFW)].
+ reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. eapply chunk_ok_val; [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact HPSP)].
+ reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. eapply chunk_ok_val; [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact HPS)].
+ reg_intro. unfold TFX_IAL_LO. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_apply rw_writable; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. img_apply HZ. left. numconst. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold rSTK, rFLAGW, rPSP, rPS, rLO, flit8, extent_of_region. cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite (ew_Ereg_nat regs [Z_to_bv 64 FW] 2 2%bv eq_refl). fold sp. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [IFF2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ew_Ereg_nat regs [Z_to_bv 64 FW] 2 2%bv eq_refl). fold sp.
replace (ew (Ereg regs [Z_to_bv 64 FW]) aFW) with (Z_to_bv 64 FW) by img_refl.
rewrite (unsigned_lit_small FW) by (img_try ((subst FW h; cbv beta); img_lia)).
numconst. repeat split; first [(subst FW h; cbv beta); img_lia | img_change (2 ^ 4) with 16; img_exact Hal | img_change (2 ^ 16) with 65536; (subst FW; cbv beta); rewrite Z.mul_comm; img_apply Z_mod_mult]. }
assert (R32 : rho_of E0 32%nat = 65536 * (bv_unsigned b2 + 256 * bv_unsigned b3)) by (img_try (unfold rho_of; img_change (ew E0 32) with (Z_to_bv 64 FW); img_apply unsigned_lit_small; (subst FW h; cbv beta); img_lia)).
srr_run_to_sh tfxtbl_rtF_ok HS (0x5e9ac + D_2c4). rename HF into HF_1. clear HFr.
pin32 HS (10%bv : bv 5) R2 R3 R32.
srr_run_to_sh tfxtbl_rtF_ok HS (0x5e9f4 + D_2c4). rename HF into HF_2. clear HFr.
pin32 HS (11%bv : bv 5) R2 R3 R32.
srr_run_to_sh tfxtbl_rtF_ok HS (0x5e9fc + D_2c4). rename HF into HF_3. clear HFr.
pin32 HS (10%bv : bv 5) R2 R3 R32.
srr_run_to_sh tfxtbl_rtF_ok HS (0x64484 + D_2c4). rename HF into HF_4. clear HFr.
assert (BV2_0 : bv_unsigned (ew E0 2) = sp) by (img_try (rewrite E2; img_refl)).
cbn [ss_mem SS_F2] in HF_1.
frame_keep HF_1 sp BV2_0 Hsp KW1. frame_keep HF_2 sp BV2_0 Hsp KW2. frame_keep HF_3 sp BV2_0 Hsp KW3. frame_keep HF_4 sp BV2_0 Hsp KW4.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms4 end.
assert (UK : forall ux, UNCH sp ux -> KEEPW sp ux) by (img_try (intros ux Hu; unfold UNCH, OUT, GAP, KEEPW in *; clear - Hu Hsp; numconst; img_lia)).
assert (EQ4 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms4 x = mem x).
{ intros x Hx. rewrite (KW4 x (UK _ Hx)), (KW3 x (UK _ Hx)), (KW2 x (UK _ Hx)). img_exact (KW1 x (UK _ Hx)). }
clear KW1 KW2 KW3 KW4.
Local Ltac do_stretch HS k d len retpc BV2 Hsp Hsp64 :=
let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in let Q1 := fresh "Q1" in
rreg HS (10%bv : bv 5) Q10; rreg HS (11%bv : bv 5) Q11; rreg HS (12%bv : bv 5) Q12; rreg HS (1%bv : bv 5) Q1;
eapply (imemset_stretch _ k _ _ _ _ d len retpc);
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (img_exact Q10) | img_try (img_exact Q11) | img_try (img_exact Q12) | img_try (img_exact Q1)
| img_lia | img_lia | img_lia | img_refl | img_lia
| img_try (let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; repeat (destruct Hr as [<-|Hr]; [cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; try rewrite BV2; clear - Hsp; numconst; img_lia|]); destruct Hr)
| img_try (let r := fresh "r" in let Hr := fresh "Hr" in let a := fresh "a" in let Ha := fresh "Ha" in
intros r a Hr Ha; repeat (destruct Hr as [<-|Hr]; [cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Ha; try rewrite BV2 in Ha; clear - Hsp Hsp64 Ha; numconst; img_lia|]); destruct Hr)
| img_try (clear Q10 Q11 Q12 Q1 HS) ].
Local Ltac name_env HS E0 b2 b3 sp En HEn HEprev R32n R32 BV2n BV2_0 :=
lazymatch type of HS with st_ok _ ?E _ _ => set (En := E) in HS end;
assert (HEn : forall k, (k < 33)%nat -> ew En k = ew E0 k) by (img_try (intros k Hk; (subst En; cbv beta); rewrite ew_havoc_old by img_lia; img_apply HEprev; img_exact Hk));
assert (R32n : rho_of En 32%nat = 65536 * (bv_unsigned b2 + 256 * bv_unsigned b3)) by (img_try (unfold rho_of; rewrite (HEn 32%nat ltac:(img_lia)); img_exact R32));
assert (BV2n : bv_unsigned (ew En 2) = sp) by (img_try (rewrite (HEn 2%nat ltac:(img_lia)); img_exact BV2_0)).
assert (HE0 : forall k, (k < 33)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
do_stretch HS 33%nat (0x12c3c8 + D_10c0) 40 (0x5ea20 + D_2c4) BV2_0 Hsp Hsp64.
intros regs1 mem1 mat1 HS _ _ FR1 _ ZR1.
name_env HS E0 b2 b3 sp En1 HE1 HE0 R32_1 R32 BV2_1 BV2_0.
assert (EQ5 : forall x : word, UNCH sp (bv_unsigned x) -> mem1 x = mem x).
{ intros x Hx. rewrite (FR1 x) by (img_try (unfold UNCH, OUT, GAP in Hx; clear - Hx; numconst; img_lia)). img_exact (EQ4 x Hx). }
assert (Z1 : forall x : word, INZ1 (bv_unsigned x) -> mem1 x = Some (Z_to_bv 8 0)) by (img_try (intros x Hx; img_apply ZR1; unfold INZ1 in Hx; img_exact Hx)).
clear EQ4 FR1 ZR1.
srr_run_to_sh tfxtbl_rtF_ok HS (0x64484 + D_2c4). clear HFr. frame_keep HF sp BV2_1 Hsp KW5.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms5 end.
assert (EQ6 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms5 x = mem x) by (img_try (intros x Hx; rewrite (KW5 x (UK _ Hx)); img_exact (EQ5 x Hx))).
assert (Z2 : forall x : word, INZ1 (bv_unsigned x) -> ms_mem ms5 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW5 x) by (img_try (unfold INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; img_lia)). img_exact (Z1 x Hx). }
clear EQ5 Z1 KW5.
do_stretch HS 36%nat (0xab3c8 + D_10c0) 262144 (0x5ea38 + D_2c4) BV2_1 Hsp Hsp64.
intros regs2 mem2 mat2 HS _ _ FR2 _ ZR2.
name_env HS E0 b2 b3 sp En2 HE2 HE1 R32_2 R32 BV2_2 BV2_0.
assert (EQ7 : forall x : word, UNCH sp (bv_unsigned x) -> mem2 x = mem x).
{ intros x Hx. rewrite (FR2 x) by (img_try (unfold UNCH, OUT, GAP in Hx; clear - Hx; numconst; img_lia)). img_exact (EQ6 x Hx). }
assert (Z3 : forall x : word, INZ2 (bv_unsigned x) -> mem2 x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct Hx as [Hx|Hx]; [|img_try (img_apply ZR2; img_exact Hx)]. rewrite (FR2 x) by (img_try (unfold INZ1 in Hx; clear - Hx; img_lia)). img_exact (Z2 x Hx). }
clear EQ6 Z2 FR2 ZR2.
srr_run_to_sh tfxtbl_rtF_ok HS (0x64484 + D_2c4). clear HFr. frame_keep HF sp BV2_2 Hsp KW6.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms6 end.
assert (EQ8 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms6 x = mem x) by (img_try (intros x Hx; rewrite (KW6 x (UK _ Hx)); img_exact (EQ7 x Hx))).
assert (Z4 : forall x : word, INZ2 (bv_unsigned x) -> ms_mem ms6 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW6 x) by (img_try (unfold INZ2, INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; img_lia)). img_exact (Z3 x Hx). }
clear EQ7 Z3 KW6.
do_stretch HS 39%nat (0xeb400 + D_10c0) 3456 (0x5ea50 + D_2c4) BV2_2 Hsp Hsp64.
intros regs3 mem3 mat3 HS _ _ FR3 _ ZR3.
name_env HS E0 b2 b3 sp En3 HE3 HE2 R32_3 R32 BV2_3 BV2_0.
assert (EQ9 : forall x : word, UNCH sp (bv_unsigned x) -> mem3 x = mem x).
{ intros x Hx. rewrite (FR3 x) by (img_try (unfold UNCH, OUT, GAP in Hx; clear - Hx; numconst; img_lia)). img_exact (EQ8 x Hx). }
assert (Z5 : forall x : word, INZ3 (bv_unsigned x) -> mem3 x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct Hx as [Hx|Hx]; [|img_try (img_apply ZR3; img_exact Hx)]. rewrite (FR3 x) by (img_try (unfold INZ2, INZ1 in Hx; clear - Hx; img_lia)). img_exact (Z4 x Hx). }
clear EQ8 Z4 FR3 ZR3.
srr_run_to_sh tfxtbl_rtF_ok HS (0x64484 + D_2c4). clear HFr. frame_keep HF sp BV2_3 Hsp KW7.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms7 end.
assert (EQ10 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms7 x = mem x) by (img_try (intros x Hx; rewrite (KW7 x (UK _ Hx)); img_exact (EQ9 x Hx))).
assert (Z6 : forall x : word, INZ3 (bv_unsigned x) -> ms_mem ms7 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW7 x) by (img_try (unfold INZ3, INZ2, INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; img_lia)). img_exact (Z5 x Hx). }
clear EQ9 Z5 KW7.
do_stretch HS 42%nat (0xec180 + D_10c0) 262728 (0x5ea68 + D_2c4) BV2_3 Hsp Hsp64.
intros regs4 mem4 mat4 HS _ _ FR4 _ ZR4.
name_env HS E0 b2 b3 sp En4 HE4 HE3 R32_4 R32 BV2_4 BV2_0.
assert (EQ11 : forall x : word, UNCH sp (bv_unsigned x) -> mem4 x = mem x).
{ intros x Hx. rewrite (FR4 x) by (img_try (unfold UNCH, OUT, GAP in Hx; clear - Hx; numconst; img_lia)). img_exact (EQ10 x Hx). }
assert (Z7 : forall x : word, INZ4 (bv_unsigned x) -> mem4 x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct Hx as [Hx|Hx]; [|img_try (img_apply ZR4; clear - Hx; img_lia)]. rewrite (FR4 x) by (img_try (unfold INZ3, INZ2, INZ1 in Hx; clear - Hx; img_lia)). img_exact (Z6 x Hx). }
clear EQ10 Z6 FR4 ZR4.
srr_run_to_sh tfxtbl_rtF_ok HS (0x5ea90 + D_2c4). clear HFr. frame_keep HF sp BV2_4 Hsp KW8.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms8 end.
assert (EQ12 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms8 x = mem x) by (img_try (intros x Hx; rewrite (KW8 x (UK _ Hx)); img_exact (EQ11 x Hx))).
assert (Z8 : forall x : word, INZ4 (bv_unsigned x) -> ms_mem ms8 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW8 x) by (img_try (unfold INZ4, INZ3, INZ2, INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; img_lia)). img_exact (Z7 x Hx). }
clear EQ11 Z7 KW8.
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion None TFX_IAL_W (TFX_IAL_W + 16) TFX_IAL_W (TFX_IAL_W + 16) [])) in HS;
[ | img_refl
| img_try (unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict];
unfold TFX_IAL_W; split; [img_lia|]; split; [img_lia|]; split; [intros o Ho; img_apply rw_writable; img_lia | constructor])
| img_try (cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite BV2_4; clear - Hsp; numconst; repeat split; img_lia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfxtbl_rtF_ok HS (0x5eac8 + D_2c4). clear HFr. frame_keep HF sp BV2_4 Hsp KW9.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
assert (EQR : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem msR x = mem x) by (img_try (intros x Hx; rewrite (KW9 x (UK _ Hx)); img_exact (EQ12 x Hx))).
assert (ZF : forall x : word, INZ4 (bv_unsigned x) -> ms_mem msR x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW9 x) by (img_try (unfold INZ4, INZ3, INZ2, INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; img_lia)). img_exact (Z8 x Hx). }
clear EQ12 Z8 KW9.
eapply (SRr_ret_at tfxsegs tfxtbl_rtF tfxtbl_rtF_ok Hwx W En4); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|].
rreg HS (1%bv : bv 5) Q1. rewrite (HE4 1%nat ltac:(img_lia)), E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { img_apply (regs_preserved_of_st_ok tfxsegs En4 _ _ regs [Z_to_bv 64 FW] HS); [| img_try ((img_case; vm_compute); img_refl)].
(subst En4 En3 En2 En1 E0; cbv beta). repeat (img_apply env_agree_havoc_ge; [img_lia|]). img_apply env_agree_refl. }
split. { rreg HS (10%bv : bv 5) R10. rewrite R10. img_refl. }
split. { intros x H1 H2 H3. img_apply EQR. left. img_exact (conj H1 (conj H2 H3)). }
split. { intros a Ha HP.
assert (D : (sp - IAL_STK <= a < sp) \/ ~ (sp - IAL_STK <= a < sp)) by img_lia. destruct D as [D|D].
- eapply (st_ok_window_apresent (w_H W) En4 _ _ 1 _ _ HS); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite BV2_4; clear - D; unfold IAL_STK in *; img_lia) | img_try (clear - Ha; img_lia)].
- img_apply (apresent_same (w_H W) mem); [|img_try (img_exact HP)]. img_apply EQR. left. unfold OUT. rewrite unsigned_lit_small by (img_try (clear - Ha; numconst; img_lia)). clear - Ha D; numconst; img_lia. }
split. { memv HS 2%nat 1%nat; [img_refl | img_refl | img_lia]. }
split. { memv HS 2%nat 0%nat; [img_refl | img_refl | img_lia]. }
split. { memv HS 0%nat 1%nat; [img_refl | img_refl | img_lia]. }
split. { memv HS 0%nat 0%nat; [img_refl | img_refl | img_try (numconst; img_lia)]. }
intros a Ha.
assert (C : a = TFX_IAL_LO \/ TFX_IAL_LO + 1 <= a < TFX_IAL_LO + 8 \/ GAP a \/ INZ4 a) by (img_try (unfold GAP, INZ4, INZ3, INZ2, INZ1; clear - Ha; numconst; img_lia)).
destruct C as [->|[C|[C|C]]].
- pose proof (chunk_val_at (w_H W) En4 _ _ 5 0 _ _ 1%N _ 0 TFX_IAL_LO HS eq_refl eq_refl eq_refl eq_refl ltac:(img_try (cbn; img_lia)) ltac:(img_try (cbn; img_lia))) as V.
specialize (V 0%nat ltac:(img_lia)). rewrite Z.add_0_r in V. img_exact V.
- eapply (st_ok_chunk_zero (w_H W) En4 _ _ 5 _ 1 _ _ a HS); [img_refl | img_refl | img_try (cbn [YQ0b.r_base base_val]; clear - C; numconst; img_lia)].
- rewrite (mbyte_mrestrict_same (w_H W) mem (ms_mem msR) a) by (img_try (img_apply EQR; right; rewrite unsigned_lit_small by (clear - C; unfold GAP in C; img_lia); img_exact C)).
img_apply HZ. left. unfold GAP in C. clear - C. numconst. img_lia.
- unfold mbyte, mrestrict. rewrite (rw_unhidden W a) by (img_try (unfold INZ4, INZ3, INZ2, INZ1 in C; clear - C; img_lia)).
rewrite (ZF (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by (unfold INZ4, INZ3, INZ2, INZ1 in C; clear - C; img_lia); img_exact C)). img_refl.
Qed.
Theorem tfx_ialloc_ok {imgk : img} : tfx_ialloc_spec.
Proof.
unfold tfx_ialloc_spec. intros W regs mem md ii. cbv zeta. intros Hra Hal Hsp Hsp64 HPRES HF1 HF2 HPSP HPS HW HZ.
destruct ii.
- destruct HW as [HW1 HW2]. img_exact (ialloc_inited W regs mem md Hra Hal Hsp Hsp64 HPRES HF1 HF2 HW1 HW2 HZ).
- img_exact (ialloc_fresh W regs mem md Hra Hal Hsp Hsp64 HPRES HF1 HF2 HPSP HPS HZ).
Qed.
End b.
