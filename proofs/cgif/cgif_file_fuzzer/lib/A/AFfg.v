(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB15 AFff.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, TFIB_IMG_END, IAL_STK, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG in *.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ialloc_inited : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
YK0s.ret_ok (getr regs 1) ->
sp mod 16 = 0 -> TFIB_IMG_END <= sp - IAL_STK -> sp < 2 ^ 64 -> (forall a, sp - IAL_STK <= a < sp -> apresent H mem a) ->
val_mem tfibsegs m TFIB_IAL_FLAG 1 1 -> val_mem tfibsegs m (TFIB_IAL_FLAG + 1) 1 0 ->
val_mem tfibsegs m TFIB_IAL_W 8 4096 -> val_mem tfibsegs m (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16) ->
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 TFIB_IAL_LO /\
(forall x : word, ~ (sp - IAL_STK <= bv_unsigned x < sp) -> ~ (TFIB_IAL_LO <= bv_unsigned x < TFIB_IAL_HI) ->
~ (TFIB_IAL_FLAG <= bv_unsigned x < TFIB_IAL_FLAG + 4) -> mem' x = mem x) /\
(forall a, TFIB_IMG_END <= a < 2 ^ 64 -> apresent H mem a -> apresent H mem' a) /\
let m' := mrestrict H mem' in
val_mem tfibsegs m' TFIB_IAL_FLAG 1 1 /\ val_mem tfibsegs m' (TFIB_IAL_FLAG + 1) 1 0 /\
val_mem tfibsegs m' TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m' (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0))).
Proof.
intros W regs mem md. cbv zeta. intros Hra Hal Hsp Hsp64 HPRES HF1 HF2 HW1 HW2 HZ. pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
set (E0 := Ereg regs [Z_to_bv 64 0]).
assert (E2 : ew E0 2 = getr regs 2) by (exact (ew_Ereg_nat regs [Z_to_bv 64 0] 2 2%bv eq_refl)).
assert (E1 : ew E0 1 = getr regs 1) by (exact (ew_Ereg_nat regs [Z_to_bv 64 0] 1 1%bv eq_refl)).
assert (HS : st_ok tfibsegs E0 SS_T (restrict (w_H W) (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfibsegs)))).
{ unfold SS_T, A_ialloc. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. unfold rSTK, rFLAG1. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ apply (region_ok_stack tfibsegs E0 _ 2 sp (- IAL_STK)); [rewrite E2; reflexivity | numconst; lia | lia |].
intros a Ha. apply apresent_writable; [numconst; lia | apply HPRES; exact Ha].
+ reg_intro. unfold TFIB_IAL_FLAG. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HF1].
- apply pairwise_disjoint_of_extents. unfold rSTK, rFLAG1, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite (ew_Ereg_nat regs [Z_to_bv 64 0] 2 2%bv eq_refl). fold sp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; lia.
- split; [|split; exact I]. cbn [IFF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ew_Ereg_nat regs [Z_to_bv 64 0] 2 2%bv eq_refl). fold sp.
replace (ew (Ereg regs [Z_to_bv 64 0]) aFW) with (Z_to_bv 64 0) by reflexivity. rewrite (unsigned_lit_small 0) by lia.
numconst. repeat split; first [lia | change (2 ^ 4) with 16; exact Hal]. }
srr_run_to_sh tfibtbl_rtF_ok HS 0x5dfac.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
assert (FR : forall x : word, ~ (sp - IAL_STK <= bv_unsigned x < sp) -> ms_mem msR x = mem x).
{ intros x Hx. apply (frame_of_outside E0 _ _ _ x HF). intros r Hr. cbn [ss_mem SS_T In] in Hr.
destruct Hr as [<-|[<-|[]]]; unfold rSTK, rFLAG1; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; [right; rewrite E2; fold sp; clear - Hx; lia | left; lia]. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { apply (regs_preserved_of_st_ok tfibsegs E0 _ _ regs [Z_to_bv 64 0] HS); [apply env_agree_refl | vm_compute; reflexivity]. }
split. { rreg HS (10%bv : bv 5) R10. rewrite R10. reflexivity. }
split. { intros x H1 _ _. apply FR. exact H1. }
split. { intros a Ha HP.
assert (D : (sp - IAL_STK <= a < sp) \/ ~ (sp - IAL_STK <= a < sp)) by lia. destruct D as [D|D].
- eapply (st_ok_window_apresent (w_H W) E0 _ _ 0 _ _ HS); [reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite E2; fold sp; clear - D; unfold IAL_STK in *; lia | clear - Ha; lia].
- apply (apresent_same (w_H W) mem); [apply FR; rewrite unsigned_lit_small by (clear - Ha; numconst; lia); exact D | exact HP]. }
assert (FRz : forall a, 0 <= a < TFIB_IMG_END -> ms_mem msR (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. apply FR. rewrite unsigned_lit_small by (clear - Ha; numconst; lia). clear - Ha Hsp; numconst; lia. }
split. { apply (val_mem_frame (w_H W) mem); [intros k Hk; apply FRz; clear - Hk; numconst; lia | exact HF1]. }
split. { apply (val_mem_frame (w_H W) mem); [intros k Hk; apply FRz; clear - Hk; numconst; lia | exact HF2]. }
split. { apply (val_mem_frame (w_H W) mem); [intros k Hk; apply FRz; clear - Hk; numconst; lia | exact HW1]. }
split. { apply (val_mem_frame (w_H W) mem); [intros k Hk; apply FRz; clear - Hk; numconst; lia | exact HW2]. }
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) mem (ms_mem msR) a); [apply HZ; exact Ha | apply FRz; clear - Ha; numconst; lia].
Qed.
Definition OUT (sp ux : Z) : Prop :=
~ (sp - IAL_STK <= ux < sp) /\ ~ (TFIB_IAL_LO <= ux < TFIB_IAL_HI) /\ ~ (TFIB_IAL_FLAG <= ux < TFIB_IAL_FLAG + 4).
Definition GAP (ux : Z) : Prop := 0xe7208 <= ux < 0xe7240.
Definition UNCH (sp ux : Z) : Prop := OUT sp ux \/ GAP ux.
Definition KEEPW (sp ux : Z) : Prop :=
~ (sp - IAL_STK <= ux < sp) /\ ~ (TFIB_IAL_FLAG <= ux < TFIB_IAL_FLAG + 4) /\ ~ (TFIB_IAL_LO <= ux < TFIB_IAL_LO + 8) /\ ~ (TFIB_IAL_W <= ux < TFIB_IAL_W + 16).
Definition INZ1 (ux : Z) : Prop := 0x128208 <= ux < 0x128230.
Definition INZ2 (ux : Z) : Prop := INZ1 ux \/ 0xa7208 <= ux < 0xe7208.
Definition INZ3 (ux : Z) : Prop := INZ2 ux \/ 0xe7240 <= ux < 0xe7fc0.
Definition INZ4 (ux : Z) : Prop := INZ3 ux \/ 0xe7fd0 <= ux < 0x128208.
Ltac frame_keep HF sp BV2 Hsp KW :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
assert (KW : forall x : word, KEEPW sp (bv_unsigned x) -> m' x = m x)
by (let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
intros x Hx; apply (frame_of_outside E rs m m' x HF); intros r Hr;
cbn [ss_mem SS_F2 ss_after_stretch In] in Hr; unfold rSTK, rFLAGW, rPSP, rPS, rLO, flit8 in Hr; unfold KEEPW in Hx;
repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; try rewrite BV2; clear - Hx Hsp; numconst; lia|]);
destruct Hr);
clear HF
end.
Lemma ialloc_fresh : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
YK0s.ret_ok (getr regs 1) ->
sp mod 16 = 0 -> TFIB_IMG_END <= sp - IAL_STK -> sp < 2 ^ 64 -> (forall a, sp - IAL_STK <= a < sp -> apresent H mem a) ->
val_mem tfibsegs m TFIB_IAL_FLAG 1 0 -> val_mem tfibsegs m (TFIB_IAL_FLAG + 1) 1 0 ->
val_mem tfibsegs m 0x9df78 8 0x135aa0 -> val_mem tfibsegs m 0x135aa0 8 4096 ->
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 TFIB_IAL_LO /\
(forall x : word, ~ (sp - IAL_STK <= bv_unsigned x < sp) -> ~ (TFIB_IAL_LO <= bv_unsigned x < TFIB_IAL_HI) ->
~ (TFIB_IAL_FLAG <= bv_unsigned x < TFIB_IAL_FLAG + 4) -> mem' x = mem x) /\
(forall a, TFIB_IMG_END <= a < 2 ^ 64 -> apresent H mem a -> apresent H mem' a) /\
let m' := mrestrict H mem' in
val_mem tfibsegs m' TFIB_IAL_FLAG 1 1 /\ val_mem tfibsegs m' (TFIB_IAL_FLAG + 1) 1 0 /\
val_mem tfibsegs m' TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m' (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0))).
Proof.
intros W regs mem md. cbv zeta. intros Hra Hal Hsp Hsp64 HPRES HF1 HF2 HPSP HPS HZ. pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
destruct (rw_mbyte W mem (TFIB_IAL_FLAG + 2) ltac:(numconst; lia)) as [b2 Hb2].
destruct (rw_mbyte W mem (TFIB_IAL_FLAG + 3) ltac:(numconst; lia)) as [b3 Hb3].
pose proof (bv_unsigned_in_range _ b2) as R2. pose proof (bv_unsigned_in_range _ b3) as R3.
unfold bv_modulus in R2, R3. change (2 ^ Z.of_N 8) with 256 in R2, R3.
set (h := bv_unsigned b2 + 256 * bv_unsigned b3). set (FW := 65536 * h).
pose proof (flagword_val _ _ b2 b3 HF1 HF2 Hb2 Hb3) as HFW. fold h in HFW. fold FW in HFW.
set (E0 := Ereg regs [Z_to_bv 64 FW]).
assert (E2 : ew E0 2 = getr regs 2) by (exact (ew_Ereg_nat regs [Z_to_bv 64 FW] 2 2%bv eq_refl)).
assert (E1 : ew E0 1 = getr regs 1) by (exact (ew_Ereg_nat regs [Z_to_bv 64 FW] 1 1%bv eq_refl)).
assert (E32 : ew E0 aFW = Z_to_bv 64 FW) by reflexivity.
assert (HS : st_ok tfibsegs E0 SS_F2 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfibsegs)))).
{ unfold SS_F2, A_ialloc. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. unfold rSTK, rFLAGW, rPSP, rPS, rLO, flit8.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
+ apply (region_ok_stack tfibsegs E0 _ 2 sp (- IAL_STK)); [rewrite E2; reflexivity | numconst; lia | lia |].
intros a Ha. apply apresent_writable; [numconst; lia | apply HPRES; exact Ha].
+ reg_intro. unfold TFIB_IAL_FLAG. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_writable; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ FW); [cbn [sv_denot]; rewrite E32, (unsigned_lit_small FW), Z.add_0_r by (subst FW h; lia); reflexivity | cbn; subst FW h; lia | cbn; lia | rewrite Z.add_0_l; exact HFW].
+ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HPSP].
+ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HPS].
+ reg_intro. unfold TFIB_IAL_LO. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_writable; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. apply HZ. left. numconst. lia.
- apply pairwise_disjoint_of_extents. unfold rSTK, rFLAGW, rPSP, rPS, rLO, flit8, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite (ew_Ereg_nat regs [Z_to_bv 64 FW] 2 2%bv eq_refl). fold sp. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; lia.
- split; [|split; exact I]. cbn [IFF2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ew_Ereg_nat regs [Z_to_bv 64 FW] 2 2%bv eq_refl). fold sp.
replace (ew (Ereg regs [Z_to_bv 64 FW]) aFW) with (Z_to_bv 64 FW) by reflexivity.
rewrite (unsigned_lit_small FW) by (subst FW h; lia).
numconst. repeat split; first [subst FW h; lia | change (2 ^ 4) with 16; exact Hal | change (2 ^ 16) with 65536; subst FW; rewrite Z.mul_comm; apply Z_mod_mult]. }
assert (R32 : rho_of E0 32%nat = 65536 * (bv_unsigned b2 + 256 * bv_unsigned b3)) by (unfold rho_of; change (ew E0 32) with (Z_to_bv 64 FW); apply unsigned_lit_small; subst FW h; lia).
srr_run_to_sh tfibtbl_rtF_ok HS 0x5de90. rename HF into HF_1. clear HFr.
pin32 HS (10%bv : bv 5) R2 R3 R32.
srr_run_to_sh tfibtbl_rtF_ok HS 0x5ded8. rename HF into HF_2. clear HFr.
pin32 HS (11%bv : bv 5) R2 R3 R32.
srr_run_to_sh tfibtbl_rtF_ok HS 0x5dee0. rename HF into HF_3. clear HFr.
pin32 HS (10%bv : bv 5) R2 R3 R32.
srr_run_to_sh tfibtbl_rtF_ok HS 0x63968. rename HF into HF_4. clear HFr.
assert (BV2_0 : bv_unsigned (ew E0 2) = sp) by (rewrite E2; reflexivity).
cbn [ss_mem SS_F2] in HF_1.
frame_keep HF_1 sp BV2_0 Hsp KW1. frame_keep HF_2 sp BV2_0 Hsp KW2. frame_keep HF_3 sp BV2_0 Hsp KW3. frame_keep HF_4 sp BV2_0 Hsp KW4.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms4 end.
assert (UK : forall ux, UNCH sp ux -> KEEPW sp ux) by (intros ux Hu; unfold UNCH, OUT, GAP, KEEPW in *; clear - Hu Hsp; numconst; lia).
assert (EQ4 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms4 x = mem x).
{ intros x Hx. rewrite (KW4 x (UK _ Hx)), (KW3 x (UK _ Hx)), (KW2 x (UK _ Hx)). exact (KW1 x (UK _ Hx)). }
clear KW1 KW2 KW3 KW4.
Local Ltac do_stretch HS k d len retpc BV2 Hsp Hsp64 :=
let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in let Q1 := fresh "Q1" in
rreg HS (10%bv : bv 5) Q10; rreg HS (11%bv : bv 5) Q11; rreg HS (12%bv : bv 5) Q12; rreg HS (1%bv : bv 5) Q1;
eapply (imemset_stretch _ k _ _ _ _ d len retpc);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| exact Q10 | exact Q11 | exact Q12 | exact Q1
| lia | lia | lia | reflexivity | lia
| let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; try rewrite BV2; clear - Hsp; numconst; lia|]); destruct Hr
| let r := fresh "r" in let Hr := fresh "Hr" in let a := fresh "a" in let Ha := fresh "Ha" in
intros r a Hr Ha; repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; try rewrite BV2 in Ha; clear - Hsp Hsp64 Ha; numconst; lia|]); destruct Hr
| clear Q10 Q11 Q12 Q1 HS ].
Local Ltac name_env HS E0 b2 b3 sp En HEn HEprev R32n R32 BV2n BV2_0 :=
lazymatch type of HS with st_ok _ ?E _ _ => set (En := E) in HS end;
assert (HEn : forall k, (k < 33)%nat -> ew En k = ew E0 k) by (intros k Hk; subst En; rewrite ew_havoc_old by lia; apply HEprev; exact Hk);
assert (R32n : rho_of En 32%nat = 65536 * (bv_unsigned b2 + 256 * bv_unsigned b3)) by (unfold rho_of; rewrite (HEn 32%nat ltac:(lia)); exact R32);
assert (BV2n : bv_unsigned (ew En 2) = sp) by (rewrite (HEn 2%nat ltac:(lia)); exact BV2_0).
assert (HE0 : forall k, (k < 33)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
do_stretch HS 33%nat 0x128208 40 0x5df04 BV2_0 Hsp Hsp64.
intros regs1 mem1 mat1 HS _ _ FR1 _ ZR1.
name_env HS E0 b2 b3 sp En1 HE1 HE0 R32_1 R32 BV2_1 BV2_0.
assert (EQ5 : forall x : word, UNCH sp (bv_unsigned x) -> mem1 x = mem x).
{ intros x Hx. rewrite (FR1 x) by (unfold UNCH, OUT, GAP in Hx; clear - Hx; numconst; lia). exact (EQ4 x Hx). }
assert (Z1 : forall x : word, INZ1 (bv_unsigned x) -> mem1 x = Some (Z_to_bv 8 0)) by (intros x Hx; apply ZR1; unfold INZ1 in Hx; exact Hx).
clear EQ4 FR1 ZR1.
srr_run_to_sh tfibtbl_rtF_ok HS 0x63968. clear HFr. frame_keep HF sp BV2_1 Hsp KW5.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms5 end.
assert (EQ6 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms5 x = mem x) by (intros x Hx; rewrite (KW5 x (UK _ Hx)); exact (EQ5 x Hx)).
assert (Z2 : forall x : word, INZ1 (bv_unsigned x) -> ms_mem ms5 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW5 x) by (unfold INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; lia). exact (Z1 x Hx). }
clear EQ5 Z1 KW5.
do_stretch HS 36%nat 0xa7208 262144 0x5df1c BV2_1 Hsp Hsp64.
intros regs2 mem2 mat2 HS _ _ FR2 _ ZR2.
name_env HS E0 b2 b3 sp En2 HE2 HE1 R32_2 R32 BV2_2 BV2_0.
assert (EQ7 : forall x : word, UNCH sp (bv_unsigned x) -> mem2 x = mem x).
{ intros x Hx. rewrite (FR2 x) by (unfold UNCH, OUT, GAP in Hx; clear - Hx; numconst; lia). exact (EQ6 x Hx). }
assert (Z3 : forall x : word, INZ2 (bv_unsigned x) -> mem2 x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct Hx as [Hx|Hx]; [|apply ZR2; exact Hx]. rewrite (FR2 x) by (unfold INZ1 in Hx; clear - Hx; lia). exact (Z2 x Hx). }
clear EQ6 Z2 FR2 ZR2.
srr_run_to_sh tfibtbl_rtF_ok HS 0x63968. clear HFr. frame_keep HF sp BV2_2 Hsp KW6.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms6 end.
assert (EQ8 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms6 x = mem x) by (intros x Hx; rewrite (KW6 x (UK _ Hx)); exact (EQ7 x Hx)).
assert (Z4 : forall x : word, INZ2 (bv_unsigned x) -> ms_mem ms6 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW6 x) by (unfold INZ2, INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; lia). exact (Z3 x Hx). }
clear EQ7 Z3 KW6.
do_stretch HS 39%nat 0xe7240 3456 0x5df34 BV2_2 Hsp Hsp64.
intros regs3 mem3 mat3 HS _ _ FR3 _ ZR3.
name_env HS E0 b2 b3 sp En3 HE3 HE2 R32_3 R32 BV2_3 BV2_0.
assert (EQ9 : forall x : word, UNCH sp (bv_unsigned x) -> mem3 x = mem x).
{ intros x Hx. rewrite (FR3 x) by (unfold UNCH, OUT, GAP in Hx; clear - Hx; numconst; lia). exact (EQ8 x Hx). }
assert (Z5 : forall x : word, INZ3 (bv_unsigned x) -> mem3 x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct Hx as [Hx|Hx]; [|apply ZR3; exact Hx]. rewrite (FR3 x) by (unfold INZ2, INZ1 in Hx; clear - Hx; lia). exact (Z4 x Hx). }
clear EQ8 Z4 FR3 ZR3.
srr_run_to_sh tfibtbl_rtF_ok HS 0x63968. clear HFr. frame_keep HF sp BV2_3 Hsp KW7.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms7 end.
assert (EQ10 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms7 x = mem x) by (intros x Hx; rewrite (KW7 x (UK _ Hx)); exact (EQ9 x Hx)).
assert (Z6 : forall x : word, INZ3 (bv_unsigned x) -> ms_mem ms7 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW7 x) by (unfold INZ3, INZ2, INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; lia). exact (Z5 x Hx). }
clear EQ9 Z5 KW7.
do_stretch HS 42%nat 0xe7fc0 262728 0x5df4c BV2_3 Hsp Hsp64.
intros regs4 mem4 mat4 HS _ _ FR4 _ ZR4.
name_env HS E0 b2 b3 sp En4 HE4 HE3 R32_4 R32 BV2_4 BV2_0.
assert (EQ11 : forall x : word, UNCH sp (bv_unsigned x) -> mem4 x = mem x).
{ intros x Hx. rewrite (FR4 x) by (unfold UNCH, OUT, GAP in Hx; clear - Hx; numconst; lia). exact (EQ10 x Hx). }
assert (Z7 : forall x : word, INZ4 (bv_unsigned x) -> mem4 x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct Hx as [Hx|Hx]; [|apply ZR4; clear - Hx; lia]. rewrite (FR4 x) by (unfold INZ3, INZ2, INZ1 in Hx; clear - Hx; lia). exact (Z6 x Hx). }
clear EQ10 Z6 FR4 ZR4.
srr_run_to_sh tfibtbl_rtF_ok HS 0x5df74. clear HFr. frame_keep HF sp BV2_4 Hsp KW8.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms8 end.
assert (EQ12 : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem ms8 x = mem x) by (intros x Hx; rewrite (KW8 x (UK _ Hx)); exact (EQ11 x Hx)).
assert (Z8 : forall x : word, INZ4 (bv_unsigned x) -> ms_mem ms8 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW8 x) by (unfold INZ4, INZ3, INZ2, INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; lia). exact (Z7 x Hx). }
clear EQ11 Z7 KW8.
apply (st_ok_add_region _ _ _ (YP09.mkRegion None TFIB_IAL_W (TFIB_IAL_W + 16) TFIB_IAL_W (TFIB_IAL_W + 16) [])) in HS;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
unfold TFIB_IAL_W; split; [lia|]; split; [lia|]; split; [intros o Ho; apply rw_writable; lia | constructor]
| cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite BV2_4; clear - Hsp; numconst; repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x5dfac. clear HFr. frame_keep HF sp BV2_4 Hsp KW9.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
assert (EQR : forall x : word, UNCH sp (bv_unsigned x) -> ms_mem msR x = mem x) by (intros x Hx; rewrite (KW9 x (UK _ Hx)); exact (EQ12 x Hx)).
assert (ZF : forall x : word, INZ4 (bv_unsigned x) -> ms_mem msR x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (KW9 x) by (unfold INZ4, INZ3, INZ2, INZ1 in Hx; unfold KEEPW; clear - Hx Hsp; numconst; lia). exact (Z8 x Hx). }
clear EQ12 Z8 KW9.
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W En4); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1. rewrite (HE4 1%nat ltac:(lia)), E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { apply (regs_preserved_of_st_ok tfibsegs En4 _ _ regs [Z_to_bv 64 FW] HS); [| vm_compute; reflexivity].
subst En4 En3 En2 En1 E0. repeat (apply env_agree_havoc_ge; [lia|]). apply env_agree_refl. }
split. { rreg HS (10%bv : bv 5) R10. rewrite R10. reflexivity. }
split. { intros x H1 H2 H3. apply EQR. left. exact (conj H1 (conj H2 H3)). }
split. { intros a Ha HP.
assert (D : (sp - IAL_STK <= a < sp) \/ ~ (sp - IAL_STK <= a < sp)) by lia. destruct D as [D|D].
- eapply (st_ok_window_apresent (w_H W) En4 _ _ 1 _ _ HS); [reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite BV2_4; clear - D; unfold IAL_STK in *; lia | clear - Ha; lia].
- apply (apresent_same (w_H W) mem); [|exact HP]. apply EQR. left. unfold OUT. rewrite unsigned_lit_small by (clear - Ha; numconst; lia). clear - Ha D; numconst; lia. }
split. { memv HS 2%nat 1%nat; [reflexivity | reflexivity | lia]. }
split. { memv HS 2%nat 0%nat; [reflexivity | reflexivity | lia]. }
split. { memv HS 0%nat 1%nat; [reflexivity | reflexivity | lia]. }
split. { memv HS 0%nat 0%nat; [reflexivity | reflexivity | numconst; lia]. }
intros a Ha.
assert (C : a = TFIB_IAL_LO \/ TFIB_IAL_LO + 1 <= a < TFIB_IAL_LO + 8 \/ GAP a \/ INZ4 a) by (unfold GAP, INZ4, INZ3, INZ2, INZ1; clear - Ha; numconst; lia).
destruct C as [->|[C|[C|C]]].
- pose proof (chunk_val_at (w_H W) En4 _ _ 5 0 _ _ 1%N _ 0 TFIB_IAL_LO HS eq_refl eq_refl eq_refl eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
specialize (V 0%nat ltac:(lia)). rewrite Z.add_0_r in V. exact V.
- eapply (st_ok_chunk_zero (w_H W) En4 _ _ 5 _ 1 _ _ a HS); [reflexivity | reflexivity | cbn [YP09.r_base base_val]; clear - C; numconst; lia].
- rewrite (mbyte_mrestrict_same (w_H W) mem (ms_mem msR) a) by (apply EQR; right; rewrite unsigned_lit_small by (clear - C; unfold GAP in C; lia); exact C).
apply HZ. left. unfold GAP in C. clear - C. numconst. lia.
- unfold mbyte, mrestrict. rewrite (rw_unhidden W a) by (unfold INZ4, INZ3, INZ2, INZ1 in C; clear - C; lia).
rewrite (ZF (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by (unfold INZ4, INZ3, INZ2, INZ1 in C; clear - C; lia); exact C). reflexivity.
Qed.
Theorem tfib_ialloc_ok : tfib_ialloc_spec.
Proof.
unfold tfib_ialloc_spec. intros W regs mem md ii. cbv zeta. intros Hra Hal Hsp Hsp64 HPRES HF1 HF2 HPSP HPS HW HZ.
destruct ii.
- destruct HW as [HW1 HW2]. exact (ialloc_inited W regs mem md Hra Hal Hsp Hsp64 HPRES HF1 HF2 HW1 HW2 HZ).
- exact (ialloc_fresh W regs mem md Hra Hal Hsp Hsp64 HPRES HF1 HF2 HPSP HPS HZ).
Qed.
End b.
