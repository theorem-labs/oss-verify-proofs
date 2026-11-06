(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of __asan_stack_free_5 (0x40190) of plugin-hostd/fuzz_command's ASan build against astack_free_cls_realizes, built from cgif_rgb_fuzzer's lib/YF3h.v (entry state, frame and flag regions, closing through astack_free_law_ok) and cgif_file_fuzzer's lib/A/AF0r.v and AF0s.v (a second symbolic phase over a fresh shadow-pointer atom and the read-out of its stores), over the asan-state definitions of the cgif_file_fuzzer proof as plugin-hostd/fuzz_command holds them: one image; class 5; the 32 stores of the .rodata word 0x10340 in place of the memset tail; module names; TfxSyms becomes CmdBSyms. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AB1w AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtStack.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtSM1T.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* Measured on the pinned fuzz_command.asan: 45 instructions, no branch of their own.
     0x40190 addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp); ld a1,2040(a0) (the flag pointer at frame + 2048 - 8);
     li s0,0; sb zero,0(a1); jal 0x40410 (a0 := (a0 >> 3) + the shadow base read through GOT 0xa63f0);
     auipc a1; ld a1,404(a1) (the .rodata word 0x10340 = 0xf5f5f5f5f5f5f5f5); 32 x sd a1,8k(a0), k = 0..31
     (0x401b4..0x40230: 256 shadow bytes = fs_frame_bytes 5 / 8); ld ra; ld s0; addi sp,sp,16; ret (0x40240).
   a1 (the size) is overwritten by the flag load before any use.
   Phase 1 runs from the entry to the first store, which names the shadow pointer the helper returned; phase 2
   gives that pointer a fresh atom with its 256-byte region and runs the stores to the ret. *)

Definition SF_ENTRY : Z := 0x40190.
Definition SF_SDSH : Z := 0x401b4.
Definition SF_RET : Z := 0x40240.
Definition FS_B : Z := 2048.
Definition SF_WIN : Z := 16.
Definition F5W : Z := 0xf5f5f5f5f5f5f5f5.
Definition sf_ranges : list (Z * nat) := [(0x40190, 45%nat); (0x40410, 28%nat)].
Definition tbl_sf : ctable := Eval vm_compute in build_ranges sf_ranges TEmpty.
Lemma tbl_sf_eq : tbl_sf = build_ranges sf_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_sf). Qed.
Lemma tbl_sf_ok : table_ok tfibsegs tbl_sf.
Proof. rewrite tbl_sf_eq. apply build_ranges_ok; [unfold sf_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)]. Qed.
Definition sf_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
[(0xa63e8, 40, [(0, 8%N, 0xae8b8); (8, 8%N, 0xb10b8); (16, 8%N, 0xb1da8); (24, 8%N, 0xb1db0); (32, 8%N, 0xb1da0)]);
(0xb10b8, 8, [(0, 8%N, 0x7fff8000)]); (0xb1da0, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0x10340, 8, [(0, 8%N, 0xf5f5f5f5f5f5f5f5)])].
Lemma sf_rodata_chk : forall ly, rodata_chk ly sf_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition aFLG : nat := 32.
Definition aSH : nat := 33.
Definition stk : YP09.region := YP09.mkRegion (Some 2%nat) (- SF_WIN) 0 (- SF_WIN) 0 [].
Definition rFF : YP09.region := YP09.mkRegion (Some 10%nat) (FS_B - 8) FS_B (FS_B - 8) (FS_B - 8) [YP09.mkChunk (FS_B - 8) (CVal 8 (SOff aFLG 0))].
Definition rFLG : YP09.region := YP09.mkRegion (Some aFLG) 0 1 0 1 [].
Definition rSH : YP09.region := YP09.mkRegion (Some aSH) 0 (FS_B / 8) 0 (FS_B / 8) [].
Definition ffLO (hi : bool) : Z := if hi then kHighMemBeg else 4096.
Definition ffHI (hi : bool) : Z := if hi then CEIL_MAX - FS_B else kLowShadowBeg - FS_B.
Definition shLO (hi : bool) : Z := if hi then kHighShadowBeg else kLowShadowBeg + TFIB_IMG_END / 8.
Definition shHI (hi : bool) : Z := if hi then kHighShadowEnd - FS_B / 8 else kLowShadowEnd - FS_B / 8.
Definition sf_facts (hi : bool) : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + SF_WIN) kHighMemEnd 4); (10%nat, mkAF (ffLO hi) (ffHI hi) 5); (aFLG, mkAF 4096 (CEIL_MAX - 1) 0)].
Definition sf_mem : smem := stk :: rFF :: rFLG :: map ro_region sf_rodata.
Definition ss0 (hi : bool) : sstate := mkSS SF_ENTRY sr_atoms sf_mem None (mkFacts (sf_facts hi) [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_sf FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition a0e : sv := SAlu ALU_ADD (SLit SHADOW_OFF) (SAlu ALU_SRL (SOff 10 0) (SLit 3)).
(* Phase 1: entry to the first shadow store. *)
Definition eH : sstate := Eval vm_compute in fst (RUN (ss0 true)).
Definition stH : run_status := Eval vm_compute in snd (RUN (ss0 true)).
Definition eL : sstate := Eval vm_compute in fst (RUN (ss0 false)).
Definition stL : run_status := Eval vm_compute in snd (RUN (ss0 false)).
Definition e1 (hi : bool) : sstate := if hi then eH else eL.
Definition st1 (hi : bool) : run_status := if hi then stH else stL.
Lemma r_1 : forall hi, RUN (ss0 hi) = (e1 hi, st1 hi). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma st1_match : forall hi (A : Type) (x y : A), match st1 hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma P1_facts : forall hi, ss_pc (e1 hi) = SF_SDSH /\ ss_resv (e1 hi) = None /\ ss_atoms_lt 34 (e1 hi) = true /\
reg_is (e1 hi) 10 a0e = true /\ match st1 hi with RS_stopped (SR_addr _) => True | _ => False end.
Proof. intros [|]; vm_compute; repeat split; reflexivity || exact I. Qed.
Definition memE : smem := Eval vm_compute in ss_mem eH.
Lemma e1_mem : forall hi, ss_mem (e1 hi) = memE. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma memE_split : memE = nth 0 memE stk :: tl memE. Proof. vm_compute. reflexivity. Qed.
(* Phase 2: the 32 stores over the shadow pointer, now the atom aSH. *)
Definition memC2 : smem := nth 0 memE stk :: rSH :: tl memE.
Definition preC2 (hi : bool) : sstate :=
RtSM1T.add_fact (mkSS (ss_pc (e1 hi)) (sr_sets (ss_regs (e1 hi)) [((10%bv : bv 5), SOff aSH 0)]) memC2 None (ss_facts (e1 hi))) aSH (mkAF (shLO hi) (shHI hi) 0).
Definition ssC2H : sstate := Eval vm_compute in preC2 true.
Definition ssC2L : sstate := Eval vm_compute in preC2 false.
Definition ssC2 (hi : bool) : sstate := if hi then ssC2H else ssC2L.
Lemma ssC2_eq : forall hi, preC2 hi = ssC2 hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition eC2H : sstate := Eval vm_compute in fst (RUN ssC2H).
Definition stC2H : run_status := Eval vm_compute in snd (RUN ssC2H).
Definition eC2L : sstate := Eval vm_compute in fst (RUN ssC2L).
Definition stC2L : run_status := Eval vm_compute in snd (RUN ssC2L).
Definition eC2 (hi : bool) : sstate := if hi then eC2H else eC2L.
Definition stC2 (hi : bool) : run_status := if hi then stC2H else stC2L.
Lemma r_C2 : forall hi, RUN (ssC2 hi) = (eC2 hi, stC2 hi). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma stC2_match : forall hi (A : Type) (x y : A), match stC2 hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma C2_facts : forall hi, stC2 hi = RS_stopped (SR_jalr (SOff 1 0)) /\ ss_resv (eC2 hi) = None /\ ss_pc (eC2 hi) = SF_RET /\
forallb (fun r => reg_is (eC2 hi) r (SOff (Z.to_nat r) 0)) [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Definition rSTK2 : YP09.region := Eval vm_compute in nth 0 (ss_mem eC2H) stk.
Definition rSH2 : YP09.region := Eval vm_compute in nth 1 (ss_mem eC2H) stk.
Definition rFLG2 : YP09.region := Eval vm_compute in nth 3 (ss_mem eC2H) stk.
Lemma eC2_regions : forall hi, nth_error (ss_mem (eC2 hi)) 0 = Some rSTK2 /\ nth_error (ss_mem (eC2 hi)) 1 = Some rSH2 /\
nth_error (ss_mem (eC2 hi)) 3 = Some rFLG2.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma rSTK2_shape : YP09.r_base rSTK2 = Some 2%nat /\ YP09.r_wlo rSTK2 = - SF_WIN /\ YP09.r_whi rSTK2 = 0. Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rSH2_shape : YP09.r_base rSH2 = Some aSH /\ YP09.r_wlo rSH2 = 0 /\ YP09.r_whi rSH2 = FS_B / 8 /\
forall j, (j < 32)%nat -> nth_error (YP09.r_chunks rSH2) j = Some (YP09.mkChunk (FS_B / 8 - 8 - 8 * Z.of_nat j) (CVal 8 (SLit F5W))).
Proof. vm_compute. repeat split; try reflexivity. intros j Hj. do 32 (destruct j as [|j]; [reflexivity|]). lia. Qed.
Lemma rFLG2_shape : YP09.r_base rFLG2 = Some aFLG /\ YP09.r_wlo rFLG2 = 0 /\ YP09.r_whi rFLG2 = 1 /\
nth_error (YP09.r_chunks rFLG2) 0 = Some (YP09.mkChunk 0 (CVal 1 (SLit 0))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rSH2_chunk : forall q, 0 <= q < 32 -> In (YP09.mkChunk (8 * q) (CVal 8 (SLit F5W))) (YP09.r_chunks rSH2).
Proof.
intros q Hq.
assert (Hc : exists j, (j < 32)%nat /\ q = 32 - 1 - Z.of_nat j) by (exists (Z.to_nat (32 - 1 - q)); split; lia).
destruct Hc as (j & Hj & ->). pose proof (proj2 (proj2 (proj2 rSH2_shape)) j Hj) as X.
replace (8 * (32 - 1 - Z.of_nat j)) with (FS_B / 8 - 8 - 8 * Z.of_nat j) by (change (FS_B / 8) with 256; lia).
exact (nth_error_In _ _ X).
Qed.
Lemma le_byte_F5W : forall k, (k < 8)%nat -> YG0f.le_byte F5W 8 k = 0xf5.
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.
Lemma mem0_windows : forall hi E a, in_wrange E (ss_mem (ss0 hi)) a ->
(bv_unsigned (ew E 2) + - SF_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 32) + 0 <= a < bv_unsigned (ew E 32) + 1).
Proof.
intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
destruct zhi; vm_compute in Ht; repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; exact Hw | exfalso; lia] |]); destruct Ht.
Qed.
Lemma memC2_windows : forall hi E a, in_wrange E (ss_mem (ssC2 hi)) a ->
(bv_unsigned (ew E 2) + - SF_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 33) + 0 <= a < bv_unsigned (ew E 33) + FS_B / 8) \/
(bv_unsigned (ew E 32) + 0 <= a < bv_unsigned (ew E 32) + 1).
Proof.
intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
destruct zhi; vm_compute in Ht; repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; exact Hw | exfalso; lia] |]); destruct Ht.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma a0e_denot : forall E FF, bv_unsigned (ew E 10) = FF -> 0 <= FF < 2 ^ 64 -> sv_denot E a0e = Z_to_bv 64 (SHADOW_OFF + FF / 8).
Proof.
intros E FF HFF Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a0e)). f_equal.
change (bv_unsigned (sv_denot E a0e)) with (U E a0e). rewrite (U_zev E a0e) by (vm_compute; reflexivity).
unfold a0e. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, !Z.add_0_r. change (Z.land (zcanon 3) 63) with 3. change (zcanon SHADOW_OFF) with SHADOW_OFF.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold SHADOW_OFF.
pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound FF 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small FF) by lia. rewrite (zcanon_small (FF / 8)) by lia. apply zcanon_small. lia.
Qed.
Lemma sf_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_sf FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_sf tbl_sf_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
Theorem tfib_stack_free_5 : astack_free_cls_realizes tfibsegs B SF_ENTRY 5.
Proof.
intros ly S W regs mem md pos n HPRE Hin G10 G11 HTR.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx.
set (H := w_H W) in *. set (sp0 := spZ regs) in *.
change (fs_frame_bytes 5) with 2048 in *. change (2048 / 8) with 256.
pose proof (proj1 HAR) as M.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))) as IMG.
assert (ZF : zone3 (ly_F ly) kFakeStackSize).
{ pose proof (proj1 (Forall_forall _ _) (lo_app ly HLY) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as IA. cbv beta in IA.
assert (D9 : zdisjoint (ly_F ly, kFakeStackSize) (ly_img ly)).
{ pose proof (lo_disj ly HLY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) (ly_F ly, kFakeStackSize) (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD ltac:(apply in_app_iff; left; unfold owned_extents; cbn; tauto) ltac:(left; reflexivity)). }
exact (zone3_intro ly (ly_F ly) kFakeStackSize IMG ltac:(unfold kFakeStackSize; lia) IA D9). }
destruct ZF as (HF1 & HF2 & HFz).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. pose proof CR as CR0. unfold YG0f.ASAN_CEIL in CR0.
unfold ASAN_CEIL, kFakeStackSize in HF1, HF2.
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in HFz.
assert (ZONE : exists hi : bool, if hi then 17594333495296 <= ly_F ly /\ ly_F ly + 11571200 <= alloc_ceiling else 6316032 <= ly_F ly /\ ly_F ly + 11571200 <= 2147446784).
{ destruct HFz as [X|[X|X]]; [exfalso; clear - X HF1; lia | exists false; exact X | exists true; exact X]. }
destruct ZONE as [hi HZ].
assert (HPOS : 0 <= pos < 512).
{ pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf B ly S _ M))) (5, pos) Hin) as [_ X]. cbn [fst snd] in X. exact X. }
set (fa := frame_addr ly 5 pos) in *. set (fl := flag_addr ly 5 pos) in *.
assert (Efa : fa = ly_F ly + 5279744 + pos * 2048).
{ unfold fa, frame_addr, fs_frame_off. change kFakeFramesOff with 36864. change (Z.shiftl 1 kStackSizeLog) with 1048576. change (fs_frame_bytes 5) with 2048. lia. }
assert (Efl : fl = ly_F ly + 35840 + pos).
{ unfold fl, flag_addr, fs_flag_off. change kFakeFlagsOff with 4096. change (fs_flags_off 5) with 31744. lia. }
destruct (al_frames _ _ LAWS ly S W mem md 5 pos HAR Hin) as (Hal32 & _ & Hfr & Hsh). fold fa in Hal32, Hfr, Hsh. change (fs_frame_bytes 5) with 2048 in Hfr, Hsh. change (2048 / 8) with 256 in Hsh.
destruct (al_flag _ _ LAWS ly S W mem md 5 pos HAR Hin) as (Hflp & Hflo & _ & _). fold fl in Hflp, Hflo.
pose proof (lo_stk_ceil ly HLY) as SC. unfold ASAN_CEIL in SC.
assert (RFA : 6316032 <= ly_F ly /\ ly_F ly + 11571200 <= alloc_ceiling) by (destruct hi; lia).
assert (Hsp : kHighMemBeg + 4096 <= sp0 <= 2 ^ 47 /\ alloc_ceiling + 4096 <= sp0) by (unfold kHighMemBeg, kHighMemEnd, sp0 in *; lia).
assert (Hsp' : 17594333499392 <= sp0) by (unfold kHighMemBeg in Hsp; lia).
set (sh := shadow_addr fa) in *.
assert (Hfa8m : fa mod 8 = 0).
{ pose proof (Z.div_mod fa 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (fa / 32)) with ((4 * (fa / 32)) * 8) by lia. apply Z_mod_mult. }
assert (Hfa8d : fa = 8 * (fa / 8)) by (pose proof (Z.div_mod fa 8 ltac:(lia)); lia).
assert (Esh : sh = SHADOW_OFF + fa / 8) by reflexivity. unfold SHADOW_OFF in Esh.
assert (HSHr : shLO hi <= sh <= shHI hi).
{ rewrite Esh. unfold shLO, shHI, FS_B, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFIB_IMG_END.
change (2048 / 8) with 256. change (6316032 / 8) with 789504.
clear - HZ Efa Hfa8d HPOS CR0. destruct hi; cbn -[Z.div Z.add Z.sub Z.mul]; lia. }
assert (HSHe : 2148213760 <= sh /\ sh + 256 <= 17594333495296).
{ clear - HSHr. unfold shLO, shHI, FS_B, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFIB_IMG_END in HSHr.
change (2048 / 8) with 256 in HSHr. change (6316032 / 8) with 789504 in HSHr. destruct hi; cbn -[Z.div Z.add Z.sub Z.mul] in HSHr; lia. }
assert (HSHF : sh + 256 <= ly_F ly \/ ly_F ly + 11571200 <= sh).
{ rewrite Esh. clear - HZ Efa Hfa8d HPOS CR0. destruct hi; [left | right]; lia. }
set (E := Ereg regs [w64 fl; w64 sh]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = fa) by (rewrite (EEreg 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 fl) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = fl) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = w64 sh) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (U33 : bv_unsigned (ew E 33) = sh) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS0 : st_ok tfibsegs E (ss0 hi) (restrict H (mkst regs (Z_to_bv 64 SF_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss0, sf_mem. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 fl; w64 sh]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- change (stk :: rFF :: rFLG :: map ro_region sf_rodata) with ([stk; rFF; rFLG] ++ map ro_region sf_rodata).
apply Forall_app. split; [|exact (rodata_ok B TB sf_rodata ly S H mem E (sf_rodata_chk ly) M)].
repeat apply Forall_cons; try apply Forall_nil.
+ unfold stk, SF_WIN. apply (region_ok_stack tfibsegs E _ 2 sp0 (- 16)); [exact E2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. fold sp0. lia.
+ unfold rFF, aFLG, FS_B, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E10.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ fa (2048 - 8) 8%N (SOff 32 0) fl); [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
replace (fa + (2048 - 8)) with (fa + 2048 - 8) by lia. exact (AE2y.val_mem_of_rdword H mem _ _ HTR).
+ unfold rFLG, aFLG, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. replace (fl + o) with fl by lia. exact (AE2y.apresent_writable H mem fl Hflp).
- apply pairwise_disjoint_of_extents. unfold stk, rFF, rFLG, aFLG, sf_rodata, ro_region, extent_of_region, SF_WIN, FS_B.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E10, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok sf_facts]. unfold afact_ok, aFLG. cbn [af_lo af_hi af_al2].
rewrite E2, E10, U32. unfold ffLO, ffHI, SF_WIN, FS_B, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | exact Hal32 | apply Z.mod_1_r | destruct hi; lia]. }
idtac "CHECKPOINT-1".
unfold cfg_at. change (w64 SF_ENTRY) with (Z_to_bv 64 SF_ENTRY).
eapply SRr_bind; [apply (sf_phase W E _ _ _ _ _ HS0 (r_1 hi))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & HFrm1). rewrite (st1_match hi) in HS1.
assert (MEQ1 : forall z : word, ~ (sp0 - 16 <= bv_unsigned z < sp0) -> bv_unsigned z <> fl -> ms_mem ms1 z = mem z).
{ intros z Hz1 Hz2. apply HFm1. intros Hw. destruct (mem0_windows hi E _ Hw) as [Hw'|Hw']; [rewrite E2 in Hw'; unfold SF_WIN in Hw'; lia | rewrite U32 in Hw'; lia]. }
clear HFm1 HFrm1.
pose proof (P1_facts hi) as (PC1 & RV1 & AT1 & R10P & _).
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS1 RV1) as Hshape1. rewrite PC1 in Hshape1. rewrite Hshape1. rewrite Hshape1 in HS1. clear Hshape1.
assert (RD1 : forall (r : bv 5) v, reg_is (e1 hi) (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H E (e1 hi) (mkst (ms_regs ms1) (Z_to_bv 64 SF_SDSH) (ms_mem ms1) (seg_rom tfibsegs)) r HS1). }
pose proof (RD1 10%bv a0e R10P) as G10'. rewrite (a0e_denot E fa E10 ltac:(lia)) in G10'. unfold SHADOW_OFF in G10'. rewrite <- Esh in G10'.
rewrite restrict_mkst_fx in HS1.
assert (SHP : forall i, 0 <= i < 256 -> apresent H (ms_mem ms1) (sh + i) /\ ~ aowned B ly S (sh + i)).
{ intros i Hi. destruct (Hsh i Hi) as [HP HO]. split; [|exact HO].
apply (apresent_same H mem); [|exact HP]. apply MEQ1; rewrite unsigned_lit_small by lia; [lia|].
intros Heq. rewrite Heq in HO. exact (HO Hflo). }
assert (HSC2 : st_ok tfibsegs E (ssC2 hi) (restrict H (mkst (ms_regs ms1) (Z_to_bv 64 SF_SDSH) (ms_mem ms1) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- (ssC2_eq hi). unfold preC2. rewrite PC1.
apply RtSM1T.st_ok_add_fact; [| reflexivity | unfold aSH; rewrite U33; exact HSHr].
apply (st_ok_set_regs_mem tfibsegs 34 E E (e1 hi) (ms_regs ms1) (ms_regs ms1) (Z_to_bv 64 SF_SDSH) SF_SDSH (mrestrict H (ms_mem ms1)) (mrestrict H (ms_mem ms1)) memC2 [((10%bv : bv 5), SOff aSH 0)] HS1).
- split; [intros; reflexivity | reflexivity].
- exact AT1.
- vm_compute. reflexivity.
- intros r Hr. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G10'. cbn [sv_denot]. unfold aSH. rewrite U33, Z.add_0_r. reflexivity.
- pose proof (st_ok_mem_ok tfibsegs E (e1 hi) _ HS1) as (WF1 & ROK1 & PD1).
rewrite (e1_mem hi), memE_split in ROK1.
split; [vm_compute; reflexivity|]. split.
+ unfold memC2. apply Forall_cons; [exact (Forall_inv ROK1)|]. apply Forall_cons; [|exact (Forall_inv_tail ROK1)].
unfold rSH, aSH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
change (FS_B / 8) with 256. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (AF0x.apresent_writable H); [unfold TFIB_IMG_END; lia|]. exact (proj1 (SHP o ltac:(lia))).
+ apply pairwise_disjoint_of_extents. let l' := eval vm_compute in memC2 in change memC2 with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?E2, ?E10, ?U32, ?U33.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hsp Hsp' Efa Efl HPOS RFA HSHe HSHF CR0. repeat split; lia. }
idtac "CHECKPOINT-2".
eapply SRr_bind; [apply (sf_phase W E (ssC2 hi) _ _ _ _ HSC2 (r_C2 hi))|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HFm2 & HFrm2). rewrite ?wvb_wvb in *. rewrite (stC2_match hi) in HS2.
assert (MEQ2 : forall z : word, ~ (sp0 - 16 <= bv_unsigned z < sp0) -> ~ (sh <= bv_unsigned z < sh + 256) -> bv_unsigned z <> fl ->
ms_mem ms2 z = ms_mem ms1 z).
{ intros z Hz1 Hz2 Hz3. apply HFm2. intros Hw. destruct (memC2_windows hi E _ Hw) as [Hw'|[Hw'|Hw']];
[rewrite E2 in Hw'; unfold SF_WIN in Hw'; lia | rewrite U33 in Hw'; change (FS_B / 8) with 256 in Hw'; lia | rewrite U32 in Hw'; lia]. }
clear HFm2 HFrm2.
assert (MEQ : forall z : word, ~ (sp0 - 16 <= bv_unsigned z < sp0) -> ~ (sh <= bv_unsigned z < sh + 256) -> bv_unsigned z <> fl ->
ms_mem ms2 z = mem z).
{ intros z Hz1 Hz2 Hz3. rewrite (MEQ2 z Hz1 Hz2 Hz3). exact (MEQ1 z Hz1 Hz3). }
clear MEQ2.
pose proof (C2_facts hi) as (ST2 & RV2 & PC2 & FB2).
eapply (SRr_ret_at tfibsegs tbl_sf tbl_sf_ok Hwx W E); [exact HS2 | exact RV2 | rewrite PC2; vm_compute; reflexivity |].
intros mat'. rewrite ?wvb_wvb.
idtac "CHECKPOINT-3".
assert (RD2 : forall (r : bv 5) v, reg_is (eC2 hi) (bv_unsigned r) v = true -> getr (ms_regs ms2) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E (eC2 hi) ms2 r HS2). }
assert (RK2 : forall rz, In rz [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms2) (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. rewrite forallb_forall in FB2. specialize (FB2 rz Hrz). cbn beta in FB2.
assert (Hr32 : 0 <= rz < 32) by (clear - Hrz; cbn in Hrz; lia).
assert (U5 : bv_unsigned (Z_to_bv 5 rz) = rz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
rewrite (RD2 (Z_to_bv 5 rz) (SOff (Z.to_nat rz) 0)); [| rewrite U5; exact FB2].
cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (RK2 1 ltac:(cbn; tauto)) as Q1. replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
replace (v_jalr (getr (ms_regs ms2) 1) 0) with (w64 (raZ regs)) by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|]. exists (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
pose proof (st_ok_mem_ok tfibsegs E (eC2 hi) _ HS2) as (_ & ROK2 & _). change (ms_mem (restrict H ms2)) with (mrestrict H (ms_mem ms2)) in ROK2.
destruct (eC2_regions hi) as (NR0 & NR1 & NR3).
pose proof (proj1 (Forall_forall _ _) ROK2 _ (nth_error_In _ _ NR1)) as OKSH.
pose proof (proj1 (Forall_forall _ _) ROK2 _ (nth_error_In _ _ NR3)) as OKFLG.
unfold region_ok in OKSH, OKFLG.
destruct rSH2_shape as (BSH & WSH1 & WSH2 & _). destruct rFLG2_shape as (BFL & WFL1 & WFL2 & CFL).
rewrite BSH in OKSH. rewrite BFL in OKFLG. cbn [base_val] in OKSH, OKFLG.
unfold aSH in OKSH. unfold aFLG in OKFLG. rewrite U33 in OKSH. rewrite U32 in OKFLG.
destruct OKSH as (_ & _ & _ & CHSH). destruct OKFLG as (_ & _ & _ & CHFL).
assert (VMFL : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (fl + 0) 1 0).
{ apply (val_of_chunk_ok tfibsegs E _ fl 0 1%N (SLit 0) 0 (proj1 (Forall_forall _ _) CHFL _ (nth_error_In _ _ CFL)) eq_refl); cbn; lia. }
assert (FL2 : aview tfibsegs H (ms_mem ms2) fl = Some 0).
{ pose proof (RtSM1T.aview_of_val_mem H (ms_mem ms2) _ 1 _ 0 VMFL ltac:(lia)) as X. rewrite !Z.add_0_r in X. exact X. }
assert (ZSH : forall i, 0 <= i < 256 -> aview tfibsegs H (ms_mem ms2) (sh + i) = Some 0xf5).
{ intros i Hi. pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
pose proof (rSH2_chunk (i / 8) ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])) as HC.
pose proof (val_of_chunk_ok tfibsegs E _ sh (8 * (i / 8)) 8%N (SLit F5W) F5W (proj1 (Forall_forall _ _) CHSH _ HC) eq_refl ltac:(unfold F5W; cbn; lia) ltac:(cbn; lia)) as VM.
pose proof (RtSM1T.aview_of_val_mem H (ms_mem ms2) _ 8 F5W (Z.to_nat (i mod 8)) VM ltac:(lia)) as X.
rewrite Z2Nat.id in X by lia. replace (sh + 8 * (i / 8) + i mod 8) with (sh + i) in X by lia. rewrite X.
rewrite le_byte_F5W by lia. reflexivity. }
assert (PW : forall b, (sp0 - 16 <= b < sp0 \/ sh <= b < sh + 256 \/ fl <= b < fl + 1) -> apresent H (ms_mem ms2) b).
{ intros b Hb. destruct rSTK2_shape as (BS0 & WS01 & WS02).
destruct Hb as [Hb|[Hb|Hb]].
- apply (st_ok_window_apresent H E (eC2 hi) ms2 0 rSTK2 b HS2 NR0); [rewrite BS0, WS01, WS02; cbn [base_val]; rewrite E2; unfold SF_WIN; lia | unfold TFIB_IMG_END; lia].
- apply (st_ok_window_apresent H E (eC2 hi) ms2 1 rSH2 b HS2 NR1); [rewrite BSH, WSH1, WSH2; cbn [base_val]; unfold aSH; rewrite U33; change (FS_B / 8) with 256; lia | unfold TFIB_IMG_END; lia].
- apply (st_ok_window_apresent H E (eC2 hi) ms2 3 rFLG2 b HS2 NR3); [rewrite BFL, WFL1, WFL2; cbn [base_val]; unfold aFLG; rewrite U32; lia | unfold TFIB_IMG_END; lia]. }
assert (AVQ : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 16 <= a < sp0 \/ sh <= a < sh + 256 \/ fl <= a < fl + 1) ->
aview tfibsegs H (ms_mem ms2) a = aview tfibsegs H mem a).
{ intros a Ha Hn. apply aview_same. apply MEQ; rewrite unsigned_lit_small by exact Ha; clear - Hn; lia. }
idtac "CHECKPOINT-4".
split; [|split; [|split; [|split; [|split]]]].
-
apply (astack_free_law_ok tfibsegs B ly S W mem md (ms_mem ms2) _ 5 pos HAR Hin).
all: change (w_H W) with H.
+ exact FL2.
+ intros a Hr Hown Hnf. apply AVQ; [exact Hr|]. intros [Hs|[Hs|Hs]].
* exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
* replace a with (sh + (a - sh)) in Hown by lia. exact (proj2 (Hsh (a - sh) ltac:(lia)) Hown).
* apply Hnf. lia.
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms2) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *. clearbody a'.
assert (CS : (sp0 - 16 <= a' < sp0 \/ sh <= a' < sh + 256 \/ fl <= a' < fl + 1) \/
~ (sp0 - 16 <= a' < sp0 \/ sh <= a' < sh + 256 \/ fl <= a' < fl + 1)) by (clear; lia).
destruct CS as [CS|CS]; [apply aview_some_of_apresent; apply PW; exact CS | rewrite (AVQ a' Hr CS); exact Hv].
+ apply MF. + apply MF. + apply MF.
+ intros a Hb Hh0. assert (Hh : H (Z_to_bv 64 a) = true) by exact Hh0. clear Hh0. pose proof (AE2y.in_band_rw_u64 a Hb) as Hr.
unfold w64. apply MEQ; rewrite unsigned_lit_small by lia.
* intros Ha. destruct (PW a ltac:(left; exact Ha)) as [Hh' _]. rewrite Hh' in Hh. discriminate.
* intros Ha. destruct (PW a ltac:(right; left; exact Ha)) as [Hh' _]. rewrite Hh' in Hh. discriminate.
* intros ->. pose proof (proj1 Hflp) as Hf0. unfold H in Hh, Hf0. rewrite Hf0 in Hh. discriminate.
-
intros r Hr. apply RK2. unfold acallee_saved in Hr. clear - Hr. cbn. lia.
-
apply with_vm_backing_same.
-
intros i Hi. fold sh. exact (ZSH i Hi).
-
intros a Ha Hs Hnf Hstk. fold sh in Hs. apply AVQ; [exact Ha|]. intros [Hq|[Hq|Hq]].
+ fold sp0 in Hstk. rewrite HES in Hstk. lia.
+ apply Hs. lia.
+ apply Hnf. lia.
-
intros a Ha. fold sp0 in Ha. rewrite HES in Ha. destruct (Z_lt_le_dec a (sp0 - 16)) as [L|L]; [|apply PW; left; lia].
destruct (HpresE a ltac:(fold sp0; lia)) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
rewrite MEQ; [exact Hb | | |]; rewrite unsigned_lit_small by lia; [lia | lia |].
intros ->. exact (al_stack _ _ LAWS ly S W mem md fl HAR ltac:(unfold sp0 in *; lia) Hflo).
Qed.
End d.
Theorem cmd_stack_free5_contract : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B -> astack_free_cls_realizes tfibsegs B 0x40190 5.
Proof. intros B LAWS TB. exact (tfib_stack_free_5 B LAWS TB). Qed.
End c.
