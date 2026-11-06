(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of __asan_stack_free_7 (0x403c0) of plugin-hostd/fuzz_command's ASan build, over the asan-state definitions and the musl memset walk of the cgif_file_fuzzer proof as plugin-hostd/fuzz_command holds them: one image instead of the two-image selector; addresses, data words and the image-end bound; module names; TfxSyms becomes CmdBSyms; the theorem is named cmd_stack_free7_contract. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AB1w AE34 AF0l AF0m AF0x AE2y AE3d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtStack.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* Measured on the pinned fuzz_command.asan: 20 instructions, no branch of their own.
     0x403c0 addi sp,sp,-32; save ra,s0,s1; mv s0,a1; mv s1,a0; lui a0,2; add a0,s1,a0; ld a0,-8(a0)  (the flag
     pointer at frame + 8192 - 8); sb zero,0(a0); mv a0,s1; jal 0x40410 (result unused); li a2,245; mv a0,s1;
     mv a1,s0; restore; addi sp,sp,32; j 0x59824 (tail jump to the shadow-fill helper, value 0xf5).
   The helper at 0x40410 reads the GOT block 0xa63e8.. (shadow cell 0xb10b8, the mid/high memory words 0xb1da0..);
   the helper at 0x59824 reads the byte 0xb091c and ends in a jump through GOT 0xa6410 -> 0xa82b0 -> musl memset
   0x9ef40. *)

Definition SF_ENTRY : Z := 0x403c0.
Definition FS_B : Z := 8192.
Definition SF_WIN : Z := 96.
Definition sf_ranges : list (Z * nat) := [(0x403c0, 20%nat); (0x40410, 28%nat); (0x59824, 233%nat)].
Definition tbl_sf : ctable := Eval vm_compute in build_ranges sf_ranges TEmpty.
Lemma tbl_sf_eq : tbl_sf = build_ranges sf_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_sf). Qed.
Lemma tbl_sf_ok : table_ok tfibsegs tbl_sf.
Proof. rewrite tbl_sf_eq. apply build_ranges_ok; [unfold sf_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)]. Qed.
Definition sf_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
[(0xa63e8, 40, [(0, 8%N, 0xae8b8); (8, 8%N, 0xb10b8); (16, 8%N, 0xb1da8); (24, 8%N, 0xb1db0); (32, 8%N, 0xb1da0)]);
(0xb10b8, 8, [(0, 8%N, 0x7fff8000)]); (0xb1da0, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0xa82b0, 8, [(0, 8%N, 0x9ef40)]); (0xb091c, 1, [(0, 1%N, 1)]); (0xa6410, 8, [(0, 8%N, 0xa82b0)])].
Lemma sf_rodata_chk : forall ly, rodata_chk ly sf_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition aFLG : nat := 32.
Definition stk : YP09.region := YP09.mkRegion (Some 2%nat) (- SF_WIN) 0 (- SF_WIN) 0 [].
Definition rFF : YP09.region := YP09.mkRegion (Some 10%nat) (FS_B - 8) FS_B (FS_B - 8) (FS_B - 8) [YP09.mkChunk (FS_B - 8) (CVal 8 (SOff aFLG 0))].
Definition rFLG : YP09.region := YP09.mkRegion (Some aFLG) 0 1 0 1 [].
Definition ffLO (hi : bool) : Z := if hi then kHighMemBeg else 4096.
Definition ffHI (hi : bool) : Z := if hi then CEIL_MAX - FS_B else kLowShadowBeg - FS_B.
Definition sf_facts (hi : bool) : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + SF_WIN) kHighMemEnd 4); (10%nat, mkAF (ffLO hi) (ffHI hi) 5); (11%nat, mkAF 8 FS_B 3); (aFLG, mkAF 4096 (CEIL_MAX - 1) 0)].
Definition sf_mem : smem := stk :: rFF :: rFLG :: map ro_region sf_rodata.
Definition ss0 (hi : bool) : sstate := mkSS SF_ENTRY sr_atoms sf_mem None (mkFacts (sf_facts hi) [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_sf FUEL s.
Definition eH : sstate := Eval vm_compute in fst (RUN (ss0 true)).
Definition eL : sstate := Eval vm_compute in fst (RUN (ss0 false)).
Definition e1 (hi : bool) : sstate := if hi then eH else eL.
Lemma r_sf : forall hi, RUN (ss0 hi) = (e1 hi, RS_stopped SR_fetch). Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition a0e : sv := SAlu ALU_ADD (SLit SHADOW_OFF) (SAlu ALU_SRL (SOff 10 0) (SLit 3)).
Definition a2e : sv := Eval vm_compute in sr_get (ss_regs eH) 12%bv.
Definition keep_regs : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sf_shape (ss : sstate) : bool :=
(ss_pc ss =? tfib_A_musl_memset) && (match ss_resv ss with None => true | _ => false end) &&
sv_eqb (sr_get (ss_regs ss) 10%bv) a0e && sv_eqb (sr_get (ss_regs ss) 11%bv) (SLit 0xf5) && sv_eqb (sr_get (ss_regs ss) 12%bv) a2e &&
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) keep_regs.
Lemma shape_sf : forall hi, sf_shape (e1 hi) = true. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma e1_stk : forall hi, exists cs, nth_error (ss_mem (e1 hi)) 0 = Some (YP09.mkRegion (Some 2%nat) (- SF_WIN) 0 (- SF_WIN) 0 cs).
Proof. intros hi. exists (YP09.r_chunks (nth 0 (ss_mem (e1 hi)) stk)). destruct hi; vm_compute; reflexivity. Qed.
Lemma e1_flg : forall hi, nth_error (ss_mem (e1 hi)) 2 = Some (YP09.mkRegion (Some aFLG) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma a2e_eq : a2e = SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff 10 0) (SLit 3))) (SLit 0).
Proof. vm_compute. reflexivity. Qed.
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
Lemma a2e_denot : forall E FF n, bv_unsigned (ew E 10) = FF -> bv_unsigned (ew E 11) = n ->
8 <= FF -> FF + n <= 2 ^ 63 -> FF mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> sv_denot E a2e = Z_to_bv 64 (n / 8).
Proof.
intros E FF n HFF Hn H8 Hhi Hm1 Hm2 Hn8. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a2e)). f_equal.
change (bv_unsigned (sv_denot E a2e)) with (U E a2e). rewrite (U_zev E a2e) by (vm_compute; reflexivity).
rewrite a2e_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, Hn, !Z.add_0_r. change (Z.land (zcanon 3) 63) with 3.
assert (Eq1 : FF = 8 * (FF / 8)) by (pose proof (Z.div_mod FF 8 ltac:(lia)); lia).
assert (Eq2 : n = 8 * (n / 8)) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
set (f := FF / 8) in *. set (m := n / 8) in *.
assert (Hf : 1 <= f) by lia. assert (Hm : 1 <= m) by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_small (FF + -8)) by lia. rewrite (zcanon_small n) by lia. rewrite (zcanon_small (FF + -8 + n)) by lia.
rewrite (zcanon_small FF) by lia. change (zcanon 1) with 1.
replace ((FF + -8 + n) / 8) with (f + m - 1) by (rewrite Eq1, Eq2; replace (8 * f + -8 + 8 * m) with ((f + m - 1) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
replace (FF / 8) with f by reflexivity.
rewrite (zcanon_small (f + m - 1)) by lia. rewrite (zcanon_small (f + m - 1 + 1)) by lia. rewrite (zcanon_small f) by lia.
replace (f + m - 1 + 1 - f) with m by lia. rewrite (zcanon_small m) by lia. apply zcanon_small. lia.
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
Theorem tfib_stack_free_7 : astack_free_realizes tfibsegs B SF_ENTRY 7.
Proof.
intros ly S W regs mem md pos n HPRE Hin G10 G11 Hn Hn8 HTR.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx.
set (H := w_H W) in *. set (sp0 := spZ regs) in *.
change (fs_frame_bytes 7) with 8192 in *.
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
assert (HPOS : 0 <= pos < 128).
{ pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf B ly S _ M))) (7, pos) Hin) as [_ X]. cbn [fst snd] in X. exact X. }
set (fa := frame_addr ly 7 pos) in *. set (fl := flag_addr ly 7 pos) in *.
assert (Efa : fa = ly_F ly + 7376896 + pos * 8192).
{ unfold fa, frame_addr, fs_frame_off. change kFakeFramesOff with 36864. change (Z.shiftl 1 kStackSizeLog) with 1048576. change (fs_frame_bytes 7) with 8192. lia. }
assert (Efl : fl = ly_F ly + 36608 + pos).
{ unfold fl, flag_addr, fs_flag_off. change kFakeFlagsOff with 4096. change (fs_flags_off 7) with 32512. lia. }
destruct (al_frames _ _ LAWS ly S W mem md 7 pos HAR Hin) as (Hal32 & _ & Hfr & Hsh). fold fa in Hal32, Hfr, Hsh. change (fs_frame_bytes 7) with 8192 in Hfr, Hsh. change (8192 / 8) with 1024 in Hsh.
destruct (al_flag _ _ LAWS ly S W mem md 7 pos HAR Hin) as (Hflp & Hflo & _ & _). fold fl in Hflp, Hflo.
pose proof (lo_stk_ceil ly HLY) as SC. unfold ASAN_CEIL in SC.
assert (RFA : 6316032 <= ly_F ly /\ ly_F ly + 11571200 <= alloc_ceiling) by (destruct hi; lia).
assert (Hsp : kHighMemBeg + 4096 <= sp0 <= 2 ^ 47 /\ alloc_ceiling + 4096 <= sp0) by (unfold kHighMemBeg, kHighMemEnd, sp0 in *; lia).
set (E := Ereg regs [w64 fl]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = fa) by (rewrite (EEreg 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (E11 : bv_unsigned (ew E 11) = n) by (rewrite (EEreg 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 fl) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = fl) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS0 : st_ok tfibsegs E (ss0 hi) (restrict H (mkst regs (Z_to_bv 64 SF_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss0, sf_mem. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 fl]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- change (stk :: rFF :: rFLG :: map ro_region sf_rodata) with ([stk; rFF; rFLG] ++ map ro_region sf_rodata).
apply Forall_app. split; [|exact (rodata_ok B TB sf_rodata ly S H mem E (sf_rodata_chk ly) M)].
repeat apply Forall_cons; try apply Forall_nil.
+ unfold stk, SF_WIN. apply (region_ok_stack tfibsegs E _ 2 sp0 (- 96)); [exact E2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. fold sp0. lia.
+ unfold rFF, aFLG, FS_B, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E10.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ fa (8192 - 8) 8%N (SOff 32 0) fl); [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
replace (fa + (8192 - 8)) with (fa + 8192 - 8) by lia. exact (AE2y.val_mem_of_rdword H mem _ _ HTR).
+ unfold rFLG, aFLG, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. replace (fl + o) with fl by lia. exact (AE2y.apresent_writable H mem fl Hflp).
- apply pairwise_disjoint_of_extents. unfold stk, rFF, rFLG, aFLG, sf_rodata, ro_region, extent_of_region, SF_WIN, FS_B.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E10, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok sf_facts]. unfold afact_ok, aFLG. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, U32. unfold ffLO, ffHI, SF_WIN, FS_B, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | exact Hal32 | exact Hn8 | apply Z.mod_1_r | destruct hi; lia]. }
idtac "CHECKPOINT-1".
unfold cfg_at. change (w64 SF_ENTRY) with (Z_to_bv 64 SF_ENTRY).
eapply SRr_bind; [apply (sf_phase W E _ _ _ _ _ HS0 (r_sf hi))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & HFrm1).
assert (MEQ1 : forall z : word, ~ (sp0 - 96 <= bv_unsigned z < sp0) -> bv_unsigned z <> fl -> ms_mem ms1 z = mem z).
{ intros z Hz1 Hz2. apply HFm1. intros Hw. destruct (in_wrange_windows E _ _ Hw) as (b & lo & hi' & Ht & Hb).
unfold ss0, sf_mem in Ht. cbn [ss_mem] in Ht. cbn in Ht.
destruct Ht as [Hq|[Hq|[Hq|Ht]]]; try (injection Hq as <- <- <-; cbn [base_val] in Hb; rewrite ?E2, ?E10, ?U32 in Hb; unfold SF_WIN, FS_B, aFLG in *; lia).
repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hb; lia|]). destruct Ht. }
clear HFm1 HFrm1.
idtac "CHECKPOINT-2".
pose proof (shape_sf hi) as Hshape. unfold sf_shape in Hshape. apply andb_prop in Hshape as [Hshape KR]. apply andb_prop in Hshape as [Hshape S12].
apply andb_prop in Hshape as [Hshape S11]. apply andb_prop in Hshape as [Hshape S10]. apply andb_prop in Hshape as [Spc Srv].
apply Z.eqb_eq in Spc. assert (Hrv : ss_resv (e1 hi) = None) by (destruct (ss_resv (e1 hi)); [discriminate | reflexivity]).
apply sv_eqb_eq in S10. apply sv_eqb_eq in S11. apply sv_eqb_eq in S12. rewrite forallb_forall in KR.
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS1 Hrv) as Hshape1. rewrite Spc in Hshape1.
set (regs1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
assert (KEEP1 : forall r, In r keep_regs -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. unfold regs1. rewrite (st_ok_restrict_reg tfibsegs H E (e1 hi) ms1 _ HS1). specialize (KR r Hr). apply sv_eqb_eq in KR. rewrite KR.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply EEreg.
unfold keep_regs in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
set (sh := shadow_addr fa) in *. set (cnt := n / 8).
assert (Hfa8 : 0 <= fa / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hcnt : 1 <= cnt <= 1024) by (unfold cnt; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (Esh : sh = SHADOW_OFF + fa / 8) by reflexivity. unfold SHADOW_OFF in Esh.
assert (A10 : getr regs1 10 = w64 sh).
{ unfold regs1. rewrite (st_ok_restrict_reg tfibsegs H E (e1 hi) ms1 10%bv HS1), S10. rewrite (a0e_denot E fa E10 ltac:(lia)). reflexivity. }
assert (A11 : getr regs1 11 = w64 0xf5) by (unfold regs1; rewrite (st_ok_restrict_reg tfibsegs H E (e1 hi) ms1 11%bv HS1), S11; reflexivity).
assert (A12 : getr regs1 12 = w64 cnt).
{ unfold regs1. rewrite (st_ok_restrict_reg tfibsegs H E (e1 hi) ms1 12%bv HS1), S12.
assert (Hfa8m : fa mod 8 = 0).
{ pose proof (Z.div_mod fa 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (fa / 32)) with ((4 * (fa / 32)) * 8) by lia. apply Z_mod_mult. }
rewrite (a2e_denot E fa n E10 E11 ltac:(lia) ltac:(lia) Hfa8m Hn8 ltac:(lia)). reflexivity. }
assert (A1 : getr regs1 1 = getr regs 1) by (exact (KEEP1 1 ltac:(unfold keep_regs; cbn [In]; tauto))).
destruct (e1_stk hi) as (cs & Hstk). pose proof (e1_flg hi) as Hflg.
assert (PW1 : forall a, sp0 - 96 <= a < sp0 -> apresent H mem1 a).
{ intros a Ha. apply (st_ok_window_apresent H E (e1 hi) ms1 0 _ a HS1 Hstk); [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite E2; unfold SF_WIN; lia | unfold TFIB_IMG_END, kHighMemBeg in *; lia]. }
assert (FL1 : aview tfibsegs H mem1 fl = Some 0).
{ pose proof (st_ok_mem_ok tfibsegs E (e1 hi) _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hflg)) as (_ & _ & _ & Hcs).
cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. unfold aFLG in Hcs. rewrite U32 in Hcs.
pose proof (val_of_chunk_ok tfibsegs E _ fl 0 1%N (SLit 0) 0 (Forall_inv Hcs) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
specialize (V 0%nat ltac:(cbn; lia)). rewrite !Z.add_0_r in V. unfold aview. fold mem1 H in V. rewrite V. reflexivity. }
assert (PRS : forall a, sh <= a < sh + cnt -> apresent H mem a /\ ~ aowned B ly S a).
{ intros a Ha. replace a with (sh + (a - sh)) by lia. apply Hsh. lia. }
assert (NSTK : forall a, sh <= a < sh + cnt -> ~ (sp0 - 96 <= a < sp0) /\ a <> fl).
{ intros a Ha. split; [unfold kHighMemBeg in Hsp; lia|]. intros ->. exact (proj2 (PRS fl Ha) Hflo). }
assert (DW : forall a, sh <= a < sh + cnt -> writable_at tfibsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (PRS a Ha) as [[Hh [b Hb]] _]. split; [|exact Hh].
apply AE2y.apresent_writable. split; [exact Hh|]. exists b. unfold mem1. rewrite MEQ1; [exact Hb | |]; rewrite unsigned_lit_small by (unfold kHighMemBeg in Hsp; lia); apply (NSTK a Ha). }
idtac "CHECKPOINT-3".
set (nn := Z.to_nat cnt). assert (Hnn : Z.of_nat nn = cnt) by (subst nn; lia).
assert (SOK : store_ok tfibsegs (mrestrict H mem1) (w64 sh) nn = true).
{ apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by lia; [lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (tfib_memset (w64 sh) (w64 0xf5) (w64 cnt) nn (mrestrict H mem1) (seg_rom tfibsegs) regs1 A10 A11 A12
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) SOK ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia))
as (regs2 & Hms & B10 & Hkeep).
rewrite A1, Hra in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 0xf5) mod 256)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 sh) (repeat cb nn)) in Hms.
set (mem2 := munrestrict H mem1 m2r).
rewrite Hshape1. fold regs1 mem1.
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _.
pose proof (same_but_materialized_trans _ _ _ (with_vm_backing_same md mat1) Hsbm) as HSBM.
change (unrestrict H mem1 (mkst regs2 (getr regs 1) m2r (seg_rom tfibsegs))) with (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)).
assert (LEN : Z.of_nat (length (repeat cb nn)) = cnt) by (rewrite repeat_length; exact Hnn).
assert (M2out : forall z : word, ~ (sh <= bv_unsigned z < sh + cnt) -> mem2 z = mem1 z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
assert (Ew : wbytes m1r (w64 sh) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) sh) as [L|L].
- apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by lia; lia.
- apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by lia. lia. }
rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < cnt -> mem2 (Z_to_bv 64 (sh + i)) = Some cb).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (sh + i) ltac:(lia))).
subst m2r. rewrite (AE2y.wbytes_inside (repeat cb nn) m1r (w64 sh) (Z_to_bv 64 (sh + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by lia; [|lia|lia].
replace (Z.to_nat (sh + i - sh)) with (Z.to_nat i) by lia. apply nth_error_repeat. lia. }
assert (CB : bv_unsigned cb = 0xf5) by (subst cb; vm_compute; reflexivity).
assert (AVin : forall i, 0 <= i < cnt -> aview tfibsegs H mem2 (sh + i) = Some 0xf5).
{ intros i Hi. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (sh + i) ltac:(lia))), (M2in i Hi). cbn [option_map]. rewrite CB. reflexivity. }
assert (AVout : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + cnt) -> ~ (sp0 - 96 <= a < sp0) -> a <> fl -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Ha Hs Hf. apply aview_same. rewrite M2out by (rewrite unsigned_lit_small by lia; exact Ha).
apply MEQ1; rewrite unsigned_lit_small by lia; assumption. }
assert (FL2 : aview tfibsegs H mem2 fl = Some 0).
{ rewrite <- FL1. apply aview_same. apply M2out. rewrite unsigned_lit_small by lia. intros Ha. exact (proj2 (NSTK fl Ha) eq_refl). }
assert (PW2 : forall a, sp0 - 96 <= a < sp0 -> apresent H mem2 a).
{ intros a Ha. destruct (PW1 a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite M2out; [exact Hb|]. rewrite unsigned_lit_small by (unfold kHighMemBeg in Hsp; lia). unfold kHighMemBeg in Hsp; lia. }
idtac "CHECKPOINT-4".
apply SRr_ret. split; [reflexivity|]. exists regs2, mem2, model'.
pose proof (same_but_materialized_frame md model' HSBM) as MF.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [|split; [|split; [exact HSBM|split; [|split]]]].
-
apply (astack_free_law_ok tfibsegs B ly S W mem md mem2 model' 7 pos HAR Hin).
+ exact FL2.
+ intros a Hr Hown Hnf. apply AVout; [exact Hr | | | exact Hnf].
* intros Ha. exact (proj2 (PRS a Ha) Hown).
* intros Ha. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hvw. fold H in Hvw |- *. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hvw.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z.eq_dec a' fl) as [Ea|Hnf]; [rewrite Ea, FL2; discriminate|].
destruct (Z_lt_le_dec a' sh) as [L1|L1]; [| destruct (Z_lt_le_dec a' (sh + cnt)) as [L2|L2]].
2:{ replace a' with (sh + (a' - sh)) by lia. rewrite AVin by lia. discriminate. }
all: destruct (Z_lt_le_dec a' (sp0 - 96)) as [L3|L3]; [rewrite AVout by lia; exact Hvw|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4]; [| rewrite AVout by lia; exact Hvw].
all: apply aview_some_of_apresent; apply PW2; lia.
+ apply MF. + apply MF. + apply MF.
+ intros a Hb Hh. change (w_H W (w64 a)) with (H (Z_to_bv 64 a)) in Hh. pose proof (AE2y.in_band_rw_u64 a Hb) as Hr.
unfold w64. rewrite M2out.
* apply MEQ1; rewrite unsigned_lit_small by lia.
-- intros Ha. destruct (PW1 a Ha) as [Hh' _]. rewrite Hh' in Hh. discriminate.
-- intros ->. pose proof (proj1 Hflp) as Hf0. unfold H in Hh, Hf0. rewrite Hf0 in Hh. discriminate.
* rewrite unsigned_lit_small by lia. intros Ha. rewrite (proj2 (DW a Ha)) in Hh. discriminate.
-
intros r Hr.
assert (NE : forall x : bv 5, 11 <= bv_unsigned x <= 16 -> Z_to_bv 5 r <> x).
{ intros x Hx Ex. rewrite <- Ex in Hx. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx. change (bv_modulus 5) with 32 in Hx.
unfold acallee_saved in Hr. rewrite Z.mod_small in Hx by lia. lia. }
rewrite Hkeep; [apply KEEP1; unfold acallee_saved in Hr; unfold keep_regs; cbn [In]; lia | | | | | |]; apply NE; (split; apply Z.leb_le; reflexivity).
-
intros i Hi. fold sh. apply AVin. fold cnt in Hi. exact Hi.
-
intros a Hr Ha Hnf Hs. fold sh in Ha. fold cnt in Ha. apply AVout; [exact Hr | exact Ha | | exact Hnf]. fold sp0 in Hs. rewrite HES in Hs. lia.
-
intros a Ha. fold sp0 in Ha. rewrite HES in Ha. destruct (Z_lt_le_dec a (sp0 - 96)) as [L|L]; [|apply PW2; lia].
destruct (HpresE a ltac:(fold sp0; lia)) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
rewrite M2out by (rewrite unsigned_lit_small by (unfold kHighMemBeg in Hsp; lia); unfold kHighMemBeg in Hsp; lia). rewrite MEQ1; [exact Hb | |]; rewrite unsigned_lit_small by (unfold kHighMemBeg in Hsp; lia); [lia|].
intros ->. exact (al_stack _ _ LAWS ly S W mem md fl HAR ltac:(unfold sp0 in *; lia) Hflo).
Qed.
End d.
Theorem cmd_stack_free7_contract : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B -> astack_free_realizes tfibsegs B 0x403c0 7.
Proof. intros B LAWS TB. exact (tfib_stack_free_7 B LAWS TB). Qed.
End c.
