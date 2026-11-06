(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025), the
   CALL SEGMENT of the malloc interceptor over ARcf: __wrap_malloc's entry (B 0x53824 `j ___interceptor_malloc`) to
   Allocate's entry (CfImg's cf_pc_allocate, B 0x326a4), through ___interceptor_malloc (0x539fc; TryAsanInitFromRtl,
   GetMallocContextSize, GetCurrentPc, the BufferedStackTrace set-up, UnwindImpl) and asan_malloc (0x32648) up to its
   `jal Allocate` (0x32670). Code read: the runtime decode table YB1q.tfibtbl_rtA (blob of lib/Reusable/YB1q.v at the
   base); the listing lib/B/Listing_prog.v covers the program range [0x816cc, 0x88fb0) only and no instruction of this
   segment lies there.
   Ported BY STATEMENT from the ARm donors over cgif's ARm on image B:
   - the prefix to UnwindImpl and its return: lib/Reusable/YFjh.v:459-614 seg0 (srr_run_to_sh to B_UNWINDIMPL_PC,
     the unwinder's spec, the stack object's regions); its U1 premises at the free donor's region list as
     lib/Reusable/YFh1.v:217-274 states them (the seed here is YFgn.REG0, WrapMallocBSeed.v);
   - asan_malloc to Allocate's entry: the first run of lib/Reusable/YFji.v:445 seg1 (s_runP from S_1 through
     asan_malloc into Allocate), stopped at Allocate's entry;
   - UnwindImpl is the donors' named premise U1 : tfib_unwind_spec (YFl0.v:24-58), relation-generic, taken as is.
   The dlsym arm (TryAsanInitFromRtl returns 0) and the short-context arm (GetMallocContextSize <= 2) are refuted as
   the donor refutes them: B_ASAN_INITED_CELL reads 1 and B_MALLOC_CONTEXT_SIZE_CELL reads 30 in the seed
   (Tfib_const through ARmcf's amc_const), so the symbolic run takes neither branch. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq YFgn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import WrapBKit WrapMallocBSeed.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require WrapBEntry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section WK.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variable mat0 : list word.
Hypothesis PRE : acall_pre_cf tfibsegs B ly S Hp W regs0 mem0 md0 ch.
Hypothesis U1 : tfib_unwind_spec.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let cfg0 : config := mkCfg (mkst regs0 (w64 B_WRAP_MALLOC_PC) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Local Notation E0 := (E0m ly regs0 ch).
Local Notation LENv := (LENm ly regs0 ch).
Local Notation tr := (trm ly regs0 ch).

Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 (XWm ly regs0 ch) k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. exact (Er 8 8%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = getr regs0 10. Proof. exact (Er 10 10%bv eq_refl). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. reflexivity. Qed.

(* The shared entry facts (WrapBEntry.v), at this walk's entry and seed environment. *)
Local Notation LY := (WrapBEntry.LY B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation IMG := (WrapBEntry.IMG B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation Hra := (WrapBEntry.Hra B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation Hal := (WrapBEntry.Hal B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation Hsp := (WrapBEntry.Hsp B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation HPRES := (WrapBEntry.HPRES B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation Hra4096 := (WrapBEntry.Hra4096 B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation Hch := (WrapBEntry.Hch B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation LYB := (WrapBEntry.LYB B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation LYD := (WrapBEntry.LYD B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation stack_ivs := (WrapBEntry.stack_ivs B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation windows_WIN := (WrapBEntry.windows_WIN B ly S Hp W regs0 mem0 md0 ch PRE E0 E2 EaT).
Local Notation WIN_not_high := (WrapBEntry.WIN_not_high B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation all_disjoint_of_forall := WrapBEntry.all_disjoint_of_forall.
Local Notation kept_of_frame := (WrapBEntry.kept_of_frame ly W regs0).
Local Notation off_T := (WrapBEntry.off_T B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation off_C := (WrapBEntry.off_C B ly S Hp W regs0 mem0 md0 ch PRE).
Local Notation tail_facts := (WrapBEntry.tail_facts B ly S Hp W regs0 mem0 md0 ch PRE E0 EaT EaC).

Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac
| unfold off_img; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; unfold TFIB_IMG_LO; unfold YImgTop.IMG_LO_B in *; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; tac ].


(* The state at Allocate's entry: registers (asan_malloc's call Allocate(&instance, n, 8, &stack, FROM_MALLOC,
   can_fill)), the interceptor's and asan_malloc's saved registers, the stack object and its trace, and the frame of
   the whole segment (memory changed only in the caller's stack window and T + t_unwinding, which reads 0 again). *)
Definition at_ALLOC (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsA memA mat,
c' = mkCfg (mkst regsA (w64 0x326a4) memA (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regsA 1 = w64 0x32674 /\ getr regsA 2 = w64 (sp0 - 2144) /\
getr regsA 10 = w64 TFIB_INST /\ getr regsA 11 = getr regs0 10 /\ getr regsA 12 = w64 8 /\
getr regsA 13 = w64 (sp0 - 2128) /\ getr regsA 14 = w64 1 /\ getr regsA 15 = w64 1 /\
getr regsA 8 = getr regs0 2 /\ getr regsA 9 = getr regs0 10 /\ getr regsA 3 = getr regs0 3 /\ getr regsA 4 = w64 TFIB_TP /\
(forall r : Z, 22 <= r <= 27 -> getr regsA (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) /\
(forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> ~ (T + t_unwinding <= bv_unsigned x < T + t_unwinding + 1) -> memA x = mem0 x) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (T + t_unwinding) 1 0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) memA a) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2128) 8 (sp0 - 2112) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2120) 8 LENv /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 56) 8 (bv_unsigned (getr regs0 21)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2144) 8 sp0 /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2136) 8 0x53b30.

Lemma seg_call : SRr tfibsegs W cfg0 at_ALLOC.
Proof.
pose proof Hwx_tfa as Hwx. pose proof (SEED_ok B TB ly S Hp W regs0 mem0 md0 ch PRE) as HS.
pose proof Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof LY as LY. pose proof IMG as IMG.
pose proof Hal as Hsp_al. pose proof Hch as Hch. pose proof Hra4096 as Hra4096.
fold sp0 in Hlo, Hbot, Hhi, Hsp_al, Hch. fold T SB in LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
(* YFjh.v:464, the run to the unwinder. *)
srr_run_to_sh tfibtbl_rtA_ok HS B_UNWINDIMPL_PC.
rename HF into HF1. clear HFr.
assert (FR1 : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0) -> ~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem ms y = mem0 y).
{ intros y Y1 Y2. apply HF1. intros Hw. destruct (windows_WIN E0 (ss_mem SS0m) _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw) as [X|X]; [exact (Y1 X) | exact (Y2 X)]. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape. rewrite Hshape.
rreg HS (2%bv : bv 5) Q2. rewrite E2 in Q2.
eapply SRr_bind.
(* YFh1.v:217-274, the unwinder's premises at YFgn.REG0 (region k of YFh1 is region k - 2 here). *)
{ apply (U1 W ly (ms_regs ms) (ms_mem ms) _ (sp0 - 2128) B_INTERCEPTOR_MALLOC_PC_OFF_C8 sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R; rewrite R, E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (12%bv : bv 5) R; rewrite R, E2. unfold sp0. symmetry. apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (14%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity. }
1:{ zlia. }
1:{ memv HS 1%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 5%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 6%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 26%nat 0%nat; [reflexivity | reflexivity | unfold TFIB_TSD; zlia]. }
1:{ memv HS 27%nat 0%nat; [reflexivity | cbn [sv_denot]; rewrite EaC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 28%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite EaC; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite EaT; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold T; zlia | clear - LB; numconst; unfold T in *; zlia]. }
1:{ memv HS 29%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T; zlia | reflexivity | zlia]. }
1:{ memv HS 29%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T; zlia
| cbn [sv_denot]; rewrite EaTOP; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 29%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T; zlia
| cbn [sv_denot]; rewrite EaTOP; unfold w64, ly_bot, kStackSpan; rewrite Zbv_add_unsigned; f_equal; zlia
| unfold ly_bot, kStackSpan; clear - LB; numconst; zlia]. }
1:{ memv HS 30%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T, t_unwinding; zlia | reflexivity | zlia]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 30 _ _ HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T; numconst; zlia | off_by ltac:(clear - LB; numconst; unfold T in *; zlia) ]. }
1:{ memv HS 21%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 22%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia). clear - Hlo LB; numconst; unfold sp0 in *; zlia. }
1:{ intros a Ha. rewrite Q2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia).
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by zlia.
rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ clear - Hlo LB; numconst; zlia. }
1:{ right. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia). zlia. }
1:{ intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
1:{ clear; numconst; zlia. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia). zlia. }
1:{ exact Hbot. }
1:{ exact Hhi. }
1:{ apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 0%nat 11%nat;
[cbn [base_val YP09.r_base]; rewrite E2; unfold sp0; zlia | cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 0%nat 10%nat;
[cbn [base_val YP09.r_base]; rewrite E2; unfold sp0; zlia | cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ exact Hra4096. }
fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hch].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [exact Hch|].
destruct Hch as [H16 Hfp]. split; [exact H16|].
apply Z.ltb_lt in Hf0.
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [exact Hfp | zlia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply (HF1 (Z_to_bv 64 (a + i))). intros Hw. rewrite unsigned_lit_small in Hw by (clear - Ha1 Ha2 H16 Hi Usp LB; numconst; zlia).
exact (WIN_not_high (a + i) ltac:(clear - Ha1 Ha2 H16 Hi Usp; zlia) (windows_WIN E0 (ss_mem SS0m) (a + i) (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw)). }
(* YFjh.v:528-604: the unwinder's return; the stack object's regions. *)
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & Hfr & Hpr & Ht1 & Ht2 & Ht3). srr_norm_model.
rreg HS (1%bv : bv 5) R1.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite Q2 in Hfr. unfold w64, UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia).
apply Hfr; unfold sp0, ASTACK in *; zlia. }
assert (Hfr'' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite Q2 in Hfr. unfold w64, UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia).
apply Hfr; unfold sp0, ASTACK in *; zlia. }
jafter_call2 HS 54%nat regs1 (mrestrict (w_H W) mem1) HP (-64) (seq 0 30) HS1.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ constructor;
[ eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr'' Hpr); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; first [zlia | right; zlia | left; zlia]
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with YFgn.SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4);
eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0) _ Hfr' Hpr); intros a Ha; cbn beta;
[ clear - Y1 Y2 Y3 Ha; zlia | clear - Y4 Ha; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; zlia ] ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply Hpr. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
set (En1 := havoc E0 54 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAVf)%nat -> ew En1 k = ew E0 k) by (intros k Hk; subst En1; apply ew_havoc_old; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold IFRAME;
split; [clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia|]; split; [clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Ho Usp Hlo LB; numconst; unfold sp0 in *; zlia) | apply PRES1; clear - Ho; numconst; unfold sp0 in *; zlia] | apply Forall_nil]
| apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with YFgn.SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; try unfold sp0 in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [intros k Hk; apply Hfr; rewrite ?Q2; unfold w64; rewrite ?unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; unfold sp0 in *; zlia); unfold UNW_STK, BST_SIZE; clear - Usp Hlo LB Hk; unfold sp0 in *; numconst; zlia|].
memv HS 0%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite E2; unfold sp0; zlia | cbn [sv_denot]; rewrite E2; unfold w64, sp0; first [f_equal; zlia | rewrite Zbv_add_unsigned; f_equal; zlia] | clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia]. }
assert (LEN : (1 <= length tr <= 30)%nat).
{ unfold trm, call_trace. destruct (frame0_ok ly regs0); [apply unwind_of_chain_length | cbn; lia]. }
(* YFjh.v:571-580, the trace length with its upper word. *)
assert (OBJ1 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 2120) 8 LENv).
{ unfold LENm. replace (Z.of_nat (length tr)) with (Z.of_nat (length tr) + 2 ^ 32 * 0) by zlia.
apply val_mem_4_4; [zlia | zlia | |].
- eapply val_mem_addr; [exact Ht1 | zlia].
- assert (Z8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120) 8 0)
by (memv HS 0%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite E2; unfold sp0; zlia | reflexivity | zlia]).
assert (Z4 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by zlia.
rewrite (Z8 (4 + k)%nat ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
eapply val_mem_frame; [intros k Hk; apply Hfr; rewrite ?Q2; unfold w64; rewrite ?unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; unfold sp0 in *; zlia); unfold UNW_STK, BST_SIZE; clear - Usp Hlo LB Hk; unfold sp0 in *; numconst; zlia| exact Z4]. }
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
(* YFji.v:455's first run (through asan_malloc), stopped at Allocate's entry (B 0x326a4, cf_pc_allocate). *)
srr_run_to_sh tfibtbl_rtA_ok HS 0x326a4.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En1 _ _ HS eq_refl) as HshA; cbn [ss_pc] in HshA.
(* The run's windows (YFh1.v:340-349's form): asan_malloc's frame below the stack object, the saved registers,
   T + t_unwinding. *)
assert (FRR : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0 - IFRAME) -> ~ (sp0 - 64 <= bv_unsigned y < sp0) ->
~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem msA y = mem1 y).
{ intros y Y1 Y2 Y3. apply HF. intros Hw. destruct (in_wrange_windows En1 _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hr;
rewrite ?(HEn1 2%nat ltac:(cbv; zlia)), ?E2, ?(HEn1 32%nat ltac:(cbv; zlia)), ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by (clear - LB; numconst; unfold T in *; zlia);
clear - Y1 Y2 Y3 Hr; unfold IFRAME, ASTACK, t_unwinding in *; unfold sp0, T in *; zlia |]).
destruct Hin. }
pose proof stack_ivs as (IT & _). fold sp0 T in IT.
assert (NT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (T + t_unwinding <= a < T + t_unwinding + 1)).
{ intros a Ha Ht. clear - Ha Ht IT. unfold kThreadObjSize, t_unwinding, ASTACK in *. zlia. }
apply SRr_ret. unfold at_ALLOC. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg _ (with_vm_backing _ ?mt _) = _ /\ _ => exists (ms_regs msA), (ms_mem msA), mt end.
split. { rewrite HshA at 1. reflexivity. }
split. { rreg HS (1%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (2%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold w64, sp0. f_equal; zlia. }
split. { rreg HS (10%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (11%bv : bv 5) R; rewrite R, (HEn1 10%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (12%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (13%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold w64, sp0. f_equal; zlia. }
split. { rreg HS (14%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (8%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (9%bv : bv 5) R; rewrite R, (HEn1 10%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (3%bv : bv 5) R; rewrite R, (HEn1 3%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
split. { intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
repeat match type of Hr' with _ \/ _ => destruct Hr' as [Hr'|Hr'] end; subst r;
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
let kb := eval vm_compute in (Z_to_bv 5 k : bv 5) in
let RR := fresh "RR" in rreg HS kb RR; change (Z_to_bv 5 k) with kb; rewrite RR, HEn1 by (cbv; zlia); apply Er; reflexivity end. }
split. { intros x X1 X2.
rewrite (FRR x) by (first [exact X2 | intros HH; apply X1; clear - HH; unfold IFRAME, ASTACK in *; zlia]).
rewrite (Hfr' x X1). exact (FR1 x X1 X2). }
split. { memv HS 31%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T, t_unwinding; zlia | reflexivity | zlia]. }
split. { intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)) as [A1|A1]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [A2|A2]].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; clear - Ha A1; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ].
- apply (apresent_same (w_H W) mem1); [|apply PRES1; exact Ha].
apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia);
[clear - A1; unfold IFRAME, ASTACK in *; zlia | clear - A2; zlia | exact (NT a Ha)].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; clear - Ha A2; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
assert (FRM : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ms_mem msA (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
{ intros a Ha. apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia);
[clear - Ha; unfold IFRAME, ASTACK in *; zlia | clear - Ha; zlia | apply NT; clear - Ha; unfold IFRAME, ASTACK in *; zlia]. }
split. { eapply val_mem_frame; [|exact OBJ0]. intros k Hk. apply FRM. unfold IFRAME. zlia. }
split. { eapply val_mem_frame; [|exact OBJ1]. intros k Hk. apply FRM. unfold IFRAME. zlia. }
split. { intros i Hi. eapply val_mem_addr; [eapply val_mem_frame; [|exact (Ht2 i Hi)] | zlia].
intros k Hk. apply FRM. unfold IFRAME. clear - Hi Hk LEN. zlia. }
split. { memv HS 1%nat 6%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 1%nat ltac:(cbv; zlia)), E1, Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 5%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 8%nat ltac:(cbv; zlia)), E8, Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 9%nat ltac:(cbv; zlia)), (Er 9 9%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 18%nat ltac:(cbv; zlia)), (Er 18 18%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 19%nat ltac:(cbv; zlia)), (Er 19 19%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 20%nat ltac:(cbv; zlia)), (Er 20 20%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 21%nat ltac:(cbv; zlia)), (Er 21 21%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 0%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2, Z.add_0_r; reflexivity | exact Usp]. }
memv HS 0%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | reflexivity | zlia].
Qed.
End WK.
End c.
