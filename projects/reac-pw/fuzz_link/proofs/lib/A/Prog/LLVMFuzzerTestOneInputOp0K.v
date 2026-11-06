(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 152 of its 197 lines of code are new or changed and 359 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: the call of kernel at 0x83584
   (+0xdac .. +0xdb0), from the cut r_d_inv to the cut r_k_inv at its return (+0xdb4). Kernel's contract
   (kernel_c.v `kernel_acontract`) is the Section hypothesis KERNEL; the call is made in the read arms' three steps
   (Kpre.v lf_kernel_apre / lf_kernel_ard, ArmR.v ar_leaf_call, Kpost.v lf_kernel_post), as op_unmark's Op3E.v.
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputArmK
  LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputOp0Cut.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis KERNEL : forall fy : YK11.FPState, @kernel_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Lemma r_kcall : forall POST i, 0 <= i <= 47 ->
  FROM POST (r_k_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (r_d_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i Hi HK cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HD.
  destruct HD as (md & mk & P & N & kbs & mbs & gbs & T3 & s & nm & kc & ac & Hsh & Hlr & Hnm & Hkc & Hac & HU).
  destruct HU as (_ & Hcore & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof HB as (HPRE & Hfrm & HGX & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 16 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & _ & R16). unfold LF_MFRAME in R. split; [exact R | exact R16]. }
  assert (Usp : spZ (ms_regs ms3) = lf_sp1 cx).
  { unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  rewrite (aw_ms_eq fy LR_kcall ms3 Hsh).
  pose proof (aw_entry0 (fx := fy) W3 (ms_regs ms3) (ms_mem ms3) LR_kcall ltac:(unfold LLVMF_STK in *; lia)
    ltac:(rewrite Usp; lia)) as HS.
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) aw_extra0))) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs aw_Bx [] (Eimg (Ereg (ms_regs ms3) aw_extra0))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_kcall)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK aw_span; [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  assert (GA : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))) by exact HGA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msA md4 KA (wcarry_on_grows _ _ _ GA) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as Hcur'.
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS; set (EA := Ex) in HS end.
  pmkst HS.
  assert (Hpc : ss_pc ssA = pa_sigma LS_kernel) by reflexivity.
  rewrite Hpc, (lv_sigma LV).
  replace (link_sigma LS_kernel) with KERNEL_A by reflexivity.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2'. prreg HS (3%bv : bv 5) R3'.
  prreg HS (4%bv : bv 5) R4'. prreg HS (10%bv : bv 5) R10.
  rewrite (img_env_codeptr EA HEI) in R1.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EA n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl), R2 in R2'.
  rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl), R3 in R3'.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl), R4 in R4'.
  rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl), R9 in R10.
  pose proof (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  pose proof (lv_text LV) as HBASE.
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite R2'. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (Ra0 : aarg (ms_regs msA) 0 = lf_sp1 cx + LS_P).
  { rewrite ar_aarg0, R10. unfold w64.
    rewrite (unsigned_lit_small (lf_sp1 cx)) by (unfold LLVMF_STK in *; lia).
    apply unsigned_lit_small. unfold LS_P, LLVMF_STK in *. lia. }
  pose proof Hjbk' as (Jk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & Hpl & _).
  pose proof Hcur' as (HcP & HcN & Hcq).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 KERNEL_A) (ms_mem msA) (seg_rom SEGS)) md4)
    with (@cfg_at fy SEGS KERNEL_A (ms_regs msA) (ms_mem msA) md4).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (KERNEL fy).
  - exact HB.
  - exact HJ.
  - exact HRO.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1, HBASE. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite R3'. exact Gp.
  - rewrite R4'. exact Tp.
  - exact Rsp.
  - rewrite KERNEL_AK_val. unfold LLVMF_STK. lia.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia.
  - apply (ar_side_room S3 fp _ Hfr).
    vm_compute. reflexivity.
  - intros a (r & Hin & Hr). unfold kernel_awr in Hin. rewrite Ra0 in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply ar_ajw_G. unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold NK_CHUNK, NK_OPEN in Hr. lia.
    + apply ar_ajw_G. unfold inG, G_HARNESS. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. unfold LONG_ALIAS_SIZE in Hr. lia.
    + apply ar_ajw_stack. unfold LS_P, LLVMF_STK in *. lia.
  - intros a (r & Hin & Hr). unfold kernel_awr in Hin. rewrite Ra0 in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply (ar_not_ro_G HSEGS). unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold NK_CHUNK, NK_OPEN in Hr. lia.
    + apply (ar_not_ro_G HSEGS). unfold inG, G_HARNESS. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. unfold LONG_ALIAS_SIZE in Hr. lia.
    + apply (ar_not_ro_high HSEGS). unfold LS_P, LLVMF_STK in *. lia.
  - intros a Ha.
    pose proof (lf_kernel_ard SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs (ms_regs msA) P N HB HJ HRO Hdat' HcP HcN
      Hcq Ra0 Rsp a Ha) as Hk. rewrite Rsp in Hk. exact Hk.
  - exact (lf_kernel_apre SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs (ms_regs msA) P N HB HJ HRO Hdat' Hpl
      HcP HcN Hcq Ra0 Rsp).
  - intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    destruct (lf_kernel_post SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N ly3 S3 W3 msA md4 ly2 S2 W2 ms2 md2 (ms_regs msA) regs2
      HB Hfr HJ HJ2 Ra0 Hkp Hsk Hs2 Hperm Hfd Hfs2 Hpost Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat')
      as (kbs' & adv & Hadv & Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & Hnx & _ & _ & _ & _ & Hopd
        & _ & _ & _).
    prreg HS (8%bv : bv 5) R8'. prreg HS (9%bv : bv 5) R9'.
    prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
    prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22.
    prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25.
    prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
    rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in R8'. rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in R9'.
    rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in R18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in R19.
    rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in R20.
    rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in R21.
    rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in R22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in R23.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in R24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in R25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in R26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in R27.
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26
      & P27).
    pose proof Hlr as (L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
    apply (HK cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, (P + adv), (N - adv), kbs', mbs, gbs, T3, s, nm, kc, ac.
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite R1. unfold LR_kret, LR_kcall, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    split.
    { unfold r_regs, ms2. cbn [ms_regs mkst].
      rewrite P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
      repeat split; assumption. }
    split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|].
    split; [|exact Hnx].
    split; [exact Hi|].
    split.
    { unfold lf_core, ms2. cbn [ms_regs mkst]. rewrite P2, P8, P9, P3, P4, R2', R8', R9', R3', R4'.
      repeat split; assumption. }
    split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|].
    split; [exact Hcur2|].
    split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|]. lia.
Qed.
End a.
