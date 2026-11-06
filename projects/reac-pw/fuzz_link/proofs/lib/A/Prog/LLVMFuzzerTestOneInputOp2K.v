(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 181 of its 228 lines of code are new or changed and 357 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): op_mark
   (+0x6a8), its own cut after kernel(&cursor) (0x832a4, ra 0x832a8 = +0xad4), and the kernel call that reaches it.
     o2_k_inv i   +0xad4  kernel has returned; the name the selector picked is in s4 (x20), w_name s nm
   o2_kcall: from the state at the call (any of the selector's four paths), kernel's contract (see
   kernel_c.v) under SRr_bind, to o2_k_inv.
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
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputSel
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation AFL := AF_LLVMFuzzerTestOneInput.
Definition LO2_kret : Z := AF_LLVMFuzzerTestOneInput + 0xad4.   (* 0x832a8 *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variables LF_MO_SET LF_MO_OP : Z.

(* the loop registers of lf_lregs (op_mark keeps them all; the name is in s4) *)
Definition o2_regs (cx : lcx) (md fp i : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 21 = w64 (md + MD_N_MARK) /\
  getr (ms_regs ms3) 22 = w64 md /\
  getr (ms_regs ms3) 23 = w64 (LA_G_NL + 0x40000) /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF.

(* what every cut of the arm carries *)
Definition o2_mem (i md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z))
    (cx : lcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
    : Prop :=
  0 <= i <= 47 /\ lf_core cx ms3 /\ o2_regs cx md fp i ms3 /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 LF_SH0 /\
  lf_slots cx md mk fp W3 ms3 /\ lf_cur cx W3 ms3 P N /\
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3
    T3 [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * i.

(* +0xad4: kernel has returned, the name in s4 *)
Definition o2_k_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (nm : option (list byte)) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_kret ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s nm /\
  o2_mem i md mk P N kbs mbs gbs T3 cx fp k2 ly3 S3 W3 ms3 md3 /\ nk_next kbs = 0.

End b.

Section c.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
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

#[local] Abbreviation FROM POST GI :=
  (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

Lemma o2_kcall : forall POST i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 md mk kbs mbs gbs T3
    (msA : machine_state) mdA P' N' s nm,
  0 <= i <= 47 -> FROM POST (o2_k_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_core cx ms3 -> lf_lregs cx md fp i ms3 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 -> lf_slots cx md mk fp W3 ms3 ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) -> nk_opened kbs <= 64 * i ->
  JRN cx fp ly3 S3 W3 (ms_mem msA) mdA k2 ->
  msA = @mkst fy (ms_regs msA) (Z_to_bv 64 KERNEL_A) (ms_mem msA) (seg_rom SEGS) ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
     getr (ms_regs msA) r = getr (ms_regs ms3) r) ->
  getr (ms_regs msA) 20 = w64 s -> w_name s nm ->
  getr (ms_regs msA) 1 = Z_to_bv 64 (BASE + (AFL + 0xad4)) ->
  aarg (ms_regs msA) 0 = lf_sp1 cx + LS_P ->
  kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
    (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA)) ->
  m_fds mdA = m_fds md3 -> m_fs mdA = m_fs md3 ->
  lf_cur cx W3 msA P' N' ->
  SRr SEGS W3 (mkCfg msA mdA) (POST cx).
Proof.
  intros POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk kbs mbs gbs T3 msA mdA P' N' s nm
    Hi HK HB Hfx HJ3 Hfr Hcore Hlr Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hop HJ Hms KR Hs Hnm R1 Ra0 KA GA Fd Fs Hcur'.
  pose proof HB as (HPRE & Hfrm & HGX & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ3) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  (* the cut kept off the cursor's two words *)
  assert (XN : forall a, lf_cut_fp MS la_nul cx fp md mk T3 a ->
            ~ (lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)).
  { intros a Ha. assert (HFR : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
    assert (Hs1 : spZ (c_regs cx) - LF_MFRAME - 16 <= lf_sp1 cx).
    { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
        as (R & _). lia. }
    destruct (lf_cut_fp_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp k2
      ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ ms3 md3 md mk T3 _ a HB HJ3 HFR Hjbk Hblk Ha) as [Hp | [Hp | Hp]];
      (pose proof (lf_sp1_le cx) as (P1 & P2);
       assert (Hr : 0 <= a < 2 ^ 64) by (unfold LF_MFRAME, LLVMF_STK in *; lia);
       rewrite Z.mod_small by exact Hr; unfold LS_P, LS_N, LF_MFRAME, LLVMF_STK in *; lia). }
  destruct (lf_cut_keep B MT MS la_nul _ cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msA mdA KA (wcarry_on_grows _ _ _ GA) Fd Fs XN Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  assert (R2' : getr (ms_regs msA) 2 = getr (ms_regs ms3) 2) by (apply KR; cbn [In]; tauto).
  assert (R3' : getr (ms_regs msA) 3 = getr (ms_regs ms3) 3) by (apply KR; cbn [In]; tauto).
  assert (R4' : getr (ms_regs msA) 4 = getr (ms_regs ms3) 4) by (apply KR; cbn [In]; tauto).
  pose proof (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  pose proof (lv_text LV) as HBASE.
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 16 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & _ & R16). unfold LF_MFRAME in R. split; [exact R | exact R16]. }
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite R2', R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  pose proof Hjbk' as (Jk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & Hpl & _).
  pose proof Hcur' as (HcP & HcN & Hcq).
  rewrite Hms.
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 KERNEL_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS KERNEL_A (ms_regs msA) (ms_mem msA) mdA).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (KERNEL fy).
  - exact HB.
  - exact HJ.
  - exact HRO.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold AFL, AF_LLVMFuzzerTestOneInput; lia | reflexivity].
  - unfold raZ. rewrite R1, HBASE. rewrite unsigned_lit_small by (unfold link_text, AFL, AF_LLVMFuzzerTestOneInput; lia).
    unfold link_text, AFL, AF_LLVMFuzzerTestOneInput. lia.
  - rewrite R3', R3. exact Gp.
  - rewrite R4', R4. exact Tp.
  - exact Rsp.
  - rewrite KERNEL_AK_val. unfold LLVMF_STK in *. lia.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia.
  - apply (ar_side_room S3 fp _ Hfr). vm_compute. reflexivity.
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
      cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs (ms_regs msA) P' N' HB HJ HRO Hdat' HcP HcN
      Hcq Ra0 Rsp a Ha) as Hk. rewrite Rsp in Hk. exact Hk.
  - exact (lf_kernel_apre SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs (ms_regs msA) P' N' HB HJ HRO Hdat' Hpl
      HcP HcN Hcq Ra0 Rsp).
  - intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    destruct (lf_kernel_post SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P' N' ly3 S3 W3 msA mdA ly2 S2 W2 ms2 md2 (ms_regs msA) regs2
      HB Hfr HJ HJ2 Ra0 Hkp Hsk Hs2 Hperm Hfd Hfs2 Hpost Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat')
      as (kbs' & adv & Hadv & Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & Hnx & _ & _ & _ & _ & Hopd
        & _ & _ & _).
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26
      & P27).
    apply (HK cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, (P' + adv), (N' - adv), s, nm, kbs', mbs, gbs, T3.
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite R1. unfold LO2_kret. repeat split; reflexivity. }
    split; [cbn [ms_regs ms2 mkst]; rewrite P20; exact Hs|].
    split; [exact Hnm|].
    split; [|exact Hnx].
    split; [exact Hi|].
    split.
    { unfold lf_core, ms2. cbn [ms_regs mkst]. rewrite P2, P8, P9, P3, P4.
      rewrite !KR by (cbn [In]; tauto). repeat split; assumption. }
    split.
    { unfold o2_regs, ms2. cbn [ms_regs mkst]. rewrite P19, P21, P22, P23, P24, P25, P26, P27.
      rewrite !KR by (cbn [In]; tauto). repeat split; assumption. }
    split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|].
    split; [exact Hcur2|].
    split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|]. lia.
Qed.

End c.
End a.
