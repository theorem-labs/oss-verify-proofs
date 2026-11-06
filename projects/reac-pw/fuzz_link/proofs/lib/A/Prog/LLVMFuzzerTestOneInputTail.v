(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 109 of its 152 lines of code are new or changed and 361 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): THE LOOP TAIL of the
   walk, +0x1110 .. +0x111c (0x838e4 .. 0x838f0), against the cut interface lib/A/Prog/LLVMFuzzerTestOneInputDefs.v:

     +0x1110  addiw s9, s9, 1          the operation counter i + 1
     +0x1114  addi  a0, zero, 0x30
     +0x1118  bne   s9, a0, -0xb80     i + 1 <> 48: back to the loop head +0x598, operation i + 1
     +0x111c  j     0x294              i + 1 = 48: to the exit +0x13b0

   No instruction reads or writes memory, so every memory clause of lf_tail_inv i is the next cut's
   (Keep.v lf_cut_keep with the empty exception set); the counters of lf_tail_inv i are those of
   lf_lh_inv (i + 1), and at i = 47 those of lf_exit_inv.

     lf_tail : forall POST i, 0 <= i <= 47 ->
               (i < 47 -> FROM POST (LH (i + 1))) -> FROM POST EXIT -> FROM POST (TAIL i)

   Section hypotheses: LAWS : AR_laws pa_segs B (the image instance, for the runner paj_run_x).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LLVMFuzzerTestOneInputDefs LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputLp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the runner's entry state at +0x1110: the registers as their atoms, no region, s9 = i in [0, 47] *)
Definition t_facts : facts := mkFacts [(25%nat, mkAF 0 47 0)] [] [].
Definition t_ss : sstate := mkSS LF_tail sr_atoms [] None t_facts.

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
Hypothesis LAWS : AR_laws pa_segs B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Lemma lf_tail : forall POST i, 0 <= i <= 47 ->
  (i < 47 -> FROM POST (lf_lh_inv B MT MS la_nul LF_MO_SET LF_MO_OP (i + 1))) ->
  FROM POST (lf_exit_inv B MT MS la_nul LF_MO_SET LF_MO_OP) ->
  FROM POST (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i Hi HLH HEX cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HT.
  pose proof HT as (md & mk & P & N & kbs & mbs & gbs & T3 & _ & Hsh & Hcore & Hlr & Hsv & Hhd & Hfs & Hsl & Hcur
    & Hjbk & Hblk & Hdat & Hop).
  pose proof HB as (_ & _ & HGX & _).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  assert (E25 : ew (Eimg (Ereg (ms_regs ms3) [])) 25 = Z_to_bv 64 i).
  { rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat _ _ 25 25%bv eq_refl).
    pose proof Hlr as (_ & _ & _ & _ & _ & R25 & _). exact R25. }
  rewrite (lf_shape_eta fy LF_tail ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  assert (HS : st_ok_pi (fx := fy) pa_segs pa_val (Eimg (Ereg (ms_regs ms3) [])) t_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_tail)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [|split; exact I]. cbn [t_facts f_atoms atoms_ok]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E25, unsigned_lit_small by lia. lia. }
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_tail)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  (* +0x1110 .. +0x1114, to the branch *)
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x1118 taken: i + 1 <> 48, the head of operation i + 1 *)
    rewrite branch_ne_U, (U_atom_off _ 25 i 1 E25), U_lit in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LF_lh; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (kagree_false_trans _ _ _ KA (kagree_frame_nil _ _ _ HFrB)) as KB.
    assert (GB : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
    assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msB) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssB msB _ r HS HA Hr)).
    destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
      W3 msB md4 KB (wcarry_on_grows _ _ _ GB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
      as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
    pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as Hcur'.
    apply (HLH ltac:(lia) cx fy fp k2 ly3 S3 W3 msB md4 HB Hfx HJ Hfr).
    exists md, mk, P, N, kbs, mbs, gbs, T3.
    split; [lia|]. split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
    split; [repeat split; (rewrite KR by (vm_compute; reflexivity)); assumption|].
    split; [|split; [exact Hsv'|split; [exact Hhd'|split; [exact Hfs'|split; [exact Hsl'|split; [exact Hcur'|
      split; [exact Hjbk'|split; [exact Hblk'|split; [exact Hdat'|lia]]]]]]]]].
    split; [rewrite KR by (vm_compute; reflexivity); exact L19|].
    split; [rewrite KR by (vm_compute; reflexivity); exact L21|].
    split; [rewrite KR by (vm_compute; reflexivity); exact L22|].
    split; [rewrite KR by (vm_compute; reflexivity); exact L23|].
    split; [rewrite KR by (vm_compute; reflexivity); exact L24|].
    split; [|split; [rewrite KR by (vm_compute; reflexivity); exact L26 | rewrite KR by (vm_compute; reflexivity); exact L27]].
    rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ ssB msB 25%bv HS).
    replace (sr_get (ss_regs ssB) 25%bv) with (SOff 25 1) by (vm_compute; reflexivity).
    unfold w64. exact (lf_sv_off _ 25 i 1 E25 ltac:(lia) ltac:(lia)).
  - (* +0x1118 not taken: i + 1 = 48, so i = 47; +0x111c j to the exit *)
    rewrite branch_ne_U, (U_atom_off _ 25 i 1 E25), U_lit in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (Hi47 : i = 47) by lia. subst i.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LF_exit; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (kagree_false_trans _ _ _ KA (kagree_frame_nil _ _ _ HFrB)) as KB.
    assert (GB : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
    assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msB) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssB msB _ r HS HA Hr)).
    destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
      W3 msB md4 KB (wcarry_on_grows _ _ _ GB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
      as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
    pose proof Hsl' as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17
      & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29).
    pose proof Hblk' as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17).
    apply (HEX cx fy fp k2 ly3 S3 W3 msB md4 HB Hfx HJ Hfr).
    exists md, mk, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
    split; [repeat split; (rewrite KR by (vm_compute; reflexivity)); assumption|].
    split; [rewrite KR by (vm_compute; reflexivity); exact L19|].
    split; [rewrite KR by (vm_compute; reflexivity); exact L22|].
    split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|].
    split; [exact S15|]. split; [exact S5|]. split; [exact S6|].
    split; [exact Hjbk'|].
    do 6 (split; [assumption|]).
    split; [intros Heq; subst mk; unfold apart, MD_SIZE, MK_SIZE in B11; lia|].
    split; [exact B14 | exact B15].
Qed.
End a.
