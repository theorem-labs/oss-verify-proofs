(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 425 of its 472 lines of code are new or changed and 1285 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   the loop of the inlined `remember` (+0x119c .. +0x11bc, then +0x11f4 .. +0x11fc; listing
   (internal path) (internal record, sha256 e84d6f0c6974)).

     +0x119c .. +0x11a4  strcmp(m + MD_MARK + 16 j, name) (the wrapper at 0x83978, LinkWalk.v aj_gx_strcmp_at over
                         RtString.v astrcmp_realizes, the Section hypothesis STRCMP)
     +0x11a8             beqz a0 -> +0x11f4 (the name is kept: the marks stay)
     +0x11ac .. +0x11b4  s10--, s2 += 16; bnez s10 -> +0x119c (turn j + 1)
     +0x11b8 .. +0x11bc  31 < n -> +0x11f4 (32 names kept: the marks stay); else +0x11c0 (o2_a_inv, the append)
     +0x11f4 .. +0x11fc  s10 := F + 0x20, s6 := m (the spill slots), -> +0xc0c (o2_u_inv)

   o2_lc   : forall POST i j, FROM POST (o2_s_inv i j) -> FROM POST (o2_l_inv i j)       (the call)
   o2_lb   : forall POST i j, FROM POST (o2_u_inv i) -> FROM POST (o2_a_inv i) -> FROM POST (o2_l_inv i (j + 1)) ->
             FROM POST (o2_s_inv i j)                                                 (the branches)
   o2_loop : forall POST i, FROM POST (o2_u_inv i) -> FROM POST (o2_a_inv i) -> forall j, FROM POST (o2_l_inv i j).

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
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c model_decide_c index_of_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2Cut LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputOp5
  LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C LLVMFuzzerTestOneInputOp2R LLVMFuzzerTestOneInputDec
  LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3W LLVMFuzzerTestOneInputOp2D LLVMFuzzerTestOneInputOp2Nm
  LLVMFuzzerTestOneInputOp2V LLVMFuzzerTestOneInputOp2Ml.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkPfPiece LinkSnpDef LinkSnpJ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSnp rememberPost
  LLVMFuzzerTestOneInputOp2M LLVMFuzzerTestOneInputOp2X LinkWalkStrArg rememberCalls.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LO2_s : Z := AF_LLVMFuzzerTestOneInput + 0x11a8.   (* 0x8397c, strcmp's return *)
Definition o2l_l_ss : sstate := mkSS LO2_l sr_atoms [] None (mkFacts [] [] []).

(* the runner's state at +0x11a8: the two spill slots the exit reloads (atom 32 = F + 0x20, atom 33 = m) *)
Definition o2l_fr : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x78 0xf0 0x78 0x78 [o2m_c8 0x78 (SOff 32 0); o2m_c8 0xe8 (SOff 33 0)].
Definition o2l_s_ss : sstate :=
  mkSS LO2_s sr_atoms [o2l_fr] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).

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
Hypothesis STRCMP : forall fy : YK11.FPState,
  @RtString.astrcmp_realizes fy rc pa_segs B (pa_sigma LS___interceptor_trampoline_strcmp).

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* +0x11a8: strcmp has answered on slot j *)
Definition o2_s_inv (i j : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_s ms3 /\
  o2_rm B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N s t kbs mbs gbs T3 cx fp k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 18 = w64 (md + MD_MARK + MARK_LEN * j) /\
  getr (ms_regs ms3) 26 = w64 (md_n_mark mbs - j) /\
  0 <= j < md_n_mark mbs /\ (forall k, 0 <= k < j -> o2l_slot mbs k <> t) /\
  (getr (ms_regs ms3) 10 = w64 0 <-> o2l_slot mbs j = t).

Lemma o2_lc : forall POST i j,
  FROM POST (o2_s_inv i j) -> FROM POST (o2_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j).
Proof.
  intros POST i j HSI cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HL.
  destruct HL as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & RM & R18 & R26 & Hj & Hne).
  pose proof RM as (R20 & Hw & Hlt & R21 & R22 & HM & Hare & R23 & Hrq & Hmm).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2l_l_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_l)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2l_l_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  rewrite (lf_shape_eta fy LO2_l ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_l)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
  pmkst HS.
  assert (Hpc : ss_pc ssA = pa_sigma LS___interceptor_trampoline_strcmp) by reflexivity.
  rewrite Hpc.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  try rewrite (img_env_codeptr E HEI) in Q1.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
  rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q10.
  rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q11.
  rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
  rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20. rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21.
  rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in Q23.
  rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
  rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
  assert (HMB : o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 msA md4)
    by exact (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs mbs gbs
      T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msA md4 HM SH_M_len KA (fun a _ H => H) HGA Fd Fs Q2 Q3 Q4 Q8 Q9 Q19 Q24
      Q25 Q27).
  pose proof HMB as (_ & _ & _ & HsvA & HhdA & HfsA & HslA & HcurA & HjbkA & HblkA & HdatnA & _).
  pose proof HjbkA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROA & _).
  pose proof HdatnA as (_ & _ & _ & _ & _ & _ & DmdA & DmwfA & _ & _ & _ & DgnA & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_lt as CL. pose proof alloc_ceiling_value as CV.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msA) md4 k2 HB HJ) as (H16 & Hceil & _ & Hshi & Hs47 & Hpres & HARA).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msA) md4 k2 HB HJ) as (Hs1 & H16' & Hlo & H47).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite Q2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. clia. }
  set (n := md_n_mark mbs) in *.
  pose proof DmwfA as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm.
  set (p := md + MD_MARK + MARK_LEN * j).
  destruct (o2m_slot_cstr _ md mbs j DmdA DmwfA ltac:(lia)) as (Hsc & Hsl16).
  set (sx := o2l_slot mbs j) in *.
  assert (HK : alloc_ceiling <= spZ (ms_regs msA) - 8192) by (rewrite Rsp; unfold LLVMF_STK in *; clia).
  destruct (o2_name_rt B TB HSEGS ly3 S3 W3 (ms_mem msA) md4 (ms_regs msA) 8192 s t HARA HROA DgnA HK Hw)
    as (Hac & Hrt & Hs16 & Hl11 & Hloc).
  pose proof (o2r_cmp_of_rt _ _ _ _ _ Hrt) as Ycmp.
  pose proof HblkA as (Bmd & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem msA) md4 md MD_SIZE HARA Bmd) as (_ & Bm4 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  assert (Hpr : md <= p /\ p + (Z.of_nat (length sx) + 1) <= md + MD_SIZE)
    by (unfold p, MD_MARK, MARK_LEN, MD_SIZE in *; clia).
  destruct (lf_md_sub SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
    (ms_mem msA) md4 k2 md mk T3 (ms_regs msA) 8192 p (Z.of_nat (length sx) + 1) HB HJ HblkA Rsp
    ltac:(unfold LLVMF_STK; lia) (proj1 Hpr) (proj2 Hpr) ltac:(lia)) as (Xra & Xhv & Xam & Xap).
  pose proof (lf_md_tail SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
    (ms_mem msA) md4 k2 md mk T3 p (Z.of_nat (length sx) + 1) HB HJ HblkA (proj1 Hpr) (proj2 Hpr) ltac:(lia)) as Xtl.
  assert (Xcmp : astrcmp_arg SEGS (ms_regs msA) 8192 (rdW W3 (ms_mem msA)) p sx).
  { split; [unfold p in *; clia|]. split; [lia|]. split; [exact Xam|]. split; [exact Xra|]. split; [exact Xhv|].
    split; [exact Xap|]. intros a Ha. apply Xtl. replace (Z.of_nat (length sx) + 1 - 1) with (Z.of_nat (length sx))
      by lia. exact Ha. }
  assert (UN0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs msA) - 8192 <= a < spZ (ms_regs msA)) ->
    aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) (ms_mem msA) a) by reflexivity.
  assert (STK0 : forall a, spZ (ms_regs msA) - 8192 <= a < spZ (ms_regs msA) -> aview SEGS (w_H W3) (ms_mem msA) a <> None).
  { intros a Ha. apply aview_some_of_apresent. apply Hpres. rewrite Rsp in Ha. unfold LLVMF_STK in *. clia. }
  assert (CL1 : 2 ^ 46 <= spZ (ms_regs msA) - 8192) by (rewrite Rsp; unfold LLVMF_STK in *; clia).
  assert (CL2 : spZ (ms_regs msA) <= 2 ^ 47) by (rewrite Rsp; unfold LLVMF_STK in *; clia).
  destruct (astr_call SEGS W3 (ms_regs msA) (ms_regs msA) (ms_mem msA) (ms_mem msA) 8192 0 p sx ltac:(lia)
    ltac:(unfold ESTACK; lia) ltac:(lia) CL1 CL2 UN0 STK0 Hsc Xcmp) as (AX1 & AX2 & AX3).
  destruct (astr_call SEGS W3 (ms_regs msA) (ms_regs msA) (ms_mem msA) (ms_mem msA) 8192 0 s t ltac:(lia)
    ltac:(unfold ESTACK; lia) ltac:(lia) CL1 CL2 UN0 STK0 Hac Ycmp) as (AY1 & AY2 & AY3).
  eapply SRr_bind.
  { eapply (aj_gx_strcmp_at SK SEGS B LAWS pa_segs_low _ (STRCMP fy)) with (x := p) (y := s) (sx := sx) (sy := t).
    - exact HGX.
    - exact HJ.
    - rewrite Rsp. exact H16'.
    - rewrite Rsp. unfold ESTACK, LLVMF_STK in *. clia.
    - rewrite Rsp. unfold LLVMF_STK in *. clia.
    - rewrite Q3, R3. exact (proj1 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)).
    - rewrite Q4, R4. exact (proj2 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)).
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q10, R18. reflexivity.
    - rewrite Q11, R20. reflexivity.
    - unfold p in *. clia.
    - clia.
    - exact AX1.
    - exact AY1.
    - exact AX2.
    - exact AY2.
    - exact AX3.
    - exact AY3.
    - intros a Hrom Hno Herr. apply HROA; [left; exact Hrom | exact Hno | exact Herr]. }
  cbv beta. intros W2 c2 HWle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HRES & HKP2 & HPR2 & HSM2).
  set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
  change mem2 with (ms_mem ms2) in HJ2, HKP2, HPR2.
  assert (Fd2 : m_fds md2 = m_fds md4) by (unfold same_but_materialized in HSM2; rewrite HSM2; reflexivity).
  assert (Fs2 : m_fs md2 = m_fs md4) by (unfold same_but_materialized in HSM2; rewrite HSM2; reflexivity).
  set (X2 := fun a => ~ (0 <= a < 2 ^ 64) \/ (lf_sp1 cx - 2 * ESTACK <= a < lf_sp1 cx)).
  assert (KB2 : kagree SEGS X2 (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem ms2))).
  { apply kagree_of_aview. intros a Ha. unfold X2 in Ha. apply HKP2; [tauto|]. rewrite Rsp. tauto. }
  assert (GB2 : mem_grows (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem ms2))) by exact (ar_grows _ _ _ HPR2).
  assert (NX2 : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> ~ X2 a).
  { intros a Hf HXa. destruct (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 msA md4 a HB HJ Hfr HjbkA HblkA Hf) as (R0 & R1).
    unfold X2 in HXa. unfold ESTACK, LLVMF_STK in *. clia. }
  pose proof (ar_pres _ _ HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
  apply (HSI cx fy fp k2 ly3 S3 W3 ms2 md2 HB Hfx HJ2 Hfr).
  exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
  split.
  { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    rewrite Q1. unfold LO2_s, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
  cbn [ms_regs ms2 mkst].
  split.
  { unfold o2_rm. cbn [ms_regs ms2 mkst]. split; [rewrite P20, Q20; exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite P21, Q21; exact R21|]. split; [rewrite P22, Q22; exact R22|].
    split.
    { apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP X2 i md mk P N kbs mbs gbs T3 SH_M cx fp k2
        ly3 S3 W3 msA md4 ms2 md2 HMB SH_M_len KB2 NX2 GB2 ltac:(rewrite Fd2; exact Fd) ltac:(rewrite Fs2; exact Fs));
        cbn [ms_regs ms2 mkst]; assumption. }
    split; [exact Hare|]. split; [rewrite P23, Q23; exact R23|]. split; [exact Hrq | exact Hmm]. }
  split; [rewrite P18, Q18; exact R18|]. split; [rewrite P26, Q26; exact R26|].
  split; [exact Hj|]. split; [exact Hne | exact HRES].
Qed.

Lemma o2_lb : forall POST i j,
  FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_a_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (o2_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i (j + 1)) -> FROM POST (o2_s_inv i j).
Proof.
  intros POST i j HU HA0 HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HSI.
  destruct HSI as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & RM & R18 & R26 & Hj & Hne & HRES).
  pose proof RM as (R20 & Hw & Hlt & R21 & R22 & HM & Hare & R23 & Hrq & Hmm).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hdatn as (_ & _ & _ & _ & _ & _ & Dmd & Dmwf & _).
  pose proof Dmwf as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm.
  set (n := md_n_mark mbs) in *.
  destruct (o5_geo SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)
    as (Hal0 & Hceil0 & H470 & Hsp1r & Hsp132 & Hsp146).
  pose proof alloc_ceiling_lt as CL.
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SWA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & SM & _).
  unfold lf_slot, lf_at in SWA, SM. apply o5_vm_of_rd in SWA, SM. unfold LS_WA, LS_M in SWA, SM.
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & _).
  pose proof (o5_aj_AR SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
  pose proof Hblk as (Bmd & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & Bm4 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (lf_F cx fp + LO_WA); Z_to_bv 64 md])) in *.
  assert (EL : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr (ms_regs ms3) r).
  { intros n0 r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n0 r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 (lf_F cx fp + LO_WA))
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 md) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx)
    by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; clear - Hsp146 Hsp1r H470; lia).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2l_s_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_s)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2l_s_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, o2l_fr, o2m_c8.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hsp146; lia|]. split; [clear - Hsp146 Hsp1r H470; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0x78 8 (SOff 32 0) (lf_F cx fp + LO_WA));
          [ cbn [sv_denot]; rewrite E32, unsigned_lit_small by (unfold LO_WA; clear - F4 Fc CL; lia);
            rewrite Z.add_0_r; reflexivity
          | unfold LO_WA; cbn; clear - F4 Fc CL; lia | cbn; lia | exact SWA ].
      + apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0xe8 8 (SOff 33 0) md);
          [ cbn [sv_denot]; rewrite E33, unsigned_lit_small by (clear - Bm4 Bmceil CL; lia);
            rewrite Z.add_0_r; reflexivity
          | cbn; clear - Bm4 Bmceil CL; lia | cbn; lia | exact SM ].
    - cbn. tauto.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
      split; [|exact I]. clear - Hsp146 Hsp1r H470 Hsp132. change (2 ^ 5) with 32. lia. }
  rewrite (lf_shape_eta fy LO2_s ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_s)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (split; [intros n0 Hn0; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia;
                reflexivity | unfold E; reflexivity]).
  assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by exact (EL 10%nat 10%bv ltac:(lia) eq_refl).
  assert (E21 : ew E 21 = w64 n) by (rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
  assert (E26 : ew E 26 = w64 (n - j)) by (rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl); exact R26).
  assert (E18 : ew E 18 = w64 (md + MD_MARK + MARK_LEN * j)) by (rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl); exact R18).
  assert (HmdS : md + MD_SIZE <= 2 ^ 47) by (unfold MD_SIZE; clear - Bmceil CL; lia).
  (* the model's marks are kept when the name is there or 32 names are *)
  assert (KEEPM : remember (md_marks mbs) t = md_marks mbs -> md_marks mbs = m_marks (o2_MM (Some t) kbs gbs)).
  { intros Hr. rewrite Hmm. destruct Hare as (_ & Hm). rewrite Hm. symmetry. exact Hr. }
  (* the cut +0xc0c from a stop there *)
  assert (CLOSEU : forall ss msC md5, st_ok_pi (fx := fy) SEGS pa_val E ss (restrict (w_H W3) msC) ->
    ss_pc ss = LO2_u -> ss_resv ss = None ->
    sr_get (ss_regs ss) 22%bv = SOff 33 0 -> sr_get (ss_regs ss) 26%bv = SOff 32 0 ->
    (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 23%bv; 24%bv; 25%bv; 27%bv] ->
       sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0) ->
    ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem msC) md5 k2 ->
    kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC)) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC)) ->
    m_fds md5 = m_fds md3 -> m_fs md5 = m_fs md3 ->
    remember (md_marks mbs) t = md_marks mbs ->
    SRr SEGS W3 (mkCfg msC md5) (POST cx)).
  { intros ss msC md5 HSC Hpc Hrv R22s R26s KRs HJC KC GC Fd5 Fs5 Hrem.
    assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 23%bv; 24%bv; 25%bv; 27%bv] ->
      getr (ms_regs msC) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ss msC _ r HSC HA (KRs r Hr))).
    apply (HU cx fy fp k2 ly3 S3 W3 msC md5 HB Hfx HJC Hfr).
    exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
    split; [rewrite <- Hpc; exact (lf_shape_of_st_ok fy W3 _ ss msC HSC Hrv)|].
    split; [rewrite KR by sel_inbv; exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msC 22%bv HSC), R22s; cbn [sv_denot];
            rewrite E33, unsigned_lit_small by (clear - Bm4 Bmceil CL; lia); rewrite Z.add_0_r; reflexivity|].
    split; [rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msC 26%bv HSC), R26s; cbn [sv_denot];
            rewrite E32, unsigned_lit_small by (unfold LO_WA; clear - F4 Fc CL; lia); rewrite Z.add_0_r; reflexivity|].
    split.
    { apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs mbs gbs
        T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msC md5 HM SH_M_len KC (fun a _ H => H) GC Fd5 Fs5);
        rewrite KR by sel_inbv; reflexivity. }
    split; [rewrite KR by sel_inbv; exact R23|]. split; [exact Hrq | exact (KEEPM Hrem)]. }
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x11a8 taken: the name is in slot j; the marks stay *)
    rewrite o2_beqz_any, E10 in Hc. apply Z.eqb_eq, o2_w64_0, HRES in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_u; [apply ar_awr_nowin; vm_compute; reflexivity|].
    rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
    pose proof (ar_kagree_nowin _ _ _ _ HFrC ltac:(vm_compute; reflexivity)) as KC.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
    apply (CLOSEU ssC msC md5 HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(intros r Hr; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr) HJ KC HGC
      ltac:(subst md5; rewrite !lf_wvb_fds; reflexivity) ltac:(subst md5; rewrite !lf_wvb_fs; reflexivity)).
    apply o2l_rem_in; [lia|]. exists j. split; [lia | exact Hc].
  - rewrite o2_beqz_any, E10 in Hc. apply Z.eqb_neq in Hc.
    assert (Hsj : o2l_slot mbs j <> t) by (intros Ht; apply Hc; apply (proj2 HRES) in Ht; rewrite Ht; reflexivity).
    clear Hc.
    paj_run_tok RUN HS HJ SHOK (0, 0); [apply ar_awr_nowin; vm_compute; reflexivity|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (ar_kagree_nowin _ _ _ _ HFrA ltac:(vm_compute; reflexivity)) as KA.
    psrr_branch_tok RUN BR HS SHOK (0, 0).
    + (* +0x11b4 taken: turn j + 1 *)
      rewrite branch_ne_U, U_SOff, U_SLit, E26 in Hc. unfold w64 in Hc.
      rewrite unsigned_lit_small in Hc by lia. unfold zcanon, M64 in Hc.
      rewrite (Z.mod_small (n - j + -1)), (Z.mod_small 0) in Hc by lia.
      apply Bool.negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_l; [apply ar_awr_nowin; vm_compute; reflexivity|].
      rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
      pose proof (ar_kagree_nowin _ _ _ _ HFrC ltac:(vm_compute; reflexivity)) as KC0.
      assert (KC : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC)))
        by (intros a0 Ha0; rewrite (KC0 a0 Ha0), (KA a0 Ha0); reflexivity).
      assert (GC : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC))) by (intros x Hx; apply HGC, HGA, Hx).
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
      assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
      assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
      lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
      assert (KR : forall r : bv 5, sr_get (ss_regs ssC) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
        getr (ms_regs msC) r = getr (ms_regs ms3) r)
        by (intros r Hr; exact (lf_reg_atom fy W3 _ ssC msC _ r HS HA Hr)).
      prreg HS (18%bv : bv 5) Q18. prreg HS (26%bv : bv 5) Q26.
      apply (HL cx fy fp k2 ly3 S3 W3 msC md5 HB Hfx HJ Hfr).
      exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
      split; [exact (lf_shape_of_st_ok fy W3 _ ssC msC HS eq_refl)|].
      split.
      { unfold o2_rm. split; [rewrite KR by (vm_compute; reflexivity); exact R20|]. split; [exact Hw|].
        split; [exact Hlt|]. split; [rewrite KR by (vm_compute; reflexivity); exact R21|].
        split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
        split.
        { apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs mbs
            gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msC md5 HM SH_M_len KC (fun a _ H => H) GC Fd5 Fs5);
            rewrite KR by (vm_compute; reflexivity); reflexivity. }
        split; [exact Hare|]. split; [rewrite KR by (vm_compute; reflexivity); exact R23|].
        split; [exact Hrq | exact Hmm]. }
      split; [rewrite Q18, E18; unfold w64; rewrite unsigned_lit_small by (unfold MD_MARK, MARK_LEN, MD_SIZE in *; lia);
              f_equal; unfold MARK_LEN; lia|].
      split; [rewrite Q26, E26; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
      split; [lia|]. intros k Hk. destruct (Z.eq_dec k j) as [-> | Hkj]; [exact Hsj | apply Hne; lia].
    + rewrite branch_ne_U, U_SOff, U_SLit, E26 in Hc. unfold w64 in Hc.
      rewrite unsigned_lit_small in Hc by lia. unfold zcanon, M64 in Hc.
      rewrite (Z.mod_small (n - j + -1)), (Z.mod_small 0) in Hc by lia.
      apply Bool.negb_false_iff, Z.eqb_eq in Hc. assert (Hjn : j = n - 1) by lia. clear Hc.
      paj_run_tok RUN HS HJ SHOK (0, 0); [apply ar_awr_nowin; vm_compute; reflexivity|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      pose proof (ar_kagree_nowin _ _ _ _ HFrB ltac:(vm_compute; reflexivity)) as KB0.
      assert (KB : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)))
        by (intros a0 Ha0; rewrite (KB0 a0 Ha0), (KA a0 Ha0); reflexivity).
      assert (GB : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
      psrr_branch_tok RUN BR HS SHOK (0, 0).
      * (* 31 < n: 32 names are kept; the marks stay *)
        rewrite YO0c.branch_lt in Hc. cbn [sv_denot] in Hc. rewrite E21 in Hc. unfold w64 in Hc.
        rewrite (unsigned_lit_small n), Z.add_0_r in Hc by lia.
        rewrite !unsigned_lit_small in Hc by lia. rewrite !YO0b.s64_small in Hc by lia.
        apply Z.ltb_lt in Hc.
        assert (Hn32 : md_n_mark mbs = 32) by (change (md_n_mark mbs) with n; lia).
        paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_u; [apply ar_awr_nowin; vm_compute; reflexivity|].
        rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
        pose proof (ar_kagree_nowin _ _ _ _ HFrC ltac:(vm_compute; reflexivity)) as KC0.
        lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
        lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
        apply (CLOSEU ssC msC md5 HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(intros r Hr; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr) HJ
          ltac:(intros a0 Ha0; rewrite (KC0 a0 Ha0), (KB a0 Ha0); reflexivity)
          ltac:(intros x Hx; apply HGC, GB, Hx)
          ltac:(subst md5; rewrite !lf_wvb_fds; reflexivity) ltac:(subst md5; rewrite !lf_wvb_fs; reflexivity)).
        apply o2l_rem_full. exact Hn32.
      * (* n <= 31: the append *)
        rewrite YO0c.branch_lt in Hc. cbn [sv_denot] in Hc. rewrite E21 in Hc. unfold w64 in Hc.
        rewrite (unsigned_lit_small n), Z.add_0_r in Hc by lia.
        rewrite !unsigned_lit_small in Hc by lia. rewrite !YO0b.s64_small in Hc by lia.
        apply Z.ltb_ge in Hc. assert (Hn31 : n <= 31) by lia.
        paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_a; [apply ar_awr_nowin; vm_compute; reflexivity|].
        rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
        pose proof (ar_kagree_nowin _ _ _ _ HFrC ltac:(vm_compute; reflexivity)) as KC0.
        assert (KC : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC)))
          by (intros a0 Ha0; rewrite (KC0 a0 Ha0), (KB a0 Ha0); reflexivity).
        assert (GC : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC))) by (intros x Hx; apply HGC, GB, Hx).
        lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
        assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
        assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
        lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
        assert (KR : forall r : bv 5, sr_get (ss_regs ssC) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
          getr (ms_regs msC) r = getr (ms_regs ms3) r)
          by (intros r Hr; exact (lf_reg_atom fy W3 _ ssC msC _ r HS HA Hr)).
        apply (HA0 cx fy fp k2 ly3 S3 W3 msC md5 HB Hfx HJ Hfr).
        exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
        split; [exact (lf_shape_of_st_ok fy W3 _ ssC msC HS eq_refl)|].
        split.
        { unfold o2_rm. split; [rewrite KR by (vm_compute; reflexivity); exact R20|]. split; [exact Hw|].
          split; [exact Hlt|]. split; [rewrite KR by (vm_compute; reflexivity); exact R21|].
          split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
          split.
          { apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs mbs
              gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msC md5 HM SH_M_len KC (fun a _ H => H) GC Fd5 Fs5);
              rewrite KR by (vm_compute; reflexivity); reflexivity. }
          split; [exact Hare|]. split; [rewrite KR by (vm_compute; reflexivity); exact R23|].
          split; [exact Hrq | exact Hmm]. }
        split; [lia|]. intros k Hk. destruct (Z.eq_dec k j) as [-> | Hkj]; [exact Hsj | apply Hne; lia].
Qed.

(* the loop, by the turns left *)
Lemma o2_loop : forall POST i,
  FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_a_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  forall j, FROM POST (o2_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j).
Proof.
  intros POST i HU HA0.
  assert (IND : forall k j, (Z.to_nat (32 - j) <= k)%nat -> FROM POST (o2_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j)).
  { induction k as [|k IH]; intros j Hk.
    - intros cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HL. exfalso.
      destruct HL as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & _ & RM & _ & _ & Hj & _).
      pose proof RM as (_ & _ & _ & _ & _ & HM & _). pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdatn & _).
      pose proof Hdatn as (_ & _ & _ & _ & _ & _ & _ & Dmwf & _).
      pose proof Dmwf as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm. lia.
    - apply o2_lc. apply o2_lb; [exact HU | exact HA0 |]. apply IH. lia. }
  intros j. exact (IND _ j (le_n _)).
Qed.

End a.
