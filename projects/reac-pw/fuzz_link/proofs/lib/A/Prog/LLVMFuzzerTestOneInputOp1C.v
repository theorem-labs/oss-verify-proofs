(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 290 of its 338 lines of code are new or changed and 1284 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write's model_write (0x83858). From the cut after
   model_begin (+0x1078, w_b_inv): `ld a0, 0xe8(s1); mv a1, s5; mv a2, s6; jal model_write`, the call under
   model_write_c.v's contract (the Section hypothesis MODEL_WRITE, model_write_c), to the cut at
   its return (+0x1088, w_m_inv). The name is the selector's (Nm.v), the alias the text_of answer (Dec.v dec_rt_ok);
   the model block and g_nl's ranges are Mdl.v's; the cut after is Mdl.v's lf_model_after.

   w_bm : forall POST i, FROM POST (w_m_inv i) -> FROM POST (w_b_inv i).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c kernel_c model_write_c index_of_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMb.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3K.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmH.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMdl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require reac_served_mark_aux.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputNm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1Lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the registers op_write keeps from model_begin's end to the loop tail *)
Definition W_R : list Z := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma W_R_saved : forall r, In r W_R -> acallee_saved r.
Proof. intros r Hr. unfold acallee_saved. cbn in Hr. lia. Qed.
Lemma W_R_low : forall r, In r W_R -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.

(* the selector's name pointer is a 47-bit address or NULL *)
Lemma w_name_range : forall s nm, w_name s nm -> 0 <= s < 2 ^ 47.
Proof.
  intros s nm [(-> & _) | [(k & Hk & -> & _) | (j & Hj & -> & _)]].
  - lia.
  - unfold LA_G_NAMES. lia.
  - rewrite w_odd_ptrs. do 6 (destruct j as [|j]; [cbn; lia|]). lia.
Qed.

(* the name as a string argument *)
Lemma w_name_arg : forall segs m s nm, w_name s nm -> (forall x, nm = Some x -> acstr_at segs m s x) ->
  astr_arg segs m s nm.
Proof.
  intros segs m s nm Hw Hc. destruct nm as [x|].
  - split; [|exact (Hc x eq_refl)].
    destruct Hw as [(_ & Hn) | [(k & Hk & -> & _) | (j & Hj & -> & _)]]; [discriminate| |].
    + unfold LA_G_NAMES. lia.
    + rewrite w_odd_ptrs. do 6 (destruct j as [|j]; [cbn; lia|]). lia.
  - destruct Hw as [(Hs0 & Hn0) | [(k & Hk & Hs1 & Hn) | (j & Hj & Hs1 & Hn)]]; [exact Hs0 | discriminate | discriminate].
Qed.

(* the errno table's codes are positive 31-bit numbers *)
Lemma w_errno_tab_range : forall e, In e nl_errno_tab -> 0 <= e < 2 ^ 31.
Proof. intros e He. cbn in He. unfold E_NOBUFS, E_INTR, E_AGAIN, E_PERM, E_MFILE, E_CONNREFUSED in He. lia. Qed.

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
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
(* model_write, as proved (model_write_c.v) *)
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Lemma w_bm : forall POST i,
  FROM POST (w_m_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (w_b_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HBI.
  destruct HBI as (md & mk & P & N & s & s6v & own1 & nm & t & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore & Hreg &
    Hnm & R20 & HC & Hcur & Hop & HD & HTX & HSL & Hnb & Hown & Hfresh & _ & _ & Hend & Hsock & Hsend & KSEQ & REQ0 &
    SENT0 & _).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  assert (Hs32 : lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (_ & R32 & _). exact R32. }
  pose proof HC as (_ & _ & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSM & _).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR Bmd) as (_ & Bm4096 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  assert (HU9 : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx)
    by (rewrite R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HSM) as Rmd.
  rewrite (lf_shape_eta fy LW_mb ms3 Hsh).
  pose proof (d4_entry_l fy W3 (ms_regs ms3) (ms_mem ms3) LW_mb LS_M md ltac:(rewrite HU9; unfold LLVMF_STK in *; lia)
    ltac:(rewrite HU9; exact Hs32) ltac:(unfold LS_M; lia) Rmd ltac:(vm_compute; reflexivity)
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HSM))) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md]))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_mb)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md]))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 md]) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 md)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ W_R HS EL W_R_low ltac:(d4chk)) as KR.
  assert (KA : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { intros a _. unfold mbyte. rewrite (HFrA (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
    lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  pose proof (d4_dec_run B ly3 S3 _ _ s6v t KA HD) as HDA.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KA (fun _ _ _ _ H => H)) as HTXA.
  pose proof (d4_slot_run W3 (ms_mem ms3) (ms_mem msA) _ _ KA HSL) as HSLA.
  clear HD HTX HSL Hcur HC Hsv Hhd Hfs Hsl Hjbk Hblk Hdat.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  try rewrite E32 in Q10.
  ew_reg EL 21%nat (21%bv : bv 5) Q11. ew_reg EL 22%nat (22%bv : bv 5) Q12.
  rewrite R21 in Q11. rewrite R22 in Q12. rewrite HBASE in Q1.
  pose proof HCA as (HJA & HfrA & HsvA & HhdA & HfsA & HslA & HjbkA & HblkA & HdatA).
  pose proof HjbkA as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HJA as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _). pose proof HARA as (MA & _).
  kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (HK8 : 0 <= MODEL_WRITE_AK <= LLVMF_STK - 448) by (rewrite MODEL_WRITE_AK_val; unfold LLVMF_STK; lia).
  assert (HKc : alloc_ceiling <= spZ (ms_regs msA) - MODEL_WRITE_AK)
    by (rewrite Rsp, MODEL_WRITE_AK_val; unfold LLVMF_STK in *; lia).
  destruct (dec_rt_ok B LAWS TB HSEGS ly3 S3 W3 (ms_mem msA) mdA (ms_regs msA) MODEL_WRITE_AK s6v t HARA HRO HKc HDA)
    as (Tcs & Trt & Tlen & Tnz).
  pose proof Trt as (T0 & T31 & Tam & Tra & Thv & Ttail & Tfr).
  pose proof (w_name_range s nm Hnm) as Rs.
  assert (Ra0 : aarg (ms_regs msA) 0 = md) by (rewrite ar_aarg0, Q10; apply unsigned_lit_small; lia).
  assert (Ra1 : aarg (ms_regs msA) 1 = s) by (rewrite ar_aarg1, Q11; unfold w64; apply unsigned_lit_small; lia).
  assert (Ra2 : aarg (ms_regs msA) 2 = s6v).
  { rewrite ar_aarg2, Q12. unfold w64. apply unsigned_lit_small. unfold amem_range, kLowMemEnd, kHighMemEnd in Tam. lia. }
  (* the name's facts *)
  assert (NM : forall x, nm = Some x ->
    acstr_at SEGS (rdW W3 (ms_mem msA)) s x /\ astrcmp_arg SEGS (ms_regs msA) MODEL_WRITE_AK (rdW W3 (ms_mem msA)) s x).
  { intros x ->. split.
    - exact (proj1 (lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x HB HJA HRO HdatA Hnm)).
    - exact (lf_name_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x (ms_regs msA) MODEL_WRITE_AK HB HJA HRO HdatA Rsp HK8
        Hnm). }
  assert (NMA : astr_arg SEGS (rdW W3 (ms_mem msA)) s nm) by (apply (w_name_arg _ _ s nm Hnm); intros x Hx; exact (proj1 (NM x Hx))).
  assert (TA : astr_arg SEGS (rdW W3 (ms_mem msA)) s6v (Some t)) by (split; [exact Tnz | exact Tcs]).
  pose proof HdatA as (Dk & Dwf & Dtab & _ & _ & _ & Dmd & Dmwf & _).
  destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
    cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk T3 (ms_regs msA) MODEL_WRITE_AK HB HJA HblkA Rsp HK8)
    as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof HblkA as (BmdA & BmkA & BmcA & _ & _ & _ & _ & _ & BmtA & _).
  replace (pa_sigma LS_model_write) with MODEL_WRITE_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 MODEL_WRITE_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS MODEL_WRITE_A (ms_regs msA) (ms_mem msA) mdA).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (MODEL_WRITE fy).
  - exact HB.
  - exact HJA.
  - exact HRO.
  - rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite K3, R3. exact Gp.
  - rewrite K4, R4. exact Tp.
  - exact Rsp.
  - exact HK8.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia.
  - apply (ar_side_room S3 fp _ HfrA). vm_compute. reflexivity.
  - intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
    destruct Hin as [<- | []]; cbn [fst snd] in Hr.
    apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a BmdA BmcA). unfold MD_SIZE in *. clia.
  - intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
    intros Hro. pose proof (lf_roP_bounds a Hro) as RB.
    destruct Hin as [<- | []]; cbn [fst snd] in Hr.
    unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in *. clia.
  - (* the read set *)
    intros a [(Hz1 & u & Hu & Ha) | [(Hz1 & u & Hu & Ha) | (bs & i0 & p & u & Hbs & Hi0 & Hp & Hu & Ha)]].
    + rewrite Ra1 in Hz1, Hu, Ha. destruct nm as [x|].
      * pose proof (kp_acstr_unique _ _ _ _ _ Hu (proj1 (NM x eq_refl))) as Eu. subst u.
        exact (lf_name_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x ly3 S3 _ _ a HB HJA HRO HdatA Hnm Ha).
      * exfalso. apply Hz1. exact NMA.
    + rewrite Ra2 in Hu, Ha.
      exact (dec_ans_akb B TB HSEGS ly3 S3 W3 (ms_mem msA) mdA s6v t _ _ a HARA HRO HDA (ex_intro _ u (conj Hu Ha))).
    + exact (lf_tab_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs _ _ HB HJA HRO HdatA bs i0 p u a Hbs Hi0 Hp Hu Ha).
  - (* the Pre *)
    exists mbs, kbs, lf_tab, nm, (Some t).
    rewrite Ra0, Ra1, Ra2.
    split; [exact Dmd|]. split; [exact Dmwf|]. split; [exact Dk|]. split; [exact Dwf|]. split; [exact Dtab|].
    split; [exact NMA|]. split; [exact TA|].
    split; [exact M1|]. split; [exact M2|].
    split; [intros x Hx; exact (proj2 (NM x Hx))|].
    split.
    { intros i0 n2 ix p Hn Hp Rp.
      exact (proj1 (lf_tab_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs (ms_regs msA) MODEL_WRITE_AK HB HJA HRO HdatA Rsp HK8
        i0 n2 ix p Hn Hp Rp)). }
    split.
    { intros u Hu. injection Hu as Hu. subst u.
      split; [lia|]. split; [apply (w_amem_sub _ _ _ Tam); lia|].
      split; [exact Tra|]. split; [exact Thv|]. split; [exact Tfr|].
      apply (w_slack_of_tail _ s6v (Z.of_nat (length t))); [lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in Tam; lia |].
      exact Ttail. }
    split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|].
    split; [exact M8|]. split; [exact M9|].
    rewrite (ts_errno B TB); unfold apart, YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, AF0m.TFIB_ERRNO,
      MD_SIZE in *; clia.
  - (* the return, +0x1088 *)
    intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    set (Er := fun a => inFP (model_write_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) in *.
    assert (LC : lf_call B cx MODEL_WRITE_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er).
    { split; [lia|]. split; [rewrite MODEL_WRITE_AK_val; unfold LLVMF_STK in *; clia|]. split; [exact Hkp | exact Hsk]. }
    assert (HE : forall a, Er a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016)).
    { intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
      destruct Hin as [<- | []]; cbn in Hr. left. exact Hr. }
    assert (HEm : forall a, Er a -> md <= a < md + MD_SIZE).
    { intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
      destruct Hin as [<- | []]; cbn in Hr. exact Hr. }
    pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
    assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
      by (intros c Hc; exact (Permutation_in _ (Permutation_sym Hperm) Hc)).
    assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Psub _ BmdA).
    assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Psub _ BmkA).
    pose proof (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 (rdW W3 (ms_mem msA)) md mk HAR2 Pmd Pmk) as WC.
    (* model_write's post *)
    specialize (Hpost mbs kbs lf_tab nm (Some t)). rewrite Ra0, Ra1, Ra2 in Hpost.
    destruct (Hpost Dmd Dk Dtab NMA TA)
      as (Hrc & (mbs' & Hmd2 & Hmwf2 & _ & _ & _ & Hrq2 & _ & Hnm2 & Hmm2)).
    clear Hpost.
    destruct (lf_model_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp MODEL_WRITE_AK ly3 S3 ly2 S2 W3 msA mdA W2 ms2 md2 Er k2 _ _ _ _ md mk kbs mbs gbs mbs' T3 _ P N LF_SH0
      HB HJA HfrA LC HE Hfd2 Hfs2 Pmd Pmk WC ltac:(vm_compute; lia) HsvA HhdA HfsA HslA HcurA
      HjbkA HblkA HdatA Hmd2 Hmwf2 Hnm2 Hmm2) as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & HRO2).
    pose proof (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 _ _ _ _
      ly3 S3 ly2 S2 W2 ms2 md2 T3 _ k2 HB HJ2 Hs2 Hperm Hjbk2) as Hjbk3.
    pose proof (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2) as Hblk3.
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    pose proof (lf_call_kagree B cx MODEL_WRITE_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er LC) as KG.
    (* the answer misses the model block *)
    assert (XB : forall k a, In (own1, k) (ablocks B ly3 S3) -> own1 <= a < own1 + k ->
      ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - MODEL_WRITE_AK) (lf_sp1 cx) Er a).
    { intros k a Hb Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ Er own1 k a Hb Ha). intros HEa.
      pose proof (HEm a HEa) as Hm.
      destruct HTXA as [(Ho & _) | (k1 & Hne & Es & Hnbe & Hin1 & Hk1 & _)].
      - subst own1. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARA Hb) as (_ & H4 & _). lia.
      - destruct (proj1 Hfresh (own1, k1) ltac:(rewrite Hnbe; left; reflexivity)) as (_ & _ & HD1).
        pose proof (HD1 (md, MD_SIZE) ltac:(left; reflexivity)) as Dmd1. unfold zdisjoint in Dmd1. cbn [fst snd] in Dmd1.
        assert (Ek : k = k1).
        { destruct (Z.eq_dec k k1) as [-> | Hne']; [reflexivity|]. exfalso.
          pose proof (w_blk_disj B ly3 S3 W3 (ms_mem msA) mdA (own1, k) (own1, k1) LAWS HARA Hb Hin1
            ltac:(congruence)) as D.
          destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARA Hin1) as (_ & _ & _ & _ & _ & _ & Hn1).
          unfold zdisjoint, req_size in D. cbn [fst snd] in D.
          destruct (k =? 0) eqn:E1; destruct (k1 =? 0) eqn:E2; lia. }
        subst k1. unfold req_size, MD_SIZE in *.
        destruct (k =? 0) eqn:Ek0; [apply Z.eqb_eq in Ek0 | apply Z.eqb_neq in Ek0]; cbn in Dmd1; lia. }
    pose proof (tx_ans_keep B own1 nb ly3 S3 ly2 S2 _ _ _ s6v t HTXA Psub KG XB) as HTX2.
    assert (HSL2 : rdword (aview SEGS (w_H W2) (ms_mem ms2)) (lf_sp1 cx + LS_T130) = Some own1).
    { apply (d4_slot_callee B cx MODEL_WRITE_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er _ own1 LC);
        [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | | exact HSLA].
      intros j Hj HEa. pose proof (HEm _ HEa). unfold LS_T130, LLVMF_STK, MD_SIZE in *. lia. }
    apply (HL cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, s, s6v, own1, nm, t, kbs, mbs', gbs, T3, nb.
    split; [exact Hi|].
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1, <- HBASE. unfold LW_mret, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    cbn [ms_regs ms2 mkst].
    kreg KR 8 (8%bv : bv 5) K8. kreg KR 9 (9%bv : bv 5) K9. kreg KR 19 (19%bv : bv 5) K19. kreg KR 20 (20%bv : bv 5) K20.
    kreg KR 21 (21%bv : bv 5) K21. kreg KR 22 (22%bv : bv 5) K22. kreg KR 23 (23%bv : bv 5) K23.
    kreg KR 24 (24%bv : bv 5) K24. kreg KR 25 (25%bv : bv 5) K25. kreg KR 26 (26%bv : bv 5) K26.
    kreg KR 27 (27%bv : bv 5) K27.
    split; [unfold lf_core; cbn [ms_regs ms2 mkst]; rewrite P2, P8, P9, P3, P4, K2, K8, K9, K3, K4; repeat split; assumption|].
    split; [unfold w_regs; cbn [ms_regs ms2 mkst]; rewrite P19, P21, P22, P23, P24, P25, P26, P27, K19, K21, K22, K23, K24, K25, K26, K27;
            repeat split; assumption|].
    split; [exact Hnm|].
    split; [rewrite P20, K20; exact R20|].
    split; [rewrite <- REQ0, <- KSEQ; exact Hrc|].
    split.
    { split; [exact HJ2|]. split; [rewrite Hfr2; exact HfrA|]. split; [exact Hsv2|]. split; [exact Hhd2|].
      split; [exact Hfs2'|]. split; [exact Hsl2|]. split; [exact Hjbk3|]. split; [exact Hblk3 | exact Hdat2]. }
    split; [exact Hcur2|]. split; [exact Hop|].
    split; [exact (tx_ans_dec B own1 nb ly2 S2 _ s6v t HTX2)|].
    split; [exact HTX2|]. split; [exact HSL2|]. split; [exact Hnb|]. split; [exact Hown|].
    split; [exact (w_fresh_sub B cx md mk T3 ly3 S3 ly2 S2 nb Psub Hfresh)|].
    split; [exact SENT0|].
    split; [rewrite Hrq2, REQ0, KSEQ; reflexivity|].
    pose proof (w_errno_tab_range _ Hend) as Ren.
    unfold write_lib. apply reac_served_mark_aux.write_rc_range; cbn [nk_kstate k_sock k_send k_end];
      [destruct Hsock as [-> | Hs]; [lia | exact (w_errno_tab_range _ Hs)]
      | destruct Hsend as [-> | Hs]; [lia | exact (w_errno_tab_range _ Hs)] | exact Ren].
Qed.

End a.
