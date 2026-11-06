(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 443 of its 490 lines of code are new or changed and 1285 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: model_read (0x8368c), +0xe90 .. +0xeb8, from the
   cut r_z_inv to the cut r_m_inv at its return (+0xebc). The kind buffer is wk (F + 0x2e0) when kc > 0, else NULL;
   the alias buffer wa (F + 0x330) when ac > 0, else NULL (`seqz; addi -1; and`). model_read's contract
   (model_read_c.v) is the Section hypothesis MODEL_READ, as in the top file; the call is made as op_unmark's
   (Op3B.v u_head: ArmR.v ar_leaf_call), and the cut after it is Mdl.v's lf_model_after at the shadow SH_R.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputMdl
  LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputNm LLVMFuzzerTestOneInputArmH LLVMFuzzerTestOneInputChk
  LLVMFuzzerTestOneInputOp0Cut LLVMFuzzerTestOneInputOp0T LLVMFuzzerTestOneInputOp0Z LLVMFuzzerTestOneInputOp3B
  LLVMFuzzerTestOneInputOp3K LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0a YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1C.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* `seqz t, c; addi t, t, -1; and d, t, p`: d = p when c <> 0, else 0 *)
Lemma r_sel : forall c p, 0 <= c < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SLTU (Z_to_bv 64 c) (Z_to_bv 64 1)) (Z_to_bv 64 (-1))) (Z_to_bv 64 p) =
  Z_to_bv 64 (if c =? 0 then 0 else p).
Proof.
  intros c p Hc Hp. apply bv_eq.
  rewrite YO0c.alu64_and, YO0c.alu64_add, YO0c.alu64_sltu. unfold YO0a.add64, YO0a.sltu.
  rewrite !unsigned_lit_small by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1).
  destruct (Z.eqb_spec c 0) as [-> | Hn].
  - change (0 <? 1) with true. cbn -[Z.pow]. rewrite unsigned_lit_small by lia. reflexivity.
  - replace (c <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (unsigned_lit_small p) by lia. rewrite Z.add_0_l, Z.mod_small by lia.
    change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
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
Hypothesis MODEL_READ : forall fy : YK11.FPState, @model_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx :=
  (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Lemma r_mread : forall POST i,
  FROM POST (r_m_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (r_z_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HM cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HZ.
  destruct HZ as (md & mk & P & N & kbs & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hsh & Hreg & Hnm &
    Hkc & Hac & Hi & Hcore & HC & Hcur & Hop & Hns & Hrq & Hks & Hra & Hbufs & Hb1 & Hb2 & ZW & ZA & NIF).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  assert (Hs32 : lf_sp1 cx mod 32 = 0) by (unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
    apply Z_mod_mult).
  pose proof HC as (_ & _ & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HSM & _).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & _).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  assert (HU9 : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx)
    by (rewrite R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HSM) as Rmd.
  rewrite (lf_shape_eta fy LR_z ms3 Hsh).
  pose proof (d4_entry_l fy W3 (ms_regs ms3) (ms_mem ms3) LR_z LS_M md ltac:(rewrite HU9; unfold LLVMF_STK in *; lia)
    ltac:(rewrite HU9; exact Hs32) ltac:(unfold LS_M; lia) Rmd ltac:(vm_compute; reflexivity)
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HSM))) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md]))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_z)) (ms_mem ms3) (seg_rom SEGS)))))
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
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS EL
    ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr) ltac:(d4chk)) as KR.
  assert (KA : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { intros a _. unfold mbyte. rewrite (HFrA (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
    lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (chk_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 SH_R ly3 S3 W3 ms3 msA md3 mdA
    SH_R_len HC HJ KA (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  assert (G0 : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))) by exact HGA.
  pose proof (fun H1 => r_atbuf_run W3 _ _ t1 kc _ KA G0 (Hb1 H1)) as Hb1A.
  pose proof (fun H1 => r_atbuf_run W3 _ _ t2 ac _ KA G0 (Hb2 H1)) as Hb2A.
  assert (NIFA : lf_slot cx W3 msA LS_NIF (nk_opened kbs)).
    by exact (lf_slot_keep (fun _ => False) cx W3 ms3 W3 msA LS_NIF _ KA (fun j _ H => H) NIF).
  clear HC Hcur Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hb1 Hb2 NIF.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
  try rewrite E32 in Q10.
  ew_reg EL 22%nat (22%bv : bv 5) Q11. ew_reg EL 21%nat (21%bv : bv 5) Q13. ew_reg EL 27%nat (27%bv : bv 5) Q15.
  rewrite !EL in Q12 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat _ _ 21%nat (21%bv : bv 5) eq_refl), (ew_Ereg_nat _ _ 18%nat (18%bv : bv 5) eq_refl) in Q12.
  rewrite !EL in Q14 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat _ _ 27%nat (27%bv : bv 5) eq_refl), (ew_Ereg_nat _ _ 20%nat (20%bv : bv 5) eq_refl) in Q14.
  rewrite R22 in Q11. rewrite R21 in Q13. rewrite R27 in Q15. rewrite R21, R18 in Q12. rewrite R27, R20 in Q14.
  pose proof HCA as (HJA & HfrA & HsvA & HhdA & HfsA & HslA & HjbkA & HblkA & HdatA).
  pose proof HjbkA as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HJA as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
  kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (HK8 : 0 <= MODEL_READ_AK <= LLVMF_STK - 448) by (rewrite MODEL_READ_AK_val; unfold LLVMF_STK; lia).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem msA) mdA k2 HB HJA HfrA) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  set (F := lf_F cx fp) in *.
  (* the two buffer arguments *)
  set (pk := if kc =? 0 then 0 else F + LO_B2E0).
  set (pa := if ac =? 0 then 0 else F + LO_B330).
  assert (PK : pk <> 0 -> pk = F + LO_B2E0 /\ 1 <= kc).
  { unfold pk. destruct (Z.eqb_spec kc 0); [intros H; exfalso; apply H; reflexivity | intros _; split; [reflexivity | lia]]. }
  assert (PA : pa <> 0 -> pa = F + LO_B330 /\ 1 <= ac).
  { unfold pa. destruct (Z.eqb_spec ac 0); [intros H; exfalso; apply H; reflexivity | intros _; split; [reflexivity | lia]]. }
  assert (PKr : 0 <= pk < 2 ^ 64) by (unfold pk; destruct (kc =? 0); unfold LO_B2E0; lia).
  assert (PAr : 0 <= pa < 2 ^ 64) by (unfold pa; destruct (ac =? 0); unfold LO_B330; lia).
  unfold w64 in Q12, Q14.
  rewrite (r_sel kc (F + LO_B2E0)) in Q12 by (unfold LO_B2E0; lia). fold pk in Q12.
  rewrite (r_sel ac (F + LO_B330)) in Q14 by (unfold LO_B330; lia). fold pa in Q14.
  pose proof (w_name_range s nm Hnm) as Rs.
  assert (Ra0 : aarg (ms_regs msA) 0 = md) by (rewrite ar_aarg0, Q10; apply unsigned_lit_small; lia).
  assert (Ra1 : aarg (ms_regs msA) 1 = s) by (rewrite ar_aarg1, Q11; unfold w64; apply unsigned_lit_small; lia).
  assert (Ra2 : aarg (ms_regs msA) 2 = pk) by (rewrite ar_aarg2, Q12; apply unsigned_lit_small; lia).
  assert (Ra3 : aarg (ms_regs msA) 3 = kc) by (rewrite ar_aarg3, Q13; unfold w64; apply unsigned_lit_small; lia).
  assert (Ra4 : aarg (ms_regs msA) 4 = pa) by (rewrite ar_aarg4, Q14; apply unsigned_lit_small; lia).
  assert (Ra5 : aarg (ms_regs msA) 5 = ac) by (rewrite ar_aarg5, Q15; unfold w64; apply unsigned_lit_small; lia).
  (* the name's facts *)
  assert (NM : forall x, nm = Some x ->
    acstr_at SEGS (rdW W3 (ms_mem msA)) s x /\ astrcmp_arg SEGS (ms_regs msA) MODEL_READ_AK (rdW W3 (ms_mem msA)) s x).
  { intros x ->. split.
    - exact (proj1 (lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x HB HJA HRO HdatA Hnm)).
    - exact (lf_name_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x (ms_regs msA) MODEL_READ_AK HB HJA HRO HdatA Rsp HK8
        Hnm). }
  assert (NMA : astr_arg SEGS (rdW W3 (ms_mem msA)) s nm)
    by (apply (w_name_arg _ _ s nm Hnm); intros x Hx; exact (proj1 (NM x Hx))).
  assert (NMI : forall x, nm = Some x -> forall y, s <= y < s + Z.of_nat (length x) + 1 -> in_img SEGS y).
  { intros x -> y Hy. destruct (lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB
      HSEGS cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x HB HJA HRO HdatA Hnm)
      as (_ & _ & _ & _ & _ & _ & _ & _ & Ni). exact (proj1 (Ni y Hy)). }
  pose proof HdatA as (Dk & Dwf & Dtab & _ & _ & _ & Dmd & Dmwf & _).
  destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
    cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk T3 (ms_regs msA) MODEL_READ_AK HB HJA HblkA Rsp HK8)
    as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof HblkA as (BmdA & BmkA & BmcA & BkcA & BmTA & BkTA & Bm16A & Bk16A & BmtA & BktA & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & _).
  (* a buffer of the frame body: not image bytes, present, its shadow in scope *)
  assert (BUF : forall off n lo, (off = LO_B2E0 /\ lo = 92 \/ off = LO_B330 /\ lo = 102) -> 1 <= n <= 40 ->
      (forall x, F + off <= x < F + off + n -> ~ in_img SEGS x /\ apresent (w_H W3) (ms_mem msA) x) /\
      range_addressable (ard SEGS (rdW W3 (ms_mem msA))) SHADOW_OFF (F + off) n /\
      shadow_hull_vis (ard SEGS (rdW W3 (ms_mem msA))) (F + off) n).
  { intros off n lo Hoff Hn.
    assert (Hlo' : 4 <= lo /\ lo + 5 <= 108) by (destruct Hoff as [(_ & ->) | (_ & ->)]; lia).
    destruct (r_buf_shadow cx fp W3 msA SH_R lo 5 HfsA SH_R_len F32 F4 Fc ltac:(lia) ltac:(lia) ltac:(lia))
      as (RA & HV).
    { intros j Hj. destruct Hoff as [(_ & ->) | (_ & ->)]; change (Z.to_nat 92) with 92%nat in Hj;
        change (Z.to_nat 102) with 102%nat in Hj; cbn in Hj; rewrite (SH_R_nth j ltac:(lia)).
      - rewrite (SH_W_nth j ltac:(lia)). destruct (Nat.leb_spec 102 j), (Nat.ltb_spec j 107),
          (Nat.leb_spec 92 j), (Nat.ltb_spec j 97); cbn [andb]; first [reflexivity | lia].
      - destruct (Nat.leb_spec 102 j), (Nat.ltb_spec j 107); cbn [andb]; first [reflexivity | lia]. }
    assert (Eo : F + 8 * lo = F + off) by (destruct Hoff as [(-> & ->) | (-> & ->)]; unfold LO_B2E0, LO_B330; lia).
    fold F in RA, HV. rewrite Eo in RA, HV. change (8 * 5) with 40 in RA, HV.
    assert (Ho : 0 <= off /\ off + 40 <= 1016) by (destruct Hoff as [(-> & _) | (-> & _)]; unfold LO_B2E0, LO_B330; lia).
    split.
    { intros x Hx. destruct (Fpres x ltac:(lia)) as (P1 & P2). exact (conj P2 P1). }
    rewrite ard_aview. split.
    - intros x Hx. apply RA. lia.
    - apply (md_hull_sub _ (F + off) 40); [exact HV | lia | lia | lia]. }
  assert (BK : 1 <= kc -> (forall x, F + LO_B2E0 <= x < F + LO_B2E0 + kc ->
                             ~ in_img SEGS x /\ apresent (w_H W3) (ms_mem msA) x) /\
      range_addressable (ard SEGS (rdW W3 (ms_mem msA))) SHADOW_OFF (F + LO_B2E0) kc /\
      shadow_hull_vis (ard SEGS (rdW W3 (ms_mem msA))) (F + LO_B2E0) kc)
    by (intros H1; apply (BUF LO_B2E0 kc 92); [left; split; reflexivity | lia]).
  assert (BA : 1 <= ac -> (forall x, F + LO_B330 <= x < F + LO_B330 + ac ->
                             ~ in_img SEGS x /\ apresent (w_H W3) (ms_mem msA) x) /\
      range_addressable (ard SEGS (rdW W3 (ms_mem msA))) SHADOW_OFF (F + LO_B330) ac /\
      shadow_hull_vis (ard SEGS (rdW W3 (ms_mem msA))) (F + LO_B330) ac)
    by (intros H1; apply (BUF LO_B330 ac 102); [right; split; reflexivity | lia]).
  (* the separations of a frame-body buffer *)
  assert (BSEP : forall off n, (off = LO_B2E0 \/ off = LO_B330) -> 1 <= n <= 40 ->
      (forall x, F + off <= x < F + off + n -> ~ in_img SEGS x) ->
      apart_frame (ms_regs msA) MODEL_READ_AK (F + off) n /\ apart (as_errno B) 4 (F + off) n /\
      apart_gnl LA_G_NL (F + off) n /\ apart (F + off) n md MD_SIZE /\
      (forall i0 n2 ix p, nth_error lf_tab i0 = Some (n2, ix) ->
         au64_at SEGS (rdW W3 (ms_mem msA)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i0) p ->
         apart (F + off) n p (Z.of_nat (length n2) + 1)) /\
      amem_range (F + off) n /\
      (forall x, nm = Some x -> apart (F + off) n s (Z.of_nat (length x) + 1))).
  { intros off n Hoff Hn NI.
    assert (Ho : 0 <= off /\ off + 40 <= 1016) by (destruct Hoff as [-> | ->]; unfold LO_B2E0, LO_B330; lia).
    pose proof (Fsep md MD_SIZE BmdA) as DmF. unfold zdisjoint in DmF. cbn [fst snd] in DmF.
    change (req_size MD_SIZE) with 8856 in DmF.
    split; [unfold apart_frame; left; rewrite Rsp, MODEL_READ_AK_val; unfold LLVMF_STK in *; lia|].
    split; [apply md_apart_of_disj; [lia | lia|]; intros x H1 H2; exact (NI x H2 (md_errno_img B TB HSEGS x H1))|].
    split.
    { assert (Ap : apart (F + off) n LA_G_NL NK_SIZE).
      { apply md_apart_of_disj; [lia | unfold NK_SIZE; lia|]. intros x H1 H2.
        apply (NI x H1). apply (proj1 (IMG x ltac:(left; exact H2))). }
      unfold apart in Ap. unfold apart_gnl. exact Ap. }
    split; [unfold apart, MD_SIZE in *; lia|].
    split.
    { intros i0 n2 ix p Hn2 Hp.
      pose proof (lf_tab_names_short) as Hsn. rewrite forallb_forall in Hsn.
      specialize (Hsn (n2, ix) (nth_error_In _ _ Hn2)). apply Nat.leb_le in Hsn. cbn [fst] in Hsn.
      destruct (Z_lt_le_dec p 0) as [Hp0 | Hp0]; [unfold apart in *; lia|].
      destruct (Z_lt_le_dec p (2 ^ 64)) as [Hp1 | Hp1]; [|unfold apart in *; lia].
      destruct (lf_tab_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs HB HJA HRO HdatA i0 n2 ix p Hn2 Hp ltac:(lia))
        as (_ & _ & _ & _ & _ & _ & _ & C7).
      apply md_apart_of_disj; [lia | lia|]. intros x H1 H2. exact (NI x H1 (proj1 (C7 x ltac:(lia)))). }
    split; [destruct Fapp as (Fa1 & Fa2); unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg,
        kHighMemEnd, ASAN_CEIL in *; lia|].
    intros x Hx. apply md_apart_of_disj; [lia | lia|]. intros y H1 H2. exact (NI y H1 (NMI x Hx y ltac:(lia))). }
  replace (pa_sigma LS_model_read) with MODEL_READ_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 MODEL_READ_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS MODEL_READ_A (ms_regs msA) (ms_mem msA) mdA).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (MODEL_READ fy).
  - exact HB.
  - exact HJA.
  - exact HRO.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, HBASE. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite K3, R3. exact Gp.
  - rewrite K4, R4. exact Tp.
  - exact Rsp.
  - exact HK8.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia.
  - apply (ar_side_room S3 fp _ HfrA). vm_compute. reflexivity.
  - intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a BmdA BmcA). unfold MD_SIZE in *. clia.
    + destruct (Z.eqb_spec pk 0) as [E0 | E0]; [try rewrite E0 in Hr; cbn in Hr; lia|].
      destruct (PK E0) as (Ep & H1). try rewrite (proj2 (Z.eqb_neq pk 0) E0) in Hr. rewrite Ep in Hr.
      apply (ar_ajw_frame B); [rewrite HFa; change (fs_frame_bytes LF_CID) with 1024; unfold LO_B2E0 in *; clia|].
      intros Hsx. unfold LLVMF_STK, LO_B2E0 in *. clia.
    + destruct (Z.eqb_spec pa 0) as [E0 | E0]; [try rewrite E0 in Hr; cbn in Hr; lia|].
      destruct (PA E0) as (Ep & H1). try rewrite (proj2 (Z.eqb_neq pa 0) E0) in Hr. rewrite Ep in Hr.
      apply (ar_ajw_frame B); [rewrite HFa; change (fs_frame_bytes LF_CID) with 1024; unfold LO_B330 in *; clia|].
      intros Hsx. unfold LLVMF_STK, LO_B330 in *. clia.
  - intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
    intros Hro. pose proof (lf_roP_bounds a Hro) as RB.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in *. clia.
    + destruct (Z.eqb_spec pk 0) as [E0 | E0]; [try rewrite E0 in Hr; cbn in Hr; lia|].
      destruct (PK E0) as (Ep & H1). try rewrite (proj2 (Z.eqb_neq pk 0) E0) in Hr. rewrite Ep in Hr.
      destruct (BK H1) as (BI & _). destruct (BI a ltac:(clia)) as (NI & _). apply NI.
      destruct Hro as [(s0 & Hs0 & _ & Hsr) | Hr2]; [exists s0; split; [exact Hs0 | exact Hsr]|].
      exact (ar_relro_img HSEGS a Hr2).
    + destruct (Z.eqb_spec pa 0) as [E0 | E0]; [try rewrite E0 in Hr; cbn in Hr; lia|].
      destruct (PA E0) as (Ep & H1). try rewrite (proj2 (Z.eqb_neq pa 0) E0) in Hr. rewrite Ep in Hr.
      destruct (BA H1) as (BI & _). destruct (BI a ltac:(clia)) as (NI & _). apply NI.
      destruct Hro as [(s0 & Hs0 & _ & Hsr) | Hr2]; [exists s0; split; [exact Hs0 | exact Hsr]|].
      exact (ar_relro_img HSEGS a Hr2).
  - (* the read set *)
    intros a [(Hz1 & u & Hu & Ha) | (bs & i0 & p & u & Hbs & Hi0 & Hp & Hu & Ha)].
    + rewrite Ra1 in Hz1, Hu, Ha. destruct nm as [x|].
      * pose proof (kp_acstr_unique _ _ _ _ _ Hu (proj1 (NM x eq_refl))) as Eu. subst u.
        exact (lf_name_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x ly3 S3 _ _ a HB HJA HRO HdatA Hnm Ha).
      * exfalso. apply Hz1. exact NMA.
    + exact (lf_tab_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs _ _ HB HJA HRO HdatA bs i0 p u a Hbs Hi0 Hp Hu Ha).
  - (* the Pre *)
    exists mbs, kbs, lf_tab, nm.
    rewrite Ra0, Ra1, Ra2, Ra3, Ra4, Ra5.
    split; [exact Dmd|]. split; [exact Dmwf|]. split; [exact Dk|]. split; [exact Dwf|]. split; [exact Dtab|].
    split; [exact NMA|].
    split.
    { intros E0 H1. destruct (PK E0) as (-> & _). destruct (BK H1) as (BI & _).
      apply u_abuf; [unfold LO_B2E0; clia | lia | unfold LO_B2E0 in *; clia |].
      intros x Hx. exact (proj2 (BI x Hx)). }
    split.
    { intros E0 H1. destruct (PA E0) as (-> & _). destruct (BA H1) as (BI & _).
      apply u_abuf; [unfold LO_B330; clia | lia | unfold LO_B330 in *; clia |].
      intros x Hx. exact (proj2 (BI x Hx)). }
    split; [exact M1|]. split; [exact M2|].
    split; [intros x Hx; exact (proj2 (NM x Hx))|].
    split.
    { intros i0 n2 ix p Hn Hp Rp.
      exact (proj1 (lf_tab_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs (ms_regs msA) MODEL_READ_AK HB HJA HRO HdatA Rsp HK8
        i0 n2 ix p Hn Hp Rp)). }
    split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|].
    split; [exact M8|]. split; [exact M9|].
    assert (BSK : 1 <= kc -> _) by (intros H1; exact (BSEP LO_B2E0 kc (or_introl eq_refl) ltac:(lia)
      (fun x Hx => proj1 (proj1 (BK H1) x Hx)))).
    assert (BSA : 1 <= ac -> _) by (intros H1; exact (BSEP LO_B330 ac (or_intror eq_refl) ltac:(lia)
      (fun x Hx => proj1 (proj1 (BA H1) x Hx)))).
    split; [intros E0; destruct (PK E0) as (-> & H1); exact (proj1 (BSK H1))|].
    split; [intros E0; destruct (PA E0) as (-> & H1); exact (proj1 (BSA H1))|].
    split; [rewrite (ts_errno B TB); unfold apart, YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, AF0m.TFIB_ERRNO,
      MD_SIZE in *; clia|].
    split; [intros E0 _; destruct (PK E0) as (-> & H1); exact (proj1 (proj2 (BSK H1)))|].
    split; [intros E0 _; destruct (PA E0) as (-> & H1); exact (proj1 (proj2 (BSA H1)))|].
    split.
    { intros E0 _. destruct (PK E0) as (-> & H1).
      destruct (BSK H1) as (_ & _ & G1 & G2 & G3 & G4 & _). destruct (BK H1) as (_ & G5 & G6).
      exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 G6))))). }
    split.
    { intros E0 _. destruct (PA E0) as (-> & H1).
      destruct (BSA H1) as (_ & _ & G1 & G2 & G3 & G4 & _). destruct (BA H1) as (_ & G5 & G6).
      exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 G6))))). }
    split.
    { intros x Hx. split.
      - intros E0 _. destruct (PK E0) as (-> & H1). destruct (BSK H1) as (_ & _ & _ & _ & _ & _ & G7). exact (G7 x Hx).
      - intros E0 _. destruct (PA E0) as (-> & H1). destruct (BSA H1) as (_ & _ & _ & _ & _ & _ & G7). exact (G7 x Hx). }
    intros E0 E1 _ _. destruct (PK E0) as (-> & _). destruct (PA E1) as (-> & _).
    unfold apart, LO_B2E0, LO_B330. lia.
  - (* the return, +0xebc *)
    intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    set (Er := fun a => inFP (model_read_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) in *.
    assert (LC : lf_call B cx MODEL_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er).
    { split; [lia|]. split; [rewrite MODEL_READ_AK_val; unfold LLVMF_STK in *; clia|]. split; [exact Hkp | exact Hsk]. }
    assert (HEr : forall a, Er a -> md <= a < md + MD_SIZE \/ F + LO_B2E0 <= a < F + LO_B2E0 + kc \/
                             F + LO_B330 <= a < F + LO_B330 + ac).
    { intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
      destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; [left; exact Hr| |].
      - destruct (Z.eqb_spec pk 0) as [E0 | E0]; [try rewrite E0 in Hr; cbn in Hr; lia|].
        destruct (PK E0) as (Ep & _). try rewrite (proj2 (Z.eqb_neq pk 0) E0) in Hr. rewrite Ep in Hr. right; left; lia.
      - destruct (Z.eqb_spec pa 0) as [E0 | E0]; [try rewrite E0 in Hr; cbn in Hr; lia|].
        destruct (PA E0) as (Ep & _). try rewrite (proj2 (Z.eqb_neq pa 0) E0) in Hr. rewrite Ep in Hr. right; right; lia. }
    assert (HE : forall a, Er a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016)).
    { intros a Ha. destruct (HEr a Ha) as [H1 | [H1 | H1]]; [left; exact H1 | right | right];
        fold F; unfold LO_B2E0, LO_B330 in *; lia. }
    pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
    assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
      by (intros c Hc; exact (Permutation_in _ (Permutation_sym Hperm) Hc)).
    assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Psub _ BmdA).
    assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Psub _ BmkA).
    pose proof (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 (rdW W3 (ms_mem msA)) md mk HAR2 Pmd Pmk) as WC.
    (* model_read's post *)
    specialize (Hpost mbs kbs lf_tab nm). rewrite Ra0, Ra1, Ra2, Ra3, Ra4, Ra5 in Hpost.
    destruct (Hpost Dmd Dk Dtab NMA)
      as (Hrc & (mbs' & Hmd2 & Hmwf2 & Hnx2 & Hso2 & Hse2 & Hrq2 & Hnr2 & Hnm2 & Hmm2) & Hkd & Hal & Hkb & Hab).
    clear Hpost.
    rewrite Hrq, Hks in Hrc, Hnx2, Hso2, Hse2, Hrq2, Hkd, Hal.
    fold (r_RR nm kc ac kbs) in Hrc, Hnx2, Hso2, Hse2, Hrq2, Hkd, Hal.
    destruct (lf_model_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp MODEL_READ_AK ly3 S3 ly2 S2 W3 msA mdA W2 ms2 md2 Er k2 _ _ _ _ md mk kbs mbs gbs mbs' T3 _ P N SH_R
      HB HJA HfrA LC HE Hfd2 Hfs2 Pmd Pmk WC ltac:(rewrite SH_R_len; lia) HsvA HhdA HfsA HslA HcurA
      HjbkA HblkA HdatA Hmd2 Hmwf2 Hnm2 Hmm2) as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & HRO2).
    pose proof (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 _ _ _ _
      ly3 S3 ly2 S2 W2 ms2 md2 T3 _ k2 HB HJ2 Hs2 Hperm Hjbk2) as Hjbk3.
    pose proof (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2) as Hblk3.
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    (* the two text buffers and the opened slot: off the write set *)
    pose proof Hbufs as (Hnb1 & Hnb2 & Hbin & Hbap).
    assert (RQ : forall c, 0 <= c -> req_size (c + 1) = c + 1)
      by (intros c Hc; unfold req_size; destruct (c + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]).
    assert (TBUF : forall t c nb, tb_nb c t nb -> incl nb (nb1 ++ nb2) -> 1 <= c -> 0 <= c < 40 ->
        atbuf_at SEGS (rdW W3 (ms_mem msA)) t c (repeat (zb GUARD_BYTE) (Z.to_nat c)) ->
        atbuf_at SEGS (rdW W2 (ms_mem ms2)) t c (repeat (zb GUARD_BYTE) (Z.to_nat c))).
    { intros t c nb Hnb Hinc H1 Hc HT.
      destruct Hnb as [(E0 & _) | (_ & _ & ->)]; [lia|].
      destruct (Hbin (t, c + 1) (Hinc _ (or_introl eq_refl))) as (Hin3 & _ & Hd).
      apply (r_atbuf_callee B LAWS cx MODEL_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er md2 t c _ LC HAR2
        Hin3 (Psub _ Hin3)); [| lia | exact HT].
      intros a Ha HEa. pose proof (Hd (md, MD_SIZE) (or_introl eq_refl)) as Dm. unfold zdisjoint in Dm.
      cbn [fst snd] in Dm. change (req_size MD_SIZE) with 8856 in Dm. rewrite RQ in Dm by lia.
      pose proof (Fsep t (c + 1) Hin3) as DF. unfold zdisjoint in DF. cbn [fst snd] in DF. rewrite RQ in DF by lia.
      destruct (HEr a HEa) as [H2 | [H2 | H2]]; unfold MD_SIZE, LO_B2E0, LO_B330 in *; lia. }
    assert (NIF2 : lf_slot cx W2 ms2 LS_NIF (nk_opened kbs)).
    { unfold lf_slot, lf_at in *.
      apply (d4_slot_callee B cx MODEL_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er _ _ LC);
        [unfold LS_NIF; lia | unfold LS_NIF, LLVMF_STK in *; lia | | exact NIFA].
      intros j Hj HEa. pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
      destruct (HEr _ HEa) as [H2 | [H2 | H2]]; unfold LS_NIF, LLVMF_STK, MD_SIZE, LO_B2E0, LO_B330 in *; lia. }
    apply (HM cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, kbs, mbs', gbs, T3, s, nm, kc, ac, t1, t2, nb1, nb2.
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1. unfold LR_m, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    kreg KR 8 (8%bv : bv 5) K8. kreg KR 9 (9%bv : bv 5) K9. kreg KR 18 (18%bv : bv 5) K18.
    kreg KR 19 (19%bv : bv 5) K19. kreg KR 20 (20%bv : bv 5) K20.
    kreg KR 21 (21%bv : bv 5) K21. kreg KR 22 (22%bv : bv 5) K22. kreg KR 23 (23%bv : bv 5) K23.
    kreg KR 24 (24%bv : bv 5) K24. kreg KR 25 (25%bv : bv 5) K25. kreg KR 26 (26%bv : bv 5) K26.
    kreg KR 27 (27%bv : bv 5) K27.
    split.
    { unfold r_regs4, ms2. cbn [ms_regs mkst].
      rewrite P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27.
      repeat split; assumption. }
    split; [exact Hrc|].
    split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
    split; [unfold lf_core, ms2; cbn [ms_regs mkst]; rewrite P2, P8, P9, P3, P4, K2, K8, K9, K3, K4;
            repeat split; assumption|].
    split.
    { split; [exact HJ2|]. split; [rewrite Hfr2; exact HfrA|]. split; [exact Hsv2|]. split; [exact Hhd2|].
      split; [exact Hfs2'|]. split; [exact Hsl2|]. split; [exact Hjbk3|]. split; [exact Hblk3 | exact Hdat2]. }
    split; [exact Hcur2|]. split; [exact Hop|]. split; [exact Hns|].
    split; [exact Hrq2|].
    split.
    { destruct (u_read_ce lf_tab nm kc ac [] (nk_kstate kbs)) as (Ce & Ee).
      apply u_md_kstate_of; [exact Hnx2 | exact Hso2 | exact Hse2 | | ];
        unfold r_RR, read_model; cbn [r_state]; [rewrite Ce | rewrite Ee]; reflexivity. }
    split.
    { split; [exact Hnb1|]. split; [exact Hnb2|]. split; [|exact Hbap].
      intros b Hb. destruct (Hbin b Hb) as (H1 & H2 & H3). exact (conj (Psub _ H1) (conj H2 H3)). }
    split; [intros H1; exact (TBUF t1 kc nb1 Hnb1 ltac:(intros x Hx; apply in_or_app; left; exact Hx) H1 Hkc (Hb1A H1))|].
    split; [intros H1; exact (TBUF t2 ac nb2 Hnb2 ltac:(intros x Hx; apply in_or_app; right; exact Hx) H1 Hac (Hb2A H1))|].
    (* a frame-body buffer the call does not write keeps its zero bytes *)
    assert (ZK : forall off c (Z0 : abytes SEGS (rdW W3 (ms_mem ms3)) (F + off) (repeat (Z_to_bv 8 0) 40)),
        (off = LO_B2E0 /\ c = kc \/ off = LO_B330 /\ c = ac) -> c < 1 ->
        abytes SEGS (rdW W2 (ms_mem ms2)) (F + off) (repeat (Z_to_bv 8 0) 40)).
    { intros off c Z0 Hoc Hc1.
      pose proof (Fsep md MD_SIZE BmdA) as DmF. unfold zdisjoint in DmF. cbn [fst snd] in DmF.
      change (req_size MD_SIZE) with 8856 in DmF.
      apply (abytes_keep SEGS _ _ _ _ _
        (lf_call_kagree B cx MODEL_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er LC)).
      - intros j Hj. rewrite repeat_length in Hj.
        apply (lfx_frm B ly3 S3 ly2 S2 _ _ Er LF_CID fp (F + off + j) ltac:(rewrite HfrA; left; reflexivity)).
        + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID) with 1024.
          destruct Hoc as [(-> & _) | (-> & _)]; unfold F, LO_B2E0, LO_B330 in *; lia.
        + intros HEa. destruct (HEr _ HEa) as [H2 | [H2 | H2]];
            destruct Hoc as [(-> & ->) | (-> & ->)]; unfold F, LO_B2E0, LO_B330, MD_SIZE in *; lia.
      - apply (abytes_keep SEGS _ _ _ _ _ KA); [intros j _ H; exact H | exact Z0]. }
    split.
    { destruct (Z_lt_le_dec kc 1) as [K0 | K1].
      - assert (Lk : r_kind (r_RR nm kc ac kbs) = []) by (unfold r_RR, read_model; cbn [r_kind]; apply r_kind_nil; lia).
        rewrite Lk. split; [|intros H1; lia]. fold F.
        exact (r_acstr_nil_of_zeros SEGS _ _ 40 (ZK LO_B2E0 kc ZW (or_introl (conj eq_refl eq_refl)) K0) ltac:(lia)).
      - destruct (PK ltac:(unfold pk; destruct (Z.eqb_spec kc 0); [lia | unfold LO_B2E0; clia])) as (Ep & _).
        rewrite Ep in Hkd, Hkb. fold F.
        split; [exact (Hkd ltac:(unfold LO_B2E0; clia) K1) | intros H1; exact (Hkb ltac:(unfold LO_B2E0; clia) H1)]. }
    split.
    { destruct (Z_lt_le_dec ac 1) as [K0 | K1].
      - assert (La : r_alias (r_RR nm kc ac kbs) = []) by (unfold r_RR, read_model; cbn [r_alias]; apply r_alias_nil; lia).
        rewrite La. split; [|intros H1; lia]. fold F.
        exact (r_acstr_nil_of_zeros SEGS _ _ 40 (ZK LO_B330 ac ZA (or_intror (conj eq_refl eq_refl)) K0) ltac:(lia)).
      - destruct (PA ltac:(unfold pa; destruct (Z.eqb_spec ac 0); [lia | unfold LO_B330; clia])) as (Ep & _).
        rewrite Ep in Hal, Hab. fold F.
        split; [exact (Hal ltac:(unfold LO_B330; clia) K1) | intros H1; exact (Hab ltac:(unfold LO_B330; clia) H1)]. }
    exact NIF2.
Qed.
End a.
