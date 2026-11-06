(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 193 of its 242 lines of code are new or changed and 1283 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   the tests after model_write and after the bcmp wrapper (listing image-A
   (internal path) (internal record, sha256 e84d6f0c6974)):

     +0x1150 bnez a0 -> +0xc08 (s7 := a0, -> +0xc0c o2_u_inv); j +0x1178 (o2_m_inv, the name is remembered next)
     +0x116c beqz a0 -> +0x1178 (o2_m_inv); s7 := 1; j +0xc0c (o2_u_inv)

   o2_wr : forall POST i, FROM POST (o2_u_inv i) -> FROM POST (o2_m_inv i) -> FROM POST (o2_w_inv i).
   o2_br : forall POST i, FROM POST (o2_u_inv i) -> FROM POST (o2_m_inv i) -> FROM POST (o2_b_inv i).

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
  LLVMFuzzerTestOneInputOp2V.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition o2x_w_ss : sstate := mkSS LO2_w sr_atoms [] None (mkFacts [] [] []).
Definition o2x_b_ss : sstate := mkSS LO2_b sr_atoms [] None (mkFacts [] [] []).

Lemma o2_beqz_any : forall (E : env) n,
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (bv_unsigned (ew E n) =? 0).
Proof.
  intros E n. rewrite branch_eq_U, U_SOff, U_lit by lia. unfold zcanon, M64. rewrite Z.add_0_r.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite (Z.mod_small (bv_unsigned (ew E n))) by lia. rewrite ?Z.mod_0_l by lia. reflexivity.
Qed.

Lemma o2_w64_0 : forall w : word, bv_unsigned w = 0 <-> w = w64 0.
Proof.
  intros w. split; intros H.
  - apply bv_eq. rewrite H. reflexivity.
  - rewrite H. reflexivity.
Qed.

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

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the end of a register-only stretch to a cut: the stretch's carry, its registers by the runner *)
Ltac o2x_carry HM KA0 HG0 Fd Fs KR :=
  apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) _ _ _ _ _ _ _ _ _ SH_M
    _ _ _ _ _ _ _ _ _ _ HM SH_M_len KA0 (fun a _ H => H) HG0 Fd Fs);
  rewrite KR by (vm_compute; reflexivity); reflexivity.

Lemma o2_wr : forall POST i,
  FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_m_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (o2_w_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HU HMI cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HW.
  destruct HW as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & R20 & Hw & Hlt & R22 & R26 & HM
    & Hare & Hr0 & Hv & R23 & R10 & WRr & Hrq).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E10 : ew E 10 = Z_to_bv 64 (w_rc (o2_WW t kbs))) by (rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2x_w_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_w)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2x_w_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  rewrite (lf_shape_eta fy LO2_w ms3 Hsh).
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_w)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) E) by exact (lf_env_agree0 (ms_regs ms3)).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x1150 taken: model_write's code is the answer *)
    rewrite (u_bne0 E 10 _ E10 ltac:(lia)) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_u; [apply awr_ok_x_nil|].
    rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
    pose proof (kagree_frame_nil _ _ _ HFrC) as KC.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
    assert (KR : forall r : bv 5, sr_get (ss_regs ssC) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msC) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssC msC _ r HS HA Hr)).
    prreg HS (23%bv : bv 5) Q23. rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl) in Q23.
    apply (HU cx fy fp k2 ly3 S3 W3 msC md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssC msC HS eq_refl)|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R26|].
    split; [o2x_carry HM KC HGC Fd5 Fs5 KR|].
    rewrite (o2_MM_open t kbs gbs Hlt Hr0). cbv zeta. rewrite Hv. cbn [Z.eqb V_MARK].
    replace (negb (w_rc (o2_WW t kbs) =? 0)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; exact Hc).
    cbn [m_rc m_reqs m_marks].
    split; [rewrite Q23; exact R10|]. split; [exact Hrq|]. destruct Hare as (_ & Hm). symmetry; exact Hm.
  - (* +0x1150 not taken: model_write answered 0; the name is remembered *)
    rewrite (u_bne0 E 10 _ E10 ltac:(lia)) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_m; [apply awr_ok_x_nil|].
    rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
    pose proof (kagree_frame_nil _ _ _ HFrC) as KC.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
    assert (KR : forall r : bv 5, sr_get (ss_regs ssC) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msC) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssC msC _ r HS HA Hr)).
    apply (HMI cx fy fp k2 ly3 S3 W3 msC md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssC msC HS eq_refl)|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R26|].
    split; [o2x_carry HM KC HGC Fd5 Fs5 KR|].
    split; [exact Hare|].
    rewrite (o2_MM_open t kbs gbs Hlt Hr0). cbv zeta. rewrite Hv. cbn [Z.eqb V_MARK].
    rewrite Hc. cbn [Z.eqb negb m_rc m_reqs m_marks].
    split; [rewrite KR by (vm_compute; reflexivity); exact R23|]. split; [exact Hrq | reflexivity].
Qed.

Lemma o2_br : forall POST i,
  FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_m_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (o2_b_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HU HMI cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HBI.
  destruct HBI as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & R20 & Hw & Hlt & R22 & R26 & HM
    & Hare & Hr0 & Hv & R23 & Hrq & HRES).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2x_b_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_b)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2x_b_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  rewrite (lf_shape_eta fy LO2_b ms3 Hsh).
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_b)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) E) by exact (lf_env_agree0 (ms_regs ms3)).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x116c taken: the alias is "reac-pw:served"; the name is remembered *)
    rewrite o2_beqz_any in Hc. apply Z.eqb_eq in Hc.
    rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl) in Hc. apply o2_w64_0, HRES in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_m; [apply awr_ok_x_nil|].
    rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
    pose proof (kagree_frame_nil _ _ _ HFrC) as KC.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
    assert (KR : forall r : bv 5, sr_get (ss_regs ssC) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msC) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssC msC _ r HS HA Hr)).
    apply (HMI cx fy fp k2 ly3 S3 W3 msC md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssC msC HS eq_refl)|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R26|].
    split; [o2x_carry HM KC HGC Fd5 Fs5 KR|].
    split; [exact Hare|].
    rewrite (o2_MM_open t kbs gbs Hlt Hr0). cbv zeta. rewrite Hv. cbn [Z.eqb V_MARK V_OURS].
    replace (bl_eqb (r_alias (o2_RR t kbs)) S_SERVED) with true by (symmetry; apply u_bl_eqb_true; exact Hc).
    cbn [andb m_rc m_reqs m_marks].
    split; [rewrite KR by (vm_compute; reflexivity); exact R23|]. split; [exact Hrq | reflexivity].
  - (* +0x116c not taken: s7 := V_OURS is the answer *)
    rewrite o2_beqz_any in Hc. apply Z.eqb_neq in Hc.
    assert (Hal : r_alias (o2_RR t kbs) <> S_SERVED).
    { intros Ha. apply (proj2 HRES) in Ha. rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl), Ha in Hc. apply Hc. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_u; [apply awr_ok_x_nil|].
    rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
    pose proof (kagree_frame_nil _ _ _ HFrC) as KC.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
    assert (KR : forall r : bv 5, sr_get (ss_regs ssC) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msC) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssC msC _ r HS HA Hr)).
    prreg HS (23%bv : bv 5) Q23.
    apply (HU cx fy fp k2 ly3 S3 W3 msC md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssC msC HS eq_refl)|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R26|].
    split; [o2x_carry HM KC HGC Fd5 Fs5 KR|].
    rewrite (o2_MM_open t kbs gbs Hlt Hr0). cbv zeta. rewrite Hv. cbn [Z.eqb V_MARK V_OURS].
    replace (bl_eqb (r_alias (o2_RR t kbs)) S_SERVED) with false
      by (symmetry; destruct (bl_eqb _ _) eqn:Eb; [exfalso; apply Hal; apply u_bl_eqb_true; exact Eb | reflexivity]).
    cbn [andb m_rc m_reqs m_marks].
    split; [rewrite Q23; reflexivity|]. split; [exact Hrq|]. destruct Hare as (_ & Hm). symmetry; exact Hm.
Qed.

End a.
