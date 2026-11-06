(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 296 of its 341 lines of code are new or changed and 1287 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm, the middle of one turn of the per-mark loop
   from the bcmp wrapper's return (+0x820, u_b_inv) to the join u_j_inv at +0x838: model_write (0x83008) with the
   empty alias .str.1 when the alias is "reac-pw:served".
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
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
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
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Definition LU_mr : Z := AF_LLVMFuzzerTestOneInput + 0x808.   (* 0x82fdc, model_read's return *)

(* the runner's state at the loop head: the frame's shadow, its window the 32 bytes of F + 0x20 *)
Definition u_fs_rg : YP09.region := YP09.mkRegion (Some 19%nat) 0 112 4 36 [].
Definition u_l_facts : facts := mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 0xffffff00000) 2)] [] [].
Definition u_l_ss : sstate := mkSS LU_body sr_atoms [u_fs_rg] None u_l_facts.

(* the frame's shadow with the object F + 0x20 in scope *)
Definition u_b_ss : sstate := mkSS LU_bc sr_atoms [] None (mkFacts [] [] []).

Lemma u_bne_any : forall (E : env) n,
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (bv_unsigned (ew E n) =? 0).
Proof.
  intros E n. rewrite branch_ne_U, U_SOff, U_lit by lia. unfold zcanon, M64. rewrite Z.add_0_r.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite (Z.mod_small (bv_unsigned (ew E n))) by lia. rewrite ?Z.mod_0_l by lia. reflexivity.
Qed.

Lemma u_bret : forall POST i j,
  FROM POST (u_j_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j) ->
  FROM POST (u_b_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j).
Proof.
  intros POST i j HJN cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HBI.
  destruct HBI as (md & mk & P & N & kbs & mbs & gbs & T3 & nm & reqs0 & K0 & Hsh & R23 & R20 & R18 & HU & Hj & Hns
    & Hnm & Hnmc & Hnml & HUW & Hrq & Hks & Hr0 & HRES).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E u_b_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_bc)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold u_b_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  rewrite (lf_shape_eta fy LU_bc ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_bc)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x820 taken: the alias is not "reac-pw:served" *)
    rewrite u_bne_any in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hal : r_alias (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) <> S_SERVED).
    { intros Ha. apply (proj2 HRES) in Ha. rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl), Ha in Hc. apply Hc. reflexivity. }
    assert (Hbl : bl_eqb (r_alias (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0)) S_SERVED = false)
      by (destruct (bl_eqb _ _) eqn:Eb; [exfalso; apply Hal; apply u_bl_eqb_true; exact Eb | reflexivity]).
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LU_join; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
    assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) E) by exact (lf_env_agree0 (ms_regs ms3)).
    assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msB) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssB msB _ r HS HA Hr)).
    apply (HJN cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R23|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R20|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R18|].
    split.
    { eapply (u_mem_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP) with (X := fun _ => False);
        [exact HU | exact SH_Z_len | exact KB | exact (fun a _ H => H) | exact HGB | exact Fd5 | exact Fs5 | ..];
        rewrite KR by (vm_compute; reflexivity); reflexivity. }
    split; [exact Hj|]. split; [exact Hns|].
    rewrite Hrq, Hks.
    exact (u_step_skip lf_tab (mk_names gbs) j nm reqs0 K0 _ ltac:(lia) Hnm HUW (or_intror Hbl)).
  - paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
    lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
    pmkst HS.
    (* +0x820 not taken: the alias is "reac-pw:served"; the call of model_write at 0x83008 *)
    rewrite u_bne_any in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (Hal : r_alias (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) = S_SERVED).
    { apply (proj1 HRES). rewrite <- (EL 10%nat 10%bv ltac:(lia) eq_refl). apply bv_eq. rewrite Hc. reflexivity. }
    assert (Hbl : bl_eqb (r_alias (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0)) S_SERVED = true)
      by (apply u_bl_eqb_true; exact Hal).
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    assert (Hpc : ss_pc ssA = pa_sigma LS_model_write) by reflexivity.
    rewrite Hpc, (lv_sigma LV).
    replace (link_sigma LS_model_write) with MODEL_WRITE_A by reflexivity.
    pose proof HU as (Hi & Hcore & Hreg & _).
    pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27).
    pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl), R22 in Q10.
    rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl), R23 in Q11.
    rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8. rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9.
    rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
    rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20. rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21.
    rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in Q23.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    assert (E249 : ew E 249 = Z_to_bv 64 0x20fc0).
    { unfold E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 249%nat with (A_OBJ 8).
      rewrite (lv_obj LV 8 ltac:(unfold link_nobj; lia)). reflexivity. }
    rewrite E249 in Q12.
    assert (HUA : u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_Z cx fp k2 ly3 S3 W3 msA md4).
    { eapply (u_mem_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP) with (X := fun _ => False);
        [exact HU | exact SH_Z_len | exact KA | exact (fun a _ H => H) | exact HGA | exact Fd | exact Fs | ..];
        assumption. }
    pose proof HUA as (_ & _ & _ & Hsv' & Hhd' & Hfs' & Hsl' & Hcur' & Hjbk' & Hblk' & Hdat' & Hop).
    pose proof (acstr_keep SEGS (fun _ => False) _ _ _ _ KA (fun _ _ H => H) Hnmc) as HnmcA.
    pose proof (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
    pose proof (lv_text LV) as HBASE.
    pose proof Hblk' as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & Bram & Brak
      & Bamm & Bamk).
    pose proof HJ as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _). pose proof HARA as (MA & _).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem msA) md4 md MD_SIZE HARA Bmd) as (_ & Bm4 & Bmceil & _).
    change (req_size MD_SIZE) with 8856 in Bmceil.
    pose proof Hdat' as (Dk & Dwf & Dtab & _ & _ & _ & Dmd & Dmwf & _ & _ & (Dmn & Dmm) & _).
    pose proof Dmwf as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm.
    assert (Hj32 : 0 <= j <= 31) by clia.
    pose proof asan_consts as ((C1a & C1b) & _).
    destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
      (ms_mem msA) md4 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
    assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
    { unfold spZ. rewrite Q2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. clia. }
    assert (Ra0 : aarg (ms_regs msA) 0 = md) by (rewrite ar_aarg0, Q10; unfold w64; apply unsigned_lit_small; clia).
    assert (Ra1 : aarg (ms_regs msA) 1 = md + MD_MARK + MARK_LEN * j)
      by (rewrite ar_aarg1, Q11; unfold w64; apply unsigned_lit_small; unfold MD_MARK, MARK_LEN, MD_SIZE in *; clia).
    assert (Ra2 : aarg (ms_regs msA) 2 = 0x20fc0) by (rewrite ar_aarg2, Q12; reflexivity).
    pose proof Hjbk' as (Jk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
    destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp ly3 S3 W3 (ms_mem msA) md4 k2 HB HJ Hfr) as (HFa2 & F32 & F4 & Fc & Fapp & Fpres2 & Fshp2 & Fsep2).
    assert (HK8 : 0 <= MODEL_WRITE_AK <= LLVMF_STK - 448) by (rewrite MODEL_WRITE_AK_val; unfold LLVMF_STK; lia).
    destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
      cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk T3 (ms_regs msA) MODEL_WRITE_AK HB HJ Hblk' Rsp HK8)
      as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
    (* .str.1, the empty alias *)
    pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    match goal with Hh : kp_kstr_b _ _ _ LA_STR_EMPTY _ = true |- _ => rename Hh into KSE end.
    destruct (kp_kstr_acstr B (w_H W3) (ms_mem msA) _ _ HRO KSE) as (HSE & _ & _).
    change (map (Z_to_bv 8) []) with (@nil byte) in HSE.
    unfold kp_kstr_b in KSE.
    repeat match type of KSE with (_ && _)%bool = true => apply andb_prop in KSE as [KSE ?] end.
    match goal with Hh : kp_hull_b LA_STR_EMPTY _ = true |- _ => rename Hh into KH1 end.
    match goal with Hh : kp_ra_b LA_STR_EMPTY _ = true |- _ => rename Hh into KR1 end.
    match goal with Hh : kp_somes_b _ (LA_STR_EMPTY + _ + 1) _ = true |- _ => rename Hh into KS1 end.
    pose proof (kp_ard_here B TB HSEGS) as KA'. unfold kp_ard_b in KA'.
    repeat match type of KA' with (_ && _)%bool = true => apply andb_prop in KA' as [KA' ?] end.
    match goal with Hh : kp_akbs_b _ _ _ LA_STR_EMPTY _ = true |- _ => rename Hh into KAse end.
    change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 MODEL_WRITE_A) (ms_mem msA) (seg_rom SEGS)) md4)
      with (@cfg_at fy SEGS MODEL_WRITE_A (ms_regs msA) (ms_mem msA) md4).
    eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
    + exact (MODEL_WRITE fy).
    + exact HB.
    + exact HJ.
    + exact HRO.
    + rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    + unfold raZ. rewrite Q1, HBASE. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
    + rewrite Q3, R3. exact Gp.
    + rewrite Q4, R4. exact Tp.
    + exact Rsp.
    + exact HK8.
    + lia.
    + unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia.
    + apply (ar_side_room S3 fp _ Hfr). vm_compute. reflexivity.
    + intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
      destruct Hin as [<- | []]; cbn [fst snd] in Hr.
      apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a Bmd Bmc). unfold MD_SIZE in *. clia.
    + intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
      intros Hro. pose proof (lf_roP_bounds a Hro) as RB.
      destruct Hin as [<- | []]; cbn [fst snd] in Hr.
      unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in *. clia.
    + (* the read set *)
      intros a [(Hz1 & s & Hs & Ha) | [(Hz1 & s & Hs & Ha) | (bs & i0 & p & s & Hbs & Hi0 & Hp & Hs & Ha)]].
      * rewrite Ra1 in Hs, Ha. pose proof (kp_acstr_unique _ _ _ _ _ Hs HnmcA) as Es. subst s.
        apply (lf_blk_akb B ly3 S3 _ _ md MD_SIZE a Bmd). change (req_size MD_SIZE) with 8856.
        unfold MD_MARK, MARK_LEN in *. clia.
      * rewrite Ra2 in Hs, Ha. pose proof (kp_acstr_unique _ _ _ _ _ Hs HSE) as Es. subst s. cbn [length Z.of_nat] in Ha.
        eapply kp_akbs_of_b; [exact KAse | unfold LA_STR_EMPTY; cbn; clia].
      * exact (lf_tab_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs _ _ HB HJ HRO Hdat' bs i0 p s a Hbs Hi0 Hp Hs Ha).
    + (* the Pre *)
      exists mbs, kbs, lf_tab, (Some nm), (Some []).
      rewrite Ra0, Ra1, Ra2.
      split; [exact Dmd|]. split; [exact Dmwf|]. split; [exact Dk|]. split; [exact Dwf|]. split; [exact Dtab|].
      split; [split; [unfold MD_MARK, MARK_LEN in *; clia | exact HnmcA]|].
      split; [split; [lia | exact HSE]|].
      split; [exact M1|]. split; [exact M2|].
      split.
      { intros s Hs. injection Hs as <-.
        destruct (lf_md_sub SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk T3 (ms_regs msA) MODEL_WRITE_AK
          (md + MD_MARK + MARK_LEN * j) (Z.of_nat (length nm) + 1) HB HJ Hblk' Rsp HK8
          ltac:(unfold MD_MARK, MARK_LEN; clia) ltac:(unfold MD_MARK, MARK_LEN, MD_SIZE; clia) ltac:(clia))
          as (S1 & S2 & S3' & S4).
        split; [unfold MD_MARK, MARK_LEN in *; clia|]. split; [clia|]. split; [exact S3'|]. split; [exact S1|].
        split; [exact S2|]. split; [exact S4|].
        intros a0 Ha0.
        apply (lf_md_tail SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk T3 (md + MD_MARK + MARK_LEN * j) (Z.of_nat (length nm) + 1)
          HB HJ Hblk' ltac:(unfold MD_MARK, MARK_LEN; clia) ltac:(unfold MD_MARK, MARK_LEN, MD_SIZE; clia) ltac:(clia)).
        replace (Z.of_nat (length nm) + 1 - 1) with (Z.of_nat (length nm)) by lia. exact Ha0. }
      split.
      { intros i0 n2 ix p Hn Hp Rp.
        exact (proj1 (lf_tab_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs (ms_regs msA) MODEL_WRITE_AK HB HJ HRO Hdat' Rsp HK8
          i0 n2 ix p Hn Hp Rp)). }
      split.
      { intros s Hs. injection Hs as <-. cbn [length Z.of_nat].
        split; [lia|]. split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
        split; [rewrite ard_aview; exact (kp_ra B TB ly3 S3 _ _ _ MA KR1)|].
        split; [rewrite ard_aview; exact (kp_hull B TB ly3 S3 _ _ _ MA KH1)|].
        split; [unfold apart_frame; left; rewrite Rsp; rewrite MODEL_WRITE_AK_val; unfold LLVMF_STK in *; clia|].
        exists (abytes_of SEGS (rdW W3 (ms_mem msA)) (0x20fc0 + 0 + 1) (Z.to_nat ((- (0x20fc0 + 0 + 1)) mod 8))).
        rewrite abytes_of_length. split; [|change ((- (0x20fc0 + 0 + 1)) mod 8) with 7; cbn; lia].
        apply abytes_of_abytes; [lia | cbn; lia|]. intros k0 Hk0.
        exact (kp_somes_mbyte SEGS (rdW W3 (ms_mem msA)) _ _ KS1 k0 Hk0). }
      split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|].
      split; [exact M8|]. split; [exact M9|].
      rewrite (ts_errno B TB); unfold apart, YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, AF0m.TFIB_ERRNO,
        MD_SIZE in *; clia.
    + (* the return, +0x838 *)
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
      pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
      assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
      assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
      pose proof (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 (rdW W3 (ms_mem msA)) md mk HAR2 Pmd Pmk) as WC.
      (* model_write's post *)
      specialize (Hpost mbs kbs lf_tab (Some nm) (Some [])). rewrite Ra0, Ra1, Ra2 in Hpost.
      destruct (Hpost Dmd Dk Dtab ltac:(split; [unfold MD_MARK, MARK_LEN in *; clia | exact HnmcA])
        ltac:(split; [lia | exact HSE]))
        as (Hrc & (mbs' & Hmd2 & Hmwf2 & Hnx2 & Hso2 & Hse2 & Hrq2 & Hnr2 & Hnm2 & Hmm2)).
      clear Hpost.
      destruct (lf_model_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
        cx fp MODEL_WRITE_AK ly3 S3 ly2 S2 W3 msA md4 W2 ms2 md2 Er k2 _ _ _ _ md mk kbs mbs gbs mbs' T3 _ P N SH_Z
        HB HJ Hfr LC HE Hfd2 Hfs2 Pmd Pmk WC ltac:(rewrite SH_Z_len; lia) Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat'
        Hmd2 Hmwf2 Hnm2 Hmm2) as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & HRO2).
      pose proof (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 _ _ _ _
        ly3 S3 ly2 S2 W2 ms2 md2 T3 _ k2 HB HJ2 Hs2 Hperm Hjbk2) as Hjbk3.
      pose proof (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2) as Hblk3.
      pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
      apply (HJN cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
      exists md, mk, P, N, kbs, mbs', gbs, T3.
      split.
      { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
        rewrite Q1. unfold LU_join, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
      cbn [ms_regs ms2 mkst].
      split; [rewrite P23, Q23; exact R23|]. split; [rewrite P20, Q20; exact R20|]. split; [rewrite P18, Q18; exact R18|].
      split.
      { split; [exact Hi|]. split.
        { unfold lf_core in *. cbn [ms_regs ms2 mkst]. rewrite P2, P8, P9, P3, P4, Q2, Q8, Q9, Q3, Q4.
          rewrite R8, R9. repeat split; assumption. }
        split.
        { unfold u_regs in *. cbn [ms_regs ms2 mkst]. rewrite P19, P21, P22, P24, P25, P26, P27, Q19, Q21, Q22, Q24,
            Q25, Q26, Q27. repeat split; assumption. }
        split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|]. split; [exact Hcur2|].
        split; [exact Hjbk3|]. split; [exact Hblk3|]. split; [exact Hdat2 | exact Hop]. }
      split; [rewrite Hnm2; exact Hj|]. split; [exact Hns|].
      cbn [write_model w_rc w_reqs w_state] in Hrc, Hnx2, Hso2, Hse2, Hrq2.
      rewrite Hrq, Hks in Hnx2, Hso2, Hse2, Hrq2.
      assert (KS : md_kstate mbs' kbs = w_state (write_core lf_tab (Some nm) (Some [])
        (r_reqs (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0)) (r_state (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0)))).
      { destruct (u_write_ce lf_tab (Some nm) (Some []) (r_reqs (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0))
          (r_state (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0))) as (Ce & Ee).
        destruct (u_read_ce lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) as (Ce' & Ee').
        apply u_md_kstate_of; [exact Hnx2 | exact Hso2 | exact Hse2 | |].
        - rewrite Ce. rewrite <- Hks. unfold md_kstate. reflexivity.
        - rewrite Ee. rewrite <- Hks. unfold md_kstate. reflexivity. }
      rewrite Hrq2, KS.
      exact (u_step_write lf_tab (mk_names gbs) j nm reqs0 K0 _ ltac:(lia) Hnm HUW Hr0 Hbl).
Qed.

End a.
