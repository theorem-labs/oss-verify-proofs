(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 189 of its 232 lines of code are new or changed and 1289 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   from +0xc0c (Op2Cut.v o2_u_inv, the model's answer in s7) through the frame objects put out of
   scope again (+0xc0c .. +0xc98: shadow indices 0x2c .. 0x2f and 0x34 .. 0x53 := the low byte of s8, 0xf8), to
   +0xc9c (o2_q_inv), where mark_quietly(mk, name) is next. The shape of Op3T.v u_tail.

   o2_un : forall POST i, FROM POST (o2_q_inv i) -> FROM POST (o2_u_inv i).

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
  LLVMFuzzerTestOneInputOp3B
  LLVMFuzzerTestOneInputOp3T LLVMFuzzerTestOneInputOp2R.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition o2u_ss : sstate := mkSS LO2_u sr_atoms [o2r_fs1; o2r_fs2] None o2r_facts.

Lemma LF_SH0_obj : forall i, (((44 <= i < 48) \/ (52 <= i < 84)))%nat -> nth i LF_SH0 0 = 248.
Proof. intros i Hi. do 84 (destruct i as [|i]; [cbn; lia || reflexivity|]). lia. Qed.

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

Lemma o2_un : forall POST i,
  FROM POST (o2_q_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HQ cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HU.
  destruct HU as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & R20 & Hw & Hlt & R22 & R26 & HM
    & R23 & Hrq & Hmk).
  destruct HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (o5_geo SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)
    as (Hal0 & Hceil0 & H470 & Hsp1r & Hsp132 & Hsp146).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  assert (HFS : lf_SH cx fp = SHADOW_OFF + lf_F cx fp / 8) by reflexivity.
  assert (SHB : kLowMemEnd + 512 <= lf_SH cx fp /\ lf_SH cx fp + 128 <= kHighMemBeg /\ lf_SH cx fp mod 4 = 0).
  { rewrite HFS. assert (D1 : 4096 / 8 <= lf_F cx fp / 8) by (apply Z.div_le_mono; clia).
    assert (D2 : lf_F cx fp / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; clia).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    pose proof (Z.div_mod (lf_F cx fp) 32 ltac:(clia)) as D. rewrite F32, Z.add_0_r in D.
    assert (Q : lf_F cx fp / 8 = 4 * (lf_F cx fp / 32)) by (rewrite D at 1; replace (32 * (lf_F cx fp / 32)) with
      ((4 * (lf_F cx fp / 32)) * 8) by clia; apply Z.div_mul; clia).
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. split; [clia|]. split; [clia|].
    rewrite Q. replace (2147450880 + 4 * (lf_F cx fp / 32)) with ((536862720 + lf_F cx fp / 32) * 4) by clia.
    apply Z_mod_mult. }
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E19 : ew E 19 = Z_to_bv 64 (lf_SH cx fp)) by (rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (U19 : bv_unsigned (ew E 19) = lf_SH cx fp)
    by (rewrite E19; apply unsigned_lit_small; clear - SHB; unfold kHighMemBeg, kLowMemEnd in *; lia).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx)
    by (rewrite E9; apply unsigned_lit_small; clear - Hsp146 Hsp1r H470; lia).
  assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 8)) by (rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl); exact (proj1 (proj2 Hkr))).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2u_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_u)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2u_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, o2r_fs1, o2r_fs2;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U19. split; [clear - SHB; unfold kLowMemEnd in *; lia|]. split; [clear - SHB; unfold kHighMemBeg in *; lia|].
        split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clear - Ho; lia.
      + rewrite U19. split; [clear - SHB; unfold kLowMemEnd in *; lia|]. split; [clear - SHB; unfold kHighMemBeg in *; lia|].
        split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clear - Ho; lia.
    - apply pairwise_disjoint_of_extents. unfold o2r_fs1, o2r_fs2, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - SHB Hsp146 Hsp1r H470 Hal0 Hceil0. pose proof alloc_ceiling_lt as CL. unfold kHighMemBeg, kLowMemEnd, LLVMF_STK, LS_B1A0 in *. repeat split; lia.
    - split; [|split; exact I]. cbn [o2r_facts o2u_ss ss_facts f_atoms atoms_ok]. split; [|split; [|exact I]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19.
        unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. split; [clia|]. split; [exact (proj2 (proj2 SHB))|]. clia.
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. clear - Hsp146 Hsp1r H470 Hsp132.
        change (2 ^ 5) with 32. lia. }
  rewrite (lf_shape_eta fy LO2_u ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_u)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_q.
  { cbn [ss_mem o2u_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    1, 2: intros a Ha; cbn [YP09.r_wlo YP09.r_whi YP09.r_base o2r_fs1 o2r_fs2 base_val] in Ha; rewrite U19 in Ha;
      left; split; [|clia]; right; right; right; exists LF_CID, fp; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite HFa; change (fs_frame_bytes LF_CID / 8) with 128;
      unfold shadow_addr; rewrite <- HFS; clia.
  }
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  set (X := fun a => (lf_SH cx fp + 44 <= a mod 2 ^ 64 < lf_SH cx fp + 48) \/
                     (lf_SH cx fp + 52 <= a mod 2 ^ 64 < lf_SH cx fp + 84)).
  assert (KA : kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { apply (u_kagree_frame E (ss_mem o2u_ss) _ _ X HFrA). intros a (r & Hr & Hw0). unfold X.
    rewrite Z_to_bv_unsigned in Hw0. unfold bv_wrap in Hw0. change (bv_modulus 64) with (2 ^ 64) in Hw0.
    cbn [ss_mem o2u_ss In] in Hr. destruct Hr as [<- | [<- | []]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base o2r_fs1 o2r_fs2 base_val] in Hw0; rewrite ?U19 in Hw0; clia. }
  assert (NX : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> X a ->
     ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_slots_fp cx a /\
     ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\ ~ lf_data_fp md mk a).
  { intros a Hf HXa. pose proof (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
      LAWS cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk Hf) as R.
    unfold X in HXa. rewrite !Z.mod_small in HXa by exact (proj1 R).
    exact (u_fs_out SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk ltac:(clia)). }
  pose proof (lf_saved_keep X cx W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (NX a ltac:(tauto) HXa) Ha) Hsv) as Hsv'.
  pose proof (lf_header_keep X cx fp W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (NX a ltac:(tauto) HXa)) Ha) Hhd) as Hhd'.
  pose proof (lf_slots_keep X cx md mk fp W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (NX a ltac:(tauto) HXa))) Ha) Hsl) as Hsl'.
  pose proof (lf_cur_keep X cx W3 ms3 W3 msA P N KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))) Ha) Hcur) as Hcur'.
  pose proof (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msA md4 KA Fd Fs
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))) Ha) Hjbk) as Hjbk'.
  pose proof (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))))) Ha) Hblk) as Hblk'.
  pose proof (lf_data_nm_keep X _ _ cx md mk kbs mbs gbs KA (wcarry_on_grows _ _ _ HGA)
    (fun a Ha HXa => proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))))) Ha) Hdatn) as Hdatn'.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssA := ssx) in HS end.
  assert (RG0 : region_ok SEGS E (rdW W3 (ms_mem msA)) (nth 0 (ss_mem ssA) o2r_fs1))
    by exact (st_ok_pi_region_nth E ssA (restrict (w_H W3) msA) 0 _ HS eq_refl).
  assert (RG1 : region_ok SEGS E (rdW W3 (ms_mem msA)) (nth 1 (ss_mem ssA) o2r_fs1))
    by exact (st_ok_pi_region_nth E ssA (restrict (w_H W3) msA) 1 _ HS eq_refl).
  assert (V24 : bv_unsigned (sv_denot E (SOff 24 0)) mod 256 = 248)
    by (rewrite (lf_sv_off E 24 _ 0 E24) by lia; rewrite Z.add_0_r, Z_to_bv_unsigned; reflexivity).
  assert (Hfs' : lf_fshadow cx fp W3 msA LF_SH0).
  { apply (o2r_fsh_upd cx fp W3 ms3 msA X SH_M LF_SH0 Hfs KA); [reflexivity|].
    intros i0 Hi0. assert (Hi1 : (i0 < 112)%nat) by exact Hi0.
    assert (OUT : ~ (((44 <= i0 < 48) \/ (52 <= i0 < 84)))%nat ->
      (~ X (lf_SH cx fp + Z.of_nat i0) /\ nth i0 LF_SH0 0 = nth i0 SH_M 0)).
    { intros Hn. split.
      - unfold X. rewrite Z.mod_small by (unfold kHighMemBeg in *; clia). clear - Hn. lia.
      - rewrite (SH_M_nth i0 Hi1). destruct (Nat.leb_spec 44 i0), (Nat.ltb_spec i0 48), (Nat.leb_spec 52 i0),
          (Nat.ltb_spec i0 84); cbn [andb orb]; try reflexivity; clear - Hn H H0 H1 H2; lia. }
    destruct (Nat.lt_ge_cases i0 44) as [L1 | L1]; [left; apply OUT; lia|].
    destruct (Nat.lt_ge_cases i0 48) as [L2 | L2].
    { right. rewrite (LF_SH0_obj i0 ltac:(lia)).
      apply (u_byte_sv E (w_H W3) (ms_mem msA) _ (lf_SH cx fp) (Z.of_nat i0) (SOff 24 0) 248 RG0).
      + cbn [nth ss_mem ssA setpc YP09.r_base base_val]. exact U19.
      + cbn [nth ss_mem ssA setpc YP09.r_chunks].
        assert (Hk' : i0 = 44%nat \/ i0 = 45%nat \/ i0 = 46%nat \/ i0 = 47%nat) by lia.
        repeat (destruct Hk' as [-> | Hk']; [cbn [In Z.of_nat]; repeat (first [left; reflexivity | right])|]).
        subst i0. cbn [In Z.of_nat]. repeat (first [left; reflexivity | right]).
      + exact V24. }
    destruct (Nat.lt_ge_cases i0 52) as [L3 | L3]; [left; apply OUT; lia|].
    destruct (Nat.lt_ge_cases i0 84) as [L4 | L4]; [|left; apply OUT; lia].
    right. rewrite (LF_SH0_obj i0 ltac:(lia)).
    apply (u_byte_sv E (w_H W3) (ms_mem msA) _ (lf_SH cx fp) (Z.of_nat i0) (SOff 24 0) 248 RG1).
    + cbn [nth ss_mem ssA setpc YP09.r_base base_val]. exact U19.
    + cbn [nth ss_mem ssA setpc YP09.r_chunks].
      assert (Hk' : exists k, (k < 32)%nat /\ i0 = (52 + k)%nat) by (exists (i0 - 52)%nat; lia).
      destruct Hk' as (k & Hk & ->).
      do 32 (destruct k as [|k]; [cbn [In Nat.add Z.of_nat]; repeat (first [left; reflexivity | right])|]). lia.
    + exact V24. }
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
  rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
  rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20.
  rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in Q23.
  rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
  rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
  apply (HQ cx fy fp k2 ly3 S3 W3 msA md4 HB Hfx HJ Hfr).
  exists md, mk, P, N, s, (Some t), kbs, mbs, gbs, T3.
  split; [exact (lf_shape_of_st_ok fy W3 _ ssA msA HS eq_refl)|].
  split; [rewrite Q20; exact R20|]. split; [exact Hw|].
  split; [rewrite Q22; exact R22|]. split; [rewrite Q26; exact R26|].
  split.
  { split; [exact Hi|]. split; [unfold lf_core in *; rewrite Q2, Q8, Q9, Q3, Q4; exact Hcore|].
    split; [unfold o2_kregs in *; rewrite Q19, Q24, Q25, Q27; exact Hkr|].
    split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|]. split; [exact Hsl'|]. split; [exact Hcur'|].
    split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact Hdatn'|]. split; [exact Hop | exact Hns]. }
  split; [rewrite Q23; exact R23|]. split; [exact Hrq | exact Hmk].
Qed.

End a.
