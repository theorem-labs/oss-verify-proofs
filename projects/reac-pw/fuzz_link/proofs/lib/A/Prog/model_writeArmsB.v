(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module names changed; 364 of its 418 lines of code are new or changed and 537 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: the three refusal arms of the MID cut (+0x124) that call nothing (cut interface
   lib/A/Prog/model_writeDefs.v; listing (internal path) (internal record, sha256 2152d78b142c)):
     +0x124  `beqz s6`          name = NULL                       -> +0x210 with s8 = -22
     +0x128..+0x134 (+0x288)    the instrumented check of the 1-byte load of name[0]
     +0x138  `beqz s3`          alias = NULL                      -> +0x210 with s8 = -22
     +0x13c..+0x140 `lbu`       the name is empty                 -> +0x210 with s8 = -22
   Template: lib/A/Prog/reac_link_alias_writeArmsB.v, arms 1, 3, 4.
   The engine runs at the atoms of the MID cut (atom r = register r there: s6 = 22 the name, s9 = 25 the shadow
   base, s3 = 19 the alias); the shadow entry `mkSHE 22 0 1` is the name's first byte, whose `sh_ok` is the Pre's
   `range_addressable` of the name carried to the cut (model_writeCut.v mw_shadow_at). No arm writes memory, so the
   EXIT cut's base is the MID cut's and its result clause is `mw_pf_at` (model_writeArmsA.v).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit model_writeStep model_writeArmsA model_writeCut
model_writeCall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma mw_ms_eta2 : forall (fx : YK11.FPState) (ms : machine_state),
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros fx [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.

Definition MwBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition MwBx : sv := SOff 25 0.                  (* s9 holds the shadow base from +0x68 on *)

(* the environment at a cut: atom r is register r there, then the extra words, then the image's objects *)
Definition mwE (ms3 : machine_state) (extra : list word) : env := Eimg (Ereg (ms_regs ms3) extra).

Lemma mwE_reg : forall ms3 extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (mwE ms3 extra) n = getr (ms_regs ms3) r.
Proof.
  intros ms3 extra n r Hn. unfold mwE.
  pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat (ms_regs ms3) extra n r Hn).
Qed.

Lemma mwE_sv : forall ms3 extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (mwE ms3 extra) (SOff n 0) = getr (ms_regs ms3) r.
Proof.
  intros ms3 extra n r Hn. cbn [sv_denot]. rewrite (mwE_reg ms3 extra n r Hn), Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma mwE_extra : forall ms3 extra j, (32 + j < A_TEXT)%nat ->
  ew (mwE ms3 extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
  intros ms3 extra j Hj. unfold mwE. rewrite Eimg_low by exact Hj.
  exact (ew_Ereg_extra (ms_regs ms3) extra j).
Qed.

(* the machine state at a cut, in the shape the run lemmas take *)
Lemma mw_mkst_at : forall (ms3 : machine_state) (pc : Z),
  ms_resv ms3 = None -> ms_svc_pending ms3 = None -> ms_rom ms3 = seg_rom SEGS ->
  ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr -> ms_pc_val ms3 = w64 (BASE + pc) ->
  ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS).
Proof.
  intros ms3 pc H1 H2 H3 H4 H5 H6.
  transitivity (mkst (ms_regs ms3) (ms_pc_val ms3) (ms_mem ms3) (ms_rom ms3));
    [exact (mw_ms_eta2 fx ms3 H1 H2 H4 H5) | rewrite H3, H6; reflexivity].
Qed.

Set Default Proof Using "All".

Lemma mw_base_shape : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr.
Proof. intros cx fpos X ly3 S3 W3 ms3 md3 H. unfold mw_base in H. cbv zeta in H. tauto. Qed.

Lemma mw_base_X : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> getr (ms_regs ms3) 19 = w64 (mw_alias cx).
Proof. intros cx fpos X ly3 S3 W3 ms3 md3 H. unfold mw_base in H. cbv zeta in H. tauto. Qed.

(* ---- the EXIT cut after a stretch that wrote nothing ---- *)
Lemma mw_exit_nomem : mw_exit_obl SK B ->
  forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 (ms : machine_state) md (rcv : Z),
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 ->
  ms_mem ms = ms_mem ms3 ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + MW_CUT_EXIT)) (ms_mem ms) (seg_rom SEGS) ->
  ajournal_gx SEGS B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx)
    ly3 S3 W3 (ms_mem ms) md (mw_k cx) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  mw_rsame (ms_regs ms3) (ms_regs ms) ->
  getr (ms_regs ms) 24 = w64 rcv ->
  (forall mbs kbs tab nm al,
     amodel_at SEGS (mw_m0 cx) (mw_m cx) mbs -> anlk_at SEGS (mw_m0 cx) LA_G_NL kbs ->
     aiftab_at SEGS (mw_m0 cx) LA_G_NL kbs tab ->
     astr_arg SEGS (mw_m0 cx) (mw_name cx) nm -> astr_arg SEGS (mw_m0 cx) (mw_alias cx) al ->
     rcv = w_rc (write_model tab nm al (md_reqs mbs) (md_kstate mbs kbs)) /\
     w_reqs (write_model tab nm al (md_reqs mbs) (md_kstate mbs kbs)) = md_reqs mbs /\
     w_state (write_model tab nm al (md_reqs mbs) (md_kstate mbs kbs)) = md_kstate mbs kbs) ->
  SRr SEGS W3 (mkCfg ms md) (mw_post SK B cx).
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 ms md rcv HPX HB Hmem Hms HJ Hfd Hfs HR R24 HRC.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HB4 : mw_base SK B cx fpos NoX ly3 S3 W3 ms md).
  { apply (mw_base_step SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 ly3 S3 W3 ms md (mw_sp1 cx) (mw_sp1 cx) NoX
             HPX HB).
    - rewrite Hms. reflexivity.
    - rewrite Hms. reflexivity.
    - rewrite Hms. reflexivity.
    - rewrite Hms. reflexivity.
    - rewrite Hms. reflexivity.
    - exact HJ.
    - reflexivity.
    - unfold mw_base in HB. cbv zeta in HB. tauto.
    - unfold mw_base in HB. cbv zeta in HB. tauto.
    - rewrite Hmem.
      destruct (mw_cut_facts SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HPX HB) as (_ & HAR3 & _).
      apply (akept_refl SK SEGS B LAWS pa_segs_low). intros a Ha. lia.
    - lia.
    - lia.
    - intros a [].
    - intros a _ [].
    - intros a _ [].
    - exact HR.
    - exact Hfd.
    - exact Hfs. }
  apply (EXIT cx fpos ly3 S3 W3 ms md HPX).
  unfold mw_gi_exit.
  split; [rewrite Hms at 1; reflexivity|].
  split; [exact (mw_base_mono SK B LAWS TB HSEGS cx fpos NoX (mw_E cx) ly3 S3 W3 ms md HB4 (fun a H => match H with end))|].
  rewrite R24.
  pose proof HPX as (_ & _ & HP).
  eapply mw_pf_at with (cx := cx) (W' := W3) (m' := ms_mem ms) (rcv := w64 rcv); [exact HP | | |].
  - intros a Ha. rewrite Hmem.
    apply (mw_view_akb SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 a HPX HB).
    eapply mw_blk_akb; try eassumption.
    unfold mw_E, mw_wr, model_write_awr. exists (mw_m cx, mw_m cx + MD_SIZE). split; [left; reflexivity|].
    cbn [fst snd]. exact Ha.
  - intros x Hx.
    destruct (mw_cut_facts SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HPX HB) as (_ & _ & Hbl & _ & Hfa & _).
    eapply mw_blk_writable with (cx := cx) (own' := (MW_CID, fpos) :: mw_own cx) (ly' := ly3) (S' := S3) (W' := W3)
      (m' := ms_mem ms) (k' := mw_k cx).
    all: first
      [ exact LAWS | exact HSEGS | exact HPX | exact HJ | exact Hfa | exact Hbl
      | intros y Hy; right; exact Hy
      | unfold mw_E, mw_wr, model_write_awr; exists (mw_m cx, mw_m cx + MD_SIZE); split; [left; reflexivity|];
        cbn [fst snd]; exact Hx ].
  - intros mbs kbs tab nm al H1 H2 H3 H4 H5. destruct (HRC mbs kbs tab nm al H1 H2 H3 H4 H5) as (Hr & Hq & Hs).
    split; [rewrite Hr; reflexivity|]. split; [exact Hq | exact Hs].
Qed.

(* the registers mw_rsame names, from a run whose symbolic end state keeps them *)
Ltac mw_rsame_with HS ms3 E19 :=
  let Q2 := fresh "Q" in let Q9 := fresh "Q" in let Q8 := fresh "Q" in let Q18 := fresh "Q" in
  let Q27 := fresh "Q" in let Q21 := fresh "Q" in let Q23 := fresh "Q" in
  let Q20 := fresh "Q" in let Q3 := fresh "Q" in let Q4 := fresh "Q" in
  prreg HS (2%bv : bv 5) Q2; rewrite (mwE_reg ms3 _ 2%nat 2%bv eq_refl) in Q2;
  prreg HS (9%bv : bv 5) Q9; rewrite (mwE_reg ms3 _ 9%nat 9%bv eq_refl) in Q9;
  prreg HS (8%bv : bv 5) Q8; rewrite (mwE_reg ms3 _ 8%nat 8%bv eq_refl) in Q8;
  prreg HS (18%bv : bv 5) Q18; rewrite (mwE_reg ms3 _ 18%nat 18%bv eq_refl) in Q18;
  prreg HS (27%bv : bv 5) Q27; rewrite (mwE_reg ms3 _ 27%nat 27%bv eq_refl) in Q27;
  prreg HS (21%bv : bv 5) Q21; rewrite (mwE_reg ms3 _ 21%nat 21%bv eq_refl) in Q21;
  prreg HS (23%bv : bv 5) Q23; rewrite (mwE_reg ms3 _ 23%nat 23%bv eq_refl) in Q23;
  prreg HS (20%bv : bv 5) Q20; rewrite (mwE_reg ms3 _ 20%nat 20%bv eq_refl) in Q20;
  prreg HS (3%bv : bv 5) Q3; rewrite (mwE_reg ms3 _ 3%nat 3%bv eq_refl) in Q3;
  prreg HS (4%bv : bv 5) Q4; rewrite (mwE_reg ms3 _ 4%nat 4%bv eq_refl) in Q4;
  exact (conj Q2 (conj Q9 (conj Q8 (conj Q18 (conj Q27 (conj Q21 (conj Q23 (conj E19 (conj Q20 (conj Q3 Q4)))))))))).
Ltac mw_rsame_of_run HS ms3 :=
  let Q19 := fresh "Q" in
  prreg HS (19%bv : bv 5) Q19; rewrite (mwE_reg ms3 _ 19%nat 19%bv eq_refl) in Q19;
  mw_rsame_with HS ms3 Q19.

(* ==========================================================================
   ARM 1: the name is NULL (+0x124 `beqz s6` taken): -22
   ========================================================================== *)
Lemma mw_arm_name_null : mw_exit_obl SK B ->
  forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3,
    mw_pre SK B cx -> mw_gi_mid SK B cx fpos ly3 S3 W3 ms3 md3 -> mw_name cx = 0 ->
    SRr SEGS W3 (mkCfg ms3 md3) (mw_post SK B cx).
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 HPX HMID Hnull.
  destruct HMID as (Hpc & Hs6 & Hs8 & Hs9 & HB).
  pose proof (mw_base_shape cx fpos NoX ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (mw_base_jx SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPX as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  assert (HEI : img_env VAL A_LIM (mwE ms3 [])) by apply Eimg_env.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_MID)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (mw_mkst_at ms3 MW_CUT_MID); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_MID)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HS : st_ok_pi SEGS VAL (mwE ms3 [])
     (mkSS MW_CUT_MID (sr_set sr_atoms 22%bv (SLit 0)) [] None (mkFacts [] [] []))
     (restrict (w_H W3) ms3)).
  { apply (ast_ok_pi_set_reg_fp (mwE ms3 []) (mkSS MW_CUT_MID sr_atoms [] None (mkFacts [] [] []))
             (restrict (w_H W3) ms3) 22%bv (SLit 0)).
    - rewrite Hrms.
      apply pa_entry_st_ok_full.
      + apply regs_ok_Eimg_Ereg.
      + vm_compute; reflexivity.
      + constructor.
      + exact I.
      + split; [exact I | split; exact I].
    - reflexivity.
    - cbn [ms_regs restrict mkst sv_denot]. rewrite Hs6, Hnull. reflexivity. }
  assert (SHOK : sh_ok SEGS MwBx [] (mwE ms3 []) (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  pose (RUNTO := paj_run_to_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  paj_run_to_tok RUNTO HS HJ3 SHOK MwBspan MW_CUT_EXIT; [apply awr_ok_x_nil |].
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ _ HS eq_refl) as Hms4.
  prreg HS (24%bv : bv 5) Q24. rewrite (mwE_reg ms3 [] 24%nat 24%bv eq_refl) in Q24.
  assert (HR : mw_rsame (ms_regs ms3) (ms_regs ms)) by (unfold mw_rsame; mw_rsame_of_run HS ms3).
  apply (mw_exit_nomem EXIT cx fpos ly3 S3 W3 ms3 md3 ms _ (-22) HPX HB Hmem Hms4 HJ3).
  - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
  - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
  - exact HR.
  - rewrite Q24. exact Hs8.
  - intros mbs kbs tab nm al H1 H2 H3 H4 H5.
    assert (Hnm : nm = None).
    { destruct nm as [s|]; [|reflexivity]. exfalso. cbn in H4. apply (proj1 H4). exact Hnull. }
    rewrite Hnm, mw_wm_name_null. cbn [w_rc w_reqs w_state].
    split; [reflexivity | split; reflexivity].
Qed.

(* the shadow entry of the name's first byte, at a cut before talk *)
Lemma mw_name_shok : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 s extra,
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) 22 = w64 (mw_name cx) -> getr (ms_regs ms3) 25 = w64 SHADOW_OFF ->
  mw_name cx <> 0 -> acstr_at SEGS (mw_m0 cx) (mw_name cx) s ->
  sh_ok SEGS MwBx [mkSHE 22 0 1] (mwE ms3 extra) (mrestrict (w_H W3) (ms_mem ms3)) /\
  0 < mw_name cx /\ mw_name cx + Z.of_nat (length s) + 1 <= 2 ^ 47 - 1.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 s extra HPX HB Hs6 Hs9 Hn0 Hcs.
  pose proof HPX as (HAPRE & HRD & HP).
  pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & al0 & _ & _ & _ & _ & _ & HNM0 & _ & _ & _ & HNS0 & _).
  assert (Enm : nm0 = Some s)
    by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_name cx)); [exact HNM0 | split; assumption]).
  destruct (HNS0 s Enm) as (Hp0 & Hlen32 & Hmr & Hra & Hhv & _).
  assert (Hakb : forall a, mw_name cx <= a < mw_name cx + (Z.of_nat (length s) + 1) ->
     akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a).
  { intros a Ha. apply HRD. left. split; [exact Hn0|]. exists s.
    split; [exact Hcs | unfold mw_name in Ha; lia]. }
  destruct (mw_shadow_at SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 (mw_name cx) (Z.of_nat (length s) + 1)
              HPX HB ltac:(lia) Hakb Hra Hhv) as (Hra3 & _).
  assert (EBx : U (mwE ms3 extra) MwBx = SHADOW_OFF).
  { unfold U, MwBx. rewrite (mwE_sv ms3 extra 25%nat 25%bv eq_refl), Hs9.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (Hn1 : 0 < mw_name cx) by exact Hp0.
  assert (Hn2 : mw_name cx + Z.of_nat (length s) + 1 <= 2 ^ 47 - 1)
    by (unfold mw_name; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr; lia).
  assert (E22 : U (mwE ms3 extra) (SOff 22 0) = mw_name cx).
  { unfold U. rewrite (mwE_sv ms3 extra 22%nat 22%bv eq_refl), Hs6. apply unsigned_lit_small. lia. }
  split; [|split; [exact Hn1 | exact Hn2]].
  constructor; [|constructor].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite EBx, E22. split.
  - intros x Hx. apply Hra3. lia.
  - intros a Ha. cbn [Z.min Z.max] in Ha. unfold mw_name in Ha.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr. unfold SHADOW_OFF. lia.
Qed.

(* ==========================================================================
   ARM 2: the name is a C string but the alias is NULL (+0x138 `beqz s3` taken): -22
   ========================================================================== *)
Lemma mw_arm_alias_null : mw_exit_obl SK B ->
  forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 s,
    mw_pre SK B cx -> mw_gi_mid SK B cx fpos ly3 S3 W3 ms3 md3 ->
    mw_name cx <> 0 -> acstr_at SEGS (mw_m0 cx) (mw_name cx) s -> mw_alias cx = 0 ->
    SRr SEGS W3 (mkCfg ms3 md3) (mw_post SK B cx).
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 s HPX HMID Hn0 Hcs Hal0.
  destruct HMID as (Hpc & Hs6 & Hs8 & Hs9 & HB).
  pose proof (mw_base_shape cx fpos NoX ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (mw_base_jx SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPX as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  destruct (mw_name_shok cx fpos ly3 S3 W3 ms3 md3 s [] HPX HB Hs6 Hs9 Hn0 Hcs) as (SHOK & Hn1 & Hn2).
  pose proof (mw_base_X cx fpos NoX ly3 S3 W3 ms3 md3 HB) as R19.
  assert (HEI : img_env VAL A_LIM (mwE ms3 [])) by apply Eimg_env.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_MID)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (mw_mkst_at ms3 MW_CUT_MID); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_MID)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HS : st_ok_pi SEGS VAL (mwE ms3 [])
     (mkSS MW_CUT_MID (sr_set sr_atoms 19%bv (SLit 0)) [] None
        (mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 1) 0); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
     (restrict (w_H W3) ms3)).
  { apply (ast_ok_pi_set_reg_fp (mwE ms3 [])
             (mkSS MW_CUT_MID sr_atoms [] None
                (mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 1) 0); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
             (restrict (w_H W3) ms3) 19%bv (SLit 0)).
    - rewrite Hrms. apply pa_entry_st_ok_full.
      + apply regs_ok_Eimg_Ereg.
      + vm_compute; reflexivity.
      + constructor.
      + exact I.
      + split; [|split; [exact I | exact I]].
        cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
        * unfold afact_ok. cbn [af_lo af_hi af_al2].
          rewrite (mwE_reg ms3 [] 22%nat 22%bv eq_refl), Hs6, unsigned_lit_small by lia.
          split; [lia | split; [apply Zmod_1_r | lia]].
        * unfold afact_ok. cbn [af_lo af_hi af_al2].
          rewrite (mwE_reg ms3 [] 25%nat 25%bv eq_refl), Hs9, unsigned_lit_small by (unfold SHADOW_OFF; lia).
          split; [lia | split; [apply Zmod_1_r | lia]].
    - reflexivity.
    - cbn [ms_regs restrict mkst sv_denot]. rewrite R19, Hal0. reflexivity. }
  pose (RUNTO := paj_run_to_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  paj_run_to_tok RUNTO HS HJ3 SHOK MwBspan MW_CUT_EXIT; [apply awr_ok_x_nil |].
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ _ HS eq_refl) as Hms4.
  prreg HS (24%bv : bv 5) Q24. rewrite (mwE_reg ms3 [] 24%nat 24%bv eq_refl) in Q24.
  prreg HS (19%bv : bv 5) Q19x.
  assert (E19 : getr (ms_regs ms) 19 = getr (ms_regs ms3) 19) by (rewrite Q19x, R19, Hal0; reflexivity).
  assert (HR : mw_rsame (ms_regs ms3) (ms_regs ms)) by (unfold mw_rsame; mw_rsame_with HS ms3 E19).
  apply (mw_exit_nomem EXIT cx fpos ly3 S3 W3 ms3 md3 ms _ (-22) HPX HB Hmem Hms4 HJ3).
  - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
  - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
  - exact HR.
  - rewrite Q24. exact Hs8.
  - intros mbs kbs tab nm al H1 H2 H3 H4 H5.
    assert (Hal : al = None).
    { destruct al as [a0|]; [|reflexivity]. exfalso. cbn in H5. apply (proj1 H5). exact Hal0. }
    rewrite Hal, mw_wm_alias_null. cbn [w_rc w_reqs w_state].
    split; [reflexivity | split; reflexivity].
Qed.

(* ==========================================================================
   ARM 3: the name is the empty string (+0x13c `lbu` reads its NUL, +0x140 `beqz` taken): -22
   ========================================================================== *)
Lemma mw_arm_name_empty : mw_exit_obl SK B ->
  forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 a0,
    mw_pre SK B cx -> mw_gi_mid SK B cx fpos ly3 S3 W3 ms3 md3 ->
    mw_name cx <> 0 -> acstr_at SEGS (mw_m0 cx) (mw_name cx) [] ->
    mw_alias cx <> 0 -> acstr_at SEGS (mw_m0 cx) (mw_alias cx) a0 ->
    SRr SEGS W3 (mkCfg ms3 md3) (mw_post SK B cx).
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 a0 HPX HMID Hn0 Hcs Ha0 Hca.
  destruct HMID as (Hpc & Hs6 & Hs8 & Hs9 & HB).
  pose proof (mw_base_shape cx fpos NoX ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (mw_base_jx SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPX as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  destruct (mw_name_shok cx fpos ly3 S3 W3 ms3 md3 [] [] HPX HB Hs6 Hs9 Hn0 Hcs) as (SHOK & Hn1 & Hn2).
  cbn [length Z.of_nat] in Hn2.
  pose proof (mw_base_X cx fpos NoX ly3 S3 W3 ms3 md3 HB) as R19.
  assert (Ha1 : 0 < mw_alias cx) by (destruct Hca as ((H0 & _ & _) & _); lia).
  pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & al0 & _ & _ & _ & _ & _ & _ & HAL0 & _ & _ & _ & _ & HAS0 & _).
  assert (Eal : al0 = Some a0)
    by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_alias cx)); [exact HAL0 | split; assumption]).
  destruct (HAS0 a0 Eal) as (_ & Hmra & _).
  assert (Ha2 : mw_alias cx + 1 <= 2 ^ 47 - 1)
    by (unfold mw_alias; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmra; lia).
  (* the name's NUL at the cut's memory *)
  assert (Hcs3 : acstr_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) (mw_name cx) []).
  { apply (mw_acstr_move SEGS (mw_m0 cx) (mrestrict (w_H W3) (ms_mem ms3)) (mw_name cx) [] Hcs).
    intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    apply (mw_view_akb SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 x HPX HB). apply HRD. left.
    split; [exact Hn0|]. exists ([] : list byte). split; [exact Hcs | unfold mw_name in *; cbn [length] in *; lia]. }
  pose proof (mw_abytes_head SEGS (mrestrict (w_H W3) (ms_mem ms3)) (mw_name cx) (zb 0) []
                ltac:(cbn [app] in Hcs3; exact (proj1 Hcs3))) as Hbyte.
  assert (HEI : img_env VAL A_LIM (mwE ms3 [])) by apply Eimg_env.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_MID)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (mw_mkst_at ms3 MW_CUT_MID); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_MID)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HS : st_ok_pi SEGS VAL (mwE ms3 [])
     (mkSS MW_CUT_MID sr_atoms
        [YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]] None
        (mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 1) 0); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
                  (19%nat, mkAF 1 (2 ^ 47 - 1) 0)] [] []))
     (restrict (w_H W3) ms3)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor; [|constructor].
      unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (mwE_reg ms3 [] 22%nat 22%bv eq_refl), Hs6, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. unfold chunk_ok.
      cbn [YP09.c_off YP09.c_val YP09.c_len]. intros i Hi.
      assert (i = 0) as -> by (cbn in Hi; lia). exists (zb 0). split.
      + cbn [cbyte byte_of_word sv_denot]. reflexivity.
      + rewrite !Z.add_0_r. exact Hbyte.
    - cbn; tauto.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. split; [|split; [|split; [|exact I]]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (mwE_reg ms3 [] 22%nat 22%bv eq_refl), Hs6, unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (mwE_reg ms3 [] 25%nat 25%bv eq_refl), Hs9, unsigned_lit_small by (unfold SHADOW_OFF; lia).
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (mwE_reg ms3 [] 19%nat 19%bv eq_refl), R19. unfold w64.
        rewrite unsigned_lit_small by (unfold mw_alias in *; lia).
        split; [unfold mw_alias in *; lia | split; [apply Zmod_1_r | unfold mw_alias in *; lia]]. }
  pose (RUNTO := paj_run_to_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  paj_run_to_tok RUNTO HS HJ3 SHOK MwBspan MW_CUT_EXIT;
    [ intros a (r0 & Hin & Hw); cbn [In] in Hin; destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; exfalso; lia |].
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & Hw). cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ _ HS eq_refl) as Hms4.
  prreg HS (24%bv : bv 5) Q24. rewrite (mwE_reg ms3 [] 24%nat 24%bv eq_refl) in Q24.
  assert (HR : mw_rsame (ms_regs ms3) (ms_regs ms)) by (unfold mw_rsame; mw_rsame_of_run HS ms3).
  apply (mw_exit_nomem EXIT cx fpos ly3 S3 W3 ms3 md3 ms _ (-22) HPX HB Hmem Hms4 HJ3).
  - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
  - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
  - exact HR.
  - rewrite Q24. exact Hs8.
  - intros mbs kbs tab nm al H1 H2 H3 H4 H5.
    assert (Hnm : nm = Some []).
    { apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_name cx)); [exact H4 | split; assumption]. }
    rewrite Hnm, mw_wm_name_empty. cbn [w_rc w_reqs w_state].
    split; [reflexivity | split; reflexivity].
Qed.

End b.
End a.
