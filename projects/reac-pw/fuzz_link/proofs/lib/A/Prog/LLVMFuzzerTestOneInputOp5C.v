(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 416 of its 465 lines of code are new or changed and 355 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): op_refused
   (+0x958) after mark_quietly returns at +0xa28: `addi a1, zero, -22; jal check_mark` (0x83200), `mv a0, s6;
   jal check_requests` (0x83208), `j +0x1110` to the loop tail.
   `o5c_tail` (+0xa38 to LF_tail), `o5c_after_cm` (+0xa30: check_requests, then the tail), `o5c_after_mq` (+0xa28:
   check_mark with -22 = the code mark_quietly answered, then the rest), from a cut of the loop at those pcs.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro PcapRelroA YC4b link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi
  LinkWalkCall LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import check_write_c check_mark_c check_requests_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation AFL := AF_LLVMFuzzerTestOneInput.

(* the runner's entry state of a register-only stretch at pc: the registers as their atoms, no region *)
Definition o5c_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

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
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis HV : LinkVals (L := link_listing).
(* check_mark and check_requests, as their lanes prove them (check_mark_c.v, check_requests_c.v) *)
Hypothesis CM : forall fx0 : YK11.FPState, @check_mark_acontract fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CR : forall fx0 : YK11.FPState, @check_requests_acontract fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
#[local] Abbreviation FROM POST GI :=
  (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Abbreviation TAIL i := (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).

Lemma o5c_entry : forall (fy : YK11.FPState) (W : world SEGS) regs mem pc,
  st_ok_pi (fx := fy) SEGS pa_val (Eimg (Ereg regs [])) (o5c_ss pc)
    (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros fy W regs mem pc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [|split; exact I]. exact I.
Qed.

(* a register a run left as the atom of its entry value holds that value, at a call stop *)
Lemma o5c_reg_atom_call : forall (fy : YK11.FPState) (W : world SEGS) E ss pc ms regs0 (r : bv 5),
  st_ok (fx := fy) SEGS E (setpc ss pc) (restrict (w_H W) ms) -> env_agree 32 (Ereg regs0 []) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fy W E ss pc ms regs0 r HS HA Hr.
  rewrite (st_ok_restrict_reg SEGS (w_H W) E (setpc ss pc) ms r HS). cbn [setpc ss_regs]. rewrite Hr.
  pose proof (bv_unsigned_in_range 5 r) as Rr. change (bv_modulus 5) with 32 in Rr.
  cbn [sv_denot]. destruct HA as [HA _]. rewrite (HA (Z.to_nat (bv_unsigned r))) by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Ereg_nat. lia.
Qed.

(* the leaf form of an aleaf contract: no read set *)
Lemma o5c_aleaf_rd : forall (fy : YK11.FPState) pc K EV SIDE Pre Wr Post,
  @aleaf fy rc SK SEGS PCAP_RLO PCAP_RHI B pc K EV SIDE Pre Wr Post ->
  @aleaf_rd fy rc SK SEGS PCAP_RLO PCAP_RHI B pc K EV SIDE Pre (fun _ _ _ => False) Wr Post.
Proof. intros fy pc K EV SIDE Pre Wr Post H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA _ HP.
  exact (H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HP). Qed.

Lemma o5c_m22_ne : w64 (- E_INVAL) <> w64 RC_FAILS.
Proof. intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate. Qed.

(* a callee-saved register across a call *)
Lemma o5c_pres : forall (regs regs2 : bvmap 5 word), aregs_preserved regs regs2 ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 Hp r Hr. pose proof (Hp (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* the data's five objects stay writable across a callee (ArmK.v ak_wcarry_callee) *)
Lemma o5c_wcarry : forall ly2 S2 (W2 : world SEGS) mem2 md2 (m : word -> option byte) md mk,
  AR SEGS B ly2 S2 W2 mem2 md2 -> In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  wcarry_on m (rdW W2 mem2) (lf_data_fp_w md mk).
Proof.
  intros ly2 S2 W2 mem2 md2 m md mk HAR Hmd Hmk a Ha _.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - generalize (rdW W2 mem2). rewrite HSEGS. intros m2. exact (LA_G_NL_writable m2 a ltac:(unfold NK_SIZE in Ha; lia)).
  - generalize (rdW W2 mem2). rewrite HSEGS. intros m2.
    exact (LA_G_NAMES_writable m2 a ltac:(unfold G_NAMES_SIZE in Ha; lia)).
  - generalize (rdW W2 mem2). rewrite HSEGS. intros m2. revert a Ha.
    apply writable_at_of_wseg; [unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS; lia |].
    exact wseg_LA_LONG_ALIAS304.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmd) as (_ & _ & _ & _ & Hp & _).
    destruct (Hp a ltac:(unfold req_size, MD_SIZE in *; cbn; lia)) as (Hpr & _).
    exact (apresent_writable SEGS (w_H W2) mem2 a Hpr).
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmk) as (_ & _ & _ & _ & Hp & _).
    destruct (Hp a ltac:(unfold req_size, MK_SIZE in *; cbn; lia)) as (Hpr & _).
    exact (apresent_writable SEGS (w_H W2) mem2 a Hpr).
Qed.

(* the cut after a leaf callee that writes nothing (check_mark, check_requests) *)
Lemma o5c_leaf_cut : forall cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 K,
  BASEF cx -> frames S3 = [(LF_CID, fp)] ->
  JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k2 ->
  0 <= K -> alloc_ceiling <= lf_sp1 cx - K ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 (ms_mem ms2) (lf_sp1 cx - K) (lf_sp1 cx) (fun a => inFP [] a) ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) ->
  S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 LF_SH0 /\
  lf_slots cx md mk fp W2 ms2 /\ lf_cur cx W2 ms2 P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly2 S2 W2 ms2 md2 T3 own /\
  lf_blocks B cx md mk T3 ly2 S2 (rdW W2 (ms_mem ms2)) /\
  lf_data cx md mk kbs mbs gbs (rdW W2 (ms_mem ms2)).
Proof.
  intros cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 K
    HB Hfr HJ3 HJ2 HK0 HK1 Hkp Hsk Hs2 Hperm Hfd Hfs Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat.
  pose proof HB as (_ & _ & _ & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
  pose proof Hjbk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof Hblk as (Bmd & Bmk & _).
  assert (LC : lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) (fun a => inFP [] a))
    by (split; [exact HK0|]; split; [exact HK1|]; split; [exact Hkp | exact Hsk]).
  assert (EN : forall a, inFP [] a -> False) by (intros a (r & Hr & _); destruct Hr).
  pose proof (lf_aro_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) _ RIMG LC
    (fun a _ H => EN a H) HRO) as HRO2.
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ3 Hn)).
  assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
  assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
  destruct (lf_cut_callee B MT MS la_nul cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2
    ms2 md2 K _ IMG RIMG LC ltac:(rewrite Hfr; left; reflexivity) HPB (fun a H _ => EN a H) Pmd Pmk
    (o5c_wcarry ly2 S2 W2 (ms_mem ms2) md2 _ md mk HAR2 Pmd Pmk) Hfd Hfs Hodd2 Htx2 (lf_la_slack_any HSEGS _)
    Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat) as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & _).
  split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
  split; [exact (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 ev mo wl lv
    ly3 S3 ly2 S2 W2 ms2 md2 T3 own k2 HB HJ2 Hs2 Hperm Hjbk2)|].
  split; [exact (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2) | exact Hdat2].
Qed.

(* +0xa38 `j +0x1110`: the loop tail, from a cut whose journal counters are already those of operation i + 1 *)
Lemma o5c_tail : forall POST i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3,
  0 <= i <= 47 -> FROM POST (TAIL i) ->
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_shape fy (AFL + 0xa38) ms3 -> lf_core cx ms3 -> lf_lregs cx md fp i ms3 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD
    ly3 S3 W3 ms3 md3 T3 [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  nk_opened kbs <= 64 * (i + 1) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 Hi NEXT HB Hfx HJ Hfr Hsh Hcore Hlr
    Hsv Hhd Hfs Hsl Hcur Hjbk Hblk Hdat Hop.
  pose proof HB as (_ & _ & HGX & _).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  rewrite (lf_shape_eta fy (AFL + 0xa38) ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (o5c_entry fy W3 (ms_regs ms3) (ms_mem ms3) (AFL + 0xa38)) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xa38))) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LF_tail; [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (lf_reg_atom fy W3 _ ssB msB _ r HS HA Hr)).
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KB (wcarry_on_grows _ _ _ HGB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as Hcur'.
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  apply (NEXT cx fy fp k2 ly3 S3 W3 msB md4 HB Hfx HJ Hfr).
  exists md, mk, P, N, kbs, mbs, gbs, T3.
  split; [lia|]. split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
  split; [repeat split; (rewrite KR by (vm_compute; reflexivity)); assumption|].
  split; [repeat split; (rewrite KR by (vm_compute; reflexivity)); assumption|].
  split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|]. split; [exact Hsl'|]. split; [exact Hcur'|].
  split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact Hdat'|]. exact Hop.
Qed.


(* +0xa30 `mv a0, s6; jal check_requests` (0x83208), then +0xa38 *)
Lemma o5c_after_cm : forall POST i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3,
  0 <= i <= 47 -> FROM POST (TAIL i) ->
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_shape fy (AFL + 0xa30) ms3 -> lf_core cx ms3 -> lf_lregs cx md fp i ms3 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD
    ly3 S3 W3 ms3 md3 T3 [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  requests_are kbs mbs ->
  nk_opened kbs <= 64 * (i + 1) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 Hi NEXT HB Hfx HJ Hfr Hsh Hcore Hlr
    Hsv Hhd Hfs Hsl Hcur Hjbk Hblk Hdat Hreq Hop.
  pose proof HB as (_ & _ & HGX & _).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  rewrite (lf_shape_eta fy (AFL + 0xa30) ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (o5c_entry fy W3 (ms_regs ms3) (ms_mem ms3) (AFL + 0xa30)) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xa30))) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok _ _ (setpc ?ssx _) _ => set (ssB := ssx) in HS end.
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (o5c_reg_atom_call fy W3 _ ssB _ msB _ r HS HA Hr)).
  (* the memory of the cut at the call *)
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KB (wcarry_on_grows _ _ _ HGB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as Hcur'.
  clear Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hcur.
  (* the registers at the call *)
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  assert (R1 : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AFL + 0xa38))).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 1%bv) with (SOff A_TEXT 4160). rewrite (codeptr_val _ 4160 HEI). reflexivity. }
  assert (R10 : getr (ms_regs msB) 10 = getr (ms_regs ms3) 22).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 10%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 10%bv) with (SOff 22 0). cbn [sv_denot]. rewrite (proj1 HA 22%nat ltac:(lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat _ _ 22 22%bv eq_refl). }
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HS eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
  rewrite Hms. clear Hms.
  rewrite pa_sigma_check_requests, (lv_text HV).
  change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 (link_text + AF_check_requests)) (ms_mem msB) (seg_rom SEGS)) md4)
    with (cfg_at SEGS CHECK_REQUESTS_A (ms_regs msB) (ms_mem msB) md4).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  pose proof Hjbk' as (J1 & _ & Jfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof Hblk' as (Bmd & Bmk & _ & _ & _ & _ & _ & _ & Bmdt & _ & _ & _ & _ & Bramd & _ & Bammd & _).
  pose proof Hdat' as (Dk & Dwf & _ & _ & _ & _ & Dmd & Dmwf & _).
  assert (Hsp : spZ (ms_regs msB) = lf_sp1 cx).
  { unfold spZ. rewrite (KR 2%bv eq_refl), C2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in Hlo. clia. }
  assert (Ha0 : aarg (ms_regs msB) 0 = md).
  { rewrite ar_aarg0, R10, L22. unfold w64. apply unsigned_lit_small.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & H4 & Hc & _). unfold req_size, MD_SIZE in *. cbn in Hc. clia. }
  assert (HKr : CHECK_REQUESTS_AK = 8272) by reflexivity.
  assert (Hev : k2 + 0 <= EV_LIB).
  { pose proof lf_ev_bound as EB. unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia. }
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_REQUESTS_A
    CHECK_REQUESTS_AK 0 [] _ _ _ _ (CR fy)
    cx fp ly3 S3 W3 (ms_mem msB) md4 k2 (ms_regs msB) (POST cx) HB HJ HRO).
  - rewrite R1. apply ret_ok_codeptr_v; [unfold AFL, AF_LLVMFuzzerTestOneInput; clia | reflexivity].
  - unfold raZ. rewrite R1, (lv_text HV). rewrite unsigned_lit_small by (unfold link_text, AFL, AF_LLVMFuzzerTestOneInput; clia).
    unfold link_text, AF_LLVMFuzzerTestOneInput; clia.
  - rewrite (KR 3%bv eq_refl), C3. exact HGP.
  - rewrite (KR 4%bv eq_refl), C4. exact HTP.
  - exact Hsp.
  - rewrite HKr. unfold LLVMF_STK. clia.
  - clia.
  - exact Hev.
  - exact (ar_side_room S3 fp [] Hfr eq_refl).
  - intros a (r & Hr & _). destruct Hr.
  - intros a (r & Hr & _). destruct Hr.
  - intros a Ha. unfold check_requests_ard, rd_ivl in Ha. rewrite Ha0 in Ha. right; left. exists md, MD_SIZE.
    split; [exact Bmd|]. change (req_size MD_SIZE) with 8856. unfold MD_SIZE in Ha. clia.
  - unfold check_requests_apre. exists kbs, mbs. rewrite Ha0.
    destruct (zsh_gnl_ard B TB SEGS ly3 S3 W3 (ms_mem msB) md4 HAR3) as (Gra & Ghv).
    split; [exact Dk|]. split; [exact Dmd|]. split; [exact Dwf|]. split; [exact Dmwf|]. split; [exact Hreq|].
    split; [exact Bramd|].
    split; [rewrite ard_aview; apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ md MD_SIZE md MD_SIZE HAR3 Bmd);
            change (req_size MD_SIZE) with 8856; unfold MD_SIZE; clia|].
    split; [exact Bammd|]. split; [exact Gra|]. split; [exact Ghv|].
    split; [unfold apart_frame; left; rewrite Hsp, HKr;
            destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & _ & Hc & _);
            unfold req_size, MD_SIZE, LLVMF_STK in *; cbn in Hc; clia|].
    unfold apart_gnl, LA_G_NL, NK_SIZE, MD_SIZE. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in Bmdt. clia.
  - intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm _.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
    change (SRr SEGS W2 (mkCfg ms2 md2) (POST cx)).
    replace (k2 + 0) with k2 in HJ2 by clia.
    destruct (o5c_leaf_cut cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N ly3 S3 W3 msB md4 ly2 S2 W2 ms2 md2
      CHECK_REQUESTS_AK HB Hfr HJ HJ2 ltac:(rewrite HKr; clia) ltac:(rewrite HKr; unfold LLVMF_STK in *; clia)
      Hkp Hsk Hs2 Hperm Hfd2 Hfs2 Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat')
      as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2).
    assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
    { intros r Hr. cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr r Hr). apply KR.
      assert (Hr' : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/
        bv_unsigned r = 9 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
        bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
        bv_unsigned r = 27) by (unfold acallee_saved in Hr; lia).
      destruct Hr' as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|E']]]]]]]]]]]]]];
        (replace r with (Z_to_bv 5 (bv_unsigned r)) by apply Z_to_bv_bv_unsigned); rewrite E'; vm_compute; reflexivity. }
    apply (o5c_tail POST i cx fy fp k2 ly2 S2 W2 ms2 md2 md mk P N kbs mbs gbs T3 Hi NEXT HB Hfx HJ2
      ltac:(rewrite Hfr2; exact Hfr)).
    + unfold lf_shape. cbn [ms2 mkst ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr].
      split; [rewrite R1; reflexivity|]. repeat split; reflexivity.
    + repeat split; rewrite PR by (unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia) | (vm_compute; right; right; right; right; right; split; discriminate) ]); assumption.
    + repeat split; rewrite PR by (unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia) | (vm_compute; right; right; right; right; right; split; discriminate) ]); assumption.
    + exact Hsv2.
    + exact Hhd2.
    + exact Hfsh2.
    + exact Hsl2.
    + exact Hcur2.
    + exact Hjbk2.
    + exact Hblk2.
    + exact Hdat2.
    + exact Hop.
Qed.

(* +0xa28 `addi a1, zero, -22; jal check_mark` (0x83200): a0 holds the code mark_quietly answered, -22 *)
Lemma o5c_after_mq : forall POST i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3,
  0 <= i <= 47 -> FROM POST (TAIL i) ->
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_shape fy (AFL + 0xa28) ms3 -> lf_core cx ms3 -> lf_lregs cx md fp i ms3 ->
  getr (ms_regs ms3) 10 = w64 (- E_INVAL) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD
    ly3 S3 W3 ms3 md3 T3 [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  requests_are kbs mbs ->
  nk_opened kbs <= 64 * (i + 1) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 Hi NEXT HB Hfx HJ Hfr Hsh Hcore Hlr HA10
    Hsv Hhd Hfs Hsl Hcur Hjbk Hblk Hdat Hreq Hop.
  pose proof HB as (_ & _ & HGX & _).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  rewrite (lf_shape_eta fy (AFL + 0xa28) ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (o5c_entry fy W3 (ms_regs ms3) (ms_mem ms3) (AFL + 0xa28)) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xa28))) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok _ _ (setpc ?ssx _) _ => set (ssB := ssx) in HS end.
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (o5c_reg_atom_call fy W3 _ ssB _ msB _ r HS HA Hr)).
  (* the memory of the cut at the call *)
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KB (wcarry_on_grows _ _ _ HGB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as Hcur'.
  clear Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hcur.
  (* the registers at the call *)
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  assert (R1 : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AFL + 0xa30))).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 1%bv) with (SOff A_TEXT 4152). rewrite (codeptr_val _ 4152 HEI). reflexivity. }
  assert (R10 : getr (ms_regs msB) 10 = getr (ms_regs ms3) 10) by (apply KR; vm_compute; reflexivity).
  assert (R11 : getr (ms_regs msB) 11 = w64 (- E_INVAL)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 11%bv HS). cbn [setpc ss_regs]. subst ssB.
    lazymatch goal with |- sv_denot _ ?e = _ => let v := eval vm_compute in e in change e with v end.
    apply bv_eq. vm_compute. reflexivity. }
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HS eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
  rewrite Hms. clear Hms.
  rewrite pa_sigma_check_mark, (lv_text HV).
  change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 (link_text + AF_check_mark)) (ms_mem msB) (seg_rom SEGS)) md4)
    with (cfg_at SEGS CHECK_MARK_A (ms_regs msB) (ms_mem msB) md4).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  pose proof Hjbk' as (J1 & _ & Jfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof Hblk' as (Bmd & Bmk & _ & _ & _ & _ & _ & _ & Bmdt & _ & _ & _ & _ & Bramd & _ & Bammd & _).
  pose proof Hdat' as (Dk & Dwf & _ & _ & _ & _ & Dmd & Dmwf & _).
  assert (Hsp : spZ (ms_regs msB) = lf_sp1 cx).
  { unfold spZ. rewrite (KR 2%bv eq_refl), C2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in Hlo. clia. }
  assert (HKr : CHECK_RC_AK = 16) by reflexivity.
  assert (Hev : k2 + 0 <= EV_LIB).
  { pose proof lf_ev_bound as EB. unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia. }
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_MARK_A
    CHECK_RC_AK 0 [] _ _ _ _ (o5c_aleaf_rd fy _ _ _ _ _ _ _ (CM fy))
    cx fp ly3 S3 W3 (ms_mem msB) md4 k2 (ms_regs msB) (POST cx) HB HJ HRO).
  - rewrite R1. apply ret_ok_codeptr_v; [unfold AFL, AF_LLVMFuzzerTestOneInput; clia | reflexivity].
  - unfold raZ. rewrite R1, (lv_text HV). rewrite unsigned_lit_small by (unfold link_text, AFL, AF_LLVMFuzzerTestOneInput; clia).
    unfold link_text, AF_LLVMFuzzerTestOneInput; clia.
  - rewrite (KR 3%bv eq_refl), C3. exact HGP.
  - rewrite (KR 4%bv eq_refl), C4. exact HTP.
  - exact Hsp.
  - rewrite HKr. unfold LLVMF_STK. clia.
  - clia.
  - exact Hev.
  - exact (ar_side_room S3 fp [] Hfr eq_refl).
  - intros a (r & Hr & _). destruct Hr.
  - intros a (r & Hr & _). destruct Hr.
  - intros a Ha. destruct Ha.
  - unfold check_rc_apre, same_rc_aregs. rewrite R10, R11, HA10.
    split; [intros E; exfalso; exact (o5c_m22_ne E) | intros _; reflexivity].
  - intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm _.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
    change (SRr SEGS W2 (mkCfg ms2 md2) (POST cx)).
    replace (k2 + 0) with k2 in HJ2 by clia.
    destruct (o5c_leaf_cut cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N ly3 S3 W3 msB md4 ly2 S2 W2 ms2 md2
      CHECK_RC_AK HB Hfr HJ HJ2 ltac:(rewrite HKr; clia) ltac:(rewrite HKr; unfold LLVMF_STK in *; clia)
      Hkp Hsk Hs2 Hperm Hfd2 Hfs2 Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat')
      as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2).
    assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
    { intros r Hr. cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr r Hr). apply KR.
      assert (Hr' : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/
        bv_unsigned r = 9 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
        bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
        bv_unsigned r = 27) by (unfold acallee_saved in Hr; lia).
      destruct Hr' as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|E']]]]]]]]]]]]]];
        (replace r with (Z_to_bv 5 (bv_unsigned r)) by apply Z_to_bv_bv_unsigned); rewrite E'; vm_compute; reflexivity. }
    apply (o5c_after_cm POST i cx fy fp k2 ly2 S2 W2 ms2 md2 md mk P N kbs mbs gbs T3 Hi NEXT HB Hfx HJ2
      ltac:(rewrite Hfr2; exact Hfr)).
    + unfold lf_shape. cbn [ms2 mkst ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr].
      split; [rewrite R1; reflexivity|]. repeat split; reflexivity.
    + repeat split; rewrite PR by (unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia) | (vm_compute; right; right; right; right; right; split; discriminate) ]); assumption.
    + repeat split; rewrite PR by (unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia) | (vm_compute; right; right; right; right; right; split; discriminate) ]); assumption.
    + exact Hsv2.
    + exact Hhd2.
    + exact Hfsh2.
    + exact Hsl2.
    + exact Hcur2.
    + exact Hjbk2.
    + exact Hblk2.
    + exact Hdat2.
    + exact Hreq.
    + exact Hop.
Qed.

End b.
End a.
