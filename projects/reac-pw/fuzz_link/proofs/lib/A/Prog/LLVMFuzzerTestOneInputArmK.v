(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 265 of its 325 lines of code are new or changed and 344 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the cut state an arm carries between its steps (for op_write
   and op_decide; generic, any arm may Require it).

   ak_cut: the memory and journal clauses every cut of the operation loop carries (lib/A/Prog/
   LLVMFuzzerTestOneInputDefs.v lf_arm_inv / lf_tail_inv without the registers and the cursor), at a general
   machine state of the arm, with the counters and the arm's own block list as parameters.
   - ak_cut_run: a register-only stretch of the body (the runner's frame_of with no region) keeps it
     (LLVMFuzzerTestOneInputKeep.v lf_cut_keep at the exception set False).
   - the block bookkeeping of the arm's allocator steps: lf_bl_perm (an aleaf callee: the block list up to
     permutation), lf_bl_cons (a fresh block, e.g. text_of's), lf_bl_uncons (a free of that block), and
     lf_jbk_restate / lf_blocks_restate, which re-state lf_jbk / lf_blocks at the return state's layout and
     allocator state once the memory clauses are carried.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Hypothesis LAWS : AR_laws SEGS B.

#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* the memory and journal clauses of a cut of the operation loop *)
Definition ak_cut (cx : lcx) (fp md mk : Z) (kbs mbs gbs : list byte) (T3 own : list (Z * Z))
    (ev mo : Z) (wl : nat) (lv k : Z) (ly : alayout) (S : astate) (W : world SEGS) (ms : machine_state)
    (mdl : Model) : Prop :=
  JRN cx fp ly S W (ms_mem ms) mdl k /\ frames S = [(LF_CID, fp)] /\
  lf_saved cx W ms /\ lf_header cx fp W ms /\ lf_fshadow cx fp W ms LF_SH0 /\ lf_slots cx md mk fp W ms /\
  lf_jbk B MT MS la_nul cx fp k ev mo wl lv ly S W ms mdl T3 own /\
  lf_blocks B cx md mk T3 ly S (rdW W (ms_mem ms)) /\
  lf_data cx md mk kbs mbs gbs (rdW W (ms_mem ms)).

(* a register-only stretch: the runner changed no byte and only materialised the model *)
Lemma ak_cut_run : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms ms' mdl mdl',
  ak_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl ->
  JRN cx fp ly S W (ms_mem ms') mdl' k ->
  kagree SEGS (fun _ => False) (rdW W (ms_mem ms)) (rdW W (ms_mem ms')) ->
  mem_grows (rdW W (ms_mem ms)) (rdW W (ms_mem ms')) ->
  m_fds mdl' = m_fds mdl -> m_fs mdl' = m_fs mdl ->
  ak_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms' mdl'.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms ms' mdl mdl'
    (_ & Hfr & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat) HJ' KA GA Fd Fs.
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k ev mo wl lv md mk kbs mbs gbs T3 own ly S W ms mdl
    W ms' mdl' KA (wcarry_on_grows _ _ _ GA) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  repeat (split; [eassumption|]). exact Hdat'.
Qed.

(* ==========================================================================
   The block list of a cut across an allocator step
   ========================================================================== *)

Lemma lf_bl_perm : forall cx own T3 ly S ly2 S2,
  lf_bl B cx own T3 ly S -> Permutation (ablocks B ly2 S2) (ablocks B ly S) -> lf_bl B cx own T3 ly2 S2.
Proof.
  intros cx own T3 ly S ly2 S2 (D & HT & HP) HP2. exists D. split; [exact HT|].
  exact (perm_trans HP2 HP).
Qed.

Lemma lf_bl_cons : forall cx own T3 ly S ly2 S2 b,
  lf_bl B cx own T3 ly S -> ablocks B ly2 S2 = ablocks B ly S ++ [b] -> lf_bl B cx (b :: own) T3 ly2 S2.
Proof.
  intros cx own T3 ly S ly2 S2 b (D & HT & HP) Hbl. exists D. split; [exact HT|].
  rewrite Hbl. cbn [app]. apply (perm_trans (Permutation_sym (Permutation_cons_append (ablocks B ly S) b))).
  apply perm_skip. exact HP.
Qed.

Lemma lf_bl_uncons : forall cx own T3 ly S ly2 S2 b l1 l2,
  lf_bl B cx (b :: own) T3 ly S -> ablocks B ly S = l1 ++ b :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
  lf_bl B cx own T3 ly2 S2.
Proof.
  intros cx own T3 ly S ly2 S2 b l1 l2 (D & HT & HP) H1 H2. exists D. split; [exact HT|].
  rewrite H2. rewrite H1 in HP. cbn [app] in HP.
  apply Permutation_sym. apply Permutation_cons_app_inv with (a := b).
  apply Permutation_sym. exact HP.
Qed.

(* a free of one of the arm's own blocks, wherever it sits in the own list *)
Lemma lf_bl_remove : forall cx o1 o2 T3 ly S ly2 S2 b l1 l2,
  lf_bl B cx (o1 ++ b :: o2) T3 ly S -> ablocks B ly S = l1 ++ b :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
  lf_bl B cx (o1 ++ o2) T3 ly2 S2.
Proof.
  intros cx o1 o2 T3 ly S ly2 S2 b l1 l2 (D & HT & HP) H1 H2. exists D. split; [exact HT|].
  rewrite H2. rewrite H1 in HP. rewrite <- app_assoc. cbn [app].
  rewrite <- app_assoc in HP. cbn [app] in HP.
  exact (Permutation_app_inv l1 l2 o1 (o2 ++ D ++ ablocks B (c_ly cx) (c_S cx)) b HP).
Qed.

(* the live bytes of a cut, from its block list *)
Lemma lf_bl_bytes : forall cx own T3 ly S,
  lf_bl B cx own T3 ly S -> exists D, T3 = c_T cx ++ D /\
    blocks_bytes S = bsum own + bsum D + blocks_bytes (c_S cx).
Proof.
  intros cx own T3 ly S (D & HT & HP). exists D. split; [exact HT|].
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  lia.
Qed.

(* ==========================================================================
   Re-stating lf_jbk and lf_blocks at the return state of a step
   ========================================================================== *)
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.

Lemma lf_jbk_restate : forall cx fp k ev mo wl lv ly S T3 own k' ev' mo' wl' lv' ly2 S2 W2 ms2 mdl2 own',
  lf_jbk B MT MS la_nul cx fp k ev mo wl lv ly S W2 ms2 mdl2 T3 own ->
  (forall c q, frame_addr ly2 c q = frame_addr (c_ly cx) c q) ->
  k' <= ev' -> blocks_bytes S2 <= blocks_bytes (c_S cx) + lv' ->
  (length (wild_part (as_universe B) (st_depot S2)) <=
     length (wild_part (as_universe B) (st_depot (c_S cx))) + wl')%nat ->
  lf_bl B cx own' T3 ly2 S2 -> incl T3 (ablocks B ly2 S2) ->
  lf_jbk B MT MS la_nul cx fp k' ev' mo' wl' lv' ly2 S2 W2 ms2 mdl2 T3 own'.
Proof.
  intros cx fp k ev mo wl lv ly S T3 own k' ev' mo' wl' lv' ly2 S2 W2 ms2 mdl2 own'
    (_ & _ & _ & Hnin & Hfd & Hfs & _ & _ & Hgi & Henv & _ & _ & Hla & Hro & Hpl & Hpv) Hfa Hk Hbb Hwl Hbl Hinc.
  split; [exact Hk|]. split; [exact Hbb|]. split; [exact Hfa|]. split; [exact Hnin|].
  split; [exact Hfd|]. split; [exact Hfs|]. split; [apply MT_LE|]. split; [exact Hwl|].
  split; [exact Hgi|]. split; [exact Henv|]. split; [exact Hbl|]. split; [exact Hinc|].
  split; [exact Hla|]. split; [exact Hro|]. split; [exact Hpl | exact Hpv].
Qed.

Lemma lf_blocks_restate : forall cx md mk T3 ly S ly2 S2 m,
  lf_blocks B cx md mk T3 ly S m -> In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  lf_blocks B cx md mk T3 ly2 S2 m.
Proof.
  intros cx md mk T3 ly S ly2 S2 m (_ & _ & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17)
    H1 H2.
  repeat (split; [assumption|]). exact H17.
Qed.

(* ==========================================================================
   A callee step of the cut (LLVMFuzzerTestOneInputKeep.v's per-predicate callee transports, then the re-statement
   at the return state)
   ========================================================================== *)
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis TB : PcapSyms B.

Lemma wseg_LA_LONG_ALIAS304 : YK1d.wseg_ok tfibsegs (Z_to_bv 64 LA_LONG_ALIAS) (Z.to_nat 304) = true.
Proof. vm_compute. reflexivity. Qed.

(* the writability of the data's five objects at the return state: the writable segments for g_nl, g_names and
   long_alias (link_ajkit.v writable_at_of_wseg), AR's block law for the two blocks *)
Lemma ak_wcarry_callee : forall ly2 S2 (W2 : world SEGS) mem2 md2 (m : word -> option byte) md mk,
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

(* the memory clauses across a callee whose write set E misses the cut's footprints and the read-only image; the
   journal clauses re-stated at the return state *)
Lemma ak_cut_callee : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3
    own' ev' mo' wl' lv' k' ly2 S2 W2 ms2 md2 K (E : Z -> Prop),
  MS = link_amf -> la_nul = LA_NUL -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  ak_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k' -> frames S2 = frames S3 ->
  AR SEGS B ly2 S2 W2 (ms_mem ms2) md2 ->
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, E a -> ~ lf_cut_fp MS la_nul cx fp md mk T3 a) ->
  (forall a, E a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  k' <= ev' -> blocks_bytes S2 <= blocks_bytes (c_S cx) + lv' ->
  (length (wild_part (as_universe B) (st_depot S2)) <=
     length (wild_part (as_universe B) (st_depot (c_S cx))) + wl')%nat ->
  lf_bl B cx own' T3 ly2 S2 -> incl T3 (ablocks B ly2 S2) ->
  ak_cut cx fp md mk kbs mbs gbs T3 own' ev' mo' wl' lv' k' ly2 S2 W2 ms2 md2 /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 own' ev' mo' wl' lv' k' ly2 S2 W2 ms2 md2 K E
    HMS HLA HPB (HJ & Hfr & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat) HJ2 Hfr2 HAR2 HC HE HEro Hfd Hfs2 Hmd2 Hmk2
    Hk' Hbb Hwl Hbl Hinc.
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLA) as (HIMG & HREL).
  pose proof Hjbk as (_ & _ & Hfa & _).
  pose proof Hblk as (Hmd3 & Hmk3 & _).
  assert (HinF : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (HX : forall a, E a -> ~ (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/
     lf_slots_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a))
    by exact HE.
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2))).
  { pose proof Hjbk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
    exact (lf_aro_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E HREL HC (fun a Hr He => HEro a He Hr) Hro). }
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  pose proof (lf_la_slack_any HSEGS (rdW W2 (ms_mem ms2))) as Hsl2.
  pose proof Hjbk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hla3 & _).
  pose proof (lf_la_nul_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E HIMG HC
    ltac:(intros HEa; apply (HX _ HEa); right; right; right; right; left; unfold lf_jbk_fp; right; left; lia) Hla3)
    as Hla2.
  split; [|exact HRO2].
  split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr|].
  split; [exact (lf_saved_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC
                   ltac:(intros a Ha HEa; apply (HX a HEa); left; exact Ha) Hsv)|].
  split; [exact (lf_header_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC HinF Hfa
                   ltac:(intros a Ha HEa; apply (HX a HEa); right; left; exact Ha) Hhd)|].
  split; [exact (lf_fshadow_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC HinF Hfa
                   ltac:(intros a Ha HEa; apply (HX a HEa); right; right; left; exact Ha) Hfs)|].
  split; [exact (lf_slots_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp HC
                   ltac:(intros a Ha HEa; apply (HX a HEa); right; right; right; left; exact Ha) Hsl)|].
  split.
  { apply (lf_jbk_restate cx fp k ev mo wl lv ly3 S3 T3 own k' ev' mo' wl' lv' ly2 S2 W2 ms2 md2 own'); try assumption.
    - apply (lf_jbk_callee B MT MS la_nul cx fp k ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E HIMG HREL HC).
      + intros a Ha HEa. apply (HX a HEa). right; right; right; right; left. unfold lf_jbk_fp, lf_jbk_fp_c in *.
        destruct Ha as [Ha | Ha]; [left; exact Ha | right; right; right; exact Ha].
      + exact (fun a Hr He => HEro a He Hr).
      + exact HPB.
      + exact Hfd.
      + exact Hfs2.
      + exact Hla2.
      + exact Hjbk.
    - intros c q. exact (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ2)). }
  split.
  { apply (lf_blocks_restate cx md mk T3 ly3 S3 ly2 S2 _ ltac:(exact (lf_blocks_callee B cx K ly3 S3 ly2 S2 W3
      (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 HC Hmd2 Hmk2 Hblk)) Hmd2 Hmk2). }
  apply (lf_data_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk kbs mbs gbs HIMG HC
    Hmd3 Hmk3 (ak_wcarry_callee ly2 S2 W2 (ms_mem ms2) md2 _ md mk HAR2 Hmd2 Hmk2)).
  - intros a Ha HEa. apply (HX a HEa). right; right; right; right; right; right.
    unfold lf_data_fp_ro, lf_data_fp in *.
    destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]; [tauto | tauto | | tauto | tauto |].
    + right; right; left. lia.
    + right; right; right; right; right. right. unfold LA_ODD, PCAP_RLO, PCAP_RHI in *. lia.
  - exact Hodd2.
  - exact Htx2.
  - exact Hsl2.
  - exact Hdat.
Qed.

(* where the cut's footprint lies: below the allocator's ceiling (with a FILE block's tail past its block's
   request), in the spill slots, or in the machine frame's saved registers. A write set on the real frame above
   the slots therefore misses it. *)
Lemma ak_cut_fp_place : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl,
  MS = link_amf -> la_nul = LA_NUL -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly S)) ->
  AR SEGS B ly S W (ms_mem ms) mdl ->
  ak_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl ->
  forall a, lf_cut_fp MS la_nul cx fp md mk T3 a ->
    a < alloc_ceiling + AMF_BLOCK \/ lf_slots_fp cx a \/ lf_saved_fp cx a.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl HMS HLA HPB HAR
    (_ & Hfr & _ & _ & _ & _ & Hjbk & Hblk & _) a Ha.
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLA) as (HIMG & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & _ & Hinc & _).
  pose proof Hblk as (Hmd & Hmk & _).
  assert (IMG : forall x, lf_img_fp MS la_nul x -> x < kLowMemEnd).
  { intros x Hx. destruct (HIMG x Hx) as (Hi & _). pose proof (pa_segs_low x Hi). lia. }
  assert (BLK : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + Z.max n AMF_BLOCK ->
                  x < alloc_ceiling + AMF_BLOCK).
  { intros p n x Hin Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hc & _ & _ & _ & Hn).
    unfold req_size in Hc. destruct (n =? 0) eqn:E; unfold AMF_BLOCK in *; lia. }
  assert (RO : forall x, in_roP SEGS PCAP_RLO PCAP_RHI x -> x < kLowMemEnd)
    by (intros x Hx; exact (proj2 (in_roP_low x Hx))).
  assert (SH : forall x, 0 <= x < alloc_ceiling -> shadow_of_addr SHADOW_OFF x < alloc_ceiling)
    by (intros x Hx; unfold shadow_of_addr, SHADOW_OFF; lia).
  assert (Hmdb : md + MD_SIZE <= alloc_ceiling /\ 0 <= md).
  { destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmd) as (_ & H4 & Hc & _). unfold req_size, MD_SIZE in *. cbn in Hc. lia. }
  assert (Hmkb : mk + MK_SIZE <= alloc_ceiling /\ 0 <= mk).
  { destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmk) as (_ & H4 & Hc & _). unfold req_size, MK_SIZE in *. cbn in Hc. lia. }
  assert (HF : lf_F cx fp + fs_frame_bytes LF_CID <= alloc_ceiling /\ 4096 <= lf_F cx fp).
  { destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & HS).
    rewrite Forall_forall in HS. pose proof (HS (LF_CID, fp) ltac:(rewrite Hfr; left; reflexivity)) as (H1 & H2).
    cbn [fst snd] in H1, H2. unfold lf_F. rewrite <- (Hfa LF_CID fp). split; [exact H2 | exact H1]. }
  pose proof LF_frame_slot as (FB & _).
  assert (HAMF : AMF_BLOCK = 1304) by reflexivity.
  unfold lf_cut_fp in Ha.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]].
  - right; right; exact Ha.
  - left. unfold lf_header_fp in Ha. rewrite FB in *. destruct Ha as [Ha | Ha]; lia.
  - left. unfold lf_fshadow_fp, lf_SH in Ha. rewrite FB in *. pose proof (SH (lf_F cx fp) ltac:(lia)).
    unfold shadow_of_addr in *. lia.
  - right; left; exact Ha.
  - left. unfold lf_jbk_fp in Ha.
    destruct Ha as [[Ha | [Ha | (f & n & Hin & Hf)]] | [Ha | [Ha | Ha]]].
    + pose proof (IMG a ltac:(unfold lf_img_fp; tauto)). lia.
    + pose proof (IMG a ltac:(unfold lf_img_fp; tauto)). lia.
    + apply (BLK f n a (Hinc _ Hin)). lia.
    + pose proof (IMG a ltac:(unfold lf_img_fp; tauto)). lia.
    + pose proof (RO a Ha). lia.
    + apply (BLK (c_p cx) (c_n cx) a (HPB ltac:(lia))). lia.
  - left. unfold lf_blocks_fp in Ha.
    destruct Ha as [(x & Hx & ->) | (x & Hx & ->)]; pose proof (SH x ltac:(lia)); lia.
  - left. unfold lf_data_fp in Ha.
    destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]];
      try (unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE, LA_LONG_ALIAS, kLowMemEnd in *; lia).
    pose proof (RO a Ha). lia.
Qed.

(* AR fixes the shadow of every live block (YG0d.v AR_shadow_law, block_shadow), so a block live at two AR states
   has the same shadow at both: ashadow_kept holds of any two AR states (a step whose post states only acall_kept,
   e.g. the allocator rules, gives it this way). *)
Lemma ashadow_kept_of_AR : forall ly3 S3 (W3 : world SEGS) mem3 md3 ly2 S2 (W2 : world SEGS) mem2 md2,
  AR SEGS B ly3 S3 W3 mem3 md3 -> AR SEGS B ly2 S2 W2 mem2 md2 ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 mem3 W2 mem2.
Proof.
  intros ly3 S3 W3 mem3 md3 ly2 S2 W2 mem2 md2 HAR3 HAR2 b m a H3 H2 Ha.
  destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 H3) as ((Hb8 & Hn3 & Hs3) & _).
  destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR2 H2) as ((_ & _ & Hs2) & _).
  assert (E : shadow_addr a = shadow_of_addr SHADOW_OFF b + (a - b) / 8).
  { unfold shadow_addr, shadow_of_addr. lia. }
  assert (Hi : 0 <= (a - b) / 8 < (req_size m + 7) / 8).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    pose proof (Z.div_mod (req_size m + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (req_size m + 7) 8 ltac:(lia)). lia. }
  rewrite E, (Hs3 _ Hi), (Hs2 _ Hi). reflexivity.
Qed.

(* two states with the same own list and T3 hold the same live bytes *)
Lemma lf_bl_bytes_eq : forall cx own T3 ly S ly' S',
  lf_bl B cx own T3 ly S -> lf_bl B cx own T3 ly' S' -> blocks_bytes S' = blocks_bytes S.
Proof.
  intros cx own T3 ly S ly' S' H H'.
  destruct (lf_bl_bytes cx own T3 ly S H) as (D & HT & Hb).
  destruct (lf_bl_bytes cx own T3 ly' S' H') as (D' & HT' & Hb').
  rewrite HT in HT'. apply app_inv_head in HT'. subst D'. lia.
Qed.

(* the counters of a cut re-set at the same state *)
Lemma ak_cut_counters : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl ev' mo' wl' lv',
  ak_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl ->
  k <= ev' -> blocks_bytes S <= blocks_bytes (c_S cx) + lv' ->
  (length (wild_part (as_universe B) (st_depot S)) <=
     length (wild_part (as_universe B) (st_depot (c_S cx))) + wl')%nat ->
  ak_cut cx fp md mk kbs mbs gbs T3 own ev' mo' wl' lv' k ly S W ms mdl.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl ev' mo' wl' lv'
    (HJ & Hfr & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat) Hk Hbb Hwl.
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & Hbl & Hinc & _).
  split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hsv|]. split; [exact Hhd|]. split; [exact Hfs|].
  split; [exact Hsl|].
  split; [exact (lf_jbk_restate cx fp k ev mo wl lv ly S T3 own k ev' mo' wl' lv' ly S W ms mdl own Hjbk Hfa Hk Hbb
                   Hwl Hbl Hinc)|].
  split; [exact Hblk | exact Hdat].
Qed.

End a.
