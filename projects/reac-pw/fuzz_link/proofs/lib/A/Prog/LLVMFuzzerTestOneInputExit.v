(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 461 of its 519 lines of code are new or changed and 346 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): THE EXIT of the
   walk, +0x13b0 .. +0x13c0 (0x83b84 .. 0x83b94), against the cut interface lib/A/Prog/LLVMFuzzerTestOneInputDefs.v:

     +0x13b0  ld   a0, 0x90(s1)        the marks block mk
     +0x13b4  jal  wrapper_free        free(mk)                          (return address 0x83b8c)
     +0x13b8  mv   a0, s6              the model m
     +0x13bc  jal  wrapper_free        free(m)                           (return address 0x83b94)
     +0x13c0                           LF_leave: the frame's release (LLVMFuzzerTestOneInputLeave.v)

     lf_frees : forall POST, FROM POST LEAVE -> FROM POST EXIT

   Each free is the raw allocator rule afree04_rule_w (LLVMFuzzerTestOneInputFree.v, lifted by aj_gx_free_w onto the
   walk's journal), applied to a block of the exit's own list; ex_free_step carries the exit's cut to the return
   state with the block out of the own list (Keep.v's per-predicate callee transports, ArmK.v's re-statement).

   Section hypotheses (discharged by the image instance, LLVMFuzzerTestOneInputInst.v / LinkImgInst.v / ACej.v):
     LAWS : AR_laws pa_segs B; TB : PcapSyms B; HSEGS : pa_segs = tfibsegs; LV : LinkVals;
     MT_LE / MT_OK : the trivial meter's laws;
     AFREE4W : afree04_rule_w at every FP state (the raw free rule with the io and depot clauses, open item W1);
     LF_TRACE_FREE : lf_trace_free B (the free sites' traces are in the allocator's universe).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Distinct blocks of one state are apart
   ========================================================================== *)

Lemma ex_zdisj_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. unfold zdisjoint. intros a b H. lia. Qed.

Lemma ex_pw_apart : forall {X} (g : X -> Z * Z) (l : list X) (rest : list (Z * Z)) x y,
  pairwise zdisjoint (map g l ++ rest) -> In x l -> In y l -> x <> y -> zdisjoint (g x) (g y).
Proof.
  intros X g l rest x y. induction l as [|z l IH]; intros HP Hx Hy Hne; [destruct Hx|].
  cbn [map app pairwise] in HP. destruct HP as (HF & HP). rewrite Forall_forall in HF.
  destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
  - exfalso. exact (Hne eq_refl).
  - apply HF. apply in_or_app. left. apply in_map. exact Hy.
  - apply ex_zdisj_sym. apply HF. apply in_or_app. left. apply in_map. exact Hx.
  - exact (IH HP Hx Hy Hne).
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
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.

#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

Lemma ex_blk_apart : forall ly S (W : world SEGS) mem md b c,
  AR SEGS B ly S W mem md -> In b (ablocks B ly S) -> In c (ablocks B ly S) -> b <> c ->
  zdisjoint (fst b, req_size (snd b)) (fst c, req_size (snd c)).
Proof.
  intros ly S W mem md b c HAR Hb Hc Hne. destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (HP & _).
  exact (ex_pw_apart (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ _ b c HP Hb Hc Hne).
Qed.

(* the exit's own blocks: in the state's list, not the caller's, not a FILE block, addressable *)
Definition ex_own (cx : lcx) (T3 own : list (Z * Z)) (ly : alayout) (S : astate) (m : word -> option byte) : Prop :=
  List.NoDup own /\ forall c, In c own ->
    In c (ablocks B ly S) /\ ~ In c (ablocks B (c_ly cx) (c_S cx)) /\ ~ In c T3 /\
    range_addressable (ard SEGS m) SHADOW_OFF (fst c) (snd c).

(* the exit's cut, but for the registers *)
Definition ex_cut (cx : lcx) (fp k ev mo : Z) (wl : nat) (lv : Z) (ly : alayout) (S : astate) (W : world SEGS)
    (ms : machine_state) (mdl : Model) (T3 own : list (Z * Z)) : Prop :=
  JRN cx fp ly S W (ms_mem ms) mdl k /\ frames S = [(LF_CID, fp)] /\
  lf_saved cx W ms /\ lf_header cx fp W ms /\ lf_fshadow cx fp W ms LF_SH0 /\
  lf_slot cx W ms LS_F (lf_F cx fp) /\ lf_slot cx W ms LS_FK (lf_F cx fp) /\
  lf_jbk B MT MS la_nul cx fp k ev mo wl lv ly S W ms mdl T3 own /\
  ex_own cx T3 own ly S (rdW W (ms_mem ms)).

(* a stretch of the walk that writes nothing and only materialises the model *)
Lemma ex_cut_run : forall cx fp k ev mo wl lv ly S W ms ms' mdl mdl' T3 own,
  ex_cut cx fp k ev mo wl lv ly S W ms mdl T3 own ->
  JRN cx fp ly S W (ms_mem ms') mdl' k ->
  kagree SEGS (fun _ => False) (rdW W (ms_mem ms)) (rdW W (ms_mem ms')) ->
  m_fds mdl' = m_fds mdl -> m_fs mdl' = m_fs mdl ->
  ex_cut cx fp k ev mo wl lv ly S W ms' mdl' T3 own.
Proof.
  intros cx fp k ev mo wl lv ly S W ms ms' mdl mdl' T3 own
    (HJ & Hfr & Hsv & Hhd & Hfs & HF & HFK & Hjbk & (Hnd & Hown)) HJ' HK Hfd Hfs'.
  split; [exact HJ'|]. split; [exact Hfr|].
  split; [exact (lf_saved_keep _ cx W ms W ms' HK (fun a _ H => H) Hsv)|].
  split; [exact (lf_header_keep _ cx fp W ms W ms' HK (fun a _ H => H) Hhd)|].
  split; [exact (lf_fshadow_keep _ cx fp W ms W ms' LF_SH0 HK (fun a _ H => H) Hfs)|].
  split; [exact (lf_slot_keep _ cx W ms W ms' LS_F _ HK (fun i _ H => H) HF)|].
  split; [exact (lf_slot_keep _ cx W ms W ms' LS_FK _ HK (fun i _ H => H) HFK)|].
  split; [exact (lf_jbk_keep B MT MS la_nul _ cx fp k ev mo wl lv ly S W ms mdl T3 own W ms' mdl' HK Hfd Hfs'
                   (fun a _ H => H) Hjbk)|].
  split; [exact Hnd|]. intros c Hc. destruct (Hown c Hc) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  exact (ra_keep SEGS _ _ _ SHADOW_OFF (fst c) (snd c) HK (fun x _ H => H) H4).
Qed.

(* ==========================================================================
   2. A free of one of the exit's own blocks
   ========================================================================== *)

Lemma ex_free_step : forall (fy : YK11.FPState) cx fp T3 o1 pa n o2 ev mo wl lv k ly3 S3 W3
    (ms3 : machine_state) md3 (regs : bvmap 5 word) rao mo' (Q : world SEGS -> config -> Prop),
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ex_cut cx fp k ev mo wl lv ly3 S3 W3 ms3 md3 T3 (o1 ++ (pa, n) :: o2) ->
  k + 1 <= EV_LIB ->
  getr regs 10 = w64 pa -> spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (link_text + rao) -> In (link_text + rao) LF_FREE_RAS ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
     aregs_preserved regs regs2 ->
     ex_cut cx fp (k + 1) (ev + 1) mo' wl lv ly2 S2 W2 (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2
       T3 (o1 ++ o2) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (@mkst fy regs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_free)) (ms_mem ms3)
    (seg_rom SEGS)) md3) Q.
Proof.
  intros fy cx fp T3 o1 pa n o2 ev mo wl lv k ly3 S3 W3 ms3 md3 regs rao mo' Q
    HB (HJ & Hfr & Hsv & Hhd & Hfs & HF & HFK & Hjbk & (Hnd & Hown)) Hk R10 Hsp Hs0 R3 R4 R1 Hsite K.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & HLAN & HMSE & _).
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
  pose proof HAFN as (_ & _ & _ & HGP & HTP & _).
  pose proof Hjbk as (Hkev & Hbb & Hfa & _ & Hfd & Hfs3 & _ & Hwl & Hgi & _ & Hbl & Hinc & Hla3 & Hro3 & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMSE HLAN) as (HIMG & HREL).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & R32 & _). unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  unfold LLVMF_STK in *.
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  pose proof HPRE as (_ & _ & _ & _ & Hpin0 & _).
  assert (Hpin : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))
    by (intros Hc; destruct Hpin0 as [(Hz & _) | (_ & Hi)]; [lia | exact Hi]).
  destruct (lf_saved_ra_s0 cx W3 ms3 Hsv) as (H8 & H16w).
  assert (Hra : raZ regs = link_text + rao)
    by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- (lv_text LV). apply ret_ok_codeptr_v.
    - unfold LF_FREE_RAS, link_text in *. cbn in Hsite. lia.
    - unfold LF_FREE_RAS, link_text in Hsite. cbn in Hsite.
      destruct Hsite as [E | [E | [E | [E | [E | [E | [E | []]]]]]]];
        (assert (rao = 0x82e70 - 0x821cc \/ rao = 0x82e78 - 0x821cc \/ rao = 0x83758 - 0x821cc \/
                 rao = 0x83760 - 0x821cc \/ rao = 0x838dc - 0x821cc \/ rao = 0x83b8c - 0x821cc \/
                 rao = 0x83b94 - 0x821cc) as Er by lia);
        destruct Er as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; reflexivity. }
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k regs HB HJ H8 H16w ltac:(lia) Hs0 Hra4) as (HCH & _).
  pose proof (lf_free_trace SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx regs HB
    LF_TRACE_FREE ltac:(rewrite Hra; exact Hsite)) as HTR.
  assert (Hpn : In (pa, n) (o1 ++ (pa, n) :: o2)) by (apply in_or_app; right; left; reflexivity).
  destruct (Hown (pa, n) Hpn) as (Hb & Hnb & HnT & _).
  replace (pa_sigma LS___interceptor_trampoline_free) with (pc_wrap_free (as_code B))
    by (rewrite (lv_sigma LV), (ts_code B TB); reflexivity).
  eapply SRr_bind.
  { apply (@aj_gx_free_w fy rc SK SEGS B MT LAWS pa_segs_low (AFREE4W fy) G_HARNESS 0 [] W3 regs (ms_mem ms3)
      LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(LF_CID, fp)] ly3 S3 md3 k pa n (getr regs 1) (lf_chain cx) HJ Hb R10).
    - rewrite Hsp. pose proof (Z.div_mod (lf_sp1 cx) 32 ltac:(lia)) as D. rewrite Hs32 in D. rewrite D.
      replace (32 * (lf_sp1 cx / 32) + 0) with ((lf_sp1 cx / 32 * 2) * 16) by lia. apply Z.mod_mul. lia.
    - rewrite Hsp. unfold LLVMF_STK, ASTACK. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp. lia.
    - rewrite R3. exact HGP.
    - rewrite R4. exact HTP.
    - reflexivity.
    - exact Hret.
    - unfold EV_LIB in *. lia.
    - exact HCH.
    - exact HTR.
    - intros Hin. contradiction.
    - apply MT_OK. }
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & (l1 & l2 & Hl1 & Hl2) & Hfr2 & HK & _ & HW & Hio).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    mem2 md2 (k + 1) HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  destruct (same_io_fds_fs md3 md2 Hio) as (Hfd2 & Hfs2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb) as (_ & Hp4 & Hpc & Happ & _ & _ & Hn).
  assert (Hr1 : 1 <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:E; [lia | apply Z.eqb_neq in E; lia]).
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> c <> (pa, n) -> In c (ablocks B ly2 S2)).
  { intros c Hc Hne. rewrite Hl2. rewrite Hl1 in Hc.
    apply in_app_iff in Hc as [Hc | [Hc | Hc]]; apply in_app_iff; [left; exact Hc | congruence | right; exact Hc]. }
  set (E := fun a => pa <= a < pa + req_size n).
  assert (HKP : akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (lf_sp1 cx - ASTACK) (lf_sp1 cx) E).
  { rewrite <- Hsp. apply (akept_of_acall_kept SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK). intros a Ha; exact Ha. }
  assert (HCALL : lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 E).
  { split; [unfold ASTACK; lia|]. split; [unfold ASTACK; lia|]. split; [exact HKP|].
    exact (ashadow_kept_of_AR B LAWS ly3 S3 W3 (ms_mem ms3) md3 ly2 S2 W2 mem2 md2 HAR3 HAR2). }
  set (ms2 := @mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)).
  assert (HinF : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  (* the freed block's bytes are heap bytes: not the stack, the frame, the shadow, the image, another block *)
  assert (NI : forall a, E a -> ~ in_img SEGS a).
  { intros a Ha. destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR3 ltac:(left; exists pa, n; split; [exact Hb | exact Ha]))
      as (_ & Hni). exact Hni. }
  assert (NB : forall c a, In c (ablocks B ly3 S3) -> c <> (pa, n) -> E a -> ~ (fst c <= a < fst c + req_size (snd c))).
  { intros c a Hc Hne Ha Hca. pose proof (ex_blk_apart ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hb Hc (fun e => Hne (eq_sym e))) as D.
    unfold zdisjoint, E in *. cbn [fst snd] in D. lia. }
  assert (NF : forall a, E a -> ~ (lf_F cx fp <= a < lf_F cx fp + 1024)).
  { intros a Ha Hfa'. pose proof LF_frame_slot as (FB & _). destruct (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (HPw & _).
    pose proof (pairwise_In zdisjoint _ (pa, req_size n) (frame_addr ly3 LF_CID fp, fs_frame_bytes LF_CID) _ _ eq_refl HPw
      ltac:(apply in_map_iff; exists (pa, n); split; [reflexivity | exact Hb])
      ltac:(apply in_map_iff; exists (LF_CID, fp); split; [reflexivity | exact HinF])) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. unfold lf_F in Hfa'. rewrite <- (Hfa LF_CID fp) in Hfa'.
    rewrite FB in *. unfold E in Ha. lia. }
  assert (NS : forall a, E a -> ~ (lf_SH cx fp <= a < lf_SH cx fp + 128)).
  { intros a Ha Hsa. destruct (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (_ & HSf). rewrite Forall_forall in HSf.
    pose proof (HSf (LF_CID, fp) HinF) as (F1 & F2). cbn [fst snd] in F1, F2.
    pose proof LF_frame_slot as (FB & _).
    assert (Fc : frame_addr ly3 LF_CID fp <= alloc_ceiling) by (rewrite FB in F2; lia).
    unfold lf_SH, lf_F, shadow_of_addr, SHADOW_OFF in Hsa. rewrite <- (Hfa LF_CID fp) in Hsa.
    pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Fc) as Fd.
    unfold E in Ha. lia. }
  assert (NSTK : forall a, E a -> ~ (lf_sp1 cx <= a < spZ (c_regs cx))) by (intros a Ha Hs; unfold E in Ha; lia).
  (* the cut at the return state *)
  assert (Hsv2 : lf_saved cx W2 (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS))).
  { exact (lf_saved_callee B cx ASTACK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HCALL
      ltac:(intros a Ha HEa; unfold lf_saved_fp in Ha; pose proof (lf_sp1_le cx); apply (NSTK a HEa);
            unfold LF_MFRAME in *; lia) Hsv). }
  assert (Hhd2 : lf_header cx fp W2 (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS))).
  { exact (lf_header_callee B cx fp ASTACK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HCALL HinF Hfa
      ltac:(intros a Ha HEa; pose proof LF_frame_slot as (FB & _); unfold lf_header_fp in Ha; rewrite FB in Ha;
            apply (NF a HEa); lia) Hhd). }
  assert (Hfs2' : lf_fshadow cx fp W2 (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) LF_SH0).
  { exact (lf_fshadow_callee B cx fp ASTACK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HCALL HinF Hfa
      ltac:(intros a Ha HEa; unfold lf_fshadow_fp in Ha; apply (NS a HEa); lia) Hfs). }
  pose proof (lf_call_kagree B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 E HCALL) as HKG.
  assert (SL : forall off v, 0 <= off -> off + 8 <= LF_MFRAME -> lf_slot cx W3 ms3 off v ->
            lf_slot cx W2 (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) off v).
  { intros off v Ho1 Ho2 Hs. apply (lf_slot_keep _ cx W3 ms3 W2 ms2 off v HKG); [|exact Hs].
    intros i Hi. pose proof (lf_sp1_le cx) as (P1 & P2).
    apply (lfx_above B cx ASTACK ly3 S3 ly2 S2 E); [unfold ASTACK; lia | unfold ASTACK; lia | lia |].
    intros HEa. apply (NSTK _ HEa). lia. }
  assert (HnE : ~ E la_nul)
    by (intros HEa; apply (NI la_nul HEa);
        exact (proj1 (HIMG la_nul ltac:(unfold lf_img_fp; right; right; right; right; right; left; lia)))).
  assert (Hla2 : val_mem SEGS (rdW W2 mem2) la_nul 1 0)
    by exact (lf_la_nul_callee B MS la_nul cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 E HIMG HCALL HnE Hla3).
  assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp (k + 1) (ev + 1) mo' wl lv ly2 S2 W2
                    (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 T3 (o1 ++ o2)).
  { eapply lf_jbk_restate; [exact MT_LE | | | | | | | ].
    - apply (lf_jbk_callee B MT MS la_nul cx fp k ev mo wl lv ly3 S3 W3 ms3 md3 T3 _ ASTACK ly2 S2 W2 ms2 md2 E
        HIMG HREL HCALL); [| | exact HPB | rewrite Hfd2; reflexivity | rewrite Hfs2; reflexivity | exact Hla2 | exact Hjbk].
      + intros a Ha HEa. unfold lf_jbk_fp_c, amf_fp in Ha.
        destruct Ha as [[Ha | [Ha | (f & m & Hf & Ha)]] | Ha].
        * apply (NI a HEa). exact (proj1 (HIMG a ltac:(unfold lf_img_fp; tauto))).
        * apply (NI a HEa). exact (proj1 (HIMG a ltac:(unfold lf_img_fp; tauto))).
        * destruct (amf_gi_shape SEGS MS T3 _ Hgi) as [Et | (f' & Et)]; rewrite Et in Hf; [destruct Hf|].
          destruct Hf as [Hf | []]. injection Hf as E1 E2. subst f' m.
          assert (HfT : In (f, AMF_BLOCK) T3) by (rewrite Et; left; reflexivity).
          apply (NB (f, AMF_BLOCK) a (Hinc _ HfT) ltac:(intros Heq; apply HnT; rewrite <- Heq; exact HfT) HEa).
          cbn [fst snd]. unfold req_size, AMF_BLOCK in *. cbn. lia.
        * assert (Hcn : 0 < c_n cx) by lia.
          apply (NB (c_p cx, c_n cx) a (HPB Hcn) ltac:(intros Heq; apply Hnb; rewrite <- Heq; exact (Hpin Hcn)) HEa).
          cbn [fst snd]. unfold req_size. destruct (c_n cx =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia | lia].
      + intros a Hro HEa. apply (NI a HEa).
        destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HREL a Hr)].
    - intros c q. exact (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ2)).
    - lia.
    - rewrite (blocks_bytes_bsum B ly2 S2), Hl2. rewrite (blocks_bytes_bsum B ly3 S3), Hl1 in Hbb.
      rewrite bsum_app in *. rewrite bsum_cons in Hbb. cbn [snd] in Hbb. lia.
    - lia.
    - exact (lf_bl_remove B cx o1 o2 T3 ly3 S3 ly2 S2 (pa, n) l1 l2 Hbl Hl1 Hl2).
    - intros c Hc. apply (Hsub c (Hinc c Hc)). intros Heq. apply HnT. rewrite <- Heq. exact Hc. }
  apply (K W2 ly2 S2 regs2 mem2 md2 HP).
  split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr|].
  split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|].
  split; [apply SL; [unfold LS_F, LF_MFRAME; lia | unfold LS_F, LF_MFRAME; lia | exact HF]|].
  split; [apply SL; [unfold LS_FK, LF_MFRAME; lia | unfold LS_FK, LF_MFRAME; lia | exact HFK]|].
  split; [exact Hjbk2|].
  split; [exact (NoDup_remove_1 o1 o2 (pa, n) Hnd)|].
  intros c Hc. assert (Hc' : In c (o1 ++ (pa, n) :: o2)).
  { apply in_app_iff in Hc as [Hc | Hc]; apply in_app_iff; [left; exact Hc | right; right; exact Hc]. }
  assert (Hne : c <> (pa, n)) by (intros ->; exact (NoDup_remove_2 o1 o2 (pa, n) Hnd Hc)).
  destruct (Hown c Hc') as (H1 & H2 & H3 & H4).
  split; [exact (Hsub c H1 Hne)|]. split; [exact H2|]. split; [exact H3|].
  destruct c as [cp cn]. cbn [fst snd] in *.
  apply (ra_keep SEGS _ _ _ SHADOW_OFF cp cn HKG); [|exact H4].
  intros x Hx. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
  apply (lfx_sh B ly3 S3 ly2 S2 _ _ E cp cn x H1 (Hsub _ H1 Hne)).
  unfold req_size. destruct (cn =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.
(* ==========================================================================
   3. The two frees: +0x13b0 .. +0x13c0
   ========================================================================== *)

(* a register a run left as its entry atom, at an absolute end state *)
Lemma ex_reg_abs : forall (fy : YK11.FPState) (W : world SEGS) E ss ms regs0 (r : bv 5),
  st_ok (fx := fy) SEGS E ss (restrict (w_H W) ms) -> env_agree 32 (Ereg regs0 []) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fy W E ss ms regs0 r HS HA Hr.
  rewrite (st_ok_restrict_reg SEGS (w_H W) E ss ms r HS), Hr.
  pose proof (bv_unsigned_in_range 5 r) as Rr. change (bv_modulus 5) with 32 in Rr.
  cbn [sv_denot]. destruct HA as [HA _]. rewrite (HA (Z.to_nat (bv_unsigned r))) by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Ereg_nat. lia.
Qed.

Lemma ex_env_agree : forall regs0 extra, env_agree 32 (Ereg regs0 []) (Eimg (Ereg regs0 extra)).
Proof.
  intros regs0 extra. split; [|reflexivity]. intros n Hn.
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite !ew_Ereg_lt by lia. reflexivity.
Qed.

Lemma ex_s0 : forall cx (regs : bvmap 5 word), getr regs 8 = w64 (spZ (c_regs cx)) -> s0Z regs = spZ (c_regs cx).
Proof.
  intros cx regs H. unfold s0Z. rewrite H. unfold w64, spZ.
  rewrite unsigned_lit_small; [reflexivity|]. apply bv_unsigned_in_range.
Qed.

Lemma ex_sp : forall cx (regs : bvmap 5 word), 0 <= lf_sp1 cx ->
  getr regs 2 = w64 (lf_sp1 cx) -> spZ regs = lf_sp1 cx.
Proof.
  intros cx regs H0 H. unfold spZ. rewrite H. unfold w64. apply unsigned_lit_small.
  pose proof (lf_sp1_le cx) as (P1 & P2). unfold LF_MFRAME in P1. lia.
Qed.

Lemma ex_pres : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 19 = getr regs 19 /\
  getr regs' 22 = getr regs 22.
Proof.
  intros regs regs' H. unfold aregs_preserved, acallee_saved in H.
  refine (conj (H 2 ltac:(lia)) (conj (H 3 ltac:(lia)) (conj (H 4 ltac:(lia)) (conj (H 8 ltac:(lia))
    (conj (H 9 ltac:(lia)) (conj (H 19 ltac:(lia)) (H 22 ltac:(lia)))))))).
Qed.

(* the plain call run (LinkWalkSide.v paj_run_call_plain_x), as reac_link_alias_writeExit.v aw_run_call *)
Ltac ex_run_call RUNC HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNC with
    | forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
      lazymatch r with
      | (?ss', PRS_call ?s) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
        eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
        [ clear Hrun | clear Hrun ]
      | ?other => fail "ex_run_call: the run does not stop at a call:" other
      end
    end
  end.

Lemma ex_sp1 : forall cx, spZ (c_regs cx) - LF_MFRAME - 32 < lf_sp1 cx.
Proof.
  intros cx. unfold lf_sp1, lf_sp1_of. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - LF_MFRAME) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ (c_regs cx) - LF_MFRAME) 32 ltac:(lia)) as D. lia.
Qed.

(* a slot of the spill region as a chunk *)
Lemma ex_chunk : forall cx (W3 : world SEGS) ms3 E off e v,
  lf_slot cx W3 ms3 off v -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) (lf_sp1 cx) (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros cx W3 ms3 E off e v Hs He. unfold lf_slot, lf_at in Hs.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) Hs) as Hv.
  apply (chunk_ok_val SEGS E _ (lf_sp1 cx) off 8 e v He); [cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ v Hs).
Qed.

Definition ex_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_MK (LS_MK + 8) LS_MK LS_MK [YP09.mkChunk LS_MK (CVal 8 (SOff 32 0))].
Definition ex_ss0 : sstate := mkSS LF_exit sr_atoms [ex_spill] None (mkFacts [] [] []).
Definition ex_ss1 : sstate := mkSS (LF_exit + 8) sr_atoms [] None (mkFacts [] [] []).

Lemma lf_frees : forall POST,
  lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST
    (lf_leave_inv B MT MS la_nul LF_MO_SET LF_MO_OP LF_MO_END) ->
  lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST
    (lf_exit_inv B MT MS la_nul LF_MO_SET LF_MO_OP).
Proof.
  intros POST HLV cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HX.
  destruct HX as (md & mk & T3 & Hsh & Hcore & R19 & R22 & Hsv & Hhd & Hfs & HMK & HF & HFK & Hjbk & Hmd & Hmk
    & Hnmd & Hnmk & HTmd & HTmk & Hne & RAmd & RAmk).
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof HB as (_ & _ & HGX & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ML & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & _ & _ & _ & Hpres & HAR).
  pose proof (lf_sp1_le cx) as (P1 & P2). pose proof (ex_sp1 cx) as P3.
  assert (S1r : alloc_ceiling <= lf_sp1 cx) by (unfold LLVMF_STK, LF_MFRAME in *; lia).
  assert (S1u : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx).
  { rewrite C9. unfold w64. apply unsigned_lit_small. unfold LF_MFRAME in *. lia. }
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HMK) as RMK.
  assert (HC0 : ex_cut cx fp k2 (lf_ev 48) (lf_mo LF_MO_SET LF_MO_OP 48) (lf_wl 48) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
                  [(md, MD_SIZE); (mk, MK_SIZE)]).
  { split; [exact HJ|]. split; [exact Hfr|]. do 5 (split; [assumption|]). split; [exact Hjbk|]. split.
    - constructor; [intros [E | []]; injection E as E1 _; exact (Hne (eq_sym E1)) | constructor; [intros [] | constructor]].
    - intros c [<- | [<- | []]]; cbn [fst snd]; repeat split; assumption. }
  rewrite (lf_shape_eta fy LF_exit ms3 Hsh).
  set (E := Eimg (Ereg (ms_regs ms3) [w64 mk])).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 mk) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  pose proof (ex_env_agree (ms_regs ms3) [w64 mk]) as HA. fold E in HA.
  assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E ex_ss0
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_exit)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor; [|constructor].
      unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks ex_spill base_val]. rewrite E9, S1u.
      unfold LS_MK, LF_MFRAME in *.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (ex_chunk cx W3 ms3 E LS_MK (SOff 32 0) mk HMK). rewrite (lf_sv_off E 32 mk 0 E32) by lia.
      rewrite Z.add_0_r. reflexivity.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  pose proof (@paj_run_call_plain_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNC.
  clearbody E.
  (* +0x13b0 .. +0x13b4: a0 := mk, the call of free *)
  ex_run_call RUNC HS HJ.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil]. cbn [r_base r_wlo r_whi ex_spill base_val]. intros a Ha. lia. }
  intros ms1 mat1 HS1 HJ1 HF1 HFr1 HG1.
  prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (1%bv : bv 5) Q1.
  pmkst HS1.
  lazymatch type of HS1 with st_ok _ _ ?ssx _ =>
    assert (KR1 : forall r : bv 5, sr_get (ss_regs ssx) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
                   getr (ms_regs ms1) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (ex_reg_abs fy W3 E ssx ms1 _ r HS1 HA Hr))
  end.
  assert (G2 : getr (ms_regs ms1) 2 = getr (ms_regs ms3) 2) by (apply KR1; vm_compute; reflexivity).
  assert (G3 : getr (ms_regs ms1) 3 = getr (ms_regs ms3) 3) by (apply KR1; vm_compute; reflexivity).
  assert (G4 : getr (ms_regs ms1) 4 = getr (ms_regs ms3) 4) by (apply KR1; vm_compute; reflexivity).
  assert (G8 : getr (ms_regs ms1) 8 = getr (ms_regs ms3) 8) by (apply KR1; vm_compute; reflexivity).
  assert (G9 : getr (ms_regs ms1) 9 = getr (ms_regs ms3) 9) by (apply KR1; vm_compute; reflexivity).
  assert (G19 : getr (ms_regs ms1) 19 = getr (ms_regs ms3) 19) by (apply KR1; vm_compute; reflexivity).
  assert (G22 : getr (ms_regs ms1) 22 = getr (ms_regs ms3) 22) by (apply KR1; vm_compute; reflexivity).
  assert (K1 : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms1))).
  { apply (lf_frame_kagree E _ _ _ (fun _ => False) HFr1).
    intros a _ (r & Hi & Hr). cbn [ex_ss0 ss_mem In] in Hi. destruct Hi as [<- | []].
    cbn [r_base r_wlo r_whi ex_spill base_val] in Hr. lia. }
  pose proof (ex_cut_run cx fp k2 _ _ _ _ ly3 S3 W3 ms3 ms1 md3 _ T3 _ HC0 HJ1 K1
    ltac:(rewrite lf_wvb_fds; reflexivity) ltac:(rewrite lf_wvb_fs; reflexivity)) as HC1.
  pose proof Hjbk as (Hk & _).
  (* free(mk), returning to +0x13b8 *)
  eapply (ex_free_step fy cx fp T3 [(md, MD_SIZE)] mk MK_SIZE [] _ _ _ _ k2 ly3 S3 W3 ms1 _ (ms_regs ms1)
    (0x83b8c - 0x821cc) (lf_mo LF_MO_SET LF_MO_OP 48) (POST cx) HB HC1).
  { unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia. }
  { rewrite Q10, E32. reflexivity. }
  { apply ex_sp; [lia|]. rewrite G2. exact C2. }
  { apply (ex_s0 cx). rewrite G8. exact C8. }
  { rewrite G3. exact C3. }
  { rewrite G4. exact C4. }
  { rewrite Q1, (lv_text LV). try (f_equal; unfold link_text; lia). }
  { unfold LF_FREE_RAS, link_text. cbn [In]. lia. }
  intros W2 ly2 S2 regs2 mem2 md2 HP2 HC2.
  destruct (ex_pres _ _ HP2) as (P2_2 & P2_3 & P2_4 & P2_8 & P2_9 & P2_19 & P2_22).
  assert (EQ2 : @mkst fy regs2 (getr (ms_regs ms1) 1) mem2 (seg_rom SEGS) =
                @mkst fy regs2 (Z_to_bv 64 (BASE + (LF_exit + 8))) mem2 (seg_rom SEGS))
    by (rewrite Q1; try (f_equal; f_equal; unfold LF_exit, AF_LLVMFuzzerTestOneInput; lia)).
  rewrite EQ2 in HC2 |- *.
  (* +0x13b8 .. +0x13bc: a0 := s6 = m, the call of free *)
  set (E2 := Eimg (Ereg regs2 [])).
  assert (HEI2 : img_env pa_val A_LIM E2) by apply Eimg_env.
  assert (E2_22 : ew E2 22 = getr regs2 22) by (apply ew_Eimg_Ereg_nat; reflexivity).
  pose proof (ex_env_agree regs2 []) as HA2. fold E2 in HA2.
  assert (HS2 : st_ok_pi (fx := fy) pa_segs pa_val E2 ex_ss1
    (restrict (w_H W2) (@mkst fy regs2 (Z_to_bv 64 (BASE + (LF_exit + 8))) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  clearbody E2.
  pose proof HC2 as (HJ2 & _).
  ex_run_call RUNC HS2 HJ2.
  { apply awr_ok_x_nil. }
  intros ms4 mat4 HS4 HJ4 HF4 HFr4 HG4.
  prreg HS4 (10%bv : bv 5) Q10b. prreg HS4 (1%bv : bv 5) Q1b.
  pmkst HS4.
  lazymatch type of HS4 with st_ok _ _ ?ssx _ =>
    assert (KR2 : forall r : bv 5, sr_get (ss_regs ssx) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
                   getr (ms_regs ms4) r = getr regs2 r)
      by (intros r Hr; exact (ex_reg_abs fy W2 E2 ssx ms4 _ r HS4 HA2 Hr))
  end.
  assert (H2_2 : getr (ms_regs ms4) 2 = getr regs2 2) by (apply KR2; vm_compute; reflexivity).
  assert (H2_3 : getr (ms_regs ms4) 3 = getr regs2 3) by (apply KR2; vm_compute; reflexivity).
  assert (H2_4 : getr (ms_regs ms4) 4 = getr regs2 4) by (apply KR2; vm_compute; reflexivity).
  assert (H2_8 : getr (ms_regs ms4) 8 = getr regs2 8) by (apply KR2; vm_compute; reflexivity).
  assert (H2_9 : getr (ms_regs ms4) 9 = getr regs2 9) by (apply KR2; vm_compute; reflexivity).
  assert (H2_19 : getr (ms_regs ms4) 19 = getr regs2 19) by (apply KR2; vm_compute; reflexivity).
  pose proof (ex_cut_run cx fp _ _ _ _ _ ly2 S2 W2 _ ms4 md2 _ T3 _ HC2 HJ4 (kagree_frame_nil E2 _ _ HFr4)
    ltac:(rewrite lf_wvb_fds; reflexivity) ltac:(rewrite lf_wvb_fs; reflexivity)) as HC3.
  (* free(m), returning to +0x13c0 = LF_leave *)
  eapply (ex_free_step fy cx fp T3 [] md MD_SIZE [] _ _ _ _ (k2 + 1) ly2 S2 W2 ms4 _ (ms_regs ms4)
    (0x83b94 - 0x821cc) (lf_mo LF_MO_SET LF_MO_OP 48 + LF_MO_END) (POST cx) HB HC3).
  { unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia. }
  { rewrite Q10b, E2_22, P2_22, G22. exact R22. }
  { apply ex_sp; [lia|]. rewrite H2_2, P2_2, G2. exact C2. }
  { apply (ex_s0 cx). rewrite H2_8, P2_8, G8. exact C8. }
  { rewrite H2_3, P2_3, G3. exact C3. }
  { rewrite H2_4, P2_4, G4. exact C4. }
  { rewrite Q1b, (lv_text LV). try (f_equal; unfold link_text; lia). }
  { unfold LF_FREE_RAS, link_text. cbn [In]. lia. }
  intros W5 ly5 S5 regs5 mem5 md5 HP5 HC5.
  destruct (ex_pres _ _ HP5) as (P5_2 & P5_3 & P5_4 & P5_8 & P5_9 & P5_19 & P5_22).
  assert (EQ5 : @mkst fy regs5 (getr (ms_regs ms4) 1) mem5 (seg_rom SEGS) =
                @mkst fy regs5 (Z_to_bv 64 (BASE + LF_leave)) mem5 (seg_rom SEGS))
    by (rewrite Q1b; try (f_equal; f_equal; unfold LF_leave, AF_LLVMFuzzerTestOneInput; lia)).
  rewrite EQ5 in HC5 |- *.
  destruct HC5 as (HJ5 & Hfr5 & Hsv5 & Hhd5 & Hfs5 & HF5 & HFK5 & Hjbk5 & _).
  apply (HLV cx fy fp (k2 + 1 + 1) ly5 S5 W5 _ md5 HB Hfx HJ5 Hfr5).
  assert (RG2 : getr regs5 2 = getr (ms_regs ms3) 2) by (rewrite P5_2, H2_2, P2_2, G2; reflexivity).
  assert (RG3 : getr regs5 3 = getr (ms_regs ms3) 3) by (rewrite P5_3, H2_3, P2_3, G3; reflexivity).
  assert (RG4 : getr regs5 4 = getr (ms_regs ms3) 4) by (rewrite P5_4, H2_4, P2_4, G4; reflexivity).
  assert (RG8 : getr regs5 8 = getr (ms_regs ms3) 8) by (rewrite P5_8, H2_8, P2_8, G8; reflexivity).
  assert (RG9 : getr regs5 9 = getr (ms_regs ms3) 9) by (rewrite P5_9, H2_9, P2_9, G9; reflexivity).
  assert (RG19 : getr regs5 19 = getr (ms_regs ms3) 19) by (rewrite P5_19, H2_19, P2_19, G19; reflexivity).
  exists T3.
  split; [unfold lf_shape; repeat split; reflexivity|].
  split; [exact (conj (eq_trans RG2 C2) (conj (eq_trans RG8 C8) (conj (eq_trans RG9 C9)
                   (conj (eq_trans RG3 C3) (eq_trans RG4 C4)))))|].
  split; [exact (eq_trans RG19 R19)|].
  split; [exact Hsv5|]. split; [exact Hhd5|]. split; [exact Hfs5|]. split; [exact HF5|]. split; [exact HFK5|].
  refine (lf_jbk_mono B MT MS la_nul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ML _ _ _ _ Hjbk5);
    [unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB; lia | lia | lia | lia].
Qed.

End a.
