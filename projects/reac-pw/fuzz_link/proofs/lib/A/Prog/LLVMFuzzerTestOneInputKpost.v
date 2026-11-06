(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 263 of its 313 lines of code are new or changed and 354 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): the cut AFTER
   kernel(&cursor), at each of the four kernel call sites of the operation loop (0x82ec0 op_unmark, 0x832a4
   op_mark, 0x83584 op_read, 0x837e4 op_write), shared by the arm lanes.

   `lf_kernel_post`: kernel_c.v's kernel_apost and its apost (akept with kernel's write set g_nl [0, NK_OPEN),
   long_alias [0, 301) and the cursor, ashadow_kept, S2 = set_fs _ S3, the block list a permutation), from the
   cut's pieces at the call, give the same pieces at the return: the stack, the frame, the slots and the blocks
   kept (Keep.v's *_callee lemmas), the cursor advanced by kernel's count, the journal clauses with the NUL of
   long_alias from kernel's post, and lf_data at kernel's new g_nl bytes (the model, the marks, the table
   pointers, g_names kept; the odd and texts tables from the read-only image; long_alias from the post).

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
  LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
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

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* kernel's write set, by range *)
Lemma kp_kernel_E : forall cx (regs : bvmap 5 word) m a, aarg regs 0 = lf_sp1 cx + LS_P ->
  inFP (kernel_awr regs m) a ->
  (LA_G_NL <= a < LA_G_NL + NK_OPEN) \/ (LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301) \/
  (lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_P + 16).
Proof.
  intros cx regs m a Ha0 (r & Hin & Hr). unfold kernel_awr in Hin. rewrite Ha0 in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
  - left. unfold NK_CHUNK in Hr. lia.
  - right; left. unfold LONG_ALIAS_SIZE in Hr. lia.
  - right; right. lia.
Qed.

Lemma kp_au8arr_prefix : forall (m : word -> option byte) a l1 l2, au8arr SEGS m a (l1 ++ l2) -> au8arr SEGS m a l1.
Proof.
  intros m a l1 l2 ((H0 & H1 & Hb) & Hw). rewrite length_app in H1, Hw. split; [split; [exact H0|]; split; [lia|]|].
  - intros i Hi. rewrite (Hb i ltac:(rewrite length_app; lia)). rewrite nth_error_app1 by exact Hi. reflexivity.
  - intros i Hi. apply Hw. lia.
Qed.

(* a byte of the call's side frame or of its shadow is neither in the image nor above the ceiling *)
Lemma kp_frame_place : forall cx fp ly3 S3 (W3 : world SEGS) mem3 md3 a,
  AR SEGS B ly3 S3 W3 mem3 md3 -> In (LF_CID, fp) (frames S3) ->
  (forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q) ->
  (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) ->
  ~ in_img SEGS a /\ a < alloc_ceiling.
Proof.
  intros cx fp ly3 S3 W3 mem3 md3 a HAR Hin Hfa Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (al_sep _ _ LAWS ly3 S3 W3 mem3 md3 HAR) as (_ & Hfs).
  rewrite Forall_forall in Hfs. specialize (Hfs (LF_CID, fp) Hin). cbn [fst snd] in Hfs.
  assert (HFB : fs_frame_bytes LF_CID = 1024) by reflexivity. rewrite HFB in Hfs.
  unfold lf_SH, lf_F, shadow_of_addr in *. rewrite <- (Hfa LF_CID fp) in Ha. destruct Ha as [Ha | Ha].
  - split; [|lia].
    pose proof (al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR) as Hc.
    apply Hc. right; left. exists LF_CID, fp. split; [exact Hin|]. rewrite HFB. exact Ha.
  - assert (Hsh : kLowMemEnd <= a) by (unfold SHADOW_OFF, kLowMemEnd in *; lia).
    split; [|unfold SHADOW_OFF in *; lia].
    intros Hi. pose proof (pa_segs_low a Hi). lia.
Qed.

(* a heap block of the state: not in the image, below the ceiling *)
Lemma kp_blk_place : forall ly3 S3 (W3 : world SEGS) mem3 md3 b n a,
  AR SEGS B ly3 S3 W3 mem3 md3 -> In (b, n) (ablocks B ly3 S3) -> b <= a < b + req_size n ->
  ~ in_img SEGS a /\ a < alloc_ceiling.
Proof.
  intros ly3 S3 W3 mem3 md3 b n a HAR Hin Ha.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b n HAR Hin) as (_ & _ & Hc & _). split; [|lia].
  apply (al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR). left. exists b, n. split; [exact Hin | lia].
Qed.

Lemma kp_img_ok_in : forall a, lf_img_ok B MS la_nul -> lf_img_fp MS la_nul a -> in_img SEGS a.
Proof. intros a H Ha. exact (proj1 (H a Ha)). Qed.

(* ==========================================================================
   The cut after kernel
   ========================================================================== *)

Lemma lf_kernel_post : forall cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N
    ly3 S3 (W3 : world SEGS) ms3 md3 ly2 S2 (W2 : world SEGS) ms2 md2 (regs regs2 : bvmap 5 word),
  BASEF cx -> frames S3 = [(LF_CID, fp)] ->
  JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k2 ->
  aarg regs 0 = lf_sp1 cx + LS_P ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 (ms_mem ms2) (lf_sp1 cx - KERNEL_AK) (lf_sp1 cx)
    (fun a => inFP (kernel_awr regs (rdW W3 (ms_mem ms3))) a) ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) ->
  S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  kernel_apost SEGS regs (rdW W3 (ms_mem ms3)) regs2 (rdW W2 (ms_mem ms2)) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  exists kbs' adv,
  0 <= adv <= N /\
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 LF_SH0 /\
  lf_slots cx md mk fp W2 ms2 /\ lf_cur cx W2 ms2 (P + adv) (N - adv) /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly2 S2 W2 ms2 md2 T3 own /\
  lf_blocks B cx md mk T3 ly2 S2 (rdW W2 (ms_mem ms2)) /\
  lf_data cx md mk kbs' mbs gbs (rdW W2 (ms_mem ms2)) /\
  nk_next kbs' = 0 /\ 0 <= nk_n_chunks kbs' <= 3 /\ In (nk_end_errno kbs') nl_errno_tab /\
  (nk_socket_errno kbs' = 0 \/ In (nk_socket_errno kbs') nl_errno_tab) /\
  (nk_send_errno kbs' = 0 \/ In (nk_send_errno kbs') nl_errno_tab) /\
  nk_opened kbs' = nk_opened kbs /\ nk_closed kbs' = nk_closed kbs /\
  nk_n_sent kbs' = nk_n_sent kbs /\ nk_sent kbs' = nk_sent kbs.
Proof.
  intros cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 regs regs2
    HB Hfr HJ3 HJ2 Ha0 Hkp Hsk Hs2 Hperm Hfd Hfs Hpost Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ3) as (Hs1 & H16 & Hlo & H47).
  pose proof KERNEL_AK_val as HK.
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & _ & HRO & _).
  pose proof Hblk as (Bmd & Bmk & _).
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  set (E := fun a => inFP (kernel_awr regs (rdW W3 (ms_mem ms3))) a) in *.
  assert (EE : forall a, E a ->
    (LA_G_NL <= a < LA_G_NL + NK_OPEN) \/ (LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301) \/
    (lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_P + 16))
    by (intros a Ha; exact (kp_kernel_E cx regs _ a Ha0 Ha)).
  (* the image part of E is in the image; the cursor part is above the ceiling *)
  assert (EI : forall a, E a -> (in_img SEGS a /\ a < LA_G_NL + NK_OPEN \/ in_img SEGS a /\ LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301)
                          \/ alloc_ceiling <= a).
  { intros a Ha. destruct (EE a Ha) as [H | [H | H]].
    - left; left. split; [|clia]. apply (kp_img_ok_in a IMG). left. unfold NK_OPEN, NK_SIZE in *. clia.
    - left; right. split; [|clia]. apply (kp_img_ok_in a IMG). right; right; left. clia.
    - right. unfold LS_P, LLVMF_STK in *. clia. }
  assert (LC : lf_call B cx KERNEL_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E).
  { split; [clia|]. split; [unfold LLVMF_STK in *; clia|]. split; [exact Hkp | exact Hsk]. }
  (* the memory clauses kept *)
  assert (Hsv2 : lf_saved cx W2 ms2).
  { apply (lf_saved_callee B cx KERNEL_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC); [|exact Hsv].
    intros a Ha HEa. unfold lf_saved_fp in Ha. destruct (EI a HEa) as [[[Hi _] | [Hi _]] | Hc].
    - pose proof (pa_segs_low a Hi). unfold LLVMF_STK in *. clia.
    - pose proof (pa_segs_low a Hi). unfold LLVMF_STK in *. clia.
    - destruct (EE a HEa) as [H | [H | H]]; unfold LS_P, LA_G_NL, LA_LONG_ALIAS, NK_OPEN, LLVMF_STK in *; clia. }
  assert (Hsl2 : lf_slots cx md mk fp W2 ms2).
  { apply (lf_slots_callee B cx KERNEL_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp LC); [|exact Hsl].
    intros a Ha HEa. unfold lf_slots_fp in Ha.
    destruct (EE a HEa) as [H | [H | H]]; unfold LS_P, LA_G_NL, LA_LONG_ALIAS, NK_OPEN, LLVMF_STK in *; clia. }
  assert (FNE : forall a, (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) -> ~ E a).
  { intros a Ha HEa. destruct (kp_frame_place cx fp ly3 S3 W3 (ms_mem ms3) md3 a HAR3 Hin Hfa Ha) as (Hni & Hc).
    destruct (EI a HEa) as [[[Hi _] | [Hi _]] | Hc']; [exact (Hni Hi) | exact (Hni Hi) | clia]. }
  assert (Hhd2 : lf_header cx fp W2 ms2).
  { apply (lf_header_callee B cx fp KERNEL_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hhd].
    intros a Ha. apply FNE. left. unfold lf_header_fp in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha. clia. }
  assert (Hfsh2 : lf_fshadow cx fp W2 ms2 LF_SH0).
  { apply (lf_fshadow_callee B cx fp KERNEL_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hfsh].
    intros a Ha. apply FNE. right. unfold lf_fshadow_fp in Ha. clia. }
  assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
  assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
  assert (Hblk2 : lf_blocks B cx md mk T3 ly2 S2 (rdW W2 (ms_mem ms2))).
  { apply (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm).
    exact (lf_blocks_callee B cx KERNEL_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 LC Pmd Pmk Hblk). }
  (* kernel's post *)
  destruct (Hpost kbs (proj1 Hdat)) as (kbs' & Hk' & Hwf' & Hnx & Hnc & Hend & Hsock & Hsend & Hop & Hopd & Hcl
    & Hmis & Hns & Hsent & Hnif & Htab & Hcurp & Haw & (la & Hla & Hlal)).
  (* long_alias's NUL at the new memory *)
  assert (HNUL : val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0).
  { rewrite HLN. unfold LA_NUL. destruct Hla as ((_ & _ & Hb) & _). intros kk Hkk.
    assert (kk = 0%nat) by clia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
    replace (LA_LONG_ALIAS + 300) with (LA_LONG_ALIAS + Z.of_nat (length la)) by clia.
    rewrite (Hb (length la)) by (rewrite length_app; cbn [length]; clia).
    rewrite nth_error_app2 by clia. rewrite Nat.sub_diag. reflexivity. }
  (* the payload block *)
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ3 Hn)).
  assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly2 S2 W2 ms2 md2 T3 own).
  { apply (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 ev mo wl lv
      ly3 S3 ly2 S2 W2 ms2 md2 T3 own k2 HB HJ2 Hs2 Hperm).
    apply (lf_jbk_callee B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own KERNEL_AK ly2 S2 W2 ms2 md2 E
      IMG RIMG LC); [| | exact HPB | exact Hfd | exact Hfs | exact HNUL | exact Hjbk].
    - intros a Ha HEa. destruct Ha as [Ha | Ha].
      + destruct Ha as [Ha | [Ha | (f & n & Hfn & Ha)]].
        * rewrite HMS in Ha. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Ha.
          destruct (EE a HEa) as [H | [H | H]]; unfold LS_P, LA_G_NL, LA_LONG_ALIAS, NK_OPEN, LLVMF_STK in *; clia.
        * rewrite HMS in Ha. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Ha.
          destruct (EE a HEa) as [H | [H | H]]; unfold LS_P, LA_G_NL, LA_LONG_ALIAS, NK_OPEN, LLVMF_STK in *; clia.
        * assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
          assert (Hn : n = AMF_BLOCK).
          { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
            destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
          subst n.
          destruct (kp_blk_place ly3 S3 W3 (ms_mem ms3) md3 f AMF_BLOCK a HAR3 HfnT
            ltac:(unfold req_size, AMF_BLOCK in *; cbn; clia)) as (Hni & Hc).
          destruct (EI a HEa) as [[[Hi _] | [Hi _]] | Hc']; [exact (Hni Hi) | exact (Hni Hi) | clia].
      + assert (Hn : 0 < c_n cx) by clia.
        destruct (kp_blk_place ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) a HAR3 (HPB Hn)
          ltac:(unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); clia)) as (Hni & Hc).
        destruct (EI a HEa) as [[[Hi _] | [Hi _]] | Hc']; [exact (Hni Hi) | exact (Hni Hi) | clia].
    - intros a Ha HEa. destruct (EE a HEa) as [H | [H | H]].
      + apply (ar_not_ro_G HSEGS a); [|exact Ha]. unfold inG, G_HARNESS. apply Exists_cons_hd.
        unfold in_zr. cbn [fst snd]. unfold NK_OPEN in H. clia.
      + apply (ar_not_ro_G HSEGS a); [|exact Ha]. unfold inG, G_HARNESS. apply Exists_cons_tl, Exists_cons_tl,
          Exists_cons_hd. unfold in_zr. cbn [fst snd]. clia.
      + apply (ar_not_ro_high HSEGS a); [unfold LS_P, LLVMF_STK in *; clia | exact Ha]. }
  (* the cursor *)
  pose proof Hcur as (HcP & HcN & (q & Hq0 & HqP & HqN)).
  assert (HP64 : 0 <= P < 2 ^ 64) by (unfold lf_slot, lf_at in HcP; exact (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcP)).
  assert (HN64 : 0 <= N < 2 ^ 64) by (unfold lf_slot, lf_at in HcN; exact (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcN)).
  destruct (Hcurp P N) as (adv & Hadv & HwP & HwN); [rewrite Ha0; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HcP) |
    rewrite Ha0; replace (lf_sp1 cx + LS_P + 8) with (lf_sp1 cx + LS_N) by (unfold LS_P, LS_N; clia);
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HcN) | exact HP64 | exact HN64 |].
  rewrite Ha0 in HwP, HwN.
  assert (HPN : P + adv < 2 ^ 64).
  { destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn | Hn].
    - destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 (HPB Hn)) as (_ & _ & Hc & _).
      unfold req_size in Hc. destruct (Z.eqb_spec (c_n cx) 0); clia.
    - clia. }
  assert (Hcur2 : lf_cur cx W2 ms2 (P + adv) (N - adv)).
  { split; [|split].
    - unfold lf_slot, lf_at. apply rdword_of_val_mem; [exact HwP | clia].
    - unfold lf_slot, lf_at. apply rdword_of_val_mem; [|clia].
      replace (lf_sp1 cx + LS_N) with (lf_sp1 cx + LS_P + 8) by (unfold LS_P, LS_N; clia). exact HwN.
    - exists (q + adv). clia. }
  (* lf_data at kernel's new bytes *)
  pose proof (lf_call_kagree B cx KERNEL_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC) as KG.
  destruct Hdat as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & Dmk & Dkwf & Dare & Difp & Dgn & Dgw & Dodd
    & Dtx & Dla).
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2))).
  { apply (lf_aro_callee B cx KERNEL_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E RIMG LC); [|exact HRO].
    intros a Ha HEa. destruct (EE a HEa) as [H | [H | H]].
    - exact (ar_not_ro_G HSEGS a ltac:(unfold inG, G_HARNESS; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
        unfold NK_OPEN in H; clia) Ha).
    - exact (ar_not_ro_G HSEGS a ltac:(unfold inG, G_HARNESS; apply Exists_cons_tl, Exists_cons_tl,
        Exists_cons_hd; unfold in_zr; cbn [fst snd]; clia) Ha).
    - exact (ar_not_ro_high HSEGS a ltac:(unfold LS_P, LLVMF_STK in *; clia) Ha). }
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  assert (WB : forall b n, In (b, n) (ablocks B ly2 S2) -> wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) b n).
  { intros b n Hbn i Hi _. destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) md2 b n HAR2 Hbn) as (_ & _ & _ & _ & Hp & _).
    apply (apresent_writable SEGS). apply (proj1 (Hp (b + i) ltac:(unfold req_size; destruct (Z.eqb_spec n 0); clia))). }
  assert (MDX : forall a, md <= a < md + MD_SIZE -> ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - KERNEL_AK) (lf_sp1 cx) E a).
  { intros a Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E md MD_SIZE a Bmd Ha). intros HEa.
    destruct (kp_blk_place ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE a HAR3 Bmd
      ltac:(unfold req_size, MD_SIZE in *; cbn; clia)) as (Hni & Hc).
    destruct (EI a HEa) as [[[Hi _] | [Hi _]] | Hc']; [exact (Hni Hi) | exact (Hni Hi) | clia]. }
  assert (MKX : forall a, mk <= a < mk + MK_SIZE -> ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - KERNEL_AK) (lf_sp1 cx) E a).
  { intros a Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E mk MK_SIZE a Bmk Ha). intros HEa.
    destruct (kp_blk_place ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE a HAR3 Bmk
      ltac:(unfold req_size, MK_SIZE in *; cbn; clia)) as (Hni & Hc).
    destruct (EI a HEa) as [[[Hi _] | [Hi _]] | Hc']; [exact (Hni Hi) | exact (Hni Hi) | clia]. }
  assert (IMX : forall a, lf_img_fp MS la_nul a -> ~ E a ->
    ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - KERNEL_AK) (lf_sp1 cx) E a)
    by (intros a Ha HEa; exact (lfx_imgfp B MS la_nul ly3 S3 ly2 S2 _ _ E a IMG Ha HEa)).
  assert (Hdat2 : lf_data cx md mk kbs' mbs gbs (rdW W2 (ms_mem ms2))).
  { refine (conj Hk' (conj Hwf' (conj (Htab lf_tab Dtab) (conj _ (conj _ (conj _ (conj _ (conj Dmwf (conj _
      (conj Dkwf (conj Dare (conj _ (conj _ (conj _ (conj Hodd2 (conj Htx2 _)))))))))))))))).
    - rewrite Hop. exact Dop.
    - rewrite Hmis. exact Dmis.
    - rewrite Hopd, Hcl. exact Doc.
    - apply (amodel_keep SEGS _ _ _ md mbs KG (WB md MD_SIZE Pmd)); [|exact Dmd].
      intros ii Hii. apply MDX. clia.
    - apply (amarks_keep SEGS _ _ _ mk gbs KG (WB mk MK_SIZE Pmk)); [|exact Dmk].
      intros ii Hii. apply MKX. clia.
    - intros e He. destruct (Difp e He) as (qq & Hq1 & Hq2 & Hq3). exists qq.
      split; [|split; [exact Hq2|]].
      + apply (au64_keep SEGS _ _ _ _ _ KG); [|exact Hq1]. intros kk Hkk. apply IMX.
        * left. unfold NK_IF_NAME, NK_SIZE in *. clia.
        * intros HEa. destruct (EE _ HEa) as [H | [H | H]]; unfold NK_IF_NAME, NK_OPEN, LA_G_NL, LA_LONG_ALIAS,
            LS_P, LLVMF_STK in *; clia.
      + intros H60. apply (au64_keep SEGS _ _ _ _ _ KG); [|exact (Hq3 H60)]. intros kk Hkk. apply IMX.
        * right; right; right; right; right; right. clia.
        * intros HEa. destruct (EE _ HEa) as [H | [H | H]]; unfold LA_ODD, LA_G_NL, LA_LONG_ALIAS, LS_P,
            LLVMF_STK in *; clia.
    - apply (lf_gnames_at_keep _ _ _ 64 KG ltac:(clia)); [|exact Dgn]. intros a Ha. apply IMX.
      + right; left. exact Ha.
      + intros HEa. destruct (EE _ HEa) as [H | [H | H]]; unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, LA_LONG_ALIAS,
          NK_OPEN, LS_P, LLVMF_STK in *; clia.
    - apply (lf_gnames_w_keep _ _ _ KG); [| |exact Dgw].
      + assert (Hw : forall (m' : word -> option byte) a, LA_G_NAMES <= a < LA_G_NAMES + 512 -> writable_at SEGS m' a)
          by (rewrite HSEGS; exact LA_G_NAMES_writable).
        intros ii Hii _. apply Hw. unfold G_NAMES_SIZE in Hii. clia.
      + intros a Ha. apply IMX.
        * right; left. exact Ha.
        * intros HEa. destruct (EE _ HEa) as [H | [H | H]]; unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL,
            LA_LONG_ALIAS, NK_OPEN, LS_P, LLVMF_STK in *; clia.
    - split; [exists la; split; [exact (kp_au8arr_prefix _ _ la [zb 0] Hla) | exact Hlal]|]. split.
      + destruct Hla as ((_ & _ & Hb) & _). intros kk Hkk.
        assert (kk = 0%nat) by clia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
        replace (LA_LONG_ALIAS + 300) with (LA_LONG_ALIAS + Z.of_nat (length la)) by clia.
        rewrite (Hb (length la)) by (rewrite length_app; cbn [length]; clia).
        rewrite nth_error_app2 by clia. rewrite Nat.sub_diag. reflexivity.
      + exact (lf_la_slack_any HSEGS _). }
  exists kbs', adv.
  split; [exact Hadv|]. split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|].
  split; [exact Hcur2|]. split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|].
  split; [exact Hnx|]. split; [exact Hnc|]. split; [exact Hend|]. split; [exact Hsock|]. split; [exact Hsend|].
  split; [rewrite Hopd; reflexivity|]. split; [exact Hcl|]. split; [exact Hns | exact Hsent].
Qed.

End b.
End a.
