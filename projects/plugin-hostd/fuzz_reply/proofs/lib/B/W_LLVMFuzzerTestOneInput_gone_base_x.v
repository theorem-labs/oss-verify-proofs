(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: KF-COUNT F3: GC1_x / GT0_x carry gn_cst (lib/A's text at 6151e809fb3) *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's base on image B (lib/B/W_LLVMFuzzerTestOneInput_gone_base.v,
   a Theorem Labs lane's, a working branch fee5272ac13, with our HB-clause fix at gn_stkr), for the conversion
   of ARM_gone to the cut invariants of lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.  _gone_base.v is not edited; its AR-free
   definitions (gn_Bx, gframe, gn_kregs, gn_op, the model notions, the GN_* texts, gn_Gs, the cut points' addresses) are
   CITED from it.  What reads AR is restated here under its name + _x; template: SmallX's image-A twin
   lib/A/W_LLVMFuzzerTestOneInput_gone_base_x.v (a working branch 95a5de32ab2), merged per item:
   - the gx wrappers of W_frame_x's plain runs (SRr_run_pi_AJX0_x, SRr_run_to_pi_AJX0_x, SRr_run_pi_AJX0_call_x) over
     W_journal_x.ajournal_gx_x;
   - gn_nums_x, gn_shent_in_block_x over ARx at the ghost list [] (cut_x's HP0 makes every ghost list of the walk
     empty); B's gn_stkr (the cut's STKR, read off lf_base_x) and gn_afn_pre (a callee's afn_pre_x at sp = F) at [];
   - the cut points GJN_x, GL1_x, GRG_x, GC1_x, GT0_x, GCSD_x, through gcom_x / gst_x: the journal is ajournal_gx_x at
     Hp = [], LS is cut_x's LSx; every other conjunct is _gone_base.v's text;
   - GN_CNL_x / GN_CSHE_x: _gone_base.v's GN_CNL / GN_CSHE with the kit's cnl_spec_x / cshe_spec_x at PST / ARx. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_base.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_xR_g6.
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_base.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.
(* @@ B-ONLY-HDR Local_Notation A_LLVMF *)
Local Notation A_LLVMF := YCfn.A_LLVMF.

(* ------------------------------------------------------------------ the gx wrappers of W_frame.v's plain runs
   (A's base Sections px / pxc / pxr, at any placement of any listing): a run that writes the fake frame's shadow,
   which the token run's static check refuses, carried over W2's ajournal_gx at XO = 0, OUT = []. *)
(* @@ SECTION px *)
Section px. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED Context ctx:L *)
Context {L : ptable wsym} {PL : PAListing L} {PI : PAImg L}.
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ AX-ONLY Variable PST *)
Variable PST : list (Z * Z).
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ RESOLVED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx hl.
(* @@ MERGED Variable G *)
Variable G : list (Z * Z).
(* @@ AX-ONLY Local_Notation AJG *)
Local Notation AJG := (ajournal_gx_x pa_segs B PST ARx G 0 []).
(* _gone_base.v:64 SRr_run_to_pi_AJX0 *)
(* @@ RESOLVED Lemma SRr_run_to_pi_AJX0 *)
Lemma SRr_run_to_pi_AJX0_x : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi pl_tpi n stop ss = (ss', st) -> pi_plain_stop st ->
  AJG STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok_pi pa_segs pa_val E ss' (restrict (w_H W) ms') ->
    AJG STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRr_run_to_pi_AJ_x B PST ARx LAWS W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HGr].
  apply (ajournal_gx_pack_x pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
(* _gone_base.v:110 SRr_run_pi_AJX0_call *)
(* @@ CONFLICT Lemma SRr_run_pi_AJX0_call *)
Lemma SRr_run_pi_AJX0_call_x : forall W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_runN_pi pl_tpi n ss = (ss', PRS_call s) ->
  AJG STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok pa_segs E (setpc ss' (pa_sigma s)) (restrict (w_H W) ms') ->
    AJG STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRr_run_pi_AJ_call_x B PST ARx LAWS W n E ss ss' s ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack_x pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
(* _gone_base.v:139 SRr_run_pi_AJX0 *)
(* @@ CONFLICT Lemma SRr_run_pi_AJX0 *)
Lemma SRr_run_pi_AJX0_x : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_runN_pi pl_tpi n ss = (ss', st) -> pi_plain_stop st ->
  AJG STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok_pi pa_segs pa_val E ss' (restrict (w_H W) ms') ->
    AJG STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRr_run_pi_AJ_x B PST ARx LAWS W n E ss ss' st ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack_x pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
(* @@ END px *)
(* ---- route R: the three runs above at SRrG pa_segs R over the journal at R (AJGR), each its strict proof over
   lib/B/W_frame_x.v's G runs SRrG_run_to_pi_AJ_xG / SRrG_run_pi_AJ_call_xG / SRrG_run_pi_AJ_xG and
   ajournal_gx_pack_xR.  Strict text above unchanged. ---- *)
Section pxR.
Variable R : world pa_segs -> world pa_segs -> Prop.
Local Notation AJGR := (ajournal_gx_xR pa_segs B PST ARx R G 0 []).

Lemma SRrG_run_to_pi_AJX0_xR : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi pl_tpi n stop ss = (ss', st) -> pi_plain_stop st ->
  AJGR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok_pi pa_segs pa_val E ss' (restrict (w_H W) ms') ->
    AJGR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    YA0nH.SRrG pa_segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  YA0nH.SRrG pa_segs R W (mkCfg ms mdc) Q.
Proof.
  intros W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRrG_run_to_pi_AJ_xG B PST ARx LAWS W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HGr].
  apply (ajournal_gx_pack_xR pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.

Lemma SRrG_run_pi_AJX0_call_xR : forall W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_runN_pi pl_tpi n ss = (ss', PRS_call s) ->
  AJGR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok pa_segs E (setpc ss' (pa_sigma s)) (restrict (w_H W) ms') ->
    AJGR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    YA0nH.SRrG pa_segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  YA0nH.SRrG pa_segs R W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRrG_run_pi_AJ_call_xG B PST ARx LAWS W n E ss ss' s ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack_xR pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.

Lemma SRrG_run_pi_AJX0_xR : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_runN_pi pl_tpi n ss = (ss', st) -> pi_plain_stop st ->
  AJGR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok_pi pa_segs pa_val E ss' (restrict (w_H W) ms') ->
    AJGR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    YA0nH.SRrG pa_segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  YA0nH.SRrG pa_segs R W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRrG_run_pi_AJ_xG B PST ARx LAWS W n E ss ss' st ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack_xR pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
End pxR.
End px.
(* @@ SECTION g *)
Section g.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* cut_x's Section w header, the part ARM_gone's cut points and phases read *)
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ MERGED Variable MT *)
Variable MT : ameter_ops.
(* @@ MERGED Variables XM_LIB *)
Variables XM_LIB : Z -> Z.
(* @@ MERGED Variables RLO *)
Variables RLO RHI : Z.
(* @@ MERGED Variable fr_live_pre *)
Variable fr_live_pre : astate -> Prop.
(* @@ AX-ONLY Variables LIBROOM *)
Variables LIBROOM NP : astate -> Prop.
(* @@ MERGED Variable G_fr *)
Variable G_fr : list (Z * Z).
(* @@ MERGED Variable fr_FP *)
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
(* @@ AX-ONLY Variable PST *)
Variable PST : list (Z * Z).
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx hl.
(* @@ MERGED Hypothesis HG *)
Hypothesis HG : gx_ok segs B G_fr.
(* @@ AX-ONLY Variable LSx *)
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
(* @@ MERGED Variable RINV *)
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* @@ RESOLVED #[local]_Notation SIGMA *)
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* ---- the walk at the ghost list [] (cut_x HP0) ---- *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* @@ AX-ONLY Local_Notation AJ0 *)
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation LFB0 *)
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
Local Notation gn_tie := (W_LLVMFuzzerTestOneInput_gone_base.gn_tie B).
(* ------------------------------------------------------------------ the arm's numbers *)
(* @@ RESOLVED Lemma gn_nums *)
Lemma gn_nums_x : forall cx own ly3 S3 W mem md k fpos,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k -> own = [(1, fpos)] ->
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in let FF := frame_addr ly3 1 fpos in
  sp0 mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= sp0 <= 2 ^ 47 /\ F mod 32 = 0 /\ sp0 - 352 < F <= sp0 - 320 /\
  4096 <= FF /\ FF + 128 <= alloc_ceiling /\ in_app FF 128 /\ frames S3 = [(1, fpos)] /\
  AR0 ly3 S3 W mem md.
Proof.
  intros cx own ly3 S3 W mem md k fpos (HAI & HPRE) HJ ->.
  pose proof HPRE as (HFN & _ & _ & _ & _ & _ & _ & Hfr0 & _).
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  rewrite !Z.add_0_r in *.
  destruct HSTK as (Hal & _ & Hceil & Hlo & Hhi & H47 & _).
  rewrite Hfr0, app_nil_r in Hfrs.
  assert (Hin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR Hin) as (H4 & Hc & Happ).
  change (fs_frame_bytes 1) with 128 in Hc, Happ.
  pose proof (YM05.alloc_ceiling_value) as AC.
  cbv zeta. unfold lf_F. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)).
  split; [exact Hal|]. split; [unfold YCfn.LLVMF_STK in *; lia|].
  split; [rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Happ|]. split; [exact Hfrs|exact HAR].
Qed.

(* STKR: the caller's stack is readable from the entry's sp up to ly_top, the LAST conjunct of the cut's
   fr_lib_pre_cf (_cut.v:265); cnl_spec's last premise is built from it (p5b gp5_stk_rd). *)
(* @@ B-ONLY-AR[lf_base] Lemma gn_stkr *)
Lemma gn_stkr_x : forall cx, LFB0 cx ->
  forall a, spZ (c_regs cx) <= a < ly_top (c_ly cx) -> aview segs (w_H (c_W cx)) (c_mem cx) a <> None.
Proof.
  intros cx (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE.
  (* fr_lib_pre_cf_x: the pre's 18 conjuncts with LIBROOM / NP after fr_live_pre; STKR is the 20th, HB after it *)
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKR & _). exact HSTKR.
Qed.

(* a shadow entry inside a live block (A's base, verbatim) *)
(* @@ RESOLVED Lemma gn_shent_in_block *)
Lemma gn_shent_in_block_x : forall ly S (W : world segs) mem md E Bx (m : nat) q p n lo hi,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> 0 <= lo -> lo <= hi -> p <= q + lo -> q + hi <= p + req_size n ->
  shent_ok segs Bx E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
  intros ly S W mem md E Bx m q p n lo hi HAR Hin HB Hm Hlo Hlh Hp1 Hp2.
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of segs).
  destruct (alx_shadow _ _ _ LAWS ly S [] W mem md p n HAR Hin (fun h Hh => False_ind _ Hh)) as [Hbs _].
  split.
  - destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; zlia].
    eapply block_shadow_range; [exact Hbs | zlia | zlia].
  - destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.

(* W_frame_b.v frm_off_imgB (image B's top 0x5fc000) over ARx at []: W_frame_x.v frm_off_imgP_x's proof with
   W_img_x.v's fr_img_cover_x (the image law's ly_img, which reaches B's top) *)
(* @@ CONVERTED Lemma frm_off_imgB *)
Lemma frm_off_imgB_x : forall ly S (W : world segs) mem md cid pos,
  AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
  intros ly S W mem md cid pos HAR Hin.
  destruct (W_img_x.fr_img_cover_x B ARx LAWS ly S [] W mem md HAR) as [_ C2].
  pose proof (proj2 (alx_img _ _ _ LAWS ly S [] W mem md HAR) cid pos Hin) as Hf.
  right. lia.
Qed.

(* A callee's afn_pre at sp = F (the cut's frame), from the cut's journal and the saved registers the prologue
   stored: B's latch twin lt_afn_pre_at (a working branch ee519e5e2f5,
   lib/B/W_LLVMFuzzerTestOneInput_latch.v:625-698), with the saved-register clause of aframe_at in place of the whole
   frame, so that every call of the arm (relay_reads, relay_instance_gone, check_no_loss, check_shape_ends) names one
   lemma. *)
(* @@ CONVERTED Lemma gn_afn_pre *)
Lemma gn_afn_pre_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* @@ RESTATED-LOCAL Ltac kept *)
Ltac kept KR := apply KR; repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ the arm's own cut points (offsets from fr_B0
   0x82344, B's objdump) *)
(* @@ RESOLVED Definition gcom *)
Definition gcom_x (cx : lfcx) (t kq : Z) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx sh (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 16) (c_p cx + kq) /\ sv8 W mem (lf_F cx + 144) (c_n cx - kq) /\
  sv8 W mem (lf_F cx + 88) t /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem.
(* the operation's facts: op 5 decoded at lm_k, the stream empty at the dispatch *)
(* _gone_base.v's AR-free names that take this Section's variables *)
(* @@ CONFLICT Definition gn_kregs *)
Local Notation gn_kregs := (W_LLVMFuzzerTestOneInput_gone_base.gn_kregs B).
(* @@ CONFLICT Definition GJN *)
Definition GJN_x (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_join) regs mem md /\
    gcom_x cx t (gn_kq cx m) fake_shadow fpos ly S W mem md kk /\
    amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\
    (* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)): the allocator's room invariant NP at the arm's state, from the
       cut's lcut_x through every allocator call's post to the latch *)
    NP S /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 24 = w64 (SB + frame_addr ly 1 fpos / 8) /\ getr regs 26 = w64 HI_G_NOUT /\
    getr regs 21 = w64 (gn_id cx m).
(* @@ CONVERTED Definition GN_CNL / GN_CSHE *)
Variable MMAX : Z.                                   (* W6's / W7's request bound *)
(* ---- the room round's count row of the arm (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c)).  RP is the room record the callees are taken at;
   gn_pk is the arm's peak (s5-r1d's pk_gone at the instance).  GN_LS_cnt_x: at the operation's LS state the live
   counts plus the arm's peak stay under the bounds.  Its guards are s5-r1d's fr_LS3cp_cnt_gone's exactly (commit
   29956454065, lib/A/ReplyLScntRP.v / ReplyLScnt.v), with RINV for fr_RINV and LSx for fr_LS3cp; the walk holds each
   at GRG and carries them to the loop in gdone ---- *)
Variable RP : roomp.
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Definition GN_LS_cnt_x : Prop := forall cx t m ly S hs,
  LSx cx t m ly S -> RINV cx t m -> gn_pairs m hs ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP (gn_pk cx m hs) (ablocks B ly S).

(* check_no_loss (0x85e3c) and check_shape_ends (0x85770) at each slot's own G (_gone_base.v gn_Gs, cited): the kit's
   cnl_spec_x / cshe_spec_x (W_contract_x.v Sections w3n / w3e) at PST / ARx and the room record RP (the room round:
   both specs take it); _gone_base.v's GN_CNL / GN_CSHE texts otherwise *)
Definition GN_CNL_x : Prop :=
  forall j, (j < 4)%nat -> cnl_spec_x (PI := PB_fr) B PST ARx MT RP (gn_Gs j) MMAX (BASE + AF_fr_check_no_loss).
Definition GN_CSHE_x : Prop :=
  forall j, (j < 4)%nat -> cshe_spec_x (PI := PB_fr) B PST ARx MT RP (gn_Gs j) (BASE + AF_fr_check_shape_ends).
(* @@ RESOLVED Definition gst *)
(* what every state of the arm after the join carries: the journal, the frame (with the fake frame's shadow
   sh), the cursor slots, the input, the image views, the model and its blocks, and the room invariant NP (the room
   round: threaded through every allocator call's post, ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)) *)
Definition gst_x (cx : lfcx) (t kq : Z) (m : lmod) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gcom_x cx t kq sh fpos ly S W mem md kk /\
  amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\ NP S.
(* the prefix snprintf left in the fake frame (FF + 32 = s3), as check_shape_ends reads it *)
(* @@ RESOLVED Definition GL1 *)
Definition GL1_x (cx : lfcx) (t : Z) (m : lmod) (q : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_l1) regs mem md /\
    gst_x cx t (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 26 = w64 HI_G_NOUT /\ getr regs 21 = w64 (gn_id cx m) /\
    getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\ getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) /\
    getr regs 23 = w64 (4 - Z.of_nat q) /\ getr regs 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\
    getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) /\
    (q < 4)%nat /\
    (forall j, (j < q)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x84b40: the four reads[] are written; relay_instance_gone(id) is next (s5 = id, s10 = HI_G_NOUT) *)
(* @@ RESOLVED Definition GRG *)
Definition GRG_x (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_rig) regs mem md /\
    gst_x cx t (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 26 = w64 HI_G_NOUT /\ getr regs 21 = w64 (gn_id cx m) /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* _gone_base.v:670 GC1 *)
(* 0x84848: the check_no_loss_read loop's head, q slots done; s4 = F + 192 + 4q, s5 = &g_s[q], s6 = F + 208 *)
(* @@ RESOLVED Definition gdone *)
Local Notation gdone := (W_LLVMFuzzerTestOneInput_gone_base.gdone RINV).
Local Notation gn_cst := (W_LLVMFuzzerTestOneInput_gone_base.gn_cst MT).

(* _gone_base.v:182 gn_nums *)
(* @@ RESOLVED Definition GC1 *)
Definition GC1_x (cx : lfcx) (t : Z) (m m1 : lmod) (q : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_c1) regs mem md /\
    gst_x cx t (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\
    getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\ getr regs 22 = w64 (lf_F cx + 208) /\
    (q < 4)%nat /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x84b78: the check_no_loss_read loop is done; the table-order loop is entered or skipped *)
(* @@ RESOLVED Definition GT0 *)
Definition GT0_x (cx : lfcx) (t : Z) (m m1 : lmod)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_t0) regs mem md /\
    gst_x cx t (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x84c84: the table-order loop is done; at = g_nout, and the model after the operation is mc *)
(* @@ RESOLVED Definition GCSD *)
Definition GCSD_x (cx : lfcx) (t : Z) (m mc : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md /\
    gst_x cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
    LSx cx (t + 1) mc ly S /\ RINV cx (t + 1) mc /\ lm_k mc = gn_kq cx m /\
    0 <= gn_kq cx m <= c_n cx /\ 0 <= t < OPS_MAX /\
    sv8 W mem (lf_F cx + 208) (Z.of_nat (length (lm_O mc))) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    gn_kregs cx (frame_addr ly 1 fpos) regs.
(* @@ END g *)
(* ---- route R: the R twins of the arm's cut points (gcom_x .. GCSD_x: AJ0 -> AJ0R at R), of the callee bundles
   GN_CNL_x / GN_CSHE_x (cnl_spec_xR / cshe_spec_xR) and of the lemmas whose statements carry the journal.  Strict
   text above unchanged. ---- *)
Section gR.
Variable R : world segs -> world segs -> Prop.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).

Lemma gn_nums_xR : forall cx own ly3 S3 W mem md k fpos,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k -> own = [(1, fpos)] ->
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in let FF := frame_addr ly3 1 fpos in
  sp0 mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= sp0 <= 2 ^ 47 /\ F mod 32 = 0 /\ sp0 - 352 < F <= sp0 - 320 /\
  4096 <= FF /\ FF + 128 <= alloc_ceiling /\ in_app FF 128 /\ frames S3 = [(1, fpos)] /\
  AR0 ly3 S3 W mem md.
Proof.
  intros cx own ly3 S3 W mem md k fpos (HAI & HPRE) HJ ->.
  pose proof HPRE as (HFN & _ & _ & _ & _ & _ & _ & Hfr0 & _).
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  rewrite !Z.add_0_r in *.
  destruct HSTK as (Hal & _ & Hceil & Hlo & Hhi & H47 & _).
  rewrite Hfr0, app_nil_r in Hfrs.
  assert (Hin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR Hin) as (H4 & Hc & Happ).
  change (fs_frame_bytes 1) with 128 in Hc, Happ.
  pose proof (YM05.alloc_ceiling_value) as AC.
  cbv zeta. unfold lf_F. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)).
  split; [exact Hal|]. split; [unfold YCfn.LLVMF_STK in *; lia|].
  split; [rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Happ|]. split; [exact Hfrs|exact HAR].
Qed.

Lemma gn_afn_pre_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch.
Proof.
  clear gn_pk.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

Definition gcom_xR (cx : lfcx) (t kq : Z) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx sh (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 16) (c_p cx + kq) /\ sv8 W mem (lf_F cx + 144) (c_n cx - kq) /\
  sv8 W mem (lf_F cx + 88) t /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem.

Definition GJN_xR (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_join) regs mem md /\
    gcom_xR cx t (gn_kq cx m) fake_shadow fpos ly S W mem md kk /\
    amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\
    (* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)): the allocator's room invariant NP at the arm's state, from the
       cut's lcut_x through every allocator call's post to the latch *)
    NP S /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 24 = w64 (SB + frame_addr ly 1 fpos / 8) /\ getr regs 26 = w64 HI_G_NOUT /\
    getr regs 21 = w64 (gn_id cx m).

Definition GN_CNL_xR : Prop :=
  forall j, (j < 4)%nat -> W_contract_xR_g6.cnl_spec_xR (PI := PB_fr) B PST ARx R MT RP (gn_Gs j) MMAX (BASE + AF_fr_check_no_loss).

Definition GN_CSHE_xR : Prop :=
  forall j, (j < 4)%nat -> W_contract_xR_g6.cshe_spec_xR (PI := PB_fr) B PST ARx R MT RP (gn_Gs j) (BASE + AF_fr_check_shape_ends).

Definition gst_xR (cx : lfcx) (t kq : Z) (m : lmod) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gcom_xR cx t kq sh fpos ly S W mem md kk /\
  amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\ NP S.

Definition GL1_xR (cx : lfcx) (t : Z) (m : lmod) (q : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_l1) regs mem md /\
    gst_xR cx t (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 26 = w64 HI_G_NOUT /\ getr regs 21 = w64 (gn_id cx m) /\
    getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\ getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) /\
    getr regs 23 = w64 (4 - Z.of_nat q) /\ getr regs 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\
    getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) /\
    (q < 4)%nat /\
    (forall j, (j < q)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).

Definition GRG_xR (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_rig) regs mem md /\
    gst_xR cx t (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 26 = w64 HI_G_NOUT /\ getr regs 21 = w64 (gn_id cx m) /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).

Definition GC1_xR (cx : lfcx) (t : Z) (m m1 : lmod) (q : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_c1) regs mem md /\
    gst_xR cx t (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\
    getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\ getr regs 22 = w64 (lf_F cx + 208) /\
    (q < 4)%nat /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).

Definition GT0_xR (cx : lfcx) (t : Z) (m m1 : lmod)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_t0) regs mem md /\
    gst_xR cx t (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).

Definition GCSD_xR (cx : lfcx) (t : Z) (m mc : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md /\
    gst_xR cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
    LSx cx (t + 1) mc ly S /\ RINV cx (t + 1) mc /\ lm_k mc = gn_kq cx m /\
    0 <= gn_kq cx m <= c_n cx /\ 0 <= t < OPS_MAX /\
    sv8 W mem (lf_F cx + 208) (Z.of_nat (length (lm_O mc))) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    gn_kregs cx (frame_addr ly 1 fpos) regs.
End gR.
End g.

