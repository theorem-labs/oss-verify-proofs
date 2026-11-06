(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's base (lib/A/W_LLVMFuzzerTestOneInput_gone_base.v,
   a Theorem Labs lane's, adapted to integ at commit 95cae0d4740), for the conversion of ARM_gone to
   the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v (a Theorem Labs lane's route (b), step 7). _gone_base.v is
   not edited; its AR-free definitions (gn_Bx, gframe, gn_kregs, gn_op, the model notions, the GN_* texts, the cut
   points' addresses) are CITED from it.  What reads AR is restated here under its name + _x:
   - the gx wrappers of W_frame_x's plain runs (SRr_run_pi_AJX0_x, SRr_run_to_pi_AJX0_x, SRr_run_pi_AJX0_call_x) over
     W_journal_x.ajournal_gx_x, with the twins' binder count (Hp after S, Hpc after Sc), so W_frame_x's run Ltacs
     (paj_run_sh_x, paj_run_to_sh_x, paj_run_shc_x, psrr_branch_pi_x) take them; _gone_base.v's paj_run_to_shx is
     W_frame.v's paj_run_to_sh, so its twin is W_frame_x's paj_run_to_sh_x;
   - gn_nums_x, gn_shent_in_block_x, gn_entryA_x over ARx at the ghost list [] (cut_x's HP0 makes every ghost list of
     the walk empty), gn_tools_x (the runs over W_journal_x's generic chain);
   - the cut points GJN_x, GL1_x, GRG_x, GC1_x, GT0_x, GCSD_x, through gcom_x / gst_x: the journal is
     ajournal_gx_x at Hp = [] (the entry's and the state's), LS is cut_x's LSx; every other conjunct is _gone_base.v's
     text.  GN_LS_rig / GN_RI_step / GN_RI_end take LS as a parameter: the walk passes LSx to them unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
(* _gone_base.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
(* route R: SRrG and its rules (the R twins below) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* _gone_base.v:59-161 Sections px / pxc / pxr: the gx wrappers of the plain runs, over ajournal_gx_x *)
Section pxx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable wsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x pa_segs B ARx hl.
Variable G : list (Z * Z).
Local Notation AJG := (ajournal_gx_x pa_segs B PST ARx G 0 []).
(* _gone_base.v:64 SRr_run_to_pi_AJX0 *)
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
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack_x pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
(* _gone_base.v:110 SRr_run_pi_AJX0_call *)
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
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the three plain-run wrappers over the gx journal at a world relation R.
   W_frame_x.v has no R twin of its plain runs SRr_run_pi_AJ_x / SRr_run_to_pi_AJ_x / SRr_run_pi_AJ_call_x (Sections
   a0 / e, over ajournal_x), so their R forms are restated here first (gn_*_AJ_xR), each with the strict proof over
   YCbqG.v's SRr_chain_AJxR.  The SRr_*_AJX0_xR forms conclude strict SRr over the R journal (a straight-line run moves
   no world); the SRrG_*_AJX0_xR forms conclude SRrG pa_segs R, from the SRr_* ones by SRrG_of_SRr_xR (SRr_SRrG at
   WLE_R, then SRrG_bind at the run's end state, whose world is the start's).  At R := wle each SRr_* form is the
   strict wrapper above. *)
Section pxxR.
Variable R : world pa_segs -> world pa_segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJR := (ajournal_xR pa_segs B PST ARx R).
Local Notation AJGR := (ajournal_gx_xR pa_segs B PST ARx R G 0 []).
(* a strict step whose end state is in the start's world, then an SRrG step from there *)
Lemma SRrG_of_SRr_xR : forall W c (Q : world pa_segs -> config -> Prop),
  SRr pa_segs W c (fun W' c' => W' = W /\ SRrG pa_segs R W c' Q) -> SRrG pa_segs R W c Q.
Proof.
  intros W c Q H.
  apply (SRrG_bind pa_segs R R_trans W c (fun W' c' => W' = W /\ SRrG pa_segs R W c' Q) Q).
  - exact (SRr_SRrG pa_segs R WLE_R W c _ H).
  - intros W' c' _ (-> & H'). exact H'.
Qed.
(* W_frame_x.v:212 SRr_run_pi_AJ_x over the journal at R (local twin, gone-prefixed: W_frame_x has no R twin) *)
Lemma gn_SRr_run_pi_AJ_xR : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_runN_pi pl_tpi n ss = (ss', st) -> pi_plain_stop st ->
  AJR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok_pi pa_segs pa_val E ss' (restrict (w_H W) ms') ->
    AJR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  unfold sym_runN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
  destruct (YP0d.sym_run_pi_sound wsym pa_segs (clookup pa_tbl) pa_val pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM
    A_LIM_text pl_lim _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
  eapply (SRr_chain_AJxR pa_segs B PST ARx LAWS pa_segs_low pa_wx W E (abs_ss pa_val ss) (abs_ss pa_val ss') ms msr');
  [ exact Hms | destruct st; cbn [prun_post] in HP; first [exact HP | destruct Hst] | destruct ss; exact Hfr | exact HJ
  | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
(* W_frame_x.v:230 SRr_run_to_pi_AJ_x over the journal at R (local twin) *)
Lemma gn_SRr_run_to_pi_AJ_xR : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi pl_tpi n stop ss = (ss', st) -> pi_plain_stop st ->
  AJR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok_pi pa_segs pa_val E ss' (restrict (w_H W) ms') ->
    AJR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  unfold sym_run_toN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
  destruct (YP0d.sym_run_to_pi_sound wsym pa_segs (clookup pa_tbl) pa_val pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM
    A_LIM_text pl_lim _ _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
  eapply (SRr_chain_AJxR pa_segs B PST ARx LAWS pa_segs_low pa_wx W E (abs_ss pa_val ss) (abs_ss pa_val ss') ms msr');
  [ exact Hms | destruct st; cbn [prun_post] in HP; first [exact HP | destruct Hst] | destruct ss; exact Hfr | exact HJ
  | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
(* W_frame_x.v:641 SRr_run_pi_AJ_call_x over the journal at R (local twin) *)
Lemma gn_SRr_run_pi_AJ_call_xR : forall W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_runN_pi pl_tpi n ss = (ss', PRS_call s) ->
  AJR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok pa_segs E (setpc ss' (pa_sigma s)) (restrict (w_H W) ms') ->
    AJR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun HJ Hwr Hk.
  unfold sym_runN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
  destruct (YP0d.sym_run_pi_sound wsym pa_segs (clookup pa_tbl) pa_val pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM
    A_LIM_text pl_lim _ E ss ss' (PRS_call s) _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
  cbn [YP0d.prun_post] in HP.
  eapply (SRr_chain_AJxR pa_segs B PST ARx LAWS pa_segs_low pa_wx W E (abs_ss pa_val ss) (setpc ss' (pa_sigma s)) ms msr');
  [ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
(* SRr_run_to_pi_AJX0_x over the journal at R *)
Lemma SRr_run_to_pi_AJX0_xR : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
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
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (gn_SRr_run_to_pi_AJ_xR W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack_xR pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
(* SRr_run_pi_AJX0_call_x over the journal at R *)
Lemma SRr_run_pi_AJX0_call_xR : forall W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
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
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (gn_SRr_run_pi_AJ_call_xR W n E ss ss' s ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack_xR pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
(* SRr_run_pi_AJX0_x over the journal at R *)
Lemma SRr_run_pi_AJX0_xR : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
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
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (gn_SRr_run_pi_AJ_xR W n E ss ss' st ms STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k Q
    HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack_xR pa_segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') _ k memS
    H0 H1); [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
(* the three at SRrG pa_segs R: the same premises, the continuation and the conclusion at SRrG *)
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
    SRrG pa_segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRrG pa_segs R W (mkCfg ms mdc) Q.
Proof.
  intros W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  apply SRrG_of_SRr_xR.
  apply (SRr_run_to_pi_AJX0_xR W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k _
    HE HS Hrun Hst HJ Hwr).
  intros ms' mat' H1 H2 H3 H4 H5. apply SRr_ret. exact (conj eq_refl (Hk ms' mat' H1 H2 H3 H4 H5)).
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
    SRrG pa_segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRrG pa_segs R W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun HJ Hwr Hk.
  apply SRrG_of_SRr_xR.
  apply (SRr_run_pi_AJX0_call_xR W n E ss ss' s ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k _
    HE HS Hrun HJ Hwr).
  intros ms' mat' H1 H2 H3 H4 H5. apply SRr_ret. exact (conj eq_refl (Hk ms' mat' H1 H2 H3 H4 H5)).
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
    SRrG pa_segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRrG pa_segs R W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  apply SRrG_of_SRr_xR.
  apply (SRr_run_pi_AJX0_xR W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k _
    HE HS Hrun Hst HJ Hwr).
  intros ms' mat' H1 H2 H3 H4 H5. apply SRr_ret. exact (conj eq_refl (Hk ms' mat' H1 H2 H3 H4 H5)).
Qed.
End pxxR.
End pxx.

Section gx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* cut_x's Section w header, the part ARM_gone's cut points and phases read *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* the walk at the empty ghost list (cut_x's HP0): AR0 is ARx at [], AJ0 the journal at G with both ghost lists [],
   LFB0 the entry's lf_base_x at [] *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* _gone_base.v's AR-free names that take this Section's variables *)
Local Notation gn_kregs := (W_LLVMFuzzerTestOneInput_gone_base.gn_kregs B).
Local Notation gdone := (W_LLVMFuzzerTestOneInput_gone_base.gdone RINV).
Local Notation gn_tie := (W_LLVMFuzzerTestOneInput_gone_base.gn_tie B).
Local Notation gn_cst := (W_LLVMFuzzerTestOneInput_gone_base.gn_cst MT).
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

(* _gone_base.v:182 gn_nums *)
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
  split; [exact Hal|]. split; [unfold LLVMF_STK in *; lia|].
  split; [rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Happ|]. split; [exact Hfrs|exact HAR].
Qed.
(* _gone_base.v:211 gn_shent_in_block (the shadow law at Hp = [], whose no-head premise is vacuous) *)
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
(* _gone_base.v:237 gn_entryA *)
Lemma gn_entryA_x : forall (W : world segs) ly S mem md regs (more : bool) idv F tv,
  AR0 ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 26 = w64 SB -> getr regs 28 = w64 tv ->
  2 ^ 46 <= F -> F + 216 <= 2 ^ 47 -> F mod 32 = 0 -> awr W mem F 216 -> sv8 W mem (F + 32) 6129888 ->
  4096 <= tv <= 2 ^ 47 -> tv + 1 <= F -> 0 <= idv < 256 ->
  (more = true -> val_mem segs (arm W mem) tv 1 idv /\
     exists p n, In (p, n) (ablocks B ly S) /\ p <= tv /\ tv + 1 <= p + req_size n) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (gn_extraA idv))) (ss_gnA more)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_gone)) mem (seg_rom segs)))
  /\ sh_ok segs gn_Bx (gn_SHA more) (Eimg (Ereg regs (gn_extraA idv))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S mem md regs more idv F tv HAR R9 R26 R28 HF1 HF2 HF3 HFw HF32 Ht1 Ht2 Hid Hmore.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (gn_extraA idv))).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = SB) by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SB; lia).
  assert (U28 : bv_unsigned (ew E 28) = tv) by (rewrite (EE 28%nat 28%bv eq_refl), R28; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = idv) by (rewrite E32; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gnA. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + destruct more; vm_compute; reflexivity.
    + assert (RF : region_ok segs E (mrestrict (w_H W) mem) gn_frA).
      { unfold region_ok, gn_frA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; replace (F + o) with (F + o) by lia; apply HFw; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ F 32 8 (SLit 6129888) 6129888); [reflexivity | lia | lia | exact HF32]. }
      destruct more; [|constructor; [exact RF | constructor]].
      destruct (Hmore eq_refl) as (Hv & _).
      constructor; [exact RF|]. constructor; [|constructor].
      unfold region_ok, gn_inA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U28. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ tv 0 1 (SOff 32 0) idv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | rewrite Z.add_0_r; exact Hv].
    + apply pairwise_disjoint_of_extents. destruct more; unfold gn_regA, gn_frA, gn_inA, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U28;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [gn_factsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U26, U28, U32. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - destruct more; unfold sh_ok, gn_SHA; [|constructor].
    destruct (Hmore eq_refl) as (_ & p & n & Hin & Hp1 & Hp2).
    constructor; [|constructor].
    apply (gn_shent_in_block_x ly S W mem md E gn_Bx 28 tv p n 0 1 HAR Hin); try lia.
    + unfold gn_Bx, U. cbn [sv_denot]. rewrite U26, Z.add_0_r, unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite U28, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
Qed.

(* _gone_base.v:295 gn_tools, over the generic chain: the token runs W_journal_x's paj_run_x_x / paj_run_to_x_x (for
   W_kit_x's paj_run_tok_x / paj_run_to_tok_x), the plain runs this file's _x wrappers (for W_frame_x's paj_run_sh_x,
   paj_run_to_sh_x, paj_run_shc_x, psrr_branch_pi_x) *)
Ltac gn_tools_x :=
  pose (RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 []);
  pose (RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 []);
  pose (BR := paj_branch (PI := PB_fr));
  pose (RUNP := SRr_run_pi_AJX0_x B PST ARx LAWS G_fr);
  pose (RUNTOP := SRr_run_to_pi_AJX0_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr);
  pose (RUNC := SRr_run_pi_AJX0_call_x B PST ARx LAWS G_fr).

(* ---------------------------------------------------------------- the cut points, over the generic journal at [] *)
(* _gone_base.v:342 gcom *)
(* what every cut point inside the arm carries: the journal, the frame (fake shadow sh), the cursor slots, the input,
   the image views *)
Definition gcom_x (cx : lfcx) (kq : Z) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx sh (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (lf_F cx + 40) (c_p cx + kq) /\ sv8 W mem (lf_F cx + 144) (c_n cx - kq) /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  (* the fake frame's flag word (lcut's, _cut.v:347-350): its last 8 bytes hold its flag pointer, which the
     shutdown stores through; no step of this arm writes them *)
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos).
(* _gone_base.v:363 GJN *)
(* 0x846f0: s4 = &g_s[0], s5 = id; F+40 / F+144 hold the cursor *)
Definition GJN_x (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_join) regs mem md /\
    gcom_x cx (gn_kq cx m) fake_shadow fpos ly S W mem md kk /\
    amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\
    (* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)): the allocator's room invariant NP at the arm's state, from the
       cut's lcut_x through every allocator call's post to the latch *)
    NP S /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m).
(* _gone_base.v:624 gst *)
(* ================================================================== the arm's own states *)
(* what every state of the arm after the join carries: the journal, the frame (with the fake frame's shadow
   sh), the cursor slots, the input, the image views, the model and its blocks, and the room invariant NP (the room
   round: threaded through every allocator call's post, ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)) *)
Definition gst_x (cx : lfcx) (kq : Z) (m : lmod) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gcom_x cx kq sh fpos ly S W mem md kk /\
  amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\ NP S.
(* _gone_base.v:639 GL1 *)
(* 0x84738: the reads[] loop's head, q of the four slots done; a2 = q, t0 = 4, t1 = F + 192,
   s4 = &g_s[0], s5 = id; prefix[48] is unpoisoned and holds the prefix; at = 0 *)
Definition GL1_x (cx : lfcx) (t : Z) (m : lmod) (q : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_l1) regs mem md /\
    gst_x cx (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m) /\
    getr regs 12 = w64 (Z.of_nat q) /\ getr regs 5 = w64 4 /\ getr regs 6 = w64 (lf_F cx + 192) /\
    (* q = 4 is not a state of 0x84738: the latch 0x847fc leaves the loop for 0x84834 at k + 1 = 4, and
       the head would read &g_s[4].open, whose granule is g_s's redzone - poison, so `azs` is FALSE
       there and the instrumented check could not be decided (p2's reading, 2026-10-29) *)
    (q < 4)%nat /\
    (forall j, (j < q)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* _gone_base.v:655 GRG *)
(* 0x84834: the four reads[] are written; relay_instance_gone(id) is next (s5 = id) *)
Definition GRG_x (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_rig) regs mem md /\
    gst_x cx (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m) /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* _gone_base.v:670 GC1 *)
(* 0x84848: the check_no_loss_read loop's head, q slots done; s4 = F + 192 + 4q, s5 = &g_s[q], s6 = F + 208 *)
Definition GC1_x (cx : lfcx) (t : Z) (m m1 : lmod) (q : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_c1) regs mem md /\
    gst_x cx (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\
    getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\ getr regs 22 = w64 (lf_F cx + 208) /\
    (* 0x84848 is a do-while head (the body runs, then `bne s4,s6`), so q = 4 is not a state of it:
       at q = 4 the test s4 = s6 would already have left the loop (p4's reading, 2026-10-29) *)
    (q < 4)%nat /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* _gone_base.v:685 GT0 *)
(* 0x84864: the check_no_loss_read loop is done; the table-order loop is entered or skipped *)
Definition GT0_x (cx : lfcx) (t : Z) (m m1 : lmod)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_t0) regs mem md /\
    gst_x cx (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* _gone_base.v:694 GCSD *)
(* 0x8494c: the table-order loop is done; at = g_nout, and the model after the operation is mc *)
Definition GCSD_x (cx : lfcx) (t : Z) (m mc : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md /\
    gst_x cx (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
    LSx cx (t + 1) mc ly S /\ RINV cx (t + 1) mc /\ lm_k mc = gn_kq cx m /\
    0 <= gn_kq cx m <= c_n cx /\ 0 <= t < OPS_MAX /\
    sv8 W mem (lf_F cx + 208) (Z.of_nat (length (lm_O mc))) /\
    awr W mem (lf_F cx + 192) 16 /\
    getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
    getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (frame_addr ly 1 fpos + 32) /\
    getr regs 23 = w64 HI_G_NSRC /\ getr regs 26 = w64 SB /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t.

(* ---------------------------------------------------------------- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0)
   The cut points at a world relation R: the journal is ajournal_gx_xR .. R (the cut journal runs from the operation's
   entry, across earlier frees / reallocs); every other conjunct is the strict text.  gn_nums_xR is gn_nums_x over that
   journal (its proof reads no world relation).  At R := wle each text is its strict twin above by conversion
   (ajournal_gx_x_wle). *)
Section gxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* gn_nums_x over the journal at R *)
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
  split; [exact Hal|]. split; [unfold LLVMF_STK in *; lia|].
  split; [rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Happ|]. split; [exact Hfrs|exact HAR].
Qed.
(* gcom_x at R *)
Definition gcom_xR (cx : lfcx) (kq : Z) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx sh (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (lf_F cx + 40) (c_p cx + kq) /\ sv8 W mem (lf_F cx + 144) (c_n cx - kq) /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos).
(* GJN_x at R *)
Definition GJN_xR (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_join) regs mem md /\
    gcom_xR cx (gn_kq cx m) fake_shadow fpos ly S W mem md kk /\
    amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\
    NP S /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m).
(* gst_x at R *)
Definition gst_xR (cx : lfcx) (kq : Z) (m : lmod) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gcom_xR cx kq sh fpos ly S W mem md kk /\
  amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\ NP S.
(* GL1_x at R *)
Definition GL1_xR (cx : lfcx) (t : Z) (m : lmod) (q : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_l1) regs mem md /\
    gst_xR cx (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m) /\
    getr regs 12 = w64 (Z.of_nat q) /\ getr regs 5 = w64 4 /\ getr regs 6 = w64 (lf_F cx + 192) /\
    (q < 4)%nat /\
    (forall j, (j < q)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* GRG_x at R *)
Definition GRG_xR (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_rig) regs mem md /\
    gst_xR cx (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LSx cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m) /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* GC1_x at R *)
Definition GC1_xR (cx : lfcx) (t : Z) (m m1 : lmod) (q : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_c1) regs mem md /\
    gst_xR cx (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\
    getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\ getr regs 22 = w64 (lf_F cx + 208) /\
    (q < 4)%nat /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* GT0_x at R *)
Definition GT0_xR (cx : lfcx) (t : Z) (m m1 : lmod)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_t0) regs mem md /\
    gst_xR cx (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* GCSD_x at R *)
Definition GCSD_xR (cx : lfcx) (t : Z) (m mc : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md /\
    gst_xR cx (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
    LSx cx (t + 1) mc ly S /\ RINV cx (t + 1) mc /\ lm_k mc = gn_kq cx m /\
    0 <= gn_kq cx m <= c_n cx /\ 0 <= t < OPS_MAX /\
    sv8 W mem (lf_F cx + 208) (Z.of_nat (length (lm_O mc))) /\
    awr W mem (lf_F cx + 192) 16 /\
    getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
    getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (frame_addr ly 1 fpos + 32) /\
    getr regs 23 = w64 HI_G_NSRC /\ getr regs 26 = w64 SB /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t.
End gxR.
End gx.
