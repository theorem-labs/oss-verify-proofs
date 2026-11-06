(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the RI plug of the image-A top (lib/A/W_LLVMFuzzerTestOneInput_top_x.v).  top_x keeps
   RINV as a Section Variable; the instance file sets RINV := @ReplyRINV.fr_RINV rc and discharges top_x's RI_*
   hypotheses by the lemmas here, over lib/A/ReplyRINV.v.
   Each lemma topx_<name> below is top_x's `Hypothesis <name>` text, copied by script byte for byte, at
   RINV := @ReplyRINV.fr_RINV rc (the Local Notation below), with fx / rc as explicit binders (lib/A/ReplyATop.v's
   atop_RI_* form).  All 33 of top_x's RI rows:
   - 13 plain plugs by lib/A/ReplyRINV.v's _holds lemma (top_x's text is the _obl's): RI_head_nout, RI_head_skip,
     RI_add_none, RI_close, RI_eintr, RI_sendmax, RI_default, RI_src, RI_fds, RI_event_live, RI_rm_found,
     RI_rm_cnlr_eof, RI_rm_step.  The rm_* names top_x cites from W_LLVMFuzzerTestOneInput_remove.v are
     ReplyRINV.v's own copies, with the same bodies (convertible).
   - 3 premise-reorder adapters, from ReplyRINV.v's _fix rules (the same premises in another order): RI_add_pre and
     RI_add_open (the t bound after RINV here, first in the _fix_obl), RI_drain_step (here: RINV, t bound, the
     held / begin bound, then the rest; in the _fix_obl: t bound, RINV, ..., the held / begin bound last).  Proved
     as ReplyATop.v's atop_RI_add_pre: unshelve eapply, the _holds lemma's unused Section variables at any value.
   - 1 lf_base -> lf_base_x bridge: RI_pro.  top_x's RI_pro takes lf_base_x at ARX and the entry's Hp; ReplyRINV.v's
     RI_pro_obl takes the AR lf_base.  RI_pro_holds reads only lf_base's input-length range (the sixth conjunct,
     ReplyRINV.v RI_pro_core), which lf_base_x has at the same place, so the adapter takes it there and applies
     RI_pro_core.
   - 9 plain plugs by exact: lib/A/ReplyRINV_a3.v (commit a36da6bbe94) RI_write_skip, RI_write_push, RI_drain_skip,
     RI_pair, and RI_event_step through its RI_event_step_x (top_x's text, which names _event.v's ev_evt / ev_step);
     lib/A/ReplyRINV_a12.v (commit b81543f5533) RI_exit_slots, RI_rm_rr_pair; lib/A/ReplyRINV_gone.v (commit
     ea932c57613, its _plug lemmas) RI_gone_pairs, RI_gone_read.
   - 4 plain plugs by exact, at commit 3f40808c334's restated texts (the arm's premise added after
     ReplyRINV_a12.v's *_obl_false showed the old texts false): RI_exit_ends, RI_rm_cnl_pre, RI_rm_cshe_pre,
     RI_rm_csd, by ReplyRINV_a12.v's RI_*_holds (commit b962c9489d0).
   - 1 plain plug by exact: RI_rm_src (commit 250502f7048's row), by ReplyRINV.v's RI_rm_src_holds.
   - 2 plain plugs at a check instance of the meter and LS (Sections topxri_gone / topxri_gone_c: MT :=
     YCbp.ameter_triv, LSx := ReplyLS3.fr_LS3 TfibB / ReplyLS3c.fr_LS3c TfibB): RI_gone_step and RI_gone_end, by
     ReplyRINV_gone.v's RI_gone_step_plug(_c) / RI_gone_end_plug(_c) (commit 8473fd78f18; REQ5 inside).  These are
     NOT the top's plugs: the top's LS is fr_LS3cp B /\ fr_OUT OM /\ fr_ENT B, closed in the top step.
   This file goes in with ReplyATop.v's LS3 switch, not before. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_addI.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x W_contract_x W_check_bounded W_palib_fr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_top.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* the start-up table's facts (ts_owned, ts_errno, Tfib_owned_static), as addI uses them *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0l AF0m.
(* the AR arm files for the model functions the RI_* / LS_* rules name (sm_*, ad_*, wr_*, WR_MMAX); Require Import
   is not transitive through _top.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_write.
(* SEG_PRO: the AR file for pro_m and its model texts, and SmallX's conversion, with the frame kit its facts name
   (W_frame's PALibF, W_frame_x's astack_malloc_pres_x / frame_flag_lawP_x, YGcallx's laws, YG01cf / YG05cf's Wf_cf and
   stack_malloc progress); imported BEFORE W_op_add so that W_op_add's oa_first / oa_cost / oa_spec_g_x (the names
   below) are not shadowed by _pro.v's / _pro_x.v's copies *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_pro W_LLVMFuzzerTestOneInput_pro_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_latch_x W_LLVMFuzzerTestOneInput_small_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_op_add W_list_push ACk0 W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_write_x.
(* ARM_event: the AR file for et_GL / et_GRE / ev_* (Require Import is not transitive), and SmallX's conversion *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_event W_LLVMFuzzerTestOneInput_event_x.
(* SEG_HEAD: the AR file for hd_kb / hd_k', and HeadX's conversion *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_head_x.
(* ARM_drain: Prog's CheckRep (texts / count_begin / set_exp_held, which its rules name), the AR file for the drain
   model (dr_at_op / dr_pick / dr_step / dr_cost ..., DR_GK), and AddX's conversion; last, and they define none of
   the names above (checked: their only clashes are Local notations) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_drain W_LLVMFuzzerTestOneInput_drain_x.
(* SEG_EXIT: the AR file (its model functions lx_* / xr_GM, cited qualified below), LatchX's conversion, the kit's
   YE01_x.v that conversion cites, _Gx.v's XR_HGM witness, AD1u.v's tfib_AIL and YG0tcf.v's stack_free law; Require
   without Import, so none of their names shadows a name the text above uses *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_LLVMFuzzerTestOneInput_exit W_LLVMFuzzerTestOneInput_exit_x YE01_x W_LLVMFuzzerTestOneInput_Gx AD1u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf.
(* ARM_remove: the AR file (its model functions rm_*, cited qualified below), WriteX's conversion, the .str.2 shadow
   lemma over ARx and W6's rg_place assembly; Require without Import, as SEG_EXIT's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_remove_x W_shadow_pin_x W_rg_place.
(* ARM_gone: the AR files (gone_base's model texts GN_*, cited qualified below) and SmallX's conversion; Require
   without Import, as SEG_EXIT's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_sites W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone W_LLVMFuzzerTestOneInput_gone_x.
(* C1 (a Theorem Labs lane's 922a710cda0; relay_event re-proved by AddX's C3 88557c15170): relay_add's, relay_event's and
   relay_finish's _x proofs, which build RA_x / RE_x / RF_x below; Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_relay_add W_relay_event W_relay_finish_h.
(* W3's check_shape_done and check_no_loss_read _x walks, which build CSD_x / CNLR_x below; Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_check_shape_done W_check_no_loss_read.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* the ASan image's sink instance, the one cut_x's journals and the arm files name (write_x.v:60) *)
#[local] Existing Instance AE2k.tfib_sink_head.

(* the obligations' file and top_x (Require without Import: ReplyRINV's rm_* / ev_* copies and top_x's names
   would shadow the names the texts above use) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyRINV W_LLVMFuzzerTestOneInput_top_x.
(* the RI rows' other files *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyRINV_a3 ReplyRINV_a12 ReplyRINV_gone.
(* GN_RI_step's instance: the trivial meter and the LS invariants *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLS3 ReplyLS3c.

Section topxri.
Context (fx : YK11.FPState) (rc : YM05.RunCeil).
(* top_x's Section variables that RI_pro's text names, under top_x's names *)
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
(* top_x's notations and instance that RI_pro's text names *)
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Local Notation G := (G_fr_c TfibB).
Local Notation ARX := W_LLVMFuzzerTestOneInput_top_x.ARX.
(* top_x's RINV at the instance's invariant *)
Local Notation RINV := (@ReplyRINV.fr_RINV rc).
(* a _holds lemma's Section variables its statement does not use (XM_LIB, RLO, MMAX, ...): any value *)
Local Ltac ri_fill :=
  first [ exact (fun z : Z => z) | exact 0 | exact (fun _ _ _ _ _ => True) | exact (fun _ : astate => True)
        | exact (@nil (Z * Z)) | exact TfibB | exact YCbp.ameter_triv ].
(* top_x.v:378 RI_head_nout: plain plug, ReplyRINV.RI_head_nout_holds *)
Lemma topx_RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (lm_clear_O m).
Proof. exact ReplyRINV.RI_head_nout_holds. Qed.
(* top_x.v:380 RI_head_skip: plain plug, ReplyRINV.RI_head_skip_holds *)
Lemma topx_RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
Proof. exact ReplyRINV.RI_head_skip_holds. Qed.
(* top_x.v:246 RI_add_pre: premise-reorder adapter, ReplyRINV.RI_add_pre_fix_holds *)
Lemma topx_RI_add_pre : forall cx t m,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
Proof.
  intros. unshelve eapply ReplyRINV.RI_add_pre_fix_holds; try eassumption; ri_fill.
Qed.
(* top_x.v:249 RI_add_open: premise-reorder adapter, ReplyRINV.RI_add_open_fix_holds *)
Lemma topx_RI_add_open : forall cx t m i q pj ev,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (ad_open m i q pj ev).
Proof.
  intros. unshelve eapply ReplyRINV.RI_add_open_fix_holds; try eassumption; ri_fill.
Qed.
(* top_x.v:253 RI_add_none: plain plug, ReplyRINV.RI_add_none_holds *)
Lemma topx_RI_add_none : forall cx t m,
  RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None -> RINV cx (t + 1) (ad_none m).
Proof. exact ReplyRINV.RI_add_none_holds. Qed.
(* top_x.v:209 RI_close: plain plug, ReplyRINV.RI_close_holds *)
Lemma topx_RI_close : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_close cx m i).
Proof. exact ReplyRINV.RI_close_holds. Qed.
(* top_x.v:212 RI_eintr: plain plug, ReplyRINV.RI_eintr_holds *)
Lemma topx_RI_eintr : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_eintr cx m i).
Proof. exact ReplyRINV.RI_eintr_holds. Qed.
(* top_x.v:215 RI_sendmax: plain plug, ReplyRINV.RI_sendmax_holds *)
Lemma topx_RI_sendmax : forall cx t m, RINV cx t m ->
  RINV cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
Proof. exact ReplyRINV.RI_sendmax_holds. Qed.
(* top_x.v:217 RI_default: plain plug, ReplyRINV.RI_default_holds *)
Lemma topx_RI_default : forall cx t m, RINV cx t m -> RINV cx (t + 1) (sm_default cx m (sm_dg cx m)).
Proof. exact ReplyRINV.RI_default_holds. Qed.
(* top_x.v:485 RI_src: plain plug, ReplyRINV.RI_src_holds *)
Lemma topx_RI_src : forall cx t m si h,
  RINV cx t m -> dr_pick cx m si h ->
  hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31.
Proof. exact ReplyRINV.RI_src_holds. Qed.
(* top_x.v:489 RI_fds: plain plug, ReplyRINV.RI_fds_holds *)
Lemma topx_RI_fds : forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
Proof. exact ReplyRINV.RI_fds_holds. Qed.
(* top_x.v:447 RI_drain_step: premise-reorder adapter, ReplyRINV.RI_drain_step_fix_holds *)
Lemma topx_RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  RINV cx t m -> 0 <= t < OPS_MAX ->
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
  dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
Proof.
  intros cx t m si h j e' h' c' O' cap' out' ev' LB E' H' HRI Ht Hcb Hat Hpick Hj Hfdj Heof Hok.
  (* the rule at its own premise order, then the premises in it (eassumption alone matches h with h') *)
  assert (Hfix : ReplyRINV.RI_drain_step_fix_obl) by (unshelve eapply ReplyRINV.RI_drain_step_fix_holds; ri_fill).
  exact (Hfix cx t m si h j e' h' c' O' cap' out' ev' LB E' H' Ht HRI Hat Hpick Hj Hfdj Heof Hok Hcb).
Qed.
(* top_x.v:402 RI_pro: lf_base -> lf_base_x bridge, ReplyRINV.RI_pro_core (the core of RI_pro_holds) at
   lf_base_x's input-length range *)
Lemma topx_RI_pro : forall cx Hp q T' pj c O cap out,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  RINV cx 0 (pro_m q T' pj c O cap out).
Proof.
  intros cx Hp q T' pj c O cap out HB _ Hcl Hbr Hdd _.
  apply (ReplyRINV.RI_pro_core cx q T' pj c O cap out); [| exact Hcl | exact Hbr | exact Hdd].
  destruct HB as (_ & _ & _ & _ & _ & Hn & _). destruct Hn as [(Hz & _) | (Hn & _)]; lia.
Qed.
(* top_x.v:318 RI_event_live: plain plug, ReplyRINV.RI_event_live_holds *)
Lemma topx_RI_event_live : forall cx t m,
  RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).
Proof. exact ReplyRINV.RI_event_live_holds. Qed.
(* top_x.v:688 RI_rm_found: plain plug, ReplyRINV.RI_rm_found_holds *)
Lemma topx_RI_rm_found : forall cx t m si h,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 4 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_remove.rm_kb cx m) = Some si -> nth si (lm_hs m) None = Some h ->
  exists j, (j < length (lm_es m))%nat /\ re_fd (W_LLVMFuzzerTestOneInput_remove.rm_ent m j) = hs_fd h.
Proof. exact ReplyRINV.RI_rm_found_holds. Qed.
(* top_x.v:734 RI_rm_cnlr_eof: plain plug, ReplyRINV.RI_rm_cnlr_eof_holds *)
Lemma topx_RI_rm_cnlr_eof : forall cx t m si h j0,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> 0 <= re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) <= 1.
Proof. exact ReplyRINV.RI_rm_cnlr_eof_holds. Qed.
(* top_x.v:757 RI_rm_step: plain plug, ReplyRINV.RI_rm_step_holds *)
Lemma topx_RI_rm_step : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2).
Proof. exact ReplyRINV.RI_rm_step_holds. Qed.
(* top_x.v:269 RI_write_skip: plain plug, ReplyRINV_a3.RI_write_skip_holds *)
Lemma topx_RI_write_skip : forall cx t m,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
  RINV cx (t + 1) (wr_skip m (wr_k2 cx m)).
Proof. exact ReplyRINV_a3.RI_write_skip_holds. Qed.
(* top_x.v:275 RI_write_push: plain plug, ReplyRINV_a3.RI_write_push_holds *)
Lemma topx_RI_write_push : forall cx t m si h l' d ev,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev).
Proof. exact ReplyRINV_a3.RI_write_push_holds. Qed.
(* top_x.v:322 RI_event_step: plain plug, ReplyRINV_a3.RI_event_step_x *)
Lemma topx_RI_event_step : forall cx t m e v out',
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  RINV cx (t + 1) (ev_step cx m e v out').
Proof. exact ReplyRINV_a3.RI_event_step_x. Qed.
(* top_x.v:441 RI_drain_skip: plain plug, ReplyRINV_a3.RI_drain_skip_holds *)
Lemma topx_RI_drain_skip : forall cx t m si h,
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
Proof. exact ReplyRINV_a3.RI_drain_skip_holds. Qed.
(* top_x.v:493 RI_pair: plain plug, ReplyRINV_a3.RI_pair_holds *)
Lemma topx_RI_pair : forall cx t m si h j,
  RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
  (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
  length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat.
Proof. exact ReplyRINV_a3.RI_pair_holds. Qed.
(* top_x.v:638 RI_exit_slots: plain plug, ReplyRINV_a12.RI_exit_slots_holds *)
Lemma topx_RI_exit_slots : forall cx t m, RINV cx t m ->
  forall j, (j < 4)%nat -> W_LLVMFuzzerTestOneInput_exit.lx_ends_slot_ok (nth j (lm_hs m) None).
Proof. exact ReplyRINV_a12.RI_exit_slots_holds. Qed.
(* top_x.v:692 RI_rm_rr_pair: plain plug, ReplyRINV_a12.RI_rm_rr_pair_holds *)
Lemma topx_RI_rm_rr_pair : forall cx t m si h j0,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
  re_skip (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = hs_overlong h /\ (re_skip (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 -> bzs (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) = bzs (hs_W h)).
Proof. exact ReplyRINV_a12.RI_rm_rr_pair_holds. Qed.
(* top_x.v:819 RI_gone_pairs: plain plug, ReplyRINV_gone.RI_gone_pairs_plug *)
Lemma topx_RI_gone_pairs : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_pairs RINV.
Proof. exact ReplyRINV_gone.RI_gone_pairs_plug. Qed.
(* top_x.v:818 RI_gone_read: plain plug, ReplyRINV_gone.RI_gone_read_plug *)
Lemma topx_RI_gone_read : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_read RINV.
Proof. exact ReplyRINV_gone.RI_gone_read_plug. Qed.
(* top_x.v:640 RI_exit_ends (commit 3f40808c334's restated text): plain plug, ReplyRINV_a12.RI_exit_ends_holds *)
Lemma topx_RI_exit_ends : forall cx t m, RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  W_LLVMFuzzerTestOneInput_exit.lx_ends_run (lm_gn m) (W_LLVMFuzzerTestOneInput_exit.lx_rf_O m)
    (W_LLVMFuzzerTestOneInput_exit.lx_norder m) (W_LLVMFuzzerTestOneInput_exit.lx_ord m) (lm_hs m) 0 =
  Some (Z.of_nat (length (W_LLVMFuzzerTestOneInput_exit.lx_rf_O m))).
Proof. exact ReplyRINV_a12.RI_exit_ends_holds. Qed.
(* top_x.v:716 RI_rm_cnl_pre (commit 3f40808c334's restated text): plain plug, ReplyRINV_a12.RI_rm_cnl_pre_holds *)
Lemma topx_RI_rm_cnl_pre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
Proof. exact ReplyRINV_a12.RI_rm_cnl_pre_holds. Qed.
(* top_x.v:736 RI_rm_cshe_pre (commit 3f40808c334's restated text): plain plug, ReplyRINV_a12.RI_rm_cshe_pre_holds *)
Lemma topx_RI_rm_cshe_pre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H') ->
  W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Proof. exact ReplyRINV_a12.RI_rm_cshe_pre_holds. Qed.
(* top_x.v:747 RI_rm_csd (commit 3f40808c334's restated text): plain plug, ReplyRINV_a12.RI_rm_csd_holds *)
Lemma topx_RI_rm_csd : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  0 <= lm_gn m <= 1 ->
  W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1 + cc = Z.of_nat (length O2).
Proof. exact ReplyRINV_a12.RI_rm_csd_holds. Qed.
(* top_x.v:697 RI_rm_src (commit 250502f7048's row): plain plug, ReplyRINV.RI_rm_src_holds *)
Lemma topx_RI_rm_src : forall cx t m si h j0,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> hl_recs (hs_expected h) = [].
Proof. exact ReplyRINV.RI_rm_src_holds. Qed.
End topxri.

(* lib/A/W_LLVMFuzzerTestOneInput_top_x.v:836 RI_gone_step at MT := YCbp.ameter_triv and LSx := ReplyLS3.fr_LS3 TfibB (this check's LS instance, not
   the top's): plain plug, ReplyRINV_gone.RI_gone_step_plug (commit 8473fd78f18) *)
Section topxri_gone.
Context (fx : YK11.FPState) (rc : YM05.RunCeil).
Local Notation RINV := (@ReplyRINV.fr_RINV rc).
Local Notation MT := YCbp.ameter_triv.
Local Notation LSx := (ReplyLS3.fr_LS3 TfibB).
Lemma topx_RI_gone_step : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step TfibB MT LSx RINV CfParamsReply.fr_MMAX.
Proof. exact (ReplyRINV_gone.RI_gone_step_plug TfibB). Qed.
(* top_x.v:837 RI_gone_end at the same MT / LSx: plain plug, ReplyRINV_gone.RI_gone_end_plug
   (commit 8473fd78f18; REQ5 is derived inside it) *)
Lemma topx_RI_gone_end : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end TfibB MT LSx RINV.
Proof. exact (ReplyRINV_gone.RI_gone_end_plug TfibB). Qed.
End topxri_gone.

(* lib/A/W_LLVMFuzzerTestOneInput_top_x.v:836 RI_gone_step at MT := YCbp.ameter_triv and LSx := ReplyLS3c.fr_LS3c TfibB (this check's LS instance, not
   the top's): plain plug, ReplyRINV_gone.RI_gone_step_plug_c (commit 8473fd78f18) *)
Section topxri_gone_c.
Context (fx : YK11.FPState) (rc : YM05.RunCeil).
Local Notation RINV := (@ReplyRINV.fr_RINV rc).
Local Notation MT := YCbp.ameter_triv.
Local Notation LSx := (ReplyLS3c.fr_LS3c TfibB).
Lemma topx_RI_gone_step_c : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step TfibB MT LSx RINV CfParamsReply.fr_MMAX.
Proof. exact (ReplyRINV_gone.RI_gone_step_plug_c TfibB). Qed.
(* top_x.v:837 RI_gone_end at the same MT / LSx: plain plug, ReplyRINV_gone.RI_gone_end_plug_c
   (commit 8473fd78f18; REQ5 is derived inside it) *)
Lemma topx_RI_gone_end_c : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end TfibB MT LSx RINV.
Proof. exact (ReplyRINV_gone.RI_gone_end_plug_c TfibB). Qed.
End topxri_gone_c.
