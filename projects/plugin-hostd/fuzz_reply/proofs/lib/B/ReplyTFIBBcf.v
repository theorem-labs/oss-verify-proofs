(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/AD1pcf.v, with its module paths and module names changed; 114 of its 150 lines of code are new or changed and 210 lines of the source are left out. *)
(* Made by a Theorem Labs lane (2026-10-29, a Theorem Labs lane's DRIVER_CF_B) as the image-B twin of lib/A/ReplyTFIBcf.v
   (commit 46f1762ad5a): TFIB_B_T from fuzz_reply's cf program interface at route R, fr_lib_contract_drvR
   (lib/B/YD1w_cf.v), over the B cf driver closure (lib/B/YD1qcf.v tfib_srealizesX and the cf site files). The
   image-B values are lib/B/ReplyTFIBBParts.v's: the read-only range 0x9d9f0 .. 0x9ec48 (.data.rel.ro start .. .got
   end), the three fprintf format addresses 0x1d745 / 0x1d75a / 0x15886, AsanUbsan.M.init_pc. Section hypotheses as
   A's (NP and its three laws, the meter MT with MT_PRE, the run count NS with NS_MO / XN_BND / nsec_malloc_cf /
   nsec_free_cf / NS_START (a Theorem Labs lane ddf9cf4d2f7 and 458a2b5da2a, KF-COUNT #7), TLLVMF, AMALLOC / AFREE) except HCOVD:
   the covered range is discharged in lib/B/YD1pcf.v by a Theorem Labs lane's YStkCov.tfib_handoff_stk_up_cov; A's _triv
   corollary is not here (B has none); A's commentary follows. *)
(* The cf driver's top for plugin-hostd/fuzz_reply.asan-ubsan: TFIB_B_T (lib/A/ReplyTFIB.v) from fuzz_reply's cf program
   interface at route R, fr_lib_contract_drvR (lib/B/YD1w_cf.v) at the world relation wle' tfibsegs RZ_cf (the library
   run can free), the form B's ENTRY (the twin of ReplyATop.v's DRIVER_CF) consumes it in.
   The same shape as lib/B/ReplyTFIBBParts.v (the donor's TFIB_B_T from its program contract tfib_lib_contract_x), with
   the second allocator instance in place of cgif's AR:
   - the driver is B/YD1qcf.v tfib_srealizesX (the cf copies of the donor's driver closure: AR switched to ARcf at the
     start-up hand-off by Reusable/YGcfNilInit.v ARcf_nil_init; no event arithmetic);
   - the sites are SitesCf's cf site proofs (B/YD1kcf, YD1lcf, YD1ocf, YD1jcf) over the interceptor walks made generic
     in the allocator invariant, and the read check and memcpy intrinsic are B/YD2mcf.v;
   - LIBROOM is YD1mcf.LIBROOM_fr (preset's LIB_ROOM abudget_cf (2 ^ 33)), discharged inside the driver;
   - NAMED HYPOTHESES, each with its owner: TLLVMF, the program interface at every run ceiling and FP state (W8's ARcf
     instance through the bridge, B's ENTRY (the twin of ReplyATop.v's DRIVER_CF) premise); NP with its three laws, the non-primary room
     between allocator calls (the cf instance's room_live_cf, a Theorem Labs lane, Reusable/YGcfRoomLive.v room_live_cf_init_gen /
     room_live_cf_step_gen / room_live_room_k, once relocated); AMALLOC / AFREE, the cf allocator's realizers
     (a Theorem Labs lane; AFREE at the primed contract YG0dcfR.afree_realizes_cf_rh); the hull admission and the RELRO bytes
     are drv_pre's own conjuncts, from HULL_NS and from RO / HSTART_ARO (part 3c: no memnorm).
   Generic in the instance's CfImg / CfParams; the B top instantiates lib.B.CfImgB.CfImg_B and lib.A.CfParamsReply.CfParams_reply.  XR0 /
   REPLYB_RO_LO / REPLYB_RO_HI have lib/B/ReplyTFIBBParts.v's bodies, so the instantiation is by conversion. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YA02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp YG0lawscf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn YB1v YF0m YCeg YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG0dcf YG0d2cf YGcfNames YG01cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
YCfn_cf YD1vcf YD1wcf YD1xcf YD1icf YD1w_cf YD1mcf YD1kcf YD1lcf YD1ocf YD1jcf YD2mcf YD1pcf YD1qcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyStartWitB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Open Scope Z_scope.
(* The constants of B's ENTRY (the twin of ReplyATop.v's DRIVER_CF) premise, with A/ReplyTFIBParts.v's bodies (stated here rather than imported:
   ReplyTFIBParts.v Requires the donor's whole AR driver and allocator closure, which this top does not use). *)
Definition XR0 : Z -> Z := fun _ => 0.
Definition REPLYB_RO_LO : Z := 0x9d9f0.
Definition REPLYB_RO_HI : Z := 0x9ec48.
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
Section b.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
(* the non-primary room and its three laws (B/YD1w_cf.v) *)
Variable NP : astate -> Prop.
Hypothesis NPI : iface_room_np_init NP.
Hypothesis NPS : iface_room_np_step NP.
Hypothesis NPT : iface_room_np_tail NP.
(* the meter and its per-call budgets (a Theorem Labs lane's 2026-10-29 20:10Z ruling: the live-state meter, W8Add's
   lib/A/ReplyMeter.v), with the meter's room at each call (B/YD1mcf.v MT_PRE) *)
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
(* the run count (at MT_sec: a Theorem Labs lane's nsec_cf), its run bound and its per-call step bound (B/YD1mcf.v; KF-COUNT #7) *)
Variables (NS : astate -> Z) (NRUN XNMAX : Z).
Hypothesis MT_PRE : forall S n, Wf_cf (as_universe TfibB) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> NP S -> NS S + XNMAX <= NRUN ->
  0 <= n < 2 ^ 26 -> mo_ok MT S (XM_LIB n).
(* the meter's step bounds the run count's step and one call's step is at most XNMAX (B/YD1mcf.v); the count's step
   at the driver's own mallocs and frees, at the text of B/CfRBridgeRulesB.v nsec_malloc_cf / nsec_free_cf with NS for
   nsec_cf; and the count's room at the start state init_state for the driver's mallocs before the loop's first call
   and the loop's at most 4 calls (B/YD1pcf.v, B/YD2dcf.v NS_START, whose comment names the mallocs) *)
Hypothesis NS_MO : forall S S' n, mo_le MT S S' (XN_LIB n) -> NS S' <= NS S + XN_LIB n.
Hypothesis XN_BND : forall n, 0 <= n < 2 ^ 26 -> 0 <= XN_LIB n <= XNMAX.
Hypothesis HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S.
Hypothesis nsec_malloc_cf : forall n tr s,
  YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s).
Hypothesis NS_START : NS init_state + 12 + 4 * XNMAX <= NRUN.
(* the program interface, at every run ceiling and FP state, at the world relation wle' tfibsegs RZ_cf (route R: the
   library run can free, so cut_x's contract at R gives the continuation only that relation; B/YD1pcf.v Rcf) *)
Hypothesis TLLVMF : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fr_lib_contract_drvR fx rc checksum_shape ci cp TfibB MT XM_LIB XN_LIB REPLYB_RO_LO REPLYB_RO_HI LIBROOM_fr NP
    (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
(* the cf allocator's malloc and free; the free at the primed contract (route R, lib/B/YG0dcfR.v; free(NULL) inside
   it), the text ReplyAllocTargetsB.afree_target_replyB states (primed at a Theorem Labs lane's 7c91d0cac15) *)
Hypothesis AMALLOC : forall (rc : YM05.RunCeil), amalloc_realizes_cf tfibsegs TfibB.
Hypothesis AFREE : forall (rc : YM05.RunCeil), YG0dcfR.afree_realizes_cf_rh tfibsegs TfibB.
(* field rounds 2 and 3: the cf driver's start witnesses (at the start-up hand-off, B/ReplyStartWitB.v), the unit's three
   image rows and the pf cells' ownership (B/YD1pcf.v HSTART / HSTART_PF / HROWS / HPFO), at every run ceiling; the
   instance supplies them (B/ReplyStartWitB.v start_cells_B / start_pf_B, B/ReplyImgRowsB.v exh_off_B / errb_obj_owned_B,
   B/ReplyImg_pfrowsB.v errb_ial_apart_reply_B / pf_cells_owned_reply_B) *)
Hypothesis HSTART : forall (rc : YM05.RunCeil), ReplyStartWitB.start_cells_ho_t TfibB.
Hypothesis HSTART_PF : forall (rc : YM05.RunCeil), ReplyStartWitB.start_pf_ho_t TfibB.
Hypothesis HROWS : YGcfImgRows.EXH_OFF_t /\ YG0ncf.errb_obj_owned_t TfibB /\ YG0ncf.errb_ial_apart_t TfibB.
Hypothesis HPFO : YG0ncf.pf_cells_owned_t TfibB.
(* field round 3 (Part A): drv_pre's RELRO bytes: the image fact (B/YD1vcf.v relro_ok; at CfImg_B
   ReplyRelroGeoB.relro_seg_reply_B and cf_relro_hi = 0x9f000 <= 0xa24f8) and their start at main's hand-off (B/YD1pcf.v
   start_aro_ho_t; at CfImg_B B/ReplyKeptAroStartB.v arodata_ho_B) *)
Hypothesis RO : relro_ok.
Hypothesis HSTART_ARO : start_aro_ho_t TfibB.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
Let AICPY : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B)). Proof. eapply tfib_AICPY_cf; eassumption. Defined.
Let ARDCHK : YD1icf.aread_check_stmt B. Proof. eapply tfib_ARDCHK_cf; eassumption. Defined.
Let LIBX : fr_lib_contract_drv_allR B MT XM_LIB XN_LIB REPLYB_RO_LO REPLYB_RO_HI LIBROOM_fr NP
  (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) := fun fx => TLLVMF rc fx.
Let RO_IN : forall a, REPLYB_RO_LO <= a < REPLYB_RO_HI -> in_ro_tfa a := fun a H => or_intror H.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1kcf.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst. Proof. eapply tfib_printf_first; eassumption. Defined.
Let PFN : printf_next_tfa B xst. Proof. eapply tfib_printf_next; eassumption. Defined.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1kcf.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est. Proof. eapply tfib_fwrite_site; eassumption. Defined.
Let RFS : refused_site_tfa B est. Proof. eapply tfib_refused_site; eassumption. Defined.
Let FPO : fprintf_s_site_tfa B est 0x1d745 (strB "cli: cannot open "%string) nlB. Proof. eapply tfib_fprintf_open_site; eassumption. Defined.
Let FPR : fprintf_s_site_tfa B est 0x1d75a (strB "cli: read error on "%string) nlB. Proof. eapply tfib_fprintf_rderr_site; eassumption. Defined.
Let FPU : fprintf_s_site_tfa B est 0x15886 (strB "usage: "%string) (strB " INPUT"%string ++ nlB). Proof. eapply tfib_fprintf_usage_site; eassumption. Defined.
Let EXS : exit_site_tfa B est xst. Proof. eapply tfib_exit_site; eassumption. Defined.
Lemma replyb_srealizesX_rc_cf : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB NP NPI NPS NPT (AMALLOC rc) (AFREE rc) AICPY ARDCHK MT XM_LIB XN_LIB REPLYB_RO_LO REPLYB_RO_HI
  NS NRUN XNMAX MT_PRE NS_MO XN_BND HULL_NS nsec_malloc_cf nsec_free_cf NS_START RO_IN RO LIBX
  xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS (HSTART rc) HSTART_ARO (HSTART_PF rc) HROWS HPFO
  sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem replyb_srealizesX_top_cf : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@replyb_srealizesX_rc_cf (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp) target_alloc_limit) sp rdraw brk mb inp
  Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
(* TFIB_B_T from the cf program interface, the meter's room at each call, the run count's laws, NP's laws, the cf
   allocator's realizers and drv_pre's RELRO facts *)
Theorem replyb_TFIB_B_T_of_cf : TFIB_B_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (replyb_srealizesX_top_cf sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.

(* NP at the cf instance's non-primary room room_live_cf (Reusable/YGcfRoomLive.v, a Theorem Labs lane, carried by RelocA-2):
   the driver's three laws are a8's driver-phase theorems under the one parameter premise rl_param_ok
   (QSEC_MAX + 6 < cf_sec_live_max; at reply's CfParams: CfParamsReply.v reply_rl_param_ok). NP_LIVE = 3 is
   room_live_cf_step_gen's live-set bound. *)
Section rl.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
Hypothesis RLP : rl_param_ok.
Lemma np_init_rl : iface_room_np_init room_live_cf.
Proof. exact (room_live_cf_init_gen RLP). Qed.
Lemma np_step_rl : iface_room_np_step room_live_cf.
Proof.
split.
- intros U S n tr trc p S' HW HQ HN HL HP.
  exact (room_live_cf_step_gen RLP U S S' HW HQ HN HL (or_introl (ex_intro _ n (ex_intro _ tr (ex_intro _ trc (ex_intro _ p HP)))))).
- intros U S p tr trc S' HW HQ HN HL HP.
  exact (room_live_cf_step_gen RLP U S S' HW HQ HN HL (or_intror (ex_intro _ p (ex_intro _ tr (ex_intro _ trc HP))))).
Qed.
Lemma np_tail_rl : iface_room_np_tail room_live_cf.
Proof. intros S H. exact (room_live_room_k S H). Qed.
(* TFIB_B_T from the cf program interface at NP := room_live_cf, rl_param_ok and the cf allocator's realizers, for a
   meter MT with the call room MT_PRE and a run count NS with its laws (B/YD1mcf.v NS_MO / XN_BND, the driver's
   malloc / free steps at B/CfRBridgeRulesB.v's texts, and the start budget B/YD2dcf.v NS_START at init_state), drv_pre's
   RELRO facts (RO / HSTART_ARO) *)
Theorem replyb_TFIB_B_T_of_cf_rl : forall (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (NS : astate -> Z) (NRUN XNMAX : Z),
  (forall S n, Wf_cf (as_universe TfibB) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> room_live_cf S -> NS S + XNMAX <= NRUN ->
     0 <= n < 2 ^ 26 -> mo_ok MT S (XM_LIB n)) ->
  (forall S S' n, mo_le MT S S' (XN_LIB n) -> NS S' <= NS S + XN_LIB n) ->
  (forall n, 0 <= n < 2 ^ 26 -> 0 <= XN_LIB n <= XNMAX) ->
  (forall S, NS S <= NRUN -> cf_hull_ok S) ->
  (forall n tr s,
     YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1))) ->
  (forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s)) ->
  NS init_state + 12 + 4 * XNMAX <= NRUN ->
  (forall (rc : YM05.RunCeil) (fx : YK11.FPState),
     @fr_lib_contract_drvR fx rc checksum_shape ci cp TfibB MT XM_LIB XN_LIB REPLYB_RO_LO REPLYB_RO_HI LIBROOM_fr room_live_cf
       (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))) ->
  (forall (rc : YM05.RunCeil), amalloc_realizes_cf tfibsegs TfibB) ->
  (forall (rc : YM05.RunCeil), YG0dcfR.afree_realizes_cf_rh tfibsegs TfibB) ->
  (forall (rc : YM05.RunCeil), ReplyStartWitB.start_cells_ho_t TfibB) ->
  (forall (rc : YM05.RunCeil), ReplyStartWitB.start_pf_ho_t TfibB) ->
  YGcfImgRows.EXH_OFF_t /\ YG0ncf.errb_obj_owned_t TfibB /\ YG0ncf.errb_ial_apart_t TfibB ->
  YG0ncf.pf_cells_owned_t TfibB ->
  relro_ok ->
  start_aro_ho_t TfibB ->
  TFIB_B_T.
Proof.
intros MT XM XN NS NRUN XNMAX MP NSMO XNB HNS NSM NSF NSS TL AM AF HST HSP HRW HPO RO HSA.
exact (replyb_TFIB_B_T_of_cf room_live_cf np_init_rl np_step_rl np_tail_rl MT XM XN NS NRUN XNMAX MP NSMO XNB HNS NSM NSF NSS
  TL AM AF HST HSP HRW HPO RO HSA).
Qed.
End rl.
