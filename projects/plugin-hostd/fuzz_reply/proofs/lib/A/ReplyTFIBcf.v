(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/AD1pcf.v, with its module paths and module names changed; 115 of its 151 lines of code are new or changed and 210 lines of the source are left out. *)
(* The cf driver's top for plugin-hostd/fuzz_reply.asan: TFIB_T (lib/A/ReplyTFIB.v) from fuzz_reply's cf program
   interface at route R, fr_lib_contract_drvR (lib/A/AD1w_cf.v) at the world relation wle' tfibsegs RZ_cf (the library
   run can free), the form ReplyATop.v's DRIVER_CF consumes it in.
   The same shape as lib/A/ReplyTFIBParts.v (the donor's TFIB_T from its program contract tfib_lib_contract_x), with
   the second allocator instance in place of cgif's AR:
   - the driver is A/AD1qcf.v tfib_srealizesX (the cf copies of the donor's driver closure: AR switched to ARcf at the
     start-up hand-off by Reusable/YGcfNilInit.v ARcf_nil_init; no event arithmetic);
   - the sites are SitesCf's cf site proofs (A/AD1kcf, AD1lcf, AD1ocf, AD1jcf) over the interceptor walks made generic
     in the allocator invariant, and the read check and memcpy intrinsic are A/AD2mcf.v;
   - LIBROOM is AD1mcf.LIBROOM_fr (preset's LIB_ROOM abudget_cf (2 ^ 33)), discharged inside the driver;
   - NAMED HYPOTHESES, each with its owner: TLLVMF, the program interface at every run ceiling and FP state (W8's ARcf
     instance through the bridge, ReplyATop.v's DRIVER_CF premise); NP with its three laws, the non-primary room
     between allocator calls (the cf instance's room_live_cf, a Theorem Labs lane, Reusable/YGcfRoomLive.v room_live_cf_init_gen /
     room_live_cf_step_gen / room_live_room_k, once relocated); AMALLOC / AFREE, the cf allocator's realizers
     (a Theorem Labs lane; AFREE at the primed contract YG0dcfR.afree_realizes_cf_rh).  The call pre's hull admission and
     read-only bytes are drv_pre's own conjuncts, from HULL_NS and from RO / HSTART_ARO (a Theorem Labs lane's part 3c: the call
     pre carries no memnorm).
   Generic in the instance's CfImg / CfParams; ReplyDriverCf.v instantiates CfImg_A and CfParams_reply.  REPLY_RO_LO /
   REPLY_RO_HI have A/ReplyTFIBParts.v's bodies, so the instantiation is by conversion. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YA02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp YG0lawscf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn AB1v AF0m ACeg AD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG0dcf YG0d2cf YGcfNames YG01cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
ACfn_cf AD1vcf AD1wcf AD1xcf AD1icf AD1w_cf AD1mcf AD1kcf AD1lcf AD1ocf AD1jcf AD2mcf AD1pcf AD1qcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyGuard.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyStartWitA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Open Scope Z_scope.
(* The read-only range of ReplyATopX.v's instance, with A/ReplyTFIBParts.v's bodies (stated here rather than imported:
   ReplyTFIBParts.v Requires the donor's whole AR driver and allocator closure, which this top does not use). *)
Definition REPLY_RO_LO : Z := 0x9d470.
Definition REPLY_RO_HI : Z := 0x9e6c8.
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
Section b.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
(* the non-primary room and its three laws (A/AD1w_cf.v) *)
Variable NP : astate -> Prop.
Hypothesis NPI : iface_room_np_init NP.
Hypothesis NPS : iface_room_np_step NP.
Hypothesis NPT : iface_room_np_tail NP.
(* the meter and its per-call budgets, with the meter's room at each call (A/AD1mcf.v MT_PRE); generic here, and
   KF-COUNT's ReplyKfMeter.MT_sec at the composition (ReplyDriverCf.v reply_tfib_of_top_x_sec) *)
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
(* the run count (at MT_sec: a Theorem Labs lane's nsec_cf), its run bound and its per-call step bound (A/AD1mcf.v; KF-COUNT #7) *)
Variables (NS : astate -> Z) (NRUN XNMAX : Z).
Hypothesis MT_PRE : forall S n, Wf_cf (as_universe TfibB) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> NP S -> NS S + XNMAX <= NRUN ->
  0 <= n < 2 ^ 26 -> mo_ok MT S (XM_LIB n).
(* the meter's step bounds the run count's step and one call's step is at most XNMAX (A/AD1mcf.v); the count's step
   at the driver's own mallocs and frees, at the text of A/CfRBridgeRules.v nsec_malloc_cf / nsec_free_cf with NS for
   nsec_cf; and the count's room at the start state init_state for the driver's mallocs before the loop's first call
   and the loop's at most 4 calls (A/AD1pcf.v, A/AD2dcf.v NS_START, whose comment names the mallocs) *)
Hypothesis NS_MO : forall S S' n, mo_le MT S S' (XN_LIB n) -> NS S' <= NS S + XN_LIB n.
Hypothesis XN_BND : forall n, 0 <= n < 2 ^ 26 -> 0 <= XN_LIB n <= XNMAX.
Hypothesis HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S.
Hypothesis nsec_malloc_cf : forall n tr s,
  YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s).
Hypothesis NS_START : NS init_state + 12 + 4 * XNMAX <= NRUN.
(* the program interface, at every run ceiling and FP state, at the world relation wle' tfibsegs RZ_cf (route R: the
   library run can free, so cut_x's contract at R gives the continuation only that relation; A/AD1pcf.v Rcf) *)
Hypothesis TLLVMF : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fr_lib_contract_drvR fx rc checksum_shape ci cp TfibB MT XM_LIB XN_LIB REPLY_RO_LO REPLY_RO_HI LIBROOM_fr NP
    (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
(* the cf allocator's malloc and free; the free at the primed contract (route R, lib/A/YG0dcfR.v; free(NULL) inside
   it), the text ReplyAllocTargets.afree_target_reply states *)
Hypothesis AMALLOC : forall (rc : YM05.RunCeil), amalloc_realizes_cf tfibsegs TfibB.
Hypothesis AFREE : forall (rc : YM05.RunCeil), YG0dcfR.afree_realizes_cf_rh tfibsegs TfibB.
(* the covered range of the start-up memory (A/AD1pcf.v handoff_cov: a Theorem Labs lane's covered-range lemma, StartupTrace's
   step (2)), which RelocA-2's AStkUp turns into the readable entry image above the entry sp *)
Hypothesis HCOVD : handoff_cov.
(* field round 3: the cf driver's two start witnesses and the unit's four image rows (A/AD1pcf.v HSTART / HSTART_PF /
   HROWS / HPFO), at every run ceiling; the instance supplies them (A/ReplyStartWitA.v start_cells_A / start_pf_A,
   A/ReplyImgRowsA.v exh_off_A / errb_obj_owned_A, A/ReplyImg_pfrows.v errb_ial_apart_reply_A / pf_cells_owned_reply_A) *)
Hypothesis HSTART : forall (rc : YM05.RunCeil), ReplyStartWitA.start_cells_ho_t TfibB.
Hypothesis HSTART_PF : forall (rc : YM05.RunCeil), ReplyStartWitA.start_pf_ho_t TfibB.
Hypothesis HROWS : YGcfImgRows.EXH_OFF_t /\ YG0ncf.errb_obj_owned_t TfibB /\ YG0ncf.errb_ial_apart_t TfibB.
Hypothesis HPFO : YG0ncf.pf_cells_owned_t TfibB.
(* field round 3 (Part A; part 3c): drv_pre's read-only bytes (arodata_ok_cf over aro_addr_cf): the image fact
   (A/AD1vcf.v relro_ok; at CfImg_A ReplyRelroGeoA.relro_seg_reply_A, cf_relro_hi = 0x9f000 <= 0xa1f78 and the
   cf_ro_reads ranges below 0xa1f78) and their start at main's hand-off (A/AD1pcf.v start_aro_ho_t; at CfImg_A
   A/ReplyKeptAroStart.v arodata_ho_A) *)
Hypothesis RO : relro_ok.
Hypothesis HSTART_ARO : start_aro_ho_t TfibB.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
Let AICPY : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B)). Proof. eapply tfib_AICPY_cf; eassumption. Defined.
Let ARDCHK : AD1icf.aread_check_stmt B. Proof. eapply tfib_ARDCHK_cf; eassumption. Defined.
Let LIBX : fr_lib_contract_drv_allR B MT XM_LIB XN_LIB REPLY_RO_LO REPLY_RO_HI LIBROOM_fr NP
  (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) := fun fx => TLLVMF rc fx.
Let RO_IN : forall a, REPLY_RO_LO <= a < REPLY_RO_HI -> in_ro_tfa a := fun a H => or_intror H.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1kcf.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst. Proof. eapply tfib_printf_first; eassumption. Defined.
Let PFN : printf_next_tfa B xst. Proof. eapply tfib_printf_next; eassumption. Defined.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1kcf.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est. Proof. eapply tfib_fwrite_site; eassumption. Defined.
Let RFS : refused_site_tfa B est. Proof. eapply tfib_refused_site; eassumption. Defined.
Let FPO : fprintf_s_site_tfa B est 0x1d72f (strB "cli: cannot open "%string) nlB. Proof. eapply tfib_fprintf_open_site; eassumption. Defined.
Let FPR : fprintf_s_site_tfa B est 0x1d744 (strB "cli: read error on "%string) nlB. Proof. eapply tfib_fprintf_rderr_site; eassumption. Defined.
Let FPU : fprintf_s_site_tfa B est 0x15877 (strB "usage: "%string) (strB " INPUT"%string ++ nlB). Proof. eapply tfib_fprintf_usage_site; eassumption. Defined.
Let EXS : exit_site_tfa B est xst. Proof. eapply tfib_exit_site; eassumption. Defined.
Lemma reply_srealizesX_rc_cf : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB NP NPI NPS NPT (AMALLOC rc) (AFREE rc) AICPY ARDCHK MT XM_LIB XN_LIB REPLY_RO_LO REPLY_RO_HI
  NS NRUN XNMAX MT_PRE NS_MO XN_BND HULL_NS nsec_malloc_cf nsec_free_cf NS_START RO_IN RO LIBX
  xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS HCOVD (HSTART rc) HSTART_ARO (HSTART_PF rc) HROWS HPFO
  sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem reply_srealizesX_top_cf : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@reply_srealizesX_rc_cf (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp) target_alloc_limit) sp rdraw brk mb inp
  Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
(* TFIB_T from the cf program interface, the meter's room at each call, the run count's laws, NP's laws, the cf
   allocator's realizers and drv_pre's read-only facts *)
Theorem reply_TFIB_T_of_cf : TFIB_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (reply_srealizesX_top_cf sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
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
(* TFIB_T from the cf program interface at NP := room_live_cf, rl_param_ok and the cf allocator's realizers, for a
   meter MT with the call room MT_PRE and a run count NS with its laws (A/AD1mcf.v NS_MO / XN_BND, the driver's
   malloc / free steps at A/CfRBridgeRules.v's texts, and the start budget A/AD2dcf.v NS_START at init_state) and
   drv_pre's read-only facts (RO / HSTART_ARO) *)
Theorem reply_TFIB_T_of_cf_rl : forall (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (NS : astate -> Z) (NRUN XNMAX : Z),
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
     @fr_lib_contract_drvR fx rc checksum_shape ci cp TfibB MT XM_LIB XN_LIB REPLY_RO_LO REPLY_RO_HI LIBROOM_fr room_live_cf
       (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))) ->
  (forall (rc : YM05.RunCeil), amalloc_realizes_cf tfibsegs TfibB) ->
  (forall (rc : YM05.RunCeil), YG0dcfR.afree_realizes_cf_rh tfibsegs TfibB) ->
  handoff_cov ->
  (forall (rc : YM05.RunCeil), ReplyStartWitA.start_cells_ho_t TfibB) ->
  (forall (rc : YM05.RunCeil), ReplyStartWitA.start_pf_ho_t TfibB) ->
  YGcfImgRows.EXH_OFF_t /\ YG0ncf.errb_obj_owned_t TfibB /\ YG0ncf.errb_ial_apart_t TfibB ->
  YG0ncf.pf_cells_owned_t TfibB ->
  relro_ok ->
  start_aro_ho_t TfibB ->
  TFIB_T.
Proof.
intros MT XM XN NS NRUN XNMAX MP NSMO XNB HNS NSM NSF NSS TL AM AF HS HST HSTPF HRW HPFO RO HSA.
exact (reply_TFIB_T_of_cf room_live_cf np_init_rl np_step_rl np_tail_rl MT XM XN NS NRUN XNMAX MP NSMO XNB HNS NSM NSF NSS TL AM AF HS
  HST HSTPF HRW HPFO RO HSA).
Qed.

End rl.
