(* Modified by Theorem Labs, 2026-10: ARcf_nil_init's new last premise (lazy addresses mapped at the hand-off model, the cf layer's YGcfNilInit.v:89-90) is given by cs_ok_lazy_in_maps_cf HC (Reusable/YCsokLazyMaps.v, a Theorem Labs lane's start-up row). *)
(* Modified by Theorem Labs, 2026-10: the entry world W1 takes lib/B/YReplyWorldH8.v's H1_H8 for the world field w_H8, the same change as lib/B/YD1p.v (ported from plugin-hostd/fuzz_command's lib/B/YD1p.v). *)
(* Modified by Theorem Labs, 2026-10: field round 3's two start witnesses (HSTART / HSTART_PF) are stated at the start-up hand-off (B/ReplyStartWitB.v start_cells_ho_t / start_pf_ho_t: the error buffer's five cells and Printf's two cells are not const cells of AR); the instance proves them (start_cells_B / start_pf_B) (a Theorem Labs lane M's patch). *)
(* Hand port by a Theorem Labs lane (2026-10-29, a Theorem Labs lane's DRIVER_CF_B): A1's raw generator copy of this file
   with CfDriver's hand edits to lib/A/AD1pcf.v (generator run out-DRV2 ->)
   three-way merged on; YCegcf -> YCeg as CfDriver's A edit (ACegcf -> ACeg), Reusable YC5d as A2's YD1w_cf, A1's
   two cf-suffix defects fixed, AStkUp -> RelocB-2's YStkUp, AD29cf -> YD29cf. No image-A literal. *)
(* copied from cgif_file lib/A/YD1p.v by rules r1,r13,r2,r3,r6,rC, generator c03cd3ee83e0f39cd4fe9d090fe9d53155314a0005789c623a860de97ecb6274 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD1p.v, with its module paths changed, and its fuzz_reply.asan-ubsan addresses relocated from cgif_file_fuzzer.asan-ubsan (3 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the model's channel reader that fdchan asks for beside the descriptor (cs_ok's co_rdr, proved at the launch); the section lemmas specialized in the proof, where their names are bound). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB01r YB1n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1g YD1f YD2i YD1t.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1vcf YD1wcf YD2acf YD26cf YD22cf YD1zcf YD2gcf YD2ccf YD2dcf YD29cf YD2ecf YD1rcf YD1xcf YD27cf YCfl YD1icf YD1ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn YCeg YE2k YD1ucf YD1mcf YD2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d2cf YG0dcf YG0lawscf YG0ncf YG0ucf YGcfNames YGcfNilInit YG01cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCsokLazyMaps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn_cf YD1mcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1w_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YStkUp YStkCov.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyStartWitB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YReplyWorldH8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Lemma wr_has_nil : forall ch bs T, wr ch bs T [].
Proof. intros. unfold wr. apply t_emit_has_nil. Qed.
Lemma diag_has_nil : forall m fs, diag m fs [].
Proof. intros. unfold diag. apply wr_has_nil. Qed.
Lemma t_alt2_has_nil_l : forall A B, A [] -> t_alt2 A B [].
Proof. intros A B H. left. exact H. Qed.
#[local] Existing Instance YK11.fx0.
(* field round 3 (Part A): the read-only RELRO bytes at main's hand-off memory FULL, where drv_pre's arodata_ok_cf
   conjunct starts (the driver's first allocator call, B/YD26cf.v m1_common, is after the driver's own code from
   FULL). HSTART_ARO's statement; at CfImg_B / TfibB it is the text of B/ReplyKeptAroStartB.v arodata_ho_B.
   LPS 727298f3: over the start of B/YD1q.v's drv_mainX_stmt, as A/AD1pcf.v's start_aro_ho_t. *)
#[local] Notation ARGH sp rdraw inp := (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
  (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
  (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).
Definition start_aro_ho_t {ci : YGcfNames.CfImg} (B : asyms) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs)
    (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV (ARGH sp rdraw inp) (in_fs inp) E ch R FULL model ->
  arodata_ok_cf TSEGS B FULL.
Section b.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
 Context {rc : YM05.RunCeil} {LS : lib_shape}.
(* route R: the world relation of the driver's re-hiding steps at the cf instance, the hidden set growing only inside
   the fixed shadow zone RZ_cf (lib/B/YGcfRehidePost.v; Reusable/YA0nH.v wle'): the primed free contract's step
   (YD1icf.tfib_free_site) and cut_x's contract at R (LIBC below) *)
Local Notation Rcf := (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf).
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
Let ML : model_laws_cf (as_universe B) := model_laws_cf_ok (as_universe B) (ts_universe B HB).
(* the cf allocator's non-primary room between the driver's allocator calls, with its three laws (A/AD1w_cf.v; the
   instance's room_live_cf discharges them at the top) *)
Variable NP : astate -> Prop.
Hypothesis NPI : iface_room_np_init NP.
Hypothesis NPS : iface_room_np_step NP.
Hypothesis NPT : iface_room_np_tail NP.
Hypothesis AMALLOC : amalloc_realizes_cf tfibsegs B.
(* ROW T (route R): the cf allocator's free at the primed contract (lib/B/YG0dcfR.v; free(NULL) inside it) *)
Hypothesis AFREE : YG0dcfR.afree_realizes_cf_rh tfibsegs B.
Hypothesis AICPY : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : YD1icf.aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
(* the run count (at MT_sec: a Theorem Labs lane's nsec_cf), its run bound and its per-call step bound (B/YD1mcf.v; KF-COUNT #7) *)
Variables (NS : astate -> Z) (NRUN XNMAX : Z).
(* the meter's room at each call (A/AD1mcf.v MT_PRE) *)
Hypothesis MT_PRE : forall S n, Wf_cf (as_universe B) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> NP S -> NS S + XNMAX <= NRUN ->
  0 <= n < 2 ^ 26 -> mo_ok MT S (XM_LIB n).
(* the meter's step bounds the run count's step and one call's step is at most XNMAX (B/YD1mcf.v) *)
Hypothesis NS_MO : forall S S' n, mo_le MT S S' (XN_LIB n) -> NS S' <= NS S + XN_LIB n.
Hypothesis XN_BND : forall n, 0 <= n < 2 ^ 26 -> 0 <= XN_LIB n <= XNMAX.
(* field round 3: the call's hull admission from the run count's bound (B/YD1mcf.v HULL_NS; at reply's instance
   NS := nsec_cf, NRUN := cf_kmax it is cf_hull_ok by conversion). It gives drv_pre's cf_hull_ok conjunct at every
   driver allocator call: before the loop with NS_PRE below (B/YD23cf.v, B/YD27cf.v, B/YD2ecf.v), after the last call
   with the loop's room (B/YD1rcf.v); at init_state cf_hull_ok_init gives it (B/YD26cf.v) *)
Hypothesis HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S.
(* the run count's step at the driver's own mallocs and frees, at the text of B/CfRBridgeRulesB.v nsec_malloc_cf /
   nsec_free_cf with NS for nsec_cf (the instance takes NS := nsec_cf and plugs those) *)
Hypothesis nsec_malloc_cf : forall n tr s,
  YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s).
(* the count's room at the start state init_state (ARcf_nil_init's state in tfib_drv_main below): the driver's
   mallocs before the loop's first call, at most 12 = B/YD26cf.v:381 (the input buffer) + B/YD23cf.v:421 (a grow, at
   most 10 under cap < 2 ^ 26 from 2 ^ 16; B/YD23cf.v:660's frees add 0) + B/YD2ecf.v:499 (the payload copy), and the
   loop's at most 4 calls (B/YD2dcf.v NS_START, whose comment has the count) *)
Hypothesis NS_START : NS init_state + 12 + 4 * XNMAX <= NRUN.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
(* field round 3 (Part A): the image fact behind drv_pre's arodata_ok_cf conjunct (B/YD1vcf.v relro_ok): the RELRO
   range lies in one segment and below the driver's image windows, so no driver step, interceptor or allocator call
   writes a RELRO byte. At CfImg_B: ReplyRelroGeoB.relro_seg_reply_B and cf_relro_hi = 0x9f000 <= 0xa24f8 *)
Hypothesis RO : relro_ok.
(* fuzz_reply's cf program interface at Rcf, with its room LIBROOM at preset's LIB_ROOM abudget_cf (2 ^ 33)
   (B/YD1mcf.v) *)
Hypothesis LIBC : fr_lib_contract_drvR B MT XM_LIB XN_LIB RLO RHI LIBROOM_fr NP Rcf.
Let MSITE : malloc_site_tfa B. Proof. eapply tfib_malloc_site; eassumption. Defined.
Let RCHK : read_check_tfa B. Proof. eapply tfib_read_check; eassumption. Defined.
Let MCPY : memcpy_site_tfa B. Proof. eapply tfib_memcpy_site; eassumption. Defined.
Let FREE : free_site_tfa B Rcf. Proof. eapply tfib_free_site; eassumption. Defined.
Let FREEN : free_null_site_tfa B Rcf. Proof. eapply tfib_free_null_site; eassumption. Defined.
Let LIB : lib_site_cf B NP NS NRUN XNMAX Rcf :=
  tfib_lib_site_cf B NP NS NRUN XNMAX Rcf MT XM_LIB XN_LIB RLO RHI MT_PRE NS_MO XN_BND HULL_NS RO_IN LIBC.
Let XNMAX_NN : 0 <= XNMAX. Proof. pose proof (XN_BND 0 ltac:(lia)). lia. Defined.
(* the count's room for the driver's mallocs before the loop (at most 12 above init_state: NS_START's comment) *)
Let NS_PRE : NS init_state + 12 <= NRUN. Proof. pose proof XNMAX_NN. lia. Qed.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d745 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d75a (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15886 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
Let RDERR : rderr_leaf_tfa B. Proof. eapply tfib_rderr_leaf; eassumption. Defined.
Let REFUSED : refused_leaf_tfa B. Proof. eapply tfib_refused_leaf; eassumption. Defined.
Let SHORT : short_leaf_tfa B NP NS. Proof. eapply tfib_short_leaf; eassumption. Defined.
Let OVERRUN : overrun_leaf_tfa B NP NS. Proof. eapply tfib_overrun_leaf; eassumption. Defined.
Let EXITL : exit_leaf_tfa B xst. Proof. eapply tfib_exit_leaf; eassumption. Defined.
Let HCO : cannot_open_tfa B. Proof. eapply tfib_cannot_open; eassumption. Defined.
(* the main tail after the loop (A/YD29cf.v), in the loop's form (A/AD1rcf.v main_tail_cf: ARcf at Hp = []) *)
Let MAINT : forall sp brk mbase inp xw xd a0 p rnd, valid_sp sp -> in_argv inp = [a0; p] ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
  main_tail_cf B xst sp inp xw xd a0 p rnd.
Proof.
intros sp brk mbase inp xw xd a0 p rnd Hsp Hargv Hva Hve Hvl Hlau Hvi
  E W ms md ly S data pb cap v k fs HEE HEd Hlen E41 E79 Hv HS HAI HAR HTOP Hbl HQT HROOM HHU HSO Hfds Hcr Hfs HAD.
eapply (YD29cf.tfib_main_tail B HB ARL xst Rcf FREE EXITL XFR RO); try eassumption; try reflexivity.
Defined.
Let LOOPL : loop_L_x B NP NS NRUN XNMAX xst :=
  tfib_loop_L B HB ARL ML xst NP NPT NS NRUN XNMAX XNMAX_NN HULL_NS nsec_free_cf RO Rcf LIB PF1 PFN FREE FREEN XFR MAINT.
Let RUNQM : run_QM_tfa B NP NS :=
  tfib_run_QM B NP NPT NPS HB ARL ML MSITE MCPY xst EXITL XFR NS NRUN XNMAX nsec_malloc_cf NS_START XNMAX_NN HULL_NS LOOPL RO.
Let RUNQ : run_Q_tfa B NP NS := tfib_run_Q B NP HB ARL xst NS NRUN XNMAX NS_START LOOPL RUNQM RO.
Let POSTP : post_P_tfa B NP NS := tfib_post_P B NP NS HB ARL RUNQ RO.
Let HDR : hdr_tfa B NP NS := tfib_hdr B NP NS HB ARL SHORT OVERRUN POSTP RO.
Let RDD : rd0_dir_tfa B NP. Proof. eapply tfib_rd0_dir; eassumption. Defined.
Let RDF : rd0_file_tfa B NP NS :=
  tfib_rd0_file B NP NPT NPS HB ARL ML MSITE RCHK MCPY Rcf FREE NS nsec_malloc_cf nsec_free_cf NRUN HULL_NS NS_PRE RO REFUSED HDR.
Let HFILE : file_arm_tfa B := tfib_file_arm B NP NPT NPS NPI HB ARL ML MSITE RO NS nsec_malloc_cf RDF.
Let HDIR : dir_arm_tfa B := tfib_dir_arm B NP NPT NPS NPI HB ARL ML MSITE RO RDD.
(* field rounds 2 and 3 of the cf layer: the conversion at init (Reusable/YGcfNilInit.v ARcf_nil_init) takes the start
   witness of the two machine cells (YG0ncf.start_cells_cf), the start witness of Printf's two image cells
   (YG0ncf.start_pf_cf, round 3), the unit's three image rows (EXH_OFF_t, errb_obj_owned_t, errb_ial_apart_t) and the
   pf cells' ownership (pf_cells_owned_t, round 3). The two start witnesses are stated at the start-up hand-off
   (B/ReplyStartWitB.v start_cells_ho_t / start_pf_ho_t: the error buffer's five cells and Printf's two cells are not
   const cells of AR). The instance supplies them (B/ReplyStartWitB.v start_cells_B / start_pf_B, B/ReplyImgRowsB.v
   exh_off_B / errb_obj_owned_B, B/ReplyImg_pfrowsB.v errb_ial_apart_reply_B / pf_cells_owned_reply_B) *)
Hypothesis HSTART : ReplyStartWitB.start_cells_ho_t B.
(* field round 3 (Part A): the RELRO bytes at main's hand-off (start_aro_ho_t above); the instance plugs
   B/ReplyKeptAroStartB.v arodata_ho_B *)
Hypothesis HSTART_ARO : start_aro_ho_t B.
Hypothesis HSTART_PF : ReplyStartWitB.start_pf_ho_t B.
Hypothesis HROWS : YGcfImgRows.EXH_OFF_t /\ YG0ncf.errb_obj_owned_t B /\ YG0ncf.errb_ial_apart_t B.
Hypothesis HPFO : YG0ncf.pf_cells_owned_t B.
(* LPS 727298f3: the statement is B/YD1q.v's [drv_mainX_stmt]: the hand-off state of the run's own CONFIG_RSEQ flag
   ([YB01r.HS_tfib_r]), the stack invariant abstract with its one consequence [SINV_sp0], the mmap base, and the
   launch's fifth [valid_entry] conjunct. *)
Theorem tfib_drv_main : forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
(forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV
(YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
  (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
  (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
  (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
  (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n) ->
(forall a, YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
  (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
  (in_execfn inp) (in_sigpipe_default inp) E a = true ->
FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) sp rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM.
pose proof Hinp as (Hva & Hve & Hvfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & _).
(* the section lemmas at this proof's names, in their sections' order; an argument a lemma does not take is
   skipped (the idiom of libreac/fuzz_decode's A/AD1p.v); the specializations are written in the proof, where
   the names are bound: a top-level [Ltac] naming [sp], which no Section binds, is refused *)
pose proof (@YReplyWorldH8.H1_H8) as H8. try specialize (H8 YK11.fx0); try specialize (H8 B); try specialize (H8 HB); try specialize (H8 sp); try specialize (H8 rdraw);
try specialize (H8 brk); try specialize (H8 mbase); try specialize (H8 inp);
try specialize (H8 Hsp); try specialize (H8 Hva); try specialize (H8 Hve); try specialize (H8 Hfit);
try specialize (H8 Hvl); try specialize (H8 Hlau); try specialize (H8 Hinp);
try specialize (H8 h); try specialize (H8 ch); try specialize (H8 E); try specialize (H8 R); try specialize (H8 FULL);
try specialize (H8 model); try specialize (H8 Hch); try specialize (H8 SINV); try specialize (H8 SP0);
try specialize (H8 HC); try specialize (H8 HE); try specialize (H8 HM); try specialize (H8 rc); try specialize (H8 Hceil).
pose proof (@sliver_allowed) as SL. try specialize (SL YK11.fx0); try specialize (SL B); try specialize (SL HB); try specialize (SL sp); try specialize (SL rdraw);
try specialize (SL brk); try specialize (SL mbase); try specialize (SL inp);
try specialize (SL Hsp); try specialize (SL Hva); try specialize (SL Hve); try specialize (SL Hfit);
try specialize (SL Hvl); try specialize (SL Hlau); try specialize (SL Hinp);
try specialize (SL h); try specialize (SL ch); try specialize (SL E); try specialize (SL R); try specialize (SL FULL);
try specialize (SL model); try specialize (SL Hch); try specialize (SL SINV); try specialize (SL SP0);
try specialize (SL HC); try specialize (SL HE); try specialize (SL HM); try specialize (SL rc); try specialize (SL Hceil).
pose proof (@tfib_main_entry) as ME. try specialize (ME YK11.fx0); try specialize (ME B); try specialize (ME HB); try specialize (ME sp); try specialize (ME rdraw);
try specialize (ME brk); try specialize (ME mbase); try specialize (ME inp);
try specialize (ME Hsp); try specialize (ME Hva); try specialize (ME Hve); try specialize (ME Hfit);
try specialize (ME Hvl); try specialize (ME Hlau); try specialize (ME Hinp);
try specialize (ME h); try specialize (ME ch); try specialize (ME E); try specialize (ME R); try specialize (ME FULL);
try specialize (ME model); try specialize (ME Hch); try specialize (ME SINV); try specialize (ME SP0);
try specialize (ME HC); try specialize (ME HE); try specialize (ME HM); try specialize (ME rc); try specialize (ME Hceil). specialize (ME SL). specialize (ME H8).
destruct ME as (Hpc & HST & HAI & Hfs & Hfds & _).
set (ly := YD1g.ly0 ch E model).
(* the switch to the second allocator instance at the start-up hand-off (Reusable/YGcfNilInit.v ARcf_nil_init). The
   switch exposes class 1's shadow band: ARcf holds at a world W' with wle W1 W', and the driver runs at W' from here. *)
(* YD1f's Section arguments by name (inst); W1h is the hand-off world its AR is stated at *)
pose proof (@tfib_AR) as HAR1. try specialize (HAR1 YK11.fx0); try specialize (HAR1 B); try specialize (HAR1 HB); try specialize (HAR1 sp); try specialize (HAR1 rdraw);
try specialize (HAR1 brk); try specialize (HAR1 mbase); try specialize (HAR1 inp);
try specialize (HAR1 Hsp); try specialize (HAR1 Hva); try specialize (HAR1 Hve); try specialize (HAR1 Hfit);
try specialize (HAR1 Hvl); try specialize (HAR1 Hlau); try specialize (HAR1 Hinp);
try specialize (HAR1 h); try specialize (HAR1 ch); try specialize (HAR1 E); try specialize (HAR1 R); try specialize (HAR1 FULL);
try specialize (HAR1 model); try specialize (HAR1 Hch); try specialize (HAR1 SINV); try specialize (HAR1 SP0);
try specialize (HAR1 HC); try specialize (HAR1 HE); try specialize (HAR1 HM); try specialize (HAR1 rc); try specialize (HAR1 Hceil).
match type of HAR1 with AR _ _ _ _ ?W _ _ => set (W1h := W) in HAR1 end.
destruct (ARcf_nil_init TSEGS B ly W1h FULL model HAR1 HAI
  (cs_ok_lazy_in_maps_cf _ _ _ _ _ _ _ _ _ _ _ _ HC)
  (HSTART sp rdraw brk mbase inp h ch E R FULL model SINV ly W1h model Hsp Hva Hve Hfit Hinp Hlau Hch SP0 HC eq_refl HAR1)
  (HSTART_PF sp rdraw brk mbase inp h ch E R FULL model SINV ly W1h Hsp Hva Hve Hfit Hinp Hlau Hch SP0 HC eq_refl)
  HROWS HPFO) as (W' & HWLE & HAI' & HAR).
(* wle W1 W' hides fewer bytes: a byte that reads at W1 reads the same at W' (YA0o.v mrestrict_hsub /
   mbyte_mrestrict_hsub). The hand-off facts below only say that bytes read, so they move from W1 to W'. *)
assert (G : forall a b, mbyte tfibsegs (mrestrict (w_H W1h) FULL) a = Some b ->
  mbyte tfibsegs (mrestrict (w_H W') FULL) a = Some b).
{ intros a b. apply mbyte_mrestrict_hsub; [exact (w_Hoff _) | exact HWLE]. }
assert (RT : forall spv l, runs_at spv (mrestrict (w_H W1h) FULL) l ->
  runs_at spv (mrestrict (w_H W') FULL) l).
{ intros spv l X. unfold runs_at in X |- *. rewrite Forall_forall in X |- *. intros ab Hab.
  destruct (X ab Hab) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
  intros j Hj. specialize (Q3 j Hj). destruct (nth_error (snd ab) j) as [b|] eqn:En.
  - try rewrite En in Q3. exact (mrestrict_hsub _ _ FULL _ b HWLE Q3).
  - apply nth_error_None in En. lia. }
assert (HTOP : YD1vcf.top_ok (bv_unsigned sp) ly).
{ pose proof (@tfib_top_ok) as L. try specialize (L YK11.fx0); try specialize (L B); try specialize (L HB); try specialize (L sp); try specialize (L rdraw);
try specialize (L brk); try specialize (L mbase); try specialize (L inp);
try specialize (L Hsp); try specialize (L Hva); try specialize (L Hve); try specialize (L Hfit);
try specialize (L Hvl); try specialize (L Hlau); try specialize (L Hinp);
try specialize (L h); try specialize (L ch); try specialize (L E); try specialize (L R); try specialize (L FULL);
try specialize (L model); try specialize (L Hch); try specialize (L SINV); try specialize (L SP0);
try specialize (L HC); try specialize (L HE); try specialize (L HM); try specialize (L rc); try specialize (L Hceil). exact L. }
assert (HFI : FINV ly (w_H W') FULL).
{ pose proof (@tfib_finv_handoff) as HFI1. try specialize (HFI1 YK11.fx0); try specialize (HFI1 B); try specialize (HFI1 HB); try specialize (HFI1 sp); try specialize (HFI1 rdraw);
try specialize (HFI1 brk); try specialize (HFI1 mbase); try specialize (HFI1 inp);
try specialize (HFI1 Hsp); try specialize (HFI1 Hva); try specialize (HFI1 Hve); try specialize (HFI1 Hfit);
try specialize (HFI1 Hvl); try specialize (HFI1 Hlau); try specialize (HFI1 Hinp);
try specialize (HFI1 h); try specialize (HFI1 ch); try specialize (HFI1 E); try specialize (HFI1 R); try specialize (HFI1 FULL);
try specialize (HFI1 model); try specialize (HFI1 Hch); try specialize (HFI1 SINV); try specialize (HFI1 SP0);
try specialize (HFI1 HC); try specialize (HFI1 HE); try specialize (HFI1 HM); try specialize (HFI1 rc); try specialize (HFI1 Hceil).
  destruct HFI1 as ((M & HX & Himg & O1 & O2 & O3 & O4 & O5 & O6) & (E1 & E2 & E3 & cv & Hcv & E4) & Hhead).
  split; [|split].
  - exists M. split; [exact HX|]. split; [exact Himg|].
    split; [exact (fun k Hk => G _ _ (O1 k Hk))|]. split; [exact (fun k Hk => G _ _ (O2 k Hk))|].
    split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. intros a Ha. exact (G _ _ (O6 a Ha)).
  - split; [exact (fun k Hk => G _ _ (E1 k Hk))|]. split; [exact (fun k Hk => G _ _ (E2 k Hk))|].
    split; [exact (fun k Hk => G _ _ (E3 k Hk))|]. exists cv. split; [exact Hcv | exact (fun k Hk => G _ _ (E4 k Hk))].
  - exact (fun k Hk => G _ _ (Hhead k Hk)). }
(* the entry image above the entry sp reads at the hand-off: RelocB-2's YStkUp hand-off with its covered-range
   premise discharged (a Theorem Labs lane's lib/B/YStkCov.v tfib_handoff_stk_up_cov),
   so the driver carries no covered-range hypothesis (A's AD1pcf.handoff_cov / HCOVD) *)
(* ... and it moves from W1 to W' byte by byte, by G above *)
assert (HUP0 : stk_up (bv_unsigned sp) ly W' FULL).
{ assert (HUP1 : stk_up (bv_unsigned sp) ly W1h FULL).
  { pose proof (@YStkCov.tfib_handoff_stk_up_cov) as L. try specialize (L YK11.fx0); try specialize (L B); try specialize (L HB); try specialize (L sp); try specialize (L rdraw);
try specialize (L brk); try specialize (L mbase); try specialize (L inp);
try specialize (L Hsp); try specialize (L Hva); try specialize (L Hve); try specialize (L Hfit);
try specialize (L Hvl); try specialize (L Hlau); try specialize (L Hinp);
try specialize (L h); try specialize (L ch); try specialize (L E); try specialize (L R); try specialize (L FULL);
try specialize (L model); try specialize (L Hch); try specialize (L SINV); try specialize (L SP0);
try specialize (L HC); try specialize (L HE); try specialize (L HM); try specialize (L rc); try specialize (L Hceil). intros a Ha. eapply L; eassumption. }
  intros a Ha. specialize (HUP1 a Ha).
  change (option_map (fun b0 => bv_unsigned b0) (mbyte tfibsegs (mrestrict (w_H W1h) FULL) a) <> None) in HUP1.
  change (option_map (fun b0 => bv_unsigned b0) (mbyte tfibsegs (mrestrict (w_H W') FULL) a) <> None).
  destruct (mbyte tfibsegs (mrestrict (w_H W1h) FULL) a) as [b|] eqn:Eb.
  - rewrite (G _ _ Eb). discriminate.
  - exfalso. apply HUP1. try rewrite Eb. reflexivity. }
(* The hand-off model's channel reader, which [fdchan] asks for at LPS 727298f3 beside the
   descriptor: [cs_ok]'s [co_rdr], proved at the launch.  The arms carry it to their sites. *)
assert (Hcr : m_channel_reader model = true) by (eapply co_rdr; exact HC).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
pose proof (HSTART_ARO sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hva Hve Hfit Hinp Hlau Hch SP0 HC) as HAD.
change TSEGS with tfibsegs in HST, HAI, HAI', HAR, HAD |- *. unfold CLOSEDX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS0 HR0].
pose proof (st_ok_wle _ _ _ _ _ _ HWLE HS0) as HS. pose proof (RT _ _ HR0) as HR.
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
eapply (tfib_arm_argv2 B HB ARL HCO HFILE HDIR RO sp brk mbase inp rdraw _ _
W' (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model ly a0 p
Hsp Hargv Hva Hve Hvl Hlau Hinp Hvfs HS HR HUP0 HAI' HAR HTOP HFI Hfs Hfds Hcr HAD).
- destruct (HST false I) as [HS0 HR0].
pose proof (st_ok_wle _ _ _ _ _ _ HWLE HS0) as HS. pose proof (RT _ _ HR0) as HR.
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
eapply (tfib_usage B HB ARL xst est XFR ESTF FPU EXS sp brk mbase inp rdraw _ _ W' (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs))
model ly); eassumption.
Qed.
End c.
End b.
