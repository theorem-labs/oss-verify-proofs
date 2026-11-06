(* copied from cgif_file lib/A/AD1p.v by rules r1,r13,r2,r3,r6,rC, generator ed5c0821ce98f1d99fcd7466c0aa65f7671a8daf838ab8f2b2da9f5038f22ee4 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (3 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: ARcf_nil_init's new last premise (lazy addresses mapped at the hand-off model, the cf layer's YGcfNilInit.v:88-89) is given by cs_ok_lazy_in_maps_cf HC (Reusable/YCsokLazyMaps.v, a Theorem Labs lane's start-up row ca5c7a243e44). *)
(* Modified by Theorem Labs, 2026-10: field round 3's ARcf_nil_init (YGcfNilInit.v:96-102): the start witnesses HSTART / HSTART_PF are stated at the start-up hand-off (A/ReplyStartWitA.v start_cells_ho_t / start_pf_ho_t), HROWS gains errb_ial_apart_t and HPFO is pf_cells_owned_t (a Theorem Labs lane M's patch). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB12 AB1h AB01 AB1n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1g AD1f AD2i AD1t.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyWorldH8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1vcf AD1wcf AD2acf AD26cf AD22cf AD1zcf AD2gcf AD2ccf AD2dcf AD29cf AD2ecf AD1rcf AD1xcf AD27cf ACfl AD1icf AD1ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn ACeg AE2k AD1ucf AD1mcf AD2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d2cf YG0dcf YG0lawscf YG0ncf YG0ucf YGcfNames YGcfNilInit YG01cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCsokLazyMaps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn_cf AD1mcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1w_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AStkUp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyStartWitA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.

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
(* the covered-range fact of StartupTrace's step (2) (a Theorem Labs lane's covered-range lemma, in its conclusion form): the
   start-up memory FULL is defined from the entry sp to the entry page top.  RelocA-2's AStkUp.tfib_handoff_stk_up
   turns it into the entry image above the entry sp being readable at main's hand-off (AD1vcf.stk_up), which W8's
   readable-stack conjunct needs at every call.  A hypothesis of the driver until a4's lemma is in the tree. *)
Definition handoff_cov : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
  (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> HS_tfib h = Some ch ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
  (YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
  (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
  (forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
  FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
  forall a, bv_unsigned sp <= a <
    entry_page_top sp (build_stack_bytes TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw) ->
  FULL (Z_to_bv 64 a) <> None.
(* field round 3 (Part A; part 3c): the read-only bytes (arodata_ok_cf over aro_addr_cf: the RELRO range and the
   cf_ro_reads ranges) at main's hand-off memory FULL, where drv_pre's arodata_ok_cf conjunct starts (the driver's
   first allocator call, A/AD26cf.v m1_common, is after the driver's own code from FULL). HSTART_ARO's statement; at
   CfImg_A / TfibB it is the text of A/ReplyKeptAroStart.v arodata_ho_A. *)
Definition start_aro_ho_t {ci : YGcfNames.CfImg} (B : asyms) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs)
    (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_argv (in_argv inp) -> HS_tfib h = Some ch ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  arodata_ok_cf TSEGS B FULL.
Section b.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
 Context {rc : YM05.RunCeil} {LS : lib_shape}.
(* route R: the world relation of the driver's re-hiding steps at the cf instance, the hidden set growing only inside
   the fixed shadow zone RZ_cf (lib/A/YGcfRehidePost.v; Reusable/YA0nH.v wle'): the primed free contract's step
   (AD1icf.tfib_free_site) and cut_x's contract at R (LIBC below) *)
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
(* ROW T (route R): the cf allocator's free at the primed contract (lib/A/YG0dcfR.v; free(NULL) inside it) *)
Hypothesis AFREE : YG0dcfR.afree_realizes_cf_rh tfibsegs B.
Hypothesis AICPY : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : AD1icf.aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
(* the run count (at MT_sec: a Theorem Labs lane's nsec_cf), its run bound and its per-call step bound (A/AD1mcf.v; KF-COUNT #7) *)
Variables (NS : astate -> Z) (NRUN XNMAX : Z).
(* the meter's room at each call (A/AD1mcf.v MT_PRE) *)
Hypothesis MT_PRE : forall S n, Wf_cf (as_universe B) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> NP S -> NS S + XNMAX <= NRUN ->
  0 <= n < 2 ^ 26 -> mo_ok MT S (XM_LIB n).
(* the meter's step bounds the run count's step and one call's step is at most XNMAX (A/AD1mcf.v) *)
Hypothesis NS_MO : forall S S' n, mo_le MT S S' (XN_LIB n) -> NS S' <= NS S + XN_LIB n.
Hypothesis XN_BND : forall n, 0 <= n < 2 ^ 26 -> 0 <= XN_LIB n <= XNMAX.
(* field round 3: the call's hull admission from the run count's bound (A/AD1mcf.v HULL_NS; at reply's instance
   NS := nsec_cf, NRUN := cf_kmax it is cf_hull_ok by conversion). It gives drv_pre's cf_hull_ok conjunct at every
   driver allocator call: before the loop with NS_PRE below (A/AD23cf.v, A/AD27cf.v, A/AD2ecf.v), after the last call
   with the loop's room (A/AD1rcf.v); at init_state cf_hull_ok_init gives it (A/AD26cf.v) *)
Hypothesis HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S.
(* the run count's step at the driver's own mallocs and frees, at the text of A/CfRBridgeRules.v nsec_malloc_cf /
   nsec_free_cf with NS for nsec_cf (the instance takes NS := nsec_cf and plugs those) *)
Hypothesis nsec_malloc_cf : forall n tr s,
  YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s).
(* the count's room at the start state init_state (ARcf_nil_init's state in tfib_drv_main below): the driver's
   mallocs before the loop's first call, at most 12 = A/AD26cf.v:377 (the input buffer) + A/AD23cf.v:418 (a grow, at
   most 10 under cap < 2 ^ 26 from 2 ^ 16; A/AD23cf.v:657's frees add 0) + A/AD2ecf.v:493 (the payload copy), and the
   loop's at most 4 calls (A/AD2dcf.v NS_START, whose comment has the count) *)
Hypothesis NS_START : NS init_state + 12 + 4 * XNMAX <= NRUN.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
(* field round 3 (Part A; part 3c): the image fact behind drv_pre's arodata_ok_cf conjunct (A/AD1vcf.v relro_ok): the
   RELRO range and each cf_ro_reads range lie in one segment and below the driver's image windows, so no driver step,
   interceptor or allocator call writes such a byte. At CfImg_A: ReplyRelroGeoA.relro_seg_reply_A, cf_relro_hi =
   0x9f000 <= 0xa1f78 and the cf_ro_reads ranges below 0xa1f78 *)
Hypothesis RO : relro_ok.
(* fuzz_reply's cf program interface at Rcf, with its room LIBROOM at preset's LIB_ROOM abudget_cf (2 ^ 33)
   (A/AD1mcf.v) *)
Hypothesis LIBC : fr_lib_contract_drvR B MT XM_LIB XN_LIB RLO RHI LIBROOM_fr NP Rcf.
(* the malloc and free sites below take acall_pre_cf from drv_pre alone (A/AD1icf.v acall_pre_of_drv; a Theorem Labs lane's part
   3c: the call pre carries no memnorm). The hull admission and the read-only bytes are drv_pre's own conjuncts. *)
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
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d72f (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d744 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15877 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
Let RDERR : rderr_leaf_tfa B. Proof. eapply tfib_rderr_leaf; eassumption. Defined.
Let REFUSED : refused_leaf_tfa B. Proof. eapply tfib_refused_leaf; eassumption. Defined.
Let SHORT : short_leaf_tfa B NP NS. Proof. eapply tfib_short_leaf; eassumption. Defined.
Let OVERRUN : overrun_leaf_tfa B NP NS. Proof. eapply tfib_overrun_leaf; eassumption. Defined.
Let EXITL : exit_leaf_tfa B xst. Proof. eapply tfib_exit_leaf; eassumption. Defined.
Let HCO : cannot_open_tfa B. Proof. eapply tfib_cannot_open; eassumption. Defined.
(* the main tail after the loop (A/AD29cf.v), in the loop's form (A/AD1rcf.v main_tail_cf: ARcf at Hp = []) *)
Let MAINT : forall sp inp xw xd a0 p, valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) ->
  main_tail_cf B xst sp inp xw xd a0 p.
Proof.
intros sp inp xw xd a0 p Hsp Hva Hve E W ms md ly S data pb cap v k fs HEE HEd Hlen E41 E79 Hv HS HAI HAR HTOP Hbl HQT HROOM HHU HSO Hfds Hfs HAD.
eapply (AD29cf.tfib_main_tail B HB ARL xst Rcf FREE EXITL XFR RO sp inp xw xd a0 p Hsp Hva Hve E W ms md ly S []); try eassumption; try reflexivity.
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
Hypothesis HCOVD : handoff_cov.
(* field round 3 of the cf layer: the conversion at init (Reusable/YGcfNilInit.v:96-102 ARcf_nil_init) takes the start
   witness of the two machine cells (YG0ncf.start_cells_cf), the start witness of Printf's two image cells
   (YG0ncf.start_pf_cf), the three rows amc_cells_owned carries (EXH_OFF_t, errb_obj_owned_t, errb_ial_apart_t) and the
   row amc_pf_owned carries (pf_cells_owned_t). The two start witnesses are stated at the start-up hand-off
   (A/ReplyStartWitA.v start_cells_ho_t / start_pf_ho_t: the error buffer's five cells and Printf's two cells are not
   const cells of AR). The instance supplies them (A/ReplyStartWitA.v start_cells_A / start_pf_A, A/ReplyImgRowsA.v
   exh_off_A / errb_obj_owned_A, A/ReplyImg_pfrows.v errb_ial_apart_reply_A / pf_cells_owned_reply_A) *)
Hypothesis HSTART : ReplyStartWitA.start_cells_ho_t B.
(* field round 3 (Part A): the RELRO bytes at main's hand-off (start_aro_ho_t above); the instance plugs
   A/ReplyKeptAroStart.v arodata_ho_A *)
Hypothesis HSTART_ARO : start_aro_ho_t B.
Hypothesis HSTART_PF : ReplyStartWitA.start_pf_ho_t B.
Hypothesis HROWS : YGcfImgRows.EXH_OFF_t /\ YG0ncf.errb_obj_owned_t B /\ YG0ncf.errb_ial_apart_t B.
Hypothesis HPFO : YG0ncf.pf_cells_owned_t B.
Theorem tfib_drv_main : forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
Proof.
intros sp rdraw brk inp h ch E R FULL model Hsp Hbrk Hfit (Hva & Hve & Hvfs & _) Hceil Hch HC HE HM.
(* the world field w_H8 at the hand-off world W1 (Reusable/YA0n.v; lib/A/ReplyWorldH8.v's H1_H8, as AStkUp.v) *)
assert (H1H8 : forall a : Z, in_band_rw a -> AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a) =
  AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8))) by exact (ReplyWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC).
pose proof (tfib_main_entry sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM (sliver_allowed sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC Hceil) H1H8) as (Hpc & HST & HAI & Hfs & Hfds & _).
set (ly := AD1g.ly0 ch E model).
(* the switch to the second allocator instance at the start-up hand-off (Reusable/YGcfNilInit.v ARcf_nil_init). The
   switch exposes class 1's shadow band: ARcf holds at a world W' with wle W1 W', and the driver runs at W' from here. *)
assert (HAR1 : AR TSEGS B ly init_state (W1 sp rdraw inp Hsp Hva ch E model H1H8) FULL model).
{ (* AD1f's Section arguments by name: its W0 carries its own w_H8 proof, so eapply alone cannot fix them *)
  pose proof (@tfib_AR) as L.
    try specialize (L B); try specialize (L HB); try specialize (L sp); try specialize (L rdraw); try specialize (L brk);
    try specialize (L inp); try specialize (L Hsp); try specialize (L Hva); try specialize (L Hve); try specialize (L Hfit);
    try specialize (L h); try specialize (L ch); try specialize (L E); try specialize (L R); try specialize (L FULL);
    try specialize (L model); try specialize (L Hch); try specialize (L HC); try specialize (L HE); try specialize (L HM);
    try specialize (L rc); try specialize (L Hceil).
  exact L. }
destruct (ARcf_nil_init TSEGS B ly (W1 sp rdraw inp Hsp Hva ch E model H1H8) FULL model HAR1 HAI
  (cs_ok_lazy_in_maps_cf _ _ _ _ _ _ _ _ _ _ _ _ HC)
  (HSTART sp rdraw brk inp h ch E R FULL model ly (W1 sp rdraw inp Hsp Hva ch E model H1H8) model Hsp Hva Hch HC eq_refl HAR1)
  (HSTART_PF sp rdraw brk inp h ch E R FULL model ly (W1 sp rdraw inp Hsp Hva ch E model H1H8) Hsp Hva Hch HC eq_refl)
  HROWS HPFO) as (W' & HWLE & HAI' & HAR).
(* wle W1 W' hides fewer bytes: a byte that reads at W1 reads the same at W' (YA0o.v mrestrict_hsub /
   mbyte_mrestrict_hsub). The hand-off facts below only say that bytes read, so they move from W1 to W'. *)
assert (G : forall a b, mbyte tfibsegs (mrestrict (w_H (W1 sp rdraw inp Hsp Hva ch E model H1H8)) FULL) a = Some b ->
  mbyte tfibsegs (mrestrict (w_H W') FULL) a = Some b).
{ intros a b. apply mbyte_mrestrict_hsub; [exact (w_Hoff _) | exact HWLE]. }
assert (RT : forall spv l, runs_at spv (mrestrict (w_H (W1 sp rdraw inp Hsp Hva ch E model H1H8)) FULL) l ->
  runs_at spv (mrestrict (w_H W') FULL) l).
{ intros spv l X. unfold runs_at in X |- *. rewrite Forall_forall in X |- *. intros ab Hab.
  destruct (X ab Hab) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
  intros j Hj. specialize (Q3 j Hj). destruct (nth_error (snd ab) j) as [b|] eqn:En.
  - try rewrite En in Q3. exact (mrestrict_hsub _ _ FULL _ b HWLE Q3).
  - apply nth_error_None in En. lia. }
assert (HTOP : AD1vcf.top_ok (bv_unsigned sp) ly).
{ pose proof (@tfib_top_ok) as L.
    try specialize (L B); try specialize (L HB); try specialize (L sp); try specialize (L rdraw); try specialize (L brk);
    try specialize (L inp); try specialize (L Hsp); try specialize (L Hva); try specialize (L Hve); try specialize (L Hfit);
    try specialize (L h); try specialize (L ch); try specialize (L E); try specialize (L R); try specialize (L FULL);
    try specialize (L model); try specialize (L Hch); try specialize (L HC); try specialize (L HE); try specialize (L HM);
    try specialize (L rc); try specialize (L Hceil).
  exact L. }
assert (HFI : FINV ly (w_H W') FULL).
{ pose proof (tfib_finv_handoff sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC) as HFI1.
  destruct HFI1 as ((M & HX & Himg & O1 & O2 & O3 & O4 & O5 & O6) & (E1 & E2 & E3 & cv & Hcv & E4) & Hhead).
  split; [|split].
  - exists M. split; [exact HX|]. split; [exact Himg|].
    split; [exact (fun k Hk => G _ _ (O1 k Hk))|]. split; [exact (fun k Hk => G _ _ (O2 k Hk))|].
    split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. intros a Ha. exact (G _ _ (O6 a Ha)).
  - split; [exact (fun k Hk => G _ _ (E1 k Hk))|]. split; [exact (fun k Hk => G _ _ (E2 k Hk))|].
    split; [exact (fun k Hk => G _ _ (E3 k Hk))|]. exists cv. split; [exact Hcv | exact (fun k Hk => G _ _ (E4 k Hk))].
  - exact (fun k Hk => G _ _ (Hhead k Hk)). }
(* the entry image above the entry sp reads at the hand-off (RelocA-2's AStkUp, over the covered range), so at W' *)
assert (HUP0 : stk_up (bv_unsigned sp) ly W' FULL).
{ assert (HUP1 : stk_up (bv_unsigned sp) ly (W1 sp rdraw inp Hsp Hva ch E model H1H8) FULL).
  { (* AStkUp's Section arguments by name: its W1 carries its own w_H8 proof, which stk_up does not read, so eapply
       alone cannot fix them *)
    pose proof (@AStkUp.tfib_handoff_stk_up) as L.
    try specialize (L B); try specialize (L HB); try specialize (L sp); try specialize (L rdraw); try specialize (L brk);
    try specialize (L inp); try specialize (L Hsp); try specialize (L Hva); try specialize (L Hve); try specialize (L Hfit);
    try specialize (L h); try specialize (L ch); try specialize (L E); try specialize (L R); try specialize (L FULL);
    try specialize (L model); try specialize (L Hch); try specialize (L HC); try specialize (L HE); try specialize (L HM);
    try specialize (L rc); try specialize (L Hceil).
    intros a Ha. eapply L; try eassumption.
    all: try exact (HCOVD sp rdraw brk inp h ch E R FULL model Hsp Hva Hve Hfit Hch HC HE HM). }
  intros a Ha. specialize (HUP1 a Ha).
  change (option_map (fun b0 => bv_unsigned b0) (mbyte tfibsegs (mrestrict (w_H (W1 sp rdraw inp Hsp Hva ch E model H1H8)) FULL) a) <> None) in HUP1.
  change (option_map (fun b0 => bv_unsigned b0) (mbyte tfibsegs (mrestrict (w_H W') FULL) a) <> None).
  destruct (mbyte tfibsegs (mrestrict (w_H (W1 sp rdraw inp Hsp Hva ch E model H1H8)) FULL) a) as [b|] eqn:Eb.
  - rewrite (G _ _ Eb). discriminate.
  - exfalso. apply HUP1. try rewrite Eb. reflexivity. }
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
pose proof (HSTART_ARO sp rdraw brk inp h ch E R FULL model Hsp Hva Hch HC) as HAD.
change TSEGS with tfibsegs in HST, HAI, HAI', HAR, HAD |- *. unfold CLOSEDX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS0 HR0].
pose proof (st_ok_wle _ _ _ _ _ _ HWLE HS0) as HS. pose proof (RT _ _ HR0) as HR.
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
exact (tfib_arm_argv2 B HB ARL HCO HFILE HDIR RO sp inp (xwE E R) (xdE inp)
W' (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model ly a0 p
Hargv Hsp Hva Hve Hfit Hvfs HS HR HUP0 HAI' HAR HTOP HFI Hfs Hfds HAD).
- destruct (HST false I) as [HS0 HR0].
pose proof (st_ok_wle _ _ _ _ _ _ HWLE HS0) as HS. pose proof (RT _ _ HR0) as HR.
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
eapply (tfib_usage B HB ARL xst est XFR ESTF FPU EXS sp inp (xwE E R) (xdE inp) W' (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs))
model ly); eassumption.
Qed.
End c.
End b.
