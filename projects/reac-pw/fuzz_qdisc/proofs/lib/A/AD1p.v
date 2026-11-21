(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_identity/lib/A/AD1p.v (donor image sha256 c954b804786c), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput and its entry-launch facts; the channel-reader conjunct of fdchan; the CONFIG_RSEQ-symbolic auxiliary vector; YA02's launch spine in the argument lists; the launch variables of the start-up plan (V_G, V_HW and the CONFIG_RSEQ flag); the stack strings at the top of the stack VMA (with the exec file name); the launch's free SIGPIPE disposition; the start-up hand-off states made in the build per CONFIG_RSEQ flag); internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_qdisc.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AB12 AB1h AB01r AB1n.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YD1h.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AD1g AD1f AD2i AD1t.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AD1v AD1w AD2a AD26 AD22 AD1z AD2g AD2c AD2d AD29 AD2e AD1r AD1x AD27 ACfl AD1i AD1n.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import ACfn ACeg AE2k AD1u AD1m AD2k.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
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
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBC : tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Let MSITE : malloc_site_tfa B := tfib_malloc_site B ML AMALLOC.
Let RCHK : read_check_tfa B := tfib_read_check B ARDCHK.
Let MCPY : memcpy_site_tfa B := tfib_memcpy_site B AICPY.
Let FREE : free_site_tfa B := tfib_free_site B ML AFREE.
Let FREEN : free_null_site_tfa B := tfib_free_null_site B ML AFREE.
Let LIB : lib_site_x B := tfib_lib_site_x B MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN LIBC.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d5c3 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d5d8 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x157c5 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
Let RDERR : rderr_leaf_tfa B := tfib_rderr_leaf B HB ARL xst est XFR ESTF FPR EXS.
Let REFUSED : refused_leaf_tfa B := tfib_refused_leaf B HB ARL xst est XFR ESTF RFS EXS.
Let SHORT : short_leaf_tfa B := tfib_short_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let OVERRUN : overrun_leaf_tfa B := tfib_overrun_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let EXITL : exit_leaf_tfa B xst := tfib_exit_leaf B HB ARL xst est XFR ESTI ESTF EXS.
Let HCO : cannot_open_tfa B := tfib_cannot_open B HB ARL xst est XFR ESTF FPO EXS.
Let LOOPL : loop_L_x B xst := tfib_loop_L B HB ARL ML xst LIB PF1 PFN FREE FREEN EXITL XFR.
Let RUNQM : run_QM_tfa B := tfib_run_QM B HB ARL ML MSITE MCPY FREE xst EXITL XFR LOOPL.
Let RUNQ : run_Q_tfa B := tfib_run_Q B HB ARL xst LOOPL RUNQM.
Let POSTP : post_P_tfa B := tfib_post_P B HB ARL RUNQ.
Let HDR : hdr_tfa B := tfib_hdr B HB ARL SHORT OVERRUN POSTP.
Let RDD : rd0_dir_tfa B := tfib_rd0_dir B HB ARL RDERR.
Let RDF : rd0_file_tfa B := tfib_rd0_file B HB ARL ML MSITE RCHK MCPY FREE REFUSED HDR.
Let HFILE : file_arm_tfa B := tfib_file_arm B HB ARL ML MSITE RDF.
Let HDIR : dir_arm_tfa B := tfib_dir_arm B HB ARL ML MSITE RDD.
(* LPS 727298f3: the driver's main over the hand-off state of the run's own CONFIG_RSEQ flag
   ([AB01r.HS_tfib_r]), with the stack invariant abstract and the launch's [entry_launch_ok_va],
   the statement [AD1q.drv_mainX_stmt] reads (as libreac/fuzz_boxreg's A/AD1q.v).  The section
   lemmas of AD1g/AD1f/AD2i/AD2k are taken at this lemma's arguments, whatever subset each one
   abstracts ([inst]), as A/AD1d.v does. *)
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
FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hbrk Hfit Hvi Hlau Hceil Hch SINV_sp0 HC HE HM.
pose proof Hvi as (Hva & Hve & Hvfs & _).
assert (Hvl : valid_launch inp) by (unfold valid_input in Hvi; tauto).
pose proof AD1g.sliver_allowed as SLA.
pose proof AD2i.tfib_main_entry as ME.
pose proof tfib_AR as HAR.
pose proof tfib_top_ok as HTOP.
pose proof tfib_finv_handoff as HFI.
(* The section lemmas at this proof's names, whatever subset of their section arguments each one abstracts.
   The tactic is local to this proof: a top-level [Ltac] resolves each name it uses where it is defined,
   and these names exist only after the [intros] above (OSSV-648's fuzz_pcap). *)
let inst H := (try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H mbase); try specialize (H inp); try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H Hvl); try specialize (H Hlau); try specialize (H Hvi); try specialize (H h); try specialize (H ch); try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H SINV); try specialize (H SINV_sp0); try specialize (H HC); try specialize (H HE); try specialize (H HM); try specialize (H SLA); try specialize (H rc); try specialize (H Hceil)) in
(inst SLA; inst ME; inst HAR; inst HTOP; inst HFI).
destruct ME as (Hpc & HST & HAI & Hfs & Hfds & _).
(* LPS 727298f3: [fdchan]'s third conjunct.  [cs_ok]'s last field [co_rdr] (YA0e.v:250)
   carries the launch's channel-reader flag, which [YA02.init_cs_ok] proves by
   computation; [eapply] leaves the projection's other arguments to [HC]. *)
assert (Hcr : m_channel_reader model = true) by (eapply co_rdr; exact HC).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI, HAR |- *. unfold CLOSEDX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
eapply (tfib_arm_argv2 B HB ARL HCO HFILE HDIR sp brk mbase inp rdraw); eassumption.
- destruct (HST false I) as [HS HR].
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
eapply (tfib_usage B HB ARL xst est XFR ESTF FPU EXS sp brk mbase inp rdraw); eassumption.
Qed.
End c.
End b.
