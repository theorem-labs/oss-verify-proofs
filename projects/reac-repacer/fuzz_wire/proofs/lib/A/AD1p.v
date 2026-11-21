(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v at theorem-labs/oss-verify-proofs@6b32741d849a, with its module paths changed, names TfibSyms -> GrantSyms and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: tfib_drv_main takes the float-state invariant P (P YK11.fx0): the slot tfib_lib_contract_xP and the hypotheses the call loop uses after a call (AFREE, PF1, PFN, EXS) hold at every float state with P; the walk before the loop is at YK11.fx0. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AD1p.v (donor image sha256 c2c7559b29bd), with its module paths changed, names GrantSyms -> WireSyms and its addresses moved to reac-repacer/fuzz_wire's ASan build; AD1g.ly0 is applied without the hand-off state. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's channel-reader fact for fdchan's third conjunct; the CONFIG_RSEQ-sized auxiliary vector; the launch's ProcInput, mmap base and entry draw; the start-up hand-off states computed in the build; the launch input with its SIGPIPE default free; the reader fact threaded through the read loop; fdchan's third conjunct, the channel-reader flag, carried in cs_ok (co_rdr) and threaded to the fd sites; the launch's string area with the exec file name); internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e
YA01 YA02 YA00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB12 AB1h AB01r AB1n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i
YA0n YA0o YA0p.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YD1h.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AD1g AD1f AD2i AD1t.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AD1v AD1w AD2a AD26 AD22 AD1z AD2g AD2c AD2d AD29
AD2e AD1r AD1x AD27 ACfl AD1i AD1n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG05 YG0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import ACfn ACeg AE2k AD1u AD1m AD2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
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
(* P: the float states the walk may be in at the head of the driver's call loop. The start state is at YK11.fx0, and
   each call of LLVMFuzzerTestOneInput returns at some float state with P (LIBC). *)
Variable P : YK11.FPState -> Prop.
Hypothesis P0 : P YK11.fx0.
Variable B : asyms.
Hypothesis HB : WireSyms B.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, P fx -> afree_realizes (fx := fx) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBC : forall fx : YK11.FPState, P fx -> tfib_lib_contract_xP (fx := fx) B MT XM_LIB XN_LIB RLO RHI P.
Let MSITE : malloc_site_tfa B := tfib_malloc_site B ML AMALLOC.
Let RCHK : read_check_tfa B := tfib_read_check B ARDCHK.
Let MCPY : memcpy_site_tfa B := tfib_memcpy_site B AICPY.
Let FREE : free_site_tfa B := tfib_free_site B ML (AFREE YK11.fx0 P0).
Let FREEN : free_null_site_tfa B := tfib_free_null_site B ML (AFREE YK11.fx0 P0).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall fx : YK11.FPState, P fx -> printf_first_tfa (fx := fx) B xst.
Hypothesis PFN : forall fx : YK11.FPState, P fx -> printf_next_tfa (fx := fx) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d5f9 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d60e (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x157da (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall fx : YK11.FPState, P fx -> exit_site_tfa (fx := fx) B est xst.
Let EXS0 : exit_site_tfa B est xst := EXS YK11.fx0 P0.
Let RDERR : rderr_leaf_tfa B := tfib_rderr_leaf B HB ARL xst est XFR ESTF FPR EXS0.
Let REFUSED : refused_leaf_tfa B := tfib_refused_leaf B HB ARL xst est XFR ESTF RFS EXS0.
Let SHORT : short_leaf_tfa B := tfib_short_leaf B HB ARL ML xst est XFR ESTF FWS EXS0 FREE.
Let OVERRUN : overrun_leaf_tfa B := tfib_overrun_leaf B HB ARL ML xst est XFR ESTF FWS EXS0 FREE.
Let EXITL : exit_leaf_tfa B xst := tfib_exit_leaf B HB ARL xst est XFR ESTI ESTF EXS0.
Let HCO : cannot_open_tfa B := tfib_cannot_open B HB ARL xst est XFR ESTF FPO EXS0.
Let LOOPL : loop_L_x B xst := tfib_loop_L B HB ARL ML xst P
(fun fx H => tfib_lib_site_x (fx := fx) B MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN P (LIBC fx H)) PF1 PFN
(fun fx H => tfib_free_site (fx := fx) B ML (AFREE fx H)) (fun fx H => tfib_free_null_site (fx := fx) B ML (AFREE fx H))
(fun fx H => tfib_exit_leaf (fx := fx) B HB ARL xst est XFR ESTI ESTF (EXS fx H)) XFR YK11.fx0 P0.
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
eapply (tfib_usage B HB ARL xst est XFR ESTF FPU EXS0 sp brk mbase inp rdraw); eassumption.
Qed.
End c.
End b.
