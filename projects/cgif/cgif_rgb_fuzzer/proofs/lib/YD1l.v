(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (trb_drv_main and trb_srealizes take valid_entry's launch conjunct entry_launch_ok_va and the mmap base, with SINV0, argH0, E0 and wrap_mem over the run's ProcInput; valid_input's conjuncts, valid_launch and the recorded-kernel one among them, taken by name; and the input passed whole to trb_startup_T1 in place of its fields rebuilt through YA02.inp; trb_drv_main's hand-off premise over the hand-off states computed from the run at the run's own CONFIG_RSEQ flag, YB01r.v; valid_launch and the channel-reader flag, the latter read from the hand-off state's cs_ok, passed to the two arms, and trb_startup_T1 given valid_input's reader clause). *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK15 YK18 YK0d YK0f YK0a YA0c YA0e YA01 YA02 YA00 YB11 YB1g YB01r
YB1m YG0h YG00 YG01 YG0u YF9j YQ0j YQ0b YQ0i YQ0a YQ04 YO3p YK05 YA0i YA0l YA0m YA0n
YB1u YD1e YD1d YD1c YD2e YD1p YG0d YD1q YD1r YD25 YD21 YD1x YD1u YD2c
YD28 YD29 YD24 YD2a YD1m YD1s YD22 YCrd YD1f YD1j YG05 YG0w
YK0p YCrc YD27 YD1n.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
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
Lemma CLOSED_has_nil : forall inp, CLOSED inp [].
Proof.
intros inp. unfold CLOSED, CLOSED_args.
destruct (in_argv inp) as [|a0 [|p [|x r]]]; try apply diag_has_nil.
destruct (classify_open p (in_fs inp)); [apply diag_has_nil | |]; apply t_alt2_has_nil_l; apply diag_has_nil.
Qed.
#[local] Existing Instance YK11.fx0.
Section b. Context {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis HB : TrbSyms B.
Let ARL : AR_laws trbsegs B := AR_laws_ok trbsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE_A : forall fx : YK11.FPState, @afree_realizes fx rc trbsegs B.
Let AFREE : afree_realizes trbsegs B := AFREE_A _.
Hypothesis AICPY : aintrin_realizes trbsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Hypothesis LIBC : trb_rlibV_contract_all B.
Let MSITE : malloc_site_tfa B := trb_malloc_site B ML AMALLOC.
Let RCHK : read_check_tfa B := trb_read_check B ARDCHK.
Let MCPY : memcpy_site_tfa B := trb_memcpy_site B AICPY.
Let FREE : free_site_tfa B := trb_free_site B ML AFREE.
Let FREEN : free_null_site_tfa B := trb_free_null_site B ML AFREE.
Let FREE_A : forall fx : YK11.FPState, @free_site_tfa fx rc B := fun fx => trb_free_site B ML (AFREE_A fx).
Let FREEN_A : forall fx : YK11.FPState, @free_null_site_tfa fx rc B := fun fx => trb_free_null_site B ML (AFREE_A fx).
Let LIB_A : forall fx : YK11.FPState, @lib_site_rgb fx rc B := trb_rlib_site B LIBC.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1_A : forall fx : YK11.FPState, @printf_first_tfa fx rc B xst.
Hypothesis PFN_A : forall fx : YK11.FPState, @printf_next_tfa fx rc B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d7c4 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d7d9 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x1591f (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS_A : forall fx : YK11.FPState, @exit_site_tfa fx rc B est xst.
Let EXS : exit_site_tfa B est xst := EXS_A _.
Let OOM : oom_leaf_tfa B := trb_oom_leaf B HB ARL xst est XFR ESTF FWS EXS.
Let RDERR : rderr_leaf_tfa B := trb_rderr_leaf B HB ARL xst est XFR ESTF FPR EXS.
Let REFUSED : refused_leaf_tfa B := trb_refused_leaf B HB ARL xst est XFR ESTF RFS EXS.
Let SHORT : short_leaf_tfa B := trb_short_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let OVERRUN : overrun_leaf_tfa B := trb_overrun_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let EXITL : exit_leaf_tfa B xst := trb_exit_leaf B HB ARL xst est XFR ESTI ESTF EXS.
Let HCO : cannot_open_tfa B := trb_cannot_open B HB ARL xst est XFR ESTF FPO EXS.
Let EXITL_A : forall fx : YK11.FPState, @exit_leaf_tfa fx rc B xst := fun fx => trb_exit_leaf B HB ARL xst est XFR ESTI ESTF (EXS_A fx).
Let LOOPL : loop_L_tfa B xst := trb_loop_L B HB ARL ML xst LIB_A PF1_A PFN_A FREE_A FREEN_A EXITL_A XFR fp_frm_zero_fx0.
Let RUNQM : run_QM_tfa B := trb_run_QM B HB ARL ML MSITE MCPY FREE xst EXITL XFR LOOPL.
Let RUNQ : run_Q_tfa B := trb_run_Q B HB ARL xst LOOPL RUNQM.
Let POSTP : post_P_tfa B := trb_post_P B HB ARL RUNQ.
Let HDR : hdr_tfa B := trb_hdr B HB ARL SHORT OVERRUN POSTP.
Let RDD : rd0_dir_tfa B := trb_rd0_dir B HB ARL RDERR.
Let RDF : rd0_file_tfa B := trb_rd0_file B HB ARL ML MSITE OOM RCHK MCPY FREE REFUSED HDR.
Let HFILE : file_arm_tfa B := trb_file_arm B HB ARL ML MSITE OOM RDF.
Let HDIR : dir_arm_tfa B := trb_dir_arm B HB ARL ML MSITE OOM RDD.
(* The start-up lemmas of YD2e, YD1d and YD1c take, after their sections close, only
   the section facts they use, in section order.  [inst_run] offers each fact in that
   order and skips a fact the lemma does not take. *)
Ltac inst_run H B HB sp rdraw brk mb inp Hsp Hva Hve Hvl Hlau h ch E R FULL model Hch HC HE HM rc Hceil :=
try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw);
try specialize (H brk); try specialize (H mb); try specialize (H inp); try specialize (H Hsp);
try specialize (H Hva); try specialize (H Hve); try specialize (H Hvl); try specialize (H Hlau);
try specialize (H h); try specialize (H ch); try specialize (H E); try specialize (H R);
try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC);
try specialize (H HE); try specialize (H HM); try specialize (H rc); try specialize (H Hceil).
Theorem trb_drv_main : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
(* #38: valid_entry's launch conjunct, in the slot the bridges put it (YZ01.v:76):
   after entry_stack_fits, before valid_input.  It is NOT derivable from the four
   others (75d69e00:Run.v:3732-3740 makes it a fifth conjunct), so it is threaded.
   Twin of YD0b.v:85-92; keep the two symmetric. *)
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
valid_input inp ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_trb_r (APC.rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
(* #38: YA02's section is over the run's input now (YA02.v:36-45), so [SINV0]
   carries [TRB] and [mbase] and takes [inp] where it took argv/envp/uid/hw, and
   [argH0]/[E0]/[wrap_mem] follow - the shape YB1m.v:84-88 and YD2e.v:188-201
   state.  [uid] and [hw] come off [inp] and are no longer passed.
   Twin of YD0b.v:96-105; keep the two symmetric. *)
cs_ok TSEGS TRB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TRB TPH sp rdraw brk mb inp)
(YA02.argH0 sp rdraw inp) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk inp) n) ->
(forall a, YA02.argH0 sp rdraw inp E a = true ->
FULL a = wrap_mem inp mb TPH (Z_to_bv 64 (a_entry TRB)) sp rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSED inp).
Proof.
intros sp rdraw brk mb inp h ch E R FULL model Hsp Hbrk Hfit Hlau Hinp Hceil Hch HC HE HM.
pose proof Hinp as (Hva & Hve & Hvfs & _).
assert (Hvl : valid_launch inp) by (unfold valid_input in Hinp; tauto).
pose proof sliver_allowed as SLA.
inst_run SLA B HB sp rdraw brk mb inp Hsp Hva Hve Hvl Hlau h ch E R FULL model Hch HC HE HM rc Hceil.
pose proof trb_main_entry as TME.
inst_run TME B HB sp rdraw brk mb inp Hsp Hva Hve Hvl Hlau h ch E R FULL model Hch HC HE HM rc Hceil.
destruct (TME SLA) as (Hpc & HST & HAI & Hfs & Hfds & _).
pose proof trb_AR_init as TAR.
inst_run TAR B HB sp rdraw brk mb inp Hsp Hva Hve Hvl Hlau h ch E R FULL model Hch HC HE HM rc Hceil.
destruct TAR as (ly & HAR & HTOP).
(* LPS 727298f3: [fdchan]'s third conjunct.  [cs_ok]'s last field [co_rdr] (YA0e.v)
   carries the launch's channel-reader flag, which the start-up proves from the
   input's [in_channel_reader] (YA02.model0_channel_reader); [eapply] leaves the
   projection's other arguments to [HC]. *)
assert (Hcr : m_channel_reader model = true) by (eapply co_rdr; exact HC).
rewrite Hpc. change (cfg_of TSEGS R TRB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TRB_MAIN) FULL (seg_rom trbsegs)) model).
change TSEGS with trbsegs in HST, HAI, HAR |- *. unfold CLOSED.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS HR].
replace (CLOSED_args (in_argv inp) (in_fs inp)) with (CLOSED_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
exact (trb_arm_argv2 B HB ARL HCO HFILE HDIR sp inp mb brk rdraw (xwE E R) (xdE inp)
(W1 sp rdraw inp Hsp Hva ch E model) (mkst R (Z_to_bv 64 TRB_MAIN) FULL (seg_rom trbsegs)) model ly a0 p
Hargv Hsp Hva Hve Hfit Hvfs Hvl Hlau HS HR HAI HAR HTOP Hfs Hfds Hcr).
- destruct (HST false I) as [HS HR].
replace (CLOSED_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ clear -Hlen. unfold CLOSED_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
exact (trb_usage B HB ARL xst est XFR ESTF FPU EXS sp inp mb brk rdraw (xwE E R) (xdE inp) (W1 sp rdraw inp Hsp Hva ch E model) (mkst R (Z_to_bv 64 TRB_MAIN) FULL (seg_rom trbsegs))
model ly Hsp Hva Hve Hfit Hvl Hlau Hlen HS HR HAI HAR HTOP Hfs Hfds Hcr).
Qed.
Theorem trb_srealizes : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
valid_input inp ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (CLOSED inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hlau Hinp Hceil.
(* #38: valid_input's conjuncts are projected by name rather than by a positional
   proj2 chain, because conjunct 17 was inserted once already and a positional
   chain would silently move with it (75d69e00:Run.v:4584-4597). *)
assert (Hva : valid_argv (in_argv inp)) by (unfold valid_input in Hinp; tauto).
assert (Hve : valid_envp (in_envp inp)) by (unfold valid_input in Hinp; tauto).
assert (Huid : valid_id (in_uid inp)) by (unfold valid_input, valid_creds in Hinp; tauto).
assert (Hhw : valid_hwcap (in_hwcap inp)) by (unfold valid_input in Hinp; tauto).
assert (Hlaunch : valid_launch inp) by (unfold valid_input in Hinp; tauto).
assert (Hrec : in_kernel inp = recorded_kernel (in_kernel inp)) by (unfold valid_input in Hinp; tauto).
(* #38: the old proof broke [inp] into fifteen fields and rebuilt it through
   [YA02.inp] so the startup could see [in_abort_on_term] and [in_va_size] as the
   literals [false] and [Sv48].  [ProcInput] has twenty fields now and
   [trb_startup_T1] (YB1m.v:51-66) quantifies over [inp] itself - its kernel
   premise is [recorded_kernel], not a literal build - so nothing has to be taken
   apart: the record is passed through whole. *)
apply (trb_startup_T1 sp rdraw brk mb inp
Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrec (valid_input_channel_reader inp Hinp)
(CLOSED inp) (CLOSED_has_nil _)).
intros h c Hok.
destruct (HS_ok_open h sp rdraw brk mb inp (in_fs inp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
exact (trb_drv_main sp rdraw brk mb inp h ch E R FULL model
Hsp Hbrk Hfit Hlau Hinp Hceil Hch HC HE HM).
Qed.
End d.
End b.
