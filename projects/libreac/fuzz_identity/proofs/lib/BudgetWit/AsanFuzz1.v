(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1p.v's argc = 2 branch, A/AD1q.v's tfib_srealizesX and A/IdentTop.v's instantiation, over the twins of lib/BudgetWit/AW at the 16 GiB limit, for inputs whose file is shorter than the driver's header; adds the budget-premise witness at a one-byte file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed HDIR, file1_main16, file1_16, file1_16_top, file1_never_refused); the hand-off's channel reader read from cs_ok's co_rdr in file1_main16; the lift's cfg_le premise given as forced_only_cfg_least _. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.libreac.fuzz_identity Require Images Statements.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK00 YK04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0c YK0e YK0f YK09 YK0a YA01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0e_w YA0d_w YA0f_w YA02_w YA00_w YA0h_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AB1h_w AB1k_w YB1j_w AB1p_w AB1l_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AB05_w AB01r_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0f YG00 YG01 YF0p.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG05_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD1g_w AD1f_w AD2i_w AD1t_w YG0d_w AD1v_w AD1w_w AD1x_w AD27_w YG0q_w ACeg_w AE2k_w AD1u_w AD1l_w AD1j_w AD1k_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2a_w AD26_w AD1z_w AD2g_w AD1n_w AD1i_w AF0w_w AF0q_w AD2m_w AD2k_w AD22_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require AE3j_w AE3k_w AE3n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AD2l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AB1m_w AB1n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit Require Import WitInput1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.

(** * libreac / fuzz_identity: the budget premise on the ASan build, on a file input

    [Statements.asan_halts] carries the premise
    [~ run_scfg_budget_refused forced_only_cfg Images.asan Budgets.Standard.lim_source en inp].
    [BudgetWit/AsanWitness.v] shows it on the usage path (argc <> 2), which
    makes no allocation.  This file shows it at argc = 2 on every valid input
    whose file argv[1] names is shorter than the driver's header
    ([YO05.HDR_MIN] = 6 bytes), and at the input [WitInput1.wit_input1]:
    argv = [[]; "in"], one file "in" holding the one byte 0.

    That run goes through ASan's allocator growth path: the driver mallocs its
    65536-byte buffer ([YO05.CAP0]), which ASan's secondary allocator serves
    with a fresh mapping, reads the file, finds [dlen data < HDR_MIN], frees the
    buffer, writes its short-input message and exits.  It does not reach
    [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path at the 16 GiB limit, in the
    twins of [lib/BudgetWit/AW]: [YG0n_w.ASAN_VM_LMIN] is 16 GiB and
    [YG0n_w.ALedger] keeps its [al_limit] clause there, so the allocator's room
    lemmas ([YG08_w.mroom_slack], [rroom_slack], [meter_room]) hold as
    released; the room the driver's call sites ask ([YG0n_w.mroom] inside
    [AD1v_w.drv_pre]) is proved on the driver's own states by
    [MroomB.mroom_init] and [MroomB.mroom_drv].  The driver's contracts in
    [AD1v_w] take the short-file premise, and their header step ([AD2g_w])
    goes to the short leaf only. *)

Lemma valid_sp_windowF : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Section asan.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Agree.checksum_shape_ag | 0.
Section RC. Context {rc : YM05.RunCeil}.

(** Reusable/YO01.v's [CLOSEDX_has_nil], for the trace set of an argv and a file system. *)
Lemma closedx_args_has_nil : forall argv fs, CLOSEDX_args argv fs [].
Proof.
intros argv fs. unfold CLOSEDX_args.
destruct argv as [|a0 [|p [|x r]]]; try apply diag_has_nil.
destruct (classify_open p fs); [apply diag_has_nil | |]; apply t_alt2_has_nil_l; apply diag_has_nil.
Qed.

Let B : asyms := IdentB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MSITE : malloc_site_tfa B := tfib_malloc_site B ML AMALLOC.
Let RCHK : read_check_tfa B := tfib_read_check B ARDCHK.
Let MCPY : memcpy_site_tfa B := tfib_memcpy_site B AICPY.
Let FREE : free_site_tfa B := tfib_free_site B ML AFREE.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k_w.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k_w.est.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB ARL.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB ARL HB.
Let FPO : fprintf_s_site_tfa B est AE3j_w.FMT_open (YO05.strB "cli: cannot open "%string) YO05.nlB :=
  tfib_fprintf_open_site B HB ARL HB.
Let FPR : fprintf_s_site_tfa B est AE3k_w.FMT_rderr (YO05.strB "cli: read error on "%string) YO05.nlB :=
  tfib_fprintf_rderr_site B HB ARL HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB ARL.
Let RDERR : rderr_leaf_tfa B := tfib_rderr_leaf B HB ARL xst est XFR ESTF FPR EXS.
Let REFUSED : refused_leaf_tfa B := tfib_refused_leaf B HB ARL xst est XFR ESTF RFS EXS.
Let SHORT : short_leaf_tfa B := tfib_short_leaf B HB ARL ML xst est XFR ESTF FWS EXS FREE.
Let HCO : cannot_open_tfa B := tfib_cannot_open B HB ARL xst est XFR ESTF FPO EXS.
Let HDR : hdr_tfa B := tfib_hdr B HB ARL SHORT.
Let RDD : rd0_dir_tfa B := tfib_rd0_dir B HB ARL RDERR.
Let RDF : rd0_file_tfa B := tfib_rd0_file B HB ARL ML MSITE RCHK MCPY FREE REFUSED HDR.
Let HFILE : file_arm_tfa B := tfib_file_arm B HB ARL ML MSITE RDF.
Let HDIR : dir_arm_tfa B := tfib_dir_arm B HB ARL ML MSITE RDD.

(** A/AD1p.v's [tfib_drv_main], its argc = 2 branch, at [YA02_w.LIMIT], for a
    file shorter than the header. *)
Theorem file1_main16 :
forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
(length (in_argv inp) = 2)%nat ->
(forall data, fs_lookup (in_fs inp) (nth 1 (in_argv inp) []) = Some data -> dlen data < HDR_MIN) ->
HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
(forall E' M, SINV E' M -> uE E' e_sp0 = YA02_w.TOP sp + 8388608) ->
cs_ok TSEGS TFIB YA02_w.LIMIT (YA02_w.TOP sp) SINV
(YA02_w.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
  (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
  (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02_w.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
  (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
  (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n) ->
(forall a, YA02_w.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
  (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
  (in_execfn inp) (in_sigpipe_default inp) E a = true ->
FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX_args (in_argv inp) (in_fs inp)).
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hbrk Hfit Hvi Hlau Hceil Hlen Hshort Hch SINV_sp0 HC HE HM.
pose proof Hvi as (Hva & Hve & Hvfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & _).
(* The section lemmas of AD1g_w, AD1f_w and AD2i_w at this proof's names, whatever subset of their
   section arguments each one abstracts.  The tactic is local to this proof: a top-level [Ltac]
   resolves each name it uses where it is defined, and these names exist only after the [intros]. *)
let instW H := (try specialize (H YK11.fx0); try specialize (H B); try specialize (H HB);
  try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H mbase); try specialize (H inp);
  try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit);
  try specialize (H Hvl); try specialize (H Hlau); try specialize (H Hvi); try specialize (H h); try specialize (H ch);
  try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch);
  try specialize (H SINV); try specialize (H SINV_sp0); try specialize (H HC);
  try specialize (H HE); try specialize (H HM); try specialize (H SL_allowed); try specialize (H rc); try specialize (H Hceil)) in
(pose proof (@AD1g_w.sliver_allowed) as SL_allowed; instW SL_allowed;
 pose proof (@tfib_main_entry) as ME; instW ME;
 destruct ME as (Hpc & HST & HAI & Hfs & Hfds & _);
 (* The hand-off model's channel reader, which [fdchan] asks for at LPS 727298f3 beside the
    descriptor: [cs_ok]'s [co_rdr], proved at the launch ([YA02_w.model0_channel_reader]). *)
 assert (Hcr : m_channel_reader model = true) by (eapply co_rdr; exact HC);
 set (ly := AD1g_w.ly0 ch E model);
 set (W1 := AD2i_w.W1 sp rdraw inp Hsp Hva ch E model);
 assert (HAR : AR TSEGS B ly init_state W1 FULL model) by (let L := fresh in pose proof (@tfib_AR) as L; instW L; exact L);
 assert (HTOP : AD1v_w.top_ok (bv_unsigned sp) ly) by (let L := fresh in pose proof (@tfib_top_ok) as L; instW L; exact L);
 assert (HFI : FINV ly (w_H W1) FULL) by (let L := fresh in pose proof (@tfib_finv_handoff) as L; instW L; exact L)).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI, HAR |- *.
assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
{ clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
destruct Hargv as (a0 & p & Hargv).
destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS HR].
assert (Hshort' : forall data, fs_lookup (in_fs inp) p = Some data -> dlen data < HDR_MIN).
{ intros data Hd. apply Hshort. rewrite Hargv. exact Hd. }
replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
eapply (tfib_arm_argv2 B HB ARL HCO HFILE HDIR sp brk mbase inp rdraw); eassumption.
Qed.

(** A/AD1q.v's [tfib_srealizesX] for such an input, at [YA02_w.LIMIT]. *)
Theorem file1_16 : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
(length (in_argv inp) = 2)%nat ->
(forall data, fs_lookup (in_fs inp) (nth 1 (in_argv inp) []) = Some data -> dlen data < HDR_MIN) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw YA02_w.LIMIT inp)
(CLOSEDX_args (in_argv inp) (in_fs inp)).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hceil Hlen Hshort.
pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal in_kernel]
in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
subst ab mmu cr spt.
rewrite Hkern in Hinp, Hsig, Hvl, Hlau |- *.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp (recorded_kernel kern) execfn true spd false)
with (YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
apply (tfib_startup_T1 sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
_ (closedx_args_has_nil _ _)).
intros h c Hok.
destruct (HS_ok_open h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
(fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
assert (SP0 : forall E' M, YA02_w.SINV0 TPH sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
kern execfn spd Asan.M.init_pc E' M -> uE E' e_sp0 = YA02_w.TOP sp + 8388608).
{ intros E' M HSv. eapply YA02_w.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact TSEGS | exact TFIB]. }
exact (file1_main16 sp rdraw brk mb (YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)
h ch E R FULL model _ Hsp Hbrk Hfit Hinp Hlau Hceil Hlen Hshort Hch SP0 HC HE HM).
Qed.
End RC.

Theorem file1_16_top : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
(length (in_argv inp) = 2)%nat ->
(forall data, fs_lookup (in_fs inp) (nth 1 (in_argv inp) []) = Some data -> dlen data < HDR_MIN) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw YA02_w.LIMIT inp)
(CLOSEDX_args (in_argv inp) (in_fs inp)).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hlen Hshort.
exact (@file1_16 (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowF sp Hsp)) sp rdraw brk mb inp
  Hsp Hbrk Hmb Hfit Hinp Hlau (YM05.ceil_of_top_run _) Hlen Hshort).
Qed.
End asan.

Lemma LIMIT_is_lim_source1 : YA02_w.LIMIT = Budgets.Standard.lim_source.
Proof. reflexivity. Qed.

(** On every valid entry of the ASan build and every valid input with argc = 2
    whose file is shorter than the driver's header, no configuration the run
    reaches under [forced_only_cfg] at [Budgets.Standard.lim_source] is refused
    by the budget. *)
Theorem file1_never_refused : forall en inp,
valid_entry OSSVerify.libreac.fuzz_identity.Images.asan en inp -> valid_input inp ->
(length (in_argv inp) = 2)%nat ->
(forall data, fs_lookup (in_fs inp) (nth 1 (in_argv inp) []) = Some data -> dlen data < HDR_MIN) ->
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_identity.Images.asan Budgets.Standard.lim_source en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hinp Hlen Hshort.
pose proof (valid_input_va_size _ Hinp) as Hv.
apply (valid_entry_sv48 _ _ _ Hv) in Hen.
destruct Hen as (Hsp & Hbrk & Hmb & Hfits & Hlau).
rewrite <- LIMIT_is_lim_source1.
(* LPS 727298f3: the run is read against [run_segments], the binary's segments with the vDSO pair.
   The bound [cfg_le forced_only_cfg ACFG] is the lift lemma's own premise; [ACFG] (Reusable/R/Cfg.v,
   which this file does not import) comes from that premise's type. *)
exact (srealizes_never_refused_run forced_only_cfg TSEGS Asan.M.init_pc TPH sp brk mbase rnd YA02_w.LIMIT inp _ eq_refl
  (forced_only_cfg_least _) (file1_16_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfits Hinp Hlau Hlen Hshort)).
Qed.

(** The witness input meets the path's premises: argc = 2, and the file it
    names holds one byte. *)
Lemma wit1_short : forall data, fs_lookup (in_fs wit_input1) (nth 1 (in_argv wit_input1) []) = Some data -> dlen data < HDR_MIN.
Proof.
intros data Hd. change (nth 1 (in_argv wit_input1) []) with wit_path in Hd.
rewrite wit_fs_lookup1 in Hd. injection Hd as <-. unfold dlen, HDR_MIN. rewrite wit_data1_length. lia.
Qed.

(** [asan_halts]'s three premises hold together at [wit_input1] (argv = [[]; "in"],
    the file "in" holding one zero byte), at the entry
    [Premises.valid_input_entry] gives for it. *)
Theorem asan_budget_witness_file1_at :
exists en, valid_entry OSSVerify.libreac.fuzz_identity.Images.asan en wit_input1 /\ valid_input wit_input1 /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_identity.Images.asan
    Budgets.Standard.lim_source en wit_input1.
Proof.
destruct wit_entry1 as [en Hen].
exists en. split; [exact Hen | split; [exact wit_valid_input1 |]].
exact (file1_never_refused en wit_input1 Hen wit_valid_input1 eq_refl wit1_short).
Qed.

Theorem asan_budget_witness_file1 :
exists en inp, valid_entry OSSVerify.libreac.fuzz_identity.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_identity.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct asan_budget_witness_file1_at as (en & H). exists en, wit_input1. exact H.
Qed.
