(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made as libreac/fuzz_identity's lib/BudgetWit/AsanWitness.v (PR #2351, from cgif_file_fuzzer's A/AD1p.v and A/AD1q.v) is made, over the twins of lib/BudgetWit/AW at the 16 GiB limit, from this unit's ASan usage path: the argc <> 2 branch of A/PresetD1pAPf.v's driver walk, here by A/AD27.v's tfib_usage at the start-up world W1, with the hand-off fact H8 from A/PWorldH8.v passed to tfib_main_entry and W1 as that walk passes it; A/AB1n.v's start-up, as A/PresetD1qA.v composes it; and the run ceiling at sp's window, as A/PresetD2oAPf.v takes it (YM05.RunCeilOf). This unit's record is TfibB (A/AD2l.v), its usage format site 0x158b3 (A/AD1l.v) and its library shape lib/ZTraceSpec.v checksum_shape. Adds the budget-premise witness for the ASan build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack; the start-up certificate per CONFIG_RSEQ flag with states computed in the build; the model's channel reader that fdchan asks for beside the descriptor (cs_ok's co_rdr, proved at the launch)); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.omx_clap_core.fuzz_preset Require Images Statements.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK00 YK04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0c YK0e YK0f YK09 YK0a YA01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import YA0e_w YA0d_w YA0f_w YA02_w YA00_w YA0h_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import AB1h_w AB1k_w YB1j_w AB1p_w AB1l_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import AB05_w AB01r_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YG00 YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import YG0n_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YA0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import AD1g_w AD1f_w AD2i_w AD1t_w YG0d_w AD1v_w AD1w_w AD1x_w AD27_w YG0q_w ACeg_w AE2k_w AD1u_w AD1l_w AD1j_w AD1k_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import AB1m_w AB1n_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.

(** * omx-clap-core / fuzz_preset: the budget premise on the ASan build holds at the statement's limit

    [Statements.asan_halts] carries the premise
    [~ run_scfg_budget_refused forced_only_cfg Images.asan Budgets.Standard.lim_source en inp].
    The input here is [Premises.witness_input false]: one empty argument, so
    argc = 1 and [main] writes its usage line to fd 2 and exits with status 2.

    The proof runs this unit's released proofs of that path at the 16 GiB
    limit in the twins of [lib/BudgetWit/AW]: the ASan start-up through the
    checker ([AB1n_w.tfib_startup_T1], whose certificate [AB1m_w.startup_cert]
    is the start-up check at [YA02_w.LIMIT] = 16 GiB), then [main]'s argc <> 2
    branch ([AD27_w.tfib_usage], at the start-up world [AD2i_w.W1]) with ASan's fprintf interceptor
    ([AD1l_w]) and exit ([AD1j_w]).  The released driver A/PresetD1pAPf.v takes
    that branch through PresetD1preA.tfib_usage_cf_A at a wider world; A/AD27.v's
    [tfib_usage], which this file uses, is in the released closure too.  Two
    things differ from the released walk: [YK18_w.srealizes] asks at each node
    for the budget mark's answer and the effect clause ([YK18_w.bnode_ok]), and
    [YG0n_w.ALedger] has no [al_limit] clause (Reusable/YG0n.v's
    ASAN_VM_LMIN = 2^39 <= vm_limit), which no lemma of this path reads.
    [YK18_w.srealizes_never_refused_run] turns the walk into the premise. *)

Lemma valid_sp_windowW : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Lemma diag_has_nilW : forall m fs, diag m fs [].
Proof. intros. unfold diag, wr. apply t_emit_has_nil. Qed.

Section asan.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape | 0.

Section RC. Context {rc : YM05.RunCeil}.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k_w.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k_w.est.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FPU : fprintf_s_site_tfa B est 0x158b3 (strB "usage: "%string) (strB " INPUT"%string ++ nlB) :=
  tfib_fprintf_usage_site B HB ARL HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB ARL.

(** The argc <> 2 branch of A/PresetD1pAPf.v's driver walk, by [AD27_w.tfib_usage], at [YA02_w.LIMIT]. *)
Theorem usage_main16 :
forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
(length (in_argv inp) <> 2)%nat ->
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
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hbrk Hfit Hvi Hlau Hceil Hlen Hch SINV_sp0 HC HE HM.
pose proof Hvi as (Hva & Hve & Hvfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & _).
(* The section lemmas of AD1g_w, AD1f_w and AD2i_w at this proof's names, whatever subset of their
   section arguments each one abstracts.  The tactic is local to this proof: a top-level [Ltac]
   resolves each name it uses where it is defined, and these names exist only after the [intros].
   The start-up world's w_H8 proof H8 is the one AD1f_w's tfib_AR states the world with (its H1H8,
   PWorldH8_w's H1_H8 at the section's binders), named with its value, so W1 is that world, as
   A/PresetD1pAPf.v's walk takes it. *)
let instW H := (try specialize (H YK11.fx0); try specialize (H B); try specialize (H HB);
  try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H mbase); try specialize (H inp);
  try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit);
  try specialize (H Hvl); try specialize (H Hlau); try specialize (H Hvi); try specialize (H h); try specialize (H ch);
  try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch);
  try specialize (H SINV); try specialize (H SINV_sp0); try specialize (H HC);
  try specialize (H HE); try specialize (H HM); try specialize (H rc); try specialize (H Hceil)) in
(pose proof (@AD1g_w.sliver_allowed) as SL_allowed; instW SL_allowed;
 pose proof (@AD1f_w.tfib_AR) as HAR; instW HAR;
 match type of HAR with AR _ _ _ _ (AD2i_w.W1 _ _ _ _ _ _ _ _ ?h8) _ _ => set (H8 := h8) in HAR end;
 pose proof (@AD2i_w.tfib_main_entry) as ME; instW ME; specialize (ME SL_allowed); specialize (ME H8);
 pose proof (@AD1f_w.tfib_top_ok) as HTOP; instW HTOP;
 destruct ME as (Hpc & HST & HAI & Hfs & Hfds & _);
 set (ly := AD1g_w.ly0 ch E model);
 set (W1 := AD2i_w.W1 sp rdraw inp Hsp Hva ch E model H8)).
(* The hand-off model's channel reader, which [fdchan] asks for at LPS 727298f3 beside the
   descriptor: [cs_ok]'s [co_rdr], proved at the launch ([YA02_w.model0_channel_reader]). *)
assert (Hcr : m_channel_reader model = true) by (eapply co_rdr; exact HC).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI, HAR |- *.
destruct (HST false I) as [HS HR].
eapply (tfib_usage B HB ARL xst est XFR ESTF FPU EXS sp brk mbase inp rdraw); eassumption.
Qed.

(** A/AB1n.v's start-up and then [usage_main16], as A/PresetD1qA.v composes them (its donor
    is A/AD1q.v's [tfib_srealizesX]), for an input with argc <> 2, at [YA02_w.LIMIT]. *)
Theorem asan_usage16 : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
(length (in_argv inp) <> 2)%nat ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw YA02_w.LIMIT inp) (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hceil Hlen.
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
_ (diag_has_nilW _ _)).
intros h c Hok.
destruct (HS_ok_open h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
(fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
assert (SP0 : forall E' M, YA02_w.SINV0 TSEGS TPH sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
kern execfn spd Asan.M.init_pc E' M -> uE E' e_sp0 = YA02_w.TOP sp + 8388608).
{ intros E' M HSv. eapply YA02_w.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact TSEGS | exact TFIB]. }
exact (usage_main16 sp rdraw brk mb (YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)
h ch E R FULL model _ Hsp Hbrk Hfit Hinp Hlau Hceil Hlen Hch SP0 HC HE HM).
Qed.
End RC.

(** At the run ceiling of [sp], as A/PresetD2oAPf.v takes it ([YM05.RunCeilOf]). *)
Theorem asan_usage16_top : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
(length (in_argv inp) <> 2)%nat ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw YA02_w.LIMIT inp)
(diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hlen.
exact (@asan_usage16 (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowW sp Hsp)) sp rdraw brk mb inp
  Hsp Hbrk Hmb Hfit Hinp Hlau (YM05.ceil_of_top_run _) Hlen).
Qed.
End asan.

Lemma LIMIT_is_lim_source : YA02_w.LIMIT = Budgets.Standard.lim_source.
Proof. reflexivity. Qed.

(** On every valid entry of the ASan build and every valid input whose argv has
    not two entries, no configuration the run reaches under [forced_only_cfg] at
    [Budgets.Standard.lim_source] is refused by the budget. *)
Theorem asan_usage_never_refused : forall en inp,
valid_entry OSSVerify.omx_clap_core.fuzz_preset.Images.asan en inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
~ run_scfg_budget_refused forced_only_cfg OSSVerify.omx_clap_core.fuzz_preset.Images.asan Budgets.Standard.lim_source en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hinp Hlen.
pose proof (valid_input_va_size _ Hinp) as Hv.
apply (valid_entry_sv48 _ _ _ Hv) in Hen.
destruct Hen as (Hsp & Hbrk & Hmb & Hfits & Hlau).
rewrite <- LIMIT_is_lim_source.
(* LPS 727298f3: the run is read against [run_segments], the binary's segments with the vDSO pair.
   The bound [cfg_le forced_only_cfg ACFG] is the lift lemma's own premise; [ACFG] (Reusable/R/Cfg.v,
   which this file does not import) comes from that premise's type. *)
exact (srealizes_never_refused_run forced_only_cfg TSEGS Asan.M.init_pc TPH sp brk mbase rnd YA02_w.LIMIT inp _ eq_refl
  (forced_only_cfg_least _) (asan_usage16_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfits Hinp Hlau Hlen)).
Qed.

(** [asan_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem asan_budget_witness :
exists en inp, valid_entry OSSVerify.omx_clap_core.fuzz_preset.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.omx_clap_core.fuzz_preset.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct (Premises.valid_input_entry OSSVerify.omx_clap_core.fuzz_preset.Images.asan (Premises.witness_input false)
  OSSVerify.omx_clap_core.fuzz_preset.Images.asan_wf Premises.witness_valid_input) as [en Hen].
exists en, (Premises.witness_input false).
split; [exact Hen | split; [exact Premises.witness_valid_input |]].
apply (asan_usage_never_refused en _ Hen Premises.witness_valid_input).
cbn. discriminate.
Qed.
