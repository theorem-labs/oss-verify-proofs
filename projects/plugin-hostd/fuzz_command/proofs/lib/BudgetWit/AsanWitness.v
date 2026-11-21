(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v and A/AD1q.v, with their module paths changed, names TfibSyms -> CmdBSyms and their addresses moved to plugin-hostd/fuzz_command's ASan build; the start-up certificate is taken through the classes of lib/A/CmdStartCert.v. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1p.v's argc <> 2 branch, A/AD1q.v's tfib_srealizesX and A/CmdTFIBLib.v's run-ceiling instantiation (cmd_srealizesX_top), over the twins of lib/BudgetWit/AW at the 16 GiB limit, as libreac/fuzz_identity's lib/BudgetWit/AsanWitness.v is made (its text, at this unit's module paths, with the allocator record CmdB of A/AD2l.v, the usage format at 0x158ea, the library shape cmd_shape of A/CmdShape.v, AD1p's H8 hand-off fact from A/CmdWorldH8.v, the start-up classes filled by the instances of A/CmdStartInst.v, and the module destructor's contract DtorExit, which the exit site takes and lib/Theorems.v fills with A/Rt/RtDtorExit.v's cmd_dtor_exit); adds the budget-premise witness for the ASan build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 as A/AD1p.v's and A/AD1q.v's ports (the hand-off state of the run's own CONFIG_RSEQ flag, the stack invariant abstract with its one consequence SINV0_sp0, the mmap base and the launch's fifth valid_entry conjunct), and the walk read over the run's segment list (srealizes_never_refused_run), as plugin-hostd/fuzz_reply's copy of this file; the model's channel reader that fdchan asks for beside the descriptor, carried from the hand-off's cs_ok (its co_rdr field, proved at the launch). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.plugin_hostd.fuzz_command Require Images Statements.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK00 YK04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK0c YK0e YK0f YK09 YK0a YA01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YA0e_w YA0d_w YA0f_w YA02_w YA00_w YA0h_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB12.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import AB1h_w AB1k_w YB1j_w AB1p_w AB1l_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f YG00 YG01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YG0n_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YA0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import CmdStartCert_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import AD1g_w AD1f_w AD2i_w AD1t_w CmdWorldH8_w YG0d_w AD1v_w AD1w_w AD1x_w AD27_w YG0q_w ACeg_w AE2k_w AD1u_w AD1l_w AD1j_w AD1k_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import CmdStartInst_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require CmdShape.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require RtDtorExit_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.

(** * plugin-hostd / fuzz_command: the budget premise on the ASan build holds at the statement's limit

    [Statements.asan_halts] carries the premise
    [~ run_scfg_budget_refused forced_only_cfg Images.asan Budgets.Standard.lim_source en inp].
    The input here is [Premises.witness_input false]: one empty argument, so
    argc = 1 and [main] writes its usage line to fd 2 and exits with status 2.

    The proof is the released proof of that path, run at the 16 GiB limit in
    the twins of [lib/BudgetWit/AW]: the ASan start-up through the checker
    ([CmdStartCert_w.tfib_startup_T1], the field of class [StartThm] that
    [CmdStartInst_w.cmd_start_thm] fills with [AB1n_w.tfib_startup_T1], whose
    certificate [AB1m_w.startup_cert] is the start-up check at
    [YA02_w.LIMIT] = 16 GiB), then [main]'s argc <> 2 branch
    ([AD27_w.tfib_usage]) with ASan's fprintf interceptor ([AD1l_w]) and exit
    ([AD1j_w]).  Two things differ from the released walk: [YK18_w.srealizes]
    asks at each node for the budget mark's answer and the effect clause
    ([YK18_w.bnode_ok]), and [YG0n_w.ALedger] has no [al_limit] clause
    (ASAN_VM_LMIN = 2^39 <= vm_limit), which no lemma of this path reads.
    [YK18_w.srealizes_never_refused_run] turns the walk into the premise. *)

Lemma valid_sp_windowW : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Lemma diag_has_nilW : forall m fs, diag m fs [].
Proof. intros. unfold diag, wr. apply t_emit_has_nil. Qed.

Section asan.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.CmdShape.cmd_shape | 0.
#[local] Existing Instance RtDtorExit_w.cmd_dtor_exit.

Section RC. Context {rc : YM05.RunCeil}.
Let B : asyms := CmdB.
Let HB : CmdBSyms B := CmdB_syms.
Let ARL : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k_w.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k_w.est.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FPU : fprintf_s_site_tfa B est 0x158ea (strB "usage: "%string) (strB " INPUT"%string ++ nlB) :=
  tfib_fprintf_usage_site B HB ARL HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB ARL.

(** A/AD1p.v's [tfib_drv_main], its argc <> 2 branch, at [YA02_w.LIMIT]: LPS 727298f3's hand-off state of the run's
    own CONFIG_RSEQ flag, the stack invariant abstract with its entry-sp fact, the mmap base and the launch's fifth
    valid_entry conjunct. *)
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
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hbrk Hfit Hinp Hlau Hceil Hlen Hch SP0 HC HE HM.
pose proof Hinp as (Hva & Hve & Hvfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & _).
(* The section lemmas of the AW twins of A/AD1g.v, A/AD2i.v and A/CmdWorldH8.v that main reads, with their section
   arguments given by name in their declaration order (each one only if the lemma takes it), as A/AD1p.v's [inst_drv];
   the start-up classes are filled by the instances of BudgetWit/AW/CmdStartInst_w.v.  [instW] and [getW] are local
   to this proof: a top-level [Ltac] resolves each name it uses where it is defined, and these names exist only after
   the [intros]. *)
let instW H := (try specialize (H B); try specialize (H HB);
  try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H mbase);
  try specialize (H inp); try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit);
  try specialize (H Hvl); try specialize (H Hlau); try specialize (H Hinp); try specialize (H h); try specialize (H ch);
  try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch);
  try specialize (H SINV); try specialize (H SP0); try specialize (H HC); try specialize (H HE); try specialize (H HM);
  try specialize (H SLA); try specialize (H H8); try specialize (H rc); try specialize (H Hceil)) in
let getW L := (let H := fresh "L" in pose proof L as H; instW H; exact H) in
(pose (SLA := ltac:(getW AD1g_w.sliver_allowed));
 pose (H8 := ltac:(getW CmdWorldH8_w.H1_H8));
 pose proof tfib_main_entry as TME; instW TME;
 destruct TME as (Hpc & HST & HAI & Hfs & Hfds & _);
 set (ly := AD1g_w.ly0 ch E model);
 set (W1 := AD2i_w.W1 sp rdraw inp Hsp Hva ch E model H8);
 assert (HAR : AR TSEGS B ly init_state W1 FULL model) by (getW tfib_AR);
 assert (HTOP : AD1v_w.top_ok (bv_unsigned sp) ly) by (getW tfib_top_ok)).
(* The hand-off model's channel reader, which [fdchan] asks for at LPS 727298f3 beside the
   descriptor: [cs_ok]'s [co_rdr], proved at the launch ([YA02_w.model0_channel_reader]). *)
assert (Hcr : m_channel_reader model = true) by (eapply co_rdr; exact HC).
rewrite Hpc. change (cfg_of TSEGS R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI, HAR |- *.
destruct (HST false I) as [HS HR].
eapply (tfib_usage B HB ARL xst est XFR ESTF FPU EXS sp brk mbase inp rdraw); eassumption.
Qed.

(** A/AD1q.v's [tfib_srealizesX] for an input with argc <> 2, at [YA02_w.LIMIT]. *)
Theorem asan_usage16 : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
(length (in_argv inp) <> 2)%nat ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw YA02_w.LIMIT inp)
(diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
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
assert (SP0 : forall E' M, YA02_w.SINV0 TPH sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
kern execfn spd Asan.M.init_pc E' M -> uE E' e_sp0 = YA02_w.TOP sp + 8388608).
{ intros E' M HSv. eapply YA02_w.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact TSEGS | exact TFIB]. }
exact (usage_main16 sp rdraw brk mb (YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)
h ch E R FULL model _ Hsp Hbrk Hfit Hinp Hlau Hceil Hlen Hch SP0 HC HE HM).
Qed.
End RC.

(** At the run ceiling of [sp], as A/CmdTFIBLib.v's [cmd_srealizesX_top]. *)
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
valid_entry OSSVerify.plugin_hostd.fuzz_command.Images.asan en inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
~ run_scfg_budget_refused forced_only_cfg OSSVerify.plugin_hostd.fuzz_command.Images.asan Budgets.Standard.lim_source en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hinp Hlen.
pose proof (valid_input_va_size _ Hinp) as Hv.
apply (valid_entry_sv48 _ _ _ Hv) in Hen.
destruct Hen as (Hsp & Hbrk & Hmb & Hfits & Hlau).
rewrite <- LIMIT_is_lim_source.
(* LPS 727298f3: the run is read against [run_segments], the binary's segments with the vDSO pair *)
exact (srealizes_never_refused_run forced_only_cfg TSEGS Asan.M.init_pc TPH sp brk mbase rnd YA02_w.LIMIT inp _ eq_refl
  (forced_only_cfg_least _) (asan_usage16_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfits Hinp Hlau Hlen)).
Qed.

(** [asan_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem asan_budget_witness :
exists en inp, valid_entry OSSVerify.plugin_hostd.fuzz_command.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.plugin_hostd.fuzz_command.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct (Premises.valid_input_entry OSSVerify.plugin_hostd.fuzz_command.Images.asan (Premises.witness_input false)
  OSSVerify.plugin_hostd.fuzz_command.Images.asan_wf Premises.witness_valid_input) as [en Hen].
exists en, (Premises.witness_input false).
split; [exact Hen | split; [exact Premises.witness_valid_input |]].
apply (asan_usage_never_refused en _ Hen Premises.witness_valid_input).
cbn. discriminate.
Qed.
