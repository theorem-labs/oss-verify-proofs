(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c, with the theorem statements restated in the form rc.2 states them; adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AB01.v (HS_tfib, HS_tfib_In) and AB1n.v (HS_ok, tfib_startup_T1, HS_ok_open), with its module paths changed; the start-up certificate's hole states are the field of class StartData and tfib_startup_T1 is the field of class StartThm, Section hypotheses until plugin-hostd/fuzz_command's certificate is generated; class TfibHolesStkAux states that every hole state reads the auxv and AT_RANDOM words (StartStkAuxG.stk_aux_chk), which the driver needs for the stack's presence at main. *)
(* Modified by Theorem Labs, 2026-11: made from A/CmdStartCert.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 by the port of its source A/CmdStartCert.v (taken three-way onto this twin), with the declarations the twin cut left cut and its modules kept on their twins. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK0c YK0e YK09 YA01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YA0c_w YA0e_w YA02_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB12.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import AB1h_w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
(* The hand-off states of the start-up run, per value [r] of its CONFIG_RSEQ flag (A/AB01r.v computes them in
   the build): [HS_tfib_r r h] is hand-off [h]'s state at flag [r] (None for a hand-off the run never reaches),
   [HS_tfib_list_r r] the states at flag [r], [HS_tfib_list_all] both flags' states, which the driver's computed
   checks run over. *)
Class StartData := {
HS_tfib_r : Z -> nat -> option acs;
HS_tfib_list_r : Z -> list acs;
HS_tfib_list_all : list acs;
HS_tfib_r_In_r : forall r h ch, HS_tfib_r r h = Some ch -> In ch (HS_tfib_list_r r);
HS_tfib_r_In : forall r h ch, HS_tfib_r r h = Some ch -> In ch HS_tfib_list_all }.
Section f.
#[local] Existing Instance YK11.fx0.
Context {SD : StartData}.
(* The launch input is YA02's: the kernel record [kb], the exec file name and the SIGPIPE disposition [sdef] are
   free, so the hand-off state is the one of the run's own CONFIG_RSEQ flag, as A/AB1n.v states it. *)
Definition HS_ok (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word)
(argv envp : list (list byte)) (fs0 : Fs.Fs) (stdin : InputStream) (uid gid hw : word)
(groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
(kb : KernelBuild) (execfn : list byte) (sdef : bool) (fsq : Fs.Fs) (c : config) : Prop :=
exists ch E R FULL model,
HS_tfib_r (rseq_z (kb_rseq kb)) h = Some ch
/\ c = cfg_of TSEGS R (pc ch) FULL model
/\ cs_ok TSEGS TFIB YA02_w.LIMIT (YA02_w.TOP sp)
(SINV0 TPH sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef Asan.M.init_pc)
(argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model.
Class StartThm : Prop := { tfib_startup_T1 :
forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
(uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
(kb : KernelBuild) (execfn : list byte) (sdef : bool),
valid_sp sp -> valid_brk TSEGS brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_nofile nofile ->
valid_sigmask (YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
valid_launch (YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
(YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
forall T : TSet, T [] ->
(forall h c, HS_ok h sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
(fs_seed_tmp fs tmp) c -> srealizes TSEGS c T) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02_w.LIMIT
(YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T }.
Lemma HS_ok_open : forall h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c,
HS_ok h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c ->
exists ch E R FULL model,
HS_tfib_r (rseq_z (kb_rseq kb)) h = Some ch /\ c = cfg_of TSEGS R (pc ch) FULL model
/\ cs_ok TSEGS TFIB YA02_w.LIMIT (YA02_w.TOP sp)
(SINV0 TPH sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef Asan.M.init_pc)
(argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model
/\ (forall n, (n < NX0G)%nat -> ev E n = ev (E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) n)
/\ (forall a, argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef E a = true ->
FULL a = wrap_mem (YA02_w.inp argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) mbase TPH
(Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp rdraw a)
/\ eb E = eb (E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
Proof.
intros h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c
(ch & E & R & FULL & model & Hh & Hc & HC).
exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
End f.
