(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (MAIN and pmain_exit_from_pat_main take the launch values (launchT); plain_impl_from_main re-proved over the ProcInput: it builds the launch values from the input, passes the startup spec and init_ms their new arguments, and proves dvalid_sp's new entry-stack bounds from launch_facts; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StartupM.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX StdioFiles Startup_A Startup Exit RDriver_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Image.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import InitMem RunConst.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section Compose.
Hypothesis STDIO_EXIT : stdio_exit_spec_stmt ps_so set_so_ps.
  Hypothesis MAIN : forall (rc : runConstT) (lx : launchT), @pmain_stmt rc lx.
#[using="STDIO_EXIT"] Lemma pexit_from_pat_exit : forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop) code ms,
pat_exit code s ms -> implM usegs (Driver.exit_model Prog.io code) s Q ms.
Proof.
intros s Q code ms H.
destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & -> & H).
destruct H as (ST & TD & EXL & GF & FA & FIN & GCX & LCH & DSO & [reg AX] & OFL & SIN & SOU & SEU & SOF & SEF & GG & GU & MI & Htp & Ha0 & Ht & LO & LOLO & SP47).
unfold Prog.io.
eapply (Exit.exit_spec ps_so set_so_ps STDIO_EXIT reg s Q);
[exact ST | exact TD | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact AX | exact OFL | exact SIN | exact SOU | exact SEU | exact SOF | exact SEF | exact GG | exact GU | exact MI | exact Htp | exact Ha0 | exact Ht | exact LO | exact LOLO | exact SP47].
Qed.
#[using="STDIO_EXIT MAIN"] Lemma pmain_exit_from_pat_main : forall (rc : runConstT) (lx : launchT) (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) ms
(Q : Empty_set -> PState -> machine_state -> Prop),
dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
pat_main sp0 argv envp uid hw draw CAN ms ->
implM usegs
(mbind (main_model Prog.io raw_malloc raw_free UREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
(fun code => exit_model Prog.io code))
(ps_init (reservedZ usegs) ATOP) Q ms.
Proof.
intros rc lx sp0 argv envp uid hw draw ms Q VSP VARGV VENVP HSEC AM.
eapply (Monad.implM_bind usegs).
- exact (MAIN rc lx sp0 argv envp uid hw draw ms VSP VARGV VENVP HSEC AM).
- intros code s' ms'' AE. cbn in AE. apply pexit_from_pat_exit. exact AE.
Qed.
#[using="STDIO_EXIT MAIN"] Theorem plain_impl_from_main : forall (en : ExecEntry) (inp : ProcInput),
valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
valid_input_either inp ->
impl usegs (at_node usegs) (Prog.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
(ms0 usegs u_init_pc u_phdrs en inp).
Proof.
intros [sp0 brk mb draw] inp VE VI.
pose proof (valid_input_either_launch _ VI) as VLAUNCH.
rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE.
destruct VE as (VSP & _ & _ & VFIT & VOK). destruct VI as (VARGV & VENVP & _).
pose proof (launch_facts inp sp0 brk mb draw VLAUNCH VOK) as (_ & HPAD & HDEP & HTOP & _ & _).
unfold ms0. cbn [en_sp en_draw en_mmap_base].
unfold Prog.prog, Prog.prog_itree.
set (rc := run_consts_of (mkEntry sp0 brk mb draw) (pcanary draw) VSP).
set (lx := launch_of inp sp0 mb draw).
change (entry_atop (mkEntry sp0 brk mb draw)) with (@ATOP rc).
set (s0 := PState.ps_init (Image.reservedZ usegs) (@ATOP rc)).
eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
2:{ intros [v ?] ms' _. destruct v. }
unfold Prog.prog_with, Prog.startup.
change (implM usegs
(mbind (mbind (msys NSetTid dec_set_tid) (fun _ => mret tt))
(fun _ => mbind (main_model Prog.io raw_malloc raw_free UREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z (in_argv inp)))
(fun code => exit_model Prog.io code)))
s0 (fun _ _ _ => True) (init_ms usegs u_init_pc u_phdrs sp0 mb draw inp)).
eapply (startup_implM_of usegs s0 _ _
(@pat_main lx sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw (pcanary draw))).
- eapply (pstartup_spec inp mb brk sp0 draw); eassumption.
- intros ms' AM.
assert (DV : @dvalid_sp rc lx sp0 (in_argv inp) (in_envp inp)).
{ split; [exact VSP|]. split; [reflexivity|]. split; [exact VFIT|].
split; [exact HPAD|]. split; [exact HDEP| exact HTOP]. }
apply (pmain_exit_from_pat_main rc lx sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw ms' _
DV VARGV VENVP eq_refl AM).
Qed.
End Compose.
