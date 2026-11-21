(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the NR part (sections 1-3) of lib/A/HaltsClosedA.v (a Theorem Labs lane; text of
   a working branch, blob e085d9c4b6, itself made from lib/A/PresetD1qA.v:68-143 and cgif_file_fuzzer
   lib/A/AD1q.v:39-100), moved WORD FOR WORD to its own file, for fuzz_preset's asan image. It is the asan twin of
   lib/AU/PresetD1qNRB.v (a Theorem Labs lane, lane CwD2), with the same role: lib/A/PresetD2oAPf.v (the room forms' proofs) and
   lib/A/HaltsClosedA.v (the halts top) both import it, so the halts top can cite the room export without a cycle
   (owner ruling relayed by a Theorem Labs lane, 2026-10-29; before the move, PresetD2oAPf.v:32 imported HaltsClosedA.v for
   NR_agrees_A and tfib_srealizesX_NR_A_holds).
   drv_mainX_stmt_NR_A, tfib_srealizesX_NR_A and tfib_srealizesX_NR_A_holds differ from lib/A/PresetD1qA.v's
   drv_mainX_stmt_A, tfib_srealizesX_A and tfib_srealizesX_A_holds ONLY in the premise parameter NR (`NR en_p inp` in
   place of the plain no-refusal premise
   `~ run_scfg_budget_refused Env.alloc_forced_only Images.plain Budgets.Asan.lim_source en_p inp`, lib/A/PresetTFIB.v:28).
   NR_agrees_A gives back PresetD1qA.v's texts by conversion (drv_mainX_stmt_NR_agrees, tfib_srealizesX_A_of_NR); the
   halts top takes NR_halts_A := fun _ _ => True.
   proves no function (kind: composition). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1qA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* ---------------------------------------------------------------------- *)
(* 1. The premise as a parameter. *)
Definition NR_agrees_A : ExecEntry -> ProcInput -> Prop := fun en_p inp =>
  ~ run_scfg_budget_refused OSSVerify.Core.Shapes.Env.alloc_forced_only
      OSSVerify.omx_clap_core.fuzz_preset.Images.plain
      OSSVerify.Core.Shapes.Budgets.Asan.lim_source en_p inp.
Definition NR_halts_A : ExecEntry -> ProcInput -> Prop := fun _ _ => True.

(* ---------------------------------------------------------------------- *)
(* 2. The driver's conclusion over NR: PresetD1qA.v's drv_mainX_stmt_A with `NR en_p inp` in place of its no-refusal
      premise. *)
Definition drv_mainX_stmt_NR_A (NR : ExecEntry -> ProcInput -> Prop) (rc : YM05.RunCeil) (HS : Z -> nat -> option acs)
  : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (en_p : ExecEntry)
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
NR en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
HS (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp) (SINV_A sp rdraw brk mbase inp) (argH_A sp rdraw inp)
(in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (E0_A sp rdraw brk inp) n) ->
(forall a, argH_A sp rdraw inp E a = true -> FULL a = FULL0_A sp rdraw mbase inp a) ->
srealizes Asan.M.loaded_segments (cfg_of Asan.M.loaded_segments R (pc ch) FULL model)
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* the agrees instance is today's text *)
Lemma drv_mainX_stmt_NR_agrees : forall rc HS, drv_mainX_stmt_A rc HS <-> drv_mainX_stmt_NR_A NR_agrees_A rc HS.
Proof. intros rc HS. split; intros H; exact H. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Start-up + driver over NR: PresetD1qA.v's tfib_srealizesX_A with `NR en_p inp` in place of its no-refusal
      premise. *)
Definition tfib_srealizesX_NR_A (NR : ExecEntry -> ProcInput -> Prop) : Prop :=
forall (rc : YM05.RunCeil) (HS : Z -> nat -> option acs),
tfib_startup_T1_A HS -> drv_mainX_stmt_NR_A NR rc HS ->
forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput) (en_p : ExecEntry),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
NR en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
srealizes Asan.M.loaded_segments (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mb rdraw YA02.LIMIT inp)
(SPECX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* PresetD1qA.v's tfib_srealizesX_A_holds, word for word, with NR for the plain premise *)
Theorem tfib_srealizesX_NR_A_holds : forall NR, tfib_srealizesX_NR_A NR.
Proof.
intros NR rc HS HST DRV sp rdraw brk mb inp en_p Hsp Hbrk Hmb Hfit Hinp Hlau HNR Hceil.
pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal in_kernel]
in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
subst ab mmu cr spt.
rewrite Hkern in Hinp, Hsig, Hvl, Hlau, HNR |- *.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp (recorded_kernel kern) execfn true spd false)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
apply (srz_conseq Asan.M.loaded_segments _
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)));
[| apply t_eq_sym; apply (specx_closedx_eq (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape))].
apply (HST sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd))
(CLOSEDX_has_nil (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) _)).
intros h c Hok.
destruct (HS_ok_open_A HS h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
(fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
exact (DRV sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) en_p
h ch E R FULL model Hsp Hbrk Hmb Hfit Hinp Hlau HNR Hceil Hch HC HE HM).
Qed.

(* the agrees instance is today's tfib_srealizesX_A *)
Lemma tfib_srealizesX_A_of_NR : tfib_srealizesX_A.
Proof. exact (tfib_srealizesX_NR_A_holds NR_agrees_A). Qed.
