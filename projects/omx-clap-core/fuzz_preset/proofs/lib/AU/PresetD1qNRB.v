(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of the NR part (sections 1-3) of lib/A/HaltsClosedA.v
   (a Theorem Labs lane, a working branch defcedd3ace4, blob 7704185517; itself made from lib/A/PresetD1qA.v:68-143
   and cgif_file_fuzzer lib/A/AD1q.v:39-100), for fuzz_preset's asan-ubsan image. Lane CwD2 (a Theorem Labs lane), for the B room
   form TFIB_T_room_B (lib/AU/PresetD2oB.v) and a Theorem Labs lane's HaltsClosedB.v.
   Made by port/a2b.py (sha256 5b422ca8702e6a4ff6132a82e3aeda2473f0324f421be16d0832b0d807e1adc2; re-run with sha256
   3be214599a27a3757474026671286ffc1fd1fd79a5eb64a8bfdc3ee5c788e044 gives the same bytes) over that text, then the
   image renames a2b does not make, by hand: Asan.M. -> AsanUbsan.M. (not Budgets.Asan, the plain budget) and the
   CwD1q names _A -> _B (NR_agrees, drv_mainX_stmt(_NR), tfib_srealizesX(_NR), tfib_startup_T1, HS_ok_open). Checked
   against lib/AU/PresetD1qB.v: drv_mainX_stmt_NR_B, tfib_srealizesX_NR_B and tfib_srealizesX_NR_B_holds differ from
   drv_mainX_stmt_B, tfib_srealizesX_B and tfib_srealizesX_B_holds ONLY in the premise parameter NR (`NR en_p inp` in
   place of the plain no-refusal premise). NR_agrees_B gives back PresetD1qB.v's texts by conversion
   (drv_mainX_stmt_NR_agrees_B, tfib_srealizesX_B_of_NR).
   Pending relocB: PresetD1qB.v's imports are on a Theorem Labs lane's relocation.
   Its A twin is now lib/A/PresetD1qNRA.v (sections 1-3 of HaltsClosedA.v moved there word for word, a working branch
   d767d529aa0), which is what lib/A/PresetD2oAPf.v imports.
   proves no function (kind: composition). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB12.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1qB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* ---------------------------------------------------------------------- *)
(* 1. The premise as a parameter. *)
Definition NR_agrees_B : ExecEntry -> ProcInput -> Prop := fun en_p inp =>
  ~ run_scfg_budget_refused OSSVerify.Core.Shapes.Env.alloc_forced_only
      OSSVerify.omx_clap_core.fuzz_preset.Images.plain
      OSSVerify.Core.Shapes.Budgets.Asan.lim_source en_p inp.
Definition NR_halts_B : ExecEntry -> ProcInput -> Prop := fun _ _ => True.

(* ---------------------------------------------------------------------- *)
(* 2. The driver's conclusion over NR: PresetD1qB.v:70-87 with `NR en_p inp` in place of :75-77. *)
Definition drv_mainX_stmt_NR_B (NR : ExecEntry -> ProcInput -> Prop) (rc : YM05.RunCeil) (HS : nat -> option acs)
  : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (en_p : ExecEntry)
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
NR en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
HS h = Some ch ->
cs_ok AsanUbsan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 AsanUbsan.M.loaded_segments AsanUbsan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 AsanUbsan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 AsanUbsan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 AsanUbsan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem AsanUbsan.M.phdrs sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes AsanUbsan.M.loaded_segments (cfg_of AsanUbsan.M.loaded_segments R (pc ch) FULL model)
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* the agrees instance is today's text *)
Lemma drv_mainX_stmt_NR_agrees_B : forall rc HS, drv_mainX_stmt_B rc HS <-> drv_mainX_stmt_NR_B NR_agrees_B rc HS.
Proof. intros rc HS. split; intros H; exact H. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Start-up + driver over NR: PresetD1qB.v:91-102 with `NR en_p inp` in place of :97-99. *)
Definition tfib_srealizesX_NR_B (NR : ExecEntry -> ProcInput -> Prop) : Prop :=
forall (rc : YM05.RunCeil) (HS : nat -> option acs),
tfib_startup_T1_B HS -> drv_mainX_stmt_NR_B NR rc HS ->
forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput) (en_p : ExecEntry),
valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
NR en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
srealizes AsanUbsan.M.loaded_segments (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw YA02.LIMIT inp)
(SPECX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* PresetD1qB.v:122-143 (tfib_srealizesX_B_holds), word for word, with NR for the plain premise *)
Theorem tfib_srealizesX_NR_B_holds : forall NR, tfib_srealizesX_NR_B NR.
Proof.
intros NR rc HS HST DRV sp rdraw brk mb inp en_p Hsp Hbrk Hmb Hfit Hinp HNR Hceil.
pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp].
cbn in Hab, Hmmu. subst ab mmu.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
apply (srz_conseq AsanUbsan.M.loaded_segments _
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
[| apply t_eq_sym; apply (specx_closedx_eq (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape))].
apply (HST sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(CLOSEDX_has_nil (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) _)).
intros h c Hok.
destruct (HS_ok_open_B HS h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok)
as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
exact (DRV sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) en_p h ch E R FULL model
Hsp Hbrk Hfit Hinp HNR Hceil Hch HC HE HM).
Qed.

(* the agrees instance is today's tfib_srealizesX_B *)
Lemma tfib_srealizesX_B_of_NR : tfib_srealizesX_B.
Proof. exact (tfib_srealizesX_NR_B_holds NR_agrees_B). Qed.

