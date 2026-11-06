(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling RunWord InitStack.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsBoth B0Img MainEntryBoth B0Handoff B0LZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import ALayout AFakeInst.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import RealizeS SeamA0 A0Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import RDriverA_ctx.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G Require Import GlueKit GlueA0 GlueAllocLay GlueAllocInit.
Import ListNotations.
Open Scope Z_scope.

Theorem inst_core : forall {HC : HasCeiling} (V : nat -> Z) inp en ms mo,
  valid_input inp -> valid_entry imgA0 en inp -> alloc_ceiling = LO (en_sp en) -> amain_at_V V en inp ms mo ->
  exists (AO : alayout_ok (AL_of V)) (AI : am_if (FI_B (AL_of V) AO)),
    (forall lo hi, a0_static lo hi -> am_static (FI_B (AL_of V) AO) AI lo hi)
    /\ (forall lo hi, am_static (FI_B (AL_of V) AO) AI lo hi -> a0_static lo hi)
    /\ am_contracts (FI_B (AL_of V) AO) AI (JA (FI_B (AL_of V) AO) AI)
    /\ alloc_init_stmt (FI_B (AL_of V) AO) AI V (en_sp en) (in_fs inp) mo.
Proof.
  intros HC V inp en ms mo VI VE CEIL AMA.
  assert (ESF : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp)).
  { pose proof (valid_input_va_size _ VI) as Hsv48. destruct en as [sp brk mb dr]. rewrite (valid_entry_sv48 _ _ _ Hsv48) in VE. cbn [imgA0] in VE. cbn.
    destruct VE as (_ & _ & _ & D). exact D. }
  destruct AMA as (w & m & Hms & VR & PINS & HMF & HPF & MI & STK & HARG & SH0 & HMFr & AMo).
  destruct PINS as (_ & _ & _ & PSP & _).
  pose proof (proj1 (Forall_app _ _ _) HPF) as [HP _].
  assert (CEILsp : alloc_ceiling = bv_unsigned (en_sp en) - 8388608) by (rewrite CEIL; reflexivity).
  assert (SP184 : bv_unsigned (en_sp en) + 184 <= 2^47).
  { unfold entry_stack_fits, entry_stack_span, sp_window_hi, auxv_size in ESF.
    pose proof (total_arg_bytes_nonneg (in_argv inp)). pose proof (total_arg_bytes_nonneg (in_envp inp)). change (2^47) with 140737488355328. lia. }
  exists (AO_run V (en_sp en) HP PSP CEILsp), (AI_run V (en_sp en) mo HP PSP CEILsp SP184).
  split; [exact (AMS_run V (en_sp en) mo HP PSP CEILsp SP184)|].
  split; [exact (ASL_run V (en_sp en) mo HP PSP CEILsp SP184)|].
  split; [exact (AC_run V (en_sp en) (in_fs inp) mo HP AMo PSP CEILsp SP184)|].
  intros w' m' HMw _ _ _ _ SHV.
  exact (alloc_init_run V (en_sp en) (in_fs inp) mo HP AMo PSP CEILsp SP184 w' m' HMw SHV).
Qed.
