(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling RunWord InitStack.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Stdio.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff A0LZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import ALayout AFakeInst F_fs_body F_fs_f5.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import RDriverA_ctx RDriverA_iface.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require IcptIC.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit GlueA0 GlueAllocLay GlueAllocInst.
Import ListNotations.
Open Scope Z_scope.

Section Inst.
  Variable PZ : mem -> Prop.

  Hypothesis FZ_GEN : forall (HC : HasCeiling) (HG : HasGuard) (IC : icpt_contracts) (FI : fs_if) (AI : am_if FI) (J : a0_judg FI AI)
      (AC : am_contracts FI AI J)
      (ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi) (AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi)
      (SM0 : stack_malloc_stmt FI 0) (SM1 : stack_malloc_stmt FI 1) (SM2 : stack_malloc_stmt FI 2) (SM3 : stack_malloc_stmt FI 3)
      (SM4 : stack_malloc_stmt FI 4) (F5 : set_shadow_f5_stmt),
      fuzz_one_stmtA FI AI J PZ.

  #[using="FZ_GEN"] Theorem INST_of_FZ : forall (HC : HasCeiling) (HG : HasGuard) (V : nat -> Z) inp en ms mo,
    valid_input inp -> valid_entry imgA0 en inp -> alloc_ceiling = LO (en_sp en) -> amain_at_V V en inp ms mo ->
    exists (FI : fs_if) (AI : am_if FI),
      (forall lo hi, a0_static lo hi -> am_static FI AI lo hi)
      /\ am_contracts FI AI (JA FI AI)
      /\ fuzz_one_stmtA FI AI (JA FI AI) PZ
      /\ alloc_init_stmt FI AI V (en_sp en) (in_fs inp) mo.
  Proof.
    intros HC HG V inp en ms mo VI VE CEIL AMA.
    destruct (inst_core V inp en ms mo VI VE CEIL AMA) as (AO & AI & AMS & ASL & AC & AINIT).
    exists (FI_B (AL_of V) AO), AI.
    split; [exact AMS|]. split; [exact AC|]. split; [| exact AINIT].
    exact (FZ_GEN HC HG IcptIC.IC_all (FI_B (AL_of V) AO) AI (JA (FI_B (AL_of V) AO) AI) AC ASL AMS
             (stack_malloc_ok0 (AL_of V) AO) (stack_malloc_ok1 (AL_of V) AO) (stack_malloc_ok2 (AL_of V) AO)
             (stack_malloc_ok3 (AL_of V) AO) (stack_malloc_ok4 (AL_of V) AO) set_shadow_f5_ok).
  Qed.
End Inst.
