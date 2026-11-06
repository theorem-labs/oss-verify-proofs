(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VCert VItab VDriver VSound VState2 VStepMem2 VCert2 VContract2 VDriverMatch2 VDriver2 VGamma2 VSound2 VSoundAll2 VStepMem2SoundE VSoundCall2x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Theorem check_units2_sound_closed (SEGS : list Segment) (G : genv2) (rom : word -> option byte) (done l : list vunit2) :
  genv_ok2 SEGS G rom -> Forall (unit_okS2 SEGS G rom) done -> check_units2 G done l = R2Ok -> Forall (unit_okS2 SEGS G rom) l.
Proof.
  intros GOK DONE CHK. exact (check_units2_sound SEGS G rom GOK (vstep2_sound_closed SEGS) (CALL_iface_holds SEGS G rom) l done DONE CHK).
Qed.

Theorem check_chunks2_sound (SEGS : list Segment) (G : genv2) (rom : word -> option byte) :
  genv_ok2 SEGS G rom ->
  forall chunks done, Forall (unit_okS2 SEGS G rom) done -> check_chunks2 G done chunks ->
  Forall (unit_okS2 SEGS G rom) (done ++ concat chunks)%list.
Proof.
  intros GOK. induction chunks as [|c t IH]; intros done DONE CHK; cbn [check_chunks2 concat] in CHK |- *.
  - rewrite app_nil_r. exact DONE.
  - destruct CHK as [C1 C2]. rewrite app_assoc. apply IH; [|exact C2].
    apply Forall_app. split; [exact DONE|]. exact (check_units2_sound_closed SEGS G rom done c GOK DONE C1).
Qed.

Theorem check_cert2_sound_closed (SEGS : list Segment) (G : genv2) (rom : word -> option byte) (C : vcert2) :
  genv_ok2 SEGS G rom -> check_cert2 G C = R2Ok -> Forall (unit_okS2 SEGS G rom) C.
Proof.
  intros GOK CHK. exact (check_cert2_sound SEGS G rom GOK (vstep2_sound_closed SEGS) (CALL_iface_holds SEGS G rom) C CHK).
Qed.
