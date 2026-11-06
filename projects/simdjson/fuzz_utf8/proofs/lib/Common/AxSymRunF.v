(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import FPSteps. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import SymStepR AxSymExec3 AxSymExec3Sound AxSymRun3. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExecF AxSymExecFSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AX2F. Import AX2FS.
Open Scope Z_scope.

Section RunF.
Variable segs : list Segment.

(* [comment removed for export] *)
Theorem runTXF_sound : forall (fx : FPState) t K fuel stops pc sr kn nx E base rom regs,
  itab_sound segs t ->
  frm_zero (@fp_csr fx) ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
  let ss' := sym_execTXF segs t K fuel true stops (SS pc sr [] kn nx) in
  exists E' R (fx' : FPState), env_agree nx E E'
    /\ (nx <= s_next ss')%nat
    /\ regs_ok E' (s_regs ss') R
    /\ log_flat E' (s_log ss')
    /\ know_ok segs E' base (s_know ss')
    /\ frm_zero (@fp_csr fx')
    /\ msteps segs (@mkst fx regs (Z_to_bv 64 pc) base rom)
                   (@mkst fx' R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
    /\ (forall E'', env_agree (s_next ss') E' E'' ->
          @st_ok fx' segs E'' base rom ss' (@mkst fx' R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof.
  intros fx t K fuel stops pc sr kn nx E base rom regs Ht Hz HR HK Hsr Hkn.
  destruct (sym_execTXF_ex segs fx t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht Hz
              (@st_okX_entry fx segs E base rom pc sr kn nx regs HR HK Hsr Hkn))
    as (E' & R & fx' & Ha & Hle & HR' & Hlf & HK' & Hz' & Hms & HALL).
  exists E', R, fx'. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|].
  split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hz'|]. split; [exact Hms|].
  intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.
End RunF.
