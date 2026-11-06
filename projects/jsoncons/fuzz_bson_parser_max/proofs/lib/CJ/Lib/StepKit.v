(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem Cells Exec.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Ltac1.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma evt_step_gen : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w i sz ms1,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
  (forall P : machine_result machine_state -> Prop,
     P (MachineOk ms1) -> P (lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m))) ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro w i sz ms1 Hf He Hd HL Hc.
  eapply evt_step; [split; [reflexivity|] | exact Hc].
  rewrite (step_gen segs R F pc fc rv m ro w i sz Hf He Hd). apply HL. reflexivity.
Qed.

Ltac2 Type exn ::= [ StepKit_stash (constr) ].
(* [comment removed for export] *)
Ltac2 probe_concl (tac : unit -> unit) : constr :=
  Control.plus (fun () => tac (); let g := Control.goal () in Control.zero (StepKit_stash g))
               (fun e => match e with StepKit_stash g => g | _ => Control.zero e end).
Ltac2 collapse_conv (tac : Ltac1.t) : unit :=
  let g0 := Control.goal () in
  let g := probe_concl (fun () => Ltac1.run tac) in
  if Constr.equal g0 g then () else ltac1:(g |- change_no_check g) (Ltac1.of_constr g).
(* [comment removed for export] *)
Ltac collapse_conv tac := let f := ltac2:(tac |- Control.enter (fun () => collapse_conv tac)) in f tac.
