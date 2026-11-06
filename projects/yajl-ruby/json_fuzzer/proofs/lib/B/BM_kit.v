(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Export StepA AImages ExecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Notation A_IMG_LO := (0x10000%Z) (only parsing).
Notation A_IMG_HI := (0x603000%Z) (only parsing).

(* [comment removed for export] *)
Ltac finish ::=
  first [ apply evt_done | apply evtA_done ];
  lazymatch goal with |- ?P0 ?ms => try unfold P0 end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac finishA2 :=
  first [ apply evt_done | apply evtA_done ];
  lazymatch goal with |- ?P0 ?ms => try unfold P0 | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac addr_diff_guard k :=
  let b := eval vm_compute in (andb (Z.leb 0 k) (Z.leb k 4096))%Z in
  lazymatch b with true => k end.
Ltac addr_diff E A ::=
  let k :=
    lazymatch E with
    | Z.add ?X ?c1 =>
        lazymatch A with
        | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
        | X => zlit c1
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    | _ =>
        lazymatch A with
        | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
        | E => constr:(0%Z)
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    end in
  addr_diff_guard k.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition hidden (P : Prop) : Prop := P.
End RC__1.
Ltac hideH H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Ltac unhideH H := unfold hidden in H.
