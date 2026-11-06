(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac kxl_all_chunks_of m :=
  let rec go acc :=
    match goal with
    | H : rw_cells _ m _ _ |- _ =>
        lazymatch acc with
        | context [H] => fail
        | _ => lazymatch acc with tt => go H | _ => go constr:((acc, H)) end
        end
    | H : ro_cells _ m _ _ |- _ =>
        lazymatch acc with
        | context [H] => fail
        | _ => lazymatch acc with tt => go H | _ => go constr:((acc, H)) end
        end
    | _ => acc
    end in
  go tt.
Ltac kxl_all_chunks :=
  lazymatch goal with
  | |- context [MS _ _ _ _ _ ?m _] => kxl_all_chunks_of m
  end.

Tactic Notation "kx_autoLx" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  let CH := kxl_all_chunks in
  kx_autoL_core 0 stops (FUEL : nat) true CH kzs rrs.
Tactic Notation "kx_autoFLx" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  let CH := kxl_all_chunks in
  kx_autoFL_core 0 stops (FUEL : nat) true CH kzs rrs wws.
Tactic Notation "kx_autoFLAx" uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  let CH := kxl_all_chunks in
  kx_autoFLA_core 0 stops (FUEL : nat) true CH aks kzs rrs wws.
(* [comment removed for export] *)
Tactic Notation "kx_autoLcx" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let kzs := eval cbv beta iota delta [app] in (KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  let CH := kxl_all_chunks in
  kx_autoL_core 0 stops (FUEL : nat) true CH kzs rrs.
Tactic Notation "kx_autoFLAcx" uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := eval cbv beta iota delta [app] in (KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  let CH := kxl_all_chunks in
  kx_autoFLA_core 0 stops (FUEL : nat) true CH aks kzs rrs wws.
