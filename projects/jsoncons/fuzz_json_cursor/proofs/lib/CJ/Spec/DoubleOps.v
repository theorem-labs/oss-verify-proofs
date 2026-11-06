(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import FP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition two_p1023 : word := Z_to_bv 64 0x7FE0000000000000.
Definition two_m969  : word := Z_to_bv 64 0x0360000000000000.

Definition scalbn_u (n : Z) : word := Z_to_bv 64 (Z.shiftl (1023 + n) 52).

Definition scalbn_reduce (x : word) (n : Z) : word * Z :=
  if (1023 <? n)%Z then
    let y := fmul_d RNE x two_p1023 in let n := (n - 1023)%Z in
    if (1023 <? n)%Z then
      let y := fmul_d RNE y two_p1023 in let n := (n - 1023)%Z in
      (y, if (1023 <? n)%Z then 1023%Z else n)
    else (y, n)
  else if (n <? -1022)%Z then
    let y := fmul_d RNE x two_m969 in let n := (n + 969)%Z in
    if (n <? -1022)%Z then
      let y := fmul_d RNE y two_m969 in let n := (n + 969)%Z in
      (y, if (n <? -1022)%Z then (-1022)%Z else n)
    else (y, n)
  else (x, n).

Definition scalbn_model (x : word) (n : Z) : word :=
  let (y, n') := scalbn_reduce x n in fmul_d RNE y (scalbn_u n').
