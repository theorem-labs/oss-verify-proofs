(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ursh_m (n : Z) : Z := Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63.

Section Block.
  Variables (ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis Hfp : (8 <= fp)%Z.
  Hypothesis UBT : (0 < T /\ T mod 8 = 0 /\ fp mod 8 = 0)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * (top + 1) <= fp)%Z.

  Notation rb := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.


  Notation W := [(T, T + 8 * (top + 1))]%Z.


  Notation ND := (Z.lxor fp 18446744073709551615).



End Block.
