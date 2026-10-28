(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition RINV (m : word -> option byte) (f : list Z) (fp T n : Z) (m1 : word -> option byte) (i : nat) : Prop :=
  limbs_at bgusegs m1 T (map (rsh_at f n) (seq 0 i)) /\ limbs_at bgusegs m1 fp f /\
  wr_at bgusegs m1 T (8 * Z.of_nat (length f)) /\ mem_inv bgusegs m1 /\
  munch [(T, T + 8 * Z.of_nat (length f))]%Z m m1 /\ wmono bgusegs m m1.

Definition negn_m (n : Z) : Z := Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63.

Section Block.
  Variables (ra sp gp tp s0 s1 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * top <= fp)%Z.

  Notation lbm := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.

  Notation SH pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 top) (Z_to_bv 64 n) x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Notation HEAD mm i x6 x7 x11 :=
    (SH 0xff49c mm (Z_to_bv 64 (T + 8 * Z.of_nat i)) x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 n) (Z_to_bv 64 (nth i f 0%Z)) (Z_to_bv 64 (top - 1))
        (Z_to_bv 64 (fp + 8 * Z.of_nat (S i))) (Z_to_bv 64 lbm) (Z_to_bv 64 rmask) (Z_to_bv 64 (T + 8 * (top - 1))) (Z_to_bv 64 0)).
  Notation KEXIT :=
    (forall m2 x5 x6 x7 x14,
       RINV m f fp T n m2 (length f - 1) ->
       evt bgusegs POST (SH 0x10a6c8 m2 x5 x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 n) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) (Z_to_bv 64 (top - 1))
                          x14 (Z_to_bv 64 lbm) (Z_to_bv 64 rmask) (Z_to_bv 64 (T + 8 * (top - 1))) (Z_to_bv 64 0))).

  End Block.
