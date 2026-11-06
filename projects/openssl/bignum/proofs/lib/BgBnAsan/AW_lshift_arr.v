(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma limbs_at_cons_writeA : forall m A v l,
  limbs_at bgasegs m (A + 8) l -> (0 <= A)%Z ->
  limbs_at bgasegs (write_to_mem m (wa A) (le8 (Z_to_bv 64 v))) A (v :: l).
Proof.
  intros m A v l H HA. pose proof (limbs_at_bound _ _ _ _ H) as B.
  change (v :: l) with ([v] ++ l). apply limbs_at_app. split.
  - unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
  - cbn [length]. apply limbs_at_write_other; [exact H | lia | rewrite length_le8; lia | rewrite length_le8; right; lia].
Qed.

Definition negn_mA (n : Z) : Z := Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63.

Section Block.
  Variables (ra sp gp tp s0 s1 a4 s2 s3 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * (top + 1) <= fp)%Z.

  Hypothesis ACF : acc bgasegs m fp (8 * top).
  Hypothesis ACT : acc bgasegs m T (8 * (top + 1)).
  Hypothesis ALF : (fp mod 8 = 0)%Z.
  Hypothesis ALT : (T mod 8 = 0)%Z.
  Hypothesis OFFT : offshW [(T, T + 8 * (top + 1))]%Z.

  Notation rb := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.

  Notation SH pc mm x5 x6 x7 x10 x11 x13 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 (Z_to_bv 64 0) x13 a4 x15 x16 x17 s2 s3 (Z_to_bv 64 n) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Notation W := [(T, T + 8 * (top + 1))]%Z.

  Definition SINV (m1 : word -> option byte) (i : nat) : Prop :=
    limbs_at bgasegs m1 (T + 8 * Z.of_nat i) (map (lsh_at f n) (seq i (S (length f) - i))) /\ limbs_at bgasegs m1 fp f /\
    wr_at bgasegs m1 T (8 * (top + 1)) /\ mem_inv bgasegs m1 /\ munch W m m1 /\ wmono bgasegs m m1.

  Definition BND : Prop := ((0 <= fp /\ fp + 8 * top <= 140737488355328) /\ (0 <= T /\ T + 8 * (top + 1) <= 140737488355328))%Z.

  Notation HEAD mm j x30 x31 :=
    (SH 0x234504 mm (Z_to_bv 64 rb) (Z_to_bv 64 rmask) (Z_to_bv 64 (Z.of_nat j + 3)) (Z_to_bv 64 T) (Z_to_bv 64 (T + 8 * Z.of_nat (S j)))
        (Z_to_bv 64 (fp + 8 * Z.of_nat j)) (Z_to_bv 64 (nth (S j) f 0%Z)) (Z_to_bv 64 n) (Z_to_bv 64 2)
        (Z_to_bv 64 (fp + 8 * Z.of_nat j)) (Z_to_bv 64 (T + 8 * Z.of_nat (S j))) x30 x31).
  Notation KEXIT :=
    (forall m2 x7 x11 x13 x28 x29 x30 x31,
       SINV m2 1 ->
       evt bgasegs POST (SH 0x234554 m2 (Z_to_bv 64 rb) (Z_to_bv 64 rmask) x7 (Z_to_bv 64 T) x11 x13 (Z_to_bv 64 (nth 0 f 0%Z)) (Z_to_bv 64 n) (Z_to_bv 64 2)
                          x28 x29 x30 x31)).

  End Block.
