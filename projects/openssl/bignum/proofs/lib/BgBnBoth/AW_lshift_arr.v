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
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnU Require Import LshiftArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop AsLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2317732 => 2
  | 2317744 => 1
  | 2317748 => 2
  | 2317812 => 1
  | 2317816 => 2
  | 2317820 => 1
  | 2317828 => 2
  | 2317856 => 1
  | 2317888 => 2
  | 2317892 => 2
  | 2317920 => 1
  | 2317924 => 2
  | 2317928 => 1
  | 2317932 => 1
  | 2317936 => 1
  | 2317940 => 1
  | 2317944 => 2
  | 2317952 => 2
  | 2317968 => 1
  | 2317972 => 1
  | 2317976 => 2
  | 2317980 => 1
  | 2317984 => 1
  | 2317988 => 1
  | 2317992 => 1
  | 2317996 => 2
  | 2318000 => 2
  | 2318004 => 1
  | 2318008 => 2
  | 2318036 => 1
  | 2318040 => 2
  | 2318044 => 1
  | 2318048 => 1
  | 2318052 => 1
  | 2318056 => 1
  | 2318060 => 2
  | 2318064 => 1
  | 2318068 => 2
  | 2318132 => 1
  | 2318148 => 2
  | 2318164 => 2
  | 2318168 => 1
  | 2318172 => 1
  | 2318176 => 2
  | 2318256 => 2
  | 2318260 => 2
  | 2318284 => 1
  | 2318288 => 1
  | 2318292 => 2
  | 2318312 => 2
  | 2318316 => 2
  | 2318320 => 1
  | 2318324 => 2
  | 2318356 => 2
  | 2318360 => 1
  | 2318364 => 2
  | 2318404 => 2
  | 2318408 => 2
  | 2318436 => 2
  | 2318440 => 2
  | 2318508 => 1
  | 2318512 => 2
  | 2318516 => 1
  | 2318524 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Lemma limbs_at_cons_writeA : forall m A v l,
  limbs_at bgbsegs m (A + 8) l -> (0 <= A)%Z ->
  limbs_at bgbsegs (write_to_mem m (wa A) (le8 (Z_to_bv 64 v))) A (v :: l).
Proof.
  intros m A v l H HA. pose proof (limbs_at_bound _ _ _ _ H) as B.
  change (v :: l) with ([v] ++ l). apply limbs_at_app. split.
  - unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
  - cbn [length]. apply limbs_at_write_other; [exact H | lia | rewrite length_le8; lia | rewrite length_le8; right; lia].
Qed.

Section Block.
  Variables (ra sp gp tp s0 s1 a4 s2 s3 s6 s7 s8 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * (top + 1) <= fp)%Z.

  Hypothesis ACF : acc bgbsegs m fp (8 * top).
  Hypothesis ACT : acc bgbsegs m T (8 * (top + 1)).
  Hypothesis ALF : (fp mod 8 = 0)%Z.
  Hypothesis ALT : (T mod 8 = 0)%Z.
  Hypothesis OFFT : offshW [(T, T + 8 * (top + 1))]%Z.

  Hypothesis T0 : (0 < T)%Z.

  Notation rb := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.

  Notation SH pc mm x6 x7 x11 x13 x15 x25 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 fp) x6 x7 s0 s1 (Z_to_bv 64 T) x11 (Z_to_bv 64 0) x13 a4 x15 (Z_to_bv 64 T) (Z_to_bv 64 1) s2 s3 (Z_to_bv 64 n) (Z_to_bv 64 SHB)
             s6 s7 s8 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgbsegs)).

  Notation W := [(T, T + 8 * (top + 1))]%Z.

  Definition SINV (m1 : word -> option byte) (i : nat) : Prop :=
    limbs_at bgbsegs m1 (T + 8 * Z.of_nat i) (map (lsh_at f n) (seq i (S (length f) - i))) /\ limbs_at bgbsegs m1 fp f /\
    wr_at bgbsegs m1 T (8 * (top + 1)) /\ mem_inv bgbsegs m1 /\ munch W m m1 /\ wmono bgbsegs m m1.

  Definition BND : Prop := ((0 <= fp /\ fp + 8 * top <= 140737488355328) /\ (0 <= T /\ T + 8 * (top + 1) <= 140737488355328))%Z.

  Notation ND := (Z.lxor fp 18446744073709551615).
  Notation HEAD mm j x11 x13 x25 :=
    (SH 0x235f3c mm (Z_to_bv 64 n) (Z_to_bv 64 ND) x11 x13 (Z_to_bv 64 (Z.of_nat (S (S j)))) x25
        (Z_to_bv 64 rb) (Z_to_bv 64 (nth (S j) f 0%Z)) (Z_to_bv 64 rmask) (Z_to_bv 64 1)).
  Notation KEXIT :=
    (forall m2 x11 x25,
       SINV m2 1 ->
       evt bgbsegs POST (SH 0x236018 m2 (Z_to_bv 64 n) (Z_to_bv 64 ND) x11 (Z_to_bv 64 (nth 0 f 0%Z)) (Z_to_bv 64 1) x25
                           (Z_to_bv 64 rb) (Z_to_bv 64 (nth 0 f 0%Z)) (Z_to_bv 64 rmask) (Z_to_bv 64 1))).

  End Block.
