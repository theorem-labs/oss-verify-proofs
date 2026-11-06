(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma limbs_at_cons_write : forall m A v l,
  limbs_at bgpsegs m (A + 8) l -> (0 <= A)%Z ->
  limbs_at bgpsegs (write_to_mem m (wa A) (le8 (Z_to_bv 64 v))) A (v :: l).
Proof.
  intros m A v l H HA. pose proof (limbs_at_bound _ _ _ _ H) as B.
  change (v :: l) with ([v] ++ l). apply limbs_at_app. split.
  - unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
  - cbn [length]. apply limbs_at_write_other; [exact H | lia | rewrite length_le8; lia | rewrite length_le8; right; lia].
Qed.

Section Block.
  Variables (ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n nn : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hnn : (0 <= nn < 18446744073709551616)%Z.
  Hypothesis Enn : (nn mod 64 = (64 - n) mod 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis Hfp : (8 <= fp)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * (top + 1) <= fp)%Z.

  Notation rb := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.

  Notation SH pc mm x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 T) (Z_to_bv 64 top) (Z_to_bv 64 0) x13 x14 x15 x16 x17 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Notation W := [(T, T + 8 * (top + 1))]%Z.

  Definition SINV (m1 : word -> option byte) (i : nat) : Prop :=
    limbs_at bgpsegs m1 (T + 8 * Z.of_nat i) (map (lsh_at f n) (seq i (S (length f) - i))) /\ limbs_at bgpsegs m1 fp f /\
    wr_at bgpsegs m1 T (8 * (top + 1)) /\ mem_inv bgpsegs m1 /\ munch W m m1 /\ wmono bgpsegs m m1.

  Notation HEAD mm j x28 x29 x30 :=
    (SH 0xff2e0 mm (Z_to_bv 64 (fp + -8)) (Z_to_bv 64 (fp + 8 * Z.of_nat j)) (Z_to_bv 64 (T + 8 * Z.of_nat (S j)))
        (Z_to_bv 64 T) (Z_to_bv 64 (nth (S j) f 0%Z)) (Z_to_bv 64 rb) (Z_to_bv 64 rmask) (Z_to_bv 64 n) x28 x29 x30).
  Notation KEXIT :=
    (forall m2 x5 x6 x7 x28 x29 x30,
       SINV m2 1 ->
       evt bgpsegs POST (SH 0xff304 m2 x5 x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 (nth 0 f 0%Z)) (Z_to_bv 64 rb) (Z_to_bv 64 rmask) (Z_to_bv 64 n) x28 x29 x30)).

  End Block.
