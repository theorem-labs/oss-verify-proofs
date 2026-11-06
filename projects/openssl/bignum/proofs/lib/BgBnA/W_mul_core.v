(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnModel BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_normal BnCalls W_mul_recursive W_mul_part_recursive.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnRep.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Section Core.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo R A B Dr Da Db CST : Z) (br : bignum bptr) (la lb : list Z).
  Notation SP := (bv_unsigned sp).
  Notation al := (Z.of_nat (length la)).
  Notation bl := (Z.of_nat (length lb)).
  Notation dmx := (Z.of_nat (bn_dmax br)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -112)).

  Definition mulc_pre : Prop :=
    limbs la /\ limbs lb /\ bn_okm br /\ (al < 8388608 /\ bl < 8388608)%Z /\
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * al <= lo /\ 0 <= Db /\ Db + 8 * bl <= lo /\
     0 <= CST /\ lo <= SP - 112 - CST /\ SP < 2^64)%Z /\
    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * al <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * bl <= R)%Z /\
    (Dr + 8 * dmx <= Da \/ Da + 8 * al <= Dr)%Z /\ (Dr + 8 * dmx <= Db \/ Db + 8 * bl <= Dr)%Z.
  Hypothesis PRE : mulc_pre.

  Definition mulc_mem : Prop :=
    rw_cells bgpsegs m R (bn_cells Dr br) /\ u64arr bgpsegs m Dr (wlimbs (bn_buf br)) /\
    rw_cells bgpsegs m A [C8 (wz Da)] /\ rw_cells bgpsegs m B [C8 (wz Db)] /\
    limbs_at bgpsegs m Da la /\ limbs_at bgpsegs m Db lb /\
    stk bgpsegs m lo (SP + -112) /\ mem_inv bgpsegs m.
  Hypothesis MEM : mulc_mem.

  Definition mulc_post (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (W : list (Z * Z)) (topn : nat) (w : list Z)
      (Q : (word -> option byte) -> Prop) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F (Z_to_bv 64 0xf90fc) fc None m' (seg_rom bgpsegs)
      /\ munch W m m' /\ wmono bgpsegs m m' /\ mem_inv bgpsegs m'
      /\ rw_cells bgpsegs m' R [C8 (wz Dr); C4 (wz (Z.of_nat topn)); C4 (wz dmx); C4 (wz (Z.b2z (bn_neg br))); C4 (wz (bn_flags br))]
      /\ limbs_at bgpsegs m' Dr w /\ stk bgpsegs m' lo (SP + -112) /\ Q m'.

  Definition mulc_tpre (TT Dt : Z) (Tl : list Z) : Prop :=
    limbs Tl /\ rw_cells bgpsegs m TT [C8 (wz Dt)] /\ limbs_at bgpsegs m Dt Tl /\ wr_at bgpsegs m Dt (8 * Z.of_nat (length Tl)) /\
    (0 <= Dt /\ Dt + 8 * Z.of_nat (length Tl) <= lo)%Z /\
    (R + 24 <= Dt \/ Dt + 8 * Z.of_nat (length Tl) <= R)%Z /\
    (Dt + 8 * Z.of_nat (length Tl) <= Da \/ Da + 8 * al <= Dt)%Z /\ (Dt + 8 * Z.of_nat (length Tl) <= Db \/ Db + 8 * bl <= Dt)%Z /\
    (Dr + 8 * dmx <= Dt \/ Dt + 8 * Z.of_nat (length Tl) <= Dr)%Z.

  End Core.
