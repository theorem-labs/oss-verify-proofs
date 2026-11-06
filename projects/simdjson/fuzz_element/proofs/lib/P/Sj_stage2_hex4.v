(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].

Section Hex4.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Definition hid (P : Prop) : Prop := P.
  Definition hex4v (q : Z) : Z :=
    or4 (dig (420 + B bs (q + 1))) (dig (210 + B bs (q + 2))) (dig (630 + B bs q)) (dig (0 + B bs (q + 3))).

  Lemma hex4_call : forall (Q : machine_state -> Prop) (R q : Z)
      x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (R = 0x418f4 \/ R = 0x4198c)%Z ->
    bytes_at psegs m1 (e_BUF E) (padded_bytes bs) -> mem_inv psegs m1 ->
    (0 <= q /\ q + 3 < e_len E + 64)%Z ->
    (forall y11 y12 y13 y14,
       evt psegs Q (S2R E R (Z_to_bv 64 R) x5 x6 x7 x8 x9 (Z_to_bv 64 (hex4v q)) y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                        x28 x29 x30 x31 F fc m1)) ->
    evt psegs Q (S2R E 0x50480 (Z_to_bv 64 R) x5 x6 x7 x8 x9 (Z_to_bv 64 (e_BUF E + q)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                     x28 x29 x30 x31 F fc m1).
  Proof using OK.
    intros Q R q x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m1 HR BUFRO MI HQ K.
    change (hid (R = 0x418f4 \/ R = 0x4198c)%Z) in HR.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (B_range bs q BOK) as HB0. pose proof (B_range bs (q + 1) BOK) as HB1.
    pose proof (B_range bs (q + 2) BOK) as HB2. pose proof (B_range bs (q + 3) BOK) as HB3.
    pose proof (padded_bytes_blen bs) as PBL.
    s2_env OK.
    zstep. s2norm. zstep. s2norm. zstep. s2norm. zstep. s2norm. zstep. s2norm.
    do 9 (zstep; s2norm).
    pose proof (dig_read m1 (420 + B bs (q + 1)) (wa (4 * B bs (q + 1) + 84048 + 1680)) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD1.
    pose proof (dig_read m1 (210 + B bs (q + 2)) (wa (4 * B bs (q + 2) + 84048 + 840)) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD2.
    pose proof (dig_read m1 (630 + B bs q) (wa (84048 + 4 * (B bs q + 630))) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD0.
    pose proof (dig_read m1 (0 + B bs (q + 3)) (wa (84048 + 4 * B bs (q + 3))) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD3.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep.
    repeat match goal with |- context [bv_unsigned (sx32 (Z_to_bv 64 (dig ?x)))] =>
      change (bv_unsigned (sx32 (Z_to_bv 64 (dig x)))) with (sxu (dig x)) end.
    match goal with |- context [Z.lor (Z.lor (Z.lor (sxu ?a) (sxu ?b)) (sxu ?c)) (sxu ?e)] =>
      change (Z.lor (Z.lor (Z.lor (sxu a) (sxu b)) (sxu c)) (sxu e)) with (or4 a b c e) end.
    unfold hex4v in K. unfold hid in HR. destruct HR as [-> | ->]; zstep; apply K.
  Qed.
End Hex4.
