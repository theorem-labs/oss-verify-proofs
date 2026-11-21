(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's ubsan binary from simdjson/fuzz_utf8's proofs/lib/AsanW/AU_vutf8.v and simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/UM_minify.v: the fallback implementation's validate_utf8 at its ubsan address, its UBSan null and pointer-overflow checks shown never to fire, proving Ubsan/PM_iface.v's vutf8_stmt. *)
(* validate_utf8 of the fallback implementation in the ubsan binary, at 0x3f130: a leaf with a 96-byte frame that holds
   s0..s10 (ra and s11 are never written).  It walks the payload 16 bytes at a time while 16 bytes remain and none of
   them has its top bit set (the 16 bytes packed into one word and masked by a word the code reads from the image, the
   ld at 0x3f25c), else one UTF-8 sequence of 1 to 4 bytes at a time.  It returns 1 at the end of the payload and 0 at
   the first bad sequence.  UBSan adds a null check of the data pointer (0x3f164) and, before the reads, checks that
   the address does not wrap: 0x3f1b4 and 0x3f1b8 on the 16-byte path, 0x3f27c, 0x3f2a0, 0x3f2d4, 0x3f2ec, 0x3f33c,
   0x3f354 and 0x3f368 on the others (each of the form [bltu a3, x] with a3 = ~D and x the offset).  All of them
   branch to the trap at 0x3f3d4.  Each is shown not taken from 0 < D, D + |pl| < 2^47 and |pl| < 2^26.  The proof
   says nothing of the result beyond 0 or 1. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ZBridge RunConst.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg PM_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import LiaTier0U StoreFast.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Section P.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (pl : list Z) (lo : Z).
  Notation n := (zlength pl).
  Notation SP := (bv_unsigned sp).
  Hypothesis DLO : 0 < D.                          (* the null check at 0x3f164 *)
  Hypothesis DHI : D + n < 2^47.                   (* below ATOP: no read address wraps *)
  Hypothesis NLT : n < 2^26.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis LO : lo <= SP - 96.
  Hypothesis FSD : D + n <= lo \/ SP <= D.         (* the payload is clear of the frame *)

  Notation W := [(SP - 96, SP)].
  Notation bs := (map (Z_to_bv 8) pl).
  Notation POST := (vutf8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo).

  (* One payload byte is readable. *)
  Lemma payload_rd : forall m1 k, bytes_at usegs m1 D bs -> 0 <= k < n ->
    exists b : byte, ov_read_bytes usegs m1 (Z_to_bv 64 (D + k)) 1 = Some [b].
  Proof.
    intros m1 k B1 Hk. unfold zlength in Hk.
    pose proof (bytes_at_read usegs m1 D bs k 1 B1 ltac:(lia) ltac:(rewrite length_map; lia)) as R.
    destruct (skipn (Z.to_nat k) bs) as [|b r] eqn:E.
    { exfalso. assert (L : length (skipn (Z.to_nat k) bs) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn, length_map in L. lia. }
    exists b. exact R.
  Qed.
  (* The same, at the address the 16-byte path forms (base D + p, offset j). *)
  Lemma payload_rd2 : forall m1 p j, bytes_at usegs m1 D bs -> 0 <= p + j < n ->
    exists b : byte, ov_read_bytes usegs m1 (Z_to_bv 64 (D + p + j)) 1 = Some [b].
  Proof. intros m1 p j B1 Hk. rewrite <- Z.add_assoc. exact (payload_rd m1 (p + j) B1 Hk). Qed.

  (* The frame after the prologue: s10..s0 at sp-88..sp-8, 8 bytes not written at sp-96. *)
  Definition FRAME (m1 : word -> option byte) : Prop := exists junk8,
    rw_cells usegs m1 (SP + -96) [CB 8 junk8; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].
  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at usegs m1 D bs /\ FRAME m1 /\ stk usegs m1 lo (SP + -96)
    /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* The loop's state: a0 the offset (or scratch), t6 and s0..s10 scratch, the rest as the code before the loop
     sets them (a3 = ~D, a4 = 0xc0, a5 = -0x41, a6 = 0xe0, a7 = 0x80, t0 = 27, t1 = 7, t2 = 0xf0, t3 = -0x110000,
     t4 = -0x100000, t5 = -8). *)
  Notation GST pc mm xa0 xt6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -96)) gp tp (Z_to_bv 64 27) (Z_to_bv 64 7) (Z_to_bv 64 240) x0 x1
             xa0 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 (Z.lxor D 18446744073709551615))
             (Z_to_bv 64 192) (Z_to_bv 64 (-65)) (Z_to_bv 64 224) (Z_to_bv 64 128)
             x2 x3 x4 x5 x6 x7 x8 x9 x10 s11
             (Z_to_bv 64 (-1114112)) (Z_to_bv 64 (-1048576)) (Z_to_bv 64 (-8)) xt6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* The epilogue (0x3f3a0): restore s0..s10, release the frame, return a0. *)
  Lemma vu_epi : forall m1 v (y5 y6 y7 x0 x1 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 y28 y29 y30 y31 : word),
    INV m1 -> (v = 0 \/ v = 1) ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (SP + -96)) gp tp y5 y6 y7 x0 x1 (Z_to_bv 64 v) ya1 ya2 ya3 ya4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x3f3a0) fc None m1 (seg_rom usegs)).
  Proof.
    intros m1 v y5 y6 y7 x0 x1 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 y28 y29 y30 y31 (BA1 & [junk8 FR] & ST & MU & WM & MI) HV.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 13 zstep.                                         (* 0x3f3a0 .. 0x3f3c8 ld s0..s10; addi sp, sp, 96; ret *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vutf8_post, VUTF8_STACK.
    do 15 eexists. exists m1. split; [unfold mkR; reflexivity|].
    split; [destruct HV as [-> | ->]; [left|right]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  Ltac pc_is p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => idtac end.
  (* A branch on payload bytes: both ways are followed, nothing about the byte is needed. *)
  Ltac br K := if_cases K; clear K.
  (* The places a path rejoins: the loop head with the next offset in t6 (0x3f1a0, or 0x3f19c for one byte), the
     return of 0 (0x3f394, or 0x3f3a0 with a0 = 0 already set) and the return of 1 (0x3f39c). *)
  Ltac fin NEXT FALSE INV1 :=
    first [ pc_is 0x3f1a0; apply NEXT; lia
          | pc_is 0x3f19c; zstep; apply NEXT; lia
          | pc_is 0x3f394; apply FALSE
          | pc_is 0x3f3a0; apply vu_epi; [exact INV1| left; reflexivity]
          | pc_is 0x3f39c; zstep; apply vu_epi; [exact INV1| right; reflexivity] ].

  (* The loop from its head (0x3f1a8) with offset pos < |pl|, by the bytes left. *)
  Lemma vu_loop : forall fuel pos m1 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 xt6 : word),
    Z.of_nat fuel > n - pos -> 0 <= pos < n -> INV m1 ->
    evt usegs POST (GST 0x3f1a8 m1 (Z_to_bv 64 pos) xt6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10).
  Proof.
    induction fuel as [|fuel IH]; intros pos m1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 xt6 FU PR INV1; [lia|].
    pose proof INV1 as (BA1 & _ & _ & _ & _ & MI).
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    assert (XD : 0 <= Z.lxor D 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
    (* Back at the loop head with the next offset q in t6: 0x3f1a0 mv a0, t6; 0x3f1a4 bgeu t6, a2 to the return of 1. *)
    assert (NEXT : forall q (ya0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 : word), pos < q <= n ->
              evt usegs POST (GST 0x3f1a0 m1 ya0 (Z_to_bv 64 q) y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)).
    { intros q ya0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 Hq.
      zstep. zstep. if_cases Kq; zify_cond Kq.
      - zstep. apply vu_epi; [exact INV1| right; reflexivity].
      - apply IH; [lia| lia| exact INV1]. }
    (* A bad sequence: 0x3f394 mv a0, zero; j 0x3f3a0. *)
    assert (FALSE : forall (ya0 yt6 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 : word),
              evt usegs POST (GST 0x3f394 m1 ya0 yt6 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)).
    { intros. zstep. zstep. apply vu_epi; [exact INV1| left; reflexivity]. }
    (* One sequence at offset pos (0x3f27c), s0 = D + pos. *)
    assert (SLOW : forall (ys0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 yt6 : word), ys0 = Z_to_bv 64 (D + pos) ->
              evt usegs POST (GST 0x3f27c m1 (Z_to_bv 64 pos) yt6 ys0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)).
    { intros ys0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 yt6 ->.
      zstep. if_cases G3; zify_cond G3; [exfalso; rewrite zb_lxor_ones in G3 by lia; lia|].   (* 0x3f27c bltu a3, a0: UBSan, D + pos wraps *)
      destruct (payload_rd m1 pos BA1 ltac:(lia)) as [b0 R0].
      zstep. clear R0.                                   (* 0x3f280 lb t6, 0(s0) *)
      zstep. br K1; try fin NEXT FALSE INV1.             (* 0x3f284 bgez t6: one byte, next at pos + 1 *)
      zstep. zstep.                                      (* 0x3f288 andi s0, t6, 0xff; 0x3f28c andi t6, s0, 0xe0 *)
      zstep. br K2.                                      (* 0x3f290 bne t6, a4: not a two-byte lead *)
      - zstep.                                           (* 0x3f2c0 andi t6, s0, 0xf0 *)
        zstep. br K6.                                    (* 0x3f2c4 bne t6, a6: not a three-byte lead *)
        + (* 0x3f328: a four-byte lead, or a bad byte *)
          zstep.                                         (* 0x3f328 andi t6, s0, 0xf8 *)
          zstep. br K7; try fin NEXT FALSE INV1.         (* 0x3f32c bne t6, t2: a bad byte, return 0 *)
          zstep.                                         (* 0x3f330 addi t6, a0, 4 *)
          zstep. if_cases K8; [apply FALSE| zify_cond K8].   (* 0x3f334 bltu a2, t6: fewer than 4 bytes left *)
          zstep.                                         (* 0x3f338 addi s1, a0, 1 *)
          zstep. if_cases G5; zify_cond G5; [exfalso; rewrite zb_lxor_ones in G5 by lia; lia|].   (* 0x3f33c bltu a3, s1: UBSan *)
          zstep.                                         (* 0x3f340 add s1, a1, s1 *)
          destruct (payload_rd m1 (pos + 1) BA1 ltac:(lia)) as [b1 R1].
          zstep. clear R1.                               (* 0x3f344 lbu s1, 0(s1) *)
          zstep.                                         (* 0x3f348 andi s2, s1, 0xc0 *)
          zstep. br K9; try fin NEXT FALSE INV1.         (* 0x3f34c bne s2, a7 *)
          zstep.                                         (* 0x3f350 addi s2, a0, 2 *)
          zstep. if_cases G6; zify_cond G6; [exfalso; rewrite zb_lxor_ones in G6 by lia; lia|].   (* 0x3f354 bltu a3, s2: UBSan *)
          zstep.                                         (* 0x3f358 add s2, a1, s2 *)
          destruct (payload_rd m1 (pos + 2) BA1 ltac:(lia)) as [b2 R2].
          zstep. clear R2.                               (* 0x3f35c lb s2, 0(s2) *)
          zstep. br K10; try fin NEXT FALSE INV1.        (* 0x3f360 blt a5, s2 *)
          zstep.                                         (* 0x3f364 addi a0, a0, 3 *)
          zstep. if_cases G7; zify_cond G7; [exfalso; rewrite zb_lxor_ones in G7 by lia; lia|].   (* 0x3f368 bltu a3, a0: UBSan *)
          zstep.                                         (* 0x3f36c add a0, a1, a0 *)
          destruct (payload_rd m1 (pos + 3) BA1 ltac:(lia)) as [b3 R3].
          zstep. clear R3.                               (* 0x3f370 lb a0, 0(a0) *)
          zstep. br K11; try fin NEXT FALSE INV1.        (* 0x3f374 blt a5, a0 *)
          do 6 zstep.                                    (* 0x3f378 .. 0x3f38c: the code point *)
          zstep. br K12; fin NEXT FALSE INV1.            (* 0x3f390 bgeu a0, t4: next at pos + 4, else 0x3f394 *)
        + (* 0x3f2c8: a three-byte lead *)
          zstep.                                         (* 0x3f2c8 addi t6, a0, 3 *)
          zstep. if_cases K13; [apply FALSE| zify_cond K13].   (* 0x3f2cc bltu a2, t6: fewer than 3 bytes left *)
          zstep.                                         (* 0x3f2d0 addi s1, a0, 1 *)
          zstep. if_cases G8; zify_cond G8; [exfalso; rewrite zb_lxor_ones in G8 by lia; lia|].   (* 0x3f2d4 bltu a3, s1: UBSan *)
          zstep.                                         (* 0x3f2d8 add s1, a1, s1 *)
          destruct (payload_rd m1 (pos + 1) BA1 ltac:(lia)) as [b1 R1].
          zstep. clear R1.                               (* 0x3f2dc lbu s1, 0(s1) *)
          zstep.                                         (* 0x3f2e0 andi s2, s1, 0xc0 *)
          zstep. br K14; try fin NEXT FALSE INV1.        (* 0x3f2e4 bne s2, a7 *)
          zstep.                                         (* 0x3f2e8 addi a0, a0, 2 *)
          zstep. if_cases G9; zify_cond G9; [exfalso; rewrite zb_lxor_ones in G9 by lia; lia|].   (* 0x3f2ec bltu a3, a0: UBSan *)
          zstep.                                         (* 0x3f2f0 add a0, a1, a0 *)
          destruct (payload_rd m1 (pos + 2) BA1 ltac:(lia)) as [b2 R2].
          zstep. clear R2.                               (* 0x3f2f4 lb a0, 0(a0) *)
          zstep. br K15; try fin NEXT FALSE INV1.        (* 0x3f2f8 blt a5, a0 *)
          do 6 zstep.                                    (* 0x3f2fc .. 0x3f310: the code point *)
          zstep. br K19; try fin NEXT FALSE INV1.        (* 0x3f314 beqz s0 *)
          zstep. br K17; try fin NEXT FALSE INV1.        (* 0x3f318 bltu s0, t0: next at pos + 3 *)
          zstep.                                         (* 0x3f31c srli a0, a0, 13 *)
          zstep. br K18; try fin NEXT FALSE INV1.        (* 0x3f320 bgeu a0, t1: next at pos + 3 *)
          zstep. fin NEXT FALSE INV1.                    (* 0x3f324 j 0x3f394 *)
      - (* 0x3f294: a two-byte lead *)
        zstep.                                           (* 0x3f294 addi t6, a0, 2 *)
        zstep. if_cases K3; [apply FALSE| zify_cond K3]. (* 0x3f298 bltu a2, t6: fewer than 2 bytes left *)
        zstep.                                           (* 0x3f29c addi s1, a0, 1 *)
        zstep. if_cases G4; zify_cond G4; [exfalso; rewrite zb_lxor_ones in G4 by lia; lia|].   (* 0x3f2a0 bltu a3, s1: UBSan *)
        zstep. zstep.                                    (* 0x3f2a4 andi s0, s0, 0x1e; 0x3f2a8 mv a0, zero *)
        zstep. br K4; try fin NEXT FALSE INV1.           (* 0x3f2ac beqz s0: overlong, to 0x3f3a0 with a0 = 0 *)
        zstep.                                           (* 0x3f2b0 add s1, a1, s1 *)
        destruct (payload_rd m1 (pos + 1) BA1 ltac:(lia)) as [b1 R1].
        zstep. clear R1.                                 (* 0x3f2b4 lb s0, 0(s1) *)
        zstep. br K5; try fin NEXT FALSE INV1.           (* 0x3f2b8 bge a5, s0: next at pos + 2 *)
        zstep. fin NEXT FALSE INV1. }                    (* 0x3f2bc j 0x3f3a0 (a0 = 0) *)
    (* The 16-byte path. *)
    zstep. zstep.                                        (* 0x3f1a8 addi t6, a0, 16; 0x3f1ac add s0, a1, a0 *)
    zstep. if_cases K16.                                 (* 0x3f1b0 bltu a2, t6: fewer than 16 bytes left *)
    { apply SLOW; word_eq_tac. }
    zify_cond K16.
    zstep. if_cases G1; zify_cond G1; [exfalso; rewrite zb_lxor_ones in G1 by lia; lia|].   (* 0x3f1b4 bltu a3, a0: UBSan, D + pos wraps *)
    zstep. if_cases G2; zify_cond G2; [exfalso; lia|].   (* 0x3f1b8 bgeu s0, t5: UBSan, D + pos within 8 of the top *)
    destruct (payload_rd m1 pos BA1 ltac:(lia)) as [c0 R0]. zstep. clear R0.              (* 0x3f1bc lbu s1, 0(s0) *)
    destruct (payload_rd2 m1 pos 1 BA1 ltac:(lia)) as [c1 R1]. zstep. clear R1.           (* 0x3f1c0 *)
    destruct (payload_rd2 m1 pos 2 BA1 ltac:(lia)) as [c2 R2]. zstep. clear R2.           (* 0x3f1c4 *)
    destruct (payload_rd2 m1 pos 3 BA1 ltac:(lia)) as [c3 R3]. zstep. clear R3.           (* 0x3f1c8 *)
    destruct (payload_rd2 m1 pos 4 BA1 ltac:(lia)) as [c4 R4]. zstep. clear R4.           (* 0x3f1cc *)
    destruct (payload_rd2 m1 pos 5 BA1 ltac:(lia)) as [c5 R5]. zstep. clear R5.           (* 0x3f1d0 *)
    destruct (payload_rd2 m1 pos 6 BA1 ltac:(lia)) as [c6 R6]. zstep. clear R6.           (* 0x3f1d4 *)
    destruct (payload_rd2 m1 pos 7 BA1 ltac:(lia)) as [c7 R7]. zstep. clear R7.           (* 0x3f1d8 *)
    do 5 zstep.                                                                            (* 0x3f1dc .. 0x3f1ec *)
    destruct (payload_rd2 m1 pos 8 BA1 ltac:(lia)) as [c8 R8]. zstep. clear R8.           (* 0x3f1f0 *)
    destruct (payload_rd2 m1 pos 9 BA1 ltac:(lia)) as [c9 R9]. zstep. clear R9.           (* 0x3f1f4 *)
    destruct (payload_rd2 m1 pos 10 BA1 ltac:(lia)) as [c10 R10]. zstep. clear R10.       (* 0x3f1f8 *)
    destruct (payload_rd2 m1 pos 11 BA1 ltac:(lia)) as [c11 R11]. zstep. clear R11.       (* 0x3f1fc *)
    do 9 zstep.                                                                            (* 0x3f200 .. 0x3f220 *)
    destruct (payload_rd2 m1 pos 12 BA1 ltac:(lia)) as [c12 R12]. zstep. clear R12.       (* 0x3f224 *)
    destruct (payload_rd2 m1 pos 13 BA1 ltac:(lia)) as [c13 R13]. zstep. clear R13.       (* 0x3f228 *)
    zstep.                                                                                 (* 0x3f22c *)
    destruct (payload_rd2 m1 pos 14 BA1 ltac:(lia)) as [c14 R14]. zstep. clear R14.       (* 0x3f230 *)
    destruct (payload_rd2 m1 pos 15 BA1 ltac:(lia)) as [c15 R15]. zstep. clear R15.       (* 0x3f234 *)
    do 8 zstep.                                                                            (* 0x3f238 .. 0x3f254 *)
    zstep. zstep.                                        (* 0x3f258 auipc s5; 0x3f25c ld s5, 0x280(s5): the mask, from the image *)
    do 6 zstep.                                          (* 0x3f260 .. 0x3f274 *)
    zstep. if_cases K.                                   (* 0x3f278 beqz s1: no byte with its top bit set *)
    - apply NEXT; lia.
    - apply SLOW; word_eq_tac.
  Qed.

  (* From the entry: the prologue, the empty payload, the null check, the loop. *)
  Lemma vu_body : bytes_at usegs m D bs -> stk usegs m lo SP -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 D) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PVUTF8) fc None m (seg_rom usegs)).
  Proof.
    intros BA1 ST MI. unfold PVUTF8.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    assert (BL : D + Z.of_nat (length bs) <= SP - 96 \/ SP <= D) by (rewrite length_map; change (Z.of_nat (length pl)) with n; lia).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 96%nat ST.
    do 12 zstep.                                         (* 0x3f130 addi sp, sp, -96; 0x3f134 .. 0x3f15c sd s0..s10 *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV1 : INV mx) by (split; [exact BA1|]; split; [eexists; exact FR|]; split; [exact ST|]; split; [exact MU|]; split; [exact WM| exact MI])
    end.
    zstep. if_cases K0; zify_cond K0.                    (* 0x3f160 beqz a2: the empty payload, return 1 *)
    - zstep. apply vu_epi; [exact INV1| right; reflexivity].
    - zstep. if_cases G0; zify_cond G0; [exfalso; lia|]. (* 0x3f164 beqz a1: UBSan, the data pointer is null *)
      do 13 zstep.                                       (* 0x3f168 .. 0x3f198: offset 0, a3 = ~D, the constants; j 0x3f1a8 *)
      apply (vu_loop (S (Z.to_nat n)) 0); [lia| lia| exact INV1].
  Qed.
End P.

Theorem vutf8_proof : vutf8_stmt.
Proof.
  unfold vutf8_stmt. intros until lo.
  intros BA PLB D0 DT NLT ST LOS FSD MI -> ->.
  pose proof (@ATOP_hi rc) as AH.
  assert (DHI : D + zlength pl < 2^47) by lia.
  assert (LO96 : lo <= bv_unsigned sp - 96) by (unfold VUTF8_STACK in LOS; exact LOS).
  assert (LO0 : 0 <= lo) by (destruct ST as [L _]; exact L).
  eapply vu_body; eassumption.
Qed.
End CANSEC1.
