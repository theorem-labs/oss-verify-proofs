(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's plain binary from simdjson/fuzz_utf8's proofs/lib/AsanW/AU_vutf8.v and simdjson/fuzz_minifyimpl's proofs/lib/Plain/PM_minify.v: the fallback validate_utf8 leaf of the plain binary (no shadow checks, an 80-byte frame saving s0..s8), proved against PM_iface.vutf8_stmt. *)
(* validate_utf8 of simdjson's fallback implementation in the plain binary (PM_iface.PVUTF8 = 0x3e49c), a leaf.
   Its code, as decoded from the plain image:
   - 0x3e49c: [beqz a2] to 0x3e6b4 ([li a0, 1; ret], no frame) when the length is 0;
   - 0x3e4a0..0x3e4c4: an 80-byte frame, s0..s8 saved at sp+0x48..sp+8;
   - 0x3e4c8..0x3e4f0: a0 = 0 (the position) and the loop constants a3 = 0xc0, a4 = -0x41, a5 = 0xe0, a6 = 0x80,
     a7 = 0x1b, t0 = 7, t1 = 0xf0, t2 = -0x110000, t3 = -0x100000, then [j 0x3e500];
   - 0x3e4f4: [addi t4, a0, 1]; 0x3e4f8: [mv a0, t4; bgeu t4, a2] to 0x3e6bc (a0 = 1, the epilogue at 0x3e6c0);
   - 0x3e500 (the loop head): with 16 bytes left (0x3e51c), the 16 bytes are read and masked with the word at
     0x134d8 (0x8080808080808080); all ASCII: position + 16 (0x3e4f8); else the first byte decides (ASCII:
     0x3e4f4, else the multi-byte checks at 0x3e5ec); with fewer left (0x3e50c), the byte at the position is read
     and decides the same way;
   - 0x3e5ec / 0x3e614 / 0x3e664: the two-, three- and four-byte sequences, each checking that its bytes lie inside
     the payload before it reads them, then position + 2/3/4 (0x3e4f8) or a0 = 0 (0x3e6ac, then 0x3e6c0);
   - 0x3e6c0: s0..s8 restored, the frame released, [ret].
   The statement says only that it returns 0 or 1, so the proof follows every path without tracking which. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg RunDraw PM_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import LiaTier0U StoreFast.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* A hypothesis hidden from lia (a disjunction the loop does not need). *)
Definition boxed (P : Prop) : Prop := P.
Ltac box1 H := lazymatch type of H with ?P => change P with (boxed P) in H end.

Section CANSEC1. Context {rc : runConstT}.

Section P.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (pl : list Z) (lo : Z).
  Notation n := (zlength pl).
  Notation SP := (bv_unsigned sp).
  Hypothesis BA : bytes_at psegs m D (map (Z_to_bv 8) pl).
  Hypothesis DLO : 0 < D.
  Hypothesis DHI : D + n <= ATOP.
  Hypothesis NLT : n < 2^26.
  Hypothesis LO : lo <= SP - 80.
  Hypothesis DSEP : D + n <= lo \/ SP <= D.

  Notation W := [(SP - 80, SP)].
  Notation bs := (map (Z_to_bv 8) pl).
  Notation VPOST := (vutf8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo).

  (* The frame: 8 unused bytes, then s8..s0 of the caller. *)
  Definition FRAME (m1 : word -> option byte) : Prop := exists junk8,
    rw_cells psegs m1 (SP + -80) [CB 8 junk8; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].
  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at psegs m1 D bs /\ FRAME m1 /\ stk psegs m1 lo (SP + -80)
    /\ munch W m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1.

  (* Each payload byte can be read. *)
  Lemma payload_rdx : forall m1 k, bytes_at psegs m1 D bs -> 0 <= k < n ->
    exists b : byte, ov_read_bytes psegs m1 (wa (D + k)) 1 = Some [b].
  Proof.
    intros m1 k B Hk. unfold zlength in Hk.
    pose proof (bytes_at_read psegs m1 D bs k 1 B ltac:(lia) ltac:(rewrite length_map; lia)) as R.
    destruct (skipn (Z.to_nat k) bs) as [|b r] eqn:E.
    { exfalso. assert (L : length (skipn (Z.to_nat k) bs) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn, length_map in L. lia. }
    exists b. exact R.
  Qed.

  (* A state of the loop: the frame built, the loop constants in a1..a7 and t0..t3, s9..s11 the caller's. *)
  Notation GST pc mm x0 x1 xa0 x2 x3 x4 x5 x6 x7 x8 y4 y5 y6 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -80)) gp tp (Z_to_bv 64 7) (Z_to_bv 64 240) (Z_to_bv 64 (-1114112)) x0 x1 xa0
             (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 192) (Z_to_bv 64 (-65)) (Z_to_bv 64 224) (Z_to_bv 64 128) (Z_to_bv 64 27)
             x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 (Z_to_bv 64 (-1048576)) y4 y5 y6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* The epilogue at 0x3e6c0, with a0 = 0 or 1. *)
  Lemma vu_epi : forall m1 v (y5 y6 y7 x0 x1 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 y28 y29 y30 y31 : word),
    INV m1 -> (v = 0 \/ v = 1) ->
    evt psegs VPOST
      (MS (mkR ra (Z_to_bv 64 (SP + -80)) gp tp y5 y6 y7 x0 x1 (Z_to_bv 64 v) ya1 ya2 ya3 ya4 ya5 ya6 ya7
               x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x3e6c0) fc None m1 (seg_rom psegs)).
  Proof.
    intros m1 v y5 y6 y7 x0 x1 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 y28 y29 y30 y31 (BA1 & [junk8 FR] & ST & MU & WM & MI) HV.
    box1 DSEP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ST as (LO0 & _ & _).
    do 11 zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vutf8_post.
    do 15 eexists. exists m1. split; [unfold mkR; reflexivity|].
    split; [destruct HV as [-> | ->]; [left|right]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  (* 0x3e6ac: a0 = 0, then the epilogue. *)
  Lemma vu_false : forall m1 (y5 y6 y7 x0 x1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 y28 y29 y30 y31 : word),
    INV m1 ->
    evt psegs VPOST
      (MS (mkR ra (Z_to_bv 64 (SP + -80)) gp tp y5 y6 y7 x0 x1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
               x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x3e6ac) fc None m1 (seg_rom psegs)).
  Proof.
    intros m1 y5 y6 y7 x0 x1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 y28 y29 y30 y31 INV1.
    zstep. zstep. apply vu_epi; [exact INV1| left; reflexivity].
  Qed.

  Ltac pc_is p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => let v := eval vm_compute in q in constr_eq v p end.
  (* A branch on a bound (the condition turned into Z). *)
  Ltac br K := if_cases K; try (zify_cond K; rewrite ?unsigned_lit in K by lia).
  (* The states a path ends in: the loop's next position (0x3e4f8, or 0x3e4f4 one past), a0 = 0 (0x3e6ac), the
     epilogue (0x3e6c0, or 0x3e6bc with a0 = 1), the two-, three- and four-byte checks (S1, S3, S4). *)
  Ltac fin NEXT S1 S3 S4 INV1 :=
    first [ pc_is 0x3e4f8; apply NEXT; lia
          | pc_is 0x3e4f4; zstep; apply NEXT; lia
          | pc_is 0x3e6ac; apply vu_false; exact INV1
          | pc_is 0x3e6c0; apply vu_epi; [exact INV1| first [left; reflexivity| right; reflexivity]]
          | pc_is 0x3e6bc; zstep; apply vu_epi; [exact INV1| right; reflexivity]
          | pc_is 0x3e5ec; eapply S1; word_eq_tac
          | pc_is 0x3e614; eapply S3; word_eq_tac
          | pc_is 0x3e664; eapply S4; word_eq_tac ].

  (* The loop head at 0x3e500, a0 = the position, by fuel. *)
  Lemma vu_loop : forall fuel pos m1 (x0 x1 x2 x3 x4 x5 x6 x7 x8 u4 u5 u6 : word),
    Z.of_nat fuel > n - pos -> 0 <= pos < n -> INV m1 ->
    evt psegs VPOST (GST 0x3e500 m1 x0 x1 (Z_to_bv 64 pos) x2 x3 x4 x5 x6 x7 x8 u4 u5 u6).
  Proof.
    induction fuel as [|fuel IH]; intros pos m1 x0 x1 x2 x3 x4 x5 x6 x7 x8 u4 u5 u6 FU PR INV1; [lia|].
    box1 DSEP.
    pose proof INV1 as (BA1 & FR & ST & MU & WM & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ST as (LO0 & _ & _).
    pose proof (@ATOP_hi rc) as AH.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    (* 0x3e4f8: a0 = t4 = the next position q; q = n ends with 1, else the loop goes on at q. *)
    assert (NEXT : forall q (y0 y1 ya0 y2 y3 y4 y5 y6 y7 y8 z5 z6 : word), pos < q <= n ->
              evt psegs VPOST (GST 0x3e4f8 m1 y0 y1 ya0 y2 y3 y4 y5 y6 y7 y8 (Z_to_bv 64 q) z5 z6)).
    { intros q y0 y1 ya0 y2 y3 y4 y5 y6 y7 y8 z5 z6 Hq.
      zstep. zstep. br Kq.
      all: first [ pc_is 0x3e6bc; zstep; apply vu_epi; [exact INV1| right; reflexivity]
                 | pc_is 0x3e500; apply IH; [lia| lia| exact INV1] ]. }
    (* 0x3e664: a four-byte sequence at the position (t5 = its address). *)
    assert (SLOW4 : forall (y0 y1 y2 y3 y4 y5 y6 y7 y8 z4 w5 z6 : word), w5 = Z_to_bv 64 (D + pos) ->
              evt psegs VPOST (GST 0x3e664 m1 y0 y1 (Z_to_bv 64 pos) y2 y3 y4 y5 y6 y7 y8 z4 w5 z6)).
    { intros y0 y1 y2 y3 y4 y5 y6 y7 y8 z4 w5 z6 ->.
      zstep. zstep. if_cases K1; try fin NEXT NEXT NEXT NEXT INV1.     (* andi t4, t6, 0xf8; bne t4, t1 *)
      zstep. zstep. br K2; try fin NEXT NEXT NEXT NEXT INV1.           (* addi t4, a0, 4; bltu a2, t4 *)
      destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1].
      destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2].
      destruct (payload_rdx m1 (pos + 3) BA1 ltac:(lia)) as [c3 R3].
      zstep. zstep. zstep. if_cases K3; try fin NEXT NEXT NEXT NEXT INV1. (* lbu a0, 1(t5); andi s0; bne s0, a6 *)
      zstep. zstep. if_cases K4; try fin NEXT NEXT NEXT NEXT INV1.     (* lb s0, 2(t5); blt a4, s0 *)
      zstep. zstep. if_cases K5; try fin NEXT NEXT NEXT NEXT INV1.     (* lb t5, 3(t5); blt a4, t5 *)
      do 6 zstep. zstep. if_cases K6; fin NEXT NEXT NEXT NEXT INV1. }  (* the code point; bgeu a0, t3 *)
    (* 0x3e614: a three-byte sequence (else the four-byte check). *)
    assert (SLOW3 : forall (y0 y1 y2 y3 y4 y5 y6 y7 y8 z4 w5 z6 : word), w5 = Z_to_bv 64 (D + pos) ->
              evt psegs VPOST (GST 0x3e614 m1 y0 y1 (Z_to_bv 64 pos) y2 y3 y4 y5 y6 y7 y8 z4 w5 z6)).
    { intros y0 y1 y2 y3 y4 y5 y6 y7 y8 z4 w5 z6 ->.
      zstep. zstep. if_cases K1; try fin NEXT NEXT NEXT SLOW4 INV1.    (* andi t4, t6, 0xf0; bne t4, a5 *)
      zstep. zstep. br K2; try fin NEXT NEXT NEXT SLOW4 INV1.          (* addi t4, a0, 3; bltu a2, t4 *)
      destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1].
      destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2].
      zstep. zstep. zstep. if_cases K3; try fin NEXT NEXT NEXT SLOW4 INV1. (* lbu a0, 1(t5); andi s0; bne s0, a6 *)
      zstep. zstep. if_cases K4; try fin NEXT NEXT NEXT SLOW4 INV1.    (* lb t5, 2(t5); blt a4, t5 *)
      do 6 zstep. zstep. if_cases K5; try fin NEXT NEXT NEXT SLOW4 INV1. (* the code point; beqz t5 *)
      zstep. if_cases K6; try fin NEXT NEXT NEXT SLOW4 INV1.           (* bltu t5, a7 *)
      zstep. zstep. if_cases K7; try fin NEXT NEXT NEXT SLOW4 INV1.    (* srli a0, a0, 13; bgeu a0, t0 *)
      zstep. fin NEXT NEXT NEXT SLOW4 INV1. }                          (* j 0x3e6ac *)
    (* 0x3e5ec: a byte above 0x7f at the position: a two-byte sequence (else the three-byte check). *)
    assert (SLOW1 : forall (y0 y1 y2 y3 y4 y5 y6 y7 y8 z4 w5 z6 : word), w5 = Z_to_bv 64 (D + pos) ->
              evt psegs VPOST (GST 0x3e5ec m1 y0 y1 (Z_to_bv 64 pos) y2 y3 y4 y5 y6 y7 y8 z4 w5 z6)).
    { intros y0 y1 y2 y3 y4 y5 y6 y7 y8 z4 w5 z6 ->.
      zstep. zstep. if_cases K1; try fin NEXT NEXT SLOW3 SLOW4 INV1.   (* andi t4, t6, 0xe0; bne t4, a3 *)
      zstep. zstep. br K2; try fin NEXT NEXT SLOW3 SLOW4 INV1.         (* addi t4, a0, 2; bltu a2, t4 *)
      zstep. zstep. zstep. if_cases K3; try fin NEXT NEXT SLOW3 SLOW4 INV1. (* andi t6, 0x1e; li a0, 0; beqz t6 *)
      destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1].
      zstep. zstep. if_cases K4; try fin NEXT NEXT SLOW3 SLOW4 INV1.   (* lb t5, 1(t5); bge a4, t5 *)
      zstep. fin NEXT NEXT SLOW3 SLOW4 INV1. }                         (* j 0x3e6c0 *)
    (* 0x3e500: t4 = position + 16, t5 = the position's address; 16 bytes left or not. *)
    zstep. zstep. zstep. br K16.
    all: first [ pc_is 0x3e51c
               | pc_is 0x3e50c;
                 destruct (payload_rdx m1 pos BA1 ltac:(lia)) as [c0 R0];
                 zstep; zstep; zstep; if_cases Ka; try fin NEXT SLOW1 SLOW3 SLOW4 INV1; (* lbu t6; slli t4, t6, 56; bgez t4 *)
                 zstep; fin NEXT SLOW1 SLOW3 SLOW4 INV1 ].                               (* j 0x3e5ec *)
    (* 0x3e51c: the 16 bytes at the position. *)
    destruct (payload_rdx m1 (pos + 0) BA1 ltac:(lia)) as [c0 R0]. destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1].
    destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2]. destruct (payload_rdx m1 (pos + 3) BA1 ltac:(lia)) as [c3 R3].
    do 4 zstep. clear R0 R1 R2 R3.
    destruct (payload_rdx m1 (pos + 4) BA1 ltac:(lia)) as [c4 R4]. destruct (payload_rdx m1 (pos + 5) BA1 ltac:(lia)) as [c5 R5].
    destruct (payload_rdx m1 (pos + 6) BA1 ltac:(lia)) as [c6 R6]. destruct (payload_rdx m1 (pos + 7) BA1 ltac:(lia)) as [c7 R7].
    do 4 zstep. clear R4 R5 R6 R7.
    do 5 zstep.
    destruct (payload_rdx m1 (pos + 8) BA1 ltac:(lia)) as [c8 R8]. destruct (payload_rdx m1 (pos + 9) BA1 ltac:(lia)) as [c9 R9].
    destruct (payload_rdx m1 (pos + 10) BA1 ltac:(lia)) as [c10 R10]. destruct (payload_rdx m1 (pos + 11) BA1 ltac:(lia)) as [c11 R11].
    do 4 zstep. clear R8 R9 R10 R11.
    do 9 zstep.
    destruct (payload_rdx m1 (pos + 12) BA1 ltac:(lia)) as [c12 R12]. destruct (payload_rdx m1 (pos + 13) BA1 ltac:(lia)) as [c13 R13].
    destruct (payload_rdx m1 (pos + 14) BA1 ltac:(lia)) as [c14 R14]. destruct (payload_rdx m1 (pos + 15) BA1 ltac:(lia)) as [c15 R15].
    do 5 zstep. clear R12 R13 R14 R15.
    do 17 zstep.                                                       (* the two words, the mask at 0x134d8 *)
    zstep. if_cases Km; try fin NEXT SLOW1 SLOW3 SLOW4 INV1.           (* beqz s0: all 16 ASCII *)
    zstep. zstep. zstep. if_cases Ka; fin NEXT SLOW1 SLOW3 SLOW4 INV1. (* the first byte: andi t6, 0xff; slli; bgez *)
  Qed.

  (* From the entry: a length of 0 returns 1 at once; else the frame, the constants, and the loop from 0. *)
  Lemma vu_body : stk psegs m lo SP -> mem_inv psegs m ->
    evt psegs VPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 D) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PVUTF8) fc None m (seg_rom psegs)).
  Proof.
    intros ST MI. unfold PVUTF8.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ST as (LO0 & _ & _).
    pose proof (@ATOP_hi rc) as AH.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    assert (BL : D + Z.of_nat (length bs) <= lo \/ SP <= D) by (rewrite length_map; unfold zlength in *; lia).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof BA as BA1.
    zstep. br K0.
    all: first [ pc_is 0x3e4a0
               | pc_is 0x3e6b4; zstep; zstep; apply evt_done; unfold vutf8_post;
                 do 15 eexists; exists m; split; [unfold mkR; reflexivity|];
                 split; [right; reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI| exact ST] ].
    carve_frame 80%nat ST.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV1 : INV mx)
        by (split; [exact BA1|]; split; [eexists; exact FR|]; split; [exact ST|]; split; [exact MU|]; split; [exact WM| exact MI])
    end.
    do 11 zstep.
    eapply (vu_loop (S (Z.to_nat n)) 0); [lia| lia| exact INV1].
  Qed.
End P.

Theorem vutf8_proof : vutf8_stmt.
Proof.
  unfold vutf8_stmt, VUTF8_STACK. intros until lo. intros BA PLB D0 DHI NLT ST LO DSEP MI -> ->.
  eapply vu_body; eassumption.
Qed.
End CANSEC1.
