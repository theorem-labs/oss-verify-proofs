(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41D.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  (* [comment removed for export] *)
  Lemma x41_end : forall mm c b pad p st lm
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINV mm -> BD4 mm c b pad p st lm ->
    evt psegs POST (ST 0x23eb0 mm x1 x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                       x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm c b pad p st lm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI BD.
    kx_autoLx [0x23454] 40%nat [KZRange SPV 4096 (2^47)] [(SPV - 256, 40)].
    all: clear KXBR.
    all: eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm);
         [exact EI | first [left; reflexivity | right; split; reflexivity]].
  Qed.

  (* [comment removed for export] *)
  Lemma x41_t4 : forall (k : nat) mb mm j c sh (c0 b0 p0 st0 lm0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    munch WD4 mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    BD4 mm c0 b0 pad p0 st0 lm0 ->
    c <= Z.of_nat k -> 1 <= c -> 0 <= j -> j + c <= dcap -> 52 <= sh <= 63 ->
    (forall mm' (y5 y6 y7 y11 y12 y13 y15 y17 y21 y28 y29 y30 y31 b' : word),
        munch WD4 mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) ->
        BD4 mm' c0 b' pad p0 st0 lm0 ->
        evt psegs POST (ST 0x23eb0 mm' x1 y5 y6 y7 x8 x9 x10 y11 y12 y13 x14 y15 x16 y17 (Z_to_bv 64 (DT + 4)) x19 x20 y21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x23e6c mm x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 sh) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 c) x14 x15 x16 x17 (Z_to_bv 64 (DT + 4)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j c sh c0 b0 p0 st0 lm0 pad x1 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      MU WM MI OUT DTB BD HK HC HJ HJC HSH K; [exfalso; lia|].
    kx_autoLx [0x23e6c; 0x23eb0] 40%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange c 1 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange SPV 4096 (2^47); KZWr DST dcap; KZWr (SPV - 256) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 256) 40; KZDisj (SPV - 256) 40 DT 16388]
      [(DT, 16388); (SPV - 256, 40)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147052) _ _ _ _) =>
             replace (DST + j + 1) with (DST + (j + 1)) by lia;
             eapply (IH mb _ (j + 1) (c + -1) sh); try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147120) _ _ _ _) => eapply K; eassumption
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_p4 : forall mb mm j dl tl rsv (c0 b0 p0 st0 lm0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    munch WD4 mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    BD4 mm c0 b0 pad p0 st0 lm0 ->
    0 <= j < dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' (y5 y6 y7 y11 y12 y13 y15 y17 y21 y28 y29 y30 y31 b' : word),
        munch WD4 mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) ->
        BD4 mm' c0 b' pad p0 st0 lm0 ->
        evt psegs POST (ST 0x23eb0 mm' x1 y5 y6 y7 x8 x9 x10 y11 y12 y13 x14 y15 x16 y17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) y21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x23e60 mm x1 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + j)) x13 x14 x15 x16 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j dl tl rsv c0 b0 p0 st0 lm0 pad x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      MU WM MI OUT DTB BD HJ HDL HTL HRSV K.
    kx_autoLx [0x23e6c] 10%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535] [].
    subst dl; rewrite (neg_dl_sh tl rsv HTL).
    replace (-1 * j + dcap) with (dcap - j) by lia.
    eapply (x41_t4 (Z.to_nat (dcap - j)) mb mm j (dcap - j) (64 - tl)); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Notation SINV := RZ_huf_dx41.SINV.
  Ltac x41_l4_run ROOM OFF :=
    lazymatch goal with
    | SB : bytes_at psegs _ ?S ?bs, SL : zlen ?bs = ?len, BD : rw_cells psegs _ _ [_; _; _; C8 (Z_to_bv 64 (?S + ?off)); _; _]
      |- evt _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 (64 - ?tl)) _ _ _ _ _ _ (Z_to_bv 64 (DST + ?j)) (Z_to_bv 64 ?bc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        kx_autoLx [0x23bb8; 0x23e60; 0x23eb0] 160%nat
          [ROOM; KZRange (len - off) 8 (2^32); OFF; KZRange bc 0 64;
           KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
           KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange SPV 4096 (2^47);
           KZWr DST dcap; KZWr (SPV - 256) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap S len; KZDisj DST dcap (SPV - 416) 160;
           KZDisj DST dcap (SPV - 256) 40; KZDisj (SPV - 256) 40 DT 16388; KZDisj (SPV - 256) 40 S len; KZDisj (SPV - 256) 40 (SPV - 416) 160]
          [(DT, 16388); (S, len); (SPV - 416, 160); (SPV - 256, 40)]
    end.

  Lemma x41_l4 : forall (k : nat) mb mm j off S len bs dl tl rsv bc (c0 b0 : word) pad
      (x1 x6 x7 x8 x9 x10 x11 x14 x15 x16 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD4 mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 (Z_to_bv 64 (DST + dcap)) w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    BD4 mm c0 b0 pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) ->
    dcap - j <= Z.of_nat k -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' (y5 y6 y7 y11 y12 y13 y15 y17 y21 y28 y29 y30 y31 c' b' p' : word),
        munch WD4 mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) ->
        BD4 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt psegs POST (ST 0x23eb0 mm' x1 y5 y6 y7 x8 x9 x10 y11 y12 y13 x14 y15 x16 y17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) y21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x23bb8 mm x1 (Z_to_bv 64 (64 - tl)) x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 bc) x14 x15 x16 (Z_to_bv 64 64) (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap - 3)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mb mm j off S len bs dl tl rsv bc c0 b0 pad x1 x6 x7 x8 x9 x10 x11 x14 x15 x16 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
        w0 w1 w2 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK HK HJ HDL HTL HRSV HS HB K.
    all: destruct HS as [-> | (O1 & O2 & B1)].
    all: try (destruct (Z_lt_le_dec (dcap - j) 4) as [RM|RM]);
         try (destruct (Z_lt_le_dec off 8) as [O8|O8]).
    all: try solve [exfalso; lia].
    all: lazymatch goal with
         | RM : 4 <= _ - _, O8 : 8 <= _ |- _ => x41_l4_run (KZRange (dcap - j) 4 (2^32)) (KZRange off 8 (2^32))
         | RM : 4 <= _ - _, O8 : _ < 8 |- _ => x41_l4_run (KZRange (dcap - j) 4 (2^32)) (KZRange off 1 7)
         | RM : _ - _ < 4, O8 : 8 <= _ |- _ => x41_l4_run (KZRange (dcap - j) 0 3) (KZRange off 8 (2^32))
         | RM : _ - _ < 4, O8 : _ < 8 |- _ => x41_l4_run (KZRange (dcap - j) 0 3) (KZRange off 1 7)
         | _ => kx_autoLx [0x23bb8; 0x23e60; 0x23eb0] 20%nat
                  [KZRange S 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
                  [(SPV - 416, 160); (SPV - 256, 40)]
         end.
    all: kx_ev_ranges; kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: try replace (DST + j + 4) with (DST + (j + 4)) by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147040) _ _ _ _) =>
             eapply (x41_p4 mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147120) _ _ _ _) => eapply K; eassumption
         | BD : rw_cells _ _ _ [_; _; _; C8 (Z_to_bv 64 ?X); _; _] |- evt _ _ (MS _ _ (Z_to_bv 64 146360) _ _ _ _) =>
             replace X with (S + (X - S)) in BD by lia;
             eapply (IH mb); try eassumption; try lia; try solve [unfold RZ_huf_dx41.SINV; lia];
             try solve [exact (bv_unsigned_in_range 64 _)]; try (intros; eapply K; eassumption)
         end.
  Qed.

End DX41D.
