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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_1A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).

  (* [comment removed for export] *)
  Lemma x42_la1 : forall mb mm j pe dl
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv ->
    (forall mm' D7 (y1 y11 y13 y16 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 -> D7 = dl ->
        evt psegs POST (ST 0x208d0 mm' y1 x5 x6 x7 (Z_to_bv 64 (DST + j)) x9 x10 y11 x12 y13 x14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + pe)) x20 (Z_to_bv 64 dl) x22 (Z_to_bv 64 D7) x24 x25 x26 w13 x28 x29 w12 x31)) ->
    evt psegs POST (ST 0x20888 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + j)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + pe)) x20 (Z_to_bv 64 dl) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe dl x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA HJ HPE HDL K.
    destruct (Z_lt_le_dec j pe) as [ROOM|FULL]; cycle 1.
    - kx_autoLx [0x208d0] 10%nat [KZRange (j - pe) 0 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange DST 4096 (2^47);
                                  KZRange SPV 4096 (2^47)] [(SPV - 416, 160)].
      all: eapply K; try eassumption; first [reflexivity | lia].
    - subst dl.
      assert (TLC : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
      repeat (destruct TLC as [TLC|TLC]); rewrite TLC in *;
        kx_autoLx [0x208d0] 60%nat
          [KZRange (dcap - j) 1 (2^32); KZRange (pe - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
           KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange rsv 0 255; KZRange SPV 4096 (2^47); KZWr DST dcap; KZDisj DST dcap DT 16388;
           KZDisj DST dcap (SPV - 416) 160]
          [(DT, 16388); (SPV - 416, 160)].
      all: kx_mem.
      all: eapply K; try eassumption; first [reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_t1 : forall (k : nat) mb mm j pe dl sh
      (x1 x5 x7 x9 x10 x11 x12 x13 x14 x15 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    pe - j <= Z.of_nat k -> 0 <= j -> j + 2 <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    (forall mm' D7 (y1 y8 y10 y11 y13 y16 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 -> D7 = dl ->
        evt psegs POST (ST 0x208d0 mm' y1 x5 (Z_to_bv 64 sh) x7 y8 x9 y10 y11 x12 y13 x14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + pe)) x20 (Z_to_bv 64 dl) x22 (Z_to_bv 64 D7) x24 x25 x26 w13 x28 x29 w12 x31)) ->
    evt psegs POST (ST 0x20850 mm x1 x5 (Z_to_bv 64 sh) x7 (Z_to_bv 64 (DST + j)) x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (DST + pe - 2)) x17 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + pe)) x20 (Z_to_bv 64 dl) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe dl sh x1 x5 x7 x9 x10 x11 x12 x13 x14 x15 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA HK HJ0 HJ HPE HDL HSH K; [exfalso; lia|].
    assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    kx_autoLx [0x20850; 0x20888] 40%nat
      [KZRange (dcap - j) 2 (2^32); KZRange (pe - j) 2 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange sh 52 63; KZWr DST dcap; KZDisj DST dcap DT 16388; KZTblLog DT sh 4 7 1 2]
      [(DT, 16388)].
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 133200) _ _ ?m2 _) =>
             eapply (IH mb m2 J pe dl sh); try eassumption; try lia; intros; eapply K; try eassumption; first [reflexivity | lia]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 133256) _ _ ?m2 _) =>
             eapply (x42_la1 mb m2 J pe dl); try eassumption; try lia; intros mm' D7; intros; eapply (K mm' D7); try eassumption; first [reflexivity | lia]
         end.
  Qed.

End DX42_1A.
