(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf42_2_t2kit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_2A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD2 := [(DST, DST + dcap); (SPV - 696, SPV - 656)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -912) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation BD2 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -696) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation K2 mb e pe dl S pad x5 x7 x18 x20 x21 x26 x28 x29 x30 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 :=
    (forall mm' (y1 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y24 y27 c' b' p' : word),
        munch WD2 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD2 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x27de4 mm' y1 x5 (Z_to_bv 64 (DT + 4)) x7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                          x18 (Z_to_bv 64 (2^61)) x20 x21 y22 y23 y24 (Z_to_bv 64 dl) x26 y27 x28 x29 x30 (Z_to_bv 64 (DST + pe)))).

  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).

  (* [comment removed for export] *)
  Lemma x42_la2 : forall mb mm j e pe dl S pad (c0 b0 p0 : word)
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
    munch WD2 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD2 mm c0 b0 pad p0 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    (DT + 16388 <= lo \/ SPV <= DT) ->
    0 <= j <= e -> e <= dcap -> pe <= dcap -> dl = tl + 256 * rsv ->
    K2 mb e pe dl S pad x5 x7 x18 x20 x21 x26 x28 x29 x30 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ->
    evt usegs POST (ST 0x27d48 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) x20 x21 x22 x23 x24 (Z_to_bv 64 dl) x26 (Z_to_bv 64 (DST + j)) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe dl S pad c0 b0 p0 x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 MU WM MI OUT DTB FA BD DJT HJ HE HPE HDL K.
    destruct (Z_lt_le_dec j e) as [ROOM|FULL]; cycle 1.
    - kx_autoLx [0x27de4] 10%nat [KZRange (j - e) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47);
                                 KZRange SPV 4096 (2^47)] [(SPV - 912, 136); (SPV - 696, 40)].
      all: eapply K; eassumption.
    - subst dl.
      assert (TLC : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
      repeat (destruct TLC as [TLC|TLC]); rewrite TLC in *;
        kx_autoLx [0x27de4; 0x2965c] 60%nat
          [KZRange (dcap - j) 1 (2^32); KZRange (e - j) 1 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32);
           KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange rsv 0 255; KZRange SPV 4096 (2^47);
           KZWr DST dcap; KZWr (SPV - 696) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 696) 40; KZDisj (SPV - 696) 40 DT 16388]
          [(DT, 16388); (SPV - 912, 136); (SPV - 696, 40)].
      all: t2ck.
      all: kx_mem.
      all: eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_t2 : forall (k : nat) mb mm j e pe dl sh S pad (c0 b0 p0 : word)
      (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
    munch WD2 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD2 mm c0 b0 pad p0 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    (DT + 16388 <= lo \/ SPV <= DT) ->
    e - j <= Z.of_nat k -> 0 <= j -> j + 2 <= e -> e <= dcap -> pe <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    K2 mb e pe dl S pad x5 x7 x18 x20 x21 x26 x28 x29 x30 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ->
    evt usegs POST (ST 0x27ce4 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 (Z_to_bv 64 (DST + e - 2)) (Z_to_bv 64 sh) x10 x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) x20 x21 (Z_to_bv 64 (-1 * DT + -5)) x23 x24 (Z_to_bv 64 dl) x26 (Z_to_bv 64 (DST + j)) x28 x29 x30
                      (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j e pe dl sh S pad c0 b0 p0 x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 MU WM MI OUT DTB FA BD DJT HK HJ0 HJ HE HPE HDL HSH K; [exfalso; lia|].
    assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    kx_autoLx [0x27ce4; 0x27d48; 0x2965c] 40%nat
      [KZRange (dcap - j) 2 (2^32); KZRange (e - j) 2 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32);
       KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZRange sh 52 63;
       KZWr DST dcap; KZWr (SPV - 696) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 696) 40; KZDisj (SPV - 696) 40 DT 16388;
       KZTblLog DT sh 4 7 1 2]
      [(DT, 16388); (SPV - 912, 136); (SPV - 696, 40)].
    all: t2ck.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?A0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27ce4) _ _ ?m2 _) =>
             eapply (IH mb m2 J e pe dl sh S pad); try eassumption; try lia
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27d48) _ _ ?m2 _) =>
             eapply (x42_la2 mb m2 J e pe dl S pad); try eassumption; try lia
         end.
  Qed.

End DX42_2A.
