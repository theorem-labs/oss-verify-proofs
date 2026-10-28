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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_2a RZ_huf_dx42_2b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf41_kit_reload huf42_2_t2kit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_2C.
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
  Notation x42_la2 := (RZ_huf_dx42_2a.x42_la2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_t2 := (RZ_huf_dx42_2a.x42_t2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_w2 := (RZ_huf_dx42_2b.x42_w2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).

  (* [comment removed for export] *)
  Lemma x42_c2 : forall mb mm j e pe S len bs dl bc A0 (c0 : word) pad
      (x1 x5 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
    munch WD2 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 A0) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    0 <= j -> j + 2 <= e -> e <= dcap -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 ->
    (bc <= 64 -> exists off, A0 = S + off /\ SINV off len bc) ->
    K2 mb e pe dl S pad x5 x7 x18 x20 x21 x26 x28 x29 x30 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ->
    evt usegs POST (ST 0x27b38 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 (Z_to_bv 64 (DST + e)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) x20 x21 x22 x23 x24 (Z_to_bv 64 dl) x26 (Z_to_bv 64 (DST + j)) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe S len bs dl bc A0 c0 pad x1 x5 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJT DJK SPA HJ HRM HE HPE HDL HB HP K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct (HP B64) as (off & -> & HO)|].
    - kx_autoLx [0x27b60; 0x2965c] 40%nat
        [KZRange bc 0 64; KZRange (e - j) 2 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
         KZRange dl 0 65292; KZRange SPV 4096 (2^47)] [(SPV - 912, 136); (SPV - 696, 40)].
      all: t2side.
      all: t2ck.
      all: subst dl; rewrite ?(neg_dl_sh tl rsv TL).
      all: try replace (DST + e + -2) with (DST + e - 2) by lia.
      all: eapply (x42_w2 (Z.to_nat dcap) mb mm j e pe off S len bs (tl + 256 * rsv) (64 - tl) bc); try eassumption; try lia.
    - kx_autoLx [0x27ce4; 0x27d48; 0x2965c] 40%nat
        [KZRange bc 65 (2^31 - 1); KZRange (e - j) 2 (2^32); KZRange (dcap - j) 2 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32);
         KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65292; KZRange SPV 4096 (2^47);
         KZWr (SPV - 696) 40; KZDisj DST dcap (SPV - 696) 40; KZDisj (SPV - 696) 40 DT 16388; KZDisj (SPV - 696) 40 S len]
        [(SPV - 912, 136); (SPV - 696, 40)].
      all: t2side.
      all: t2ck.
      all: kx_ev_ranges; kx_mem.
      all: subst dl; rewrite ?(neg_dl_sh tl rsv TL).
      all: try replace (DST + e + -2) with (DST + e - 2) by lia.
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x27ce4) _ _ ?m2 _) =>
               eapply (x42_t2 (Z.to_nat dcap) mb m2 j e pe (tl + 256 * rsv) (64 - tl) S pad); try eassumption; try lia
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x27d48) _ _ ?m2 _) =>
               eapply (x42_la2 mb m2 j e pe (tl + 256 * rsv) S pad); try eassumption; try lia
           end.
  Qed.

End DX42_2C.
