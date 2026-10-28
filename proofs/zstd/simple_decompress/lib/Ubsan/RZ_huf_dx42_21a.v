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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2 RZ_huf_dx42_20.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf411_kit_rs huf42_2_ftkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_21A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis TL11 : tl = 11.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation DSX pc mm x1 x7 pe x9 x10 x11 x12 x14 x16 x17 x18 x19 x20 x21 x22 x23 j x25 x26 x27 x29 x31 :=
    (ST pc mm x1 (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 (DST + pe)) x9 x10 x11 x12 (Z_to_bv 64 (-1 * DT + -5)) x14
        (Z_to_bv 64 9) x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (DST + j)) x25 x26 x27 (Z_to_bv 64 64) x29 (Z_to_bv 64 (DT + 4)) x31).

  Notation x42_tblf := (RZ_huf_dx42_20.x42_tblf DT dtb tl X2OK TL11).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] | solve [ft_al] ].

  (* [comment removed for export] *)
  Lemma x42_la5 : forall mb mm j pe
      (x1 x7 x9 x10 x11 x12 x14 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x29 x31 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    0 <= j <= pe -> pe <= dcap ->
    (forall mm' j' (y1 y7 y17 y18 y19 y21 y22 y23 y25 y26 y27 : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        j <= j' <= pe ->
        evt usegs POST (DSX 0x22028 mm' y1 y7 pe x9 x10 x11 x12 x14 x16 y17 y18 y19 x20 y21 y22 y23 j' y25 y26 y27 x29 x31)) ->
    evt usegs POST (DSX 0x21ff8 mm x1 x7 pe x9 x10 x11 x12 x14 x16 x17 x18 x19 x20 x21 x22 x23 j x25 x26 x27 x29 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe x1 x7 x9 x10 x11 x12 x14 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x29 x31 MU WM MI OUT DTB HJ HPE K.
    destruct (Z_lt_le_dec j pe) as [ROOM|FULL]; cycle 1.
    - kx_autoLx [0x22028; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190] 10%nat
        [KZRange (j - pe) 0 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)).
      all: ft_ck.
      all: eapply K; try eassumption; lia.
    - kx_autoLx [0x22028; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190] 30%nat
        [KZRange (dcap - j) 1 (2^32); KZRange (pe - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
         KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZAlign DT 4; KZWr DST dcap; KZDisj DST dcap DT 16388]
        [(DT, 16388)].
      all: ft_ck.
      all: kx_mem.
      all: ft_k24 DST K.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_t5 : forall (k : nat) mb mm j pe
      (x1 x7 x9 x10 x11 x12 x14 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x29 x31 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    pe - j <= Z.of_nat k -> 0 <= j -> j + 2 <= pe -> pe <= dcap ->
    (forall mm' j' (y1 y7 y17 y18 y19 y21 y22 y23 y25 y26 y27 : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        j <= j' <= pe ->
        evt usegs POST (DSX 0x22028 mm' y1 y7 pe x9 x10 x11 x12 x14 x16 y17 y18 y19 x20 y21 y22 y23 j' y25 y26 y27 x29 x31)) ->
    evt usegs POST (DSX 0x21fb0 mm x1 x7 pe x9 x10 x11 x12 x14 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (DST + pe - 2)) j x25 x26 x27 x29 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe x1 x7 x9 x10 x11 x12 x14 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x29 x31
      MU WM MI OUT DTB HK HJ0 HJ HPE K; [exfalso; lia|].
    assert (TBL : tbl_in usegs mm DT 8196 4 7 1 2) by (apply x42_tblf; exact DTB).
    kx_autoLx [0x21fb0; 0x21ff8; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190] 40%nat
      [KZRange (dcap - j) 2 (2^32); KZRange (pe - j) 2 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZAlign DT 4; KZWr DST dcap; KZDisj DST dcap DT 16388; KZTbl DT 8196 4 7 1 2]
      [(DT, 16388)].
    all: ft_ck.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: try replace (DST + pe + -2) with (DST + pe - 2) by lia.
    all: ft_r24 DST.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?J)) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x21fb0) _ _ ?m2 _) =>
             eapply (IH mb m2 J pe); try eassumption; try lia; intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?J)) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x21ff8) _ _ ?m2 _) =>
             eapply (x42_la5 mb m2 J pe); try eassumption; try lia; intros; eapply K; try eassumption; lia
         end.
  Qed.

End DX42_21A.
