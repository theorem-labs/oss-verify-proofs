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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2 RZ_huf_dx42_20.
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
  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Notation x42_tblf := (RZ_huf_dx42_20.x42_tblf DT dtb tl X2OK TL11).

  (* [comment removed for export] *)
  Lemma x42_la5 : forall mb mm j pe
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    0 <= j <= pe -> pe <= dcap ->
    (forall mm' (y11 y18 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x1f4fc mm' x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4)) y11 x12 x13 x14 x15 x16 x17 y18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (DST + pe)))) ->
    evt psegs POST (ST 0x1f4dc mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 MU WM MI OUT DTB HJ HPE K.
    destruct (Z_lt_le_dec j pe) as [ROOM|FULL]; cycle 1.
    - kx_autoLx [0x1f4fc] 10%nat [KZRange (j - pe) 0 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)).
      all: eapply K; eassumption.
    - kx_autoLx [0x1f4fc] 30%nat
        [KZRange (dcap - j) 1 (2^32); KZRange (pe - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
         KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZWr DST dcap; KZDisj DST dcap DT 16388]
        [(DT, 16388)].
      all: kx_mem.
      all: eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_t5 : forall (k : nat) mb mm j pe
      (x1 x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    pe - j <= Z.of_nat k -> 0 <= j -> j + 2 <= pe -> pe <= dcap ->
    (forall mm' (y9 y11 y12 y18 y19 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x1f4fc mm' x1 x5 x6 x7 x8 y9 (Z_to_bv 64 (DT + 4)) y11 y12 (Z_to_bv 64 (DST + pe - 2)) x14 x15 x16 x17 y18 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (DST + pe)))) ->
    evt psegs POST (ST 0x1f4a8 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4)) x11 x12 (Z_to_bv 64 (DST + pe - 2)) x14 x15 x16 x17 (Z_to_bv 64 (DST + j)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe x1 x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 MU WM MI OUT DTB HK HJ0 HJ HPE K; [exfalso; lia|].
    assert (TBL : tbl_in psegs mm DT 8196 4 7 1 2) by (apply x42_tblf; exact DTB).
    kx_autoLx [0x1f4a8; 0x1f4dc] 40%nat
      [KZRange (dcap - j) 2 (2^32); KZRange (pe - j) 2 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZWr DST dcap; KZDisj DST dcap DT 16388; KZTbl DT 8196 4 7 1 2]
      [(DT, 16388)].
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 128168) _ _ ?m2 _) =>
             eapply (IH mb m2 J pe); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 128220) _ _ ?m2 _) =>
             eapply (x42_la5 mb m2 J pe); try eassumption; try lia; intros mm'; intros; eapply (K mm'); eassumption
         end.
  Qed.

End DX42_21A.
