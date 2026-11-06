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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_2a RZ_huf_dx42_2b.
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
  Notation x42_la2 := (RZ_huf_dx42_2a.x42_la2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_t2 := (RZ_huf_dx42_2a.x42_t2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_w2 := (RZ_huf_dx42_2b.x42_w2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).

  (* [comment removed for export] *)
  Lemma x42_c2 : forall mb mm j pe S len bs dl bc A0
      (x1 x6 x7 x8 x9 x10 x11 x12 x13 x14 x17 x19 x21 x24 x25 x26 x27 x28 x29 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (S + 8)) w16 w17 w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    0 <= j <= pe -> j + 2 <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 ->
    (bc <= 64 -> exists off, A0 = S + off /\ SINV off len bc) ->
    (forall mm' D7 (y5 y6 y7 y8 y9 y11 y13 y16 y17 y22 y28 y29 y31 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (S + 8)) w16 w17 w18 w19 -> D7 = dl ->
        evt psegs POST (ST 0x20f5c mm' x1 y5 y6 y7 y8 y9 x10 y11 x12 y13 x14 w18 y16 y17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 S) x21 y22 (Z_to_bv 64 D7) x24 x25 x26 x27 y28 y29 w12 y31)) ->
    evt psegs POST (ST 0x20dcc mm x1 (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 A0) x17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 S) x21 (Z_to_bv 64 bc) (Z_to_bv 64 dl) x24 x25 x26 x27 x28 x29 w12 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe S len bs dl bc A0 x1 x6 x7 x8 x9 x10 x11 x12 x13 x14 x17 x19 x21 x24 x25 x26 x27 x28 x29 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS HJ HRM HPE HDL HB HP K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct (HP B64) as (off & -> & HO)|].
    all: lazymatch goal with
         | B64 : _ <= 64 |- _ =>
             kx_autoLx [0x20dec; 0x20eec; 0x20f24] 40%nat
               [KZRange (pe - j) 2 (2^32); KZRange bc 0 64; KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange dl 0 65535; KZRange SPV 4096 (2^47)] [(SPV - 416, 160)]
         | _ =>
             kx_autoLx [0x20dec; 0x20eec; 0x20f24] 40%nat
               [KZRange (pe - j) 2 (2^32); KZRange bc 65 (2^31 - 1); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange dl 0 65535; KZRange SPV 4096 (2^47)] [(SPV - 416, 160)]
         end.
    all: subst dl; rewrite ?(neg_dl_sh tl rsv TL).
    all: try replace (DST + pe + -2) with (DST + pe - 2) by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 134948) _ _ _ _) =>
             eapply (x42_la2 mb mm j pe (tl + 256 * rsv)); try eassumption; try lia; try reflexivity; intros mm' D7; intros; eapply (K mm' D7); try eassumption; first [reflexivity | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 134636) _ _ _ _) =>
             eapply (x42_w2 (Z.to_nat dcap) mb mm j pe off S len bs (tl + 256 * rsv) (64 - tl) bc); try eassumption; try lia;
             try reflexivity; intros mm' D7; intros; eapply (K mm' D7); try eassumption; first [reflexivity | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 134892) _ _ _ _) =>
             eapply (x42_t2 (Z.to_nat dcap) mb mm j pe (tl + 256 * rsv) (64 - tl)); try eassumption; try lia; try reflexivity;
             intros mm' D7; intros; eapply (K mm' D7); try eassumption; first [reflexivity | lia]
         end.
  Qed.

End DX42_2C.
