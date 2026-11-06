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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_4a.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_4B.
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
  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).

  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).
  Notation x42_la4 := (RZ_huf_dx42_4a.x42_la4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_t4 := (RZ_huf_dx42_4a.x42_t4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).

  Ltac x42_w4_run ROOM ROOM2 OFF :=
    lazymatch goal with
    | SB : bytes_at psegs _ ?S ?bs, SL : zlen ?bs = ?len, BD : rw_cells psegs _ _ [_; _; _; C8 (Z_to_bv 64 (?S + ?off)); _; _]
      |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?j)) (Z_to_bv 64 ?bc) (Z_to_bv 64 ?sh) _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?pe)) _ _ _ _ _ _) _ _ _ _ _ _) =>
        kx_autoLx [0x21a9c; 0x21bac; 0x21bec] 120%nat
          [ROOM2; ROOM; KZRange (len - off) 8 (2^32); OFF; KZRange bc 0 64; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32);
           KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47);
           KZRange sh 52 63; KZRange SPV 4096 (2^47); KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap S len;
           KZDisj DST dcap (SPV - 416) 160; KZTblLog DT sh 4 7 1 2; KZWr (SPV - 256) 40; KZDisj DST dcap (SPV - 256) 40; KZDisj (SPV - 256) 40 DT 16388; KZDisj (SPV - 256) 40 (SPV - 416) 160; KZDisj (SPV - 256) 40 S len]
          [(DT, 16388); (S, len); (SPV - 416, 160); (SPV - 256, 40)]
    end.

  (* [comment removed for export] *)
  Lemma x42_w4 : forall (k : nat) mb mm j pe off S len bs dl sh bc (c0 b0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x16 x17 x19 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD4 mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 -> BD4 mm c0 b0 pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) ->
    pe - j <= Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' D7 (y5 y6 y7 y11 y12 y13 y15 y18 y28 y29 y30 y31 c' b' p' : word),
        munch WD4 mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 -> BD4 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> D7 = dl ->
        evt psegs POST (ST 0x21c34 mm' x1 y5 y6 y7 x8 x9 x10 y11 y12 y13 (Z_to_bv 64 sh) y15 x16 x17 y18 x19 x20 x21 x22 (Z_to_bv 64 D7) x24 (Z_to_bv 64 (DST + pe)) x26 x27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x21a9c mm x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (DST + pe - 2)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 bc) (Z_to_bv 64 sh) (Z_to_bv 64 64) x16 x17 (Z_to_bv 64 (DT + 4)) x19 x20 x21 x22 (Z_to_bv 64 dl) x24 (Z_to_bv 64 (DST + pe)) x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe off S len bs dl sh bc c0 b0 pad x1 x5 x6 x7 x8 x9 x10 x16 x17 x19 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA BD DJ3 SB SL S0 S1 SL32 DJS DJK HK HJ HPE HDL HSH HS HB K.
    all: assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    all: destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]; destruct (Z_le_gt_dec (2 + j) pe) as [RM|RM]].
    all: try solve [exfalso; lia].
    all: lazymatch goal with
         | O8 : 8 <= _, RM : 2 + _ <= _ |- _ => x42_w4_run (KZRange (pe - j) 2 (2^32)) (KZRange (dcap - j) 2 (2^32)) (KZRange off 8 (2^32))
         | O8 : _ < 8, RM : 2 + _ <= _ |- _ => x42_w4_run (KZRange (pe - j) 2 (2^32)) (KZRange (dcap - j) 2 (2^32)) (KZRange off 1 7)
         | O8 : 8 <= _, RM : 2 + _ > _ |- _ => x42_w4_run (KZRange (pe - j) 0 1) (KZRange (dcap - j) 0 (2^32)) (KZRange off 8 (2^32))
         | O8 : _ < 8, RM : 2 + _ > _ |- _ => x42_w4_run (KZRange (pe - j) 0 1) (KZRange (dcap - j) 0 (2^32)) (KZRange off 1 7)
         | _ => kx_autoLx [0x21a9c; 0x21bac; 0x21bec] 30%nat
                  [KZRange S 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32);
                   KZRange DST 4096 (2^47)] [(SPV - 416, 160); (SPV - 256, 40)]
         end.
    all: kx_ev_ranges; kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with
         | BD' : rw_cells _ _ _ [_; _; _; C8 (Z_to_bv 64 ?X); _; _] |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 137884) _ _ ?m2 _) =>
             replace X with (S + (X - S)) in BD' by lia;
             eapply (IH mb m2 J pe (X - S) S len bs dl sh BC); try eassumption; try lia; try solve [unfold RZ_huf_dx41.SINV; lia];
             try solve [exact (bv_unsigned_in_range 64 _)]; try (intros; eapply K; try eassumption; first [reflexivity | lia])
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 138156) _ _ ?m2 _) =>
             eapply (x42_t4 (Z.to_nat dcap) mb m2 J pe dl sh); try eassumption; try lia; intros mm' D7; intros; eapply (K mm' D7); try eassumption; first [reflexivity | lia]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 138220) _ _ ?m2 _) =>
             eapply (x42_la4 mb m2 J pe dl); try eassumption; try lia; intros mm' D7; intros; eapply (K mm' D7); try eassumption; first [reflexivity | lia]
         end.
  Qed.

End DX42_4B.
