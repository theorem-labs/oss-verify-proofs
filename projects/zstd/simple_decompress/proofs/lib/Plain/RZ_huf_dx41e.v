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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41d.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41E.
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

  Notation SINV := RZ_huf_dx41.SINV.
  Notation x41_p4 := (x41_p4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3).
  Notation x41_l4 := (x41_l4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3).

  (* [comment removed for export] *)
  Lemma x41_e4 : forall mb mm j off S len bs dl tl rsv bc (c0 b0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD4 mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 (Z_to_bv 64 (DST + dcap)) w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    BD4 mm c0 b0 pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) ->
    0 <= j <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' (y5 y6 y7 y11 y12 y13 y15 y17 y21 y28 y29 y30 y31 c' b' p' : word),
        munch WD4 mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) ->
        BD4 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt psegs POST (ST 0x23eb0 mm' x1 y5 y6 y7 x8 x9 x10 y11 y12 y13 x14 y15 x16 y17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) y21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x23d30 mm x1 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 bc) x14 x15 x16 x17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j off S len bs dl tl rsv bc c0 b0 pad x1 x5 x6 x7 x8 x9 x10 x11 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK HJ HDL HTL HRSV HS HB K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]]|].
    all: lazymatch goal with
         | B64 : _ > 64 |- _ =>
             kx_autoLx [0x23e60; 0x23eb0] 30%nat [KZRange bc 65 (2^64 - 1); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 0 (2^32);
                                 KZRange DST 4096 (2^47); KZWr (SPV - 256) 40; KZDisj (SPV - 256) 40 (SPV - 416) 160]
               [(SPV - 416, 160); (SPV - 256, 40)]
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x23e60; 0x23eb0] 120%nat
               [KZRange (len - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZWr (SPV - 256) 40; KZDisj (SPV - 256) 40 S len; KZDisj (SPV - 256) 40 (SPV - 416) 160]
               [(S, len); (SPV - 416, 160); (SPV - 256, 40)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x23e60; 0x23eb0] 120%nat
               [KZRange (len - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZWr (SPV - 256) 40; KZDisj (SPV - 256) 40 S len; KZDisj (SPV - 256) 40 (SPV - 416) 160]
               [(S, len); (SPV - 416, 160); (SPV - 256, 40)]
         | _ => kx_autoLx [0x23e60; 0x23eb0] 30%nat [KZRange bc 0 64; KZRange S 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32);
                                    KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] [(SPV - 416, 160); (SPV - 256, 40)]
         end.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147040) _ _ _ _) =>
             eapply (x41_p4 mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147120) _ _ _ _) => eapply K; eassumption
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_d4 : forall mb mm j off S len bs dl tl rsv bc (c0 : word) pad
      (x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17 w18 w19 : word),
    munch WD4 mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 (Z_to_bv 64 (DST + dcap)) w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (DST + dcap - 3)) w16 w17 w18 w19 ->
    BD4 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) ->
    0 <= j <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^32 ->
    (forall mm' (y5 y6 y7 y11 y12 y13 y15 y17 y21 y28 y29 y30 y31 c' b' p' : word),
        munch WD4 mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) ->
        BD4 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt psegs POST (ST 0x23eb0 mm' x1 y5 y6 y7 x8 x9 x10 y11 y12 y13 x14 y15 x16 y17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) y21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x23b94 mm x1 (Z_to_bv 64 (DST + dcap)) x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + j)) x13 x14 x15 x16 x17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j off S len bs dl tl rsv bc c0 pad x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17 w18 w19 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK HJ HDL HTL HRSV HS HB K.
    kx_autoLx [0x23d30; 0x23bb8; 0x23e60; 0x23eb0] 40%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange bc 0 (2^32 - 1);
       KZRange dl 0 65535; KZRange SPV 4096 (2^47); KZWr (SPV - 256) 40; KZDisj (SPV - 256) 40 (SPV - 416) 160]
      [(SPV - 416, 160); (SPV - 256, 40)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147040) _ _ _ _) =>
             eapply (x41_p4 mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147120) _ _ _ _) => eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 146736) _ _ _ _) =>
             eapply (x41_e4 mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 146360) _ _ _ _) =>
             subst dl; rewrite (neg_dl_sh tl rsv HTL);
             eapply (x41_l4 (Z.to_nat (dcap - j)) mb); try eassumption; try lia; try reflexivity;
             intros; eapply K; eassumption
         end.
  Qed.

End DX41E.
