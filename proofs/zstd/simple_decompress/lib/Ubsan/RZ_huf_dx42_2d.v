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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_2a RZ_huf_dx42_2b RZ_huf_dx42_2c.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf41_kit_reload huf42_2_t2kit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_2D.
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
  Notation x42_c2 := (RZ_huf_dx42_2c.x42_c2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).

  Ltac pm2_walk S len off bc BLO BHI OLO OHI :=
    kx_autoLx [0x274f4; 0x2965c] 60%nat
      [KZRange bc BLO BHI; KZRange off OLO OHI; KZRange (len - off) 8 (2^32); KZRange len 9 (2^32); KZRange S 4096 (2^47);
       KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange DT 4096 (2^47);
       KZWr (SPV - 696) 40; KZDisj (SPV - 696) 40 S len; KZDisj (SPV - 696) 40 DT 16388; KZDisj DST dcap (SPV - 696) 40]
      [(S, len); (SPV - 912, 136); (SPV - 696, 40)].

  Lemma x42_pm2 : forall mb mm off S len bs bc (c0 : word) pad e pe
      (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
    munch WD2 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> (S + len <= lo \/ SPV <= S) ->
    1 <= off <= 7 -> off + 8 <= len -> 0 <= bc <= 64 ->
    (forall mm' off' bc' fl (c' y11 y12 y13 y14 y15 y16 y17 : word),
        munch WD2 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD2 mm' c' (Z_to_bv 64 bc') pad (Z_to_bv 64 (S + off')) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        bytes_at usegs mm' S bs -> 0 <= off' <= off -> 0 <= bc' <= 64 -> 0 <= fl <= 1 ->
        evt usegs POST (ST 0x274f4 mm' x1 x5 x6 x7 x8 x9 (Z_to_bv 64 fl) y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x2740c mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 bc) (Z_to_bv 64 S) (Z_to_bv 64 (S + off)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm off S len bs bc c0 pad e pe x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJT DJK HO HOL HB K.
    assert (QC : 0 <= bc <= 7 \/ 8 <= bc <= 15 \/ 16 <= bc <= 23 \/ 24 <= bc <= 31 \/ 32 <= bc <= 39 \/ 40 <= bc <= 47 \/ 48 <= bc <= 55 \/ 56 <= bc <= 63 \/ 64 <= bc <= 64) by lia.
    destruct QC as [QC|[QC|[QC|[QC|[QC|[QC|[QC|[QC|QC]]]]]]]];
      [ pm2_walk S len off bc 0 7 1 7
      | pm2_walk S len off bc 8 15 1 7
      | destruct (Z_lt_le_dec off 2) as [OQ|OQ]; [pm2_walk S len off bc 16 23 1 1 | pm2_walk S len off bc 16 23 2 7]
      | destruct (Z_lt_le_dec off 3) as [OQ|OQ]; [pm2_walk S len off bc 24 31 1 2 | pm2_walk S len off bc 24 31 3 7]
      | destruct (Z_lt_le_dec off 4) as [OQ|OQ]; [pm2_walk S len off bc 32 39 1 3 | pm2_walk S len off bc 32 39 4 7]
      | destruct (Z_lt_le_dec off 5) as [OQ|OQ]; [pm2_walk S len off bc 40 47 1 4 | pm2_walk S len off bc 40 47 5 7]
      | destruct (Z_lt_le_dec off 6) as [OQ|OQ]; [pm2_walk S len off bc 48 55 1 5 | pm2_walk S len off bc 48 55 6 7]
      | destruct (Z_lt_le_dec off 7) as [OQ|OQ]; [pm2_walk S len off bc 56 63 1 6 | pm2_walk S len off bc 56 63 7 7]
      | pm2_walk S len off bc 64 64 1 7
      ].
    all: t2side.
    all: t2ck.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | H : rw_cells usegs ?m2 (SPV + -696) [C8 ?c; C4 (Z_to_bv 64 ?B); CB 4 _; C8 (Z_to_bv 64 ?X); _; _]
           |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?FL) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m2 _) =>
             eapply (K m2 (X - S) B FL c); try eassumption; try lia; replace (S + (X - S)) with X by lia; exact H
         end.
  Qed.

  Ltac p2_res := lazymatch goal with
    | SB : bytes_at usegs _ ?S _ |- sc_resid _ _ _ (SCReadBase _ _ _ _) => try (kx_rd SB)
    | |- sc_resid _ _ _ _ => try kx_z
    | _ => idtac end.

  Ltac p2_go S len j e sh ROOM ROOM2 OFFH LENH BCH :=
    kx_autoLx [0x273f8; 0x2740c; 0x27b38; 0x27d48; 0x2965c; 0x25ca0] 200%nat
      [ROOM2; ROOM; OFFH; LENH; BCH; KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZRange sh 52 63;
       KZWr DST dcap; KZWr (SPV - 696) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap S len; KZDisj DST dcap (SPV - 696) 40;
       KZDisj (SPV - 696) 40 S len; KZDisj (SPV - 696) 40 DT 16388; KZTblLog DT sh 4 7 1 2; KZDisj DST dcap (SPV - 912) 136;
       KZDisj (SPV - 696) 40 (SPV - 912) 136]
      [(DT, 16388); (S, len); (SPV - 912, 136); (SPV - 696, 40)].

  Lemma x42_pd2 : forall mb mm j e pe off S len bs dl sh bc fl (c0 : word) pad
      (x1 x5 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
    munch WD2 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    0 <= j <= e -> e <= dcap -> pe <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    0 <= off -> off + 8 <= len -> 0 <= bc <= 64 -> 0 <= fl <= 1 ->
    K2 mb e pe dl S pad x5 x7 x18 x20 x21 x26 x28 x29 x30 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ->
    (forall mm' J off2 bc2 (c2 y1 y8 y11 y12 y13 y14 y15 y16 y17 : word),
        munch WD2 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD2 mm' c2 (Z_to_bv 64 bc2) pad (Z_to_bv 64 (S + off2)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        bytes_at usegs mm' S bs -> j < J <= e -> RZ_huf_dx41.SINV off2 len bc2 -> 0 <= bc2 <= 64 ->
        evt usegs POST (ST 0x273f8 mm' y1 x5 (Z_to_bv 64 (DT + 4)) x7 y8 (Z_to_bv 64 64) (Z_to_bv 64 bc2) y11 y12 y13 y14 y15 y16 y17
                          x18 (Z_to_bv 64 (2^61)) x20 x21 (Z_to_bv 64 (DST + e - 9)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 dl) x26
                          (Z_to_bv 64 (DST + J)) x28 x29 x30 (Z_to_bv 64 (DST + pe)))) ->
    evt usegs POST (ST 0x274f4 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 (Z_to_bv 64 64) (Z_to_bv 64 fl) x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) x20 x21 (Z_to_bv 64 (DST + e - 9)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 dl) x26
                      (Z_to_bv 64 (DST + j)) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe off S len bs dl sh bc fl c0 pad x1 x5 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJT DJK SPA HJ HE HPE HDL HSH HO HOL HB HFL K HD.
    assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    destruct (Z_le_gt_dec (10 + j) e) as [RM|RM];
      [ p2_go S len j e sh (KZRange (e - j) 10 (2^32)) (KZRange (dcap - j) 10 (2^32)) (KZRange off 0 (2^32)) (KZRange (len - off) 8 (2^32)) (KZRange bc 0 64)
      | p2_go S len j e sh (KZRange (e - j) 0 9) (KZRange (dcap - j) 0 (2^32)) (KZRange off 0 (2^32)) (KZRange (len - off) 8 (2^32)) (KZRange bc 0 64) ].
    all: t2side.
    all: t2ck.
    all: p2_res.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x273f8) _ _ ?m2 _) =>
             lazymatch goal with H : rw_cells usegs m2 (SPV + -696) [_; _; _; C8 (Z_to_bv 64 ?X); _; _] |- _ =>
               eapply (HD m2 J (X - S) BC); try eassumption; try lia;
               try (replace (S + (X - S)) with X by lia; exact H); try solve [unfold RZ_huf_dx41.SINV; lia]
             end
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27b38) _ _ ?m2 _) =>
             lazymatch goal with H : rw_cells usegs m2 (SPV + -696) [_; C4 (Z_to_bv 64 ?B); _; C8 (Z_to_bv 64 ?X); _; _] |- _ =>
               eapply (x42_c2 mb m2 J e pe S len bs dl B X); try eassumption; try lia;
               try (intros; exists (X - S); split; [lia | unfold RZ_huf_dx41.SINV; lia]);
               try (kx_ev_ranges; lia); try (intro; kx_ev_ranges; exfalso; lia)
             end
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27d48) _ _ ?m2 _) =>
             eapply (x42_la2 mb m2 J e pe dl S pad); try eassumption; try lia
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_p2 : forall (k : nat) mb mm j e pe off S len bs dl sh bc (c0 : word) pad
      (x1 x5 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
    munch WD2 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    e - j <= Z.of_nat k -> 0 <= j <= e -> e <= dcap -> pe <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    SINV off len bc -> 0 <= bc <= 64 ->
    K2 mb e pe dl S pad x5 x7 x18 x20 x21 x26 x28 x29 x30 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ->
    evt usegs POST (ST 0x273f8 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 (Z_to_bv 64 64) (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) x20 x21 (Z_to_bv 64 (DST + e - 9)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 dl) x26
                      (Z_to_bv 64 (DST + j)) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    pose proof huf_reload_proof as HRL. unfold huf_reload_stmt, huf_reload_stmt_at, bitd_cells in HRL.
    induction k as [|k IH]; intros mb mm j e pe off S len bs dl sh bc c0 pad x1 x5 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJT DJK SPA HK HJ HE HPE HDL HSH HS HB K.
    all: assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    all: assert (BDA : (SPV + -696) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
    all: assert (HD : forall mm' J off2 bc2 (c2 y1 y8 y11 y12 y13 y14 y15 y16 y17 : word),
        munch WD2 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD2 mm' c2 (Z_to_bv 64 bc2) pad (Z_to_bv 64 (S + off2)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        bytes_at usegs mm' S bs -> j < J <= e -> RZ_huf_dx41.SINV off2 len bc2 -> 0 <= bc2 <= 64 ->
        evt usegs POST (ST 0x273f8 mm' y1 x5 (Z_to_bv 64 (DT + 4)) x7 y8 (Z_to_bv 64 64) (Z_to_bv 64 bc2) y11 y12 y13 y14 y15 y16 y17
                          x18 (Z_to_bv 64 (2^61)) x20 x21 (Z_to_bv 64 (DST + e - 9)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 dl) x26
                          (Z_to_bv 64 (DST + J)) x28 x29 x30 (Z_to_bv 64 (DST + pe))))
      by (intros mm' J off2 bc2 c2 y1 y8 y11 y12 y13 y14 y15 y16 y17; intros;
          first [exfalso; lia | eapply (IH mb mm' J e pe off2 S len bs dl sh bc2); first [eassumption | lia]]).
    all: destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]]; destruct (Z_le_gt_dec (10 + j) e) as [RM|RM].
    all: try solve [exfalso; lia].
    all: lazymatch goal with
         | O8 : 8 <= _, RM : 10 + _ <= _ |- _ =>
             p2_go S len j e sh (KZRange (e - j) 10 (2^32)) (KZRange (dcap - j) 10 (2^32)) (KZRange off 8 (2^32)) (KZRange (len - off) 8 (2^32)) (KZRange bc 0 64)
         | O8 : 8 <= _ |- _ =>
             p2_go S len j e sh (KZRange (e - j) 0 9) (KZRange (dcap - j) 0 (2^32)) (KZRange off 8 (2^32)) (KZRange (len - off) 8 (2^32)) (KZRange bc 0 64)
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x2740c; 0x2965c] 20%nat
               [KZRange off 1 7; KZRange (len - off) 8 (2^32); KZRange bc 0 64; KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(SPV - 912, 136); (SPV - 696, 40)]
         | RM : 10 + _ <= _ |- _ =>
             kx_autoLx [0x27b38; 0x27d48; 0x2965c] 40%nat
               [KZRange (e - j) 10 (2^32); KZRange bc 0 64; KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47);
                KZRange SPV 4096 (2^47)] [(SPV - 912, 136); (SPV - 696, 40)]
         | _ =>
             kx_autoLx [0x27b38; 0x27d48; 0x2965c] 40%nat
               [KZRange (e - j) 0 9; KZRange bc 0 64; KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47);
                KZRange SPV 4096 (2^47)] [(SPV - 912, 136); (SPV - 696, 40)]
         end.
    all: t2side.
    all: t2ck.
    all: p2_res.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2740c) _ _ _ _) =>
             try replace (off + S) with (S + off) by lia;
             eapply (x42_pm2 mb mm off S len bs bc c0 pad e pe); try eassumption; try lia;
             intros mm' o3 b3 fl c' y11 y12 y13 y14 y15 y16 y17 MU' WM' MI' OUT' DTB' FA' BD' SB' HO3 HB3 HFL;
             clear MU WM MI OUT DTB FA BD SB TBL;
             eapply (x42_pd2 mb mm' j e pe o3 S len bs dl sh b3 fl c'); try eassumption; lia
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x25ca0) _ _ _ _) =>
             eapply evt_cut;
             [ eapply HRL; [ exact MI | exact BD | exact BDA | exact SB | exact SL | lia | lia | lia | lia | lia | lia | lia | lia ]
             | post_call usegs mm ];
             unfold bitd_cells in *;
             replace (S + off - bc / 8) with (S + (off - bc / 8)) in * by lia;
             assert (O3 : 0 <= off - bc / 8 /\ off - bc / 8 + 8 <= len) by (Z.div_mod_to_equations; lia);
             assert (B3 : 0 <= bc mod 8 < 8) by (apply Z.mod_pos_bound; lia);
             set (o3 := off - bc / 8) in *; set (b3 := bc mod 8) in *; clearbody o3 b3;
             kx_autoLx [0x274f4; 0x2965c] 20%nat
               [KZRange o3 0 (2^32); KZRange (len - o3) 8 (2^32); KZRange b3 0 7; KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(SPV - 912, 136); (SPV - 696, 40)];
             t2side; t2ck; p2_res
         | _ => idtac
         end.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?FL) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x274f4) _ _ ?m2 _) =>
             lazymatch goal with H : rw_cells usegs m2 (SPV + -696) [C8 ?c; C4 (Z_to_bv 64 ?B); _; C8 (Z_to_bv 64 ?X); _; _] |- _ =>
               eapply (x42_pd2 mb m2 j e pe (X - S) S len bs dl sh B FL c); try eassumption; try lia;
               replace (S + (X - S)) with X by lia; exact H
             end
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27b38) _ _ ?m2 _) =>
             lazymatch goal with H : rw_cells usegs m2 (SPV + -696) [_; C4 (Z_to_bv 64 ?B); _; C8 (Z_to_bv 64 ?X); _; _] |- _ =>
               eapply (x42_c2 mb m2 J e pe S len bs dl B X); try eassumption; try lia;
               try (intros; exists (X - S); split; [lia | unfold RZ_huf_dx41.SINV; lia])
             end
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27d48) _ _ ?m2 _) =>
             eapply (x42_la2 mb m2 J e pe dl S pad); try eassumption; try lia
         end.
  Qed.

End DX42_2D.
