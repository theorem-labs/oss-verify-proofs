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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf41_kit_x41ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41D.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 224, SPV - 184)].
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation K4E mb st lm pad dl x8 x9 x18 x22 x23 x24 x26 :=
    (forall mm' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y27 y28 y29 y30 y31 c' b' p' : word),
        munch WD4 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) ->
        BD4 mm' c' b' pad p' st lm ->
        evt usegs POST (ST 0x24fcc mm' y1 y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) y21
                           x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 y27 y28 y29 y30 y31)).

  (* [comment removed for export] *)
  Lemma x41_end : forall mm (c1 b1 p1 st1 lm1 c2 b2 p2 st2 lm2 c3 b3 p3 st3 lm3 c4 b4 p4 st4 lm4 : word) pad1 pad2 pad3 pad4
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w14 w15 w16 : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINV mm -> FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 dcap) w14 w15 w16 ->
    BD1 mm c1 b1 pad1 p1 st1 lm1 -> BD2 mm c2 b2 pad2 p2 st2 lm2 -> BD3 mm c3 b3 pad3 p3 st3 lm3 -> BD4 mm c4 b4 pad4 p4 st4 lm4 ->
    evt usegs POST (ST 0x24fcc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                       x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm c1 b1 p1 st1 lm1 c2 b2 p2 st2 lm2 c3 b3 p3 st3 lm3 c4 b4 p4 st4 lm4 pad1 pad2 pad3 pad4
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w14 w15 w16
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI FA B1 B2 B3 B4.
    kx_autoLx [0x23594] 40%nat [KZRange SPV 4096 (2^47)]
      [(SPV - 512, 136); (SPV - 376, 40); (SPV - 224, 40); (SPV - 184, 40); (SPV - 144, 40)].
    all: clear KXBR.
    all: eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm);
         [exact EI | first [left; reflexivity | right; split; reflexivity]].
  Qed.

  (* [comment removed for export] *)
  Lemma x41_t4 : forall (k : nat) mb mm j sh dl (c0 b0 p0 st0 lm0 : word) pad
      (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x22 x23 x24 x26 x28 x29 x30 x31 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    BD4 mm c0 b0 pad p0 st0 lm0 ->
    dcap - j <= Z.of_nat k -> 0 <= j < dcap -> 52 <= sh <= 63 ->
    K4E mb st0 lm0 pad dl x8 x9 x18 x22 x23 x24 x26 ->
    evt usegs POST (ST 0x24f80 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 sh) (Z_to_bv 64 2) (Z_to_bv 64 (DST + j))
                       x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + j)) x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26
                       (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j sh dl c0 b0 p0 st0 lm0 pad x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x22 x23 x24 x26 x28 x29 x30 x31
      MU WM MI OUT DTB BD HK HJ HSH K; [exfalso; lia|].
    kx_autoLx [0x24f80; 0x24fcc] 40%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange SPV 4096 (2^47); KZWr DST dcap; KZWr (SPV - 224) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 224) 40; KZDisj (SPV - 224) 40 DT 16388]
      [(DT, 16388); (SPV - 224, 40)].
    all: x41_ck.
    all: kx_ev_ranges; kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x24f80) _ _ _ _) =>
             replace A with (DST + (A - DST)) by lia;
             eapply (IH mb _ (A - DST) sh dl); try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24fcc) _ _ _ _) => eapply K; eassumption
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_p4 : forall mb mm j dl tl rsv (c0 b0 p0 st0 lm0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x28 x29 x30 x31 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    BD4 mm c0 b0 pad p0 st0 lm0 ->
    0 <= j < dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    K4E mb st0 lm0 pad dl x8 x9 x18 x22 x23 x24 x26 ->
    evt usegs POST (ST 0x24f6c mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62))
                       (Z_to_bv 64 (DST + j)) x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j dl tl rsv c0 b0 p0 st0 lm0 pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x28 x29 x30 x31
      MU WM MI OUT DTB BD HJ HDL HTL HRSV K.
    kx_autoLx [0x24f80] 10%nat
      [KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange dl 1 65535] [].
    subst dl; rewrite (neg_dl_sh tl rsv HTL).
    eapply (x41_t4 (Z.to_nat (dcap - j)) mb mm j (64 - tl) (tl + 256 * rsv)); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Notation SINV := RZ_huf_dx41.SINV.
  Ltac x41_side := lazymatch goal with |- evt _ _ _ => idtac | |- _ => try solve [lia] end.
  Ltac x41_fl :=
    lazymatch goal with
    | A : atoms_ok ?zs ?E |- context [bv_unsigned (edenot ?E (EAlu ALU_SLTU ?a ?b))] =>
        rewrite (kxub_sltu zs E a b A);
        lazymatch goal with |- context [Z.b2z ?c] => destruct c end; cbn; lia
    end.
  Ltac x41_exit mb K :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x24f6c) _ _ _ _) =>
        replace A with (DST + (A - DST)) by lia;
        eapply (x41_p4 mb _ (A - DST)); try eassumption; try lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24fcc) _ _ _ _) => eapply K; eassumption
    end.
  Ltac x41_res :=
    match goal with
    | SB : bytes_at usegs _ _ _ |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_rd SB
    | |- sc_resid _ _ _ _ => kx_z
    | |- _ => idtac
    end.
  Ltac x41_r4_walk S len off bc BLO BHI OLO OHI :=
    kx_autoLx [0x24d00] 60%nat
      [KZRange bc BLO BHI; KZRange off OLO OHI; KZRange (len - off) 8 (2^32); KZRange len 9 (2^32); KZRange S 4096 (2^47);
       KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange DT 4096 (2^47);
       KZWr (SPV - 224) 40; KZDisj (SPV - 224) 40 S len; KZDisj (SPV - 224) 40 (SPV - 512) 136; KZDisj DST dcap (SPV - 224) 40]
      [(S, len); (SPV - 512, 136); (SPV - 224, 40)].
  Ltac x41_b4_walk S len P j bc tl FUEL ROOM :=
    kx_autoLx [0x24f6c; 0x24fcc; 0x24c4c] FUEL
      [ROOM; KZRange (P - S) 0 (2^32); KZRange (S + len - P) 8 (2^32); KZRange bc 0 64; KZRange len 8 (2^32);
       KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange SPV 4096 (2^47);
       KZWr DST dcap; KZWr (SPV - 224) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap S len; KZDisj DST dcap (SPV - 512) 136;
       KZDisj DST dcap (SPV - 224) 40; KZDisj (SPV - 224) 40 DT 16388; KZDisj (SPV - 224) 40 S len; KZDisj (SPV - 224) 40 (SPV - 512) 136]
      [(DT, 16388); (S, len); (SPV - 512, 136); (SPV - 224, 40)].

  Lemma x41_r4 : forall mb mm j off S len bs dl tl bc (c0 b0 : word) pad
      (x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (DST + dcap)) w9 (Z_to_bv 64 (DST + dcap - 3)) w11 w12 w13 w14 w15 w16 ->
    BD4 mm c0 b0 pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    1 <= off <= 7 -> off + 8 <= len -> 0 <= bc <= 64 ->
    (forall mm' P bc' fl A5 (c' b' y7 y28 y29 y30 y31 : word),
        munch WD4 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (DST + dcap)) w9 (Z_to_bv 64 (DST + dcap - 3)) w11 w12 w13 w14 w15 w16 ->
        BD4 mm' c' b' pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs ->
        S <= P -> P + 8 <= S + len -> 0 <= bc' <= 64 -> (fl = 0 \/ fl = 1) -> A5 = DST + j ->
        evt usegs POST (ST 0x24d00 mm' x1 (Z_to_bv 64 fl) (Z_to_bv 64 P) y7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + j + 3))
                           (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j))
                           (Z_to_bv 64 bc') x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) (Z_to_bv 64 A5) x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26
                           (Z_to_bv 64 (DST + dcap)) y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x24c4c mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + j + 3)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 2)
                       (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 bc) x18 (Z_to_bv 64 dl)
                       (Z_to_bv 64 (2^62)) x21 x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j off S len bs dl tl bc c0 b0 pad x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK HO HOL HB K.
    assert (QC : 0 <= bc <= 7 \/ 8 <= bc <= 15 \/ 16 <= bc <= 23 \/ 24 <= bc <= 31 \/ 32 <= bc <= 39 \/ 40 <= bc <= 47 \/
                 48 <= bc <= 55 \/ 56 <= bc <= 63 \/ 64 <= bc <= 64) by lia.
    destruct QC as [QC|[QC|[QC|[QC|[QC|[QC|[QC|[QC|QC]]]]]]]];
      [ x41_r4_walk S len off bc 0 7 1 7
      | x41_r4_walk S len off bc 8 15 1 7
      | destruct (Z_lt_le_dec off 2) as [OQ|OQ]; [x41_r4_walk S len off bc 16 23 1 1 | x41_r4_walk S len off bc 16 23 2 7]
      | destruct (Z_lt_le_dec off 3) as [OQ|OQ]; [x41_r4_walk S len off bc 24 31 1 2 | x41_r4_walk S len off bc 24 31 3 7]
      | destruct (Z_lt_le_dec off 4) as [OQ|OQ]; [x41_r4_walk S len off bc 32 39 1 3 | x41_r4_walk S len off bc 32 39 4 7]
      | destruct (Z_lt_le_dec off 5) as [OQ|OQ]; [x41_r4_walk S len off bc 40 47 1 4 | x41_r4_walk S len off bc 40 47 5 7]
      | destruct (Z_lt_le_dec off 6) as [OQ|OQ]; [x41_r4_walk S len off bc 48 55 1 5 | x41_r4_walk S len off bc 48 55 6 7]
      | destruct (Z_lt_le_dec off 7) as [OQ|OQ]; [x41_r4_walk S len off bc 56 63 1 6 | x41_r4_walk S len off bc 56 63 7 7]
      | x41_r4_walk S len off bc 64 64 1 7 ].
    all: x41_side.
    all: x41_ck.
    all: kx_ev_ranges; kx_mem; kx_land_ranges; kx_strip_mod.
    all: eapply K; try eassumption; try lia; x41_fl.
  Qed.

  Lemma x41_b4 : forall mb mm j P S len bs dl tl rsv bc fl A5 (c0 b0 : word) pad
      (x1 x7 x8 x9 x18 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (DST + dcap)) w9 (Z_to_bv 64 (DST + dcap - 3)) w11 w12 w13 w14 w15 w16 ->
    BD4 mm c0 b0 pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    S <= P -> P + 8 <= S + len -> 0 <= bc <= 64 -> (fl = 0 \/ fl = 1) -> A5 = DST + j ->
    K4E mb (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) pad dl x8 x9 x18 x22 x23 x24 x26 ->
    (forall mm' A1 A6 bc' (c' b' y5 y6 y7 y21 y28 y29 y30 y31 : word),
        munch WD4 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (DST + dcap)) w9 (Z_to_bv 64 (DST + dcap - 3)) w11 w12 w13 w14 w15 w16 ->
        BD4 mm' c' b' pad (Z_to_bv 64 (S + (P - S))) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs ->
        0 <= P - S -> P - S + 8 <= len -> A1 = DST + (j + 4) + 3 -> A6 = DST + (j + 4) -> j + 4 <= dcap -> 0 <= bc' <= 64 ->
        evt usegs POST (ST 0x24c4c mm' x1 y5 y6 y7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 A1) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 2)
                           (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A6) (Z_to_bv 64 bc') x18 (Z_to_bv 64 dl)
                           (Z_to_bv 64 (2^62)) y21 x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 (Z_to_bv 64 (DST + dcap)) y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x24d00 mm x1 (Z_to_bv 64 fl) (Z_to_bv 64 P) x7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + j + 3))
                       (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j))
                       (Z_to_bv 64 bc) x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) (Z_to_bv 64 A5) x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26
                       (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j P S len bs dl tl rsv bc fl A5 c0 b0 pad x1 x7 x8 x9 x18 x22 x23 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK HJ HDL HTL HRSV
      HP0 HP1 HB HFL HA5 K KB.
    subst A5.
    destruct HFL as [-> | ->]; [|destruct (Z_lt_le_dec (dcap - j) 4) as [RM|RM]];
      [ x41_b4_walk S len P j bc tl 40%nat (KZRange (dcap - j) 0 (2^32))
      | x41_b4_walk S len P j bc tl 40%nat (KZRange (dcap - j) 0 3)
      | x41_b4_walk S len P j bc tl 200%nat (KZRange (dcap - j) 4 (2^32)) ].
    all: x41_side.
    all: x41_ck.
    all: x41_res.
    all: kx_ev_ranges; kx_mem; kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with
         | H : rw_cells usegs _ (SPV + -224) [_; _; _; C8 (Z_to_bv 64 ?X); C8 (Z_to_bv 64 ?S0); _]
           |- evt _ _ (MS _ _ (Z_to_bv 64 0x24c4c) _ _ _ _) =>
             replace X with (S0 + (X - S0)) in H by lia;
             eapply KB; try eassumption; try lia
         | |- _ => x41_exit mb K
         end.
  Qed.

  Lemma x41_l4 : forall (k : nat) mb mm j off S len bs dl tl rsv bc (c0 b0 : word) pad
      (x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (DST + dcap)) w9 (Z_to_bv 64 (DST + dcap - 3)) w11 w12 w13 w14 w15 w16 ->
    BD4 mm c0 b0 pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) ->
    dcap - j <= Z.of_nat k -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    K4E mb (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) pad dl x8 x9 x18 x22 x23 x24 x26 ->
    evt usegs POST (ST 0x24c4c mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + j + 3)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 2)
                       (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 bc) x18 (Z_to_bv 64 dl)
                       (Z_to_bv 64 (2^62)) x21 x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mb mm j off S len bs dl tl rsv bc c0 b0 pad x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x26 x28 x29 x30 x31
        w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK HK HJ HDL HTL HRSV HS HB K.
    all: destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]].
    all: lazymatch goal with
         | O8 : _ < 8 |- _ =>
             eapply (x41_r4 mb mm j off S len bs dl tl bc c0 b0 pad); try eassumption; try lia;
             intros mm2 P bc2 fl A5 c2 b2 y7 y28 y29 y30 y31 MU2 WM2 MI2 OUT2 DTB2 FA2 BD2 SB2 HP0 HP1 HB2 HFL HA5;
             eapply (x41_b4 mb mm2 j P S len bs dl tl rsv bc2 fl A5); try eassumption; try lia
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x24d00] 30%nat
               [KZRange off 8 (2^32); KZRange (len - off) 8 (2^32); KZRange bc 0 64; KZRange len 16 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
                KZRange DT 4096 (2^47); KZWr (SPV - 224) 40; KZDisj (SPV - 224) 40 S len; KZDisj (SPV - 224) 40 (SPV - 512) 136;
                KZDisj DST dcap (SPV - 224) 40]
               [(S, len); (SPV - 512, 136); (SPV - 224, 40)];
             x41_side; x41_ck; kx_ev_ranges; kx_mem; kx_land_ranges; kx_strip_mod;
             eapply (x41_b4 mb _ j); try eassumption; try lia
         | |- _ =>
             kx_autoLx [0x24f6c; 0x24fcc] 20%nat
               [KZRange S 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
               [(SPV - 512, 136); (SPV - 224, 40)];
             x41_side; x41_ck; kx_ev_ranges; kx_mem; x41_exit mb K
         end.
    all: intros mm3 A1 A6 bc3 c3 b3 z5 z6 z7 z21 z28 z29 z30 z31 MU3 WM3 MI3 OUT3 DTB3 FA3 BD3 SB3 HQ0 HQ1 HA1 HA6 HJ4 HB3;
         subst A1 A6.
    all: first [ exfalso; lia
               | eapply (IH mb mm3 (j + 4)); try eassumption; try lia; try solve [unfold RZ_huf_dx41.SINV; lia] ].
  Qed.

End DX41D.
