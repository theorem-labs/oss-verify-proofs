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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_dx42_0b huf41_kit_reload.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_4A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 912, SPV - 616)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -912) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD4 := [(DST, DST + dcap); (SPV - 776, SPV - 736)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -776) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).

  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).
  Notation x42_tbl_nb := (RZ_huf_dx42_0b.x42_tbl_nb SPV DST dcap DT lo dtb CTX tl TL NBOK).
  Notation FRA7 mm pe w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 :=
    (FRA mm w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 (DST + pe - 7)) w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4))).
  Notation K4 mb pe S pad x26 w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 :=
    (forall mm' (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y27 y28 y29 y30 y31 c' b' p' : word),
        munch WD4 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA7 mm' pe w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 -> BD4 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x290ec mm' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 x26 y27 y28 y29 y30 y31)).
  Ltac x42_chk := kx_trap_fast.

  Lemma x42_rl4 : forall mb mm (RA : Z) (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (c0 : word) bc p S len bs pad (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD4 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 p) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 -> 0 <= bc <= 64 -> S + 8 <= p -> p <= S + len - 8 ->
    0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall mm' c' (y11 y12 y13 y14 y15 y16 : word),
        munch WD4 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
        BD4 mm' c' (Z_to_bv 64 (bc mod 8)) pad (Z_to_bv 64 (p - bc / 8)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        bytes_at usegs mm' S bs ->
        evt usegs POST (ST RA mm' (Z_to_bv 64 RA) x5 x6 x7 x8 x9 (Z_to_bv 64 (SPV + -776)) y11 y12 y13 y14 y15 y16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x25ca0 mm (Z_to_bv 64 RA) x5 x6 x7 x8 x9 (Z_to_bv 64 (SPV + -776)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm RA x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 c0 bc p S len bs pad
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 DJS DJK SPA HB HP1 HP2 RA0 RA2 KC.
    pose proof huf_reload_proof as HR. unfold huf_reload_stmt, huf_reload_stmt_at in HR.
    eapply evt_cut.
    { eapply (HR (Z_to_bv 64 RA) (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm (SPV + -776) S len bc p c0 pad bs);
        [exact MI | unfold bitd_cells; exact BD | lia | exact SB | exact SL | lia | lia | lia | lia | lia | lia | lia | lia]. }
    intros ms' (a1 & a2 & a3 & a4 & a5 & a6 & m' & cont' & -> & MU1 & WM1 & MI1 & BD1).
    unfold bitd_cells in BD1. rewrite (ret_pc_even RA RA0 RA2).
    apply (KC m' cont' a1 a2 a3 a4 a5 a6).
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU1].
      intros x Hx. cbn in Hx |- *. destruct Hx as (H1 & H2 & _). split; [lia | exact I].
    - eapply wmono_trans; eassumption.
    - exact MI1.
    - eapply stk_transport_disjoint; [exact OUT | exact MU1 | exact WM1 |]. cbn. split; [lia | exact I].
    - eapply bytes_at_transport; [exact DTB | exact MU1 |]. cbn. split; [lia | exact I].
    - eapply rw_cells_transport; [exact FA | exact MU1 | exact WM1 |]. cbn. split; [lia | exact I].
    - exact BD1.
    - eapply bytes_at_transport; [exact SB | exact MU1 |]. cbn. split; [lia | exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_la4 : forall mb mm j pe dl S (c0 b0 p0 : word) pad
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA7 mm pe w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 -> BD4 mm c0 b0 pad p0 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv ->
    K4 mb pe S pad x26 w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 ->
    evt usegs POST (ST 0x29058 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (2^61))
                       x20 x21 x22 x23 x24 (Z_to_bv 64 dl) x26 x27 x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe dl S c0 b0 p0 pad x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 MU WM MI OUT DTB FA BD HJ HPE HDL K.
    destruct (Z_lt_le_dec j pe) as [ROOM|FULL]; cycle 1.
    - kx_autoLx [0x290ec] 10%nat [KZRange (j - pe) 0 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange DST 4096 (2^47);
                                  KZRange SPV 4096 (2^47)] [(SPV - 912, 136); (SPV - 776, 40)].
      all: eapply K; eassumption.
    - subst dl.
      assert (TLC : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
      repeat (destruct TLC as [TLC|TLC]); rewrite TLC in *;
        kx_autoLx [0x290ec; 0x2965c] 60%nat
          [KZRange (dcap - j) 1 (2^32); KZRange (pe - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
           KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange rsv 0 255; KZRange SPV 4096 (2^47); KZWr DST dcap; KZWr (SPV - 776) 40;
           KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 912) 136; KZDisj DST dcap (SPV - 776) 40]
          [(DT, 16388); (SPV - 912, 136); (SPV - 776, 40)].
      all: kx_ev_ranges.
      all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2965c) _ _ _ _) => x42_chk | _ => idtac end.
      all: kx_mem.
      all: eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_t4 : forall (k : nat) mb mm j pe dl sh S (c0 b0 p0 : word) pad
      (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x26 x27 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA7 mm pe w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 -> BD4 mm c0 b0 pad p0 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    pe - j <= Z.of_nat k -> 0 <= j -> j + 2 <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    K4 mb pe S pad x26 w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 ->
    evt usegs POST (ST 0x29000 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 (Z_to_bv 64 (DST + pe - 2)) (Z_to_bv 64 sh) x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (-1 * DT + -5)) x21 x22 x23 x24 (Z_to_bv 64 dl) x26 x27 x28 x29 x30
                       (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe dl sh S c0 b0 p0 pad x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x26 x27 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 MU WM MI OUT DTB FA BD HK HJ0 HJ HPE HDL HSH K; [exfalso; lia|].
    assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    kx_autoLx [0x29000; 0x29058; 0x2965c] 60%nat
      [KZRange (dcap - j) 2 (2^32); KZRange (pe - j) 2 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange SPV 4096 (2^47); KZWr DST dcap; KZWr (SPV - 776) 40;
       KZDisj DST dcap DT 16388; KZTblLog DT sh 4 7 1 2; KZDisj DST dcap (SPV - 912) 136; KZDisj DST dcap (SPV - 776) 40;
       KZDisj (SPV - 776) 40 DT 16388; KZDisj (SPV - 776) 40 (SPV - 912) 136]
      [(DT, 16388); (SPV - 912, 136); (SPV - 776, 40)].
    all: kx_ev_ranges.
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2965c) _ _ _ _) => x42_chk | _ => idtac end.
    all: kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x29000) _ _ ?m2 _) =>
             eapply (IH mb m2 J pe dl sh S); try eassumption; try lia
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x29058) _ _ ?m2 _) =>
             eapply (x42_la4 mb m2 J pe dl S); try eassumption; try lia
         end.
  Qed.

End DX42_4A.
