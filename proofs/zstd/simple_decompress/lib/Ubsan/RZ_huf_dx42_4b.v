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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2 KXSx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_4a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_dx42_0b.
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
  Notation x42_la4 := (RZ_huf_dx42_4a.x42_la4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_t4 := (RZ_huf_dx42_4a.x42_t4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_rl4 := (RZ_huf_dx42_4a.x42_rl4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation FRA7 mm pe w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 :=
    (FRA mm w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 (DST + pe - 7)) w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4))).
  Notation K4 mb pe S pad x26 w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 :=
    (forall mm' (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y27 y28 y29 y30 y31 c' b' p' : word),
        munch WD4 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA7 mm' pe w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 -> BD4 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x290ec mm' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 x26 y27 y28 y29 y30 y31)).
  Ltac x42_chk := kx_trap_fast.

  Ltac x42_w4_go S len j pe sh STOPS EXTRA :=
    kx_autoLcx STOPS 120%nat
      (EXTRA ++ [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange (dcap - pe) 0 (2^32);
       KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange len 0 (2^32); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47);
       KZRange SPV 4096 (2^47); KZRange sh 52 63; KZWr DST dcap; KZWr (SPV - 776) 40; KZTblLog DT sh 4 7 1 2;
       KZDisj DST dcap DT 16388; KZDisj DST dcap S len; KZDisj DST dcap (SPV - 912) 136; KZDisj DST dcap (SPV - 776) 40;
       KZDisj (SPV - 776) 40 DT 16388; KZDisj (SPV - 776) 40 (SPV - 912) 136; KZDisj (SPV - 776) 40 S len])
      [(DT, 16388); (S, len); (SPV - 912, 136); (SPV - 776, 40)].

  Ltac x42_sxh :=
    try kx_read_ranges;
    repeat match goal with
    | KXA : atoms_ok ?zs ?E, H : rw_cells _ _ _ ?L |- _ =>
        lazymatch L with context [C4 (edenot E ?e)] =>
          let nz := kx_len zs in
          let z := kx_ez2 E zs nz e in
          let P := kx_sxc E zs nz e in
          let HH := fresh "KXSX" in
          assert (HH : edenot E e = Z_to_bv 64 z) by (refine (ez2_sound zs E e KXA (_ : P)); repeat split; Lia.lia);
          rewrite HH in H; clear HH
        end
    end.

  Ltac x42_w4_fin IH mb S len bs pe dl sh :=
    lazymatch goal with
    | BD' : rw_cells _ ?m2 (SPV + -776) [_; C4 (Z_to_bv 64 ?ZC); _; C8 (Z_to_bv 64 ?X); _; _]
      |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x28e94) _ _ ?m2 _) =>
        (tryif constr_eq ZC BC then idtac else replace ZC with BC in BD' by lia);
        eapply (IH mb m2 J pe dl sh S len bs BC (X - S)); try eassumption; try (replace (S + (X - S)) with X by lia; eassumption);
        try lia; try solve [unfold RZ_huf_dx41.SINV in *; lia]
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x29000) _ _ ?m2 _) =>
        eapply (x42_t4 (Z.to_nat dcap) mb m2 J pe dl sh S); try eassumption; try lia
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x29058) _ _ ?m2 _) =>
        eapply (x42_la4 mb m2 J pe dl S); try eassumption; try lia
    | |- evt _ _ (MS ?R _ ?PC _ _ ?m2 _) =>
        lazymatch goal with H : rw_cells _ m2 (SPV + -776) ?L |- _ => fail 0 "NOFIN" PC "CELLS" L "REGS" R | _ => fail 0 "NOFIN0" PC R end
    | |- ?G => fail 0 "NOGOAL" G
    end.

  Ltac x42_norm := try (lazymatch goal with |- sc_resid _ ?m _ _ => first [kx_z | match goal with H : bytes_at _ m _ _ |- _ => kx_rd H end] end); kx_ev_ranges;
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2965c) _ _ _ _) => x42_chk | _ => idtac end.
  Ltac x42_post bc := kx_mem; kx_land_ranges; kx_strip_mod; try kx_sx; x42_sxh; rewrite ?(Z.mod_small bc (2^64)) in * by lia.

  (* [comment removed for export] *)
  Lemma x42_w4 : forall (k : nat) mb mm j pe dl sh S len bs bc off (c0 : word) pad
      (x1 x5 x7 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x26 x27 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA7 mm pe w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 -> BD4 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    pe - j < Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    SINV off len bc -> 0 <= bc <= 64 ->
    K4 mb pe S pad x26 w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 ->
    evt usegs POST (ST 0x28e94 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 (Z_to_bv 64 (DST + pe - 2)) (Z_to_bv 64 sh) (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (-1 * DT + -5)) x21 (Z_to_bv 64 64) x23 x24 (Z_to_bv 64 dl) x26 x27 x28 x29 x30
                       (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe dl sh S len bs bc off c0 pad x1 x5 x7 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x26 x27 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 w14 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK SPA HK HJ HPE HDL HSH HS HB K;
      [exfalso; lia|].
    assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]]; destruct (Z_le_gt_dec (2 + j) pe) as [RM|RM].
    - x42_w4_go S len j pe sh [0x29000; 0x29058; 0x2965c] [KZRange (pe - j) 2 (2^32); KZRange (dcap - j) 2 (2^32); KZRange bc 0 64].
      all: x42_norm.
      all: x42_post bc.
      all: x42_w4_fin IH mb S len bs pe dl sh.
    - x42_w4_go S len j pe sh [0x29000; 0x29058; 0x2965c] [KZRange (pe - j) 0 1; KZRange (dcap - j) 0 (2^32); KZRange bc 0 64].
      all: x42_norm.
      all: x42_post bc.
      all: x42_w4_fin IH mb S len bs pe dl sh.
    - x42_w4_go S len j pe sh [0x28e94; 0x29000; 0x29058; 0x2965c]
        [KZRange (pe - j) 2 (2^32); KZRange (dcap - j) 2 (2^32); KZRange bc 0 64; KZRange off 1 7; KZRange (len - off) 8 (2^32)].
      all: x42_norm.
      all: x42_post bc.
      all: x42_w4_fin IH mb S len bs pe dl sh.
    - x42_w4_go S len j pe sh [0x28e94; 0x29000; 0x29058; 0x2965c]
        [KZRange (pe - j) 0 1; KZRange (dcap - j) 0 (2^32); KZRange bc 0 64; KZRange off 1 7; KZRange (len - off) 8 (2^32)].
      all: x42_norm.
      all: x42_post bc.
      all: x42_w4_fin IH mb S len bs pe dl sh.
    - x42_w4_go S len j pe sh [0x25ca0; 0x2965c]
        [KZRange (pe - j) 2 (2^32); KZRange (dcap - j) 2 (2^32); KZRange bc 0 64; KZRange off 8 (2^32); KZRange (len - off) 8 (2^32)].
      all: x42_norm.
      all: kx_mem.
      all: eapply (x42_rl4 mb); try eassumption; try lia.
      all: intros mm' c' y11 y12 y13 y14 y15 y16 MU' WM' MI' OUT' DTB' FA' BD' SB'.
      all: assert (TBL' : tbl_in_log usegs mm' DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB').
      all: x42_w4_go S len j pe sh [0x28e94; 0x29000; 0x29058; 0x2965c]
        [KZRange (pe - j) 2 (2^32); KZRange (dcap - j) 2 (2^32); KZRange bc 0 64; KZRange off 8 (2^32); KZRange (len - off) 8 (2^32)].
      all: x42_norm.
      all: x42_post bc.
      all: x42_w4_fin IH mb S len bs pe dl sh.
    - x42_w4_go S len j pe sh [0x25ca0; 0x2965c]
        [KZRange (pe - j) 0 1; KZRange (dcap - j) 0 (2^32); KZRange bc 0 64; KZRange off 8 (2^32); KZRange (len - off) 8 (2^32)].
      all: x42_norm.
      all: kx_mem.
      all: eapply (x42_rl4 mb); try eassumption; try lia.
      all: intros mm' c' y11 y12 y13 y14 y15 y16 MU' WM' MI' OUT' DTB' FA' BD' SB'.
      all: assert (TBL' : tbl_in_log usegs mm' DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB').
      all: x42_w4_go S len j pe sh [0x28e94; 0x29000; 0x29058; 0x2965c]
        [KZRange (pe - j) 0 1; KZRange (dcap - j) 0 (2^32); KZRange bc 0 64; KZRange off 8 (2^32); KZRange (len - off) 8 (2^32)].
      all: x42_norm.
      all: x42_post bc.
      all: x42_w4_fin IH mb S len bs pe dl sh.
  Qed.

End DX42_4B.
