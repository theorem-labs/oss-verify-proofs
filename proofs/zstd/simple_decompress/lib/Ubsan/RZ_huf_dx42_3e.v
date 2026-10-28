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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_3a RZ_huf_dx42_3b RZ_huf_dx42_3c RZ_huf_dx42_3d.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2 KXSx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_dx42_0b huf41_kit_reload.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_3E.
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
  Notation WD3 := [(DST, DST + dcap); (SPV - 736, SPV - 696)].
  Notation BD3 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -736) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).

  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).
  Notation x42_la3 := (RZ_huf_dx42_3a.x42_la3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_t3 := (RZ_huf_dx42_3a.x42_t3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_w3 := (RZ_huf_dx42_3b.x42_w3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_c3 := (RZ_huf_dx42_3c.x42_c3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_p3 := (RZ_huf_dx42_3d.x42_p3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).

  Ltac x3e_sxh :=
    repeat match goal with
    | KXA : atoms_ok ?zs ?E, H0 : context [bv_unsigned (edenot ?E ?e)] |- _ =>
        kx_sx_has e;
        let nz := kx_len zs in
        let z := kx_ez2 E zs nz e in
        let P := kx_sxc E zs nz e in
        let H := fresh "KXSX" in
        assert (H : bv_unsigned (edenot E e) = z);
        [ refine (ez2_sound_u zs E e KXA (_ : P) (_ : 0 <= z < 2^64)); [ repeat split; Lia.lia | Lia.lia ]
        | rewrite !H in *; clear H ]
    end.

  Ltac x3e_fin mb e pe S len bs dl K :=
    lazymatch goal with
    | BD' : rw_cells _ ?m2 (SPV + -736) [C8 ?C; C4 (Z_to_bv 64 ?B); CB 4 ?pad; C8 (Z_to_bv 64 ?X); C8 _; C8 _]
      |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x2854c) _ _ _ _) =>
        try kx_read_ranges; try x3e_sxh;
        replace (Z_to_bv 64 P) with (Z_to_bv 64 (DST + (P - DST))) by (f_equal; lia);
        eapply (x42_c3 mb m2 (P - DST) e pe X S len bs dl B C pad);
        first [ eassumption | exact K | lia | intro; unfold RZ_huf_dx41.SINV in *; lia ]
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x28740) _ _ ?m2 _) =>
        replace (Z_to_bv 64 P) with (Z_to_bv 64 (DST + (P - DST))) by (f_equal; lia);
        eapply (x42_la3 mb m2 (P - DST) e pe dl); first [eassumption | exact K | lia]
    end.

  Lemma x42_q3b : forall mb mm j e pe pt S len bs dl sh bc (c0 : word) pad
      (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    munch WD3 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD3 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 pt) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    0 <= j <= e -> e <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl -> SINV (pt - S) len bc -> 0 <= bc <= 64 ->
    (forall mm' j' bc' (c' y1 y5 y7 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 : word),
        munch WD3 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD3 mm' c' (Z_to_bv 64 bc') pad (Z_to_bv 64 pt) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        bytes_at usegs mm' S bs -> j < j' <= e -> SINV (pt - S) len bc' -> 0 <= bc' <= 64 ->
        evt usegs POST (ST 0x2825c mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 (Z_to_bv 64 64) (Z_to_bv 64 (DST + e - 7)) (Z_to_bv 64 bc') y11 y12 y13 y14 y15 y16 y17
                          x18 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DST + e)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) y24
                          (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) y28 y29 y30 (Z_to_bv 64 (DST + pe)))) ->
    (forall mm' (y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y28 y29 y30 c' b' p' : word),
        munch WD3 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x287cc mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 (2^61)) y20 y21 y22 y23 y24
                          (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) y28 y29 y30 (Z_to_bv 64 (DST + pe)))) ->
    evt usegs POST (ST 0x28354 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 (Z_to_bv 64 64) (Z_to_bv 64 (DST + e - 7)) x10 x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + e)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) x24
                      (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe pt S len bs dl sh bc c0 pad x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK SPM HJ HE HDL HSH HS HB KH K.
    assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    destruct (Z_le_gt_dec (j + 8) e) as [RM|RM];
    [ kx_autoLx [0x2825c; 0x2854c; 0x28740; 0x2965c] 160%nat
        [KZRange (e - j) 8 (2^32); KZRange (dcap - j) 8 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange bc 0 64;
         KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange SPV 4096 (2^47); KZRange S 4096 (2^47);
         KZWr DST dcap; KZWr (SPV - 736) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 912) 296; KZDisj (SPV - 912) 296 DT 16388;
         KZTblLog DT sh 4 7 1 2]
        [(DT, 16388); (SPV - 912, 136); (SPV - 736, 40)]
    | kx_autoLx [0x2825c; 0x2854c; 0x28740; 0x2965c] 20%nat
        [KZRange (e - j) 0 7; KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47)]
        [(SPV - 912, 136); (SPV - 736, 40)] ].
    all: kx_ev_ranges.
    all: x3_uim.
    all: kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: kx_sx.
    all: lazymatch goal with
         | BD' : rw_cells _ ?m2 (SPV + -736) [C8 ?C; C4 (Z_to_bv 64 ?B); CB 4 _; C8 _; C8 _; C8 _]
           |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x2825c) _ _ _ _) =>
             replace (Z_to_bv 64 P) with (Z_to_bv 64 (DST + (P - DST))) by (f_equal; lia);
             eapply (KH m2 (P - DST) B C); first [eassumption | solve [unfold RZ_huf_dx41.SINV in *; lia] | lia]
         | |- _ => x3e_fin mb e pe S len bs dl K
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_q3 : forall (k : nat) mb mm j e pe pt S len bs dl sh bc (c0 : word) pad
      (x1 x5 x7 x11 x12 x13 x14 x15 x16 x17 x18 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    munch WD3 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD3 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 pt) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    e - j <= Z.of_nat k -> 0 <= j <= e -> e <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl -> SINV (pt - S) len bc -> 0 <= bc <= 64 ->
    (forall mm' (y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y28 y29 y30 c' b' p' : word),
        munch WD3 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x287cc mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 (2^61)) y20 y21 y22 y23 y24
                          (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) y28 y29 y30 (Z_to_bv 64 (DST + pe)))) ->
    evt usegs POST (ST 0x2825c mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 (Z_to_bv 64 64) (Z_to_bv 64 (DST + e - 7)) (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + e)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) x24
                      (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j e pe pt S len bs dl sh bc c0 pad x1 x5 x7 x11 x12 x13 x14 x15 x16 x17 x18 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK SPM HK HJ HE HDL HSH HS HB K.
    all: destruct HS as [HO | (O1 & O2 & B1)];
      [assert (EP : pt = S) by lia; subst pt; destruct (Z_le_gt_dec (j + 2) e) as [RM|RM]
      | remember (pt - S) as off eqn:EOFF; assert (EPT : pt = S + off) by lia; subst pt; clear EOFF;
        destruct (Z_lt_le_dec off 8) as [O8|O8]].
    all: lazymatch goal with
         | RM : _ + 2 <= _ |- _ =>
             kx_autoLx [0x28354; 0x25ca0; 0x2854c; 0x28740; 0x2965c] 20%nat
               [KZRange (e - j) 2 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47);
                KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(SPV - 912, 136); (SPV - 736, 40)]
         | RM : _ + 2 > _ |- _ =>
             kx_autoLx [0x28354; 0x25ca0; 0x2854c; 0x28740; 0x2965c] 20%nat
               [KZRange (e - j) 0 1; KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47);
                KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(SPV - 912, 136); (SPV - 736, 40)]
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x28354; 0x25ca0; 0x2854c; 0x28740; 0x2965c] 120%nat
               [KZRange off 1 7; KZRange (len - off) 8 (2^32); KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47);
                KZWr (SPV - 736) 40; KZDisj (SPV - 736) 40 S len; KZDisj (SPV - 912) 296 S len]
               [(S, len); (SPV - 912, 136); (SPV - 736, 40)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x28354; 0x25ca0; 0x2854c; 0x28740; 0x2965c] 20%nat
               [KZRange off 8 (2^32); KZRange (len - off) 8 (2^32); KZRange bc 0 64; KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47);
                KZRange SPV 4096 (2^47)]
               [(SPV - 912, 136); (SPV - 736, 40)]
         end.
    all: kx_ev_ranges.
    all: x3_uim.
    all: try x3_call SPV.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x28350) _ _ _ _) =>
             kx_autoLx [0x28354] 4%nat [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47)] [(SPV - 912, 136)];
             kx_ev_ranges
         | |- _ => idtac
         end.
    all: kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with
         | BD' : rw_cells _ ?m2 (SPV + -736) [C8 ?C; C4 (Z_to_bv 64 ?B); CB 4 _; C8 (Z_to_bv 64 ?X); C8 _; C8 _]
           |- evt _ _ (MS _ _ (Z_to_bv 64 0x28354) _ _ _ _) =>
             eapply (x42_q3b mb m2 j e pe X S len bs dl sh B C pad);
             first [ eassumption | exact K | solve [unfold RZ_huf_dx41.SINV in *; lia] | lia
                   | intros; first [ solve [exfalso; lia] | eapply IH; first [eassumption | solve [unfold RZ_huf_dx41.SINV in *; lia] | lia] ] ]
         | |- _ => x3e_fin mb e pe S len bs dl K
         end.
  Qed.

End DX42_3E.
