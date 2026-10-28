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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_2a RZ_huf_dx42_2b RZ_huf_dx42_2c RZ_huf_dx42_2d RZ_huf_dx42_2e.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf41_kit_reload huf42_2_t2kit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_2F.
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
  Notation x42_c2 := (RZ_huf_dx42_2c.x42_c2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_p2 := (RZ_huf_dx42_2d.x42_p2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_q2 := (RZ_huf_dx42_2e.x42_q2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).

  Ltac s2_walk S len j e bc off BLO BHI OLO OHI :=
    kx_autoLx [0x27b38; 0x27d48; 0x2965c; 0x25ca0] 60%nat
      [KZRange bc BLO BHI; KZRange off OLO OHI; KZRange (e - j) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange (len - off) 8 (2^32);
       KZRange len 9 (2^32); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange dcap 0 (2^32); KZRange DT 4096 (2^47);
       KZWr (SPV - 696) 40; KZDisj (SPV - 696) 40 S len; KZDisj (SPV - 696) 40 DT 16388; KZDisj DST dcap (SPV - 696) 40]
      [(S, len); (SPV - 912, 136); (SPV - 696, 40)].

  (* [comment removed for export] *)
  Lemma x42_s2 : forall mb mm j e pe off S len bs dl bc (c0 : word) pad
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
    munch WD2 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    0 <= j <= e -> e <= dcap -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 -> (bc <= 64 -> SINV off len bc) ->
    K2 mb e pe dl S pad x5 x7 x18 x20 x21 x26 x28 x29 x30 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ->
    evt usegs POST (ST 0x27704 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) x20 x21 x22 x23 x24 (Z_to_bv 64 dl) x26 (Z_to_bv 64 (DST + j)) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    pose proof huf_reload_proof as HRL. unfold huf_reload_stmt, huf_reload_stmt_at, bitd_cells in HRL.
    intros mb mm j e pe off S len bs dl bc c0 pad x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJT DJK SPA HJ HE HPE HDL HB HS K.
    assert (BDA : (SPV + -696) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct (HS B64) as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]]|].
    all: lazymatch goal with
         | O8 : 8 <= _ |- _ =>
             s2_walk S len j e bc off 0 64 8 (2^32)
         | O8 : _ < 8 |- _ =>
             assert (QC : 0 <= bc <= 7 \/ 8 <= bc <= 15 \/ 16 <= bc <= 23 \/ 24 <= bc <= 31 \/ 32 <= bc <= 39 \/ 40 <= bc <= 47 \/ 48 <= bc <= 55 \/ 56 <= bc <= 63 \/ 64 <= bc <= 64) by lia;
             destruct QC as [QC|[QC|[QC|[QC|[QC|[QC|[QC|[QC|QC]]]]]]]];
               [ s2_walk S len j e bc off 0 7 1 7
               | s2_walk S len j e bc off 8 15 1 7
               | destruct (Z_lt_le_dec off 2) as [OQ|OQ]; [s2_walk S len j e bc off 16 23 1 1 | s2_walk S len j e bc off 16 23 2 7]
               | destruct (Z_lt_le_dec off 3) as [OQ|OQ]; [s2_walk S len j e bc off 24 31 1 2 | s2_walk S len j e bc off 24 31 3 7]
               | destruct (Z_lt_le_dec off 4) as [OQ|OQ]; [s2_walk S len j e bc off 32 39 1 3 | s2_walk S len j e bc off 32 39 4 7]
               | destruct (Z_lt_le_dec off 5) as [OQ|OQ]; [s2_walk S len j e bc off 40 47 1 4 | s2_walk S len j e bc off 40 47 5 7]
               | destruct (Z_lt_le_dec off 6) as [OQ|OQ]; [s2_walk S len j e bc off 48 55 1 5 | s2_walk S len j e bc off 48 55 6 7]
               | destruct (Z_lt_le_dec off 7) as [OQ|OQ]; [s2_walk S len j e bc off 56 63 1 6 | s2_walk S len j e bc off 56 63 7 7]
               | s2_walk S len j e bc off 64 64 1 7
               ]
         | B64 : _ <= 64 |- _ =>
             kx_autoLx [0x27b38; 0x27d48; 0x2965c] 40%nat
               [KZRange bc 0 64; KZRange (e - j) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47);
                KZRange SPV 4096 (2^47)] [(SPV - 912, 136); (SPV - 696, 40)]
         | _ =>
             kx_autoLx [0x27b38; 0x27d48; 0x2965c] 40%nat
               [KZRange bc 65 (2^31 - 1); KZRange (e - j) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47);
                KZRange S 4096 (2^47); KZRange SPV 4096 (2^47); KZRange dcap 0 (2^32);
                KZWr (SPV - 696) 40; KZDisj (SPV - 696) 40 DT 16388; KZDisj DST dcap (SPV - 696) 40; KZDisj (SPV - 696) 40 S len]
               [(SPV - 912, 136); (SPV - 696, 40)]
         end.
    all: t2side.
    all: t2ck.
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
             kx_autoLx [0x27b38; 0x27d48; 0x2965c] 40%nat
               [KZRange b3 0 7; KZRange o3 0 (2^32); KZRange (e - j) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47);
                KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)] [(SPV - 912, 136); (SPV - 696, 40)];
             t2side; t2ck
         | _ => idtac
         end.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27b38) _ _ ?m2 _) =>
             lazymatch goal with H : rw_cells usegs m2 (SPV + -696) [_; C4 (Z_to_bv 64 ?B); _; C8 (Z_to_bv 64 ?X); _; _] |- _ =>
               eapply (x42_c2 mb m2 J e pe S len bs dl B X); try eassumption; try lia;
               try (intros; exists (X - S); split; [lia | unfold RZ_huf_dx41.SINV; lia])
             end
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27d48) _ _ ?m2 _) =>
             eapply (x42_la2 mb m2 J e pe dl S pad); try eassumption; try lia
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_d2 : forall mb mm j e pe off S len bs dl bc (c0 : word) pad
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
    munch WD2 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    0 <= j <= e -> e <= dcap -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 -> (bc <= 64 -> SINV off len bc) ->
    (forall mm' (y1 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y24 y27 c' b' p' : word),
        munch WD2 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD2 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x27de4 mm' y1 x5 (Z_to_bv 64 (DT + 4)) x7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                          x18 (Z_to_bv 64 (2^61)) x20 x21 y22 y23 y24 (Z_to_bv 64 dl) x26 y27 x28 x29 x30 (Z_to_bv 64 (DST + pe)))) ->
    evt usegs POST (ST 0x273a4 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                      x18 (Z_to_bv 64 (2^61)) x20 x21 x22 x23 x24 (Z_to_bv 64 dl) x26 (Z_to_bv 64 (DST + j)) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe off S len bs dl bc c0 pad x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJT DJK SPA HJ HE HPE HDL HB HS K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64].
    all: lazymatch goal with
         | B64 : _ <= 64 |- _ =>
             kx_autoLx [0x273f8; 0x27704; 0x27838; 0x27b38; 0x27d48; 0x2965c] 40%nat
               [KZRange bc 0 64; KZRange (e - j) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange dl 0 65292; KZRange SPV 4096 (2^47); KZRange S 4096 (2^47); KZRange DT 4096 (2^47);
                KZWr (SPV - 696) 40; KZDisj (SPV - 696) 40 DT 16388; KZDisj DST dcap (SPV - 696) 40; KZDisj (SPV - 696) 40 S len]
               [(SPV - 912, 136); (SPV - 696, 40)]
         | _ =>
             kx_autoLx [0x273f8; 0x27704; 0x27838; 0x27b38; 0x27d48; 0x2965c] 40%nat
               [KZRange bc 65 (2^31 - 1); KZRange (e - j) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange dl 0 65292; KZRange SPV 4096 (2^47); KZRange S 4096 (2^47); KZRange DT 4096 (2^47);
                KZWr (SPV - 696) 40; KZDisj (SPV - 696) 40 DT 16388; KZDisj DST dcap (SPV - 696) 40; KZDisj (SPV - 696) 40 S len]
               [(SPV - 912, 136); (SPV - 696, 40)]
         end.
    all: t2side.
    all: t2ck.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: subst dl; rewrite ?(neg_dl_sh tl rsv TL).
    all: try replace (DST + e + -9) with (DST + e - 9) by lia.
    all: try replace (DST + e + -7) with (DST + e - 7) by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x273f8) _ _ ?m2 _) =>
             eapply (x42_p2 (Z.to_nat dcap) mb m2 j e pe off S len bs (tl + 256 * rsv) (64 - tl) bc c0 pad); try eassumption; try lia;
             try solve [destruct (HS B64) as [-> | ?]; unfold RZ_huf_dx41.SINV; lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x27838) _ _ ?m2 _) =>
             eapply (x42_q2 (Z.to_nat dcap) mb m2 j e pe off S len bs (tl + 256 * rsv) (64 - tl) bc c0 pad); try eassumption; try lia;
             try solve [destruct (HS B64) as [-> | ?]; unfold RZ_huf_dx41.SINV; lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x27704) _ _ ?m2 _) =>
             eapply (x42_s2 mb m2 j e pe off S len bs (tl + 256 * rsv) bc c0 pad); try eassumption; try lia
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27b38) _ _ ?m2 _) =>
             lazymatch goal with H : rw_cells usegs m2 (SPV + -696) [_; C4 (Z_to_bv 64 ?B); _; C8 (Z_to_bv 64 ?X); _; _] |- _ =>
               eapply (x42_c2 mb m2 J e pe S len bs (tl + 256 * rsv) B X); try eassumption; try lia;
               try (intros; exists (X - S); split; [lia | unfold RZ_huf_dx41.SINV; lia])
             end
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ _ _ _) _ (Z_to_bv 64 0x27d48) _ _ ?m2 _) =>
             eapply (x42_la2 mb m2 J e pe (tl + 256 * rsv) S pad); try eassumption; try lia
         end.
  Qed.

End DX42_2F.
