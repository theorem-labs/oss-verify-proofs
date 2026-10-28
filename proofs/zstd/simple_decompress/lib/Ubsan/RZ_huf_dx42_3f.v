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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_3a RZ_huf_dx42_3b RZ_huf_dx42_3c RZ_huf_dx42_3d RZ_huf_dx42_3e.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2 KXSx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_dx42_0b huf41_kit_reload.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_3F.
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
  Notation x42_q3 := (RZ_huf_dx42_3e.x42_q3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).

  Ltac x3f_fin mb e pe S len bs dl K :=
    lazymatch goal with
    | BD' : rw_cells _ ?m2 (SPV + -736) [C8 ?C; C4 (Z_to_bv 64 ?B); CB 4 ?pad; C8 (Z_to_bv 64 ?X); C8 _; C8 _]
      |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x2854c) _ _ _ _) =>
        replace (Z_to_bv 64 P) with (Z_to_bv 64 (DST + (P - DST))) by (f_equal; lia);
        eapply (x42_c3 mb m2 (P - DST) e pe X S len bs dl B C pad);
        first [ eassumption | exact K | lia | intro; unfold RZ_huf_dx41.SINV in *; lia ]
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x28740) _ _ ?m2 _) =>
        replace (Z_to_bv 64 P) with (Z_to_bv 64 (DST + (P - DST))) by (f_equal; lia);
        eapply (x42_la3 mb m2 (P - DST) e pe dl); first [eassumption | exact K | lia]
    end.

  (* [comment removed for export] *)
  Lemma x42_s3 : forall mb mm j e pe pt S len bs dl bc (c0 : word) pad
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x27 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    munch WD3 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD3 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 pt) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    0 <= j <= e -> e <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 -> (bc <= 64 -> SINV (pt - S) len bc) ->
    (forall mm' (y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y28 y29 y30 c' b' p' : word),
        munch WD3 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x287cc mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 (2^61)) y20 y21 y22 y23 y24
                          (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) y28 y29 y30 (Z_to_bv 64 (DST + pe)))) ->
    evt usegs POST (ST 0x28130 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j))
                      (Z_to_bv 64 (DST + e)) x22 x23 x24 (Z_to_bv 64 dl) x26 x27 x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe pt S len bs dl bc c0 pad x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x27 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK SPM HJ HE HDL HB HS K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64];
      [destruct (HS B64) as [HO | (O1 & O2 & B1)]; [assert (EP : pt = S) by lia; subst pt
      |remember (pt - S) as off eqn:EOFF; assert (EPT : pt = S + off) by lia; subst pt; clear EOFF; destruct (Z_lt_le_dec off 8) as [O8|O8]]|].
    all: destruct (Z_le_gt_dec (j + 2) e) as [RM|RM].
    all: let R := lazymatch goal with RM : ?J + 2 <= ?E |- _ => constr:(KZRange (E - J) 2 (2^32)) | RM : ?J + 2 > ?E |- _ => constr:(KZRange (E - J) 0 1) end in
         lazymatch goal with
         | B64 : _ > 64 |- _ =>
             kx_autoLx [0x2854c; 0x28740; 0x25ca0; 0x2965c] 20%nat
               [R; KZRange bc 65 (2^31 - 1); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange S 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 736) 40]
               [(SPV - 912, 136); (SPV - 736, 40)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x2854c; 0x28740; 0x25ca0; 0x2965c] 20%nat
               [R; KZRange (len - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32);
                KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(SPV - 912, 136); (SPV - 736, 40)]
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x2854c; 0x28740; 0x25ca0; 0x2965c] 120%nat
               [R; KZRange (len - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32);
                KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47);
                KZWr (SPV - 736) 40; KZDisj (SPV - 736) 40 S len; KZDisj (SPV - 912) 296 S len]
               [(S, len); (SPV - 912, 136); (SPV - 736, 40)]
         | _ =>
             kx_autoLx [0x2854c; 0x28740; 0x25ca0; 0x2965c] 20%nat
               [R; KZRange bc 0 64; KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(SPV - 912, 136); (SPV - 736, 40)]
         end.
    all: kx_ev_ranges.
    all: x3_uim.
    all: try x3_call SPV.
    all: let R := lazymatch goal with RM : ?J + 2 <= ?E |- _ => constr:(KZRange (E - J) 2 (2^32)) | RM : ?J + 2 > ?E |- _ => constr:(KZRange (E - J) 0 1) end in
         lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2850c) _ _ _ _) =>
             kx_autoLx [0x2854c; 0x28740] 10%nat [R; KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47);
                                                KZRange DT 4096 (2^47)] [(SPV - 912, 136)];
             kx_ev_ranges
         | |- _ => idtac
         end.
    all: kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: x3f_fin mb e pe S len bs dl K.
  Qed.

  Ltac x42_d3_k K mb :=
    intros mm' D7; intros;
    lazymatch goal with
    | MU2 : munch _ mb ?m2, WM2 : wmono _ mb ?m2, MU' : munch _ ?m2 mm', WM' : wmono _ ?m2 mm' |- _ =>
        eapply (K mm' D7);
        [ eapply munch_trans; [exact MU2|]; eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros; lia
        | exact (wmono_trans usegs mb m2 mm' WM2 WM') | eassumption | eassumption | eassumption | eassumption | first [reflexivity | lia] ]
    end.

  (* [comment removed for export] *)
  Lemma x42_d3 : forall mb mm j e pe off S len bs dl bc (c0 : word) pad
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x26 x27 x28 x29 x30 : word)
      (w0 w1 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    munch WD3 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 (Z_to_bv 64 (DST + e)) w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD3 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    0 <= j <= e -> e <= dcap -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 -> (bc <= 64 -> SINV off len bc) ->
    (forall mm' (y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y28 y29 y30 c' b' p' : word),
        munch WD3 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 (Z_to_bv 64 (DST + e)) w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x287cc mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 (2^61)) y20 y21 y22 y23 y24 (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) y28 y29 y30 (Z_to_bv 64 (DST + pe)))) ->
    evt usegs POST (ST 0x27de4 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j)) x21 x22 x23 x24 (Z_to_bv 64 dl) x26 x27 x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe off S len bs dl bc c0 pad x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x26 x27 x28 x29 x30
      w0 w1 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJT DJK SPM HJ HE HPE HDL HB HS K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [specialize (HS B64)|].
    all: destruct (Z_lt_le_dec (e - j) 8) as [SH|LG]; [|destruct (Z_le_gt_dec 12 tl) as [T12|T11]].
    all: let RB := lazymatch goal with B64 : ?B <= 64 |- _ => constr:(KZRange B 0 64) | B64 : ?B > 64 |- _ => constr:(KZRange B 65 (2^31 - 1)) end in
         let RE := lazymatch goal with SH : ?X < 8 |- _ => constr:(KZRange X 0 7) | LG : 8 <= ?X |- _ => constr:(KZRange X 8 (2^32)) end in
         let RT := lazymatch goal with
                   | T12 : 12 <= ?T |- _ => constr:(KZRange T 12 12)
                   | T11 : 12 > ?T |- _ => constr:(KZRange T 1 11)
                   | _ => constr:(KZRange tl 1 12)
                   end in
         kx_autoLx [0x28130; 0x27e28; 0x2825c; 0x2854c; 0x28740; 0x2965c] 40%nat
           [RB; RE; RT; KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47);
            KZRange dl 0 65535; KZRange SPV 4096 (2^47); KZRange S 4096 (2^47); KZWr (SPV - 736) 40; KZDisj DST dcap (SPV - 736) 40;
            KZDisj (SPV - 912) 136 (SPV - 736) 40]
           [(SPV - 912, 136); (SPV - 736, 40)].
    all: subst dl; rewrite ?(neg_dl_sh tl rsv TL) in *.
    all: kx_ev_ranges.
    all: x3_uim.
    all: kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: kx_sx.
    all: try replace (DST + e + -9) with (DST + e - 9) in * by lia; try replace (DST + e + -7) with (DST + e - 7) in * by lia.
    all: try replace (Z_to_bv 64 12) with (Z_to_bv 64 tl) by (f_equal; lia).
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x28130) _ _ ?m2 _) =>
             eapply (x42_s3 mb m2 j e pe (S + off) S len bs (tl + 256 * rsv) bc c0 pad);
             first [eassumption | exact K | lia | intro; unfold RZ_huf_dx41.SINV in *; lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x27e28) _ _ ?m2 _) =>
             eapply (x42_p3 (Z.to_nat (e - j)) mb m2 j e pe (S + off) S len bs (tl + 256 * rsv) (64 - tl) bc c0 pad);
             first [eassumption | exact K | solve [unfold RZ_huf_dx41.SINV in *; lia] | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2825c) _ _ ?m2 _) =>
             eapply (x42_q3 (Z.to_nat (e - j)) mb m2 j e pe (S + off) S len bs (tl + 256 * rsv) (64 - tl) bc c0 pad);
             first [eassumption | exact K | solve [unfold RZ_huf_dx41.SINV in *; lia] | lia]
         | |- _ => x3f_fin mb e pe S len bs (tl + 256 * rsv) K
         end.
  Qed.

End DX42_3F.
