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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_1a RZ_huf_dx42_1b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2 KXSx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_dx42_0b huf41_kit_reload.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_1C.
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
  Notation WD1 := [(DST, DST + dcap); (SPV - 800, SPV - 792); (SPV - 656, SPV - 616)].
  Notation BD1 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -656) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation KD1 mb e pe dl pad st w0 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w13 x18 x20 x26 x27 :=
    (forall mm' (y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y23 y24 y28 y29 y30 c' b' p' : word),
        munch WD1 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 (Z_to_bv 64 dl) w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 (DST + e)) w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD1 mm' c' b' pad p' (Z_to_bv 64 st) (Z_to_bv 64 (st + 8)) ->
        evt usegs POST (ST 0x273a4 mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 (2^61)) x20 y21 y22 y23 y24 (Z_to_bv 64 dl) x26 x27 y28 y29 y30 (Z_to_bv 64 (DST + pe)))).

  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).
  Notation x42_la1 := (RZ_huf_dx42_1a.x42_la1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_t1 := (RZ_huf_dx42_1a.x42_t1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_w1 := (RZ_huf_dx42_1b.x42_w1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).

  (* [comment removed for export] *)
  Lemma x42_c1 : forall mb mm j e pe P S len bs dl bc (c0 : word) pad
      (x1 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x26 x27 x28 x29 x30 : word)
      (w0 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w13 : word),
    munch WD1 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 (Z_to_bv 64 dl) w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 (DST + e)) w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD1 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> SPV mod 16 = 0 ->
    0 <= j <= e -> e <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 ->
    (bc <= 64 -> exists off, P = S + off /\ SINV off len bc) ->
    KD1 mb e pe dl pad S w0 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w13 x18 x20 x26 x27 ->
    evt usegs POST (ST 0x270f0 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 (Z_to_bv 64 (DST + j)) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (2^61)) x20 x21 (Z_to_bv 64 (DST + e)) x23 x24 (Z_to_bv 64 dl) x26 x27 x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe P S len bs dl bc c0 pad x1 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x26 x27 x28 x29 x30
      w0 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w13 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK SPM HJ HED HDL HB HP K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct (HP B64) as (off & -> & HO)|].
    all: lazymatch goal with
         | B64 : _ <= 64 |- _ =>
             kx_autoLx [0x27118; 0x272a4; 0x27308; 0x2965c] 30%nat
               [KZRange bc 0 64; KZRange (e - j) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange DT 4096 (2^47); KZRange dl 0 65535; KZRange SPV 4096 (2^47)]
               [(SPV - 912, 136); (SPV - 656, 40)]
         | _ =>
             kx_autoLx [0x27118; 0x272a4; 0x27308; 0x2965c] 30%nat
               [KZRange bc 65 (2^31 - 1); KZRange (e - j) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange DT 4096 (2^47); KZRange dl 0 65535; KZRange SPV 4096 (2^47); KZWr (SPV - 656) 40; KZDisj DST dcap (SPV - 656) 40;
                KZDisj (SPV - 912) 136 (SPV - 656) 40]
               [(SPV - 912, 136); (SPV - 656, 40)]
         end.
    all: subst dl; rewrite ?(neg_dl_sh tl rsv TL) in *.
    all: kx_ev_ranges.
    all: x1_uim.
    all: kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: kx_sx.
    all: try replace (DST + e + -2) with (DST + e - 2) in * by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x27118) _ _ ?m2 _) =>
             eapply (x42_w1 (Z.to_nat (e - j)) mb m2 j e pe off S len bs (tl + 256 * rsv) (64 - tl) (-1 * DT + -5) bc); first [eassumption | exact K | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x272a4) _ _ ?m2 _) =>
             eapply (x42_t1 (Z.to_nat (e - j)) mb m2 j e pe (tl + 256 * rsv) (64 - tl) (-1 * DT + -5) S); first [eassumption | exact K | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x27308) _ _ ?m2 _) =>
             eapply (x42_la1 mb m2 j e pe (tl + 256 * rsv) S); first [eassumption | exact K | lia]
         end.
  Qed.

End DX42_1C.
