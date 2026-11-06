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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2 RZ_huf_dx42_20 RZ_huf_dx42_21a RZ_huf_dx42_21b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_21C.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis TL11 : tl = 11.

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
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Notation x42_tblf := (RZ_huf_dx42_20.x42_tblf DT dtb tl X2OK TL11).
  Notation x42_la5 := (RZ_huf_dx42_21a.x42_la5 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11).
  Notation x42_t5 := (RZ_huf_dx42_21a.x42_t5 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11).
  Notation x42_w5 := (RZ_huf_dx42_21b.x42_w5 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11).

  (* [comment removed for export] *)
  Lemma x42_c5 : forall mb mm j pe S len bs bc A0
      (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x29 x30 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    0 <= j <= pe -> j + 2 <= pe -> pe <= dcap -> 0 <= bc < 2^31 ->
    (bc <= 64 -> exists off, A0 = S + off /\ SINV off len bc) ->
    (forall mm' (y9 y11 y12 y13 y18 y19 y20 y24 y25 y26 y27 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x1f4fc mm' x1 x5 x6 x7 x8 y9 (Z_to_bv 64 (DT + 4)) y11 y12 y13 x14 x15 x16 x17 y18 y19 y20 x21 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) y24 y25 y26 y27 (Z_to_bv 64 64) x29 x30 (Z_to_bv 64 (DST + pe)))) ->
    evt psegs POST (ST 0x1f3c4 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 A0) (Z_to_bv 64 bc) x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j)) x19 x20 x21 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) x24 x25 x26 x27 (Z_to_bv 64 64) x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe S len bs bc A0 x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x29 x30 MU WM MI OUT DTB SB SL S0 S1 SL32 DJS HJ HRM HPE HB HP K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct (HP B64) as (off & -> & HO)|].
    all: lazymatch goal with
         | B64 : _ <= 64 |- _ =>
             kx_auto [0x1f3cc; 0x1f4a8; 0x1f4dc] 40%nat
               [KZRange (pe - j) 2 (2^32); KZRange bc 0 64; KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
               (@nil (Z * Z))
         | _ =>
             kx_auto [0x1f3cc; 0x1f4a8; 0x1f4dc] 40%nat
               [KZRange (pe - j) 2 (2^32); KZRange bc 65 (2^31 - 1); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
               (@nil (Z * Z))
         end.
    all: try replace (DST + pe + -2) with (DST + pe - 2) by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 128220) _ _ _ _) =>
             eapply (x42_la5 mb mm j pe); try eassumption; try lia; intros mm'; intros; eapply (K mm'); eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 127948) _ _ _ _) =>
             eapply (x42_w5 (Z.to_nat dcap) mb mm j pe off S len bs bc); try eassumption; try lia; intros mm'; intros; eapply (K mm'); eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 128168) _ _ _ _) =>
             eapply (x42_t5 (Z.to_nat dcap) mb mm j pe); try eassumption; try lia; intros mm'; intros; eapply (K mm'); eassumption
         end.
  Qed.

End DX42_21C.
