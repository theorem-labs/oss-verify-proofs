(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s32k AF_huf_w4s32k2 AF_huf_w4s32k3 AF_huf_w4s32z.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AFrameD.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).


Section CANSEC1. Context {rc : runConstT}.

Lemma w4s32_sub1 : forall lo hi A B, sub_fp [(A, B)] [(lo, hi); (A, B)].
Proof. intros lo hi A B x Hx. cbn [outside] in *. lia. Qed.


Lemma w4s32_lp : forall (n : nat) (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x9 x10 x12 x13 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  seg - q - i <= Z.of_nat n -> munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm0 mm -> wmono bsegs mm0 mm ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> (off = 0 /\ 1 <= len \/ 1 <= off /\ off + 8 <= len) -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (DST + seg + q)) x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 2 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (DST + 2 * seg)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b380) fc None mm (seg_rom bsegs)).
Proof.
  induction n as [|n IH]; intros until len; intros HN MU0 WM0; intros.
  all: destruct (Z.eq_dec off 0) as [HO0 | HO1];
       [ eapply w4s32_x2z with (mm := mm) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia
       | destruct (Z_le_gt_dec off 7) as [HS7 | HS7];
         [ destruct (Z_lt_le_dec (8 * off + 7) b) as [HT | HT];
           [ eapply w4s32_x2s with (mm := mm) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia
           | destruct (Z_lt_le_dec seg (q + i + 4)) as [HX | HX];
             [ eapply w4s32_x2s with (mm := mm) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia
             | try lia; eapply w4s32_l2s with (mm := mm) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia ] ]
         | destruct (Z_lt_le_dec seg (q + i + 4)) as [HX | HX];
           [ eapply w4s32_x2f with (mm := mm) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia
           | try lia; eapply w4s32_l2f with (mm := mm) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia ] ] ].
  all: intros mm' ob' c' b'; intros.
  all: first
       [ eapply w4s32_jsd with (mm0 := mm0) (mm := mm') (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia
       | try replace (S + off - b / 8) with (S + (off - b / 8)) in * by lia;
         eapply IH with (mm0 := mm0) (mm := mm') (off := off - b / 8) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3);
         try eassumption; try lia ].
  all: try (lazymatch goal with |- munch _ _ _ =>
       eapply munch_trans; [eassumption | eapply munch_weaken; [| eassumption];
         first [ apply w4s32_sub1 | apply w4s32_sub2; lia ] ] end).
  all: try (lazymatch goal with |- wmono _ _ _ => eapply wmono_trans; eassumption end).
  all: try (Z.div_mod_to_equations; lia).
Qed.








Lemma w4s32_e2k : forall (Q : machine_state -> Prop) (RNG : footprint) (mm mm1 : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp : word) (pad1 : list byte) (SP DST dcap seg q DT dl lo : Z),
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' -> stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))) ->
  munch [(SP + -144, SP + -104); (SP + -496, SP + -480)] mm mm1 -> wmono bsegs mm mm1 -> stk bsegs mm1 lo (SP + -480) -> DST + dcap <= lo ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104)] mm1 mm' -> wmono bsegs mm1 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))).
Proof.
  intros until lo. intros K0 MU0 WM0 STK HLO.
  intros mm' ob' cw' bw' pw' aw' ew'. intros.
  eapply K0; try eassumption.
  - eapply munch_trans;
      [ eapply munch_weaken; [ | exact MU0]; unfold sub_fp; intros; cbn [outside] in *; tauto
      | eapply munch_weaken; [ | eassumption]; unfold sub_fp; intros; cbn [outside] in *; tauto ].
  - eapply wmono_trans; [exact WM0 | eassumption].
  - eapply stk_transportD; [exact STK | eassumption | cbn [disjoint_from]; lia].
Qed.

Lemma w4s32_tsw : forall (Q : machine_state -> Prop) (RNG : footprint) (mm mm1 : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pw aw ew cw : word) (pad1 : list byte) (cbs ob : list byte)
    (SP DST dcap seg q DT dl b tl rsv lo : Z),
    (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' -> stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))) ->
  munch [(SP + -144, SP + -104); (SP + -496, SP + -480)] mm mm1 -> wmono bsegs mm mm1 -> mem_inv bsegs mm1 -> stk bsegs mm1 lo (SP + -480) -> DST + dcap <= lo -> lo <= SP + -496 ->
rw_cells bsegs mm1 (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm1 (SP + -144) [C8 cw; C4 (Z_to_bv 64 b); CB 4 pad1; C8 pw; C8 aw; C8 ew] ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A2 L2 A3 L3 : Z), A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A2 -> 0 <= A3 ->
  A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -480) 480 ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q < seg -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 0 <= b < 2^32 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q)) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b8c8) fc None mm1 (seg_rom bsegs)).
Proof.
  intros until lo. intros K0 MU1 WM1 MI1 STK HLO HLS FR1 C1. intros.
  rewrite <- (Z_to_bv_bv_unsigned cw) in C1.
  pose proof (bv_unsigned_in_range _ cw) as CR. unfold bv_modulus in CR. change (Z.of_N 64) with 64 in CR.
  pose proof (w4s32_e2k Q RNG mm mm1 F fc gp tp pad1 SP DST dcap seg q DT dl lo K0 MU1 WM1 STK HLO) as K2.
  replace (DST + seg + q) with (DST + seg + q + 0) by lia.
  eapply w4s32_tsd with (mm0 := mm1) (mm := mm1) (j := 0) (c := bv_unsigned cw) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3);
    try eassumption; try lia.
  all: try (lazymatch goal with |- munch _ ?m ?m => apply munch_refl end).
  all: try (lazymatch goal with |- wmono _ ?m ?m => apply wmono_refl end).
  all: try (lazymatch goal with |- bytes_at _ ?m _ _ =>
      eapply bytes_at_transport; [eassumption | eassumption | cbn [disjoint_from]; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- u8arr _ ?m _ _ =>
      eapply u8arr_transportD; [eassumption | eassumption | cbn [disjoint_from]; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- unpoisoned ?m ?lo ?hi =>
      eapply (unpoisoned_munch _ _ m lo hi); [eassumption | eassumption |
        cbn [disjoint_from]; unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; unfold KXGoM.apart in *; lia] end).
  all: try (lazymatch goal with |- ztab_fact _ ?m ?A ?N _ _ =>
      eapply (w4_ztab_munch _ m _ A N); [eassumption | eassumption | cbn [disjoint_from]; unfold KXGoM.apart in *; lia | lia | lia] end).
Qed.

Ltac w4s32_e2c KD m lo A2 L2 A3 L3 cbs ob tl rsv :=
  intros;
  first [ eapply KD
        | eapply w4s32_tsw with (mm := m) (lo := lo) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3) (cbs := cbs) (ob := ob)
            (tl := tl) (rsv := rsv); [exact KD | ..] ];
  try (lazymatch goal with |- munch _ ?m ?m => apply munch_refl end);
  try (lazymatch goal with |- wmono _ ?m ?m => apply wmono_refl end);
  try (lazymatch goal with |- munch _ _ _ =>
      eapply munch_weaken; [ | eassumption]; unfold sub_fp; intros; cbn [outside] in *; tauto end);
  try eassumption;
  try (lazymatch goal with |- stk _ _ _ _ => eapply stk_transportD; [eassumption | eassumption | cbn [disjoint_from]; lia] end);
  try (lazymatch goal with |- u8arr _ _ _ _ =>
      eapply u8arr_transportD; [eassumption | eassumption | cbn [disjoint_from]; unfold KXGoM.apart in *; lia] end);
  try lia.

Lemma w4s32_e2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 c : word) (pad1 : list byte)
    (bz : list Z) (cbs ob : list byte) (SP DST dcap seg q DT dl S pt b tl rsv len lo : Z),
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -144, SP + -104); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' -> stk bsegs mm' lo (SP + -480) ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -144) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + 2 * seg))
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8b994) fc None mm' (seg_rom bsegs))) ->
  Z.of_nat (length bz) = len -> (pt = 0 \/ 1 <= pt /\ pt + 8 <= len /\ b <= 64) ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -144) [C8 c; C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + pt)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S (map (Z_to_bv 8) bz) -> Forall (fun c => 0 <= c < 256) bz ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16 ->
  KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) ->
  DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q <= seg -> seg - q < 4 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 2^20 <= SP -> 4096 <= S -> S + len <= 2^47 -> len <= 2^32 -> 0 <= pt -> 0 <= b < 2^31 ->
  4096 <= DT <= 2^47 -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  SP mod 8 = 0 -> stk bsegs mm lo (SP + -480) -> ATOP + 4096 <= lo -> lo <= SP + -496 -> DST + dcap <= lo ->
  artcells mm -> ablk S (S + len) -> unpoisoned mm (SP + -144) (SP + -104) -> rng RNG (shad (SP + -144)) 5 ->
  rng RNG (shad S) (nshad (len + S mod 8)) -> rng RNG (SP + -496) 16 -> rng_aimg RNG -> rng_aimg_sh RNG ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + seg + q)) x9 (Z_to_bv 64 (4)) (Z_to_bv 64 (seg - q)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 (2147450880)) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31) F (Z_to_bv 64 571280) fc None mm (seg_rom bsegs)).
Proof.
  intros until lo. intros KD LBZ HPT. intros.
  assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bz)) = len) by (rewrite length_map; exact LBZ).
  destruct (Z_lt_le_dec 64 b) as [HB | HB].
  - eapply w4s32_e2a with (x10 := gp) (x11 := gp) (x18 := gp) (S := S) (pt := pt) (b := b) (tl := tl) (rsv := rsv); try eassumption; try lia.
    all: w4s32_e2c KD mm lo A2 L2 A3 L3 cbs ob tl rsv.
  - destruct (Z.eq_dec pt 0) as [HP | HP].
    + eapply w4s32_e2z with (x10 := gp) (x11 := gp) (x18 := gp) (S := S) (pt := pt) (b := b) (tl := tl) (rsv := rsv); try eassumption; try lia.
      all: w4s32_e2c KD mm lo A2 L2 A3 L3 cbs ob tl rsv.
    + destruct (Z_le_gt_dec pt 7) as [HP7 | HP7].
      * eapply w4s32_e2s with (x10 := gp) (x11 := gp) (x18 := gp) (S := S) (pt := pt) (b := b) (tl := tl) (rsv := rsv) (bs := map (Z_to_bv 8) bz) (len := len) (A1 := A1) (L1 := L1); try eassumption; try lia.
        all: w4s32_e2c KD mm lo A2 L2 A3 L3 cbs ob tl rsv.
      * eapply w4s32_e2r with (x10 := gp) (x11 := gp) (x18 := gp) (S := S) (pt := pt) (b := b) (tl := tl) (rsv := rsv) (bs := bz) (lo := lo); rewrite ?LBZ; try eassumption; try lia.
        all: w4s32_e2c KD mm lo A2 L2 A3 L3 cbs ob tl rsv.
Qed.

End CANSEC1.
