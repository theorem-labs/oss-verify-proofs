(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufX1.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m AF_huf_w4e.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3_iface AF_huf_w4s3_iface2 AF_huf_w4s3_iface3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b AF_huf_w4p AF_huf_w4s33z AF_huf_w4s33k AF_huf_w4s33c AF_huf_w4s33k2 AF_huf_w4s33k3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC0. Context {rc : runConstT}.
Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
Import KXS.

Lemma w4s33_l3s : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i + 4 <= seg -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 8 * off + 7 -> off + 8 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (y8 y10 y12 y13 y28 y29 y30 y31 : word),
     munch [(DST + 2 * seg + q + i, DST + 2 * seg + q + i + 4); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 (Z_to_bv 64 (S + off - b / 8)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
     bytes_at bsegs mm' S bs -> bytes_at bsegs mm' (DT + 4) cbs ->
     unpoisoned mm' S (S + len) -> unpoisoned mm' (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm' DST (DST + dcap) ->
     ztab_fact bsegs mm' (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] -> 0 <= c' < 2^64 -> 0 <= b' <= 64 ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) y8 x9 y10 (Z_to_bv 64 b') y12 y13
               (Z_to_bv 64 64) (Z_to_bv 64 (i + 4)) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x8b9d0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  intros until len.
  destruct (Z.eq_dec off 1) as [HO1|HO1]; [exact (w4s33_l3s1 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO1) |].
  destruct (Z.eq_dec off 2) as [HO2|HO2]; [exact (w4s33_l3s2 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO2) |].
  destruct (Z.eq_dec off 3) as [HO3|HO3]; [exact (w4s33_l3s3 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO3) |].
  destruct (Z.eq_dec off 4) as [HO4|HO4]; [exact (w4s33_l3s4 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO4) |].
  destruct (Z.eq_dec off 5) as [HO5|HO5]; [exact (w4s33_l3s5 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO5) |].
  destruct (Z.eq_dec off 6) as [HO6|HO6]; [exact (w4s33_l3s6 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO6) |].
  destruct (Z.eq_dec off 7) as [HO7|HO7]; [exact (w4s33_l3s7 Q RNG mm F fc gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob SP DST dcap seg q DT dl S off b c tl rsv i len HO7) |].
  intros. exfalso. lia.
Qed.

Lemma w4s33_l3 : forall (n : nat) (Q : machine_state -> Prop) (RNG : footprint) (mm0 mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  seg - q - i <= 4 * Z.of_nat n ->
  munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm0 mm -> wmono bsegs mm0 mm ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 0 <= off -> (off = 0 \/ off + 8 <= len) -> 1 <= len -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm0 mm' -> wmono bsegs mm0 mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad1; C8 pw'; C8 aw'; C8 ew'] ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23 (Z_to_bv 64 0x7fff8000) y25
               (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x8bff0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) x8 x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + 3 * seg - 3)) (Z_to_bv 64 (- DT - 5))
               x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) x23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8b9d0) fc None mm (seg_rom bsegs)).
Proof.
  induction n as [|n IH]; intros until len; intros HN MU0 WM0 CF CD; intros;
  (match goal with H : forall (_ : amem) (_ : list byte) (_ _ _ _ _ : word), _ |- _ => rename H into KD end);
  (destruct (Z.eq_dec off 0) as [HOZ|HOZ];
   [ eapply w4s33_x81b with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia; intros; eapply KD; try eassumption; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption]
   | destruct (Z_le_gt_dec 8 off) as [HO8|HO8];
     [ destruct (Z_lt_le_dec seg (q + i + 4)) as [HXE|HXE];
       [ eapply w4s33_x81a with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia; intros; eapply KD; try eassumption; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption]
       | ]
     | destruct (Z_le_gt_dec b (8 * off + 7)) as [HB|HB];
       [ destruct (Z_lt_le_dec seg (q + i + 4)) as [HXS|HXS];
         [ eapply w4s33_x3s with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia; intros; eapply KD; try eassumption; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption]
         | ]
       | eapply w4s33_x3e with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia; intros; eapply KD; try eassumption; [eapply munch_trans; eassumption | eapply wmono_trans; eassumption] ] ] ]).
  - lia.
  - lia.
  - eapply w4s33_l3f with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
    intros mm1 ob1 c1 b1 y10 y12 y13 y28 y29 y30 y31 MU1 WM1 MI1 U1 UL1 CF1 CD1. intros.
    replace (S + off - b / 8) with (S + (off - b / 8)) in CD1 by lia.
    assert (MU2 : munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm0 mm1).
    { eapply munch_trans; [exact MU0 | eapply munch_weaken; [ | exact MU1]].
      intros x Hx; cbn [outside] in *; lia. }
    pose proof (wmono_trans _ _ _ _ WM0 WM1) as WM2.
    eapply IH with (off := off - b / 8) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia; try (Z.div_mod_to_equations; lia).
  - eapply w4s33_l3s with (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia.
    intros mm1 ob1 c1 b1 y8 y10 y12 y13 y28 y29 y30 y31 MU1 WM1 MI1 U1 UL1 CF1 CD1. intros.
    replace (S + off - b / 8) with (S + (off - b / 8)) in CD1 by lia.
    assert (MU2 : munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm0 mm1).
    { eapply munch_trans; [exact MU0 | eapply munch_weaken; [ | exact MU1]].
      intros x Hx; cbn [outside] in *; lia. }
    pose proof (wmono_trans _ _ _ _ WM0 WM1) as WM2.
    eapply IH with (off := off - b / 8) (A1 := A1) (L1 := L1) (A2 := A2) (L2 := L2) (A3 := A3) (L3 := L3); try eassumption; try lia; try (Z.div_mod_to_equations; lia).
Qed.

End CANSEC0.

Section CANSEC1. Context {rc : runConstT}.
Section W4S33.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -496).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis DSTF : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : DT + DTL <= SS \/ SS + n <= DT.
  Hypothesis DJ2 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis DJ3 : DT + DTL <= DST \/ DST + dcap <= DT.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TPA : tp = Z_to_bv 64 ATP.
  Hypothesis HINV : harness_invA m0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WIS : rng_aimg_sh RNG.
  Hypothesis WFS : rng_fs L RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation WB l := (l AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src
                      cells cbs pdt SBL SBH rstk AH NFK ABL MTL TLM HDT TOK ECB LCB DSTF DC BYS NSM S16 SRCB DJ1 DJ2 DJ3
                      LOA LOS SPT SP16 TPA HINV RCL RLO RHI RRL RRS WSK WIM WIS WFS).

  Hypothesis CONT4 : w4s34_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl
                        tl lo src cbs.

  Lemma w4s33_proof : w4s33_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl
                        tl lo src cbs.
  Proof using All.
    unfold w4s33_goal.
    intros l1 l2 l3 q pt3 pt4 b3 b4 c1 bw1 p1 a1 e1 c2 bw2 p2 a2 e2 c3 c4 pad1 pad2 pad3 pad4 rest w0 w8 w16 w40 w48 w56 mm
           x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31
           HW HL1 HL2 HL3 HN D6 H3S TS3 TS4 HQ HQ2.
    pose proof (WB w4p_ctx mm _ _ _ _ _ (SS + 6 + l1 + l2) l3 HW D6 ltac:(lia) ltac:(lia) ltac:(lia))
      as ((bs & BS & BSL) & HCB & HCBL & P2 & (ob & OB & OBL) & U1 & U2 & U3 & R1 & R2 & R3 &
          (A1 & L1 & A2 & L2 & A3 & L3 & M1 & M2 & M3 & Z1 & Z2 & Z3 & I1 & I2 & I3 & I4 & I5 & I6 & RS1 & RS2 & RS3) &
          AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & AP7 & MI & RSP & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & ZT).
    pose proof HW as HW'. unfold W4F in HW'.
    destruct HW' as (_ & _ & _ & _ & ST & F0 & _ & _ & _ & _ & _ & K3 & _ & _ & _ & _ & _ & MU & WM).
    replace (SP + -480 + 296) with (SP + -184) in K3 by lia.
    unfold W4FRW in F0. cbv zeta in F0. unfold W4DS in K3.
    pose proof (w4e_sp AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (SPa & SPb & SPc & SPd).
    pose proof (w4e_blocks AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs pdt SBL SBH AH MTL TLM HDT LCB DSTF DC SRCB DJ2
      (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (w4e_d0 AI L RNG st LB sp m0 DST dcap SS DT mtl tl src cbs AH DSTF DC DJ2
      (ltac:(unfold KXGoM.apart; lia) : KXGoM.apart DST dcap DT DTL)) as (D1 & D2 & D3).
    pose proof (@ATOP_hi rc) as AT1. pose proof (@ATOP_lo rc) as AT2.
    pose proof TS3 as (TP0 & TPC & TB).
    assert (SG : 4 * seg <= dcap + 3 < 4 * seg + 4).
    { pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)). lia. }
    assert (EC : Z_to_bv 64 (bv_unsigned c3) = c3) by apply Z_to_bv_bv_unsigned.
    assert (CR : 0 <= bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range _ c3) as CR0; unfold bv_modulus in CR0; exact CR0).
    assert (SP8 : SP mod 8 = 0).
    { pose proof (Z.div_mod SP 16 ltac:(lia)) as E16. rewrite SP16 in E16. rewrite E16.
      replace (16 * (SP / 16) + 0) with ((2 * (SP / 16)) * 8) by lia. apply Z_mod_mult. }
    assert (AP8 : KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -496) 16) by (unfold KXGoM.apart; lia).
    assert (ART : artcells mm)
      by exact (AI_rtcells AI _ _ _ _ _ (w4e_aheap AI L RNG st LB sp m0 DST dcap tl lo src cbs AH DSTF DC LOA LOS SPT mm MU WM)).
    assert (HABS : ablk (SS + 6 + l1 + l2) (SS + 6 + l1 + l2 + l3)).
    { destruct (SRCB ltac:(lia)) as (p & HBs & SB1 & SB2).
      pose proof (hb_unpoisoned AI L RNG st LB m0 p SBL (SBH - SBL) AH HBs) as (_ & _ & _ & K & _).
      unfold ablk in K |- *. lia. }
    assert (RCm : rclean mm rstk).
    { apply (rclean_transport _ m0 mm rstk RCL MU WM).
      unfold appW, KLOW, KHIGH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; lia. }
    pose proof (rclean_shclean _ _ RCm) as SHm.
    pose proof (shclean_hull _ _ _ _ _ SHm) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
    assert (UST : unpoisoned mm (SP + -184) (SP + -144)).
    { apply (shclean_unpoisoned mm _ _ (r_rlo rstk) (r_rhi rstk)). eapply shclean_sub; [exact SHm | lia | lia | lia]. }
    assert (RSH : rng RNG (shad (SP + -184)) 5).
    { unfold rrng in RRS. apply (w4p_rng_sub RNG _ _ _ _ RRS); rewrite ?shad_div;
        [clear - HU1 HU2 RLO RHI SPd SP16; Z.div_mod_to_equations; lia
        |clear - HU1 HU2 RLO RHI SPd SP16; Z.div_mod_to_equations; lia
        |lia]. }
    assert (R496 : rng RNG (SP + -496) 16).
    { apply (w4p_rng_sub RNG lo (al_top L - lo)); [exact WSK | lia | lia | lia]. }
    assert (KD : forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
                   (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
        munch [(DST, DST + dcap); (SP + -184, SP + -144); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' lo (SP + -480) ->
        u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
        rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad3; C8 pw'; C8 aw'; C8 ew'] ->
        evtF bsegs RNG POST (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
                 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) y22 y23 (Z_to_bv 64 AW4_KSB) y25
                 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
            FR (Z_to_bv 64 AW4_D4) fc None mm' (seg_rom bsegs))).
    { intros mm' ob' cw' bw' pw' aw' ew' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31
             MU' WM' MI' ST' OB' OBL' K3'.
      apply (CONT4 l1 l2 l3 q pt4 b4 c1 bw1 p1 a1 e1 c2 bw2 p2 a2 e2 cw' bw' pw' aw' ew' c4 pad1 pad2 pad3 pad4 rest
               w0 w8 w16 w40 w48 w56 mm' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31);
        [|exact HL1|exact HL2|exact HL3|exact HN|exact D6|exact H3S|exact TS4|exact HQ|exact HQ2].
      replace (SP + -144) with (SP + -184 + 40) in MU' by lia.
      apply (WB w4p_W4F_upd3 mm mm' _ _ _ _ _ _ _ (W4DX cw' bw' pw' aw' ew' pad3) _ (SP + -184) ob' HW MU' WM' MI' ST' OB' OBL');
        [lia | lia | left; split; [reflexivity | lia] | left; split; [reflexivity | lia]
        | right; split; [exact K3' | reflexivity] | left; split; [reflexivity | lia]]. }
    assert (KD2 : forall (mm' : amem) (ob' : list byte) (cw' bw' pw' aw' ew' : word)
                   (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
        munch [(DST, DST + dcap); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
        u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
        rw_cells bsegs mm' (SP + -184) [C8 cw'; C4 bw'; CB 4 pad3; C8 pw'; C8 aw'; C8 ew'] ->
        evtF bsegs RNG POST (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18
                 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 (2^62)) y22 y23 (Z_to_bv 64 AW4_KSB) y25
                 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
            FR (Z_to_bv 64 AW4_D4) fc None mm' (seg_rom bsegs))).
    { intros mm' ob' cw' bw' pw' aw' ew' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31
             MU' WM' MI' OB' OBL' K3'.
      apply (KD mm' ob' cw' bw' pw' aw' ew' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31);
        [| exact WM' | exact MI' | | exact OB' | exact OBL' | exact K3'].
      - eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in Hx |- *.
        destruct Hx as (Hx1 & Hx2 & _). split; [exact Hx1|]. split; [exact Hx2|exact I].
      - apply (stk_magree bsegs _ mm mm' lo (SP + -480) (magree_of_munch bsegs _ _ _ MU' WM') ST).
        intros a Ha. cbn [outside]. split; [lia|]. split; [lia|exact I]. }
    refine (w4s33_d3 _ RNG mm FR fc gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31
              w0 w8 w16 w40 w48 w56 c3 pad3 SP DST dcap seg q DT (tl + 256 * mtl) tl mtl b3 (SS + 6 + l1 + l2) pt3
              F0 K3 MI RSP ltac:(lia) G3 ltac:(lia) ltac:(lia) HQ2 G4 TB G10 G11 eq_refl _ _ _).
    - 
      intros HA.
      exact (w4s33_e3 _ RNG mm FR fc gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31
               w0 w8 w16 w40 w48 w56 pad3 bs cbs ob SP DST dcap seg q DT (tl + 256 * mtl) (SS + 6 + l1 + l2) pt3 b3 (bv_unsigned c3)
               tl mtl l3 lo
               F0 ltac:(rewrite EC; exact K3) BS BSL HCB HCBL P2 OB OBL U1 U2 U3 R1 R2 R3
               A1 L1 A2 L2 A3 L3 M1 M2 M3 Z1 Z2 Z3 I1 I2 I3 I4 I5 I6 RS1 RS2 RS3
               AP1 AP2 AP3 AP4 AP8 AP5 AP6 AP7 G2 G9 MI RSP
               ltac:(lia) G3 ltac:(lia) HQ ltac:(lia) HA HQ2
               G4 G5 G6 TP0 ltac:(lia) G7 TB ltac:(lia)
               G10 G11 eq_refl CR ZT
               SP8 ST LOA ltac:(lia) ltac:(lia) ART WIM WIS HABS UST RSH R496 KD).
    - 
      intros HA HB64.
      exact (w4s33_x49 _ RNG mm FR fc gp tp x5 x6 x7 x8 x9 x12 x13 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31
               w0 w8 w16 w40 w48 w56
               (Z_to_bv 64 (SS + 6 + l1 + l2 + pt3)) (Z_to_bv 64 (SS + 6 + l1 + l2)) (Z_to_bv 64 (SS + 6 + l1 + l2 + 8))
               pad3 cbs ob SP DST dcap seg q DT (tl + 256 * mtl) b3 (bv_unsigned c3) tl mtl
               F0 ltac:(rewrite EC; exact K3) HCB HCBL P2 OB OBL U2 U3 R2 R3
               A2 L2 A3 L3 M2 M3 Z2 Z3 I3 I4 I5 I6 RS2 RS3
               AP2 AP4 AP5 AP6 AP7 G2 G9 MI RSP
               ltac:(lia) G3 ltac:(lia) HQ ltac:(lia) HQ2
               G4 ltac:(lia) ltac:(lia)
               G10 G11 eq_refl CR ZT KD2).
    - 
      intros HA HB64 y10.
      exact (w4s33_l3 (Z.to_nat seg) _ RNG mm mm FR fc gp tp x8 x9 y10 x12 x13 x18 x23 x25 x27 x28 x29 x30 x31
               w0 w8 w16 w40 w48 w56 pad3 bs cbs ob SP DST dcap seg q DT (tl + 256 * mtl) (SS + 6 + l1 + l2) pt3 b3 (bv_unsigned c3)
               tl mtl 0 l3
               ltac:(rewrite Z2Nat.id by lia; lia) ltac:(apply munch_refl) ltac:(apply wmono_refl)
               F0 ltac:(rewrite EC; exact K3) BS BSL HCB HCBL P2 OB OBL U1 U2 U3 R1 R2 R3
               A1 L1 A2 L2 A3 L3 M1 M2 M3 Z1 Z2 Z3 I1 I2 I3 I4 I5 I6 RS1 RS2 RS3
               AP1 AP2 AP3 AP4 AP5 AP6 AP7 G2 G9 MI RSP
               ltac:(lia) G3 ltac:(lia) HQ ltac:(lia) ltac:(lia) HQ2
               G4 G5 G6 TP0 ltac:(lia) ltac:(lia) G7 ltac:(lia) ltac:(lia)
               G10 G11 eq_refl CR ZT KD2).
  Qed.

End W4S33.
End CANSEC1.
