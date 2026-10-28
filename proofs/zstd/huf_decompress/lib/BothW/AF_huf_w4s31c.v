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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b AF_huf_w4s31z AF_huf_w4s31k AF_huf_w4s31k4.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation amem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.


Lemma w4s31_sub2 : forall lo hi lo' hi' A B, lo' <= lo -> hi <= hi' -> sub_fp [(lo, hi); (A, B)] [(lo', hi'); (A, B)].
Proof. intros lo hi lo' hi' A B H1 H2 x Hx. cbn [outside] in *. lia. Qed.


Lemma w4s31_sub1 : forall lo hi A B, sub_fp [(A, B)] [(lo, hi); (A, B)].
Proof. intros lo hi A B x Hx. cbn [outside] in *. tauto. Qed.

Ltac w4s31_wk MU := eapply munch_weaken; [| exact MU]; first [apply w4s31_sub2; lia | apply w4s31_sub1].

Ltac w4s31_kd KD MU MU2 :=
  eapply KD;
  [ eapply munch_trans; [w4s31_wk MU | w4s31_wk MU2]
  | eapply wmono_trans; eassumption
  | assumption | assumption | assumption | eassumption ].

Ltac w4s31_kd1 KD MU :=
  eapply KD;
  [ w4s31_wk MU | assumption | assumption | eexists; split; eassumption | assumption | eassumption ].


Lemma w4s31_loop : forall (fuel : nat) (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv i len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
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
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> q + i <= seg -> seg - q - i <= 4 * Z.of_nat fuel -> 0 <= i -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> (off = 0 \/ (1 <= off /\ off + 8 <= len)) -> len <= 2^32 -> 0 <= b <= 64 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
    (forall (mm' : amem) (cw bw pw' aw ew : word) (y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y23 y27 y28 y29 y30 y31 : word),
     munch [(DST + q + i, DST + seg); (SP + -376, SP + -336)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     (exists ob', u8arr bsegs mm' DST ob' /\ Z.of_nat (length ob') = dcap) ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 cw; C4 bw; CB 4 pad1; C8 pw'; C8 aw; C8 ew] ->
     evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 (Z_to_bv 64 (DST + seg + q)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
                (Z_to_bv 64 (DST + 2 * seg + q)) y23 (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
           F (Z_to_bv 64 570176) fc None mm' (seg_rom bsegs))) ->

  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (DST + 3 * seg)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl))
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (DST + seg + q)) x9 x10 (Z_to_bv 64 b) x12 x13
               (Z_to_bv 64 64) (Z_to_bv 64 i) (Z_to_bv 64 (DST + seg - 3)) (Z_to_bv 64 (- DT - 5))
               (Z_to_bv 64 (DST + q)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904)
               (Z_to_bv 64 (DST + 2 * seg + q)) (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 seg) x28 x29 x30 x31)
          F (Z_to_bv 64 0x8acdc) fc None mm (seg_rom bsegs)).
Proof.
  intro fuel; induction fuel as [|fuel IH];
  intros Q RNG mm F fc gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob
    SP DST dcap seg q DT dl S off b c tl rsv i len
    FR DS BS BL CB CL TL OB OL U1 U2 U3 R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6 H1 H2 H3
    P1 P2 P3 P4 P5 P6 P7 E1 E2 MI RF HDST HDC HSEG HQ HQI HFU HI HQ3 HSP HS1 HS2 HOFF HLEN HB HDT HTL HRSV HDL HC ZT KD;
  (destruct HOFF as [HO|[HO1 HO2]];
   [ apply (w4s31_x0 Q RNG mm F fc gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob
              SP DST dcap seg q DT dl S off b c tl rsv i len
              FR DS BS BL CB CL TL OB OL U1 U2 U3 R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6 H1 H2 H3
              P1 P2 P3 P4 P5 P6 P7 E1 E2 MI RF HDST HDC HSEG HQ HQI HI HQ3 HSP HS1 HS2 HO HLEN HB HDT HTL HRSV HDL HC ZT);
     [ (intros HQE mm' ob' c' b' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 y18 y27
    MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  w4s31_kd1 KD MU) | (intros HQL mm' ob' c' b' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
    MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  apply (w4s31_tail Q RNG mm' F fc gp tp x25 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
           w0 w8 w16 w40 w48 w56 (Z_to_bv 64 (S + off)) pad1 bs cbs ob' SP DST dcap seg q DT dl S b' c' tl rsv i len
           FR' DS' BS' BL CB' CL TL OB' OL' U1' U2' U3' R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
           H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI' RF HDST HDC HSEG HQ HQL HI HQ3 HSP HS1 HS2 HLEN ltac:(lia)
           HDT HTL HRSV HDL HC' ZT');
  intros mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 z27 z28 z29 z30 z31
    MU2 WM2 MI2 OB2 FR2 DS2;
  w4s31_kd KD MU MU2) ]
   | ]);
  (destruct (Z_le_gt_dec 8 off) as [OF|OF];
   [ destruct (Z_le_gt_dec (q + i + 4) seg) as [R|R];
     [ first [ exfalso; lia
             | apply (w4s31_l1f Q RNG mm F fc gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob
                        SP DST dcap seg q DT dl S off b c tl rsv i len
                        FR DS BS BL CB CL TL OB OL U1 U2 U3 R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
                        H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI RF HDST HDC HSEG HQ R HI HQ3 HSP HS1 HS2 OF HO2 HLEN HB HDT
                        HTL HRSV HDL HC ZT);
               (intros mm' ob' c' b' y10 y12 y13 y28 y29 y30 y31 MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  replace (S + off - b / 8) with (S + (off - b / 8)) in DS' by lia;
  apply (IH Q RNG mm' F fc gp tp x9 y10 y12 y13 x25 y28 y29 y30 y31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob'
           SP DST dcap seg q DT dl S (off - b / 8) b' c' tl rsv (i + 4) len
           FR' DS' BS' BL CB' CL TL OB' OL' U1' U2' U3' R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
           H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI' RF HDST HDC HSEG HQ ltac:(lia) ltac:(lia) ltac:(lia) HQ3 HSP HS1 HS2
           ltac:(lia) HLEN HB' HDT HTL HRSV HDL HC' ZT');
  intros mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 z27 z28 z29 z30 z31
    MU2 WM2 MI2 OB2 FR2 DS2;
  w4s31_kd KD MU MU2) ]
     | apply (w4s31_xf Q RNG mm F fc gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob
                SP DST dcap seg q DT dl S off b c tl rsv i len
                FR DS BS BL CB CL TL OB OL U1 U2 U3 R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6 H1 H2 H3
                P1 P2 P3 P4 P5 P6 P7 E1 E2 MI RF HDST HDC HSEG HQ HQI ltac:(lia) HI HQ3 HSP HS1 HS2 OF HO2 HLEN HB HDT
                HTL HRSV HDL HC ZT);
       [ (intros HQE mm' ob' c' b' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 y18 y27
    MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  w4s31_kd1 KD MU) | (intros HQL mm' ob' c' b' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
    MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  apply (w4s31_tail Q RNG mm' F fc gp tp x25 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
           w0 w8 w16 w40 w48 w56 (Z_to_bv 64 (S + off - b / 8)) pad1 bs cbs ob' SP DST dcap seg q DT dl S b' c' tl rsv i len
           FR' DS' BS' BL CB' CL TL OB' OL' U1' U2' U3' R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
           H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI' RF HDST HDC HSEG HQ HQL HI HQ3 HSP HS1 HS2 HLEN ltac:(lia)
           HDT HTL HRSV HDL HC' ZT');
  intros mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 z27 z28 z29 z30 z31
    MU2 WM2 MI2 OB2 FR2 DS2;
  w4s31_kd KD MU MU2) ] ]
   | ]);
  (destruct (Z_le_gt_dec b (8 * off + 7)) as [BB|BB];
   [ destruct (Z_le_gt_dec (q + i + 4) seg) as [R|R];
     [ first [ exfalso; lia
             | apply (w4s31_l1s Q RNG mm F fc gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob
                        SP DST dcap seg q DT dl S off b c tl rsv i len
                        FR DS BS BL CB CL TL OB OL U1 U2 U3 R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
                        H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI RF HDST HDC HSEG HQ R HI HQ3 HSP HS1 HS2 ltac:(lia) BB HO2
                        HLEN HB HDT HTL HRSV HDL HC ZT);
               (intros mm' ob' c' b' y9 y10 y12 y13 y28 y29 y30 y31 MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  replace (S + off - b / 8) with (S + (off - b / 8)) in DS' by lia;
  apply (IH Q RNG mm' F fc gp tp y9 y10 y12 y13 x25 y28 y29 y30 y31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob'
           SP DST dcap seg q DT dl S (off - b / 8) b' c' tl rsv (i + 4) len
           FR' DS' BS' BL CB' CL TL OB' OL' U1' U2' U3' R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
           H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI' RF HDST HDC HSEG HQ ltac:(lia) ltac:(lia) ltac:(lia) HQ3 HSP HS1 HS2
           ltac:(lia) HLEN HB' HDT HTL HRSV HDL HC' ZT');
  intros mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 z27 z28 z29 z30 z31
    MU2 WM2 MI2 OB2 FR2 DS2;
  w4s31_kd KD MU MU2) ]
     | apply (w4s31_xs Q RNG mm F fc gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob
                SP DST dcap seg q DT dl S off b c tl rsv i len
                FR DS BS BL CB CL TL OB OL U1 U2 U3 R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6 H1 H2 H3
                P1 P2 P3 P4 P5 P6 P7 E1 E2 MI RF HDST HDC HSEG HQ HQI ltac:(lia) HI HQ3 HSP HS1 HS2 ltac:(lia) BB HO2
                HLEN HB HDT HTL HRSV HDL HC ZT);
       [ (intros HQE mm' ob' c' b' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 y18 y27
    MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  w4s31_kd1 KD MU) | (intros HQL mm' ob' c' b' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
    MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  apply (w4s31_tail Q RNG mm' F fc gp tp x25 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
           w0 w8 w16 w40 w48 w56 (Z_to_bv 64 (S + off - b / 8)) pad1 bs cbs ob' SP DST dcap seg q DT dl S b' c' tl rsv i len
           FR' DS' BS' BL CB' CL TL OB' OL' U1' U2' U3' R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
           H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI' RF HDST HDC HSEG HQ HQL HI HQ3 HSP HS1 HS2 HLEN ltac:(lia)
           HDT HTL HRSV HDL HC' ZT');
  intros mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 z27 z28 z29 z30 z31
    MU2 WM2 MI2 OB2 FR2 DS2;
  w4s31_kd KD MU MU2) ] ]
   | apply (w4s31_xe Q RNG mm F fc gp tp x9 x10 x12 x13 x25 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 pad1 bs cbs ob
              SP DST dcap seg q DT dl S off b c tl rsv i len
              FR DS BS BL CB CL TL OB OL U1 U2 U3 R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6 H1 H2 H3
              P1 P2 P3 P4 P5 P6 P7 E1 E2 MI RF HDST HDC HSEG HQ HQI HI HQ3 HSP HS1 HS2 ltac:(lia) ltac:(lia) HO2
              HLEN HB HDT HTL HRSV HDL HC ZT);
     [ (intros HQE mm' ob' c' b' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 y18 y27
    MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  w4s31_kd1 KD MU) | (intros HQL mm' ob' c' b' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
    MU WM MI' OB' OL' FR' DS' BS' CB' U1' U2' U3' ZT' HC' HB';
  apply (w4s31_tail Q RNG mm' F fc gp tp x25 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
           w0 w8 w16 w40 w48 w56 (Z_to_bv 64 S) pad1 bs cbs ob' SP DST dcap seg q DT dl S b' c' tl rsv i len
           FR' DS' BS' BL CB' CL TL OB' OL' U1' U2' U3' R1 R2 R3 A1 L1 A2 L2 A3 L3 M1 M2 M3 N1 N2 N3 B1 B2 B3 B4 B5 B6
           H1 H2 H3 P1 P2 P3 P4 P5 P6 P7 E1 E2 MI' RF HDST HDC HSEG HQ HQL HI HQ3 HSP HS1 HS2 HLEN ltac:(lia)
           HDT HTL HRSV HDL HC' ZT');
  intros mm2 cw bw pw2 aw ew z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z23 z27 z28 z29 z30 z31
    MU2 WM2 MI2 OB2 FR2 DS2;
  w4s31_kd KD MU MU2) ] ]).
Qed.










End CANSEC1.
