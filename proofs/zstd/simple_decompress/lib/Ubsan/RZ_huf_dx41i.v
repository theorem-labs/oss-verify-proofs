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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41h huf411_kit_rs huf41_kit_x41ck huf417_kit_rlk huf417_kit_rld.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41I.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 224, SPV - 184)].
  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation WFR := [(SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.

  Lemma x41_m1 : forall (k : nat) mm rest j e1 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv
      (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x7 x8 x9 x12 x14 x21 x22 x27 x29 : word)
      (w0 w12 w15 : word),
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb -> huf_nb_ok false dtb tl ->
    FRA mm w0 (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 dl) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (S2 + 8))
      (Z_to_bv 64 (3 * e1)) (Z_to_bv 64 (2 * e1)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + dcap - 3))
      (Z_to_bv 64 (DST + 2 * e1)) w12 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) w15 (Z_to_bv 64 (S4 + o4)) ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 -> HINV o4 n4 c4 ->
    dcap - 3 * e1 - j <= Z.of_nat k -> 0 <= j -> j + 3 * e1 + 4 <= dcap -> 0 <= e1 ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> sh = 64 - tl ->
    evt usegs POST (ST 0x22df8 mm (Z_to_bv 64 c2) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) x7 x8 x9 (Z_to_bv 64 (-20)) (Z_to_bv 64 (-1 * DT + -5))
                     x12 (Z_to_bv 64 c1) x14 (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 sh) (Z_to_bv 64 (-1)) (Z_to_bv 64 c4) (Z_to_bv 64 c3) k2 x21 x22 k4
                     (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) x27 k1 x29 (Z_to_bv 64 (S1 + o1)) k3).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mm rest j e1 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv k1 k2 k3 k4 pad1 pad2 pad3 pad4
        x7 x8 x9 x12 x14 x21 x22 x27 x29
        w0 w12 w15 PV MI OUT DTB NBOK FA HB1 HB2 HB3 HB4 SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 HK HJ HROOM HE1 HDL HTL HRSV HSH; [exfalso; lia|].
    assert (TBL : tbl_in_log usegs mm DT sh 2 4 0 12).
    { apply (tbl_in_log_bytes_at usegs mm DT dtb sh 2 4 0 12 DTB); [lia | lia |].
      intros i Hi. replace (64 - sh) with tl in Hi by lia. destruct (NBOK i Hi) as (b & Hb & Hr). exists b. split; [exact Hb|].
      pose proof (bv_unsigned_in_range 8 b). lia. }
    assert (MU : munch WDF mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    pose proof (proj1 HI1) as C1. pose proof (proj1 HI2) as C2. pose proof (proj1 HI3) as C3. pose proof (proj1 HI4) as C4.
    kx_autoLx [0x2323c; 0x253c0] 240%nat
      [KZRange (dcap - 3 * e1 - j) 4 (2^32); KZRange (dcap - 2 * e1 - j) 4 (2^32); KZRange (dcap - e1 - j) 4 (2^32); KZRange (dcap - j) 4 (2^32);
       KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange (2 * e1) 0 (2^32); KZRange (3 * e1) 0 (2^32); KZRange dcap 0 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZRange sh 52 63;
       KZRange c1 0 64; KZRange c2 0 64; KZRange c3 0 64; KZRange c4 0 64;
       KZTblLog DT sh 2 4 0 12; KZWr DST dcap; KZWr (SPV - 376) 40; KZWr (SPV - 224) 40; KZWr (SPV - 184) 40; KZWr (SPV - 144) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 512) 176; KZDisj DST dcap (SPV - 224) 120;
       KZDisj (SPV - 512) 176 DT 16388; KZDisj (SPV - 224) 120 DT 16388]
      [(DT, 16388); (SPV - 512, 136); (SPV - 376, 40); (SPV - 224, 40); (SPV - 184, 40); (SPV - 144, 40)].
    all: x41_ck.
    kx_ev_ranges. kx_mem.
    assert (SB1' : SBUF m S1 n1 b1) by (eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB1 | exact MU]).
    assert (SB2' : SBUF m S2 n2 b2) by (eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB2 | exact MU]).
    assert (SB3' : SBUF m S3 n3 b3) by (eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB3 | exact MU]).
    assert (SB4' : SBUF m S4 n4 b4) by (eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB4 | exact MU]).
    assert (PV' : X41P m rest) by (eapply x41p_transport; first [exact CTX | exact DJ3 | exact PV | exact MU | exact WM]).
    assert (KHj : huf417_kit_rld.KH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb
                    rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0).
    { unfold huf417_kit_rld.KH.
      intros mm' k1' k2' k3' k4' c1' o1' c2' o2' c3' o3' c4' o4' y7 y8 y9 y12 y14 y21 y22 y27 y29 w12' w15'
        (PV2 & MI2 & OUT2 & DTB2 & NB2 & SB12 & SB22 & SB32 & SB42 & HJ2 & HE2 & HR2 & HDL2 & HTL2 & HRSV2)
        FA2 B12 B22 B32 B42 H12 H22 H32 H42.
      eapply (IH mm' rest (j + 4) e1 (64 - tl) S1 n1 b1 o1' c1' S2 n2 b2 o2' c2' S3 n3 b3 o3' c3' S4 n4 b4 o4' c4' dl tl rsv
                 k1' k2' k3' k4' pad1 pad2 pad3 pad4 y7 y8 y9 y12 y14 y21 y22 y27 y29 w0 w12' w15').
      all: first [ eassumption | lia ]. }
    pose proof (x41_r ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 SPVA DTA
                  rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 KHj) as KR.
    unfold huf417_kit_rld.K4264 in KR.
    subst sh.
    lazymatch goal with
    | |- evt _ _ (MS (mkR ?R1 _ _ _ _ _ _ _ _ _ _ _ ?R13 ?R14 _ _ _ ?R18 ?R19 _ _ _ _ ?R24 _ _ _ _ ?R29 _ _) _ _ _ _ _ _) =>
        lazymatch R1 with Z_to_bv 64 ?P2 =>
        lazymatch R13 with Z_to_bv 64 ?P1 =>
        lazymatch R18 with Z_to_bv 64 ?P4 =>
        lazymatch R19 with Z_to_bv 64 ?P3 =>
          replace R14 with (Z_to_bv 64 (DST + (j + 3 * e1 + 3))) by (f_equal; lia);
          replace R24 with (Z_to_bv 64 (DST + (j + 3))) by (f_equal; lia);
          replace R29 with (Z_to_bv 64 (DST + j)) by (f_equal; lia);
          eapply (KR m k1 k2 k3 k4 P1 o1 P2 o2 P3 o3 P4 o4 _ _ _ _ _ _ w12 w15)
        end end end end
    end.
    1: repeat (split; [first [eassumption | lia] |]); first [eassumption | lia].
    all: first [ eassumption
               | (unfold x41_dinv; unfold RZ_huf_dx41g.HINV in HI1, HI2, HI3, HI4; lia) ].
  Qed.

End DX41I.
(* [comment removed for export] *)
(* [comment removed for export] *)
