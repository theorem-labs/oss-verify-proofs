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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41h.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41I.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation WFR := [(SPV - 416, SPV - 216)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.

  Lemma x41_m1 : forall (k : nat) mm rest j e1 e2 e3 g2 g3 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv
      (k1 k2 k3 k4 b4w p4w : word) pad
      (x1 x5 x8 x9 x11 x12 x14 x16 x19 x28 x29 x31 : word)
      (w0 w6 w9 : word),
    X41P mm rest -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb -> huf_nb_ok false dtb tl ->
    FRA mm w0 (Z_to_bv 64 S1) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 dl) w6 (Z_to_bv 64 (DST + e3)) (Z_to_bv 64 S3) w9 (Z_to_bv 64 (DST + e2)) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 dcap) (Z_to_bv 64 g3) (Z_to_bv 64 g2) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c2) ->
    BD4 mm k4 b4w pad p4w (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 -> HINV o4 n4 c4 ->
    dcap - g3 - j <= Z.of_nat k -> 0 <= j -> j + g3 + 4 <= dcap -> 0 <= e1 <= g3 -> 0 <= g2 <= g3 -> 0 <= e2 <= dcap -> 0 <= e3 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 -> sh = 64 - tl ->
    evt psegs POST (ST 0x22e10 mm x1 x5 k4 (Z_to_bv 64 (DST + j)) x8 x9 (Z_to_bv 64 (S4 + o4)) x11 x12 (Z_to_bv 64 c1) x14 k3 x16 (Z_to_bv 64 sh) (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 c3) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 e1) k2 k1 x28 x29 (Z_to_bv 64 c4) x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mm rest j e1 e2 e3 g2 g3 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv k1 k2 k3 k4 b4w p4w pad
        x1 x5 x8 x9 x11 x12 x14 x16 x19 x28 x29 x31
        w0 w6 w9 PV MI OUT DTB NBOK FA BD SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 HK HJ HROOM HE1 HG2 HE2 HE3 HDL HTL HRSV HSH; [exfalso; lia|].
    assert (TBL : tbl_in_log psegs mm DT sh 2 4 0 12).
    { apply (tbl_in_log_bytes_at psegs mm DT dtb sh 2 4 0 12 DTB); [lia | lia |].
      intros i Hi. replace (64 - sh) with tl in Hi by lia. destruct (NBOK i Hi) as (b & Hb & Hr). exists b. split; [exact Hb|].
      pose proof (bv_unsigned_in_range 8 b). lia. }
    assert (MU : munch WDF mm mm) by apply munch_refl.
    assert (WM : wmono psegs mm mm) by apply wmono_refl.
    pose proof (proj1 HI1) as C1. pose proof (proj1 HI2) as C2. pose proof (proj1 HI3) as C3. pose proof (proj1 HI4) as C4.
    kx_autoLx [0x23024] 200%nat
      [KZRange (dcap - g3 - j) 4 (2^32); KZRange (dcap - g2 - j) 4 (2^32); KZRange (dcap - e1 - j) 4 (2^32); KZRange (dcap - j) 4 (2^32);
       KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32); KZRange dcap 0 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZRange sh 52 63;
       KZRange c1 0 64; KZRange c2 0 64; KZRange c3 0 64; KZRange c4 0 64;
       KZTblLog DT sh 2 4 0 12; KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 416) 160; KZDisj DST dcap (SPV - 256) 40]
      [(DT, 16388); (SPV - 416, 160); (SPV - 256, 40)].
    kx_ev_ranges. kx_mem.
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ ?Q3 _ ?Q4 _ _ _ _ _ _ _ _ _ _ ?Q2 _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        replace Q3 with (Z_to_bv 64 (bv_unsigned Q3)) by apply Z_to_bv_bv_unsigned;
        replace Q4 with (Z_to_bv 64 (bv_unsigned Q4)) by apply Z_to_bv_bv_unsigned;
        replace Q2 with (Z_to_bv 64 (bv_unsigned Q2)) by apply Z_to_bv_bv_unsigned
    end.
    kx_ev_ranges.
    assert (SB1' : SBUF m S1 n1 b1) by (eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB1 | exact MU]).
    assert (SB2' : SBUF m S2 n2 b2) by (eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB2 | exact MU]).
    assert (SB3' : SBUF m S3 n3 b3) by (eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB3 | exact MU]).
    assert (SB4' : SBUF m S4 n4 b4) by (eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB4 | exact MU]).
    eapply (x41_r ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX m j (j + g3) e1 g2 g3 S1 n1 b1 o1 _ S2 n2 b2 o2 _ _ S3 n3 b3 o3 _ _ S4 n4 b4 o4 _ _);
      try eassumption; try lia.
    1-4: (unfold RZ_huf_dx41g.DINV1, RZ_huf_dx41g.DINV2; unfold RZ_huf_dx41g.HINV in HI1, HI2, HI3, HI4; lia).
    - (* [comment removed for export] *)
      intros mm' T2 P1 P2 P3 P4 c1' c2' c3' c4' k3' k4' b4w' p4w' ? ? ? ? ? ? ? ? ? ? ? ? MU' WM' MI' FA' BD' HI1' HI2' HI3' HI4' HT2 HRM.
      subst T2.
      replace P1 with (S1 + (P1 - S1)) by lia. replace P2 with (S2 + (P2 - S2)) by lia.
      replace P3 with (S3 + (P3 - S3)) by lia. replace P4 with (S4 + (P4 - S4)) by lia.
      assert (MUF : munch WDF mm mm')
        by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros; lia).
      assert (WMF : wmono psegs mm mm') by exact (wmono_trans psegs mm m mm' WM WM').
      eapply (IH mm' rest (j + 4) e1 e2 e3 g2 g3 sh S1 n1 b1 (P1 - S1) c1' S2 n2 b2 (P2 - S2) c2' S3 n3 b3 (P3 - S3) c3'
                 S4 n4 b4 (P4 - S4) c4' dl tl rsv).
      all: first [ exact MI' | exact NBOK | exact FA' | exact BD' | exact HI1' | exact HI2' | exact HI3' | exact HI4' | lia
                 | eapply x41p_transport; first [exact CTX | exact DJ3 | exact PV | exact MUF | exact WMF]
                 | eapply (stk_transport_disjoint psegs _ m mm' _ _ OUT MU' WM'); cbn [disjoint_from]; lia
                 | eapply (bytes_at_transport psegs _ m mm' DT dtb DTB MU'); cbn [disjoint_from]; lia
                 | eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MUF] ].
    - (* [comment removed for export] *)
      intros mm' T0 A2 A5 A7 P1 P2 P3 P4 c1' c2' c3' c4' k3' k4' ? ? ? ? ? ? ? ? ? ? ? ? ? MU' WM' MI' FA' BD' HS1 HS2 HS3 HS4
        HC1 HC2 HC3 HC4 HT0 HA7 HA5 HA2.
      subst T0 A7 A5 A2.
      replace P1 with (S1 + (P1 - S1)) by lia. replace P2 with (S2 + (P2 - S2)) by lia.
      replace P3 with (S3 + (P3 - S3)) by lia. replace P4 with (S4 + (P4 - S4)) in BD' by lia.
      assert (MUF : munch WDF mm mm')
        by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros; lia).
      assert (WMF : wmono psegs mm mm') by exact (wmono_trans psegs mm m mm' WM WM').
      eapply (x41_c0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 mm' rest (j + 4) (j + 4 + e1) (j + 4 + g2) (j + 4 + g3) e1 e2 e3
                S1 n1 b1 (P1 - S1) c1' S2 n2 b2 (P2 - S2) c2' S3 n3 b3 (P3 - S3) c3' S4 n4 b4 (P4 - S4) c4' dl tl rsv k4' pad).
      all: first [ exact MI' | exact FA' | exact BD' | exact HS1 | exact HS2 | exact HS3 | exact HS4 | lia
                 | eapply x41p_transport; first [exact CTX | exact DJ3 | exact PV | exact MUF | exact WMF]
                 | eapply (stk_transport_disjoint psegs _ m mm' _ _ OUT MU' WM'); cbn [disjoint_from]; lia
                 | eapply (bytes_at_transport psegs _ m mm' DT dtb DTB MU'); cbn [disjoint_from]; lia
                 | eapply sbuf_transport; first [exact CTX | exact DJ3 | exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact MUF] ].
  Qed.

End DX41I.
