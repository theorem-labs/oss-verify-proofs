(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2 ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42 AZ_huf_bitinit AZ_huf_4x2 AZ_huf_dx42_4g AZ_huf_dx42_3g AZ_huf_dx42_2g AZ_huf_dx42_1g AZ_huf_dx42_m0 AZ_huf_dx42_c0 AZ_huf_dx42_i4 AZ_huf_dx42_i3 AZ_huf_dx42_i2 AZ_huf_dx42_i1 AZ_huf_dx42_s0.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
#[local] Ltac kx_path_hyp E zs nz KXA BR ::= kx_rr_dedup; kx_path_hyp_fast E zs nz KXA BR.
#[local] Ltac kx_sx3 ::= kx_rr_dedup; repeat kx_sx3_1.     (* [comment removed for export] *)
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
#[local] Ltac kxl_rd_exact ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : rw_cells segs m A _ |- _ => apply (kxl_rd_rw segs m A _ N H); reflexivity
      | H : ro_cells segs m A _ |- _ => apply (kxl_rd_ro segs m A _ N H); reflexivity
      | H : bytes_at segs m A ?bs, L : Z.of_nat (length ?bs) = N |- _ => rewrite <- L; exact (rd_at_bytes_at segs m A bs H)
      end
  end.
(* [comment removed for export] *)
#[local] Ltac kxl_lia ::= first [kxl_hyp | solve [kxl_lia_small] | kx_lia].

Section CANSEC1. Context {rc : runConstT}.
Ltac zdj := cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd]; lia.
Ltac ztr := first
  [ eassumption
  | lazymatch goal with
    | |- rw_cells bsegs ?mq ?A ?cs =>
        match goal with
        | H : rw_cells bsegs ?mp A cs, M : munch ?W ?mp mq, WMo : wmono bsegs ?mp mq |- _ =>
            eapply rw_cells_transport; [exact H | exact M | exact WMo | zdj]
        end
    | |- bytes_at bsegs ?mq ?A ?bs =>
        match goal with
        | H : bytes_at bsegs ?mp A bs, M : munch ?W ?mp mq |- _ =>
            eapply bytes_at_transport; [exact H | exact M | zdj]
        end
    end ].
Ltac zfw H M WMo N :=
  lazymatch type of H with
  | rw_cells bsegs ?mp ?A ?cs =>
      lazymatch type of M with
      | munch ?W mp ?mq =>
          assert (N : rw_cells bsegs mq A cs) by (eapply rw_cells_transport; [exact H | exact M | exact WMo | zdj])
      end
  | bytes_at bsegs ?mp ?A ?bs =>
      lazymatch type of M with
      | munch ?W mp ?mq =>
          assert (N : bytes_at bsegs mq A bs) by (eapply bytes_at_transport; [exact H | exact M | zdj])
      end
  end.
Ltac zside := lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- munch _ ?a ?a => apply munch_refl
  | |- wmono _ ?a ?a => apply wmono_refl
  | |- rw_cells _ _ _ _ => ztr
  | |- bytes_at _ _ _ _ => ztr
  | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
  | |- _ -> SINVA _ _ _ => first [assumption | intros; unfold SINVA in *; lia]
  | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
  | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
  | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
  | |- _ /\ _ => first [eassumption | lia | idtac]
  | |- Z.le _ _ => first [eassumption | lia]
  | |- Z.lt _ _ => first [eassumption | lia]
  | |- _ => first [eassumption | idtac]
  end.
Ltac zrest := lazymatch goal with
  | |- forall _ : amem, _ => idtac
  | |- forall _ : Z, _ => idtac
  | |- _ => zside
  end.
Section DX42BZ.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis PRE0 : huf_dec_preA RNG m0 SPV lo 3136 DST dcap SRC n src.
  Hypothesis DTP0 : huf_dt_preA RNG m0 SPV lo DST dcap DT dtb.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 :=
    (rw_cells bsegs mm (SPV + -408) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 w18]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRA mm j0 d j1 := (rw_cells bsegs mm (SPV + -576) [CB 40 j0; C8 d; CB 120 j1]).
  Notation FRJ mm j2 := (rw_cells bsegs mm (SPV + -216) [CB 112 j2]).
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].

  (* [comment removed for export] *)
  Lemma x42b_ret0 : forall mm (j0 j1 j2 pad4 : list byte)
      (d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 c4 b4 p4 st4 lm4 : word)
      (x1 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    stk bsegs mm DST (DST + dcap) -> FRQ mm -> stk bsegs mm lo (SPV + -576) ->
    munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    FRA mm j0 d j1 -> FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 ->
    BD4 mm c4 b4 pad4 p4 st4 lm4 -> FRJ mm j2 ->
    evtF bsegs RNG POST (ST 0xa3488 mm x1 (Z_to_bv 64 dcap) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                            x28 x29 x30 x31).
  Proof using CTX ACTX rc.
    intros mm j0 j1 j2 pad4 d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 c4 b4 p4 st4 lm4
           x1 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 OUT FQ STK MU WM MI FA FR B4 FJ.
    eapply (AZ_huf_dx42.x42_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX);
      [eapply AZ_huf_dx42_c0.x42_einvB; eassumption | exact B4].
  Qed.

  Lemma x42b_small : forall (m1 : amem) (junk : list byte)
      (x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 : word),
    n < 10 ->
    munch [(SPV - 624, SPV)] m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (SPV + -576) [CB 472 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs m1 lo (SPV + -576) ->
    evtF bsegs RNG POST (ST 0x9dc38 m1 (Z_to_bv 64 n) (Z_to_bv 64 dcap) (Z_to_bv 64 DT) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                            (Z_to_bv 64 DST) x25 x26 SB x28 x29 x30 (Z_to_bv 64 SRC)).
  Proof using CTX PRE0 DTP0 rc.
    intros m1 junk x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 NS MU1 WM1 MI1 FQB STK1.
    pose proof PRE0 as PRE'.
    destruct PRE' as (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & ARD & ARS & ART & AST & AZS & ARC & SPA).
    pose proof DTP0 as DTP'. destruct DTP' as (DTB & DL & T0 & T1 & OS3 & DJ2 & ARODT & DTA). unfold HUF_DTABLE_BYTES in *.
    destruct AST as (KLO & RSTK & RI). destruct ARODT as (UDT & RDT & RDTS).
    refine (AZ_huf_dx42_s0.x42_pro_small RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb
              CTX m1 junk x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30
              NS UDT _ RDT RDTS _ _ RSTK RI AZS ARC ART OUT MU1 WM1 MI1 FQB STK1).
    - intros Hd; destruct (ARD Hd) as (_ & U & _); exact U.
    - intros Hd; destruct (ARD Hd) as (_ & _ & R & _); exact R.
    - intros Hd; destruct (ARD Hd) as (_ & _ & _ & R); exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma x42b_n0 : forall (m1 : amem) (junk : list byte)
      (x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 : word),
    n = 0 ->
    munch [(SPV - 624, SPV)] m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (SPV + -576) [CB 472 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs m1 lo (SPV + -576) ->
    evtF bsegs RNG POST (ST 0x9dc38 m1 (Z_to_bv 64 n) (Z_to_bv 64 dcap) (Z_to_bv 64 DT) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                            (Z_to_bv 64 DST) x25 x26 SB x28 x29 x30 (Z_to_bv 64 SRC)).
  Proof using CTX PRE0 DTP0 rc.
    intros m1 junk x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 N0.
    exact (x42b_small m1 junk x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 ltac:(lia)).
  Qed.
End DX42BZ.

(* [comment removed for export] *)
Theorem x42b_proofB : bit_init_stmtA -> x42d_seg_stmt.
Proof.
  intros BITINIT. unfold x42d_seg_stmt.
  intros RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30
         m m1 SPV DST dcap SRC n DT tl lo src dtb junk PRE DTP DT2 TL X2 NB MU1 WM1 MI1 FQB STK1.
  pose proof PRE as PRE'.
  destruct PRE' as (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & ARD & ARS & ART & AST & AZS & ARC & SPA).
  pose proof DTP as DTP'. destruct DTP' as (DTB & DL & T0 & T1 & OS3 & DJ2 & ARODT & DTA). unfold HUF_DTABLE_BYTES in *.
  destruct AST as (KLO & RSTK & RI). destruct ARODT as (UDT & RDT & RDTS).
  assert (DSTA : dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)).
  { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd]; [| left; lia]. right.
    destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  assert (DHI : 0 < dcap -> 0x625000 <= DST).
  { intros Hd. destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  destruct (nth_error dtb 3) as [b3|] eqn:DT3; [| apply nth_error_None in DT3; exfalso; lia].
  assert (CTX : x42b_ctx SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb).
  { pose proof (bv_unsigned_in_range 8 b3) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    assert (EB : Z_to_bv 8 (bv_unsigned b3) = b3)
      by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    unfold x42b_ctx. rewrite EB. unfold KHIGH in KLO. repeat split; try assumption; lia. }
  destruct (Z_lt_le_dec n 10) as [NS|N10].
  { exact (x42b_small RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb CTX PRE DTP
             m1 junk x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 NS MU1 WM1 MI1 FQB STK1). }
  destruct (ARS ltac:(lia)) as (ABS & USRC & RSRC & RSRCS).
  assert (ACTX : x42b_actx RNG m SPV DST dcap SRC n DT lo).
  { unfold x42b_actx. unfold KHIGH in KLO |- *.
    split; [exact USRC|]. split; [exact UDT|].
    split; [intros Hd; destruct (ARD Hd) as (_ & U & _); exact U|].
    split; [exact RSRC|]. split; [exact RSRCS|]. split; [exact RDT|]. split; [exact RDTS|].
    split; [intros Hd; destruct (ARD Hd) as (_ & _ & R & _); exact R|].
    split; [intros Hd; destruct (ARD Hd) as (_ & _ & _ & R); exact R|].
    split; [exact RSTK|]. split; [exact RI|]. split; [exact AZS|]. split; [exact ARC | exact ART]. }
  refine (AZ_huf_dx42_s0.x42_pro RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
            CTX ACTX BITINIT _ m1 junk x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30
            N10 OUT SRCB DTB MU1 WM1 MI1 FQB STK1).
  intros dl pe1 pe2 pe3 S1k n1 S2k n2 S3k n3 S4k n4 bs1 bs2 bs3 bs4 mb o1 b1 o2 b2 o3 b3k o4 b4 k1 k2 k3 k4 pad4 j0 j1 j2
         w0 w8 w9 w10 w11 w12 w13 w14 w16 w18 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z17 z29 z30 z31
         HDL PE1 PE2 PE3 PE4 BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4 E1 E2 E3 E4 E5
         FQ MU0 WM0 MI2 OUT2 DTB2 STK2 FA FR B4 FJ SB1 SB2 SB3 SB4 H1 H2 H3 H4.
  eapply (AZ_huf_dx42_m0.x42_m0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
            CTX X2 ACTX NB dl pe1 pe2 pe3 (64 - tl) (-1 * DT + -5) S1k n1 S2k n2 S3k n3 S4k n4 bs1 bs2 bs3 bs4 mb
            HDL PE1 PE2 PE3 PE4 eq_refl eq_refl BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  all: zrest.
  refine (AZ_huf_dx42_c0.x42_c0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
            CTX X2 ACTX dl pe1 pe2 pe3 S1k n1 S2k n2 S3k n3 S4k n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4
            BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4 FQ _).
  eapply AZ_huf_dx42_1g.x42_d4_1.
  all: zrest.
  all: try (exact (AZ_huf_dx42_2g.x42_d4_2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
                     CTX X2 ACTX)).
  intros mk mq P3 P4 Q3 Q4 f3 f4 c3 c4 pad4' j0' j1' j2' w2 w3 w5 w8' w13' w14' y9 y12 y25 c'
         MUk WMk MUkq WMkq MUq WMq FA2 B42 FJ2 SB32 SB42 SI3 F3 Q3B SI4 F4 Q4B P3H P3L P4L P4H P3E.
  zfw FA2 MUkq WMkq FAq. zfw B42 MUkq WMkq B4q. zfw FJ2 MUkq WMkq FJq.
  zfw SB32 MUkq WMkq S3q. zfw SB42 MUkq WMkq S4q. zfw FQ MUq WMq FQq.
  intros mm' y1 y5 y7 y8 y11 y14 y15 y16 y17 y29 y30 y31 MU' WM' MU0' WM0' MI' OUT' DTB' STK' FR'.
  eapply (AZ_huf_dx42_3g.x42_d4_3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
            CTX X2 ACTX mq mm' (P3 - DST) pe3 dl Q3 S3k n3 bs3 f3 S2k pe2).
  all: zrest.
  intros mm3 r1 r5 r7 r8 r9 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r26 r28 r29 r30 r31
         v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 MU3 WM3 MU03 WM03 MI3 OUT3 DTB3 STK3 FR3.
  zfw FQq MU3 WM3 FQ3.
  replace (Z_to_bv 64 P4) with (Z_to_bv 64 (DST + (P4 - DST))) by (f_equal; lia).
  eapply (AZ_huf_dx42_4g.x42_d4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
            CTX X2 ACTX mm3 mm3 (P4 - DST) dl Q4 S4k n4 bs4 f4 c4 pad4' j0' j1' j2').
  all: zrest.
  intros mm4 u1 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31
         cq bq pq stq lmq padq j0q j1q j2q dq q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
         MU4 WM4 MU04 WM04 MI4 OUT4 DTB4 STK4 FA4 FR4 B44 FJ4.
  zfw FQ3 MU4 WM4 FQ4.
  eapply (x42b_ret0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb CTX ACTX);
    eassumption.
Qed.

(* [comment removed for export] *)
Theorem x42b_proof : x42d_seg_stmt.
Proof. exact (x42b_proofB bit_init_proofA). Qed.
End CANSEC1.
