(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42 AZ_huf_dx42_3a.
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
Section DX42B3B.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STC ra mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 678828) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 :=
    (rw_cells bsegs mm (SPV + -408) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 w18]).
  Notation FRS3 mm S pe w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 :=
    (FRS mm w0 (Z_to_bv 64 (DST + dcap)) w2 w3 (Z_to_bv 64 (DST + pe)) w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 (S + 8)) w13 w14 w15 w16 w17
         (Z_to_bv 64 (DT + 4))).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation WD3 := [(DST, DST + dcap); (SPV - 408, SPV - 256)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation x42_end := (AZ_huf_dx42.x42_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation K3 mb dl x10 :=
    (forall mm' (y1 y5 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23 y26 y28 y29 y30 y31 : word)
            (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : word),
        munch WD3 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRS mm' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 (Z_to_bv 64 (DT + 4)) ->
        evtF bsegs RNG POST (ST 0xa256c mm' y1 y5 (Z_to_bv 64 tl) y7 y8 y9 x10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21
                                (Z_to_bv 64 (DST + dcap - 7)) y23 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) y26 SB
                                y28 y29 y30 y31)).

  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333498432 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
  (* [comment removed for export] *)
  Ltac dfacts MU0 UDST RDST RDSTS DSTA AW0 R1 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let D := fresh "DPOS" in
    assert (D : 0 < dcap) by lia;
    assert (UDSTc : unpoisoned mm DST (DST + dcap))
      by (eapply unp_carryW; [exact (UDST D) | exact MU0 | apply aappW_cons_D; [exact DSTA | exact D | exact AW0] | clear - R1; lia | clear - R1 D; lia | clear - R1; lia]);
    pose proof (RDST D) as RDSTc; pose proof (RDSTS D) as RDSTSc;
    assert (DSTAc : DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST) by (clear - D DSTA; lia);
    pose proof (rng_shspanZ _ _ _ RDSTSc) as RDSTz;
    pose proof (unpoisoned_unpZ _ _ _ DST (DST + dcap) UDSTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R1; lia)) as UDSTz;
    clear D.
  (* [comment removed for export] *)
  Ltac sfacts0 MU0 USRC DSTA AW0 R1 R2 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let N := fresh "NPOS" in
    assert (N : 0 < n) by lia;
    assert (USRCc : unpoisoned mm SRC (SRC + n))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact USRC | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R2; lia | clear - R2 N; lia | clear - R2; lia]
          | eapply unp_carryW; [exact USRC | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R2; lia | clear - R2 N; lia | clear - R2; lia] ]);
    clear N.
  Ltac sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc :=
    lazymatch type of BSE with ?S + ?len <= SRC + n =>
      assert (SF : (4096 <= S <= 140737488355328) /\ (4096 <= S + len <= 140737488355328) /\ (1 <= len <= 4294967296) /\ S + len < 2^47 /\
                   (DST + dcap <= S \/ S + len <= DST) /\ (S + len <= lo \/ SPV <= S) /\
                   (SPV - 256 + 40 <= S \/ S + len <= SPV - 256) /\ (SPV - 576 + 576 <= S \/ S + len <= SPV - 576))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      destruct SF as (S0 & S1 & SL32 & S2 & DJS & DJK & DJB & DJFr);
      assert (RS : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia)) as RSz;
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia)) as USz
      end
    end.
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 408 \/ SPV - 408 + 152 <= DST) /\ (DST + dcap <= SPV - 256 \/ SPV - 256 + 40 <= DST) /\
                 (SPV - 256 + 40 <= DT \/ DT + 16388 <= SPV - 256) /\ (SPV - 408 + 152 <= DT \/ DT + 16388 <= SPV - 408) /\
                 (DST + dcap <= SPV - 576 \/ SPV - 576 + 576 <= DST))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4 & DJF5).
  (* [comment removed for export] *)
  Ltac kclean :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : DT mod 4 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < dcap -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < dcap -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : aro_client RNG m0 |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : Z.of_nat (length src) = n |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac evr := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end); kx_ev_ranges.
  (* [comment removed for export] *)
  Ltac lside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [lia | kx_lia | idtac]
    | |- _ \/ _ => try lia
    | |- Z.le _ _ => lia
    | |- Z.lt _ _ => lia
    | |- _ => eassumption
    end.

      (* [comment removed for export] *)
          (* [comment removed for export] *)
  Notation x42_z4_3 := (AZ_huf_dx42_3a.x42_z4_3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x42_t4_3 := (AZ_huf_dx42_3a.x42_t4_3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x42_g4_3 := (AZ_huf_dx42_3a.x42_g4_3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma x42_2rl_3 : forall mb mm j pe pe2 dl sh P S len bs bc
      (x1 x5 x8 x9 x10 x11 x12 x14 x16 x20 x21 x23 x25 x26 x28 x30 x31 : word)
      (w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 : word),
    munch WD3 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRS3 mm S pe w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= pe -> pe <= dcap -> pe2 = DST + pe + -2 -> sh = 64 - tl -> dl = tl + 256 * rsv ->
    SINVA (P - S) len bc -> 0 <= bc <= 64 ->
    K3 mb dl x10 ->
    (forall mm' fl nb bc' (y1 y5 y8 y9 y12 y14 y20 y21 y23 y25 y26 y28 y30 y31 : word),
        munch WD3 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRS3 mm' S pe w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 ->
        bytes_at bsegs mm' S bs -> (fl = 0 \/ fl = 1) -> 0 <= nb <= 8 -> S <= P - nb -> P - nb + 8 <= S + len -> 0 <= bc' <= 64 -> (fl = 1 -> bc' <= 7) ->
        evtF bsegs RNG POST (ST 0xa2204 mm' y1 y5 (Z_to_bv 64 tl) (Z_to_bv 64 pe2) y8 y9 x10 (Z_to_bv 64 fl) y12 (Z_to_bv 64 (DST + j)) y14 (Z_to_bv 64 P)
                                (Z_to_bv 64 nb) (Z_to_bv 64 64) (Z_to_bv 64 bc') (Z_to_bv 64 S) y20 y21 (Z_to_bv 64 (DST + dcap - 7)) y23 (Z_to_bv 64 dl) y25 y26 SB
                                y28 (Z_to_bv 64 sh) y30 y31)) ->
    evtF bsegs RNG POST (ST 0xa21c8 mm x1 x5 (Z_to_bv 64 tl) (Z_to_bv 64 pe2) x8 x9 x10 x11 x12 (Z_to_bv 64 (DST + j)) x14 (Z_to_bv 64 P)
                            x16 (Z_to_bv 64 64) (Z_to_bv 64 bc) (Z_to_bv 64 S) x20 x21 (Z_to_bv 64 (DST + dcap - 7)) x23 (Z_to_bv 64 dl) x25 x26 SB
                            x28 (Z_to_bv 64 sh) x30 x31).
  Proof using CTX X2OK ACTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mb mm j pe pe2 dl sh P S len bs bc x1 x5 x8 x9 x10 x11 x12 x14 x16 x20 x21 x23 x25 x26 x28 x30 x31
      w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17
      MU WM MU0 WM0 MI OUT DTB STK FR SBH BL BSS BSE LEN1 HJ HPE HPE2 HSH HDL HS HBC K KB.
    assert (O : exists off, P = S + off) by (exists (P - S); lia). destruct O as (off & ->).
    replace (S + off - S) with off in HS by lia.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO.
    assert (KF : 0 <= j <= 4294967296 /\ 0 <= pe - j <= 4294967296) by (clear - HJ HPE GF2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2).
    subst pe2.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - HBC; lia).
    destruct QR as (q & r & Ebc & HQ & HR).
    destruct HS as [-> | (O1 & O2 & B1)].
    - (* [comment removed for export] *)
      kclean. subst bc.
      kx_autoFLA FR (@nil kza) [0xa2204; 0xa23b4] 20%nat
        [KZRange S 4096 140737488355328; KZRange SPV 17594333495296 140737488355328; KZRange DST 4096 140737488355328; KZRange (8 * q + r) 0 64]
        [(SPV + -408, 152)] [(SPV - 576, 576)].
      all: aside.
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: eapply (x42_g4_3 mb); lside; first [exact K | lia].
    - assert (KF4 : 8 <= len - off <= 4294967296 /\ 9 <= len <= 4294967296) by (clear - O2 SL32 O1; lia). destruct KF4 as (KF4 & KF3).
      destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
      + (* [comment removed for export] *)
        assert (KF5 : 1 <= q - off <= 8 /\ 1 <= off <= 7) by (clear - CQ C8 O1 HQ; lia). destruct KF5 as (KF5 & KF6).
        kclean. subst bc.
        kx_autoFLA FR (@nil kza) [0xa2204; 0xa23b4] 40%nat
          [KZRange (len - off) 8 4294967296; KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange len 9 4294967296; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange (S + off) 4097 140737488355320;
           KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328;
           KZRange SPV 17594333495296 140737488355328]
          [(SPV + -408, 152)] [(SPV - 576, 576)].
        all: aside.
        all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
        all: try clear KF5 KF6.
        all: kx_gen_regsF [5%nat]; intros.
        all: evr; kx_mem; kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
        all: try (replace ((8 * q + r) / 8) with q in * by (clear - HQ HR; Z.div_mod_to_equations; lia)).
        all: eapply KB; lside; first [left; reflexivity | lia].
      + (* [comment removed for export] *)
        assert (KF5 : 0 <= off - q <= 7 /\ 1 <= off <= 7) by (clear - CQ C8 O1 HQ; lia). destruct KF5 as (KF5 & KF6).
        kclean. subst bc.
        kx_autoFLA FR (@nil kza) [0xa2204; 0xa23b4] 40%nat
          [KZRange (len - off) 8 4294967296; KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange len 9 4294967296; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange (S + off) 4097 140737488355320;
           KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328;
           KZRange SPV 17594333495296 140737488355328]
          [(SPV + -408, 152)] [(SPV - 576, 576)].
        all: aside.
        all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
        all: try clear KF5 KF6.
        all: kx_gen_regsF [5%nat]; intros.
        all: evr; kx_mem; kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
        all: try (replace ((8 * q + r) / 8) with q in * by (clear - HQ HR; Z.div_mod_to_equations; lia)).
        all: eapply KB; lside; first [right; reflexivity | lia].
      + (* [comment removed for export] *)
        assert (KF6 : 8 <= off <= 4294967296) by (clear - C8 O2 SL32; lia).
        kclean. subst bc.
        kx_autoFLA FR (@nil kza) [0xa2204; 0xa23b4] 30%nat
          [KZRange (len - off) 8 4294967296; KZRange off 8 4294967296; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange (S + off) 4096 140737488355328;
           KZRange SPV 17594333495296 140737488355328]
          [(SPV + -408, 152)] [(SPV - 576, 576)].
        all: aside.
        (* [comment removed for export] *)
        all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
        all: try clear KF6.
        all: kx_gen_regsF [5%nat]; intros.
        all: evr; kx_mem; kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
        all: try (replace ((8 * q + r) / 8) with q in * by (clear - HQ HR; Z.div_mod_to_equations; lia)).
        all: try (replace (8 * q + r - 8 * q) with r in * by lia).
        all: eapply KB; lside; first [right; reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_p4b_3 : forall mb mm j pe pe2 dl sh fl nb P S len bs bc
      (x1 x5 x8 x9 x10 x12 x14 x20 x21 x23 x25 x26 x28 x30 x31 : word)
      (w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 : word),
    munch WD3 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRS3 mm S pe w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= pe -> pe <= dcap -> pe2 = DST + pe + -2 -> sh = 64 - tl -> dl = tl + 256 * rsv ->
    (fl = 0 \/ fl = 1) -> 0 <= nb <= 8 -> S <= P - nb -> P - nb + 8 <= S + len -> 0 <= bc <= 64 -> (fl = 1 -> bc <= 7) ->
    K3 mb dl x10 ->
    (forall mm' j' bc' P' (y1 y5 y8 y9 y11 y12 y14 y16 y20 y21 y23 y25 y26 y28 y30 y31 : word),
        munch WD3 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRS3 mm' S pe w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 ->
        bytes_at bsegs mm' S bs -> j < j' <= pe -> 0 <= bc' <= 64 -> P' = P - nb -> SINVA (P' - S) len bc' ->
        evtF bsegs RNG POST (ST 0xa21c8 mm' y1 y5 (Z_to_bv 64 tl) (Z_to_bv 64 pe2) y8 y9 x10 y11 y12 (Z_to_bv 64 (DST + j')) y14 (Z_to_bv 64 P')
                                y16 (Z_to_bv 64 64) (Z_to_bv 64 bc') (Z_to_bv 64 S) y20 y21 (Z_to_bv 64 (DST + dcap - 7)) y23 (Z_to_bv 64 dl) y25 y26 SB
                                y28 (Z_to_bv 64 sh) y30 y31)) ->
    evtF bsegs RNG POST (ST 0xa2204 mm x1 x5 (Z_to_bv 64 tl) (Z_to_bv 64 pe2) x8 x9 x10 (Z_to_bv 64 fl) x12 (Z_to_bv 64 (DST + j)) x14 (Z_to_bv 64 P)
                            (Z_to_bv 64 nb) (Z_to_bv 64 64) (Z_to_bv 64 bc) (Z_to_bv 64 S) x20 x21 (Z_to_bv 64 (DST + dcap - 7)) x23 (Z_to_bv 64 dl) x25 x26 SB
                            x28 (Z_to_bv 64 sh) x30 x31).
  Proof using CTX X2OK ACTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mb mm j pe pe2 dl sh fl nb P S len bs bc x1 x5 x8 x9 x10 x12 x14 x20 x21 x23 x25 x26 x28 x30 x31
      w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17
      MU WM MU0 WM0 MI OUT DTB STK FR SBH BL BSS BSE LEN1 HJ HPE HPE2 HSH HDL HFL HNB OP1 OP2 HBC HB7 K KH.
    assert (O : exists off, P = S + off + nb) by (exists (P - nb - S); lia). destruct O as (off & ->).
    assert (O12 : 0 <= off /\ off + 8 <= len) by (clear - OP1 OP2; lia). destruct O12 as (O1 & O2).
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO.
    assert (KF : 0 <= j <= 4294967296 /\ 0 <= pe - j <= 4294967296 /\ 8 <= len <= 4294967296 /\ 0 <= off <= 4294967288 /\ 8 <= len - off <= 4294967296)
      by (clear - HJ HPE GF2 O1 O2 SL32; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5).
    subst pe2.
    destruct HFL as [-> | ->].
    { (* [comment removed for export] *)
      kclean.
      kx_autoFLA FR [KAUnp S len] [0xa21c8; 0xa23b4] 60%nat
        [KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange (pe - j) 0 4294967296; KZRange (dcap - j) 0 4294967296; KZRange DST 4096 140737488355328;
         KZRange nb 0 8; KZRange len 8 4294967296; KZRange off 0 4294967288; KZRange (len - off) 8 4294967296;
         KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange SPV 17594333495296 140737488355328]
        [(S, len); (SPV + -408, 152)] [(S, len); (SPV - 576, 576)].
      all: aside.
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: kx_gen_regsF [5%nat; 8%nat; 9%nat; 11%nat; 15%nat; 16%nat; 26%nat; 28%nat; 30%nat; 31%nat]; intros.
      all: evr; kx_mem.
      all: eapply (x42_g4_3 mb); lside; first [exact K | lia]. }
    destruct (Z_lt_le_dec (pe - j) 2) as [SM|ROOM].
    { (* [comment removed for export] *)
      kclean.
      kx_autoFLA FR [KAUnp S len] [0xa21c8; 0xa23b4] 60%nat
        [KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange (pe - j) 0 1; KZRange (dcap - j) 0 4294967296; KZRange DST 4096 140737488355328;
         KZRange nb 0 8; KZRange len 8 4294967296; KZRange off 0 4294967288; KZRange (len - off) 8 4294967296;
         KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange SPV 17594333495296 140737488355328]
        [(S, len); (SPV + -408, 152)] [(S, len); (SPV - 576, 576)].
      all: aside.
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: kx_gen_regsF [5%nat; 8%nat; 9%nat; 11%nat; 15%nat; 16%nat; 26%nat; 28%nat; 30%nat; 31%nat]; intros.
      all: evr; kx_mem.
      all: eapply (x42_g4_3 mb); lside; first [exact K | lia]. }
    (* [comment removed for export] *)
    specialize (HB7 eq_refl).
    dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. kclean.
    assert (TBL : tbl_in_log bsegs mm DT sh 4 7 1 2) by (rewrite HSH; exact (x42_tblA dtb tl DT mm DL TL X2OK DTB)).
    assert (KF6 : 4096 <= DST + j <= 140737488355326 /\ 2 <= pe - j) by (clear - ROOM R1 HJ HPE; lia). destruct KF6 as (KF6 & KF7).
    kx_autoFLA FR [KAUnp DT 16388; KAUnp S len; KAUnp DST dcap; KAApp DST dcap] [0xa21c8; 0xa23b4] 120%nat
        [KZRange (pe - j) 2 4294967296; KZRange (dcap - j) 2 4294967296; KZRange bc 0 7; KZRange nb 0 8; KZRange len 8 4294967296; KZRange off 0 4294967288;
         KZRange (len - off) 8 4294967296;
         KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355326;
         KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange sh 52 63;
         KZRange SPV 17594333495296 140737488355328; KZWr DST dcap;
         KZDisj DST dcap DT 16388; KZDisj DST dcap S len; KZDisj DST dcap (SPV - 576) 576; KZTblLog DT sh 4 7 1 2]
        [(DT, 16388); (S, len); (SPV + -408, 152)] [(DT, 16388); (S, len); (DST, dcap); (SPV - 576, 576)].
    all: aside.
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: try clear KF6 KF7.
    all: kx_gen_regsF [5%nat; 8%nat; 9%nat; 11%nat; 16%nat; 26%nat; 30%nat; 31%nat]; intros.
    all: evr; kx_mem; kx_sx3; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa23b4) _ _ _ _) => eapply (x42_g4_3 mb); lside; first [exact K | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa21c8) _ _ _ _) => eapply KH; lside; first [unfold SINVA; lia | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_p4_3 : forall (k : nat) mb mm j pe pe2 dl sh P S len bs bc
      (x1 x5 x8 x9 x10 x11 x12 x14 x16 x20 x21 x23 x25 x26 x28 x30 x31 : word)
      (w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 : word),
    munch WD3 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRS3 mm S pe w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    pe - j <= Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> pe2 = DST + pe + -2 -> sh = 64 - tl -> dl = tl + 256 * rsv ->
    SINVA (P - S) len bc -> 0 <= bc <= 64 ->
    K3 mb dl x10 ->
    evtF bsegs RNG POST (ST 0xa21c8 mm x1 x5 (Z_to_bv 64 tl) (Z_to_bv 64 pe2) x8 x9 x10 x11 x12 (Z_to_bv 64 (DST + j)) x14 (Z_to_bv 64 P)
                            x16 (Z_to_bv 64 64) (Z_to_bv 64 bc) (Z_to_bv 64 S) x20 x21 (Z_to_bv 64 (DST + dcap - 7)) x23 (Z_to_bv 64 dl) x25 x26 SB
                            x28 (Z_to_bv 64 sh) x30 x31).
  Proof using CTX X2OK ACTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    induction k as [|k IH]; intros mb mm j pe pe2 dl sh P S len bs bc x1 x5 x8 x9 x10 x11 x12 x14 x16 x20 x21 x23 x25 x26 x28 x30 x31
      w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17
      MU WM MU0 WM0 MI OUT DTB STK FR SBH BL BSS BSE LEN1 HK HJ HPE HPE2 HSH HDL HS HBC K.
    all: eapply (x42_2rl_3 mb); lside; try exact K.
    all: intros mm' fl nb bc' y1 y5 y8 y9 y12 y14 y20 y21 y23 y25 y26 y28 y30 y31 MU' WM' MU0' WM0' MI' OUT' DTB' STK' FR' SB' HFL HNB HO' HO2' HBC' HB7.
    all: eapply (x42_p4b_3 mb); lside; first [exact K | exact HFL | exact HB7 | lia | idtac].
    (* [comment removed for export] *)
    all: try (intros; exfalso; lia).
    intros mm2 j2 bc2 P2 z1 z5 z8 z9 z11 z12 z14 z16 z20 z21 z23 z25 z26 z28 z30 z31 MU2 WM2 MU02 WM02 MI2 OUT2 DTB2 STK2 FR2 SB2 HJ2 HB2 HP2 HS2.
    eapply (IH mb); lside; first [exact K | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_c4_3 : forall mb mm j pe dl S len bs bc (p0 : word)
      (x1 x5 x7 x8 x9 x10 x11 x12 x14 x16 x17 x20 x21 x23 x25 x26 x29 x30 x31 : word)
      (w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 : word),
    munch WD3 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRS3 mm S pe w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17 ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2147483648 ->
    (bc <= 64 -> exists off, p0 = Z_to_bv 64 (S + off) /\ SINVA off len bc) ->
    K3 mb dl x10 ->
    evtF bsegs RNG POST (ST 0xa219c mm x1 x5 (Z_to_bv 64 tl) x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (DST + j)) x14 p0 x16 x17
                            (Z_to_bv 64 bc) (Z_to_bv 64 S) x20 x21 (Z_to_bv 64 (DST + dcap - 7)) x23 (Z_to_bv 64 dl) x25 x26 SB
                            (Z_to_bv 64 (DST + pe)) x29 x30 x31).
  Proof using CTX X2OK ACTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mb mm j pe dl S len bs bc p0 x1 x5 x7 x8 x9 x10 x11 x12 x14 x16 x17 x20 x21 x23 x25 x26 x29 x30 x31
      w0 w2 w3 w5 w6 w7 w8 w9 w10 w11 w13 w14 w15 w16 w17
      MU WM MU0 WM0 MI OUT DTB STK FR SBH BL BSS BSE LEN1 HJ HPE HDL HBC HP K.
    facts R1 R2 R3 TL RSV LO SPB KLO. subst dl.
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (KF : 0 <= j <= 4294967296 /\ 0 <= pe - j <= 4294967296) by (clear - HJ HPE GF2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2).
    destruct (Z_le_gt_dec bc 64) as [B64|B64].
    - destruct (HP B64) as (off & -> & HO).
      kx_autoFLA FR (@nil kza) [0xa21c8; 0xa23c4; 0xa23b4] 30%nat
        [KZRange bc 0 64; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange (pe - j) 0 4294967296; KZRange (dcap - j) 0 4294967296; KZRange DST 4096 140737488355328;
         KZRange S 4096 140737488355328; KZRange DT 4096 140737488338940;
         KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535; KZRange SPV 17594333495296 140737488355328]
        [(SPV + -408, 152)] [(SPV - 576, 576)].
      all: aside.
      all: kit_sh_fix.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa23c4) _ _ _ _) => eapply (x42_z4_3 mb); lside; first [exact K | reflexivity]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa21c8) _ _ _ _) =>
               eapply (x42_p4_3 (Z.to_nat pe) mb); lside; first [exact K | exact HO | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa23b4) _ _ _ _) =>
               eapply (x42_g4_3 mb); lside; first [exact K | reflexivity | lia]
           end.
    - kx_autoFLA FR (@nil kza) [0xa21c8; 0xa23c4; 0xa23b4] 30%nat
        [KZRange bc 65 2147483647; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange (pe - j) 0 4294967296; KZRange (dcap - j) 0 4294967296; KZRange DST 4096 140737488355328;
         KZRange DT 4096 140737488338940;
         KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535; KZRange SPV 17594333495296 140737488355328]
        [(SPV + -408, 152)] [(SPV - 576, 576)].
      all: aside.
      all: try kx_mem.
      all: kit_sh_fix.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa23c4) _ _ _ _) => eapply (x42_z4_3 mb); lside; first [exact K | reflexivity]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa23b4) _ _ _ _) =>
               eapply (x42_g4_3 mb); lside; first [exact K | reflexivity | lia]
           end.
  Qed.
End DX42B3B.
End CANSEC1.
