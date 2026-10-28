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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42 AZ_huf_dx42_1a AZ_huf_dx42_1b AZ_huf_dx42_1d AZ_huf_dx42_1f.
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
Section DX42B1G.
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
  Notation FRS2 mm S pe w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w12 w13 w14 w15 w17 :=
    (FRS mm w0 w1 w2 w3 w4 w5 (Z_to_bv 64 (DST + pe)) w7 w8 w9 w10 (Z_to_bv 64 (S + 8)) w12 w13 w14 w15 (Z_to_bv 64 tl) w17 (Z_to_bv 64 (DT + 4))).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation WD2 := [(DST, DST + dcap); (SPV - 408, SPV - 256)].
  Notation WD1 := [(DST, DST + dcap); (SPV - 408, SPV - 256)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation ZFL := (Z_to_bv 64 AG_huf_BIT_reloadDStream_zeroFilled).
  Notation x42_end := (AZ_huf_dx42.x42_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation K2 mb dl S x9 x10 x12 x13 x18 x19 x23 x25 w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w12 w13 w14 w15 w17 pe :=
    (forall mm' (y1 y5 y7 y8 y11 y14 y15 y16 y17 y29 y30 y31 : word),
        munch WD2 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRS2 mm' S pe w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w12 w13 w14 w15 w17 ->
        evtF bsegs RNG POST (ST 0xa1648 mm' y1 y5 (Z_to_bv 64 tl) y7 y8 x9 x10 y11 x12 x13 y14 y15 y16 y17 x18 w7 (Z_to_bv 64 S) x9 w9 x23
                                (Z_to_bv 64 dl) x25 x19 SB w4 y29 y30 y31)).
  Notation K1 mb dl S x1 x6 x10 x13 x15 x18 x19 x20 x22 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 :=
    (forall mm' (y5 y7 y8 y9 y11 y12 y14 y16 y17 y21 y25 y26 y30 y31 c' : word),
        munch WD1 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRS mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 (Z_to_bv 64 (S + 8)) w11 w12 w13 w14 w15 (Z_to_bv 64 tl) c' (Z_to_bv 64 (DT + 4)) ->
        evtF bsegs RNG POST (ST 0xa0738 mm' x1 y5 x6 y7 y8 y9 x10 y11 y12 x13 y14 x15 y16 y17 x18 x19 x20 y21 x22
                                (Z_to_bv 64 S) (Z_to_bv 64 dl) y25 y26 SB w4 x6 y30 y31)).

  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333497904 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
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
                   (SPV - 256 + 40 <= S \/ S + len <= SPV - 256) /\ (SPV - 408 + 152 <= S \/ S + len <= SPV - 408))
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
  (* [comment removed for export] *)
  Notation x42_c4_1 := (AZ_huf_dx42_1b.x42_c4_1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x42_5loop_1 := (AZ_huf_dx42_1d.x42_5loop_1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x42_4loop_1 := (AZ_huf_dx42_1f.x42_4loop_1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  (* [comment removed for export] *)
  Ltac to_c4 mb K :=
    eapply (x42_c4_1 mb); lside;
    first [ exact K
          | let B := fresh "B" in intro B;
            first [ exfalso; lia
                  | lazymatch goal with
                    | |- exists o, Z_to_bv 64 ?X = Z_to_bv 64 (?S0 + o) /\ _ => exists (X - S0); split; [f_equal; lia | unfold SINVA; lia]
                    end ] ].

  (* [comment removed for export] *)
  Lemma x42_s4_1 : forall mb mm j pe dl P S len bs bc (cont : word)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x30 x31 : word)
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 : word),
    munch WD1 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRS mm (Z_to_bv 64 dl) w1 w2 w3 w4 w5 w6 w7 w8 w9 (Z_to_bv 64 (S + 8)) w11 w12 w13 w14 w15 (Z_to_bv 64 tl) cont (Z_to_bv 64 (DT + 4)) ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= pe -> pe <= dcap -> pe - j < 8 -> dl = tl + 256 * rsv -> 0 <= bc < 2147483648 -> (bc <= 64 -> SINVA (P - S) len bc) ->
    K1 mb dl S x1 x6 x10 x13 x15 x18 x19 x20 x22 (Z_to_bv 64 dl) w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 ->
    evtF bsegs RNG POST (ST 0x9fda0 mm x1 x5 x6 x7 x8 (Z_to_bv 64 bc) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (DST + j)) x22
                            (Z_to_bv 64 S) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 P) SB w4 (Z_to_bv 64 dl) x30 x31).
  Proof using CTX X2OK ACTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mb mm j pe dl P S len bs bc cont x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x30 x31
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15
      MU WM MU0 WM0 MI OUT DTB STK FR SBH BL BSS BSE LEN1 HJ HPE RM HDL HBW HS K.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO.
    assert (KF : 0 <= j <= 4294967296 /\ 0 <= pe - j <= 7) by (clear - HJ HPE RM GF2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2).
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; cycle 1.
    - (* [comment removed for export] *)
      kclean.
      kx_autoFLA FR (@nil kza) [0xa0364] 30%nat
        [KZRange bc 65 2147483647; KZRange S 4096 140737488355328; KZRange SPV 17594333495296 140737488355328;
         KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange pe 0 4294967296]
        [(SPV + -408, 152)] [(SPV - 576, 576)].
      all: aside.
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: to_c4 mb K.
    - pose proof (HS B64) as HSI. assert (HBC : 0 <= bc <= 64) by (clear - HBW B64; lia). clear HBW B64.
      assert (O : exists off, P = S + off) by (exists (P - S); lia). destruct O as (off & ->).
      replace (S + off - S) with off in HSI by lia.
      assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - HBC; lia).
      destruct QR as (q & r & Ebc & HQ & HR).
      destruct HSI as [-> | (O1 & O2 & B1)].
      + (* [comment removed for export] *)
        kclean. subst bc.
        kx_autoFLA FR (@nil kza) [0xa0364] 40%nat
          [KZRange (8 * q + r) 0 64; KZRange S 4096 140737488355328; KZRange SPV 17594333495296 140737488355328; KZRange DST 4096 140737488355328;
           KZRange dcap 0 4294967296; KZRange pe 0 4294967296]
          [(SPV + -408, 152)] [(SPV - 576, 576)].
        all: aside.
        all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
        all: to_c4 mb K.
      + assert (KF4 : 8 <= len - off <= 4294967296 /\ 9 <= len <= 4294967296) by (clear - O2 SL32 O1; lia). destruct KF4 as (KF4 & KF3).
        destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
        * assert (KF5 : 1 <= q - off <= 8 /\ 1 <= off <= 7) by (clear - CQ C8 O1 HQ; lia). destruct KF5 as (KF5 & KF6).
          kclean. subst bc.
          kx_autoFLA FR [KAUnp S len] [0xa0364] 120%nat
          [KZRange (pe - j) 0 7; KZRange (dcap - j) 0 4294967296; KZRange (len - off) 8 4294967296; KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange len 9 4294967296; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange (S + off) 4097 140737488355320;
           KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940;
           KZRange SPV 17594333495296 140737488355328; KZDisj DST dcap (SPV - 576) 576; KZWr (SPV - 408) 152; KZDisj (SPV - 408) 152 S len]
          [(S, len); (SPV + -408, 152)] [(S, len); (SPV - 576, 576)].
          all: aside.
          all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
          all: try clear KF5 KF6.
          all: kx_gen_regsF [5%nat; 7%nat; 11%nat; 14%nat; 16%nat; 17%nat]; intros.
          all: evr; kx_mem; kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
          all: try (replace ((8 * q + r) / 8) with q in * by (clear - HQ HR; Z.div_mod_to_equations; lia)).
          all: try (replace (8 * q + r - 8 * q) with r in * by lia).
          all: to_c4 mb K.
        * assert (KF5 : 0 <= off - q <= 7 /\ 1 <= off <= 7) by (clear - CQ C8 O1 HQ; lia). destruct KF5 as (KF5 & KF6).
          kclean. subst bc.
          kx_autoFLA FR [KAUnp S len] [0xa0364] 120%nat
          [KZRange (pe - j) 0 7; KZRange (dcap - j) 0 4294967296; KZRange (len - off) 8 4294967296; KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange len 9 4294967296; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange (S + off) 4097 140737488355320;
           KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940;
           KZRange SPV 17594333495296 140737488355328; KZDisj DST dcap (SPV - 576) 576; KZWr (SPV - 408) 152; KZDisj (SPV - 408) 152 S len]
          [(S, len); (SPV + -408, 152)] [(S, len); (SPV - 576, 576)].
          all: aside.
          all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
          all: try clear KF5 KF6.
          all: kx_gen_regsF [5%nat; 7%nat; 11%nat; 14%nat; 16%nat; 17%nat]; intros.
          all: evr; kx_mem; kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
          all: try (replace ((8 * q + r) / 8) with q in * by (clear - HQ HR; Z.div_mod_to_equations; lia)).
          all: try (replace (8 * q + r - 8 * q) with r in * by lia).
          all: to_c4 mb K.
        * (* [comment removed for export] *)
          assert (KF6 : 8 <= off <= 4294967296) by (clear - C8 O2 SL32; lia).
          kclean. subst bc.
          kx_autoFLA FR [KAUnp S len] [0xa0364] 120%nat
          [KZRange (pe - j) 0 7; KZRange (dcap - j) 0 4294967296; KZRange (len - off) 8 4294967296; KZRange off 8 4294967296; KZRange (off - q) 0 4294967296; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange len 9 4294967296; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange (S + off) 4096 140737488355328;
           KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940;
           KZRange SPV 17594333495296 140737488355328; KZDisj DST dcap (SPV - 576) 576; KZWr (SPV - 408) 152; KZDisj (SPV - 408) 152 S len]
          [(S, len); (SPV + -408, 152)] [(S, len); (SPV - 576, 576)].
          all: aside.
          all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
          all: try clear KF6.
          all: kx_gen_regsF [5%nat; 7%nat; 11%nat; 14%nat; 16%nat; 17%nat]; intros.
          all: evr; kx_mem; kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
          all: try (replace ((8 * q + r) / 8) with q in * by (clear - HQ HR; Z.div_mod_to_equations; lia)).
          all: try (replace (8 * q + r - 8 * q) with r in * by lia).
          all: to_c4 mb K.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_d4s_1 : forall mb mm j pe dl P S len bs bc (cont : word)
      (x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x18 x19 x20 x21 x22 x23 x25 x30 x31 : word)
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 : word),
    munch WD1 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRS mm (Z_to_bv 64 dl) w1 w2 w3 w4 w5 w6 w7 w8 w9 (Z_to_bv 64 (S + 8)) w11 w12 w13 w14 w15 w16 cont (Z_to_bv 64 (DT + 4)) ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2147483648 -> (bc <= 64 -> SINVA (P - S) len bc) ->
    K1 mb dl S x1 x6 x10 x13 x15 x18 x19 x14 x22 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 ->
    evtF bsegs RNG POST (ST 0x9f7f4 mm x1 x5 x6 x7 x8 (Z_to_bv 64 bc) x10 x11 (Z_to_bv 64 S) x13 x14 x15 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe))
                            x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (DST + j)) x25 (Z_to_bv 64 P) SB w4 (Z_to_bv 64 dl) x30 x31).
  Proof using CTX X2OK ACTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mb mm j pe dl P S len bs bc cont x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x18 x19 x20 x21 x22 x23 x25 x30 x31
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16
      MU WM MU0 WM0 MI OUT DTB STK FR SBH BL BSS BSE LEN1 HJ HPE HDL HBW HS K.
    facts R1 R2 R3 TL RSV LO SPB KLO. subst dl.
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (DJFr : SPV - 408 + 152 <= S \/ S + len <= SPV - 408) by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia).
    assert (KF : 0 <= j <= 4294967296 /\ 0 <= pe - j <= 4294967296) by (clear - HJ HPE GF2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2).
    destruct (Z_le_gt_dec bc 64) as [B64|B64].
    - kx_autoFLA FR (@nil kza) [0x9fda0; 0x9fe6c; 0x9f844] 40%nat
        [KZRange bc 0 64; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange (pe - j) 0 4294967296; KZRange (dcap - j) 0 4294967296;
         KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535;
         KZRange S 4096 140737488355328; KZWr (SPV - 408) 152; KZDisj (SPV - 408) 152 S len; KZRange SPV 17594333495296 140737488355328]
        [(SPV + -408, 152)] [(SPV - 576, 576)].
      all: aside.
      all: kit_sh_fix.
      all: kx_mem.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fda0) _ _ _ _) => eapply (x42_s4_1 mb); lside; first [exact K | exact HS | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fe6c) _ _ _ _) =>
               eapply (x42_4loop_1 (Z.to_nat (pe - j)) mb); lside; first [exact K | exact (HS B64) | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9f844) _ _ _ _) =>
               eapply (x42_5loop_1 (Z.to_nat (pe - j)) mb); lside; first [exact K | exact (HS B64) | lia]
           end.
    - kx_autoFLA FR (@nil kza) [0x9fda0; 0xa0364] 40%nat
        [KZRange bc 65 2147483647; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange (pe - j) 0 4294967296; KZRange (dcap - j) 0 4294967296;
         KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535;
         KZRange S 4096 140737488355328; KZWr (SPV - 408) 152; KZDisj (SPV - 408) 152 S len; KZRange SPV 17594333495296 140737488355328]
        [(SPV + -408, 152)] [(SPV - 576, 576)].
      all: aside.
      all: kit_sh_fix.
      all: kx_mem.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fda0) _ _ _ _) => eapply (x42_s4_1 mb); lside; first [exact K | exact HS | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa0364) _ _ _ _) => to_c4 mb K
           end.
  Qed.

  Section C0K.
  Variables (dl pe1 pe2 pe3 : Z) (S1 n1 S2 n2 S3 n3 S4 n4 : Z) (bs1 bs2 bs3 bs4 : list byte) (mb : amem).
  Hypotheses (HDL : dl = tl + 256 * rsv) (PE1 : pe1 = (dcap + 3) / 4) (PE2 : pe2 = 2 * pe1) (PE3 : pe3 = 3 * pe1) (PE4 : pe3 <= dcap).
  Hypotheses (BL1 : zlen bs1 = n1) (SS1 : SRC <= S1) (SE1 : S1 + n1 <= SRC + n) (LN1 : 1 <= n1).
  Hypotheses (BL2 : zlen bs2 = n2) (SS2 : SRC <= S2) (SE2 : S2 + n2 <= SRC + n) (LN2 : 1 <= n2).
  Hypotheses (BL3 : zlen bs3 = n3) (SS3 : SRC <= S3) (SE3 : S3 + n3 <= SRC + n) (LN3 : 1 <= n3).
  Hypotheses (BL4 : zlen bs4 = n4) (SS4 : SRC <= S4) (SE4 : S4 + n4 <= SRC + n) (LN4 : 1 <= n4).
  Notation WDM := [(DST, DST + dcap); (SPV - 576, SPV - 104)].
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRA mm j0 d j1 := (rw_cells bsegs mm (SPV + -576) [CB 40 j0; C8 d; CB 120 j1]).
  Notation FRJ mm j2 := (rw_cells bsegs mm (SPV + -216) [CB 112 j2]).
  Hypothesis HK1 : forall mb mm j pe dl P S len bs bc (cont : word)
      (x5 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x21 x23 x25 x26 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w12 w13 w14 w15 w17 : word),
    munch WD2 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRS2 mm S pe w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w12 w13 w14 w15 w17 ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2147483648 -> (bc <= 64 -> SINVA (P - S) len bc) ->
    K2 mb dl S x9 x10 x12 x13 x18 x19 x23 x25 w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w12 w13 w14 w15 w17 pe ->
    evtF bsegs RNG POST (ST 0xa0738 mm (Z_to_bv 64 bc) x5 cont x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (DST + j))
                            x16 x17 x18 x19 (Z_to_bv 64 S) x21 (Z_to_bv 64 P) x23 (Z_to_bv 64 dl) x25 x26 SB w4 cont x30 x31).
  Hypothesis HK2 : forall (mk mq : amem) (P3 P4 Q3 Q4 f3 f4 : Z) (c3 c4 : word) (pad4 j0 j1 j2 : list byte)
      (w2 w3 w5 w8 w13 w14 y9 y12 y25 c' : word),
    munch WDM mb mk -> wmono bsegs mb mk -> munch WD1 mk mq -> wmono bsegs mk mq ->
    munch WDM mb mq -> wmono bsegs mb mq ->
    FRA mk j0 (Z_to_bv 64 dcap) j1 ->
    BD4 mk c4 (Z_to_bv 64 f4) pad4 (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mk j2 ->
    bytes_at bsegs mk S3 bs3 -> bytes_at bsegs mk S4 bs4 ->
    (f3 <= 64 -> SINVA (Q3 - S3) n3 f3) -> 0 <= f3 < 2^31 -> S3 <= Q3 <= S3 + n3 ->
    (f4 <= 64 -> SINVA (Q4 - S4) n4 f4) -> 0 <= f4 < 2^31 -> S4 <= Q4 <= S4 + n4 ->
    P3 <= DST + dcap -> DST + pe2 <= P3 -> DST + pe3 <= P4 -> P4 <= DST + dcap -> P3 <= DST + pe3 ->
    K2 mq dl S2 y9 (Z_to_bv 64 P4) y12 (Z_to_bv 64 P3) (Z_to_bv 64 f3) c3 (Z_to_bv 64 S1) y25
       (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) w2 w3 (Z_to_bv 64 (DST + pe3)) w5 (Z_to_bv 64 S3) w8 (Z_to_bv 64 (DST + dcap - 7))
       (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S3 + 8)) w13 w14 (Z_to_bv 64 Q3) c' pe2.
  Lemma x42_d4_1 :
    (forall (mm' : amem) (P1 P2 P3 P4 Q1 Q2 Q3 Q4 f1 f2 f3 f4 : Z) (c1 c2 c3 c4 : word) (pad4 j0 j1 j2 : list byte)
            (w1 w2 w3 w5 w8 w13 w14 w16 : word)
            (y5 y7 y8 y11 y20 y21 y23 y25 y30 y31 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRA mm' j0 (Z_to_bv 64 dcap) j1 ->
        FRS mm' (Z_to_bv 64 dl) w1 w2 w3 (Z_to_bv 64 (DST + pe3)) w5 (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) w8
                (Z_to_bv 64 (DST + dcap - 7)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) w13 w14
                (Z_to_bv 64 Q3) w16 c1 (Z_to_bv 64 (DT + 4)) ->
        BD4 mm' c4 (Z_to_bv 64 f4) pad4 (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mm' j2 ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        (f1 <= 64 -> SINVA (Q1 - S1) n1 f1) -> 0 <= f1 < 2^31 -> S1 <= Q1 <= S1 + n1 ->
        (f2 <= 64 -> SINVA (Q2 - S2) n2 f2) -> 0 <= f2 < 2^31 -> S2 <= Q2 <= S2 + n2 ->
        (f3 <= 64 -> SINVA (Q3 - S3) n3 f3) -> 0 <= f3 < 2^31 -> S3 <= Q3 <= S3 + n3 ->
        (f4 <= 64 -> SINVA (Q4 - S4) n4 f4) -> 0 <= f4 < 2^31 -> S4 <= Q4 <= S4 + n4 ->
        DST <= P1 -> P1 <= DST + dcap -> P2 <= DST + dcap -> P3 <= DST + dcap ->
        DST + pe1 <= P2 -> DST + pe2 <= P3 -> DST + pe3 <= P4 -> P4 <= DST + dcap ->
        P1 <= DST + pe1 -> P2 <= DST + pe2 -> P3 <= DST + pe3 ->
        evtF bsegs RNG POST (ST 0x9f7f4 mm' (Z_to_bv 64 f2) y5 c2 y7 y8 (Z_to_bv 64 f1) (Z_to_bv 64 P4) y11 (Z_to_bv 64 S1)
                                (Z_to_bv 64 P3) (Z_to_bv 64 S2) (Z_to_bv 64 P2) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1))
                                (Z_to_bv 64 f3) c3 y20 y21 (Z_to_bv 64 Q2) y23 (Z_to_bv 64 P1) y25 (Z_to_bv 64 Q1) SB
                                (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 dl) y30 y31)).
  Proof using CTX X2OK ACTX HDL PE1 PE2 PE3 PE4 BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4 HK1 HK2.
    pose proof CTX as CTX'. x42b_ctx_open CTX'.
    intros mm P1 P2 P3 P4 Q1 Q2 Q3 Q4 f1 f2 f3 f4 c1 c2 c3 c4 pad4 j0 j1 j2 w1 w2 w3 w5 w8 w13 w14 w16
      y5 y7 y8 y11 y20 y21 y23 y25 y30 y31
      MUM WMM MU0 WM0 MI OUT DTB STK FA FR B4 FJ SB1 SB2 SB3 SB4 HS1 HF1 HQ1 HS2 HF2 HQ2 HS3 HF3 HQ3 HS4 HF4 HQ4
      HP1 HU1 HU2 HU3 HP2 HP3 HP4 HP5 HE1 HE2 HE3.
    assert (PEF : 0 <= pe1 /\ pe2 = 2 * pe1 /\ pe3 = 3 * pe1 /\ pe3 <= dcap) by (clear - HP1 HE1 PE2 PE3 PE4; lia).
    replace (Z_to_bv 64 P1) with (Z_to_bv 64 (DST + (P1 - DST))) by (f_equal; lia).
    eapply (x42_d4s_1 mm mm (P1 - DST) pe1 dl Q1 S1 n1 bs1 f1 c1 (Z_to_bv 64 f2) y5 c2 y7 y8 (Z_to_bv 64 P4) y11 (Z_to_bv 64 P3) (Z_to_bv 64 S2)
              (Z_to_bv 64 P2) (Z_to_bv 64 f3) c3 y20 y21 (Z_to_bv 64 Q2) y23 y25 y30 y31
              w1 w2 w3 (Z_to_bv 64 (DST + pe3)) w5 (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) w8 (Z_to_bv 64 (DST + dcap - 7))
              (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) w13 w14 (Z_to_bv 64 Q3) w16);
      [ apply munch_refl | apply wmono_refl | exact MU0 | exact WM0 | exact MI | exact OUT | exact DTB | exact STK | exact FR | exact SB1
      | exact BL1 | exact SS1 | exact SE1 | exact LN1 | clear - HP1 HE1; lia | clear - PEF; lia | exact HDL | exact HF1 | exact HS1 | ].
    intros mm2 z5 z7 z8 z9 z11 z12 z14 z16 z17 z21 z25 z26 z30 z31 c' MU1 WM1 MU01 WM01 MI1 OUT1 DTB1 STK1 FR1.
    assert (BS2 : bytes_at bsegs mm2 S2 bs2)
      by (eapply (bytes_at_transport bsegs _ mm mm2 _ _ SB2 MU1); cbn [disjoint_from]; clear - BL2 SS2 SE2 LN2 DJ1 OS2 LO; repeat split; lia).
    replace (Z_to_bv 64 P2) with (Z_to_bv 64 (DST + (P2 - DST))) by (f_equal; lia).
    eapply (HK1 mm2 mm2 (P2 - DST) pe2 dl Q2 S2 n2 bs2 f2 c2 z5 z7 z8 z9 (Z_to_bv 64 P4) z11 z12 (Z_to_bv 64 P3) z14 z16 z17
              (Z_to_bv 64 f3) c3 z21 (Z_to_bv 64 S1) z25 z26 z30 z31
              (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) w2 w3 (Z_to_bv 64 (DST + pe3)) w5 (Z_to_bv 64 S3) w8 (Z_to_bv 64 (DST + dcap - 7))
              (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S3 + 8)) w13 w14 (Z_to_bv 64 Q3) c');
      [ apply munch_refl | apply wmono_refl | exact MU01 | exact WM01 | exact MI1 | exact OUT1 | exact DTB1 | exact STK1 | exact FR1 | exact BS2
      | exact BL2 | exact SS2 | exact SE2 | exact LN2 | clear - PEF HP1 HE1 HP2 HE2; lia | clear - PEF; lia | exact HDL | exact HF2 | exact HS2 | ].
    assert (MUQ : munch WDM mb mm2)
      by (eapply (munch_trans WDM mb mm mm2 MUM); eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; clear; intros; lia).
    assert (WMQ : wmono bsegs mb mm2) by (eapply wmono_trans; [exact WMM | exact WM1]).
    apply (HK2 mm mm2 P3 P4 Q3 Q4 f3 f4 c3 c4 pad4 j0 j1 j2 w2 w3 w5 w8 w13 w14 z9 z12 z25 c'); assumption.
  Qed.
  End C0K.
End DX42B1G.
End CANSEC1.
