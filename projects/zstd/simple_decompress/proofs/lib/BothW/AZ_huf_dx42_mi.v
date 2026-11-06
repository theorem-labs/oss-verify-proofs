(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42 AZ_huf_dx42_mh AZ_huf_dx42_md1 AZ_huf_dx42_md2 AZ_huf_dx42_md3 AZ_huf_dx42_md4 AZ_huf_dx42_mr0000 AZ_huf_dx42_mr0001 AZ_huf_dx42_mr0010 AZ_huf_dx42_mr0011 AZ_huf_dx42_mr0100 AZ_huf_dx42_mr0101 AZ_huf_dx42_mr0110 AZ_huf_dx42_mr0111 AZ_huf_dx42_mr1000 AZ_huf_dx42_mr1001 AZ_huf_dx42_mr1010 AZ_huf_dx42_mr1011 AZ_huf_dx42_mr1100 AZ_huf_dx42_mr1101 AZ_huf_dx42_mr1110 AZ_huf_dx42_mr1111.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
Section DX42MI.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis HRL : huf_reload_int_stmtA.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2608 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STC ra mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 (SPV + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 678828) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 :=
    (rw_cells bsegs mm (SPV + -384) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -264) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -184) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -144) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 2608, SPV)].
  Notation WD4 := [(DST, DST + dcap); (SPV - 264, SPV - 224); (SPV - 400, SPV - 384)].
  Notation WD3 := [(DST, DST + dcap); (SPV - 224, SPV - 184); (SPV - 400, SPV - 384)].
  Notation WD2 := [(DST, DST + dcap); (SPV - 184, SPV - 144); (SPV - 400, SPV - 384)].
  Notation WD1 := [(DST, DST + dcap); (SPV - 144, SPV - 104); (SPV - 296, SPV - 280); (SPV - 400, SPV - 384)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  (* [comment removed for export] *)
  Variables (dl pe1 pe2 pe3 sh nd : Z) (S1 n1 S2 n2 S3 n3 S4 n4 : Z) (bs1 bs2 bs3 bs4 : list byte) (mb : amem).
  Hypothesis HDL : dl = tl + 256 * rsv.
  Hypothesis PE1 : pe1 = (dcap + 3) / 4.
  Hypothesis PE2 : pe2 = 2 * pe1.
  Hypothesis PE3 : pe3 = 3 * pe1.
  Hypothesis PE4 : pe3 <= dcap.
  Hypothesis HSH : sh = 64 - tl.
  Hypothesis HND : nd = -1 * DT + -5.
  Hypothesis BL1 : zlen bs1 = n1.  Hypothesis SS1 : SRC <= S1.  Hypothesis SE1 : S1 + n1 <= SRC + n.  Hypothesis LN1 : 1 <= n1.
  Hypothesis BL2 : zlen bs2 = n2.  Hypothesis SS2 : SRC <= S2.  Hypothesis SE2 : S2 + n2 <= SRC + n.  Hypothesis LN2 : 1 <= n2.
  Hypothesis BL3 : zlen bs3 = n3.  Hypothesis SS3 : SRC <= S3.  Hypothesis SE3 : S3 + n3 <= SRC + n.  Hypothesis LN3 : 1 <= n3.
  Hypothesis BL4 : zlen bs4 = n4.  Hypothesis SS4 : SRC <= S4.  Hypothesis SE4 : S4 + n4 <= SRC + n.  Hypothesis LN4 : 1 <= n4.
  (* [comment removed for export] *)
  Notation WDM := [(DST, DST + dcap); (SPV - 384, SPV - 104)].
  Notation Q61 := (Z_to_bv 64 2305843009213693952).
  (* [comment removed for export] *)
  Notation K0 :=
    (forall (mm' : amem) (P1 P2 P3 P4 Q1 Q2 Q3 Q4 f1 f2 f3 f4 : Z) (c1' c2' c3' c4' : word) (pad1' pad2' pad3' pad4' : list byte)
            (w0 w4 w5 w7 w8 w11 w12 : word)
            (y1 y5 y6 y7 y8 y10 y11 y13 y14 y15 y16 y20 y22 y23 y24 y25 y26 y27 y28 y29 y31 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -384) ->
        FRS mm' w0 (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8
                (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 (DST + pe2)) w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap) ->
        BD1 mm' c1' (Z_to_bv 64 f1) pad1' (Z_to_bv 64 Q1) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
        BD2 mm' c2' (Z_to_bv 64 f2) pad2' (Z_to_bv 64 Q2) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
        BD3 mm' c3' (Z_to_bv 64 f3) pad3' (Z_to_bv 64 Q3) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
        BD4 mm' c4' (Z_to_bv 64 f4) pad4' (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        (f1 <= 64 -> SINVA (Q1 - S1) n1 f1) -> 0 <= f1 < 2147483648 -> S1 <= Q1 <= S1 + n1 ->
        (f2 <= 64 -> SINVA (Q2 - S2) n2 f2) -> 0 <= f2 < 2147483648 -> S2 <= Q2 <= S2 + n2 ->
        (f3 <= 64 -> SINVA (Q3 - S3) n3 f3) -> 0 <= f3 < 2147483648 -> S3 <= Q3 <= S3 + n3 ->
        (f4 <= 64 -> SINVA (Q4 - S4) n4 f4) -> 0 <= f4 < 2147483648 -> S4 <= Q4 <= S4 + n4 ->
        DST <= P1 -> P1 <= DST + dcap -> P2 <= DST + dcap -> P3 <= DST + dcap ->   (* [comment removed for export] *)
        DST + pe1 <= P2 -> DST + pe2 <= P3 -> DST + pe3 <= P4 -> P4 <= DST + dcap ->
        evtF bsegs RNG POST (ST 0xa74b4 mm' y1 y5 y6 y7 y8 (Z_to_bv 64 P4) y10 y11 (Z_to_bv 64 P1) y13 y14 y15 y16
                                (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 P3) (Z_to_bv 64 P2) y20 SB y22 y23 y24 y25 y26 y27 y28 y29
                                (Z_to_bv 64 (DT + 4)) y31)).

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
    assert (AW0 : aappW [(SPV - 2608, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 400) 400) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
                   (SPV - 264 + 160 <= S \/ S + len <= SPV - 264) /\ (SPV - 400 + 136 <= S \/ S + len <= SPV - 400))
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
    assert (FF : (DST + dcap <= SPV - 400 \/ SPV - 400 + 136 <= DST) /\ (DST + dcap <= SPV - 264 \/ SPV - 264 + 160 <= DST) /\
                 (SPV - 264 + 160 <= DT \/ DT + 16388 <= SPV - 264) /\ (SPV - 400 + 136 <= DT \/ DT + 16388 <= SPV - 400) /\
                 (DST + dcap <= SPV - 400 \/ SPV - 400 + 400 <= DST))
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
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 706616) _ _ _ _) => kx_trap_fast end).
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
  Ltac kx_lia_or1 :=
    match goal with
    | H : _ \/ _ |- _ =>
        solve [ repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end;
                repeat match goal with H' : _ -> _ |- _ => clear H' end; lia ]
    end.
  Ltac kx_lia_m1 := first [ solve [kx_clear_or; lia] | solve [kx_lia_or1] | kx_bv_ranges; solve [kx_clear_or; lia] | solve [kx_bv_ranges; kx_lia_or1] ].
  (* [comment removed for export] *)
  Ltac mdh_hyp := lazymatch goal with |- ?G => match goal with H : G |- _ => exact H | H : mdh G |- _ => exact H end end.
  Ltac kx_lia_m2 :=
    lazymatch goal with
    | |- _ /\ _ => first [ mdh_hyp | solve [kx_clear_or; lia] | split; kx_lia_m2 ]
    | |- _ \/ _ => first [ mdh_hyp | kx_lia_m1 ]
    | |- _ <= _ <= _ => first [ mdh_hyp | kx_lia_m1 ]
    | |- _ => kx_lia_m1
    end.
  #[local] Ltac kx_lia ::= kx_lia_m2.
  #[local] Ltac kxl_lia ::= first [ mdh_hyp | kx_lia_m2 ].
  #[local] Ltac kxl_hyp ::= mdh_hyp.
  #[local] Ltac kxa_hyp ::= mdh_hyp.
  (* [comment removed for export] *)
  Ltac evw := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end);
    repeat match goal with
    | KXK : know_ok _ ?E _ _ |- context [ev ?E ?j] =>
        lazymatch goal with
        | _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail
        | _ => let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H
        end
    end.
  (* [comment removed for export] *)
  Ltac kside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- _ <= bv_unsigned (ev _ ?j) <= _ =>
        first [ assumption
              | let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H; clear - H; lia ]
    | |- _ <= _ <= _ => first [assumption | kx_lia_m1]
    | |- @eq Z _ _ => first [reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- _ => first [eassumption | kx_lia_m1]
    end.
  (* [comment removed for export] *)
  #[local] Ltac kxl_wr_exact ::=
    lazymatch goal with
    | |- wr_at ?segs ?m ?A ?N =>
        match goal with
        | H : wr_at segs m A N |- _ => exact H
        | H : rw_cells segs m A ?cs |- _ => let n := eval lazy in (Z.of_nat (cells_size cs)) in lazymatch n with N => exact (proj2 H) end
        end
    end.
  (* [comment removed for export] *)
  Ltac lclean2 :=
    repeat match goal with
           | H : ?A \/ _ |- _ => lazymatch A with _ = 0 => fail | _ => clear H end
           | H : mdh _ |- _ => clear H
           | H : rng _ _ _ |- _ => clear H
           | H : rng_aimg _ |- _ => clear H
           | H : 4096 <= _ <= _ |- _ => clear H
           | H : 17594333495296 <= _ <= _ |- _ => clear H
           | H : 17594333497904 <= _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac aclean :=
    repeat match goal with
           | H : unpZ _ _ _ |- _ => clear H
           | H : unpoisoned _ _ _ |- _ => clear H
           | H : rng _ (KXSHLO + _ / 8) _ |- _ => clear H
           | H : rng _ (shad _) _ |- _ => clear H
           | H : aappW _ |- _ => clear H
           | H : _ + _ <= _ \/ _ + _ <= _ |- _ => clear H
           | H : _ + _ + _ <= _ \/ _ + _ <= _ + _ |- _ => clear H
           end.
  Notation x42_md1 := (AZ_huf_dx42_md1.x42_md1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_md2 := (AZ_huf_dx42_md2.x42_md2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_md3 := (AZ_huf_dx42_md3.x42_md3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_md4 := (AZ_huf_dx42_md4.x42_md4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0000 := (AZ_huf_dx42_mr0000.x42_mr0000 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0001 := (AZ_huf_dx42_mr0001.x42_mr0001 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0010 := (AZ_huf_dx42_mr0010.x42_mr0010 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0011 := (AZ_huf_dx42_mr0011.x42_mr0011 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0100 := (AZ_huf_dx42_mr0100.x42_mr0100 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0101 := (AZ_huf_dx42_mr0101.x42_mr0101 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0110 := (AZ_huf_dx42_mr0110.x42_mr0110 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0111 := (AZ_huf_dx42_mr0111.x42_mr0111 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1000 := (AZ_huf_dx42_mr1000.x42_mr1000 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1001 := (AZ_huf_dx42_mr1001.x42_mr1001 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1010 := (AZ_huf_dx42_mr1010.x42_mr1010 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1011 := (AZ_huf_dx42_mr1011.x42_mr1011 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1100 := (AZ_huf_dx42_mr1100.x42_mr1100 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1101 := (AZ_huf_dx42_mr1101.x42_mr1101 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1110 := (AZ_huf_dx42_mr1110.x42_mr1110 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1111 := (AZ_huf_dx42_mr1111.x42_mr1111 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).

  (* [comment removed for export] *)
  Lemma x42_it : forall mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 (k1 k2 k3 k4 : word) (pad1 pad2 pad3 pad4 : list byte)
      (x8 x10 x11 x13 x17 x22 x25 x27 x28 x29 : word)
      (w0 w4 w5 w7 : word),
    munch WDM mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -384) ->
    (FRS mm w0 (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 k2 (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 (DST + pe2)) k4 k3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
    (BD1 mm k1 (Z_to_bv 64 (b1)) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8))) ->
    (BD2 mm k2 (Z_to_bv 64 (b2)) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8))) ->
    (BD3 mm k3 (Z_to_bv 64 (b3)) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8))) ->
    (BD4 mm k4 (Z_to_bv 64 (b4)) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8))) ->
    bytes_at bsegs mm S1 bs1 -> bytes_at bsegs mm S2 bs2 -> bytes_at bsegs mm S3 bs3 -> bytes_at bsegs mm S4 bs4 ->
    HINV o1 n1 b1 -> HINV o2 n2 b2 -> HINV o3 n3 b3 -> HINV o4 n4 b4 ->
    q1 + 8 <= dcap -> q2 + 8 <= dcap -> q3 + 8 <= dcap -> q4 + 8 <= dcap -> 0 <= q1 -> 0 <= q2 -> 0 <= q3 -> 0 <= q4 ->
    pe1 <= q2 -> pe2 <= q3 -> pe3 <= q4 -> 0 <= pe1 ->
    (forall mm' (q1' q2' q3' q4' o1' o2' o3' o4' b1' b2' b3' b4' : Z) (k1' k2' k3' k4' : word) (w0' w4' w5' w7' : word) (y8 y10 y11 y13 y17 y22 y25 y27 y28 y29 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -384) ->
        (FRS mm' w0' (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4' w5' (Z_to_bv 64 (DST + dcap)) w7' k2' (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 (DST + pe2)) k4' k3' (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
        (BD1 mm' k1' (Z_to_bv 64 (b1')) pad1 (Z_to_bv 64 (S1 + o1')) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8))) ->
        (BD2 mm' k2' (Z_to_bv 64 (b2')) pad2 (Z_to_bv 64 (S2 + o2')) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8))) ->
        (BD3 mm' k3' (Z_to_bv 64 (b3')) pad3 (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8))) ->
        (BD4 mm' k4' (Z_to_bv 64 (b4')) pad4 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8))) ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        1 <= o1' -> o1' + 8 <= n1 -> 0 <= b1' <= 7 -> 1 <= o2' -> o2' + 8 <= n2 -> 0 <= b2' <= 7 ->
        1 <= o3' -> o3' + 8 <= n3 -> 0 <= b3' <= 7 -> 1 <= o4' -> o4' + 8 <= n4 -> 0 <= b4' <= 7 ->
        q1 + 4 <= q1' <= q1 + 8 -> q2 + 4 <= q2' <= q2 + 8 -> q3 + 4 <= q3' <= q3 + 8 -> q4 + 4 <= q4' <= q4 + 8 -> q4' + 8 <= dcap ->
        evtF bsegs RNG POST (ST 0xa6094 mm' (Z_to_bv 64 (b2')) (Z_to_bv 64 (2305843009213693952)) (Z_to_bv 64 (sh)) (Z_to_bv 64 (nd)) y8 (Z_to_bv 64 (DST + q4')) y10 y11 (Z_to_bv 64 (DST + q1')) y13 (Z_to_bv 64 (S1 + o1')) (Z_to_bv 64 (S2 + o2')) (Z_to_bv 64 (S3 + o3')) y17 (Z_to_bv 64 (DST + q3')) (Z_to_bv 64 (DST + q2')) (Z_to_bv 64 (b3')) SB y22 k1' (Z_to_bv 64 (b4')) y25 (Z_to_bv 64 (b1')) y27 y28 y29 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (S4 + o4')))) ->
    K0 ->
    evtF bsegs RNG POST (ST 0xa6094 mm (Z_to_bv 64 (b2)) (Z_to_bv 64 (2305843009213693952)) (Z_to_bv 64 (sh)) (Z_to_bv 64 (nd)) x8 (Z_to_bv 64 (DST + q4)) x10 x11 (Z_to_bv 64 (DST + q1)) x13 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) x17 (Z_to_bv 64 (DST + q3)) (Z_to_bv 64 (DST + q2)) (Z_to_bv 64 (b3)) SB x22 k1 (Z_to_bv 64 (b4)) x25 (Z_to_bv 64 (b1)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (S4 + o4))).
  Proof using CTX X2OK ACTX HRL NBOK HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4.
    intros mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 k1 k2 k3 k4 pad1 pad2 pad3 pad4
      x8 x10 x11 x13 x17 x22 x25 x27 x28 x29
      w0 w4 w5 w7
      MU WM MU0 WM0 MI OUT DTB STK FR B1 B2 B3 B4 SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 HQ1 HQ2 HQ3 HQ4 HP1 HP2 HP3 HP4
      HE2 HE3 HE4 HE0 KH KX.
    (* [comment removed for export] *)
    eapply (x42_md1 mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 k1 k2 k3 k4 pad1 pad2 pad3 pad4); [exact MU | exact WM | exact MU0 | exact WM0 | exact MI | exact OUT | exact DTB | exact STK | exact FR | exact B1 | exact B2 | exact B3 | exact B4 | exact SB1 | exact SB2 | exact SB3 | exact SB4 | exact HI1 | exact HI2 | exact HI3 | exact HI4 | exact HQ1 | exact HQ2 | exact HQ3 | exact HQ4 | exact HP1 | exact HP2 | exact HP3 | exact HP4 |].
    intros mm2 c12 c22 c32 c42 l12 l22 l32 l42 w0_2 w4_2 w5_2 w7_2 y11_2 y13_2 y20_2 y27_2 y29_2
      MU2 WM2 MU02 WM02 MI2 OUT2 DTB2 STK2 FR2 B12 B22 B32 B42 SB12 SB22 SB32 SB42 HL1_2 HL2_2 HL3_2 HL4_2 HC1_2 HC2_2 HC3_2 HC4_2.
    (* [comment removed for export] *)
    eapply (x42_md2 mm2 q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 c12 c22 c32 c42 k1 k2 k3 k4 l12 l22 l32 l42 pad1 pad2 pad3 pad4); [exact MU2 | exact WM2 | exact MU02 | exact WM02 | exact MI2 | exact OUT2 | exact DTB2 | exact STK2 | exact FR2 | exact B12 | exact B22 | exact B32 | exact B42 | exact SB12 | exact SB22 | exact SB32 | exact SB42 | exact HI1 | exact HI2 | exact HI3 | exact HI4 | exact HQ1 | exact HQ2 | exact HQ3 | exact HQ4 | exact HP1 | exact HP2 | exact HP3 | exact HP4 | exact HL1_2 | exact HL2_2 | exact HL3_2 | exact HL4_2 | exact HC1_2 | exact HC2_2 | exact HC3_2 | exact HC4_2 |].
    intros mm3 u13 u23 u33 u43 c13 c23 c33 c43 l53 l63 l73 l83 w0_3 w4_3 w5_3 w7_3 y1_3 y11_3 y13_3 y28_3 y29_3
      MU3 WM3 MU03 WM03 MI3 OUT3 DTB3 STK3 FR3 B13 B23 B33 B43 SB13 SB23 SB33 SB43 HL5_3 HL6_3 HL7_3 HL8_3 HU1_3 HU2_3 HU3_3 HU4_3 HC1_3 HC2_3 HC3_3 HC4_3.
    (* [comment removed for export] *)
    eapply (x42_md3 mm3 q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 u13 u23 u33 u43 c13 c23 c33 c43 k1 k2 k3 k4 l53 l63 l73 l83 pad1 pad2 pad3 pad4); [exact MU3 | exact WM3 | exact MU03 | exact WM03 | exact MI3 | exact OUT3 | exact DTB3 | exact STK3 | exact FR3 | exact B13 | exact B23 | exact B33 | exact B43 | exact SB13 | exact SB23 | exact SB33 | exact SB43 | exact HI1 | exact HI2 | exact HI3 | exact HI4 | exact HQ1 | exact HQ2 | exact HQ3 | exact HQ4 | exact HP1 | exact HP2 | exact HP3 | exact HP4 | exact HL5_3 | exact HL6_3 | exact HL7_3 | exact HL8_3 | exact HU1_3 | exact HU2_3 | exact HU3_3 | exact HU4_3 | exact HC1_3 | exact HC2_3 | exact HC3_3 | exact HC4_3 |].
    intros mm4 v14 v24 v34 v44 c14 c24 c34 c44 l94 l104 l114 l124 w0_4 w4_4 w5_4 w7_4 y11_4 y13_4 y26_4 y27_4 y29_4
      MU4 WM4 MU04 WM04 MI4 OUT4 DTB4 STK4 FR4 B14 B24 B34 B44 SB14 SB24 SB34 SB44 HL9_4 HL10_4 HL11_4 HL12_4 HV1_4 HV2_4 HV3_4 HV4_4 HC1_4 HC2_4 HC3_4 HC4_4.
    (* [comment removed for export] *)
    eapply (x42_md4 mm4 q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 v14 v24 v34 v44 c14 c24 c34 c44 k1 k2 k3 k4 l94 l104 l114 l124 pad1 pad2 pad3 pad4); [exact MU4 | exact WM4 | exact MU04 | exact WM04 | exact MI4 | exact OUT4 | exact DTB4 | exact STK4 | exact FR4 | exact B14 | exact B24 | exact B34 | exact B44 | exact SB14 | exact SB24 | exact SB34 | exact SB44 | exact HI1 | exact HI2 | exact HI3 | exact HI4 | exact HQ1 | exact HQ2 | exact HQ3 | exact HQ4 | exact HP1 | exact HP2 | exact HP3 | exact HP4 | exact HL9_4 | exact HL10_4 | exact HL11_4 | exact HL12_4 | exact HV1_4 | exact HV2_4 | exact HV3_4 | exact HV4_4 | exact HC1_4 | exact HC2_4 | exact HC3_4 | exact HC4_4 |].
    intros mm5 r15 r25 r35 r45 c15 c25 c35 c45 l135 l145 l155 l165 w0_5 w4_5 w7_5 y13_5 y22_5 y23_5 y27_5 y28_5 y29_5
      MU5 WM5 MU05 WM05 MI5 OUT5 DTB5 STK5 FR5 B15 B25 B35 B45 SB15 SB25 SB35 SB45 HL13_5 HL14_5 HL15_5 HL16_5 HW1_5 HW2_5 HW3_5 HW4_5 HC1_5 HC2_5 HC3_5 HC4_5.
    (* [comment removed for export] *)
    assert (HRS : (0 <= o1 /\ (o1 = 0 \/ (o1 + 8 <= n1 /\ 8 * (c15 / 8) + c15 mod 8 <= 56)) /\ 0 <= c15 mod 8 <= 7 /\ 0 <= c15 / 8 /\ 8 * (c15 / 8) + c15 mod 8 <= 112) /\
                  (0 <= o2 /\ (o2 = 0 \/ (o2 + 8 <= n2 /\ 8 * (c25 / 8) + c25 mod 8 <= 56)) /\ 0 <= c25 mod 8 <= 7 /\ 0 <= c25 / 8 /\ 8 * (c25 / 8) + c25 mod 8 <= 112) /\
                  (0 <= o3 /\ (o3 = 0 \/ (o3 + 8 <= n3 /\ 8 * (c35 / 8) + c35 mod 8 <= 56)) /\ 0 <= c35 mod 8 <= 7 /\ 0 <= c35 / 8 /\ 8 * (c35 / 8) + c35 mod 8 <= 112) /\
                  (0 <= o4 /\ (o4 = 0 \/ (o4 + 8 <= n4 /\ 8 * (c45 / 8) + c45 mod 8 <= 56)) /\ 0 <= c45 mod 8 <= 7 /\ 0 <= c45 / 8 /\ 8 * (c45 / 8) + c45 mod 8 <= 112)).
    { unfold HINV in HI1, HI2, HI3, HI4.
      pose proof (Z.div_mod c15 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound c15 8 ltac:(lia)) as M1.
      pose proof (Z.div_mod c25 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound c25 8 ltac:(lia)) as M2.
      pose proof (Z.div_mod c35 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound c35 8 ltac:(lia)) as M3.
      pose proof (Z.div_mod c45 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound c45 8 ltac:(lia)) as M4.
      clear - HI1 HI2 HI3 HI4 HC1_5 HC2_5 HC3_5 HC4_5 D1 M1 D2 M2 D3 M3 D4 M4. lia. }
    destruct HRS as ((O1 & HR1 & RR1 & CQ1 & CC1) & (O2 & HR2 & RR2 & CQ2 & CC2) & (O3 & HR3 & RR3 & CQ3 & CC3) & (O4 & HR4 & RR4 & CQ4 & CC4)).
    replace (Z_to_bv 64 c15) with (Z_to_bv 64 (8 * (c15 / 8) + c15 mod 8)) in * by (f_equal; pose proof (Z.div_mod c15 8 ltac:(lia)); lia).
    replace (Z_to_bv 64 c25) with (Z_to_bv 64 (8 * (c25 / 8) + c25 mod 8)) in * by (f_equal; pose proof (Z.div_mod c25 8 ltac:(lia)); lia).
    replace (Z_to_bv 64 c35) with (Z_to_bv 64 (8 * (c35 / 8) + c35 mod 8)) in * by (f_equal; pose proof (Z.div_mod c35 8 ltac:(lia)); lia).
    replace (Z_to_bv 64 c45) with (Z_to_bv 64 (8 * (c45 / 8) + c45 mod 8)) in * by (f_equal; pose proof (Z.div_mod c45 8 ltac:(lia)); lia).
    destruct (Z_lt_le_dec o1 8) as [C1|C1];
      [ destruct (Z_lt_le_dec o2 8) as [C2|C2];
        [ destruct (Z_lt_le_dec o3 8) as [C3|C3];
          [ destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr0000 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4)
            | eapply (x42_mr0001 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4) ]
          | destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr0010 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4)
            | eapply (x42_mr0011 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4) ] ]
        | destruct (Z_lt_le_dec o3 8) as [C3|C3];
          [ destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr0100 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4)
            | eapply (x42_mr0101 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4) ]
          | destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr0110 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4)
            | eapply (x42_mr0111 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4) ] ] ]
      | destruct (Z_lt_le_dec o2 8) as [C2|C2];
        [ destruct (Z_lt_le_dec o3 8) as [C3|C3];
          [ destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr1000 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4)
            | eapply (x42_mr1001 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4) ]
          | destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr1010 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4)
            | eapply (x42_mr1011 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4) ] ]
        | destruct (Z_lt_le_dec o3 8) as [C3|C3];
          [ destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr1100 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4)
            | eapply (x42_mr1101 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4) ]
          | destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr1110 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4)
            | eapply (x42_mr1111 mm5 q1 q2 q3 q4 o1 o2 o3 o4 r15 r25 r35 r45 (c15 / 8) (c15 mod 8) (c25 / 8) (c25 mod 8) (c35 / 8) (c35 mod 8) (c45 / 8) (c45 mod 8) k1 k2 k3 k4 l135 l145 l155 l165 pad1 pad2 pad3 pad4) ] ] ] ].
    all: try first [ exact MU5 | exact WM5 | exact MU05 | exact WM05 | exact MI5 | exact OUT5 | exact DTB5 | exact STK5 | exact FR5
                   | exact B15 | exact B25 | exact B35 | exact B45 | exact SB15 | exact SB25 | exact SB35 | exact SB45 ].
    all: try assumption.
    all: try (clear - C1 C2 C3 C4; lia).
    (* [comment removed for export] *)
    all: try (intros mm' q1' q2' q3' q4' o1' o2' o3' o4' b1' b2' b3' b4' k1' k2' k3' k4' w0' w4' w5' w7' y8 y10 y11 y13 y17 y22 y25 y27 y28 y29
                MU' WM' MU0' WM0' MI' OUT' DTB' STK' FR' B1' B2' B3' B4' SB1' SB2' SB3' SB4' O1a O1b HB1 O2a O2b HB2 O3a O3b HB3 O4a O4b HB4 HT1 HT2 HT3 HT4 HROOM';
              eapply (KH mm' q1' q2' q3' q4' o1' o2' o3' o4' b1' b2' b3' b4' k1' k2' k3' k4' w0' w4' w5' w7');
              first [eassumption | clear - HT1 HT2 HT3 HT4 HROOM' HW1_5 HW2_5 HW3_5 HW4_5 O1a O1b HB1 O2a O2b HB2 O3a O3b HB3 O4a O4b HB4; lia]).
    (* [comment removed for export] *)
    all: try exact KX.
  Qed.
End DX42MI.
End CANSEC1.
