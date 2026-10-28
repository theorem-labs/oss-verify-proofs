(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx41 AZ_huf_dx41_4a.
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
(* [comment removed for export] *)
#[local] Ltac kx_wr_at ::=
  lazymatch goal with
  | |- wr_at ?segs ?m ?A ?N =>
      first [ match goal with
              | H : wr_at segs m A ?N0 |- _ => apply (wr_at_sub segs m A N0 A N H); kx_lia
              | H : rw_cells segs m A ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (wr_at_sub segs m A n A N (proj2 H)); kx_lia
              | H : stk segs m A ?hi |- _ => apply (wr_at_sub segs m A (hi - A) A N); [apply (wr_at_stk segs m A hi H); kx_lia | kx_lia | kx_lia]
              end
            | match goal with
              | H : wr_at segs m ?A0 ?N0 |- _ => apply (wr_at_sub segs m A0 N0 A N H); kx_lia
              | H : u8arr segs m ?A0 ?bs |- _ => apply (wr_at_sub segs m A0 (Z.of_nat (length bs)) A N (proj2 H)); kx_lia
              | H : rw_cells segs m ?A0 ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (wr_at_sub segs m A0 n A N (proj2 H)); kx_lia
              | H : stk segs m ?lo ?hi |- _ => apply (wr_at_sub segs m lo (hi - lo) A N); [apply (wr_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
              end ]
  end.
Section CANSEC1. Context {rc : runConstT}.
Section DX41A1.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x41a_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis DHI : dst_hi dcap DST.
  (* [comment removed for export] *)

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -496)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SG41 := ((dcap + 3) / 4).
  Notation x41_b2_stmt := (AZ_huf_dx41.x41_b2_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo dtb).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation WT := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).

  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\ (4096 <= SRC <= 140737488355328) /\
                 (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\ (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\
                 (0 <= rsv <= 255) /\ (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333498016 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  Ltac afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
  Ltac zsfacts :=
    assert (ZS1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS3 : 0 <= SPV - 352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV - 352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV + -352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 136 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV + -360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia).
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 352 \/ SPV - 352 + 96 <= DST) /\ (SPV - 352 + 96 <= DT \/ DT + 16388 <= SPV - 352) /\
                 (DST + dcap <= SPV - 496 \/ SPV - 496 + 496 <= DST))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF5).
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
  Ltac evr := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end); kx_ev_ranges.
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
  Ltac b2side MU WM :=
    first [ eassumption
          | eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; lia]
          | eapply bytes_at_transport; [eassumption | exact MU | cbn [disjoint_from fst snd]; lia]
          | lside ].

  (* [comment removed for export] *)
  Definition x41_t1_stmt : Prop :=
    forall mm rest q dl j S1 S2 n2 bs2 o2 bc2 S3 n3 bs3 o3 bc3 S4 n4 bs4 o4 bc4 (c1 c2 c3 c4 : word) pad4
      (w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168 : word)
      (x5 x6 x10 x12 x13 x17 x20 x26 x27 x28 x29 x30 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
    munch [(DST, DST + dcap); (SPV - 2720, SPV)] m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w40 w48 w56 w64 w72 w80 w88
      (Z_to_bv 64 SG41) (Z_to_bv 64 dl) (Z_to_bv 64 S3) w120 w128 ->
    X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8))
      (Z_to_bv 64 (DST + 2 * SG41)) (Z_to_bv 64 (DST + SG41)) c3 c2 c1 ->
    X41BD4 SPV mm c4 (Z_to_bv 64 bc4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 -> SINVA o2 n2 bc2 -> 0 <= bc2 < 2147483648 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 -> SINVA o3 n3 bc3 -> 0 <= bc3 < 2147483648 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 -> SINVA o4 n4 bc4 -> 0 <= bc4 < 2147483648 ->
    0 <= q -> 6 <= dcap -> 3 * SG41 + q <= dcap -> dl = tl + 256 * rsv -> 0 <= j <= SG41 ->
    evtF bsegs RNG POST (ST 0xa7cbc mm (Z_to_bv 64 (DST + dcap + -3)) x5 x6 (Z_to_bv 64 (DST + 2 * SG41 + q)) (Z_to_bv 64 S3)
      (Z_to_bv 64 (DST + dcap)) x10 (Z_to_bv 64 (DST + j)) x12 x13 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + SG41 + q))
      (Z_to_bv 64 (DST + 3 * SG41 + q)) x17 (Z_to_bv 64 S2) (Z_to_bv 64 bc3) x20 (Z_to_bv 64 bc2) (Z_to_bv 64 (DT + 4))
      (Z_to_bv 64 (DST + 3 * SG41)) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S2 + o2)) x26 x27 x28 x29 x30 x31).

  Definition x41_e1_stmt : Prop :=
    forall mm rest q dl j S1 n1 bs1 o1 bc1 S2 n2 bs2 o2 bc2 S3 n3 bs3 o3 bc3 S4 n4 bs4 o4 bc4 (c1 c2 c3 c4 : word) pad4
      (w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168 : word)
      (x5 x6 x10 x11 x12 x13 x17 x28 x29 x30 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
    munch [(DST, DST + dcap); (SPV - 2720, SPV)] m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w40 w48 w56 w64 w72 w80 w88
      (Z_to_bv 64 SG41) (Z_to_bv 64 dl) (Z_to_bv 64 S3) w120 w128 ->
    X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8))
      (Z_to_bv 64 (DST + 2 * SG41)) (Z_to_bv 64 (DST + SG41)) c3 c2 c1 ->
    X41BD4 SPV mm c4 (Z_to_bv 64 bc4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    bytes_at bsegs mm S1 bs1 -> zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 -> SINVA o1 n1 bc1 -> 0 <= bc1 < 2147483648 ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 -> SINVA o2 n2 bc2 -> 0 <= bc2 < 2147483648 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 -> SINVA o3 n3 bc3 -> 0 <= bc3 < 2147483648 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 -> SINVA o4 n4 bc4 -> 0 <= bc4 < 2147483648 ->
    0 <= q -> 6 <= dcap -> 3 * SG41 + q <= dcap -> dl = tl + 256 * rsv -> 0 <= j <= SG41 -> SG41 - j < 4 ->
    evtF bsegs RNG POST (ST 0xa7b34 mm (Z_to_bv 64 (DST + dcap + -3)) x5 x6 (Z_to_bv 64 (DST + 2 * SG41 + q)) (Z_to_bv 64 S3)
      (Z_to_bv 64 (DST + dcap)) x10 x11 x12 x13 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + SG41 + q))
      (Z_to_bv 64 (DST + 3 * SG41 + q)) x17 (Z_to_bv 64 S2) (Z_to_bv 64 bc3) (Z_to_bv 64 S1) (Z_to_bv 64 bc2) (Z_to_bv 64 (DT + 4))
      (Z_to_bv 64 (DST + 3 * SG41)) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 bc1)
      x28 x29 x30 x31).

  Definition x41_l1_inv (k : nat) : Prop :=
    forall mm rest q dl j S1 n1 bs1 o1 bc1 S2 n2 bs2 o2 bc2 S3 n3 bs3 o3 bc3 S4 n4 bs4 o4 bc4 (c1 c2 c3 c4 : word) pad4
      (w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168 : word)
      (x6 x11 x12 x28 x29 x30 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
    munch [(DST, DST + dcap); (SPV - 2720, SPV)] m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w40 w48 w56 w64 w72 w80 w88
      (Z_to_bv 64 SG41) (Z_to_bv 64 dl) (Z_to_bv 64 S3) w120 w128 ->
    X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8))
      (Z_to_bv 64 (DST + 2 * SG41)) (Z_to_bv 64 (DST + SG41)) c3 c2 c1 ->
    X41BD4 SPV mm c4 (Z_to_bv 64 bc4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    bytes_at bsegs mm S1 bs1 -> zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 -> SINVA o1 n1 bc1 -> 0 <= bc1 <= 64 ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 -> SINVA o2 n2 bc2 -> 0 <= bc2 < 2147483648 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 -> SINVA o3 n3 bc3 -> 0 <= bc3 < 2147483648 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 -> SINVA o4 n4 bc4 -> 0 <= bc4 < 2147483648 ->
    0 <= q -> 6 <= dcap -> 3 * SG41 + q <= dcap -> dl = tl + 256 * rsv -> 0 <= j <= SG41 -> SG41 - j <= 4 * Z.of_nat k -> 4 <= SG41 ->
    evtF bsegs RNG POST (ST 0xa77f8 mm (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 (64 - tl)) x6 (Z_to_bv 64 (DST + 2 * SG41 + q))
      (Z_to_bv 64 S3) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + j)) x11 x12 (Z_to_bv 64 64) (Z_to_bv 64 (DST + j))
      (Z_to_bv 64 (DST + SG41 + q)) (Z_to_bv 64 (DST + 3 * SG41 + q)) (Z_to_bv 64 (DST + SG41 + -3)) (Z_to_bv 64 S2)
      (Z_to_bv 64 bc3) (Z_to_bv 64 S1) (Z_to_bv 64 bc2) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + 3 * SG41))
      (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 bc1) x28 x29 x30 x31).

  Lemma x41_t1 : forall (k : nat) mb mm j pe sh (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 c1 : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x30 x31 : word),
    munch WT mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SB SPV mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 c1 ->
    x5 = Z_to_bv 64 (pe - j) -> x11 = Z_to_bv 64 (DST + j) -> x14 = Z_to_bv 64 (DST + j) -> x17 = Z_to_bv 64 sh ->
    pe - j <= Z.of_nat k -> 0 <= j < pe -> pe <= dcap -> 52 <= sh <= 63 ->
    (forall mm' (y5 y6 y11 y12 y13 y14 y27 y28 : word),
        munch WT mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -496) ->
        X41SB SPV mm' u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 c1 ->
        evtF bsegs RNG POST (ST 0xa7d7c mm' x1 y5 y6 x7 x8 x9 x10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21
                                (Z_to_bv 64 (DT + 4)) x23 x24 x25 x26 y27 y28 SB x30 x31)) ->
    evtF bsegs RNG POST (ST 0xa7ce8 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            (Z_to_bv 64 (DT + 4)) x23 x24 x25 x26 x27 x28 SB x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    induction k as [|k IH]; intros mb mm j pe sh u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 c1
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x30 x31
      MU WM MU0 WM0 MI OUT DTB STK SBK E5 E11 E14 E17 HK HJ HPE HSH K; [exfalso; lia|].
    subst x5 x11 x14 x17.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS3 LO. zsfacts.
    dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. kclean.
    assert (RJ : 1 <= pe - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355327 /\ 1 <= dcap <= 4294967296 /\
                 0 <= pe <= 4294967296 /\ 4096 <= DST + pe <= 140737488355328 /\ 0 <= dcap - pe <= 4294967296 /\ 1 <= dcap - j <= 4294967296) by (clear - HJ HPE R1; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4 & RJ5 & RJ6 & RJ7 & RJ8).
    kx_autoFLA SBK [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 352) 96] [0xa7ce8; 0xa7d7c] 60%nat
      [KZRange (pe - j) 1 4294967296; KZRange (dcap - j) 1 4294967296; KZRange j 0 4294967296; KZRange pe 0 4294967296; KZRange (dcap - pe) 0 4294967296; KZRange dcap 1 4294967296;
       KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355327; KZRange (DST + pe) 4096 140737488355328;
       KZRange DT 4096 140737488338940; KZRange sh 52 63; KZRange SPV 17594333498016 140737488355328;
       KZWr DST dcap;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 352) 96; KZDisj DST dcap (SPV - 496) 496; KZDisj (SPV - 352) 96 DT 16388]
      [(DT, 16388); (SPV + -352, 96)] [(DT, 16388); (DST, dcap); (SPV - 496, 496)].
    all: [> aside ..].
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear DJF1 DJF2 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8.
    all: [> kx_gen_regsF [6%nat; 12%nat; 13%nat; 27%nat; 28%nat] ..].
    all: [> intros; evr; kx_mem ..].
    all: [> kx_strip_mod ..].
    all: [> lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7d7c) _ _ _ _) => eapply K; lside
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7ce8) _ _ _ _) => eapply (IH mb _ (j + 1) pe sh); lside; first [exact K | idtac]
         end ..].
  Qed.

  (* [comment removed for export] *)
  Lemma x41_ts1 : x41_b2_stmt -> x41_t1_stmt.
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros XB2. unfold AZ_huf_dx41.x41_b2_stmt in XB2. unfold x41_t1_stmt.
    intros mm rest q dl j S1 S2 n2 bs2 o2 bc2 S3 n3 bs3 o3 bc3 S4 n4 bs4 o4 bc4 c1 c2 c3 c4 pad4
      w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168 x5 x6 x10 x12 x13 x17 x20 x26 x27 x28 x29 x30 x31
      SV JK MU0 WM0 MI OUT DTB STK SA SH SBK B4 BS2 L2 S2L S2H N2 SI2 BC2 BS3 L3 S3L S3H N3 SI3 BC3 BS4 L4 S4L S4H N4 SI4 BC4
      HQ HD6 HSG HDL HJ.
    subst dl. facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS3 LO. zsfacts. kclean.
    remember ((dcap + 3) / 4) as pe eqn:HPE.
    assert (RJ : 2 <= pe <= 4294967296 /\ 0 <= j <= 4294967296 /\ 0 <= pe - j <= 4294967296 /\ 4096 <= DST + j <= 140737488355328 /\
                 4096 <= DST + pe <= 140737488355328 /\ pe <= dcap) by (subst pe; clear - HJ HD6 HSG HQ R1; Z.div_mod_to_equations; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4 & RJ5 & RJ6).
    kx_autoFLA (SA, SH, SBK) [KAApp (SPV - 496) 240] [0xa7ce8; 0xa7d7c] 30%nat
      [KZRange j 0 4294967296; KZRange pe 2 4294967296; KZRange (pe - j) 0 4294967296; KZRange DST 4096 140737488355328;
       KZRange (DST + j) 4096 140737488355328; KZRange (DST + pe) 4096 140737488355328;
       KZRange tl 1 12; KZRange rsv 0 255; KZRange SPV 17594333498016 140737488355328]
      [(SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96)] [(SPV - 496, 496)].
    all: [> aside ..].
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear DJF1 DJF2 DJF5; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8.
    all: [> lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7d7c) _ _ _ _) => subst pe; eapply XB2; b2side MU0 WM0
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7ce8) _ _ _ _) =>
             kit_sh_fix; eapply (x41_t1 (Z.to_nat (pe - j)) mm mm j pe);
             first [ apply munch_refl | apply wmono_refl | lside ];
             lazymatch goal with
             | |- forall _, _ =>
                 intros mm' y5 y6 y11 y12 y13 y14 y27 y28 MU' WM' MU0' WM0' MI' OUT' DTB' STK' SB';
                 subst pe; eapply XB2; b2side MU' WM'
             | |- _ => idtac
             end
         end ..].
  Qed.
End DX41A1.
End CANSEC1.
