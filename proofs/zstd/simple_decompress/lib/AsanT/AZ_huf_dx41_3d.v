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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_3a AZ_huf_dx41_3c.
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
Section DX41A3.
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
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation SG41 := ((dcap + 3) / 4).
  Notation x41_b4_stmt := (AZ_huf_dx41.x41_b4_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo dtb).
  Notation x41_ts3 := (AZ_huf_dx41_3a.x41_ts3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_l3_d := (AZ_huf_dx41_3c.x41_l3_d RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_l3_inv k := (AZ_huf_dx41_3a.x41_l3_inv RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo dtb k).

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
                   (SPV - 496 + 496 <= S \/ S + len <= SPV - 496))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      destruct SF as (SF0 & SF1 & SL32 & SF2 & DJS & DJK & DJW);
      assert (RS : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia)) as RSz;
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia)) as USz
      end
    end.
  Ltac zsfacts :=
    assert (ZS1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS3 : 0 <= SPV - 360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV - 360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV + -360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia).
  Ltac zsfactsS :=
    lazymatch goal with
    | BSE : ?S + ?len <= SRC + n |- _ =>
        assert (ZS9 : 0 <= S - 0 < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= S < 2 ^ 64) by (kx_clear_or; lia)
    end.
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 496 \/ SPV - 496 + 496 <= DST) /\ (SPV - 496 + 496 <= DT \/ DT + 16388 <= SPV - 496))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2).
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
  Ltac p_fix :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        lazymatch X with DST + _ => idtac | _ => replace X with (DST + (X - DST)) by lia end
    end.
  Ltac o_fix S :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        lazymatch X with S + _ => idtac | _ => replace X with (S + (X - S)) by lia end
    end.
  (* [comment removed for export] *)
  Lemma x41_l3_c : forall (k : nat), (forall j, k = S j -> x41_l3_inv j) -> x41_b4_stmt ->
    forall mm rest q dl PP S1 S2 S3 n3 bs3 o3 bc3 S4 n4 bs4 o4 bc4 (c1 c2 c3 c4 : word) pad4
      (w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168 : word)
      (x10 x12 x13 x14 x15 x18 x20 x25 x26 x27 x28 x29 x30 x31 : word),
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
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 -> SINVA o3 n3 bc3 -> 0 <= bc3 <= 64 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 -> SINVA o4 n4 bc4 -> 0 <= bc4 < 2147483648 ->
    0 <= q -> 6 <= dcap -> 3 * SG41 + q <= dcap -> dl = tl + 256 * rsv -> DST <= PP <= DST + 3 * SG41 ->
    DST + 3 * SG41 - PP <= 4 * Z.of_nat k -> o3 < 8 ->
    evtF bsegs RNG POST (ST 0xa8338 mm (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 (DST + 3 * SG41 + -3)) (Z_to_bv 64 (64 - tl))
      (Z_to_bv 64 PP) (Z_to_bv 64 S3) (Z_to_bv 64 (DST + dcap)) x10 (Z_to_bv 64 PP) x12 x13 x14 x15
      (Z_to_bv 64 (DST + 3 * SG41 + q)) (Z_to_bv 64 64) x18 (Z_to_bv 64 bc3) x20 (Z_to_bv 64 dl) (Z_to_bv 64 (DT + 4))
      (Z_to_bv 64 (DST + 3 * SG41)) (Z_to_bv 64 (S3 + o3)) x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros k IH B4 mm rest q dl PP S1 S2 S3 n3 bs3 o3 bc3 S4 n4 bs4 o4 bc4 c1 c2 c3 c4 pad4
      w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168
      x10 x12 x13 x14 x15 x18 x20 x25 x26 x27 x28 x29 x30 x31
      SV JK MU0 WM0 MI OUT DTB STK SA SH SB BD BS3 L3 S3L S3H N3 SI3 BC3 BS4 L4 S4L S4H N4 SI4 BC4 Q0 D6 QD HDL HPP HK O8.
    subst dl. facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts S3L S3H N3 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO. zsfacts. kclean.
    remember (3 * SG41) as pe eqn:HPE.
    assert (RJ : 4096 <= PP <= 140737488355328 /\ 0 <= DST + pe - PP <= 4294967296 /\ 0 <= PP - DST <= 4294967296 /\
                 0 <= pe <= 4294967296 /\ 4096 <= DST + pe <= 140737488355328 /\ 0 <= q <= 4294967296 /\
                 4096 <= DST + pe + q <= 140737488355328 /\ 6 <= dcap <= 4294967296 /\ 1 <= n3 <= 4294967296)
      by (clear - HPP HPE QD Q0 D6 R1 R2 S3L S3H N3; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4 & RJ5 & RJ6 & RJ7 & RJ8 & RJ9).
    destruct SI3 as [O0 | (O1 & O2 & B1)].
    - subst o3.
      kx_autoFLA (SA, SB, SH) (@nil kza) [0xa840c; 0xa8798] 20%nat
        [KZRange PP 4096 140737488355328; KZRange (DST + pe - PP) 0 4294967296; KZRange (PP - DST) 0 4294967296;
         KZRange pe 0 4294967296; KZRange (DST + pe) 4096 140737488355328; KZRange q 0 4294967296;
         KZRange (DST + pe + q) 4096 140737488355328; KZRange dcap 6 4294967296;
         KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange tl 1 12; KZRange rsv 0 255;
         KZRange bc3 0 64; KZRange SPV 17594333498016 140737488355328;
         KZRange S3 4096 140737488355328; KZRange n3 1 4294967296; KZRange (S3 + n3) 4096 140737488355328]
        [(SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96)] [(SPV - 496, 496)].
      all: [> aside ..].
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJF1 DJF2; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7.
      all: [> lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8798) _ _ _ _) => subst pe; eapply (x41_ts3 B4); lside
           end ..].
    - assert (RO : 1 <= o3 <= 7 /\ 8 <= n3 - o3 <= 4294967296 /\ 9 <= n3 <= 4294967296 /\ 4097 <= S3 + o3 <= 140737488355328)
        by (clear - O1 O2 O8 SF0 SF1 SL32; lia).
      destruct RO as (RO1 & RO2 & RO3 & RO4).
      assert (QR : exists qb rb, bc3 = 8 * qb + rb /\ 0 <= qb <= 8 /\ 0 <= rb <= 7) by (exists (bc3 / 8), (bc3 mod 8); clear - BC3; lia).
      destruct QR as (qb & rb & Ebc & HQB & HRB). subst bc3.
      destruct (Z_lt_le_dec o3 qb) as [CQ|CQ].
      + assert (KF : 1 <= qb - o3 <= 8) by (clear - CQ RO1 HQB; lia).
        kx_autoFLA (SA, SB, SH) [KAUnp S3 n3] [0xa840c; 0xa8798] 80%nat
          [KZRange PP 4096 140737488355328; KZRange (DST + pe - PP) 0 4294967296; KZRange (PP - DST) 0 4294967296;
           KZRange pe 0 4294967296; KZRange (DST + pe) 4096 140737488355328; KZRange q 0 4294967296;
           KZRange (DST + pe + q) 4096 140737488355328; KZRange dcap 6 4294967296;
           KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange tl 1 12; KZRange rsv 0 255;
           KZRange o3 1 7; KZRange (qb - o3) 1 8; KZRange qb 0 8; KZRange rb 0 7; KZRange (8 * qb + rb) 0 64;
           KZRange (n3 - o3) 8 4294967296; KZRange SPV 17594333498016 140737488355328;
           KZRange S3 4096 140737488355328; KZRange n3 9 4294967296; KZRange (S3 + n3) 4096 140737488355328;
           KZRange (S3 + o3) 4097 140737488355328]
          [(S3, n3); (SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96)] [(S3, n3); (SPV - 496, 496)].
        all: [> aside ..].
        all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJF1 DJF2; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7.
        all: [> kx_gen_regsF [8%nat; 12%nat; 13%nat; 14%nat; 15%nat; 26%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
        all: [> intros; evr; kx_mem ..].
        all: [> kx_sx3; rewrite ?(Z.mod_small (8 * qb + rb) (2^64)) in * by lia; kx_land_ranges; kx_strip_mod; land7_lin ..].
        all: try (replace ((8 * qb + rb) / 8) with qb in * by (clear - HQB HRB; Z.div_mod_to_equations; lia)).
        all: [> lazymatch goal with
             | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8798) _ _ _ _) => subst pe; eapply (x41_ts3 B4); lside
             | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa840c) _ _ _ _) =>
                 repeat match goal with
                 | H : bv_unsigned (edenot _ (EAlu ALU_SLTU _ _)) <> 0 |- _ =>
                     kx_sltu_in H; kx_ub_norm H;
                     lazymatch type of H with
                     | Z.b2z (?a <? ?b) <> 0 =>
                         let HL := fresh "HL" in
                         revert H; destruct (a <? b) eqn:HL; intro H; [apply Z.ltb_lt in HL; clear H | exfalso; apply H; reflexivity]
                     end
                 end;
                 subst pe; o_fix S3; eapply (x41_l3_d k IH B4); lside
             end ..].
      + assert (KF : 0 <= o3 - qb <= 7) by (clear - CQ RO1 HQB; lia).
        kx_autoFLA (SA, SB, SH) [KAUnp S3 n3] [0xa840c; 0xa8798] 80%nat
          [KZRange PP 4096 140737488355328; KZRange (DST + pe - PP) 0 4294967296; KZRange (PP - DST) 0 4294967296;
           KZRange pe 0 4294967296; KZRange (DST + pe) 4096 140737488355328; KZRange q 0 4294967296;
           KZRange (DST + pe + q) 4096 140737488355328; KZRange dcap 6 4294967296;
           KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange tl 1 12; KZRange rsv 0 255;
           KZRange o3 1 7; KZRange (o3 - qb) 0 7; KZRange qb 0 8; KZRange rb 0 7; KZRange (8 * qb + rb) 0 64;
           KZRange (n3 - o3) 8 4294967296; KZRange SPV 17594333498016 140737488355328;
           KZRange S3 4096 140737488355328; KZRange n3 9 4294967296; KZRange (S3 + n3) 4096 140737488355328;
           KZRange (S3 + o3) 4097 140737488355328]
          [(S3, n3); (SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96)] [(S3, n3); (SPV - 496, 496)].
        all: [> aside ..].
        all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJF1 DJF2; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7.
        all: [> kx_gen_regsF [8%nat; 12%nat; 13%nat; 14%nat; 15%nat; 26%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
        all: [> intros; evr; kx_mem ..].
        all: [> kx_sx3; rewrite ?(Z.mod_small (8 * qb + rb) (2^64)) in * by lia; kx_land_ranges; kx_strip_mod; land7_lin ..].
        all: try (replace ((8 * qb + rb) / 8) with qb in * by (clear - HQB HRB; Z.div_mod_to_equations; lia)).
        all: [> lazymatch goal with
             | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8798) _ _ _ _) => subst pe; eapply (x41_ts3 B4); lside
             | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa840c) _ _ _ _) =>
                 repeat match goal with
                 | H : bv_unsigned (edenot _ (EAlu ALU_SLTU _ _)) <> 0 |- _ =>
                     kx_sltu_in H; kx_ub_norm H;
                     lazymatch type of H with
                     | Z.b2z (?a <? ?b) <> 0 =>
                         let HL := fresh "HL" in
                         revert H; destruct (a <? b) eqn:HL; intro H; [apply Z.ltb_lt in HL; clear H | exfalso; apply H; reflexivity]
                     end
                 end;
                 subst pe; o_fix S3; eapply (x41_l3_d k IH B4); lside
             end ..].
  Qed.
End DX41A3.
End CANSEC1.
