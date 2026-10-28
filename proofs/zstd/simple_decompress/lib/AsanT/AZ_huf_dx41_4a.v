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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx41.
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
(* [comment removed for export] *)
Definition dst_hi (dcap DST : Z) : Prop := 0 < dcap -> 0x625000 <= DST.
(* [comment removed for export] *)
Definition x41_held (P : Prop) : Prop := P.
Lemma x41_held_intro : forall P : Prop, P -> x41_held P. Proof. intros P H. exact H. Qed.
Section CANSEC1. Context {rc : runConstT}.
Section DX41A4.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x41a_actx RNG m0 SPV DST dcap SRC n DT lo.
  (* [comment removed for export] *)
  Hypothesis DHI : dst_hi dcap DST.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -496)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).
  Notation SG41 := ((dcap + 3) / 4).
  Notation EINVA := (AZ_huf_dx41.EINVA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_end := (AZ_huf_dx41.x41_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).

  (* [comment removed for export] *)

  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\ (4096 <= SRC <= 140737488355328) /\
                 (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\ (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\
                 (0 <= rsv <= 255) /\ (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333498016 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
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
                   (SPV - 224 + 40 <= S \/ S + len <= SPV - 224) /\ (SPV - 480 + 104 <= S \/ S + len <= SPV - 480) /\
                   (SPV - 496 + 496 <= S \/ S + len <= SPV - 496))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      destruct SF as (S0 & S1 & SL32 & S2 & DJS & DJK & DJB & DJFr & DJW);
      assert (RS : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia)) as RSz;
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia)) as USz
      end
    end.
  (* [comment removed for export] *)
  Ltac zsfacts :=
    assert (ZS1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS3 : 0 <= SPV - 224 - -224 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV - 224 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -224 - -224 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -224 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV - 480 - -480 < 2 ^ 64 /\ 0 <= 104 < 2 ^ 64 /\ 0 <= SPV - 480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -480 - -480 < 2 ^ 64 /\ 0 <= 104 < 2 ^ 64 /\ 0 <= SPV + -480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 480 - -480 < 2 ^ 64 /\ 0 <= 480 < 2 ^ 64 /\ 0 <= SPV - 480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia).
  Ltac zsfactsS :=
    lazymatch goal with
    | BSE : ?S + ?len <= SRC + n |- _ =>
        assert (ZS9 : 0 <= S - 0 < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= S < 2 ^ 64) by (kx_clear_or; lia)
    end.
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 480 \/ SPV - 480 + 104 <= DST) /\ (DST + dcap <= SPV - 224 \/ SPV - 224 + 40 <= DST) /\
                 (SPV - 224 + 40 <= DT \/ DT + 16388 <= SPV - 224) /\ (SPV - 480 + 104 <= DT \/ DT + 16388 <= SPV - 480) /\
                 (DST + dcap <= SPV - 496 \/ SPV - 496 + 496 <= DST))
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
  Ltac trap_close := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa413c) _ _ _ _) => kx_trap_fast end).
  Ltac traps := trap_close.
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

  Definition x41_t4_stmt : Prop :=
    forall mm rest q dl (c4 b4 p4 st4 lm4 : word) pad4
      (w0 w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
    munch [(DST, DST + dcap); (SPV - 2720, SPV)] m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 w24 (Z_to_bv 64 dcap) w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 ->
    X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 ->
    X41BD4 SPV mm c4 b4 pad4 p4 st4 lm4 ->
    0 <= q -> 3 * SG41 + q <= dcap -> dl = tl + 256 * rsv ->
    evtF bsegs RNG POST (ST 0xa8cb0 mm x1 x5 x6 x7 x8 (Z_to_bv 64 (DST + dcap)) x10 x11 x12 x13 x14 x15
      (Z_to_bv 64 (DST + 3 * SG41 + q)) x17 x18 x19 x20 (Z_to_bv 64 dl) (Z_to_bv 64 (DT + 4)) x23 x24 x25 x26 x27 x28
      x29 x30 x31).

  Definition x41_e4_stmt : Prop :=
    forall mm rest q dl S4 n4 bs4 o4 bc4 (c4 b4 : word) pad4
      (w0 w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
    munch [(DST, DST + dcap); (SPV - 2720, SPV)] m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 w24 (Z_to_bv 64 dcap) w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 ->
    X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 ->
    X41BD4 SPV mm c4 b4 pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 -> SINVA o4 n4 bc4 -> 0 <= bc4 < 2147483648 ->
    0 <= q -> 3 * SG41 + q <= dcap -> dl = tl + 256 * rsv ->
    evtF bsegs RNG POST (ST 0xa8b94 mm x1 x5 x6 x7 x8 (Z_to_bv 64 (DST + dcap)) x10 x11 x12 x13 x14 (Z_to_bv 64 bc4)
      (Z_to_bv 64 (DST + 3 * SG41 + q)) x17 x18 x19 x20 (Z_to_bv 64 dl) (Z_to_bv 64 (DT + 4)) x23 x24 x25 x26 x27 x28
      x29 x30 x31).

  Definition x41_l4_inv : Prop :=
    forall mm rest q dl S4 n4 bs4 o4 bc4 (c4 b4 : word) pad4
      (w0 w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word)
      (x6 x7 x8 x10 x12 x13 x14 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
    munch [(DST, DST + dcap); (SPV - 2720, SPV)] m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 w24 (Z_to_bv 64 dcap) w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 ->
    X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 ->
    X41BD4 SPV mm c4 b4 pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 -> SINVA o4 n4 bc4 -> 0 <= bc4 <= 64 ->
    0 <= q -> 6 <= dcap -> 3 * SG41 + q <= dcap -> dl = tl + 256 * rsv ->
    evtF bsegs RNG POST (ST 0xa8860 mm (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 (64 - tl)) x6 x7 x8 (Z_to_bv 64 (DST + dcap))
      x10 (Z_to_bv 64 (DST + 3 * SG41 + q)) x12 x13 x14 (Z_to_bv 64 bc4) (Z_to_bv 64 (DST + 3 * SG41 + q)) (Z_to_bv 64 64)
      x18 x19 x20 (Z_to_bv 64 dl) (Z_to_bv 64 (DT + 4)) x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Lemma x41_einvA : forall mm rest (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 c4 b4 p4 st4 lm4 : word) pad4,
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm ->
    stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 -> X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 -> X41BD4 SPV mm c4 b4 pad4 p4 st4 lm4 ->
    EINVA mm.
  Proof using CTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'.
    intros until pad4. intros SV RS MI OUT MU0 WM0 STK SA SH SB4 B4.
    pose proof (stk_of_rw_cells bsegs mm _ _ SA) as H1.
    pose proof (stk_of_rw_cells bsegs mm _ _ SH) as H2.
    pose proof (stk_of_rw_cells bsegs mm _ _ SB4) as H3.
    pose proof (stk_of_rw_cells bsegs mm _ _ B4) as H4.
    pose proof (stk_of_rw_cells bsegs mm _ _ RS) as H5.
    cbn [cells_size csize Nat.add] in H1, H2, H3, H4, H5.
    change (Z.of_nat 136) with 136 in H1. change (Z.of_nat 8) with 8 in H2. change (Z.of_nat 96) with 96 in H3.
    change (Z.of_nat 40) with 40 in H4. change (Z.of_nat 112) with 112 in H5.
    replace (SPV + -496 + 136) with (SPV + -360) in H1 by lia.
    replace (SPV + -360 + 8) with (SPV + -352) in H2 by lia.
    replace (SPV + -352 + 96) with (SPV + -256) in H3 by lia.
    replace (SPV + -256 + 40) with (SPV + -216) in H4 by lia.
    replace (SPV + -216 + 112) with (SPV + -104) in H5 by lia.
    unfold AZ_huf_dx41.EINVA. split; [exact OUT|]. split; [exact SV|]. split; [|split; [exact MU0|split; [exact WM0|exact MI]]].
    eapply (stk_merge bsegs mm lo (SPV + -216)); [|exact H5|lia].
    eapply (stk_merge bsegs mm lo (SPV + -256)); [|exact H4|lia].
    eapply (stk_merge bsegs mm lo (SPV + -352)); [|exact H3|lia].
    eapply (stk_merge bsegs mm lo (SPV + -360)); [|exact H2|lia].
    eapply (stk_merge bsegs mm lo (SPV + -496)); [exact STK|exact H1|lia].
  Qed.

  Lemma x41_sa_dcap : forall mm (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word),
    X41SA SPV mm w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 ->
    rw_cells bsegs mm (SPV + -464) [C8 w32].
  Proof.
    intros mm w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 H.
    change [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104;
            C8 w112; C8 w120; C8 w128]
      with ([C8 w0; C8 w8; C8 w16; C8 w24] ++ [C8 w32] ++ [C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96;
            C8 w104; C8 w112; C8 w120; C8 w128]) in H.
    destruct H as [[HW HB] HR].
    apply cells_wf_app in HW. destruct HW as [HW1 HW2]. apply cells_wf_app in HW2. destruct HW2 as [HW2 _].
    rewrite !cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [_ HB]. apply bytes_at_app in HB. destruct HB as [HB _].
    rewrite (cells_bytes_length _ HW1) in HB.
    split; [split; [exact HW2|] |].
    - replace (SPV + -464) with (SPV + -496 + Z.of_nat (cells_size [C8 w0; C8 w8; C8 w16; C8 w24])) by (cbn; lia). exact HB.
    - eapply (wr_at_sub bsegs mm (SPV + -496) _ (SPV + -464) _ HR); rewrite ?cells_size_app; cbn; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_t4 : forall (k : nat) mm rest j sh (c4 b4 p4 st4 lm4 : word) pad4
      (w0 w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word)
      (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x18 x19 x20 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
    munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 w24 (Z_to_bv 64 dcap) w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 ->
    X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 ->
    X41BD4 SPV mm c4 b4 pad4 p4 st4 lm4 ->
    dcap - j <= Z.of_nat k -> 0 <= j < dcap -> 52 <= sh <= 63 ->
    evtF bsegs RNG POST (ST 0xa8cc4 mm x1 x5 x6 x7 x8 OEND x10 (Z_to_bv 64 (DST + j)) x12 x13 x14 x15 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 sh)
                            x18 x19 x20 x21 (Z_to_bv 64 (DT + 4)) x23 x24 x25 x26 x27 SB x29 x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    induction k as [|k IH]; intros mm rest j sh c4 b4 p4 st4 lm4 pad4
      w0 w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232
      x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x18 x19 x20 x21 x23 x24 x25 x26 x27 x29 x30 x31
      SV JK MU0 WM0 MI OUT DTB STK SA SH SB4 BD HK HJ HSH; [exfalso; lia|].
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    dfacts MU0 UDST RDST RDSTS DSTA AW0 R1.
    assert (RJ : 1 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355327 /\ 1 <= dcap <= 4294967296) by (clear - HJ R1; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4).
    kx_autoFLA BD [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 256) 40] [0xa8cc4; 0xa8d60] 60%nat
      [KZRange (dcap - j) 1 4294967296; KZRange j 0 4294967296; KZRange dcap 1 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355327;
       KZRange DT 4096 140737488338940; KZRange sh 52 63; KZRange SPV 17594333498016 140737488355328; KZAlign SPV 16; KZAlign DT 4;
       KZWr DST dcap; KZWr (SPV - 256) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 256) 40; KZDisj DST dcap (SPV - 496) 496; KZDisj (SPV - 256) 40 DT 16388]
      [(DT, 16388); (SPV - 256, 40)] [(DT, 16388); (DST, dcap); (SPV - 496, 496)].
    all: [> aside ..].
    all: [> kx_gen_regsF [5%nat; 6%nat; 7%nat; 14%nat; 15%nat] ..].
    all: [> intros; kx_ev_ranges ..].
    all: [> kx_mem ..].
    all: [> kx_strip_mod ..].
    all: [> lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8d60) _ _ _ _) =>
             eapply x41_end; [eapply x41_einvA; eassumption | eapply x41_sa_dcap; eassumption | unfold AZ_huf_dx41.x41a_bd; eassumption]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8cc4) _ _ _ _) =>
             try replace (DST + j + 1) with (DST + (j + 1)) by lia;
             eapply (IH _ rest (j + 1)); try eassumption; try lia; try reflexivity
         end ..].
  Qed.

  (* [comment removed for export] *)
  Lemma x41_g4 : x41_t4_stmt.
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    unfold x41_t4_stmt.
    intros mm rest q dl c4 b4 p4 st4 lm4 pad4
      w0 w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232
      x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31
      SV JK MU0 WM0 MI OUT DTB STK SA SH SB4 BD HQ HQD HDL.
    subst dl. facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    assert (HJ : 0 <= 3 * SG41 + q <= dcap) by (pose proof (Z.div_pos (dcap + 3) 4 ltac:(lia) ltac:(lia)); lia).
    replace (DST + 3 * SG41 + q) with (DST + (3 * SG41 + q)) by lia.
    revert HJ. generalize (3 * SG41 + q) as j. intros j HJ. clear HQ HQD.
    assert (RJ : 0 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355328) by (clear - HJ R1; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3).
    kx_autoFLA SH (@nil kza) [0xa8cc4; 0xa8d60] 12%nat
      [KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange (dcap - j) 0 4294967296; KZRange DST 4096 140737488355328;
       KZRange (DST + j) 4096 140737488355328; KZRange tl 1 12; KZRange rsv 0 255; KZRange SPV 17594333498016 140737488355328]
      [(SPV - 360, 8)] [(SPV - 496, 496)].
    all: [> aside ..].
    all: [> lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8d60) _ _ _ _) =>
             eapply x41_end; [eapply x41_einvA; eassumption | eapply x41_sa_dcap; eassumption | unfold AZ_huf_dx41.x41a_bd; eassumption]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8cc4) _ _ _ _) =>
             kit_sh_fix; eapply (x41_t4 (Z.to_nat (dcap - j)) mm); try eassumption; try lia; try reflexivity
         end ..].
  Qed.
End DX41A4.
End CANSEC1.
