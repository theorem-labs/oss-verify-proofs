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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_mr0000 AZ_huf_dx41_mr0001 AZ_huf_dx41_mr0010 AZ_huf_dx41_mr0011 AZ_huf_dx41_mr0100 AZ_huf_dx41_mr0101 AZ_huf_dx41_mr0110 AZ_huf_dx41_mr0111 AZ_huf_dx41_mr1000 AZ_huf_dx41_mr1001 AZ_huf_dx41_mr1010 AZ_huf_dx41_mr1011 AZ_huf_dx41_mr1100 AZ_huf_dx41_mr1101 AZ_huf_dx41_mr1110 AZ_huf_dx41_mr1111.
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
Section DX41AM.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x41a_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis DHI : dst_hi dcap DST.
  Hypothesis NBOK : huf_nb_ok false dtb tl.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -496)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation WDM := [(DST, DST + dcap); (SPV - 496, SPV - 216)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation SG41 := ((dcap + 3) / 4).

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
  (* [comment removed for export] *)
  Ltac sfactsF BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc :=
    lazymatch type of BSE with ?S + ?len <= SRC + n =>
      let sf := fresh "SF" in
      assert (sf : (4096 <= S <= 140737488355328) /\ (4096 <= S + len <= 140737488355328) /\ (1 <= len <= 4294967296) /\ S + len < 2^47 /\
                   (DST + dcap <= S \/ S + len <= DST) /\ (S + len <= lo \/ SPV <= S) /\
                   (SPV - 496 + 280 <= S \/ S + len <= SPV - 496) /\ (SPV - 216 + 112 <= S \/ S + len <= SPV - 216) /\
                   (0 <= S - 0 < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= S < 2 ^ 64))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      let a1 := fresh "SF" in let a2 := fresh "SF" in let a3 := fresh "SF" in let a4 := fresh "SF" in
      let a5 := fresh "SF" in let a6 := fresh "SF" in let a7 := fresh "SF" in let a8 := fresh "SF" in let a9 := fresh "SF" in
      destruct sf as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9);
      let rs := fresh "RS" in
      assert (rs : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia));
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia))
      end
    end.
  Ltac zsfacts :=
    assert (ZS1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS3 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 280 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 280 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV + -360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV + -360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV + -352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia);
    assert (ZS9 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 136 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS10 : 0 <= SPV + -256 - -256 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -256 < 2 ^ 64) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 496 \/ SPV - 496 + 280 <= DST) /\ (DST + dcap <= SPV - 216 \/ SPV - 216 + 112 <= DST) /\
                 (SPV - 216 + 112 <= DT \/ DT + 16388 <= SPV - 216) /\ (SPV - 496 + 280 <= DT \/ DT + 16388 <= SPV - 496) /\
                 (DST + dcap <= SPV - 496 \/ SPV - 496 + 496 <= DST))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4 & DJF5).
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
           | H : 0 <= _ - 0 < 2 ^ 64 /\ _ |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac kx_lia_or1 :=
    match goal with
    | H : _ \/ _ |- _ =>
        solve [ repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end;
                repeat match goal with H' : _ -> _ |- _ => clear H' end; lia ]
    end.
  Ltac kx_lia_m1 := first [ solve [kx_clear_or; lia] | solve [kx_lia_or1] | kx_bv_ranges; solve [kx_clear_or; lia] | solve [kx_bv_ranges; kx_lia_or1] ].
  #[local] Ltac kx_lia ::= kx_lia_m1.
  #[local] Ltac kxl_lia ::= first [ kxl_hyp | solve [kx_clear_or; lia] | solve [kxl_lia_small] | kx_lia_m1 ].
  (* [comment removed for export] *)
  Ltac lclean2 :=
    repeat match goal with H : ?o = 0 \/ _ |- _ => revert H end;
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : rng _ _ _ |- _ => clear H
           | H : rng_aimg _ |- _ => clear H
           | H : 4096 <= _ <= _ |- _ => clear H
           | H : 17594333495296 <= _ <= _ |- _ => clear H
           | H : 17594333498016 <= _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
           | H : atoms_ok _ _ |- _ => clear H
           | H : reads_ok _ _ _ _ _ |- _ => clear H
           | H : know_ok _ _ _ _ |- _ => clear H
           end;
    intros.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa413c) _ _ _ _) => kx_trap_fast end).
  Ltac evr := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end); kx_ev_ranges.
  Ltac lside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [assumption | lia | kx_lia | idtac]
    | |- _ \/ _ => first [assumption | lia | idtac]
    | |- Z.le _ _ => first [assumption | lia]
    | |- Z.lt _ _ => first [assumption | lia]
    | |- _ => eassumption
    end.
  Notation x41_mr0000 := (AZ_huf_dx41_mr0000.x41_mr0000 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr0001 := (AZ_huf_dx41_mr0001.x41_mr0001 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr0010 := (AZ_huf_dx41_mr0010.x41_mr0010 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr0011 := (AZ_huf_dx41_mr0011.x41_mr0011 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr0100 := (AZ_huf_dx41_mr0100.x41_mr0100 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr0101 := (AZ_huf_dx41_mr0101.x41_mr0101 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr0110 := (AZ_huf_dx41_mr0110.x41_mr0110 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr0111 := (AZ_huf_dx41_mr0111.x41_mr0111 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr1000 := (AZ_huf_dx41_mr1000.x41_mr1000 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr1001 := (AZ_huf_dx41_mr1001.x41_mr1001 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr1010 := (AZ_huf_dx41_mr1010.x41_mr1010 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr1011 := (AZ_huf_dx41_mr1011.x41_mr1011 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr1100 := (AZ_huf_dx41_mr1100.x41_mr1100 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr1101 := (AZ_huf_dx41_mr1101.x41_mr1101 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr1110 := (AZ_huf_dx41_mr1110.x41_mr1110 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_mr1111 := (AZ_huf_dx41_mr1111.x41_mr1111 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Ltac fix_s1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  (* [comment removed for export] *)
  Ltac bc_var X q r := let XP := fresh "XP" q in let E := fresh "E" q in let RB := fresh "RB" q in let QB := fresh "QB" q in
    assert (XP : 0 <= X) by (kx_clear_or; lia);
    pose proof (Z.div_mod X 8 ltac:(clear; lia)) as E; pose proof (Z.mod_pos_bound X 8 ltac:(clear; lia)) as RB;
    assert (QB : 0 <= X / 8) by (apply Z.div_pos; [exact XP | clear; lia]);
    remember (X / 8) as q eqn:Hq; remember (X mod 8) as r eqn:Hr; clear Hq Hr;
    replace (Z_to_bv 64 X) with (Z_to_bv 64 (8 * q + r)) by (f_equal; first [exact E | symmetry; exact E]);
    repeat match goal with B : rw_cells _ _ _ [_; C4 (Z_to_bv 64 X); _; _; _; _] |- _ =>
      replace (Z_to_bv 64 X) with (Z_to_bv 64 (8 * q + r)) in B by (f_equal; first [exact E | symmetry; exact E]) end.
  Ltac bc_sum P K q r := let E := fresh "E" q in let RB := fresh "RB" q in let QB := fresh "QB" q in
    pose proof (Z.div_mod (P + K) 8 ltac:(clear; lia)) as E; pose proof (Z.mod_pos_bound (P + K) 8 ltac:(clear; lia)) as RB;
    assert (QB : 0 <= (P + K) / 8) by (apply Z.div_pos; [kx_clear_or; lia | clear; lia]);
    remember ((P + K) / 8) as q eqn:Hq; remember ((P + K) mod 8) as r eqn:Hr; clear Hq Hr.
  Ltac bc_fix := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 ?P4) _ ?W2 _ _ _ _ _ _ _ ?W4 (Z_to_bv 64 ?P3) _ _ ?W3 _ (Z_to_bv 64 ?P2) _ _ _ _ _ (Z_to_bv 64 ?X1) _ _ _ _) _ _ _ _ _ _) =>
    let q1 := fresh "q1" in let r1 := fresh "r1" in let q2 := fresh "q2" in let r2 := fresh "r2" in
    let q3 := fresh "q3" in let r3 := fresh "r3" in let q4 := fresh "q4" in let r4 := fresh "r4" in
    rewrite <- (Z_to_bv_bv_unsigned W2), <- (Z_to_bv_bv_unsigned W3), <- (Z_to_bv_bv_unsigned W4);
    repeat match goal with
           | H : _ <= bv_unsigned W2 <= _ |- _ => clear H
           | H : _ <= bv_unsigned W3 <= _ |- _ => clear H
           | H : _ <= bv_unsigned W4 <= _ |- _ => clear H
           end;
    kx_ev_ranges;
    bc_var X1 q1 r1; bc_sum P2 (bv_unsigned W2) q2 r2; bc_sum P3 (bv_unsigned W3) q3 r3; bc_sum P4 (bv_unsigned W4) q4 r4 end.

  (* [comment removed for export] *)
  Definition HINV (o len b : Z) : Prop := 0 <= o /\ ((o + 8 <= len /\ 0 <= b <= 8) \/ (o = 0 /\ 0 <= b <= 64)).
  (* [comment removed for export] *)
  Definition HINV2 (o len d : Z) : Prop := 0 <= o /\ ((o + 8 <= len /\ 0 <= d <= 32) \/ (o = 0 /\ 0 <= d <= 88)).
  Ltac lsideM := lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- HINV _ _ _ => unfold HINV; lia
    | |- HINV2 _ _ _ => unfold HINV2; unfold HINV in *; unfold HINV2 in *; lia
    | |- _ => lside
    end.

  Lemma x41_mb : forall mb mm q sh dl o1 S1 n1 bs1 d1 o2 S2 n2 bs2 d2 k2 o3 S3 n3 bs3 d3 k3 o4 S4 n4 bs4 d4 k4
      (c1 c2 c3 c4 c4o b4o p4o : word) pad4o (w8 w16 w40 w48 w56 w64 : word) (x15 x16 x18 x27 x31 : word),
    munch WDM mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm (Z_to_bv 64 DT) w8 w16 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w40 w48 w56 w64 (Z_to_bv 64 S1) (Z_to_bv 64 S2)
      (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SG41) (Z_to_bv 64 dl) (Z_to_bv 64 S3) (Z_to_bv 64 (DST + 2 * SG41))
      (Z_to_bv 64 (DST + 3 * SG41)) ->
    X41SH SPV mm ->
    X41SB SPV mm (Z_to_bv 64 (DST + SG41)) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 (DST + 3 * SG41))
      (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (DST + 2 * SG41))
      (Z_to_bv 64 (DST + SG41)) c3 c2 c1 ->
    X41BD4 SPV mm c4o b4o pad4o p4o (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    bytes_at bsegs mm S1 bs1 -> zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 ->
    HINV2 o1 n1 d1 -> HINV2 o2 n2 (d2 + k2) -> HINV2 o3 n3 (d3 + k3) -> HINV2 o4 n4 (d4 + k4) ->
    0 <= d2 -> 0 <= k2 -> 0 <= d3 -> 0 <= k3 -> 0 <= d4 -> 0 <= k4 ->
    0 <= q -> 3 * SG41 + q + 4 <= dcap -> sh = 64 - tl -> dl = tl + 256 * rsv ->
    (forall mm' (o1' o2' o3' o4' b1' b2' b3' b4' : Z) (c1' c2' c3' c4' c4o' : word)
            (y1 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y29 y31 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -496) ->
        X41SA SPV mm' (Z_to_bv 64 DT) w8 w16 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w40 w48 w56 w64 (Z_to_bv 64 S1) (Z_to_bv 64 S2)
          (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SG41) (Z_to_bv 64 dl) (Z_to_bv 64 S3) (Z_to_bv 64 (DST + 2 * SG41))
          (Z_to_bv 64 (DST + 3 * SG41)) ->
        X41SH SPV mm' ->
        X41SB SPV mm' (Z_to_bv 64 (DST + SG41)) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 (DST + 3 * SG41))
          (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (DST + 2 * SG41))
          (Z_to_bv 64 (DST + SG41)) c3' c2' c1' ->
        X41BD4 SPV mm' c4o' b4o pad4o p4o (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        1 <= o1' -> o1' + 8 <= n1 -> 0 <= b1' <= 7 -> 1 <= o2' -> o2' + 8 <= n2 -> 0 <= b2' <= 7 ->
        1 <= o3' -> o3' + 8 <= n3 -> 0 <= b3' <= 7 -> 1 <= o4' -> o4' + 8 <= n4 -> 0 <= b4' <= 7 ->
        3 * SG41 + (q + 4) + 4 <= dcap ->
        evtF bsegs RNG POST (ST 0xa6bf4 mm' y1 (Z_to_bv 64 b4') y6 y7 c4' y9 (Z_to_bv 64 (S4 + o4')) y11 y12 y13 y14 y15 y16
          y17 y18 (Z_to_bv 64 b3') SB (Z_to_bv 64 b2') (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + 3 * SG41))
          (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S2 + o2')) (Z_to_bv 64 (S1 + o1')) (Z_to_bv 64 b1') (Z_to_bv 64 (q + 4)) y29
          (Z_to_bv 64 sh) y31)) ->
    (forall mm' (o1' o2' o3' o4' b1' b2' b3' b4' : Z) (c1' c2' c3' c4' : word)
            (y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y20 y29 y30 y31 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -496) ->
        X41SA SPV mm' (Z_to_bv 64 DT) w8 w16 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w40 w48 w56 w64 (Z_to_bv 64 S1) (Z_to_bv 64 S2)
          (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SG41) (Z_to_bv 64 dl) (Z_to_bv 64 S3) (Z_to_bv 64 (DST + 2 * SG41))
          (Z_to_bv 64 (DST + 3 * SG41)) ->
        X41SH SPV mm' ->
        X41SB SPV mm' (Z_to_bv 64 (DST + SG41)) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 (DST + 3 * SG41))
          (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (DST + 2 * SG41))
          (Z_to_bv 64 (DST + SG41)) c3' c2' c1' ->
        X41BD4 SPV mm' c4' b4o pad4o p4o (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        SINVA o1' n1 b1' -> 0 <= b1' < 2147483648 -> SINVA o2' n2 b2' -> 0 <= b2' < 2147483648 ->
        SINVA o3' n3 b3' -> 0 <= b3' < 2147483648 -> SINVA o4' n4 b4' -> 0 <= b4' < 2147483648 ->
        evtF bsegs RNG POST (ST 0xa7744 mm' (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 b4') y6 y7 y8 y9 (Z_to_bv 64 (S4 + o4'))
          y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 b3') y20 (Z_to_bv 64 b2') (Z_to_bv 64 (DT + 4))
          (Z_to_bv 64 (DST + 3 * SG41)) (Z_to_bv 64 (S3 + o3')) (Z_to_bv 64 (S2 + o2')) (Z_to_bv 64 (S1 + o1'))
          (Z_to_bv 64 b1') (Z_to_bv 64 (q + 4)) y29 y30 y31)) ->
    evtF bsegs RNG POST (ST 0xa6eec mm (Z_to_bv 64 (DST + SG41 + q)) (Z_to_bv 64 d4) (Z_to_bv 64 d1) (Z_to_bv 64 k3) c4
      (Z_to_bv 64 (DST + 3 * SG41 + q)) (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DST + SG41 + q))
      (Z_to_bv 64 (DST + 2 * SG41 + q)) (Z_to_bv 64 (DST + 3 * SG41 + q)) x15 x16 (Z_to_bv 64 (DST + 2 * SG41 + q)) x18
      (Z_to_bv 64 d3) SB (Z_to_bv 64 d2) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 k2) (Z_to_bv 64 (S3 + o3))
      (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S1 + o1)) x27 (Z_to_bv 64 q) (Z_to_bv 64 k4) (Z_to_bv 64 sh) x31).
  Proof using CTX ACTX NBOK.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    remember ((dcap + 3) / 4) as e1 eqn:HSG.
    intros mb mm q sh dl o1 S1 n1 bs1 d1 o2 S2 n2 bs2 d2 k2 o3 S3 n3 bs3 d3 k3 o4 S4 n4 bs4 d4 k4 c1 c2 c3 c4 c4o b4o p4o pad4o w8 w16 w40 w48 w56 w64 x15 x16 x18 x27 x31
      MU WM MU0 WM0 MI OUT DTB STK SAF SHF SBF BDF SB1 BL1 SS1 SE1 LN1 SB2 BL2 SS2 SE2 LN2 SB3 BL3 SS3 SE3 LN3 SB4 BL4 SS4 SE4 LN4 HI1 HI2 HI3 HI4 HP2 HK2 HP3 HK3 HP4 HK4 HJ HROOM HSH HDL KH KE.
    assert (HE1 : 0 <= e1) by (rewrite HSG; apply Z.div_pos; [clear - R1; lia | clear; lia]).
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    ffacts OS1 OS3 LO. dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. zsfacts. kclean.
    assert (TBL : tbl_in_log bsegs mm DT sh 2 4 0 12).
    { apply (tbl_in_log_bytes_at bsegs mm DT dtb sh 2 4 0 12 DTB); [clear - R3 DL HSH TL; lia | clear - HSH TL; lia |].
      intros i Hi. replace (64 - sh) with tl in Hi by (clear - HSH; lia). destruct (NBOK i Hi) as (bb & Hb & Hr). exists bb. split; [exact Hb|].
      pose proof (bv_unsigned_in_range 8 bb). lia. }
    unfold HINV2 in HI1, HI2, HI3, HI4.
    assert (KF : (4 <= dcap - 3 * e1 - q <= 4294967296) /\ (4 <= dcap - 2 * e1 - q <= 4294967296) /\ (4 <= dcap - e1 - q <= 4294967296) /\
                 (4 <= dcap - q <= 4294967296) /\ (0 <= q <= 4294967296) /\ (0 <= e1 <= 4294967296) /\ (0 <= e1 + q <= 4294967296) /\
                 (0 <= 2 * e1 + q <= 4294967296) /\ (0 <= 3 * e1 + q <= 4294967296) /\
                 (4096 <= DST + q <= 140737488355324) /\ (4096 <= DST + e1 + q <= 140737488355324) /\
                 (4096 <= DST + 2 * e1 + q <= 140737488355324) /\ (4096 <= DST + 3 * e1 + q <= 140737488355324) /\
                 (52 <= sh <= 63) /\ (0 <= d1 <= 88) /\ (0 <= d2 <= 88) /\ (0 <= d3 <= 88) /\ (0 <= d4 <= 88) /\
                 (0 <= k2 <= 88) /\ (0 <= k3 <= 88) /\ (0 <= k4 <= 88) /\
                 (4096 <= DST + e1 <= 140737488355328) /\ (4096 <= DST + 2 * e1 <= 140737488355328) /\ (4096 <= DST + 3 * e1 <= 140737488355328) /\
                 (4 <= dcap <= 4294967296))
      by (clear - HJ HE1 HROOM HSH TL R1 HI1 HI2 HI3 HI4 HP2 HK2 HP3 HK3 HP4 HK4; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 & KF13 & KF14 & KF15 & KF16 & KF17 & KF18 & KF19 & KF20 & KF21 & KF22 & KF23 & KF24 & KF25).
    assert (SFM : (4096 <= S1 <= 140737488355328) /\ (4096 <= S1 + n1 <= 140737488355328) /\ (1 <= n1 <= 4294967296) /\ (DST + dcap <= S1 \/ S1 + n1 <= DST) /\
                  (4096 <= S2 <= 140737488355328) /\ (4096 <= S2 + n2 <= 140737488355328) /\ (1 <= n2 <= 4294967296) /\ (DST + dcap <= S2 \/ S2 + n2 <= DST) /\
                  (4096 <= S3 <= 140737488355328) /\ (4096 <= S3 + n3 <= 140737488355328) /\ (1 <= n3 <= 4294967296) /\ (DST + dcap <= S3 \/ S3 + n3 <= DST) /\
                  (4096 <= S4 <= 140737488355328) /\ (4096 <= S4 + n4 <= 140737488355328) /\ (1 <= n4 <= 4294967296) /\ (DST + dcap <= S4 \/ S4 + n4 <= DST))
      by (clear - SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4 R2 DJ1 GF4 GF5 GF6; lia).
    destruct SFM as (SF1a & SF1b & SF1c & SF1d & SF2a & SF2b & SF2c & SF2d & SF3a & SF3b & SF3c & SF3d & SF4a & SF4b & SF4c & SF4d).
    (* [comment removed for export] *)
    kx_autoFLA (SAF, SHF, SBF, BDF) [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap] [0xa71cc] 300%nat
      [KZRange (dcap - 3 * e1 - q) 4 4294967296; KZRange (dcap - 2 * e1 - q) 4 4294967296; KZRange (dcap - e1 - q) 4 4294967296;
       KZRange (dcap - q) 4 4294967296; KZRange q 0 4294967296; KZRange e1 0 4294967296; KZRange (e1 + q) 0 4294967296;
       KZRange (2 * e1 + q) 0 4294967296; KZRange (3 * e1 + q) 0 4294967296;
       KZRange (DST + q) 4096 140737488355324; KZRange (DST + e1 + q) 4096 140737488355324;
       KZRange (DST + 2 * e1 + q) 4096 140737488355324; KZRange (DST + 3 * e1 + q) 4096 140737488355324;
       KZRange (DST + e1) 4096 140737488355328; KZRange (DST + 2 * e1) 4096 140737488355328; KZRange (DST + 3 * e1) 4096 140737488355328;
       KZRange sh 52 63; KZRange d1 0 88; KZRange d2 0 88; KZRange d3 0 88; KZRange d4 0 88;
       KZRange k2 0 88; KZRange k3 0 88; KZRange k4 0 88;
       KZRange dcap 4 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940;
       KZRange SPV 17594333498016 140737488355328; KZTblLog DT sh 2 4 0 12;
       KZRange S1 4096 140737488355328; KZRange (S1 + n1) 4096 140737488355328; KZRange n1 1 4294967296; KZDisj DST dcap S1 n1;
       KZRange S2 4096 140737488355328; KZRange (S2 + n2) 4096 140737488355328; KZRange n2 1 4294967296; KZDisj DST dcap S2 n2;
       KZRange S3 4096 140737488355328; KZRange (S3 + n3) 4096 140737488355328; KZRange n3 1 4294967296; KZDisj DST dcap S3 n3;
       KZRange S4 4096 140737488355328; KZRange (S4 + n4) 4096 140737488355328; KZRange n4 1 4294967296; KZDisj DST dcap S4 n4;
       KZWr DST dcap;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 496) 496;
       KZDisj (SPV - 496) 280 DT 16388;
       KZDisj (SPV - 496) 280 S1 n1; KZDisj (SPV - 496) 280 S2 n2; KZDisj (SPV - 496) 280 S3 n3; KZDisj (SPV - 496) 280 S4 n4]
      [(DT, 16388); (SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96); (SPV + -256, 40)] [(DT, 16388); (DST, dcap); (SPV - 496, 496)].
    all: [> aside ..].
    all: traps.
    all: try clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12 KF13 KF14 KF15 KF16 KF17 KF18 KF19 KF20 KF21 KF22 KF23 KF24 KF25.
    all: aclean.
    all: [> kx_gen_regsF [6%nat; 11%nat; 12%nat; 13%nat; 14%nat; 17%nat; 18%nat; 29%nat; 31%nat] ..].
    all: [> intros; evr; kx_mem ..].
    all: [> kx_sx3; kx_strip_mod ..].
    (* [comment removed for export] *)
    all: fix_s1 (DST + 3 * e1 + q).
    all: bc_fix.
    all: lclean2.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 ?P4) _ (Z_to_bv 64 ?K2) _ _ _ _ _ _ _ (Z_to_bv 64 ?K4) (Z_to_bv 64 ?P3) _ _ (Z_to_bv 64 ?K3) _ (Z_to_bv 64 ?P2) _ _ _ _ _ (Z_to_bv 64 (8 * ?Q1 + ?RR1)) _ _ _ _) _ _ _ _ _ _) =>
      lazymatch goal with E2 : P2 + K2 = 8 * ?Q2 + ?RR2, E3 : P3 + K3 = 8 * ?Q3 + ?RR3, E4 : P4 + K4 = 8 * ?Q4 + ?RR4 |- _ =>
      assert (HRF1 : o1 = 0 \/ (o1 + 8 <= n1 /\ 8 * Q1 + RR1 <= 56)) by lia;
      assert (HRF2 : o2 = 0 \/ (o2 + 8 <= n2 /\ 8 * Q2 + RR2 <= 56)) by lia;
      assert (HRF3 : o3 = 0 \/ (o3 + 8 <= n3 /\ 8 * Q3 + RR3 <= 56)) by lia;
      assert (HRF4 : o4 = 0 \/ (o4 + 8 <= n4 /\ 8 * Q4 + RR4 <= 56)) by lia;
      assert (RQ1 : (0 <= RR1 <= 7) /\ 0 <= Q1 /\ 8 * Q1 + RR1 <= 112) by lia; destruct RQ1 as (RQ1a & RQ1b & RQ1c);
      assert (RQ2 : (0 <= RR2 <= 7) /\ 0 <= Q2 /\ 8 * Q2 + RR2 <= 112) by lia; destruct RQ2 as (RQ2a & RQ2b & RQ2c);
      assert (RQ3 : (0 <= RR3 <= 7) /\ 0 <= Q3 /\ 8 * Q3 + RR3 <= 112) by lia; destruct RQ3 as (RQ3a & RQ3b & RQ3c);
      assert (RQ4 : (0 <= RR4 <= 7) /\ 0 <= Q4 /\ 8 * Q4 + RR4 <= 112) by lia; destruct RQ4 as (RQ4a & RQ4b & RQ4c);
      assert (OO : 0 <= o1 /\ 0 <= o2 /\ 0 <= o3 /\ 0 <= o4) by lia; destruct OO as (OO1 & OO2 & OO3 & OO4)
      end
    end.
    all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 ?P4) _ (Z_to_bv 64 ?K2) _ _ _ _ _ _ _ (Z_to_bv 64 ?K4) (Z_to_bv 64 ?P3) _ _ (Z_to_bv 64 ?K3) _ (Z_to_bv 64 ?P2) _ _ _ _ _ (Z_to_bv 64 (8 * ?Q1 + ?RR1)) _ _ _ _) _ _ _ _ ?m _) =>
      lazymatch goal with E2 : P2 + K2 = 8 * ?Q2 + ?RR2, E3 : P3 + K3 = 8 * ?Q3 + ?RR3, E4 : P4 + K4 = 8 * ?Q4 + ?RR4 |- _ =>
      subst e1;
      destruct (Z_lt_le_dec o1 8) as [C1|C1]; [destruct (Z_lt_le_dec o2 8) as [C2|C2]; [destruct (Z_lt_le_dec o3 8) as [C3|C3]; [destruct (Z_lt_le_dec o4 8) as [C4|C4]|destruct (Z_lt_le_dec o4 8) as [C4|C4]]|destruct (Z_lt_le_dec o3 8) as [C3|C3]; [destruct (Z_lt_le_dec o4 8) as [C4|C4]|destruct (Z_lt_le_dec o4 8) as [C4|C4]]]
                                               |destruct (Z_lt_le_dec o2 8) as [C2|C2]; [destruct (Z_lt_le_dec o3 8) as [C3|C3]; [destruct (Z_lt_le_dec o4 8) as [C4|C4]|destruct (Z_lt_le_dec o4 8) as [C4|C4]]|destruct (Z_lt_le_dec o3 8) as [C3|C3]; [destruct (Z_lt_le_dec o4 8) as [C4|C4]|destruct (Z_lt_le_dec o4 8) as [C4|C4]]]];
      [ eapply (x41_mr0000 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr0001 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr0010 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr0011 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr0100 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr0101 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr0110 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr0111 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr1000 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr1001 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr1010 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr1011 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr1100 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr1101 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr1110 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4)
      | eapply (x41_mr1111 mb m q sh dl S1 n1 bs1 o1 Q1 RR1 S2 n2 bs2 o2 Q2 RR2 P2 K2 S3 n3 bs3 o3 Q3 RR3 P3 K3 S4 n4 bs4 o4 Q4 RR4 P4 K4) ]
      end
    end.
    all: lside.
    all: first [exact KH | exact KE].
  Qed.
End DX41AM.
End CANSEC1.
