(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_libc_iface AZ_huf_lbkit AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_fq AZ_huf_dx41_fik.
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
#[local] Ltac kx_rd_at ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      first [ match goal with
              | H : bytes_at segs m A ?bs |- _ => apply (rd_at_sub segs m A (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A bs H)); kx_lia
              | H : rw_cells segs m A ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (rd_at_sub segs m A n A N (rd_at_rw_cells segs m A cs H)); kx_lia
              | H : ro_cells segs m A ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (rd_at_sub segs m A n A N (rd_at_ro_cells segs m A cs H)); kx_lia
              end
            | let A' := eval lazy in A in
              lazymatch A' with Z0 => idtac | Zpos _ => idtac end;
              apply (rd_at_imgZ segs m A N); [lia | lia | lia | vm_compute; reflexivity]
            | match goal with
              | H : bytes_at segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A0 bs H)); kx_lia
              | H : u8arr segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_u8arr segs m A0 bs H)); kx_lia
              | H : rw_cells segs m ?A0 ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (rd_at_sub segs m A0 n A N (rd_at_rw_cells segs m A0 cs H)); kx_lia
              | H : ro_cells segs m ?A0 ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (rd_at_sub segs m A0 n A N (rd_at_ro_cells segs m A0 cs H)); kx_lia
              | H : stk segs m ?lo ?hi |- _ => apply (rd_at_sub segs m lo (hi - lo) A N); [apply (rd_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
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
  Hypothesis TL11 : tl = 11.
  Hypothesis XMC : zd_memcpyZ_stmtA.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -496)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation WDM := [(DST, DST + dcap); (SPV - 496, SPV - 256)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).

  (* [comment removed for export] *)
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt ilow oend ie0 ie1 ie2 ie3 :=
    (rw_cells bsegs mm (SPV + -256) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 b0; C8 b1; C8 b2; C8 b3;
                                     C8 adt; C8 ilow; C8 oend; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  (* [comment removed for export] *)
  Notation SVS mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Notation WDF := [(DST, DST + dcap); (SPV - 496, SPV - 104)].
  Notation WD := [(DST, DST + dcap)].
  Notation TBLV := (Z_to_bv 64 ACTZ_TBL41).
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
                   (SPV - 496 + 240 <= S \/ S + len <= SPV - 496) /\ (SPV - 256 + 152 <= S \/ S + len <= SPV - 256) /\
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
    assert (ZS3 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 240 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 240 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV - 256 - -256 < 2 ^ 64 /\ 0 <= 152 < 2 ^ 64 /\ 0 <= SPV - 256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -256 - -256 < 2 ^ 64 /\ 0 <= 152 < 2 ^ 64 /\ 0 <= SPV + -256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia);
    assert (ZS9 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 136 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS10 : 0 <= SPV + -360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV + -360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS11 : 0 <= SPV + -352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV + -352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS12 : 0 <= SPV + -104 - -104 < 2 ^ 64 /\ 0 <= 104 < 2 ^ 64 /\ 0 <= SPV + -104 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS13 : 0 <= SPV + -256 - -256 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -256 < 2 ^ 64) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 496 \/ SPV - 496 + 240 <= DST) /\ (DST + dcap <= SPV - 256 \/ SPV - 256 + 152 <= DST) /\
                 (SPV - 256 + 152 <= DT \/ DT + 16388 <= SPV - 256) /\ (SPV - 496 + 240 <= DT \/ DT + 16388 <= SPV - 496) /\
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

  (* [comment removed for export] *)
  Ltac sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS :=
    sfacts0 MU0 USRC DSTA AW0 R1 R2;
    pose proof (rng_shspanZ _ _ _ RSRCS) as RSz;
    lazymatch goal with U : unpoisoned ?mm SRC (SRC + n) |- _ =>
      pose proof (unpoisoned_unpZ mm _ _ SRC (SRC + n) U ltac:(lia) ltac:(clear - R2; lia) ltac:(unfold KXKEND; clear - R2; lia)) as USz end.
  (* [comment removed for export] *)
  Ltac kcleanF :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < dcap -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < dcap -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : aro_client RNG m0 |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac lclean3 :=
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
           end.
  Ltac lsideF := lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- _ => lside
    end.
  Ltac zsfactsF :=
    assert (ZF1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF3 : 0 <= SRC - 0 < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= SRC < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF4 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 256 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF5 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Notation KW mb x5 x6 x8 x9 x14 x15 x16 x17 x25 x28 x30 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 :=
    (forall mm' (y1 y7 y10 y11 y12 y13 y18 y19 y20 y21 y22 y23 y24 y26 y27 y29 y31 : word),
        munch WD mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (X41SA SPV mm' (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) OEND w6 w7 w8 w9
          (Z_to_bv 64 (DT + 4)) w11 w12 w13 w14 w15 w16) -> X41SH SPV mm' -> bytes_at bsegs mm' SRC src ->
        evtF bsegs RNG POST (ST 0xa5fc0 mm' y1 x5 x6 y7 x8 x9 y10 y11 y12 y13 x14 x15 x16 x17 y18 y19 y20 y21 y22 y23 y24 x25 y26 y27 x28 y29 x30 y31)).
  Notation X41PF := (AZ_huf_dx41_fq.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo).
  Notation x41pf_transport := (AZ_huf_dx41_fq.x41pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo).
  Lemma x41_fi_8 : forall mb mm R ol dl o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 (c3 e3 z0 z1 z2 : word) (ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew : word)
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x30 x31 : word) (u0 u1 u2 u9 : word),
    X41PF mm ->
    munch WDF mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    X41SA SPV mm (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803))
      (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + ol)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (65128)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o0)) ->
    X41SH SPV mm ->
    X41SB SPV mm u0 u1 u2 z2 z1 z0 (Z_to_bv 64 (DST + o3 + dl)) (Z_to_bv 64 (SRC + i0 - bv_unsigned z0 / 8)) (Z_to_bv 64 (SRC + i1 - bv_unsigned z1 / 8)) u9 (Z_to_bv 64 ACTZ_TBL41) (Z_to_bv 64 (dl)) ->
    (ARGS mm ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt (Z_to_bv 64 (SRC)) oew (Z_to_bv 64 (SRC + je0)) (Z_to_bv 64 (SRC + je1)) (Z_to_bv 64 (SRC + je2)) (Z_to_bv 64 (SRC + je3))) ->
    bytes_at bsegs mm SRC src ->
    1 <= R -> 7 * R <= i0 -> i0 + 8 <= n -> 7 * R <= i1 -> i1 + 8 <= n -> 7 * R <= i2 -> i2 + 8 <= n -> 7 * R <= i3 -> i3 + 8 <= n ->
    0 <= dl -> 0 <= o0 -> o0 + dl + 5 * R <= dcap -> 0 <= o1 -> o1 + dl + 5 * R <= dcap -> 0 <= o2 -> o2 + dl + 5 * R <= dcap -> 0 <= o3 -> o3 + dl + 5 * R = ol -> ol <= dcap ->
    6 <= je0 <= n -> 6 <= je1 <= n -> 6 <= je2 <= n -> 6 <= je3 <= n -> 0 < dcap -> 9 <= n ->
    0 <= bv_unsigned z0 <= 63 -> 0 <= bv_unsigned z1 <= 63 -> 0 <= bv_unsigned z2 <= 63 ->
    (forall mm' (z0' z1' z2' z3' : word) (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
        X41PF mm' ->
        munch WDF mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        X41SA SPV mm' (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803))
          (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + ol)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (65128)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o0)) ->
        X41SH SPV mm' ->
        X41SB SPV mm' u0 u1 z3' z2' z1' z0' (Z_to_bv 64 (DST + o3 + dl)) (Z_to_bv 64 (SRC + i0 - bv_unsigned z0' / 8)) (Z_to_bv 64 (SRC + i1 - bv_unsigned z1' / 8)) (Z_to_bv 64 (SRC + i2 - bv_unsigned z2' / 8)) (Z_to_bv 64 ACTZ_TBL41) (Z_to_bv 64 (dl)) ->
        (ARGS mm' ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt (Z_to_bv 64 (SRC)) oew (Z_to_bv 64 (SRC + je0)) (Z_to_bv 64 (SRC + je1)) (Z_to_bv 64 (SRC + je2)) (Z_to_bv 64 (SRC + je3))) ->
        bytes_at bsegs mm' SRC src ->
        0 <= bv_unsigned z0' <= 63 -> 0 <= bv_unsigned z1' <= 63 -> 0 <= bv_unsigned z2' <= 63 -> 0 <= bv_unsigned z3' <= 63 ->
        evtF bsegs RNG POST (ST 0xa5568 mm' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DT + 4)) y19 y20 y21 y22 y23 y24 y25
          y26 (Z_to_bv 64 (SRC + i3 - bv_unsigned z3' / 8)) y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST 0xa54f4 mm x1 x5 c3 x7 x8 x9 x10 x11 x12 x13 SB x15 x16 x17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 (SRC + i2 - bv_unsigned z2 / 8)) (Z_to_bv 64 (151050438420815295)) x22 x23 x24 x25
      x26 (Z_to_bv 64 (SRC + i3)) x28 e3 x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mb mm R ol dl o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 c3 e3 z0 z1 z2 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew
      x1 x5 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x30 x31
      u0 u1 u2 u9
      PV MU WM MU0 WM0 MI OUT DTB SA SH SBK AR SRCB HR HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HDL HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HOL HJE0 HJE1 HJE2 HJE3 DP N9 HZ0 HZ1 HZ2 KH.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS3 LO.
    sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS. dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. zsfacts. zsfactsF. kcleanF.
    assert (TBLC : tbl_in bsegs mm ACTZ_TBL41 64 1 0 0 63) by exact (actz_tbl41 mm MI).
    assert (KF : (0 <= o0 <= 4294967296) /\ (0 <= o1 <= 4294967296) /\ (0 <= o2 <= 4294967296) /\ (0 <= o3 <= 4294967296) /\ (0 <= dl <= 4294967296) /\
                 (0 <= o0 + dl <= 4294967296) /\ (0 <= o1 + dl <= 4294967296) /\ (0 <= o2 + dl <= 4294967296) /\ (0 <= o3 + dl <= 4294967296) /\
                 (4096 <= DST + o0 <= 140737488355323) /\ (4096 <= DST + o1 <= 140737488355323) /\ (4096 <= DST + o2 <= 140737488355323) /\ (4096 <= DST + o3 <= 140737488355323) /\
                 (4096 <= DST + o0 + dl <= 140737488355323) /\ (4096 <= DST + o1 + dl <= 140737488355323) /\ (4096 <= DST + o2 + dl <= 140737488355323) /\ (4096 <= DST + o3 + dl <= 140737488355323) /\
                 (4103 <= SRC + i0 <= 140737488355320) /\ (4103 <= SRC + i1 <= 140737488355320) /\ (4103 <= SRC + i2 <= 140737488355320) /\ (4103 <= SRC + i3 <= 140737488355320) /\
                 (5 <= dcap - o0 <= 4294967296) /\ (5 <= dcap - o1 <= 4294967296) /\ (5 <= dcap - o2 <= 4294967296) /\ (5 <= dcap - o3 <= 4294967296) /\
                 (5 <= dcap - (o0 + dl) <= 4294967296) /\ (5 <= dcap - (o1 + dl) <= 4294967296) /\ (5 <= dcap - (o2 + dl) <= 4294967296) /\ (5 <= dcap - (o3 + dl) <= 4294967296) /\
                 (5 <= ol - o3 <= 4294967296) /\ (5 <= ol - (o3 + dl) <= 4294967296) /\ (5 <= ol <= 4294967296) /\ (0 <= dcap - ol <= 4294967296) /\
                 (7 <= i0 <= 4294967296) /\ (7 <= i1 <= 4294967296) /\ (7 <= i2 <= 4294967296) /\ (7 <= i3 <= 4294967296) /\
                 (8 <= n - i0 <= 4294967296) /\ (8 <= n - i1 <= 4294967296) /\ (8 <= n - i2 <= 4294967296) /\ (8 <= n - i3 <= 4294967296) /\
                 (1 <= dcap <= 4294967296) /\ (9 <= n <= 4294967296) /\ (4096 <= DST + ol <= 140737488355328))
      by (clear - HR HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HDL HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HOL HJE0 HJE1 HJE2 HJE3 DP N9 R1 R2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 & KF13 & KF14 & KF15 & KF16 & KF17 & KF18 & KF19 & KF20 & KF21 & KF22 & KF23 &
                                       KF24 & KF25 & KF26 & KF27 & KF28 & KF29 & KF30 & KF31 & KF32 & KF33 & KF34 & KF35 & KF36 & KF37 & KF38 & KF39 & KF40 & KF41 & KF42 & KF43 & KF44).
    assert (KZ2 : (0 <= bv_unsigned z2 / 8 <= 7) /\ (4096 <= SRC + i2 - bv_unsigned z2 / 8 <= 140737488355320))
      by (clear - HZ2 HI2 HI2b R2 KF20; Z.div_mod_to_equations; lia).
    destruct KZ2 as (KZ2a & KZ2b).
    destruct PV as (SV & STK).
    assert (PVD : disjoint_from WDF (SPV + -104) 104 /\ disjoint_from WDF lo (SPV + -496 - lo)) by (cbn [disjoint_from]; clear - R1 LO OS1; lia).
    pose proof (munch_refl WDF mm) as MUS. pose proof (wmono_refl bsegs mm) as WMS.
    kx_autoFLA (SA, SH, SBK, AR) [KAUnp DT 16388; KAUnp SRC n; KAUnp DST dcap; KAApp DST dcap] [0xa5568] 40%nat
        [KZRange (bv_unsigned z2) 0 63; KZRange (bv_unsigned z2 / 8) 0 7; KZRange (SRC + i2 - bv_unsigned z2 / 8) 4096 140737488355320;
         KZRange o0 0 4294967296; KZRange o1 0 4294967296; KZRange o2 0 4294967296; KZRange o3 0 4294967296; KZRange dl 0 4294967296;
         KZRange (o0 + dl) 0 4294967296; KZRange (o1 + dl) 0 4294967296; KZRange (o2 + dl) 0 4294967296; KZRange (o3 + dl) 0 4294967296;
         KZRange (DST + o0) 4096 140737488355323; KZRange (DST + o1) 4096 140737488355323; KZRange (DST + o2) 4096 140737488355323; KZRange (DST + o3) 4096 140737488355323;
         KZRange (DST + o0 + dl) 4096 140737488355323; KZRange (DST + o1 + dl) 4096 140737488355323; KZRange (DST + o2 + dl) 4096 140737488355323; KZRange (DST + o3 + dl) 4096 140737488355323;
         KZRange (SRC + i0) 4103 140737488355320; KZRange (SRC + i1) 4103 140737488355320; KZRange (SRC + i2) 4103 140737488355320; KZRange (SRC + i3) 4103 140737488355320;
         KZRange (dcap - o0) 5 4294967296; KZRange (dcap - o1) 5 4294967296; KZRange (dcap - o2) 5 4294967296; KZRange (dcap - o3) 5 4294967296;
         KZRange (dcap - (o0 + dl)) 5 4294967296; KZRange (dcap - (o1 + dl)) 5 4294967296; KZRange (dcap - (o2 + dl)) 5 4294967296; KZRange (dcap - (o3 + dl)) 5 4294967296;
         KZRange (ol - o3) 5 4294967296; KZRange (ol - (o3 + dl)) 5 4294967296; KZRange ol 5 4294967296; KZRange (dcap - ol) 0 4294967296;
         KZRange i0 7 4294967296; KZRange i1 7 4294967296; KZRange i2 7 4294967296; KZRange i3 7 4294967296;
         KZRange (n - i0) 8 4294967296; KZRange (n - i1) 8 4294967296; KZRange (n - i2) 8 4294967296; KZRange (n - i3) 8 4294967296;
         KZRange dcap 1 4294967296; KZRange n 9 4294967296; KZRange (DST + ol) 4096 140737488355328;
         KZRange DST 4096 140737488355328; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328;
         KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944; KZAlign DT 4; KZRange SPV 17594333498016 140737488355328;
         KZTbl ACTZ_TBL41 64 1 0 0 63; KZImg 0x22378 0x223b8; KZImg 0x103e8 0x103f0;
         KZWr DST dcap; KZWr (SPV + -352) 96; KZDisj (SPV - 352) 96 SRC n; KZDisj (SPV - 352) 96 DT 16388;
         KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n; KZDisj DST dcap (SPV - 496) 496]
        [(DT, 16388); (SRC, n); (SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96); (SPV + -256, 152); (0x22378, 64); (0x103e8, 8)] [(DT, 16388); (SRC, n); (DST, dcap); (SPV - 496, 496)].
    all: [> aside ..].
    (* [comment removed for export] *)
    all: try clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12 KF13 KF14 KF15 KF16 KF17 KF18 KF19 KF20 KF21 KF22 KF23 KF24 KF25 KF26 KF27 KF28 KF29 KF30 KF31 KF32 KF33 KF34 KF35 KF36 KF37 KF38 KF39 KF40 KF41 KF42 KF43 KF44; try clear KZ2a KZ2b.
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr DJW RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8; try clear ZS9.
    all: try clear RSz USz ZF1 ZF2 ZF3 ZF4 ZF5 ZS10 ZS11 ZS12 ZS13.
    all: aclean.
    all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
    all: [> intros; evr; kx_mem ..].
    all: lazymatch goal with H : rw_cells bsegs ?m (SPV + -352) [_; _; C8 ?ZT; _; _; _; _; _; _; _; _; _] |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
           lazymatch ZT with ev _ ?J => kx_erange KXW (EVar J); cbn [edenot] in KXW end;
           set (z3 := ZT) in *; clearbody z3 end.
    (* [comment removed for export] *)
    all: replace (SRC + (i3 + -1 * (bv_unsigned z3 / 8))) with (SRC + i3 - bv_unsigned z3 / 8) by lia.
    all: lazymatch goal with H : rw_cells bsegs ?m (SPV + -352) _, ST1 : stk bsegs ?m lo (SPV + -496) |- _ =>
           replace (SRC + (i2 + -1 * (bv_unsigned z2 / 8))) with (SRC + i2 - bv_unsigned z2 / 8) in H by lia end.
    (* [comment removed for export] *)
    all: lclean2.
    all: lazymatch goal with MUS : munch WDF ?mm0 ?m1, WMS : wmono bsegs ?mm0 ?m1, SV1 : SVS ?m1, ST1 : stk bsegs ?m1 lo (SPV + -496) |- _ =>
           eapply KH; first [exact (conj SV1 ST1) | exact KXW | lsideF] end.
  Qed.
End DX41AM.
End CANSEC1.
