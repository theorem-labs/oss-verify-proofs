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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_4e AZ_huf_dx41_1e AZ_huf_dx41_2e AZ_huf_dx41_3e AZ_huf_dx41_c0 AZ_huf_dx41_m1.
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
  Notation Q62 := (Z_to_bv 64 4611686018427387904).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).
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
    assert (ZS12 : 0 <= SPV + -256 - -256 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS13 : 0 <= SPV + -216 - -216 < 2 ^ 64 /\ 0 <= 112 < 2 ^ 64 /\ 0 <= SPV + -216 < 2 ^ 64) by (kx_clear_or; lia).
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
  Notation x41_c0 := (AZ_huf_dx41_c0.x41_c0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI).
  Notation x41_m1 := (AZ_huf_dx41_m1.x41_m1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI NBOK).
  Notation HINV := AZ_huf_dx41_m1.HINV.
  Ltac lsideM := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- AZ_huf_dx41_m1.HINV _ _ _ => first [assumption | unfold AZ_huf_dx41_m1.HINV; unfold HINVA in *; lia]
    | |- SINVA _ _ _ => unfold SINVA; unfold HINVA in *; lia
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia | apply bv64_eqm_k; reflexivity]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [assumption | lia | unfold HINVA in *; lia | idtac]
    | |- _ \/ _ => first [assumption | lia | idtac]
    | |- Z.le _ _ => first [assumption | lia | unfold HINVA in *; lia]
    | |- Z.lt _ _ => first [assumption | lia]
    | |- _ => eassumption
    end.

  (* [comment removed for export] *)
  Lemma x41_m0 : x41_m0_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo dtb.
  Proof using CTX ACTX DHI NBOK.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    (* [comment removed for export] *)
    unfold x41_m0_stmt.
    intros mm rest dl S1 n1 bs1 o1 b1 S2 n2 bs2 o2 b2 S3 n3 bs3 o3 b3 S4 n4 bs4 o4 b4 c1 c2 c3 c4 pad4
      w8 w16 w40 w48 w56 w64 w72 w80 w88 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      SV JK MU0 WM0 MI OUT DTB STK FSA FSH FSB B4 SB1 BL1 SS1 SE1 LN1 HI1 SB2 BL2 SS2 SE2 LN2 HI2 SB3 BL3 SS3 SE3 LN3 HI3
      SB4 BL4 SS4 SE4 LN4 HI4 HS1 HD6 HDL.
    subst dl. facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (HE1 : 4 * SG41 <= dcap + 3 < 4 * SG41 + 4)
      by (pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)); pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)); lia).
    remember SG41 as e1 eqn:HE1d in *.
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    ffacts OS1 OS3 LO. kclean.
    pose proof HI1 as HI1'. pose proof HI2 as HI2'. pose proof HI3 as HI3'. pose proof HI4 as HI4'.
    unfold HINVA in HI1', HI2', HI3', HI4'.
    assert (KF : (0 <= e1 <= 4294967296) /\ (0 <= 3 * e1 <= 4294967296) /\ (0 <= dcap - 3 * e1 <= 4294967296) /\ (0 <= 2 * e1 <= 4294967296) /\
                 (4096 <= DST + e1 <= 140737488355328) /\ (4096 <= DST + 2 * e1 <= 140737488355328) /\ (4096 <= DST + 3 * e1 <= 140737488355328) /\
                 (4096 <= S1 + o1 <= 140737488355328) /\ (4096 <= S2 + o2 <= 140737488355328) /\ (4096 <= S3 + o3 <= 140737488355328) /\ (4096 <= S4 + o4 <= 140737488355328) /\
                 (0 <= b1 <= 64) /\ (0 <= b2 <= 64) /\ (0 <= b3 <= 64) /\ (0 <= b4 <= 64) /\
                 (4096 <= S1 <= 140737488355328) /\ (4096 <= S2 <= 140737488355328) /\ (4096 <= S3 <= 140737488355328) /\ (4096 <= S4 <= 140737488355328) /\
                 (1 <= n1 <= 4294967296) /\ (1 <= n2 <= 4294967296) /\ (1 <= n3 <= 4294967296) /\ (1 <= n4 <= 4294967296) /\
                 (4096 <= DST + dcap <= 140737488355328) /\ (4096 <= DST + dcap + -3 <= 140737488355328) /\ (4096 <= SRC + 14 <= 281474976710656) /\
                 (4096 <= S2 + 8 <= 281474976710656) /\ (4096 <= S3 + 8 <= 281474976710656) /\ (4096 <= S4 + 8 <= 281474976710656))
      by (clear - HE1 HD6 R1 R2 HS1 HI1' HI2' HI3' HI4' SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 & KF13 & KF14 & KF15 & KF16 & KF17 & KF18 & KF19 & KF20 & KF21 & KF22 & KF23 & KF24 & KF25 & KF26 & KF27 & KF28 & KF29).
    (* [comment removed for export] *)
    assert (SFM : (SPV - 496 + 280 <= S1 \/ S1 + n1 <= SPV - 496) /\ (SPV - 496 + 280 <= S2 \/ S2 + n2 <= SPV - 496) /\
                  (SPV - 496 + 280 <= S3 \/ S3 + n3 <= SPV - 496) /\ (SPV - 496 + 280 <= S4 \/ S4 + n4 <= SPV - 496) /\
                  (SPV - 496 + 280 <= DT \/ DT + 16388 <= SPV - 496))
      by (clear - SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4 OS2 OS3 LO R2 R3; lia).
    destruct SFM as (SF1d & SF2d & SF3d & SF4d & SFTd).
    pose proof (munch_refl WDM mm) as MUS. pose proof (wmono_refl bsegs mm) as WMS.
    kx_autoFLA (FSA, FSH, FSB, B4) (@nil kza) [0xa6bf4; 0xa77a4] 64%nat
      [KZRange e1 0 4294967296; KZRange (3 * e1) 0 4294967296; KZRange (dcap - 3 * e1) 0 4294967296; KZRange (2 * e1) 0 4294967296;
       KZRange (DST + e1) 4096 140737488355328; KZRange (DST + 2 * e1) 4096 140737488355328; KZRange (DST + 3 * e1) 4096 140737488355328;
       KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944;
       KZRange (DST + dcap) 4096 140737488355328; KZRange (DST + dcap + -3) 4096 140737488355328;
       KZRange SPV 17594333498016 140737488355328; KZRange (tl + 256 * rsv) 1 65535; KZRange tl 1 12; KZRange rsv 0 255;
       KZRange SRC 4096 140737488355328; KZRange (SRC + 14) 4096 281474976710656;
       KZRange S1 4096 140737488355328; KZRange S2 4096 140737488355328; KZRange S3 4096 140737488355328; KZRange S4 4096 140737488355328;
       KZRange (S2 + 8) 4096 281474976710656; KZRange (S3 + 8) 4096 281474976710656; KZRange (S4 + 8) 4096 281474976710656;
       KZRange (S1 + o1) 4096 140737488355328; KZRange (S2 + o2) 4096 140737488355328; KZRange (S3 + o3) 4096 140737488355328; KZRange (S4 + o4) 4096 140737488355328;
       KZRange n1 1 4294967296; KZRange n2 1 4294967296; KZRange n3 1 4294967296; KZRange n4 1 4294967296;
       KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
       KZWr (SPV + -496) 136; KZWr (SPV + -352) 96;
       KZDisj (SPV - 496) 280 S1 n1; KZDisj (SPV - 496) 280 S2 n2; KZDisj (SPV - 496) 280 S3 n3; KZDisj (SPV - 496) 280 S4 n4;
       KZDisj (SPV - 496) 280 DT 16388; KZDisj DST dcap (SPV - 496) 496]
      [(SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96); (SPV + -256, 40)] [(SPV - 496, 496)].
    all: [> aside ..].
    all: try clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12 KF13 KF14 KF15 KF16 KF17 KF18 KF19 KF20 KF21 KF22 KF23 KF24 KF25 KF26 KF27 KF28 KF29.
    all: try clear HI1' HI2' HI3' HI4'.
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr DJW RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8; try clear ZS9.
    all: aclean.
    all: [> lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa6bf4) _ _ _ _) => kx_gen_regsF [1%nat; 6%nat; 7%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 29%nat; 31%nat]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa77a4) _ _ _ _) => kx_gen_regsF [5%nat; 6%nat; 11%nat; 12%nat; 13%nat; 17%nat; 28%nat; 29%nat; 30%nat; 31%nat]
         | |- _ => idtac
         end ..].
    all: [> intros; evr; kx_mem ..].
    all: [> kx_sx3; kx_strip_mod ..].
    (* [comment removed for export] *)
    all: clear MUS WMS.
    (* [comment removed for export] *)
    all: kit_sh_fix.
    all: try replace (SRC + 14) with (S1 + 8) in * by (clear - HS1; lia).
    all: subst e1.
    all: lclean2.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa6bf4) _ _ ?m1 _) =>
             (* [comment removed for export] *)
             eapply (x41_m1 (Z.to_nat (dcap - 3 * SG41)) m1 m1 rest _ _ (tl + 256 * rsv)
                            o1 S1 n1 bs1 b1 o2 S2 n2 bs2 b2 o3 S3 n3 bs3 b3 o4 S4 n4 bs4 b4 c1 c2 c3 c4 c4 (Z_to_bv 64 b4) (Z_to_bv 64 (S4 + o4)) pad4); lsideM
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa77a4) _ _ ?m1 _) =>
             (* [comment removed for export] *)
             pose proof (x41_c0 m1 rest 0 (tl + 256 * rsv) S1 n1 bs1 o1 b1 S2 n2 bs2 o2 b2 S3 n3 bs3 o3 b3 S4 n4 bs4 o4 b4 c1 c2 c3 c4 pad4) as C0;
             rewrite ?Z.add_0_r in C0; eapply C0; lsideM
         end.
  Qed.
End DX41AM.
End CANSEC1.
