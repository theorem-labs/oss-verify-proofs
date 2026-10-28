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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_4e AZ_huf_dx41_1e AZ_huf_dx41_2e AZ_huf_dx41_3e AZ_huf_dx41_c0 AZ_huf_dx41_mb.
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
                   (SPV - 480 + 144 <= S \/ S + len <= SPV - 480) /\ (SPV - 224 + 120 <= S \/ S + len <= SPV - 224) /\
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
    assert (ZS3 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 136 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV + -360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV + -360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV + -352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV + -256 - -256 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia);
    assert (ZS9 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 136 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS10 : 0 <= SPV - 360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV - 360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS11 : 0 <= SPV - 352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV - 352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS12 : 0 <= SPV - 256 - -256 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV - 256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS13 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 496 \/ SPV - 496 + 496 <= DST) /\
                 (SPV - 496 + 496 <= DT \/ DT + 16388 <= SPV - 496) /\ (SPV - 496 + 136 <= DT \/ DT + 16388 <= SPV - 496) /\
                 (SPV - 360 + 8 <= DT \/ DT + 16388 <= SPV - 360) /\ (SPV - 352 + 96 <= DT \/ DT + 16388 <= SPV - 352) /\
                 (SPV - 256 + 40 <= DT \/ DT + 16388 <= SPV - 256))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4 & DJF5 & DJF6).
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
  Notation x41_c0 := (AZ_huf_dx41_c0.x41_c0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI).
  Notation x41_mb := (AZ_huf_dx41_mb.x41_mb RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX NBOK).
  Ltac fix_a5 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_ra E := lazymatch goal with |- evtF _ _ _ (MS (mkR (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_t2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_s1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a7 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a6 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a3 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a4 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac wrap_w W := lazymatch W with
    | Z_to_bv 64 _ => idtac
    | ev _ ?j => replace W with (Z_to_bv 64 (bv_unsigned W)) by (rewrite Z_to_bv_bv_unsigned; reflexivity);
                 let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H
    end.
  Ltac fix_kw := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ ?W7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?W23 _ _ _ _ _ ?W29 _ _) _ _ _ _ _ _) => wrap_w W7; wrap_w W23; wrap_w W29 end.

  (* [comment removed for export] *)
  Definition HINV (o len b : Z) : Prop := 0 <= o /\ ((o + 8 <= len /\ 0 <= b <= 8) \/ (o = 0 /\ 0 <= b <= 64)).
  (* [comment removed for export] *)
  Definition HINV2 (o len d : Z) : Prop := 0 <= o /\ ((o + 8 <= len /\ 0 <= d <= 32) \/ (o = 0 /\ 0 <= d <= 88)).
  Ltac lsideM := lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- HINV _ _ _ => unfold HINV; lia
    | |- AZ_huf_dx41_mb.HINV2 _ _ _ => unfold AZ_huf_dx41_mb.HINV2; unfold HINV in *; lia
    | |- HINV2 _ _ _ => unfold HINV2; unfold HINV in *; unfold HINV2 in *; lia
    | |- _ => lside
    end.

  Lemma x41_m1x : forall mm rest q dl S1 n1 bs1 o1 b1 S2 n2 bs2 o2 b2 S3 n3 bs3 o3 b3 S4 n4 bs4 o4 b4 (c1 c2 c3 c4 b4o p4o : word) pad4o
      (w8 w16 w40 w48 w56 w64 : word) (x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x29 x30 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
    munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm (Z_to_bv 64 DT) w8 w16 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w40 w48 w56 w64 (Z_to_bv 64 S1) (Z_to_bv 64 S2)
      (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SG41) (Z_to_bv 64 dl) (Z_to_bv 64 S3) (Z_to_bv 64 (DST + 2 * SG41))
      (Z_to_bv 64 (DST + 3 * SG41)) ->
    X41SH SPV mm ->
    X41SB SPV mm (Z_to_bv 64 (DST + SG41)) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 (DST + 3 * SG41))
      (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (DST + 2 * SG41))
      (Z_to_bv 64 (DST + SG41)) c3 c2 c1 ->
    X41BD4 SPV mm c4 b4o pad4o p4o (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    bytes_at bsegs mm S1 bs1 -> zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 -> SINVA o1 n1 b1 -> 0 <= b1 < 2147483648 ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 -> SINVA o2 n2 b2 -> 0 <= b2 < 2147483648 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 -> SINVA o3 n3 b3 -> 0 <= b3 < 2147483648 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 -> SINVA o4 n4 b4 -> 0 <= b4 < 2147483648 ->
    0 <= q -> 3 * SG41 + q + 4 <= dcap -> dl = tl + 256 * rsv ->
    evtF bsegs RNG POST (ST 0xa7744 mm (Z_to_bv 64 (DST + dcap + -3)) (Z_to_bv 64 b4) x6 x7 x8 x9 (Z_to_bv 64 (S4 + o4))
      x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 b3) x20 (Z_to_bv 64 b2) (Z_to_bv 64 (DT + 4))
      (Z_to_bv 64 (DST + 3 * SG41)) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S1 + o1))
      (Z_to_bv 64 b1) (Z_to_bv 64 (q + 4)) x29 x30 x31).
  Proof using CTX ACTX DHI.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mm rest q dl S1 n1 bs1 o1 b1 S2 n2 bs2 o2 b2 S3 n3 bs3 o3 b3 S4 n4 bs4 o4 b4 c1 c2 c3 c4 b4o p4o pad4o w8 w16 w40 w48 w56 w64
      x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x29 x30 x31
      SV JK MU0 WM0 MI OUT DTB STK FSA FSH FSB FB4 SB1 BL1 SS1 SE1 LN1 HS1 HB1 SB2 BL2 SS2 SE2 LN2 HS2 HB2
      SB3 BL3 SS3 SE3 LN3 HS3 HB3 SB4 BL4 SS4 SE4 LN4 HS4 HB4 HJ HROOM HDL.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    zsfacts. kclean.
    assert (PVD : disjoint_from WDM (SPV + -104) 104 /\ disjoint_from WDM (SPV + -216) 112) by (cbn [disjoint_from]; clear - R1 LO OS1; lia).
    assert (HE1 : dcap <= 4 * SG41 <= dcap + 3)
      by (pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)); pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)); lia).
    set (e1 := SG41) in *. assert (HE1D : e1 = SG41) by reflexivity. clearbody e1.
    assert (SFM : (S1 + n1 <= SPV - 496 \/ SPV <= S1) /\ (S2 + n2 <= SPV - 496 \/ SPV <= S2) /\
                  (S3 + n3 <= SPV - 496 \/ SPV <= S3) /\ (S4 + n4 <= SPV - 496 \/ SPV <= S4) /\
                  (4096 <= S1 <= 140737488355328) /\ (4096 <= S1 + n1 <= 140737488355328) /\ (1 <= n1 <= 4294967296) /\
                  (4096 <= S2 <= 140737488355328) /\ (4096 <= S2 + n2 <= 140737488355328) /\ (1 <= n2 <= 4294967296) /\
                  (4096 <= S3 <= 140737488355328) /\ (4096 <= S3 + n3 <= 140737488355328) /\ (1 <= n3 <= 4294967296) /\
                  (4096 <= S4 <= 140737488355328) /\ (4096 <= S4 + n4 <= 140737488355328) /\ (1 <= n4 <= 4294967296) /\
                  (4096 <= DST + (q + 4) <= 140737488355328) /\ (4096 <= DST + e1 + (q + 4) <= 140737488355328) /\
                  (4096 <= DST + 2 * e1 + (q + 4) <= 140737488355328) /\ (4096 <= DST + 3 * e1 + (q + 4) <= 140737488355328) /\
                  (0 <= e1 <= 4294967296) /\ (4 <= q + 4 <= 4294967296))
      by (clear - SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4 OS2 LO R1 R2 HJ HE1 HROOM; lia).
    destruct SFM as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7 & SF8 & SF9 & SF10 & SF11 & SF12 & SF13 & SF14 & SF15 & SF16 &
                     SF17 & SF18 & SF19 & SF20 & SF21 & SF22).
    pose proof (munch_refl WDM mm) as MUS. pose proof (wmono_refl bsegs mm) as WMS.
    kx_autoFLA (FSA, FSH, FSB, FB4) (@nil kza) [0xa77a4] 30%nat
      [KZRange (q + 4) 4 4294967296; KZRange e1 0 4294967296; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296;
       KZRange (DST + (q + 4)) 4096 140737488355328; KZRange (DST + e1 + (q + 4)) 4096 140737488355328;
       KZRange (DST + 2 * e1 + (q + 4)) 4096 140737488355328; KZRange (DST + 3 * e1 + (q + 4)) 4096 140737488355328;
       KZRange b4 0 2147483647; KZRange SPV 17594333498016 140737488355328;
       KZRange S1 4096 140737488355328; KZRange (S1 + n1) 4096 140737488355328; KZRange n1 1 4294967296;
       KZRange S2 4096 140737488355328; KZRange (S2 + n2) 4096 140737488355328; KZRange n2 1 4294967296;
       KZRange S3 4096 140737488355328; KZRange (S3 + n3) 4096 140737488355328; KZRange n3 1 4294967296;
       KZRange S4 4096 140737488355328; KZRange (S4 + n4) 4096 140737488355328; KZRange n4 1 4294967296;
       KZWr (SPV + -256) 40; KZDisj DST dcap (SPV - 496) 496; KZDisj (SPV - 496) 496 DT 16388;
       KZDisj (SPV - 496) 496 S1 n1; KZDisj (SPV - 496) 496 S2 n2; KZDisj (SPV - 496) 496 S3 n3; KZDisj (SPV - 496) 496 S4 n4]
      [(SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96); (SPV + -256, 40)] [(SPV - 496, 496)].
    all: aside.
    all: aclean.
    all: [> kx_gen_regsF [5%nat; 6%nat; 11%nat; 12%nat; 13%nat; 17%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
    all: [> intros; evr; kx_mem ..].
    all: [> kx_sx3; kx_strip_mod ..].
    all: lazymatch goal with MUS : munch WDM ?mm0 ?m1, WMS : wmono bsegs ?mm0 ?m1 |- _ =>
           first [ pose proof (rw_cells_transport bsegs _ mm0 m1 _ _ SV MUS WMS (proj1 PVD)) as SV1; clear SV | rename SV into SV1 ];
           first [ pose proof (rw_cells_transport bsegs _ mm0 m1 _ _ JK MUS WMS (proj2 PVD)) as JK1; clear JK | rename JK into JK1 ];
           clear MUS WMS end.
    all: fix_t2 (DST + 2 * e1 + (q + 4)). all: fix_a4 (DST + (q + 4)). all: fix_a5 (DST + e1 + (q + 4)). all: fix_a6 (DST + 3 * e1 + (q + 4)).
    all: lclean2.
    all: subst e1.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
           eapply (x41_c0 m rest (q + 4) dl S1 n1 bs1 o1 b1 S2 n2 bs2 o2 b2 S3 n3 bs3 o3 b3 S4 n4 bs4 o4 b4 c1 c2 c3 c4 pad4o) end.
    all: lsideM.
  Qed.

  Lemma x41_m1 : forall (k : nat) mb mm rest q sh dl o1 S1 n1 bs1 b1 o2 S2 n2 bs2 b2 o3 S3 n3 bs3 b3 o4 S4 n4 bs4 b4
      (c1 c2 c3 c4 c4o b4o p4o : word) pad4o (w8 w16 w40 w48 w56 w64 : word)
      (x1 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x29 x31 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest ->
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
    HINV o1 n1 b1 -> HINV o2 n2 b2 -> HINV o3 n3 b3 -> HINV o4 n4 b4 ->
    dcap - 3 * SG41 - q <= Z.of_nat k -> 0 <= q -> 3 * SG41 + q + 4 <= dcap -> sh = 64 - tl -> dl = tl + 256 * rsv ->
    evtF bsegs RNG POST (ST 0xa6bf4 mm x1 (Z_to_bv 64 b4) x6 x7 c4 x9 (Z_to_bv 64 (S4 + o4)) x11 x12 x13 x14 x15 x16 x17 x18
      (Z_to_bv 64 b3) SB (Z_to_bv 64 b2) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + 3 * SG41)) (Z_to_bv 64 (S3 + o3))
      (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 b1) (Z_to_bv 64 q) x29 (Z_to_bv 64 sh) x31).
  Proof using CTX ACTX DHI NBOK.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    (* [comment removed for export] *)
    assert (PVD : disjoint_from WDM (SPV + -104) 104 /\ disjoint_from WDM (SPV + -216) 112) by (cbn [disjoint_from]; clear - R1 LO OS1; lia).
    induction k as [|k IH]; intros mb mm rest q sh dl o1 S1 n1 bs1 b1 o2 S2 n2 bs2 b2 o3 S3 n3 bs3 b3 o4 S4 n4 bs4 b4 c1 c2 c3 c4 c4o b4o p4o pad4o w8 w16 w40 w48 w56 w64 x1 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x29 x31
      SV JK MU WM MU0 WM0 MI OUT DTB STK FSA FSH FSB FB4 SB1 BL1 SS1 SE1 LN1 SB2 BL2 SS2 SE2 LN2 SB3 BL3 SS3 SE3 LN3 SB4 BL4 SS4 SE4 LN4 HI1 HI2 HI3 HI4 HK HJ HROOM HSH HDL; [exfalso; clear - HK HJ HROOM; lia|].
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    ffacts OS1 OS3 LO. dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. zsfacts. kclean.
    assert (TBL : tbl_in_log bsegs mm DT sh 2 4 0 12).
    { apply (tbl_in_log_bytes_at bsegs mm DT dtb sh 2 4 0 12 DTB); [clear - R3 DL HSH TL; lia | clear - HSH TL; lia |].
      intros i Hi. replace (64 - sh) with tl in Hi by (clear - HSH; lia). destruct (NBOK i Hi) as (bb & Hb & Hr). exists bb. split; [exact Hb|].
      pose proof (bv_unsigned_in_range 8 bb). lia. }
    unfold HINV in HI1, HI2, HI3, HI4.
    assert (HE1 : dcap <= 4 * SG41 <= dcap + 3)
      by (pose proof (Z.div_mod (dcap + 3) 4 ltac:(lia)); pose proof (Z.mod_pos_bound (dcap + 3) 4 ltac:(lia)); lia).
    set (e1 := SG41) in *. assert (HE1D : e1 = SG41) by reflexivity. clearbody e1.
    assert (KF : (4 <= dcap - 3 * e1 - q <= 4294967296) /\ (4 <= dcap - 2 * e1 - q <= 4294967296) /\ (4 <= dcap - e1 - q <= 4294967296) /\
                 (4 <= dcap - q <= 4294967296) /\ (0 <= q <= 4294967296) /\ (0 <= e1 <= 4294967296) /\ (0 <= e1 + q <= 4294967296) /\
                 (0 <= 2 * e1 + q <= 4294967296) /\ (0 <= 3 * e1 + q <= 4294967296) /\
                 (4096 <= DST + q <= 140737488355324) /\ (4096 <= DST + e1 + q <= 140737488355324) /\
                 (4096 <= DST + 2 * e1 + q <= 140737488355324) /\ (4096 <= DST + 3 * e1 + q <= 140737488355324) /\
                 (52 <= sh <= 63) /\ (0 <= b1 <= 64) /\ (0 <= b2 <= 64) /\ (0 <= b3 <= 64) /\ (0 <= b4 <= 64) /\
                 (4096 <= DST + e1 <= 140737488355328) /\ (4096 <= DST + 2 * e1 <= 140737488355328) /\ (4096 <= DST + 3 * e1 <= 140737488355328) /\
                 (4 <= dcap <= 4294967296))
      by (clear - HJ HE1 HROOM HSH TL R1 HI1 HI2 HI3 HI4; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 & KF13 & KF14 & KF15 & KF16 & KF17 & KF18 & KF19 & KF20 & KF21 & KF22).
    assert (SFM : (4096 <= S1 <= 140737488355328) /\ (4096 <= S1 + n1 <= 140737488355328) /\ (1 <= n1 <= 4294967296) /\ (DST + dcap <= S1 \/ S1 + n1 <= DST) /\
                  (4096 <= S2 <= 140737488355328) /\ (4096 <= S2 + n2 <= 140737488355328) /\ (1 <= n2 <= 4294967296) /\ (DST + dcap <= S2 \/ S2 + n2 <= DST) /\
                  (4096 <= S3 <= 140737488355328) /\ (4096 <= S3 + n3 <= 140737488355328) /\ (1 <= n3 <= 4294967296) /\ (DST + dcap <= S3 \/ S3 + n3 <= DST) /\
                  (4096 <= S4 <= 140737488355328) /\ (4096 <= S4 + n4 <= 140737488355328) /\ (1 <= n4 <= 4294967296) /\ (DST + dcap <= S4 \/ S4 + n4 <= DST))
      by (clear - SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4 R2 DJ1 GF4 GF5 GF6; lia).
    destruct SFM as (SF1a & SF1b & SF1c & SF1d & SF2a & SF2b & SF2c & SF2d & SF3a & SF3b & SF3c & SF3d & SF4a & SF4b & SF4c & SF4d).
    (* [comment removed for export] *)
    pose proof (munch_refl WDM mm) as MUS. pose proof (wmono_refl bsegs mm) as WMS.
    (* [comment removed for export] *)
    kx_autoFLA (FSA, FSH, FSB, FB4) [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap] [0xa6eec] 300%nat
      [KZRange (dcap - 3 * e1 - q) 4 4294967296; KZRange (dcap - 2 * e1 - q) 4 4294967296; KZRange (dcap - e1 - q) 4 4294967296;
       KZRange (dcap - q) 4 4294967296; KZRange q 0 4294967296; KZRange e1 0 4294967296; KZRange (e1 + q) 0 4294967296;
       KZRange (2 * e1 + q) 0 4294967296; KZRange (3 * e1 + q) 0 4294967296;
       KZRange (DST + q) 4096 140737488355324; KZRange (DST + e1 + q) 4096 140737488355324;
       KZRange (DST + 2 * e1 + q) 4096 140737488355324; KZRange (DST + 3 * e1 + q) 4096 140737488355324;
       KZRange (DST + e1) 4096 140737488355328; KZRange (DST + 2 * e1) 4096 140737488355328; KZRange (DST + 3 * e1) 4096 140737488355328;
       KZRange sh 52 63; KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
       KZRange dcap 4 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940;
       KZRange SPV 17594333498016 140737488355328; KZTblLog DT sh 2 4 0 12;
       KZRange S1 4096 140737488355328; KZRange (S1 + n1) 4096 140737488355328; KZRange n1 1 4294967296; KZDisj DST dcap S1 n1;
       KZRange S2 4096 140737488355328; KZRange (S2 + n2) 4096 140737488355328; KZRange n2 1 4294967296; KZDisj DST dcap S2 n2;
       KZRange S3 4096 140737488355328; KZRange (S3 + n3) 4096 140737488355328; KZRange n3 1 4294967296; KZDisj DST dcap S3 n3;
       KZRange S4 4096 140737488355328; KZRange (S4 + n4) 4096 140737488355328; KZRange n4 1 4294967296; KZDisj DST dcap S4 n4;
       KZWr DST dcap;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 496) 496;
       KZDisj (SPV - 496) 136 DT 16388; KZDisj (SPV - 360) 8 DT 16388; KZDisj (SPV - 352) 96 DT 16388; KZDisj (SPV - 256) 40 DT 16388]
      [(DT, 16388); (SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96); (SPV + -256, 40)] [(DT, 16388); (DST, dcap); (SPV - 496, 496)].
    all: [> aside ..].
    all: traps.
    all: try clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12 KF13 KF14 KF15 KF16 KF17 KF18 KF19 KF20 KF21 KF22.
    all: aclean.
    all: [> kx_gen_regsF [15%nat; 16%nat; 18%nat; 27%nat; 31%nat] ..].
    all: [> intros; evr; kx_mem ..].
    all: [> kx_sx3; kx_strip_mod ..].
    (* [comment removed for export] *)
    all: lazymatch goal with MUS : munch WDM ?mm0 ?m1, WMS : wmono bsegs ?mm0 ?m1 |- _ =>
           first [ pose proof (rw_cells_transport bsegs _ mm0 m1 _ _ SV MUS WMS (proj1 PVD)) as SV1; clear SV | rename SV into SV1 ];
           first [ pose proof (rw_cells_transport bsegs _ mm0 m1 _ _ JK MUS WMS (proj2 PVD)) as JK1; clear JK | rename JK into JK1 ];
           clear MUS WMS end.
    all: fix_ra (DST + e1 + q). all: fix_s1 (DST + 3 * e1 + q). all: fix_a7 (DST + 2 * e1 + q).
    all: fix_a1 (DST + q). all: fix_a2 (DST + e1 + q). all: fix_a3 (DST + 2 * e1 + q). all: fix_a4 (DST + 3 * e1 + q).
    all: fix_kw.
    all: lclean2.
    all: subst e1.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
           eapply (x41_mb m m q sh dl o1 S1 n1 bs1 _ o2 S2 n2 bs2 _ _ o3 S3 n3 bs3 _ _ o4 S4 n4 bs4 _ _) end.
    all: lsideM.
    (* [comment removed for export] *)
    all: try (intros mm' o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' c4o' y1 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y29 y31
                MU' WM' MU0' WM0' MI' OUT' DTB' STK' FSA' FSH' FSB' FB4' SB1' SB2' SB3' SB4' O1a O1b B1' O2a O2b B2' O3a O3b B3' O4a O4b B4' HROOM';
              lazymatch type of MU' with munch _ ?mc _ =>
              eapply (IH mc mm' rest (q + 4) sh dl o1' S1 n1 bs1 b1' o2' S2 n2 bs2 b2' o3' S3 n3 bs3 b3' o4' S4 n4 bs4 b4');
              [ exact (rw_cells_transport bsegs _ mc mm' _ _ SV1 MU' WM' (proj1 PVD))
              | exact (rw_cells_transport bsegs _ mc mm' _ _ JK1 MU' WM' (proj2 PVD))
              | lsideM.. ] end).
    (* [comment removed for export] *)
    all: intros mm' o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y20 y29 y30 y31
                MU' WM' MU0' WM0' MI' OUT' DTB' STK' FSA' FSH' FSB' FB4' SB1' SB2' SB3' SB4' HS1' HB1' HS2' HB2' HS3' HB3' HS4' HB4';
         lazymatch type of MU' with munch _ ?mc _ =>
         eapply (x41_m1x mm' rest q dl S1 n1 bs1 o1' b1' S2 n2 bs2 o2' b2' S3 n3 bs3 o3' b3' S4 n4 bs4 o4' b4');
         [ exact (rw_cells_transport bsegs _ mc mm' _ _ SV1 MU' WM' (proj1 PVD))
         | exact (rw_cells_transport bsegs _ mc mm' _ _ JK1 MU' WM' (proj2 PVD))
         | lsideM.. ] end.
  Qed.
End DX41AM.
End CANSEC1.
