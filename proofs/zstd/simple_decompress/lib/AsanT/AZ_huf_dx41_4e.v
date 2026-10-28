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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_4b AZ_huf_dx41_4c AZ_huf_dx41_4d.
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
                   (SPV - 256 + 40 <= S \/ S + len <= SPV - 256) /\ (SPV - 360 + 8 <= S \/ S + len <= SPV - 360) /\
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
    assert (ZS3 : 0 <= SPV - 256 - -256 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV - 256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -256 - -256 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV - 360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV - 360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV + -360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia).
  Ltac zsfactsS :=
    lazymatch goal with
    | BSE : ?S + ?len <= SRC + n |- _ =>
        assert (ZS9 : 0 <= S - 0 < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= S < 2 ^ 64) by (kx_clear_or; lia)
    end.
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 360 \/ SPV - 360 + 8 <= DST) /\ (DST + dcap <= SPV - 256 \/ SPV - 256 + 40 <= DST) /\
                 (SPV - 256 + 40 <= DT \/ DT + 16388 <= SPV - 256) /\ (SPV - 360 + 8 <= DT \/ DT + 16388 <= SPV - 360) /\
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

  (* [comment removed for export] *)
  Ltac p_fix :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        replace X with (DST + 3 * SG41 + (X - DST - 3 * SG41)) by lia
    end.
  Notation x41_g4 := (AZ_huf_dx41_4a.x41_g4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_e4 := (AZ_huf_dx41_4b.x41_e4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_l4_f := (AZ_huf_dx41_4c.x41_l4_f RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_l4_c := (AZ_huf_dx41_4d.x41_l4_c RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_l4_invk k := (AZ_huf_dx41_4c.x41_l4_invk RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo dtb k).
  Notation x41_b4_stmt := (AZ_huf_dx41.x41_b4_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo dtb).
  (* [comment removed for export] *)
  Lemma x41_l4_it : forall (k : nat), x41_l4_invk k -> x41_l4_invk (S k).
  Proof using CTX ACTX.
    intros k IH. unfold AZ_huf_dx41_4c.x41_l4_invk.
    intros mm rest q dl S4 n4 bs4 o4 bc4 c4 b4 pad4
      w0 w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232
      x6 x7 x8 x10 x12 x13 x14 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31
      HK SV JK MU0 WM0 MI OUT DTB STK SA SH SB4 BD BS LEN BSS BSE LEN1 HS HB HQ HD6 HQD HDL.
    destruct (Z.eq_dec o4 0) as [O0|O0].
    - (* [comment removed for export] *)
      subst o4. rewrite Z.add_0_r in BD.
      pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
      facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
      sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO. zsfacts. zsfactsS.
      dfacts MU0 UDST RDST RDSTS DSTA AW0 R1.
      assert (HJ0 : 0 <= 3 * SG41 + q) by (pose proof (Z.div_pos (dcap + 3) 4 ltac:(lia) ltac:(lia)); lia).
      assert (HQJ : 3 * SG41 <= 3 * SG41 + q) by lia.
      replace (DST + 3 * SG41 + q) with (DST + (3 * SG41 + q)) by lia.
      revert HJ0 HQJ HK HQD. generalize (3 * SG41 + q) as j. intros j HJ0 HQJ HK HQD. clear HQ.
      assert (KF : 0 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355328 /\ 6 <= dcap <= 4294967296 /\
                   4096 <= DST + dcap + -3 <= 140737488355328)
        by (clear - HJ0 HQD HD6 R1 GF1 GF2; lia).
      destruct KF as (KF1 & KF2 & KF3 & KF4 & KF5).
      kx_autoFLA (SH, BD) (@nil kza) [0xa8cb0] 20%nat
        [KZRange (dcap - j) 0 4294967296; KZRange j 0 4294967296; KZRange dcap 6 4294967296; KZRange DST 4096 140737488355328;
         KZRange (DST + j) 4096 140737488355328; KZRange (DST + dcap + -3) 4096 140737488355328; KZRange n4 1 4294967296; KZRange bc4 0 64;
         KZRange S4 4096 140737488355328; KZRange (S4 + n4) 4096 140737488355328;
         KZRange DT 4096 140737488338940; KZRange (64 - tl) 52 63;
         KZRange SPV 17594333498016 140737488355328; KZAlign SPV 16;
         KZDisj DST dcap DT 16388; KZDisj DST dcap S4 n4; KZDisj DST dcap (SPV - 496) 496;
         KZDisj (SPV - 256) 40 DT 16388; KZDisj (SPV - 256) 40 S4 n4]
        [(S4, n4); (SPV + -360, 8); (SPV + -256, 40)] [(DT, 16388); (S4, n4); (DST, dcap); (SPV - 496, 496)].
      all: [> aside ..].
      all: p_fix; eapply x41_g4; lside.
    - (* [comment removed for export] *)
      destruct (Z_lt_le_dec o4 8) as [O8|O8].
      + eapply (x41_l4_c k IH); try eassumption; clear - HS O0 O8; unfold SINVA in HS; lia.
      + eapply (x41_l4_f k IH); eassumption.
  Qed.
  (* [comment removed for export] *)
  Lemma x41_l4 : forall (k : nat), x41_l4_invk k.
  Proof using CTX ACTX.
    induction k as [|k IH].
    - unfold AZ_huf_dx41_4c.x41_l4_invk. intros * HK. intros. exfalso. change (Z.of_nat 0) with 0 in HK. lia.
    - exact (x41_l4_it k IH).
  Qed.
  (* [comment removed for export] *)
  Ltac d4_x5z :=
    cbn [edenot]; rewrite w_subw; unfold v_subw; rewrite Z_to_bv_unsigned;
    match goal with KXA : atoms_ok ?zs ?E |- context [ev ?E 20] => rewrite (KXA 20%nat) by (cbn; lia) end;
    cbn [znth]; rewrite !Z_to_bv_unsigned;
    unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus; cbn [Z.of_N].
  Ltac d4_x5 :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ ?X5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        let H := fresh "HX5" in
        assert (H : X5 = Z_to_bv 64 (64 - tl));
        [ f_equal; change 63 with (Z.ones 6); rewrite Z.land_ones by lia; d4_x5z; lia
        | rewrite H; clear H ]
    end.
  Lemma x41_d4 : x41_b4_stmt.
  Proof using CTX ACTX DHI.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    unfold AZ_huf_dx41.x41_b4_stmt.
    intros mm rest q dl Q1 Q2 Q3 S4 n4 bs4 o4 bc4 c1 c2 c3 c4 pad4
      w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w120 w128 w144 w152 w160 w168
      x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31
      SV JK MU0 WM0 MI OUT DTB STK SA SH SB B4 BS4 LEN4 BSS BSE LEN1 HS HB HQ HD6 HQD HDL.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO.
    zsfacts. kclean.
    destruct HB as (B0 & B31).
    assert (HJ0 : 0 <= 3 * SG41 + q) by (pose proof (Z.div_pos (dcap + 3) 4 ltac:(lia) ltac:(lia)); lia).
    assert (HQJ : 3 * SG41 <= 3 * SG41 + q) by lia.
    replace (DST + 3 * SG41 + q) with (DST + (3 * SG41 + q)) by lia.
    revert HJ0 HQJ HQD. generalize (3 * SG41 + q) as j. intros j HJ0 HQJ HQD. clear HQ.
    assert (KF : 0 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355328 /\ 6 <= dcap <= 4294967296 /\
                 4096 <= DST + dcap <= 140737488355328 /\ 4096 <= DST + dcap + -3 <= 140737488355328 /\ 0 <= bc4 <= 2147483647)
      by (clear - HJ0 HQD HD6 R1 GF1 GF2 B0 B31; lia).
    destruct KF as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7).
    kx_autoFLA (SH, B4) [KAApp (SPV - 256) 40] [0xa8860; 0xa8b94; 0xa8cb0] 40%nat
      [KZRange (dcap - j) 0 4294967296; KZRange j 0 4294967296; KZRange dcap 6 4294967296; KZRange DST 4096 140737488355328;
       KZRange (DST + j) 4096 140737488355328; KZRange (DST + dcap) 4096 140737488355328; KZRange (DST + dcap + -3) 4096 140737488355328;
       KZRange bc4 0 2147483647; KZRange S4 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange (64 - tl) 52 63;
       KZRange SPV 17594333498016 140737488355328; KZWr (SPV - 256) 40]
      [(SPV + -256, 40)] [(SPV - 496, 496)].
    all: [> aside ..].
    all: try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJW SZS RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8; try clear ZS9 ZS10 ZS11.
    all: [> lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8860) _ _ _ _) => kx_gen_regsF [14%nat]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8b94) _ _ _ _) => kx_gen_regsF [11%nat; 14%nat]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8cb0) _ _ _ _) => kx_gen_regsF [11%nat; 14%nat; 15%nat; 17%nat]
         end ..].
    all: [> intros; evr; try kx_mem ..].
    all: [> try (solve [lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8860) _ _ _ _) => d4_x5; p_fix; eapply (x41_l4 (S (Z.to_nat (dcap - j)))); lside
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8b94) _ _ _ _) => p_fix; eapply x41_e4; lside
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8cb0) _ _ _ _) => p_fix; eapply x41_g4; lside
         end]) ..].
  Qed.
End DX41A4.
End CANSEC1.
