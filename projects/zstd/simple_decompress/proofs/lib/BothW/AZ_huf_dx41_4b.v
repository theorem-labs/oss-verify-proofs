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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_huf_dx41 AZ_huf_dx41_4a.
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
  Hypothesis HRL : huf_reload_int_stmtA.
  (* [comment removed for export] *)
  Hypothesis DHI : dst_hi dcap DST.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 :=
    (rw_cells bsegs mm (SPV + -480) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation WD4 := [(DST, DST + dcap); (SPV - 224, SPV - 184); (SPV - 496, SPV - 480)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).

  (* [comment removed for export] *)
  Notation K4 mb st lm x8 x9 x18 x19 x21 x22 x23 x24 x25 x26 x27 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 :=
    (forall mm' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 c' b' p' : word) (pad' : list byte),
        munch WD4 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -480) ->
        FRS mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ->
        BD4 mm' c' b' pad' p' st lm ->
        evtF bsegs RNG POST (ST 0xa3b94 mm' y1 y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 y20 x21 x22 x23 x24 x25 x26 x27
                                y28 y29 y30 y31)).

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
    assert (RFR : rng RNG (SPV - 480) 480) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
  Ltac precall m1 :=
    repeat match goal with
           | H : atoms_ok _ _ |- _ => clear H
           | H : reads_ok _ _ _ _ _ |- _ => clear H
           | H : know_ok _ _ _ _ |- _ => clear H
           | H : unpoisoned m1 _ _ |- _ => clear H
           | H : unpZ m1 _ _ |- _ => clear H
           | H : azstk _ m1 _ _ |- _ => clear H
           | H : aappW _ |- _ => clear H
           | H : rng _ (KXSHLO + _) _ |- _ => clear H
           | H : rng _ (SPV - 480) 480 |- _ => clear H
           end;
    try (repeat match goal with H : env |- _ => clear H end);
    repeat match goal with H : _ \/ _ |- _ => apply x41_held_intro in H end;
    repeat match goal with
           | H : x41_held (DST + dcap <= lo \/ _) |- _ => unfold x41_held in H
           | H : x41_held (DT + 16388 <= lo \/ _) |- _ => unfold x41_held in H
           | H : x41_held (SPV - 224 + 40 <= _ \/ _) |- _ => unfold x41_held in H
           | H : x41_held (SPV - 496 + 496 <= _ \/ _) |- _ => unfold x41_held in H
           | H : x41_held (DST + dcap <= SPV - 224 \/ _) |- _ => unfold x41_held in H
           | H : x41_held (DST + dcap <= SPV - 496 \/ _) |- _ => unfold x41_held in H
           end.
  (* [comment removed for export] *)
  Ltac rl_call BD SBH BL S len bc off cont pad bs O8 O2 B1 B0 :=
    lazymatch goal with
    | MU0 : munch _ m0 ?m1, WM0 : wmono _ m0 ?m1, MI1 : mem_inv _ ?m1, STK1 : stk _ ?m1 lo (SPV + -480),
      LO : 4096 <= lo <= SPV - 2720, KLO : 0x10007fff8000 <= lo, SPB : SPV < 2^47, SPA : SPV mod 16 = 0,
      R1 : 4096 <= DST /\ _ /\ _, R2 : 4096 <= SRC /\ _ /\ _, OS2 : SRC + n <= lo \/ SPV <= SRC, DSTA : dcap <= 0 \/ _,
      AZS : azstk RNG m0 lo SPV, ART : art m0, RSTK : rng RNG lo (SPV - lo), RI : rng_aimg RNG,
      USRC : unpoisoned m0 SRC (SRC + n), RSRC : rng RNG SRC n, RSRCS : rng RNG (shad SRC) (shspan SRC n),
      BSS : SRC <= S, BSE : S + len <= SRC + n |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) =>
      constr_eq m1 mq;
      let AW0 := fresh "AW0" in let AZmm := fresh "AZmm" in let ARTmm := fresh "ARTmm" in let RBD := fresh "RBD" in
      let AROB := fresh "AROB" in let APB := fresh "APB" in let ASTK' := fresh "ASTK'" in let BDA := fresh "BDA" in
      assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply Forall_cons; [cbn [fst snd]; unfold KHIGH; clear - LO KLO; lia | apply Forall_nil]);
      assert (AZmm : azstk RNG m1 lo SPV)
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply azstk_transport; [exact AZS | exact MU0 | exact WM0 | apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; clear - DSTA Hd; lia | exact AW0] | clear - LO; lia]
            | eapply azstk_transport; [exact AZS | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                                      | exact WM0 | exact AW0 | clear - LO; lia] ]);
      assert (ARTmm : art m1)
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply (art_transportW _ m0 m1 ART MU0 WM0); constructor; [cbn [fst]; pose proof (DHI Hd); unfold dst_hi in *; lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]]
            | eapply (art_transportW [(SPV - 2720, SPV)] m0 m1 ART); [| exact WM0 |];
              [ eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
              | constructor; [cbn [fst]; clear - LO KLO; lia | constructor] ] ]);
      assert (RBD : rng RNG (SPV + -224) 40) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]);
      assert (AROB : aro RNG m1 (SPV + -224) 40) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | clear; lia | clear; lia | exact RBD]);
      assert (APB : app_blk (SPV + -224) (SPV + -224 + 40)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]);
      assert (ASTK' : astk RNG lo (SPV + -480))
        by (split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | clear; lia | clear - LO; lia] | exact RI]]);
      assert (BDA : (SPV + -224) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia);
      let NUMS := fresh "NUMS" in
      assert (NUMS : (4096 <= SPV + -224) /\ (SPV + -224 + 40 < 2^47) /\ (4096 <= S) /\ (S + len < 2^47) /\
                     (SPV + -224 + 40 <= S \/ S + len <= SPV + -224) /\ (0 <= bc <= 64) /\ (S + 8 <= S + off) /\ (S + off <= S + len - 8) /\
                     (lo <= SPV + -480 - 16) /\ (SPV + -480 < 2^47) /\ (SPV + -224 + 40 <= lo \/ SPV + -480 <= SPV + -224) /\
                     (S + len <= lo \/ SPV + -480 <= S))
        by (clear - LO SPB R2 OS2 BSS BSE O8 O2 B1 B0; lia);
      let P1 := fresh "P" in let P2 := fresh "P" in let P3 := fresh "P" in let P4 := fresh "P" in let P5 := fresh "P" in
      let P6 := fresh "P" in let P7 := fresh "P" in let P8 := fresh "P" in let P9 := fresh "P" in let P10 := fresh "P" in
      let P11 := fresh "P" in let P12 := fresh "P" in
      destruct NUMS as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12);
      let AROS := fresh "AROS" in
      assert (AROS : aro RNG m1 S len)
        by (apply (aro_sub RNG m1 SRC n S len);
            [ split; [| split; [exact RSRC | exact RSRCS]];
              eapply unp_carryS; [exact USRC | exact MU0 | clear - R2; lia | clear - R2; lia | clear - DSTA; lia | clear - LO KLO; lia]
            | exact BSS | clear - P7 P8; lia | exact BSE ]);
      clear AW0 AZmm RBD;
      eapply evtF_cut;
        [ eapply (HRL RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -480) lo (SPV + -224) S len bc (S + off) cont pad bs);
          [ exact BD | exact SBH | exact BL | exact P1 | exact P2 | exact P3 | exact P4 | exact BDA | exact P5 | exact P6 | exact P7 | exact P8
          | exact STK1 | exact P9 | exact P10 | exact P11 | exact P12 | exact APB | exact AROB | exact AROS | exact ARTmm | exact ASTK' | exact MI1 ]
        | clear STK1 ARTmm AROB APB ASTK' AROS BDA P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12; clear BD;
          precall m1; unfold huf_reload_int_postA, bitd_cells; post_call bsegs m1; unfold x41_held in * ]
    end.
  (* [comment removed for export] *)
  Ltac after_call :=
    lazymatch goal with
    | B : rw_cells _ ?m2 (SPV + -224) (C8 ?c' :: _), S2 : stk _ ?m2 lo (SPV + -480), M2 : mem_inv _ ?m2 |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
        rename B into BD; rename S2 into STK; try rename M2 into MI
    end.

  Notation x41_g4 := (AZ_huf_dx41_4a.x41_g4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).

  (* [comment removed for export] *)
  Lemma x41_e4 : forall mb mm j off S len bs dl bc (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : word),
    munch WD4 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -480) ->
    FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 OEND ->
    BD4 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= dcap -> dcap - j < 4 -> dl = tl + 256 * rsv -> SINVA off len bc -> 0 <= bc < 2147483648 ->
    K4 mb (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) x8 x9 x18 (Z_to_bv 64 dl) Q62 x22 x23 SB x25 (Z_to_bv 64 (DT + 4)) x27 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 OEND ->
    evtF bsegs RNG POST (ST 0xa39bc mm x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 bc) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + j)) Q62 x22 x23 SB x25
                            (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31).
  Proof using CTX ACTX HRL DHI.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mb mm j off S len bs dl bc c0 pad x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 MU WM MU0 WM0 MI OUT DTB STK FR BD SBH BL BSS BSE LEN1 HJ RM HDL HS HB K.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO.
    destruct HB as (B0 & B31).
    destruct HS as [-> | (O1 & O2 & B1)].
    - (* [comment removed for export] *)
      kclean.
      assert (KF : 0 <= dcap - j <= 3 /\ 0 <= bc <= 2147483647 /\ 0 <= j <= 4294967296) by (clear - RM B0 B31 HJ R1; lia).
      pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3).
      kx_autoFLA (FR, BD) (@nil kza) [0xa3ac8] 40%nat
        [KZRange (dcap - j) 0 3; KZRange bc 0 2147483647; KZRange j 0 4294967296; KZRange dcap 0 4294967296;
         KZRange DST 4096 140737488355328; KZRange S 4096 140737488355328; KZRange SPV 17594333498016 140737488355328; KZWr (SPV + -224) 40]
        [(SPV + -480, 104); (SPV + -224, 40)] [(SPV - 480, 480)].
      all: [> aside ..].
      all: traps.
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr DJW RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8; try clear ZS9.
      all: [> kx_mem ..].
      all: eapply (x41_g4 mb); lside; first [exact K | intros; eapply K; lside].
    - destruct (Z_lt_le_dec off 8) as [O8|O8].
      + (* [comment removed for export] *)
        kclean.
        assert (KF : 0 <= dcap - j <= 3 /\ 1 <= off <= 7 /\ 0 <= bc <= 64 /\ 8 <= len - off <= 4294967296 /\ 9 <= len <= 4294967296 /\
                     0 <= j <= 4294967296) by (clear - RM O8 O1 O2 B1 B0 HJ SL32 R1; lia).
        pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6).
        kx_autoFLA (FR, BD) [KAUnp S len; KAApp (SPV - 224) 40] [0xa3ac8] 80%nat
          [KZRange (dcap - j) 0 3; KZRange (len - off) 8 4294967296; KZRange off 1 7; KZRange bc 0 64;
           KZRange len 9 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328;
           KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange SPV 17594333498016 140737488355328;
           KZWr (SPV + -224) 40; KZDisj (SPV - 224) 40 S len]
          [(S, len); (SPV + -480, 104); (SPV + -224, 40)] [(S, len); (SPV - 480, 480)].
      all: [> aside ..].
      all: traps.
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr DJW RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8; try clear ZS9.
        all: [> kx_gen_regsF [10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat] ..].
        all: [> intros; evr; kx_mem ..].
        all: eapply (x41_g4 mb); lside; first [exact K | intros; eapply K; lside].
      + (* [comment removed for export] *)
        kx_autoFLA (FR, BD) (@nil kza) [0xa3ac8] 20%nat
          [KZRange (len - off) 8 4294967296; KZRange off 8 4294967296; KZRange bc 0 64; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328;
           KZRange SPV 17594333498016 140737488355328]
          [(SPV + -480, 104); (SPV + -224, 40)] [(SPV - 480, 480)].
        all: [> aside ..].
        all: rl_call BD SBH BL S len bc off c0 pad bs O8 O2 B1 B0.
        all: after_call. all: kclean.
        all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr DJW RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8; try clear ZS9.
        all: eapply (x41_g4 mb); lside; first [exact K | intros; eapply K; lside].
  Qed.
End DX41A4.
End CANSEC1.
