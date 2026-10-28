(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42.
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

Section CANSEC1. Context {rc : runConstT}.
Section DX42BC0.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 :=
    (rw_cells bsegs mm (SPV + -408) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 w18]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRA mm j0 d j1 := (rw_cells bsegs mm (SPV + -576) [CB 40 j0; C8 d; CB 120 j1]).
  Notation FRJ mm j2 := (rw_cells bsegs mm (SPV + -216) [CB 112 j2]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).

  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333498432 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
                   (SPV - 576 + 472 <= S \/ S + len <= SPV - 576) /\ (SPV - 408 + 152 <= S \/ S + len <= SPV - 408))
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
    assert (FF : (DST + dcap <= SPV - 408 \/ SPV - 408 + 152 <= DST) /\ (DST + dcap <= SPV - 576 \/ SPV - 576 + 472 <= DST) /\
                 (SPV - 576 + 472 <= DT \/ DT + 16388 <= SPV - 576) /\ (SPV - 408 + 152 <= DT \/ DT + 16388 <= SPV - 408) /\
                 (DST + dcap <= SPV - 576 \/ SPV - 576 + 576 <= DST))
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

  Notation x42_end := (AZ_huf_dx42.x42_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x42_err := (AZ_huf_dx42.x42_err RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x42_reta0 := (AZ_huf_dx42.x42_reta0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).

  (* [comment removed for export] *)
  Lemma x42_einvB : forall mm (j0 j1 j2 : list byte) (d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : word)
      (c4 b4 p4 st4 lm4 : word) pad4,
    FRQ mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm -> stk bsegs mm lo (SPV + -576) ->
    FRA mm j0 d j1 -> FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 ->
    BD4 mm c4 b4 pad4 p4 st4 lm4 -> FRJ mm j2 ->
    EINVB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo mm.
  Proof using CTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'.
    intros until pad4. intros FQ MI OUT MU0 WM0 STK FA FR B4 FJ.
    split; [exact OUT|]. split; [exact FQ|]. split; [|split; [exact MU0 | split; [exact WM0 | exact MI]]].
    pose proof (stk_of_rw_cells bsegs mm _ _ FA) as T0. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T0.
    pose proof (stk_of_rw_cells bsegs mm _ _ FR) as T1. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T1.
    pose proof (stk_of_rw_cells bsegs mm _ _ B4) as T4. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T4.
    pose proof (stk_of_rw_cells bsegs mm _ _ FJ) as TJ. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in TJ.
    lazymatch type of T0 with stk _ _ _ ?b => replace b with (SPV + -408) in T0 by lia end.
    lazymatch type of T1 with stk _ _ _ ?b => replace b with (SPV + -256) in T1 by lia end.
    lazymatch type of T4 with stk _ _ _ ?b => replace b with (SPV + -216) in T4 by lia end.
    lazymatch type of TJ with stk _ _ _ ?b => replace b with (SPV + -104) in TJ by lia end.
    eapply stk_merge; [| exact TJ | clear - LO; lia]. eapply stk_merge; [| exact T4 | clear - LO; lia].
    eapply stk_merge; [| exact T1 | clear - LO; lia].
    eapply stk_merge; [exact STK | exact T0 | clear - LO; lia].
  Qed.

  Section C0K.
  (* [comment removed for export] *)
  Variables (dl pe1 pe2 pe3 : Z) (S1 n1 S2 n2 S3 n3 S4 n4 : Z) (bs1 bs2 bs3 bs4 : list byte) (mb : amem).
  Hypotheses (HDL : dl = tl + 256 * rsv) (PE1 : pe1 = (dcap + 3) / 4) (PE2 : pe2 = 2 * pe1) (PE3 : pe3 = 3 * pe1) (PE4 : pe3 <= dcap).
  Hypotheses (BL1 : zlen bs1 = n1) (SS1 : SRC <= S1) (SE1 : S1 + n1 <= SRC + n) (LN1 : 1 <= n1).
  Hypotheses (BL2 : zlen bs2 = n2) (SS2 : SRC <= S2) (SE2 : S2 + n2 <= SRC + n) (LN2 : 1 <= n2).
  Hypotheses (BL3 : zlen bs3 = n3) (SS3 : SRC <= S3) (SE3 : S3 + n3 <= SRC + n) (LN3 : 1 <= n3).
  Hypotheses (BL4 : zlen bs4 = n4) (SS4 : SRC <= S4) (SE4 : S4 + n4 <= SRC + n) (LN4 : 1 <= n4).
  Notation WDM := [(DST, DST + dcap); (SPV - 576, SPV - 104)].

  Ltac cside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- munch _ ?m ?m => apply munch_refl
    | |- wmono _ ?m ?m => apply wmono_refl
    | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
    | |- _ -> SINVA _ _ _ => first [assumption | intros; unfold SINVA in *; lia]
    | |- forall _, _ => idtac
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [eassumption | lia | kx_lia | idtac]
    | |- _ \/ _ => first [eassumption | lia | idtac]
    | |- Z.le _ _ => first [eassumption | lia]
    | |- Z.lt _ _ => first [eassumption | lia]
    | |- _ => first [eassumption | idtac]
    end.
  (* [comment removed for export] *)
  Ltac djf := cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].

  Notation KS1 :=
    (forall (mm' : amem) (P1 P2 P3 P4 Q1 Q2 Q3 Q4 f1 f2 f3 f4 : Z) (c1 c2 c3 c4 : word) (pad4 j0 j1 j2 : list byte)
            (w1 w2 w3 w5 w8 w13 w14 w16 : word)
            (y5 y7 y8 y11 y20 y21 y23 y25 y30 y31 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRA mm' j0 (Z_to_bv 64 dcap) j1 ->
        FRS mm' (Z_to_bv 64 dl) w1 w2 w3 (Z_to_bv 64 (DST + pe3)) w5 (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) w8
                (Z_to_bv 64 (DST + dcap - 7)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) w13 w14
                (Z_to_bv 64 Q3) w16 c1 (Z_to_bv 64 (DT + 4)) ->
        BD4 mm' c4 (Z_to_bv 64 f4) pad4 (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mm' j2 ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        (f1 <= 64 -> SINVA (Q1 - S1) n1 f1) -> 0 <= f1 < 2^31 -> S1 <= Q1 <= S1 + n1 ->
        (f2 <= 64 -> SINVA (Q2 - S2) n2 f2) -> 0 <= f2 < 2^31 -> S2 <= Q2 <= S2 + n2 ->
        (f3 <= 64 -> SINVA (Q3 - S3) n3 f3) -> 0 <= f3 < 2^31 -> S3 <= Q3 <= S3 + n3 ->
        (f4 <= 64 -> SINVA (Q4 - S4) n4 f4) -> 0 <= f4 < 2^31 -> S4 <= Q4 <= S4 + n4 ->
        DST <= P1 -> P1 <= DST + dcap -> P2 <= DST + dcap -> P3 <= DST + dcap ->
        DST + pe1 <= P2 -> DST + pe2 <= P3 -> DST + pe3 <= P4 -> P4 <= DST + dcap ->
        P1 <= DST + pe1 -> P2 <= DST + pe2 -> P3 <= DST + pe3 ->
        evtF bsegs RNG POST (ST 0x9f7f4 mm' (Z_to_bv 64 f2) y5 c2 y7 y8 (Z_to_bv 64 f1) (Z_to_bv 64 P4) y11 (Z_to_bv 64 S1)
                                (Z_to_bv 64 P3) (Z_to_bv 64 S2) (Z_to_bv 64 P2) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1))
                                (Z_to_bv 64 f3) c3 y20 y21 (Z_to_bv 64 Q2) y23 (Z_to_bv 64 P1) y25 (Z_to_bv 64 Q1) SB
                                (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 dl) y30 y31)).

  Lemma x42_c0 : FRQ mb -> KS1 ->
    (forall (mm' : amem) (P1 P2 P3 P4 Q1 Q2 Q3 Q4 f1 f2 f3 f4 : Z) (c1 c2 c3 c4 : word) (pad4 j0 j1 j2 : list byte)
            (w1 w2 w3 w5 w8 w13 w14 w16 : word)
            (y5 y6 y7 y8 y11 y20 y21 y23 y25 y30 y31 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRA mm' j0 (Z_to_bv 64 dcap) j1 ->
        FRS mm' (Z_to_bv 64 dl) w1 w2 w3 (Z_to_bv 64 (DST + pe3)) w5 (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) w8
                (Z_to_bv 64 (DST + dcap - 7)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) w13 w14
                (Z_to_bv 64 Q3) w16 c1 (Z_to_bv 64 (DT + 4)) ->
        BD4 mm' c4 (Z_to_bv 64 f4) pad4 (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mm' j2 ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        (f1 <= 64 -> SINVA (Q1 - S1) n1 f1) -> 0 <= f1 < 2^31 -> S1 <= Q1 <= S1 + n1 ->
        (f2 <= 64 -> SINVA (Q2 - S2) n2 f2) -> 0 <= f2 < 2^31 -> S2 <= Q2 <= S2 + n2 ->
        (f3 <= 64 -> SINVA (Q3 - S3) n3 f3) -> 0 <= f3 < 2^31 -> S3 <= Q3 <= S3 + n3 ->
        (f4 <= 64 -> SINVA (Q4 - S4) n4 f4) -> 0 <= f4 < 2^31 -> S4 <= Q4 <= S4 + n4 ->
        DST <= P1 -> P1 <= DST + dcap -> P2 <= DST + dcap -> P3 <= DST + dcap ->
        DST + pe1 <= P2 -> DST + pe2 <= P3 -> DST + pe3 <= P4 -> P4 <= DST + dcap ->
        evtF bsegs RNG POST (ST 0x9f7d8 mm' (Z_to_bv 64 f2) y5 y6 y7 y8 (Z_to_bv 64 f1) (Z_to_bv 64 P4) y11 (Z_to_bv 64 S1)
                                (Z_to_bv 64 P3) (Z_to_bv 64 S2) (Z_to_bv 64 P2) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1))
                                (Z_to_bv 64 f3) c3 y20 y21 (Z_to_bv 64 Q2) y23 (Z_to_bv 64 P1) y25 (Z_to_bv 64 Q1) SB
                                (Z_to_bv 64 (DST + pe3)) c2 y30 y31)).
  Proof using CTX X2OK ACTX HDL PE1 PE2 PE3 PE4 BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros FQ0 KS mm P1 P2 P3 P4 Q1 Q2 Q3 Q4 f1 f2 f3 f4 c1 c2 c3 c4 pad4 j0 j1 j2 w1 w2 w3 w5 w8 w13 w14 w16
      y5 y6 y7 y8 y11 y20 y21 y23 y25 y30 y31
      MUM WMM MU0 WM0 MI OUT DTB STK FA FR B4 FJ SB1 SB2 SB3 SB4 HS1 HF1 HQ1 HS2 HF2 HQ2 HS3 HF3 HQ3 HS4 HF4 HQ4 HP1 HU1 HU2 HU3 HP2 HP3 HP4 HP5.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (FQ : FRQ mm)
      by (eapply (rw_cells_transport bsegs _ mb mm _ _ FQ0 MUM WMM); djf; clear - LO OS1 R1; lia).
    clear FQ0.
    assert (PEF : 0 <= pe1 /\ pe1 <= pe2 /\ pe2 <= pe3 /\ pe3 <= dcap /\ pe2 <= dcap /\ pe1 <= dcap)
      by (subst pe2 pe3; clear - PE1 PE4 GF2; Z.div_mod_to_equations; lia).
    destruct PEF as (PF0 & PF1 & PF2 & PF3 & PF4 & PF5).
    assert (KF : 4096 <= P1 <= 140737488355328 /\ 4096 <= P2 <= 140737488355328 /\ 4096 <= P3 <= 140737488355328 /\ 4096 <= P4 <= 140737488355328 /\
                 0 <= pe1 <= 4294967296 /\ 0 <= pe2 <= 4294967296 /\ 0 <= pe3 <= 4294967296)
      by (clear - HP1 HU1 HU2 HU3 HP2 HP3 HP4 HP5 PF0 PF1 PF2 PF3 R1 GF1 GF2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7).
    clear PE1 PE2 PE3.
    kclean.
    kx_autoFLA FR (@nil kza) [0x9fd5c; 0x9fd60; 0x9f7f4] 30%nat
      [KZRange P1 4096 140737488355328; KZRange P2 4096 140737488355328; KZRange P3 4096 140737488355328; KZRange P4 4096 140737488355328;
       KZRange pe1 0 4294967296; KZRange pe2 0 4294967296; KZRange pe3 0 4294967296;
       KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange SPV 17594333498432 140737488355328]
      [(SPV + -408, 152)] [(SPV - 576, 576)].
    all: aside.
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fd5c) _ _ _ _) =>
             eapply x42_err; eapply (x42_einvB mm); eassumption
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fd60) _ _ _ _) =>
             try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity));
             eapply x42_reta0; [eapply (x42_einvB mm); eassumption | right; split; [vm_compute; reflexivity | lia]]
         | _ => idtac
         end.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply KS; cside.
  Qed.
  End C0K.
End DX42BC0.
End CANSEC1.
