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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42 AZ_huf_dx42_4a AZ_huf_dx42_4b AZ_huf_dx42_4d AZ_huf_dx42_4f AZ_huf_dx42_4g AZ_huf_dx42_3a AZ_huf_dx42_3b AZ_huf_dx42_3d AZ_huf_dx42_3f AZ_huf_dx42_3g AZ_huf_dx42_2a AZ_huf_dx42_2b AZ_huf_dx42_2d AZ_huf_dx42_2f AZ_huf_dx42_2g AZ_huf_dx42_1a AZ_huf_dx42_1b AZ_huf_dx42_1d AZ_huf_dx42_1f AZ_huf_dx42_1g.
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

Section CANSEC1. Context {rc : runConstT}.
Section DX42BC0.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis HRL : huf_reload_int_stmtA.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2608 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STC ra mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 (SPV + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 678828) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 :=
    (rw_cells bsegs mm (SPV + -384) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -264) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -184) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -144) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 2608, SPV)].
  Notation WD4 := [(DST, DST + dcap); (SPV - 264, SPV - 224); (SPV - 400, SPV - 384)].
  Notation WD3 := [(DST, DST + dcap); (SPV - 224, SPV - 184); (SPV - 400, SPV - 384)].
  Notation WD2 := [(DST, DST + dcap); (SPV - 184, SPV - 144); (SPV - 400, SPV - 384)].
  Notation WD1 := [(DST, DST + dcap); (SPV - 144, SPV - 104); (SPV - 296, SPV - 280); (SPV - 400, SPV - 384)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).

  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333497904 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 2608, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 400) 400) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
                   (SPV - 264 + 160 <= S \/ S + len <= SPV - 264) /\ (SPV - 400 + 136 <= S \/ S + len <= SPV - 400))
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
    assert (FF : (DST + dcap <= SPV - 400 \/ SPV - 400 + 136 <= DST) /\ (DST + dcap <= SPV - 264 \/ SPV - 264 + 160 <= DST) /\
                 (SPV - 264 + 160 <= DT \/ DT + 16388 <= SPV - 264) /\ (SPV - 400 + 136 <= DT \/ DT + 16388 <= SPV - 400) /\
                 (DST + dcap <= SPV - 400 \/ SPV - 400 + 400 <= DST))
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
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 706616) _ _ _ _) => kx_trap_fast end).
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
  Notation x42_ret := (AZ_huf_dx42.x42_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x42_d4 := (AZ_huf_dx42_4g.x42_d4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).
  Notation x42_d4_3 := (AZ_huf_dx42_3g.x42_d4_3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).
  Notation x42_d4_2 := (AZ_huf_dx42_2g.x42_d4_2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).
  Notation x42_d4_1 := (AZ_huf_dx42_1g.x42_d4_1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).

  (* [comment removed for export] *)
  Lemma x42_einvB : forall mm (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word)
      (c1 b1 p1 st1 lm1 c2 b2 p2 st2 lm2 c3 b3 p3 st3 lm3 c4 b4 p4 st4 lm4 : word) pad1 pad2 pad3 pad4,
    FRQ mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm -> stk bsegs mm lo (SPV + -384) ->
    FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ->
    BD1 mm c1 b1 pad1 p1 st1 lm1 -> BD2 mm c2 b2 pad2 p2 st2 lm2 -> BD3 mm c3 b3 pad3 p3 st3 lm3 -> BD4 mm c4 b4 pad4 p4 st4 lm4 ->
    EINVB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo mm.
  Proof using CTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'.
    intros until pad4. intros FQ MI OUT MU0 WM0 STK FR B1 B2 B3 B4.
    split; [exact OUT|]. split; [exact FQ|]. split; [|split; [exact MU0 | split; [exact WM0 | exact MI]]].
    pose proof (stk_of_rw_cells bsegs mm _ _ FR) as T0. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T0.
    pose proof (stk_of_rw_cells bsegs mm _ _ B4) as T4. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T4.
    pose proof (stk_of_rw_cells bsegs mm _ _ B3) as T3. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T3.
    pose proof (stk_of_rw_cells bsegs mm _ _ B2) as T2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T2.
    pose proof (stk_of_rw_cells bsegs mm _ _ B1) as T1. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T1.
    lazymatch type of T0 with stk _ _ _ ?b => replace b with (SPV + -264) in T0 by lia end.
    lazymatch type of T4 with stk _ _ _ ?b => replace b with (SPV + -224) in T4 by lia end.
    lazymatch type of T3 with stk _ _ _ ?b => replace b with (SPV + -184) in T3 by lia end.
    lazymatch type of T2 with stk _ _ _ ?b => replace b with (SPV + -144) in T2 by lia end.
    lazymatch type of T1 with stk _ _ _ ?b => replace b with (SPV + -104) in T1 by lia end.
    eapply stk_merge; [| exact T1 | clear - LO; lia]. eapply stk_merge; [| exact T2 | clear - LO; lia].
    eapply stk_merge; [| exact T3 | clear - LO; lia]. eapply stk_merge; [| exact T4 | clear - LO; lia].
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
  Notation WDM := [(DST, DST + dcap); (SPV - 384, SPV - 104)].

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

  Lemma x42_c0 : FRQ mb ->
    (forall (mm' : amem) (P1 P2 P3 P4 Q1 Q2 Q3 Q4 f1 f2 f3 f4 : Z) (c1' c2' c3' c4' : word) (pad1' pad2' pad3' pad4' : list byte)
            (w0 w4 w5 w7 w8 w11 w12 : word)
            (y1 y5 y6 y7 y8 y10 y11 y13 y14 y15 y16 y20 y22 y23 y24 y25 y26 y27 y28 y29 y31 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -384) ->
        FRS mm' w0 (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8
                (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 (DST + pe2)) w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap) ->
        BD1 mm' c1' (Z_to_bv 64 f1) pad1' (Z_to_bv 64 Q1) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
        BD2 mm' c2' (Z_to_bv 64 f2) pad2' (Z_to_bv 64 Q2) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
        BD3 mm' c3' (Z_to_bv 64 f3) pad3' (Z_to_bv 64 Q3) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
        BD4 mm' c4' (Z_to_bv 64 f4) pad4' (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        (f1 <= 64 -> SINVA (Q1 - S1) n1 f1) -> 0 <= f1 < 2147483648 -> S1 <= Q1 <= S1 + n1 ->
        (f2 <= 64 -> SINVA (Q2 - S2) n2 f2) -> 0 <= f2 < 2147483648 -> S2 <= Q2 <= S2 + n2 ->
        (f3 <= 64 -> SINVA (Q3 - S3) n3 f3) -> 0 <= f3 < 2147483648 -> S3 <= Q3 <= S3 + n3 ->
        (f4 <= 64 -> SINVA (Q4 - S4) n4 f4) -> 0 <= f4 < 2147483648 -> S4 <= Q4 <= S4 + n4 ->
        DST <= P1 -> P1 <= DST + dcap -> P2 <= DST + dcap -> P3 <= DST + dcap -> DST + pe1 <= P2 -> DST + pe2 <= P3 -> DST + pe3 <= P4 -> P4 <= DST + dcap ->
        evtF bsegs RNG POST (ST 0xa74b4 mm' y1 y5 y6 y7 y8 (Z_to_bv 64 P4) y10 y11 (Z_to_bv 64 P1) y13 y14 y15 y16
                                (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 P3) (Z_to_bv 64 P2) y20 SB y22 y23 y24 y25 y26 y27 y28 y29
                                (Z_to_bv 64 (DT + 4)) y31)).
  Proof using CTX X2OK ACTX HRL HDL PE1 PE2 PE3 PE4 BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros FQ0 mm P1 P2 P3 P4 Q1 Q2 Q3 Q4 f1 f2 f3 f4 c1 c2 c3 c4 pad1 pad2 pad3 pad4 w0 w4 w5 w7 w8 w11 w12
      y1 y5 y6 y7 y8 y10 y11 y13 y14 y15 y16 y20 y22 y23 y24 y25 y26 y27 y28 y29 y31
      MUM WMM MU0 WM0 MI OUT DTB STK FR B1 B2 B3 B4 SB1 SB2 SB3 SB4 HS1 HF1 HQ1 HS2 HF2 HQ2 HS3 HF3 HQ3 HS4 HF4 HQ4 HP1 HU1 HU2 HU3 HP2 HP3 HP4 HP5.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (FQ : FRQ mm)
      by (eapply (rw_cells_transport bsegs _ mb mm _ _ FQ0 MUM WMM); djf; clear - LO OS1 R1; lia).
    clear FQ0 MUM WMM.
    assert (PEF : 0 <= pe1 /\ pe1 <= pe2 /\ pe2 <= pe3 /\ pe3 <= dcap /\ pe2 <= dcap /\ pe1 <= dcap)
      by (subst pe2 pe3; clear - PE1 PE4 GF2; Z.div_mod_to_equations; lia).
    destruct PEF as (PF0 & PF1 & PF2 & PF3 & PF4 & PF5).
    assert (KF : 4096 <= P1 <= 140737488355328 /\ 4096 <= P2 <= 140737488355328 /\ 4096 <= P3 <= 140737488355328 /\ 4096 <= P4 <= 140737488355328 /\
                 0 <= pe1 <= 4294967296 /\ 0 <= pe2 <= 4294967296 /\ 0 <= pe3 <= 4294967296)
      by (clear - HP1 HU1 HU2 HU3 HP2 HP3 HP4 HP5 PF0 PF1 PF2 PF3 R1 GF1 GF2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7).
    clear PE1 PE2 PE3.
    kclean.
    kx_autoFLA FR (@nil kza) [0xa7cb0; 0xa7444; 0xa74cc] 30%nat
      [KZRange P1 4096 140737488355328; KZRange P2 4096 140737488355328; KZRange P3 4096 140737488355328; KZRange P4 4096 140737488355328;
       KZRange pe1 0 4294967296; KZRange pe2 0 4294967296; KZRange pe3 0 4294967296;
       KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange SPV 17594333495296 140737488355328]
      [(SPV + -384, 120)] [(SPV - 400, 400)].
    all: aside.
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7cb0) _ _ _ _) =>
             eapply x42_err; eapply (x42_einvB mm); eassumption
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7444) _ _ _ _) =>
             try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity));
             eapply x42_ret; [eapply (x42_einvB mm); eassumption | right; split; [vm_compute; reflexivity | lia]]
         | _ => idtac
         end.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 P1) with (Z_to_bv 64 (DST + (P1 - DST))) by (f_equal; lia).
    eapply (x42_d4_1 mm mm (P1 - DST) pe1 dl Q1 S1 n1 bs1 f1 c1 pad1); cside.
    intros mm1 u1 u5 u7 u8 u10 u11 u12 u13 u14 u15 u16 u17 u20 u22 u23 u24 u25 v12 c1f b1f p1f st1f lm1f pad1f
      MU1 WM1 MU01 WM01 MI1 OUT1 DTB1 STK1 FR1 B1f.
    assert (SB2a : bytes_at bsegs mm1 S2 bs2) by (eapply (bytes_at_transport bsegs _ mm mm1 S2 bs2 SB2 MU1); djf; clear - SS2 SE2 BL2 R2 DJ1 OS2 LO; lia).
    assert (SB3a : bytes_at bsegs mm1 S3 bs3) by (eapply (bytes_at_transport bsegs _ mm mm1 S3 bs3 SB3 MU1); djf; clear - SS3 SE3 BL3 R2 DJ1 OS2 LO; lia).
    assert (SB4a : bytes_at bsegs mm1 S4 bs4) by (eapply (bytes_at_transport bsegs _ mm mm1 S4 bs4 SB4 MU1); djf; clear - SS4 SE4 BL4 R2 DJ1 OS2 LO; lia).
    assert (B2a : BD2 mm1 c2 (Z_to_bv 64 f2) pad2 (Z_to_bv 64 Q2) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm mm1 _ _ B2 MU1 WM1); djf; clear - R1 LO OS1; lia).
    assert (B3a : BD3 mm1 c3 (Z_to_bv 64 f3) pad3 (Z_to_bv 64 Q3) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm mm1 _ _ B3 MU1 WM1); djf; clear - R1 LO OS1; lia).
    assert (B4a : BD4 mm1 c4 (Z_to_bv 64 f4) pad4 (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm mm1 _ _ B4 MU1 WM1); djf; clear - R1 LO OS1; lia).
    assert (FQ1 : FRQ mm1) by (eapply (rw_cells_transport bsegs _ mm mm1 _ _ FQ MU1 WM1); djf; clear - R1 LO OS1; lia).
    clear MU1 WM1 SB1 SB2 SB3 SB4 B2 B3 B4 FR FQ.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 P2) with (Z_to_bv 64 (DST + (P2 - DST))) by (f_equal; lia).
    eapply (x42_d4_2 mm1 mm1 (P2 - DST) pe2 dl Q2 S2 n2 bs2 f2 c2 pad2); cside.
    intros mm2 u1b u5b u7b u8b u10b u11b u12b u13b u14b u15b u16b u17b u19b u20b u22b u23b u24b u25b u27b c2f b2f p2f st2f lm2f pad2f
      MU2 WM2 MU02 WM02 MI2 OUT2 DTB2 STK2 FR2 B2f.
    assert (SB3b : bytes_at bsegs mm2 S3 bs3) by (eapply (bytes_at_transport bsegs _ mm1 mm2 S3 bs3 SB3a MU2); djf; clear - SS3 SE3 BL3 R2 DJ1 OS2 LO; lia).
    assert (SB4b : bytes_at bsegs mm2 S4 bs4) by (eapply (bytes_at_transport bsegs _ mm1 mm2 S4 bs4 SB4a MU2); djf; clear - SS4 SE4 BL4 R2 DJ1 OS2 LO; lia).
    assert (B3b : BD3 mm2 c3 (Z_to_bv 64 f3) pad3 (Z_to_bv 64 Q3) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm1 mm2 _ _ B3a MU2 WM2); djf; clear - R1 LO OS1; lia).
    assert (B4b : BD4 mm2 c4 (Z_to_bv 64 f4) pad4 (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm1 mm2 _ _ B4a MU2 WM2); djf; clear - R1 LO OS1; lia).
    assert (FQ2 : FRQ mm2) by (eapply (rw_cells_transport bsegs _ mm1 mm2 _ _ FQ1 MU2 WM2); djf; clear - R1 LO OS1; lia).
    assert (B1g : BD1 mm2 c1f b1f pad1f p1f st1f lm1f) by (eapply (rw_cells_transport bsegs _ mm1 mm2 _ _ B1f MU2 WM2); djf; clear - R1 LO OS1; lia).
    clear MU2 WM2 SB2a SB3a SB4a B2a B3a B4a FR1 FQ1 B1f.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 P3) with (Z_to_bv 64 (DST + (P3 - DST))) by (f_equal; lia).
    eapply (x42_d4_3 mm2 mm2 (P3 - DST) pe3 dl Q3 S3 n3 bs3 f3 c3 pad3); cside.
    intros mm3 u1c u5c u7c u8c u10c u11c u12c u13c u14c u15c u16c u17c u18c u19c u20c u22c u23c u24c c3f b3f p3f st3f lm3f pad3f
      MU3 WM3 MU03 WM03 MI3 OUT3 DTB3 STK3 FR3 B3f.
    assert (SB4c : bytes_at bsegs mm3 S4 bs4) by (eapply (bytes_at_transport bsegs _ mm2 mm3 S4 bs4 SB4b MU3); djf; clear - SS4 SE4 BL4 R2 DJ1 OS2 LO; lia).
    assert (B4c : BD4 mm3 c4 (Z_to_bv 64 f4) pad4 (Z_to_bv 64 Q4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm2 mm3 _ _ B4b MU3 WM3); djf; clear - R1 LO OS1; lia).
    assert (FQ3 : FRQ mm3) by (eapply (rw_cells_transport bsegs _ mm2 mm3 _ _ FQ2 MU3 WM3); djf; clear - R1 LO OS1; lia).
    assert (B1h : BD1 mm3 c1f b1f pad1f p1f st1f lm1f) by (eapply (rw_cells_transport bsegs _ mm2 mm3 _ _ B1g MU3 WM3); djf; clear - R1 LO OS1; lia).
    assert (B2h : BD2 mm3 c2f b2f pad2f p2f st2f lm2f) by (eapply (rw_cells_transport bsegs _ mm2 mm3 _ _ B2f MU3 WM3); djf; clear - R1 LO OS1; lia).
    clear MU3 WM3 SB3b SB4b B3b B4b FR2 FQ2 B1g B2f.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 P4) with (Z_to_bv 64 (DST + (P4 - DST))) by (f_equal; lia).
    eapply (x42_d4 mm3 mm3 (P4 - DST) dl Q4 S4 n4 bs4 f4 c4 pad4); cside.
    intros mm4 z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12' v13 c4f b4f p4f st4f lm4f pad4f
      MU4 WM4 MU04 WM04 MI4 OUT4 DTB4 STK4 FR4 B4f.
    assert (FQ4 : FRQ mm4) by (eapply (rw_cells_transport bsegs _ mm3 mm4 _ _ FQ3 MU4 WM4); djf; clear - R1 LO OS1; lia).
    assert (B1i : BD1 mm4 c1f b1f pad1f p1f st1f lm1f) by (eapply (rw_cells_transport bsegs _ mm3 mm4 _ _ B1h MU4 WM4); djf; clear - R1 LO OS1; lia).
    assert (B2i : BD2 mm4 c2f b2f pad2f p2f st2f lm2f) by (eapply (rw_cells_transport bsegs _ mm3 mm4 _ _ B2h MU4 WM4); djf; clear - R1 LO OS1; lia).
    assert (B3i : BD3 mm4 c3f b3f pad3f p3f st3f lm3f) by (eapply (rw_cells_transport bsegs _ mm3 mm4 _ _ B3f MU4 WM4); djf; clear - R1 LO OS1; lia).
    eapply x42_end; [| exact FR4 | exact B1i | exact B2i | exact B3i | exact B4f].
    eapply (x42_einvB mm4); [exact FQ4 | exact MI4 | exact OUT4 | exact MU04 | exact WM04 | exact STK4 | exact FR4 | exact B1i | exact B2i | exact B3i | exact B4f].
  Qed.
  End C0K.
End DX42BC0.
End CANSEC1.
