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
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42 AZ_huf_dx42_2a AZ_huf_dx42_2b AZ_huf_dx42_2d AZ_huf_dx42_2f.
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
Section DX42B2G.
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
  Notation x42_end := (AZ_huf_dx42.x42_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation K2 mb dl pe x9 x18 x28 x29 x31 w0 w1 w4 w5 w7 w8 w9 w11 w12 :=
    (forall mm' (y1 y5 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y22 y23 y24 y25 y27 : word) (c' b' p' st' lm' : word) (pad' : list byte),
        munch WD2 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -384) ->
        (FRS mm' w0 w1 (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + pe)) w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
        BD2 mm' c' b' pad' p' st' lm' ->
        evtF bsegs RNG POST (ST 0xa9938 mm' y1 y5 (Z_to_bv 64 (DST + dcap)) y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 y19 y20 SB y22 y23 y24 y25 (Z_to_bv 64 (2305843009213693952)) y27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)).

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

  Ltac rl_call BDOFF BD SBH BL S len bc off cont pad bs HBC O8 O2 :=
    lazymatch goal with
    | MU0 : munch _ m0 ?m1, WM0 : wmono _ m0 ?m1, MI1 : mem_inv _ ?m1, STK1 : stk _ ?m1 lo (SPV + -384),
      LO : 4096 <= lo <= SPV - 2608, KLO : 0x10007fff8000 <= lo, SPB : SPV < 2^47, SPA : SPV mod 16 = 0,
      R1 : 4096 <= DST /\ _ /\ _, R2 : 4096 <= SRC /\ _ /\ _, DHI : 0 < dcap -> 0x629000 <= DST, OS2 : SRC + n <= lo \/ SPV <= SRC, DSTA : dcap <= 0 \/ _,
      AZS : azstk RNG m0 lo SPV, ART : art m0, RSTK : rng RNG lo (SPV - lo), RI : rng_aimg RNG,
      USRC : unpoisoned m0 SRC (SRC + n), RSRC : rng RNG SRC n, RSRCS : rng RNG (shad SRC) (shspan SRC n),
      BSS : SRC <= S, BSE : S + len <= SRC + n |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) =>
      constr_eq m1 mq;
      let AW0 := fresh "AW0" in let AZmm := fresh "AZmm" in let ARTmm := fresh "ARTmm" in let RBD := fresh "RBD" in
      let AROB := fresh "AROB" in let APB := fresh "APB" in let ASTK' := fresh "ASTK'" in let BDA := fresh "BDA" in
      assert (AW0 : aappW [(SPV - 2608, SPV)]) by (apply Forall_cons; [cbn [fst snd]; unfold KHIGH; clear - LO KLO; lia | apply Forall_nil]);
      assert (AZmm : azstk RNG m1 lo SPV)
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply azstk_transport; [exact AZS | exact MU0 | exact WM0 | apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; clear - DSTA Hd; lia | exact AW0] | clear - LO; lia]
            | eapply azstk_transport; [exact AZS | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                                      | exact WM0 | exact AW0 | clear - LO; lia] ]);
      assert (ARTmm : art m1)
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply (art_transportW42 _ m0 m1 ART MU0 WM0); constructor; [cbn [fst]; pose proof (DHI Hd); lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]]
            | eapply (art_transportW42 [(SPV - 2608, SPV)] m0 m1 ART); [| exact WM0 |];
              [ eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
              | constructor; [cbn [fst]; clear - LO KLO; lia | constructor] ] ]);
      assert (RBD : rng RNG (SPV + BDOFF) 40) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]);
      assert (AROB : aro RNG m1 (SPV + BDOFF) 40) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | lia | clear; lia | exact RBD]);
      assert (APB : app_blk (SPV + BDOFF) (SPV + BDOFF + 40)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | lia | clear; lia]);
      assert (ASTK' : astk RNG lo (SPV + -384))
        by (split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | lia | clear - LO; lia] | exact RI]]);
      assert (BDA : (SPV + BDOFF) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia);
      let NUMS := fresh "NUMS" in
      assert (NUMS : (4096 <= SPV + BDOFF) /\ (SPV + BDOFF + 40 < 2^47) /\ (4096 <= S) /\ (S + len < 2^47) /\
                     (SPV + BDOFF + 40 <= S \/ S + len <= SPV + BDOFF) /\ (0 <= bc <= 64) /\ (S + 8 <= S + off) /\ (S + off <= S + len - 8) /\
                     (lo <= SPV + -384 - 16) /\ (SPV + -384 < 2^47) /\ (SPV + BDOFF + 40 <= lo \/ SPV + -384 <= SPV + BDOFF) /\
                     (S + len <= lo \/ SPV + -384 <= S))
        by (clear - LO SPB R2 OS2 BSS BSE HBC O8 O2; lia);
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
      (* [comment removed for export] *)
      repeat match goal with
             | H : 0 <= bv_unsigned _ <= _ |- _ => clear H
             | H : reads_ok _ _ _ _ _ |- _ => clear H | H : know_ok _ _ _ _ |- _ => clear H | H : atoms_ok _ _ |- _ => clear H
             end;
      repeat match goal with H : mem_inv _ m1 |- _ => tryif constr_eq H MI1 then fail else clear H end;
      repeat match goal with E : env |- _ => clear E end;
      eapply evtF_cut;
        [ eapply (HRL RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -384) lo (SPV + BDOFF) S len bc (S + off) cont pad bs);
          [ exact BD | exact SBH | exact BL | exact P1 | exact P2 | exact P3 | exact P4 | exact BDA | exact P5 | exact P6 | exact P7 | exact P8
          | exact STK1 | exact P9 | exact P10 | exact P11 | exact P12 | exact APB | exact AROB | exact AROS | exact ARTmm | exact ASTK' | exact MI1 ]
        | clear ARTmm AROB APB ASTK' AROS BDA P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12;
          unfold huf_reload_int_postA, bitd_cells;
          (* [comment removed for export] *)
          let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO;
          let m2 := fresh "mc" in let cont' := fresh "cont'" in let E := fresh "E" in
          let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MI2 := fresh "MI" in let STK2 := fresh "STK" in let BD2 := fresh "BD" in
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & cont' & E & MUc & WMc & MI2 & STK2 & BD2); subst ms';
          lazymatch goal with
          | FR : rw_cells _ m1 (SPV + -384) ?cs, DTB : bytes_at _ m1 DT dtb, OUT : stk _ m1 DST (DST + dcap),
            MU : munch ?WD ?mb m1, WM : wmono _ ?mb m1, MU0 : munch W0 m0 m1, WM0 : wmono _ m0 m1,
            OS1 : DST + dcap <= lo \/ SPV <= DST, OS3 : DT + 16388 <= lo \/ SPV <= DT,
            DL : Z.of_nat (length dtb) = 16388, R3 : 4096 <= DT /\ _ |- _ =>
            let Wc := lazymatch type of MUc with munch ?W _ _ => W end in
            apply (rw_cells_transport bsegs Wc m1 m2 (SPV + -384) cs) in FR;
              [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia];
            apply (bytes_at_transport bsegs Wc m1 m2 DT dtb) in DTB; [| exact MUc | cbn [disjoint_from]; clear - DL OS3 LO R3; lia];
            apply (bytes_at_transport bsegs Wc m1 m2 S bs) in SBH; [| exact MUc | cbn [disjoint_from]; clear - BL BSS BSE OS2 LO R2; lia];
            apply (stk_transport_disjoint bsegs Wc m1 m2 DST (DST + dcap)) in OUT; [| exact MUc | exact WMc | cbn [disjoint_from]; clear - OS1 LO R1; lia];
            let MU' := fresh "MU" in
            assert (MU' : munch WD mb m2) by (eapply (munch_trans WD mb m1 m2 MU); eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear; intros; lia);
            let MU0' := fresh "MU0" in
            assert (MU0' : munch W0 m0 m2) by (eapply (munch_trans W0 m0 m1 m2 MU0); eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear - LO; intros; lia);
            let WM' := fresh "WM" in assert (WM' : wmono bsegs mb m2) by (exact (wmono_trans bsegs mb m1 m2 WM WMc));
            let WM0' := fresh "WM0" in assert (WM0' : wmono bsegs m0 m2) by (exact (wmono_trans bsegs m0 m1 m2 WM0 WMc));
            clear MU WM MU0 WM0 MUc WMc STK1 MI1 BD;
            rename MU' into MU; rename WM' into WM; rename MU0' into MU0; rename WM0' into WM0; rename MI2 into MI; rename STK2 into STK; rename BD2 into BD;
            try clear m1
          end;
          try (lazymatch goal with
               | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nr)) _ _ _ _) =>
                   replace (ret_pc (Z_to_bv 64 nr)) with (Z_to_bv 64 nr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
               end) ]
    end.
  Notation x42_c4_2 := (AZ_huf_dx42_2b.x42_c4_2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).
  Notation x42_5loop_2 := (AZ_huf_dx42_2d.x42_5loop_2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).
  Notation x42_4loop_2 := (AZ_huf_dx42_2f.x42_4loop_2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).
  (* [comment removed for export] *)
  Ltac to_c4 mb K :=
    eapply (x42_c4_2 mb); lside;
    first [ exact K
          | let B := fresh "B" in intro B;
            first [ exfalso; lia
                  | lazymatch goal with
                    | |- exists o, Z_to_bv 64 ?X = Z_to_bv 64 (?S0 + o) /\ _ => exists (X - S0); split; [f_equal; lia | unfold SINVA; lia]
                    end ] ].
  (* [comment removed for export] *)
  Ltac after_call := idtac.

  (* [comment removed for export] *)
  Lemma x42_s4_2 : forall mb mm j pe dl P S len bs bc (cont : word) pad
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
      (w0 w1 w4 w5 w7 w8 w9 w11 w12 : word),
    munch WD2 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -384) ->
    (FRS mm w0 w1 (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + pe)) w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
    BD2 mm cont (Z_to_bv 64 bc) pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= pe -> pe <= dcap -> pe - j < 8 -> dl = tl + 256 * rsv -> 0 <= bc < 2147483648 -> (bc <= 64 -> SINVA (P - S) len bc) ->
    K2 mb dl pe x9 x18 x28 x29 x31 w0 w1 w4 w5 w7 w8 w9 w11 w12 ->
    evtF bsegs RNG POST (ST 0xa8dc4 mm x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + j)) x20 SB x22 x23 x24 x25 (Z_to_bv 64 (2305843009213693952)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31).
  Proof using CTX X2OK ACTX HRL.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mb mm j pe dl P S len bs bc cont pad x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31
      w0 w1 w4 w5 w7 w8 w9 w11 w12
      MU WM MU0 WM0 MI OUT DTB STK FR BD SBH BL BSS BSE LEN1 HJ HPE RM HDL HBW HS K.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO.
    assert (KF : 0 <= j <= 4294967296 /\ 0 <= pe - j <= 7) by (clear - HJ HPE HPE RM GF2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2).
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; cycle 1.
    - (* [comment removed for export] *)
      kclean.
      kx_autoFLA (FR, BD) (@nil kza) [0xa9478] 30%nat
        [KZRange bc 65 2147483647; KZRange S 4096 140737488355328; KZRange SPV 17594333495296 140737488355328; KZWr (SPV + -184) 40;
         KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange pe 0 4294967296]
        [(SPV + -384, 120); (SPV + -184, 40)] [(SPV - 400, 400)].
      all: aside.
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: kx_mem.
      all: to_c4 mb K.
    - pose proof (HS B64) as HSI. assert (HBC : 0 <= bc <= 64) by (clear - HBW B64; lia). clear HBW B64.
      assert (O : exists off, P = S + off) by (exists (P - S); lia). destruct O as (off & ->).
      replace (S + off - S) with off in HSI by lia.
      assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - HBC; lia).
      destruct QR as (q & r & Ebc & HQ & HR).
      destruct HSI as [-> | (O1 & O2 & B1)].
      + (* [comment removed for export] *)
        kclean. subst bc.
        kx_autoFLA (FR, BD) (@nil kza) [0xa9478] 40%nat
          [KZRange (8 * q + r) 0 64; KZRange S 4096 140737488355328; KZRange SPV 17594333495296 140737488355328; KZRange DST 4096 140737488355328;
           KZRange dcap 0 4294967296; KZRange pe 0 4294967296]
          [(SPV + -384, 120); (SPV + -184, 40)] [(SPV - 400, 400)].
        all: aside.
        all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
        all: to_c4 mb K.
      + assert (KF4 : 8 <= len - off <= 4294967296 /\ 9 <= len <= 4294967296) by (clear - O2 SL32 O1; lia). destruct KF4 as (KF4 & KF3).
        destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
        * assert (KF5 : 1 <= q - off <= 8 /\ 1 <= off <= 7) by (clear - CQ C8 O1 HQ; lia). destruct KF5 as (KF5 & KF6).
          kclean. subst bc.
          kx_autoFLA (FR, BD) [KAUnp S len; KAApp (SPV - 184) 40] [0xa9478] 120%nat
          [KZRange (pe - j) 0 7; KZRange (dcap - j) 0 4294967296; KZRange (len - off) 8 4294967296; KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange len 9 4294967296; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange (S + off) 4097 140737488355320;
           KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940;
           KZRange SPV 17594333495296 140737488355328; KZWr (SPV + -184) 40; KZDisj (SPV - 184) 40 S len; KZDisj (SPV - 184) 40 DT 16388;
           KZDisj DST dcap (SPV - 400) 400]
          [(S, len); (SPV + -384, 120); (SPV + -184, 40)] [(S, len); (SPV - 400, 400)].
          all: aside.
          all: traps.
          all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
          all: try clear KF5 KF6.
          all: kx_gen_regsF [10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 5%nat; 7%nat]; intros.
          all: evr; kx_mem; kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
          all: to_c4 mb K.
        * assert (KF5 : 0 <= off - q <= 7 /\ 1 <= off <= 7) by (clear - CQ C8 O1 HQ; lia). destruct KF5 as (KF5 & KF6).
          kclean. subst bc.
          kx_autoFLA (FR, BD) [KAUnp S len; KAApp (SPV - 184) 40] [0xa9478] 120%nat
          [KZRange (pe - j) 0 7; KZRange (dcap - j) 0 4294967296; KZRange (len - off) 8 4294967296; KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange len 9 4294967296; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328; KZRange (S + off) 4097 140737488355320;
           KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940;
           KZRange SPV 17594333495296 140737488355328; KZWr (SPV + -184) 40; KZDisj (SPV - 184) 40 S len; KZDisj (SPV - 184) 40 DT 16388;
           KZDisj DST dcap (SPV - 400) 400]
          [(S, len); (SPV + -384, 120); (SPV + -184, 40)] [(S, len); (SPV - 400, 400)].
          all: aside.
          all: traps.
          all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
          all: try clear KF5 KF6.
          all: kx_gen_regsF [10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 5%nat; 7%nat]; intros.
          all: evr; kx_mem; kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
          all: to_c4 mb K.
        * (* [comment removed for export] *)
          assert (KF6 : 8 <= off <= 4294967296) by (clear - C8 O2 SL32; lia).
          kx_autoFLA (FR, BD) (@nil kza) [0xa9478] 30%nat
            [KZRange bc 0 64; KZRange (len - off) 8 4294967296; KZRange off 8 4294967296; KZRange S 4096 140737488355328; KZRange (S + len) 4096 140737488355328;
             KZRange SPV 17594333495296 140737488355328]
            [(SPV + -384, 120); (SPV + -184, 40)] [(SPV - 400, 400)].
          all: aside.
          all: rl_call (-184) BD SBH BL S len bc off cont pad bs HBC KF6 O2.
          all: after_call. all: kclean.
          all: rewrite Ebc in *.
          all: replace ((8 * q + r) mod 8) with r in * by (clear - HQ HR; Z.div_mod_to_equations; lia).
          all: replace ((8 * q + r) / 8) with q in * by (clear - HQ HR; Z.div_mod_to_equations; lia).
          all: kx_autoFLA (FR, BD) (@nil kza) [0xa9478] 20%nat
            [KZRange S 4096 140737488355328; KZRange SPV 17594333495296 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange pe 0 4294967296]
            [(SPV + -384, 120); (SPV + -184, 40)] [(SPV - 400, 400)].
          all: aside.
          all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
          all: try clear KF6.
          all: kx_gen_regsF [10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 5%nat; 7%nat]; intros.
          all: try kx_mem.
          all: to_c4 mb K.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_d4_2 : forall mb mm j pe dl P S len bs bc (cont : word) pad
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
      (w0 w1 w4 w5 w7 w8 w9 w11 w12 : word),
    munch WD2 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -384) ->
    (FRS mm w0 w1 (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + pe)) w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
    BD2 mm cont (Z_to_bv 64 bc) pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2147483648 -> (bc <= 64 -> SINVA (P - S) len bc) ->
    K2 mb dl pe x9 x18 x28 x29 x31 w0 w1 w4 w5 w7 w8 w9 w11 w12 ->
    evtF bsegs RNG POST (ST 0xa8720 mm x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + j)) x20 SB x22 x23 x24 x25 (Z_to_bv 64 (2305843009213693952)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31).
  Proof using CTX X2OK ACTX HRL.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mb mm j pe dl P S len bs bc cont pad x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31
      w0 w1 w4 w5 w7 w8 w9 w11 w12
      MU WM MU0 WM0 MI OUT DTB STK FR BD SBH BL BSS BSE LEN1 HJ HPE HDL HBW HS K.
    facts R1 R2 R3 TL RSV LO SPB KLO. subst dl.
    assert (KF : 0 <= j <= 4294967296 /\ 0 <= pe - j <= 4294967296) by (clear - HJ HPE GF2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2).
    destruct (Z_le_gt_dec bc 64) as [B64|B64].
    - kx_autoFLA (FR, BD) (@nil kza) [0xa8dc4; 0xa8f1c; 0xa877c; 0xa9478] 40%nat
        [KZRange bc 0 64; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange (pe - j) 0 4294967296; KZRange (dcap - j) 0 4294967296;
         KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535;
         KZRange S 4096 140737488355328; KZRange SPV 17594333495296 140737488355328]
        [(SPV + -384, 120); (SPV + -184, 40)] [(SPV - 400, 400)].
      all: aside.
      all: traps.
      all: kit_sh_fix.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8dc4) _ _ _ _) => eapply (x42_s4_2 mb); lside; first [exact K | exact HS | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8f1c) _ _ _ _) =>
               eapply (x42_4loop_2 (Z.to_nat pe) mb); lside; first [exact K | exact (HS B64) | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa877c) _ _ _ _) =>
               eapply (x42_5loop_2 (Z.to_nat pe) mb); lside; first [exact K | exact (HS B64) | lia]
           end.
    - kx_autoFLA (FR, BD) (@nil kza) [0xa8dc4; 0xa8f1c; 0xa877c; 0xa9478] 40%nat
        [KZRange bc 65 2147483647; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange (pe - j) 0 4294967296; KZRange (dcap - j) 0 4294967296;
         KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535;
         KZRange S 4096 140737488355328; KZRange SPV 17594333495296 140737488355328; KZWr (SPV + -184) 40]
        [(SPV + -384, 120); (SPV + -184, 40)] [(SPV - 400, 400)].
      all: aside.
      all: traps.
      all: try kx_mem.
      all: kit_sh_fix.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa8dc4) _ _ _ _) => eapply (x42_s4_2 mb); lside; first [exact K | exact HS | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa9478) _ _ _ _) => to_c4 mb K
           end.
  Qed.
End DX42B2G.
End CANSEC1.
