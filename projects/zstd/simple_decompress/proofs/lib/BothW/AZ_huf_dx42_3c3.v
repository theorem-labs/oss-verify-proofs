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
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42 AZ_huf_dx42_3a AZ_huf_dx42_3b AZ_huf_dx42_3c4.
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
Section DX42B3C3.
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
  Notation K3 mb dl pe x9 x25 x27 x28 x29 x31 w0 w4 w5 w7 w8 w9 w10 w11 w12 :=
    (forall mm' (y1 y5 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y22 y23 y24 : word) (c' b' p' st' lm' : word) (pad' : list byte),
        munch WD3 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -384) ->
        (FRS mm' w0 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
        BD3 mm' c' b' pad' p' st' lm' ->
        evtF bsegs RNG POST (ST 0xaab44 mm' y1 y5 (Z_to_bv 64 (DST + dcap)) y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 SB y22 y23 y24 x25 (Z_to_bv 64 (2305843009213693952)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)).

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
  Notation x42_c4_3 := (AZ_huf_dx42_3b.x42_c4_3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).
  (* [comment removed for export] *)
  Notation HK5 jb mb P S len bs pad dl pe pe9 pe7 pe2 sh nd x8 x9 x22 x25 x27 x28 x29 x31
      w0 w4 w5 w7 w8 w9 w10 w11 w12 :=
    (forall mm' j' bc' (cont' y1 y5 y7 y10 y12 y13 y14 y15 y16 y17 : word),
        munch WD3 mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -384) ->
        (FRS mm' w0 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
        BD3 mm' cont' (Z_to_bv 64 bc') pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        bytes_at bsegs mm' S bs -> jb < j' <= pe -> 0 <= bc' <= 64 -> SINVA (P - S) len bc' ->
        evtF bsegs RNG POST (ST 0xa998c mm' y1 y5 (Z_to_bv 64 (DST + dcap)) y7 x8 x9 y10 (Z_to_bv 64 (bc')) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (64)) (Z_to_bv 64 (pe9)) SB x22 (Z_to_bv 64 (sh)) (Z_to_bv 64 (nd)) x25 (Z_to_bv 64 (2305843009213693952)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)).
  (* [comment removed for export] *)
  Ltac to_c4 mb K :=
    eapply (x42_c4_3 mb); lside;
    first [ exact K
          | let B := fresh "B" in intro B;
            first [ exfalso; lia
                  | lazymatch goal with
                    | |- exists o, Z_to_bv 64 ?X = Z_to_bv 64 (?S0 + o) /\ _ => exists (X - S0); split; [f_equal; lia | unfold SINVA; lia]
                    end ] ].
  (* [comment removed for export] *)
  Ltac mid_run FR BD STOPS R BCMAX lv j idx lenw bc sh pe :=
        kx_autoFLA (FR, BD) [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 224) 40] STOPS 90%nat
          [KZRange (pe - j) R 4294967296; KZRange (dcap - j) R 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange pe 0 4294967296; KZRange DST 4096 140737488355328;
           KZRange (DST + j) 4096 (140737488355328 - R);
           KZRange idx 0 4095; KZRange (bv_unsigned lenw) 1 2; KZRange bc 0 BCMAX; KZRange lv 1 2; KZWord (DT + 4 * idx + 7) 1 lv;
           KZRange SPV 17594333495296 140737488355328; KZRange DT 4096 140737488338940; KZRange sh 52 63;
           KZWr DST dcap; KZWr (SPV + -224) 40;
           KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 400) 400; KZDisj (SPV - 224) 40 DT 16388]
          [(DT, 16388); (SPV + -384, 120); (SPV + -224, 40)] [(DT, 16388); (DST, dcap); (SPV - 400, 400)].
  (* [comment removed for export] *)
  Ltac mid_sides HK HSH TL K :=
    first [ exact HK | exact K
          | apply (x42_idx_lt tl); [rewrite HSH; repeat (rewrite Z.mod_small by lia); reflexivity | exact TL]
          | apply x42_len_ob; assumption
          | lazymatch goal with |- _ <= bv_unsigned (ev ?E ?k) <= _ => let H := fresh "KXLR" in kx_erange H (EVar k); exact H end
          | lia ].
  Notation x42_5m4_3 := (AZ_huf_dx42_3c4.x42_5m4_3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL).

  (* [comment removed for export] *)
  Lemma x42_5m3_3 : forall jb mb mm j pe pe9 pe7 pe2 sh nd dl P S len bs bc idx (cont lenw : word) pad
      (x1 x5 x7 x8 x9 x13 x14 x15 x16 x17 x18 x22 x25 x27 x28 x29 x31 : word)
      (w0 w4 w5 w7 w8 w9 w10 w11 w12 : word),
    munch WD3 mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -384) ->
    (FRS mm w0 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
    BD3 mm cont (Z_to_bv 64 bc) pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at bsegs mm S bs -> zlen bs = len -> SRC <= S -> S + len <= SRC + n -> 1 <= len ->
    HK5 jb mb P S len bs pad dl pe pe9 pe7 pe2 sh nd x8 x9 x22 x25 x27 x28 x29 x31
       w0 w4 w5 w7 w8 w9 w10 w11 w12 ->
    jb <= j -> 0 <= j -> 8 <= pe - j -> pe <= dcap -> pe9 = DST + pe + -9 -> pe7 = DST + pe + -7 -> pe2 = DST + pe + -2 -> sh = 64 - tl -> nd = -1 * DT + -5 -> dl = tl + 256 * rsv -> 0 <= bc <= 700 ->
    S <= P -> P + 8 <= S + len -> 0 <= idx < 2^tl -> 1 <= bv_unsigned lenw <= 2 ->
    K3 mb dl pe x9 x25 x27 x28 x29 x31 w0 w4 w5 w7 w8 w9 w10 w11 w12 ->
    evtF bsegs RNG POST (ST 0xa9c6c mm x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4 * idx + 4)) lenw x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (64)) (Z_to_bv 64 (pe9)) SB x22 (Z_to_bv 64 (sh)) (Z_to_bv 64 (nd)) x25 (Z_to_bv 64 (2305843009213693952)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31).
  Proof using CTX X2OK ACTX HRL.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros jb mb mm j pe pe9 pe7 pe2 sh nd dl P S len bs bc idx cont lenw pad x1 x5 x7 x8 x9 x13 x14 x15 x16 x17 x18 x22 x25 x27 x28 x29 x31
      w0 w4 w5 w7 w8 w9 w10 w11 w12
      MU WM MU0 WM0 MI OUT DTB STK FR BD SBH BL BSS BSE LEN1 HK HJB HJ ROOM HPE HPE9 HPE7 HPE2 HSH HND HDL HBC OP1 OP2 HI HL K.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2. sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. ffacts OS1 OS3 LO.
    dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. kclean. subst pe9 pe7 pe2 nd.
    assert (P2 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia).
    assert (HI4 : 0 <= idx <= 4095) by (clear - HI P2; lia).
    destruct (x42_lenword DT tl dtb mm idx DTB DL X2OK TL HI) as (lv & LV & LW).
    mid_run FR BD [0xa9d28] 8 700 lv j idx lenw bc sh pe.
    all: aside.
    all: traps.
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: try clear P2 HI4 LW.
    all: kx_gen_regsF [13%nat; 14%nat]; intros.
    all: evr; kx_mem; kx_sx3; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with TL : 1 <= tl <= 12 |- _ => eapply (x42_5m4_3 jb mb); try lside; mid_sides HK HSH TL K end.
  Qed.
End DX42B3C3.
End CANSEC1.
