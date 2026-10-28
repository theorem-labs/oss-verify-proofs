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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42 AZ_huf_dx42_mh AZ_huf_dx42_md1 AZ_huf_dx42_md2 AZ_huf_dx42_md3 AZ_huf_dx42_md4 AZ_huf_dx42_mr0000 AZ_huf_dx42_mr0001 AZ_huf_dx42_mr0010 AZ_huf_dx42_mr0011 AZ_huf_dx42_mr0100 AZ_huf_dx42_mr0101 AZ_huf_dx42_mr0110 AZ_huf_dx42_mr0111 AZ_huf_dx42_mr1000 AZ_huf_dx42_mr1001 AZ_huf_dx42_mr1010 AZ_huf_dx42_mr1011 AZ_huf_dx42_mr1100 AZ_huf_dx42_mr1101 AZ_huf_dx42_mr1110 AZ_huf_dx42_mr1111.
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
Section DX42MI.
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
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  (* [comment removed for export] *)
  Variables (dl pe1 pe2 pe3 sh nd : Z) (S1 n1 S2 n2 S3 n3 S4 n4 : Z) (bs1 bs2 bs3 bs4 : list byte) (mb : amem).
  Hypothesis HDL : dl = tl + 256 * rsv.
  Hypothesis PE1 : pe1 = (dcap + 3) / 4.
  Hypothesis PE2 : pe2 = 2 * pe1.
  Hypothesis PE3 : pe3 = 3 * pe1.
  Hypothesis PE4 : pe3 <= dcap.
  Hypothesis HSH : sh = 64 - tl.
  Hypothesis HND : nd = -1 * DT + -5.
  Hypothesis BL1 : zlen bs1 = n1.  Hypothesis SS1 : SRC <= S1.  Hypothesis SE1 : S1 + n1 <= SRC + n.  Hypothesis LN1 : 1 <= n1.
  Hypothesis BL2 : zlen bs2 = n2.  Hypothesis SS2 : SRC <= S2.  Hypothesis SE2 : S2 + n2 <= SRC + n.  Hypothesis LN2 : 1 <= n2.
  Hypothesis BL3 : zlen bs3 = n3.  Hypothesis SS3 : SRC <= S3.  Hypothesis SE3 : S3 + n3 <= SRC + n.  Hypothesis LN3 : 1 <= n3.
  Hypothesis BL4 : zlen bs4 = n4.  Hypothesis SS4 : SRC <= S4.  Hypothesis SE4 : S4 + n4 <= SRC + n.  Hypothesis LN4 : 1 <= n4.
  (* [comment removed for export] *)
  Notation WDM := [(DST, DST + dcap); (SPV - 576, SPV - 104)].
  (* [comment removed for export] *)
  Notation K0 :=
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
        DST <= P1 -> P1 <= DST + dcap -> P2 <= DST + dcap -> P3 <= DST + dcap ->   (* [comment removed for export] *)
        DST + pe1 <= P2 -> DST + pe2 <= P3 -> DST + pe3 <= P4 -> P4 <= DST + dcap ->
        evtF bsegs RNG POST (ST 0x9f7d8 mm' (Z_to_bv 64 f2) y5 y6 y7 y8 (Z_to_bv 64 f1) (Z_to_bv 64 P4) y11 (Z_to_bv 64 S1)
                                (Z_to_bv 64 P3) (Z_to_bv 64 S2) (Z_to_bv 64 P2) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1))
                                (Z_to_bv 64 f3) c3 y20 y21 (Z_to_bv 64 Q2) y23 (Z_to_bv 64 P1) y25 (Z_to_bv 64 Q1) SB
                                (Z_to_bv 64 (DST + pe3)) c2 y30 y31)).
  Notation HD mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 k2 k3 x5 x6 x7 x8 x11 x14 x16 x17 x21 x23 x25 x31 :=
    (ST 0x9e754 mm (Z_to_bv 64 b2) x5 x6 x7 x8 (Z_to_bv 64 b1) (Z_to_bv 64 (DST + q4)) x11 (Z_to_bv 64 (S4 + o4))
        (Z_to_bv 64 (DST + q3)) x14 (Z_to_bv 64 (DST + q2)) x16 x17 (Z_to_bv 64 b3) k3 (Z_to_bv 64 (DT + 4)) x21
        (Z_to_bv 64 (S2 + o2)) x23 (Z_to_bv 64 (DST + q1)) x25 (Z_to_bv 64 (S1 + o1)) SB (Z_to_bv 64 sh) k2
        (Z_to_bv 64 b4) x31).

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

  (* [comment removed for export] *)
  Ltac kx_lia_or1 :=
    match goal with
    | H : _ \/ _ |- _ =>
        solve [ repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end;
                repeat match goal with H' : _ -> _ |- _ => clear H' end; lia ]
    end.
  Ltac kx_lia_m1 := first [ solve [kx_clear_or; lia] | solve [kx_lia_or1] | kx_bv_ranges; solve [kx_clear_or; lia] | solve [kx_bv_ranges; kx_lia_or1] ].
  (* [comment removed for export] *)
  Ltac mdh_hyp := lazymatch goal with |- ?G => match goal with H : G |- _ => exact H | H : mdh G |- _ => exact H end end.
  Ltac kx_lia_m2 :=
    lazymatch goal with
    | |- _ /\ _ => first [ mdh_hyp | solve [kx_clear_or; lia] | split; kx_lia_m2 ]
    | |- _ \/ _ => first [ mdh_hyp | kx_lia_m1 ]
    | |- _ <= _ <= _ => first [ mdh_hyp | kx_lia_m1 ]
    | |- _ => kx_lia_m1
    end.
  #[local] Ltac kx_lia ::= kx_lia_m2.
  #[local] Ltac kxl_lia ::= first [ mdh_hyp | kx_lia_m2 ].
  #[local] Ltac kxl_hyp ::= mdh_hyp.
  #[local] Ltac kxa_hyp ::= mdh_hyp.
  (* [comment removed for export] *)
  Ltac evw := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end);
    repeat match goal with
    | KXK : know_ok _ ?E _ _ |- context [ev ?E ?j] =>
        lazymatch goal with
        | _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail
        | _ => let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H
        end
    end.
  (* [comment removed for export] *)
  Ltac kside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- _ <= bv_unsigned (ev _ ?j) <= _ =>
        first [ assumption
              | let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H; clear - H; lia ]
    | |- _ <= _ <= _ => first [assumption | kx_lia_m1]
    | |- @eq Z _ _ => first [reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- _ => first [eassumption | kx_lia_m1]
    end.
  (* [comment removed for export] *)
  #[local] Ltac kxl_wr_exact ::=
    lazymatch goal with
    | |- wr_at ?segs ?m ?A ?N =>
        match goal with
        | H : wr_at segs m A N |- _ => exact H
        | H : rw_cells segs m A ?cs |- _ => let n := eval lazy in (Z.of_nat (cells_size cs)) in lazymatch n with N => exact (proj2 H) end
        end
    end.
  (* [comment removed for export] *)
  Ltac lclean2 :=
    repeat match goal with
           | H : ?A \/ _ |- _ => lazymatch A with _ = 0 => fail | _ => clear H end
           | H : mdh _ |- _ => clear H
           | H : rng _ _ _ |- _ => clear H
           | H : rng_aimg _ |- _ => clear H
           | H : 4096 <= _ <= _ |- _ => clear H
           | H : 17594333495296 <= _ <= _ |- _ => clear H
           | H : 17594333497904 <= _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
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
           end.
  Notation x42_md1 := (AZ_huf_dx42_md1.x42_md1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_md2 := (AZ_huf_dx42_md2.x42_md2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_md3 := (AZ_huf_dx42_md3.x42_md3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_md4 := (AZ_huf_dx42_md4.x42_md4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0000 := (AZ_huf_dx42_mr0000.x42_mr0000 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0001 := (AZ_huf_dx42_mr0001.x42_mr0001 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0010 := (AZ_huf_dx42_mr0010.x42_mr0010 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0011 := (AZ_huf_dx42_mr0011.x42_mr0011 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0100 := (AZ_huf_dx42_mr0100.x42_mr0100 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0101 := (AZ_huf_dx42_mr0101.x42_mr0101 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0110 := (AZ_huf_dx42_mr0110.x42_mr0110 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr0111 := (AZ_huf_dx42_mr0111.x42_mr0111 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1000 := (AZ_huf_dx42_mr1000.x42_mr1000 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1001 := (AZ_huf_dx42_mr1001.x42_mr1001 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1010 := (AZ_huf_dx42_mr1010.x42_mr1010 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1011 := (AZ_huf_dx42_mr1011.x42_mr1011 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1100 := (AZ_huf_dx42_mr1100.x42_mr1100 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1101 := (AZ_huf_dx42_mr1101.x42_mr1101 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1110 := (AZ_huf_dx42_mr1110.x42_mr1110 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).
  Notation x42_mr1111 := (AZ_huf_dx42_mr1111.x42_mr1111 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).

  (* [comment removed for export] *)
  Lemma x42_it : forall mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 (k1 k2 k3 k4 bw4 : word) (pad4 j0 j1 j2 : list byte)
      (w13 w14 : word) (x5 x6 x7 x8 x11 x14 x16 x17 x21 x23 x25 x31 : word),
    munch WDM mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRA mm j0 (Z_to_bv 64 dcap) j1 ->
    FRS mm (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + pe3))
        (Z_to_bv 64 S1) (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap - 7))
        (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) w13 w14 (Z_to_bv 64 (S3 + o3)) k4 k1
        (Z_to_bv 64 (DT + 4)) ->
    BD4 mm k4 bw4 pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mm j2 ->
    bytes_at bsegs mm S1 bs1 -> bytes_at bsegs mm S2 bs2 -> bytes_at bsegs mm S3 bs3 -> bytes_at bsegs mm S4 bs4 ->
    HINV o1 n1 b1 -> HINV o2 n2 b2 -> HINV o3 n3 b3 -> HINV o4 n4 b4 ->
    q1 + 8 <= dcap -> q2 + 8 <= dcap -> q3 + 8 <= dcap -> q4 + 8 <= dcap -> 0 <= q1 -> 0 <= q2 -> 0 <= q3 -> 0 <= q4 ->
    pe1 <= q2 -> pe2 <= q3 -> pe3 <= q4 -> 0 <= pe1 ->
    (forall mm' (q1' q2' q3' q4' o1' o2' o3' o4' b1' b2' b3' b4' : Z) (k1' k2' k3' k4' bw4' : word) (w13' w14' : word)
            (y5 y6 y7 y8 y11 y14 y16 y17 y21 y23 y25 y31 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -576) ->
        FRA mm' j0 (Z_to_bv 64 dcap) j1 ->
        FRS mm' (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + pe3))
               (Z_to_bv 64 S1) (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap - 7))
               (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) w13' w14' (Z_to_bv 64 (S3 + o3')) k4' k1'
               (Z_to_bv 64 (DT + 4)) ->
        BD4 mm' k4' bw4' pad4 (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mm' j2 ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        1 <= o1' -> o1' + 8 <= n1 -> 0 <= b1' <= 7 -> 1 <= o2' -> o2' + 8 <= n2 -> 0 <= b2' <= 7 ->
        1 <= o3' -> o3' + 8 <= n3 -> 0 <= b3' <= 7 -> 1 <= o4' -> o4' + 8 <= n4 -> 0 <= b4' <= 7 ->
        q1 + 4 <= q1' <= q1 + 8 -> q2 + 4 <= q2' <= q2 + 8 -> q3 + 4 <= q3' <= q3 + 8 -> q4 + 4 <= q4' <= q4 + 8 -> q4' + 8 <= dcap ->
        evtF bsegs RNG POST (HD mm' q1' q2' q3' q4' o1' b1' o2' b2' o3' b3' o4' b4' k2' k3'
                                y5 y6 y7 y8 y11 y14 y16 y17 y21 y23 y25 y31)) ->
    K0 ->
    evtF bsegs RNG POST (HD mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 k2 k3 x5 x6 x7 x8 x11 x14 x16 x17 x21 x23 x25 x31).
  Proof using CTX X2OK ACTX NBOK HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4.
    intros mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 k1 k2 k3 k4 bw4 pad4 j0 j1 j2 w13 w14
      x5 x6 x7 x8 x11 x14 x16 x17 x21 x23 x25 x31
      MU WM MU0 WM0 MI OUT DTB STK FA FR BD FJ B1 B2 B3 B4 HI1 HI2 HI3 HI4 HQ1 HQ2 HQ3 HQ4 HP1 HP2 HP3 HP4
      HE2 HE3 HE4 HE0 KH KX.
    (* [comment removed for export] *)
    eapply (x42_md1 mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 k1 k2 k3 k4 bw4 pad4 j0 j1 j2 w13 w14
              x5 x6 x7 x8 x11 x14 x16 x17 x21 x23 x25 x31); [ eassumption .. | idtac ].
    intros mm2 nb1_2 nb2_2 nb3_2 ln1_2 ln2_2 ln3_2 i4_2 y5_2 y7_2 y8_2 y14_2 y25_2. intros.
    (* [comment removed for export] *)
    eapply (x42_md2 mm2 q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 _ _ _ _ _ _ _ _ _ _ _ nb1_2 nb2_2 nb3_2 ln1_2 ln2_2 ln3_2 i4_2
              y5_2 y7_2 y8_2 y14_2 y25_2); [ eassumption .. | idtac ].
    intros mm3 p1_3 p2_3 p3_3 p4_3 e1_3 e2_3 e3_3 e4_3 nb1_3 nb2_3 nb3_3 ln1_3 ln2_3 ln3_3 i4_3 y7_3 y14_3 y23_3 y24_3 y25_3. intros.
    (* [comment removed for export] *)
    eapply (x42_md3 mm3 q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 p1_3 p2_3 p3_3 p4_3 e1_3 e2_3 e3_3 e4_3 _ _ _ _ _ _ _ _ _ _ _ nb1_3 nb2_3 nb3_3 ln1_3 ln2_3 ln3_3 i4_3
              y7_3 y14_3 y23_3 y24_3 y25_3); [ eassumption .. | idtac ].
    intros mm4 p1_4 p2_4 p3_4 p4_4 e1_4 e2_4 e3_4 e4_4 nb1_4 nb2_4 nb3_4 ln1_4 ln2_4 ln3_4 i4_4 y7_4 y10_4 y17_4 y24_4 y25_4. intros.
    (* [comment removed for export] *)
    eapply (x42_md4 mm4 q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 p1_4 p2_4 p3_4 p4_4 e1_4 e2_4 e3_4 e4_4 _ _ _ _ _ _ _ _ _ _ _ nb1_4 nb2_4 nb3_4 ln1_4 ln2_4 ln3_4 i4_4
              y7_4 y10_4 y17_4 y24_4 y25_4); [ eassumption .. | idtac ].
    intros mm5 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5 i4_5 y5_5 y6_5 y8_5 y9_5 y16_5 y20_5 y24_5 y31_5. intros.
    (* [comment removed for export] *)
    destruct (Z_lt_le_dec o1 8) as [C1|C1];
      [ destruct (Z_lt_le_dec o2 8) as [C2|C2];
        [ destruct (Z_lt_le_dec o3 8) as [C3|C3];
          [ destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr0000 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5)
            | eapply (x42_mr0001 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5) ]
          | destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr0010 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5)
            | eapply (x42_mr0011 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5) ] ]
        | destruct (Z_lt_le_dec o3 8) as [C3|C3];
          [ destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr0100 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5)
            | eapply (x42_mr0101 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5) ]
          | destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr0110 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5)
            | eapply (x42_mr0111 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5) ] ] ]
      | destruct (Z_lt_le_dec o2 8) as [C2|C2];
        [ destruct (Z_lt_le_dec o3 8) as [C3|C3];
          [ destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr1000 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5)
            | eapply (x42_mr1001 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5) ]
          | destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr1010 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5)
            | eapply (x42_mr1011 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5) ] ]
        | destruct (Z_lt_le_dec o3 8) as [C3|C3];
          [ destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr1100 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5)
            | eapply (x42_mr1101 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5) ]
          | destruct (Z_lt_le_dec o4 8) as [C4|C4];
            [ eapply (x42_mr1110 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5)
            | eapply (x42_mr1111 mm5 q1 q2 q3 q4 o1 o2 o3 o4 p1_5 p2_5 p3_5 p4_5 e1_5 e2_5 e3_5 e4_5 i4_5 nb1_5 nb2_5 nb3_5 ln1_5 ln2_5 ln3_5) ] ] ] ].
    (* [comment removed for export] *)
    all: first [ exact KX | eassumption
               | (intros; eapply KH; first [ eassumption | lia ])
               | (unfold HINV in HI1, HI2, HI3, HI4; lia) ].
    (* [comment removed for export] *)
  Qed.
End DX42MI.
End CANSEC1.
