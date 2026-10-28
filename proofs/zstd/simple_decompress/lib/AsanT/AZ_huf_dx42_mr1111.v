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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42 AZ_huf_dx42_mh.
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
Section DX42MR1111.
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

  (* [comment removed for export] *)
  Ltac sfactsF BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc :=
    lazymatch type of BSE with ?S + ?len <= SRC + n =>
      let sf := fresh "SF" in
      assert (sf : (4096 <= S <= 140737488355328) /\ (4096 <= S + len <= 140737488355328) /\ (1 <= len <= 4294967296) /\ S + len < 2^47 /\
                   (DST + dcap <= S \/ S + len <= DST) /\ (S + len <= lo \/ SPV <= S) /\
                   (SPV - 576 + 472 <= S \/ S + len <= SPV - 576))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      let a1 := fresh "SF" in let a2 := fresh "SF" in let a3 := fresh "SF" in let a4 := fresh "SF" in
      let a5 := fresh "SF" in let a6 := fresh "SF" in let a7 := fresh "SF" in
      destruct sf as (a1 & a2 & a3 & a4 & a5 & a6 & a7);
      let rs := fresh "RS" in
      assert (rs : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia));
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia))
      end
    end.
  (* [comment removed for export] *)
  Ltac lsideR := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- _ <= 64 -> SINVA _ _ _ => intros ?; unfold SINVA; kx_lia_m1
    | |- _ <= bv_unsigned (ev _ ?j) <= _ => first [ assumption | let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H; clear - H; lia ]
    | |- @eq Z _ _ => first [eassumption | reflexivity | kx_lia_m1]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; kx_lia_m1]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [assumption | kx_lia_m1 | idtac]
    | |- _ \/ _ => try kx_lia_m1
    | |- Z.le _ _ => first [assumption | kx_lia_m1]
    | |- Z.lt _ _ => first [assumption | kx_lia_m1]
    | |- _ => eassumption
    end.
  (* [comment removed for export] *)
  Ltac nrmB B X := lazymatch X with B + _ => idtac | B => replace B with (B + 0) by (clear; lia) | _ => replace X with (B + (X - B)) by (clear; lia) end.

  Lemma x42_nbword : forall mm idx, bytes_at bsegs mm DT dtb -> 0 <= idx < 2 ^ tl ->
    exists nv, 0 <= nv <= tl /\ rdn bsegs mm (wa (DT + 4 * idx + 6)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 nv)).
  Proof using NBOK.
    intros mm idx DTB HI. destruct (NBOK idx HI) as (b & NTH & BR).
    change (nth_error dtb (Z.to_nat (4 * idx + 6)) = Some b) in NTH. clear - DTB HI NTH BR.
    exists (bv_unsigned b). split; [pose proof (bv_unsigned_in_range 8 b); lia|].
    assert (L : (Z.to_nat (4 * idx + 6) + 1 <= length dtb)%nat).
    { assert (Z.to_nat (4 * idx + 6) < length dtb)%nat by (apply nth_error_Some; rewrite NTH; discriminate). lia. }
    pose proof (bytes_at_rdn bsegs mm DT dtb (Z.to_nat (4 * idx + 6)) 1 DTB L) as R.
    rewrite Z2Nat.id in R by lia. replace (DT + 4 * idx + 6) with (DT + (4 * idx + 6)) by lia. rewrite R.
    rewrite (firstn1_skipn _ _ _ NTH). unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. f_equal.
    symmetry. apply bv_eq. rewrite Z_to_bv_unsigned.
    pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in RB.
    rewrite Z_to_bv_unsigned. rewrite !bv_wrap_small; [reflexivity| |]; unfold bv_modulus.
    - change (2 ^ Z.of_N 64) with (2^64). lia.
    - change (2 ^ Z.of_N 8) with 256. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_mr1111 : forall mm q1 q2 q3 q4 o1 o2 o3 o4 e1 e2 e3 e4 g1 g2 g3 g4 idx4
      (d1 d2 d3 l1 l2 l3 k1 k2 k3 k4 bw4 : word) (pad4 j0 j1 j2 : list byte)
      (x5 x6 x8 x9 x16 x20 x24 x31 : word),
    munch WDM mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -576) ->
    FRA mm j0 (Z_to_bv 64 dcap) j1 ->
    FRS mm (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + pe3))
           (Z_to_bv 64 S1) (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap - 7))
           (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) l2 l1 (Z_to_bv 64 (S3 + o3)) k4 k1
           (Z_to_bv 64 (DT + 4)) ->
    BD4 mm k4 bw4 pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mm j2 ->
    bytes_at bsegs mm S1 bs1 -> bytes_at bsegs mm S2 bs2 -> bytes_at bsegs mm S3 bs3 -> bytes_at bsegs mm S4 bs4 ->
    0 <= o1 -> 0 <= g1 -> bv_unsigned d1 <= 12 -> (o1 = 0 \/ (o1 + 8 <= n1 /\ g1 + bv_unsigned d1 <= 56)) -> g1 + bv_unsigned d1 <= 112 ->
    0 <= o2 -> 0 <= g2 -> bv_unsigned d2 <= 12 -> (o2 = 0 \/ (o2 + 8 <= n2 /\ g2 + bv_unsigned d2 <= 56)) -> g2 + bv_unsigned d2 <= 112 ->
    0 <= o3 -> 0 <= g3 -> bv_unsigned d3 <= 12 -> (o3 = 0 \/ (o3 + 8 <= n3 /\ g3 + bv_unsigned d3 <= 56)) -> g3 + bv_unsigned d3 <= 112 ->
    0 <= o4 -> 0 <= g4 -> 0 <= idx4 < 2 ^ tl -> (o4 = 0 \/ (o4 + 8 <= n4 /\ g4 <= 44)) -> g4 <= 100 ->
    8 <= o1 -> 8 <= o2 -> 8 <= o3 -> 8 <= o4 ->
    1 <= bv_unsigned l1 <= 2 -> 1 <= bv_unsigned l2 <= 2 -> 1 <= bv_unsigned l3 <= 2 ->
    q1 + 3 <= e1 <= q1 + 6 -> q2 + 3 <= e2 <= q2 + 6 -> q3 + 3 <= e3 <= q3 + 6 -> q4 + 3 <= e4 <= q4 + 6 ->
    q1 + 8 <= dcap -> q2 + 8 <= dcap -> q3 + 8 <= dcap -> q4 + 8 <= dcap -> 0 <= q1 -> pe1 <= q2 -> pe2 <= q3 -> pe3 <= q4 -> 0 <= pe1 ->
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
        e1 + 1 <= q1' <= e1 + 2 -> e2 + 1 <= q2' <= e2 + 2 -> e3 + 1 <= q3' <= e3 + 2 -> e4 + 1 <= q4' <= e4 + 2 -> q4' + 8 <= dcap ->
        evtF bsegs RNG POST (HD mm' q1' q2' q3' q4' o1' b1' o2' b2' o3' b3' o4' b4' k2' k3'
                                y5 y6 y7 y8 y11 y14 y16 y17 y21 y23 y25 y31)) ->
    K0 ->
    evtF bsegs RNG POST (ST 0x9f004 mm (Z_to_bv 64 g2) x5 x6 d3 x8 x9 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DT + 4 * idx4 + 4))
                            (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (DST + e3)) (Z_to_bv 64 (DST + e4)) (Z_to_bv 64 (DST + e2)) x16
                            (Z_to_bv 64 g1) (Z_to_bv 64 g3) k3 x20 l3 (Z_to_bv 64 (S2 + o2)) d2 x24 d1 (Z_to_bv 64 (S1 + o1)) SB
                            (Z_to_bv 64 sh) k2 (Z_to_bv 64 g4) x31).
  Proof using CTX X2OK ACTX NBOK HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mm q1 q2 q3 q4 o1 o2 o3 o4 e1 e2 e3 e4 g1 g2 g3 g4 idx4 d1 d2 d3 l1 l2 l3 k1 k2 k3 k4 bw4 pad4 j0 j1 j2
      x5 x6 x8 x9 x16 x20 x24 x31
      MU WM MU0 WM0 MI OUT DTB STK FA FR B4 FJ SB1 SB2 SB3 SB4
      O1 G1 D1 HR1 CC1 O2 G2 D2 HR2 CC2 O3 G3 D3 HR3 CC3 O4 G4 IX HR4 CC4 CO1 CO2 CO3 CO4
      HL1 HL2 HL3 HW1 HW2 HW3 HW4 HQ1 HQ2 HQ3 HQ4 HP1 HE2 HE3 HE4 HE0 KH KX.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2.
    sfactsF SS1 SE1 LN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc. sfactsF SS2 SE2 LN2 R2 DJ1 OS2 LO RSRC RSRCS USRCc.
    sfactsF SS3 SE3 LN3 R2 DJ1 OS2 LO RSRC RSRCS USRCc. sfactsF SS4 SE4 LN4 R2 DJ1 OS2 LO RSRC RSRCS USRCc.
    ffacts OS1 OS3 LO. dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. kclean.
    assert (TL12 : 2 ^ tl <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; clear - TL; lia).
    destruct (x42_lenword DT tl dtb mm idx4 DTB DL X2OK TL IX) as (lv & HLV & RLV).
    destruct (x42_nbword mm idx4 DTB IX) as (nv & HNV & RNV).
    assert (DR1 : 0 <= bv_unsigned d1 <= 12) by (pose proof (bv_unsigned_in_range 64 d1); lia).
    assert (DR2 : 0 <= bv_unsigned d2 <= 12) by (pose proof (bv_unsigned_in_range 64 d2); lia).
    assert (DR3 : 0 <= bv_unsigned d3 <= 12) by (pose proof (bv_unsigned_in_range 64 d3); lia).
    assert (HF1 : o1 + 8 <= n1 /\ g1 + bv_unsigned d1 <= 56) by (destruct HR1 as [HR|HR]; [lia | exact HR]).
    assert (HF2 : o2 + 8 <= n2 /\ g2 + bv_unsigned d2 <= 56) by (destruct HR2 as [HR|HR]; [lia | exact HR]).
    assert (HF3 : o3 + 8 <= n3 /\ g3 + bv_unsigned d3 <= 56) by (destruct HR3 as [HR|HR]; [lia | exact HR]).
    assert (HF4 : o4 + 8 <= n4 /\ nv + g4 <= 56) by (destruct HR4 as [HR|HR]; [lia | destruct HR; split; lia]).
    destruct HF1 as (HN1 & HF1). destruct HF2 as (HN2 & HF2). destruct HF3 as (HN3 & HF3). destruct HF4 as (HN4 & HF4).
    clear HR1 HR2 HR3 HR4 CC1 CC2 CC3 CC4.
    assert (QR1 : exists cq cr, g1 + bv_unsigned d1 = 8 * cq + cr /\ 0 <= cq <= 7 /\ 0 <= cr <= 7)
      by (exists ((g1 + bv_unsigned d1) / 8), ((g1 + bv_unsigned d1) mod 8); clear - G1 DR1 HF1; Z.div_mod_to_equations; lia).
    assert (QR2 : exists cq cr, g2 + bv_unsigned d2 = 8 * cq + cr /\ 0 <= cq <= 7 /\ 0 <= cr <= 7)
      by (exists ((g2 + bv_unsigned d2) / 8), ((g2 + bv_unsigned d2) mod 8); clear - G2 DR2 HF2; Z.div_mod_to_equations; lia).
    assert (QR3 : exists cq cr, g3 + bv_unsigned d3 = 8 * cq + cr /\ 0 <= cq <= 7 /\ 0 <= cr <= 7)
      by (exists ((g3 + bv_unsigned d3) / 8), ((g3 + bv_unsigned d3) mod 8); clear - G3 DR3 HF3; Z.div_mod_to_equations; lia).
    assert (QR4 : exists cq cr, nv + g4 = 8 * cq + cr /\ 0 <= cq <= 7 /\ 0 <= cr <= 7)
      by (exists ((nv + g4) / 8), ((nv + g4) mod 8); clear - G4 HNV HF4; Z.div_mod_to_equations; lia).
    destruct QR1 as (cq1 & cr1 & EF1 & HCQ1 & HCR1). assert (EG1 : g1 = 8 * cq1 + cr1 - bv_unsigned d1) by lia. subst g1.
    destruct QR2 as (cq2 & cr2 & EF2 & HCQ2 & HCR2). assert (EG2 : g2 = 8 * cq2 + cr2 - bv_unsigned d2) by lia. subst g2.
    destruct QR3 as (cq3 & cr3 & EF3 & HCQ3 & HCR3). assert (EG3 : g3 = 8 * cq3 + cr3 - bv_unsigned d3) by lia. subst g3.
    destruct QR4 as (cq4 & cr4 & EF4 & HCQ4 & HCR4). assert (EG4 : g4 = 8 * cq4 + cr4 - nv) by lia. subst g4.
    clear EF1 EF2 EF3 EF4.
    assert (KFG5 : (0 <= dcap <= 4294967296) /\ (52 <= sh <= 63) /\ (4096 <= DST <= 140737488355328) /\ (2 <= dcap - e4 <= 4294967296) /\ (4089 <= DST + dcap - 7 <= 140737488355321)) by (clear - R1 HSH TL HW4 HQ4 HE4 HE0 PE2 PE3; lia).
    destruct KFG5 as (KF1 & KF2 & KF3 & KF4 & KF5).
    assert (KFG7 : (3 <= e1 <= 4294967296) /\ (4096 <= DST + e1 <= 140737488355326)) by (clear - HW1 HQ1 HP1 HE2 HE3 HE4 HE0 PE2 PE3 R1; lia).
    destruct KFG7 as (KF6 & KF7).
    assert (KFG9 : (3 <= e2 <= 4294967296) /\ (4096 <= DST + e2 <= 140737488355326)) by (clear - HW2 HQ2 HP1 HE2 HE3 HE4 HE0 PE2 PE3 R1; lia).
    destruct KFG9 as (KF8 & KF9).
    assert (KFG11 : (3 <= e3 <= 4294967296) /\ (4096 <= DST + e3 <= 140737488355326)) by (clear - HW3 HQ3 HP1 HE2 HE3 HE4 HE0 PE2 PE3 R1; lia).
    destruct KFG11 as (KF10 & KF11).
    assert (KFG13 : (3 <= e4 <= 4294967296) /\ (4096 <= DST + e4 <= 140737488355326)) by (clear - HW4 HQ4 HP1 HE2 HE3 HE4 HE0 PE2 PE3 R1; lia).
    destruct KFG13 as (KF12 & KF13).
    assert (KFG21 : (8 <= o1 <= 4294967296) /\ (8 <= n1 - o1 <= 4294967296) /\ (0 <= cq1 <= 7) /\ (0 <= cr1 <= 7) /\ (0 <= 8 * cq1 + cr1 <= 56) /\ (1 <= o1 - cq1 <= 4294967296) /\ (4096 <= S1 + o1 - cq1 <= 140737488355319) /\ (4104 <= S1 + o1 <= 140737488355327)) by (clear - O1 HN1 HF1 HCQ1 HCR1 CO1 SS1 SE1 LN1 R2; lia).
    destruct KFG21 as (KF14 & KF15 & KF16 & KF17 & KF18 & KF19 & KF20 & KF21).
    assert (KFG29 : (8 <= o2 <= 4294967296) /\ (8 <= n2 - o2 <= 4294967296) /\ (0 <= cq2 <= 7) /\ (0 <= cr2 <= 7) /\ (0 <= 8 * cq2 + cr2 <= 56) /\ (1 <= o2 - cq2 <= 4294967296) /\ (4096 <= S2 + o2 - cq2 <= 140737488355319) /\ (4104 <= S2 + o2 <= 140737488355327)) by (clear - O2 HN2 HF2 HCQ2 HCR2 CO2 SS2 SE2 LN2 R2; lia).
    destruct KFG29 as (KF22 & KF23 & KF24 & KF25 & KF26 & KF27 & KF28 & KF29).
    assert (KFG37 : (8 <= o3 <= 4294967296) /\ (8 <= n3 - o3 <= 4294967296) /\ (0 <= cq3 <= 7) /\ (0 <= cr3 <= 7) /\ (0 <= 8 * cq3 + cr3 <= 56) /\ (1 <= o3 - cq3 <= 4294967296) /\ (4096 <= S3 + o3 - cq3 <= 140737488355319) /\ (4104 <= S3 + o3 <= 140737488355327)) by (clear - O3 HN3 HF3 HCQ3 HCR3 CO3 SS3 SE3 LN3 R2; lia).
    destruct KFG37 as (KF30 & KF31 & KF32 & KF33 & KF34 & KF35 & KF36 & KF37).
    assert (KFG45 : (8 <= o4 <= 4294967296) /\ (8 <= n4 - o4 <= 4294967296) /\ (0 <= cq4 <= 7) /\ (0 <= cr4 <= 7) /\ (0 <= 8 * cq4 + cr4 <= 56) /\ (1 <= o4 - cq4 <= 4294967296) /\ (4096 <= S4 + o4 - cq4 <= 140737488355319) /\ (4104 <= S4 + o4 <= 140737488355327)) by (clear - O4 HN4 HF4 HCQ4 HCR4 CO4 SS4 SE4 LN4 R2; lia).
    destruct KFG45 as (KF38 & KF39 & KF40 & KF41 & KF42 & KF43 & KF44 & KF45).
    assert (KFG49 : (0 <= 8 * cq1 + cr1 - bv_unsigned d1 <= 56) /\ (0 <= 8 * cq2 + cr2 - bv_unsigned d2 <= 56) /\ (0 <= 8 * cq3 + cr3 - bv_unsigned d3 <= 56) /\ (0 <= 8 * cq4 + cr4 - nv <= 56)) by (clear - G1 G2 G3 G4 HF1 HF2 HF3 HF4 DR1 DR2 DR3 HNV TL HCQ1 HCR1 HCQ2 HCR2 HCQ3 HCR3 HCQ4 HCR4; lia).
    destruct KFG49 as (KF46 & KF47 & KF48 & KF49). clear HF1 HF2 HF3 HF4.
    assert (KFG53 : (0 <= idx4 <= 4095) /\ (4100 <= DT + 4 * idx4 + 4 <= 140737488355328) /\ (0 <= nv <= 12)) by (clear - IX TL12 R3 HNV TL; lia).
    destruct KFG53 as (KF50 & KF51 & KF52).
    kx_autoFLA (FA, FR, B4, FJ) [KAUnp DT 16388; KAUnp S1 n1; KAUnp S2 n2; KAUnp S3 n3; KAUnp S4 n4; KAApp (SPV - 576) 472] [0x9f7d8; 0x9e754] 300%nat
      [KZRange sh 52 63; 
           KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944;
           KZRange SPV 17594333495296 140737488355328; 
           KZRange S1 4096 140737488355328; KZRange (S1 + n1) 4096 140737488355328; KZRange n1 1 4294967296;
           KZRange S2 4096 140737488355328; KZRange (S2 + n2) 4096 140737488355328; KZRange n2 1 4294967296;
           KZRange S3 4096 140737488355328; KZRange (S3 + n3) 4096 140737488355328; KZRange n3 1 4294967296;
           KZRange S4 4096 140737488355328; KZRange (S4 + n4) 4096 140737488355328; KZRange n4 1 4294967296;
           KZWr (SPV + -408) 152; KZWr (SPV + -256) 40;
           KZDisj (SPV - 576) 472 DT 16388;
           KZDisj (SPV - 576) 472 S1 n1; KZDisj (SPV - 576) 472 S2 n2; KZDisj (SPV - 576) 472 S3 n3; KZDisj (SPV - 576) 472 S4 n4;
       KZRange o1 8 4294967296; KZRange (n1 - o1) 8 4294967296; KZRange cq1 0 7; KZRange cr1 0 7; KZRange (8 * cq1 + cr1) 0 56; KZRange (o1 - cq1) 1 4294967296; KZRange (S1 + o1 - cq1) 4096 140737488355319; KZRange (S1 + o1) 4104 140737488355327;
       KZRange o2 8 4294967296; KZRange (n2 - o2) 8 4294967296; KZRange cq2 0 7; KZRange cr2 0 7; KZRange (8 * cq2 + cr2) 0 56; KZRange (o2 - cq2) 1 4294967296; KZRange (S2 + o2 - cq2) 4096 140737488355319; KZRange (S2 + o2) 4104 140737488355327;
       KZRange o3 8 4294967296; KZRange (n3 - o3) 8 4294967296; KZRange cq3 0 7; KZRange cr3 0 7; KZRange (8 * cq3 + cr3) 0 56; KZRange (o3 - cq3) 1 4294967296; KZRange (S3 + o3 - cq3) 4096 140737488355319; KZRange (S3 + o3) 4104 140737488355327;
       KZRange o4 8 4294967296; KZRange (n4 - o4) 8 4294967296; KZRange cq4 0 7; KZRange cr4 0 7; KZRange (8 * cq4 + cr4) 0 56; KZRange (o4 - cq4) 1 4294967296; KZRange (S4 + o4 - cq4) 4096 140737488355319; KZRange (S4 + o4) 4104 140737488355327;
       KZRange e1 3 4294967296; KZRange (DST + e1) 4096 140737488355326;
       KZRange e2 3 4294967296; KZRange (DST + e2) 4096 140737488355326;
       KZRange e3 3 4294967296; KZRange (DST + e3) 4096 140737488355326;
       KZRange e4 3 4294967296; KZRange (DST + e4) 4096 140737488355326;
       KZRange (dcap - e4) 2 4294967296; KZRange (DST + dcap - 7) 4089 140737488355321;
       KZRange (bv_unsigned l1) 1 2;
       KZRange (bv_unsigned l2) 1 2;
       KZRange (bv_unsigned l3) 1 2;
       KZRange (bv_unsigned d1) 0 12; KZRange (bv_unsigned d2) 0 12; KZRange (bv_unsigned d3) 0 12;
       KZRange (8 * cq1 + cr1 - bv_unsigned d1) 0 56; KZRange (8 * cq2 + cr2 - bv_unsigned d2) 0 56; KZRange (8 * cq3 + cr3 - bv_unsigned d3) 0 56;
       KZRange idx4 0 4095; KZRange (DT + 4 * idx4 + 4) 4100 140737488355328; KZRange nv 0 12; KZRange lv 1 2; KZRange (8 * cq4 + cr4 - nv) 0 56;
       KZWord (DT + 4 * idx4 + 6) 1 nv; KZWord (DT + 4 * idx4 + 7) 1 lv]
      [(DT, 16388); (SPV + -576, 168); (SPV + -408, 152); (SPV + -256, 40); (SPV + -216, 112); (S1, n1); (S2, n2); (S3, n3); (S4, n4)] [(DT, 16388); (SPV - 576, 576); (S1, n1); (S2, n2); (S3, n3); (S4, n4)].
    all: aside.
    all: try clear KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12 KF13 KF14 KF15 KF16 KF17 KF18 KF19 KF20 KF21 KF22 KF23 KF24 KF25 KF26 KF27 KF28 KF29 KF30 KF31 KF32 KF33 KF34 KF35 KF36 KF37 KF38 KF39 KF40 KF41 KF42 KF43 KF44 KF45 KF46 KF47 KF48 KF49 KF50 KF51 KF52.
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: aclean.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9e754) _ _ _ _) => kx_gen_regsF [5%nat; 6%nat; 7%nat; 8%nat; 11%nat; 14%nat; 16%nat; 17%nat; 21%nat; 23%nat; 25%nat; 31%nat]
         | |- _ => kx_gen_regsF [5%nat; 6%nat; 7%nat; 8%nat; 11%nat; 20%nat; 21%nat; 23%nat; 25%nat; 30%nat; 31%nat]
         end.
    all: intros; evr; kx_mem.
    all: kx_sx3; kx_land_ranges; kx_strip_mod; land7_lin.
    (* [comment removed for export] *)
    all: repeat match goal with
         | B : rw_cells _ _ _ [_; _; _; C8 (Z_to_bv 64 ?X); C8 (Z_to_bv 64 ?S); _] |- _ =>
             lazymatch X with S + _ => fail | _ => replace X with (S + (X - S)) in B by (clear; lia) end
         | B : rw_cells _ _ _ [_; _; _; _; _; _; _; C8 (Z_to_bv 64 ?S); _; _; _; _; _; _; _; C8 (Z_to_bv 64 ?X); _; _; _] |- _ =>
             lazymatch X with S + _ => fail | _ => replace X with (S + (X - S)) in B by (clear; lia) end
         end.
    all: lclean2.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9e754) _ _ _ _) =>
             (* [comment removed for export] *)
             lazymatch goal with
             | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?T4) _ (Z_to_bv 64 ?P4) (Z_to_bv 64 ?T3) _ (Z_to_bv 64 ?T2) _ _ _ _ _ _ (Z_to_bv 64 ?P2) _ (Z_to_bv 64 ?T1) _ (Z_to_bv 64 ?P1) _ _ _ _ _) _ _ _ _ _ _) =>
                 nrmB S1 P1; nrmB S2 P2; nrmB S4 P4; nrmB DST T1; nrmB DST T2; nrmB DST T3; nrmB DST T4
             end;
             eapply KH; lsideR
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9f7d8) _ _ _ _) => eapply KX; lsideR
         end.
  Qed.
End DX42MR1111.
End CANSEC1.
