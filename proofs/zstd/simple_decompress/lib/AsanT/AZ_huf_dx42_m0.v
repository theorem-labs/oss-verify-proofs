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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42 AZ_huf_dx42_mh AZ_huf_dx42_m1.
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
Section DX42M0.
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
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 654748) _ _ _ _) => kx_trap_fast end).
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
  Notation x42_m1 := (AZ_huf_dx42_m1.x42_m1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX NBOK dl pe1 pe2 pe3 sh nd S1 n1 S2 n2 S3 n3 S4 n4 bs1 bs2 bs3 bs4 mb HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4).

  (* [comment removed for export] *)
  Ltac lsideM := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- HINV _ _ _ => assumption
    | |- _ <= 64 -> SINVA _ _ _ => intros ?; unfold SINVA; unfold HINV in *; kx_lia_m1
    | |- @eq Z _ _ => first [eassumption | reflexivity | kx_lia_m1]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; kx_lia_m1 | apply Z_to_bv_eqm; reflexivity]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [assumption | kx_lia_m1 | unfold HINV in *; kx_lia_m1 | idtac]
    | |- _ \/ _ => try kx_lia_m1
    | |- Z.le _ _ => first [assumption | kx_lia_m1 | unfold HINV in *; kx_lia_m1]
    | |- Z.lt _ _ => first [assumption | kx_lia_m1 | unfold HINV in *; kx_lia_m1]
    | |- _ => eassumption
    end.

  (* [comment removed for export] *)
  Lemma x42_m0 : forall o1 b1 o2 b2 o3 b3 o4 b4 (k1 k2 k3 k4 : word) (pad4 j0 j1 j2 : list byte)
      (w0 w8 w9 w10 w11 w12 w13 w14 w16 w18 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x29 x30 x31 : word),
    S1 = SRC + 6 ->
    munch W0 m0 mb -> wmono bsegs m0 mb -> mem_inv bsegs mb -> stk bsegs mb DST (DST + dcap) ->
    bytes_at bsegs mb DT dtb -> stk bsegs mb lo (SPV + -576) ->
    FRA mb j0 (Z_to_bv 64 dcap) j1 ->
    FRS mb w0 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 S1)
        (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (S3 + o3)) w16 k1 w18 ->
    BD4 mb k4 (Z_to_bv 64 b4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mb j2 ->
    bytes_at bsegs mb S1 bs1 -> bytes_at bsegs mb S2 bs2 -> bytes_at bsegs mb S3 bs3 -> bytes_at bsegs mb S4 bs4 ->
    HINV o1 n1 b1 -> HINV o2 n2 b2 -> HINV o3 n3 b3 -> HINV o4 n4 b4 ->
    K0 ->
    evtF bsegs RNG POST (ST 0x9e6cc mb x1 x5 x6 x7 (Z_to_bv 64 dl) (Z_to_bv 64 b1) x10 x11 x12 x13 x14 x15
                            (Z_to_bv 64 (DST + dcap)) x17 (Z_to_bv 64 b3) k3 (Z_to_bv 64 SRC) (Z_to_bv 64 b2)
                            (Z_to_bv 64 (S2 + o2)) k2 (Z_to_bv 64 DST) (Z_to_bv 64 DT) (Z_to_bv 64 (S1 + o1)) SB
                            (Z_to_bv 64 (DST + pe3)) x29 x30 x31).
  Proof using CTX X2OK ACTX NBOK HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros o1 b1 o2 b2 o3 b3 o4 b4 k1 k2 k3 k4 pad4 j0 j1 j2
      w0 w8 w9 w10 w11 w12 w13 w14 w16 w18
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x29 x30 x31
      HS1 MU0 WM0 MI OUT DTB STK FA FR B4 FJ SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 KX.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS3 LO. kclean.
    pose proof HI1 as HI1'. pose proof HI2 as HI2'. pose proof HI3 as HI3'. pose proof HI4 as HI4'. unfold HINV in HI1', HI2', HI3', HI4'.
    assert (HE : 0 <= pe1 /\ 4 * pe1 <= dcap + 3 /\ dcap < 4 * pe1 + 1) by (rewrite PE1; clear - R1; Z.div_mod_to_equations; lia).
    assert (KFG : (0 <= pe1 <= 4294967296) /\ (0 <= pe2 <= 4294967296) /\ (0 <= pe3 <= 4294967296) /\ (0 <= dcap - pe3 <= 4294967296) /\
                  (4096 <= DST + pe3 <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (1 <= dl <= 65535) /\
                  (0 <= b1 <= 64) /\ (0 <= b2 <= 64) /\ (0 <= b3 <= 64) /\ (0 <= b4 <= 64) /\
                  (4096 <= S1 + o1 <= 140737488355328) /\ (4096 <= S2 + o2 <= 140737488355328) /\ (4096 <= S3 + o3 <= 140737488355328) /\ (4096 <= S4 + o4 <= 140737488355328))
      by (clear - HE PE2 PE3 PE4 R1 R2 HDL TL RSV HI1' HI2' HI3' HI4' SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4; lia).
    destruct KFG as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 & KF13 & KF14 & KF15).
    pose proof (munch_refl WDM mb) as MU. pose proof (wmono_refl bsegs mb) as WM.
    kx_autoFLA (FA, FR, B4, FJ) [KAUnp DT 16388; KAApp (SPV - 576) 472] [0x9e754; 0x9f7d8] 200%nat
      [KZRange pe1 0 4294967296; KZRange pe2 0 4294967296; KZRange pe3 0 4294967296; KZRange (dcap - pe3) 0 4294967296; KZRange (DST + pe3) 4096 140737488355328;
       KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944;
       KZRange SPV 17594333495296 140737488355328; KZRange dl 1 65535; KZRange tl 1 12; KZRange rsv 0 255;
       KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
       KZRange (S1 + o1) 4096 140737488355328; KZRange (S2 + o2) 4096 140737488355328; KZRange (S3 + o3) 4096 140737488355328; KZRange (S4 + o4) 4096 140737488355328;
      KZWr (SPV + -408) 152; KZWr (SPV + -256) 40; KZDisj (SPV - 576) 472 DT 16388]
      [(DT, 16388); (SPV + -576, 168); (SPV + -408, 152); (SPV + -256, 40); (SPV + -216, 112)] [(DT, 16388); (SPV - 576, 576)].
    all: aside.
    all: traps.
    all: try clear KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12 KF13 KF14 KF15.
    all: try clear HI1' HI2' HI3' HI4'.
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: aclean.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9e754) _ _ _ _) => kx_gen_regsF [5%nat; 6%nat; 7%nat; 8%nat; 11%nat; 14%nat; 16%nat; 17%nat; 21%nat; 23%nat; 25%nat; 31%nat]
         | |- _ => kx_gen_regsF [5%nat; 6%nat; 7%nat; 8%nat; 11%nat; 20%nat; 21%nat; 23%nat; 25%nat; 30%nat; 31%nat]
         end.
    all: intros; evr.
    all: kx_mem.
    all: kx_sx3; kx_land_ranges; kx_strip_mod.
    all: lclean2.
    all: try replace (DST + dcap + -7) with (DST + dcap - 7) in * by (clear; lia).
    all: try replace (SRC + 14) with (S1 + 8) in * by (clear - HS1; lia).
    all: try replace (SRC + 6) with S1 by (clear - HS1; lia).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9e754) _ _ ?m1 _) =>
             (* [comment removed for export] *)
             try replace (Z.land ((-1 * dl) mod 2 ^ 64) 63) with sh
               by (rewrite HSH, HDL; change 63 with (Z.ones 6); rewrite Z.land_ones by (pose proof (Z.mod_pos_bound (-1 * (tl + 256 * rsv)) (2 ^ 64) ltac:(clear; lia)); lia);
                   change (2 ^ 6) with 64; clear - TL RSV; Z.div_mod_to_equations; lia);
             try replace (Z_to_bv 64 (-1 * DT + -5)) with (Z_to_bv 64 nd) by (rewrite HND; reflexivity);
             try replace (Z_to_bv 64 (18446744073709551611 - DT)) with (Z_to_bv 64 nd) by (rewrite HND; apply Z_to_bv_eqm; reflexivity);
             try lazymatch goal with
             | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?T) _ _ _) _ _ _ _ _ _) =>
                 replace T with sh by (rewrite HSH; rewrite ?HDL; first
                   [ apply shift_of_dl; clear - TL RSV; lia
                   | change 63 with (Z.ones 6); rewrite Z.land_ones by (clear; lia); change (2 ^ 6) with 64; clear - TL RSV; Z.div_mod_to_equations; lia ])
             end;
             let HM := fresh "HM" in
             pose proof (x42_m1 (Z.to_nat dcap) m1 0 pe1 pe2 pe3 o1 b1 o2 b2 o3 b3 o4 b4 k1 k2 k3 k4 (Z_to_bv 64 b4)) as HM;
             replace (DST + 0) with DST in HM by (clear; lia);
             eapply HM; clear HM; lsideM
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9f7d8) _ _ _ _) =>
             (* [comment removed for export] *)
             eapply KX; lsideM
         end.
    all: try (clear - HE PE2 PE3 PE4; unfold HINV in *; lia).
  Qed.
End DX42M0.
End CANSEC1.
