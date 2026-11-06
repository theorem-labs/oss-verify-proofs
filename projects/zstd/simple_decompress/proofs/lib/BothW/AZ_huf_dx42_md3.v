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
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42 AZ_huf_dx42_mh.
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
Section DX42MD3.
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
  Notation WDM := [(DST, DST + dcap); (SPV - 384, SPV - 104)].
  Notation Q61 := (Z_to_bv 64 2305843009213693952).
  (* [comment removed for export] *)
  Notation K0 :=
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
        DST <= P1 -> P1 <= DST + dcap -> P2 <= DST + dcap -> P3 <= DST + dcap ->   (* [comment removed for export] *)
        DST + pe1 <= P2 -> DST + pe2 <= P3 -> DST + pe3 <= P4 -> P4 <= DST + dcap ->
        evtF bsegs RNG POST (ST 0xa74b4 mm' y1 y5 y6 y7 y8 (Z_to_bv 64 P4) y10 y11 (Z_to_bv 64 P1) y13 y14 y15 y16
                                (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 P3) (Z_to_bv 64 P2) y20 SB y22 y23 y24 y25 y26 y27 y28 y29
                                (Z_to_bv 64 (DT + 4)) y31)).

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

  (* [comment removed for export] *)
  Lemma x42_md3 : forall mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 u1 u2 u3 u4 c1 c2 c3 c4 (k1 k2 k3 k4 l5 l6 l7 l8 : word) (pad1 pad2 pad3 pad4 : list byte)
      (x1 x11 x13 x28 x29 : word)
      (w0 w4 w5 w7 : word),
    munch WDM mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> stk bsegs mm lo (SPV + -384) ->
    (FRS mm w0 (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 k2 (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 (DST + pe2)) k4 k3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
    (BD1 mm k1 (Z_to_bv 64 (c1)) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8))) ->
    (BD2 mm k2 (Z_to_bv 64 (c2)) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8))) ->
    (BD3 mm k3 (Z_to_bv 64 (c3)) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8))) ->
    (BD4 mm k4 (Z_to_bv 64 (c4)) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8))) ->
    bytes_at bsegs mm S1 bs1 -> bytes_at bsegs mm S2 bs2 -> bytes_at bsegs mm S3 bs3 -> bytes_at bsegs mm S4 bs4 ->
    HINV o1 n1 b1 -> HINV o2 n2 b2 -> HINV o3 n3 b3 -> HINV o4 n4 b4 ->
    q1 + 8 <= dcap -> q2 + 8 <= dcap -> q3 + 8 <= dcap -> q4 + 8 <= dcap -> 0 <= q1 -> 0 <= q2 -> 0 <= q3 -> 0 <= q4 ->
    1 <= bv_unsigned l5 <= 2 ->
    1 <= bv_unsigned l6 <= 2 ->
    1 <= bv_unsigned l7 <= 2 ->
    1 <= bv_unsigned l8 <= 2 ->
    q1 + 1 <= u1 <= q1 + 2 ->
    q2 + 1 <= u2 <= q2 + 2 ->
    q3 + 1 <= u3 <= q3 + 2 ->
    q4 + 1 <= u4 <= q4 + 2 ->
    b1 <= c1 <= b1 + 24 ->
    b2 <= c2 <= b2 + 24 ->
    b3 <= c3 <= b3 + 24 ->
    b4 <= c4 <= b4 + 24 ->
    (forall mm' v1' v2' v3' v4' c1' c2' c3' c4' (l9' l10' l11' l12' : word) (w0 w4 w5 w7 : word) (y11 y13 y26 y27 y29 : word),
        munch WDM mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb -> stk bsegs mm' lo (SPV + -384) ->
        (FRS mm' w0 (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 k2 (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 (DST + pe2)) k4 k3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
        (BD1 mm' k1 (Z_to_bv 64 (c1')) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8))) ->
        (BD2 mm' k2 (Z_to_bv 64 (c2')) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8))) ->
        (BD3 mm' k3 (Z_to_bv 64 (c3')) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8))) ->
        (BD4 mm' k4 (Z_to_bv 64 (c4')) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8))) ->
        bytes_at bsegs mm' S1 bs1 -> bytes_at bsegs mm' S2 bs2 -> bytes_at bsegs mm' S3 bs3 -> bytes_at bsegs mm' S4 bs4 ->
        1 <= bv_unsigned l9' <= 2 ->
        1 <= bv_unsigned l10' <= 2 ->
        1 <= bv_unsigned l11' <= 2 ->
        1 <= bv_unsigned l12' <= 2 ->
        q1 + 2 <= v1' <= q1 + 4 ->
        q2 + 2 <= v2' <= q2 + 4 ->
        q3 + 2 <= v3' <= q3 + 4 ->
        q4 + 2 <= v4' <= q4 + 4 ->
        b1 <= c1' <= b1 + 36 ->
        b2 <= c2' <= b2 + 36 ->
        b3 <= c3' <= b3 + 36 ->
        b4 <= c4' <= b4 + 36 ->
        evtF bsegs RNG POST (ST 0xa6914 mm' l10' (Z_to_bv 64 (2305843009213693952)) (Z_to_bv 64 (sh)) (Z_to_bv 64 (nd)) (Z_to_bv 64 (c1')) (Z_to_bv 64 (DST + v4')) k1 y11 (Z_to_bv 64 (DST + v1')) y13 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) k2 (Z_to_bv 64 (DST + v3')) (Z_to_bv 64 (DST + v2')) (Z_to_bv 64 (c2')) SB l12' (Z_to_bv 64 (c3')) (Z_to_bv 64 (c4')) l9' y26 y27 l11' y29 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (S4 + o4)))) ->
    evtF bsegs RNG POST (ST 0xa663c mm x1 (Z_to_bv 64 (2305843009213693952)) (Z_to_bv 64 (sh)) (Z_to_bv 64 (nd)) (Z_to_bv 64 (c1)) (Z_to_bv 64 (DST + u4)) k1 x11 (Z_to_bv 64 (DST + u1)) x13 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) k2 (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (c2)) SB l8 (Z_to_bv 64 (c3)) (Z_to_bv 64 (c4)) l5 l6 l7 x28 x29 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (S4 + o4))).
  Proof using CTX X2OK ACTX HRL NBOK HDL PE1 PE2 PE3 PE4 HSH HND BL1 SS1 SE1 LN1 BL2 SS2 SE2 LN2 BL3 SS3 SE3 LN3 BL4 SS4 SE4 LN4.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mm q1 q2 q3 q4 o1 b1 o2 b2 o3 b3 o4 b4 u1 u2 u3 u4 c1 c2 c3 c4 k1 k2 k3 k4 l5 l6 l7 l8 pad1 pad2 pad3 pad4
      x1 x11 x13 x28 x29
      w0 w4 w5 w7
      MU WM MU0 WM0 MI OUT DTB STK FR B1 B2 B3 B4 SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 HQ1 HQ2 HQ3 HQ4 HP1 HP2 HP3 HP4
      HL5 HL6 HL7 HL8 HU1 HU2 HU3 HU4 HC1 HC2 HC3 HC4 K.
    unfold HINV in HI1, HI2, HI3, HI4.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    ffacts OS1 OS3 LO. dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. kclean.
    assert (TL12 : 2 ^ tl <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; clear - TL; lia).
    assert (TBL : tbl_in_log bsegs mm DT sh 4 7 1 2) by (rewrite HSH; exact (x42_tblA dtb tl DT mm DL TL X2OK DTB)).
    assert (TBN : tbl_in_log bsegs mm DT sh 4 6 0 12).
    { apply (tbl_in_log_bytes_at bsegs mm DT dtb sh 4 6 0 12 DTB); [clear - R3 DL HSH TL; lia | clear - HSH TL; lia |].
      intros i Hi. replace (64 - sh) with tl in Hi by (clear - HSH; lia). destruct (NBOK i Hi) as (bb & Hb & Hr). exists bb. split; [exact Hb|].
      pose proof (bv_unsigned_in_range 8 bb). lia. }
    assert (KF : (8 <= dcap - q1 <= 4294967296) /\ (8 <= dcap - q2 <= 4294967296) /\ (8 <= dcap - q3 <= 4294967296) /\ (8 <= dcap - q4 <= 4294967296) /\ (0 <= q1 <= 4294967296) /\ (0 <= q2 <= 4294967296) /\ (0 <= q3 <= 4294967296) /\ (0 <= q4 <= 4294967296) /\ (4096 <= DST + q1 <= 140737488355320) /\ (4096 <= DST + q2 <= 140737488355320) /\ (4096 <= DST + q3 <= 140737488355320) /\ (4096 <= DST + q4 <= 140737488355320) /\ (52 <= sh <= 63) /\ (0 <= b1 <= 64) /\ (0 <= b2 <= 64) /\ (0 <= b3 <= 64) /\ (0 <= b4 <= 64) /\ (4100 <= DT + 4 <= 140737488338944) /\ (0 <= c1 <= 88) /\ (0 <= c2 <= 88) /\ (0 <= c3 <= 88) /\ (0 <= c4 <= 88))
      by (clear - HQ1 HQ2 HQ3 HQ4 HP1 HP2 HP3 HP4 HSH TL TL12 R1 R3 HI1 HI2 HI3 HI4 HL5 HL6 HL7 HL8 HU1 HU2 HU3 HU4 HC1 HC2 HC3 HC4; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 & KF13 & KF14 & KF15 & KF16 & KF17 & KF18 & KF19 & KF20 & KF21 & KF22).
    (* [comment removed for export] *)
    assert (SFM : (4096 <= S1 <= 140737488355328) /\ (4096 <= S1 + n1 <= 140737488355328) /\ (1 <= n1 <= 4294967296) /\ (DST + dcap <= S1 \/ S1 + n1 <= DST) /\
                  (4096 <= S2 <= 140737488355328) /\ (4096 <= S2 + n2 <= 140737488355328) /\ (1 <= n2 <= 4294967296) /\ (DST + dcap <= S2 \/ S2 + n2 <= DST) /\
                  (4096 <= S3 <= 140737488355328) /\ (4096 <= S3 + n3 <= 140737488355328) /\ (1 <= n3 <= 4294967296) /\ (DST + dcap <= S3 \/ S3 + n3 <= DST) /\
                  (4096 <= S4 <= 140737488355328) /\ (4096 <= S4 + n4 <= 140737488355328) /\ (1 <= n4 <= 4294967296) /\ (DST + dcap <= S4 \/ S4 + n4 <= DST))
      by (clear - SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4 R2 DJ1 GF4 GF5 GF6; lia).
    destruct SFM as (SF1a & SF1b & SF1c & SF1d & SF2a & SF2b & SF2c & SF2d & SF3a & SF3b & SF3c & SF3d & SF4a & SF4b & SF4c & SF4d).
    subst nd.
    remember (DST + u1) as A1 eqn:HA1 in |- *. remember (DST + u2) as A2 eqn:HA2 in |- *. remember (DST + u3) as A3 eqn:HA3 in |- *. remember (DST + u4) as A4 eqn:HA4 in |- *.
    assert (KA : (4096 <= A1 <= 140737488355322) /\ (4096 <= A2 <= 140737488355322) /\ (4096 <= A3 <= 140737488355322) /\ (4096 <= A4 <= 140737488355322) /\
                 (DST <= A1 /\ A1 + 6 <= DST + dcap) /\ (DST <= A2 /\ A2 + 6 <= DST + dcap) /\
                 (DST <= A3 /\ A3 + 6 <= DST + dcap) /\ (DST <= A4 /\ A4 + 6 <= DST + dcap)) by (clear - HA1 HA2 HA3 HA4 KF R1 HU1 HU2 HU3 HU4; lia).
    destruct KA as (KA1 & KA2 & KA3 & KA4 & KA5 & KA6 & KA7 & KA8).
    assert (KB1 : mdh (A1 + 6 <= SPV - 384 \/ SPV - 384 + 280 <= A1)) by (unfold mdh; clear - KA5 DJF5; lia).
    assert (KB9 : mdh (A1 + 6 <= DT \/ DT + 16388 <= A1)) by (unfold mdh; clear - KA5 DJ2; lia).
    assert (KP1 : mdh (A1 + 6 <= 2147450880 \/ 17594333495296 <= A1)) by (unfold mdh; clear - KA5 DSTAc; lia).
    assert (KS1 : mdh (A1 + 6 <= S1 \/ S1 + n1 <= A1)) by (unfold mdh; clear - KA5 SF1d; lia).
    assert (KS2 : mdh (A1 + 6 <= S2 \/ S2 + n2 <= A1)) by (unfold mdh; clear - KA5 SF2d; lia).
    assert (KS3 : mdh (A1 + 6 <= S3 \/ S3 + n3 <= A1)) by (unfold mdh; clear - KA5 SF3d; lia).
    assert (KS4 : mdh (A1 + 6 <= S4 \/ S4 + n4 <= A1)) by (unfold mdh; clear - KA5 SF4d; lia).
    assert (KB2 : mdh (A2 + 6 <= SPV - 384 \/ SPV - 384 + 280 <= A2)) by (unfold mdh; clear - KA6 DJF5; lia).
    assert (KB10 : mdh (A2 + 6 <= DT \/ DT + 16388 <= A2)) by (unfold mdh; clear - KA6 DJ2; lia).
    assert (KP2 : mdh (A2 + 6 <= 2147450880 \/ 17594333495296 <= A2)) by (unfold mdh; clear - KA6 DSTAc; lia).
    assert (KS5 : mdh (A2 + 6 <= S1 \/ S1 + n1 <= A2)) by (unfold mdh; clear - KA6 SF1d; lia).
    assert (KS6 : mdh (A2 + 6 <= S2 \/ S2 + n2 <= A2)) by (unfold mdh; clear - KA6 SF2d; lia).
    assert (KS7 : mdh (A2 + 6 <= S3 \/ S3 + n3 <= A2)) by (unfold mdh; clear - KA6 SF3d; lia).
    assert (KS8 : mdh (A2 + 6 <= S4 \/ S4 + n4 <= A2)) by (unfold mdh; clear - KA6 SF4d; lia).
    assert (KB3 : mdh (A3 + 6 <= SPV - 384 \/ SPV - 384 + 280 <= A3)) by (unfold mdh; clear - KA7 DJF5; lia).
    assert (KB11 : mdh (A3 + 6 <= DT \/ DT + 16388 <= A3)) by (unfold mdh; clear - KA7 DJ2; lia).
    assert (KP3 : mdh (A3 + 6 <= 2147450880 \/ 17594333495296 <= A3)) by (unfold mdh; clear - KA7 DSTAc; lia).
    assert (KS9 : mdh (A3 + 6 <= S1 \/ S1 + n1 <= A3)) by (unfold mdh; clear - KA7 SF1d; lia).
    assert (KS10 : mdh (A3 + 6 <= S2 \/ S2 + n2 <= A3)) by (unfold mdh; clear - KA7 SF2d; lia).
    assert (KS11 : mdh (A3 + 6 <= S3 \/ S3 + n3 <= A3)) by (unfold mdh; clear - KA7 SF3d; lia).
    assert (KS12 : mdh (A3 + 6 <= S4 \/ S4 + n4 <= A3)) by (unfold mdh; clear - KA7 SF4d; lia).
    assert (KB4 : mdh (A4 + 6 <= SPV - 384 \/ SPV - 384 + 280 <= A4)) by (unfold mdh; clear - KA8 DJF5; lia).
    assert (KB12 : mdh (A4 + 6 <= DT \/ DT + 16388 <= A4)) by (unfold mdh; clear - KA8 DJ2; lia).
    assert (KP4 : mdh (A4 + 6 <= 2147450880 \/ 17594333495296 <= A4)) by (unfold mdh; clear - KA8 DSTAc; lia).
    assert (KS13 : mdh (A4 + 6 <= S1 \/ S1 + n1 <= A4)) by (unfold mdh; clear - KA8 SF1d; lia).
    assert (KS14 : mdh (A4 + 6 <= S2 \/ S2 + n2 <= A4)) by (unfold mdh; clear - KA8 SF2d; lia).
    assert (KS15 : mdh (A4 + 6 <= S3 \/ S3 + n3 <= A4)) by (unfold mdh; clear - KA8 SF3d; lia).
    assert (KS16 : mdh (A4 + 6 <= S4 \/ S4 + n4 <= A4)) by (unfold mdh; clear - KA8 SF4d; lia).
    assert (KSF1 : mdh (SPV - 384 + 280 <= S1 \/ S1 + n1 <= SPV - 384)) by (unfold mdh; clear - SS1 SE1 LN1 OS2 LO; lia).
    assert (KSF2 : mdh (SPV - 384 + 280 <= S2 \/ S2 + n2 <= SPV - 384)) by (unfold mdh; clear - SS2 SE2 LN2 OS2 LO; lia).
    assert (KSF3 : mdh (SPV - 384 + 280 <= S3 \/ S3 + n3 <= SPV - 384)) by (unfold mdh; clear - SS3 SE3 LN3 OS2 LO; lia).
    assert (KSF4 : mdh (SPV - 384 + 280 <= S4 \/ S4 + n4 <= SPV - 384)) by (unfold mdh; clear - SS4 SE4 LN4 OS2 LO; lia).
    assert (WAD : wr_at bsegs mm DST dcap)
      by (pose proof (wr_at_stk bsegs mm DST (DST + dcap) OUT ltac:(clear - KF; lia)) as W; replace (DST + dcap - DST) with dcap in W by (clear; lia); exact W).
    assert (UA1 : unpZ mm A1 (A1 + 6)) by (apply (unpoisoned_unpZ mm DST (DST + dcap) A1 (A1 + 6) UDSTc); [clear - KA5; lia | clear - KA5; lia | unfold KXKEND; clear - KA1; lia]).
    assert (RZ1 : rng RNG (KXSHLO + A1 / 8) (shspanZ A1 6)) by (apply (rng_sub' RNG _ _ _ _ RDSTz); unfold shspanZ; clear - KA1 KA5 GF1; Z.div_mod_to_equations; lia).
    assert (RW1 : rng RNG A1 6) by (apply (rng_sub RNG DST dcap A1 6 RDSTc); clear - KA5; lia).
    assert (WA1 : wr_at bsegs mm A1 6) by (apply (wr_at_sub bsegs mm DST dcap A1 6 WAD); clear - KA5; lia).
    assert (UA2 : unpZ mm A2 (A2 + 6)) by (apply (unpoisoned_unpZ mm DST (DST + dcap) A2 (A2 + 6) UDSTc); [clear - KA6; lia | clear - KA6; lia | unfold KXKEND; clear - KA2; lia]).
    assert (RZ2 : rng RNG (KXSHLO + A2 / 8) (shspanZ A2 6)) by (apply (rng_sub' RNG _ _ _ _ RDSTz); unfold shspanZ; clear - KA2 KA6 GF1; Z.div_mod_to_equations; lia).
    assert (RW2 : rng RNG A2 6) by (apply (rng_sub RNG DST dcap A2 6 RDSTc); clear - KA6; lia).
    assert (WA2 : wr_at bsegs mm A2 6) by (apply (wr_at_sub bsegs mm DST dcap A2 6 WAD); clear - KA6; lia).
    assert (UA3 : unpZ mm A3 (A3 + 6)) by (apply (unpoisoned_unpZ mm DST (DST + dcap) A3 (A3 + 6) UDSTc); [clear - KA7; lia | clear - KA7; lia | unfold KXKEND; clear - KA3; lia]).
    assert (RZ3 : rng RNG (KXSHLO + A3 / 8) (shspanZ A3 6)) by (apply (rng_sub' RNG _ _ _ _ RDSTz); unfold shspanZ; clear - KA3 KA7 GF1; Z.div_mod_to_equations; lia).
    assert (RW3 : rng RNG A3 6) by (apply (rng_sub RNG DST dcap A3 6 RDSTc); clear - KA7; lia).
    assert (WA3 : wr_at bsegs mm A3 6) by (apply (wr_at_sub bsegs mm DST dcap A3 6 WAD); clear - KA7; lia).
    assert (UA4 : unpZ mm A4 (A4 + 6)) by (apply (unpoisoned_unpZ mm DST (DST + dcap) A4 (A4 + 6) UDSTc); [clear - KA8; lia | clear - KA8; lia | unfold KXKEND; clear - KA4; lia]).
    assert (RZ4 : rng RNG (KXSHLO + A4 / 8) (shspanZ A4 6)) by (apply (rng_sub' RNG _ _ _ _ RDSTz); unfold shspanZ; clear - KA4 KA8 GF1; Z.div_mod_to_equations; lia).
    assert (RW4 : rng RNG A4 6) by (apply (rng_sub RNG DST dcap A4 6 RDSTc); clear - KA8; lia).
    assert (WA4 : wr_at bsegs mm A4 6) by (apply (wr_at_sub bsegs mm DST dcap A4 6 WAD); clear - KA8; lia).
    kx_autoFLA (FR, B1, B2, B3, B4) [KAUnp DT 16388; KAApp (SPV - 384) 280; KAUnp A1 6; KAUnp A2 6; KAUnp A3 6; KAUnp A4 6; KAApp A1 6; KAApp A2 6; KAApp A3 6; KAApp A4 6] [0xa6914; 0xac838] 300%nat
          [KZRange sh 52 63; KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
           KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944;
           KZRange SPV 17594333495296 140737488355328; KZTblLog DT sh 4 6 0 12; KZTblLog DT sh 4 7 1 2;
           KZRange S1 4096 140737488355328; KZRange (S1 + n1) 4096 140737488355328; KZRange n1 1 4294967296;
           KZRange S2 4096 140737488355328; KZRange (S2 + n2) 4096 140737488355328; KZRange n2 1 4294967296;
           KZRange S3 4096 140737488355328; KZRange (S3 + n3) 4096 140737488355328; KZRange n3 1 4294967296;
           KZRange S4 4096 140737488355328; KZRange (S4 + n4) 4096 140737488355328; KZRange n4 1 4294967296;
           KZWr (SPV + -384) 120; KZWr (SPV + -264) 40; KZWr (SPV + -224) 40; KZWr (SPV + -184) 40; KZWr (SPV + -144) 40;
           KZDisj (SPV - 384) 280 DT 16388;
           KZDisj (SPV - 384) 280 S1 n1; KZDisj (SPV - 384) 280 S2 n2; KZDisj (SPV - 384) 280 S3 n3; KZDisj (SPV - 384) 280 S4 n4;
           KZRange A1 4096 140737488355322; KZWr A1 6; KZDisj A1 6 (SPV - 384) 280; KZDisj A1 6 DT 16388; KZDisj A1 6 S1 n1; KZDisj A1 6 S2 n2; KZDisj A1 6 S3 n3; KZDisj A1 6 S4 n4;
           KZRange A2 4096 140737488355322; KZWr A2 6; KZDisj A2 6 (SPV - 384) 280; KZDisj A2 6 DT 16388; KZDisj A2 6 S1 n1; KZDisj A2 6 S2 n2; KZDisj A2 6 S3 n3; KZDisj A2 6 S4 n4;
           KZRange A3 4096 140737488355322; KZWr A3 6; KZDisj A3 6 (SPV - 384) 280; KZDisj A3 6 DT 16388; KZDisj A3 6 S1 n1; KZDisj A3 6 S2 n2; KZDisj A3 6 S3 n3; KZDisj A3 6 S4 n4;
           KZRange A4 4096 140737488355322; KZWr A4 6; KZDisj A4 6 (SPV - 384) 280; KZDisj A4 6 DT 16388; KZDisj A4 6 S1 n1; KZDisj A4 6 S2 n2; KZDisj A4 6 S3 n3; KZDisj A4 6 S4 n4;
           KZRange c1 0 88; KZRange c2 0 88; KZRange c3 0 88; KZRange c4 0 88; KZRange (bv_unsigned l5) 1 2; KZRange (bv_unsigned l6) 1 2; KZRange (bv_unsigned l7) 1 2; KZRange (bv_unsigned l8) 1 2]
          [(DT, 16388); (SPV + -384, 120); (SPV + -264, 40); (SPV + -224, 40); (SPV + -184, 40); (SPV + -144, 40)] [(DT, 16388); (A1, 6); (A2, 6); (A3, 6); (A4, 6); (SPV - 400, 400)].
    all: aside.
    all: traps.
    all: clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12 KF13 KF14 KF15 KF16 KF17 KF18 KF19 KF20 KF21 KF22.
    all: clear KA1 KA2 KA3 KA4 KA5 KA6 KA7 KA8 KB1 KB2 KB3 KB4 KB9 KB10 KB11 KB12 KS1 KS2 KS3 KS4 KS5 KS6 KS7 KS8 KS9 KS10 KS11 KS12 KS13 KS14 KS15 KS16 KP1 KP2 KP3 KP4 KSF1 KSF2 KSF3 KSF4 WAD UA1 RZ1 RW1 WA1 UA2 RZ2 RW2 WA2 UA3 RZ3 RW3 WA3 UA4 RZ4 RW4 WA4.
    all: aclean.
    all: kx_gen_regsF [11%nat; 13%nat; 26%nat; 27%nat; 29%nat]; intros.
    all: evw.
    all: kx_mem.
    all: kx_strip_mod.
    all: lclean2.
    all: subst A1 A2 A3 A4.
    (* [comment removed for export] *)
    all: repeat match goal with
         | |- context [Z_to_bv 64 (DST + ?a + ?b)] => replace (DST + a + b) with (DST + (a + b)) by (clear; lia)
         | |- context [Z_to_bv 64 (?a + (DST + ?b))] => replace (a + (DST + b)) with (DST + (b + a)) by (clear; lia)
         end.
    all: eapply K.
    all: kside.
  Qed.
End DX42MD3.
End CANSEC1.
