(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image InitMem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2 ZdWalkKit ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_libc_iface AZ_huf_lbkit AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_c0 AZ_huf_dx41_i4 AZ_huf_dx41_fq AZ_huf_dx41_e AZ_huf_dx41_ffo.
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

(* [comment removed for export] *)
#[local] Ltac kx_rd_at ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      first [ match goal with
              | H : bytes_at segs m A ?bs |- _ => apply (rd_at_sub segs m A (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A bs H)); kx_lia
              | H : rw_cells segs m A ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (rd_at_sub segs m A n A N (rd_at_rw_cells segs m A cs H)); kx_lia
              | H : ro_cells segs m A ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (rd_at_sub segs m A n A N (rd_at_ro_cells segs m A cs H)); kx_lia
              end
            | let A' := eval lazy in A in
              lazymatch A' with Z0 => idtac | Zpos _ => idtac end;
              apply (rd_at_imgZ segs m A N); [lia | lia | lia | vm_compute; reflexivity]
            | match goal with
              | H : bytes_at segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A0 bs H)); kx_lia
              | H : u8arr segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_u8arr segs m A0 bs H)); kx_lia
              | H : rw_cells segs m ?A0 ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (rd_at_sub segs m A0 n A N (rd_at_rw_cells segs m A0 cs H)); kx_lia
              | H : ro_cells segs m ?A0 ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (rd_at_sub segs m A0 n A N (rd_at_ro_cells segs m A0 cs H)); kx_lia
              | H : stk segs m ?lo ?hi |- _ => apply (rd_at_sub segs m lo (hi - lo) A N); [apply (rd_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
              end ]
  end.
Section CANSEC1. Context {rc : runConstT}.
Section DX41AM.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x41a_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis HRL : huf_reload_int_stmtA.
  Hypothesis DHI : dst_hi dcap DST.
  Hypothesis NBOK : huf_nb_ok false dtb tl.
  Hypothesis TL11 : tl = 11.
  Hypothesis XMC : zd_memcpyZ_stmtA.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 :=
    (rw_cells bsegs mm (SPV + -480) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12]).
  Notation BD1 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -376) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -144) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -184) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation WDM := [(DST, DST + dcap); (SPV - 480, SPV - 336); (SPV - 224, SPV - 104)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).

  (* [comment removed for export] *)
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt ilow oend ie0 ie1 ie2 ie3 :=
    (rw_cells bsegs mm (SPV + -376) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 b0; C8 b1; C8 b2; C8 b3;
                                     C8 adt; C8 ilow; C8 oend; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  (* [comment removed for export] *)
  Notation LOCO mm p0 p1 p2 p3 u := (rw_cells bsegs mm (SPV + -224) [C8 p0; C8 p1; C8 p2; C8 p3; C8 u]).
  Notation LOCI mm i0 i1 i2 i3 u := (rw_cells bsegs mm (SPV + -184) [C8 i0; C8 i1; C8 i2; C8 i3; C8 u]).
  Notation LOCB mm c0 c1 c2 c3 u := (rw_cells bsegs mm (SPV + -144) [C8 c0; C8 c1; C8 c2; C8 c3; C8 u]).
  Notation SVS mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Notation WDF := [(DST, DST + dcap); (SPV - 480, SPV - 104)].
  Notation WD := [(DST, DST + dcap)].
  Notation TBLV := (Z_to_bv 64 139943).
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\ (4096 <= SRC <= 140737488355328) /\
                 (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\ (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\
                 (0 <= rsv <= 255) /\ (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333498016 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
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
  (* [comment removed for export] *)
  Ltac sfactsF BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc :=
    lazymatch type of BSE with ?S + ?len <= SRC + n =>
      let sf := fresh "SF" in
      assert (sf : (4096 <= S <= 140737488355328) /\ (4096 <= S + len <= 140737488355328) /\ (1 <= len <= 4294967296) /\ S + len < 2^47 /\
                   (DST + dcap <= S \/ S + len <= DST) /\ (S + len <= lo \/ SPV <= S) /\
                   (SPV - 480 + 144 <= S \/ S + len <= SPV - 480) /\ (SPV - 224 + 120 <= S \/ S + len <= SPV - 224) /\
                   (0 <= S - 0 < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= S < 2 ^ 64))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      let a1 := fresh "SF" in let a2 := fresh "SF" in let a3 := fresh "SF" in let a4 := fresh "SF" in
      let a5 := fresh "SF" in let a6 := fresh "SF" in let a7 := fresh "SF" in let a8 := fresh "SF" in let a9 := fresh "SF" in
      destruct sf as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9);
      let rs := fresh "RS" in
      assert (rs : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia));
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia))
      end
    end.
  Ltac zsfacts :=
    assert (ZS1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS3 : 0 <= SPV - 480 - -480 < 2 ^ 64 /\ 0 <= 144 < 2 ^ 64 /\ 0 <= SPV - 480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -480 - -480 < 2 ^ 64 /\ 0 <= 144 < 2 ^ 64 /\ 0 <= SPV + -480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV - 224 - -224 < 2 ^ 64 /\ 0 <= 120 < 2 ^ 64 /\ 0 <= SPV - 224 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -224 - -224 < 2 ^ 64 /\ 0 <= 120 < 2 ^ 64 /\ 0 <= SPV + -224 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 480 - -480 < 2 ^ 64 /\ 0 <= 480 < 2 ^ 64 /\ 0 <= SPV - 480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia);
    assert (ZS9 : 0 <= SPV + -480 - -480 < 2 ^ 64 /\ 0 <= 104 < 2 ^ 64 /\ 0 <= SPV + -480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS10 : 0 <= SPV + -376 - -376 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -376 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS11 : 0 <= SPV + -144 - -144 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -144 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS12 : 0 <= SPV + -184 - -184 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -184 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS13 : 0 <= SPV + -224 - -224 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -224 < 2 ^ 64) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 480 \/ SPV - 480 + 144 <= DST) /\ (DST + dcap <= SPV - 224 \/ SPV - 224 + 120 <= DST) /\
                 (SPV - 224 + 120 <= DT \/ DT + 16388 <= SPV - 224) /\ (SPV - 480 + 144 <= DT \/ DT + 16388 <= SPV - 480) /\
                 (DST + dcap <= SPV - 480 \/ SPV - 480 + 480 <= DST))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4 & DJF5).
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
           | H : 0 <= _ - 0 < 2 ^ 64 /\ _ |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac kx_lia_or1 :=
    match goal with
    | H : _ \/ _ |- _ =>
        solve [ repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end;
                repeat match goal with H' : _ -> _ |- _ => clear H' end; lia ]
    end.
  Ltac kx_lia_m1 := first [ solve [kx_clear_or; lia] | solve [kx_lia_or1] | kx_bv_ranges; solve [kx_clear_or; lia] | solve [kx_bv_ranges; kx_lia_or1] ].
  #[local] Ltac kx_lia ::= kx_lia_m1.
  #[local] Ltac kxl_lia ::= first [ kxl_hyp | solve [kx_clear_or; lia] | solve [kxl_lia_small] | kx_lia_m1 ].
  (* [comment removed for export] *)
  Ltac lclean2 :=
    repeat match goal with H : ?o = 0 \/ _ |- _ => revert H end;
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : rng _ _ _ |- _ => clear H
           | H : rng_aimg _ |- _ => clear H
           | H : 4096 <= _ <= _ |- _ => clear H
           | H : 17594333495296 <= _ <= _ |- _ => clear H
           | H : 17594333498016 <= _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
           | H : atoms_ok _ _ |- _ => clear H
           | H : reads_ok _ _ _ _ _ |- _ => clear H
           | H : know_ok _ _ _ _ |- _ => clear H
           end;
    intros.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa413c) _ _ _ _) => kx_trap_fast end).
  Ltac evr := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end); kx_ev_ranges.
  Ltac lside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [assumption | lia | kx_lia | idtac]
    | |- _ \/ _ => first [assumption | lia | idtac]
    | |- Z.le _ _ => first [assumption | lia]
    | |- Z.lt _ _ => first [assumption | lia]
    | |- _ => eassumption
    end.

  (* [comment removed for export] *)
  Ltac sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS :=
    sfacts0 MU0 USRC DSTA AW0 R1 R2;
    pose proof (rng_shspanZ _ _ _ RSRCS) as RSz;
    lazymatch goal with U : unpoisoned ?mm SRC (SRC + n) |- _ =>
      pose proof (unpoisoned_unpZ mm _ _ SRC (SRC + n) U ltac:(lia) ltac:(clear - R2; lia) ltac:(unfold KXKEND; clear - R2; lia)) as USz end.
  (* [comment removed for export] *)
  Ltac kcleanF :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < dcap -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < dcap -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : aro_client RNG m0 |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac lclean3 :=
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
           end.
  Ltac lsideF := lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- _ => lside
    end.
  Ltac zsfactsF :=
    assert (ZF1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF3 : 0 <= SRC - 0 < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= SRC < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF4 : 0 <= SPV - 480 - -480 < 2 ^ 64 /\ 0 <= 376 < 2 ^ 64 /\ 0 <= SPV - 480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF5 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Notation KW mb x8 x15 x17 x18 x19 x20 x21 x23 x24 x26 x29 x30 x31 w0 w1 w2 w3 w4 w12 :=
    (forall mm' (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y16 y22 y25 y27 y28 : word),
        munch WD mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w0 w1 w2 w3 w4 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) OEND w12) -> bytes_at bsegs mm' SRC src ->
        evtF bsegs RNG POST (ST 0xa0fb0 mm' y1 y5 y6 y7 x8 y9 y10 y11 y12 y13 y14 x15 y16 x17 x18 x19 x20 x21 y22 x23 x24 y25 x26 y27 y28 x29 x30 x31)).
  Notation X41PF := (AZ_huf_dx41_fq.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo).
  Notation x41_fo := (AZ_huf_dx41_ffo.x41_fo RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI NBOK TL11 XMC).

  (* [comment removed for export] *)
  Ltac asan_now MU0 WM0 AZS ART DSTA LO KLO R1 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (AZmm : azstk RNG mm lo SPV)
      by (eapply azstk_transport; [exact AZS | exact MU0 | exact WM0 | apply aappW_cons_D; [exact DSTA | lia | exact AW0] | clear - LO; lia]);
    assert (ARTmm : art mm)
      by (eapply (art_transportW _ m0 mm ART MU0 WM0); constructor; [cbn [fst]; pose proof (DHI ltac:(lia)); unfold dst_hi in *; lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]]);
    clear AW0.
  (* [comment removed for export] *)
  Ltac fixaddr H a := lazymatch type of H with rw_cells _ _ ?x _ => replace x with a in H by (cbn; lia) end.
  Ltac mc_side SB2 A2 STK AZmm ARTmm RSTK RI ASTK LO GS :=
    first [ lazymatch goal with
            | |- evtF _ _ _ _ => idtac
            | |- bytes_at _ _ _ _ => exact SB2
            | |- length _ = _ => cbn [cells_bytes cbytes app]; rewrite !length_app, !length_le8; reflexivity
            | |- rw_cells _ _ _ _ => exact A2
            | |- mem_inv _ _ => assumption
            | |- stk _ _ _ _ => exact STK
            | |- app_blk _ _ => eapply (azstk_app _ _ _ _ _ _ AZmm); clear - LO; lia
            | |- aro _ _ _ _ => eapply (azstk_aro _ _ _ _ _ _ AZmm); [clear - LO; lia | clear; lia | clear - LO; lia | eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]]
            | |- ahull _ _ _ _ => eapply (azstk_ahull _ _ _ _ _ _ AZmm); clear - LO; lia
            | |- art _ => exact ARTmm
            | |- astk _ _ _ => exact ASTK
            | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
            | |- _ \/ _ => clear - LO GS; lia
            | |- _ => clear - LO GS; lia
            end
          | lazymatch goal with |- ?G => idtac "MCSIDE-LEFT:" G end ].

  (* [comment removed for export] *)
  Ltac carve40 A A32 D U u :=
    lazymatch goal with B : rw_cells bsegs ?m A [CB 40 ?j] |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      let e := fresh "e" in let jb := fresh "jb" in let ju := fresh "ju" in
      destruct (cb_carve bsegs m A 40 j 0 32 B ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (e & jb & ju & _ & D & U); clear B;
      change (Z.to_nat 32) with 32%nat in D; change (40 - Z.to_nat 0 - Z.to_nat 32)%nat with (8 * 1)%nat in U;
      replace (A + 0) with A in D by (clear; lia); replace (A + 0 + 32) with A32 in U by (clear; lia);
      apply (cb_as_c8s _ _ 1) in U; cbn [c8s_of] in U;
      set (u := le_bytes_to_word (firstn 8 ju)) in U; clearbody u; clear e ju
    end.

  (* [comment removed for export] *)
  Lemma x41_fast : AZ_huf_dx41_e.x41_fast_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb.
  Proof using CTX ACTX DHI NBOK TL11 XMC.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    unfold AZ_huf_dx41_e.x41_fast_stmt.
    intros mm l1 l2 l3 b0 b1 b2 b3 junk4 junk3 junk2 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w0 w1 w2 w3 w4 w8 w12
      SV STK MU0 WM0 MI OUT DTB SRCB FR AR BJ4 BJ3 BJ2 HL1 HL2 HL3 HLN HQ3 TL11' HS0 HS1 HS2 HS3.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (ASTK' : astk RNG lo (SPV + -480)) by (split; [exact KLO | split; [eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia] | exact RI]]).
    assert (DP : 0 < dcap) by (clear - HQ3 R1; lia).
    assert (RFR : rng RNG (SPV - 480) 480) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (HLB0 : LBW 8 b0) by (unfold LBW; apply lb_of_mod512; exact HS0).
    assert (HLB1 : LBW 8 b1) by (unfold LBW; apply lb_of_mod512; exact HS1).
    assert (HLB2 : LBW 8 b2) by (unfold LBW; apply lb_of_mod512; exact HS2).
    assert (HLB3 : LBW 8 b3) by (unfold LBW; apply lb_of_mod512; exact HS3).
    (* [comment removed for export] *)
    unfold fast_args_cells in AR. cbv zeta in AR.
    replace (SRC + 6 + l1 - 8) with (SRC + (l1 - 2)) in AR by (clear; lia).
    replace (SRC + 6 + l1 + l2 - 8) with (SRC + (l1 + l2 - 2)) in AR by (clear; lia).
    replace (SRC + 6 + l1 + l2 + l3 - 8) with (SRC + (l1 + l2 + l3 - 2)) in AR by (clear; lia).
    replace (SRC + n - 8) with (SRC + (n - 8)) in AR by (clear; lia).
    replace (SRC + 6 + l1 + l2 + l3) with (SRC + (6 + l1 + l2 + l3)) in AR by (clear; lia).
    replace (SRC + 6 + l1 + l2) with (SRC + (6 + l1 + l2)) in AR by (clear; lia).
    replace (SRC + 6 + l1) with (SRC + (6 + l1)) in AR by (clear; lia).
    replace (C8 (Z_to_bv 64 DST)) with (C8 (Z_to_bv 64 (DST + 0))) in AR by (do 2 f_equal; clear; lia).
    lazymatch type of AR with rw_cells bsegs mm (SPV + -376) [C8 (Z_to_bv 64 (SRC + (l1 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 + l3 - 2))); C8 (Z_to_bv 64 (SRC + (n - 8))); C8 (Z_to_bv 64 (DST + 0)); C8 (Z_to_bv 64 (DST + (dcap + 3) / 4)); C8 (Z_to_bv 64 (DST + 2 * ((dcap + 3) / 4))); C8 (Z_to_bv 64 (DST + 3 * ((dcap + 3) / 4))); C8 b0; C8 b1; C8 b2; C8 b3; C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (SRC + 6)); C8 (Z_to_bv 64 (SRC + (6 + l1))); C8 (Z_to_bv 64 (SRC + (6 + l1 + l2))); C8 (Z_to_bv 64 (SRC + (6 + l1 + l2 + l3)))] => idtac | ?T => fail 100 "unexpected args cells" T end.
    assert (KF : (38 <= n <= 4294967296) /\ (1 <= dcap <= 4294967296)) by (clear - HL1 HL2 HL3 HLN DP R1 R2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2).
    (* [comment removed for export] *)
    kx_autoFLA (FR, AR) (@nil kza) [0x9f5d8; 0xa105c] 25%nat
      [KZRange SPV 17594333498016 140737488355328; KZRange n 38 4294967296; KZRange dcap 1 4294967296; KZRange DST 4096 140737488355328;
       KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944;
       KZWr (SPV + -480) 104; KZDisj (SPV - 480) 104 SRC n; KZDisj (SPV - 480) 104 DT 16388]
      [(SPV + -480, 104); (SPV + -376, 152)] [(SPV - 480, 480)].
    all: [> aside ..].
    all: [> kx_mem ..].
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "RUN0-LEAF" pc end.
    try clear KF KF1 KF2. try clear KXK; try clear KXA; try clear KXRD; try clear KXE.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch W0 m0 ?m, WM : wmono bsegs m0 ?m |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => asan_now MU WM AZS ART DSTA LO KLO R1 end.
    zstep. zstep. zstep. zstep. kx_mkR_fold.
    lazymatch goal with A : rw_cells bsegs ?m (SPV + -376) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      apply (proj1 (rw_cells_app bsegs _ _ [_; _; _; _] _)) in A; destruct A as [ARi A1]; fixaddr A1 (SPV + -344);
      apply (proj1 (rw_cells_app bsegs _ _ [_; _; _; _] _)) in A1; destruct A1 as [ARo A2]; fixaddr A2 (SPV + -312);
      apply (proj1 (rw_cells_app bsegs _ _ [_; _; _; _] _)) in A2; destruct A2 as [ARb AR3]; fixaddr AR3 (SPV + -280) end.
    pose proof (proj2 (proj1 ARb)) as SBb.
    carve40 (SPV + -144) (SPV + -112) DB2 UB2 ub.
    lazymatch goal with H : stk bsegs ?m lo (SPV + -480) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename H into STK1 end.
    call (XMC RNG (SPV + -144) (SPV + -312) 32 (SPV + -480)).
    all: mc_side SBb DB2 STK1 AZmm ARTmm RSTK RI ASTK' LO GF7.
    try clear STK1; try clear AZmm; try clear ARTmm; try clear SBb; try clear DB2.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -144) [CB _ _] |- _ =>
      assert (LB4 : rw_cells bsegs m (SPV + -144) [C8 b0; C8 b1; C8 b2; C8 b3])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch W0 m0 ?m, WM : wmono bsegs m0 ?m |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => asan_now MU WM AZS ART DSTA LO KLO R1 end.
    zstep. zstep. zstep. zstep. kx_mkR_fold.
    lazymatch goal with A : rw_cells bsegs ?m (SPV + -376) [_; _; _; _] |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => pose proof (proj2 (proj1 A)) as SBi end.
    carve40 (SPV + -184) (SPV + -152) DB3 UB3 ui.
    lazymatch goal with H : stk bsegs ?m lo (SPV + -480) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename H into STK2 end.
    call (XMC RNG (SPV + -184) (SPV + -376) 32 (SPV + -480)).
    all: mc_side SBi DB3 STK2 AZmm ARTmm RSTK RI ASTK' LO GF7.
    try clear STK2; try clear AZmm; try clear ARTmm; try clear SBi; try clear DB3.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -184) [CB _ _] |- _ =>
      assert (LI4 : rw_cells bsegs m (SPV + -184) [C8 (Z_to_bv 64 (SRC + (l1 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 + l3 - 2))); C8 (Z_to_bv 64 (SRC + (n - 8)))])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch W0 m0 ?m, WM : wmono bsegs m0 ?m |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => asan_now MU WM AZS ART DSTA LO KLO R1 end.
    zstep. zstep. zstep. zstep. zstep. kx_mkR_fold.
    lazymatch goal with A : rw_cells bsegs ?m (SPV + -344) [_; _; _; _] |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => pose proof (proj2 (proj1 A)) as SBo end.
    carve40 (SPV + -224) (SPV + -192) DB4 UB4 uo.
    lazymatch goal with H : stk bsegs ?m lo (SPV + -480) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename H into STK3 end.
    call (XMC RNG (SPV + -224) (SPV + -344) 32 (SPV + -480)).
    all: mc_side SBo DB4 STK3 AZmm ARTmm RSTK RI ASTK' LO GF7.
    try clear STK3; try clear AZmm; try clear ARTmm; try clear SBo; try clear DB4.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -224) [CB _ _] |- _ =>
      assert (LO4 : rw_cells bsegs m (SPV + -224) [C8 (Z_to_bv 64 (DST + 0)); C8 (Z_to_bv 64 (DST + (dcap + 3) / 4)); C8 (Z_to_bv 64 (DST + 2 * ((dcap + 3) / 4))); C8 (Z_to_bv 64 (DST + 3 * ((dcap + 3) / 4)))])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    try clear POST POST0 POST1.
    (* [comment removed for export] *)
    lazymatch goal with I : rw_cells bsegs ?m (SPV + -376) [_; _; _; _], O : rw_cells bsegs ?m (SPV + -344) [_; _; _; _],
                        B : rw_cells bsegs ?m (SPV + -312) [_; _; _; _], Q : rw_cells bsegs ?m (SPV + -280) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      assert (AR : rw_cells bsegs m (SPV + -376) [C8 (Z_to_bv 64 (SRC + (l1 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 + l3 - 2))); C8 (Z_to_bv 64 (SRC + (n - 8))); C8 (Z_to_bv 64 (DST + 0)); C8 (Z_to_bv 64 (DST + (dcap + 3) / 4)); C8 (Z_to_bv 64 (DST + 2 * ((dcap + 3) / 4))); C8 (Z_to_bv 64 (DST + 3 * ((dcap + 3) / 4))); C8 b0; C8 b1; C8 b2; C8 b3; C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (SRC + 6)); C8 (Z_to_bv 64 (SRC + (6 + l1))); C8 (Z_to_bv 64 (SRC + (6 + l1 + l2))); C8 (Z_to_bv 64 (SRC + (6 + l1 + l2 + l3)))]);
      [ apply (proj2 (rw_cells_app bsegs _ (SPV + -376) [_; _; _; _] _)); split; [exact I|];
        lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -344) by (cbn; lia) end;
        apply (proj2 (rw_cells_app bsegs _ (SPV + -344) [_; _; _; _] _)); split; [exact O|];
        lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -312) by (cbn; lia) end;
        apply (proj2 (rw_cells_app bsegs _ (SPV + -312) [_; _; _; _] _)); split; [exact B|];
        lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -280) by (cbn; lia) end; exact Q
      | clear I O B Q ] end.
    lazymatch goal with U2 : rw_cells bsegs ?m (SPV + -112) [C8 ub], U3 : rw_cells bsegs ?m (SPV + -152) [C8 ui], U4 : rw_cells bsegs ?m (SPV + -192) [C8 uo]
                   |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      assert (LCO : LOCO m (Z_to_bv 64 (DST + 0)) (Z_to_bv 64 (DST + (dcap + 3) / 4)) (Z_to_bv 64 (DST + 2 * ((dcap + 3) / 4))) (Z_to_bv 64 (DST + 3 * ((dcap + 3) / 4))) uo)
        by (apply (proj2 (rw_cells_app bsegs _ (SPV + -224) [_; _; _; _] _)); split; [exact LO4|];
            lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -192) by (cbn; lia) end; exact U4);
      assert (LCI : LOCI m (Z_to_bv 64 (SRC + (l1 - 2))) (Z_to_bv 64 (SRC + (l1 + l2 - 2))) (Z_to_bv 64 (SRC + (l1 + l2 + l3 - 2))) (Z_to_bv 64 (SRC + (n - 8))) ui)
        by (apply (proj2 (rw_cells_app bsegs _ (SPV + -184) [_; _; _; _] _)); split; [exact LI4|];
            lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -152) by (cbn; lia) end; exact U3);
      assert (LCB : LOCB m b0 b1 b2 b3 ub)
        by (apply (proj2 (rw_cells_app bsegs _ (SPV + -144) [_; _; _; _] _)); split; [exact LB4|];
            lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -112) by (cbn; lia) end; exact U2);
      clear LO4 U4 LI4 U3 LB4 U2 end.
    (* [comment removed for export] *)
    kcleanF.
    lazymatch goal with F' : rw_cells bsegs ?m (SPV + -480) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename F' into FRb end.
    kx_autoFLA FRb (@nil kza) [0x9f6a8] 50%nat
      [KZRange SPV 17594333498016 140737488355328; KZRange dcap 1 4294967296; KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944;
       KZRange DST 4096 140737488355328; KZImg 0x103a8 0x103b0;
       KZWr (SPV + -480) 104; KZDisj (SPV - 480) 104 SRC n; KZDisj (SPV - 480) 104 DT 16388; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 38 4294967296]
      [(SPV + -480, 104); (0x103a8, 8)] [(SPV - 480, 480)].
    all: [> aside ..].
    all: traps.
    all: [> kx_mem ..].
    all: kx_strip_mod.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "F1-LEAF" pc R end.
    all: try match goal with H : rw_cells bsegs ?m (SPV + -480) ?cs |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => idtac "FRS" cs end.
    all: try (lazymatch goal with H : rw_cells bsegs ?m (SPV + -480) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => replace (dcap + DST) with (DST + dcap) in H by (clear; lia) end).
    all: lazymatch goal with SV' : SVS ?m, PC' : stk bsegs ?m lo (SPV + -480) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      eapply (x41_fo (S (Z.to_nat dcap)) m m 0 ((dcap + 3) / 4) (2 * ((dcap + 3) / 4)) (3 * ((dcap + 3) / 4))
                     (l1 - 2) (l1 + l2 - 2) (l1 + l2 + l3 - 2) (n - 8) 6 (6 + l1) (6 + l1 + l2) (6 + l1 + l2 + l3));
      first [ exact (conj SV' PC') | eassumption | apply munch_refl | apply wmono_refl
            | lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => clear - HL1 HL2 HL3 HLN HQ3 DP R1 R2; lia end
            | match goal with |- ?G => idtac "LEFT" G end ] end.
  Qed.
End DX41AM.
End CANSEC1.
