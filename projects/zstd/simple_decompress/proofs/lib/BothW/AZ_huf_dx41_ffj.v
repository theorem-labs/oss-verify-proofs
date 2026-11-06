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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2 ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_libc_iface AZ_huf_lbkit AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_c0 AZ_huf_dx41_i4 AZ_huf_dx41_fq AZ_huf_dx41_ffi0 AZ_huf_dx41_ffi1 AZ_huf_dx41_ffi2 AZ_huf_dx41_ffi3 AZ_huf_dx41_ffi4 AZ_huf_dx41_ffi5 AZ_huf_dx41_ffi6 AZ_huf_dx41_ffi7 AZ_huf_dx41_ffi8 AZ_huf_dx41_ffi9.
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
  Notation x41pf_transport := (AZ_huf_dx41_fq.x41pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo).
  Notation x41_fi_0 := (AZ_huf_dx41_ffi0.x41_fi_0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX NBOK TL11).
  Notation x41_fi_1 := (AZ_huf_dx41_ffi1.x41_fi_1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX NBOK TL11).
  Notation x41_fi_2 := (AZ_huf_dx41_ffi2.x41_fi_2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX NBOK TL11).
  Notation x41_fi_3 := (AZ_huf_dx41_ffi3.x41_fi_3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX NBOK TL11).
  Notation x41_fi_4 := (AZ_huf_dx41_ffi4.x41_fi_4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX NBOK TL11).
  Notation x41_fi_5 := (AZ_huf_dx41_ffi5.x41_fi_5 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX ).
  Notation x41_fi_6 := (AZ_huf_dx41_ffi6.x41_fi_6 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX ).
  Notation x41_fi_7 := (AZ_huf_dx41_ffi7.x41_fi_7 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX ).
  Notation x41_fi_8 := (AZ_huf_dx41_ffi8.x41_fi_8 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX ).
  Notation x41_fi_9 := (AZ_huf_dx41_ffi9.x41_fi_9 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX ).
  Lemma x41_fi : forall mb mm R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 (c0 c1 c2 c3 ub uo ui : word) (ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt oew : word)
      (x9 x10 x12 x18 x19 x20 x22 x25 : word) (w0 w1 w2 : word),
    X41PF mm ->
    munch WDF mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) OEND (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) OEND (Z_to_bv 64 (SRC))) -> (ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt (Z_to_bv 64 (SRC)) oew (Z_to_bv 64 (SRC + je0)) (Z_to_bv 64 (SRC + je1)) (Z_to_bv 64 (SRC + je2)) (Z_to_bv 64 (SRC + je3))) ->
    LOCB mm c0 c1 c2 c3 ub -> LOCO mm (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) uo -> LOCI mm (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) ui ->
    bytes_at bsegs mm SRC src ->
    1 <= R -> 7 * R <= i0 -> i0 + 8 <= n -> 7 * R <= i1 -> i1 + 8 <= n -> 7 * R <= i2 -> i2 + 8 <= n -> 7 * R <= i3 -> i3 + 8 <= n ->
    0 <= o0 -> o0 + 5 * R <= dcap -> 0 <= o1 -> o1 + 5 * R <= dcap -> 0 <= o2 -> o2 + 5 * R <= dcap -> 0 <= o3 -> o3 + 5 * R = ol -> ol <= dcap ->
    6 <= je0 <= n -> 6 <= je1 <= n -> 6 <= je2 <= n -> 6 <= je3 <= n -> 0 < dcap -> 9 <= n ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    (forall mm' (d0 d1 d2 d3 : word) (j0 j1 j2 j3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
        X41PF mm' ->
        munch WDF mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w0 w1 w2 (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) OEND (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) OEND (Z_to_bv 64 (SRC))) -> (ARGS mm' ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt (Z_to_bv 64 (SRC)) oew (Z_to_bv 64 (SRC + je0)) (Z_to_bv 64 (SRC + je1)) (Z_to_bv 64 (SRC + je2)) (Z_to_bv 64 (SRC + je3))) ->
        LOCB mm' d0 d1 d2 d3 ub -> LOCO mm' (Z_to_bv 64 (DST + o0 + 5)) (Z_to_bv 64 (DST + o1 + 5)) (Z_to_bv 64 (DST + o2 + 5)) (Z_to_bv 64 (DST + o3 + 5)) uo -> LOCI mm' (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + j1)) (Z_to_bv 64 (SRC + j2)) (Z_to_bv 64 (SRC + j3)) ui ->
        bytes_at bsegs mm' SRC src ->
        i0 - 7 <= j0 <= i0 -> i1 - 7 <= j1 <= i1 -> i2 - 7 <= j2 <= i2 -> i3 - 7 <= j3 <= i3 -> LBW 8 d0 -> LBW 8 d1 -> LBW 8 d2 -> LBW 8 d3 -> 2 <= R ->
        evtF bsegs RNG POST (ST 0x9f740 mm' (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 (18446744073709551592)) (Z_to_bv 64 (2)) (Z_to_bv 64 (3)) (Z_to_bv 64 (DST + ol)) y9 y10 (Z_to_bv 64 (-1 * DT + -5)) y12 (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (SPV + -144)) (Z_to_bv 64 (18446744073709551599)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (18446744073709551591)) y18 y19 y20 (Z_to_bv 64 (67108)) y22 (Z_to_bv 64 (DT + 4)) SB y25 TBLV (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (4)) (Z_to_bv 64 (5)) (Z_to_bv 64 (6)) (Z_to_bv 64 (18446744073709551608)))) ->
    (forall mm' (d0 d1 d2 d3 : word) (j0 j1 j2 j3 : Z) (y8 y9 y10 y12 y18 y19 y20 y22 y25 : word),
        X41PF mm' ->
        munch WDF mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w0 w1 w2 (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) OEND (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) OEND (Z_to_bv 64 (SRC))) -> (ARGS mm' ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt (Z_to_bv 64 (SRC)) oew (Z_to_bv 64 (SRC + je0)) (Z_to_bv 64 (SRC + je1)) (Z_to_bv 64 (SRC + je2)) (Z_to_bv 64 (SRC + je3))) ->
        LOCB mm' d0 d1 d2 d3 ub -> LOCO mm' (Z_to_bv 64 (DST + o0 + 5)) (Z_to_bv 64 (DST + o1 + 5)) (Z_to_bv 64 (DST + o2 + 5)) (Z_to_bv 64 (DST + o3 + 5)) uo -> LOCI mm' (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + j1)) (Z_to_bv 64 (SRC + j2)) (Z_to_bv 64 (SRC + j3)) ui ->
        bytes_at bsegs mm' SRC src ->
        i0 - 7 <= j0 <= i0 -> i1 - 7 <= j1 <= i1 -> i2 - 7 <= j2 <= i2 -> i3 - 7 <= j3 <= i3 -> LBW 8 d0 -> LBW 8 d1 -> LBW 8 d2 -> LBW 8 d3 -> R = 1 ->
        evtF bsegs RNG POST (ST 0x9f6a8 mm' (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 (18446744073709551592)) (Z_to_bv 64 (2)) (Z_to_bv 64 (3)) y8 y9 y10 (Z_to_bv 64 (-1 * DT + -5)) y12 (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (SPV + -144)) (Z_to_bv 64 (18446744073709551599)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (18446744073709551591)) y18 y19 y20 (Z_to_bv 64 (67108)) y22 (Z_to_bv 64 (DT + 4)) SB y25 TBLV (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (4)) (Z_to_bv 64 (5)) (Z_to_bv 64 (6)) (Z_to_bv 64 (18446744073709551608)))) ->
    evtF bsegs RNG POST (ST 0x9f740 mm (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 (18446744073709551592)) (Z_to_bv 64 (2)) (Z_to_bv 64 (3)) (Z_to_bv 64 (DST + ol)) x9 x10 (Z_to_bv 64 (-1 * DT + -5)) x12 (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (SPV + -144)) (Z_to_bv 64 (18446744073709551599)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (18446744073709551591)) x18 x19 x20 (Z_to_bv 64 (67108)) x22 (Z_to_bv 64 (DT + 4)) SB x25 TBLV (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (4)) (Z_to_bv 64 (5)) (Z_to_bv 64 (6)) (Z_to_bv 64 (18446744073709551608))).
  Proof using CTX ACTX NBOK TL11.
    intros mb mm R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 c0 c1 c2 c3 ub uo ui ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt oew
      x9 x10 x12 x18 x19 x20 x22 x25
      w0 w1 w2
      PV MU WM MU0 WM0 MI OUT DTB FR AR LCB LCO LCI SRCB HR HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HOL HJE0 HJE1 HJE2 HJE3 DP N9 HLBc0 HLBc1 HLBc2 HLBc3 KH KO.
    eapply (x41_fi_0 mb mm R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3). all: try exact PV. all: try eassumption.
    (* [comment removed for export] *)
    intros mm1 e10 e11 e12 e13; do 8 (let y := fresh "yy" in intro y);
         intros PV1 MU1 WM1 MU01 WM01 MI1 OUT1 DTB1 FR1 AR1 LCB1 LCO1 LCI1 SRCB1 HL10 HL11 HL12 HL13.
    eapply (x41_fi_1 mb mm1 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 ). all: try exact PV1. all: try eassumption.
    (* [comment removed for export] *)
    intros mm2 e20 e21 e22 e23; do 8 (let y := fresh "yy" in intro y);
         intros PV2 MU2 WM2 MU02 WM02 MI2 OUT2 DTB2 FR2 AR2 LCB2 LCO2 LCI2 SRCB2 HL20 HL21 HL22 HL23.
    eapply (x41_fi_2 mb mm2 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 ). all: try exact PV2. all: try eassumption.
    (* [comment removed for export] *)
    intros mm3 e30 e31 e32 e33; do 8 (let y := fresh "yy" in intro y);
         intros PV3 MU3 WM3 MU03 WM03 MI3 OUT3 DTB3 FR3 AR3 LCB3 LCO3 LCI3 SRCB3 HL30 HL31 HL32 HL33.
    eapply (x41_fi_3 mb mm3 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 ). all: try exact PV3. all: try eassumption.
    (* [comment removed for export] *)
    intros mm4 e40 e41 e42 e43; do 8 (let y := fresh "yy" in intro y);
         intros PV4 MU4 WM4 MU04 WM04 MI4 OUT4 DTB4 FR4 AR4 LCB4 LCO4 LCI4 SRCB4 HL40 HL41 HL42 HL43.
    eapply (x41_fi_4 mb mm4 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 ). all: try exact PV4. all: try eassumption.
    (* [comment removed for export] *)
    intros mm5 e50 e51 e52 e53; do 8 (let y := fresh "yy" in intro y);
         intros PV5 MU5 WM5 MU05 WM05 MI5 OUT5 DTB5 FR5 AR5 LCB5 LCO5 LCI5 SRCB5 HL50 HL51 HL52 HL53.
    eapply (x41_fi_5 mb mm5 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 ). all: try exact PV5. all: try eassumption.
    (* [comment removed for export] *)
    intros mm6 z0 ; do 5 (let y := fresh "yy" in intro y);
         intros PV6 MU6 WM6 MU06 WM06 MI6 OUT6 DTB6 FR6 AR6 LCB6 LCO6 LCI6 SRCB6 HZ0.
    eapply (x41_fi_6 mb mm6 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 ). all: try exact PV6. all: try eassumption.
    (* [comment removed for export] *)
    intros mm7 d0 z1 j0; do 6 (let y := fresh "yy" in intro y);
         intros PV7 MU7 WM7 MU07 WM07 MI7 OUT7 DTB7 FR7 AR7 LCB7 LCO7 LCI7 SRCB7 HJ0 HZ1 HLBd0.
    eapply (x41_fi_7 mb mm7 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 j0). all: try exact PV7. all: try eassumption.
    (* [comment removed for export] *)
    intros mm8 d1 z2 j1; do 6 (let y := fresh "yy" in intro y);
         intros PV8 MU8 WM8 MU08 WM08 MI8 OUT8 DTB8 FR8 AR8 LCB8 LCO8 LCI8 SRCB8 HJ1 HZ2 HLBd1.
    eapply (x41_fi_8 mb mm8 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 j0 j1). all: try exact PV8. all: try eassumption.
    (* [comment removed for export] *)
    intros mm9 d2 z3 j2; do 6 (let y := fresh "yy" in intro y);
         intros PV9 MU9 WM9 MU09 WM09 MI9 OUT9 DTB9 FR9 AR9 LCB9 LCO9 LCI9 SRCB9 HJ2 HZ3 HLBd2.
    eapply (x41_fi_9 mb mm9 R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 j0 j1 j2). all: try exact PV9. all: try eassumption.
    (* [comment removed for export] *)
    - intros mm10 d3 j3; do 8 (let y := fresh "yy" in intro y);
         intros PV10 MU10 WM10 MU010 WM010 MI10 OUT10 DTB10 FR10 AR10 LCB10 LCO10 LCI10 SRCB10 HJ3 HLBd3 HR2.
      eapply (KH mm10 d0 d1 d2 d3 j0 j1 j2 j3). all: try exact PV10. all: try eassumption.
    - intros mm11 d3 j3; do 9 (let y := fresh "yy" in intro y);
         intros PV11 MU11 WM11 MU011 WM011 MI11 OUT11 DTB11 FR11 AR11 LCB11 LCO11 LCI11 SRCB11 HJ3 HLBd3 HR1.
      eapply (KO mm11 d0 d1 d2 d3 j0 j1 j2 j3). all: try exact PV11. all: try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_fij : forall (Rn : nat), forall mb mm R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 (c0 c1 c2 c3 ub uo ui : word) (ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt oew : word)
      (x9 x10 x12 x18 x19 x20 x22 x25 : word) (w0 w1 w2 : word),
    X41PF mm ->
    munch WDF mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) OEND (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) OEND (Z_to_bv 64 (SRC))) -> (ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt (Z_to_bv 64 (SRC)) oew (Z_to_bv 64 (SRC + je0)) (Z_to_bv 64 (SRC + je1)) (Z_to_bv 64 (SRC + je2)) (Z_to_bv 64 (SRC + je3))) ->
    LOCB mm c0 c1 c2 c3 ub -> LOCO mm (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) uo -> LOCI mm (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) ui ->
    bytes_at bsegs mm SRC src ->
    1 <= R -> 7 * R <= i0 -> i0 + 8 <= n -> 7 * R <= i1 -> i1 + 8 <= n -> 7 * R <= i2 -> i2 + 8 <= n -> 7 * R <= i3 -> i3 + 8 <= n ->
    0 <= o0 -> o0 + 5 * R <= dcap -> 0 <= o1 -> o1 + 5 * R <= dcap -> 0 <= o2 -> o2 + 5 * R <= dcap -> 0 <= o3 -> o3 + 5 * R = ol -> ol <= dcap ->
    6 <= je0 <= n -> 6 <= je1 <= n -> 6 <= je2 <= n -> 6 <= je3 <= n -> 0 < dcap -> 9 <= n ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    R <= Z.of_nat Rn ->
    (forall mm' (d0 d1 d2 d3 : word) (p0 p1 p2 p3 q0 q1 q2 q3 : Z) (y8 y9 y10 y12 y18 y19 y20 y22 y25 : word),
        X41PF mm' ->
        munch WDF mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w0 w1 w2 (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) OEND (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) OEND (Z_to_bv 64 (SRC))) -> (ARGS mm' ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt (Z_to_bv 64 (SRC)) oew (Z_to_bv 64 (SRC + je0)) (Z_to_bv 64 (SRC + je1)) (Z_to_bv 64 (SRC + je2)) (Z_to_bv 64 (SRC + je3))) ->
        LOCB mm' d0 d1 d2 d3 ub -> LOCO mm' (Z_to_bv 64 (DST + p0)) (Z_to_bv 64 (DST + p1)) (Z_to_bv 64 (DST + p2)) (Z_to_bv 64 (DST + p3)) uo -> LOCI mm' (Z_to_bv 64 (SRC + q0)) (Z_to_bv 64 (SRC + q1)) (Z_to_bv 64 (SRC + q2)) (Z_to_bv 64 (SRC + q3)) ui ->
        bytes_at bsegs mm' SRC src ->
        p0 = o0 + (ol - o3) -> p1 = o1 + (ol - o3) -> p2 = o2 + (ol - o3) -> p3 = ol -> 0 <= q0 <= i0 -> 0 <= q1 <= i1 -> 0 <= q2 <= i2 -> 0 <= q3 <= i3 -> LBW 8 d0 -> LBW 8 d1 -> LBW 8 d2 -> LBW 8 d3 ->
        evtF bsegs RNG POST (ST 0x9f6a8 mm' (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 (18446744073709551592)) (Z_to_bv 64 (2)) (Z_to_bv 64 (3)) y8 y9 y10 (Z_to_bv 64 (-1 * DT + -5)) y12 (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (SPV + -144)) (Z_to_bv 64 (18446744073709551599)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (18446744073709551591)) y18 y19 y20 (Z_to_bv 64 (67108)) y22 (Z_to_bv 64 (DT + 4)) SB y25 TBLV (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (4)) (Z_to_bv 64 (5)) (Z_to_bv 64 (6)) (Z_to_bv 64 (18446744073709551608)))) ->
    evtF bsegs RNG POST (ST 0x9f740 mm (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 (18446744073709551592)) (Z_to_bv 64 (2)) (Z_to_bv 64 (3)) (Z_to_bv 64 (DST + ol)) x9 x10 (Z_to_bv 64 (-1 * DT + -5)) x12 (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (SPV + -144)) (Z_to_bv 64 (18446744073709551599)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (18446744073709551591)) x18 x19 x20 (Z_to_bv 64 (67108)) x22 (Z_to_bv 64 (DT + 4)) SB x25 TBLV (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (4)) (Z_to_bv 64 (5)) (Z_to_bv 64 (6)) (Z_to_bv 64 (18446744073709551608))).
  Proof using CTX ACTX NBOK TL11.
    induction Rn as [|Rn IH]; intros mb mm R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3 c0 c1 c2 c3 ub uo ui ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt oew
      x9 x10 x12 x18 x19 x20 x22 x25
      w0 w1 w2
      PV MU WM MU0 WM0 MI OUT DTB FR AR LCB LCO LCI SRCB HR HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HOL HJE0 HJE1 HJE2 HJE3 DP N9 HLBc0 HLBc1 HLBc2 HLBc3 HRN KOJ.
    { exfalso. clear - HR HRN. lia. }
    eapply (x41_fi mb mm R ol o0 o1 o2 o3 i0 i1 i2 i3 je0 je1 je2 je3). all: try exact PV. all: try eassumption.
    - (* [comment removed for export] *)
      intros mm10 d0 d1 d2 d3 j0 j1 j2 j3; do 8 (let y := fresh "yy" in intro y);
         intros PV10 MU10 WM10 MU010 WM010 MI10 OUT10 DTB10 FR10 AR10 LCB10 LCO10 LCI10 SRCB10 HJ0 HJ1 HJ2 HJ3 HLBd0 HLBd1 HLBd2 HLBd3 HR2.
      replace (DST + o0 + 5) with (DST + (o0 + 5)) in LCO10 by (clear; lia).
      replace (DST + o1 + 5) with (DST + (o1 + 5)) in LCO10 by (clear; lia).
      replace (DST + o2 + 5) with (DST + (o2 + 5)) in LCO10 by (clear; lia).
      replace (DST + o3 + 5) with (DST + (o3 + 5)) in LCO10 by (clear; lia).
      eapply (IH mb mm10 (R - 1) ol (o0 + 5) (o1 + 5) (o2 + 5) (o3 + 5) j0 j1 j2 j3 je0 je1 je2 je3).
      all: try exact PV10. all: try exact LCO10. all: try eassumption.
      all: try (clear IH KOJ; clear - HR HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HOL HJE0 HJE1 HJE2 HJE3 DP N9 HJ0 HJ1 HJ2 HJ3 HR2 HRN; lia).
      (* [comment removed for export] *)
      intros mm' e0 e1 e2 e3 p0 p1 p2 p3 q0 q1 q2 q3; do 9 (let y := fresh "yy" in intro y);
        intros PV' MU' WM' MU0' WM0' MI' OUT' DTB' FR' AR' LCB' LCO' LCI' SRCB' EP0 EP1 EP2 EP3 GQ0 GQ1 GQ2 GQ3 GL0 GL1 GL2 GL3.
      eapply (KOJ mm' e0 e1 e2 e3 p0 p1 p2 p3 q0 q1 q2 q3). all: try exact PV'. all: try eassumption.
      all: clear IH KOJ; clear - HR HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HOL HJE0 HJE1 HJE2 HJE3 DP N9 HJ0 HJ1 HJ2 HJ3 HR2 HRN EP0 EP1 EP2 EP3 GQ0 GQ1 GQ2 GQ3; lia.
    - (* [comment removed for export] *)
      intros mm11 d0 d1 d2 d3 j0 j1 j2 j3; do 9 (let y := fresh "yy" in intro y);
         intros PV11 MU11 WM11 MU011 WM011 MI11 OUT11 DTB11 FR11 AR11 LCB11 LCO11 LCI11 SRCB11 HJ0 HJ1 HJ2 HJ3 HLBd0 HLBd1 HLBd2 HLBd3 HR1.
      replace (DST + o0 + 5) with (DST + (o0 + 5)) in LCO11 by (clear; lia).
      replace (DST + o1 + 5) with (DST + (o1 + 5)) in LCO11 by (clear; lia).
      replace (DST + o2 + 5) with (DST + (o2 + 5)) in LCO11 by (clear; lia).
      replace (DST + o3 + 5) with (DST + (o3 + 5)) in LCO11 by (clear; lia).
      eapply (KOJ mm11 d0 d1 d2 d3 (o0 + 5) (o1 + 5) (o2 + 5) (o3 + 5) j0 j1 j2 j3). all: try exact PV11. all: try eassumption.
      all: clear IH KOJ; clear - HR HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HOL HJE0 HJE1 HJE2 HJE3 DP N9 HJ0 HJ1 HJ2 HJ3 HR1; lia.
  Qed.
End DX41AM.
End CANSEC1.
