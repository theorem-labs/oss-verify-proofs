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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_4e AZ_huf_dx41_1e AZ_huf_dx41_2e AZ_huf_dx41_3e AZ_huf_dx41_c0 AZ_huf_dx41_mb AZ_huf_dx41_m1 AZ_huf_dx41_m0 AZ_huf_dx41_i4 AZ_huf_dx41_i3.
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
  Hypothesis BITINIT : bit_init_stmtA.

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
  Notation x41_ret := (AZ_huf_dx41.x41_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation X41PA := (AZ_huf_dx41_c0.X41PA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV).
  Notation HINV := AZ_huf_dx41_m1.HINV.
  Notation EINVA := (AZ_huf_dx41.EINVA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_einvS := (AZ_huf_dx41_i4.x41_einvS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).
  Notation x41_i3 := (AZ_huf_dx41_i3.x41_i3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX HRL DHI NBOK BITINIT).
  (* [comment removed for export] *)
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.
  (* [comment removed for export] *)
  Ltac err_ret PV1 HER HRB := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    eapply (x41_ret m2 _);
    [ eapply (x41_einvS m2 _);
      [ exact PV1 | eassumption | eassumption | eassumption | eassumption | eassumption
      | tostk (SPV + -480) | tostk (SPV + -376) | tostk (SPV + -224) | tostk (SPV + -184) | tostk (SPV + -144) ]
    | right; split; [exact HER | exact HRB] ] end.
  Ltac fix_a1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  (* [comment removed for export] *)
  Ltac hold_ors := repeat match goal with H : _ \/ _ |- _ => apply x41_held_intro in H end.
  Ltac unhold_ors := repeat match goal with H : x41_held _ |- _ => unfold x41_held in H end.

  (* [comment removed for export] *)
  Lemma x41_i2 : forall mm rest e1 tot dl S1 n1 bs1 b1 o1 S2 n2 bs2 S3 n3 bs3 S4 n4 bs4 (c1 : word) pad1 junk2 junk3 junk4
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w5 w6 w7 : word),
    X41PA mm rest -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    stk bsegs mm lo (SPV + -480) ->
    (FRS mm w0 w1 w2 w3 (Z_to_bv 64 (e1)) w5 w6 w7 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (DST + 2 * e1)) OEND) ->
    (BD1 mm c1 (Z_to_bv 64 b1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8))) ->
    rw_cells bsegs mm (SPV + -144) [CB 40 junk2] ->
    rw_cells bsegs mm (SPV + -184) [CB 40 junk3] ->
    rw_cells bsegs mm (SPV + -224) [CB 40 junk4] ->
    bytes_at bsegs mm S1 bs1 -> zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 0 <= n2 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 0 <= n3 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 0 <= n4 ->
    HINV o1 n1 b1 -> 
    0 <= e1 -> 3 * e1 <= dcap -> dl = tl + 256 * rsv -> S1 = SRC + 6 -> S2 = S1 + n1 -> S3 = S2 + n2 -> S4 = S3 + n3 -> tot = 6 + n1 + n2 + n3 -> n4 = n - tot ->
    evtF bsegs RNG POST (ST 0xa12b4 mm x1 x5 x6 x7 (Z_to_bv 64 (tot)) (Z_to_bv 64 18446744073709551496) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * e1)) (Z_to_bv 64 (n)) (Z_to_bv 64 (S3)) (Z_to_bv 64 (n3)) (Z_to_bv 64 (n2)) (Z_to_bv 64 (S2)) SB (Z_to_bv 64 (dl)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + 3 * e1)) x28 x29 x30 x31).
  Proof using CTX ACTX HRL DHI NBOK BITINIT rc.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mm rest e1 tot dl S1 n1 bs1 b1 o1 S2 n2 bs2 S3 n3 bs3 S4 n4 bs4 c1 pad1 junk2 junk3 junk4
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      w0 w1 w2 w3 w5 w6 w7
      PV MU0 WM0 MI OUT DTB STK FR B1 BJ2 BJ3 BJ4 SB1 BL1 SS1 SE1 LN1 SB2 BL2 SS2 SE2 LN2 SB3 BL3 SS3 SE3 LN3 SB4 BL4 SS4 SE4 LN4 HI1 HE1 HE3 HDL HS1 HS2 HS3 HS4 HTOT HN4.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 480) 480) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (KF : (0 <= n4 <= 4294967296) /\ (4096 <= S4 <= 140737488355328) /\ (0 <= tot <= 4294967296) /\ (4096 <= S3 <= 140737488355328) /\ (0 <= n3 <= 4294967296))
      by (clear - R2 SS4 SE4 LN4 SS3 SE3 LN3 HTOT HN4 LN1 LN2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5).
    (* [comment removed for export] *)
    kx_autoFLA tt (@nil kza) [0xa55d8] 12%nat
      [KZRange n 0 4294967296; KZRange tot 0 4294967296; KZRange (n - tot) 0 4294967296; KZRange n4 0 4294967296; KZRange S3 4096 140737488355328;
       KZRange n3 0 4294967296; KZRange (S3 + n3) 4096 140737488355328; KZRange S4 4096 140737488355328; KZRange SPV 17594333498016 140737488355328]
      (@nil (Z * Z)) [(SPV - 480, 480)].
    all: [> aside ..].
    all: [> kx_mem ..].
    all: try clear KXK KXA KXRD; try clear KXE.
    (* [comment removed for export] *)
    assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
    assert (AZmm : azstk RNG mm lo SPV).
    { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd].
      - eapply azstk_transport; [exact AZS | exact MU0 | exact WM0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - LO; lia].
      - eapply azstk_transport; [exact AZS | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                                | exact WM0 | exact AW0 | clear - LO; lia]. }
    assert (ARTmm : art mm).
    { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd].
      - eapply (art_transportW W0 m0 mm ART MU0 WM0). constructor; [cbn [fst]; pose proof (DHI Hd); unfold dst_hi in *; lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]].
      - eapply (art_transportW [(SPV - 2720, SPV)] m0 mm ART); [| exact WM0 |].
        + eapply munch_drop_empty. replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia). exact MU0.
        + constructor; [cbn [fst]; clear - LO KLO; lia | constructor]. }
    sfacts0 MU0 USRC DSTA AW0 R1 R2.
    assert (AROS : 0 < n2 -> aro RNG mm S2 n2).
    { intros Hn. eapply aro_sub; [split; [exact USRCc | split; [exact RSRC | exact RSRCS]] | exact SS2 | exact LN2 | exact SE2]. }
    assert (RBD : rng RNG (SPV + -144) 40) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (AROB : aro RNG mm (SPV + -144) 40) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | clear; lia | clear; lia | exact RBD]).
    assert (AHB : ahull RNG mm (SPV + -144) 40) by (eapply azstk_ahull; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
    assert (APB : app_blk (SPV + -144) (SPV + -144 + 40)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
    assert (ASTK' : astk RNG lo (SPV + -480)).
    { split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | clear; lia | clear - LO; lia] | exact RI]]. }
    assert (BDA : (SPV + -144) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia).
    assert (NUMS : (4096 <= SPV + -144) /\ (SPV + -144 + 40 < 2^47) /\ (4096 <= S2) /\ (S2 + n2 < 2^47) /\ (n2 < 2^32) /\
                   (SPV + -144 + 40 <= S2 \/ S2 + n2 <= SPV + -144) /\ (lo <= SPV + -480 - 2224) /\ (SPV + -480 < 2^47) /\
                   (SPV + -144 + 40 <= lo \/ SPV + -480 <= SPV + -144) /\ (S2 + n2 <= lo \/ SPV + -480 <= S2))
      by (clear - LO SPB R2 SS2 SE2 LN2 OS2; lia).
    destruct NUMS as (P6 & P7 & P8 & P9 & P10 & P11 & P13 & P14 & P15 & P16).
    destruct PV as (SV & RS).
    clear USRCc AZmm AW0 RBD KF KF1 KF2 KF3 KF4 KF5.
    clear AZS ARC ART USRC UDT UDST RDST RDSTS RDT RDTS RSRC RSRCS.
    hold_ors. unfold x41_held in OS1, OS2, OS3.
    eapply evtF_cut;
      [ eapply (bit_init_g BITINIT RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (SPV + -480) (SPV + -144) S2 n2 lo bs2 junk2);
        [ exact MI | exact BJ2 | exact BDA | exact SB2 | exact BL2 | exact P6 | exact P7 | exact P8 | exact P9 | exact P10 | exact P11
        | exact STK | exact P13 | exact P14 | exact P15 | exact P16 | exact APB | exact AROB | exact AHB | exact AROS | exact ARTmm | exact ASTK' ]
      | clear ARTmm AROS AROB AHB APB ASTK' BDA P6 P7 P8 P9 P10 P11 P13 P14 P15 P16 BJ2 STK;
        unfold bit_init_postA; post_call bsegs mm ].
    unhold_ors. try clear MI.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    (* [comment removed for export] *)
    lazymatch goal with SV' : rw_cells _ m2 (SPV + -104) _, RS' : rw_cells _ m2 (SPV + -336) [CB 112 rest], ST' : stk _ m2 lo (SPV + -480) |- _ =>
      pose proof (conj SV' RS' : X41PA m2 rest) as PV1; rename ST' into STK1; clear SV' RS' end.
    destruct POST as [(HR & HN1 & cont & bc & pad & HB1 & HB2 & BDC) | (HER & HRB & bs & BDC)].
    - (* [comment removed for export] *)
      lazymatch type of HR with ?rr = n2 => subst rr end. unfold bitd_cells in BDC.
      replace (bitd_ptr S2 n2) with (S2 + (bitd_ptr S2 n2 - S2)) in BDC by lia.
      kx_autoFLA tt (@nil kza) [0xa12cc; 0xa3c30] 12%nat
        [KZRange n2 1 4294967296; KZRange SPV 17594333498016 140737488355328] (@nil (Z * Z)) [(SPV - 480, 480)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr DJW RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8; try clear ZS9.
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa12cc) _ _ _ _) =>
             eapply (x41_i3 m2 rest e1 tot dl S1 n1 bs1 b1 o1 S2 n2 bs2 bc (bitd_ptr S2 n2 - S2) S3 n3 bs3 S4 n4 bs4 c1 cont pad1 pad junk3 junk4);
             first [ exact PV1 | eassumption | unfold AZ_huf_dx41_m1.HINV; unfold bitd_ptr; clear - HN1 HB1 HB2; destruct (Z.leb_spec 8 n2); lia | lia ] end.
    - (* [comment removed for export] *)
      lazymatch type of HER with zd_is_error ?rr = true => rename rr into r end.
      assert (HERR : 18446744073709551497 <= r <= 18446744073709551615) by (unfold zd_is_error, ZE_maxCode in HER; apply Z.ltb_lt in HER; clear - HER HRB; lia).
      kx_autoFLA tt (@nil kza) [0xa12cc; 0xa3c30] 12%nat
        [KZRange r 18446744073709551497 18446744073709551615; KZRange SPV 17594333498016 140737488355328] (@nil (Z * Z)) [(SPV - 480, 480)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa3c30) _ _ _ _) => err_ret PV1 HER HRB end.
  Qed.
End DX41AM.
End CANSEC1.
