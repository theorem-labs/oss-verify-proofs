(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     AFake_arep FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x1t_bdefs.

Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT DTB WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT DTB WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + DTB).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : artcells m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Variable POST : machine_state -> Prop.

  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (n SRC : Z) (flags : word).
  Notation ST3 pc mm dtd mtl tl' nbs xa1 xa2 x5 x6 x7 x28 x29 :=
    (ST pc mm (Z_to_bv 64 0x80454) x5 x6 x7 (Z_to_bv 64 DT) xa1 xa2 (Z_to_bv 64 (2147450880 + DT / 8)) (Z_to_bv 64 (mtl + 1))
        (Z_to_bv 64 (Z.min (mtl + 1) 11)) (Z_to_bv 64 nbs) (Z_to_bv 64 tl')
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).

  Ltac brk := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let KB := fresh "KB" in destruct c eqn:KB end.
  Ltac wto stops := repeat (lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        let o := eval vm_compute in (p - 0x80298) in
        let b := eval vm_compute in (existsb (Z.eqb o) stops) in lazymatch b with true => fail | false => zstep end
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => brk end).
  Ltac nrm255 DTM :=
    repeat (first
      [ match goal with |- context [?x mod 2^64] => rewrite (Z.mod_small x (2^64)) by lia end
      | match goal with |- context [Z.land ?x 255] =>
          replace (Z.land x 255) with (x mod 256) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity) end
      | rewrite DTM ]).
  Ltac kbz H DTM :=
    rewrite ?AKit.zx32_lit, ?AKit.sx32_lit, ?unsigned_lit in H by lia;
    revert H; nrm255 DTM; intro H; rewrite ?Bool.negb_involutive in H;
    first [ apply Bool.negb_true_iff, Z.ltb_ge in H | apply Bool.negb_false_iff, Z.ltb_lt in H
          | apply Z.ltb_lt in H | apply Z.ltb_ge in H | idtac ].
  Ltac zb := repeat match goal with
    | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
    | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    end.
  Ltac kball DTM := repeat match goal with H : context [bv_ltu] |- _ => revert H | H : context [bv_lts] |- _ => revert H | H : context [Z.ltb] |- _ => revert H end;
    unfold bv_ltu, bv_lts; rewrite ?AKit.zx32_lit, ?AKit.sx32_lit by lia; rewrite ?Z_to_bv_unsigned, ?Z_to_bv_signed;
    unfold bv_wrap, bv_swrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); change (2 ^ (Z.of_N 64 - 1)) with (2^63);
    rewrite ?AKit.zx32_lit, ?AKit.sx32_lit, ?unsigned_lit by lia; nrm255 DTM; intros; zb.
  Ltac rz DTM := rewrite ?AKit.zx32_lit, ?AKit.sx32_lit by lia;
    repeat (first [ rewrite unsigned_lit by lia | progress nrm255 DTM ]).

  Lemma x1_h1A : forall (mtl dtd nbs tl fl : Z) (jA jC jD jB jE j3 j5 j6 : list byte)
      (x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
    mem_inv bsegs m5 ->
    rw_cells bsegs m5 SPA (X1FRA FF DT WK jA jC jD jB jE) ->
    rw_cells bsegs m5 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    rw_cells bsegs m5 DT [C4 (Z_to_bv 64 dtd)] -> 0 <= dtd < 2^32 -> dtd mod 256 = mtl -> 4 <= DTB ->
    1 <= mtl <= 12 -> 1 <= tl <= 12 -> 2 <= nbs <= 256 ->
    (Z.min (mtl + 1) 11 <= tl ->
       evtF bsegs RNG POST (ST3 0x80610 m5 dtd mtl tl nbs (Z_to_bv 64 mtl) (Z_to_bv 64 nbs) x5 x6 x7 x28 x29)) ->
    (tl < Z.min (mtl + 1) 11 ->
       evtF bsegs RNG POST (ST3 0x804bc m5 dtd mtl tl nbs (Z_to_bv 64 mtl) (Z_to_bv 64 nbs) x5 x6 x7 x28 x29)) ->
    evtF bsegs RNG POST (ST 0x80464 m5 (Z_to_bv 64 0x80454) x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                           (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32))
                           (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31).
  Proof.
    intros until x31; intros MI FR FFC DTC DTR DTM DTB4 MTL TLR NBSR K888 K548.
    destruct HY as (DT1 & DT2 & DT4 & WK1 & WK2 & WK4 & WS & KH & LOA & LOS & SPV1 & SPV16 & SPAB & SPA32 & DSD & WSD & DWD
                    & FF64 & FF1 & FF2 & FFB & DFD & WFD & DTBk & DTR' & DTS & WKB & WKR & WKS & FFR & LOR & RI).
    pose proof atop_range as ATR.
    pose proof (unpoisoned_check bsegs m5 DT (DT + DTB) DT 4 UDT ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear - DT4 DT1; Z.div_mod_to_equations; lia)) as (b & SHB & HB).
    assert (RSH : rng RNG (shad DT) 1)
      by (apply (rng_sub' RNG (shad DT) (shspan DT DTB) (shad DT) 1 DTS); unfold shspan; Z.div_mod_to_equations; lia).
    replace (shad DT) with (Z.shiftr DT 3 + 2147450880) in SHB, RSH by (unfold shad, ASHOFF; lia).
    unfold X1FRA in FR. unfold X1FFHDR in FFC.
    apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 X1_MAGIC_LIVE); C8 (Z_to_bv 64 X1_DESC); C8 (Z_to_bv 64 0x80298)] 8 j3
             [C4 (Z_to_bv 64 tl); CB 12 j5; C4 (Z_to_bv 64 nbs); CB 4 j6; C8 (Z_to_bv 64 fl)] [8]%nat) in FFC; [| reflexivity].
    cbn [mk_CB_cells app] in FFC.
    zstep. zstep. zstep.
    if_cases K0.
    2: { exfalso; apply Z.eqb_neq in K0; apply K0; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4; rewrite DT4; reflexivity. }
    clear K0. zstep. zstep. zstep. zstep.
    zstep. rewrite sxb_sval. if_cases K1.
    2: destruct HB as [HB0 | (HB1 & HB2)].
    2: { exfalso. rewrite HB0 in K1. cbv in K1. discriminate K1. }
    2: (zstep; zstep; zstep; zstep).

    2: (lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:K2 end).
    2: { exfalso. assert (L7 : Z.land DT 7 = DT mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
         assert (M8 : 0 <= DT mod 8 < 8) by (apply Z.mod_pos_bound; lia).
         unfold bv_lts in K2. rewrite L7 in K2. rewrite !signed_lit in K2 by (clear - M8 HB1; lia).
         apply Bool.negb_true_iff, Z.ltb_ge in K2. clear - K2 HB2. lia. }
    2: zstep.
    all: zstep. all: zstep. all: zstep. all: zstep. all: zstep.
    assert (LM : Z.land dtd 255 = mtl) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; exact DTM).
    all: rewrite ?LM.
    all: zstep. all: wto [548; 888].

    all: try clear K1.
    all: kball DTM.
    all: first [ setreg 11 (Z_to_bv 64 mtl) ltac:(rz DTM; reflexivity) | idtac "HFAIL" 11 ].
    all: first [ setreg 12 (Z_to_bv 64 nbs) ltac:(rz DTM; reflexivity) | idtac "HFAIL" 12 ].
    all: first [ setreg 13 (Z_to_bv 64 (2147450880 + DT / 8)) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia) | idtac "HFAIL" 13 ].
    all: first [ setreg 14 (Z_to_bv 64 (mtl + 1)) ltac:(rz DTM; reflexivity) | idtac "HFAIL" 14 ].
    all: first [ setreg 16 (Z_to_bv 64 nbs) ltac:(rz DTM; f_equal; rewrite ?Z.add_0_r; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with (2^32); change (2 ^ (Z.of_N 32 - 1)) with (2^31); rewrite Z.mod_small by (clear - NBSR; lia); clear - NBSR; lia) | idtac "HFAIL" 16 ].
    all: first [ setreg 30 (Z_to_bv 64 dtd) ltac:(rz DTM; reflexivity) | idtac "HFAIL" 30 ].
    all: first [ rewrite (Z.min_l (mtl + 1) 11) in K888, K548 by lia | rewrite (Z.min_r (mtl + 1) 11) in K888, K548 by lia ].
    all: setreg 17 (Z_to_bv 64 tl) ltac:(rewrite ?AKit.sx32_lit by lia; first [reflexivity | f_equal; lia]).
    all: lazymatch goal with |- evtF _ _ _ ?S =>
           first [ lazymatch type of K888 with _ -> evtF _ _ _ ?S2 =>
                     replace S with S2 by (cbv [mkR]; repeat f_equal; first [reflexivity | lia]); apply K888; lia end
                 | lazymatch type of K548 with _ -> evtF _ _ _ ?S2 =>
                     replace S with S2 by (cbv [mkR]; repeat f_equal; first [reflexivity | lia]); apply K548; lia end ] end.

  Qed.
End X1B.
End CANSEC1.
