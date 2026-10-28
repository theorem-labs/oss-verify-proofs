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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x1t_bdefs AF_huf_x1t_bpure.

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

  Notation ST4 nbs tl dtd mm xa0 xa1 xa2 xa4 xa5 x6 x7 x28 x29 :=
    (ST 0x80718 mm (Z_to_bv 64 0x80454) (Z_to_bv 64 (nbs - 4)) x6 x7 xa0 xa1 xa2 (Z_to_bv 64 (0x7fff8000 + DT / 8)) xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 tl)
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

  Definition x1_h3aA_stmt : Prop :=
    forall m1 (hw rank dt rst : list Z) (syb jA jC jD jB jE j3 j5 j6 : list byte) (nbs tl tl0 dtd mtl fl : Z)
      (x5 x6 x7 xa1 xa2 x28 x29 : word),
    1 <= tl <= 12 -> 1 <= mtl <= 12 -> 2 <= nbs <= 256 -> zlen hw = 256 -> zlen rank = 13 -> 0 <= dtd < 2^32 -> 4 <= DTB ->
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) -> zlen dt = DTB -> Forall isbyte dt ->
    Znth 0 dt + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt = dtd -> Znth 0 dt = mtl -> Znth 3 dt = mtl ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) -> zlen rst = 13 -> Forall (fun v : Z => 0 <= v) rst ->
    stk bsegs m1 (WK + 104) (WK + 980) -> u8arr bsegs m1 (WK + 980) syb -> zlen syb = 256 -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
    stk bsegs m1 lo SPA -> mem_inv bsegs m1 -> munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
    (forall m2, mtl + 1 < tl -> mem_inv bsegs m2 -> munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m2 -> wmono bsegs m5 m2 -> stk bsegs m2 lo SPA ->
       rw_cells bsegs m2 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (ST3 0x80618 m2 dtd mtl tl nbs xa1 xa2 x5 x6 x7 x28 x29)) ->
    (forall m2 (dt' : list Z) (k176 : word) (jA' jA2 jD' jB' : list byte) (ya0 ya1 ya2 ya4 ya5 : word), tl <= mtl + 1 ->
       XB m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl k176 jA' jA2 jC jD' jB' jE dt' rst syb m2 -> x1pref mtl tl 0 dt' ->
       rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (ST4 nbs tl dtd m2 ya0 ya1 ya2 ya4 ya5 x6 x7 x28 x29)) ->
    evtF bsegs RNG POST (ST3 0x80610 m1 dtd mtl tl nbs xa1 xa2 x5 x6 x7 x28 x29).


  Lemma x1_h3aA : forall m1 (hw rank dt rst : list Z) (syb jA jC jD jB jE j3 j5 j6 : list byte) (nbs tl tl0 dtd mtl fl : Z)
      (x5 x6 x7 xa1 xa2 x28 x29 : word),
    1 <= tl <= 12 -> 1 <= mtl <= 12 -> 2 <= nbs <= 256 -> zlen hw = 256 -> zlen rank = 13 -> 0 <= dtd < 2^32 -> 4 <= DTB ->
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) -> zlen dt = DTB -> Forall isbyte dt ->
    Znth 0 dt + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt = dtd -> Znth 0 dt = mtl -> Znth 3 dt = mtl ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) -> zlen rst = 13 -> Forall (fun v : Z => 0 <= v) rst ->
    stk bsegs m1 (WK + 104) (WK + 980) -> u8arr bsegs m1 (WK + 980) syb -> zlen syb = 256 -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
    stk bsegs m1 lo SPA -> mem_inv bsegs m1 -> munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
    (forall m2, mtl + 1 < tl -> mem_inv bsegs m2 -> munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m2 -> wmono bsegs m5 m2 -> stk bsegs m2 lo SPA ->
       rw_cells bsegs m2 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (ST3 0x80618 m2 dtd mtl tl nbs xa1 xa2 x5 x6 x7 x28 x29)) ->
    (forall m2 (dt' : list Z) (k176 : word) (jA' jA2 jD' jB' : list byte) (ya0 ya1 ya2 ya4 ya5 : word), tl <= mtl + 1 ->
       XB m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl k176 jA' jA2 jC jD' jB' jE dt' rst syb m2 -> x1pref mtl tl 0 dt' ->
       rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (ST4 nbs tl dtd m2 ya0 ya1 ya2 ya4 ya5 x6 x7 x28 x29)) ->
    evtF bsegs RNG POST (ST3 0x80610 m1 dtd mtl tl nbs xa1 xa2 x5 x6 x7 x28 x29).

  Proof.
    intros until x29; intros TLR MTL NBSR LHW LRK DTDR DTB4 DTC DTLEN DTBY HDTD Z0 Z3 HWC RK RST RSTLEN RSTNN STS SYC SYLEN WKR STK MI MU WM FR FFC KE KS.
    pose proof HY as HY0.
    destruct HY0 as (DT1 & DT2 & DT4 & WK1 & WK2 & WK4 & WS & KH & LOA & LOS & SPV1 & SPV16 & SPAB & SPA32 & DSD & WSD & DWD
                    & FF64 & FF1 & FF2 & FFB & DFD & WFD & DTBk & DTR' & DTS & WKB & WKR' & WKS & FFR & LOR & RI).
    pose proof atop_range as ATR.
    assert (LDT : zlen (map (Z_to_bv 8) dt) = DTB) by (rewrite length_map; exact DTLEN).
    assert (LHK : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; exact LHW).
    assert (LRKB : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length2, LRK; reflexivity).
    assert (LRSB : zlen (map (Z_to_bv 8) (u32b rst)) = 52) by (rewrite length_map, u32b_length2, RSTLEN; reflexivity).
    unfold X1FRA in FR. unfold X1FFHDR in FFC.
    zstep.
    assert (UDT1 : unpoisoned m DT (DT + DTB)) by (eapply x1_unp_dtM; eassumption).
    pose proof (unpoisoned_check bsegs m DT (DT + DTB) DT 4 UDT1 ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear - DT4 DT1; Z.div_mod_to_equations; lia)) as (b & SHB & HB).
    assert (RSH : rng RNG (shad DT) 1)
      by (apply (rng_sub' RNG (shad DT) (shspan DT DTB) (shad DT) 1 DTS); unfold shspan; Z.div_mod_to_equations; lia).
    replace (shad DT) with (Z.shiftr DT 3 + 2147450880) in SHB, RSH by (unfold shad, ASHOFF; lia).
    lazymatch type of SHB with rw_cells _ _ (Z.shiftr DT 3 + ?o) _ =>
      replace (Z.shiftr DT 3 + o) with (DT / 8 + o) in SHB, RSH by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia) end.
    zstep.
    if_cases K0.
    2: { kball Z0. apply KE; try assumption; try lia. }
    kball Z0.
    lazymatch type of SHB with rw_cells _ _ (DT / 8 + ?o) _ => setreg 13 (Z_to_bv 64 (DT / 8 + o)) ltac:(f_equal; lia) end.
    zstep. zstep. rewrite sxb_sval. if_cases K1.
    2: destruct HB as [HB0 | (HB1 & HB2)].
    2: { exfalso. rewrite HB0 in K1. cbv in K1. discriminate K1. }
    2: (zstep; zstep; zstep; zstep).
    2: (lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:K2 end).
    2: { exfalso. assert (L7 : Z.land DT 7 = DT mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
         assert (M8 : 0 <= DT mod 8 < 8) by (apply Z.mod_pos_bound; lia).
         unfold bv_lts in K2. rewrite L7 in K2. rewrite !signed_lit in K2 by (clear - M8 HB1; lia).
         apply Bool.negb_true_iff, Z.ltb_ge in K2. clear - K2 HB2. lia. }
    2: zstep.
    all: zstep.
    all: zstep. all: zstep. all: zstep. all: zstep. all: zstep. all: zstep. all: zstep.
    all: pose proof (OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.StrFun.u8arr_store_ok_n bsegs _ DT _ 0 4 (Z_to_bv 64 DT) DTC ltac:(lia) ltac:(change (Z.of_nat 4) with 4; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    all: zstep.
    all: clear SHB RSH.
    all: assert (BL : forall a b k, 0 <= k -> (Z.land a b / 2^k) mod 256 = Z.land ((a / 2^k) mod 256) ((b / 2^k) mod 256))
           by (intros a0 b0 k Hk; rewrite <- !Z.shiftr_div_pow2 by lia; rewrite Z.shiftr_land;
               change 256 with (2^8); rewrite <- !Z.land_ones by lia;
               rewrite <- (Z.land_diag (Z.ones 8)) at 1; rewrite !Z.land_assoc; f_equal; rewrite <- !Z.land_assoc; f_equal; apply Z.land_comm).
    all: assert (BO : forall a b k, 0 <= k -> (Z.lor a b / 2^k) mod 256 = Z.lor ((a / 2^k) mod 256) ((b / 2^k) mod 256))
           by (intros a0 b0 k Hk; rewrite <- !Z.shiftr_div_pow2 by lia; rewrite Z.shiftr_lor;
               change 256 with (2^8); rewrite <- !Z.land_ones by lia; apply Z.land_lor_distr_l).
    all: assert (BY0 : 0 <= Znth 0 dt < 256) by (apply (Forall_Znth _ dt 0 DTBY); lia).
    all: assert (BY1 : 0 <= Znth 1 dt < 256) by (apply (Forall_Znth _ dt 1 DTBY); lia).
    all: assert (BY2 : 0 <= Znth 2 dt < 256) by (apply (Forall_Znth _ dt 2 DTBY); lia).
    all: assert (BY3 : 0 <= Znth 3 dt < 256) by (apply (Forall_Znth _ dt 3 DTBY); lia).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 DT) (le4 (Z_to_bv 64 (Z.lor (Z.land ?D ?M1) (Z.shiftr (Z.land (Z.shiftl ?T 56) ?M2) 40))))) _) =>
      assert (TV : Z.shiftr (Z.land (Z.shiftl tl 56) M2) 40 = tl * 65536)
        by (change M2 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.shiftl_mul_pow2 by lia;
            change (2^56) with 72057594037927936; change (2^64) with 18446744073709551616;
            rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^40) with 1099511627776;
            change 72057594037927936 with (65536 * 1099511627776); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity);
      rewrite TV;
      assert (BY : forall k, 0 <= k -> (Z.lor (Z.land dtd M1) (tl * 65536) / 2^k) mod 256
                     = Z.lor (Z.land ((dtd / 2^k) mod 256) ((M1 / 2^k) mod 256)) ((tl * 65536 / 2^k) mod 256))
        by (intros k Hk; rewrite BO, BL by lia; reflexivity);
      assert (E0 : Z.lor (Z.land dtd M1) (tl * 65536) mod 256 = mtl)
        by (pose proof (BY 0 ltac:(lia)) as H; change (2^0) with 1 in H; rewrite !Z.div_1_r in H; rewrite H;
            replace (M1 mod 256) with 255 by reflexivity;
            replace (dtd mod 256) with mtl by (rewrite <- Z0, <- HDTD; clear - BY0 BY1 BY2 BY3; Z.div_mod_to_equations; lia);
            replace ((tl * 65536) mod 256) with 0 by (clear - TLR; Z.div_mod_to_equations; lia);
            rewrite Z.lor_0_r; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia);
      assert (E1 : (Z.lor (Z.land dtd M1) (tl * 65536) / 256) mod 256 = 0)
        by (pose proof (BY 8 ltac:(lia)) as H; change (2^8) with 256 in H; rewrite H;
            replace ((M1 / 256) mod 256) with 0 by reflexivity; rewrite Z.land_0_r;
            replace ((tl * 65536 / 256) mod 256) with 0 by (clear - TLR; Z.div_mod_to_equations; lia); reflexivity);
      assert (E2 : (Z.lor (Z.land dtd M1) (tl * 65536) / 65536) mod 256 = tl)
        by (pose proof (BY 16 ltac:(lia)) as H; change (2^16) with 65536 in H; rewrite H;
            replace ((M1 / 65536) mod 256) with 0 by reflexivity; rewrite Z.land_0_r;
            replace ((tl * 65536 / 65536) mod 256) with tl by (clear - TLR; Z.div_mod_to_equations; lia); reflexivity);
      assert (E3 : (Z.lor (Z.land dtd M1) (tl * 65536) / 16777216) mod 256 = mtl)
        by (pose proof (BY 24 ltac:(lia)) as H; change (2^24) with 16777216 in H; rewrite H;
            replace ((M1 / 16777216) mod 256) with 255 by reflexivity;
            replace ((dtd / 16777216) mod 256) with mtl by (rewrite <- Z3, <- HDTD; clear - BY0 BY1 BY2 BY3; Z.div_mod_to_equations; lia);
            replace ((tl * 65536 / 16777216) mod 256) with 0 by (clear - TLR; Z.div_mod_to_equations; lia);
            rewrite Z.lor_0_r; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia);
      assert (LE : le4 (Z_to_bv 64 (Z.lor (Z.land dtd M1) (tl * 65536))) = map (Z_to_bv 8) [mtl; 0; tl; mtl])
        by (apply le4_lit_of_mod32; [reflexivity|]; cbn [map le_val]; rewrite !byte_lit by lia;
            revert E0 E1 E2 E3; generalize (Z.lor (Z.land dtd M1) (tl * 65536)); clear - MTL TLR; intros zz E0 E1 E2 E3;
            Z.div_mod_to_equations; lia)
    end.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 DT) ?bs) _) =>
      assert (DTC' : u8arr bsegs (write_to_mem mm (wa DT) bs) DT (map (Z_to_bv 8) ([mtl; 0; tl; mtl] ++ drop 4 dt)))
        by (replace (wa DT) with (wa (DT + 0)) by (unfold wa; f_equal; lia);
            replace (map (Z_to_bv 8) ([mtl; 0; tl; mtl] ++ drop 4 dt)) with (upd_bytes (map (Z_to_bv 8) dt) (Z.to_nat 0) bs)
              by (rewrite LE; unfold upd_bytes; rewrite map_app, skipn_map; reflexivity);
            apply OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.StrFun.u8arr_write_bytes; [exact DTC | lia | rewrite LE, length_map; cbn [length map]; lia]);
      change (write_to_mem mm (Z_to_bv 64 DT) bs) with (write_to_mem mm (wa DT) bs);
      apply (mem_inv_store bsegs mm (wa DT) bs) in MI; [| rewrite LE; exact SOK];
      assert (LB : zlen bs = 4) by (rewrite LE; reflexivity);
      apply (wmono_write bsegs m5 mm (wa DT) bs) in WM;
      apply (munch_write _ m5 mm DT bs) in MU; [| clear - DT1; lia | clear - DT2 LB DTB4; lia | cbn [inside]; clear - DT1 DT2 LB DTB4; lia];
      apply (stk_write bsegs mm _ _ DT bs) in STK; [| clear - DT1; lia | clear - DT2 LB DTB4; lia];
      apply (stk_write bsegs mm _ _ DT bs) in STS; [| clear - DT1; lia | clear - DT2 LB DTB4; lia];
      apply (stk_write bsegs mm _ _ DT bs) in WKR; [| clear - DT1; lia | clear - DT2 LB DTB4; lia];
      apply (u8arr_frame bsegs mm _ _ DT bs) in HWC; [| clear - DT1; lia | clear - DT2 LB DTB4; lia | rewrite LHK; clear - DWD WS LB DTB4; lia];
      apply (u8arr_frame bsegs mm _ _ DT bs) in RK; [| clear - DT1; lia | clear - DT2 LB DTB4; lia | rewrite LRKB; clear - DWD WS LB DTB4; lia];
      apply (u8arr_frame bsegs mm _ _ DT bs) in RST; [| clear - DT1; lia | clear - DT2 LB DTB4; lia | rewrite LRSB; clear - DWD WS LB DTB4; lia];
      apply (u8arr_frame bsegs mm _ _ DT bs) in SYC; [| clear - DT1; lia | clear - DT2 LB DTB4; lia | rewrite SYLEN; clear - DWD WS LB DTB4; lia];
      apply (rw_cells_frame bsegs mm _ _ DT bs) in FR; [| clear - DT1; lia | clear - DT2 LB DTB4; lia | cbn [cells_size csize Nat.add]; clear - DSD LOS SPAB LB DTB4; lia];
      apply (rw_cells_frame bsegs mm _ _ DT bs) in FFC; [| clear - DT1; lia | clear - DT2 LB DTB4; lia | cbn [cells_size csize Nat.add]; clear - DFD LB DTB4; lia];
      clear DTC SOK LDT; rename DTC' into DTC;
      assert (LDT : zlen (map (Z_to_bv 8) ([mtl; 0; tl; mtl] ++ drop 4 dt)) = DTB)
        by (rewrite length_map, length_app, length_drop; cbn [length]; clear - DTLEN DTB4; lia);
      clear BL BO BY E0 E1 E2 E3 TV LE LB;
      let m' := fresh "m" in remember (write_to_mem mm (wa DT) bs) as m' eqn:HM; clear HM;
      try clear mm
    end.
    all: zstep.
    all: lazymatch goal with |- context [bv_swrap 32 (?N + -4)] =>
      replace (bv_swrap 32 (N + -4)) with (N - 4)
        by (clear - NBSR; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with (2^32); change (2 ^ (Z.of_N 32 - 1)) with (2^31);
            rewrite Z.mod_small by lia; lia) end.
    all: if_cases K3.
    2,4: (exfalso; revert K3; unfold bv_lts; rewrite !signed_lit by (clear - NBSR; lia); intro K3; apply Z.ltb_ge in K3; clear - K3 NBSR; lia).
    all: zstep. all: zstep.
    all: assert (SW : bv_swrap 32 (tl + 1) = tl + 1)
           by (clear - TLR; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with (2^32); change (2 ^ (Z.of_N 32 - 1)) with (2^31);
               rewrite Z.mod_small by lia; lia).
    all: rewrite SW in FR |- *.
    all: zstep.
    all: if_cases K4.
    2,4: (exfalso; revert K4; unfold bv_lts; rewrite !signed_lit by (clear - TLR; lia); intro K4; apply Bool.negb_false_iff, Z.ltb_lt in K4; clear - K4; lia).
    all: lazymatch type of FR with rw_cells _ ?mm _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; CB 80 ?j; ?c12; ?c13; ?c14] =>
      apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] 80 j [c12; c13; c14] [72; 8]%nat) in FR; [| reflexivity];
      cbn [mk_CB_cells app] in FR end.
    all: assert (CB8C8 : forall mm A pre j post, rw_cells bsegs mm A (pre ++ CB 8 j :: post) -> exists w, rw_cells bsegs mm A (pre ++ C8 w :: post))
           by (intros mm A pre j post H; apply ABytes.rw_cells_app in H; destruct H as [H1 H2];
               change (CB 8 j :: post) with ([CB 8 j] ++ post) in H2; apply ABytes.rw_cells_app in H2; destruct H2 as [H2 H3];
               destruct (ABytes.c8_of_CB _ _ _ H2) as [w [H4 _]]; exists w; apply ABytes.rw_cells_app; split; [exact H1|];
               change (C8 w :: post) with ([C8 w] ++ post); apply ABytes.rw_cells_app; split; [exact H4 | exact H3]).
    all: lazymatch type of FR with rw_cells _ ?mm _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; CB 8 ?j; ?c12; ?c13; ?c14] =>
      destruct (CB8C8 mm SPA [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] j [c12; c13; c14] FR) as [k176 FR']; clear FR; cbn [app] in FR' end.
    all: lazymatch goal with |- context [Z_to_bv 64 (DT / 8 + ?o)] => setreg 13 (Z_to_bv 64 (o + DT / 8)) ltac:(f_equal; lia) end.
    all: assert (DTLEN' : zlen ([mtl; 0; tl; mtl] ++ drop 4 dt) = DTB) by (rewrite length_app, length_drop; cbn [length]; clear - DTLEN DTB4; lia).
    all: assert (DTBY' : Forall isbyte ([mtl; 0; tl; mtl] ++ drop 4 dt))
           by (apply Forall_app; split; [repeat constructor; lia | apply Forall_drop; exact DTBY]).
    all: eapply KS;
      [ clear - K0; lia
      | unfold XB, X1FRB; repeat (split; [eassumption|]); exact FR'
      | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | intros u Hu; exfalso; clear - Hu; lia]]]]
      | unfold X1FFHDR; exact FFC ].
  Qed.
End X1B.
End CANSEC1.
