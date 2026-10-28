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
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import ZdHufStats ZdHufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x1t_bpure ADepotKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_x1t_bh1 AF_huf_x1t_bh2 AF_huf_x1t_bh3 AF_huf_x1t_brs AF_huf_x1t_bs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_x1t_bopen AF_huf_x1t_bfk AF_huf_x1t_bwl.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_x1t_bc12 AF_huf_x1t_bc4 AF_huf_x1t_bc8 AF_huf_x1t_bc16c.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
  Section BODY.
  Notation NRS := (18446744073709551615 - (WK + 52)) (only parsing).
  Notation STF mm nbs x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31 :=
    (ST 0x80fa8 mm (Z_to_bv 64 0x80454) x5 x6 (Z_to_bv 64 (WK + 980)) xa0 (Z_to_bv 64 (WK + 52)) xa2 (Z_to_bv 64 NRS) xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  Variable mtl : Z.
  Notation XW := [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] (only parsing).
  Notation SX pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 FF) x19 x20
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition x1_kendX : Prop :=
    forall (hw rank : list Z) (tl : Z) m2 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z)
      (xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    XF m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m2 -> x1pref mtl tl (2 ^ tl) dt ->
    1 <= tl <= mtl + 1 -> tl <= 12 -> zlen hw = 256 -> zlen rank = 13 ->
    evtF bsegs RNG POST (SX 0x80618 m2 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x19 x20 x21 (Z_to_bv 64 r) x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Definition x1_kerrX : Prop :=
    forall m2 (jA jC jD jB jE : list byte) (rv : Z)
      (xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    2 ^ 64 - 119 <= rv < 2 ^ 64 ->
    mem_inv bsegs m2 -> munch XW m5 m2 -> wmono bsegs m5 m2 -> stk bsegs m2 lo SPA ->
    rw_cells bsegs m2 SPA (X1FRA FF DT WK jA jC jD jB jE) ->
    evtF bsegs RNG POST (SX 0x80618 m2 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x19 x20 x21 (Z_to_bv 64 rv) x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Definition x1_fillX : Prop :=
    forall (hw rank : list Z) (nbs tl : Z) m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31 : word),
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 1 <= tl <= 12 -> tl <= mtl + 1 -> 2 <= nbs <= 256 -> zlen hw = 256 -> Forall isbyte hw -> zlen rank = 13 ->
    4 + 2 * 2 ^ tl <= DTB ->
    XB m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl (Z_to_bv 64 (WK + 980)) jA jA2 jC jD jB jE dt rst syb m1 -> x1pref mtl tl 0 dt ->
    evtF bsegs RNG POST (STF m1 nbs x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31).

  Definition x1_bodyA_stmt : Prop :=
    1 <= mtl <= 12 -> 4 + 2 * 2 ^ (mtl + 1) <= DTB -> x1_kendX -> x1_kerrX -> x1_fillX ->
    forall (hw rank : list Z) (nbs tl : Z) (dt : list Z) (fl : Z) (jA jC jD jB jE j3 j5 j6 : list byte)
      (x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 1 <= tl <= 12 -> 2 <= nbs <= 256 -> zlen hw = 256 -> Forall isbyte hw ->
    mem_inv bsegs m5 -> stk bsegs m5 lo SPA ->
    rw_cells bsegs m5 SPA (X1FRA FF DT WK jA jC jD jB jE) ->
    rw_cells bsegs m5 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    u8arr bsegs m5 DT (map (Z_to_bv 8) dt) -> zlen dt = DTB -> Forall isbyte dt -> Znth 0 dt = mtl -> Znth 3 dt = mtl ->
    u8arr bsegs m5 (WK + 1236) (map (Z_to_bv 8) hw) -> u32arr bsegs m5 WK (map (Z_to_bv 64) rank) ->
    stk bsegs m5 (WK + 52) (WK + 1236) -> stk bsegs m5 (WK + 1492) (WK + wksz) ->
    evtF bsegs RNG POST (ST 0x80464 m5 (Z_to_bv 64 0x80454) x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                           (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32))
                           (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31).

  Notation ST3 pc mm dtd mtl tl' nbs xa1 xa2 x5 x6 x7 x28 x29 :=
    (ST pc mm (Z_to_bv 64 0x80454) x5 x6 x7 (Z_to_bv 64 DT) xa1 xa2 (Z_to_bv 64 (2147450880 + DT / 8)) (Z_to_bv 64 (mtl + 1))
        (Z_to_bv 64 (Z.min (mtl + 1) 11)) (Z_to_bv 64 nbs) (Z_to_bv 64 tl')
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).

  Lemma x1b_hdr_c4 : forall m A (dt : list Z) (d : Z), u8arr bsegs m A (map (Z_to_bv 8) dt) -> 4 <= zlen dt -> Forall isbyte dt ->
    Znth 0 dt + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt = d ->
    rw_cells bsegs m A [C4 (Z_to_bv 64 d)] /\ 0 <= d < 2 ^ 32 /\ d mod 256 = Znth 0 dt.
  Proof.
    intros m A dt d H L B E.
    pose proof (Forall_Znth _ dt 0 B ltac:(lia)) as B0. pose proof (Forall_Znth _ dt 1 B ltac:(lia)) as B1.
    pose proof (Forall_Znth _ dt 2 B ltac:(lia)) as B2. pose proof (Forall_Znth _ dt 3 B ltac:(lia)) as B3.
    cbv beta in B0, B1, B2, B3.
    assert (R : 0 <= d < 2 ^ 32) by (subst d; lia).
    split; [| split; [exact R | subst d; Z.div_mod_to_equations; lia]].
    apply AF_huf_x1t_bfk.x1f_u32q_c4; [| exact R].
    destruct dt as [|d0 [|d1 [|d2 [|d3 rr]]]]; cbn [length] in L; try lia.
    replace (u32q d) with [d0; d1; d2; d3].
    - change (d0 :: d1 :: d2 :: d3 :: rr) with ([d0; d1; d2; d3] ++ rr) in H. rewrite map_app in H.
      apply u8arr_app in H. exact (proj1 H).
    - assert (Z0 : Znth 0 (d0 :: d1 :: d2 :: d3 :: rr) = d0) by reflexivity.
      assert (Z1 : Znth 1 (d0 :: d1 :: d2 :: d3 :: rr) = d1) by reflexivity.
      assert (Z2 : Znth 2 (d0 :: d1 :: d2 :: d3 :: rr) = d2) by reflexivity.
      assert (Z3 : Znth 3 (d0 :: d1 :: d2 :: d3 :: rr) = d3) by reflexivity.
      rewrite Z0, Z1, Z2, Z3 in E. rewrite Z0 in B0. rewrite Z1 in B1. rewrite Z2 in B2. rewrite Z3 in B3.
      subst d. unfold u32q.
      f_equal; [| f_equal; [| f_equal; [| f_equal]]]. all: try reflexivity. all: Z.div_mod_to_equations; lia.
  Qed.


  Lemma x1_fillX_ok : x1_kendX -> x1_fillX.
  Proof using HY UDT UW ART0 Hr.
    intros KX. unfold x1_fillX.
    intros hw rank nbs tl m1 dt rst syb jA jA2 jC jD jB jE x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31 STATS TLR TLM NBSR LHW BHW LRK DTBT I PF.
    eapply (AF_huf_x1t_bwl.x1_fillA RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r) with (hw := hw) (rank := rank) (nbs := nbs) (tl := tl) (mtl := mtl).
    all: first [exact HY | exact UDT | exact UW | exact ART0 | exact Hr | exact STATS | exact TLR | exact NBSR | exact LHW | exact BHW | exact LRK
               | exact DTBT | exact I | exact PF
               | (eapply AF_huf_x1t_bc12.x1_c1A; eassumption) | (eapply AF_huf_x1t_bc12.x1_c2A; eassumption)
               | (eapply AF_huf_x1t_bc4.x1_c4A; eassumption) | (eapply AF_huf_x1t_bc8.x1_c8A; eassumption)
               | (eapply AF_huf_x1t_bc16c.x1_cdA; eassumption)
               | (intros; eapply KX; [eassumption | eassumption | lia | lia | exact LHW | exact LRK])].
  Qed.

  Lemma x1_bodyA : x1_bodyA_stmt.
  Proof using HY UDT UW ART0 Hr.
    assert (HSORT : forall (hw rank : list Z) (nbs tl dtd : Z),
      huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 1 <= tl <= 12 -> 2 <= nbs <= 256 -> zlen hw = 256 -> Forall isbyte hw -> zlen rank = 13 ->
      AF_huf_x1t_bs.x1_sortA_stmt RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r POST n SRC flags hw rank nbs tl dtd).
    { intros. eapply AF_huf_x1t_bs.x1_sortA; eassumption. }
    assert (H2 : AF_huf_x1t_bh2.x1_h2A_stmt RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r POST n SRC flags).
    { unfold AF_huf_x1t_bh2.x1_h2A_stmt. intros.
      eapply AF_huf_x1t_bh2.x1_h2A with (hw := hw) (rank := rank) (dt := dt); eassumption. }
    assert (H3 : AF_huf_x1t_bh3.x1_h3aA_stmt RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r POST n SRC flags).
    { unfold AF_huf_x1t_bh3.x1_h3aA_stmt. intros.
      eapply AF_huf_x1t_bh3.x1_h3aA with (hw := hw) (rank := rank) (dt := dt) (rst := rst) (syb := syb); eassumption. }
    unfold x1_bodyA_stmt.
    intros MTLR DTBM KEND KERR FILLX hw rank nbs tl dt fl jA jC jD jB jE j3 j5 j6 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31
      STATS TLR NBSR LHW BHW MI SLO FR FFC DTC0 DTLEN DTBY DTZ0 DTZ3 HWC RK0 WS1 WKR.
    pose proof STATS as (_ & _ & _ & LRK0 & _). unfold FseNCount.Zlength in LRK0.
    assert (POW : 0 < 2 ^ (mtl + 1)) by (apply Z.pow_pos_nonneg; lia).
    pose proof (u32arr_u32b bsegs m5 WK rank RK0) as RK.
    pose (dtd := Znth 0 dt + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt).
    assert (DTDE : Znth 0 dt + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt = dtd) by reflexivity.
    clearbody dtd.
    destruct (x1b_hdr_c4 m5 DT dt dtd DTC0 ltac:(lia) DTBY DTDE) as (DTC4 & DTDR & DTDM). rewrite DTZ0 in DTDM.
    assert (TAIL : forall m1 (hw1 rank1 : list Z) (tl1 : Z) (y5 y6 y7 ya1 ya2 y28 y29 : word),
      huf_stats_ok (firstn (Z.to_nat nbs) hw1) rank1 tl1 -> Z.min (mtl + 1) 11 <= tl1 <= 12 -> zlen hw1 = 256 -> Forall isbyte hw1 ->
      zlen rank1 = 13 -> mem_inv bsegs m1 -> munch XW m5 m1 -> wmono bsegs m5 m1 -> stk bsegs m1 lo SPA ->
      rw_cells bsegs m1 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
      u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
      u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw1) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank1)) ->
      stk bsegs m1 (WK + 52) (WK + 1236) -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
      evtF bsegs RNG POST (ST3 0x80610 m1 dtd mtl tl1 nbs ya1 ya2 y5 y6 y7 y28 y29)).
    { intros m1 hw1 rank1 tl1 y5 y6 y7 ya1 ya2 y28 y29 ST1 TL1 LH1 BH1 LR1 MI1 MU1 WM1 SLO1 FR1 FFC1 DTC1 HWC1 RK1 WS WKR1.
      destruct (stk_split bsegs _ (WK + 52) (WK + 104) (WK + 1236) WS ltac:(lia)) as [WRS WS2].
      destruct (stk_split bsegs _ (WK + 104) (WK + 980) (WK + 1236) WS2 ltac:(lia)) as [SKS WSY].
      AF_huf_x1t_bopen.open_hx HY.
      destruct (u32b_of_stk bsegs m1 (WK + 52) 13%nat
                  ltac:(replace (WK + 52 + 4 * Z.of_nat 13) with (WK + 104) by lia; exact WRS) ltac:(lia) ltac:(lia)) as (rst & RST & RL & RNN).
      destruct (stk_open bsegs m1 (WK + 980) (WK + 1236) (WK + 980) 256%nat WSY ltac:(lia) ltac:(lia)) as (syb & SYC & _ & _).
      assert (SYLEN : zlen syb = 256) by (destruct SYC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; rewrite LJ; reflexivity).
      apply u8arr_of_rw_cells in SYC.
      assert (RNN0 : Forall (fun v : Z => 0 <= v) rst).
      { rewrite Forall_forall in RNN |- *. intros v Hv. specialize (RNN v Hv). cbv beta in RNN. lia. }
      eapply (H3 m1 hw1 rank1 dt rst syb jA jC jD jB jE j3 j5 j6 nbs tl1 tl dtd mtl fl y5 y6 y7 ya1 ya2 y28 y29);
        [lia | exact MTLR | exact NBSR | exact LH1 | exact LR1 | exact DTDR | lia | exact DTC1 | exact DTLEN | exact DTBY | exact DTDE
        | exact DTZ0 | exact DTZ3 | exact HWC1 | exact RK1 | exact RST | rewrite RL; reflexivity | exact RNN0 | exact SKS | exact SYC
        | exact SYLEN | exact WKR1 | exact SLO1 | exact MI1 | exact MU1 | exact WM1 | exact FR1 | exact FFC1 | | ].
      - intros m2 TLX MI2 MU2 WM2 SLO2 FR2 FFC2.
        eapply KERR; [| exact MI2 | exact MU2 | exact WM2 | exact SLO2 | exact FR2].
        change (2 ^ 64) with 18446744073709551616. lia.
      - intros m2 dt2 k176 jA' jA2 jD' jB' za0 za1 za2 za4 za5 TLM I2 PF2 FFC2.
        eapply (AF_huf_x1t_brs.x1_rs0A RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r)
          with (hw := hw1) (rank := rank1) (nbs := nbs) (tl := tl1) (dtd := dtd);
          first [exact HY | exact UDT | exact UW | exact ART0 | exact Hr | exact ST1 | exact NBSR | exact LH1 | exact BH1 | exact LR1 | lia | idtac].
        1: exact I2. 1: exact FFC2.
        intros m3 rs3 v6 I3 RSI3 FFC3.
        eapply (AF_huf_x1t_brs.x1_rsA RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r)
          with (hw := hw1) (rank := rank1) (nbs := nbs) (tl := tl1) (dtd := dtd);
          first [exact HY | exact UDT | exact UW | exact ART0 | exact Hr | exact ST1 | exact NBSR | exact LH1 | exact BH1 | exact LR1 | lia | idtac].
        1: exact I3. 1: exact RSI3. 1: exact FFC3.
        intros m4 rs4 wa0 wa2 wa3 wa4 wa5 w6 w28 w29 I4 RSI4 FFC4.
        eapply (HSORT hw1 rank1 nbs tl1 dtd ST1 ltac:(lia) NBSR LH1 BH1 LR1); [exact I4 | exact RSI4 |].
        intros m6 rs6 syb6 u5 u6 ua0 ua2 ua4 ua5 u28 u29 u30 u31 I6.
        assert (P2 : 2 ^ tl1 <= 2 ^ (mtl + 1)) by (apply Z.pow_le_mono_r; lia).
        eapply (FILLX hw1 rank1 nbs tl1); [exact ST1 | lia | exact TLM | exact NBSR | exact LH1 | exact BH1 | exact LR1 | lia | exact I6 | exact PF2]. }
    eapply (AF_huf_x1t_bh1.x1_h1A RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r)
      with (mtl := mtl) (dtd := dtd) (nbs := nbs) (tl := tl) (fl := fl)
           (jA := jA) (jC := jC) (jD := jD) (jB := jB) (jE := jE) (j3 := j3) (j5 := j5) (j6 := j6);
      first [exact HY | exact UDT | exact UW | exact ART0 | exact Hr | exact MI | exact FR | exact FFC | exact DTC4 | exact DTDR | exact DTDM
            | exact MTLR | exact TLR | exact NBSR | lia | idtac].
    - intros TLG.
      eapply (TAIL m5 hw rank tl); first [exact STATS | lia | exact LHW | exact BHW | exact LRK0 | exact MI | apply munch_refl | apply wmono_refl
        | exact SLO | exact FR | exact FFC | exact DTC0 | exact HWC | exact RK | exact WS1 | exact WKR].
    - intros TLL.
      eapply (H2 m5 hw rank dt nbs tl mtl fl jA jC jD jB jE j3 j5 j6 x5 x6 x7 x28 x29 dtd);
        first [exact STATS | exact MTLR | lia | exact NBSR | exact LHW | exact BHW | exact LRK0 | exact MI | apply munch_refl | apply wmono_refl
          | exact SLO | exact FR | exact FFC | exact DTC0 | exact DTLEN | exact HWC | exact RK | exact WS1 | exact WKR | idtac].
      intros m2 hw' rank' y5 y6 y7 ya1 ya2 y28 y29 ST' LH' BH' LR' MI2 MU2 WM2 SLO2 FR2 FFC2 DTC2 HWC2 RK2 WS2 WKR2.
      eapply (TAIL m2 hw' rank' (Z.min (mtl + 1) 11)); first [exact ST' | lia | exact LH' | exact BH' | exact LR' | exact MI2 | exact MU2
        | exact WM2 | exact SLO2 | exact FR2 | exact FFC2 | exact DTC2 | exact HWC2 | exact RK2 | exact WS2 | exact WKR2].
  Qed.
  End BODY.
End X1B.
End CANSEC1.
