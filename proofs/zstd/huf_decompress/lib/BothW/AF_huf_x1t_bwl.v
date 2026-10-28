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
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs AF_huf_x1t_bfk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import ZdHufStats ZdHufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x1t_bpure ADepotKit.
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
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Variables (n0 SRC : Z) (flags : word).

  Section WL.
  Variables (hw rank : list Z) (nbs tl mtl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Hypothesis DTBT : 4 + 2 * 2 ^ tl <= DTB.
  Notation XBm := (XB m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Notation XFm := (XF m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Notation XCm := (XC m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).

  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.
  Lemma fill_facts : forall w, 1 <= w <= tl ->
    0 <= Znth w rank <= 256 /\ 0 <= xsym rank w /\ xsym rank w + Znth w rank <= 256 /\ 0 <= xcur rank w /\
    0 <= Znth w rank * hw_cells w /\ xcur rank w + Znth w rank * hw_cells w <= 2^tl /\ 2^tl <= 4096 /\ 1 <= hw_cells w <= 2048.
  Proof.
    intros w Hw. pose proof STATS as (TL0 & _).
    pose proof (rank_small w ltac:(lia)) as CNTR.
    pose proof (xcur_nonneg _ _ _ STATS w ltac:(lia)) as CUR0. pose proof (xsym_nonneg _ _ _ STATS w ltac:(lia)) as SYM0.
    assert (P2TL : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (WSL : FseNCount.Zlength (firstn (Z.to_nat nbs) hw) = nbs) by (unfold FseNCount.Zlength; rewrite length_firstn; lia).
    assert (SYMH : xsym rank w + Znth w rank <= 256).
    { rewrite <- (xsym_step rank w ltac:(lia)). pose proof (xsym_mono _ _ _ STATS (w + 1) 13 ltac:(lia) ltac:(lia)) as X.
      rewrite (xsym_total _ _ _ STATS), WSL in X. lia. }
    assert (LENR : 1 <= hw_cells w <= 2048).
    { split; [unfold hw_cells; destruct (Z.eqb_spec w 0); [lia|]; pose proof (Z.pow_pos_nonneg 2 (w - 1) ltac:(lia) ltac:(lia)); lia | apply hw_cells_bound; lia]. }
    assert (CLB : 0 <= Znth w rank * hw_cells w /\ xcur rank w + Znth w rank * hw_cells w <= 2^tl).
    { rewrite <- (xcur_step rank w ltac:(lia)). pose proof (xcur_mono _ _ _ STATS (w + 1) (tl + 1) ltac:(lia) ltac:(lia)) as X.
      rewrite (xcur_end _ _ _ STATS) in X. split; [nia | lia]. }
    repeat split; lia.
  Qed.

  Notation NRS := (18446744073709551615 - (WK + 52)) (only parsing).
  Notation SF pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation STF mm x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31 :=
    (ST 0x80fa8 mm (Z_to_bv 64 0x80454) x5 x6 (Z_to_bv 64 (WK + 980)) xa0 (Z_to_bv 64 (WK + 52)) xa2 (Z_to_bv 64 NRS) xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n0) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  Notation STW mm w xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x81030 mm xra x5 x6 x7 xa0 (Z_to_bv 64 w) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31).
  Notation STC pc mm nb len xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF pc mm xra x5 x6 x7 xa0 (Z_to_bv 64 nb) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation STL mm len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x81964 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).

  Hypothesis KEND : forall m2 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z)
      (xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    XFm j0 j192 dt rst syb rsacc sym m2 -> x1pref mtl tl (2^tl) dt ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 FF) (Z_to_bv 64 0x7fff8000)
                                  xs4 xs5 (Z_to_bv 64 r) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) xs9 xs10 xs11 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x80618) fc None m2 (seg_rom bsegs)).

  Hypothesis HC1 : AF_huf_x1t_bc12.x1_c1A_stmt RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r POST hw rank tl mtl.
  Hypothesis HC2 : AF_huf_x1t_bc12.x1_c2A_stmt RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r POST hw rank tl mtl.
  Hypothesis HC4 : AF_huf_x1t_bc4.x1_c4A_stmt RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r POST hw rank tl mtl.
  Hypothesis HC8 : AF_huf_x1t_bc8.x1_c8A_stmt RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r POST hw rank tl mtl.
  Hypothesis HCD : AF_huf_x1t_bc16c.x1_cdA_stmt RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r POST hw rank tl mtl.

  Local Ltac sect := first [exact HY| exact UDT| exact UW| exact ART0| exact Hr| exact STATS| exact TLR| exact NBSR| exact LHW| exact BHW| exact LRK| exact KEND| exact DTBT| idtac].

  Lemma x1_wloopA : forall (f : nat) m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym : Z)
      xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31,
    XFm j0 j192 dt rst syb cur sym m1 -> 1 <= w <= tl -> Z.of_nat f = tl + 1 - w -> cur = xcur rank w -> sym = xsym rank w -> x1pref mtl tl cur dt ->
    evtF bsegs RNG POST (STW m1 w xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros I HW HF HC HS PF; [exfalso; lia|].
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    assert (KL : forall len m2 (dt' : list Z) (k112 k120 k128 k136 k144 : word)
                        (yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 : word),
              len = hw_cells w -> XCm j0 j192 dt' rst syb w cur sym (Znth w rank) k112 k120 k128 k136 k144 m2 -> x1pref mtl tl (cur + Znth w rank * len) dt' ->
              evtF bsegs RNG POST (STL m2 len yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31)).
    { intros len m2 dt' k112 k120 k128 k136 k144 yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 HL I2 PF2. subst len.
      (eapply (x1_latchA RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r) with (cnt := Znth w rank) (len := hw_cells w); sect);
        [exact I2| exact HW| lia| lia| lia| lia| exact LENR| lia| lia| |].
      - intro m3; do 14 intro; intros Hw I3. eapply (IH _ j0 j192 dt' rst syb (w + 1)); [exact I3| lia| lia| | |].
        + rewrite (xcur_step rank w) by lia. lia.
        + rewrite (xsym_step rank w) by lia. lia.
        + exact PF2.
      - intro m3; do 15 intro; intros Hw I3.
        (eapply (x1_fdoneA RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r); sect); [exact I3|].
        replace (2^tl) with (cur + Znth w rank * hw_cells w); [exact PF2|].
        rewrite HC, <- (xcur_step rank w) by lia. replace (w + 1) with (tl + 1) by lia. apply (xcur_end _ _ _ STATS). }
    (eapply (x1_wheadA RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r) with (w := w) (cur := cur) (sym := sym); sect);
      [exact I| exact HW| exact HC| exact HS| | | | |].
    - intros until y31; intros W1 I2.
      assert (L1 : hw_cells w = 1) by (subst w; reflexivity).
      (eapply HC1 with (cnt := Znth w rank); sect);
        [exact I2| exact HW| exact HC| exact HS| reflexivity| exact L1| reflexivity| exact PF|].
      intros; eapply (KL 1); [lia| eassumption| first [eassumption| rewrite Z.mul_1_r; eassumption| rewrite Z.mul_1_r in *; eassumption]].
    - intros until y31; intros W2 I2.
      assert (L2 : hw_cells w = 2) by (subst w; reflexivity).
      (eapply HC2 with (cnt := Znth w rank); sect);
        [exact I2| exact HW| exact HC| exact HS| reflexivity| exact L2| reflexivity| exact PF|].
      intros; eapply (KL 2); [lia| eassumption| eassumption].
    - intros until y31; intros W3 I2.
      assert (L4 : hw_cells w = 4) by (subst w; reflexivity).
      (eapply HC4 with (cnt := Znth w rank); sect);
        [exact I2| exact HW| exact HC| exact HS| reflexivity| exact L4| reflexivity| exact PF|].
      intros; eapply (KL 4); [lia| eassumption| eassumption].
    - intros until y31; intros W4 I2.
      assert (L8 : hw_cells w = 8) by (subst w; reflexivity).
      (eapply HC8 with (cnt := Znth w rank); sect);
        [exact I2| exact HW| exact HC| exact HS| reflexivity| exact L8| reflexivity| exact PF|].
      intros; eapply (KL 8); [lia| eassumption| eassumption].
    - intros until len; intros W5 HL I2.
      assert (L16 : len = hw_cells w) by (rewrite HL; unfold hw_cells; destruct (Z.eqb_spec w 0); [lia| reflexivity]).
      (eapply HCD with (cnt := Znth w rank); sect);
        [exact I2| exact HW| exact HC| exact HS| reflexivity| exact W5| exact L16| reflexivity| exact PF|].
      intros; eapply (KL len); [exact L16| eassumption| eassumption].
  Qed.

  Lemma x1_fillA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31,
    XBm (Z_to_bv 64 (WK + 980)) jA jA2 jC jD jB jE dt rst syb m1 -> x1pref mtl tl 0 dt ->
    evtF bsegs RNG POST (STF m1 x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PF.
    (eapply (x1_fsetA RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r); sect); [exact I|].
    intros m2 j0 j192 y5 ya0 ya2 ya3 ya7 I2.
    eapply (x1_wloopA (Z.to_nat tl) m2 j0 j192 dt rst syb 1); [exact I2| lia| lia| | | exact PF].
    - unfold xcur. change (Z.to_nat 1) with 1%nat. cbn [psum]. change (Z.of_nat 0) with 0. unfold hw_cells. rewrite Z.eqb_refl. lia.
    - unfold xsym. change (Z.to_nat 1) with 1%nat. cbn [psum]. change (Z.of_nat 0) with 0. lia.
  Qed.
  End WL.
End X1B.
End CANSEC1.
