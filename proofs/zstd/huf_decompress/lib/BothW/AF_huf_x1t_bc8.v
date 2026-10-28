(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import ZdHufStats ZdHufX1.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     AFake_arep FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs AF_huf_x1t_bfk AF_huf_x1t_bpure ADepotKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
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
  Section C8.
  Variables (hw rank : list Z) (nbs tl mtl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
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
  Notation SF pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation STC pc mm nb len xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF pc mm xra x5 x6 x7 xa0 (Z_to_bv 64 nb) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation STL mm len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x81964 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation ST8 mm nb sym cur cnt u xra x5 x6 xa1 xa2 xa5 xs2 xs4 xs5 xs10 xs11 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 (Z_to_bv 64 (DT + 2 * cur)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             (Z_to_bv 64 (16 * (256 - sym))) xa1 xa2 (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (sym + u)) xa5 (Z_to_bv 64 (cur + 8 * u)) (Z_to_bv 64 nb)
             xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5 (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 8) xs10 xs11
             (Z_to_bv 64 (16 * cnt)) x29 x30 x31)
        F (Z_to_bv 64 0x81294) fc None mm (seg_rom bsegs)).

  Definition x1_c8_bodyA_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb u : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 x6 xa1 xa2 xa5 xs2 xs4 xs5 xs10 xs11 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 8 ->
    nb = tl + 1 - w -> 0 <= u < cnt -> x1pref mtl tl (cur + 8 * u) dt ->
    (forall m2 (dt' : list Z) (y5 y6 ya1 ya2 ya5 ys2 ys4 ys5 ys10 y29 y30 y31 : word), u + 1 < cnt -> XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 -> x1pref mtl tl (cur + 8 * (u + 1)) dt' ->
       evtF bsegs RNG POST (ST8 m2 nb sym cur cnt (u + 1) xra y5 y6 ya1 ya2 ya5 ys2 ys4 ys5 ys10 xs11 y29 y30 y31)) ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 y28 y29 y30 y31 : word), u + 1 = cnt -> XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 8) dt' ->
       evtF bsegs RNG POST (STL m2 8 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST8 m1 nb sym cur cnt u xra x5 x6 xa1 xa2 xa5 xs2 xs4 xs5 xs10 xs11 x29 x30 x31).
  Definition x1_c8_loopA_stmt : Prop := forall (f : nat) m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb u : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 x6 xa1 xa2 xa5 xs2 xs4 xs5 xs10 xs11 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 8 ->
    nb = tl + 1 - w -> 0 <= u -> u + Z.of_nat (S f) = cnt -> x1pref mtl tl (cur + 8 * u) dt ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 y28 y29 y30 y31 : word), XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 8) dt' ->
       evtF bsegs RNG POST (STL m2 8 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST8 m1 nb sym cur cnt u xra x5 x6 xa1 xa2 xa5 xs2 xs4 xs5 xs10 xs11 x29 x30 x31).
  Lemma x1_c8_loopA_of : x1_c8_bodyA_stmt -> x1_c8_loopA_stmt.
  Proof.
    intros BODY f. induction f as [|f IH]; intros until x31; intros I HW HC HS HCN HL8 HNB HS0 HF PF KE.
    - eapply (BODY m1 j0 j192 dt rst syb w cur sym cnt nb u); [exact I| exact HW| exact HC| exact HS| exact HCN| exact HL8| exact HNB| lia| exact PF| intros; exfalso; lia|].
      intros m2 dt' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 y28 y29 y30 y31 _ I2 PF2. eapply KE; [exact I2| exact PF2].
    - eapply (BODY m1 j0 j192 dt rst syb w cur sym cnt nb u); [exact I| exact HW| exact HC| exact HS| exact HCN| exact HL8| exact HNB| lia| exact PF| | intros; exfalso; lia].
      intros m2 dt' y5 y6 ya1 ya2 ya5 ys2 ys4 ys5 ys10 y29 y30 y31 Hu I2 PF2.
      eapply (IH m2 j0 j192 dt' rst syb w cur sym cnt nb (u + 1)); [exact I2| exact HW| exact HC| exact HS| exact HCN| exact HL8| exact HNB| lia| lia| exact PF2| exact KE].
  Qed.
  Definition x1_c8A_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 8 ->
    nb = tl + 1 - w -> x1pref mtl tl cur dt ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 y28 y29 y30 y31 : word), XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 8) dt' ->
       evtF bsegs RNG POST (STL m2 8 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STC 0x81248 m1 nb 8 xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Lemma c8_u32b_len : forall ws, length (u32b ws) = (4 * length ws)%nat.
  Proof. intros ws; induction ws as [|x t IH]; [reflexivity|]. simpl. rewrite IH. lia. Qed.
  Lemma c8_sok : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt : Z) (k112 k120 k128 k136 k144 : word) i,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 0 <= i < DTB ->
    store_ok bsegs m1 (wa (DT + i)) 1 = true.
  Proof.
    intros until i. intros I Hi. open_xc I.
    apply (u8arr_store_ok bsegs m1 DT (map (Z_to_bv 8) dt) i); [exact DTC| rewrite length_map; lia| reflexivity].
  Qed.
  Lemma c8_sb : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt : Z) (k112 k120 k128 k136 k144 : word) i x v,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 0 <= i < DTB -> x mod 256 = v -> 0 <= v < 256 ->
    XCm j0 j192 (Zupd i v dt) rst syb w cur sym cnt k112 k120 k128 k136 k144 (write_to_mem m1 (wa (DT + i)) (le1 (Z_to_bv 64 x))).
  Proof.
    intros until v. intros I Hi Hx0 Hv.
    assert (Hx : x mod 256 = v mod 256) by (rewrite Hx0; symmetry; apply Z.mod_small; exact Hv).
    pose proof (c8_sok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i I Hi) as SOK.
    pose proof HY as H0. unfold x1A_hyps in H0.
    destruct H0 as (D1 & D2 & D3 & W1h & W2h & W3h & WKS & KHL & ALO & LOS & SPH & SP16 & SPAR & SPA32 & DSP & WSP & DWK & F64 & F4K & FAT
                    & FBL & DFF & WFF & DBL & RDT & RSD & WBL & RWK & RSW & RFF & RLO & RAI).
    open_xc I.
    assert (L1 : length (le1 (Z_to_bv 64 x)) = 1%nat) by reflexivity.
    assert (SDA : DT + DTB <= SPA \/ SPA + 216 <= DT) by (clear - DSP LOS SPAR; lia).
    assert (WDA : DT + DTB <= WK \/ WK + wksz <= DT) by exact DWK.
    clear DSP WSP DFF WFF DWK.
    unfold XC, X1FR1, X1FR4.
    split; [exact DTF|].
    split; [apply u8arr_sb; [exact DTC| lia| exact Hx]|].
    split; [rewrite Zupd_length2; exact DTLEN|].
    split; [apply Forall_Zupd; [exact DTBY| hnf; lia]|].
    split; [apply u8arr_frame; [exact HWC| lia| rewrite L1; lia| rewrite L1, length_map; clear - WDA WKS Hi LHW; lia]|].
    split; [apply u8arr_frame; [exact RK| lia| rewrite L1; lia| rewrite L1, length_map, c8_u32b_len; clear - WDA WKS Hi LRK; lia]|].
    split; [apply u8arr_frame; [exact RST| lia| rewrite L1; lia| rewrite L1, length_map, c8_u32b_len; clear - WDA WKS Hi RSTLEN; lia]|].
    split; [exact RSTLEN|].
    split; [apply stk_write; [exact STS| lia| rewrite L1; lia]|].
    split; [apply u8arr_frame; [exact SYC| lia| rewrite L1; lia| rewrite L1; clear - WDA WKS Hi SYLEN; lia]|].
    split; [exact SYLEN|].
    split; [apply stk_write; [exact WKR| lia| rewrite L1; lia]|].
    split; [apply stk_write; [exact STK| lia| rewrite L1; lia]|].
    split; [apply mem_inv_store; [exact MI| rewrite L1; exact SOK]|].
    split; [apply munch_write; [exact MU| lia| rewrite L1; lia| cbn [inside]; rewrite L1; lia]|].
    split; [apply wmono_write; exact WM|].
    split; [apply rw_cells_frame; [exact FR1| lia| rewrite L1; lia| rewrite L1; cbn; clear - SDA Hi; lia]|].
    split; [apply rw_cells_frame; [exact FR2| lia| rewrite L1; lia| rewrite L1; cbn; clear - SDA Hi; lia]|].
    apply rw_cells_frame; [exact FR4| lia| rewrite L1; lia| rewrite L1; cbn; clear - SDA Hi; lia].
  Qed.
  Local Ltac zltb :=
    repeat match goal with
    | |- context [?a <? ?b] =>
        first [ replace (a <? b) with false
                  by (symmetry; apply Z.ltb_ge; try change 9223372036854775808 with (2^63); rewrite ?zb_lxor_pow2_small by lia; lia)
              | replace (a <? b) with true
                  by (symmetry; apply Z.ltb_lt; try change 9223372036854775808 with (2^63); rewrite ?zb_lxor_pow2_small by lia; lia) ]
    end; cbn [Z.b2z Z.lxor].
  Local Ltac ck K := zstep; try (zltb);
    try ((bcase K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|])).
  Local Ltac c8_bok D := first [ exact D | rewrite Z.shiftr_div_pow2 by lia; exact D ].
  Local Ltac c8_st I i v D :=
    let a := cur_mem_addr in
    pose proof (c8_sok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i I ltac:(lia)) as SOK;
    replace (wa (DT + i)) with a in SOK by (unfold wa; f_equal; lia);
    zstep; clear SOK;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a' (le1 (Z_to_bv 64 ?x))) _) =>
      let I' := fresh "I" in
      pose proof (c8_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i x v I ltac:(lia) ltac:(c8_bok D) ltac:(lia)) as I';
      replace (wa (DT + i)) with a' in I' by (unfold wa; f_equal; lia); clear I; rename I' into I
    end.
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
  Local Ltac c8_bad K S CK SR a :=
    exfalso; clear - K S CK SR;
    assert (LA : Z.land a 7 = a mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity);
    rewrite LA in S; rewrite !signed_lit_small64 in S by lia; lia.
  Lemma x1_c8_bodyA : x1_c8_bodyA_stmt.
  Proof.
    intros m1 j0 j192 dt rst syb w cur sym cnt nb u k112 k120 k128 k136 k144 xra x5 x6 xa1 xa2 xa5 xs2 xs4 xs5 xs10 xs11 x29 x30 x31
      I HW HC HS HCN HL8 HNB HSR PF KH KE.
    (pose proof I as I0; open_xc I).
    (pose proof HY as H0; unfold x1A_hyps in H0;
      destruct H0 as (D1 & D2 & D3 & W1h & W2h & W3h & WKS & KHL & ALO & LOS & SPH & SP16 & SPAR & SPA32 & DSP & WSP & DWK & F64 & F4K & FAT
                      & FBL & DFF & WFF & DBL & RDT & RSD & WBL & RWK & RSW & RFF & RLO & RAI)).
    (pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR); rewrite HL8 in CL0, CLH).
    (rewrite <- HC, <- HS, <- HCN in *).
    ck K0. ck K1. ck K2. ck K3. ck K4. ck K5. ck K6.
    (assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption)).
    (assert (UD1 : unpoisoned m1 DT (DT + DTB)) by (eapply x1_unp_dtM; eassumption)).
    (destruct (chkB m1 WK (WK + wksz) (WK + 980 + (sym + u)) UW1 ltac:(lia) ltac:(lia)) as (b1 & RB1 & CK1 & SR1)).
    (assert (RS1 : rng RNG (Z.shiftr (WK + 980 + (sym + u)) 3 + ASHOFF) 1);
      [apply (rng_sub' _ _ _ _ _ RSW); rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold shspan;
       clear - WKS W1h W2h SYM0 SYMH HSR; Z.div_mod_to_equations; lia|]; unfold ASHOFF in RS1).
    (clear DSP WSP DWK DFF WFF).
    assert (JOIN1 : forall y12 y15 : word,
      evtF bsegs RNG POST (SF (0x80298 + 4128) m1 xra x5 x6 (Z_to_bv 64 (DT + 2 * cur)) (Z_to_bv 64 (16 * (256 - sym)))
        (Z_to_bv 64 (WK + 980 + (sym + u))) y12 (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (sym + u)) y15 (Z_to_bv 64 (cur + 8 * u)) (Z_to_bv 64 nb)
        xs2 xs4 xs5 (Z_to_bv 64 8) xs10 xs11 (Z_to_bv 64 (16 * cnt)) x29 x30 x31)).
    2: {
    zstep. rewrite sxb_sval.
    zstep.
    bcase KB1.
    - zstep. zstep. bcase KS1.
      + (apply JOIN1).
      + c8_bad KB1 KS1 CK1 SR1 (WK + 980 + (sym + u)).
    - (apply JOIN1). }
    intros y12 y15. clear RB1 CK1 SR1 RS1 b1.
    ck K7. ck K8. ck K9. ck K10. ck K11. ck K12. ck K13. ck K14. ck K15.
    zstep. zstep.
    (assert (B2 : DT + 2 * cur + 16 * u + 4 + 1 <= DT + DTB) by lia;
      assert (B3 : DT + 2 * cur + 16 * u + 19 + 1 <= DT + DTB) by lia).
    (destruct (chkB m1 DT (DT + DTB) (DT + 2 * cur + 16 * u + 4) UD1 ltac:(lia) B2) as (b2 & RB2 & CK2 & SR2)).
    (assert (RS2 : rng RNG (Z.shiftr (DT + 2 * cur + 16 * u + 4) 3 + ASHOFF) 1);
      [apply (rng_sub' _ _ _ _ _ RSD); rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold shspan;
       clear - B2 D1 D2 CUR0 HSR; Z.div_mod_to_equations; lia|]; unfold ASHOFF in RS2).
    destruct (nth_error syb (Z.to_nat (sym + u))) as [sb|] eqn:NSB.
    2: { exfalso. apply nth_error_None in NSB. lia. }
    (pose proof (u8arr_read bsegs m1 (WK + 980) syb (sym + u) sb _ SYC NSB ltac:(lia) eq_refl) as RSY; unfold wa in RSY).
    (assert (RS3 : rng RNG (WK + 980 + (sym + u)) 1) by (apply (rng_sub' _ _ _ _ _ RWK); lia)).
    zstep. rewrite sxb_sval.
    zstep.
    assert (SVR : 0 <= bv_unsigned sb < 256) by (pose proof (bv_unsigned_in_range 8 sb) as R; unfold bv_modulus in R; exact R).
    assert (JOIN2 : forall y5 y12 : word,
      evtF bsegs RNG POST (SF (0x80298 + 4184) m1 xra y5 (Z_to_bv 64 (DT + 2 * cur + 16 * u)) (Z_to_bv 64 (DT + 2 * cur)) (Z_to_bv 64 (16 * (256 - sym)))
        (Z_to_bv 64 (bv_unsigned sb)) y12 (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (sym + u)) (Z_to_bv 64 (DT + 2 * cur + 16 * u + 4))
        (Z_to_bv 64 (cur + 8 * u)) (Z_to_bv 64 nb) xs2 xs4 xs5 (Z_to_bv 64 8) xs10 xs11 (Z_to_bv 64 (16 * cnt)) x29 x30 x31)).
    2: {
    zstep.
    bcase KB2.
    - zstep. zstep. bcase KS2.
      + (apply JOIN2).
      + c8_bad KB2 KS2 CK2 SR2 (DT + 2 * cur + 16 * u + 4).
    - (apply JOIN2). }
    clear y12 y15. intros y5 y12. clear RB2 CK2 SR2 RS2 b2 RSY RS3.
    (destruct (chkB m1 DT (DT + DTB) (DT + 2 * cur + 16 * u + 11) UD1 ltac:(lia) ltac:(lia)) as (b3 & RB3 & CK3 & SR3)).
    (assert (RS4 : rng RNG (Z.shiftr (DT + 2 * cur + 16 * u + 11) 3 + ASHOFF) 1);
      [apply (rng_sub' _ _ _ _ _ RSD); rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold shspan;
       clear - B3 D1 D2 CUR0 HSR; Z.div_mod_to_equations; lia|]; unfold ASHOFF in RS4).
    assert (JOIN3 : forall y5 y29 : word,
      evtF bsegs RNG POST (SF (0x80298 + 4204) m1 xra y5 (Z_to_bv 64 (DT + 2 * cur + 16 * u)) (Z_to_bv 64 (DT + 2 * cur)) (Z_to_bv 64 (16 * (256 - sym)))
        (Z_to_bv 64 (bv_unsigned sb)) (Z_to_bv 64 (DT + 2 * cur + 16 * u + 11)) (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (sym + u)) (Z_to_bv 64 (DT + 2 * cur + 16 * u + 4))
        (Z_to_bv 64 (cur + 8 * u)) (Z_to_bv 64 nb) xs2 xs4 xs5 (Z_to_bv 64 8) xs10 xs11 (Z_to_bv 64 (16 * cnt)) y29 x30 x31)).
    2: {
    zstep. zstep. zstep.
    zstep. rewrite sxb_sval.
    zstep.
    bcase KB3.
    - zstep. zstep. bcase KS3.
      + (apply JOIN3).
      + c8_bad KB3 KS3 CK3 SR3 (DT + 2 * cur + 16 * u + 11).
    - (apply JOIN3). }
    clear y5 y12. intros y5 y29. clear RB3 CK3 SR3 RS4 b3.
    zstep. zstep. zstep. zstep.
    (pose proof (d4k_bytes (bv_unsigned sb) nb ltac:(lia) ltac:(lia)) as (D4M & D40 & D41 & D42 & D43 & D44 & D45 & D46 & D47)).
    (assert (D4R : 0 <= d4k (bv_unsigned sb) nb < 2^64) by (rewrite <- D4M; apply Z.mod_pos_bound; lia)).
    (assert (NBR : 1 <= nb <= 12) by (clear - HNB HW TLR; lia)).
    (lazymatch goal with |- context [Z.lor (Z.land (Z.shiftl (bv_unsigned sb) 8) ?M) nb * ?K] =>
      assert (EQ : Z.lor (Z.land (Z.shiftl (bv_unsigned sb) 8) M) nb * K = d4k (bv_unsigned sb) nb);
      [ replace M with (Z.ones 64) by reflexivity; rewrite Z.land_ones by lia;
        rewrite Z.mod_small by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; clear - SVR; lia);
        rewrite Z.lor_comm, lor_shiftl8_add by (clear - SVR NBR; lia); unfold d4k; ring
      | rewrite EQ; clear EQ ]
    end).
    zstep. zstep. zstep. zstep.
    zstep. zstep. zstep.
    (assert (RS5 : rng RNG (DT + 4 + 2 * cur + 16 * u) 16) by (apply (rng_sub' _ _ _ _ _ RDT); lia)).
    c8_st I0 (4 + 2 * (cur + 8 * u + 2)) nb D44.
    c8_st I0 (4 + 2 * (cur + 8 * u + 2) + 1) (bv_unsigned sb) D45.
    c8_st I0 (4 + 2 * (cur + 8 * u + 3)) nb D46.
    c8_st I0 (4 + 2 * (cur + 8 * u + 3) + 1) (bv_unsigned sb) D47.
    c8_st I0 (4 + 2 * (cur + 8 * u + 0)) nb D40.
    c8_st I0 (4 + 2 * (cur + 8 * u + 0) + 1) (bv_unsigned sb) D41.
    c8_st I0 (4 + 2 * (cur + 8 * u + 1)) nb D42.
    c8_st I0 (4 + 2 * (cur + 8 * u + 1) + 1) (bv_unsigned sb) D43.
    ck K16.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (UD2 : unpoisoned mx DT (DT + DTB)) by (clear - I0 HY UDT; open_xc I0; eapply x1_unp_dtM; eassumption) end.
    zstep. zstep. zstep.
    (destruct (chkB _ DT (DT + DTB) (DT + 2 * cur + 16 * u + 12) UD2 ltac:(lia) ltac:(lia)) as (b4 & RB4 & CK4 & SR4)).
    (assert (RS6 : rng RNG (Z.shiftr (DT + 2 * cur + 16 * u + 12) 3 + ASHOFF) 1);
      [apply (rng_sub' _ _ _ _ _ RSD); rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold shspan;
       clear - B3 D1 D2 CUR0 HSR; Z.div_mod_to_equations; lia|]; unfold ASHOFF in RS6).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (JOIN4 : forall y12 y15 : word,
      evtF bsegs RNG POST (SF (0x80298 + 4304) mx xra y5 (Z_to_bv 64 (DT + 2 * cur + 16 * u)) (Z_to_bv 64 (DT + 2 * cur)) (Z_to_bv 64 (16 * (256 - sym)))
        (Z_to_bv 64 (d4k (bv_unsigned sb) nb)) y12 (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (sym + u)) y15
        (Z_to_bv 64 (cur + 8 * u)) (Z_to_bv 64 nb) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 16)) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 40))
        (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 8)) (Z_to_bv 64 8) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 32)) xs11 (Z_to_bv 64 (16 * cnt))
        (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 56)) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 24)) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 48))))
    end.
    2: {
    zstep. rewrite sxb_sval.
    zstep.
    bcase KB4.
    - zstep. zstep. bcase KS4.
      + (apply JOIN4).
      + c8_bad KB4 KS4 CK4 SR4 (DT + 2 * cur + 16 * u + 12).
    - (apply JOIN4). }
    intros y12 y15. clear RB4 CK4 SR4 RS6 b4.
    zstep. zstep. zstep.
    (destruct (chkB _ DT (DT + DTB) (DT + 2 * cur + 16 * u + 19) UD2 ltac:(lia) B3) as (b5 & RB5 & CK5 & SR5)).
    (assert (RS7 : rng RNG (Z.shiftr (DT + 2 * cur + 16 * u + 19) 3 + ASHOFF) 1);
      [apply (rng_sub' _ _ _ _ _ RSD); rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold shspan;
       clear - B3 D1 D2 CUR0 HSR; Z.div_mod_to_equations; lia|]; unfold ASHOFF in RS7).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (JOIN5 : forall q5 q15 : word,
      evtF bsegs RNG POST (SF (0x80298 + 4324) mx xra q5 (Z_to_bv 64 (DT + 2 * cur + 16 * u)) (Z_to_bv 64 (DT + 2 * cur)) (Z_to_bv 64 (16 * (256 - sym)))
        (Z_to_bv 64 (d4k (bv_unsigned sb) nb)) (Z_to_bv 64 (DT + 2 * cur + 16 * u + 19)) (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (sym + u)) q15
        (Z_to_bv 64 (cur + 8 * u)) (Z_to_bv 64 nb) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 16)) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 40))
        (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 8)) (Z_to_bv 64 8) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 32)) xs11 (Z_to_bv 64 (16 * cnt))
        (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 56)) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 24)) (Z_to_bv 64 (Z.shiftr (d4k (bv_unsigned sb) nb) 48))))
    end.
    2: {
    zstep. rewrite sxb_sval.
    zstep.
    bcase KB5.
    - zstep. zstep. bcase KS5.
      + (apply JOIN5).
      + c8_bad KB5 KS5 CK5 SR5 (DT + 2 * cur + 16 * u + 19).
    - (apply JOIN5). }
    clear y5 y12 y15. intros y5 y15. clear RB5 CK5 SR5 RS7 b5.
    c8_st I0 (4 + 2 * (cur + 8 * u + 6)) nb D44.
    c8_st I0 (4 + 2 * (cur + 8 * u + 6) + 1) (bv_unsigned sb) D45.
    c8_st I0 (4 + 2 * (cur + 8 * u + 7)) nb D46.
    c8_st I0 (4 + 2 * (cur + 8 * u + 7) + 1) (bv_unsigned sb) D47.
    zstep. zstep.
    c8_st I0 (4 + 2 * (cur + 8 * u + 4)) nb D40.
    c8_st I0 (4 + 2 * (cur + 8 * u + 4) + 1) (bv_unsigned sb) D41.
    c8_st I0 (4 + 2 * (cur + 8 * u + 5)) nb D42.
    c8_st I0 (4 + 2 * (cur + 8 * u + 5) + 1) (bv_unsigned sb) D43.
    zstep. bcase K17; [exfalso; rewrite !signed_lit_small64 in K17 by lia; lia|].
    zstep. zstep. zstep.
    zstep. bcase KL.
    all: lazymatch type of I0 with XC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ _ _ _ _ _ _ _ _ _ _ _ =>
      assert (PF' : x1pref mtl tl (cur + 8 * (u + 1)) d)
        by (replace (cur + 8 * (u + 1)) with (cur + 8 * u + Z.of_nat 8) by lia;
            eapply (prf_close_c mtl tl (cur + 8 * u) [5; 4; 7; 6; 1; 0; 3; 2]); [| lia| vm_compute; reflexivity];
            eapply (prf_st_sy mtl tl (cur + 8 * u) [5; 4; 7; 6; 1; 0; 3; 2] _ 5); [| lia| lia| reflexivity];
            eapply (prf_st_nb mtl tl (cur + 8 * u) [4; 7; 6; 1; 0; 3; 2] _ 5); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy mtl tl (cur + 8 * u) [4; 7; 6; 1; 0; 3; 2] _ 4); [| lia| lia| reflexivity];
            eapply (prf_st_nb mtl tl (cur + 8 * u) [7; 6; 1; 0; 3; 2] _ 4); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy mtl tl (cur + 8 * u) [7; 6; 1; 0; 3; 2] _ 7); [| lia| lia| reflexivity];
            eapply (prf_st_nb mtl tl (cur + 8 * u) [6; 1; 0; 3; 2] _ 7); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy mtl tl (cur + 8 * u) [6; 1; 0; 3; 2] _ 6); [| lia| lia| reflexivity];
            eapply (prf_st_nb mtl tl (cur + 8 * u) [1; 0; 3; 2] _ 6); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy mtl tl (cur + 8 * u) [1; 0; 3; 2] _ 1); [| lia| lia| reflexivity];
            eapply (prf_st_nb mtl tl (cur + 8 * u) [0; 3; 2] _ 1); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy mtl tl (cur + 8 * u) [0; 3; 2] _ 0); [| lia| lia| reflexivity];
            eapply (prf_st_nb mtl tl (cur + 8 * u) [3; 2] _ 0); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy mtl tl (cur + 8 * u) [3; 2] _ 3); [| lia| lia| reflexivity];
            eapply (prf_st_nb mtl tl (cur + 8 * u) [2] _ 3); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy mtl tl (cur + 8 * u) [2] _ 2); [| lia| lia| reflexivity];
            eapply (prf_st_nb mtl tl (cur + 8 * u) [] dt 2); [apply prf_open; exact PF| lia| lia| reflexivity| lia| lia])
    end.
    - setreg_m 13 (16 * (u + 1)). setreg_m 14 (sym + (u + 1)). setreg_m 16 (cur + 8 * (u + 1)).
      (eapply KH; [lia | exact I0 | exact PF']).
    - zstep.
      (eapply KE; [lia | exact I0 | replace (cur + cnt * 8) with (cur + 8 * (u + 1)) by lia; exact PF']).
  Qed.
  Lemma c8_bf : forall (f g : Z -> Z) (L : list Z) s, forallb (fun t => Z.eqb (f t) (g t)) L = true -> In s L -> f s = g s.
  Proof. intros f g L s B IN. rewrite forallb_forall in B. apply Z.eqb_eq. exact (B s IN). Qed.
  Local Ltac bf_eq s n :=
    lazymatch goal with |- ?l = ?r =>
      let f := eval pattern s in l in let g := eval pattern s in r in
      lazymatch f with ?F s => lazymatch g with ?G s =>
        apply (c8_bf F G (map Z.of_nat (seq 0 n)) s);
        [vm_compute; reflexivity| apply in_map_iff; exists (Z.to_nat s); split; [lia| apply in_seq; lia]]
      end end
    end.
  Lemma x1_c8A : x1_c8A_stmt.
  Proof.
    intros m1 j0 j192 dt rst syb w cur sym cnt nb k112 k120 k128 k136 k144 xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11
      x28 x29 x30 x31 I HW HC HS HCN HL8 HNB PF KE.
    pose proof (x1_c8_loopA_of x1_c8_bodyA) as LOOP.
    pose proof I as I0. open_xc I.
    pose proof HY as H0. unfold x1A_hyps in H0.
    destruct H0 as (D1 & D2 & D3 & W1h & W2h & W3h & WKS & KHL & ALO & LOS & SPH & SP16 & SPAR & SPA32 & DSP & WSP & DWK & F64 & F4K & FAT
                    & FBL & DFF & WFF & DBL & RDT & RSD & WBL & RWK & RSW & RFF & RLO & RAI).
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR). rewrite HL8 in CL0, CLH.
    rewrite <- HC, <- HS, <- HCN in *.
    clear DSP WSP DWK DFF WFF.
    assert (CB : 0 <= cur < 2^32) by lia.
    pose proof (rw_cells_C8_C4C4 bsegs m1 (SPA + 80) [] [C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 w); C8 k112; C8 k120;
      C8 k128; C8 k136; C8 k144; C8 (Z_to_bv 64 cnt)] cur FR2 CB) as FRc.
    cbn [app] in FRc. clear FR2.
    zstep. zstep. bcase KZ.
    - (eapply KE; [exact I0| replace (cur + cnt * 8) with cur by (rewrite ?signed_lit_small64 in KZ by lia; lia); exact PF]).
    - do 17 (zstep).
      rewrite ?(sx32_small cur), ?(sx32_small sym) by lia.
      lazymatch StepF.reg_val 10 with Z_to_bv 64 ?z =>
        replace (Z_to_bv 64 z) with (Z_to_bv 64 (16 * (256 - sym))) by (f_equal; bf_eq sym 257%nat) end.
      replace (Z.land nb 255) with nb by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small;
        change (2^8) with 256; lia).
      rewrite (unsigned_lit cur) by lia. rewrite !(Z.shiftl_mul_pow2 cur 1) by lia. replace (2 ^ 1) with 2 by reflexivity.
      replace (Z_to_bv 64 (bv_swrap 32 (sym + 0))) with (Z_to_bv 64 (sym + 0)) by (f_equal; bf_eq sym 257%nat).
      replace (Z_to_bv 64 (cnt ≪ 4)) with (Z_to_bv 64 (16 * cnt)) by (f_equal; bf_eq cnt 257%nat).
      setreg_m 13 (16 * 0). setreg_m 16 (cur + 8 * 0). setreg_m 7 (DT + 2 * cur).
      (eapply (LOOP (Z.to_nat (cnt - 1)) m1 j0 j192 dt rst syb w cur sym cnt nb 0);
        [exact I0| exact HW| exact HC| exact HS| exact HCN| exact HL8| exact HNB| lia| lia| rewrite Z.mul_0_r, Z.add_0_r; exact PF| exact KE]).
  Qed.
  End C8.
End X1B.
End CANSEC1.
