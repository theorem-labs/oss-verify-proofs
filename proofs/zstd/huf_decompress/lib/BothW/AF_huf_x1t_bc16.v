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
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs AF_huf_x1t_bfk AF_huf_x1t_bpure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition d4f (d sv nb : Z) : Prop :=
  0 <= d <= 18446744073709551615 /\ d mod 2 ^ 64 = d /\ d mod 256 = nb /\ (d / 256) mod 256 = sv /\ (d / 65536) mod 256 = nb /\ (d / 16777216) mod 256 = sv /\
  (d / 4294967296) mod 256 = nb /\ (d / 1099511627776) mod 256 = sv /\ (d / 281474976710656) mod 256 = nb /\ (d / 72057594037927936) mod 256 = sv.
Lemma d4f_ok : forall sv nb, 0 <= sv < 256 -> 0 <= nb < 256 -> d4f (d4k sv nb) sv nb.
Proof.
  intros sv nb Hs Hn. pose proof (d4k_bytes sv nb Hs Hn) as (M & B). split; [| split; [exact M| exact B]].
  pose proof (Z.mod_pos_bound (d4k sv nb) (2 ^ 64) ltac:(lia)) as R. rewrite M in R. lia.
Qed.
Lemma len16 : forall w, 5 <= w <= 12 -> 16 <= hw_cells w <= 2048 /\ (16 | hw_cells w).
Proof.
  intros w Hw. unfold hw_cells. destruct (Z.eqb_spec w 0); [lia|].
  split; [split; [change 16 with (2^4); apply Z.pow_le_mono_r; lia| change 2048 with (2^11); apply Z.pow_le_mono_r; lia]|].
  exists (2^(w - 1 - 4)). change 16 with (2^4). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma q_bounds : forall cur cnt len s, 0 <= cur -> 0 <= len -> 0 <= s < cnt -> cur + cnt * len <= 4096 ->
  0 <= cur + len * s /\ cur + len * s + len <= 4096.
Proof. intros cur0 cnt len s Hc Hl Hs Hb. split; [nia|]. assert (len * s + len <= cnt * len) by nia. lia. Qed.
Lemma u32b_len : forall ws, length (u32b ws) = (4 * length ws)%nat.
Proof. induction ws as [|x t IH]; [reflexivity|]. cbn [u32b]. rewrite length_app, IH. cbn [length u32q]. lia. Qed.
Ltac splitn n := lazymatch n with O => idtac | S ?k => split; [| splitn k] end.
Ltac x1_hy HY := pose proof HY as (DT4 & DTH & DTA & WK4 & WKH & WKA & WKS & KHL & ATL & LOS & SPVH & SPVA & SPAR & SPAA &
    DTLO & WKLO & DTWK & FFA & FF4 & FFT & FFB & DTFF & WKFF & DTB0 & RDT & RSDT & WKB0 & RWK & RSWK & RFF & RLO & RAI).
Ltac w4ez :=
  repeat lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs));
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end
  end.
Ltac w4br :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ =>
      w4ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      rewrite ?Z.mod_small by lia;
      first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
            | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
  end.
Ltac xa_norm E :=
  let b := eval unfold E in E in
  lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
    let na := eval vm_compute in (length zv) in
    rewrite ?adenot_wa; change E with (kE zv xs);
    repeat match goal with
    | |- context [estart (kE zv xs) ?a] =>
        rewrite (estart_ez_kE zv xs a); [ | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia ]
    end;
    rewrite ?(ez_ok zv (kE zv xs) (kE_atoms zv xs));
    cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
  end.
Ltac xa_store8 SPA :=
  lazymatch goal with |- store_ok _ _ (adenot ?E _) _ = true => xa_norm E end;
  lazymatch goal with |- store_ok _ ?m (wa (SPA + ?o)) _ = true =>
    let k := eval vm_compute in (Z.to_nat (o - 80)) in
    lazymatch goal with H : rw_cells _ m (SPA + 80) ?cs |- _ =>
      eapply (rw_cells_store_ok_at bsegs m (SPA + 80) cs k); [exact H | reflexivity | reflexivity | unfold wa; f_equal; lia] end
  end.
Ltac negfix :=
  repeat match goal with |- context [Z_to_bv 64 (Zneg ?p)] =>
    let v := eval vm_compute in (2^64 + Zneg p) in
    replace (Z_to_bv 64 (Zneg p)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; reflexivity) end.
Ltac w4neq :=
  lazymatch goal with
  | |- branch_taken BC_EQ _ _ = false =>
      w4ez; unfold branch_taken; apply bv_eqb_neq; let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E;
      rewrite !Z_to_bv_unsigned in E; unfold bv_wrap, bv_modulus in E; rewrite !Z.mod_small in E by lia; lia
  | |- branch_taken BC_NE _ _ = true =>
      w4ez; unfold branch_taken; apply Bool.negb_true_iff, bv_eqb_neq; let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E;
      rewrite !Z_to_bv_unsigned in E; unfold bv_wrap, bv_modulus in E; rewrite !Z.mod_small in E by lia; lia
  end.
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
  Section C16.
  Variables (hw rank : list Z) (nbs tl mtl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Notation XFm := (XF m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Notation XCm := (XC m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Notation SF pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation STC pc mm nb len xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF pc mm xra x5 x6 x7 xa0 (Z_to_bv 64 nb) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation STL mm len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x81964 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation XDm j0 j192 dt rst syb w cur sym cnt nb len :=
    (XCm j0 j192 dt rst syb w cur sym cnt (Z_to_bv 64 (2 * len)) (Z_to_bv 64 cnt) (Z_to_bv 64 nb) (Z_to_bv 64 sym) (Z_to_bv 64 (256 - sym))).
  Notation STO mm s q len x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 xa1 xa2 (Z_to_bv 64 s) (Z_to_bv 64 (DT + 2 * q)) xa5 (Z_to_bv 64 q) xa7
             xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5 (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 len) xs10 xs11
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x81460) fc None mm (seg_rom bsegs)).
  Notation STI mm u s q len d x5 x6 x7 xa0 xa2 xa5 xa7 xs4 xs5 xs10 xs11 x29 x30 :=
    (MS (mkR (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 (Z_to_bv 64 d) xa2 (Z_to_bv 64 s) (Z_to_bv 64 (DT + 2 * q)) xa5 (Z_to_bv 64 q) xa7
             (Z_to_bv 64 (32 * u)) (Z_to_bv 64 0x7fff8000) xs4 xs5 (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 len) xs10 xs11
             (Z_to_bv 64 (16 * u)) x29 x30 (Z_to_bv 64 (18446744073709551615 - (DT + 4 + 2 * q))))
        F (Z_to_bv 64 0x814dc) fc None mm (seg_rom bsegs)).
  Notation STI2 mm u s q len d x5 x6 xa0 :=
    (MS (mkR (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 SPA) gp tp x5 x6 (Z_to_bv 64 (d / 256)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 (Z_to_bv 64 d) (Z_to_bv 64 (DT + 2 * q + 32 * u)) (Z_to_bv 64 s) (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 (DT + 2 * q + 32 * u + 4)) (Z_to_bv 64 q)
             (Z_to_bv 64 (DT + 2 * q + 32 * u))
             (Z_to_bv 64 (32 * u)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (d / 4294967296)) (Z_to_bv 64 (d / 72057594037927936))
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 len)
             (Z_to_bv 64 (d / 65536)) (Z_to_bv 64 (d / 16777216))
             (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (d / 1099511627776)) (Z_to_bv 64 (d / 281474976710656)) (Z_to_bv 64 (18446744073709551615 - (DT + 4 + 2 * q))))
        F (Z_to_bv 64 0x815a0) fc None mm (seg_rom bsegs)).
  Notation STDL mm s q len x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 xa1 xa2 (Z_to_bv 64 s) (Z_to_bv 64 (DT + 2 * q)) xa5 (Z_to_bv 64 q) xa7
             xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5 (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 len) xs10 xs11
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x816a4) fc None mm (seg_rom bsegs)).
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
  Lemma XC_sb : forall j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 a x v,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> DT <= a < DT + DTB -> x mod 256 = v mod 256 -> 0 <= v < 256 ->
    XCm j0 j192 (Zupd (a - DT) v dt) rst syb w cur sym cnt k112 k120 k128 k136 k144 (write_to_mem m1 (wa a) (le1 (Z_to_bv 64 x))).
  Proof.
    intros until v. intros I AR XV VR. open_xc I. x1_hy HY.
    pose proof (u32b_len rank) as LRS. pose proof (u32b_len rst) as LRT.
    assert (L1 : length (le1 (Z_to_bv 64 x)) = 1%nat) by reflexivity.
    replace (wa a) with (wa (DT + (a - DT))) by (f_equal; lia).
    unfold XC. splitn 18%nat.
    - exact DTF.
    - apply u8arr_sb; [exact DTC | lia | exact XV].
    - rewrite Zupd_length2; exact DTLEN.
    - apply Forall_Zupd; [exact DTBY | cbn; lia].
    - apply u8arr_frame; [exact HWC | lia | rewrite L1; lia | rewrite L1, length_map; lia].
    - apply u8arr_frame; [exact RK | lia | rewrite L1; lia | rewrite L1, length_map; lia].
    - apply u8arr_frame; [exact RST | lia | rewrite L1; lia | rewrite L1, length_map; lia].
    - exact RSTLEN.
    - apply stk_write; [exact STS | lia | rewrite L1; lia].
    - apply u8arr_frame; [exact SYC | lia | rewrite L1; lia | rewrite L1; lia].
    - exact SYLEN.
    - apply stk_write; [exact WKR | lia | rewrite L1; lia].
    - apply stk_write; [exact STK | lia | rewrite L1; lia].
    - apply mem_inv_store; [exact MI | rewrite L1; eapply (u8arr_store_ok _ _ _ _ (a - DT)); [exact DTC | rewrite length_map; lia | reflexivity]].
    - apply munch_write; [exact MU | lia | rewrite L1; lia | rewrite L1; cbn [inside]; left; lia].
    - apply wmono_write; exact WM.
    - apply rw_cells_frame; [exact FR1 | lia | rewrite L1; lia | rewrite L1; unfold X1FR1; cbn [cells_size csize]; lia].
    - apply rw_cells_frame; [exact FR2 | lia | rewrite L1; lia | rewrite L1; cbn [cells_size csize]; lia].
    - apply rw_cells_frame; [exact FR4 | lia | rewrite L1; lia | rewrite L1; unfold X1FR4; cbn [cells_size csize]; lia].
  Qed.
  Definition XC2 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (cs : list cell) (m1 : amem) : Prop :=
    4 + 2 * 2 ^ tl <= DTB
    /\ u8arr bsegs m1 DT (map (Z_to_bv 8) dt) /\ zlen dt = DTB /\ Forall isbyte dt
    /\ u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) /\ u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank))
    /\ u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) /\ zlen rst = 13
    /\ stk bsegs m1 (WK + 104) (WK + 980) /\ u8arr bsegs m1 (WK + 980) syb /\ zlen syb = 256 /\ stk bsegs m1 (WK + 1492) (WK + wksz)
    /\ stk bsegs m1 lo SPA /\ mem_inv bsegs m1
    /\ munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 /\ wmono bsegs m5 m1
    /\ rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0)
    /\ rw_cells bsegs m1 (SPA + 80) cs
    /\ rw_cells bsegs m1 (SPA + 160) (X1FR4 DT WK FF j192).
  Lemma XC2_wr8 : forall j0 j192 dt rst syb cs m1 (k : nat) w0 v a,
    XC2 j0 j192 dt rst syb cs m1 -> cell_at cs k = Some (C8 w0) -> (k + 8 <= 80)%nat -> a = SPA + 80 + Z.of_nat k ->
    XC2 j0 j192 dt rst syb (cell_upd cs k (C8 v)) (CatExec.wbytes m1 (wa a) (word_to_le_bytes 8 v)).
  Proof.
    intros until a. intros I CK KR AE. x1_hy HY.
    destruct I as (DTF & DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & STK & MI & MU & WM & FR1 & FR2 & FR4).
    pose proof (u32b_len rank) as LRS. pose proof (u32b_len rst) as LRT.
    assert (L8 : length (word_to_le_bytes 8 v) = 8%nat) by reflexivity.
    subst a. change (CatExec.wbytes m1 (wa (SPA + 80 + Z.of_nat k)) (word_to_le_bytes 8 v))
      with (write_to_mem m1 (wa (SPA + 80 + Z.of_nat k)) (word_to_le_bytes 8 v)).
    unfold XC2. splitn 18%nat.
    - exact DTF.
    - apply u8arr_frame; [exact DTC | lia | rewrite L8; lia | rewrite L8, length_map; lia].
    - exact DTLEN.
    - exact DTBY.
    - apply u8arr_frame; [exact HWC | lia | rewrite L8; lia | rewrite L8, length_map; lia].
    - apply u8arr_frame; [exact RK | lia | rewrite L8; lia | rewrite L8, length_map; lia].
    - apply u8arr_frame; [exact RST | lia | rewrite L8; lia | rewrite L8, length_map; lia].
    - exact RSTLEN.
    - apply stk_write; [exact STS | lia | rewrite L8; lia].
    - apply u8arr_frame; [exact SYC | lia | rewrite L8; lia | rewrite L8; lia].
    - exact SYLEN.
    - apply stk_write; [exact WKR | lia | rewrite L8; lia].
    - apply stk_write; [exact STK | lia | rewrite L8; lia].
    - change (word_to_le_bytes 8 v) with (cbytes (C8 v)).
      apply mem_inv_store_cbytes; [exact MI | exact I | eapply rw_cells_store_ok; [exact FR2 | exact CK | reflexivity]].
    - apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; right; right; left; lia].
    - apply wmono_write; exact WM.
    - apply rw_cells_frame; [exact FR1 | lia | rewrite L8; lia | rewrite L8; unfold X1FR1; cbn [cells_size csize]; lia].
    - change (word_to_le_bytes 8 v) with (cbytes (C8 v)).
      eapply rw_cells_write; [exact FR2 | exact CK | reflexivity | exact I].
    - apply rw_cells_frame; [exact FR4 | lia | rewrite L8; lia | rewrite L8; unfold X1FR4; cbn [cells_size csize]; lia].
  Qed.
  Lemma XC2_wr8c : forall j0 j192 dt rst syb cs cs' m1 (k : nat) w0 v a,
    XC2 j0 j192 dt rst syb cs m1 -> cell_at cs k = Some (C8 w0) -> (k + 8 <= 80)%nat -> a = SPA + 80 + Z.of_nat k ->
    cs' = cell_upd cs k (C8 v) ->
    XC2 j0 j192 dt rst syb cs' (CatExec.wbytes m1 (wa a) (word_to_le_bytes 8 v)).
  Proof. intros until a. intros I CK KR AE ->. exact (XC2_wr8 _ _ _ _ _ _ _ _ _ _ _ I CK KR AE). Qed.
  Ltac xc2_mem M :=
    lazymatch M with
    | CatExec.wbytes ?m (wa (SPA + ?o)) (word_to_le_bytes 8 ?v) =>
        xc2_mem m;
        lazymatch goal with H : XC2 _ _ _ _ _ ?cs _ |- _ =>
          let k := eval vm_compute in (Z.to_nat (o - 80)) in
          let cs' := eval cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in (cell_upd cs k (C8 v)) in
          eapply (XC2_wr8c _ _ _ _ _ cs cs' m k _ v (SPA + o)) in H;
          [ | reflexivity | apply Nat.leb_le; reflexivity | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; ring | reflexivity ]
        end
    | _ => idtac
    end.
  Ltac xc2_chain := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => xc2_mem M end.
  Definition x1_cd_setA_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w ->
    (forall m2 (ya0 ya1 ya2 : word), 0 < cnt -> XDm j0 j192 dt rst syb w cur sym cnt nb len m2 ->
       evtF bsegs RNG POST (STO m2 0 cur len x5 x6 x7 ya0 ya1 ya2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31)) ->
    (forall (ya0 : word), cnt = 0 ->
       evtF bsegs RNG POST (STL m1 len xra x5 x6 x7 ya0 (Z_to_bv 64 nb) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (STC 0x813f8 m1 nb len xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Lemma x1_cd_setA : x1_cd_setA_stmt.
  Proof.
    unfold x1_cd_setA_stmt. intros until x31. intros I HW HC HS HCN W5 HL HNB K1 KE.
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite <- HC, <- HS, <- HCN in *. rewrite <- HL in CL0, CLH, LENR.
    pose proof (proj1 (len16 w ltac:(lia))) as LEN16. rewrite <- HL in LEN16.
    pose proof I as I0. open_xc I0. x1_hy HY.
    assert (CR : 0 <= cur <= 4096) by lia. assert (SR : 0 <= sym <= 256) by lia. assert (NR : 0 <= cnt <= 256) by lia.
    assert (NBR : 1 <= nb <= 12) by lia.
    destruct (Z.eq_dec cnt 0) as [C0|CP].
    - kx_runFmd [529504; 530788] 10%nat [true]
        [KZRange SPA 4096 (2^47); KZRange cnt 0 0; KZWord (SPA + 152) 8 cnt]
        (@nil (Z * Z)) [(SPA, 216)] (@nil (Z * Z)).
      all: try w4br.
      kx_post_regs. cbn [mem_denot]. negfix. apply (KE _ C0).
    - kx_runFm [529504; 530788] 40%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256;
         KZRange cnt 1 256; KZRange nb 1 12; KZRange len 16 2048;
         KZWord (SPA + 152) 8 cnt; KZWord (SPA + 88) 8 sym; KZWord (SPA + 80) 8 cur; KZWord (SPA + 64) 8 DT]
        (@nil (Z * Z)) [(SPA, 216)] (@nil (Z * Z)).
      all: try w4br.
      1-5: xa_store8 SPA.
      kx_post_regs.
      lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; xa_norm E end.
      assert (I2 : XC2 j0 j192 dt rst syb [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 w);
                                            C8 k112; C8 k120; C8 k128; C8 k136; C8 k144; C8 (Z_to_bv 64 cnt)] m1) by exact I.
      xc2_chain.
      replace (Z_to_bv 64 (-1 * sym + 256)) with (Z_to_bv 64 (256 - sym)) in * by (f_equal; lia).
      replace (Z_to_bv 64 (- sym + 256)) with (Z_to_bv 64 (256 - sym)) by (f_equal; lia).
      negfix.
      eapply K1; [lia | exact I2].
  Qed.
  Definition x1_cd_headA_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len s q : Z)
      x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XDm j0 j192 dt rst syb w cur sym cnt nb len m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w -> 0 <= s < cnt -> q = cur + len * s -> 0 <= q -> q + len <= 4096 ->
    (forall m2 (sv d : Z) (ya0 ya2 ya5 : word), 0 <= sv < 256 -> d4f d sv nb ->
       XDm j0 j192 dt rst syb w cur sym cnt nb len m2 ->
       evtF bsegs RNG POST (STI m2 0 s q len d x5 x6 x7 ya0 ya2 ya5 xa7 xs4 xs5 xs10 xs11 x29 x30)) ->
    evtF bsegs RNG POST (STO m1 s q len x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Lemma x1_cd_headA : x1_cd_headA_stmt.
  Proof.
    unfold x1_cd_headA_stmt. intros until x31. intros I HW HC HS HCN W5 HL HNB SR HQ Q0 QH K.
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite <- HC, <- HS, <- HCN in *. rewrite <- HL in CL0, CLH, LENR.
    pose proof (proj1 (len16 w ltac:(lia))) as LEN16. rewrite <- HL in LEN16.
    pose proof I as I0. open_xc I0. x1_hy HY.
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption).
    assert (CR : 0 <= cur <= 4096) by lia. assert (SYR : 0 <= sym <= 256) by lia. assert (NR : 1 <= cnt <= 256) by lia.
    assert (NBR : 1 <= nb <= 12) by lia. assert (S8 : 0 <= s <= 255) by lia. assert (QR : 0 <= q <= 4080) by lia.
    assert (SSY : s + sym < 256) by lia.
    unfold shspan in RSDT, RSWK.
    kx_runFm [529628] 60%nat
      [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256;
       KZRange cnt 1 256; KZRange nb 1 12; KZRange len 16 2048; KZRange s 0 255; KZRange q 0 4080;
       KZWord (SPA + 144) 8 (256 - sym); KZWord (SPA + 136) 8 sym; KZWord (SPA + 168) 8 (18446744073709551615 - (WK + 980));
       KZWord (SPA + 176) 8 (WK + 980); KZWord (SPA + 184) 8 (DT + 4); KZWord (SPA + 128) 8 nb; KZWord (SPA + 160) 8 281479271743489]
      [(WK + 980 + sym + s, 1)] [(SPA, 216); (WK + 980 + sym + s, 1)] [(WK + 980 + sym + s, 1)].
    all: try w4br.
    1: w4neq.
    kx_range (EVar 31) BR.
    kx_post_regs. cbn [mem_denot]. negfix.
    set (b := bv_unsigned (ev KXE 31)) in *.
    replace (Z_to_bv 64 (- DT + -2 * q + -5)) with (Z_to_bv 64 (18446744073709551615 - (DT + 4 + 2 * q)))
      by (apply Z_to_bv_eqm; replace (18446744073709551615 - (DT + 4 + 2 * q)) with ((- DT + -2 * q + -5) + 1 * 2^64) by lia;
          rewrite Z_mod_plus_full; reflexivity).
    apply (K m1 b (d4k b nb)); [lia | apply d4f_ok; lia | exact I].
  Qed.
  Definition x1_cd_slA_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len s q : Z)
      x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XDm j0 j192 dt rst syb w cur sym cnt nb len m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w -> 0 <= s < cnt -> q = cur + len * s -> 0 <= q -> q + len <= 4096 ->
    (forall (ya0 ya1 : word), s + 1 < cnt ->
       evtF bsegs RNG POST (STO m1 (s + 1) (q + len) len x5 x6 x7 ya0 ya1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31)) ->
    (forall (yra ya0 ya1 ya3 ya4 ya6 : word), s + 1 = cnt ->
       evtF bsegs RNG POST (STL m1 len yra x5 x6 x7 ya0 ya1 xa2 ya3 ya4 xa5 ya6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (STDL m1 s q len x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Lemma x1_cd_slA : x1_cd_slA_stmt.
  Proof.
    unfold x1_cd_slA_stmt. intros until x31. intros I HW HC HS HCN W5 HL HNB SR HQ Q0 QH KN KE.
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite <- HC, <- HS, <- HCN in *. rewrite <- HL in CL0, CLH, LENR.
    pose proof (proj1 (len16 w ltac:(lia))) as LEN16. rewrite <- HL in LEN16.
    pose proof I as I0. open_xc I0. x1_hy HY.
    assert (NR : 1 <= cnt <= 256) by lia. assert (S8 : 0 <= s <= 255) by lia. assert (QR : 0 <= q <= 4080) by lia.
    destruct (Z.eq_dec (s + 1) cnt) as [SE|SN].
    - kx_runFm [529504; 530788] 30%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange len 16 2048; KZRange s 0 255; KZRange q 0 4080;
         KZRange cnt 1 256; KZWord (SPA + 112) 8 (2 * len); KZWord (SPA + 120) 8 (s + 1)]
        (@nil (Z * Z)) [(SPA, 216)] (@nil (Z * Z)).
      all: try w4br.
      kx_post_regs. cbn [mem_denot]. negfix. apply (KE _ _ _ _ _ _ SE).
    - kx_runFmd [529504; 530788] 30%nat [true]
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange len 16 2048; KZRange s 0 255; KZRange q 0 4080;
         KZRange cnt 1 256; KZWord (SPA + 112) 8 (2 * len); KZWord (SPA + 120) 8 cnt]
        (@nil (Z * Z)) [(SPA, 216)] (@nil (Z * Z)).
      all: try w4br.
      1: w4neq.
      kx_post_regs. cbn [mem_denot]. negfix.
      replace (DT + (2 * q + 2 * len)) with (DT + 2 * (q + len)) by lia.
      apply KN. lia.
  Qed.
  End C16.
End X1B.
End CANSEC1.
