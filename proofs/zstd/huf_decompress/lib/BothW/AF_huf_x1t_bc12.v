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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Lemma brute_eq : forall (g h : Z -> Z), forallb (fun n => Z.eqb (g (Z.of_nat n)) (h (Z.of_nat n))) (seq 0 4097) = true ->
  forall c, 0 <= c <= 4096 -> g c = h c.
Proof.
  intros g h B c Hc. rewrite forallb_forall in B.
  specialize (B (Z.to_nat c)). rewrite in_seq, Z2Nat.id in B by lia.
  apply Z.eqb_eq, B. lia.
Qed.
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
  Section C12.
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
  Lemma mod256_lo : forall a b, (a + 256 * b) mod 256 = a mod 256.
  Proof. intros a b. rewrite (Z.mul_comm 256 b), Z.mod_add; lia. Qed.
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
  Notation SF pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation STC pc mm nb len xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF pc mm xra x5 x6 x7 xa0 (Z_to_bv 64 nb) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation STL mm len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x81964 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation ST2 mm nb sym cur cnt u xra x5 xa1 xa2 xa3 xa5 xs2 xs4 xs5 xs10 xs11 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 (Z_to_bv 64 (DT + 4 + 2 * cur)) (Z_to_bv 64 (cur + 2 * u)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             (Z_to_bv 64 (DT + 2 * cur)) xa1 xa2 xa3 (Z_to_bv 64 (4 * u)) xa5 (Z_to_bv 64 nb) (Z_to_bv 64 (sym + u)) xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 2) xs10 xs11
             (Z_to_bv 64 (4 * (256 - sym))) (Z_to_bv 64 (4 * cnt)) (Z_to_bv 64 (cur + 2 * u)) x31)
        F (Z_to_bv 64 0x810f0) fc None mm (seg_rom bsegs)).
  Definition x1_c2_bodyA_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb u : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 xa1 xa2 xa3 xa5 xs2 xs4 xs5 xs10 xs11 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 2 ->
    nb = tl + 1 - w -> 0 <= u < cnt -> x1pref mtl tl (cur + 2 * u) dt ->
    (forall m2 (dt' : list Z) (y5 ya1 ya2 ya3 ya5 y31 : word), u + 1 < cnt -> XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 -> x1pref mtl tl (cur + 2 * (u + 1)) dt' ->
       evtF bsegs RNG POST (ST2 m2 nb sym cur cnt (u + 1) xra y5 ya1 ya2 ya3 ya5 xs2 xs4 xs5 xs10 xs11 y31)) ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), u + 1 = cnt -> XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 2) dt' ->
       evtF bsegs RNG POST (STL m2 2 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST2 m1 nb sym cur cnt u xra x5 xa1 xa2 xa3 xa5 xs2 xs4 xs5 xs10 xs11 x31).
  Lemma x1_c2_bodyA : x1_c2_bodyA_stmt.
  Proof.
    unfold x1_c2_bodyA_stmt. intros until x31. intros I HW HC HS HCN HL2 HNB HU PF KH KE.
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite HL2 in CL0, CLH. rewrite <- HC, <- HS, <- HCN in *.
    pose proof I as I0. open_xc I0. x1_hy HY.
    assert (UDT1 : unpoisoned m1 DT (DT + DTB)) by (eapply x1_unp_dtM; eassumption).
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption).
    assert (CR : 0 <= cur <= 4096) by lia. assert (SYR : 0 <= sym <= 256) by lia. assert (NR : 1 <= cnt <= 256) by lia.
    assert (NBR : 1 <= nb <= 12) by lia. assert (UR : 0 <= u <= 255) by lia.
    assert (SSY : sym + u < 256) by lia. assert (CU : cur + 2 * u + 1 < 4096) by lia.
    assert (DTW : DT + 4 + 2 * cur + 4 * u + 4 <= DT + DTB) by lia.
    unfold shspan in RSDT, RSWK.
    assert (LSY : Z.of_nat (length syb) = 256) by exact SYLEN.
    assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = DTB) by (rewrite length_map; exact DTLEN).
    assert (CK : u + 1 < cnt \/ u + 1 = cnt) by lia. destruct CK as [CK|CK].
    - kx_runFm [0x810f0; 0x81964; 0x80618; 0x819cc] 80%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256;
         KZRange cnt 1 256; KZRange nb 1 12; KZRange u 0 255; KZRange (sym + u) 0 255; KZRange (cur + 2 * u) 0 4094;
         KZRange (cnt - u - 2) 0 254; KZWr (DT + 4 + 2 * cur + 4 * u) 4;
         KZWord (SPA + 168) 8 (18446744073709551615 - (WK + 980)); KZWord (SPA + 176) 8 (WK + 980); KZWord (SPA + 184) 8 (DT + 4)]
        [(WK + 980 + sym + u, 1)] [(DT + 4 + 2 * cur + 4 * u, 4)] [(WK + 980 + sym + u, 1); (DT + 4 + 2 * cur + 4 * u, 4)].
      all: try w4br.
      all: try w4neq.
      all: try (unfold accP; cbn [fst snd]; lazymatch goal with |- RNG (bv_unsigned (adenot ?E _)) _ => xa_norm E end;
            unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
            first [ apply RLO; cbn [Z.of_nat Pos.of_succ_nat]; lia | apply RWK; cbn [Z.of_nat Pos.of_succ_nat]; lia ]).
      all: try clear BND; pose proof (x1_bands RNG SPV SPA lo DT DTB WK wksz FF HY) as BND.
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => idtac end;
         unfold flat, elenZ; repeat split; xa_norm KXE; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
         change (2 ^ Z.of_N 64) with (2^64) in *; change (3 mod 64) with 3 in *;
         rewrite ?(Z.mod_small 1) by lia; rewrite ?Z.mod_small by lia;
         unfold ASHOFF, KLOW, KHIGH, AIMG_HI in *; Z.div_mod_to_equations; lia).
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => idtac end;
         unfold ASHOFF, KLOW, KHIGH, AIMG_HI in *; change (2 ^ Z.of_N 64) with (2^64) in *; rewrite ?(Z.mod_small 1) by lia;
         change (3 mod 64) with 3 in *; Z.div_mod_to_equations; lia).
      kx_post_regs.
      lazymatch goal with |- context [mem_denot _ _ (SE _ _ (EVar ?k) :: _)] =>
        kx_range (EVar k) RB; set (b := bv_unsigned (ev KXE k)) in * end.
      cbn [mem_denot]. negfix. xa_norm KXE.
      rewrite !wbytes_eq. change (word_to_le_bytes 1) with le1.
      lazymatch goal with |- context [?w4 (?w3 (?w2 (?w1 m1 (wa ?a4) (?l1 (Z_to_bv 64 ?x4))) (wa ?a5) (?l2 (Z_to_bv 64 ?x5))) (wa ?a6) (?l3 (Z_to_bv 64 ?x6))) (wa ?a7) (?l4 (Z_to_bv 64 ?x7))] =>
        pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a4 x4 nb I ltac:(lia) (mod256_lo nb b) ltac:(lia)) as XC1;
        pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a5 x5 b XC1 ltac:(lia) eq_refl ltac:(lia)) as XC2;
        pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a6 x6 nb XC2 ltac:(lia) (mod256_lo nb b) ltac:(lia)) as XC3;
        pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a7 x7 b XC3 ltac:(lia) eq_refl ltac:(lia)) as XC4
      end.
      lazymatch goal with |- evtF ?ga ?gb ?gc ?s1 =>
        let H := fresh "HS" in
        assert (H : forall s2, s2 = s1 -> evtF ga gb gc s2 -> evtF ga gb gc s1) by (intros ? -> ?; assumption);
        eapply H; clear H; [ | eapply (KH _ _) ] end.
      + (f_equal; f_equal; first [reflexivity | f_equal; lia]).
      + exact CK.
      + exact XC4.
      + lazymatch goal with |- x1pref _ _ ?c _ => replace c with (cur + 2 * u + Z.of_nat 2) by lia end.
        apply (prf_close_c mtl tl (cur + 2 * u) [1; 0]); [ | lia | reflexivity ].
        apply (prf_st_sy mtl tl (cur + 2 * u) [1; 0] _ 1); [ | lia | lia | lia ].
        apply (prf_st_nb mtl tl (cur + 2 * u) [0] _ 1); [ | lia | lia | lia | rewrite ?Zupd_length2; lia | lia ].
        apply (prf_st_sy mtl tl (cur + 2 * u) [0] _ 0); [ | lia | lia | lia ].
        apply (prf_st_nb mtl tl (cur + 2 * u) [] _ 0); [ apply prf_open; exact PF | lia | lia | lia | rewrite ?Zupd_length2; lia | lia ].
    - rewrite <- CK.
      kx_runFm [0x810f0; 0x81964; 0x80618; 0x819cc] 80%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256;
         KZRange nb 1 12; KZRange u 0 255; KZRange (sym + u) 0 255; KZRange (cur + 2 * u) 0 4094;
         KZWr (DT + 4 + 2 * cur + 4 * u) 4;
         KZWord (SPA + 168) 8 (18446744073709551615 - (WK + 980)); KZWord (SPA + 176) 8 (WK + 980); KZWord (SPA + 184) 8 (DT + 4)]
        [(WK + 980 + sym + u, 1)] [(DT + 4 + 2 * cur + 4 * u, 4)] [(WK + 980 + sym + u, 1); (DT + 4 + 2 * cur + 4 * u, 4)].
      all: try w4br.
      all: try w4neq.
      all: try (unfold accP; cbn [fst snd]; lazymatch goal with |- RNG (bv_unsigned (adenot ?E _)) _ => xa_norm E end;
            unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
            first [ apply RLO; cbn [Z.of_nat Pos.of_succ_nat]; lia | apply RWK; cbn [Z.of_nat Pos.of_succ_nat]; lia ]).
      all: try clear BND; pose proof (x1_bands RNG SPV SPA lo DT DTB WK wksz FF HY) as BND.
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => idtac end;
         unfold flat, elenZ; repeat split; xa_norm KXE; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
         change (2 ^ Z.of_N 64) with (2^64) in *; change (3 mod 64) with 3 in *;
         rewrite ?(Z.mod_small 1) by lia; rewrite ?Z.mod_small by lia;
         unfold ASHOFF, KLOW, KHIGH, AIMG_HI in *; Z.div_mod_to_equations; lia).
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => idtac end;
         unfold ASHOFF, KLOW, KHIGH, AIMG_HI in *; change (2 ^ Z.of_N 64) with (2^64) in *; rewrite ?(Z.mod_small 1) by lia;
         change (3 mod 64) with 3 in *; Z.div_mod_to_equations; lia).
      kx_post_regs.
      lazymatch goal with |- context [mem_denot _ _ (SE _ _ (EVar ?k) :: _)] =>
        kx_range (EVar k) RB; set (b := bv_unsigned (ev KXE k)) in * end.
      cbn [mem_denot]. negfix. xa_norm KXE.
      rewrite !wbytes_eq. change (word_to_le_bytes 1) with le1.
      lazymatch goal with |- context [?w4 (?w3 (?w2 (?w1 m1 (wa ?a4) (?l1 (Z_to_bv 64 ?x4))) (wa ?a5) (?l2 (Z_to_bv 64 ?x5))) (wa ?a6) (?l3 (Z_to_bv 64 ?x6))) (wa ?a7) (?l4 (Z_to_bv 64 ?x7))] =>
        pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a4 x4 nb I ltac:(lia) (mod256_lo nb b) ltac:(lia)) as XC1;
        pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a5 x5 b XC1 ltac:(lia) eq_refl ltac:(lia)) as XC2;
        pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a6 x6 nb XC2 ltac:(lia) (mod256_lo nb b) ltac:(lia)) as XC3;
        pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a7 x7 b XC3 ltac:(lia) eq_refl ltac:(lia)) as XC4
      end.
      lazymatch goal with |- evtF ?ga ?gb ?gc ?s1 =>
        let H := fresh "HS" in
        assert (H : forall s2, s2 = s1 -> evtF ga gb gc s2 -> evtF ga gb gc s1) by (intros ? -> ?; assumption);
        eapply H; clear H; [ | eapply (KE _ _) ] end.
      + (f_equal; f_equal; first [reflexivity | f_equal; lia]).
      + exact CK.
      + exact XC4.
      + lazymatch goal with |- x1pref _ _ ?c _ => replace c with (cur + 2 * u + Z.of_nat 2) by lia end.
        apply (prf_close_c mtl tl (cur + 2 * u) [1; 0]); [ | lia | reflexivity ].
        apply (prf_st_sy mtl tl (cur + 2 * u) [1; 0] _ 1); [ | lia | lia | lia ].
        apply (prf_st_nb mtl tl (cur + 2 * u) [0] _ 1); [ | lia | lia | lia | rewrite ?Zupd_length2; lia | lia ].
        apply (prf_st_sy mtl tl (cur + 2 * u) [0] _ 0); [ | lia | lia | lia ].
        apply (prf_st_nb mtl tl (cur + 2 * u) [] _ 0); [ apply prf_open; exact PF | lia | lia | lia | rewrite ?Zupd_length2; lia | lia ].
  Qed.
  Definition x1_c2_loopA_stmt : Prop := forall (f : nat) m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb u : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 xa1 xa2 xa3 xa5 xs2 xs4 xs5 xs10 xs11 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 2 ->
    nb = tl + 1 - w -> 0 <= u -> u + Z.of_nat (S f) = cnt -> x1pref mtl tl (cur + 2 * u) dt ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 2) dt' ->
       evtF bsegs RNG POST (STL m2 2 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST2 m1 nb sym cur cnt u xra x5 xa1 xa2 xa3 xa5 xs2 xs4 xs5 xs10 xs11 x31).
  Lemma x1_c2_loopA_of : x1_c2_bodyA_stmt -> x1_c2_loopA_stmt.
  Proof.
    intros BODY f. induction f as [|f IH]; intros until x31; intros I HW HC HS HCN HL2 HNB HS0 HF PF KE.
    - eapply (BODY m1 j0 j192 dt rst syb w cur sym cnt nb u); [exact I| exact HW| exact HC| exact HS| exact HCN| exact HL2| exact HNB| lia| exact PF| intros; exfalso; lia|].
      intros m2 dt' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 _ I2 PF2. eapply KE; [exact I2| exact PF2].
    - eapply (BODY m1 j0 j192 dt rst syb w cur sym cnt nb u); [exact I| exact HW| exact HC| exact HS| exact HCN| exact HL2| exact HNB| lia| exact PF| | intros; exfalso; lia].
      intros m2 dt' y5 ya1 ya2 ya3 ya5 y31 Hu I2 PF2.
      eapply (IH m2 j0 j192 dt' rst syb w cur sym cnt nb (u + 1)); [exact I2| exact HW| exact HC| exact HS| exact HCN| exact HL2| exact HNB| lia| lia| exact PF2| exact KE].
  Qed.
  Definition x1_c2A_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 2 ->
    nb = tl + 1 - w -> x1pref mtl tl cur dt ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 2) dt' ->
       evtF bsegs RNG POST (STL m2 2 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STC 0x81098 m1 nb 2 xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Lemma x1_c2A : x1_c2A_stmt.
  Proof.
    unfold x1_c2A_stmt. intros until x31. intros I HW HC HS HCN HL2 HNB PF KE.
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite HL2 in CL0, CLH. rewrite <- HC, <- HS, <- HCN in *.
    pose proof I as I0. open_xc I0. x1_hy HY.
    assert (CR : 0 <= cur <= 4096) by lia. assert (SYR : 0 <= sym <= 256) by lia.
    assert (NBR : 1 <= nb <= 12) by lia.
    destruct (Z.eq_dec cnt 0) as [C0|C0].
    - 
      kx_runFm [0x810f0; 0x81964; 0x80618; 0x819cc] 10%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256; KZRange nb 1 12; KZRange cnt 0 0;
         KZWord (SPA + 152) 8 cnt]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      1: (unfold accP; cbn [fst snd]; lazymatch goal with |- RNG (bv_unsigned (adenot ?E _)) _ => xa_norm E end;
          unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
          apply RLO; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      kx_post_regs. cbn [mem_denot]. negfix.
      apply (KE m1 dt); [exact I | replace (cur + cnt * 2) with cur by lia; exact PF].
    - kx_runFm [0x810f0; 0x81964; 0x80618; 0x819cc] 40%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256;
         KZRange cnt 1 256; KZRange nb 1 12; KZRange (256 - sym) 1 256;
         KZWord (SPA + 152) 8 cnt; KZWord (SPA + 88) 8 sym; KZWord (SPA + 80) 8 cur;
         KZWord (SPA + 64) 8 DT; KZWord (SPA + 184) 8 (DT + 4)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      all: try (unfold accP; cbn [fst snd]; lazymatch goal with |- RNG (bv_unsigned (adenot ?E _)) _ => xa_norm E end;
            unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
            apply RLO; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      kx_post_regs. cbn [mem_denot]. negfix.
      lazymatch goal with |- evtF ?ga ?gb ?gc ?s1 =>
        let H := fresh "HS" in
        assert (H : forall s2, s2 = s1 -> evtF ga gb gc s2 -> evtF ga gb gc s1) by (intros ? -> ?; assumption);
        eapply H; clear H; [ | eapply (x1_c2_loopA_of x1_c2_bodyA (Z.to_nat (cnt - 1)) m1 j0 j192 dt rst syb w cur sym cnt nb 0) ] end.
      + (f_equal; f_equal; try reflexivity; try (f_equal; lia)).
      + exact I.
      + exact HW.
      + exact HC.
      + exact HS.
      + exact HCN.
      + exact HL2.
      + exact HNB.
      + lia.
      + rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
      + replace (cur + 2 * 0) with cur by lia. exact PF.
      + exact KE.
  Qed.
  Notation ST1 mm nb sym cur cnt u xra x5 xa1 xa2 xs2 xs4 xs5 xs10 xs11 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 (Z_to_bv 64 (2 * (2147483647 - cur))) (Z_to_bv 64 (2 * (256 - sym))) (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             (Z_to_bv 64 (2 * u)) xa1 xa2 (Z_to_bv 64 nb) (Z_to_bv 64 (sym + u)) (Z_to_bv 64 (DT + 2 * cur)) (Z_to_bv 64 (cur + u)) (Z_to_bv 64 (DT + 4 + 2 * cur))
             xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5 (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 1) xs10 xs11
             (Z_to_bv 64 (2 * cnt)) x29 x30 x31)
        F (Z_to_bv 64 0x81748) fc None mm (seg_rom bsegs)).
  Definition x1_c1_bodyA_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb u : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 xa1 xa2 xs2 xs4 xs5 xs10 xs11 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 1 ->
    nb = tl + 1 - w -> 0 <= u < cnt -> x1pref mtl tl (cur + u) dt ->
    (forall m2 (dt' : list Z) (y5 ya1 ya2 y29 y30 y31 : word), u + 1 < cnt -> XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 -> x1pref mtl tl (cur + (u + 1)) dt' ->
       evtF bsegs RNG POST (ST1 m2 nb sym cur cnt (u + 1) xra y5 ya1 ya2 xs2 xs4 xs5 xs10 xs11 y29 y30 y31)) ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), u + 1 = cnt -> XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 1) dt' ->
       evtF bsegs RNG POST (STL m2 1 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST1 m1 nb sym cur cnt u xra x5 xa1 xa2 xs2 xs4 xs5 xs10 xs11 x29 x30 x31).
  Lemma x1_c1_bodyA : x1_c1_bodyA_stmt.
  Proof.
    unfold x1_c1_bodyA_stmt. intros until x31. intros I HW HC HS HCN HL1 HNB HU PF KH KE.
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite HL1 in CL0, CLH. rewrite <- HC, <- HS, <- HCN in *.
    pose proof I as I0. open_xc I0. x1_hy HY.
    assert (UDT1 : unpoisoned m1 DT (DT + DTB)) by (eapply x1_unp_dtM; eassumption).
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply x1_unp_wkM; eassumption).
    assert (CR : 0 <= cur <= 4096) by lia. assert (SYR : 0 <= sym <= 256) by lia. assert (NR : 1 <= cnt <= 256) by lia.
    assert (NBR : 1 <= nb <= 12) by lia. assert (UR : 0 <= u <= 255) by lia.
    assert (SSY : sym + u < 256) by lia. assert (CU : cur + u < 4096) by lia.
    assert (DTW : DT + 4 + 2 * cur + 2 * u + 2 <= DT + DTB) by lia.
    unfold shspan in RSDT, RSWK.
    assert (LSY : Z.of_nat (length syb) = 256) by exact SYLEN.
    assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = DTB) by (rewrite length_map; exact DTLEN).
    assert (CK : u + 1 < cnt \/ u + 1 = cnt) by lia. destruct CK as [CK|CK].
    - kx_runFm [0x81748; 0x81964; 0x80618; 0x819cc] 60%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256;
         KZRange cnt 1 256; KZRange nb 1 12; KZRange u 0 255; KZRange (sym + u) 0 255; KZRange (cur + u) 0 4095;
         KZRange (cnt - u - 2) 0 254; KZWr (DT + 4 + 2 * cur + 2 * u) 2;
         KZWord (SPA + 168) 8 (18446744073709551615 - (WK + 980)); KZWord (SPA + 176) 8 (WK + 980); KZWord (SPA + 184) 8 (DT + 4)]
        [(WK + 980 + sym + u, 1)] [(DT + 4 + 2 * cur + 2 * u, 2)] [(WK + 980 + sym + u, 1); (DT + 4 + 2 * cur + 2 * u, 2)].
      all: try w4br.
      all: try w4neq.
      1-4: (unfold accP; cbn [fst snd]; lazymatch goal with |- RNG (bv_unsigned (adenot ?E _)) _ => xa_norm E end;
            unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
            first [ apply RLO; cbn [Z.of_nat Pos.of_succ_nat]; lia | apply RWK; cbn [Z.of_nat Pos.of_succ_nat]; lia ]).
      kx_post_regs.
      lazymatch goal with |- context [mem_denot _ _ (SE _ _ (EVar ?k) :: _)] =>
        kx_range (EVar k) RB; set (b := bv_unsigned (ev KXE k)) in * end.
      cbn [mem_denot]. negfix. xa_norm KXE.
      rewrite !wbytes_eq. change (word_to_le_bytes 1) with le1.
      replace (2 * cur + (2 * u + DT) + 5) with (2 * cur + (2 * u + DT) + 4 + 1) by lia.
      pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (2 * cur + (2 * u + DT) + 4) (nb + 256 * b) nb I ltac:(lia) (mod256_lo nb b) ltac:(lia)) as XC1.
      pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (2 * cur + (2 * u + DT) + 4 + 1) b b XC1 ltac:(lia) eq_refl ltac:(lia)) as XC2.
      lazymatch goal with |- evtF ?ga ?gb ?gc ?s1 =>
        let H := fresh "HS" in
        assert (H : forall s2, s2 = s1 -> evtF ga gb gc s2 -> evtF ga gb gc s1) by (intros ? -> ?; assumption);
        eapply H; clear H; [ | eapply (KH _ (Zupd (2 * cur + (2 * u + DT) + 4 + 1 - DT) b (Zupd (2 * cur + (2 * u + DT) + 4 - DT) nb dt))) ] end.
      + f_equal; f_equal; first [reflexivity | f_equal; lia].
      + exact CK.
      + exact XC2.
      +
        replace (cur + (u + 1)) with (cur + u + Z.of_nat 1) by lia.
        apply (prf_close_c mtl tl (cur + u) [0]); [ | lia | reflexivity ].
        apply (prf_st_sy mtl tl (cur + u) [0] _ 0); [ | lia | lia | lia ].
        eapply prf_st_nb; [ apply prf_open; exact PF | lia | lia | lia | | lia ].
        lia.
    - rewrite <- CK.
      kx_runFm [0x81748; 0x81964; 0x80618; 0x819cc] 60%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256;
         KZRange nb 1 12; KZRange u 0 255; KZRange (sym + u) 0 255; KZRange (cur + u) 0 4095;
         KZWr (DT + 4 + 2 * cur + 2 * u) 2;
         KZWord (SPA + 168) 8 (18446744073709551615 - (WK + 980)); KZWord (SPA + 176) 8 (WK + 980); KZWord (SPA + 184) 8 (DT + 4)]
        [(WK + 980 + sym + u, 1)] [(DT + 4 + 2 * cur + 2 * u, 2)] [(WK + 980 + sym + u, 1); (DT + 4 + 2 * cur + 2 * u, 2)].
      all: try w4br.
      all: try w4neq.
      1-4: (unfold accP; cbn [fst snd]; lazymatch goal with |- RNG (bv_unsigned (adenot ?E _)) _ => xa_norm E end;
            unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
            first [ apply RLO; cbn [Z.of_nat Pos.of_succ_nat]; lia | apply RWK; cbn [Z.of_nat Pos.of_succ_nat]; lia ]).
      kx_post_regs.
      lazymatch goal with |- context [mem_denot _ _ (SE _ _ (EVar ?k) :: _)] =>
        kx_range (EVar k) RB; set (b := bv_unsigned (ev KXE k)) in * end.
      cbn [mem_denot]. negfix. xa_norm KXE.
      rewrite !wbytes_eq. change (word_to_le_bytes 1) with le1.
      replace (2 * cur + (2 * u + DT) + 5) with (2 * cur + (2 * u + DT) + 4 + 1) by lia.
      pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (2 * cur + (2 * u + DT) + 4) (nb + 256 * b) nb I ltac:(lia) (mod256_lo nb b) ltac:(lia)) as XC1.
      pose proof (XC_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (2 * cur + (2 * u + DT) + 4 + 1) b b XC1 ltac:(lia) eq_refl ltac:(lia)) as XC2.
      lazymatch goal with |- evtF ?ga ?gb ?gc ?s1 =>
        let H := fresh "HS" in
        assert (H : forall s2, s2 = s1 -> evtF ga gb gc s2 -> evtF ga gb gc s1) by (intros ? -> ?; assumption);
        eapply H; clear H; [ | eapply (KE _ (Zupd (2 * cur + (2 * u + DT) + 4 + 1 - DT) b (Zupd (2 * cur + (2 * u + DT) + 4 - DT) nb dt))) ] end.
      + f_equal; f_equal; first [reflexivity | f_equal; lia].
      + exact CK.
      + exact XC2.
      + replace (cur + cnt * 1) with (cur + (u + 1)) by lia.
        replace (cur + (u + 1)) with (cur + u + Z.of_nat 1) by lia.
        apply (prf_close_c mtl tl (cur + u) [0]); [ | lia | reflexivity ].
        apply (prf_st_sy mtl tl (cur + u) [0] _ 0); [ | lia | lia | lia ].
        eapply prf_st_nb; [ apply prf_open; exact PF | lia | lia | lia | | lia ].
        lia.
  Qed.
  Definition x1_c1_loopA_stmt : Prop := forall (f : nat) m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb u : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 xa1 xa2 xs2 xs4 xs5 xs10 xs11 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 1 ->
    nb = tl + 1 - w -> 0 <= u -> u + Z.of_nat (S f) = cnt -> x1pref mtl tl (cur + u) dt ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 1) dt' ->
       evtF bsegs RNG POST (STL m2 1 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST1 m1 nb sym cur cnt u xra x5 xa1 xa2 xs2 xs4 xs5 xs10 xs11 x29 x30 x31).
  Lemma x1_c1_loopA_of : x1_c1_bodyA_stmt -> x1_c1_loopA_stmt.
  Proof.
    intros BODY f. induction f as [|f IH]; intros until x31; intros I HW HC HS HCN HL1 HNB HS0 HF PF KE.
    - eapply (BODY m1 j0 j192 dt rst syb w cur sym cnt nb u); [exact I| exact HW| exact HC| exact HS| exact HCN| exact HL1| exact HNB| lia| exact PF| intros; exfalso; lia|].
      intros m2 dt' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 _ I2 PF2. eapply KE; [exact I2| exact PF2].
    - eapply (BODY m1 j0 j192 dt rst syb w cur sym cnt nb u); [exact I| exact HW| exact HC| exact HS| exact HCN| exact HL1| exact HNB| lia| exact PF| | intros; exfalso; lia].
      intros m2 dt' y5 ya1 ya2 y29 y30 y31 Hu I2 PF2.
      eapply (IH m2 j0 j192 dt' rst syb w cur sym cnt nb (u + 1)); [exact I2| exact HW| exact HC| exact HS| exact HCN| exact HL1| exact HNB| lia| lia| exact PF2| exact KE].
  Qed.
  Definition x1_c1A_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> hw_cells w = 1 ->
    nb = tl + 1 - w -> x1pref mtl tl cur dt ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), XCm j0 j192 dt' rst syb w cur sym cnt k112 k120 k128 k136 k144 m2 ->
       x1pref mtl tl (cur + cnt * 1) dt' ->
       evtF bsegs RNG POST (STL m2 1 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs4 xs5 xs10 xs11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STC 0x816e0 m1 nb 1 xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Lemma x1_c1A : x1_c1A_stmt.
  Proof.
    unfold x1_c1A_stmt. intros until x31. intros I HW HC HS HCN HL1 HNB PF KE.
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite HL1 in CL0, CLH. rewrite <- HC, <- HS, <- HCN in *.
    pose proof I as I0. open_xc I0. x1_hy HY.
    assert (CR : 0 <= cur <= 4096) by lia. assert (SYR : 0 <= sym <= 256) by lia.
    assert (NBR : 1 <= nb <= 12) by lia.
    destruct (Z.eq_dec cnt 0) as [C0|C0].
    - 
      kx_runFm [0x81748; 0x81964; 0x80618; 0x819cc] 10%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256; KZRange nb 1 12; KZRange cnt 0 0;
         KZWord (SPA + 152) 8 cnt]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      1: (unfold accP; cbn [fst snd]; lazymatch goal with |- RNG (bv_unsigned (adenot ?E _)) _ => xa_norm E end;
          unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
          apply RLO; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      kx_post_regs. cbn [mem_denot]. negfix.
      apply (KE m1 dt); [exact I | replace (cur + cnt * 1) with cur by lia; exact PF].
    - kx_runFm [0x81748; 0x81964; 0x80618; 0x819cc] 40%nat
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange cur 0 4096; KZRange sym 0 256;
         KZRange cnt 1 256; KZRange nb 1 12; KZRange (256 - sym) 1 256;
         KZWord (SPA + 152) 8 cnt; KZWord (SPA + 88) 8 sym; KZWord (SPA + 80) 8 cur; KZWord (SPA + 16) 8 18446744071562067967;
         KZWord (SPA + 64) 8 DT; KZWord (SPA + 184) 8 (DT + 4)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      all: try (unfold accP; cbn [fst snd]; lazymatch goal with |- RNG (bv_unsigned (adenot ?E _)) _ => xa_norm E end;
            unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
            apply RLO; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      kx_post_regs. cbn [mem_denot]. negfix.
      lazymatch goal with |- evtF ?ga ?gb ?gc ?s1 =>
        let H := fresh "HS" in
        assert (H : forall s2, s2 = s1 -> evtF ga gb gc s2 -> evtF ga gb gc s1) by (intros ? -> ?; assumption);
        eapply H; clear H; [ | eapply (x1_c1_loopA_of x1_c1_bodyA (Z.to_nat (cnt - 1)) m1 j0 j192 dt rst syb w cur sym cnt nb 0) ] end.
      + (f_equal; f_equal; try reflexivity; try (f_equal; lia)).
        (xa_norm KXE; cbn [edenot]; rewrite (kE_atoms _ _ 27) by (cbn; lia); cbn [nth]; rewrite u_xor64, ?Z_to_bv_unsigned).
        f_equal. assert (CR' : 0 <= cur <= 4096) by lia. revert CR'. generalize cur. intros c Hc.
        lazymatch goal with |- ?l = ?r =>
          let tl := eval pattern c in l in let tr := eval pattern c in r in
          lazymatch tl with ?g _ => lazymatch tr with ?h _ =>
            change (g c = h c); (apply (brute_eq g h); [vm_compute; reflexivity | exact Hc]) end end end.
      + exact I.
      + exact HW.
      + exact HC.
      + exact HS.
      + exact HCN.
      + exact HL1.
      + exact HNB.
      + lia.
      + rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
      + replace (cur + 0) with cur by lia. exact PF.
      + exact KE.
  Qed.
  End C12.
End X1B.
End CANSEC1.
