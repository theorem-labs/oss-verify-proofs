(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_globals AZ_globalsR AZ_findfsi_a AZ_findfsi_b AZ_findfsi_c AZ_finddsize_a AZ_finddsize_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation SHB := 2147450880.
Notation KM8 := 18446744073709551608.
Notation K9 := 4294967287.
Notation KSK := (Z_to_bv 64 25481893).

Section CANSEC1. Context {rc : runConstT}.

Section FD.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA SRC : Z) (src : list Z) (size0 lo FF SHF FLG : Z).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size0.
  Hypothesis N40 : size0 < 1099511627776.
  Hypothesis NLEN : size0 <= zlen src.
  Hypothesis SRCE : SRC + zlen src < 2^64.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 4672 /\ SPV - 208 <= SPA <= SPV - 192 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC).
  Hypothesis G_ff : ablk FF (FF + 128) /\ FF mod 128 = 0 /\ FF + 128 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 128 <= al_fake L + FAKESZ
                    /\ (SRC + zlen src <= FF \/ FF + 128 <= SRC).
  Hypothesis G_flg : FLG = fflag L 1 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB1 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_ff : rng RNG FF 128 /\ rng RNG SHF 16 /\ rng RNG FLG 1.
  Hypothesis R_fsi : rng RNG (shad (SPA + 64)) (shspan (SPA + 64) 24).
  Hypothesis LBH : ablkLB LB.
  (* [comment removed for export] *)
  Variable SZB : Z.

  Notation POST := (zd_finddsize_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV src size0 lo m0).
  Notation RES := (find_decompressed_size src size0).
  Notation BINV := (AZ_finddsize_a.BINV AI L RNG st LB m0 SPV FF).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 KM8) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation XINVg := (AZ_finddsize_b.XINVg AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA SRC src lo FF SHF FLG).
  Notation XINV := (XINVg DSH0).


  (* [comment removed for export] *)
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis GETFH : zd_getfh_stmtA AI rng_fs.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis ASH : ashort LB 3.
  Hypothesis RFS : rng_fs L RNG.
  Hypothesis SPT : SPV + 16 < al_top L.
  Hypothesis RSTKT : rng RNG lo (al_top L - lo).
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis INS : 0 < zlen src -> ainimg LB SRC (zlen src).

  (* [comment removed for export] *)
  Hypothesis PXEXIT : forall sh m1 r (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x27 x28 x29 x30 x31 : word),
    XINVg sh m1 -> cells_size sh = 16%nat -> Z_to_bv 64 r = Z_to_bv 64 RES ->
    evtF bsegs RNG POST (STpc 0x83dac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 r) x27 x28 x29 x30 x31).
  Hypothesis PXHERR : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 : word),
    XINVg DSHZ m1 -> RES = ZD_CONTENTSIZE_ERROR ->
    evtF bsegs RNG POST (STpc 0x84074 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31).
  Hypothesis PFSI : forall m1 off sz total v (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    XINV m1 -> 5 <= sz -> 0 <= off -> off + sz <= size0 -> 0 <= total < 18446744073709551616 ->
    RES = (if zd_is_error (find_frame_compressed_size src off sz) then ZD_CONTENTSIZE_ERROR
           else find_dsize src (off + find_frame_compressed_size src off sz) (sz - find_frame_compressed_size src off sz) total) ->
    Z_to_bv 64 v = Z_to_bv 64 ZD_CONTENTSIZE_ERROR -> sz <= SZB ->
    evtF bsegs RNG POST (STpc 0x83f94 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              (Z_to_bv 64 v) (Z_to_bv 64 total) x28 x29 x30 x31).

  Ltac gf_unhold := unfold fk_held in *.
  Ltac fd_geom :=
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6); pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7);
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4); pose proof G_src as (S1 & S2); pose proof R_src as (RS1 & RS2); pose proof R_ff as (RF1 & RF2 & RF3);
    let ATR := fresh "ATR" in pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
    let FL := fresh "FL" in let SL := fresh "SL" in let LL := fresh "LL" in
    pose proof (fk_ablk_lits _ _ (proj1 G_ff)) as FL; pose proof (fk_ablk_lits _ _ (proj1 G_src)) as SL; pose proof (fk_ablk_lits _ _ (proj1 (proj2 G_flg))) as LL;
    let ESHF := fresh "ESHF" in let GS := fresh "GS" in
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite (proj1 (proj2 (proj2 (proj2 G_ff)))), shad_div; reflexivity);
    assert (GS : SHB + 805376 <= SHF /\ SHF + 16 <= 17594333495296) by (rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia);
    assert (FFSH : FF + 128 <= SHF \/ SHF + 16 <= FF) by (clear - FL GS ATR; lia);
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 16 <= FLG) by (clear - LL GS ATR; lia);
    assert (SSH : SRC + zlen src <= SHF \/ SHF + 16 <= SRC) by (clear - SL GS ATR; lia);
    let FLA := fresh "FLA" in pose proof ((proj2 (proj2 (proj2 (proj2 G_flg)))) _ ltac:(left; reflexivity)) as FLA; cbn [ab_addr ab_size] in FLA.

  (* [comment removed for export] *)
  Lemma dshz_rd : forall (m : amem) k, rw_cells bsegs m (shad FF) DSHZ -> 0 <= FF -> 0 <= k < 6 ->
    m (wa (ASHOFF + FF / 8 + 4 + k)) = Some (Z_to_bv 8 0).
  Proof.
    intros m k H F0 Hk. unfold DSHZ in H. rewrite shad_div in H.
    apply (proj1 (rw_cells_app bsegs _ _ [C1 BF1; C1 BF1; C1 BF1; C1 BF1] _)) in H. destruct H as [_ H].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
    assert (STEP : forall a cs, rw_cells bsegs m a (C1 B00 :: cs) -> 0x625000 <= a -> m (wa a) = Some (Z_to_bv 8 0) /\ rw_cells bsegs m (a + 1) cs).
    { intros a cs Hc Ha. apply (proj1 (rw_cells_app bsegs _ _ [C1 B00] cs)) in Hc. destruct Hc as [Hx Hy].
      split; [exact (fk_byte_of_c1 m _ _ Hx Ha)| exact Hy]. }
    destruct (STEP _ _ H ltac:(unfold ASHOFF; lia)) as [R0 H1]. destruct (STEP _ _ H1 ltac:(unfold ASHOFF; lia)) as [R1 H2].
    destruct (STEP _ _ H2 ltac:(unfold ASHOFF; lia)) as [R2 H3]. destruct (STEP _ _ H3 ltac:(unfold ASHOFF; lia)) as [R3 H4].
    destruct (STEP _ _ H4 ltac:(unfold ASHOFF; lia)) as [R4 H5]. destruct (STEP _ _ H5 ltac:(unfold ASHOFF; lia)) as [R5 _].
    assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
    destruct E as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      [ rewrite <- R0 | rewrite <- R1 | rewrite <- R2 | rewrite <- R3 | rewrite <- R4 | rewrite <- R5 ]; f_equal; f_equal; lia.
  Qed.
  Lemma dshz_unp : forall (m : amem), rw_cells bsegs m (shad FF) DSHZ -> FF mod 8 = 0 -> 0 <= FF -> FF + 128 <= 2^47 ->
    unpoisoned m (FF + 32) (FF + 32 + 48).
  Proof.
    intros m H F8 F0 FH. split; [lia|]. split; [lia|]. intros G HG H1 H2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    replace (ASHOFF + G) with (ASHOFF + FF / 8 + 4 + (G - FF / 8 - 4)) by lia. apply (dshz_rd m (G - FF / 8 - 4) H F0). Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xinv_rep : forall (m m' : amem), XINVg DSHZ m -> munch [(SHF, SHF + 16)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
    rw_cells bsegs m' SHF DSH0 -> XINV m'.
  Proof.
    intros m m' (BI & SAV & [jA FRA] & [jB FRB] & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO) MUL WML MI' XS'.
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI). fd_geom.
    assert (F0' : 6443008 <= FF) by (clear - FL; lia).
    assert (DJ : forall X k, SPA <= X -> 0 <= k -> disjoint_from [(SHF, SHF + 16)] X k)
      by (intros X k H1 Hk; cbn [disjoint_from]; clear - H1 Hk GS G2 G3 KLO; unfold KHIGH in KLO; split; [lia| exact I]).
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]]].
    - split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | exact MI']]]].
      + eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
        constructor; [cbn [fst snd] | constructor].
        rewrite F4. replace (shad FF + 16 - shad FF) with 16 by (clear; lia).
        eapply (fk_acr_fshadow AI _ 1 FF 128 FF 16); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - F0'; lia].
      + eapply ffr_pres_trans; [exact FFR1|].
        eapply (fk_ffr_fin AI L RNG st LB m m m' 1 FF 128 SHF 16 [] []);
          [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
          | constructor | constructor | apply ffr_pres_refl
          | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
          | exact WML ].
      + eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
        destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *.
        assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
        clear - Hx F5 F6 L3a L3b FA8 F2. Z.div_mod_to_equations. lia.
    - eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | apply DJ; [clear - G3; lia| clear; lia]].
    - exists jA. eapply rw_cells_transport; [exact FRA | exact MUL | exact WML | apply DJ; clear; lia].
    - exists jB. eapply rw_cells_transport; [exact FRB | exact MUL | exact WML | apply DJ; clear; lia].
    - exists jC. eapply rw_cells_transport; [exact FRC | exact MUL | exact WML | apply DJ; clear; lia].
    - eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - GS G2 KLO; unfold KHIGH in KLO; lia].
    - eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | apply DJ; clear - G3; lia].
    - exists jH. eapply rw_cells_transport; [exact XH | exact MUL | exact WML | cbn; clear - FFSH; lia].
    - eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLSH; lia].
    - exact XS'.
    - eapply bytes_at_transport; [exact SB1 | exact MUL | rewrite length_map; cbn; clear - SSH; lia].
    - eapply unpoisoned_munch; [exact US | exact MUL |]. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
      clear - F7 F2 SL DB. split; [| exact I]. Z.div_mod_to_equations. lia.
    - eapply unpoisoned_munch; [exact UP | exact MUL |]. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      clear - G1 G2 G3 F3 ATR. split; [| exact I]. Z.div_mod_to_equations. lia.
    - eapply aro_client_transport_gen; [exact WML | exact ARO | exact MUL |]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      clear - B1 B2 B3 FL. split; [| exact I]. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_join : forall m1 off sz total fcs (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    XINV m1 -> 5 <= sz -> 0 <= off -> off + sz <= size0 -> 0 <= total < 18446744073709551616 -> 0 <= fcs < 18446744073709551614 ->
    RES = (if 18446744073709551616 <=? total + fcs then ZD_CONTENTSIZE_ERROR
           else if zd_is_error (find_frame_compressed_size src off sz) then ZD_CONTENTSIZE_ERROR
           else find_dsize src (off + find_frame_compressed_size src off sz) (sz - find_frame_compressed_size src off sz) (total + fcs)) ->
    sz <= SZB ->
    evtF bsegs RNG POST (STpc 0x83f88 m1 x1 x5 x6 x7 (Z_to_bv 64 fcs) x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 total) x28 x29 x30 x31).
  Proof.
    intros m1 off sz total fcs x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 XI R5 ROFF RSZ RT RFCS ER RB.
    pose proof XI as (BI & REST). destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    fk_hold XI. fk_hold REST. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold ER.
    fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS.
    (* [comment removed for export] *)
    assert (TL : evtF bsegs RNG POST (STpc 0x83f8c m1 x1 x5 x6 x7 (Z_to_bv 64 fcs) x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 (fcs + total)) x28 x29 x30 x31)).
    {
      zstep.                                               (* [comment removed for export] *)
      zstep. if_cases KO; zify_cond KO.                    (* [comment removed for export] *)
      - (* [comment removed for export] *)
        gf_unhold. eapply PXEXIT; [exact XI | reflexivity |].
        rewrite ER. replace (18446744073709551616 <=? total + fcs) with true
          by (symmetry; apply Z.leb_le; destruct (Z.lt_ge_cases (total + fcs) 18446744073709551616) as [Lt|Lt]; [rewrite Z.mod_small in KO by (clear - Lt RT RFCS; lia); exfalso; clear - KO RT; lia| exact Lt]).
        apply Z_to_bv_eqm. reflexivity.
      - assert (NOV : total + fcs < 18446744073709551616).
        { destruct (Z.lt_ge_cases (total + fcs) 18446744073709551616) as [Lt|Lt]; [exact Lt| exfalso].
          assert (E : (fcs + total) mod 18446744073709551616 = fcs + total - 18446744073709551616) by (symmetry; apply Z.mod_unique with 1; clear - Lt RT RFCS; lia).
          clear - KO E Lt RT RFCS. lia. }
        replace (18446744073709551616 <=? total + fcs) with false in ER by (symmetry; apply Z.leb_gt; clear - NOV; lia).
        replace (fcs + total) with (total + fcs) by (clear; lia).
        gf_unhold. eapply (PFSI m1 off sz (total + fcs) (-2)); [exact XI | exact R5 | exact ROFF | exact RSZ | clear - NOV RT RFCS; lia | exact ER | apply Z_to_bv_eqm; reflexivity | exact RB]. }
    zstep.                                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try (let w := getreg 27 in replace w with (Z_to_bv 64 (fcs + total)) by (first [f_equal; clear; lia | apply Z_to_bv_eqm; clear; lia])).
    exact TL.
  Qed.

  (* [comment removed for export] *)
  Lemma p_reg : forall m1 off sz total (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    XINV m1 -> 5 <= sz -> 0 <= off -> off + sz <= size0 ->
    RES = find_dsize src off sz total -> 0 <= total < 18446744073709551616 -> is_skippable_magic (le32 src off) = false -> sz <= SZB ->
    evtF bsegs RNG POST (STpc 0x83f04 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 total) x28 x29 x30 x31).
  Proof.
    intros m1 off sz total x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 XI R5 ROFF RSZ ER RT SK RB.
    pose proof XI as (BI & SAV & [jA FRA] & [jB FRB] & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO).
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    fd_geom.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (NZ : 0 < zlen src) by (clear - RSZ R5 ROFF NLEN; lia).
    assert (OFS : off + sz <= zlen src) by (clear - RSZ NLEN; lia).
    destruct (FHL _ _ _ _ _ AH1) as [FAB FABD]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH1) as (LY1 & LY2 & LY3 & LY4 & LY5).
    (* [comment removed for export] *)
    rewrite (find_dsize_eq src OK) in ER by (change (2^64) with 18446744073709551616; clear - RSZ N40 ROFF; lia).
    unfold ZD_FRAMEHEADERSIZE_PREFIX in ER. replace (sz <? 5) with false in ER by (symmetry; apply Z.ltb_ge; clear - R5; lia).
    rewrite SK in ER. cbv zeta in ER.
    unfold DSH0 in XS.
    pose proof (munch_refl [(SHF, SHF + 16)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS. fk_hold ASH.
    fk_hold XI. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold SAV. fk_hold FRA. fk_hold FRB. fk_hold FRC. fk_hold STL. fk_hold STG. fk_hold XH. fk_hold XL. fk_hold SB1. fk_hold US. fk_hold UP. fk_hold ARO.
    fk_hold L4. fk_hold FABD. fk_hold LY5. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FABL. fk_hold FLA. fk_hold S2. fk_hold F7. fk_hold ER.
    fk_hold FFSH. fk_hold FLSH. fk_hold SSH.
    do 6 zstep.                                            (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    change (rw_cells bsegs m2 SHF DSHZ) in XS.
    gf_unhold.
    assert (AH2 : AHEAP AI L RNG st (FB1 FF :: LB) m2).
    { eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd] | constructor].
      rewrite F4. replace (shad FF + 16 - shad FF) with 16 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 1 FF 128 FF 16); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia]. }
    assert (DJ : forall X k, SPA <= X -> 0 <= k -> disjoint_from [(SHF, SHF + 16)] X k)
      by (intros X k H1 Hk; cbn [disjoint_from]; clear - H1 Hk GS G2 G3 KLO; unfold KHIGH in KLO; split; [lia| exact I]).
    assert (SAV2 : rw_cells bsegs m2 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | apply DJ; [clear - G3; lia| clear; lia]]).
    assert (FRA2 : rw_cells bsegs m2 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)]) by (eapply rw_cells_transport; [exact FRA | exact MUL | exact WML | apply DJ; clear; lia]).
    assert (FRB2 : rw_cells bsegs m2 (SPA + 24) [C8 (Z_to_bv 64 K9); CB 24 jB; C8 (Z_to_bv 64 FF)]) by (eapply rw_cells_transport; [exact FRB | exact MUL | exact WML | apply DJ; clear; lia]).
    assert (FRC2 : rw_cells bsegs m2 (SPA + 64) [CB 24 jC]) by (eapply rw_cells_transport; [exact FRC | exact MUL | exact WML | apply DJ; clear; lia]).
    assert (STL2 : stk bsegs m2 lo SPA) by (eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - GS G2 KLO; unfold KHIGH in KLO; lia]).
    assert (STG2 : stk bsegs m2 (SPA + 88) (SPV + -104)) by (eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | apply DJ; clear - G3; lia]).
    assert (XH2 : rw_cells bsegs m2 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 96 jH; C8 (Z_to_bv 64 FLG)])
      by (eapply rw_cells_transport; [exact XH | exact MUL | exact WML | cbn; clear - FFSH; lia]).
    assert (XL2 : rw_cells bsegs m2 FLG [C1 (Z_to_bv 8 1)]) by (eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLSH; lia]).
    assert (SB2 : bytes_at bsegs m2 SRC (map (Z_to_bv 8) src)) by (eapply bytes_at_transport; [exact SB1 | exact MUL | rewrite length_map; cbn; clear - SSH; lia]).
    assert (US2 : unpoisoned m2 SRC (SRC + zlen src)).
    { eapply unpoisoned_munch; [exact US | exact MUL |]. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF.
      unfold ASHOFF. clear - F7 F2 SL NZ. split; [| exact I]. Z.div_mod_to_equations. lia. }
    assert (UP2 : unpoisoned m2 (SPA + 64) (SPA + 88)).
    { eapply unpoisoned_munch; [exact UP | exact MUL |]. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      clear - G1 G2 G3 F3 ATR. split; [| exact I]. Z.div_mod_to_equations. lia. }
    assert (ARO2 : aro_client RNG m2).
    { eapply aro_client_transport_gen; [exact WML | exact ARO | exact MUL |]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      clear - B1 B2 B3 FL. split; [| exact I]. Z.div_mod_to_equations. lia. }
    clear SAV FRA FRB FRC STL STG XL SB1 US UP ARO. rename MUL into MU12. rename WML into WM12.
    assert (LBH' : ablkLB (FB1 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    assert (ASH' : ashort (FB1 FF :: LB) 1) by (apply ashort_push; [eapply ashort_mono; [exact ASH| clear; lia]| clear; lia]).
    assert (ART2 : art m2).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH2) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (AFP : afpre AI rng_fs L RNG st (FB1 FF :: LB) m2 lo SPA 1).
    { unfold afpre, astk. split; [exact AH2|]. split; [exact ASH'|]. split; [exact ART2|].
      split; [split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact G1|]. split; [clear - G3 SPT; lia|]. split; [clear - G4; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH']. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c)] 96 jH [C8 (Z_to_bv 64 FLG)] [8; 48; 40]%nat) in XH2; [| reflexivity].
    cbn [mk_CB_cells app] in XH2.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 8 (firstn 8 jH)] _) XH2) as [XHA XHB].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XHB.
    pose proof (proj1 (rw_cells_app bsegs _ _ [CB 48 (firstn 48 (skipn 8 jH))] _) XHB) as [XZ XHC].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XZ, XHC.
    match type of XZ with rw_cells _ _ ?a _ => replace a with (FF + 32) in XZ by (clear; lia) end.
    match type of XHC with rw_cells _ _ ?a _ => replace a with (FF + 80) in XHC by (clear; lia) end.
    clear XH2 XHB.
    assert (UZ2 : unpoisoned m2 (FF + 32) (FF + 32 + 48)).
    { apply (dshz_unp m2); [rewrite <- F4; exact XS | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia | clear - FL ATR; lia]. }
    assert (SRCAP : ainblk (FB1 FF :: LB) SRC (zlen src)).
    { destruct (INS NZ) as [(b & Hb & Hb1 & Hb2)|[IM1 IM2]]; [| unfold AIMG_HI in IM2; exfalso; clear - IM2 SL NZ ATR; lia].
      exists b. split; [right; exact Hb| split; [exact Hb1| exact Hb2]]. }
    zstep. zstep. zstep. zstep.                            (* [comment removed for export] *)
    zstep. unfold zd_getfh_stmtA, APZD_GETFH in GETFH.
    eapply evtF_cut.
    { eapply (GETFH L RNG st (FB1 FF :: LB)) with (lo := lo) (ZFH := FF + 32) (SRC := SRC) (src := src) (off := off) (size := sz);
      first [ exact SB2 | exact OK | exact ROFF | exact R5 | exact OFS | exact XZ | exact STL2 | exact AFP | exact ARO2 | exact MI | exact TP | reflexivity
            | clear - G2; lia
            | clear - SL; lia
            | clear - F3 G1; lia
            | clear - S2 G3; lia
            | clear - F7; lia
            | intros _; split; [exact S1| split; [exact US2| split; [exact RS1| exact RS2]]]
            | intros _; left; exact SRCAP
            | clear - F2; Z.div_mod_to_equations; lia
            | intros _; split; [eapply ablk_sub; [exact F1| clear; lia| clear; lia] | split; [exact UZ2| split; [eapply rng_sub'; [exact RF1| clear; lia]| eapply rng_sub'; [exact RF2| unfold shspan; rewrite F4, !shad_div; unfold ASHOFF; clear - F2; Z.div_mod_to_equations; lia]]]]
            | exists FF, (FF + 128); split; [clear; lia|]; split; [clear; lia|]; split; [clear - F2; Z.div_mod_to_equations; lia|]; split; [clear - F2; Z.div_mod_to_equations; lia|];
              split; [clear - FL; lia|]; split; [unfold KEND; clear - FL ATR; lia|];
              rewrite <- F4; replace (shad (FF + 128) - SHF) with 16 by (rewrite F4, !shad_div; clear - F2; Z.div_mod_to_equations; lia);
              split; [exact (proj2 XS) | exact RF2]
            | exists (FB1 FF); split; [left; reflexivity| cbn; clear; lia]
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & cs & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & ZC5 & ZSZ5 & ZOK5).
    rd_retlit.
    (* [comment removed for export] *)
    set (W5 := [(FF + 32, FF + 32 + 48); (SPA - 4320, SPA)]) in MU5.
    assert (AW5 : aappW W5).
    { subst W5. unfold aappW. pose proof (ablk_disj_band _ _ F1) as DBF. unfold KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - DBF; lia|]. apply Forall_cons; [cbn [fst snd]; clear - KLO G2; lia|]. apply Forall_nil. }
    assert (DSTK : forall X k, SPA <= X -> 0 <= k -> disjoint_from (W5 ++ fake_area L) X k).
    { intros X k H1 Hk. subst W5. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
      clear - H1 Hk FABL F3 G1 G2 ATR KLO. unfold KHIGH in KLO. repeat split; Z.div_mod_to_equations; lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV2 MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as SAV5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA2 MU5 WM5 ltac:(apply DSTK; clear; lia)) as FRA5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU5 WM5 ltac:(apply DSTK; clear; lia)) as FRB5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRC2 MU5 WM5 ltac:(apply DSTK; clear; lia)) as FRC5.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG2 MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as STG5.
    (* [comment removed for export] *)
    assert (PFF : forall a, FF <= a < FF + 128 -> ~ (FF + 32 <= a < FF + 80) ->
              (in_fake (FB1 FF :: LB) a /\ outside [(FF + 32, FF + 32 + 48)] a) \/ (exists a', in_fake (FB1 FF :: LB) a' /\ a = shad a')).
    { intros a Ha N1. left. split; [exists 1, FF, 128; split; [left; reflexivity| exact Ha]|]. cbn [outside]. clear - Ha N1. split; [lia| exact I]. }
    assert (PSF : forall a, SHF <= a < SHF + 16 -> (in_fake (FB1 FF :: LB) a /\ outside [(FF + 32, FF + 32 + 48)] a) \/ (exists a', in_fake (FB1 FF :: LB) a' /\ a = shad a')).
    { intros a Ha. right. exists (8 * (a - SHB)). rewrite ESHF in Ha.
      split; [exists 1, FF, 128; split; [left; reflexivity| clear - Ha F2; Z.div_mod_to_equations; lia]|].
      rewrite shad_div. unfold ASHOFF. clear - Ha. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XHA ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XHA5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XHC ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XHC5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XS ltac:(unfold DSHZ; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PSF; clear - Ha; lia)) as XS5.
    (* [comment removed for export] *)
    assert (XL5 : rw_cells bsegs m5 FLG [C1 (Z_to_bv 8 1)]).
    { rewrite L0. destruct (FFLAG _ _ _ _ _ 1 FF 128 AH5 ltac:(left; reflexivity)) as (X & _). exact X. }
    (* [comment removed for export] *)
    assert (FFR5' : ffr_pres W5 (FB1 FF :: LB) m2 m5).
    { eapply magree_mono; [exact FFR5|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
      subst W5; cbn [outside app] in HO |- *. destruct HO as (O1 & _). exact (conj O1 I). }
    assert (DFSR : disjoint_from W5 SRC (zlen src)) by (subst W5; cbn [disjoint_from]; clear - F7 S2 G2 G3; repeat split; lia).
    assert (UP5 : unpoisoned m5 (SPA + 64) (SPA + 88)).
    { eapply unpoisoned_munch; [exact UP2 | exact MU5 |]. subst W5. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
      clear - FABL FL G1 G2 G3 G5 ATR KLO. unfold KHIGH in KLO. repeat split; Z.div_mod_to_equations; lia. }
    pose proof (fcall_bytes_pres AI FHL _ _ _ _ _ _ _ _ SRC (map (Z_to_bv 8) src) AH2 ltac:(rewrite length_map; exact SRCAP) ltac:(rewrite length_map; exact DFSR) MU5 FFR5' SB2) as SB5.
    pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH2 SRCAP NZ ltac:(unfold KEND; clear - SL ATR; lia) AW5 MU5 FFR5' US2) as US5.
    assert (ARO5 : aro_client RNG m5) by (eapply aro_client_transport_F; [exact ARO2| exact MU5| exact WM5| exact AW5| exact FAB]).
    (* [comment removed for export] *)
    assert (FFR05 : ffr_pres [] LB m0 m5).
    { eapply ffr_pres_trans; [exact FFR1|]. eapply ffr_pres_trans.
      - eapply (fk_ffr_fin AI L RNG st LB m1 m1 m2 1 FF 128 SHF 16 [] []);
          [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
          | constructor | constructor | apply ffr_pres_refl
          | cbn [app]; eapply munch_weaken; [| exact MU12]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
          | exact WM12 ].
      - eapply magree_mono; [exact FFR5|]. intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha) & ->)].
        + left. split; [exists c, A, k; split; [right; exact Hb| exact Ha]|].
          pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 _ Hb) as D1. cbn [ab_addr ab_size] in D1.
          cbn [outside]. clear - D1 Ha. split; [lia| exact I].
        + right. exists a'. split; [exists c, A, k; split; [right; exact Hb| exact Ha]| reflexivity]. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU05 : munch ((SPV - 5024, SPV) :: fake_area L) m0 m5).
    { eapply munch_trans; [exact MU1|]. eapply munch_trans.
      - eapply munch_weaken; [| exact MU12]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
        destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 FA8 F2. Z.div_mod_to_equations. lia.
      - eapply munch_weaken; [| exact MU5]. subst W5. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx. unfold FAKESZ in *.
        clear - Hx F5 F6 G3. lia. }
    assert (WM05 : wmono bsegs m0 m5) by (exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM12 WM5))).
    assert (BI5 : BINV m5) by (split; [exact AH5| split; [exact FFR05| split; [exact MU05| split; [exact WM05| exact MI5]]]]).
    set (gfh := get_frame_header src off sz) in *.
    assert (RRET : 0 <= fh_retval gfh < 18446744073709551616).
    { destruct gfh as [hh|v] eqn:G; cbn [fh_retval]; [clear; lia|]. pose proof (gfh_ret_pos src off sz v R5 G) as RP. clear - RP; lia. }
    (* [comment removed for export] *)
    assert (XIZ : forall csz, rw_cells bsegs m5 (FF + 32) csz -> cells_size csz = 48%nat -> XINVg DSHZ m5).
    { intros csz ZC SZ. destruct (rw_cells_forget _ _ _ _ ZC) as [jz ZC']. rewrite SZ in ZC'.
      assert (XH5 : rw_cells bsegs m5 FF ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c)] ++ [CB 8 (firstn 8 jH); CB 48 jz; CB 40 (firstn 40 (skipn 48 (skipn 8 jH)))] ++ [C8 (Z_to_bv 64 FLG)])).
      { cbn [app]. apply (proj2 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 8 (firstn 8 jH)] _)). split; [exact XHA5|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. apply (proj2 (rw_cells_app bsegs _ _ [CB 48 jz] _)). split; [replace (FF + 32) with (FF + 32) by reflexivity; match goal with |- rw_cells _ _ ?a _ => replace a with (FF + 32) by (clear; lia) end; exact ZC'|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. match goal with |- rw_cells _ _ ?a _ => replace a with (FF + 80) by (clear; lia) end. exact XHC5. }
      apply rw_cells_merge in XH5. cbn [app cells_size csize Nat.add cells_bytes] in XH5.
      split; [exact BI5|]. split; [exact SAV5|]. split; [exists jA; exact FRA5|]. split; [exists jB; exact FRB5|]. split; [exists jC; exact FRC5|].
      split; [exact ST5|]. split; [exact STG5|]. split; [eexists; exact XH5|]. split; [exact XL5|]. split; [exact XS5|].
      split; [exact SB5|]. split; [exact US5|]. split; [exact UP5| exact ARO5]. }
    clear MU5 WM5 FFR5 FFR5' PFF PSF DSTK AW5 DFSR SAV2 FRA2 FRB2 FRC2 STL2 STG2 XHA XZ XHC XS XL2 SB2 US2 UP2 ARO2 UZ2 AFP ART2 AH2 MU12 WM12 MI AH1 FFR1 MU1 WM1 XH XI.
    fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS. fk_hold ASH.
    fk_hold L4. fk_hold FABD. fk_hold LY5. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FABL. fk_hold FLA. fk_hold S2. fk_hold F7.
    fk_hold FFSH. fk_hold FLSH. fk_hold SSH. fk_hold ZOK5. fk_hold SRCAP. fk_hold LBH'. fk_hold ASH'.
    fk_hold SAV5. fk_hold FRA5. fk_hold FRB5. fk_hold FRC5. fk_hold STG5. fk_hold ST5. fk_hold XHA5. fk_hold XHC5. fk_hold XL5. fk_hold SB5. fk_hold US5. fk_hold UP5. fk_hold ARO5.
    fk_hold AH5. fk_hold FFR05. fk_hold MU05. fk_hold WM05. fk_hold BI5. fk_hold XIZ. fk_hold ER.
    zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      gf_unhold. eapply PXHERR; [exact (XIZ cs ZC5 ZSZ5)|].
      rewrite ER. unfold get_frame_content_size. fold gfh.
      destruct gfh as [hh|v] eqn:G; cbn [fh_retval] in KE |- *; [exfalso; clear - KE; lia|].
      unfold ZD_CONTENTSIZE_ERROR. change (2^64 - 2) with 18446744073709551614. cbn [Z.leb Z.compare Pos.compare Pos.compare_cont]. reflexivity.
    - (* [comment removed for export] *)
      destruct (gfh_ok_of_ret0 src off sz R5 ltac:(fold gfh; clear - KE RRET; lia)) as [h G]. fold gfh in G.
      gf_unhold. rewrite (ZOK5 h G) in ZC5. pose proof (XIZ _ ZC5 eq_refl) as XI5. clear XIZ.
      pose proof (get_frame_header_ok src OK off sz h G) as (TY & _ & _ & RFCS & _). change (2^64) with 18446744073709551616 in RFCS.
      unfold get_frame_content_size in ER. fold gfh in ER. rewrite G in ER.
      set (fcs := if fh_type h =? 1 then 0 else fh_fcs h) in *.
      assert (RFCS2 : 0 <= fcs < 18446744073709551616) by (unfold fcs; destruct (fh_type h =? 1); clear - RFCS; lia).
      unfold zfh_cells in ZC5.
      pose proof (munch_refl [(SHF, SHF + 16)] m5) as MUL. pose proof (wmono_refl bsegs m5) as WML.
      fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS. fk_hold ASH.
      fk_hold L4. fk_hold FABD. fk_hold LY5. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FABL. fk_hold FLA. fk_hold S2. fk_hold F7.
      fk_hold FFSH. fk_hold FLSH. fk_hold SSH. fk_hold ZOK5. fk_hold SRCAP. fk_hold LBH'. fk_hold ASH'.
      fk_hold SAV5. fk_hold FRA5. fk_hold FRB5. fk_hold FRC5. fk_hold STG5. fk_hold ST5. fk_hold XHA5. fk_hold XHC5. fk_hold XL5. fk_hold SB5. fk_hold US5. fk_hold UP5. fk_hold ARO5.
      fk_hold AH5. fk_hold FFR05. fk_hold MU05. fk_hold WM05. fk_hold BI5. fk_hold XI5. fk_hold ER. fk_hold TY.
      unfold DSHZ in XS5.
      zstep. rewrite sx32w_small by (unfold fk_held in TY; clear - TY; lia).     (* [comment removed for export] *)
      zstep. zstep. if_cases KT; zify_cond KT.
      + (* [comment removed for export] *)
        zstep.                                             (* [comment removed for export] *)
        do 6 zstep.                                        (* [comment removed for export] *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        change (rw_cells bsegs m6 SHF DSH0) in XS5.
        gf_unhold.
        pose proof (xinv_rep m5 m6 XI5 MUL WML ltac:(assumption) XS5) as XI6.
        replace (fh_fcs h) with fcs in * by (unfold fcs; replace (fh_type h =? 1) with false by (symmetry; apply Z.eqb_neq; clear - KT TY; lia); reflexivity).
        clear MUL WML ZC5 XS5 XI5.
        fk_hold XI6. fk_hold ER. fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS.
        zstep. zstep. replace (Z_to_bv 64 (-3)) with (Z_to_bv 64 18446744073709551613) by (apply Z_to_bv_eqm; reflexivity).
        zstep. if_cases KF; zify_cond KF.
        * (* [comment removed for export] *)
          gf_unhold. eapply PXEXIT; [exact XI6 | reflexivity |].
          rewrite ER. unfold ZD_CONTENTSIZE_ERROR. change (2^64 - 2) with 18446744073709551614.
          replace (18446744073709551614 <=? fcs) with true by (symmetry; apply Z.leb_le; clear - KF; lia). reflexivity.
        * gf_unhold. unfold ZD_CONTENTSIZE_ERROR in ER. change (2^64 - 2) with 18446744073709551614 in ER.
          replace (18446744073709551614 <=? fcs) with false in ER by (symmetry; apply Z.leb_gt; clear - KF; lia).
          change (2^64) with 18446744073709551616 in ER.
          eapply p_join; [exact XI6 | exact R5 | exact ROFF | exact RSZ | exact RT | clear - KF RFCS2; lia | exact ER | exact RB].
      + (* [comment removed for export] *)
        zstep.                                             (* [comment removed for export] *)
        do 6 zstep.                                        (* [comment removed for export] *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        change (rw_cells bsegs m6 SHF DSH0) in XS5.
        gf_unhold.
        pose proof (xinv_rep m5 m6 XI5 MUL WML ltac:(assumption) XS5) as XI6.
        assert (EF : fcs = 0) by (unfold fcs; replace (fh_type h =? 1) with true by (symmetry; apply Z.eqb_eq; clear - KT TY; lia); reflexivity).
        rewrite EF in ER.
        clear MUL WML ZC5 XS5 XI5.
        zstep.                                             (* [comment removed for export] *)
        unfold ZD_CONTENTSIZE_ERROR in ER. change (2^64 - 2) with 18446744073709551614 in ER. change (2^64) with 18446744073709551616 in ER.
        cbn [Z.leb Z.compare Pos.compare Pos.compare_cont] in ER.
        eapply p_join; [exact XI6 | exact R5 | exact ROFF | exact RSZ | exact RT | clear; lia | | exact RB].
        rewrite ER. replace (18446744073709551616 <=? total + 0) with false by (symmetry; apply Z.leb_gt; clear - RT; lia). reflexivity.
  Qed.
End FD.
End CANSEC1.
