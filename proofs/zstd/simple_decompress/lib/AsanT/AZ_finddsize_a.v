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
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_findfsi_a.
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
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF5 := (Z_to_bv 8 18446744073709551605).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B00 := (Z_to_bv 8 0).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition DSH0 : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3].
Definition DSHZ : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3].

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

  Notation POST := (zd_finddsize_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV src size0 lo m0).
  Notation RES := (find_decompressed_size src size0).

  (* [comment removed for export] *)
  Definition BINV (m1 : amem) : Prop :=
    AHEAP AI L RNG st (FB1 FF :: LB) m1 /\ ffr_pres [] LB m0 m1
    /\ munch ((SPV - 5024, SPV) :: fake_area L) m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1.

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 KM8) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma p_exit : forall m1 r jA csB csC w0 shb (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x27 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m1 (SPA + 24) csB -> cells_size csB = 40%nat -> rw_cells bsegs m1 (SPA + 64) csC -> cells_size csC = 24%nat ->
    stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 88) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 120) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 16 shb] ->
    Z_to_bv 64 r = Z_to_bv 64 RES ->
    evtF bsegs RNG POST (STpc 0x83dac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 r) x27 x28 x29 x30 x31).
  Proof.
    intros m1 r jA csB csC w0 shb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x27 x28 x29 x30 x31
           (AH1 & FFR1 & MU1 & WM1 & MI) SAV FRA FRB SZB FRC SZC STL STG XM XP XL XS ER.
    destruct G_lo as (G1 & G2 & G3 & G4 & G5 & G6). destruct G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    destruct G_flg as (L0 & L1 & L2 & L3 & L4). destruct R_ff as (RF1 & RF2 & RF3).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 16 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 128 <= SHF \/ SHF + 16 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 16 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL GS ATR; lia).
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    assert (L0' : 6443008 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL; lia).
    clear G_src R_src OK N0 N40 NLEN R_fsi.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells bsegs _ _ _ FRB) as FRBS. rewrite SZB in FRBS. pose proof (stk_of_rw_cells bsegs _ _ _ FRC) as FRCS. rewrite SZC in FRCS.
    assert (STH : stk bsegs m1 (SPA + 24) (SPV + -104)).
    { eapply stk_merge with (mid := SPA + 64); [| eapply stk_merge with (mid := SPA + 88); [| exact STG | clear - G3; lia] | clear - G3; lia].
      - replace (SPA + 64) with (SPA + 24 + Z.of_nat 40) by (clear; lia). exact FRBS.
      - replace (SPA + 88) with (SPA + 64 + Z.of_nat 24) by (clear; lia). exact FRCS. }
    clear FRB FRC SZB SZC FRBS FRCS STG.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in XS; [| reflexivity]. cbn [mk_CB_cells app] in XS.
    pose proof (munch_refl [(FF, FF + 8); (SHF, SHF + 16)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold MU1. fk_hold WM1. fk_hold FFR1. fk_hold RI.
    fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L1. fk_hold L3. fk_hold L4. fk_hold F7. fk_hold LBH. fk_hold ER.
    zstep. zstep.                                          (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 F0'; lia|].   (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    fk_hold FLA. fk_hold XM.
    do 16 zstep.                                           (* [comment removed for export] *)
    unfold fk_held in FLA.
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (AHA : AHEAP AI L RNG st (FB1 FF :: LB) mA).
    { eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia] |].
      constructor; [cbn [fst snd] | constructor].
      rewrite F4. replace (shad FF + 16 - shad FF) with 16 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 1 FF 128 FF 16); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - F0'; lia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(FLG, FLG + 1)] mA) as MU2.
    fk_hold FFSH. fk_hold AHA. fk_hold MUL.
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    unfold fk_held in AHA.
    assert (AHB : AHEAP AI L RNG st LB mB).
    { subst FLG. eapply (fk_release AI fflag L RNG st LB mA mB 1 FF 128 FRL AHA); [clear - L0'; lia | clear - L2 ATR; lia | clear - L0'; lia | exact MU2 | exact XL]. }
    clear AHA. unfold fk_held in MUL.
    assert (MUX : munch [(FF, FF + 8); (SHF, SHF + 16); (FLG, FLG + 1)] m1 mB)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUL] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
    clear MUL MU2.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep.                                                 (* [comment removed for export] *)
    unfold FSAVED in SAV.
    do 13 zstep.                                           (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    unfold fk_held in ER. rewrite ER.
    apply evtF_done. unfold zd_finddsize_postA.
    do 14 eexists. exists mB. split; [reflexivity|].
    unfold fk_held in *.
    pose proof (stk_of_rw_cells bsegs _ _ _ SAV) as SAVS. cbn [cells_size csize Nat.add length] in SAVS.
    pose proof (stk_of_rw_cells bsegs _ _ _ FRA) as FRAS. cbn [cells_size csize Nat.add length] in FRAS.
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    split.
    { (* [comment removed for export] *)
      eapply munch_trans; [exact MU1|].
      eapply munch_weaken; [| exact MUX]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 L3a L3b FA8 F2. Z.div_mod_to_equations. lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 WML)|].
    split; [assumption|].
    split.
    { eapply stk_merge; [exact STL | | clear - G2 G3; lia].
      eapply stk_merge; [| eapply stk_merge; [exact STH | | clear - G3; lia] | clear - G3; lia].
      - replace (SPA + 24) with (SPA + Z.of_nat 24) by (clear; lia). exact FRAS.
      - replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by (clear; lia). exact SAVS. }
    split.
    { (* [comment removed for export] *)
      eapply ffr_pres_trans; [exact FFR1|].
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mB 1 FF 128 SHF 16 [] [(FF, FF + 8); (FLG, FLG + 1)]);
        [exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia | | | apply ffr_pres_refl | | exact WML].
      - constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 b Hb) as HB; clear - HB; lia
                                                            | exists FF, (FF + 128); split; [exact F1 | clear; lia]]] |].
        constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; exact (L4 b (or_intror Hb)) | exists FLG, (FLG + 1); split; [exact L1 | clear; lia]]] | constructor].
      - constructor.
      - cbn [app]. eapply munch_weaken; [| exact MUX]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
    exact AHB.
  Qed.

  (* [comment removed for export] *)
  Lemma p_end : forall m1 off sz total jA csB csC w0 shb (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m1 (SPA + 24) csB -> cells_size csB = 40%nat -> rw_cells bsegs m1 (SPA + 64) csC -> cells_size csC = 24%nat ->
    stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 88) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 120) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 16 shb] ->
    RES = find_dsize src off sz total -> 0 <= sz < 5 -> 0 <= total < 18446744073709551616 ->
    evtF bsegs RNG POST (STpc 0x83da0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 sz) x20 x21 x22 (Z_to_bv 64 total) x28 x29 x30 x31).
  Proof.
    intros m1 off sz total jA csB csC w0 shb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31
           BI SAV FRA FRB SZB FRC SZC STL STG XM XP XL XS ER RSZ RT.
    rewrite (find_dsize_eq src OK) in ER by (change (2^64) with 18446744073709551616; clear - RSZ; lia).
    unfold ZD_FRAMEHEADERSIZE_PREFIX in ER. replace (sz <? 5) with true in ER by (symmetry; apply Z.ltb_lt; clear - RSZ; lia).
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    clear G_src R_src R_fsi N0 N40 NLEN SRCE KLO.
    fk_hold BI. fk_hold SAV. fk_hold FRA. fk_hold FRB. fk_hold FRC. fk_hold STL. fk_hold STG. fk_hold XM. fk_hold XP. fk_hold XL. fk_hold XS. fk_hold ER.
    fk_hold G_lo. fk_hold G_ff. fk_hold G_flg. fk_hold R_ff. fk_hold LBH. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1.
    zstep. if_cases K; zify_cond K.
    - zstep. unfold fk_held in *. eapply p_exit; try eassumption.
      rewrite ER. replace (sz =? 0) with true by (symmetry; apply Z.eqb_eq; clear - K RSZ; lia). reflexivity.
    - zstep. zstep. unfold fk_held in *. eapply p_exit; try eassumption.
      rewrite ER. replace (sz =? 0) with false by (symmetry; apply Z.eqb_neq; clear - K RSZ; lia). apply Z_to_bv_eqm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma p_herr : forall m1 jA csB csC w0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m1 (SPA + 24) csB -> cells_size csB = 40%nat -> rw_cells bsegs m1 (SPA + 64) csC -> cells_size csC = 24%nat ->
    stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 88) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 120) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF DSHZ ->
    RES = ZD_CONTENTSIZE_ERROR ->
    evtF bsegs RNG POST (STpc 0x84074 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31).
  Proof.
    intros m1 jA csB csC w0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31
           BI SAV FRA FRB SZB FRC SZC STL STG XM XP XL XS ER.
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof G_flg as (L0 & L1 & L2 & L3 & L4).
    pose proof R_ff as (RF1 & RF2 & RF3).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 16 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 128 <= SHF \/ SHF + 16 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 16 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL GS ATR; lia).
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    unfold DSHZ in XS.
    pose proof (munch_refl [(SHF, SHF + 16)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    clear G_src R_src R_fsi OK N0 N40 NLEN SRCE.
    fk_hold BI. fk_hold SAV. fk_hold FRA. fk_hold FRB. fk_hold FRC. fk_hold STL. fk_hold STG. fk_hold XM. fk_hold XP. fk_hold XL. fk_hold ER. fk_hold SZB. fk_hold SZC.
    fk_hold G_lo. fk_hold G_ff. fk_hold G_flg. fk_hold R_ff. fk_hold LBH. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1.
    fk_hold FLA. fk_hold L4. fk_hold L3. fk_hold F5. fk_hold F6. fk_hold F7.
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 KM8) by (apply Z_to_bv_eqm; reflexivity).
    do 6 zstep.                                            (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.
    unfold fk_held in *.
    destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. cbn [cells_size csize Nat.add] in XS'.
    eapply (p_exit mC (-2) jA csB csC w0 shb);
      [| eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | unfold FSAVED; cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
       | eapply rw_cells_transport; [exact FRA | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
       | eapply rw_cells_transport; [exact FRB | exact MUL | exact WML | rewrite SZB; cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
       | exact SZB
       | eapply rw_cells_transport; [exact FRC | exact MUL | exact WML | rewrite SZC; cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
       | exact SZC
       | eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
       | eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
       | eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - FFSH; lia]
       | eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - FFSH; lia]
       | eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLSH; lia]
       | exact XS'
       | rewrite ER; apply Z_to_bv_eqm; reflexivity ].
    split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
    - eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd] | constructor].
      rewrite F4. replace (shad FF + 16 - shad FF) with 16 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 1 FF 128 FF 16); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - F0'; lia].
    - eapply ffr_pres_trans; [exact FFR1|].
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mC 1 FF 128 SHF 16 [] []);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor | constructor | apply ffr_pres_refl
        | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WML ].
    - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *.
      assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
      clear - Hx F5 F6 L3a L3b FA8 F2. Z.div_mod_to_equations. lia.
  Qed.
End FD.
End CANSEC1.
