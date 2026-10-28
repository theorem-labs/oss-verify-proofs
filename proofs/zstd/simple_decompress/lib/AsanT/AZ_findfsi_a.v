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
     AZ_frame_iface AZ_libc_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF5 := (Z_to_bv 8 18446744073709551605).
Notation BF8 := (Z_to_bv 8 18446744073709551608).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition FSAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition FSH5 : list cell :=
  [C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5;
   C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5].

(* [comment removed for export] *)
Lemma ffr_pres_mono_nil1 : forall W LB (m m' : amem), ffr_pres [] LB m m' -> ffr_pres W LB m m'.
Proof.
  intros W LB m m' H a Ha HP. apply (H a Ha). destruct HP as [[HF _]|HS]; [left; split; [exact HF| exact I]| right; exact HS].
Qed.

Section FS.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA FSIP SRC : Z) (src : list Z) (off size lo FF SHF FLG : Z).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis N40 : size < 1099511627776.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis SRCE : SRC + zlen src < 2^64.
  Hypothesis F8 : FSIP mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 4320 /\ SPV - 176 <= SPA <= SPV - 160 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis G_fsip : (17594333495296 <= FSIP /\ FSIP + 32 <= 2^47) /\ SPV <= FSIP.
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC) /\ (FSIP + 24 <= SRC \/ SRC + zlen src <= FSIP).
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ
                    /\ (FSIP + 24 <= FF \/ FF + 256 <= FSIP) /\ (SRC + zlen src <= FF \/ FF + 256 <= SRC).
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (FSIP + 24 <= FLG \/ FLG + 1 <= FSIP).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_fsip : rng RNG FSIP 24 /\ rng RNG (shad FSIP) (shspan FSIP 24).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.

  Notation WR := [(FSIP, FSIP + 24)].
  Notation POST := (zd_findfsi_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV FSIP src off size lo m0).
  Notation RES := (find_frame_size_info src off size).

  (* [comment removed for export] *)
  Definition BINV (m1 : amem) : Prop :=
    AHEAP AI L RNG st (FB2 FF :: LB) m1 /\ ffr_pres WR LB m0 m1
    /\ munch ([(FSIP, FSIP + 24); (SPV - 4672, SPV)] ++ fake_area L) m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1.

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma p_ret : forall m1 jfr w0 shb j0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 56 jfr] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    rw_cells bsegs m1 FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize RES)); C8 (Z_to_bv 64 (fsi_bound RES))] ->
    evtF bsegs RNG POST (STpc 0x84440 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 jfr w0 shb j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31
           (AH1 & FFR1 & MU1 & WM1 & MI) SAV FRA STL STG XM XP XL XS FC1.
    destruct G_lo as (G1 & G2 & G3 & G4 & G5 & G6). destruct G_fsip as (P1 & P2). destruct G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8').
    destruct G_flg as (L0 & L1 & L2 & L3 & L4 & L5). destruct R_ff as (RF1 & RF2 & RF3). destruct R_fsip as (RP1 & RP2).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 32 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL GS ATR; lia).
    assert (PSH : FSIP + 24 <= SHF \/ SHF + 32 <= FSIP) by (clear - P1 GS ATR; lia).
    assert (P0' : 0 <= FSIP) by (clear - P1; lia).
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    assert (L0' : 6443008 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL; lia).
    clear G_src R_src OK OFF0 N5 N40 OFS F8.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in XS; [| reflexivity]. cbn [mk_CB_cells app] in XS.
    (* [comment removed for export] *)
    fk_hold FC1.
    pose proof (munch_refl [(SHF, SHF + 32)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold MU1. fk_hold WM1. fk_hold FFR1. fk_hold RI. fk_hold RP1. fk_hold RP2.
    fk_hold P1. fk_hold P2. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L1. fk_hold L3. fk_hold L4. fk_hold L5. fk_hold F7. fk_hold F8'. fk_hold PSH. fk_hold LBH.
    zstep.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    fk_hold FLA. fk_hold XM.
    do 32 zstep.                                           (* [comment removed for export] *)
    unfold fk_held in FLA.
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (AHA : AHEAP AI L RNG st (FB2 FF :: LB) mA).
    { eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd] | constructor].
      rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - F0'; lia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(FLG, FLG + 1)] mA) as MU2.
    fk_hold FFSH. fk_hold AHA. fk_hold MUL.
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    unfold fk_held in AHA.
    assert (AHB : AHEAP AI L RNG st LB mB).
    { subst FLG. eapply (fk_release AI fflag L RNG st LB mA mB 2 FF 256 FRL AHA); [clear - L0'; lia | clear - L2 ATR; lia | clear - L0'; lia | exact MU2 | exact XL]. }
    clear AHA. unfold fk_held in MUL.
    assert (MUX : munch [(SHF, SHF + 32); (FLG, FLG + 1)] m1 mB)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUL] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
    clear MUL MU2.
    (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    unfold FSAVED in SAV.
    do 13 zstep.                                           (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    apply evtF_done. unfold zd_findfsi_postA.
    do 15 eexists. exists mB, j0. split; [reflexivity|].
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
      eapply stk_merge; [| eapply stk_merge; [exact STG | | clear - G3; lia] | clear - G3; lia].
      - replace (SPA + 56) with (SPA + Z.of_nat 56) by (clear; lia). exact FRAS.
      - replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by (clear; lia). exact SAVS. }
    split.
    { (* [comment removed for export] *)
      eapply ffr_pres_trans; [exact FFR1|]. apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mB 2 FF 256 SHF 32 [] [(FSIP, FSIP + 24); (FLG, FLG + 1)]);
        [exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia | | | apply ffr_pres_refl | | exact WML].
      - constructor; [cbn [fst snd]; split; [clear; lia | left; clear - P1 P2 G1 G2 G3; lia] |].
        constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; exact (L4 b (or_intror Hb)) | exists FLG, (FLG + 1); split; [exact L1 | clear; lia]]] | constructor].
      - constructor.
      - cbn [app]. eapply munch_weaken; [| exact MUX]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
    split; [exact AHB|].
    eapply rw_cells_transport; [exact FC1 | exact MUX | exact WML | cbn [cells_size csize Nat.add disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PSH L5; lia].
  Qed.

  Ltac fin_hold_geom :=
    fk_hold G_lo; fk_hold G_fsip; fk_hold G_src; fk_hold G_ff; fk_hold G_flg; fk_hold R_src; fk_hold R_fsip; fk_hold LBH.

  (* [comment removed for export] *)
  Lemma p_fin : forall m1 jfr w0 shb j0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 56 jfr] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    rw_cells bsegs m1 FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize RES)); C8 (Z_to_bv 64 (fsi_bound RES))] ->
    evtF bsegs RNG POST (STpc 0x84414 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 jfr w0 shb j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31
           (AH1 & FFR1 & MU1 & WM1 & MI) SAV FRA STL STG XM XP XL XS FC1.
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8'). pose proof G_flg as (L0 & L1 & L2 & L3 & L4 & L5).
    pose proof G_fsip as (P1 & P2). pose proof R_ff as (RF1 & RF2 & RF3).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 32 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL GS ATR; lia).
    assert (PSH : FSIP + 24 <= SHF \/ SHF + 32 <= FSIP) by (clear - P1 GS ATR; lia).
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [4;1;1;1;1;1;1;22]%nat) in XS; [| reflexivity]. cbn [mk_CB_cells app] in XS.
    pose proof (munch_refl [(SHF, SHF + 32); (FF, FF + 8)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fin_hold_geom. fk_hold MU1. fk_hold WM1. fk_hold FFR1. fk_hold AH1. fk_hold FC1. fk_hold XL. fk_hold FLA. fk_hold L4. fk_hold L3. fk_hold F5. fk_hold F6.
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    do 6 zstep.                                            (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 F0'; lia|].   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.
    unfold fk_held in *.
    destruct (rw_cells_forget _ _ _ _ XS) as [shb' XS']. cbn [cells_size csize Nat.add] in XS'.
    assert (FFRC : ffr_pres WR LB m0 mC).
    { eapply ffr_pres_trans; [exact FFR1|].
      apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mC 2 FF 256 SHF 32 [] [(FSIP, FSIP + 24); (FF, FF + 8)]);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - P1 P2 G1 G2 G3; lia] |];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 b Hb) as HB; clear - HB; lia
                                                              | exists FF, (FF + 256); split; [exact F1 | clear; lia]]] | constructor]
        | constructor
        | apply ffr_pres_refl
        | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WML ]. }
    eapply (p_ret mC jfr _ shb' j0); [| exact SAV | exact FRA | exact STL | exact STG | exact XM | exact XP | | exact XS' |].
    - split; [| split; [exact FFRC | split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
      + eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
        constructor; [cbn [fst snd] | constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia] | constructor]].
        rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
        eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - F0'; lia].
      + eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
        destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *.
        assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
        clear - Hx F5 F6 L3a L3b FA8 F2. Z.div_mod_to_equations. lia.
    - eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLSH FLA; lia].
    - eapply rw_cells_transport; [exact FC1 | exact MUL | exact WML | cbn; clear - PSH F7; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma p_fin_sk : forall m1 jfr w0 shb j0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 56 jfr] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    rw_cells bsegs m1 FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize RES)); C8 (Z_to_bv 64 (fsi_bound RES))] ->
    evtF bsegs RNG POST (STpc 0x84310 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 jfr w0 shb j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31
           (AH1 & FFR1 & MU1 & WM1 & MI) SAV FRA STL STG XM XP XL XS FC1.
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8'). pose proof G_flg as (L0 & L1 & L2 & L3 & L4 & L5).
    pose proof G_fsip as (P1 & P2). pose proof R_ff as (RF1 & RF2 & RF3).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    pose proof (munch_refl [(FF, FF + 8)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fin_hold_geom. fk_hold MU1. fk_hold WM1. fk_hold FFR1. fk_hold AH1. fk_hold FC1. fk_hold XL. fk_hold XS. fk_hold FLA. fk_hold L4. fk_hold L3. fk_hold F5. fk_hold F6.
    zstep. zstep.                                          (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [| exfalso; clear - K0 F0'; lia].   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.
    unfold fk_held in *.
    assert (FFRC : ffr_pres WR LB m0 mC).
    { eapply ffr_pres_trans; [exact FFR1|].
      apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mC 2 FF 256 SHF 32 [] [(FSIP, FSIP + 24); (FF, FF + 8)]);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - P1 P2 G1 G2 G3; lia] |];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 b Hb) as HB; clear - HB; lia
                                                              | exists FF, (FF + 256); split; [exact F1 | clear; lia]]] | constructor]
        | constructor
        | apply ffr_pres_refl
        | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WML ]. }
    eapply (p_ret mC jfr _ shb j0); [| exact SAV | exact FRA | exact STL | exact STG | exact XM | exact XP | | | ].
    - split; [| split; [exact FFRC | split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
      + eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
        constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia] | constructor].
      + eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
        clear - Hx F5 F6. lia.
    - eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLA; lia].
    - eapply rw_cells_transport; [exact XS | exact MUL | exact WML | cbn; clear - FFSH; lia].
    - eapply rw_cells_transport; [exact FC1 | exact MUL | exact WML | cbn; clear - F7; lia].
  Qed.
End FS.
End CANSEC1.
