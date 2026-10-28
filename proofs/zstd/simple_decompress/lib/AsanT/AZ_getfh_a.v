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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_frame_iface AZ_libc_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
(* [comment removed for export] *)
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma tblA_did_rd : forall (m : amem) k, mem_inv bsegs m -> 0 <= k < 4 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (136800 + k * 8)) 8 = Some (le8 (Z_to_bv 64 (did_fieldSize k))).
Proof.
  intros m k MI Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; (apply img_rd8; [exact MI | vm_compute; reflexivity | lia | lia]).
Qed.
Lemma tblA_fcs_rd : forall (m : amem) k, mem_inv bsegs m -> 0 <= k < 4 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (136864 + k * 8)) 8 = Some (le8 (Z_to_bv 64 (fcs_fieldSize k))).
Proof.
  intros m k MI Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; (apply img_rd8; [exact MI | vm_compute; reflexivity | lia | lia]).
Qed.

(* [comment removed for export] *)
Definition GFSAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition GFHDR (FLG : Z) (junk : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1e002); C8 (Z_to_bv 64 0x8324c); CB 32 junk; C8 (Z_to_bv 64 FLG)].
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF5 := (Z_to_bv 8 18446744073709551605).
Definition GFSH : list cell := [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF3; C1 BF3; C1 BF3].
Definition GFSH5 : list cell := [C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5].

(* [comment removed for export] *)
Definition Z0A (hs : word) : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 hs; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Section GF.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 m2 m3 : amem) (SPV SPA ZFH SRC : Z) (src : list Z) (off size lo FF SHF FLG : Z) (jF : list byte).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis Z8 : ZFH mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 2208 /\ SPV - 144 <= SPA <= SPV - 128 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_zfh : ablk ZFH (ZFH + 48) /\ (ZFH + 48 <= lo \/ SPV <= ZFH).
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC) /\ (ZFH + 48 <= SRC \/ SRC + zlen src <= ZFH).
  Hypothesis G_ff : ablk FF (FF + 64) /\ FF mod 64 = 0 /\ FF + 64 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 64 <= al_fake L + FAKESZ
                    /\ (ZFH + 48 <= FF \/ FF + 64 <= ZFH) /\ (SRC + zlen src <= FF \/ FF + 64 <= SRC).
  Hypothesis G_flg : FLG = fflag L 0 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB0 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (ZFH + 48 <= FLG \/ FLG + 1 <= ZFH).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_zfh : rng RNG ZFH 48 /\ rng RNG (shad ZFH) (shspan ZFH 48).
  Hypothesis R_ff : rng RNG FF 64 /\ rng RNG SHF 8 /\ rng RNG FLG 1.
  Hypothesis R_tbl : rng RNG 136800 32 /\ rng RNG (shad 136800) (shspan 136800 32) /\ rng RNG 136864 32 /\ rng RNG (shad 136864) (shspan 136864 32).
  (* [comment removed for export] *)
  Hypothesis LBH : ablkLB LB.
  Hypothesis AINZ : ainblk LB ZFH 48.
  Hypothesis AH2 : AHEAP AI L RNG st (FB0 FF :: LB) m2.
  Hypothesis FFR2 : ffr_pres [] LB m0 m2.
  Hypothesis MU23 : munch [(ZFH, ZFH + 48); (SPA - 2208, SPA + 32); (FF, FF + 24); (SHF, SHF + 8)] m2 m3.
  Hypothesis WM23 : wmono bsegs m2 m3.
  Hypothesis MU03 : munch ([(ZFH, ZFH + 48); (SPV - 4320, SPV)] ++ fake_area L) m0 m3.
  Hypothesis WM03 : wmono bsegs m0 m3.

  Notation WB := [(ZFH, ZFH + 48)].
  Notation WX := [(ZFH, ZFH + 48); (FF, FF + 8); (SHF, SHF + 8); (FLG, FLG + 1)].
  Notation POST := (zd_getfh_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV ZFH src off size lo m0).

  Notation fhd := (Znth (off + 4) src).
  Notation sseg := (fhd_singleSegment fhd).
  Notation dcode := (fhd_dictIDSizeCode fhd).
  Notation fcsid := (fhd_fcsID fhd).
  Notation P1 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0)).
  Notation P2 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0) + did_fieldSize (fhd_dictIDSizeCode fhd)).
  Notation DID := (fh_read_dictID src P1 dcode).
  Notation FCS := (fh_read_fcs src P2 fcsid sseg).
  Notation WS := (if fhd_singleSegment fhd =? 0 then wl_windowSize (Znth (off + 5) src) else FCS).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 ZFH) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size) (Z_to_bv 64 0) (Z_to_bv 64 FF)
             (Z_to_bv 64 SHF) (Z_to_bv 64 SHB) (Z_to_bv 64 5) s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition XINV (m1 : amem) : Prop :=
    rw_cells bsegs m1 (SPV + -96) (GFSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)
    /\ (exists jA, rw_cells bsegs m1 SPA [CB 32 jA])
    /\ stk bsegs m1 lo SPA /\ stk bsegs m1 (SPA + 32) (SPV + -96)
    /\ rw_cells bsegs m1 FF (GFHDR FLG jF) /\ rw_cells bsegs m1 SHF GFSH /\ rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)]
    /\ unpoisoned m1 SRC (SRC + zlen src) /\ unpoisoned m1 ZFH (ZFH + 48)
    /\ unpoisoned m1 136800 (136800 + 32) /\ unpoisoned m1 136864 (136864 + 32)
    /\ munch WB m3 m1 /\ wmono bsegs m3 m1 /\ mem_inv bsegs m1.

  Definition MINV (m1 : amem) (zc : list cell) : Prop :=
    bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) /\ rw_cells bsegs m1 ZFH zc /\ XINV m1.

  Ltac xinv_i SAV FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI :=
    split; [exact SAV|]; split; [eexists; exact FRA|]; split; [exact STL|]; split; [exact STG|];
    split; [exact XF|]; split; [exact XS|]; split; [exact XL|]; split; [exact US|]; split; [exact UZ|];
    split; [exact UT1|]; split; [exact UT2|]; split; [exact MU|]; split; [exact WM| exact MI].
  Ltac xinv_e XI SAV jA FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI :=
    destruct XI as (SAV & [jA FRA] & STL & STG & XF & XS & XL & US & UZ & UT1 & UT2 & MU & WM & MI).

  (* [comment removed for export] *)
  Lemma p_exit : forall m1 cs r res (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    XINV m1 -> rw_cells bsegs m1 ZFH cs -> cells_size cs = 48%nat ->
    get_frame_header src off size = res ->
    Z_to_bv 64 r = Z_to_bv 64 (fh_retval res) ->
    (forall h, res = FH_ok h -> cs = zfh_cells h) ->
    evtF bsegs RNG POST (STpc 0x83378 m1 x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros m1 cs r res x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 XI ZC1 SZ1 ERES ER HD.
    xinv_e XI SAV jA FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI.
    clear US UZ UT1 UT2.
    destruct G_lo as (G1 & G2 & G3 & G4 & G5 & G6). destruct G_zfh as (Z1 & Z2). destruct G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    destruct G_flg as (L0 & L1 & L2 & L3 & L4 & L5). destruct R_ff as (RF1 & RF2 & RF3). destruct R_zfh as (RZ1 & RZ2).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    (* [comment removed for export] *)
    assert (GS : SHB + 805376 <= SHF /\ SHF + 8 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 64 <= SHF \/ SHF + 8 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 8 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL GS ATR; lia).
    assert (ZCSH : ZFH + 48 <= SHF \/ SHF + 8 <= ZFH) by (pose proof (fk_ablk_lits _ _ Z1) as ZL; clear - ZL GS ATR; lia).
    assert (Z0' : 0 <= ZFH) by (pose proof (fk_ablk_lits _ _ Z1) as ZL; clear - ZL; lia).
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    assert (L0' : 6443008 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL; lia).
    clear G_src R_src R_tbl OK OFF0 N5 OFS Z8.
    (* [comment removed for export] *)
    apply (munch_weaken _ [(ZFH, ZFH + 48); (FF, FF + 8); (SHF, SHF + 8)]) in MU; [| unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia].
    unfold GFHDR in XF. unfold GFSH in XS.
    (* [comment removed for export] *)
    fk_hold ZC1. pose proof (munch_refl [(FF, FF + 8); (SHF, SHF + 8); (FLG, FLG + 1)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold RI. fk_hold RZ1. fk_hold RZ2. fk_hold FFR2. fk_hold MU03. fk_hold WM03.
    fk_hold Z1. fk_hold Z2. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L1. fk_hold L3. fk_hold L4. fk_hold LBH.
    zstep. zstep.                                          (* [comment removed for export] *)
    fk_hold FLSH. fk_hold ZCSH. fk_hold L5. fk_hold F8.
    zstep.                                                 (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 F0'; lia|].   (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    unfold fk_held in FLSH. fk_hold F7. fk_hold FLA.
    do 8 zstep.                                            (* [comment removed for export] *)
    unfold fk_held in FLA.
    zstep.                                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (AHA : AHEAP AI L RNG st (FB0 FF :: LB) mA).
    { eapply (AI_frame AI) with (W := [(ZFH, ZFH + 48); (SPA - 2208, SPA + 32); (FF, FF + 24); (SHF, SHF + 8)]); [exact AH2 | | exact (wmono_trans _ _ _ _ WM23 WM) |].
      - eapply munch_trans; [exact MU23 |]. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia.
      - constructor; [cbn [fst snd]; apply fk_acr_inblk; destruct AINZ as (b & Hb & Hb1 & Hb2); exists b; split; [right; exact Hb| clear - Hb1 Hb2; lia] |].
        constructor; [cbn [fst snd]; eapply fk_acr_stack; [exact G1 | clear - G2; lia | clear - G3 G5; lia] |].
        constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia] |].
        constructor; [cbn [fst snd] | constructor].
        rewrite F4. replace (shad FF + 8 - shad FF) with 8 by (clear; lia).
        eapply (fk_acr_fshadow AI _ 0 FF 64 FF 8); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - F0'; lia]. }
    (* [comment removed for export] *)
    apply (munch_weaken _ WX) in MU; [| unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia].
    pose proof (munch_refl [(FLG, FLG + 1)] mA) as MU2.
    fk_hold FFSH. fk_hold AHA.
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    unfold fk_held in AHA.
    assert (AHB : AHEAP AI L RNG st LB mB).
    { subst FLG. eapply (fk_release AI fflag L RNG st LB mA mB 0 FF 64 FRL AHA); [clear - L0'; lia | clear - L2 ATR; lia | clear - L0'; lia | exact MU2 | exact XL]. }
    clear MU2 AHA.
    (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    unfold GFSAVED in SAV.
    do 12 zstep.                                           (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    apply evtF_done. unfold zd_getfh_postA. rewrite ERES, <- ER.
    do 14 eexists. exists mB, cs. split; [reflexivity|].
    unfold fk_held in *.
    pose proof (stk_of_rw_cells bsegs _ _ _ SAV) as SAVS. cbn [cells_size csize Nat.add length] in SAVS.
    pose proof (stk_of_rw_cells bsegs _ _ _ FRA) as FRAS. cbn [cells_size csize Nat.add length] in FRAS.
    assert (FA8 : al_fake L mod 8 = 0) by (unfold al_fake; Z.div_mod_to_equations; lia).
    split.
    { (* [comment removed for export] *)
      eapply munch_trans; [eapply munch_weaken; [| exact MU03]; unfold sub_fp; cbn [outside app]; intros x Hx; exact Hx |].
      eapply munch_weaken; [| exact MU]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 L3a L3b FA8 F2. Z.div_mod_to_equations. lia. }
    split; [exact (wmono_trans _ _ _ _ WM03 WM)|].
    split; [exact MI|].
    split.
    { eapply stk_merge; [exact STL | | clear - G2 G3; lia].
      eapply stk_merge; [| eapply stk_merge; [exact STG | | clear - G3; lia] | clear - G3; lia].
      - replace (SPA + 32) with (SPA + Z.of_nat 32) by (clear; lia). exact FRAS.
      - replace SPV with (SPV + -96 + Z.of_nat 96) at 2 by (clear; lia). exact SAVS. }
    split.
    { (* [comment removed for export] *)
      eapply (fk_ffr_fin AI L RNG st LB m0 m2 mB 0 FF 64 SHF 8 [(ZFH, ZFH + 48)] [(SPA - 2208, SPA + 32); (FF, FF + 24); (FLG, FLG + 1)]);
        [exact AH2 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia | | | exact FFR2 | | exact (wmono_trans _ _ _ _ WM23 WM)].
      - constructor; [cbn [fst snd]; split; [clear - G2; lia | left; clear - G1 G2 G3 G5; lia] |].
        constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2 b Hb); clear - H; lia | exists FF, (FF + 64); split; [exact F1 | clear; lia]]] |].
        constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; exact (L4 b (or_intror Hb)) | exists FLG, (FLG + 1); split; [exact L1 | clear; lia]]] | constructor].
      - constructor; [cbn [fst snd]; split; [exists ZFH, (ZFH + 48); split; [exact Z1 | clear; lia] | clear; lia] | constructor].
      - cbn [app]. eapply munch_trans; [eapply munch_weaken; [| exact MU23] | eapply munch_weaken; [| exact MU]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
    split; [exact AHB|].
    split; [eapply rw_cells_transport; [exact ZC1 | exact MUL | exact WML | rewrite SZ1; cbn [disjoint_from Z.of_nat]; clear - F7 ZCSH L5; lia]|].
    split; [exact SZ1 | exact HD].
  Qed.

  (* [comment removed for export] *)
  Definition MAINP : Prop :=
    le32 src off = ZD_MAGICNUMBER /\ fhd_header_size fhd <= size /\ fhd_reserved fhd = 0 /\ (sseg = 0 -> Znth (off + 5) src <= 175).

  Lemma gfh_magic : le32 src off = ZD_MAGICNUMBER -> get_frame_header src off size = get_frame_header_zstd src off size.
  Proof.
    intros MG. unfold get_frame_header, ZD_FRAMEHEADERSIZE_PREFIX.
    replace (size <? 5) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta. rewrite MG, Z.eqb_refl. reflexivity.
  Qed.

  Lemma main_ok : MAINP ->
    get_frame_header src off size = FH_ok (mkFH FCS WS (Z.min WS ZD_BLOCKSIZE_MAX) 0 (fhd_header_size fhd) DID (fhd_checksumFlag fhd)).
  Proof.
    intros (MG & NF & RSV & WOK). rewrite (gfh_magic MG). unfold get_frame_header_zstd.
    rewrite frame_header_size_ge5 by (unfold ZD_FRAMEHEADERSIZE_PREFIX; lia). cbv zeta.
    replace (size <? fhd_header_size fhd) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite RSV. change (negb (0 =? 0)) with false. cbv iota.
    rewrite wl_windowLog_ok_iff by (apply OK).
    destruct (Z.eqb_spec sseg 0) as [E|E]; cbn [andb]; [| reflexivity].
    replace (175 <? Znth (off + 5) src) with false by (symmetry; apply Z.ltb_ge; auto). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma p_fin : forall m1 (x1 x5 x6 x7 x10 x14 x15 x17 x28 x29 x30 x31 : word),
    MAINP -> MINV m1 (Z0A (Z_to_bv 64 (fhd_header_size fhd))) ->
    evtF bsegs RNG POST (STpc 0x83998 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 WS) (Z_to_bv 64 FCS) (Z_to_bv 64 fhd) x14 x15 (Z_to_bv 64 DID) x17 x28 x29 x30 x31).
  Proof.
    intros m1 x1 x5 x6 x7 x10 x14 x15 x17 x28 x29 x30 x31 MP (SB1 & ZC1 & XI).
    pose proof MP as (MG & NF & RSV & WOK).
    xinv_e XI SAV jA FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI.
    destruct G_lo as (G1 & G2 & G3 & G4 & G5 & G6). destruct G_zfh as (Z1 & Z2). destruct G_src as (S1 & S2 & S3).
    destruct G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). destruct G_flg as (L0 & L1 & L2 & L3 & L4 & L5). destruct R_zfh as (RZ1 & RZ2).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (fk_ablk_lits _ _ Z1) as ZL. pose proof (fk_ablk_lits _ _ F1) as FL. pose proof (fk_ablk_lits _ _ L1) as LL. pose proof (fk_ablk_lits _ _ S1) as SL.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 8 <= 17594333495296) by (rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    pose proof (OK (off + 4)) as RF.
    pose proof (fh_read_fcs_range src OK P2 fcsid sseg) as RFCS. change (2^64) with 18446744073709551616 in RFCS.
    pose proof (fh_read_dictID_range src OK P1 dcode) as RDID. change (2^32) with 4294967296 in RDID.
    assert (RWS : 0 <= WS < 18446744073709551616).
    { destruct (Z.eqb_spec sseg 0) as [E|E]; [| exact RFCS].
      pose proof (wl_windowSize_range (Znth (off + 5) src) ltac:(apply OK)) as RW.
      pose proof (wl_windowLog_ok_iff (Znth (off + 5) src) ltac:(apply OK)) as WI.
      replace (175 <? Znth (off + 5) src) with false in WI by (symmetry; apply Z.ltb_ge; auto).
      apply Z.ltb_ge in WI. specialize (RW WI). change (2^32) with 4294967296 in RW. change (2^10) with 1024 in RW. lia. }
    unfold Z0A in ZC1.
    pose proof (munch_refl WB m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    remember WS as ws eqn:EWS. remember FCS as fcs eqn:EFCS. remember DID as did eqn:EDID.
    (* [comment removed for export] *)
    assert (ZR : 6443008 <= ZFH /\ ZFH + 56 <= 2^47) by (clear - ZL ATR; lia).
    assert (DZ1 : ZFH + 48 <= SPA \/ SPA + 32 <= ZFH) by (clear - Z2 G2 G3; lia).
    assert (DZ2 : ZFH + 48 <= SPV + -96 \/ SPV + -96 + 96 <= ZFH) by (clear - Z2 G2 G3; lia).
    assert (DZ3 : ZFH + 48 <= SHF \/ SHF + 8 <= ZFH) by (clear - ZL GS ATR; lia).
    clear SB1 RFCS RDID.
    (* [comment removed for export] *)
    fk_hold SAV. fk_hold FRA. fk_hold XF. fk_hold XS. fk_hold XL. fk_hold US. fk_hold UT1. fk_hold UT2.
    fk_hold Z2. fk_hold S2. fk_hold S3. fk_hold F7. fk_hold F8. fk_hold L4. fk_hold L5. fk_hold FL. fk_hold LL. fk_hold SL. fk_hold Z1. fk_hold F1. fk_hold L1. fk_hold S1.
    fk_hold FFR2. fk_hold MU03. fk_hold WM03. fk_hold MU23. fk_hold WM23. fk_hold AH2. fk_hold G4. fk_hold G6. fk_hold F2. fk_hold F4. fk_hold ESHF.
    fk_hold EWS. fk_hold EFCS. fk_hold EDID. fk_hold MG. fk_hold NF. fk_hold RSV. fk_hold WOK. fk_hold MP. fk_hold OFS. fk_hold RSTK. fk_hold R_src. fk_hold R_ff. fk_hold R_tbl.
    fk_hold DZ1. fk_hold DZ2. fk_hold DZ3. fk_hold GS. fk_hold F3. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L2. fk_hold L3.
    (* [comment removed for export] *)
    move RZ1 at bottom. move UZ at bottom.
    kx_autoFLAx [KAUnp ZFH 48; KAApp ZFH 48] [0x83378] 60%nat
      [KZRange ZFH 6443008 (2^47 - 56); KZAlign ZFH 8; KZWr ZFH 48; KZRange fhd 0 255]
      [] [(ZFH, 48)].
    all: try kx_acc RZ1.
    all: kx_mem.
    all: unfold fk_held in *.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
           eapply rw_cells_transport in SAV; [| exact MUL | exact WML | cbn [GFSAVED cells_size csize Nat.add length disjoint_from Z.of_nat]; clear - DZ2; lia];
           eapply rw_cells_transport in FRA; [| exact MUL | exact WML | cbn [cells_size csize Nat.add length disjoint_from Z.of_nat]; clear - DZ1; lia];
           eapply rw_cells_transport in XF; [| exact MUL | exact WML | cbn [GFHDR cells_size csize Nat.add length disjoint_from Z.of_nat]; clear - F7; lia];
           eapply rw_cells_transport in XS; [| exact MUL | exact WML | cbn [GFSH cells_size csize Nat.add length disjoint_from Z.of_nat]; clear - DZ3; lia];
           eapply rw_cells_transport in XL; [| exact MUL | exact WML | cbn [cells_size csize Nat.add length disjoint_from Z.of_nat]; clear - L5; lia];
           eapply unpoisoned_munch in US; [| exact MUL | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; clear - ZL SL ATR; Z.div_mod_to_equations; lia];
           eapply unpoisoned_munch in UZ; [| exact MUL | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; clear - ZL ATR; Z.div_mod_to_equations; lia];
           eapply unpoisoned_munch in UT1; [| exact MUL | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; clear - ZL ATR; Z.div_mod_to_equations; lia];
           eapply unpoisoned_munch in UT2; [| exact MUL | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; clear - ZL ATR; Z.div_mod_to_equations; lia]
         end.
    all: replace ((2305843009213693952 * fhd) mod 2 ^ 64 / 9223372036854775808) with (fhd_checksumFlag fhd) in ZC1 by (unfold fhd_checksumFlag; byte_brute fhd).
    (* [comment removed for export] *)
    all: eapply (p_exit _ _ 0); [xinv_i SAV FRA STL STG XF XS XL US UZ UT1 UT2 MU WM KXMI | exact ZC1 | reflexivity | subst ws fcs did; exact (main_ok MP) | reflexivity |];
         intros h E; injection E as <-; unfold zfh_cells; cbn [fh_fcs fh_window fh_bsmax fh_type fh_hsize fh_dictID fh_checksum]; subst ws fcs did.
    - rewrite Z.min_l by (unfold ZD_BLOCKSIZE_MAX; clear - KXBR; lia). reflexivity.
    - rewrite Z.min_r by (unfold ZD_BLOCKSIZE_MAX; clear - KXBR; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
End GF.
End CANSEC1.
