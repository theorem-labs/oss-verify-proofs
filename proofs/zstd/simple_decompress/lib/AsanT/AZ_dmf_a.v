(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_libc_iface AZ_kx.
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
Definition DSAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma dm_ffr_pres_mono_nil1 : forall W LB (m m' : amem), ffr_pres [] LB m m' -> ffr_pres W LB m m'.
Proof.
  intros W LB m m' H a Ha HP. apply (H a Ha). destruct HP as [[HF _]|HS]; [left; split; [exact HF| exact I]| right; exact HS].
Qed.
Lemma dm_disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; intros a n a' n' D H1 H2; cbn in *; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; [exact D2| lia| lia]].
Qed.
Lemma dm_stk_empty : forall (m : amem) A, 0 <= A -> A <= 2^64 -> stk bsegs m A A.
Proof. intros m A H0 H1. split; [exact H0|]. split; [exact H1|]. intros a Ha. lia. Qed.

Section DM.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA lo DCTX DST CAP SRC : Z) (src : list Z) (size FF SHF FLG : Z).
  (* [comment removed for export] *)
  Hypothesis RD0 : 4096 <= DCTX.  Hypothesis RD1 : DCTX + 95992 < 2^47.  Hypothesis RD8 : DCTX mod 8 = 0.
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size.  Hypothesis NLEN : size <= zlen src.  Hypothesis N40 : size < 1099511627776.
  Hypothesis RS0 : 4096 <= SRC.  Hypothesis RS1 : SRC + zlen src < 2^47.
  Hypothesis RC0 : 0 <= CAP.  Hypothesis RC40 : CAP < 1099511627776.
  Hypothesis DNULL : DST = 0 -> CAP = 0.  Hypothesis DNN : DST <> 0 -> 4096 <= DST.  Hypothesis RDST : DST + CAP < 2^47.
  Hypothesis S_DC : DCTX + 95992 <= lo \/ SPV <= DCTX.
  Hypothesis S_DS : DST + CAP <= lo \/ SPV <= DST.
  Hypothesis S_SR : SRC + zlen src <= lo \/ SPV <= SRC.
  Hypothesis S_GT : 0xc7fd0 + 16 <= lo \/ SPV <= 0xc7fd0.
  Hypothesis D_DC : DST + CAP <= DCTX \/ DCTX + 95992 <= DST.
  Hypothesis D_SR : DST + CAP <= SRC \/ SRC + zlen src <= DST.
  Hypothesis SR_DC : SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC.
  Hypothesis GT_DC : 0xc7fd0 + 16 <= DCTX \/ DCTX + 95992 <= 0xc7fd0.
  Hypothesis GT_DS : 0xc7fd0 + 16 <= DST \/ DST + CAP <= 0xc7fd0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 7184 /\ SPV - 543 <= SPA <= SPV - 512 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ
                    /\ (DCTX + 95992 <= FF \/ FF + 256 <= DCTX) /\ (DST + CAP <= FF \/ FF + 256 <= DST) /\ (SRC + zlen src <= FF \/ FF + 256 <= SRC).
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG).
  (* [comment removed for export] *)
  Hypothesis B_dc : ablk DCTX (DCTX + 95992) /\ ainblk LB DCTX 95992.
  Hypothesis B_sr : ablk SRC (SRC + zlen src) /\ (0 < zlen src -> ainimg LB SRC (zlen src)).
  Hypothesis B_ds : 0 < CAP -> ablk DST (DST + CAP) /\ ainblk LB DST CAP.
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_dc : rng RNG DCTX 95992 /\ rng RNG (shad DCTX) (shspan DCTX 95992).
  Hypothesis R_ds : 0 < CAP -> rng RNG DST CAP /\ rng RNG (shad DST) (shspan DST CAP).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.

  Notation WR := [(DCTX, DCTX + 95992); (DST, DST + CAP)].
  Notation POST := (zd_dmf_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DCTX DST CAP src size lo m0).

  (* [comment removed for export] *)
  Definition BINV (m1 : amem) : Prop :=
    AHEAP AI L RNG st (FB2 FF :: LB) m1 /\ ffr_pres WR LB m0 m1
    /\ munch ([(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - 7184, SPV)] ++ fake_area L) m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1.

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 SHF) x22 (Z_to_bv 64 SHB) x24 x25 x26 x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma dctx_any_transport : forall W' m1 m2, dctx_any m1 DCTX -> munch W' m1 m2 -> wmono bsegs m1 m2 ->
    disjoint_from W' DCTX 95992 -> dctx_any m2 DCTX.
  Proof.
    intros W' m1 m2 (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                     PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]) MU WM DJ.
    assert (TR : forall A cs, rw_cells bsegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells bsegs m2 A cs).
    { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply dm_disjoint_from_sub; [exact DJ | lia | lia]. }
    assert (TS : forall a b, stk bsegs m1 a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk bsegs m2 a b).
    { intros a b SK L1 L2 L3. eapply stk_transport_disjoint; [exact SK | exact MU | exact WM |]. eapply dm_disjoint_from_sub; [exact DJ | lia | lia]. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
    exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, ws, jhb, ovd, dcb, dce, trace.
    split; [apply TR; [exact PT | lia | cbn; lia]|].
    split; [apply TR; [exact H1 | lia | cbn; lia]|].
    split; [split; [apply TR; [exact FPC | lia | rewrite FPSZ; lia]| exact FPSZ]|].
    split; [apply TR; [exact H3 | lia | cbn; lia]|].
    split; [split; [apply TR; [exact XSC | lia | rewrite XSSZ; lia]| exact XSSZ]|].
    split; [split; [apply TR; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
    split; [exact H5OK|].
    split; [apply TR; [exact TX | lia | cbn; lia]|].
    split; apply TS; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_tail : forall m1 r jA w0 shb (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 408 jA] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 408) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    dctx_any m1 DCTX -> stk bsegs m1 DST (DST + CAP) ->
    0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evtF bsegs RNG POST (STpc 0x855b4 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 FF) x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 r jA w0 shb x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31
           (AH1 & FFR1 & MU1 & WM1 & MI) SAV FRA STL STG XM XP XL XS DA1 DSK1 RR RM.
    destruct G_lo as (G1 & G2 & G3 & G4 & G5 & G6). destruct G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8' & F9').
    destruct G_flg as (L0 & L1 & L2 & L3 & L4). destruct R_ff as (RF1 & RF2 & RF3). destruct B_dc as [ABD IBD].
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (FLD : FLG + 1 <= DCTX \/ DCTX + 95992 <= FLG).
    { destruct IBD as (bb & Hb & Hb1 & Hb2). pose proof (L4 bb ltac:(right; exact Hb)) as X. clear - X Hb1 Hb2. lia. }
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 32 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL GS ATR; lia).
    assert (DCSH : DCTX + 95992 <= SHF \/ SHF + 32 <= DCTX) by (pose proof (fk_ablk_lits _ _ ABD) as LL; clear - LL GS ATR; lia).
    assert (DSSH : 0 < CAP -> DST + CAP <= SHF \/ SHF + 32 <= DST) by (intros HC; pose proof (fk_ablk_lits _ _ (proj1 (B_ds HC))) as LL; clear - LL GS ATR; lia).
    assert (DSFL : 0 < CAP -> FLG + 1 <= DST \/ DST + CAP <= FLG).
    { intros HC. destruct (proj2 (B_ds HC)) as (bb & Hb & Hb1 & Hb2). pose proof (L4 bb ltac:(right; exact Hb)) as X. clear - X Hb1 Hb2. lia. }
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    assert (L0' : 6443008 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL; lia).
    clear B_sr R_src OK N0 NLEN N40.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in XS; [| reflexivity]. cbn [mk_CB_cells app] in XS.
    pose proof (munch_refl [(SHF, SHF + 32); (FF, FF + 8)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    (* [comment removed for export] *)
    fk_hold MU1. fk_hold WM1. fk_hold FFR1. fk_hold RI. fk_hold DA1. fk_hold DSK1. fk_hold RM. fk_hold RR.
    fk_hold F1. fk_hold F2. fk_hold F4. fk_hold F5. fk_hold F6. fk_hold F7. fk_hold F8'. fk_hold F9'. fk_hold L0. fk_hold L1. fk_hold L3. fk_hold L4.
    fk_hold LBH. fk_hold IBD. fk_hold ABD. fk_hold DSSH. fk_hold DSFL. fk_hold FLD. fk_hold DCSH. fk_hold ESHF. fk_hold G4. fk_hold G5. fk_hold G6.
    fk_hold S_DC. fk_hold S_DS. fk_hold S_SR. fk_hold S_GT. fk_hold D_DC. fk_hold D_SR. fk_hold SR_DC. fk_hold GT_DC. fk_hold GT_DS. fk_hold B_ds. fk_hold R_ds.
    fk_hold RD0. fk_hold RD1. fk_hold RD8. fk_hold RS0. fk_hold RS1. fk_hold RC0. fk_hold RC40. fk_hold DNULL. fk_hold DNN. fk_hold RDST.
    fk_hold R_dc. fk_hold AH1.
    zstep.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    do 32 zstep.                                           (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    unfold fk_held in AH1.
    assert (AHA : AHEAP AI L RNG st (FB2 FF :: LB) mA).
    { unfold fk_held in F2. eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd] | constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia] | constructor]].
      unfold fk_held in F4. rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - F0'; lia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(FLG, FLG + 1)] mA) as MU2.
    fk_hold AHA. fk_hold MUL. fk_hold AH1.
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    unfold fk_held in AHA. unfold fk_held in L0.
    assert (AHB : AHEAP AI L RNG st LB mB).
    { subst FLG. eapply (fk_release AI fflag L RNG st LB mA mB 2 FF 256 FRL AHA); [clear - L0'; lia | clear - L2 ATR; lia | clear - L0'; lia | exact MU2 | exact XL]. }
    clear AHA. unfold fk_held in MUL.
    assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 8); (FLG, FLG + 1)] m1 mB)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUL] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
    assert (WMX : wmono bsegs m1 mB) by (first [exact WML | eapply wmono_trans; [exact WML|]; assumption]).
    clear MU2. fk_hold MUX. fk_hold WMX. fk_hold AHB. clear MUL WML.
    zstep.
    zstep.                                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    unfold DSAVED in SAV.
    do 13 zstep.                                           (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    apply evtF_done. unfold zd_dmf_postA.
    do 14 eexists. exists mB, r. split; [reflexivity|].
    unfold fk_held in *.
    pose proof (stk_of_rw_cells bsegs _ _ _ SAV) as SAVS. cbn [cells_size csize Nat.add length] in SAVS.
    pose proof (stk_of_rw_cells bsegs _ _ _ FRA) as FRAS. cbn [cells_size csize Nat.add length] in FRAS.
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    split.
    { (* [comment removed for export] *)
      eapply munch_trans; [exact MU1|].
      eapply munch_weaken; [| exact MUX]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 L3a L3b FA8 F2. Z.div_mod_to_equations. lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 WMX)|].
    split; [assumption|].
    split.
    { eapply stk_merge; [exact STL | | clear - G2 G3; lia].
      eapply stk_merge; [| eapply stk_merge; [exact STG | | clear - G3; lia] | clear - G3; lia].
      - replace (SPA + 408) with (SPA + Z.of_nat 408) by (clear; lia). exact FRAS.
      - replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by (clear; lia). exact SAVS. }
    split.
    { (* [comment removed for export] *)
      eapply ffr_pres_trans; [exact FFR1|]. apply dm_ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mB 2 FF 256 SHF 32 [] [(FF, FF + 8); (FLG, FLG + 1)]);
        [exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia | | | apply ffr_pres_refl | | exact WMX].
      - constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 b Hb) as HB; clear - HB; lia
                                                            | exists FF, (FF + 256); split; [exact F1 | clear; lia]]] |].
        constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; exact (L4 b (or_intror Hb)) | exists FLG, (FLG + 1); split; [exact L1 | clear; lia]]] | constructor].
      - constructor.
      - cbn [app]. eapply munch_weaken; [| exact MUX]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
    split; [exact AHB|].
    split.
    { eapply dctx_any_transport; [exact DA1| exact MUX| exact WMX|]. cbn [disjoint_from]. clear - DCSH F7 FLD. repeat split; lia. }
    split.
    { destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
      - eapply stk_transport_disjoint; [exact DSK1| exact MUX| exact WMX|]. cbn [disjoint_from].
        pose proof (DSSH HC) as X1. pose proof (DSFL HC) as X2. clear - X1 X2 F8' HC. repeat split; lia.
      - replace (DST + CAP) with DST by (clear - HC RC0; lia). apply dm_stk_empty; [| clear - RDST RC0; lia].
        destruct (Z.eq_dec DST 0) as [->|Hd]; [clear; lia| pose proof (DNN Hd) as X; clear - X; lia]. }
    split; [exact RR| exact RM].
  Qed.
End DM.
End CANSEC1.
