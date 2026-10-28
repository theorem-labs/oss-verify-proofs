(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AZ_blk_iface AZ_blk_iface2 AZ_bst_env.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF5 := (Z_to_bv 8 18446744073709551605).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition BSH5 : list cell :=
  [C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5;
   C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5].

(* [comment removed for export] *)
Lemma bs_ffr_pres_mono_nil1 : forall W LB (m m' : amem), ffr_pres [] LB m m' -> ffr_pres W LB m m'.
Proof.
  intros W LB m m' H a Ha HP. apply (H a Ha). destruct HP as [[HF _]|HS]; [left; split; [exact HF| exact I]| right; exact HS].
Qed.

Section BS.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA lo FF SHF FLG : Z)
            (DTS DTP SRC W DFLT BASE BITS ty : Z) (k : seq_kind) (dt0 wb0 : list byte) (srcb : list Z) (frw oldp nbw coldw : word).
  (* [comment removed for export] *)
  Hypothesis LD0 : zlen dt0 = 8 + 8 * 2^(kind_maxLog k).
  Hypothesis LW0 : 626 <= zlen wb0.
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) srcb.
  Hypothesis SLEN : zlen srcb <= 1048576.
  Hypothesis TYR : 0 <= ty <= 3.
  Hypothesis DTP8 : DTP mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 5136 /\ SPV - 208 <= SPA <= SPV - 192 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_dts : ablk DTS (DTS + zlen dt0) /\ (DTS + zlen dt0 <= lo \/ SPV + 16 <= DTS) /\ (FF + 256 <= DTS \/ DTS + zlen dt0 <= FF) /\ 4096 <= DTS /\ DTS + zlen dt0 < 2^47.
  Hypothesis G_dtp : ablk DTP (DTP + 8) /\ (DTP + 8 <= lo \/ SPV + 16 <= DTP) /\ (FF + 256 <= DTP \/ DTP + 8 <= FF) /\ 4096 <= DTP /\ DTP + 8 < 2^47.
  Hypothesis G_w : ablk W (W + zlen wb0) /\ (W + zlen wb0 <= lo \/ SPV + 16 <= W) /\ (FF + 256 <= W \/ W + zlen wb0 <= FF) /\ 4096 <= W /\ W + zlen wb0 < 2^47.
  Hypothesis G_src : ablk SRC (SRC + zlen srcb) /\ (SRC + zlen srcb <= lo \/ SPV <= SRC) /\ (FF + 256 <= SRC \/ SRC + zlen srcb <= FF)
                     /\ 4096 <= SRC /\ SRC + zlen srcb < 2^47.
  Hypothesis G_img : 4096 <= BASE /\ BASE + 212 <= AIMG_HI /\ 4096 <= BITS /\ BITS + 53 <= AIMG_HI.
  Hypothesis G_sep : (DTS + zlen dt0 <= DTP \/ DTP + 8 <= DTS) /\ (DTS + zlen dt0 <= W \/ W + zlen wb0 <= DTS) /\ (DTS + zlen dt0 <= SRC \/ SRC + zlen srcb <= DTS)
                     /\ (DTP + 8 <= W \/ W + zlen wb0 <= DTP) /\ (DTP + 8 <= SRC \/ SRC + zlen srcb <= DTP) /\ (W + zlen wb0 <= SRC \/ SRC + zlen srcb <= W).
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ.
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (DTS + zlen dt0 <= FLG \/ FLG + 1 <= DTS) /\ (DTP + 8 <= FLG \/ FLG + 1 <= DTP) /\ (W + zlen wb0 <= FLG \/ FLG + 1 <= W).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV + 16 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_dts : rng RNG DTS (zlen dt0) /\ rng RNG (shad DTS) (shspan DTS (zlen dt0)).
  Hypothesis R_dtp : rng RNG DTP 8 /\ rng RNG (shad DTP) (shspan DTP 8).
  Hypothesis R_w : rng RNG W (zlen wb0) /\ rng RNG (shad W) (shspan W (zlen wb0)).
  Hypothesis R_src : rng RNG SRC (zlen srcb) /\ rng RNG (shad SRC) (shspan SRC (zlen srcb)).
  Hypothesis HSRC : ahull RNG m0 SRC (zlen srcb).
  Hypothesis R_img : aro RNG m0 BASE (4 * zlen (kind_base k)) /\ aro RNG m0 BITS (zlen (kind_bits k)).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.
  Hypothesis G_in : ainblk LB DTS (zlen dt0) /\ ainblk LB DTP 8 /\ ainblk LB W (zlen wb0) /\ (0 < zlen srcb -> ainimg LB SRC (zlen srcb)).
  (* [comment removed for export] *)
  Hypothesis G_af : ashort LB 3 /\ rng_fs L RNG /\ SPV + 16 < al_top L /\ rng RNG lo (al_top L - lo) /\ KHIGH <= lo.
  Hypothesis TP : tp = Z_to_bv 64 ATP.

  Notation WR := [(DTS, DTS + zlen dt0); (DTP, DTP + 8); (W, W + zlen wb0)].
  Notation POST := (zd_buildseq_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DTS DTP W DFLT k ty (zlen srcb) frw oldp dt0 (length wb0) lo m0).

  (* [comment removed for export] *)
  Definition BINV (m1 : amem) : Prop :=
    AHEAP AI L RNG st (FB2 FF :: LB) m1 /\ ffr_pres WR LB m0 m1
    /\ munch ([(DTS, DTS + zlen dt0); (DTP, DTP + 8); (W, W + zlen wb0); (SPV - 5136, SPV)] ++ fake_area L) m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1.

  (* [comment removed for export] *)
  Notation STb pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 FF) x21 x22 (Z_to_bv 64 SHF) x24 x25 (Z_to_bv 64 SHB) x27 x28 x29 x30 x31)   (* [comment removed for export] *)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition bs_resA (m1 : amem) (r : Z) (dt' : list byte) (pv : word) : Prop :=
    zd_is_error r = true
    \/ (r <= zlen srcb /\
        ((ty = 0 /\ pv = Z_to_bv 64 DFLT /\ dt' = dt0)
         \/ (ty = 3 /\ frw <> Z_to_bv 64 0 /\ pv = oldp /\ dt' = dt0)
         \/ ((ty = 1 \/ ty = 2) /\ pv = Z_to_bv 64 DTS /\
             exists t, seq_table_ok k t /\ firstn (length (seq_table_bytes t)) dt' = map (Z_to_bv 8) (seq_table_bytes t)))).

  (* [comment removed for export] *)
  Lemma bs_exitA : forall m1 jfr w0 shb dt' wb' pv r (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 88 jfr] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 88) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    u8arr bsegs m1 DTS dt' -> length dt' = length dt0 -> u8arr bsegs m1 W wb' -> length wb' = length wb0 -> rw_cells bsegs m1 DTP [C8 pv] ->
    0 <= r < 2^64 -> bs_resA m1 r dt' pv ->
    evtF bsegs RNG POST (STb 0x89084 m1 x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31).
  Proof.
    intros m1 jfr w0 shb dt' wb' pv r x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31
           (AH1 & FFR1 & MU1 & WM1 & MI) SAV FRA STL STG XM XP XL XS DTA LDT WA LWA DTPC RR RES.
    destruct G_lo as (G1 & G2 & G3 & G4 & G5 & G6). destruct G_ff as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct G_flg as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7). destruct R_ff as (RF1 & RF2 & RF3).
    destruct G_dts as (D1 & D2 & D3 & D4 & D5). destruct G_dtp as (P1 & P2 & P3 & P4 & P5). destruct G_w as (W1 & W2 & W3 & W4 & W5).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 788992 <= SHF /\ SHF + 32 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 32 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL GS ATR; lia).
    assert (DSH : DTS + zlen dt0 <= SHF \/ SHF + 32 <= DTS) by (pose proof (fk_ablk_lits _ _ D1) as DL; clear - DL GS ATR; lia).
    assert (PSH : DTP + 8 <= SHF \/ SHF + 32 <= DTP) by (pose proof (fk_ablk_lits _ _ P1) as PL; clear - PL GS ATR; lia).
    assert (WSH : W + zlen wb0 <= SHF \/ SHF + 32 <= W) by (pose proof (fk_ablk_lits _ _ W1) as WL; clear - WL GS ATR; lia).
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    assert (L0' : 6443008 <= FLG) by (pose proof (fk_ablk_lits _ _ L1) as LL; clear - LL; lia).
    clear G_src R_src FBY SLEN.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in XS; [| reflexivity]. cbn [mk_CB_cells app] in XS.
    (* [comment removed for export] *)
    fk_hold DTA. fk_hold WA. fk_hold DTPC.
    pose proof (munch_refl [(SHF, SHF + 32)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold MU1. fk_hold WM1. fk_hold FFR1. fk_hold RI.
    fk_hold P1. fk_hold P2. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L1. fk_hold L3. fk_hold L4. fk_hold L5. fk_hold L6. fk_hold L7. fk_hold PSH. fk_hold LBH.
    fk_hold D1. fk_hold D2. fk_hold D3. fk_hold W1. fk_hold W2. fk_hold W3. fk_hold DSH. fk_hold WSH. fk_hold G_sep. fk_hold G_img. fk_hold R_img.
    zstep.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    fk_hold FLA. fk_hold XM.
    clear G_lo G_dts G_dtp G_w G_ff G_flg R_ff R_dts R_dtp R_w. fk_hold RES.   (* [comment removed for export] *)
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
    zstep.                                                 (* [comment removed for export] *)
    unfold BSAVED in SAV.
    do 13 zstep.                                           (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    apply evtF_done. unfold zd_buildseq_postA.
    do 14 eexists. exists mB, r, dt', wb', pv. split; [reflexivity|].
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
      - replace (SPA + 88) with (SPA + Z.of_nat 88) by (clear; lia). exact FRAS.
      - replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by (clear; lia). exact SAVS. }
    split.
    { (* [comment removed for export] *)
      eapply ffr_pres_trans; [exact FFR1|]. apply bs_ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mB 2 FF 256 SHF 32 [] [(FLG, FLG + 1)]);
        [exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia | | | apply ffr_pres_refl | | exact WML].
      - constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; exact (L4 b (or_intror Hb)) | exists FLG, (FLG + 1); split; [exact L1 | clear; lia]]] | constructor].
      - constructor.
      - cbn [app]. eapply munch_weaken; [| exact MUX]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
    split; [exact AHB|].
    split; [eapply u8arr_transport; [exact DTA | exact MUX | exact WML | rewrite LDT; cbn [disjoint_from fst snd]; clear - DSH L5; lia]|].
    split; [exact LDT|].
    split; [eapply u8arr_transport; [exact WA | exact MUX | exact WML | rewrite LWA; cbn [disjoint_from fst snd]; clear - WSH L7; lia]|].
    split; [exact LWA|].
    split; [eapply rw_cells_transport; [exact DTPC | exact MUX | exact WML | cbn [cells_size csize Nat.add disjoint_from fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PSH L6; lia]|].
    split; [exact RR| exact RES].
  Qed.
End BS.
End CANSEC1.
