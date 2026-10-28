(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg
  AF_huf_x2t_bgeo.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.

Lemma hdr_le4 : forall (mtl : Z) (b0 b1 b2 b3 : byte),
  b0 = Z_to_bv 8 mtl -> 0 <= mtl < 256 ->
  exists hdw, hdw mod 256 = mtl /\ 0 <= hdw < 2^32 /\ [b0; b1; b2; b3] = le4 (Z_to_bv 64 hdw).
Proof.
  intros mtl b0 b1 b2 b3 E0 HMT.
  pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R1, R2, R3.
  exists (mtl + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
  split; [Z.div_mod_to_equations; lia|]. split; [lia|].
  symmetry. apply le4_of_mod32; [reflexivity|]. rewrite unsigned_lit by lia. cbn [le_val map]. subst b0. rewrite (byte_lit mtl) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma x2b_dtb_range : forall mtl, 1 <= mtl <= 12 -> 8 <= 4 * (1 + 2 ^ mtl) <= 16388.
Proof.
  intros mtl H.
  pose proof (Z.pow_le_mono_r 2 1 mtl ltac:(lia) ltac:(lia)) as P1.
  pose proof (Z.pow_le_mono_r 2 mtl 12 ltac:(lia) ltac:(lia)) as P2.
  change (2 ^ 1) with 2 in P1. change (2 ^ 12) with 4096 in P2. lia.
Qed.

Lemma sdw8_c1sB : forall m s, rw_cells bsegs m s [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m s [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.


Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - 528 - 4096 - 16.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Notation SPA := (SPB SP).
  Notation X2BSAVED' := (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation RET mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (ret_pc ra) fc None mm (seg_rom bsegs)).


  Lemma x2_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xba300)] -> rw_cells bsegs m 0xba300 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA jB,
        ms' = MS (mkR (Z_to_bv 64 0x81ecc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                     (Z_to_bv 64 64) (Z_to_bv 64 0xba2f8) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     a1 (Z_to_bv 64 2147450880) a0 a2 s6 a4 s8 a5 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x3cc38) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 528, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) X2BSAVED'
        /\ rw_cells bsegs m' SPA [CB 352 jA; C8 a3; CB 48 jB]
        /\ stk bsegs m' lo SPA /\ stk bsegs m' (SPA + 408) (SP + -104))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81e48) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_R in *.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof (spb_props SP SP16) as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 528, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.
    carve_frame 104%nat ST. carve_frame 408%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.

    release_frame FR0 ST (SP + -104).
    destruct (stk_split bsegs _ lo (SPA + 408) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA + 408) 408 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 408) with 408 in STL, FRA. replace (SPA + 408 - 408) with SPA in STL, FRA by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 408 _ [] [352; 8; 48]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    zstep.
    zstep. zstep.
    zstep.
    zstep. zstep.
    zstep. zstep. zstep. zstep.
    clear GOT GSU.
    zstep. rewrite (sx32_small 1) by lia.
    zstep.
    zstep.
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. zstep.
    apply evtF_done.
    eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR|]. split; [eassumption|]. split; [exact STL| exact STG].
  Qed.
  Definition X2BFFHDR (FLG : Z) (j3 : list byte) : list cell :=
    [C8 (Z_to_bv 64 X2B_MAGIC_LIVE); C8 (Z_to_bv 64 X2B_DESC); C8 (Z_to_bv 64 0x81e48); CB 32 j3; C8 (Z_to_bv 64 FLG)].
  Definition X2BFRA0 (FF DT WK : Z) (jA jB jC jT jD jE : list byte) : list cell :=
    [CB 128 jA; C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); CB 32 jB; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF);
     CB 8 jC; C8 (Z_to_bv 64 (WK + 676)); CB 8 jT; C8 (Z_to_bv 64 DT); CB 128 jD; C8 (Z_to_bv 64 WK); CB 40 jE; C8 (Z_to_bv 64 FF)].

  Lemma x2_hdr1 : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 xs6 xs8 xs10 xs11 flags : word) m (FF FLG DT WK wksz SRC n mtl : Z)
      (j0 j1 j2 : word) (junk jA jB : list byte) (dtb : list byte) (Q : machine_state -> Prop),
    rw_cells bsegs m SPA [CB 352 jA; C8 (Z_to_bv 64 WK); CB 48 jB] -> stk bsegs m lo SPA ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m X2B_GOTPC [C8 (Z_to_bv 64 0x81e48)] -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    u8arr bsegs m DT dtb -> zlen dtb = (4 * (1 + 2 ^ mtl)) -> nth_error dtb 0 = Some (Z_to_bv 8 mtl) -> 1 <= mtl <= 12 ->
    unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl))) -> ablk DT (DT + (4 * (1 + 2 ^ mtl))) -> 4096 <= DT -> DT + (4 * (1 + 2 ^ mtl)) < 2^47 -> DT mod 4 = 0 -> (DT + (4 * (1 + 2 ^ mtl)) <= FF \/ FF + 64 <= DT) -> (DT + (4 * (1 + 2 ^ mtl)) <= lo \/ SP <= DT) ->
    rng RNG DT (4 * (1 + 2 ^ mtl)) -> rng RNG (shad DT) 1 ->
    0 <= wksz < 2^32 -> 4096 <= WK -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
    (forall m' (j3 : list byte) (y12 : word),
        wksz < 2124 ->
        munch [(SPA, SPA + 408); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' (SPA + 168) [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
        stk bsegs m' lo (SPA + 168) -> stk bsegs m' (SPA + 192) (SPA + 408) ->
        rw_cells bsegs m' FF (X2BFFHDR FLG j3) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) X2BSH ->
        u8arr bsegs m' DT dtb ->
        Q (MS (mkR (Z_to_bv 64 0x81ecc) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                   (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 531) y12 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
                   (Z_to_bv 64 X2B_MAGIC_LIVE) (Z_to_bv 64 FF)
                   (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 DT) (Z_to_bv 64 n) xs6 (Z_to_bv 64 wksz) xs8 flags xs10 xs11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x82cdc) fc None m' (seg_rom bsegs))) ->
    (forall m' (j3 jA' jB' jC jT jD jE : list byte) (hdw : Z),
        2124 <= wksz -> hdw mod 256 = mtl -> 0 <= hdw < 2^32 -> firstn 4 dtb = le4 (Z_to_bv 64 hdw) ->
        munch [(SPA, SPA + 408); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' SPA (X2BFRA0 FF DT WK jA' jB' jC jT jD jE) -> stk bsegs m' lo SPA ->
        rw_cells bsegs m' FF (X2BFFHDR FLG j3) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) X2BSH ->
        u8arr bsegs m' DT dtb ->
        Q (MS (mkR (Z_to_bv 64 0x81ff4) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                   (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 0) (Z_to_bv 64 112) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
                   (Z_to_bv 64 X2B_MAGIC_LIVE) (Z_to_bv 64 FF)
                   (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 hdw) (Z_to_bv 64 n) (Z_to_bv 64 mtl) (Z_to_bv 64 WK) xs8 flags (Z_to_bv 64 (WK + 624)) xs11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x51574) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 0x81ecc) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 DT) (Z_to_bv 64 n) xs6 (Z_to_bv 64 wksz) xs8 flags xs10 xs11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x81ecc) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros FRA STL FFC SHF GPC MI FH FC F64 RF RSF DTC DTLEN DT0 MTL UD ABD DTL DTH DT4 DFD SDS RDT RSD1 WR WKL WKH WK4 KEXIT KCALL.
    pose proof (x2b_dtb_range mtl MTL) as DTBR. set (DTB := 4 * (1 + 2 ^ mtl)) in *. clearbody DTB.
    pose proof ABD as ABDu. unfold ablk, AIMG_HI, KLS in ABDu.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    unfold X2B_GOTPC in *. pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (spb_props SP SP16) as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply sdw8_c1sB in SHF. replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(SPA, SPA + 408); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    apply (rw_cells_split_CB bsegs _ _ [] 352 _ [C8 (Z_to_bv 64 WK); CB 48 jB] [128; 8; 32; 8; 8; 8; 8; 8; 8; 8; 128]%nat) in FRA; [| reflexivity].
    cbn [mk_CB_cells app] in FRA.
    lazymatch type of FRA with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; CB 48 ?j] =>
      apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] 48 j [] [40; 8]%nat) in FRA; [| reflexivity] end.
    cbn [mk_CB_cells app] in FRA.
    zstep.
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
    do 6 zstep.
    zstep.
    zstep. zstep.
    zstep. zstep. zstep.
    zstep. zstep.
    rewrite (Z.shiftr_div_pow2 FF 3) in * by lia. change (2^3) with 8 in *.
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (FF / 8 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 4%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.
    zstep. replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (FF / 8 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.
    zstep.
    zstep.
    zstep. bcase KA.
    { exfalso. apply KA. clear - DT4 DTL. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4. exact DT4. }
    zstep. zstep.
    zstep. zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MUx : munch _ m mx |- _ =>
        assert (UMx : unpoisoned mx DT (DT + DTB));
          [eapply unpoisoned_munch; [exact UD| exact MUx|]; rewrite !shad_div; cbn [disjoint_from]; unfold ASHOFF;
           refine (conj _ (conj _ (conj _ I))); clear - DTBR DFD F64 DTL DTH FHu ABDu SDS SPAB LOS LO0 ATR BSF SPT LOC; Z.div_mod_to_equations; lia |]
      end end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (chk1A mx DT (DT + DTB) DT 4 UMx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - DT4; Z.div_mod_to_equations; lia)) as (b & RDB & CK & SR) end.
    zstep. rewrite sxb_sval.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (JOIN : forall y10 y11 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x81ecc) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
          y10 y11 (Z_to_bv 64 0x81e48) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
          (Z_to_bv 64 1102416563) (Z_to_bv 64 FF)
          (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 DT) (Z_to_bv 64 n) xs6 (Z_to_bv 64 wksz) xs8 flags xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x81f84) fc None mx (seg_rom bsegs))) end.
    { intros y10 y11. clear RDB CK SR.
      zstep.
      zstep. replace (Z_to_bv 64 (-4)) with (Z_to_bv 64 18446744073709551612) by (apply Z_to_bv_eqm; reflexivity).
      zstep.
      zstep. bcase KD4; [exfalso; clear - KD4 DTL DTH DTBR; lia|].
      zstep.
      zstep. bcase KD0; [exfalso; clear - KD0 DTL DTH DTBR; lia|].
      zstep. zstep.
      zstep. bcase KW.
      -
        zstep.
        zstep. bcase KZ; [exfalso; clear - KZ WKL; lia|].
        zstep.
        zstep. bcase KA2; [exfalso; apply KA2; clear - WK4 WKL; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4; exact WK4|].
        zstep.
        zstep. replace (Z_to_bv 64 (-5)) with (Z_to_bv 64 18446744073709551611) by (apply Z_to_bv_eqm; reflexivity).
        zstep.
        zstep. bcase KB; [exfalso; clear - KB WKL WKH WR; lia|].
        zstep.
        assert (X4 : exists b1 b2 b3 dtl, dtb = Z_to_bv 8 mtl :: b1 :: b2 :: b3 :: dtl).
        { destruct dtb as [| b0 [| b1 [| b2 [| b3 dtl]]]]; [cbn in DTLEN; lia| cbn in DTLEN; lia| cbn in DTLEN; lia| cbn in DTLEN; lia|].
          cbn in DT0. injection DT0 as E0. exists b1, b2, b3, dtl. rewrite E0. reflexivity. }
        destruct X4 as (b1 & b2 & b3 & dtl & EDT).
        destruct (hdr_le4 mtl (Z_to_bv 8 mtl) b1 b2 b3 eq_refl ltac:(lia)) as (hdw & HM & HR & E4).
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?my _) =>
          lazymatch goal with DC : u8arr bsegs my DT _ |- _ =>
          assert (RDW : ov_read_bytes bsegs my (Z_to_bv 64 (DT + 0)) 4 = Some (le4 (Z_to_bv 64 hdw)))
            by (rewrite <- E4; destruct DC as [BA _]; rewrite EDT in BA; exact (bytes_at_read bsegs my DT _ 0 4 BA ltac:(lia) ltac:(cbn; lia))) end end.
        zstep.
        replace (zx32 (Z_to_bv 64 hdw)) with (Z_to_bv 64 hdw) by (unfold zx32; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
        clear RDW.
        zstep.
        replace (Z.land hdw 255) with mtl by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; symmetry; exact HM).
        zstep. zstep.
        zstep. zstep. zstep.
        zstep.
        replace (FF / 8 + 2147450880) with (Z.shiftr FF 3 + 2147450880) in * by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).

        apply evtF_done.
        eapply KCALL; [rewrite Z.shiftr_div_pow2 in KW by lia; clear - KW WR; Z.div_mod_to_equations; lia| exact HM| exact HR| rewrite EDT; exact E4| | exact WM| eassumption| | exact STL| | |eassumption];
            [ eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia
            | unfold X2BFRA0; eassumption
            | unfold X2BFFHDR, X2B_MAGIC_LIVE, X2B_DESC; eassumption
            | unfold X2BSH; eassumption ].
      -
        zstep. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
        zstep.
        replace (FF / 8 + 2147450880) with (Z.shiftr FF 3 + 2147450880) in * by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        lazymatch goal with FRAx : rw_cells _ ?my SPA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13] |- _ =>
          pose proof (proj1 (rd_rw_cells_appA bsegs _ _ [c0; c1; c2] [c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13]) FRAx) as [FA0 FA1];
          pose proof (proj1 (rd_rw_cells_appA bsegs _ _ [c3; c4; c5] [c6; c7; c8; c9; c10; c11; c12; c13]) FA1) as [FA2 FA3]; clear FA1 end.
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FA2, FA3.
        apply stk_of_rw_cells in FA0. apply stk_of_rw_cells in FA3. cbn [cells_size csize Nat.add app] in FA0, FA3.
        change (Z.of_nat 168) with 168 in *. change (Z.of_nat 24) with 24 in *. change (Z.of_nat 216) with 216 in *.
        replace (SPA + 168 + 24 + 216) with (SPA + 408) in FA3 by lia. replace (SPA + 168 + 24) with (SPA + 192) in FA3 by lia.
        apply evtF_done. eapply KEXIT; [rewrite Z.shiftr_div_pow2 in KW by lia; clear - KW WR; Z.div_mod_to_equations; lia| | exact WM| eassumption| exact FA2 | | exact FA3 | | | eassumption];
            [ eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia
            | exact (stk_merge bsegs _ lo SPA (SPA + 168) STL FA0 ltac:(lia))
            | unfold X2BFFHDR, X2B_MAGIC_LIVE, X2B_DESC; eassumption
            | unfold X2BSH; eassumption ]. }
    zstep. if_cases G; zify_cond G.
    - zstep. zstep. zstep. if_cases G'; zify_cond G'.
      + apply JOIN.
      +
        exfalso. rewrite (signed_lit_small64 (sval b)) in G' by (clear - SR; lia).
        change 7 with (Z.ones 3) in G'. rewrite Z.land_ones in G' by lia. change (2^3) with 8 in G'.
        rewrite (signed_lit_small64 (DT mod 8 + 3)) in G' by (Z.div_mod_to_equations; lia).
        clear - CK G G' SR. Z.div_mod_to_equations. lia.
    - apply JOIN.
  Qed.

  Lemma x2_hdr2 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 xs8 xs11 flags : word) m (FF DT WK SRC n hdw mtl : Z)
      (jA jB jC jT jD jE : list byte) (Q : machine_state -> Prop),
    1 <= mtl <= 12 -> stk bsegs m lo SPA -> mem_inv bsegs m -> rw_cells bsegs m SPA (X2BFRA0 FF DT WK jA jB jC jT jD jE) ->
    (forall m',
        munch [(SPA - 16, SPA)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
        stk bsegs m' lo (SPA - 16) -> rw_cells bsegs m' (SPA - 16) [C8 (Z_to_bv 64 876); C8 flags] ->
        rw_cells bsegs m' SPA (X2BFRA0 FF DT WK jA jB jC jT jD jE) ->
        Q (MS (mkR (Z_to_bv 64 0x82044) (Z_to_bv 64 (SPA - 16)) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                   (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 256) (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 (WK + 1248))
                   (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 hdw) (Z_to_bv 64 n) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 WK) (Z_to_bv 64 (WK + 992)) flags (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
              F (Z_to_bv 64 0x9733c) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 hdw) (Z_to_bv 64 n) (Z_to_bv 64 mtl) (Z_to_bv 64 WK) xs8 flags (Z_to_bv 64 (WK + 624)) xs11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x81ff4) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros MTL STL MI FRA KCALL.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (spb_props SP SP16) as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    pose proof (munch_refl [(SPA - 16, SPA)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold X2BFRA0 in FRA.
    zstep. zstep. replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 18446744073709551572) by (apply Z_to_bv_eqm; reflexivity).
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep.
    do 4 zstep.
    zstep.
    carve_frame 16%nat STL.
    zstep. zstep.
    zstep. zstep.
    do 7 zstep.
    replace (SPA + -16) with (SPA - 16) in * by lia.
    apply evtF_done. eapply KCALL; [| exact WM| eassumption| eassumption| eassumption| exact FRA].
    eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia.
  Qed.

  Lemma x2_epi : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      m (FF FLG r : Z) (j0 : word),
    rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) X2BSH ->
    rw_cells bsegs m FF [C8 j0] -> rw_cells bsegs m (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m (SP + -104) X2BSAVED' ->
    rw_cells bsegs m (SPA + 168) [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
    stk bsegs m lo (SPA + 168) -> stk bsegs m (SPA + 192) (SP + -104) -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= FF \/ FF + 64 <= FLG) ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG FLG 1 -> 0 <= r < 2^64 ->
    evtF bsegs RNG (fun ms' => exists mp m' x11' x12' x13',
        ms' = RET m' x5 x6 x7 (Z_to_bv 64 r) x11' x12' x13' x14 x15 x16 x17 x28 x29 x30 x31
        /\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x82cdc) fc None m (seg_rom bsegs)).
  Proof.
    intros until j0. intros SHF FF0 FF56 FLC FRB FRA STL STG MI FH FC F64 GH GC GF RF RSF RG Hr.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in *.
    unfold X2BSH in SHF. unfold X2BSAVED in FRB.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (spb_props SP SP16) as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m) as MU1.
    pose proof (wmono_refl bsegs m) as WM1.
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 4%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK.
    zstep.
    zstep. zstep.
    zstep.
    zstep.
    zstep.
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (bx (mem_inv bsegs mx)) in MIp end end.
    lazymatch type of MU1 with ?T => change T with (bx T) in MU1 end.
    lazymatch type of WM1 with ?T => change T with (bx T) in WM1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
    zstep.
    zstep.
    zstep. zstep.
    do 13 zstep. zstep. zstep.
    apply stk_of_rw_cells in FRA. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA + 168) (SPA + 192) STL ltac:(replace (SPA + 192) with (SPA + 168 + 24) by lia; exact FRA) ltac:(lia)) as ST1;
      pose proof (stk_merge bsegs mx lo (SPA + 192) (SP + -104) ST1 STG ltac:(lia)) as ST2 end.
    release_frame FRB ST2 SP.
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    eexists _, _, _, _, _. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM1|]. split; [exact MIp|].
    split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
    split; [exact ST2| exact FLC].
  Qed.

  Definition X2BFRA1 (FF DT WK : Z) (jA jB jC : list byte) (wT : word) (jD jE : list byte) : list cell :=
    [CB 128 jA; C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); CB 32 jB; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF);
     CB 8 jC; C8 (Z_to_bv 64 (WK + 676)); C8 wT; C8 (Z_to_bv 64 DT); CB 128 jD; C8 (Z_to_bv 64 WK); CB 40 jE; C8 (Z_to_bv 64 FF)].
  Lemma x2_rsw : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 : word) m
      (FF DT WK hdw mtl r tl : Z) (jA jB jC jT jD jE : list byte) (Q : machine_state -> Prop),
    stk bsegs m lo (SPA - 16) -> mem_inv bsegs m ->
    rw_cells bsegs m SPA (X2BFRA0 FF DT WK jA jB jC jT jD jE) ->
    (r <= 2^64 - 120 -> rw_cells bsegs m (FF + 32) [C4 (Z_to_bv 64 tl)]) ->
    0 <= r < 2^64 -> 0 <= tl < 2^32 -> (r <= 2^64 - 120 -> tl < 2^31) -> 0 <= hdw < 2^32 -> hdw mod 256 = mtl -> 1 <= mtl <= 12 ->
    4096 <= FF -> FF + 64 <= ATOP -> FF mod 64 = 0 -> ablk FF (FF + 64) -> rng RNG FF 64 ->
    (2^64 - 120 < r ->
       Q (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                  (Z_to_bv 64 r) (Z_to_bv 64 (-120)) x12 x13 x14 x15 x16 x17
                  xs2 xs3 (Z_to_bv 64 hdw) xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
             F (Z_to_bv 64 (X2B_ENTRY + 3732)) fc None m (seg_rom bsegs))) ->
    (forall m', r <= 2^64 - 120 -> mtl < tl ->
       munch [(SPA + 208, SPA + 216)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
       rw_cells bsegs m' SPA (X2BFRA1 FF DT WK jA jB jC (Z_to_bv 64 tl) jD jE) ->
       Q (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                  (Z_to_bv 64 (-44)) (Z_to_bv 64 r) (Z_to_bv 64 mtl) (Z_to_bv 64 tl) x14 x15 x16 x17
                  xs2 xs3 (Z_to_bv 64 hdw) xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
             F (Z_to_bv 64 (X2B_ENTRY + 3732)) fc None m' (seg_rom bsegs))) ->
    (forall m', r <= 2^64 - 120 -> tl <= mtl ->
       munch [(SPA + 208, SPA + 216)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
       rw_cells bsegs m' SPA (X2BFRA1 FF DT WK jA jB jC (Z_to_bv 64 tl) jD jE) ->
       Q (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                  (Z_to_bv 64 (-44)) (Z_to_bv 64 r) (Z_to_bv 64 mtl) (Z_to_bv 64 tl) x14 x15 x16 x17
                  xs2 xs3 (Z_to_bv 64 hdw) xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
             F (Z_to_bv 64 (X2B_ENTRY + 544)) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SPA - 16)) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
               (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               xs2 xs3 (Z_to_bv 64 hdw) xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
          F (Z_to_bv 64 (X2B_ENTRY + 508)) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros STL MI FRA TLC HR HTL HTL2 HHW HM HMTL FL FC F64 FH RF KERR KTL KOK.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (spb_props SP SP16) as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    assert (LM : Z.land hdw 255 = mtl)
      by (rewrite <- HM; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity).
    lazymatch goal with |- context [Z_to_bv 64 (X2B_ENTRY + ?k)] =>
      let v := eval vm_compute in (X2B_ENTRY + k) in change (X2B_ENTRY + k) with v end.
    unfold X2BFRA0 in FRA.
    pose proof (munch_refl [(SPA + 208, SPA + 216)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. zstep. zstep. bcase K0.
    all: rewrite ?unsigned_lit_wrap in K0; rewrite ?(Z.mod_small r) in K0 by lia;
         rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt in K0.
    { apply evtF_done. replace (SPA - 16 + 16) with SPA by lia. apply KERR. lia. }
    assert (RL : r <= 2^64 - 120) by lia. specialize (HTL2 RL). specialize (TLC RL).
    do 6 zstep.
    rewrite ?sx32_small in * by lia. rewrite ?LM in *.
    bcase K1.
    all: rewrite ?unsigned_lit in K1 by lia; rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt in K1.
    all: apply evtF_done; replace (SPA - 16 + 16) with SPA by lia.
    - eapply KTL; [lia| lia| | eassumption| eassumption| unfold X2BFRA1; eassumption].
      eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia.
    - eapply KOK; [lia| lia| | eassumption| eassumption| unfold X2BFRA1; eassumption].
      eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia.
  Qed.

  End S.
End CANSEC1.
