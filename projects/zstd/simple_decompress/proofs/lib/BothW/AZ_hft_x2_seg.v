(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseRdKit FseRdKit2 StrFun.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AZ_kx AZ_hft_x2_geo.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma hdr_le4 : forall (b0 b1 b2 b3 : byte),
  b0 = Z_to_bv 8 12 ->
  exists hdw, hdw mod 256 = 12 /\ 0 <= hdw < 2^32 /\ [b0; b1; b2; b3] = le4 (Z_to_bv 64 hdw).
Proof.
  intros b0 b1 b2 b3 E0.
  pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R1, R2, R3.
  exists (12 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
  split; [Z.div_mod_to_equations; lia|]. split; [lia|].
  symmetry. apply le4_of_mod32; [reflexivity|]. rewrite unsigned_lit by lia. cbn [le_val map]. subst b0. rewrite (byte_lit 12) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

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

  Notation SPA := (SPA2 SP).
  Notation X2SAVED' := (X2SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation RET mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (ret_pc ra) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma x2_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xd4300)] -> rw_cells bsegs m 0xd4300 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA jB,
        ms' = MS (mkR (Z_to_bv 64 0x993d8) (Z_to_bv 64 SPA) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                     (Z_to_bv 64 64) (Z_to_bv 64 0xd42f8) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     a1 (Z_to_bv 64 2147450880) a0 a2 s6 a4 s8 a5 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x3ef30) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 528, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) X2SAVED'
        /\ rw_cells bsegs m' SPA [CB 352 jA; C8 a3; CB 48 jB]
        /\ stk bsegs m' lo SPA /\ stk bsegs m' (SPA + 408) (SP + -104))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99354) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_R in *.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof (spa2_props SP SP16) as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 528, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 408%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    (* [comment removed for export] *)
    release_frame FR0 ST (SP + -104).
    destruct (stk_split bsegs _ lo (SPA + 408) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA + 408) 408 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 408) with 408 in STL, FRA. replace (SPA + 408 - 408) with SPA in STL, FRA by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 408 _ [] [352; 8; 48]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR|]. split; [eassumption|]. split; [exact STL| exact STG].
  Qed.
  (* [comment removed for export] *)
  Definition X2FFHDR (FLG : Z) (j3 : list byte) : list cell :=
    [C8 (Z_to_bv 64 X2_MAGIC_LIVE); C8 (Z_to_bv 64 X2_DESC); C8 (Z_to_bv 64 0x99354); CB 32 j3; C8 (Z_to_bv 64 FLG)].
  (* [comment removed for export] *)
  Definition X2FRA0 (FF DT WK : Z) (jA jB jC jT jD jE : list byte) : list cell :=
    [CB 128 jA; C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); CB 32 jB; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF);
     CB 8 jC; C8 (Z_to_bv 64 (WK + 676)); CB 8 jT; C8 (Z_to_bv 64 DT); CB 128 jD; C8 (Z_to_bv 64 WK); CB 40 jE; C8 (Z_to_bv 64 FF)].

  (* [comment removed for export] *)
  Lemma x2_hdr1 : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 xs6 xs8 xs10 xs11 flags : word) m (FF FLG DT WK wksz SRC n : Z)
      (j0 j1 j2 : word) (junk jA jB : list byte) (dtb : list byte) (Q : machine_state -> Prop),
    rw_cells bsegs m SPA [CB 352 jA; C8 (Z_to_bv 64 WK); CB 48 jB] -> stk bsegs m lo SPA ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m AGOT_X2PC [C8 (Z_to_bv 64 0x99354)] -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    u8arr bsegs m DT dtb -> zlen dtb = 16388 -> nth_error dtb 0 = Some (Z_to_bv 8 12) ->
    unpoisoned m DT (DT + 16388) -> ablk DT (DT + 16388) -> 4096 <= DT -> DT + 16388 < 2^47 -> DT mod 4 = 0 -> (DT + 16388 <= FF \/ FF + 64 <= DT) -> (DT + 16388 <= lo \/ SP <= DT) ->
    rng RNG DT 16388 -> rng RNG (shad DT) 1 ->
    0 <= wksz < 2^32 -> 4096 <= WK -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
    (forall m' (j3 : list byte) (y12 : word),
        wksz < 2124 ->
        munch [(SPA, SPA + 408); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' (SPA + 168) [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
        stk bsegs m' lo (SPA + 168) -> stk bsegs m' (SPA + 192) (SPA + 408) ->
        rw_cells bsegs m' FF (X2FFHDR FLG j3) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) X2SH ->
        u8arr bsegs m' DT dtb ->
        Q (MS (mkR (Z_to_bv 64 0x993d8) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                   (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 531) y12 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
                   (Z_to_bv 64 X2_MAGIC_LIVE) (Z_to_bv 64 FF)
                   (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 DT) (Z_to_bv 64 n) xs6 (Z_to_bv 64 wksz) xs8 flags xs10 xs11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x9a1e8) fc None m' (seg_rom bsegs))) ->
    (forall m' (j3 jA' jB' jC jT jD jE : list byte) (hdw : Z),
        2124 <= wksz -> hdw mod 256 = 12 -> 0 <= hdw < 2^32 -> firstn 4 dtb = le4 (Z_to_bv 64 hdw) ->
        munch [(SPA, SPA + 408); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' SPA (X2FRA0 FF DT WK jA' jB' jC jT jD jE) -> stk bsegs m' lo SPA ->
        rw_cells bsegs m' FF (X2FFHDR FLG j3) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) X2SH ->
        u8arr bsegs m' DT dtb ->
        Q (MS (mkR (Z_to_bv 64 0x99500) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                   (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 0) (Z_to_bv 64 112) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
                   (Z_to_bv 64 X2_MAGIC_LIVE) (Z_to_bv 64 FF)
                   (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 hdw) (Z_to_bv 64 n) (Z_to_bv 64 12) (Z_to_bv 64 WK) xs8 flags (Z_to_bv 64 (WK + 624)) xs11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x53d44) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 0x993d8) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 DT) (Z_to_bv 64 n) xs6 (Z_to_bv 64 wksz) xs8 flags xs10 xs11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x993d8) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros FRA STL FFC SHF GPC MI FH FC F64 RF RSF DTC DTLEN DT0 UD ABD DTL DTH DT4 DFD SDS RDT RSD1 WR WKL WKH WK4 KEXIT KCALL.
    pose proof ABD as ABDu. unfold ablk, AIMG_HI, KLS in ABDu.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    unfold AGOT_X2PC in *. pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (spa2_props SP SP16) as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply shadow8_c1sA in SHF. replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(SPA, SPA + 408); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 352 _ [C8 (Z_to_bv 64 WK); CB 48 jB] [128; 8; 32; 8; 8; 8; 8; 8; 8; 8; 128]%nat) in FRA; [| reflexivity].
    cbn [mk_CB_cells app] in FRA.
    lazymatch type of FRA with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; CB 48 ?j] =>
      apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] 48 j [] [40; 8]%nat) in FRA; [| reflexivity] end.
    cbn [mk_CB_cells app] in FRA.
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    do 6 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    rewrite (Z.shiftr_div_pow2 FF 3) in * by lia. change (2^3) with 8 in *.
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (FF / 8 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 4%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (FF / 8 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase KA.                              (* [comment removed for export] *)
    { exfalso. apply KA. clear - DT4 DTL. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4. exact DT4. }
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MUx : munch _ m mx |- _ =>
        assert (UMx : unpoisoned mx DT (DT + 16388));
          [eapply unpoisoned_munch; [exact UD| exact MUx|]; rewrite !shad_div; cbn [disjoint_from]; unfold ASHOFF;
           refine (conj _ (conj _ (conj _ I))); clear - DFD F64 DTL DTH FHu ABDu SDS SPAB LOS LO0 ATR BSF SPT LOC; Z.div_mod_to_equations; lia |]
      end end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (chk1A mx DT (DT + 16388) DT 4 UMx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - DT4; Z.div_mod_to_equations; lia)) as (b & RDB & CK & SR) end.
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (JOIN : forall y10 y11 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x993d8) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
          y10 y11 (Z_to_bv 64 0x99354) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
          (Z_to_bv 64 1102416563) (Z_to_bv 64 FF)
          (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 DT) (Z_to_bv 64 n) xs6 (Z_to_bv 64 wksz) xs8 flags xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x99490) fc None mx (seg_rom bsegs))) end.
    { intros y10 y11. clear RDB CK SR.
      zstep.                                      (* [comment removed for export] *)
      zstep. replace (Z_to_bv 64 (-4)) with (Z_to_bv 64 18446744073709551612) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. bcase KD4; [exfalso; clear - KD4 DTL DTH; lia|].   (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. bcase KD0; [exfalso; clear - KD0 DTL DTH; lia|].   (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      zstep. bcase KW.                            (* [comment removed for export] *)
      - (* [comment removed for export] *)
        zstep.                                    (* [comment removed for export] *)
        zstep. bcase KZ; [exfalso; clear - KZ WKL; lia|].   (* [comment removed for export] *)
        zstep.                                    (* [comment removed for export] *)
        zstep. bcase KA2; [exfalso; apply KA2; clear - WK4 WKL; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4; exact WK4|].   (* [comment removed for export] *)
        zstep.                                    (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (-5)) with (Z_to_bv 64 18446744073709551611) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
        zstep.                                    (* [comment removed for export] *)
        zstep. bcase KB; [exfalso; clear - KB WKL WKH WR; lia|].   (* [comment removed for export] *)
        zstep.                                    (* [comment removed for export] *)
        (* [comment removed for export] *)
        assert (X4 : exists b1 b2 b3 dtl, dtb = Z_to_bv 8 12 :: b1 :: b2 :: b3 :: dtl).
        { destruct dtb as [| b0 [| b1 [| b2 [| b3 dtl]]]]; [cbn in DTLEN; lia| cbn in DTLEN; lia| cbn in DTLEN; lia| cbn in DTLEN; lia|].
          cbn in DT0. injection DT0 as E0. exists b1, b2, b3, dtl. rewrite E0. reflexivity. }
        destruct X4 as (b1 & b2 & b3 & dtl & EDT).
        destruct (hdr_le4 (Z_to_bv 8 12) b1 b2 b3 eq_refl) as (hdw & HM & HR & E4).
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?my _) =>
          lazymatch goal with DC : u8arr bsegs my DT _ |- _ =>
          assert (RDW : ov_read_bytes bsegs my (Z_to_bv 64 (DT + 0)) 4 = Some (le4 (Z_to_bv 64 hdw)))
            by (rewrite <- E4; destruct DC as [BA _]; rewrite EDT in BA; exact (bytes_at_read bsegs my DT _ 0 4 BA ltac:(lia) ltac:(cbn; lia))) end end.
        zstep.                                    (* [comment removed for export] *)
        replace (zx32 (Z_to_bv 64 hdw)) with (Z_to_bv 64 hdw) by (unfold zx32; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
        clear RDW.
        zstep.                                    (* [comment removed for export] *)
        replace (Z.land hdw 255) with 12 by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; symmetry; exact HM).
        zstep. zstep.                             (* [comment removed for export] *)
        zstep. zstep. zstep.                      (* [comment removed for export] *)
        zstep.                                    (* [comment removed for export] *)
        replace (FF / 8 + 2147450880) with (Z.shiftr FF 3 + 2147450880) in * by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).

        apply evtF_done.
        eapply KCALL; [rewrite Z.shiftr_div_pow2 in KW by lia; clear - KW WR; Z.div_mod_to_equations; lia| exact HM| exact HR| rewrite EDT; exact E4| | exact WM| eassumption| | exact STL| | |eassumption];
            [ eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia
            | unfold X2FRA0; eassumption
            | unfold X2FFHDR, X2_MAGIC_LIVE, X2_DESC; eassumption
            | unfold X2SH; eassumption ].
      - (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
        zstep.                                    (* [comment removed for export] *)
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
            | unfold X2FFHDR, X2_MAGIC_LIVE, X2_DESC; eassumption
            | unfold X2SH; eassumption ]. }
    (* [comment removed for export] *)
    zstep. if_cases G; zify_cond G.
    - zstep. zstep. zstep. if_cases G'; zify_cond G'.     (* [comment removed for export] *)
      + apply JOIN.
      + (* [comment removed for export] *)
        exfalso. rewrite (signed_lit_small64 (sval b)) in G' by (clear - SR; lia).
        change 7 with (Z.ones 3) in G'. rewrite Z.land_ones in G' by lia. change (2^3) with 8 in G'.
        rewrite (signed_lit_small64 (DT mod 8 + 3)) in G' by (Z.div_mod_to_equations; lia).
        clear - CK G G' SR. Z.div_mod_to_equations. lia.
    - apply JOIN.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_hdr2 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 xs8 xs11 flags : word) m (FF DT WK SRC n hdw : Z)
      (jA jB jC jT jD jE : list byte) (Q : machine_state -> Prop),
    stk bsegs m lo SPA -> mem_inv bsegs m -> rw_cells bsegs m SPA (X2FRA0 FF DT WK jA jB jC jT jD jE) ->
    (forall m',
        munch [(SPA - 16, SPA)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
        stk bsegs m' lo (SPA - 16) -> rw_cells bsegs m' (SPA - 16) [C8 (Z_to_bv 64 876); C8 flags] ->
        rw_cells bsegs m' SPA (X2FRA0 FF DT WK jA jB jC jT jD jE) ->
        Q (MS (mkR (Z_to_bv 64 0x99550) (Z_to_bv 64 (SPA - 16)) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
                   (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 256) (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 (WK + 1248))
                   (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 hdw) (Z_to_bv 64 n) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 WK) (Z_to_bv 64 (WK + 992)) flags (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
              F (Z_to_bv 64 0xaeb6c) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 SRC) (Z_to_bv 64 2147450880) (Z_to_bv 64 hdw) (Z_to_bv 64 n) (Z_to_bv 64 12) (Z_to_bv 64 WK) xs8 flags (Z_to_bv 64 (WK + 624)) xs11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x99500) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros STL MI FRA KCALL.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (spa2_props SP SP16) as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    pose proof (munch_refl [(SPA - 16, SPA)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold X2FRA0 in FRA.
    zstep. zstep. replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 18446744073709551572) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    carve_frame 16%nat STL.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    do 7 zstep.                                   (* [comment removed for export] *)
    replace (SPA + -16) with (SPA - 16) in * by lia.
    apply evtF_done. eapply KCALL; [| exact WM| eassumption| eassumption| eassumption| exact FRA].
    eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_epi : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      m (FF FLG r : Z) (j0 : word),
    rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) X2SH ->
    rw_cells bsegs m FF [C8 j0] -> rw_cells bsegs m (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m (SP + -104) X2SAVED' ->
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
          F (Z_to_bv 64 0x9a1e8) fc None m (seg_rom bsegs)).
  Proof.
    intros until j0. intros SHF FF0 FF56 FLC FRB FRA STL STG MI FH FC F64 GH GC GF RF RSF RG Hr.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in *.
    unfold X2SH in SHF. unfold X2SAVED in FRB.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (spa2_props SP SP16) as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m) as MU1.
    pose proof (wmono_refl bsegs m) as WM1.
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 4%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK.                             (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (bx (mem_inv bsegs mx)) in MIp end end.
    lazymatch type of MU1 with ?T => change T with (bx T) in MU1 end.
    lazymatch type of WM1 with ?T => change T with (bx T) in WM1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    do 13 zstep. zstep. zstep.                    (* [comment removed for export] *)
    (* [comment removed for export] *)
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
End S.
End CANSEC1.
