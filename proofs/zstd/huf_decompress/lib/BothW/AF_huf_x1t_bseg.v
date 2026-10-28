(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Lemma sdw8_c1sX : forall m s, rw_cells bsegs m s [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m s [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_X1PC : Z := 0xb2db0.
Definition X1_MAGIC_LIVE : Z := 0x41b58ab3.
Definition X1_DESC : Z := 0x11394.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - 336 - 4096 - 16.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition SPA1 : Z := (SP - 320) - (SP - 320) mod 32.
  Lemma spa1_props : SP - 336 <= SPA1 <= SP - 320 /\ SPA1 mod 32 = 0 /\ (SP + -320) - (SP + -320) mod 2^5 = SPA1.
  Proof. unfold SPA1. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

  Definition X1SAVED : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition X1SH : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551603)].

  Notation RET mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (ret_pc ra) fc None mm (seg_rom bsegs)).

  Lemma x1_epi : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      m (FF FLG r : Z) (j0 : word),
    rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) X1SH ->
    rw_cells bsegs m FF [C8 j0] -> rw_cells bsegs m (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m (SP + -104) X1SAVED ->
    rw_cells bsegs m (SPA1 + 24) [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF)] ->
    stk bsegs m lo (SPA1 + 24) -> stk bsegs m (SPA1 + 40) (SP + -104) -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= FF \/ FF + 64 <= FLG) ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG FLG 1 -> 0 <= r < 2^64 ->
    evtF bsegs RNG (fun ms' => exists mp m' x10' x12',
        ms' = RET m' x5 x6 x7 (Z_to_bv 64 r) x10' x12' x13 x14 x15 x16 x17 x28 x29 x30 x31
        /\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 SPA1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 x20 x21 (Z_to_bv 64 r) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x80618) fc None m (seg_rom bsegs)).
  Proof.
    intros until j0. intros SHF FF0 FF56 FLC FRB FRA STL STG MI FH FC F64 GH GC GF RF RSF RG Hr.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in *.
    unfold X1SH in SHF. unfold X1SAVED in FRB.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof spa1_props as (SPAB & SPA32 & _).
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
    zstep. zstep. zstep.
    do 13 zstep. zstep. zstep.
    apply stk_of_rw_cells in FRA. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA1 + 24) (SPA1 + 40) STL ltac:(replace (SPA1 + 40) with (SPA1 + 24 + 16) by lia; exact FRA) ltac:(lia)) as ST1;
      pose proof (stk_merge bsegs mx lo (SPA1 + 40) (SP + -104) ST1 STG ltac:(lia)) as ST2 end.
    release_frame FRB ST2 SP.
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    eexists _, _, _, _. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM1|]. split; [exact MIp|].
    split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
    split; [exact ST2| exact FLC].
  Qed.

  Lemma x1_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xba300)] -> rw_cells bsegs m 0xba300 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA jB,
        ms' = MS (mkR (Z_to_bv 64 0x80320) (Z_to_bv 64 SPA1) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPA1)
                     (Z_to_bv 64 64) (Z_to_bv 64 0xba2f8) (Z_to_bv 64 1) a3 a4 a5 a6 a0
                     a0 (Z_to_bv 64 2147450880) s4 a4 s6 s7 a2 a1 a5 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x3cc38) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 336, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) X1SAVED
        /\ rw_cells bsegs m' SPA1 [CB 96 jA; C8 a3; CB 112 jB]
        /\ stk bsegs m' lo SPA1 /\ stk bsegs m' (SPA1 + 216) (SP + -104))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80298) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_R in *.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof spa1_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 336, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.
    carve_frame 104%nat ST. carve_frame 216%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    release_frame FR0 ST (SP + -104).
    destruct (stk_split bsegs _ lo (SPA1 + 216) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA1 + 216) 216 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 216) with 216 in STL, FRA. replace (SPA1 + 216 - 216) with SPA1 in STL, FRA by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 216 _ [] [96; 8; 112]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
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
    zstep. zstep. zstep.
    apply evtF_done.
    eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR|]. split; [eassumption|]. split; [exact STL| exact STG].
  Qed.
  Definition X1FFHDR (FLG : Z) (j3 j5 j6 : list byte) (tlw nbw : word) : list cell :=
    [C8 (Z_to_bv 64 X1_MAGIC_LIVE); C8 (Z_to_bv 64 X1_DESC); C8 (Z_to_bv 64 0x80298); CB 8 j3; C4 tlw; CB 12 j5; C4 nbw; CB 4 j6; C8 (Z_to_bv 64 FLG)].
  Definition X1FRA (FF DT WK : Z) (jA jC jD jB jE : list byte) : list cell :=
    [CB 24 jA; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); CB 16 jC; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DT); CB 24 jD;
     C8 (Z_to_bv 64 WK); CB 80 jB; C8 (Z_to_bv 64 (DT + 4)); CB 16 jE; C8 (Z_to_bv 64 FF)].

  Lemma x1_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 flags : word) m (FF FLG DT WK wksz SRC n : Z)
      (j0 j1 j2 : word) (junk jA jB : list byte) (Q : machine_state -> Prop),
    rw_cells bsegs m SPA1 [CB 96 jA; C8 (Z_to_bv 64 WK); CB 112 jB] -> stk bsegs m lo SPA1 ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m AGOT_X1PC [C8 (Z_to_bv 64 0x80298)] -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    0 <= wksz < 2^32 -> 4096 <= WK -> WK < 2^47 -> WK mod 4 = 0 -> 4096 <= DT -> DT + 4 < 2^47 ->
    (forall m' (jA' jC jD jB' jE j3 j5 j6 : list byte) (y10 y11 y12 y13 y14 y15 y16 y17 : word),
        wksz < 1492 ->
        munch [(SPA1 - 16, SPA1 + 216); (FF, FF + 56); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' SPA1 (X1FRA FF DT WK jA' jC jD jB' jE) -> stk bsegs m' lo SPA1 ->
        rw_cells bsegs m' FF (X1FFHDR FLG j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0)) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) X1SH ->
        Q (MS (mkR (Z_to_bv 64 0x80320) (Z_to_bv 64 SPA1) gp tp (Z_to_bv 64 FF) x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA1)
                   y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 wksz) (Z_to_bv 64 18446744073709551572)
                   s7 (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x80618) fc None m' (seg_rom bsegs))) ->
    (forall m' (jA' jC jD jB' jE j3 j5 j6 : list byte),
        1492 <= wksz ->
        munch [(SPA1 - 16, SPA1 + 216); (FF, FF + 56); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' SPA1 (X1FRA FF DT WK jA' jC jD jB' jE) -> stk bsegs m' lo (SPA1 - 16) ->
        rw_cells bsegs m' (SPA1 - 16) [C8 (Z_to_bv 64 876); C8 flags] ->
        rw_cells bsegs m' FF (X1FFHDR FLG j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0)) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) X1SH ->
        Q (MS (mkR (Z_to_bv 64 0x80454) (Z_to_bv 64 (SPA1 - 16)) gp tp (Z_to_bv 64 FF) x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA1)
                   (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 256) (Z_to_bv 64 WK) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 (WK + 104))
                   (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572)
                   (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31)
              F (Z_to_bv 64 0x9733c) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 0x80320) (Z_to_bv 64 SPA1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA1)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 DT) (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 wksz) s6 s7 (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x80320) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros FRA STL FFC SHF GPC MI FH FC F64 RF RSF WR WKL WKH WK4 DTL DTH KEXIT KCALL.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    unfold AGOT_X1PC in *. pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof spa1_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply sdw8_c1sX in SHF. replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(SPA1 - 16, SPA1 + 216); (FF, FF + 56); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    apply (rw_cells_split_CB bsegs _ _ [] 96 _ [C8 (Z_to_bv 64 WK); CB 112 jB] [24; 8; 8; 16; 8; 8; 24]%nat) in FRA; [| reflexivity].
    cbn [mk_CB_cells app] in FRA.
    lazymatch type of FRA with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; CB 112 ?j] =>
      apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7] 112 j [] [80; 8; 16; 8]%nat) in FRA; [| reflexivity] end.
    cbn [mk_CB_cells app] in FRA.
    apply (rw_cells_split_CB bsegs _ _ [C8 j0; C8 j1; C8 j2] 32 junk [C8 (Z_to_bv 64 FLG)] [8; 4; 12; 4; 4]%nat) in FFC; [| reflexivity].
    cbn [mk_CB_cells app] in FFC.
    zstep.
    zstep.
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
    zstep. zstep.
    do 7 zstep.
    zstep.
    zstep. zstep.
    zstep. zstep. zstep.
    zstep. zstep.
    rewrite (Z.shiftr_div_pow2 FF 3) in * by lia. change (2^3) with 8 in *.
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
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
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep. bcase KG; [| exfalso; rewrite ?unsigned_lit in KG by lia; lia].
    zstep.
    zstep. replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 18446744073709551572) by (apply Z_to_bv_eqm; reflexivity).
    zstep. bcase KW.
    -
      zstep. zstep.
      zstep. bcase KZ; [| exfalso; clear - KZ WKL WKH; lia].
      zstep.
      zstep. bcase KA; [| exfalso; apply KA; clear - WK4 WKL WKH;
                         change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4; rewrite WK4; reflexivity].
      do 4 zstep.
      zstep.
      carve_frame 16%nat STL.
      zstep. zstep.
      zstep. zstep.
      do 6 zstep.
      replace (FF / 8 + 2147450880) with (Z.shiftr FF 3 + 2147450880) in * by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      replace (SPA1 + -16) with (SPA1 - 16) in * by lia.
      apply evtF_done. eapply KCALL; [lia| | exact WM| eassumption| | | | |];
        [ eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia
        | unfold X1FRA; eassumption
        | eassumption
        | eassumption
        | unfold X1FFHDR, X1_MAGIC_LIVE, X1_DESC; eassumption
        | unfold X1SH; eassumption ].
    -
      zstep. zstep.
      replace (FF / 8 + 2147450880) with (Z.shiftr FF 3 + 2147450880) in * by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      apply evtF_done. eapply KEXIT; [lia| | exact WM| eassumption| | exact STL| |];
        [ eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia
        | unfold X1FRA; eassumption
        | unfold X1FFHDR, X1_MAGIC_LIVE, X1_DESC; eassumption
        | unfold X1SH; eassumption ].
  Qed.
End S.
End CANSEC1.
