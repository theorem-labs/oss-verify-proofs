(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_FDWPC : Z := 0xb2da8.     (* [comment removed for export] *)

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - 272 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition SPAf : Z := (SP - 256) - (SP - 256) mod 32.
  Lemma spa_propsF : SP - 272 <= SPAf <= SP - 256 /\ SPAf mod 32 = 0 /\ (SP + -256) - (SP + -256) mod 2^5 = SPAf.
Proof. unfold SPAf. change (2^5) with 32. Z.div_mod_to_equations.
lia. Qed.

  Definition FRBf : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma fdw_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xba300)] -> rw_cells bsegs m 0xba300 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' (k0 k56 : list byte),
        ms' = MS (mkR (Z_to_bv 64 0x981e8) (Z_to_bv 64 SPAf) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPAf)
                     (Z_to_bv 64 64) (Z_to_bv 64 0xba2f8) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 2147450880) a1 a3 a5 a6 a2 a4 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x3cc38) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 272, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) FRBf /\ rw_cells bsegs m' SPAf [CB 48 k0; C8 a0; CB 96 k56]
        /\ stk bsegs m' lo SPAf /\ stk bsegs m' (SPAf + 152) (SP + -104))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x98160) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_R in *.
  unfold KEND in SPT. pose proof atop_range as ATR.
  pose proof spa_propsF as (SPAB & SPA32 & ESPA').
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(SP - 272, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep.
  carve_frame 104%nat ST. carve_frame 152%nat ST.
  zstep.
  do 13 zstep.
  zstep.
  zstep.
  change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
  release_frame FR0 ST (SP + -104).
  destruct (stk_split bsegs _ lo (SPAf + 152) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
  destruct (stk_carve bsegs _ lo (SPAf + 152) 152 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
  change (Z.of_nat 152) with 152 in STL, FRA. replace (SPAf + 152 - 152) with SPAf in STL, FRA by lia.
  pose proof (rw_cells_split_CB bsegs _ SPAf [] 152 jA [] [48; 8; 96]%nat FRA eq_refl) as FRA2.
  cbn [app mk_CB_cells] in FRA2. clear FRA.
  do 7 zstep.
  zstep. zstep.
  zstep. zstep.
  clear GOT GSU.
  zstep. rewrite (sx32_small 1) by lia.
  zstep.
  zstep.
  zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
  zstep. zstep.
  apply evtF_done.
  do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact FR|]. split; [exact FRA2|]. split; [exact STL| exact STG].
Qed.

  (* [comment removed for export] *)
  Definition FDHDR (FF FLG : Z) (j24 j52 : list byte) : list cell :=
    [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1d69d); C8 (Z_to_bv 64 0x98160); CB 24 j24;
     C4 (Z_to_bv 64 255); CB 4 j52; C8 (Z_to_bv 64 FLG)].
  Definition FDSH : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551603)].

  (* [comment removed for export] *)
  Lemma fdw_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (FF FLG DST dcap S size maxLog W wks : Z)
      (j0 j1 j2 : word) (junk : list byte) (k0 k56 : list byte) (Q : machine_state -> Prop),
    rw_cells bsegs m SPAf [CB 48 k0; C8 (Z_to_bv 64 DST); CB 96 k56] ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m AGOT_FDWPC [C8 (Z_to_bv 64 0x98160)] -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    0 <= wks < 2^64 -> 0 < W < 2^47 -> W mod 8 = 0 ->
    (forall m' (j8 j64 j80 : list byte) (y11 y12 y13 y14 : word),
        wks < 512 ->
        munch [(SPAf, SPAf + 152); (FF, FF + 64); (shad FF, shad FF + 8)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' SPAf [CB 48 j8; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880); CB 8 j64; C8 (Z_to_bv 64 FF); CB 72 j80] ->
        rw_cells bsegs m' FF (FDHDR FF FLG (firstn 24 junk) (skipn 28 junk)) ->
        rw_cells bsegs m' (shad FF) FDSH ->
        evtF bsegs RNG Q
          (MS (mkR (Z_to_bv 64 0x981e8) (Z_to_bv 64 SPAf) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAf)
                   (Z_to_bv 64 (-1)) y11 y12 y13 y14 x15 (Z_to_bv 64 FF) x17
                   (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 (W + 512)) (Z_to_bv 64 dcap)
                   (Z_to_bv 64 size) (Z_to_bv 64 W) (Z_to_bv 64 wks) (Z_to_bv 64 S) (Z_to_bv 64 maxLog) s11
                   x28 x29 x30 x31)
              F (Z_to_bv 64 0x98320) fc None m' (seg_rom bsegs))) ->
    (forall m' (j0' j64 j80 : list byte),
        512 <= wks ->
        munch [(SPAf, SPAf + 152); (FF, FF + 64); (shad FF, shad FF + 8)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' SPAf [CB 32 j0'; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST);
                                C8 (Z_to_bv 64 2147450880); CB 8 j64; C8 (Z_to_bv 64 FF); CB 72 j80] ->
        rw_cells bsegs m' FF (FDHDR FF FLG (firstn 24 junk) (skipn 28 junk)) ->
        rw_cells bsegs m' (shad FF) FDSH ->
        evtF bsegs RNG Q
          (MS (mkR (Z_to_bv 64 0x98300) (Z_to_bv 64 SPAf) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAf)
                   (Z_to_bv 64 W) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 size)
                   (Z_to_bv 64 0) (Z_to_bv 64 FF) x17
                   (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (W + 512)) (Z_to_bv 64 dcap)
                   (Z_to_bv 64 size) (Z_to_bv 64 W) (Z_to_bv 64 wks) (Z_to_bv 64 S) (Z_to_bv 64 maxLog) (Z_to_bv 64 (FF + 48))
                   x28 x29 x30 x31)
              F (Z_to_bv 64 0x969fc) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 0x981e8) (Z_to_bv 64 SPAf) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAf)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               s2 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 dcap) (Z_to_bv 64 size) (Z_to_bv 64 W) (Z_to_bv 64 wks)
               (Z_to_bv 64 S) (Z_to_bv 64 maxLog) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x981e8) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros FRA FFC SHF GPC MI FH FC F64 RF RSF WK W0 W8 K1 K2.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
  unfold AGOT_FDWPC in *. pose proof atop_range as ATR. unfold KEND in SPT.
  pose proof spa_propsF as (SPAB & SPA32 & _).
  pose proof (cells_at_wf bsegs _ _ _ (proj1 FFC)) as LJ. cbn [cells_wf cell_wf] in LJ.
  destruct LJ as (_ & _ & _ & LJ & _).
  apply shadow8_c1sA in SHF.
  replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF, K1, K2 by (unfold shad, ASHOFF; lia).
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
  pose proof (rw_cells_split_CB bsegs m SPAf [CB 48 k0; C8 (Z_to_bv 64 DST)] 96 k56 [] [8; 8; 8; 72]%nat FRA eq_refl) as FRA1.
  cbn [app mk_CB_cells] in FRA1. clear FRA.
  pose proof (rw_cells_split_CB bsegs m SPAf [] 48 k0 _ [32; 8; 8]%nat FRA1 eq_refl) as FRA.
  cbn [app mk_CB_cells] in FRA. clear FRA1.
  pose proof (rw_cells_split_CB bsegs m FF [C8 j0; C8 j1; C8 j2] 32 junk [C8 (Z_to_bv 64 FLG)] [24; 4; 4]%nat FFC eq_refl) as FFC1.
  cbn [app mk_CB_cells] in FFC1. clear FFC.
  pose proof (munch_refl [(SPAf, SPAf + 152); (FF, FF + 64); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep.
  zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
  do 8 zstep.
  replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
  replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
  do 3 zstep.
  zstep.
  zstep.
  do 4 zstep.
  zstep.
  zstep.
  zstep.
  replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
      pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
  zstep. clear SOK.
  do 7 zstep.
  zstep. if_cases G1; zify_cond G1; [| exfalso; lia].
  do 4 zstep. zstep.
  replace (0 <? W) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 <? W + 512) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.b2z]. change (Z.lxor 1 1) with 0. if_true.
  zstep. zstep. if_cases G; zify_cond G.
  - zstep. zstep.
    replace (bv_eqb (Z_to_bv 64 W) (Z_to_bv 64 0)) with false
      by (symmetry; rewrite bv_eqb_Z, !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
          apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
    change (negb false) with true. cbv iota.
    zstep.
    replace (Z.land W 1) with 0
      by (change 1 with (2^1 - 1); rewrite land_ones_mod by lia; change (2^1) with 2; symmetry; Z.div_mod_to_equations; lia).
    zstep. try if_true.
    do 9 zstep. zstep.
    eapply K2; [lia | exact MU | exact WM | assumption | eassumption | | eassumption].
    unfold FDHDR.
      replace (skipn 28 junk) with (firstn 4 (skipn 4 (skipn 24 junk)))
        by (clear - LJ; do 32 (destruct junk as [|? junk]; [cbn in LJ; lia|]); destruct junk; [reflexivity | cbn in LJ; lia]).
      eassumption.
  - zstep. zstep.
    lazymatch goal with H : rw_cells bsegs ?mx SPAf (CB 32 ?a :: CB 8 ?b :: CB 8 ?c :: ?post) |- _ =>
      pose proof (rw_cells_merge bsegs mx SPAf [] [CB 32 a; CB 8 b; CB 8 c] post H) as FRM end.
    cbn [app cells_size csize Nat.add] in FRM.
    eapply K1; [lia | exact MU | exact WM | assumption | exact FRM | | eassumption].
    unfold FDHDR.
      replace (skipn 28 junk) with (firstn 4 (skipn 4 (skipn 24 junk)))
        by (clear - LJ; do 32 (destruct junk as [|? junk]; [cbn in LJ; lia|]); destruct junk; [reflexivity | cbn in LJ; lia]).
      eassumption.
Qed.

  Notation RETf mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (ret_pc ra) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma fdw_epi : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) m (FF FLG : Z)
      (j0 : word) csA,
    rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) FDSH ->
    rw_cells bsegs m FF [C8 j0] -> rw_cells bsegs m (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m (SP + -104) FRBf -> rw_cells bsegs m SPAf csA -> cells_size csA = 152%nat ->
    stk bsegs m lo SPAf -> stk bsegs m (SPAf + 152) (SP + -104) -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= FF \/ FF + 64 <= FLG) ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG FLG 1 ->
    evtF bsegs RNG (fun ms' => exists mp m',
        ms' = RETf m' x5 x6 x7 x10 (Z_to_bv 64 FLG) x12 x13 x14 x15 (Z_to_bv 64 FF) x17 x28 x29 x30 x31
        /\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 SPAf) gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 FF) x17
               (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x98320) fc None m (seg_rom bsegs)).
Proof.
  intros until csA. intros SHF FF0 FF56 FLC FRB FRA CSZ STL STG MI FH FC F64 GH GC GF RF RSF RG.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in *.
  unfold FDSH in SHF. unfold FRBf in FRB.
  pose proof atop_range as ATR. unfold KEND in SPT.
  pose proof spa_propsF as (SPAB & SPA32 & _).
  assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
  replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
  pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
  pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m) as MU1.
  pose proof (wmono_refl bsegs m) as WM1.
  zstep. try replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
  zstep. zstep.
  zstep. zstep. zstep.
  zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
  zstep. try replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
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
  eapply stk_release in FRA; [| exact STL| lia]. rewrite CSZ in FRA. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in FRA.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (stk_merge bsegs mx lo (SPAf + 152) (SP + -104) FRA STG ltac:(lia)) as ST2 end.
  release_frame FRB ST2 SP.
  apply evtF_done. unfold bx in MU1, WM1, MIp.
  eexists _, _. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM1|]. split; [exact MIp|].
  split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
  split; [exact ST2| exact FLC].
Qed.
End S.
End CANSEC1.
