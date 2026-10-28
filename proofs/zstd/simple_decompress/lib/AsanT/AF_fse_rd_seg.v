(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.
Ltac zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
  zify_bool K.

(* [comment removed for export] *)
Lemma land_align_downA : forall x j, 0 <= x < 2^64 -> 0 <= j <= 64 ->
  Z.land x (2^64 - 2^j) = x - x mod 2^j.
Proof.
  intros x j Hx Hj.
  replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
  2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
      replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
  rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition AGOT_SUAR_R : Z := 0xc7360.    (* [comment removed for export] *)
Definition AGOT_SHB_R : Z := 0xc7308.     (* [comment removed for export] *)
Definition AGOT_RDPC : Z := 0xc7f80.      (* [comment removed for export] *)

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - 176 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition SPAz : Z := (SP - 160) - (SP - 160) mod 32.
  Lemma spa_propsA : SP - 176 <= SPAz <= SP - 160 /\ SPAz mod 32 = 0 /\ (SP + -160) - (SP + -160) mod 2^5 = SPAz.
  Proof. unfold SPAz. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Definition RFRB : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma rd_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xcfd00)] -> rw_cells bsegs m 0xcfd00 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA,
    ms' = MS (mkR (Z_to_bv 64 0xaab40) (Z_to_bv 64 SPAz) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
    (Z_to_bv 64 64) (Z_to_bv 64 0xcfcf8) (Z_to_bv 64 1) a3 a4 a5 a6 a7
    s2 a1 a3 a0 a2 a4 (Z_to_bv 64 2147450880) s9 s10 s11 t3 t4 t5 t6)
    F (Z_to_bv 64 0x3ee8c) fc None m' (seg_rom bsegs)
    /\ munch [(SP - 176, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (SP + -104) RFRB /\ rw_cells bsegs m' SPAz [CB 56 jA]
    /\ stk bsegs m' lo SPAz /\ stk bsegs m' (SPAz + 56) (SP + -104))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xaaac0) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_R in *.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof spa_propsA as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 176, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 56%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    (* [comment removed for export] *)
    release_frame FR0 ST (SP + -104).
    destruct (stk_split bsegs _ lo (SPAz + 56) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPAz + 56) 56 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 56) with 56 in STL, FRA. replace (SPAz + 56 - 56) with SPAz in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                          (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  (* [comment removed for export] *)
  Definition RFFHDR (FF FLG : Z) (junk : list byte) : list cell :=
    [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 32 junk; C8 (Z_to_bv 64 FLG)].
  Definition RFFSH : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 18446744073709551608); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)].

  Lemma shadow8_c1sA : forall m s, rw_cells bsegs m s [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m s [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma rd_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) m (FF FLG MSVP BUF NC TLP hb : Z)
  (j0 j1 j2 : word) (junk : list byte) (jA : list byte) (Q : machine_state -> Prop),
  rw_cells bsegs m SPAz [CB 56 jA] ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m AGOT_RDPC [C8 (Z_to_bv 64 0xaaac0)] -> mem_inv bsegs m ->
    unpoisoned m MSVP (MSVP + 4) -> MSVP mod 4 = 0 -> ablk MSVP (MSVP + 4) -> (MSVP + 4 <= FF \/ FF + 64 <= MSVP) ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG (shad MSVP) 1 ->
    0 <= hb < 2^64 ->
    (forall m' j48 (y10 y11 y13 y14 : word),
    munch [(SPAz, SPAz + 56); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' SPAz [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
        rw_cells bsegs m' FF (RFFHDR FF FLG junk) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH ->
        Q (MS (mkR (Z_to_bv 64 0xaab40) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
        y10 y11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) y13 y14 x15 x16 x17
        (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb)
        (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (if 7 <? hb then 0xaac48 else 0xaabec)) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 0xaab40) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb)
               (Z_to_bv 64 2147450880) s9 s10 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xaab40) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros FRA FFC SHF GPC MI UM M4 BM MF FH FC F64 RF RSF RSM Hhb K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ BM) as (BMa & BMb & BMc & BMd). unfold AIMG_HI in *.
    unfold AGOT_RDPC in *. pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof spa_propsA as (SPAB & SPA32 & _).
    apply shadow8_c1sA in SHF. replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.   (* [comment removed for export] *)
    pose proof (munch_refl [(SPAz, SPAz + 56); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    zstep. zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    do 9 zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MUx : munch _ m mx |- _ =>
        assert (UMx : unpoisoned mx MSVP (MSVP + 4))
          by (eapply unpoisoned_munch; [exact UM| exact MUx|]; rewrite !shad_div; cbn [disjoint_from]; rewrite !Z.shiftr_div_pow2 by lia; unfold ASHOFF;
              change (2 ^ 3) with 8; refine (conj _ (conj _ (conj _ I))); Z.div_mod_to_equations; lia)
      end end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (chk1A mx MSVP (MSVP + 4) MSVP 4 UMx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK & SR) end.
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (JOIN : forall (y10 y11 : word),
        evtF bsegs RNG Q
          (MS (mkR (Z_to_bv 64 0xaab40) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
          y10 y11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551608) x15 x16 x17
          (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb)
          (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xaabe4) fc None mx (seg_rom bsegs)))
    end.
    { intros y10 y11. clear RDB CK SR.
      zstep. zstep.                               (* [comment removed for export] *)
      if_cases B; zify_cond B.
      - apply evtF_done. replace (7 <? hb) with true in K by (symmetry; apply Z.ltb_lt; lia).
        eapply K; eassumption.
      - apply evtF_done. replace (7 <? hb) with false in K by (symmetry; apply Z.ltb_ge; lia).
        eapply K; eassumption. }
    zstep. if_cases G; zify_cond G.               (* [comment removed for export] *)
    - zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN.
    - apply JOIN.
  Qed.

  (* [comment removed for export] *)
  Notation RET mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (ret_pc ra) fc None mm (seg_rom bsegs)).

  Definition bx (P : Prop) : Prop := P.

  Lemma rd_epi : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word) m (FF FLG : Z) (j0 : word) csA,
    rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH ->
    rw_cells bsegs m FF [C8 j0] -> rw_cells bsegs m (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m (SP + -104) RFRB -> rw_cells bsegs m SPAz csA -> cells_size csA = 56%nat ->
    stk bsegs m lo SPAz -> stk bsegs m (SPAz + 56) (SP + -104) -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= FF \/ FF + 64 <= FLG) ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG FLG 1 ->
    evtF bsegs RNG (fun ms' => exists mp m',
        ms' = RET m' x5 x6 x7 x11 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
        /\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xab14c) fc None m (seg_rom bsegs)).
  Proof.
    intros until csA. intros SHF FF0 FF56 FLC FRB FRA CSA STL STG MI FH FC F64 GH GC GF RF RSF RG.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in *.
    unfold RFFSH in SHF. unfold RFRB in FRB.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof spa_propsA as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m) as MU1.
    pose proof (wmono_refl bsegs m) as WM1.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    (* [comment removed for export] *)
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
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    do 13 zstep. zstep. zstep.                    (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply stk_release in FRA; [| exact STL| lia]. rewrite CSA in FRA. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPAz + 56) (SP + -104) FRA STG ltac:(lia)) as ST2 end.
    release_frame FRB ST2 SP.
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    eexists _, _. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM1|]. split; [exact MIp|].
    split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
    split; [exact ST2| exact FLC].
  Qed.

  (* [comment removed for export] *)
  Definition RFFSH0 : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)].

  (* [comment removed for export] *)
  Lemma c1z_unpoisoned : forall m A k, rw_cells bsegs m (Z.shiftr A 3 + 2147450880) [C1 (Z_to_bv 8 0)] -> A mod 8 = 0 ->
    0 <= A -> 0 <= k <= 8 -> A + 8 <= 2^47 -> unpoisoned m A (A + k).
  Proof.
    intros m A k H A8 A0 K8 AH. split; [lia|]. split; [lia|]. intros G H0 H1 H2.
    assert (EG : G = A / 8) by (Z.div_mod_to_equations; lia). subst G.
    exists (Z_to_bv 8 0). split.
    - unfold ASHOFF. rewrite Z.shiftr_div_pow2 in H by lia. change (2^3) with 8 in H.
      replace (2147450880 + A / 8) with (A / 8 + 2147450880) by lia.
      apply (rw_C1_high m _ _ H). Z.div_mod_to_equations; lia.
    - left. reflexivity.
  Qed.

  Lemma pad_tailA : forall (z : byte) k, (k <= 8)%nat -> firstn (8 - k) (skipn k (repeat z 8)) = repeat z (8 - k).
  Proof. intros z k Hk. do 9 (destruct k as [|k]; [reflexivity|]). lia. Qed.

  (* [comment removed for export] *)
  Lemma rd_small1 : forall (x10 x11 x12 x13 x14 x15 x27 x5 x6 x7 x16 x17 x28 x29 x30 x31 : word) m (FF FLG MSVP BUF NC TLP : Z)
  (buf : list Z) (junk : list byte) (RLO1 RHI1 : Z) (Q : machine_state -> Prop),
    0 <= zlen buf < 8 -> Forall (fun c => 0 <= c < 256) buf ->
    bytes_at bsegs m BUF (map (Z_to_bv 8) buf) ->
    rw_cells bsegs m FF (RFFHDR FF FLG junk) -> rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH ->
    mem_inv bsegs m -> stk bsegs m lo SPAz ->
    rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
    app_blk BUF (BUF + zlen buf) -> unpoisoned m BUF (BUF + zlen buf) ->
    (RLO1 <= BUF /\ BUF + zlen buf <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
    wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO1) (shad RHI1 - shad RLO1) ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> (BUF + zlen buf <= FF \/ FF + 64 <= BUF) -> ablk BUF (BUF + zlen buf) ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG BUF (zlen buf) ->
    (forall m' rs j16 (y5 y6 y7 y16 y17 y28 y29 y30 y31 : word),
        munch [(SPAz - 2224, SPAz); (FF + 24, FF + 56); (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' lo SPAz ->
        rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 8 rs;
                              CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - zlen buf)))); CB 16 j16; C8 (Z_to_bv 64 FLG)] ->
        rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH0 ->
        bytes_at bsegs m' BUF (map (Z_to_bv 8) buf) ->
        evtF bsegs RNG Q
          (MS (mkR (Z_to_bv 64 0xaac24) (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                   (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 8) (Z_to_bv 64 0) y16 y17
                   (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
                   (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 y28 y29 y30 y31)
                   F (Z_to_bv 64 0xaaac0) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 0xaab40) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xaabec) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros Hhb FBY HBUF FFC SHF MI ST GOT RIC SHB INI LAY REAL APPS UB HULL1 WR1 RSH1 FH FC F64 SEPB BBK RF RSF RB K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ BBK) as (BKa & BKb & BKc & BKd). unfold AIMG_HI in *.
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu. pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof spa_propsA as (SPAB & SPA32 & _).
    replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    unfold RFFHDR in FFC. unfold RFFSH in SHF.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB bsegs m FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0)] 32 junk
                  [C8 (Z_to_bv 64 FLG)] [8%nat; 8%nat; 16%nat] FFC eq_refl) as FF2.
    cbn [app mk_CB_cells] in FF2. clear FFC.
    pose proof (munch_refl [(SPAz - 2224, SPAz); (FF + 24, FF + 56); (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BBK as BBu. unfold ablk, AIMG_HI, KLS in BBu.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) buf)) = zlen buf) by (rewrite length_map; reflexivity).
    set (hb := zlen buf) in *. set (hbn := Z.to_nat hb).
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    change [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 72612); C8 (Z_to_bv 64 699072); CB 8 (firstn 8 junk);
            C8 (Z_to_bv 64 0); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]
      with ([C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 72612); C8 (Z_to_bv 64 699072); CB 8 (firstn 8 junk)]
            ++ [C8 (Z_to_bv 64 0)] ++ [CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]) in FF2.
    apply rd_rw_cells_appA in FF2. destruct FF2 as [FA FF2]. apply rd_rw_cells_appA in FF2. destruct FF2 as [FB FCc].
    cbn [cells_size csize Nat.add] in FB, FCc. change (Z.of_nat 32) with 32 in FB, FCc. change (Z.of_nat 8) with 8 in FCc.
    pose proof (rw_cells_merge bsegs _ (FF + 32) [] [C8 (Z_to_bv 64 0)] [] FB) as FM.
    cbn [app cells_size cells_bytes csize cbytes Nat.add] in FM. clear FB.
    change (le8 (Z_to_bv 64 0) ++ []) with (repeat (Z_to_bv 8 0) 8) in FM.
    pose proof (rw_cells_split_CB bsegs _ (FF + 32) [] 8 (repeat (Z_to_bv 8 0) 8) [] [hbn; (8 - hbn)%nat] FM ltac:(cbn [sum_nat]; lia)) as FS.
    cbn [app mk_CB_cells] in FS. clear FM.
    change [CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8)); CB (8 - hbn) (firstn (8 - hbn) (skipn hbn (repeat (Z_to_bv 8 0) 8)))]
      with ([CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8))] ++ [CB (8 - hbn) (firstn (8 - hbn) (skipn hbn (repeat (Z_to_bv 8 0) 8)))]) in FS.
    apply rd_rw_cells_appA in FS. destruct FS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
    replace (FF + 32 + Z.of_nat (hbn + 0)) with (FF + 32 + hb) in R2 by lia.
    (* [comment removed for export] *)
    assert (UD : unpoisoned m1 (FF + 32) (FF + 32 + hb)).
    { change [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
              C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603);
              C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)]
        with ([C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
               C1 (Z_to_bv 8 18446744073709551601)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 18446744073709551603);
               C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)]) in SHF.
      pose proof SHF as SH2. apply rd_rw_cells_appA in SH2. destruct SH2 as [_ SH2]. apply rd_rw_cells_appA in SH2. destruct SH2 as [SH4 _].
      cbn [cells_size csize Nat.add] in SH4.
      apply c1z_unpoisoned; [| Z.div_mod_to_equations; lia| lia| lia| lia].
      replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact SH4|].
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    destruct HULL1 as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
    assert (WR2 : wr_at bsegs m1 (shad FF) (shad (FF + 64) - shad FF)).
    { destruct SHF as [_ W]. cbn [cells_size csize Nat.add] in W. replace (shad FF) with (Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
      replace (shad (FF + 64) - (Z.shiftr FF 3 + 2147450880)) with (Z.of_nat 8); [exact W|].
      unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    assert (RSF2 : rng RNG (shad FF) (shad (FF + 64) - shad FF)).
    { replace (shad FF) with (Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
      replace (shad (FF + 64) - (Z.shiftr FF 3 + 2147450880)) with 8; [exact RSF|].
      unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    assert (UB1 : unpoisoned m1 BUF (BUF + hb)).
    { eapply unpoisoned_munch; [exact UB| exact MU|]. rewrite !shad_div. cbn [disjoint_from]. unfold ASHOFF.
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. refine (conj _ (conj _ (conj _ I))); Z.div_mod_to_equations; lia. }
    clear UB.
    eapply evtF_cut; [eapply amemcpy_specZ with (A := FF + 32) (S := BUF) (n := hb) (SPz := SPAz) (RLO1 := RLO1) (RHI1 := RHI1)
                                               (RLO2 := FF) (RHI2 := FF + 64) | post_call bsegs m1 ];
      try (lazymatch goal with |- rng _ _ _ => solve_rng end).
    all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => eassumption
         | |- bytes_at _ _ _ _ => eassumption
         | |- rw_cells _ _ _ _ => first [exact R1 | assumption]
         | |- app_blk _ _ => first [exact APPS | apply ablk_app_blk; [eapply ablk_sub; [exact FH| lia| lia]| lia]]
         | |- unpoisoned _ _ _ => first [exact UD | exact UB1]
         | |- wr_at _ _ _ _ => eassumption
         | |- rng _ _ _ => first [exact RSF2 | eassumption | eapply rng_sub'; [exact RF| lia] | eapply rng_sub'; [exact RSTK| lia]]
         | |- length _ = _ => rewrite length_map; lia
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ => unfold KHIGH, KEND in *; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
    (* [comment removed for export] *)
    rewrite (pad_tailA (Z_to_bv 8 0) hbn) in R2 by lia.
    lazymatch goal with P : rw_cells bsegs ?mx (FF + 32) [CB (Z.to_nat hb) (map (Z_to_bv 8) buf)] |- _ => rename P into RB1; rename mx into m2 end.
    assert (RB8 : rw_cells bsegs m2 (FF + 32) [CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb))))]).
    { replace (FF + 32 + hb) with (FF + 32 + Z.of_nat (cells_size [CB hbn (map (Z_to_bv 8) buf)])) in R2
        by (cbn [cells_size csize Nat.add]; lia).
      pose proof (proj2 (rd_rw_cells_appA bsegs m2 (FF + 32) [CB hbn (map (Z_to_bv 8) buf)]
                          [CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))]) (conj RB1 R2)) as RJ.
      pose proof (rw_cells_merge bsegs m2 (FF + 32) [] [CB hbn (map (Z_to_bv 8) buf); CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] [] RJ) as RMg.
      cbn [app cells_size cells_bytes csize cbytes Nat.add] in RMg. rewrite app_nil_r in RMg.
      replace (hbn + (8 - hbn + 0))%nat with 8%nat in RMg by lia.
      rewrite map_app, map_repeat. replace (Z.to_nat (8 - hb)) with (8 - hbn)%nat by lia. exact RMg. }
    clear RB1 R2.
    assert (FRM : rw_cells bsegs m2 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 8 (firstn 8 junk);
                              CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb)))); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]).
    { change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 8 (firstn 8 junk);
              CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb)))); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]
        with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 8 (firstn 8 junk)]
              ++ [CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb))))] ++ [CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]).
      apply rd_rw_cells_appA. split; [eassumption|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
      apply rd_rw_cells_appA. split; [exact RB8|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8. eassumption. }
    do 6 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_small2 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word) m (FF n hb : Z) (Q : machine_state -> Prop),
    rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH0 -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF mod 64 = 0 -> rng RNG (shad FF) 8 ->
    0 <= n <= hb -> hb < 8 ->
    (forall m' (y10 y12 : word),
        munch [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH ->
        evtF bsegs RNG Q
          (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                   y10 (Z_to_bv 64 n) y12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) x19 x20 x21 x22 (Z_to_bv 64 hb) x23 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0xab14c) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
               (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 x20 x21 x22 (Z_to_bv 64 hb) x23 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xaac24) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros SHF MI FH F64 RSF Hn Hhb K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu. pose proof atop_range as ATR. unfold KEND in SPT.
    replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    unfold RFFSH0 in SHF.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. bcase B; [| exfalso; rewrite ?unsigned_lit in B by lia; destruct (Z.ltb_spec hb n); cbn in B; try lia; rewrite ?Z.land_0_r in B; lia].   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    eapply K; try eassumption.
  Qed.
End S.
End CANSEC1.
