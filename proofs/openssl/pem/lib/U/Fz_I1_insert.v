(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition keep (P : Prop) : Prop := P.

Definition FZ_LH_INSERT : Z := 0xe9c14.
Definition LHI_STACK : Z := 80 + CRE_STACK.
Definition lhi_frame (j0 : list byte) (hs ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell := [CB 8 j0; C8 hs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition lhi_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st1 : PState) (LBall1 LB : list block) (L1 : @clist bptr) (f1 : nat) (m1 : mem) (lo Bd lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z)))
    : nat -> @clist bptr -> PState -> machine_state -> Prop :=
  fun f' L' s' ms' => exists v m' LBall' g' bks',
    cret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v m' ms'
    /\ (f1 - 1 <= f')%nat /\ cgrow L1 L' 1 0 0
    /\ cstate s' LBall' LB L' m' sp tp lo Bd
    /\ cframe (lh_T pl pb bks) [] (bv_unsigned sp) st1 LBall1 L1 m1 s' LBall' L' m'
    /\ (forall q, In q (map blk_id LBall1) \/ In q (map fst L1) -> ~ lh_T pl pb bks q -> ~ lh_T pl pb bks' q)
    /\ lh_rep DVERR m' LBall' L' ERR_FNS lh pl pb B nmb g' bks'
    /\ g_nn g' = g_nn g /\ g_na g' = g_na g /\ g_p g' = g_p g /\ g_pmax g' = g_pmax g /\ g_items g <= g_items g' <= g_items g + 1.

Lemma lhi_tail : crypto_malloc_stmt ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (st1 : PState) (LBall1 LB : list block) (L1 : @clist bptr) (f1 : nat)
         (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data lo Bd : Z) (j0 : list byte) (hs : word),
  (1 <= f1)%nat -> croom L1 1 0 0 ->
  cstate st1 LBall1 LB L1 m1 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd -> bv_unsigned sp <= Bd ->
  lh_rep DVERR m1 LBall1 L1 ERR_FNS lh pl pb B nmb g bks -> g_items g < LH_KMAX -> DVERR data ->
  rw_cells usegs m1 (bv_unsigned sp + -80) (lhi_frame j0 hs ra s0 s1 s2 s3 s4 s5 s6) ->
  lo <= bv_unsigned sp - LHI_STACK -> bv_unsigned sp mod 16 = 0 ->
  climpl f1 L1 st1
    (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y1 y2 y3 sp (Z_to_bv 64 lh) y4 y5 y6 y7 y8 y9 y10 y11
             (Z_to_bv 64 data) y12 y13 y14 y15 s7 s8 s9 s10 s11 y16 y17 y18 y19)
        F (Z_to_bv 64 0xe9c70) fc None m1 (seg_rom usegs))
    (lhi_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st1 LBall1 LB L1 f1 m1 lo Bd lh pl pb B nmb g bks).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 F fc m1 st1 LBall1 LB L1 f1
         lh pl pb B nmb g bks data lo Bd j0 hs Hf ROOM CST SPB REP ITEMS DVD FR SLO SA.
  pose proof CST as (HP & _ & (errv & _ & _ & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  rewrite unsigned_lit in ST by lia.
  (* [comment removed for export] *)
  unfold lhi_frame in FR.
  change [CB 8 j0; C8 hs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] with ([CB 8 j0] ++ [C8 hs] ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
  apply (proj1 (rw_cells_app usegs m1 _ _ _)) in FR. destruct FR as [FR0 FR]. apply (proj1 (rw_cells_app usegs m1 _ _ _)) in FR. destruct FR as [FRH FRS].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRH, FRS.
  replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in * by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in * by lia.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp - 64)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP) as (S_LB & S_N & S_X & S_F).
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SCm) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB.
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SCm.
  (* [comment removed for export] *)
  assert (EPI : forall (v z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 hv : word) (mc : mem) (jj : list byte),
    rw_cells usegs mc (bv_unsigned sp + -80) [CB 8 jj] -> rw_cells usegs mc (bv_unsigned sp + -72) [C8 hv] ->
    rw_cells usegs mc (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -80) -> mem_inv usegs mc ->
    evt usegs (fun ms' => cret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v mc ms' /\ stk usegs mc lo (bv_unsigned sp))
      (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp z1 z2 z3 z4 z5 v z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 s7 s8 s9 s10 s11 z18 z19 z20 z21)
          F (Z_to_bv 64 0xe9e20) fc None mc (seg_rom usegs))).
  { intros v z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 hv mc jj F0 FH FS STc MIc.
    assert (FJ : rw_cells usegs mc (bv_unsigned sp + -80) ([CB 8 jj] ++ [C8 hv] ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact F0|]. apply rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by lia. auto. }
    cbn [app] in FJ. clear F0 FH FS.
    do 9 step. release_frame FJ STc (bv_unsigned sp). step.
    apply evt_done. split; [unfold cret; do 14 eexists; reflexivity| exact STc]. }
  assert (DRD : 0x2c0638 <= data /\ data + 16 <= 0x32e038) by (pose proof (proj2 DVD data ltac:(lia)) as X; pose proof (proj2 DVD (data + 15) ltac:(lia)) as Y; unfold cimg_addr, RMallocRep.RGOT_SSP in X, Y; lia).
  assert (KEX : exists kw : word, rw_cells usegs m1 data [C8 kw]) by (destruct (DVERR_cell m1 data 0 CIMG DVD ltac:(lia)) as [kw KC]; rewrite Z.add_0_r in KC; exists kw; exact KC).
  pose proof (proj1 DVD) as DAL. cprefix. do 4 step.
  calle (eapply getrn_spec with (lh := lh) (data := data) (hp := bv_unsigned sp + -72) (lo := lo)); try (unfold GETRN_STACK, GLOBALS_TOP; lia).
  lazymatch goal with H : nth (Z.to_nat ?ii) bks [] = ?n1 ++ ?n2 |- _ => rename H into ENTH; rename ii into i; rename n1 into ns1; rename n2 into ns2 end.
  lazymatch goal with H : lseg _ ?mm _ _ _ ns1 ?r |- _ => rename H into S1; rename r into rn; rename mm into m2 end.
  lazymatch goal with H : chain _ m2 _ _ rn ns2 |- _ => rename H into C2 end.
  lazymatch goal with H : 0 <= i < g_nn g |- _ => rename H into IR end.
  lazymatch goal with H : rw_cells _ m2 (bv_unsigned sp + -72) [C8 ?hh] |- _ => rename H into HPC; set (h := hh) in * end.
  lazymatch goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
  lazymatch goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG12. assert (MU12 : keep (munch [(bv_unsigned sp - 176, bv_unsigned sp - 64)]%Z m1 m2)) by exact MU.
  assert (WM12 : keep (wmono usegs m1 m2)) by exact WM.
  assert (LI : (Z.to_nat i < length bks)%nat) by lia.
  assert (FOI : ForallOrdPairs apart24 (map snd ns1 ++ map snd ns2)) by (rewrite <- map_app, <- ENTH; exact (S_F _ LI)).
  destruct (fop_app_inv _ _ _ FOI) as (FO1 & FO2 & X12).
  assert (NI : forall p A, In (p, A) (ns1 ++ ns2) -> (A + 24 <= lh \/ lh + 104 <= A) /\ (A + 24 <= B \/ B + 8 * g_na g <= A) /\ 0 < A /\ A + 24 <= alloc_ceiling).
  { intros p A Hin. rewrite <- ENTH in Hin. destruct (S_N _ p A LI Hin) as [X1 X2]. split; [exact X1|]. split; [exact X2|].
    pose proof (CH i ltac:(lia)) as (c0 & SS & _). exact (lseg_ranges _ _ _ _ _ _ _ SS p A Hin). }
  (* [comment removed for export] *)
  assert (RNLOC : (ns1 = [] /\ rn = B + 8 * i) \/ exists pre pr Ar, ns1 = pre ++ [(pr, Ar)] /\ rn = Ar + 8) by exact (lseg_end_loc _ _ _ _ _ _ _ S1).
  assert (RNAL : rn mod 8 = 0).
  { destruct RNLOC as [[_ ->]|(pre & pr & Ar & E1 & ->)].
    - pose proof (cown_al8 _ _ _ _ _ _ _ _ HP OB) as (BAL & _). clear - BAL. Z.div_mod_to_equations. lia.
    - assert (INR : In (pr, Ar) ns1) by (rewrite E1; apply in_or_app; right; left; reflexivity).
      pose proof (cown_al8 _ _ _ _ _ _ _ _ HP (lseg_owns _ _ _ _ _ _ _ S1 pr Ar INR)) as (AAL & _). clear - AAL. Z.div_mod_to_equations. lia. }
  destruct ns2 as [|[pk Ak] rest].
  2:{ (* [comment removed for export] *)
    pose proof C2 as (c' & (CRN & OWNk & RGk & (dk & hk & K1 & DVk & K2) & RSEG) & TERM). unfold wz in CRN, K1, TERM.
    destruct (NI pk Ak ltac:(apply in_or_app; right; left; reflexivity)) as (NK1 & NK2 & _).
    assert (RNK : rn + 8 <= Ak \/ Ak + 24 <= rn).
    { destruct RNLOC as [[_ ->]|(pre & pr & Ar & E1 & ->)]; [pose proof GB; lia|].
      assert (X : apart24 Ar Ak) by (apply X12; [rewrite E1, map_app; apply in_or_app; right; left; reflexivity| left; reflexivity]). unfold apart24 in X. lia. }
    assert (TERMK : keep (rw_cells usegs m2 c' [C8 (Z_to_bv 64 0)])) by exact TERM.
    clear MU. pose proof (munch_refl [(Ak, Ak + 8)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    pose proof (rw_cells_bound _ _ _ _ CRN) as RNB0. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in RNB0. step. step. step. ubs_if. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    pose proof (cown_al8 _ _ _ _ _ _ _ _ HP OWNk) as (AKAL & _). step. step. ubs_if.
    do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    chere.
    eapply climpl_evt; [eapply (EPI (Z_to_bv 64 dk)); eassumption|].
    intros ms' (RET & STF). apply climpl_done.
    exists (Z_to_bv 64 dk), m3, LBall1, g, bks.
    pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG23.
    unfold keep in MU12, WM12.
    assert (MU13 : munch [(bv_unsigned sp - 176, bv_unsigned sp - 64); (Ak, Ak + 8)]%Z m1 m3).
    { eapply munch_trans; (eapply munch_weaken; [| eassumption]); intros xx Hxx; cbn [outside] in Hxx |- *; clear - Hxx; tauto. }
    assert (WM13 : wmono usegs m1 m3) by (eapply wmono_trans; eassumption).
    assert (INK : In (pk, Ak, 24) LBall1) by exact (proj1 OWNk).
    assert (TK : lh_T pl pb bks pk).
    { right; right. apply in_map_iff. exists (pk, Ak). split; [reflexivity|]. eapply in_nth_concat. rewrite ENTH. apply in_or_app. right. left. reflexivity. }
    split; [exact RET|]. split; [lia|]. split; [unfold cgrow; lia|].
    split. { eapply (cstate_seg _ _ _ _ _ m1 m3 _ sp tp lo Bd (bv_unsigned sp)); [exact CST| exact MU13| exact WM13| eassumption| | lia| lia| | exact STF| exact SPB].
      - constructor; [apply cwin_stack; lia| constructor; [| constructor]]. apply (cwin_block _ _ _ (pk, Ak, 24)); [exact INK| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      - cbn [disjoint_from]. unfold LX_FLAGS. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INK) as (_ & _ & _ & _ & X). lia. }
    split. { eapply cframe_seg; [apply cframe_refl| exact MU13| exact WM13| exact HP| lia|].
      constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
      apply (cseg_ok_block _ _ _ _ _ (pk, Ak, 24)); [exact INK| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. exact TK. }
    split; [intros q _ X; exact X|].
    split; [| repeat split; lia].
    (* [comment removed for export] *)
    assert (OUT13 : forall a, 0 <= a < alloc_ceiling -> ~ (Ak <= a < Ak + 8) -> outside [(bv_unsigned sp - 176, bv_unsigned sp - 64); (Ak, Ak + 8)]%Z a)
      by (intros a Ha NA; cbn [outside]; lia).
    pose proof (agree_on_of_munch _ _ _ MU13 WM13) as AG13.
    eapply (lh_rep_upd DVERR m1 m3 LBall1 L1 LBall1 L1 ERR_FNS lh pl pb B nmb g g bks bks (fun j => j = i)); try eassumption; try reflexivity.
    - intros j. lia.
    - exists x40, x48, err, pad. unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz.
      exact SCm.
    - intros q A0 n0 nm0 _ X. exact X.
    - intros j Hj ->. rewrite ENTH.
      (* [comment removed for export] *)
      assert (AGN : forall X, In X (map snd ns1 ++ map snd rest) -> forall a, X <= a < X + 24 -> outside [(Ak, Ak + 8)]%Z a).
      { intros X HX a Ha. cbn [outside]. split; [| exact I]. apply in_app_or in HX. destruct HX as [HX|HX].
        - pose proof (X12 X Ak HX ltac:(left; reflexivity)) as Y. unfold apart24 in Y. lia.
        - cbn [map snd] in FO2. inversion FO2 as [|xx ll FA _]; subst xx ll. pose proof (proj1 (Forall_forall _ _) FA X HX) as Y. unfold apart24 in Y. lia. }
      exists c'. split.
      + eapply lseg_app.
        * eapply lseg_agree; [exact S1| | intros ? ? _ X; exact X]. eapply agree_on_mono; [exact AG23|]. intros a Ha.
          destruct (lseg_fp_where _ _ _ Ha) as [Y|(p0 & X & HX & Y)]; [cbn [outside]; pose proof GB; lia|].
          apply (AGN X); [apply in_or_app; left; apply (in_map snd) in HX; exact HX| exact Y].
        * cbn [lseg]. split; [exact CRN|]. split; [exact OWNk|]. split; [exact RGk|]. split; [exists data, hk; unfold wz; auto|].
          eapply lseg_agree; [exact RSEG| | intros ? ? _ X; exact X]. eapply agree_on_mono; [exact AG23|]. intros a Ha.
          destruct (lseg_fp_where _ _ _ Ha) as [Y|(p0 & X & HX & Y)]; [cbn [outside]; lia|].
          apply (AGN X); [apply in_or_app; right; apply (in_map snd) in HX; exact HX| exact Y].
      + unfold keep in TERMK. eapply rw_cells_agree; [exact AG23| exact TERMK|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha.
        destruct (lseg_end_loc _ _ _ _ _ _ _ RSEG) as [[_ ->]|(pre & pr & Ar & E1 & ->)]; [cbn [outside]; lia|].
        apply (AGN Ar); [apply in_or_app; right; rewrite E1, map_app; apply in_or_app; right; left; reflexivity| lia].
    - intros j Hj NJ. split; [reflexivity|]. eapply agree_on_mono; [exact AG13|]. intros a [Ha|(p0 & X & HX & Ha)].
      + apply OUT13; [pose proof GB; lia|]. lia.
      + assert (LJ : (Z.to_nat j < length bks)%nat) by lia.
        pose proof (CH j Hj) as (c0 & SS & _). pose proof (lseg_ranges _ _ _ _ _ _ _ SS p0 X HX) as XR.
        assert (XA : apart24 X Ak).
        { apply (S_X (Z.to_nat j) (Z.to_nat i) (p0, X) (pk, Ak) LJ LI); [lia| exact HX| rewrite ENTH; apply in_or_app; right; left; reflexivity]. }
        unfold apart24 in XA. apply OUT13; lia. }

  (* [comment removed for export] *)
  rewrite app_nil_r in ENTH, FOI. clear FO2 X12.
  pose proof C2 as (c' & E & TERM). cbn [lseg] in E. subst c'. unfold wz in TERM.
  assert (TERMK : keep (rw_cells usegs m2 rn [C8 (Z_to_bv 64 0)])) by exact TERM.
  (* [comment removed for export] *)
  assert (RNB : exists pr Ar nr, In (pr, Ar, nr) LBall1 /\ lh_T pl pb bks pr /\ Ar <= rn /\ rn + 8 <= Ar + nr /\ (Ar + nr <= lh \/ lh + 104 <= Ar) /\ 0 < Ar /\ Ar + nr <= alloc_ceiling).
  { destruct RNLOC as [[_ ->]|(pre & pr & Ar & E1 & ->)].
    - exists pb, B, (8 * g_na g). split; [exact (proj1 OB)|]. split; [right; left; reflexivity|]. pose proof GB. lia.
    - assert (INR : In (pr, Ar) ns1) by (rewrite E1; apply in_or_app; right; left; reflexivity).
      destruct (NI pr Ar ltac:(rewrite app_nil_r; exact INR)) as (N1 & N2 & N3 & N4).
      exists pr, Ar, 24. split; [rewrite <- ENTH in INR; exact (proj1 (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP pr Ar (in_nth_concat _ _ _ INR)))|].
      split; [right; right; apply in_map_iff; exists (pr, Ar); split; [reflexivity| rewrite <- ENTH in INR; exact (in_nth_concat _ _ _ INR)]|]. lia. }
  destruct RNB as (pr & Ar & nr & INR & TR & RN1 & RN2 & RNS & RN3 & RN4).
  step. step. step. ubs_if. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  do 5 step. chere.
  unfold keep in MU12, WM12.
  assert (CST2 : cstate st1 LBall1 LB L1 m2 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m1 m2 _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU12| exact WM12| exact MI2| | lia| lia| | |].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST2.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRA : cframe (lh_T pl pb bks) [] (bv_unsigned sp) st1 LBall1 L1 m1 st1 LBall1 L1 m2).
  { eapply cframe_seg; [apply cframe_refl| exact MU12| exact WM12| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply CM with (n := 24); [exact Hf| | lia| exact CST2| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| reflexivity].
    destruct (wA_small 24 ltac:(unfold TIER_A_MAX; lia)) as (W1 & W2 & W3). rewrite W1, W2, W3. exact ROOM. }
  intros f3 L3 st3 ms3 (v & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (pn & An & jk & -> & -> & -> & RNG & NEW)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM3 as (CFR3 & KP3 & _). change (Z.to_nat 24) with 24%nat in NEW.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _].
  assert (PNEW : forall q A0 n0, In (q, A0, n0) LBall1 -> pn <> q).
  { intros q A0 n0 Hin E. cbn [map blk_id fst] in ND3. inversion ND3 as [|xx ll NIx _]; subst xx ll. apply NIx. subst q. apply in_map_iff. exists (pn, A0, n0). auto. }
  pose proof RNG as (An0 & An16 & _ & AnC & AnIMG).
  assert (AP_R : An + 24 <= Ar \/ Ar + nr <= An)
    by (eapply (own_apart _ _ _ pn An 24 pr Ar nr HP3); [left; reflexivity| right; exact INR| exact (PNEW _ _ _ INR)]).
  assert (AP_L : An + 24 <= lh \/ lh + 104 <= An)
    by (eapply (own_apart _ _ _ pn An 24 pl lh 104 HP3); [left; reflexivity| right; exact (proj1 OL)| exact (PNEW _ _ _ (proj1 OL))]).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR0 ltac:(lia)) as FR03.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 HPC ltac:(lia)) as HPC3.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FRS ltac:(lia)) as FRS3.
  unfold keep in TERMK.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pr, Ar, nr) CFR3 TERMK INR (fun X => X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as TERM3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pl, lh, 104) CFR3 SCm (proj1 OL) (fun X => X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as SC3.
  clear FR0 HPC FRS SCm TERM.
  pose proof (munch_refl [(An, An + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  (* [comment removed for export] *)
  cprefix. step. if_cases K9; zify_cond K9. { exfalso. rewrite ?unsigned_lit in K9 by lia. lia. }
  do 2 step. step. ubs_if. do 3 step. cstep. do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
  chere.
  eapply climpl_evt; [eapply (EPI (Z_to_bv 64 0)); eassumption|].
  intros ms' (RET & STF). apply climpl_done.
  set (g' := mkGeo (g_nn g) (g_na g) (g_p g) (g_pmax g) (g_items g + 1)).
  set (bks' := lupd (Z.to_nat i) (ns1 ++ [(pn, An)]) bks).
  exists (Z_to_bv 64 0), m4, ((pn, An, 24) :: LBall1), g', bks'.
  pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG34.
  assert (INN : In (pn, An, 24) ((pn, An, 24) :: LBall1)) by (left; reflexivity).
  assert (INR' : In (pr, Ar, nr) ((pn, An, 24) :: LBall1)) by (right; exact INR).
  assert (INL' : In (pl, lh, 104) ((pn, An, 24) :: LBall1)) by (right; exact (proj1 OL)).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INR) as (_ & _ & _ & _ & ARIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OL)) as (_ & _ & _ & _ & LHIMG).
  split; [exact RET|]. split; [exact FU3|].
  split. { destruct (wA_small 24 ltac:(unfold TIER_A_MAX; lia)) as (W1 & W2 & W3). rewrite W1, W2, W3 in GR3. exact GR3. }
  split. { eapply (cstate_seg _ _ _ _ _ m3 m4 _ sp tp lo Bd (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| eassumption| | lia| lia| | exact STF| exact SPB].
    - constructor; [| constructor; [| constructor; [| constructor]]].
      + apply (cwin_block _ _ _ (pn, An, 24)); [exact INN| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (pr, Ar, nr)); [exact INR'| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL'| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRA| exact FRM3| lia| intros a X; exact X| intros q0 _ _ X; exact X]| exact MU3| exact WM3| exact HP3| lia|].
    constructor; [| constructor; [| constructor; [| constructor]]].
    - apply (cseg_ok_block _ _ _ _ _ (pn, An, 24)); [exact INN| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      destruct FRA as (_ & KPA & _). exact (cfresh_new _ _ _ _ _ _ KPA ND3).
    - apply (cseg_ok_block _ _ _ _ _ (pr, Ar, nr)); [exact INR'| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. exact TR.
    - apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL'| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. left. reflexivity. }
  split. { (* [comment removed for export] *)
    intros q QIN NT [E|[E|E]]; [apply NT; left; exact E| apply NT; right; left; exact E|].
    assert (PM : Permutation (concat bks') ((pn, An) :: concat bks)).
    { unfold bks'. eapply Permutation_trans; [apply concat_lupd; exact LI|].
      eapply Permutation_trans; [| apply perm_skip; apply Permutation_sym; apply (concat_split_perm bks (Z.to_nat i) LI)]. rewrite ENTH.
      rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_cons_app. apply Permutation_refl. }
    apply (Permutation_in _ (Permutation_map fst PM)) in E. cbn [map fst] in E. destruct E as [E|E]; [| apply NT; right; right; exact E].
    assert (QB : In q (map blk_id LBall1)) by (destruct QIN as [X|X]; [exact X| destruct CST as (_ & CO & _); exact (cl_own_ids _ _ _ _ CO X)]).
    apply in_map_iff in QB. destruct QB as ([[q0 A0] n0] & E0 & QB). unfold blk_id in E0. cbn [fst] in E0. subst q0. exact (PNEW _ _ _ QB E). }
  split; [| cbn [g' g_nn g_na g_p g_pmax g_items]; repeat split; lia].
  (* [comment removed for export] *)
  assert (OWNS : forall q A0 n0 nm0, cown LBall1 L1 q A0 n0 nm0 -> cown ((pn, An, 24) :: LBall1) ((pn, 24) :: L1) q A0 n0 nm0) by (intros; apply cown_cons; assumption).
  assert (AG23 : agree_on (lh_fp lh B g bks) m2 m3).
  { eapply (cfr_agree_lh _ _ _ _ _ _ _ _ _ _ pl pb CFR3 (proj1 OL) (proj1 OB)); [| intros q _ X; exact X].
    intros p0 A0 Hin. exact (proj1 (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP p0 A0 Hin)). }
  (* [comment removed for export] *)
  assert (NODE_OUT : forall p0 X, In (p0, X) (concat bks) -> forall a, X <= a < X + 24 -> ~ (rn <= a < rn + 8) ->
            outside [(An, An + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z a).
  { intros p0 X Hin a Ha NR. pose proof (proj1 (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP p0 X Hin)) as INX.
    assert (AX : An + 24 <= X \/ X + 24 <= An) by (eapply (own_apart _ _ _ pn An 24 p0 X 24 HP3); [left; reflexivity| right; exact INX| exact (PNEW _ _ _ INX)]).
    apply in_concat in Hin. destruct Hin as (nsx & Hns & Hin). destruct (In_nth _ _ [] Hns) as (jx & Hjx & Ejx). subst nsx.
    destruct (S_N jx p0 X Hjx Hin) as [XL _]. cbn [outside]. clear - Ha NR AX XL. lia. }
  assert (CELL_OUT : forall j, 0 <= j < g_na g -> j <> i -> forall a, B + 8 * j <= a < B + 8 * j + 8 -> outside [(An, An + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z a).
  { intros j Hj NJ a Ha.
    assert (AB : An + 24 <= B \/ B + 8 * g_na g <= An) by (eapply (own_apart _ _ _ pn An 24 pb B (8 * g_na g) HP3); [left; reflexivity| right; exact (proj1 OB)| exact (PNEW _ _ _ (proj1 OB))]).
    cbn [outside]. destruct RNLOC as [[_ ->]|(pre & pr0 & Ar0 & E1 & ->)]; [clear - Ha NJ Hj AB S_LB IR GB; lia|].
    destruct (NI pr0 Ar0 ltac:(rewrite app_nil_r, E1; apply in_or_app; right; left; reflexivity)) as (_ & N2 & _). clear - Ha Hj AB S_LB N2. lia. }
  eapply (lh_rep_upd DVERR m1 m4 LBall1 L1 _ _ ERR_FNS lh pl pb B nmb g g' bks bks' (fun j => j = i)); try eassumption.
  - intros j. lia.
  - reflexivity.
  - destruct G as (G1 & G2 & G3 & G4 & G5 & G6). unfold lh_geo_ok, g', LH_KMAX. unfold LH_KMAX in ITEMS, G6. cbn [g_nn g_na g_p g_pmax g_items]. clear - G1 G2 G3 G4 G5 G6 ITEMS. lia.
  - exists x40, x48, err, pad. unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz, g'. cbn [g_nn g_na g_p g_pmax g_items]. exact SC3.
  - intros q A0 n0 nm0 _ X. exact (OWNS _ _ _ _ X).
  - unfold bks'. rewrite lupd_length. exact LEN.
  - intros j Hj ->. unfold bks'. rewrite nth_lupd_eq by exact LI.
    change [C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 0); C8 h] with ([C8 (Z_to_bv 64 data)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 h]) in NEW.
    apply (proj1 (rw_cells_app usegs m4 _ _ _)) in NEW. destruct NEW as [ND0 NEW]. apply (proj1 (rw_cells_app usegs m4 _ _ _)) in NEW. destruct NEW as [ND8 ND16].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ND8, ND16. replace (An + 8 + 8) with (An + 16) in ND16 by lia.
    exists (An + 8). split; [| exact ND8].
    eapply lseg_app.
    + (* [comment removed for export] *)
      eapply lseg_agree; [eapply lseg_agree; [exact S1| | intros p0 A0 _ X; exact X]| | intros p0 A0 _ X; exact (OWNS _ _ _ _ X)].
      * eapply agree_on_mono; [exact AG23|]. intros a Ha. destruct (lseg_fp_where _ _ _ Ha) as [Y|(p0 & X & HX & Y)].
        -- right; left. pose proof GB. lia.
        -- right; right. exists p0, X. split; [| exact Y]. eapply in_nth_concat. rewrite ENTH. exact HX.
      * eapply agree_on_mono; [exact AG34|]. intros a Ha.
        assert (NRN : ~ (rn <= a < rn + 8)).
        { eapply (lseg_fp_end _ _ _ _ _ _ S1 FOI); [| exact Ha]. apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([p0 X0] & EX & HX). cbn [snd] in EX. subst X0.
          destruct (NI p0 X ltac:(rewrite app_nil_r; exact HX)) as (_ & N2 & _). unfold apartc. clear - N2 GB IR. lia. }
        destruct (lseg_fp_where _ _ _ Ha) as [Y|(p0 & X & HX & Y)].
        -- assert (AB : An + 24 <= B \/ B + 8 * g_na g <= An) by (eapply (own_apart _ _ _ pn An 24 pb B (8 * g_na g) HP3); [left; reflexivity| right; exact (proj1 OB)| exact (PNEW _ _ _ (proj1 OB))]).
           cbn [outside]. clear - Y AB NRN S_LB IR GB. lia.
        -- apply (NODE_OUT p0 X); [eapply in_nth_concat; rewrite ENTH; exact HX| exact Y| exact NRN].
    + cbn [lseg]. split; [exact TERM3|]. split; [apply cown_new|]. split; [lia|]. split; [exists data, h; unfold wz; auto| reflexivity].
  - intros j Hj NJ. unfold bks'. rewrite nth_lupd_ne by (clear - NJ Hj IR; lia). split; [reflexivity|].
    eapply agree_on_trans; [| eapply agree_on_trans]; [eapply agree_on_mono; [exact AG12|]| eapply agree_on_mono; [exact AG23|]| eapply agree_on_mono; [exact AG34|]].
    + intros a [Ha|(p0 & X & HX & Ha)]; cbn [outside].
      * pose proof GB. lia.
      * pose proof (CH j Hj) as (c0 & SS & _). pose proof (lseg_ranges _ _ _ _ _ _ _ SS p0 X HX). lia.
    + intros a [Ha|(p0 & X & HX & Ha)]; [right; left; lia| right; right; exists p0, X; split; [eapply in_nth_concat; exact HX| exact Ha]].
    + intros a [Ha|(p0 & X & HX & Ha)]; [exact (CELL_OUT j Hj NJ a Ha)|].
      apply (NODE_OUT p0 X); [eapply in_nth_concat; exact HX| exact Ha|].
      assert (LJ : (Z.to_nat j < length bks)%nat) by lia.
      destruct (S_N _ p0 X LJ HX) as [_ XB].
      destruct RNLOC as [[_ ->]|(pre & pr0 & Ar0 & E1 & ->)]; [clear - XB Ha IR GB; lia|].
      assert (XA : apart24 X Ar0).
      { apply (S_X (Z.to_nat j) (Z.to_nat i) (p0, X) (pr0, Ar0) LJ LI); [clear - NJ Hj IR; lia| exact HX| rewrite ENTH, E1; apply in_or_app; right; left; reflexivity]. }
      unfold apart24 in XA. clear - XA Ha. lia.
  - intros j Hj. unfold g' in Hj. cbn [g_nn] in Hj. unfold bks'. rewrite nth_lupd_ne by lia. apply EMP. exact Hj.
  - (* [comment removed for export] *)
    assert (PM : Permutation (concat bks') ((pn, An) :: concat bks)).
    { unfold bks'. eapply Permutation_trans; [apply concat_lupd; exact LI|].
      eapply Permutation_trans; [| apply perm_skip; apply Permutation_sym; apply (concat_split_perm bks (Z.to_nat i) LI)]. rewrite ENTH.
      rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_cons_app. apply Permutation_refl. }
    eapply Permutation.Permutation_NoDup.
    { apply Permutation_sym. apply perm_skip. apply perm_skip. apply Permutation_map. exact PM. }
    cbn [map fst]. eapply Permutation.Permutation_NoDup; [| constructor; [| exact ND]].
    + eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
    + intros [E|[E|E]].
      * exact (PNEW _ _ _ (proj1 OL) (eq_sym E)).
      * exact (PNEW _ _ _ (proj1 OB) (eq_sym E)).
      * apply in_map_iff in E. destruct E as ([p0 X] & E1 & Hin). cbn [fst] in E1. subst p0.
        exact (PNEW _ _ _ (proj1 (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP pn X Hin)) eq_refl).
Qed.
End WithCeiling0.
