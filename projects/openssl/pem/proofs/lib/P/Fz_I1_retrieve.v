(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OSSVerify.Proofs.openssl.pem.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Layout Fz_iface Driver_iface Drv_kit InitMem Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand Str_cpy Fz_M_malloc Fz_kit_ra Fz_I1_insert1.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.pem.lib.P Require Printf_lib.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_LH_RETRIEVE : Z := 0xe434c.
Definition LHR_STACK : Z := 32 + GETRN_STACK.

Definition lh_retrieve_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' v,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ lh_rep DVERR m' LBall L ERR_FNS lh pl pb B nmb g bks
    /\ (v = 0 \/ DVERR v).

Theorem lh_retrieve_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (s : PState) (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data lo : Z) (m0 : mem),
  RHEAP s LBall m0 -> lh_rep DVERR m0 LBall L ERR_FNS lh pl pb B nmb g bks ->      (* [comment removed for export] *)
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks ->
  (exists kw : word, rw_cells psegs m data [C8 kw]) -> ((0x27a000 <= data /\ data + 8 <= 0x30d000) \/ bv_unsigned sp <= data) -> cimg m ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 data ->
  stk psegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - LHR_STACK -> mem_inv psegs m ->
  evt psegs (lh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L lh pl pb B nmb g bks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_LH_RETRIEVE) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall L lh pl pb B nmb g bks data lo m0
         HP REP0 REP KEY0 KLOC CI -> -> ST GLO CLO SLO MI.
  unfold LHR_STACK, GETRN_STACK, GLOBALS_TOP, FZ_LH_RETRIEVE in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP0) as (S_LB & S_N & S_X & S_F).
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SCm) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB.
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SCm.
  destruct KEY0 as [kw KC].
  assert (LHIMG : lh + 104 <= 0x10000 \/ 0x30d000 <= lh).
  { pose proof (RHEAP_block_range_proof _ _ _ (pl, lh, 104) HP (proj1 OL)) as (_ & _ & _ & _ & X). unfold blk_addr, blk_size in X. cbn [fst snd] in X. exact X. }
  pose proof (rw_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in KB.
  (* [comment removed for export] *)
  assert (REPAT : forall mc (err' : word), munch [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc -> wmono psegs m mc ->
    rw_cells psegs mc lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 932816); C8 (Z_to_bv 64 932716); C8 (Z_to_bv 64 932868); C8 (Z_to_bv 64 932900); C8 x40; C8 x48;
                          C4 (Z_to_bv 64 (g_nn g)); C4 (Z_to_bv 64 (g_na g)); C4 (Z_to_bv 64 (g_p g)); C4 (Z_to_bv 64 (g_pmax g)); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256);
                          C8 (Z_to_bv 64 (g_items g)); C4 err'; C4 pad] ->
    lh_rep DVERR mc LBall L ERR_FNS lh pl pb B nmb g bks).
  { intros mc err' MUc WMc SCc. pose proof (agree_on_of_munch _ _ _ MUc WMc) as AGc.
    eapply (lh_rep_upd DVERR m mc LBall L LBall L ERR_FNS lh pl pb B nmb g g bks bks (fun _ => False) REP); try reflexivity; try assumption.
    - intros i. right. intros X. exact X.
    - exists x40, x48, err', pad. unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz. exact SCc.
    - intros q A n nm _ X. exact X.
    - intros i Hi [].
    - intros i Hi _. split; [reflexivity|]. eapply agree_on_mono; [exact AGc|]. intros a [Ha|(q & A & Hq & Ha)]; cbn [outside]; [lia|].
      assert (LI : (Z.to_nat i < length bks)%nat) by lia. destruct (S_N _ q A LI Hq) as [X1 _]. pose proof (CH i Hi) as (c0 & SS & _).
      pose proof (lseg_ranges _ _ _ _ _ _ _ SS q A Hq). lia. }
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  (* [comment removed for export] *)
  assert (TAIL : forall (err' y : word) (mc : mem),
    rw_cells psegs mc lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 932816); C8 (Z_to_bv 64 932716); C8 (Z_to_bv 64 932868); C8 (Z_to_bv 64 932900); C8 x40; C8 x48;
                          C4 (Z_to_bv 64 (g_nn g)); C4 (Z_to_bv 64 (g_na g)); C4 (Z_to_bv 64 (g_p g)); C4 (Z_to_bv 64 (g_pmax g)); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256);
                          C8 (Z_to_bv 64 (g_items g)); C4 err'; C4 pad] ->
    rw_cells psegs mc data [C8 kw] -> stk psegs mc lo (bv_unsigned sp) ->
    munch [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc -> wmono psegs m mc -> mem_inv psegs mc ->
    evt psegs (lh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L lh pl pb B nmb g bks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lh) (Z_to_bv 64 data) y a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe4358) fc None mc (seg_rom psegs))).
  { intros err' y mc SCc KCc STc MUc WMc MIc.
    (* [comment removed for export] *)
    assert (EPI : forall (v : Z) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 hv : word) (mc2 : mem) (jj : list byte),
      (v = 0 \/ DVERR v) ->
      rw_cells psegs mc2 (bv_unsigned sp + -32) [CB 8 jj] -> rw_cells psegs mc2 (bv_unsigned sp + -24) [C8 hv] -> rw_cells psegs mc2 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      rw_cells psegs mc2 lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 932816); C8 (Z_to_bv 64 932716); C8 (Z_to_bv 64 932868); C8 (Z_to_bv 64 932900); C8 x40; C8 x48;
                             C4 (Z_to_bv 64 (g_nn g)); C4 (Z_to_bv 64 (g_na g)); C4 (Z_to_bv 64 (g_p g)); C4 (Z_to_bv 64 (g_pmax g)); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256);
                             C8 (Z_to_bv 64 (g_items g)); C4 err'; C4 pad] ->
      stk psegs mc2 lo (bv_unsigned sp + -32) -> munch [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc2 -> wmono psegs m mc2 -> mem_inv psegs mc2 ->
      evt psegs (lh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L lh pl pb B nmb g bks)
        (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp z1 z2 z3 z4 s1 (Z_to_bv 64 v) z5 z6 z7 z8 z9 z10 z11 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z12 z13 z14 z15)
            F (Z_to_bv 64 0xe437c) fc None mc2 (seg_rom psegs))).
    { intros v z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 hv mc2 jj VOK F0 FH FS SC2 ST2 MU2 WM2 MI2.
      assert (FJ : rw_cells psegs mc2 (bv_unsigned sp + -32) ([CB 8 jj] ++ [C8 hv] ++ [C8 s0; C8 ra])).
      { apply rw_cells_app. split; [exact F0|]. apply rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia. replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) by lia. auto. }
      cbn [app] in FJ. clear F0 FH FS.
      do 2 step. release_frame FJ ST2 (bv_unsigned sp). step. step.
      apply evt_done. unfold lh_retrieve_post. do 14 eexists. exists mc2, v. split; [reflexivity|].
      split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact (REPAT mc2 err' MU2 WM2 SC2)| exact VOK]. }
    step. carve_frame 32%nat STc. do 5 step.
    apply (rw_cells_split_CB psegs _ _ [] 16 _ _ [8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (cb8_c8_in' _ _ [CB 8 _] _ _) in FR. cbn [app] in FR.
    lazymatch type of FR with rw_cells _ _ _ [CB 8 ?j; C8 ?hs; C8 s0; C8 ra] =>
      change [CB 8 j; C8 hs; C8 s0; C8 ra] with ([CB 8 j] ++ [C8 hs] ++ [C8 s0; C8 ra]) in FR end.
    apply (proj1 (rw_cells_app psegs _ _ _ _)) in FR. destruct FR as [FR0 FR]. apply (proj1 (rw_cells_app psegs _ _ _ _)) in FR. destruct FR as [FRH FRS].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRH, FRS.
    replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in * by lia. replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CIc : cimg mm) by (eapply cimg_seg; [exact CI| eassumption|]; intros a Ha; unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; cbn [outside]; unfold ceil_window in *; lia);
      pose proof (REPAT mm err' ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as REPc;
      assert (KEXc : exists kw0 : word, rw_cells psegs mm data [C8 kw0]) by (exists kw; eassumption) end.
    calle (eapply getrn_spec with (lh := lh) (data := data) (hp := bv_unsigned sp + -24) (lo := lo)); try (unfold GETRN_STACK, GLOBALS_TOP; lia).
    lazymatch goal with H : chain _ ?mm _ _ ?r ?n2 |- _ => rename H into C2; rename r into rn; rename n2 into ns2; rename mm into mq end.
    destruct (chain_chainv _ _ _ _ _ _ C2) as (v & CRN & CV). unfold wz in CRN.
    pose proof (rw_cells_bound _ _ _ _ CRN) as RNB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in RNB.
    destruct ns2 as [|[pk Ak] rest]; cbn [chainv] in CV.
    - subst v. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
      eapply (EPI 0); try eassumption. left. reflexivity.
    - destruct CV as (-> & OWNk & RGk & (d & hN & N1 & DVd & N2) & _). unfold wz in N1.
      step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
      step. eapply (EPI d); try eassumption. right. exact DVd. }
  step. step. if_cases K.
  - eapply TAIL; eassumption.
  - cstep. eapply TAIL; eassumption.
Qed.
End WithCeiling0.
