(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.
Definition ASETDEPTH : Z := 0xc04f4.
Definition ASETDEPTH_STACK : Z := 64 + OPNEW_NT_STACK_A.

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition asetdepth_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (lo IMPL : Z) (pf : list byte) (m : amem) (pp : AsanCtrl.aptr * AsanCtrl.aptr) (s' : APS) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres_x CI LB (bv_unsigned sp) (IMPL + 40) 32 m m'
    /\ aps_rest s' = aps_rest s
    /\ exists AOC AIA joc jia,
         ablock_range AOC OC_BYTES /\ ablock_range AIA ISARR_BYTES
         /\ AHEAP AI L RNG' (aps_m s') (HB (snd pp) AIA ISARR_BYTES :: HB (fst pp) AOC OC_BYTES :: LB) m'
         /\ rw_cells asegs m' AOC [CB (Z.to_nat OC_BYTES) joc] /\ rw_cells asegs m' AIA [CB (Z.to_nat ISARR_BYTES) jia]
         /\ rw_cells asegs m' (IMPL + 40) [C8 (Z_to_bv 64 MAX_DEPTH); CB 8 pf; C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)].

Definition asetdepth_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (lo IMPL : Z) (d0 : word) (pf : list byte) (pim : AsanCtrl.aptr),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ASETDEPTH_STACK ->
  bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  rt_got m -> rt_shbase m ->
  In (HB pim IMPL IMPL_BYTES) LB ->
  rw_cells asegs m (IMPL + 40) [C8 d0; CB 8 pf; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> aps_ok L s ->
  a0 = Z_to_bv 64 IMPL -> a1 = Z_to_bv 64 MAX_DEPTH ->
  implMA RNG (HarnessP.impl_set_max_depth amalloc_M (new_handlerA AAllocAsan)) s
        (asetdepth_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo IMPL pf m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASETDEPTH) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Theorem asetdepth_proof : asetdepth_stmt.
  Proof.
    unfold asetdepth_stmt. intros until pim. intros AH MI ST LOA LOS STOP SP16 TP GOT SHB HIN IC TRM RSTK RI AOK A0 A1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ASETDEPTH_STACK, OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK in LOS. atop_facts.
    pose proof (proj2 ONTA) as ONT2. unfold opnew_nt_stmtA_at in ONT2.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & (IB1 & IB2 & IB3 & IB4) & _).
    pose proof (ablk_lin _ _ IB1) as (IB1a & IB1b & IB1c & IB1d). unfold AIMG_HI, IMPL_BYTES in *. band_ind IB1 bI.
    assert (IB4mod8 : IMPL mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof (got_nothrow_of_aheap AI _ _ _ _ _ AH MI) as GNT. unfold AGOT_NOTHROW, ANOTHROW in GNT.
    unfold HarnessP.impl_set_max_depth, OC_BYTES, ISARR_BYTES, MAX_DEPTH in *.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST.
    subst a0 a1. unfold ASETDEPTH.
    steps_to 0xc0520. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; apply K; reflexivity].
    steps_to 0xe2e60.
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx) by (eapply AHEAP_stack_frame; [exact AH| exact MU| exact WM| repeat constructor; cbn; lia]) end.
    eapply implMA_bind.
    { eapply ONT2 with (lo := lo) (n := 8192); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact TP | exact RSTK | exact TRM | exact AOK | eassumption | (cbn; lia)
              | (unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia) | (unfold AREQMAX; lia) | lia]. }
    cbv beta. intros ocp s1' RNG1 ms1 (FPL1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & AOC & joc & -> & MI2 & ST2 & HPR1 & ARS1 & BRO & AH2 & BLKO & ROC & RSOC).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR1 by lia.
    retlit.
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FR| apply aclient_range_stack; cbn; lia]) end.
    lazymatch type of IC with rw_cells _ _ _ ?cs =>
      assert (IC2 : rw_cells asegs m2 (IMPL + 40) cs)
        by (eapply aheap_pres_rw_cells; [exact HPR1| exact IC| right; left; exists (HB pim IMPL 96); split; [exact HIN| cbn; lia]]) end.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT2 & _ & _ & SHB2 & _).
    pose proof (got_nothrow_of_aheap AI _ _ _ _ _ AH2 MI2) as GNT2. unfold AGOT_NOTHROW, ANOTHROW in GNT2.
    clear FR IC GOT SHB GNT AH1.
    pose proof (rng_fp_le _ _ _ _ FPL1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FPL1 RI) as RI1. clear RI.
    pose proof BRO as (BRO1 & BRO2 & BRO3 & BRO4). pose proof (ablk_lin _ _ BRO1) as (BRO1a & BRO1b & BRO1c & BRO1d). unfold AIMG_HI in BRO1a.
    assert (HIN2 : In (HB pim IMPL 96) (HB ocp AOC 8192 :: LB)) by (right; exact HIN).
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH2 HIN) as DJ1. cbn [ab_addr ab_size] in DJ1.
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (IMPL + 56) AH2 HIN2 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite IB4mod8; reflexivity)) as (SC56 & RS56).
    pose proof (blk_shx_bounds (IMPL + 56) ltac:(lia) ltac:(lia)) as SB56.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 HIN2) as (_ & _ & RIM1 & _).
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (IMPL + 40, IMPL + 72)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    steps_to 0xe2e60.
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH3 : AHEAP AI L RNG1 (aps_m s1') (HB ocp AOC 8192 :: LB) mx)
        by (eapply (AI_frame AI); [exact AH2| exact MU2| exact WM2|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (HB pim IMPL 96); split; [exact HIN2| cbn; lia]| apply Forall_nil])
    end.
    eapply implMA_bind.
    { eapply ONT2 with (lo := lo) (n := 1024); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH3 | exact TP | exact RSTK1 | exact TRM | eassumption | (cbn; lia)
              | (eapply aps_ok_rest; [exact ARS1| exact AOK])
              | (unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia) | (unfold AREQMAX; lia) | lia]. }
    cbv beta. intros iap s2' RNG2 ms2 (FPL2 & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & AIA & jia & -> & MI3 & ST3 & HPR2 & ARS2 & BRI & AH4 & BLKI & RIA & RSIA).
    rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR2 by lia.
    retlit.
    lazymatch type of FR2 with rw_cells _ _ _ ?cs =>
      assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -64) cs) by (eapply aheap_pres_rw_cells; [exact HPR2| exact FR2| apply aclient_range_stack; cbn; lia]) end.
    assert (HIN3 : In (HB pim IMPL 96) (HB iap AIA 1024 :: HB ocp AOC 8192 :: LB)) by (right; exact HIN2).
    lazymatch type of IC2 with rw_cells _ _ _ ?cs =>
      assert (IC3 : rw_cells asegs m3 (IMPL + 40) cs)
        by (eapply aheap_pres_rw_cells; [exact HPR2| exact IC2| right; left; exists (HB pim IMPL 96); split; [exact HIN2| cbn; lia]]) end.
    assert (BLKO3 : rw_cells asegs m3 AOC [CB (Z.to_nat 8192) joc])
      by (eapply aheap_pres_rw_cells; [exact HPR2| exact BLKO| right; left; exists (HB ocp AOC 8192); split; [left; reflexivity| cbn; lia]]).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH4) as (GOT3 & _ & _ & SHB3 & _).
    clear FR2 IC2 BLKO GOT2 SHB2 GNT2 SC56 RS56 AH3.
    pose proof (rng_fp_le _ _ _ _ FPL2 RSTK1) as RSTK2. pose proof (rng_fp_le _ _ _ _ FPL2 RI1) as RI2. clear RI1.
    pose proof BRI as (BRI1 & BRI2 & BRI3 & BRI4). pose proof (ablk_lin _ _ BRI1) as (BRI1a & BRI1b & BRI1c & BRI1d). unfold AIMG_HI in BRI1a.
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH4 HIN2) as DJ2. cbn [ab_addr ab_size] in DJ2.
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH4 (or_introl eq_refl)) as DJ3. cbn [ab_addr ab_size] in DJ3.
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (IMPL + 64) AH4 HIN3 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite IB4mod8; reflexivity)) as (SC64 & RS64).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (IMPL + 56) AH4 HIN3 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite IB4mod8; reflexivity)) as (SC56 & RS56).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (IMPL + 40) AH4 HIN3 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite IB4mod8; reflexivity)) as (SC40 & RS40).
    pose proof (blk_shx_bounds (IMPL + 64) ltac:(lia) ltac:(lia)) as SB64. pose proof (blk_shx_bounds (IMPL + 40) ltac:(lia) ltac:(lia)) as SB40.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 HIN3) as (_ & _ & RIM2 & _).
    apply implMA_ret.
    pose proof (munch_refl [(lo, bv_unsigned sp); (IMPL + 40, IMPL + 72)] m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    steps_to 0xc05b8. zstep. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia| clear K4].
    steps_to 0xc05ec.
    replace (AOC <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    change (Z.land (Z.land (Z.b2z false + -1) 18446744073709551615) 1024) with 1024.
    change (Z.shiftl (Z.b2z false) 1) with 0.
    steps_to 0xc0614. zstep.
    release_frame FR3 ST3 (bv_unsigned sp).
    apply evtF_done. unfold asetdepth_post.
    split; [eapply fp_le_trans; eassumption|]. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|].
    split.
    { eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_pres; [exact HPR1| lia| intros b Hb; exact Hb]. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc Hx.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_pres; [exact HPR2| lia| intros b Hb; right; exact Hb]. }
      eapply aheap_pres_x_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc Hx.
      destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
    split; [congruence|].
    exists AOC, AIA, joc, jia. split; [exact BRO|]. split; [exact BRI|].
    split.
    { eapply (AI_frame AI); [exact AH4| exact MU3| exact WM3|].
      apply Forall_cons; [left; left; cbn; lia|]. apply Forall_cons; [right; left; exists (HB pim IMPL 96); split; [exact HIN3| cbn; lia]| apply Forall_nil]. }
    split; [eassumption|]. split; [eassumption| eassumption].
  Qed.
End Proof.
End S.
End CANSEC1.
