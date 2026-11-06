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
Definition ADOC_DTOR : Z := 0x96538.
Definition ADOCDTOR_STACK : Z := 32 + AFREE_STACK.

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition adocdtor_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (psb ptp : AsanCtrl.aptr) (lo DOC : Z) (m : amem) (r : unit) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres_x CI (lb_remove ptp (lb_remove psb LB)) (bv_unsigned sp) DOC 16 m m'
    /\ aps_rest s' = aps_rest s
    /\ AHEAP AI L RNG' (aps_m s') (lb_remove ptp (lb_remove psb LB)) m'.

Definition adocdtor_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (psb ptp : AsanCtrl.aptr) (SBA TPA nsb ntp lo DOC : Z),
  AHEAP AI L RNG (aps_m s) LB m -> In (HB psb SBA nsb) LB -> In (HB ptp TPA ntp) LB -> psb <> ptp ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ADOCDTOR_STACK ->
  bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  rt_got m -> rt_shbase m ->
  rw_cells asegs m DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)] -> 0 <= DOC -> DOC + 16 <= ATOP -> DOC mod 8 = 0 ->
  (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= DOC /\ DOC + 16 <= FA + FN /\ ablk FA (FA + FN)) ->
  shc m DOC -> shc m (DOC + 8) -> rng RNG DOC 16 -> rng RNG (shx DOC) 1 -> rng RNG (shx (DOC + 8)) 1 ->
  bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  In [AFREE_PC; 0x96580] (al_U L) -> In [AFREE_PC; bv_unsigned ra] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> aps_ok L s ->
  a0 = Z_to_bv 64 DOC ->
  implMA RNG (HarnessP.doc_dtor afree_M psb ptp) s
        (adocdtor_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB psb ptp lo DOC m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADOC_DTOR) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis ODA : opdelete_arr_stmtA AI.
  Theorem adocdtor_proof : adocdtor_stmt.
  Proof.
    unfold adocdtor_stmt. intros until DOC. intros AH INS INT NE MI ST LOA LOS STOP SP16 TP GOT SHB DC D0 DTOP D8 FK SC0 SC8 RD RS0 RS8 S0SP RA4 RAF TR1 TR2 RSTK RI AOK A0.
    destruct FK as (fcls & FA & FN & INF & FK1 & FK2 & FKB).
    pose proof (ablk_lin _ _ FKB) as (FKB1 & FKB2 & FKB3 & FKB4). unfold AIMG_HI in FKB1. band_ind FKB bF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ADOCDTOR_STACK, AFREE_STACK in LOS. atop_facts.
    pose proof ODA as ODA'. unfold opdelete_arr_stmtA, opdelete_stmtA_at in ODA'.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    unfold HarnessP.doc_dtor.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    subst a0. unfold ADOC_DTOR.
    unfold shc, shx, ASHOFF in SC0, SC8. unfold shx, ASHOFF in RS0, RS8.
    assert (SHB0 : 0x7fff8000 <= Z.shiftr DOC 3 + 2147450880 /\ Z.shiftr (DOC + 8) 3 + 2147450880 + 1 <= 0x10007fff8000
                   /\ Z.shiftr (DOC + 8) 3 = Z.shiftr DOC 3 + 1).
    { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH INS) as (_ & (BS1 & BS2 & BS3 & BS4) & _).
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH INT) as (_ & (BT1 & BT2 & BT3 & BT4) & _).
    pose proof (ablk_lin _ _ BS1) as (BS1a & BS1b & BS1c & BS1d). pose proof (ablk_lin _ _ BT1) as (BT1a & BT1b & BT1c & BT1d).
    unfold AIMG_HI in BS1a, BT1a.
    steps_to 0x96574. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia| clear K1].
    steps_to 0xe2e9c.
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF| cbn; lia]| apply Forall_nil])
    end.
    eapply implMA_bind.
    { eapply ODA' with (lo := lo) (A := SBA) (n := nsb) (tr := []); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact INS | exact MI | exact ST | exact TP | exact RSTK | exact AOK | exact TR1
              | apply uchain_data; lia | (cbn; lia) | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia) | lia]. }
    cbv beta. intros [] s1' RNG1 ms1 (ARS1 & FPL1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & HPR1 & AH2).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR1 by lia.
    retlit.
    (* [comment removed for export] *)
    assert (INF1 : In (mkABlock (ABFake fcls) FA FN) (lb_remove psb LB)) by (apply lb_remove_keep_fake; exact INF).
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FR| apply aclient_range_stack; cbn; lia]) end.
    lazymatch type of DC with rw_cells _ _ _ ?cs =>
      assert (DC2 : rw_cells asegs m2 DOC cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact DC| eapply aclient_range_fake; [exact INF1| lia| cbn; lia]]) end.
    assert (SC02 : rw_cells asegs m2 (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact SC0| eapply aclient_range_fake_sh; [exact INF1| lia| lia| exact D8| lia]]).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT2 & _ & _ & SHB2 & _).
    clear FR DC SC0 SC8 GOT SHB.
    pose proof (rng_fp_le _ _ _ _ FPL1 RS0) as RS01. pose proof (rng_fp_le _ _ _ _ FPL1 RD) as RD1.
    pose proof (rng_fp_le _ _ _ _ FPL1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FPL1 RI) as RI1.
    clear RS0 RS8 RD RI.
    assert (INT2 : In (HB ptp TPA ntp) (lb_remove psb LB)) by (apply lb_remove_keep_heap; [exact INT| exact (not_eq_sym NE)]).
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 16)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    steps_to 0x96598. zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia| clear K2].
    steps_to 0xe2e9c.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH3 : AHEAP AI L RNG1 (aps_m s1') (lb_remove psb LB) mx)
        by (eapply (AI_frame AI); [exact AH2| exact MU2| exact WM2|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF1| cbn; lia]| apply Forall_nil])
    end.
    eapply implMA_mono.
    { eapply ODA' with (lo := lo) (A := TPA) (n := ntp) (tr := []); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH3 | exact INT2 | eassumption | exact TP | exact TR2
              | apply uchain_data; lia | (cbn; lia) | (unfold AFREE_STACK; lia) | (unfold AFREE_PC in *; lia) | lia
              | (eapply rng_fp_le; [exact FPL1| exact RSTK]) | (eapply aps_ok_rest; [exact ARS1| exact AOK]) ]. }
    cbv beta. intros [] s2' RNG2 ms2 (ARS2 & FPL2 & v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & HPR2 & AH4).
    unfold adocdtor_post. split; [eapply fp_le_trans; eassumption|]. do 15 eexists. exists m3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|].
    assert (SUBL : forall b, In b (lb_remove ptp (lb_remove psb LB)) -> In b LB) by (intros b Hb; apply lb_remove_sub in Hb; apply lb_remove_sub in Hb; exact Hb).
    split.
    { eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH SUBL Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_pres; [exact HPR1| lia| intros b Hb; apply lb_remove_sub in Hb; exact Hb]. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc Hx.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH SUBL Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_of_pres; [exact HPR2| lia| intros b Hb; exact Hb]. }
    split; [congruence| exact AH4].
  Qed.

End Proof.
End S.
End CANSEC1.
