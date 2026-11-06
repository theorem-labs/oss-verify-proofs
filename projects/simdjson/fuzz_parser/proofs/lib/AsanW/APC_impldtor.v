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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2 APC_kit3.
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
Definition AIMPL_DTOR : Z := 0xc0748.
Definition AIMPLDTOR_STACK : Z := 32 + AFREE_STACK.

(* [comment removed for export] *)
Definition aimpl_rm (pim psi poc pia : AsanCtrl.aptr) (LB : list ablock) : list ablock :=
  lb_remove pim (lb_remove psi (lb_remove poc (lb_remove pia LB))).

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition aimpldtor_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (pim psi poc pia : AsanCtrl.aptr) (lo : Z) (m : amem) (r : unit) (s' : APS) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (aimpl_rm pim psi poc pia LB) (bv_unsigned sp) m m'
    /\ aps_rest s' = aps_rest s
    /\ AHEAP AI L RNG' (aps_m s') (aimpl_rm pim psi poc pia LB) m'.

Definition aimpldtor_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (pim psi poc pia : AsanCtrl.aptr)
         (AIM ASI AOC AIA nim nsi noc nia lo : Z) (v0 : word) (tr : list Z),
  AHEAP AI L RNG (aps_m s) LB m -> In (HB pim AIM nim) LB -> In (HB psi ASI nsi) LB -> In (HB poc AOC noc) LB -> In (HB pia AIA nia) LB ->
  List.NoDup [pim; psi; poc; pia] -> 72 <= nim ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AIMPLDTOR_STACK ->
  bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m AIM [C8 v0] -> rw_cells asegs m (AIM + 16) [C8 (Z_to_bv 64 ASI)] ->
  rw_cells asegs m (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] ->
  uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr -> bv_unsigned sp + 16 <= bv_unsigned s0 ->
  In (AFREE_PC :: bv_unsigned ra :: tr) (al_U L) -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> (length tr <= 28)%nat ->
  In [AFREE_PC; 0xc0790] (al_U L) -> In [AFREE_PC; 0xc07b8] (al_U L) -> In [AFREE_PC; 0xc07fc] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> aps_ok L s ->
  a0 = Z_to_bv 64 AIM ->
  implMA RNG (HarnessP.impl_dtor afree_M (pim, psi, poc, pia)) s
        (aimpldtor_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB pim psi poc pia lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AIMPL_DTOR) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis ODA : opdelete_arr_stmtA AI.
  Hypothesis OD : opdelete_stmtA AI.
  Theorem aimpldtor_proof : aimpldtor_stmt.
  Proof.
    unfold aimpldtor_stmt. intros until tr.
    intros AH INM INS INO INA ND NIM MI ST LOA LOS STOP SP16 TP IM0 IM16 IM56 UC S0SP TRU RA4 RAF TRL TR1 TR2 TR3 RSTK RI AOK A0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AIMPLDTOR_STACK, AFREE_STACK in LOS. atop_facts.
    assert (NE : pim <> psi /\ pim <> poc /\ pim <> pia /\ psi <> poc /\ psi <> pia /\ poc <> pia).
    { apply NoDup_cons_iff in ND as [N1 ND]. apply NoDup_cons_iff in ND as [N2 ND]. apply NoDup_cons_iff in ND as [N3 _].
      cbn in N1, N2, N3. repeat split; intros E; subst; tauto. }
    destruct NE as (NE1 & NE2 & NE3 & NE4 & NE5 & NE6).
    (* [comment removed for export] *)
    assert (INM1 : In (HB pim AIM nim) (lb_remove pia LB)) by (apply lb_remove_keep_heap; [exact INM| exact NE3]).
    assert (INS1 : In (HB psi ASI nsi) (lb_remove pia LB)) by (apply lb_remove_keep_heap; [exact INS| exact NE5]).
    assert (INO1 : In (HB poc AOC noc) (lb_remove pia LB)) by (apply lb_remove_keep_heap; [exact INO| exact NE6]).
    assert (INM2 : In (HB pim AIM nim) (lb_remove poc (lb_remove pia LB))) by (apply lb_remove_keep_heap; [exact INM1| exact NE2]).
    assert (INS2 : In (HB psi ASI nsi) (lb_remove poc (lb_remove pia LB))) by (apply lb_remove_keep_heap; [exact INS1| exact NE4]).
    assert (INM3 : In (HB pim AIM nim) (lb_remove psi (lb_remove poc (lb_remove pia LB)))) by (apply lb_remove_keep_heap; [exact INM2| exact NE1]).
    clear NE1 NE2 NE3 NE4 NE5 NE6 ND. boxm RAF.
    pose proof ODA as ODA'. unfold opdelete_arr_stmtA, opdelete_stmtA_at in ODA'.
    pose proof (proj1 OD) as ODS. unfold opdelete_stmtA_at in ODS.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH INM) as (NRM & (BM1 & BM2 & BM3 & BM4) & RIM & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH INS) as (_ & (BS1 & BS2 & BS3 & BS4) & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH INO) as (_ & (BO1 & BO2 & BO3 & BO4) & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH INA) as (_ & (BA1 & BA2 & BA3 & BA4) & _).
    pose proof (ablk_lin _ _ BM1) as (BM1a & BM1b & BM1c & BM1d). pose proof (ablk_lin _ _ BS1) as (BS1a & BS1b & BS1c & BS1d).
    pose proof (ablk_lin _ _ BO1) as (BO1a & BO1b & BO1c & BO1d). pose proof (ablk_lin _ _ BA1) as (BA1a & BA1b & BA1c & BA1d).
    unfold AIMG_HI in BM1a, BS1a, BO1a, BA1a. band_ind BM1 bM.
    assert (AM8 : AIM mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof (blk_shx_bounds AIM ltac:(lia) ltac:(lia)) as SB0. pose proof (blk_shx_bounds (AIM + 16) ltac:(lia) ltac:(lia)) as SB16.
    pose proof (blk_shx_bounds (AIM + 56) ltac:(lia) ltac:(lia)) as SB56. pose proof (blk_shx_bounds (AIM + 64) ltac:(lia) ltac:(lia)) as SB64.
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 64) AH INM ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite AM8; reflexivity)) as (SM64 & RM64).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 56) AH INM ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite AM8; reflexivity)) as (SM56 & RM56).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 16) AH INM ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite AM8; reflexivity)) as (SM16 & RM16).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ AIM AH INM ltac:(lia) ltac:(lia) AM8) as (SM0 & RM0).
    assert (IM64 : rw_cells asegs m (AIM + 64) [C8 (Z_to_bv 64 AIA)]) by
      (destruct (rw_cells_cut asegs _ _ _ 1 IM56) as [_ X]; cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X;
       replace (AIM + 64) with (AIM + 56 + 8) by lia; exact X).
    assert (IM56' : rw_cells asegs m (AIM + 56) [C8 (Z_to_bv 64 AOC)]) by
      (destruct (rw_cells_cut asegs _ _ _ 1 IM56) as [X _]; cbn [firstn skipn] in X; exact X).
    clear IM56.
    unfold HarnessP.impl_dtor.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (AIM, AIM + nim)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    subst a0. unfold AIMPL_DTOR.
    steps_to 0xc0784. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia| clear K1].
    steps_to 0xe2e9c.
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (HB pim AIM nim); split; [exact INM| cbn; lia]| apply Forall_nil])
    end.
    (* [comment removed for export] *)
    eapply implMA_bind.
    { eapply ODA' with (lo := lo) (A := AIA) (n := nia) (tr := []); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact INA | eassumption | exact TP | exact TR1 | exact RSTK | exact AOK
              | apply uchain_data; lia | (cbn; lia) | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia) | lia]. }
    cbv beta. intros [] s1' RNG1 ms1 (ARS1 & FPL1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & HPR1 & AH2).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR1 by lia.
    retlit.
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FR| apply aclient_range_stack; cbn; lia]) end.
    lazymatch type of IM0 with rw_cells _ _ _ ?cs =>
      assert (IM0b : rw_cells asegs m2 AIM cs)
        by (eapply aheap_pres_rw_cells; [exact HPR1| exact IM0| right; left; exists (HB pim AIM nim); split; [exact INM1| cbn; lia]]) end.
    assert (IM16b : rw_cells asegs m2 (AIM + 16) [C8 (Z_to_bv 64 ASI)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact IM16| right; left; exists (HB pim AIM nim); split; [exact INM1| cbn; lia]]).
    assert (IM56b : rw_cells asegs m2 (AIM + 56) [C8 (Z_to_bv 64 AOC)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact IM56'| right; left; exists (HB pim AIM nim); split; [exact INM1| cbn; lia]]).
    clear FR IM0 IM16 IM56' IM64 SM64 SM56 SM16 SM0 GOT RIC REAL SHB SUA INI LAY AH1.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT2 & RIC2 & REAL2 & SHB2 & SUA2 & INI2 & LAY2).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 56) AH2 INM1 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite AM8; reflexivity)) as (SM56 & RM56b).
    pose proof (rng_fp_le _ _ _ _ FPL1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FPL1 RI) as RI1. pose proof (rng_fp_le _ _ _ _ FPL1 RIM) as RIM1.
    clear RM64 RM56 RM16 RM0.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (AIM, AIM + nim)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    steps_to 0xc07ac. zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia| clear K2].
    steps_to 0xe2e9c.
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH3 : AHEAP AI L RNG1 (aps_m s1') (lb_remove pia LB) mx)
        by (eapply (AI_frame AI); [exact AH2| exact MU2| exact WM2|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (HB pim AIM nim); split; [exact INM1| cbn; lia]| apply Forall_nil])
    end.
    (* [comment removed for export] *)
    eapply implMA_bind.
    { eapply ODA' with (lo := lo) (A := AOC) (n := noc) (tr := []); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH3 | exact INO1 | eassumption | exact TP | exact TR2 | exact RSTK1 | (eapply aps_ok_rest; [exact ARS1| exact AOK])
              | apply uchain_data; lia | (cbn; lia) | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia) | lia]. }
    cbv beta. intros [] s2' RNG2 ms2 (ARS2 & FPL2 & v0' & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & -> & MI4 & ST4 & HPR2 & AH4).
    rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR2 by lia.
    retlit.
    lazymatch type of FR2 with rw_cells _ _ _ ?cs =>
      assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -32) cs) by (eapply aheap_pres_rw_cells; [exact HPR2| exact FR2| apply aclient_range_stack; cbn; lia]) end.
    lazymatch type of IM0b with rw_cells _ _ _ ?cs =>
      assert (IM0c : rw_cells asegs m4 AIM cs)
        by (eapply aheap_pres_rw_cells; [exact HPR2| exact IM0b| right; left; exists (HB pim AIM nim); split; [exact INM2| cbn; lia]]) end.
    assert (IM16c : rw_cells asegs m4 (AIM + 16) [C8 (Z_to_bv 64 ASI)])
      by (eapply aheap_pres_rw_cells; [exact HPR2| exact IM16b| right; left; exists (HB pim AIM nim); split; [exact INM2| cbn; lia]]).
    clear FR2 IM0b IM16b SM56 GOT2 RIC2 REAL2 SHB2 SUA2 INI2 LAY2 AH3.
    repeat match goal with H : rw_cells asegs _ (AIM + 56) _ |- _ => clear H end.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH4) as (GOT4 & RIC4 & REAL4 & SHB4 & SUA4 & INI4 & LAY4).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ AIM AH4 INM2 ltac:(lia) ltac:(lia) AM8) as (SM0 & RM0).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 16) AH4 INM2 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite AM8; reflexivity)) as (SM16 & RM16).
    pose proof (rng_fp_le _ _ _ _ FPL2 RSTK1) as RSTK2. pose proof (rng_fp_le _ _ _ _ FPL2 RI1) as RI2. pose proof (rng_fp_le _ _ _ _ FPL2 RIM1) as RIM2.
    clear RM56b.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (AIM, AIM + nim)] m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
    steps_to 0xc07f0. zstep. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia| clear K3].
    steps_to 0xe2e9c.
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH5 : AHEAP AI L RNG2 (aps_m s2') (lb_remove poc (lb_remove pia LB)) mx)
        by (eapply (AI_frame AI); [exact AH4| exact MU4| exact WM4|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (HB pim AIM nim); split; [exact INM2| cbn; lia]| apply Forall_nil])
    end.
    (* [comment removed for export] *)
    eapply implMA_bind.
    { eapply ODA' with (lo := lo) (A := ASI) (n := nsi) (tr := []); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH5 | exact INS2 | eassumption | exact TP | exact TR3 | exact RSTK2 | (eapply aps_ok_rest; [etransitivity; [exact ARS2| exact ARS1]| exact AOK])
              | apply uchain_data; lia | (cbn; lia) | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia) | lia]. }
    cbv beta. intros [] s3' RNG3 ms3 (ARS3 & FPL3 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & -> & MI6 & ST6 & HPR3 & AH6).
    rewrite ?unsigned_lit in ST6 by lia. rewrite ?unsigned_lit in HPR3 by lia.
    retlit.
    lazymatch type of FR4 with rw_cells _ _ _ ?cs =>
      assert (FR6 : rw_cells asegs m6 (bv_unsigned sp + -32) cs) by (eapply aheap_pres_rw_cells; [exact HPR3| exact FR4| apply aclient_range_stack; cbn; lia]) end.
    clear FR4 SM0 SM16 GOT4 RIC4 REAL4 SHB4 SUA4 INI4 LAY4 AH5.
    repeat match goal with H : rw_cells asegs _ AIM _ |- _ => clear H | H : rw_cells asegs _ (AIM + 16) _ |- _ => clear H end.
    pose proof (rng_fp_le _ _ _ _ FPL3 RSTK2) as RSTK3. pose proof (rng_fp_le _ _ _ _ FPL3 RI2) as RI3.
    clear RM0 RM16.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
    steps_to 0xe2e98.
    release_frame FR6 ST6 (bv_unsigned sp).
    apply evtF_done.
    (* [comment removed for export] *)
    assert (SPA : ATOP <= bv_unsigned sp) by lia.
    assert (SUB4 : forall b, In b (aimpl_rm pim psi poc pia LB) -> In b LB)
      by (intros b Hb; unfold aimpl_rm in Hb; do 4 apply lb_remove_sub in Hb; exact Hb).
    assert (HL4 : forall b, In b (aimpl_rm pim psi poc pia LB) -> In b LB /\ b <> HB pim AIM nim)
      by (intros b Hb; split; [exact (SUB4 b Hb)| unfold aimpl_rm in Hb; exact (lb_remove_ne _ _ _ _ _ Hb)]).
    assert (OWN4 : forall a, aclient_addr CI (aimpl_rm pim psi poc pia LB) (bv_unsigned sp) a -> outside [(lo, bv_unsigned sp); (AIM, AIM + nim)] a).
    { intros a Hc. pose proof (removed_not_client AI _ _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH INM HL4 SPA Hc) as NR.
      destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH SUB4 Hc) as [Y|Y]; cbn; lia. }
    assert (HPRE : aheap_pres CI (aimpl_rm pim psi poc pia LB) (bv_unsigned sp) m m6).
    { eapply aheap_pres_trans; [eapply aheap_pres_of_munch; [exact MU| exact WM| exact OWN4]|].
      eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact HPR1| lia| intros b Hb; unfold aimpl_rm in Hb; do 3 apply lb_remove_sub in Hb; exact Hb]|].
      eapply aheap_pres_trans; [eapply aheap_pres_of_munch; [exact MU2| exact WM2| exact OWN4]|].
      eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact HPR2| lia| intros b Hb; unfold aimpl_rm in Hb; do 2 apply lb_remove_sub in Hb; exact Hb]|].
      eapply aheap_pres_trans; [eapply aheap_pres_of_munch; [exact MU4| exact WM4| exact OWN4]|].
      eapply aheap_pres_weaken; [exact HPR3| lia| intros b Hb; unfold aimpl_rm in Hb; do 1 apply lb_remove_sub in Hb; exact Hb]. }
    pose proof (uchain_of_pres CI _ _ _ _ _ _ _ _ _ HPRE LY3 ltac:(lia) UC S0SP) as UC6.
    (* [comment removed for export] *)
    eapply implMA_mono.
    { eapply ODS with (lo := lo) (A := AIM) (n := nim) (tr := tr); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH6 | exact INM3 | exact MI6 | exact ST6 | exact TP | exact UC6 | exact TRU | exact RA4 | (unbox RAF; exact RAF) | exact TRL | exact RSTK3
              | (eapply aps_ok_rest; [etransitivity; [exact ARS3| etransitivity; [exact ARS2| exact ARS1]]| exact AOK])
              | (cbn; lia) | (unfold AFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s4' RNG4 ms4 (ARS4 & FPL4 & x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m8 & -> & MI8 & ST8 & HPR4 & AH8).
    unfold aimpldtor_post.
    split; [eapply fp_le_trans; [exact FPL1| eapply fp_le_trans; [exact FPL2| eapply fp_le_trans; [exact FPL3| exact FPL4]]]|].
    do 15 eexists. exists m8. split; [reflexivity|].
    split; [exact MI8|]. split; [exact ST8|].
    split; [eapply aheap_pres_trans; [exact HPRE| exact HPR4]|].
    split; [rewrite ARS4, ARS3, ARS2, ARS1; reflexivity| exact AH8].
  Qed.
End Proof.
End S.
End CANSEC1.
