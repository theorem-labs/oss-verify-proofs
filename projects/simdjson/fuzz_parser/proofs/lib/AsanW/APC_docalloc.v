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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require PC_kit PC_docalloc.
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
Definition ADOC_ALLOC : Z := 0x962f8.
Definition ADOCALLOC_STACK : Z := 64 + OPNEW_NT_STACK_A.

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition adocalloc_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (len lo DOC : Z) (m : amem) (pp : AsanCtrl.aptr * AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres_x CI LB (bv_unsigned sp) DOC 24 m m'
    /\ aps_rest s' = aps_rest s
    /\ exists SBA TPA jsb jtp,
         ablock_range SBA (SB_BYTES len) /\ ablock_range TPA (TAPE_BYTES len)
         /\ AHEAP AI L RNG' (aps_m s') (HB (snd pp) TPA (TAPE_BYTES len) :: HB (fst pp) SBA (SB_BYTES len) :: LB) m'
         /\ rw_cells asegs m' SBA [CB (Z.to_nat (SB_BYTES len)) jsb] /\ rw_cells asegs m' TPA [CB (Z.to_nat (TAPE_BYTES len)) jtp]
         /\ rw_cells asegs m' DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA); C8 (Z_to_bv 64 (CAP len))].

Definition adocalloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (len lo DOC : Z) (c0 : word),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ADOCALLOC_STACK ->
  bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  rt_got m -> rt_shbase m ->
  rw_cells asegs m DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 c0] -> 0 <= DOC -> DOC + 24 <= ATOP -> DOC mod 8 = 0 ->
  (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= DOC /\ DOC + 24 <= FA + FN /\ ablk FA (FA + FN)) ->
  shc m DOC -> shc m (DOC + 8) -> shc m (DOC + 16) ->
  rng RNG DOC 24 -> rng RNG (shx DOC) 1 -> rng RNG (shx (DOC + 8)) 1 -> rng RNG (shx (DOC + 16)) 1 ->
  0 <= len < 2^26 ->
  In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> aps_ok L s ->
  a0 = Z_to_bv 64 DOC -> a1 = Z_to_bv 64 (CAP len) ->
  implMA RNG (HarnessP.doc_allocate amalloc_M (new_handlerA AAllocAsan) len) s
        (adocalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB len lo DOC m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADOC_ALLOC) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Theorem adocalloc_proof : adocalloc_stmt.
  Proof.
    unfold adocalloc_stmt. intros until c0. intros AH MI ST LOA LOS STOP SP16 TP GOT SHB DC D0 DTOP D8 FK SC0 SC8 SC16 RD RS0 RS8 RS16 HL TRM RSTK RI AOK A0 A1.
    destruct FK as (fcls & FA & FN & INF & FK1 & FK2 & FKB).
    pose proof (ablk_lin _ _ FKB) as (FKB1 & FKB2 & FKB3 & FKB4). unfold AIMG_HI in FKB1. band_ind FKB bF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ADOCALLOC_STACK, OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK in LOS. atop_facts.
    pose proof (proj2 ONTA) as ONT2. unfold opnew_nt_stmtA_at in ONT2.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (PC_docalloc.sb_size_eq len HL) as SBE. pose proof (PC_docalloc.tape_size_eq len HL) as TPE.
    pose proof (sizes_pos len ltac:(lia)) as SZP. pose proof (sizes_upper len ltac:(lia)) as SZU.
    assert (CAPR : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
    unfold HarnessP.doc_allocate.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST.
    subst a0 a1. unfold ADOC_ALLOC.
    unfold shc, shx, ASHOFF in SC0, SC8, SC16. unfold shx, ASHOFF in RS0, RS8, RS16.
    assert (SHB0 : 0x7fff8000 <= Z.shiftr DOC 3 + 2147450880 /\ Z.shiftr (DOC + 16) 3 + 2147450880 + 1 <= 0x10007fff8000
                   /\ Z.shiftr (DOC + 8) 3 = Z.shiftr DOC 3 + 1 /\ Z.shiftr (DOC + 16) 3 = Z.shiftr DOC 3 + 2).
    { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    pose proof (got_nothrow_of_aheap AI _ _ _ _ _ AH MI) as GNT. unfold AGOT_NOTHROW, ANOTHROW in GNT.
    remember (CAP len) as cap eqn:CAPE.
    steps_to 0x9632c. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia| clear K0].
    zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; rewrite Z.shiftr_div_pow2 in K1 by lia; apply K1; apply Z.div_small; lia].
    steps_to 0xe2e60.
    rewrite SBE. apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF| cbn; lia]| apply Forall_nil])
    end.
    eapply implMA_bind.
    { eapply ONT2 with (lo := lo) (n := SB_BYTES len); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact MI | exact ST | exact TP | exact RSTK | exact AOK | exact TRM | (cbn; lia)
              | (unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia) | (unfold AREQMAX; lia) | lia]. }
    cbv beta. intros sbp s1' RNG1 ms1 (FPL1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & SBA & jsb & -> & MI2 & ST2 & HPR1 & ARS1 & BRS & AH2 & BLKS & RSB & RSSB).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR1 by lia.
    retlit.
    assert (INF1 : In (mkABlock (ABFake fcls) FA FN) (HB sbp SBA (SB_BYTES len) :: LB)) by (right; exact INF).
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FR| apply aclient_range_stack; cbn; lia]) end.
    assert (DC2 : rw_cells asegs m2 DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 c0])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact DC| eapply aclient_range_fake; [exact INF| lia| cbn; lia]]).
    assert (SC02 : rw_cells asegs m2 (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact SC0| eapply aclient_range_fake_sh; [exact INF| lia| lia| exact D8| lia]]).
    assert (SC82 : rw_cells asegs m2 (Z.shiftr (DOC + 8) 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact SC8| eapply aclient_range_fake_sh; [exact INF| lia| lia| rewrite Z.add_mod by lia; rewrite D8; reflexivity| lia]]).
    assert (SC162 : rw_cells asegs m2 (Z.shiftr (DOC + 16) 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact SC16| eapply aclient_range_fake_sh; [exact INF| lia| lia| rewrite Z.add_mod by lia; rewrite D8; reflexivity| lia]]).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT2 & _ & _ & SHB2 & _).
    pose proof (got_nothrow_of_aheap AI _ _ _ _ _ AH2 MI2) as GNT2. unfold AGOT_NOTHROW, ANOTHROW in GNT2.
    clear FR DC SC0 SC8 SC16 GOT SHB AH1 GNT.
    pose proof (rng_fp_le _ _ _ _ FPL1 RS0) as RS01. pose proof (rng_fp_le _ _ _ _ FPL1 RS8) as RS81. pose proof (rng_fp_le _ _ _ _ FPL1 RS16) as RS161.
    pose proof (rng_fp_le _ _ _ _ FPL1 RD) as RD1. pose proof (rng_fp_le _ _ _ _ FPL1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FPL1 RI) as RI1.
    clear RS0 RS8 RS16 RD RI.
    pose proof BRS as (BRS1 & BRS2 & BRS3 & BRS4). pose proof (ablk_lin _ _ BRS1) as (BRS1a & BRS1b & BRS1c & BRS1d). unfold AIMG_HI in BRS1a.
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 (or_introl eq_refl) INF1 ltac:(discriminate)) as DJS. cbn [ab_addr ab_size] in DJS.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 24)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    steps_to 0xe2e60.
    rewrite TPE. apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH3 : AHEAP AI L RNG1 (aps_m s1') (HB sbp SBA (SB_BYTES len) :: LB) mx)
        by (eapply (AI_frame AI); [exact AH2| exact MU2| exact WM2|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF1| cbn; lia]| apply Forall_nil])
    end.
    eapply implMA_bind.
    { eapply ONT2 with (lo := lo) (n := TAPE_BYTES len); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH3 | exact TP | exact RSTK1 | exact TRM | eassumption | (cbn; lia)
              | (eapply aps_ok_rest; [exact ARS1| exact AOK])
              | (unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia) | (unfold AREQMAX; lia) | lia]. }
    cbv beta. intros tpp s2' RNG2 ms2 (FPL2 & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & TPA & jtp & -> & MI3 & ST3 & HPR2 & ARS2 & BRT & AH4 & BLKT & RTP & RSTP).
    rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR2 by lia.
    retlit.
    assert (INF2 : In (mkABlock (ABFake fcls) FA FN) (HB tpp TPA (TAPE_BYTES len) :: HB sbp SBA (SB_BYTES len) :: LB)) by (right; exact INF1).
    lazymatch type of FR2 with rw_cells _ _ _ ?cs =>
      assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -64) cs) by (eapply aheap_pres_rw_cells; [exact HPR2| exact FR2| apply aclient_range_stack; cbn; lia]) end.
    lazymatch type of DC2 with rw_cells _ _ _ ?cs =>
      assert (DC3 : rw_cells asegs m3 DOC cs) by (eapply aheap_pres_rw_cells; [exact HPR2| exact DC2| eapply aclient_range_fake; [exact INF1| lia| cbn; lia]]) end.
    assert (SC03 : rw_cells asegs m3 (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR2| exact SC02| eapply aclient_range_fake_sh; [exact INF1| lia| lia| exact D8| lia]]).
    assert (SC83 : rw_cells asegs m3 (Z.shiftr (DOC + 8) 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR2| exact SC82| eapply aclient_range_fake_sh; [exact INF1| lia| lia| rewrite Z.add_mod by lia; rewrite D8; reflexivity| lia]]).
    assert (SC163 : rw_cells asegs m3 (Z.shiftr (DOC + 16) 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR2| exact SC162| eapply aclient_range_fake_sh; [exact INF1| lia| lia| rewrite Z.add_mod by lia; rewrite D8; reflexivity| lia]]).
    assert (BLKS3 : rw_cells asegs m3 SBA [CB (Z.to_nat (SB_BYTES len)) jsb])
      by (eapply aheap_pres_rw_cells; [exact HPR2| exact BLKS| right; left; exists (HB sbp SBA (SB_BYTES len)); split; [left; reflexivity| cbn; lia]]).
    clear FR2 DC2 SC02 SC82 SC162 BLKS GOT2 SHB2 AH3.
    pose proof (rng_fp_le _ _ _ _ FPL2 RS01) as RS02. pose proof (rng_fp_le _ _ _ _ FPL2 RS81) as RS82. pose proof (rng_fp_le _ _ _ _ FPL2 RS161) as RS162.
    pose proof (rng_fp_le _ _ _ _ FPL2 RD1) as RD2. pose proof (rng_fp_le _ _ _ _ FPL2 RSTK1) as RSTK2. pose proof (rng_fp_le _ _ _ _ FPL2 RI1) as RI2.
    clear RS01 RS81 RS161 RD1 RI1.
    pose proof BRT as (BRT1 & BRT2 & BRT3 & BRT4). pose proof (ablk_lin _ _ BRT1) as (BRT1a & BRT1b & BRT1c & BRT1d). unfold AIMG_HI in BRT1a.
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH4 (or_introl eq_refl) INF2 ltac:(discriminate)) as DJT. cbn [ab_addr ab_size] in DJT.
    apply implMA_ret.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 24)] m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    steps_to 0x96458. zstep. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia| clear K4].
    steps_to 0x96468. zstep. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia| clear K5].
    steps_to 0x964f8. zstep.
    release_frame FR3 ST3 (bv_unsigned sp).
    apply evtF_done. unfold adocalloc_post.
    split; [eapply fp_le_trans; eassumption|]. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [exact ST3|].
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
    exists SBA, TPA, jsb, jtp. split; [exact BRS|]. split; [exact BRT|].
    split.
    { eapply (AI_frame AI); [exact AH4| exact MU3| exact WM3|].
      apply Forall_cons; [left; left; cbn; lia|]. apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF2| cbn; lia]| apply Forall_nil]. }
    split; [eassumption|]. split; [eassumption|]. subst cap. exact DC3.
  Qed.

End Proof.
End S.
End CANSEC1.
