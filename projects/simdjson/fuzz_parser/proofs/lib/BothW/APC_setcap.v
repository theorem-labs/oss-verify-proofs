(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import ShadowTac APC_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require PC_kit PC_setcap.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_bkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.
Definition ASETCAP : Z := 0xcb288.
Definition ASETCAP_STACK : Z := 48 + OPNEW_NT_STACK_A.

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition asetcap_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (len lo IMPL : Z) (p1 p2 : list byte) (nx : word) (m : amem) (si : AsanCtrl.aptr) (s' : APS) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres_x CI LB (bv_unsigned sp) (IMPL + 8) 32 m m'
    /\ aps_rest s' = aps_rest s
    /\ exists ASI jsi,
         ablock_range ASI (SIDX_BYTES len)
         /\ AHEAP AI L RNG' (aps_m s') (HB si ASI (SIDX_BYTES len) :: LB) m'
         /\ rw_cells bsegs m' ASI [C4 (Z_to_bv 64 0); CB (Z.to_nat (SIDX_BYTES len - 4)) jsi]
         /\ rw_cells bsegs m' (IMPL + 8) [C4 (Z_to_bv 64 0); CB 4 p1; C8 (Z_to_bv 64 ASI); C4 nx; CB 4 p2; C8 (Z_to_bv 64 (CAP len))].

Definition asetcap_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (len lo IMPL : Z) (n0 nx c0 : word) (p1 p2 : list byte)
         (pim : AsanCtrl.aptr),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ASETCAP_STACK ->
  bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  rt_got m -> rt_shbase m ->
  In (HB pim IMPL IMPL_BYTES) LB ->
  rw_cells bsegs m (IMPL + 8) [C4 n0; CB 4 p1; C8 (Z_to_bv 64 0); C4 nx; CB 4 p2; C8 c0] ->
  0 <= len < 2^26 ->
  In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> aps_ok L s ->
  a0 = Z_to_bv 64 IMPL -> a1 = Z_to_bv 64 (CAP len) ->
  implMA RNG (HarnessP.impl_set_capacity amalloc_M (new_handlerA AAllocAsan) len) s
        (asetcap_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB len lo IMPL p1 p2 nx m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASETCAP) fc None m (seg_rom bsegs)).

Section Proof.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Theorem asetcap_proof : asetcap_stmt.
  Proof.
    unfold asetcap_stmt. intros until pim. intros AH MI ST LOA LOS STOP SP16 TP GOT SHB HIN IC HL TRM RSTK RI AOK A0 A1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ASETCAP_STACK, OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK in LOS. atop_facts.
    pose proof (proj2 ONTA) as ONT2. unfold opnew_nt_stmtA_at in ONT2.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & (IB1 & IB2 & IB3 & IB4) & _).
    pose proof (ablk_lin _ _ IB1) as (IB1a & IB1b & IB1c & IB1d). unfold AIMG_HI, IMPL_BYTES in *. band_ind IB1 bI.
    assert (IB4mod8 : IMPL mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof (PC_setcap.sidx_size_eq len HL) as SIE.
    assert (SIDXGE : 36 <= SIDX_BYTES len)
      by (unfold SIDX_BYTES; assert (32 <= CAP len) by (unfold CAP; lia); pose proof (ROUNDUP64_bounds (CAP len) ltac:(lia)); lia).
    pose proof (sizes_pos len ltac:(lia)) as SZP. pose proof (sizes_upper len ltac:(lia)) as SZU.
    assert (CAPR : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
    pose proof (got_nothrow_of_aheap AI _ _ _ _ _ AH MI) as GNT. unfold AGOT_NOTHROW, ANOTHROW in GNT.
    unfold HarnessP.impl_set_capacity.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 48%nat ST.
    subst a0 a1. unfold ASETCAP.
    remember (CAP len) as cap eqn:CAPE.
    steps_to 0xcb2ac. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; rewrite Z.shiftr_div_pow2 in K by lia; apply K; apply Z.div_small; lia].
    steps_to 0xee5e0.
    rewrite SIE. apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx) by (eapply AHEAP_stack_frame; [exact AH| exact MU| exact WM| repeat constructor; cbn; lia]) end.
    eapply implMA_post_evtF.
    { eapply ONT2 with (lo := lo) (n := SIDX_BYTES len); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact TP | exact RSTK | exact TRM | exact AOK | eassumption | (cbn; lia)
              | (unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia) | (unfold AREQMAX; lia) | lia]. }
    cbv beta. intros sip s1' RNG1 ms1 (FPL1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ASI & jsi & -> & MI2 & ST2 & HPR1 & ARS1 & BRS & AH2 & BLKS & RSI & RSSI).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR1 by lia.
    retlit.
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -48) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FR| apply aclient_range_stack; cbn; lia]) end.
    assert (IC2 : rw_cells bsegs m2 (IMPL + 8) [C4 n0; CB 4 p1; C8 (Z_to_bv 64 0); C4 nx; CB 4 p2; C8 c0])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact IC| right; left; exists (HB pim IMPL 96); split; [exact HIN| cbn; lia]]).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT2 & _ & _ & SHB2 & _).
    clear FR IC GOT SHB GNT AH1.
    pose proof (rng_fp_le _ _ _ _ FPL1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FPL1 RI) as RI1. clear RI.
    pose proof BRS as (BRS1 & BRS2 & BRS3 & BRS4). pose proof (ablk_lin _ _ BRS1) as (BRS1a & BRS1b & BRS1c & BRS1d). unfold AIMG_HI in BRS1a.
    band_ind BRS1 bS.
    assert (HIN2 : In (HB pim IMPL 96) (HB sip ASI (SIDX_BYTES len) :: LB)) by (right; exact HIN).
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH2 HIN) as DJ. cbn [ab_addr ab_size] in DJ.
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (IMPL + 16) AH2 HIN2 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite IB4mod8; reflexivity)) as (SC16 & RS16).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (IMPL + 8) AH2 HIN2 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite IB4mod8; reflexivity)) as (SC8 & RS8).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (IMPL + 32) AH2 HIN2 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite IB4mod8; reflexivity)) as (SC32 & RS32).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ ASI AH2 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (SCI & RSCI).
    pose proof (blk_shx_bounds (IMPL + 8) ltac:(lia) ltac:(lia)) as SB8. pose proof (blk_shx_bounds (IMPL + 16) ltac:(lia) ltac:(lia)) as SB16.
    pose proof (blk_shx_bounds (IMPL + 32) ltac:(lia) ltac:(lia)) as SB32. pose proof (blk_shx_bounds ASI ltac:(lia) ltac:(lia)) as SBI.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 HIN2) as (_ & _ & RIM & _).
    assert (BLKS' : rw_cells bsegs m2 ASI (mk_CB_cells [4%nat; Z.to_nat (SIDX_BYTES len - 4)] jsi))
      by (pose proof (rw_cells_split_CB bsegs m2 ASI [] (Z.to_nat (SIDX_BYTES len)) jsi [] [4%nat; Z.to_nat (SIDX_BYTES len - 4)]) as SPL;
          rewrite app_nil_r in SPL; cbn [app] in SPL; apply SPL; [exact BLKS| cbn [sum_nat]; lia]).
    cbn [mk_CB_cells] in BLKS'. clear BLKS.
    pose proof (munch_refl [(lo, bv_unsigned sp); (IMPL + 8, IMPL + 40); (ASI, ASI + 4)] m2) as MU2. pose proof (wmono_refl bsegs m2) as WM2.
    (* [comment removed for export] *)
    steps_to 0xcb2f4. zstep. if_cases KA; zify_cond KA; [exfalso; exact (KA (land3_of_mod16 ASI BRS4))|].
    steps_to 0xcb32c. zstep. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia| clear K3].
    (* [comment removed for export] *)
    steps_to 0xcb334. zstep. if_cases KB; zify_cond KB; [exfalso; exact (KB (land3_of_mod16 ASI BRS4))|].
    steps_to 0xcb39c. zstep.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold asetcap_post.
    split; [exact FPL1|]. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|].
    split.
    { eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_pres; [exact HPR1| lia| intros b Hb; exact Hb]. }
      eapply aheap_pres_x_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc Hx.
      pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH2 ltac:(lia) Hc) as NF.
      destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
    split; [exact ARS1|].
    exists ASI, (take (Z.to_nat (SIDX_BYTES len - 4)) (drop 4 jsi)). split; [exact BRS|].
    split.
    { eapply (AI_frame AI); [exact AH2| exact MU2| exact WM2|].
      apply Forall_cons; [left; left; cbn; lia|]. apply Forall_cons; [right; left; exists (HB pim IMPL 96); split; [exact HIN2| cbn; lia]|].
      apply Forall_cons; [right; left; exists (HB sip ASI (SIDX_BYTES len)); split; [left; reflexivity| cbn; lia]| apply Forall_nil]. }
    split; [exact BLKS'| subst cap; exact IC2].
  Qed.
End Proof.
End S.
End CANSEC1.
