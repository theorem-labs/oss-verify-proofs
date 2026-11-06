(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PC_kit PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).


Section CANSEC1. Context {rc : runConstT}.
Definition PSETDEPTH : Z := 0x3846c.
Definition SETDEPTH_STACK : Z := 32 + OPNEW_NT_STACK.

Definition setdepth_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B IMPL : Z) (pf : list byte) (m : mem) (pp : bptr * bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_x LB (bv_unsigned sp) (IMPL + 40) 32 m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ exists AOC AIA joc jia,
         rblock_range AOC OC_BYTES /\ rblock_range AIA ISARR_BYTES
         /\ RHEAP s' ((snd pp, AIA, ISARR_BYTES) :: (fst pp, AOC, OC_BYTES) :: LB) m'
         /\ rw_cells psegs m' AOC [CB (Z.to_nat OC_BYTES) joc] /\ rw_cells psegs m' AIA [CB (Z.to_nat ISARR_BYTES) jia]
         /\ rw_cells psegs m' (IMPL + 40) [C8 (Z_to_bv 64 MAX_DEPTH); CB 8 pf; C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)].

Definition setdepth_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (lo B IMPL : Z) (errv d0 : word) (pf : list byte) (pim : bptr),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SETDEPTH_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  In (pim, IMPL, IMPL_BYTES) LB ->
  rw_cells psegs m (IMPL + 40) [C8 d0; CB 8 pf; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells psegs m PGOT_NOTHROW [C8 (Z_to_bv 64 PNOTHROW)] ->
  a0 = Z_to_bv 64 IMPL -> a1 = Z_to_bv 64 MAX_DEPTH ->
  implM psegs (HarnessP.impl_set_max_depth raw_malloc ProgP.new_handler) s
        (setdepth_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B IMPL pf m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PSETDEPTH) fc None m (seg_rom psegs)).

Section Proof.
  Hypothesis ONT : opnew_nt_stmt.
  Theorem setdepth_proof : setdepth_stmt.
  Proof.
    unfold setdepth_stmt. intros until pim. intros HP AUX SPB ST LOA LOS ERR MI TP HIN IC GOT A0 A1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold SETDEPTH_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR. unfold PGOT_NOTHROW, PNOTHROW in GOT.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    destruct (LBR _ HP HIN) as (IB1 & IB2 & IB3 & IB4 & IB5). cbn [blk_addr blk_size fst snd] in IB1, IB2, IB3, IB4, IB5. unfold IMPL_BYTES in *.
    clear LBR.
    unfold HarnessP.impl_set_max_depth, OC_BYTES, ISARR_BYTES, MAX_DEPTH in *.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 32%nat ST.
    subst a0 a1. unfold PSETDEPTH.
    do 7 zstep.
    if_cases K; zify_cond K; [| exfalso; lia].
    do 5 zstep.
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX.
    eapply implM_bind.
    { eapply (proj2 ONT) with (lo := lo) (B := B); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; unfold RERRNO; exact ERR) | (unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia)
              | lia]. }
    cbv beta. intros ocp s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    destruct RR as (AOC & joc & -> & BRO & HP2 & BLKO & _).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    lazymatch goal with FR : rw_cells psegs _ (bv_unsigned sp + -32) ?cs |- _ =>
      assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -32) cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]); clear FR end.
    assert (IC2 : rw_cells psegs m2 (IMPL + 40) [C8 d0; CB 8 pf; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact IC| right; right; exists (pim, IMPL, 96); split; [exact HIN| cbn; lia]]).
    assert (GOT2 : rw_cells psegs m2 482752 [C8 (Z_to_bv 64 113616)])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact GOT| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia]).
    clear IC GOT ST MI ERR AUX1.
    pose proof BRO as (BRO1 & BRO2 & BRO3 & BRO4 & BRO5).
    pose proof (new_block_disj _ _ _ _ _ _ _ HP2 HIN) as NBD. cbn [blk_addr blk_size fst snd] in NBD.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (IMPL + 40, IMPL + 72)] m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
    do 3 zstep.
    if_cases K3; zify_cond K3; [| exfalso; lia].
    do 4 zstep.
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP3 : RHEAP s1' ((ocp, AOC, 8192) :: LB) mx)
        by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU2| exact WM2|];
            apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [right; right; exists (pim, IMPL, 96); split; [right; exact HIN| cbn; lia]| apply Forall_nil]);
      assert (AUX3 : rauxv_ok mx B)
        by (eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil])
    end.
    clear HP2 AUX2.
    eapply implM_bind.
    { eapply (proj2 ONT) with (lo := lo) (B := B); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP3 | exact AUX3 | exact ST2 | exact MI2 | (rewrite errno_lit; unfold RERRNO; exact ERR2) | (unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia)
              | lia]. }
    cbv beta. intros iap s2' ms2 PO.
    destruct PO as (v0 & v1 & v2 & c0' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv2 & -> & MI3 & ST3 & ERR3 & AUX3' & HPR2 & FAE2 & SOE2 & RR2).
    destruct RR2 as (AIA & jia & -> & BRI & HP4 & BLKI & _).
    rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR2 by lia. rewrite errno_lit in ERR3. unfold RERRNO in ERR3.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    lazymatch goal with FR : rw_cells psegs _ (bv_unsigned sp + -32) ?cs |- _ =>
      assert (FR3 : rw_cells psegs m3 (bv_unsigned sp + -32) cs) by (eapply rheap_pres_rw_cells; [exact HPR2| exact FR| left; cbn; lia]); clear FR end.
    lazymatch goal with IC : rw_cells psegs _ (IMPL + 40) ?cs |- _ =>
      assert (IC3 : rw_cells psegs m3 (IMPL + 40) cs)
        by (eapply rheap_pres_rw_cells; [exact HPR2| exact IC| right; right; exists (pim, IMPL, 96); split; [right; exact HIN| cbn; lia]]); clear IC end.
    lazymatch goal with BL : rw_cells psegs _ AOC ?cs |- _ =>
      assert (BLKO3 : rw_cells psegs m3 AOC cs)
        by (eapply rheap_pres_rw_cells; [exact HPR2| exact BL| right; right; exists (ocp, AOC, 8192); split; [left; reflexivity| cbn; lia]]); clear BL end.
    clear ST2 MI2 ERR2 AUX3.
    pose proof BRI as (BRI1 & BRI2 & BRI3 & BRI4 & BRI5).
    pose proof (new_block_disj _ _ _ _ _ _ _ HP4 (or_intror HIN)) as NBD2. cbn [blk_addr blk_size fst snd] in NBD2.
    pose proof (new_block_disj _ _ _ _ _ _ _ HP4 (or_introl eq_refl)) as NBD3. cbn [blk_addr blk_size fst snd] in NBD3.
    apply implM_ret.
    pose proof (munch_refl [(lo, bv_unsigned sp); (IMPL + 40, IMPL + 72)] m3) as MU3. pose proof (wmono_refl psegs m3) as WM3.
    do 3 zstep.
    if_cases K4; zify_cond K4; [| exfalso; lia].
    do 13 zstep.
    assert (B11 : Z.land (Z.b2z (0 <? AIA)) (Z.b2z (0 <? AOC)) = 1)
      by (rewrite (proj2 (Z.ltb_lt 0 AIA)), (proj2 (Z.ltb_lt 0 AOC)) by lia; reflexivity).
    rewrite B11 in *.
    change (Z.land (Z.land (0 + Z.opp 1) 18446744073709551615) 1024) with 1024 in *.
    change (Z.land (Z.land (1 + -1) 18446744073709551615) 2) with 0 in *.
    zstep.
    release_frame FR3 ST3 (bv_unsigned sp).
    apply evt_done. unfold setdepth_post.
    do 15 eexists. exists errv2. split; [reflexivity|].
    assert (OUTW : forall a, 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a -> ~ (IMPL + 40 <= a < IMPL + 40 + 32) ->
              outside [(lo, bv_unsigned sp)] a /\ outside [(lo, bv_unsigned sp); (IMPL + 40, IMPL + 72)] a).
    { intros a Ha Hc Hx. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [split; lia| split; lia|].
      pose proof (LBB b Hb) as LB1. lia. }
    split; [exact MI3|]. split; [exact ST3|]. split; [rewrite errno_lit; exact ERR3|].
    split; [eapply rauxv_ok_frame; [exact AUX3'| exact MU3| exact WM3| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil]|].
    split.
    { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (proj1 (OUTW a Ha Hc Hx))]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b Hb; exact Hb]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (proj2 (OUTW a Ha Hc Hx))]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR2| lia| intros b Hb; right; exact Hb]|].
      eapply rheap_pres_x_of_munch; [exact MU3| exact WM3| intros a Ha Hc Hx; exact (proj2 (OUTW a Ha Hc Hx))]. }
    split; [congruence|]. split; [congruence|].
    exists AOC, AIA, joc, jia. split; [exact BRO|]. split; [exact BRI|].
    split.
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP4| exact MU3| exact WM3|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; exists (pim, IMPL, 96); split; [right; right; exact HIN| cbn; lia]| apply Forall_nil]. }
    split; [exact BLKO3|]. split; [exact BLKI|]. exact IC3.
  Qed.
End Proof.
End CANSEC1.
