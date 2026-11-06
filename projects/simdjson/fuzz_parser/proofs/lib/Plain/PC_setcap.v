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

Lemma land_m256_35 : forall y, 0 <= y < 2^35 -> Z.land y 34359738112 = y / 256 * 256.
Proof.
  intros y Hy. change 34359738112 with (Z.land (Z.ones 35) (Z.lnot (Z.ones 8))).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma sidx_size_eq : forall len, 0 <= len < 2^26 ->
  Z.land (Z.land (Z.shiftl (CAP len) 2 + 252) 18446744073709551615) 34359738112 + 36 = SIDX_BYTES len.
Proof.
  intros len H. assert (C : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  rewrite land_ones64 by lia. rewrite land_m256_35 by lia. unfold SIDX_BYTES, ROUNDUP64.
  replace (CAP len * 4 + 252) with (4 * (CAP len + 63)) by lia.
  change 256 with (4 * 64) at 1. rewrite Z.div_mul_cancel_l by lia. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition PSETCAP : Z := 0x383a8.
Definition SETCAP_STACK : Z := 32 + OPNEW_NT_STACK.

Definition setcap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (len lo B IMPL : Z) (p1 p2 : list byte) (nx : word) (m : mem) (si : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_x LB (bv_unsigned sp) (IMPL + 8) 32 m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ exists ASI jsi,
         rblock_range ASI (SIDX_BYTES len)
         /\ RHEAP s' ((si, ASI, SIDX_BYTES len) :: LB) m'
         /\ rw_cells psegs m' ASI [C4 (Z_to_bv 64 0); CB (Z.to_nat (SIDX_BYTES len - 4)) jsi]
         /\ rw_cells psegs m' (IMPL + 8) [C4 (Z_to_bv 64 0); CB 4 p1; C8 (Z_to_bv 64 ASI); C4 nx; CB 4 p2; C8 (Z_to_bv 64 (CAP len))].

Definition setcap_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (len lo B IMPL : Z) (errv n0 nx c0 : word) (p1 p2 : list byte) (pim : bptr),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SETCAP_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  In (pim, IMPL, IMPL_BYTES) LB ->
  rw_cells psegs m (IMPL + 8) [C4 n0; CB 4 p1; C8 (Z_to_bv 64 0); C4 nx; CB 4 p2; C8 c0] ->
  rw_cells psegs m PGOT_NOTHROW [C8 (Z_to_bv 64 PNOTHROW)] ->
  0 <= len < 2^26 ->
  a0 = Z_to_bv 64 IMPL -> a1 = Z_to_bv 64 (CAP len) ->
  implM psegs (HarnessP.impl_set_capacity raw_malloc ProgP.new_handler len) s
        (setcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB len lo B IMPL p1 p2 nx m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PSETCAP) fc None m (seg_rom psegs)).

Section Proof.
  Hypothesis ONT : opnew_nt_stmt.
  Theorem setcap_proof : setcap_stmt.
  Proof.
    unfold setcap_stmt. intros until pim. intros HP AUX SPB ST LOA LOS ERR MI TP HIN IC GOT HL A0 A1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold SETCAP_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR. unfold PGOT_NOTHROW, PNOTHROW in GOT.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    destruct (LBR _ HP HIN) as (IB1 & IB2 & IB3 & IB4 & IB5). cbn [blk_addr blk_size fst snd] in IB1, IB2, IB3, IB4, IB5. unfold IMPL_BYTES in *.
    clear LBR.
    unfold HarnessP.impl_set_capacity.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 32%nat ST.
    subst a0 a1. unfold PSETCAP.
    pose proof (sidx_size_eq len HL) as SIE.
    assert (SIDXGE : 36 <= SIDX_BYTES len)
      by (unfold SIDX_BYTES; assert (32 <= CAP len) by (unfold CAP; lia); pose proof (ROUNDUP64_bounds (CAP len) ltac:(lia)); lia).
    pose proof (sizes_pos len ltac:(lia)) as SZP. pose proof (sizes_upper len ltac:(lia)) as SZU.
    assert (CAPR : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
    remember (CAP len) as cap eqn:CAPE.
    do 7 zstep.
    if_cases K; zify_cond K; [| exfalso; rewrite Z.shiftr_div_pow2 in K by lia; apply K; apply Z.div_small; lia].
    do 11 zstep.
    rewrite SIE. apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX.
    eapply implM_post_evt.
    { eapply (proj2 ONT) with (lo := lo) (B := B); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; unfold RERRNO; exact ERR) | (unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia)
              | lia]. }
    cbv beta. intros sip s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    destruct RR as (ASI & jsi & -> & BRS & HP2 & BLKS & _).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -32) [CB 8 (take 8 (take 16 (take 24 junk))); C8 s1; C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    assert (IC2 : rw_cells psegs m2 (IMPL + 8) [C4 n0; CB 4 p1; C8 (Z_to_bv 64 0); C4 nx; CB 4 p2; C8 c0])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact IC| right; right; exists (pim, IMPL, 96); split; [exact HIN| cbn; lia]]).
    clear FR IC GOT ST MI ERR AUX1.
    pose proof BRS as (BRS1 & BRS2 & BRS3 & BRS4 & BRS5).
    pose proof (new_block_disj _ _ _ _ _ _ _ HP2 HIN) as NBD. cbn [blk_addr blk_size fst snd] in NBD.
    assert (BLKS' : rw_cells psegs m2 ASI (mk_CB_cells [4%nat; Z.to_nat (SIDX_BYTES len - 4)] jsi))
      by (pose proof (rw_cells_split_CB psegs m2 ASI [] (Z.to_nat (SIDX_BYTES len)) jsi [] [4%nat; Z.to_nat (SIDX_BYTES len - 4)]) as SPL;
          rewrite app_nil_r in SPL; cbn [app] in SPL; apply SPL; [exact BLKS| cbn [sum_nat]; lia]).
    cbn [mk_CB_cells] in BLKS'. clear BLKS.
    pose proof (munch_refl [(lo, bv_unsigned sp); (IMPL + 8, IMPL + 40); (ASI, ASI + 4)] m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
    do 3 zstep.
    if_cases K3; zify_cond K3; [| exfalso; lia].
    do 2 zstep.
    if_cases K4; zify_cond K4; [| exfalso; lia].
    do 9 zstep.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold setcap_post.
    do 15 eexists. exists errv1. split; [reflexivity|].
    assert (OUTW : forall a, 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a -> ~ (IMPL + 8 <= a < IMPL + 8 + 32) ->
              outside [(lo, bv_unsigned sp)] a /\ outside [(lo, bv_unsigned sp); (IMPL + 8, IMPL + 40); (ASI, ASI + 4)] a).
    { intros a Ha Hc Hx. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [split; lia| split; lia|].
      pose proof (LBB b Hb) as LB1. pose proof (new_block_disj _ _ _ _ _ _ _ HP2 Hb) as D. lia. }
    split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|].
    split; [eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil]|].
    split.
    { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (proj1 (OUTW a Ha Hc Hx))]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b Hb; exact Hb]|].
      eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (proj2 (OUTW a Ha Hc Hx))]. }
    split; [exact FAE|]. split; [exact SOE|].
    exists ASI, (take (Z.to_nat (SIDX_BYTES len - 4)) (drop 4 jsi)). split; [exact BRS|].
    split.
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU2| exact WM2|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; exists (pim, IMPL, 96); split; [right; exact HIN| cbn; lia]|].
      apply Forall_cons; [right; right; exists (sip, ASI, SIDX_BYTES len); split; [left; reflexivity| cbn; lia]| apply Forall_nil]. }
    split; [exact BLKS'| subst cap; exact IC2].
  Qed.
End Proof.
End CANSEC1.
