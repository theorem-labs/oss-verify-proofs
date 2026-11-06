(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import PC_kit PC_ukit PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).



Lemma sb_size_eq : forall len, 0 <= len < 2^26 ->
  Z.land (Z.land (Z.shiftl (Z.shiftr (CAP len * 2863311531) 33) 2 + Z.shiftr (CAP len * 2863311531) 33 + 127) 18446744073709551615)
    18446744073709551552 = SB_BYTES len.
Proof.
  intros len H. assert (C : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
  rewrite div3_magic by lia. rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_pos (CAP len) 3 ltac:(lia) ltac:(lia)). assert (CAP len / 3 <= CAP len) by (apply Z.div_le_upper_bound; lia).
  rewrite land_ones64 by lia. rewrite land_m64 by lia. unfold SB_BYTES, ROUNDUP64. f_equal. f_equal. lia.
Qed.

Lemma tape_size_eq : forall len, 0 <= len < 2^26 ->
  Z.land (Z.land (Z.shiftl (CAP len) 3 + 528) 18446744073709551615) 68719476224 = TAPE_BYTES len.
Proof.
  intros len H. assert (C : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  rewrite land_ones64 by lia. rewrite land_m512_36 by lia. unfold TAPE_BYTES, ROUNDUP64.
  replace (CAP len * 8 + 528) with (8 * (CAP len + 3 + 63)) by lia.
  change 512 with (8 * 64) at 1. rewrite Z.div_mul_cancel_l by lia. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition PDOC_ALLOC : Z := 0x26fb8.
Definition DOCALLOC_STACK : Z := 32 + OPNEW_NT_STACK.

Definition docalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (len lo B DOC : Z) (m : mem) (pp : bptr * bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_x LB (bv_unsigned sp) DOC 24 m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ exists ASB ATP jsb jtp,
         rblock_range ASB (SB_BYTES len) /\ rblock_range ATP (TAPE_BYTES len)
         /\ RHEAP s' ((snd pp, ATP, TAPE_BYTES len) :: (fst pp, ASB, SB_BYTES len) :: LB) m'
         /\ rw_cells usegs m' ASB [CB (Z.to_nat (SB_BYTES len)) jsb] /\ rw_cells usegs m' ATP [CB (Z.to_nat (TAPE_BYTES len)) jtp]
         /\ rw_cells usegs m' DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB); C8 (Z_to_bv 64 (CAP len))].

Definition docalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (len lo B DOC : Z) (errv c0 : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - DOCALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 c0] -> bv_unsigned sp <= DOC -> DOC + 24 <= B ->
  rw_cells usegs m PGOT_NOTHROW [C8 (Z_to_bv 64 PNOTHROW)] ->
  0 <= len < 2^26 ->
  a0 = Z_to_bv 64 DOC -> a1 = Z_to_bv 64 (CAP len) ->
  implM usegs (HarnessP.doc_allocate raw_malloc ProgP.new_handler len) s
        (docalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB len lo B DOC m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PDOC_ALLOC) fc None m (seg_rom usegs)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Proof.
  Hypothesis ONT : opnew_nt_stmt.
  Theorem docalloc_proof : docalloc_stmt.
  Proof.
    unfold docalloc_stmt. intros until c0. intros HP AUX SPB ST LOA LOS ERR MI TP DC DSP DTOP GOT HL A0 A1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold DOCALLOC_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR. unfold PGOT_NOTHROW, PNOTHROW in GOT.
    unfold HarnessP.doc_allocate.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    subst a0 a1. unfold PDOC_ALLOC.
    pose proof (sb_size_eq len HL) as SBE. pose proof (tape_size_eq len HL) as TPE.
    pose proof (sizes_pos len ltac:(lia)) as SZP. pose proof (sizes_upper len ltac:(lia)) as SZU.
    assert (CAPR : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    clear LBR.
    remember (CAP len) as cap eqn:CAPE.
    do 7 zstep.
    if_cases K; zify_cond K; [exfalso; lia|].
    do 3 zstep.
    if_cases K2; zify_cond K2; [| exfalso; rewrite Z.shiftr_div_pow2 in K2 by lia; apply K2; apply Z.div_small; lia].
    do 13 zstep.
    rewrite SBE. apply evt_done.
    assert (FW : Forall (fun iv => ATOP <= fst iv) [(lo, bv_unsigned sp); (DOC, DOC + 24)]) by (repeat constructor; cbn; lia).
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| exact FW]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX.
    eapply implM_bind.
    { eapply (proj2 ONT) with (lo := lo) (B := B); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; unfold RERRNO; exact ERR) | (unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia) | (pose proof (Z.div_le_upper_bound cap 3 cap ltac:(lia) ltac:(lia)); lia)]. }
    cbv beta. intros sbp s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    destruct RR as (ASB & jsb & -> & BRS & HP2 & BLKS & _).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    replace (ret_pc (Z_to_bv 64 159816)) with (Z_to_bv 64 159816) by (symmetry; rpc).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    assert (DC2 : rw_cells usegs m2 DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 c0])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact DC| left; cbn; lia]).
    assert (GOT2 : rw_cells usegs m2 523040 [C8 (Z_to_bv 64 112848)])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact GOT| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia]).
    clear FR DC GOT ST MI ERR AUX1.
    pose proof BRS as (BRS1 & BRS2 & BRS3 & BRS4 & BRS5).
    assert (DATOP : ATOP <= DOC) by lia.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 24)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    do 3 zstep.
    if_cases K3; zify_cond K3; [| exfalso; lia].
    do 9 zstep.
    rewrite TPE. apply evt_done.
    assert (FW2 : Forall (fun iv => ATOP <= fst iv) [(lo, bv_unsigned sp); (DOC, DOC + 24)]) by (repeat constructor; cbn; lia).
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP3 : RHEAP s1' ((sbp, ASB, SB_BYTES len) :: LB) mx) by (eapply RHEAP_stack_frame; [exact HP2| exact MU2| exact WM2| exact FW2]);
      assert (AUX3 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX2| exact MU2| exact WM2| repeat constructor; cbn; lia])
    end.
    clear HP2 AUX2.
    eapply implM_bind.
    { eapply (proj2 ONT) with (lo := lo) (B := B); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP3 | exact AUX3 | exact ST2 | exact MI2 | (rewrite errno_lit; unfold RERRNO; exact ERR2) | (unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia)
              | (pose proof (Z.div_le_upper_bound cap 3 cap ltac:(lia) ltac:(lia)); lia)]. }
    cbv beta. intros tpp s2' ms2 PO.
    destruct PO as (v0 & v1 & v2 & c0' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv2 & -> & MI3 & ST3 & ERR3 & AUX3' & HPR2 & FAE2 & SOE2 & RR2).
    destruct RR2 as (ATP & jtp & -> & BRT & HP4 & BLKT & _).
    rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR2 by lia. rewrite errno_lit in ERR3. unfold RERRNO in ERR3.
    replace (ret_pc (Z_to_bv 64 159872)) with (Z_to_bv 64 159872) by (symmetry; rpc).
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR2| exact FR2| left; cbn; lia]).
    assert (DC3 : rw_cells usegs m3 DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ASB); C8 c0])
      by (eapply rheap_pres_rw_cells; [exact HPR2| exact DC2| left; cbn; lia]).
    assert (GOT3 : rw_cells usegs m3 523040 [C8 (Z_to_bv 64 112848)])
      by (eapply rheap_pres_rw_cells; [exact HPR2| exact GOT2| right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia]).
    assert (BLKS3 : rw_cells usegs m3 ASB [CB (Z.to_nat (SB_BYTES len)) jsb])
      by (eapply rheap_pres_rw_cells; [exact HPR2| exact BLKS| right; right; exists (sbp, ASB, SB_BYTES len); split; [left; reflexivity| cbn; lia]]).
    clear FR2 DC2 GOT2 BLKS ST2 MI2 ERR2 AUX3.
    pose proof BRT as (BRT1 & BRT2 & BRT3 & BRT4 & BRT5).
    apply implM_ret.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 24)] m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    (* [comment removed for export] *)
    do 2 zstep.
    if_cases KA; zify_cond KA; [exfalso; exact (KA (land7_of_mod16 ATP BRT2))|].
    do 3 zstep.
    if_cases K4; zify_cond K4; [| exfalso; lia].
    do 2 zstep.
    if_cases K5; zify_cond K5; [exfalso; lia|].
    do 2 zstep.
    if_cases K6; zify_cond K6; [exfalso; lia|].
    do 3 zstep.
    do 7 zstep.
    release_frame FR3 ST3 (bv_unsigned sp).
    apply evt_done. unfold docalloc_post.
    do 14 eexists. exists m5, errv2. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [rewrite errno_lit; exact ERR3|].
    split; [eapply rauxv_ok_stack_frame; [exact AUX3'| exact MU3| exact WM3| repeat constructor; cbn; lia]|].
    assert (OUTW : forall LB0 a, 0 <= a < 2^64 -> rclient_addr LB0 (bv_unsigned sp) a -> ~ (DOC <= a < DOC + 24) ->
              (forall b, In b LB0 -> blk_addr b + blk_size b <= ATOP) -> outside [(lo, bv_unsigned sp); (DOC, DOC + 24)] a).
    { intros LB0 a Ha Hc Hx HB. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|].
      specialize (HB b Hb). lia. }
    split.
    { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW LB a Ha Hc Hx LBB)]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b Hb; exact Hb]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (OUTW LB a Ha Hc Hx LBB)]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR2| lia| intros b Hb; right; exact Hb]|].
      eapply rheap_pres_x_of_munch; [exact MU3| exact WM3| intros a Ha Hc Hx; exact (OUTW LB a Ha Hc Hx LBB)]. }
    split; [congruence|]. split; [congruence|].
    exists ASB, ATP, jsb, jtp. split; [exact BRS|]. split; [exact BRT|].
    split; [eapply RHEAP_stack_frame; [exact HP4| exact MU3| exact WM3| repeat constructor; cbn; lia]|].
    split; [exact BLKS3|]. split; [exact BLKT|]. subst cap. exact DC3.
  Qed.

End Proof.
End CANSEC1.
