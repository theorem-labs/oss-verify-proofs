(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg F_memset.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RunDraw PU_iface PM_kit PM_model PM_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Section Proof.
  Hypothesis ON : opnew_stmt.

  Theorem vctor_proof : vctor_stmt.
  Proof.
    unfold vctor_stmt. intros until vj. intros HP AUX SPB ST LOA LOS ERR MI TP VC VSP VB HN A0 A1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold VCTOR_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    unfold vctor_model.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 32%nat ST.
    subst a0 a1. unfold PVCTOR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    clear LBR.
    (* [comment removed for export] *)
    assert (OUTW : forall LB0 SP0 a, 0 <= a < 2^64 -> rclient_addr LB0 SP0 a -> ~ (V <= a < V + 24) -> bv_unsigned sp + -64 <= SP0 ->
              (forall b, In b LB0 -> blk_addr b + blk_size b <= ATOP) -> outside [(lo, SP0); (V, V + 24)] a).
    { intros LB0 SP0 a Ha Hc Hx HS HB. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
      specialize (HB b Hb). lia. }
    do 8 zstep.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      replace (n =? 0) with true by (symmetry; apply Z.eqb_eq; exact K0).
      apply evt_done. apply implM_ret.
      do 6 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold helper_post. do 15 eexists. exists m0, errv. split; [reflexivity|].
      split; [exact MI|]. split; [exact ST|]. split; [rewrite errno_lit; exact ERR|].
      split; [eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia]|].
      split; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
      split; [reflexivity|]. split; [reflexivity|].
      unfold vctor_K. split; [exact K0|]. split; [| exact VC].
      eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia].
    - (* [comment removed for export] *)
      replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact K0).
      do 3 zstep.
      carve_frame 32%nat ST.
      do 4 zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].     (* [comment removed for export] *)
      do 4 zstep.
      apply evt_done.
      assert (FW : Forall (fun iv => ATOP <= fst iv) [(lo, bv_unsigned sp); (V, V + 24)]) by (repeat constructor; cbn; lia).
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| exact FW]);
        assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
      end.
      clear HP AUX. hide MU. hide WM.
      eapply implM_bind.
      { eapply ON with (lo := lo) (B := B); try reflexivity; rewrite ?unsigned_lit by lia;
          first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; exact ERR) | (unfold OPNEW_STACK, RMALLOC_STACK; lia) ]. }
      cbv beta. intros p s1' ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
      destruct RR as (A & jk & -> & BR & HP2 & BLK & _).
      rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
      ret_lit.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      (* [comment removed for export] *)
      trp HPR. clear ST MI ERR AUX1 HP1.
      (* [comment removed for export] *)
      apply implM_ret.
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
      do 4 zstep.
      do 5 zstep. ret_lit.
      release_frame FR0 ST2 (bv_unsigned sp + -32).
      (* [comment removed for export] *)
      do 5 zstep.
      eapply evt_cut.
      { eapply memset_spec; rewrite ?unsigned_lit by lia; [exact BLK| exact MI2]. }
      intros ms3 PO. destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & SET4).
      rewrite ?unsigned_lit in MU4 by lia. rewrite ?unsigned_lit in SET4 by lia. change (0 mod 256) with 0 in SET4.
      ret_lit.
      trm MU4 WM4.
      assert (ST4 : stk psegs m4 lo (bv_unsigned sp + -32)) by (eapply stk_transport_disjoint; [exact ST2| exact MU4| exact WM4| cbn; lia]).
      clear ST2 MI2 BLK. hide MU4. hide WM4.
      (* [comment removed for export] *)
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
      zstep.
      do 6 zstep.
      release_frame FR ST4 (bv_unsigned sp).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      apply evt_done. unfold helper_post. do 15 eexists. exists m5, errv2. split; [reflexivity|].
      split; [exact MI4|]. split; [exact ST4|]. split; [rewrite errno_lit; exact ERR2|].
      assert (FWB : Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv))
                      [(lo, bv_unsigned sp); (V, V + 24)]) by (unfold RAUXV_CELL; repeat constructor; cbn; lia).
      unhide MU4. unhide WM4.
      split.
      { eapply rauxv_ok_frame; [| exact MU5| exact WM5| exact FWB].
        eapply rauxv_ok_frame; [| exact MU4| exact WM4| constructor; [cbn; unfold RAUXV_CELL; split; [lia| destruct BR5; [left; lia| right; lia]]| constructor]].
        eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2| exact FWB]. }
      split.
      { unhide MU. unhide WM.
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b Hb; exact Hb]|].
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
        eapply rheap_pres_x_trans.
        { eapply rheap_pres_x_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc Hx. cbn.
          destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [split; [lia| exact I]| unfold ralloc_static in Hc; split; [lia| exact I]|].
          pose proof (new_block_disj _ _ _ _ _ _ b HP2 Hb). split; [lia| exact I]. }
        eapply rheap_pres_x_of_munch; [exact MU5| exact WM5| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]. }
      split; [exact FAE|]. split; [exact SOE|].
      unfold vctor_K. exists A. split; [lia|]. split; [exact BR|]. split.
      { eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU5| exact WM5| repeat constructor; cbn; lia].
        eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU4| exact WM4|].
        2:{ constructor; [| constructor]. right; right. exists (p, A, n). split; [left; reflexivity| cbn; lia]. }
        eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU2| exact WM2| repeat constructor; cbn; lia]. }
      split; [exact SET4|].
      lazymatch goal with H : rw_cells psegs m5 V _ |- _ => unfold vec_cells; exact H end.
  Qed.
End Proof.
End CANSEC1.
