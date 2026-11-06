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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PM_model.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RunDraw PU_iface PM_kit PM_iface UM_guards.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Definition PZFILL : Z := 0x3c9d0.        (* [comment removed for export] *)
Definition PZFILL_EXIT : Z := 0x3c9e8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zfill_step : forall (b : byte) (bs0 : list byte) (i : nat), (i < length bs0)%nat ->
  upd (repeat b i ++ skipn i bs0) i b = repeat b (S i) ++ skipn (S i) bs0.
Proof.
  intros b bs0 i. revert bs0. induction i as [|i IH]; intros [|y l] Hi; cbn in Hi; try lia.
  - reflexivity.
  - cbn. f_equal. rewrite (IH l) by lia. reflexivity.
Qed.
Lemma zfill_length : forall (b : byte) (bs0 : list byte) (i : nat), (i <= length bs0)%nat ->
  length (repeat b i ++ skipn i bs0) = length bs0.
Proof. intros b bs0 i Hi. rewrite length_app, repeat_length, length_skipn. lia. Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Section ZFill.
  Variables (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (A n : Z) (bs0 : list byte).
  Hypothesis ARNG : 0 < A /\ A + n < 2^64 - 1.
  Hypothesis NRNG : 0 < n.
  Hypothesis LEN0 : length bs0 = Z.to_nat n.

  Definition ZINV (i : Z) (m1 : mem) : Prop :=
    u8arr usegs m1 A (repeat (Z_to_bv 8 0) (Z.to_nat i) ++ skipn (Z.to_nat i) bs0)
    /\ munch [(A, A + n)] m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1.

  Definition zfill_post : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) (Z_to_bv 64 (A + n))
                    (Z_to_bv 64 (-1)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PZFILL_EXIT) fc None m' (seg_rom usegs)
      /\ ZINV n m'.

  Lemma zinv_store_ok : forall m1 i, ZINV i m1 -> 0 <= i < n -> store_ok usegs m1 (Z_to_bv 64 (A + i)) 1 = true.
  Proof.
    intros m1 i (U & _) Hi. eapply (u8arr_store_ok usegs m1 A _ i); [exact U| rewrite zfill_length; rewrite ?LEN0; lia| reflexivity].
  Qed.
  Lemma zinv_store : forall m1 i, ZINV i m1 -> 0 <= i < n -> ZINV (i + 1) (write_to_mem m1 (Z_to_bv 64 (A + i)) (le1 (Z_to_bv 64 0))).
  Proof.
    intros m1 i (U & MU & WM & MI) Hi.
    change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. change (Z_to_bv 64 (A + i)) with (wa (A + i)). unfold ZINV.
    split; [| split; [| split]].
    - pose proof (u8arr_write usegs m1 A _ i (Z_to_bv 8 0) U ltac:(rewrite zfill_length; rewrite ?LEN0; lia)) as U'.
      rewrite zfill_step in U' by (rewrite LEN0; lia). replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact U'.
    - apply munch_write; [exact MU| lia| cbn; lia| cbn; left; lia].
    - apply wmono_write. exact WM.
    - apply mem_inv_store; [exact MI|]. cbn [length]. eapply (u8arr_store_ok usegs m1 A _ i); [exact U| rewrite zfill_length; rewrite ?LEN0; lia| reflexivity].
  Qed.

  Lemma zfill_loop : forall fuel k m1 (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    Z.of_nat fuel > k -> 0 < k <= n -> ZINV (n - k) m1 ->
    evt usegs zfill_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 k) (Z_to_bv 64 (A + (n - k))) (Z_to_bv 64 (A + n))
               (Z_to_bv 64 (-1)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZFILL) fc None m1 (seg_rom usegs)).
  Proof.
    induction fuel as [|fuel IH]; intros k m1 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 FU Hk INV1; [lia|].
    unfold PZFILL.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].                    (* [comment removed for export] *)
    pose proof (zinv_store_ok m1 (n - k) INV1 ltac:(lia)) as ST1. zstep. clear ST1.   (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV2 : ZINV (n - k + 1) mx) by (exact (zinv_store m1 (n - k) INV1 ltac:(lia)));
      remember mx as m2 eqn:Em2; clear Em2 end.
    clear INV1.
    zstep. if_cases K1; zify_cond K1; [exfalso; lia|].                    (* [comment removed for export] *)
    zstep.                                                                 (* [comment removed for export] *)
    zstep.                                                                 (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      replace (A + (n - k) + 1) with (A + (n - (k + -1))) by lia. replace (n - k + 1) with (n - (k + -1)) in INV2 by lia.
      apply IH; [lia| lia| exact INV2].
    - (* [comment removed for export] *)
      apply evt_done. unfold zfill_post. exists t0, t1, t2, a5, a6, a7, t3, t4, t5, t6, m2.
      replace (k + -1) with 0 by lia. replace (A + (n - k) + 1) with (A + n) by lia. replace (n - k + 1) with n in INV2 by lia.
      split; [reflexivity| exact INV2].
  Qed.
End ZFill.

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
    pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    subst a0 a1. unfold PVCTOR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    clear LBR.
    (* [comment removed for export] *)
    assert (OUTW : forall LB0 SP0 a, 0 <= a < 2^64 -> rclient_addr LB0 SP0 a -> ~ (V <= a < V + 24) -> bv_unsigned sp + -80 <= SP0 ->
              (forall b, In b LB0 -> blk_addr b + blk_size b <= ATOP) -> outside [(lo, SP0); (V, V + 24)] a).
    { intros LB0 SP0 a Ha Hc Hx HS HB. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
      specialize (HB b Hb). lia. }
    do 4 zstep.                                                  (* [comment removed for export] *)
    do 3 zstep.                                                  (* [comment removed for export] *)
    do 2 zstep.                                                  (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      replace (n =? 0) with true by (symmetry; apply Z.eqb_eq; exact K0).
      apply evt_done. apply implM_ret.
      do 5 zstep.
      release_frame FR ST (bv_unsigned sp).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      apply evt_done. unfold helper_post. do 15 eexists. exists m5, errv. split; [reflexivity|].
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
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
      zstep. zstep. zstep.
      zstep. if_cases K2; zify_cond K2; [exfalso; rewrite zb_lxor_ones in K2 by lia; lia|].   (* [comment removed for export] *)
      zstep. zstep.
      do 5 zstep. ret_lit.
      release_frame FR0 ST2 (bv_unsigned sp + -48).
      (* [comment removed for export] *)
      do 3 zstep.
      zstep.                                                                (* [comment removed for export] *)
      zstep.                                                                (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3; [exfalso; lia|].                  (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases K4; zify_cond K4; [exfalso; ubguard K4; lia|].     (* [comment removed for export] *)
      zstep. if_cases K5; zify_cond K5; [exfalso; lia|].                  (* [comment removed for export] *)
      zstep.                                                                (* [comment removed for export] *)
      pose proof (u8arr_of_cells _ _ _ BLK) as U0. cbn [cells_bytes cbytes] in U0. rewrite app_nil_r in U0.
      assert (LENJ : length jk = Z.to_nat n) by (destruct BLK as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
      eapply evt_cut.
      { replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + (n - n))) by (f_equal; lia). replace (Z_to_bv 64 (n + A)) with (Z_to_bv 64 (A + n)) by (f_equal; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply zfill_loop with (m0 := mx) (A := A) (n := n) (bs0 := jk) (fuel := S (Z.to_nat n)) (k := n) end; try lia.
        unfold ZINV. replace (Z.to_nat (n - n)) with 0%nat by lia. cbn [repeat skipn app].
        split; [exact U0|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI2]. }
      intros ms3 PO. destruct PO as (y0 & y1 & y2 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m4 & -> & U4 & MU4 & WM4 & MI4).
      rewrite skipn_all2 in U4 by (rewrite LENJ; lia). rewrite app_nil_r in U4.
      pose proof (cells_of_u8arr _ _ _ U4) as SET4. rewrite repeat_length in SET4.
      trm MU4 WM4.
      assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST2| exact MU4| exact WM4| cbn; lia]).
      clear ST2 MI2 BLK U0 U4. hide MU4. hide WM4.
      (* [comment removed for export] *)
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m4) as MU5. pose proof (wmono_refl usegs m4) as WM5.
      unfold PZFILL_EXIT. zstep. zstep. zstep. ret_lit.
      do 5 zstep.
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
      lazymatch goal with H : rw_cells usegs m5 V _ |- _ => unfold vec_cells; exact H end.
  Qed.
End Proof.
End CANSEC1.
