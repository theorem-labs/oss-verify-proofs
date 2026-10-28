(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface W_akit W_obj_free ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sk_new.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Definition OPENSSL_SK_NEW_NULL_A : Z := 0x1fb288.
Definition SK_NEW_NULL_STACK_A : Z := 32 + CRYPTO_ZALLOC_STACK.
Definition OPENSSL_SK_SET_THUNKS_A : Z := 0x1fb870.
Definition OPENSSL_SK_SET_CMP_THUNKS_A : Z := 0x1fb8c0.
Definition OPENSSL_SK_SET_COPY_THUNKS_A : Z := 0x1fb910.

Notation sk_cells0 := CtSctP.W_sk_new.sk_cells0.
Definition sk_zero_cells : list cell :=
  [C4 (wz 0); C4 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Lemma zero56_sk_cellsA : forall m A,
  rw_cells ctasegs m A [CB 56%nat (repeat (Z_to_bv 8 0) 56%nat)] -> rw_cells ctasegs m A sk_zero_cells.
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; auto| unfold sk_zero_cells, MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

Definition setter_siteA (entry : Z) (cmp fr cp f cmp' fr' cp' : Z) : Prop :=
  (entry = OPENSSL_SK_SET_CMP_THUNKS_A /\ cmp' = f /\ fr' = fr /\ cp' = cp)
  \/ (entry = OPENSSL_SK_SET_THUNKS_A /\ cmp' = cmp /\ fr' = f /\ cp' = cp)
  \/ (entry = OPENSSL_SK_SET_COPY_THUNKS_A /\ cmp' = cmp /\ fr' = fr /\ cp' = f).

Local Notation E_skn_zalloc := (E_OPENSSL_sk_new_null_1f6928 : uk_call 0x1fb288 0x1fb2bc 0x1fcef0).   (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma OPENSSL_sk_new_null_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SK_NEW_NULL_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx OPENSSL_SK_NEW_NULL_A (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB STACK_SIZE lo m
                  (fun A m' => rw_cells ctasegs m' A (sk_cells0 0 0 0)) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc STACK_SIZE k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz OPENSSL_SK_NEW_NULL_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS UW CTX K.
  unfold SK_NEW_NULL_STACK_A, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, OPENSSL_SK_NEW_NULL_A, STACK_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  carve_frame 32%nat ST. do 5 step.
  (* [comment removed for export] *)
  do 5 step.
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia | constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU1) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done.
  eapply (CRYPTO_zalloc_walkAp) with (n := 56) (lo := lo) (OW := OW) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity.
  - exact HEAP1.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. lia.
  - rewrite ESP. alia.
  - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact CS1.
  - lia.
  - unfold mcost. cbn. exact (af_credit_nonneg RT AF Σ m1 (AH_art _ _ _ _ HEAP1)).
  - rewrite ESP. uw_call_mu_tac m 32 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia].
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_skn_zalloc CTX).
  - intros p Σ' ms' Hp PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & A & -> & MI2 & ST2 & AG2 & CR2 & BR2 & HEAP2 & ACC2 & BLK).
    unfold MallocRep.wz in *. rewrite ESP in ST2, AG2.
    rewrite (ret_pc_even 0x1fb2bc) by (lia || reflexivity).
    pose proof BR2 as (A0 & A16 & _ & ACE & AIMG).
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; alia).
    pose proof (AH_offsh _ _ _ _ (p, A, 56) HEAP2 (or_introl eq_refl)) as OSHA. cbn [blk_addr blk_size fst snd] in OSHA.
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; alia].
    apply zero56_sk_cellsA in BLK. unfold sk_zero_cells, MallocRep.wz in BLK.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 56)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
    assert (OFF2 : offshW [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 56)]%Z) by (cbn [offshW]; alia).
    rename MU1 into MU0. clear WM1 HEAP1 CS1 SHB1 SHB2.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA in KA; lia|]. clear KA.
    step. step. step.
    do 3 step. release_frame FR ST2 (bv_unsigned sp). step. step.
    name_mem m9.
    apply evt_done. apply (K p Σ' _ Hp).
    unfold calloc_postA, MallocRep.wz.
    do 16 eexists. exists m9, A. split; [reflexivity|].
    assert (MU9 : munch [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 56)]%Z m2 m9) by assumption.
    split; [assumption|]. split; [assumption|].
    split.
    { eapply agree_on_trans; [| eapply agree_on_trans; [eapply agree_on_mono; [exact AG2| intros a [Ha|[Ha|Ha]]; [left; lia| right; left; exact Ha| right; right; exact Ha]]|]].
      - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU0)|].
        intros a [Ha|[Ha|Ha]]; cbn [outside]; (split; [|exact I]).
        + lia.
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
        + destruct Ha as (b & Hb & Hr). pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
      - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU9)|]. intros a Ha. cbn [outside].
        split; [| split; [| exact I]].
        + destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
          * destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
          * pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
        + intros HAr. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
          * unfold BnHeapA.ACEIL in *. lia.
          * eapply (blk_not_static _ ((p, A, 56) :: OW) LB m2 (p, A, 56) a HEAP2 (or_introl eq_refl)); [cbn; lia | exact Ha].
          * assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
            pose proof (AH_disjoint_gen _ _ _ _ b (p, A, 56) HEAP2 (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia. }
    split; [exact CR2|]. split; [exact BR2|].
    assert (HEAP9 : AHEAP Σ' ((p, A, 56) :: OW) LB m9).
    { eapply AH_frame; [exact HEAP2| exact MU9| apply wmono_refl || assumption|].
      constructor; [left; cbn; alia|]. constructor; [right; right; exists (p, A, 56); split; [left; reflexivity| cbn; lia]| constructor]. }
    split; [exact HEAP9|].
    split; [exact (proj2 (AH_acc _ _ _ _ (p, A, 56) HEAP9 (or_introl eq_refl)))|].
    unfold CtSctP.W_sk_new.sk_cells0, MallocRep.wz.
    match goal with H : rw_cells ctasegs m9 A _ |- _ => exact H end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma OPENSSL_sk_set_thunk_specA : forall (entry cmp fr cp f cmp' fr' cp' : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (pst : bptr) (SA : Z),
  setter_siteA entry cmp fr cp f cmp' fr' cp' ->
  AHEAP Σ OW LB m -> In (pst, SA, STACK_SIZE) (OW ++ LB) ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 16 ->
  rw_cells ctasegs m SA (sk_cells0 cmp fr cp) -> 0 <= f < 2^64 ->
  SA mod 16 = 0 ->                                          (* [comment removed for export] *)
  a0 = wz SA -> a1 = wz f ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz SA) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctasegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (SA, SA + STACK_SIZE)] m m' /\ wmono ctasegs m m'
               /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
               /\ rw_cells ctasegs m' SA (sk_cells0 cmp' fr' cp'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until SA. intros SITE HEAP HIN ST MI CEIL LO HC Hf AL16 -> ->.
  unfold OPENSSL_SK_SET_CMP_THUNKS_A, OPENSSL_SK_SET_THUNKS_A, OPENSSL_SK_SET_COPY_THUNKS_A, STACK_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  assert (EA : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; alia).
  ablock HEAP HIN ACCS OFFS.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (SA, SA + 56)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (SA, SA + 56)]%Z) by (cbn [offshW]; alia).
  assert (SEPA : SA + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= SA) by (unfold BnHeapA.ACEIL in *; lia).
  unfold CtSctP.W_sk_new.sk_cells0, MallocRep.wz in HC.
  destruct SITE as [(-> & -> & -> & ->)|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]];
    (carve_frame 16%nat ST; do 4 step;
     step; if_cases K; zify_cond K; [exfalso; rewrite ?EA in K; lia|]; clear K;
     step; do 2 step; release_frame FR ST (bv_unsigned sp); step; step;
     name_mem m2; apply evt_done; do 15 eexists; split; [reflexivity|];
     split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; unfold CtSctP.W_sk_new.sk_cells0, MallocRep.wz;
     match goal with H : rw_cells ctasegs _ SA _ |- _ => exact H end).
Qed.

End WithRT.
