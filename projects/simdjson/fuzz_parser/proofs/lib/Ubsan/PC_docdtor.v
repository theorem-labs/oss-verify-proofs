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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import PC_kit PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bptr_eqb_true : forall p q, bptr_eqb p q = true -> p = q.
Proof.
  intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma bptr_eqb_self : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.

Lemma lb_remove_keep_in : forall p b L, In b L -> blk_id b <> p -> In b (lb_remove p L).
Proof.
  intros p b L. unfold lb_remove. induction L as [|c L IH]; intros H NE; [destruct H|].
  rewrite filter_cons. destruct H as [E|H].
  - subst c. destruct (decide _) as [Y|N]; [left; reflexivity|]. exfalso. apply N.
    destruct (bptr_eqb (blk_id b) p) eqn:E; [apply bptr_eqb_true in E; contradiction| exact I].
  - destruct (decide _); [right|]; apply IH; assumption.
Qed.
Lemma lb_remove_in_inv : forall p b L, In b (lb_remove p L) -> In b L.
Proof.
  intros p b L. unfold lb_remove. induction L as [|c L IH]; intros H; [exact H|].
  rewrite filter_cons in H. destruct (decide _); [destruct H as [E|H]; [subst c; left; reflexivity| right; apply IH; exact H]| right; apply IH; exact H].
Qed.
Lemma lb_remove_in_ne : forall p b L, In b (lb_remove p L) -> blk_id b <> p.
Proof.
  intros p b L. unfold lb_remove. induction L as [|c L IH]; intros H; [destruct H|].
  rewrite filter_cons in H. destruct (decide _) as [Y|N]; [|apply IH; exact H].
  destruct H as [E|H]; [|apply IH; exact H]. subst c. intros E.
  rewrite E, bptr_eqb_self in Y. exact Y.
Qed.
Lemma lb_remove_notin' : forall p L, ~ In p (map blk_id L) -> lb_remove p L = L.
Proof.
  intros p L. unfold lb_remove. induction L as [|b L IH]; intros H; [reflexivity|].
  rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
  - rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
  - exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
    + apply H. left. apply bptr_eqb_true in E. exact E.
    + apply N. cbn [negb]. exact I.
Qed.
(* [comment removed for export] *)
Lemma lb_remove_mid : forall L1 b L2, List.NoDup (map blk_id (L1 ++ b :: L2)) -> lb_remove (blk_id b) (L1 ++ b :: L2) = L1 ++ L2.
Proof.
  intros L1 b L2 ND. rewrite map_app in ND. cbn [map] in ND.
  apply NoDup_remove in ND as [ND NI]. rewrite <- map_app in ND, NI.
  unfold lb_remove. rewrite stdpp.list_basics.list.filter_app, filter_cons. rewrite bptr_eqb_self. destruct (decide _) as [Y|N]; [destruct Y|].
  rewrite <- stdpp.list_basics.list.filter_app. apply (lb_remove_notin' (blk_id b) (L1 ++ L2)). exact NI.
Qed.
Lemma lb_remove_hd' : forall b L, List.NoDup (map blk_id (b :: L)) -> lb_remove (blk_id b) (b :: L) = L.
Proof. intros b L ND. exact (lb_remove_mid [] b L ND). Qed.

(* [comment removed for export] *)
Lemma rheap_pres_x_of_pres_rm : forall LB p SP SP' X n m m', rheap_pres (lb_remove p LB) SP' m m' -> SP' <= SP ->
  rheap_pres_x (lb_remove p LB) SP X n m m'.
Proof. intros LB p SP SP' X n m m' H HS. eapply rheap_pres_x_of_pres; [exact H| exact HS| intros b Hb; exact Hb]. Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition PDOC_DTOR : Z := 0x27104.
Definition DOCDTOR_STACK : Z := 16 + RFREE_STACK.

Definition docdtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (psb ptp : bptr) (lo B DOC : Z) (m : mem) (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_x (lb_remove ptp (lb_remove psb LB)) (bv_unsigned sp) DOC 16 m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (lb_remove ptp (lb_remove psb LB)) m'
    /\ stk usegs m' DOC (DOC + 16).

Definition docdtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (psb ptp : bptr) (ASB ATP nsb ntp lo B DOC : Z) (errv : word),
  RHEAP s LB m -> In (psb, ASB, nsb) LB -> In (ptp, ATP, ntp) LB -> psb <> ptp ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - DOCDTOR_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)] -> bv_unsigned sp <= DOC -> DOC + 16 <= B ->
  stk usegs m DOC (DOC + 16) ->
  a0 = Z_to_bv 64 DOC ->
  implM usegs (HarnessP.doc_dtor raw_free psb ptp) s
        (docdtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB psb ptp lo B DOC m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PDOC_DTOR) fc None m (seg_rom usegs)).

Section Proof.
  Hypothesis ODA : opdelete_arr_stmt.
  Theorem docdtor_proof : docdtor_stmt.
  Proof.
    unfold docdtor_stmt. intros until errv. intros HP INS INT NE AUX SPB ST LOA LOS ERR MI TP DC DSP DTOP DSTK A0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold DOCDTOR_STACK, RFREE_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HP INS) as (BS1 & BS2 & BS3 & BS4 & BS5).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HP INT) as (BT1 & BT2 & BT3 & BT4 & BT5).
    cbn [blk_addr blk_size fst snd] in *.
    unfold HarnessP.doc_dtor, HarnessP.opdelete.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 16)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    subst a0. unfold PDOC_DTOR.
    do 7 zstep.
    if_cases K1; zify_cond K1; [exfalso; lia|].
    do 1 zstep.
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX.
    eapply implM_bind.
    { eapply ODA with (lo := lo) (B := B) (A := ASB) (n := nsb); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact INS | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; unfold RERRNO; exact ERR) | (unfold RFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & HP2).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    lazymatch goal with FR : rw_cells usegs _ (bv_unsigned sp + -16) ?cs |- _ =>
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]); clear FR end.
    lazymatch goal with D : rw_cells usegs _ DOC ?cs |- _ =>
      assert (DC2 : rw_cells usegs m2 DOC cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact D| left; cbn; lia]); clear D end.
    lazymatch goal with D : stk usegs _ DOC (DOC + 16) |- _ =>
      assert (DSTK2 : stk usegs m2 DOC (DOC + 16)) by (eapply rheap_pres_stk; [exact HPR| exact D| lia]); clear D end.
    clear ST MI ERR AUX1.
    assert (INT2 : In (ptp, ATP, ntp) (lb_remove psb LB)) by (apply lb_remove_keep_in; [exact INT| cbn; congruence]).
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DOC, DOC + 16)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    do 3 zstep.
    if_cases K2; zify_cond K2; [exfalso; lia|].
    do 4 zstep.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP3 : RHEAP s1' (lb_remove psb LB) mx) by (eapply RHEAP_stack_frame; [exact HP2| exact MU2| exact WM2| repeat constructor; cbn; lia]);
      assert (AUX3 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX2| exact MU2| exact WM2| repeat constructor; cbn; lia])
    end.
    eapply implM_mono.
    { eapply ODA with (lo := lo) (B := B) (A := ATP) (n := ntp); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP3 | exact INT2 | exact AUX3 | exact ST2 | exact MI2 | (rewrite errno_lit; unfold RERRNO; exact ERR2) | (unfold RFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s2' ms2 PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3' & HPR2 & FAE2 & SOE2 & HP4).
    unfold docdtor_post. do 16 eexists. exists errv. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3'|].
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP)
      by (intros b Hb; destruct (RMalloc_ifaceP.RHEAP_block_range_proof s LB _ b HP1 Hb) as (_ & _ & _ & R4 & _); exact R4).
    assert (OUTW : forall LB0 a, 0 <= a < 2^64 -> rclient_addr LB0 (bv_unsigned sp) a -> ~ (DOC <= a < DOC + 16) ->
              (forall b, In b LB0 -> blk_addr b + blk_size b <= ATOP) -> outside [(lo, bv_unsigned sp); (DOC, DOC + 16)] a).
    { intros LB0 a Ha Hc Hx HB. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]. specialize (HB b Hb). lia. }
    assert (LBB2 : forall b, In b (lb_remove ptp (lb_remove psb LB)) -> blk_addr b + blk_size b <= ATOP)
      by (intros b Hb; apply LBB; apply lb_remove_in_inv in Hb; apply lb_remove_in_inv in Hb; exact Hb).
    split.
    { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW _ a Ha Hc Hx LBB2)]|].
      eapply rheap_pres_x_trans.
      { eapply rheap_pres_x_of_pres; [exact HPR| lia|]. intros b Hb. exact (lb_remove_in_inv _ _ _ Hb). }
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (OUTW _ a Ha Hc Hx LBB2)]|].
      eapply rheap_pres_x_of_pres; [exact HPR2| lia| intros b Hb; exact Hb]. }
    split; [congruence|]. split; [congruence|]. split; [exact HP4|].
    lazymatch goal with D : stk usegs _ DOC (DOC + 16) |- _ => eapply rheap_pres_stk; [exact HPR2| exact D| lia] end.
  Qed.
End Proof.
End CANSEC1.
