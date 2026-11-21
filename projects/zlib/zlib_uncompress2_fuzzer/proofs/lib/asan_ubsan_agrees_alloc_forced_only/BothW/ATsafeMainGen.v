(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree Stdio Harness Adapter Driver ProgA
  AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps AsanInv AsanTotal AsanOK RSimProg Prog.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import CMonad ProgAC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require HarnessC AdapterC DriverC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import CLogicA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Client EquivPA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg AProto ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps ATsafeProg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Definition VMAX : Z := MAIN_COST Q_BATCH_BYTES Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX.

Lemma VMAX_val : VMAX = 201752576. Proof. reflexivity. Qed.
Lemma VMAX_room : 0 <= VMAX <= Q_MAX. Proof. rewrite VMAX_val. unfold Q_MAX. lia. Qed.

Section Gen.
  Variable NMAX : nat.
  Variables SB PA : Z.
  Variable A0 : alw.
  Variable K0 : Z.
  Hypothesis HLIM : NLK0 + Z.of_nat NMAX * 4096 <= HLIMIT.
  Hypothesis ABASE_SH : forall z',
    ((exists c, 1 <= c <= 31 /\ shad (SB + c * K_REGION) <= z' < shad (SB + c * K_REGION + UWIN))
     \/ (exists c, 1 <= c <= 31 /\ shad (SB + c * K_REGION + K_FREEARR_OFF) <= z' < shad (SB + c * K_REGION + K_FREEARR_OFF + K_FREEARR_MAX))
     \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> A0 (page_base_of z').
  Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
  Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
  Hypothesis HK0 : 0 <= K0 /\ K0 + VMAX / 1024 <= Z.of_nat NMAX.
  Hypothesis HA0 : abud A0 K0.

  Definition J : list (AsanCtrl.aptr * Z) -> Z -> preT (St:=APS) := JJ NMAX SB PA A0.

  Lemma J_acct : forall Y v RNG A s mo, J Y v RNG A s mo -> acct_ok NMAX RNG A mo.
  Proof. exact (JJ_acct NMAX SB PA A0 HLIM). Qed.
  Lemma J_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> J Y v RNG A s mo -> J Y' v RNG A s mo.
  Proof. exact (JJ_perm NMAX SB PA A0). Qed.
  Lemma J_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> J Y v RNG A s mo -> J Y v' RNG A s mo.
  Proof. exact (JJ_credit NMAX SB PA A0). Qed.
  Lemma J_io : forall n Y v RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> J Y v RNG A s mo -> J Y v RNG A s mo'.
  Proof. exact (JJ_io NMAX SB PA A0 HSB HPA). Qed.
  Lemma J_so : forall Y v RNG A s mo w, J Y v RNG A s mo -> J Y v RNG A (aset_so w s) mo.
  Proof. exact (JJ_so NMAX SB PA A0). Qed.

  Local Notation TSM := (TSM NMAX (St:=APS)).

  Lemma Jm : forall Y v n, 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
    TSM (fun RNG A s mo => J Y v RNG A s mo /\ n + Q_BATCH_BYTES <= v) (amalloc_M n)
        (fun r RNG A s mo => exists q, r = Some q /\ J ((q, n) :: Y) (v - n - Q_BATCH_BYTES) RNG A s mo /\ n < 2^63).
  Proof. exact (U_malloc NMAX SB PA A0 HLIM ABASE_SH). Qed.
  Lemma Jf : forall Y v p n, TSM (J ((p, n) :: Y) v) (afree_M p) (fun _ => J Y v).
  Proof. exact (U_free NMAX SB PA A0 HLIM ABASE_SH). Qed.

  Lemma J_nonneg : forall Y v RNG A s mo, J Y v RNG A s mo -> 0 <= v.
  Proof. intros Y v RNG A s mo (_ & _ & _ & _ & _ & [H _] & _). exact H. Qed.

  Ltac jx := first [ exact J_acct | exact J_perm | exact J_credit | exact J_io | exact J_so | exact Jm | exact Jf | exact asan_qov0 | exact J_nonneg ].

  Lemma Jemit : forall Y v z, TSJ NMAX J Y v (io_emit (ioA AAllocAsan) z).
  Proof. intros Y v z. cbn [io_emit ioA io_S]. eapply s_emit_ok; jx. Qed.

  Lemma Jrun : forall X cfg payload v, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST Q_BATCH_BYTES Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX <= v ->
    TSM (J X v) (runA AAllocAsan cfg payload) (fun _ => J X (v - RUN_COST Q_BATCH_BYTES Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX)).
  Proof.
    intros X cfg payload v HX Hp Hv. unfold runA, fuzz_oneA. cbn [amalloc afree AAllocAsan].
    eapply target_run_ok; try jx; first [apply Jemit| exact HX| exact Hp| exact Hv| exact Client.script_ok| exact EquivPA.client_nreq| exact EquivPA.client_rmax].
  Qed.

  Lemma Jdiag : forall Y v d, TSJ NMAX J Y v (io_diag (ioA AAllocAsan) d).
  Proof. intros. cbn [io_diag ioA io_S]. eapply s_diag_ok; jx. Qed.
  Lemma Jioexit : forall Y v, TSJ NMAX J Y v (io_exit (ioA AAllocAsan)).
  Proof. intros. cbn [io_exit ioA io_S]. eapply stdout_exit_flush_ok; jx. Qed.
  Lemma Jinit : forall Y v bm, TSJ NMAX J Y v (alloc_initA AAllocAsan bm).
  Proof. intros. unfold alloc_initA, target_alloc_init. eapply TSJ_ret; jx. Qed.
  Lemma Jcount : forall Y v, TSJ NMAX J Y v (alloc_countA AAllocAsan).
  Proof. intros. unfold alloc_countA, target_alloc_count. eapply TSJ_ret; jx. Qed.

  Lemma progA_main_ok : forall rs argv v (Q : postM (St:=APS) Empty_set), MAIN_COST Q_BATCH_BYTES Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX <= v ->
    TSM (J [] v) (progA_main AAllocAsan rs argv) Q.
  Proof.
    intros rs argv v Q Hv. unfold progA_main. cbn [amalloc afree aptr_addr AAllocAsan].
    eapply main_exit_ok; try jx; first [apply Jdiag| apply Jinit| apply Jcount| apply Jrun| apply Jioexit| exact Hv| exact EquivPA.client_rmax].
  Qed.

  Lemma JrunC : forall X cfg payload v, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST Q_BATCH_BYTES Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX <= v ->
    cTSM NMAX (J X v) (runAC AAllocAsan cfg payload) (fun _ => J X (v - RUN_COST Q_BATCH_BYTES Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX)).
  Proof.
    intros X cfg payload v HX Hp Hv. unfold runAC, fuzz_oneAC. cbn [amalloc afree AAllocAsan].
    eapply target_runC_ok; try jx; first [apply Jemit| exact HX| exact Hp| exact Hv| exact Client.client_ok| exact EquivPA.client_nreq| exact EquivPA.client_rmax].
  Qed.

  Lemma progA_mainC_ok : forall rs argv v (Q : postM (St:=APS) Empty_set), MAIN_COST Q_BATCH_BYTES Client.CLIENT_MAX_REQS Client.CLIENT_REQ_MAX <= v ->
    cTSM NMAX (J [] v) (progA_mainC AAllocAsan rs argv) Q.
  Proof.
    intros rs argv v Q Hv. unfold progA_mainC. cbn [amalloc afree aptr_addr AAllocAsan].
    eapply main_exitC_ok; try jx; first [apply Jdiag| apply Jinit| apply Jcount| apply JrunC| apply Jioexit| exact Hv| exact EquivPA.client_rmax].
  Qed.

  Lemma J_init : forall s0 mo0,
    AI [] s0 mo0 -> aps_atop s0 = ATOP -> a_space_beg (aps_m s0) = SB -> a_ptr_array (aps_m s0) = PA ->
    QOK [] (aps_m s0) -> acost (aps_m s0) <= 0 ->
    J [] VMAX (fp_ok (m_vm_lazy mo0) A0) A0 s0 mo0.
  Proof.
    intros s0 mo0 HAI HAT ESB EPA HQ HC. pose proof VMAX_room as VR.
    unfold J, JJ. split; [exact HAI|]. split; [exact HAT|]. split; [reflexivity|]. split; [exact ESB|]. split; [exact EPA|].
    split; [split; lia|].
    exists [], K0. split; [exact HQ|]. split; [apply alw_le_refl|]. split; [apply GA_nil|]. split; [exact HA0|]. exact HK0.
  Qed.

  Theorem progA_tsafe_gen : forall rs argv s0 mo0,
    AI [] s0 mo0 -> aps_atop s0 = ATOP -> a_space_beg (aps_m s0) = SB -> a_ptr_array (aps_m s0) = PA ->
    QOK [] (aps_m s0) -> acost (aps_m s0) <= 0 ->
    tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy mo0) A0) A0 (progA_tree AAllocAsan s0 rs argv) mo0.
  Proof.
    intros rs argv s0 mo0 HAI HAT ESB EPA HQ HC.
    apply (TS_tsafeA NMAX _ _ _ _ (EQ (fun (_ : unit) _ _ _ => True))).
    unfold progA_tree. eapply TS_ebind.
    - exact (progA_main_ok rs argv VMAX (fun _ _ _ _ _ => True) ltac:(unfold VMAX; lia) _ _ _ _ (J_init s0 mo0 HAI HAT ESB EPA HQ HC)).
    - intros [[] s] RNG' A' mo' _ _.
  Qed.
  Theorem progA_tsafe_genD : forall D rs argv s0 mo0,
    AI [] s0 mo0 -> aps_atop s0 = ATOP -> a_space_beg (aps_m s0) = SB -> a_ptr_array (aps_m s0) = PA ->
    QOK [] (aps_m s0) -> acost (aps_m s0) <= 0 ->
    tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy mo0) A0) A0 (progA_treeD AAllocAsan D s0 rs argv) mo0.
  Proof.
    intros D rs argv s0 mo0 HAI HAT ESB EPA HQ HC.
    apply (TS_tsafeA NMAX _ _ _ _ (EQ (fun (_ : unit) _ _ _ => True))).
    unfold progA_treeD, progA_mainD. eapply TS_ebind.
    - exact (cTSM_RES NMAX _ _ _ (progA_mainC_ok rs argv VMAX (fun _ _ _ _ _ => True) ltac:(unfold VMAX; lia)) D [] _ _ _ _ (J_init s0 mo0 HAI HAT ESB EPA HQ HC)).
    - intros [[] s] RNG' A' mo' _ _.
  Qed.
End Gen.

Lemma acost_ainit : forall sb pa, acost (ainit sb pa) = 0.
Proof. intros. apply acost_ainit0. Qed.
End CANSEC1.
