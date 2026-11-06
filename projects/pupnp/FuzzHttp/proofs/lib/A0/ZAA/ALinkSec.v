(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning ITree Nodes Decode Ceiling VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout PEnv ASec F_sec_A LJ ALinkPg ALinkVm ALink.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation stwfL := (Bridge.stwf nodeL nstepL nexitL nsafeL).

Section S.
Context {HC : HasCeiling}.
Variable Bs : vmbase.
Variable AL : alayout.
Hypothesis BO : base_ok Bs.

Definition parr_step_cost : Z := 155648.
#[using="Type"] Lemma parr_step_cost_eq : K_PARR_STEP + K_PARR_STEP / 8 + 2 * page_size = parr_step_cost. Proof. reflexivity. Qed.

Definition va_sec_alloc (v : vabs) (S : asec) (a n : Z) : vabs :=
  mkVA (va_prim v) ((a, n) :: va_chunks v) (va_nsec v + 1) (va_aux v + (if se_n S =? se_nres S then parr_step_cost else 0)).

#[using="BO"] Lemma link_sec_alloc : forall v mo (S : asec) size avoid (Q : exc Z -> Model -> Prop),
  LINK Bs v mo ->
  let n := lenZ (sec_msize size) in
  69632 <= n -> avoid_ok mo avoid ->
  vroom Bs v (n + (n / 8 + 2 * page_size) + 8192 + parr_step_cost) -> gap_room Bs v n ->
  (se_n S = se_nres S ->
     (exists e, In e (vb_maps Bs) /\ vlo e <= al_parr AL + 8 * se_nres S /\ al_parr AL + 8 * se_nres S + K_PARR_STEP <= vhi e)
     /\ 0 < al_parr AL + 8 * se_nres S /\ al_parr AL + 8 * se_nres S + K_PARR_STEP <= alloc_ceiling
     /\ (al_parr AL + 8 * se_nres S + K_PARR_STEP <= 0x10000 \/ 0x609000 <= al_parr AL + 8 * se_nres S)
     /\ (al_parr AL + 8 * se_nres S + K_PARR_STEP <= 0x7fff7000 \/ 0x10007fff8000 <= al_parr AL + 8 * se_nres S)) ->
  (forall a mo', chunk_sane (a, n) -> a + n <= alloc_ceiling -> LINK Bs (va_sec_alloc v S a n) mo' ->
                 m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok a) mo') ->
  stwfL (sec_alloc_tree AL S size avoid) mo Q.
Proof.
  intros v mo S size avoid Q LK n Hn Hav VR GR PA HQ. unfold sec_alloc_tree.
  apply stwf_ebind.
  apply (link_anon Bs v mo (sec_msize size) avoid _ BO LK Hn Hav); [fold n; unfold vroom in *; unfold parr_step_cost in *; lia| exact GR|].
  intros a mo1 CS CE LK1 [F1 F2]. fold n in CS, CE, LK1.
  apply stwf_ebind. destruct (Z.eqb_spec (se_n S) (se_nres S)) as [EQ|NE].
  - destruct (PA EQ) as (INE & P0 & PC & PI & PB).
    assert (EL : lenZ K_PARR_STEP = K_PARR_STEP) by (apply lenZ_id; [lia| reflexivity]).
    apply (link_commit_aux Bs _ mo1 (al_parr AL + 8 * se_nres S) K_PARR_STEP _ LK1); rewrite ?EL; try assumption; try lia.
    +
      destruct CS as (C1 & C2 & _). cbn [fst snd] in C1, C2. pose proof (hull_bytes_bound a n ltac:(lia) ltac:(lia)) as HB.
      rewrite parr_step_cost_eq. unfold vroom in *. cbn [va_prim va_chunks va_nsec va_aux chunks_weight fold_right fst snd]. fold (chunks_weight (va_chunks v)).
      unfold parr_step_cost, page_size in *. lia.
    + intros mo2 LK2 [G1 G2]. apply stwf_ret. apply stwf_ret. apply HQ; [exact CS| exact CE| | split; congruence].
      unfold va_sec_alloc. rewrite (proj2 (Z.eqb_eq _ _) EQ). cbn [va_prim va_chunks va_nsec va_aux] in LK2. rewrite ?EL, parr_step_cost_eq in LK2. exact LK2.
  - apply stwf_ret. apply stwf_ret. apply HQ; [exact CS| exact CE| | split; assumption].
    unfold va_sec_alloc. rewrite (proj2 (Z.eqb_neq _ _) NE). rewrite Z.add_0_r. exact LK1.
Qed.
End S.
