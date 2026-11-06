(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint PHI (L : list (Z * Z)) : Z :=
  match L with [] => 0 | b :: r => snd b + MBLK + PHI r end.

Lemma PHI_app : forall L1 L2, PHI (L1 ++ L2) = PHI L1 + PHI L2.
Proof. induction L1 as [|b r IH]; intros L2; cbn; [reflexivity | rewrite IH; lia]. Qed.

Lemma PHI_nonneg : forall L, (forall b, In b L -> 0 <= snd b) -> 0 <= PHI L.
Proof.
  induction L as [|b r IH]; intros H; cbn; [lia|].
  pose proof (H b ltac:(left; reflexivity)). assert (0 <= PHI r) by (apply IH; intros; apply H; right; assumption). unfold MBLK. lia.
Qed.

(* [comment removed for export] *)
Definition MH_GBUDGET : Z := 3 * 2 ^ 32.          (* [comment removed for export] *)
Definition VMLIM : Z := MH_GBUDGET + MBASE + 2 ^ 21.
Definition MH_NMAX : Z := 2 ^ 40.                 (* [comment removed for export] *)
Definition MSTK_M : Z := 1280.                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_blocks (Lc : list (Z * Z)) (z : Z) : Prop := exists b n, In (b, n) Lc /\ b <= z < b + n.
Definition in_wins (Wl : list (Z * Z)) (z : Z) : Prop := exists lo hi, In (lo, hi) Wl /\ lo <= z < hi.

Section Defs.
  Context {RN : run_ceil}.

  (* [comment removed for export] *)
  Definition blk_ok (p n : Z) : Prop := HEAPLO + 16 <= p /\ p + n <= CEIL /\ (p + n <= IMG_LO \/ IMG_HI <= p).

  (* [comment removed for export] *)
  Definition mh_changed (stk : Z) (Lc : list (Z * Z)) (sp : Z) (a : word) : Prop :=
    (HEAPLO <= bv_unsigned a < CEIL /\ (bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a) /\ ~ in_blocks Lc (bv_unsigned a))
    \/ (sp - stk <= bv_unsigned a < sp)
    \/ (CTX <= bv_unsigned a < CTX_END) \/ (A_ERRNO <= bv_unsigned a < A_ERRNO + 4).

  Definition AINV (L : list (Z * Z)) (B C : Z) (M : mem) (mdl : Model) : Prop :=
    MInv L M (m_vmmaps mdl) /\ PHI L <= B /\ Z.of_nat (length L) <= C /\ VMLIM <= vm_limit (m_vmmaps mdl).

  Definition AINVF (L : list (Z * Z)) (B C : Z) (M : mem) (mdl : Model) : Prop :=
    MInvF L M (m_vmmaps mdl) /\ PHI L <= B /\ Z.of_nat (length L) <= C /\ VMLIM <= vm_limit (m_vmmaps mdl).

  Lemma AINVF_AINV : forall L B C M mdl, AINVF L B C M mdl -> AINV L B C M mdl.
  Proof. intros L B C M mdl (H & X). split; [exact (MInvF_MInv L M _ H) | exact X]. Qed.

  (* [comment removed for export] *)
  Definition lone (st : mst) (g : Z) : Prop :=
    g_lastidx st g = 0 /\ s_kind st g = GTop /\ 0 < g_maplen st g /\
    (48 <= g_sc st g \/ g_stride st g < UNIT * size_class (g_sc st g)) /\
    exists p n off res, s_slot st g 0 = SUser p n off res.

  (* [comment removed for export] *)
  Definition MInvR (L : list (Z * Z)) (M : mem) (vm : VmMaps) : Prop :=
    exists st, WF st L /\ REP st M /\ LEDGER st vm /\ nojunk st /\ nolimbo st /\ (forall g, is_group st g -> lone st g).

  Definition AINV_R (L : list (Z * Z)) (B C : Z) (M : mem) (mdl : Model) : Prop :=
    MInvR L M (m_vmmaps mdl) /\ PHI L <= B /\ Z.of_nat (length L) <= C /\ VMLIM <= vm_limit (m_vmmaps mdl).

  (* [comment removed for export] *)
  Lemma lone_full : forall st L g, WF st L -> is_group st g -> lone st g ->
    mr_avail (s_meta st g) = 0 /\ mr_freed (s_meta st g) = 0.
  Proof.
    intros st L g HWF Hg (HL & _ & _ & _ & p & n & off & res & HS).
    pose proof (wG_each st L (proj1 (proj2 (proj2 (proj2 HWF)))) g Hg) as WG.
    pose proof (wg_avr st L g WG) as RA. pose proof (wg_frr st L g WG) as RF.
    assert (ZB : forall v, 0 <= v -> (forall i, 0 <= i -> Z.testbit v i = false) -> v = 0).
    { intros v Hv Hb. apply Z.bits_inj_0. intros i. destruct (Z.lt_ge_cases i 0) as [Hi|Hi].
      - apply Z.testbit_neg_r. exact Hi.
      - apply Hb. exact Hi. }
    split.
    - apply ZB; [lia|]. intros i Hi. destruct (Z.testbit (mr_avail (s_meta st g)) i) eqn:T; [|reflexivity]. exfalso.
      destruct (proj1 (wg_av st L g WG i Hi) T) as [Hle E].
      assert (i = 0) by (unfold g_lastidx in *; lia). subst i. rewrite HS in E. discriminate E.
    - apply ZB; [lia|]. intros i Hi. destruct (Z.testbit (mr_freed (s_meta st g)) i) eqn:T; [|reflexivity]. exfalso.
      destruct (proj1 (wg_fr st L g WG i Hi) T) as [Hle E].
      assert (i = 0) by (unfold g_lastidx in *; lia). subst i. rewrite HS in E. discriminate E.
  Qed.

  Lemma MInvR_MInvF : forall L M vm, MInvR L M vm -> MInvF L M vm.
  Proof.
    intros L M vm (st & W & R & Lg & NJ & NL & LO). exists st.
    refine (conj W (conj R (conj Lg (conj NJ (conj NL _))))).
    intros g Hg. exact (lone_full st L g W Hg (LO g Hg)).
  Qed.

  Lemma AINV_R_AINVF : forall L B C M mdl, AINV_R L B C M mdl -> AINVF L B C M mdl.
  Proof. intros L B C M mdl (H & X). split; [exact (MInvR_MInvF L M _ H) | exact X]. Qed.

  Lemma AINV_R_AINV : forall L B C M mdl, AINV_R L B C M mdl -> AINV L B C M mdl.
  Proof. intros L B C M mdl H. apply AINVF_AINV, AINV_R_AINVF, H. Qed.

End Defs.
