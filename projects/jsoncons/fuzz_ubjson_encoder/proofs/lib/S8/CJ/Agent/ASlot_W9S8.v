(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import TacS8 ImageS8 ZBridgeS8 SysStepS8 SFModelS8 ITreeS8 NodesS8 DecodeS8 ArrS8.

From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import F_syscallsS8 MallocRepS8 F_malloc_freeS8 F_malloc_fastS8 F_malloc_enframeS8 MallocTreeS8 MallocKit_AS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import MallocKit_ABS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MonadS8 ProgS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import Malloc_fpS8 MallocKit_A2S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import MallocNatS8 MallocFacts_ASS8 MallocKit_A3S8 ASlot_W0S8 ASlot_W1S8 ASlot_W2S8 ASlot_W3S8 ASlot_W4S8 ASlot_W5S8 ASlot_W6S8 ASlot_W7S8 ASlot_W8S8.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Record gmf (st : mstate) (sc : Z) (g : aptr) : Prop := mkGMF {
  gmf_slot : meta_slot st g;
  gmf_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  gmf_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  gmf_mw : mw_ok (get_meta_rec st g);
  gmf_sc48 : m_sizeclass (get_meta_rec st g) < 48;
  gmf_cls : m_sizeclass (get_meta_rec st g) = sc;
  gmf_grp : exists b gh, m_mem (get_meta_rec st g) = Some b /\ (s_groups st) !! b = Some gh /\ g_meta gh = Some g
             /\ 0 <= g_active_idx gh <= m_last_idx (get_meta_rec st g)
             /\ (m_sizeclass (get_meta_rec st g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec st g))
             /\ (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h);
  gmf_fbits : forall i, 0 <= i -> Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_abits : forall i, 0 <= i -> Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_links : exists n p, m_next (get_meta_rec st g) = Some n /\ m_prev (get_meta_rec st g) = Some p
}.

Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
  taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
  taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
               gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
  taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
               gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
  taf_bnc : forall i, 0 <= bounces st i < 256
}.

Lemma gmf_geom st st1 sc g : ta_rel sc st st1 -> gmf st sc g ->
  meta_slot st1 g /\ 0 <= m_avail (get_meta_rec st1 g) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 g) < 2^32
  /\ mw_ok (get_meta_rec st1 g)
  /\ m_mem (get_meta_rec st1 g) = m_mem (get_meta_rec st g)
  /\ m_last_idx (get_meta_rec st1 g) = m_last_idx (get_meta_rec st g)
  /\ m_sizeclass (get_meta_rec st1 g) = m_sizeclass (get_meta_rec st g)
  /\ m_freeable (get_meta_rec st1 g) = m_freeable (get_meta_rec st g)
  /\ conc st1 g = conc st g.
Proof.
  intros TR GM. destruct (tr_geom _ _ _ TR g) as (E1 & E2 & E3 & E4 & E5).
  destruct (tr_mrange _ _ _ TR g (gmf_avail _ _ _ GM) (gmf_freed _ _ _ GM)) as [RA RF].
  pose proof (gmf_mw _ _ _ GM) as MW. unfold mw_ok in *. rewrite E2, E3, E4, E5.
  split; [eapply meta_slot_same_areas; [apply (tr_areas _ _ _ TR)| apply (gmf_slot _ _ _ GM)]|].
  repeat (split; [first [assumption| lia| reflexivity]|]).
  unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity.
Qed.

Lemma disjoint_high W A n : (forall lo hi, In (lo, hi) W -> hi <= alloc_ceiling) -> alloc_ceiling <= A -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros HW HA; cbn; [exact I|].
  split; [pose proof (HW lo hi ltac:(left; reflexivity)); lia|]. apply IH; [|exact HA]. intros lo' hi' Hin. apply (HW lo' hi'). right. exact Hin.
Qed.

Lemma decay_cases c st : decay_bounces c st = st \/ exists v, decay_bounces c st = set_bounce (c - 7) v st.
Proof. unfold decay_bounces. destruct (_ && _); [right; eexists; reflexivity| left; reflexivity]. Qed.
Lemma active_decay c st i : active (decay_bounces c st) i = active st i.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma rec_decay c st q : get_meta_rec (decay_bounces c st) q = get_meta_rec st q.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma active_upd_meta g f st i : active (upd_meta g f st) i = active st i.
Proof. reflexivity. Qed.

Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
Variables (ra sp gp tp t0 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Let spv := bv_unsigned sp.

Definition nclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

End PHASE.
End CEIL_WRAP_1.

