(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp MallocKit_A2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS MallocKit_A3 ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0.ASlot_W3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0.ASlot_W5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0.ASlot_W6. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_AB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp MallocKit_A2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_AB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp MallocKit_A2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_AB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp MallocKit_A2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_AB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ CTX <= a < CTX + 928
  \/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
  taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
  taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
               gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
  taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
               gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
  taf_bnc : forall i, 0 <= bounces st i < 256
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gmf_geom st st1 sc g : ta_rel sc st st1 -> gmf st sc g ->
  meta_slot st1 g /\ 0 <= m_avail (get_meta_rec st1 g) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 g) < 2^32
  /\ mw_ok (get_meta_rec st1 g)
  /\ m_mem (get_meta_rec st1 g) = m_mem (get_meta_rec st g)
  /\ m_last_idx (get_meta_rec st1 g) = m_last_idx (get_meta_rec st g)
  /\ m_sizeclass (get_meta_rec st1 g) = m_sizeclass (get_meta_rec st g)
  /\ m_freeable (get_meta_rec st1 g) = m_freeable (get_meta_rec st g)
  /\ conc st1 g = conc st g.
Proof.
  intros TR GM. cps_destruct (tr_geom _ _ _ TR g) as (E1 & E2 & E3 & E4 & E5).
  destruct (tr_mrange _ _ _ TR g (gmf_avail _ _ _ GM) (gmf_freed _ _ _ GM)) as [RA RF].
  pose proof (gmf_mw _ _ _ GM) as MW. unfold mw_ok in *. rewrite E2, E3, E4, E5.
  split; [eapply meta_slot_same_areas; [apply (tr_areas _ _ _ TR)| apply (gmf_slot _ _ _ GM)]|].
  repeat (split; [first [assumption| lia| reflexivity]|]).
  unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma disjoint_high W A n : (forall lo hi, In (lo, hi) W -> hi <= alloc_ceiling) -> alloc_ceiling <= A -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros HW HA; cbn; [exact I|].
  split; [pose proof (HW lo hi ltac:(left; reflexivity)); lia|]. apply IH; [|exact HA]. intros lo' hi' Hin. apply (HW lo' hi'). right. exact Hin.
Qed.


(* [comment removed for export] *)
Lemma decay_cases c st : decay_bounces c st = st \/ exists v, decay_bounces c st = set_bounce (c - 7) v st.
Proof. unfold decay_bounces. destruct (_ && _); [right; eexists; reflexivity| left; reflexivity]. Qed.
Lemma active_decay c st i : active (decay_bounces c st) i = active st i.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma rec_decay c st q : get_meta_rec (decay_bounces c st) q = get_meta_rec st q.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma active_upd_meta g f st i : active (upd_meta g f st) i = active st i.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Hypothesis HK1 : forall stX g3 msk k m' (t1' t3' t4' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
  mrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv asegs m' -> stk asegs m' lo spv ->
  pres_except (ta_fp st lo spv) m m' ->
  implT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (wz k) a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
        F (ret_pc ra) fc None m' (seg_rom asegs)).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End PHASE.

End ACeilS1.
