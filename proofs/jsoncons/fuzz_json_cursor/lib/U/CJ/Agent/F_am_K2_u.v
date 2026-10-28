(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocKit_A2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u MallocTree_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocKit_B_u MallocModel_B_u MallocKit_B2_u MallocKit_B3_u F_ntf_B_u.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition clear_range (st : mstate) (lo n : Z) : Prop :=
  forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).

Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof.
  intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).

Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

Lemma gr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma gr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
Lemma gr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
  rewrite gr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
  - rewrite lookup_insert_eq in H. left. split; congruence.
  - rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
Lemma gr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite gr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma gr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rewrite gr_regions, lookup_insert_eq. reflexivity. Qed.
Lemma gr_conc q : conc st' q = conc st q.
Proof.
  unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
  - rewrite E, gr_lookup_new, Hr. reflexivity.
  - rewrite gr_lookup_old by exact NE. reflexivity.
Qed.
Lemma gr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

Lemma ptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End GROW.

Lemma impl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
  impl asegs (at_node asegs) (enode n dec) (epost P) ms ->
  (forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
  impl asegs (at_node asegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof.
  intros H HD. unfold enode in *. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec' rsp) as [a|] eqn:E.
  - destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
  - cbn. apply evt_done. exact I.
Qed.
End CEIL_WRAP_1.

