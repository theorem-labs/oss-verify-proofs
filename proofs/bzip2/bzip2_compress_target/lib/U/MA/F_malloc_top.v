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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A Malloc_iface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require AllocSlot_iface F_malloc_join F_malloc_small F_malloc_entry F_malloc_core.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.F_malloc_enf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.AllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_small OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_core.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma follow_steq {R} (t1 t2 : Malloc.M R) : steq t1 t2 -> forall ans, follow t1 ans = follow t2 ans.
Proof.
  induction 1 as [r | e k1 k2 Hk IH]; intros ans; [reflexivity|].
  cbn. destruct e; try reflexivity; destruct ans; try reflexivity; apply IH.
Qed.

Lemma follow_sbind {R S} (t : Malloc.M R) (f : R -> Malloc.M S) :
  forall ans x y, follow t ans = Some x ->
  (forall ans', follow (f x) ans' = Some y) ->
  follow (sbind t f) ans = Some y.
Proof.
  induction t as [r | e k IH]; intros ans x y H Hf.
  - cbn in H. inversion H; subst. rewrite sbind_ret_l. apply Hf.
  - rewrite sbind_vis. cbn in H |- *. destruct e; try discriminate; destruct ans as [|a ans]; try discriminate; eapply IH; eauto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mrun_enframe_full o st g b idx n ctr :
  m_mem (get_meta_rec st g) = Some b ->
  let stride := get_stride (get_meta_rec st g) in
  let off := fold_off (if rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) =? 0 then Z.land ctr 255
                       else Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2)
                                    + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
                      ((stride - IB - n) / UNIT) in
  mrun o (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p)))
  = SRet (o, (havoc (snd (enframe_at st g idx n off)) n (fst (enframe_at st g idx n off)), Some (snd (enframe_at st g idx n off)))).
Proof.
  intros Hmem stride off. unfold mrun, enframe_full, enframe_read_off.
  assert (Hp0 : slot_start' (get_meta_rec st g) idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd]. fold stride.
  rewrite (rd8_oracle pans_mem pans_mem_range).
  assert (OFFa : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = 0 -> fold_off (Z.land ctr 255) ((stride - IB - n) / UNIT) = off).
  { intros E0. subst off. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
  assert (OFFb : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) <> 0 ->
     fold_off (Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
              ((stride - IB - n) / UNIT) = off).
  { intros E0. subst off. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
  clearbody off.
  destruct (Z.eqb_spec (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3)) 0) as [E|NE]; cbn [negb].
  - rewrite (OFFa E). rewrite surj_pair_let. reflexivity.
  - rewrite (rd16_oracle pans_mem pans_mem_range). unfold aadd. cbn [fst snd].
    rewrite (OFFb NE). rewrite surj_pair_let. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strip_eq_proj a b : strip a = strip b ->
  s_ctx a = s_ctx b /\ s_regions a = s_regions b /\ s_next_rid a = s_next_rid b /\ s_metas a = s_metas b
  /\ s_areas a = s_areas b /\ s_groups a = s_groups b /\ s_slots a = s_slots b /\ s_reserved a = s_reserved b.
Proof.
  intros E.
  pose proof (f_equal s_ctx E) as E1. pose proof (f_equal s_regions E) as E2. pose proof (f_equal s_next_rid E) as E3.
  pose proof (f_equal s_metas E) as E4. pose proof (f_equal s_areas E) as E5. pose proof (f_equal s_groups E) as E6.
  pose proof (f_equal s_slots E) as E7. pose proof (f_equal s_reserved E) as E8.
  cbn in E1, E2, E3, E4, E5, E6, E7, E8. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma mrun_fst {R} (t : Malloc.M R) : forall o ans o1 x, follow (mrun o t) ans = Some (o1, x) -> o1 = o.
Proof.
  unfold mrun, prun. induction t as [r | e k IH]; intros o ans o1 x H.
  - cbn in H. inversion H. reflexivity.
  - cbn [eruns] in H. destruct (psel pans_mem o e) as [a|] eqn:P.
    + unfold pupd_mem in H. eapply IH. exact H.
    + cbn in H. destruct e; try discriminate; destruct ans; try discriminate; unfold pupd_mem in H; eapply IH; exact H.
Qed.

Lemma mod16_slot (B s st k off : Z) : B mod 4096 = 0 -> s mod 16 = 0 -> st mod 16 = 0 -> 0 <= k ->
  (B + s + 16 + st * k + 16 * off) mod 16 = 0.
Proof.
  intros HB HS HT HK.
  destruct (Z.mod_divide st 16 ltac:(lia)) as [D _]. destruct (D HT) as [q Hq].
  assert (E : st * k = 16 * (q * k)) by (rewrite Hq; ring).
  set (w := q * k) in E. clearbody w. rewrite E. Z.div_mod_to_equations. lia.
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis BIG : big_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End TOPLEVEL.

End ACeilS1.
