(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import Malloc_fp F_malloc_enf AllocSlot_iface F_malloc_join F_malloc_small F_malloc_entry F_malloc_core.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require MallocFacts_inv2.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

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

Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 -> forall ans r1 r2, follow t1 ans = Some r1 -> follow t2 ans = Some r2 -> RR r1 r2.
Proof.
  induction 1 as [a b Hab | e k1 k2 Hk IH]; intros ans r1 r2 F1 F2.
  - cbn in F1, F2. inversion F1; inversion F2; subst. exact Hab.
  - cbn in F1, F2. destruct e; try discriminate; destruct ans as [|z ans]; try discriminate; eapply IH; eauto.
Qed.

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
End TOPLEVEL.