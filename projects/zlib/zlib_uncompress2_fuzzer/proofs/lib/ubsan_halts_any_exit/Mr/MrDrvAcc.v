(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrTall MrShape MrDrv MrAccPath.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ucost_sbind {R S} (t : M R) (f : R -> M S) C U (P : R -> Z -> Z -> Prop) (Q : S -> Z -> Z -> Prop) :
  ucost t C U P -> (forall r c u, P r c u -> ucost (f r) c u Q) -> ucost (sbind t f) C U Q.
Proof.
  revert C U. induction t as [r | e k IH]; intros C U H Hf; cbn in *; [apply Hf; exact H|].
  destruct e; try exact I; try contradiction.
  - destruct H as [Hl H]. split; [exact Hl|]. intros z. apply IH; [apply H | exact Hf].
  - intros z. apply IH; [apply H | exact Hf].
  - intros z. apply IH; [apply H | exact Hf].
Qed.

Lemma ucost_guard {R} tag c (k bail : M R) C U (P : R -> Z -> Z -> Prop) : ucost k C U P -> ucost (guard tag c k bail) C U P.
Proof. intros H. unfold guard. destruct c; [exact H | exact I]. Qed.

Theorem cmalloc_big_cost d cs a44 fl bl n C U :
  KST d cs a44 fl bl -> 1 <= d -> MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2 ^ 30 - 4096 ->
  ucost (cmalloc cs n) C U (fun _ c u => c <= C + 2 /\ u <= U + (n + IB + UNIT + 4096)).
Proof.
  intros K Hd Hn Hn2. unfold cmalloc. eapply ucost_sbind with (P := fun _ c u => c <= C + 2 /\ u <= U + (n + IB + UNIT + 4096)).
  2:{ intros [st1 r] c u H. exact H. }
  unfold malloc_core. destruct (size_overflows n); [cbn; unfold IB, UNIT, MMAP_THRESHOLD in *; lia|].
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hn).
  cbn [ucost]. split; [unfold IB, UNIT, MMAP_THRESHOLD in *; lia|]. intros z.
  destruct (negb (mmap_answer_ok _ _ _ z)); [exact I|].
  destruct (is_err z); [cbn; split; lia|].
  destruct (new_region RKGroup z (n + IB + UNIT) cs) as [st1 rid] eqn:E.
  assert (Est1 : st1 = fst (new_region RKGroup z (n + IB + UNIT) cs)) by (rewrite E; reflexivity).
  assert (K2 : KST d (step_seq st1) a44 fl bl).
  { eapply KST_weaken_rid; [exact K | | | | | | |]; rewrite Est1; unfold step_seq, new_region; cbn [fst];
      destruct (c_seq _ =? 255); try reflexivity; try (intros sc; reflexivity); cbn; lia. }
  match goal with |- ucost (alloc_meta ?st ?k ?bail) _ _ _ =>
    destruct (alloc_meta_KST d st a44 fl bl k bail K2 Hd) as (g & cs' & EQ & _) end.
  rewrite EQ. cbn [ucost]. split; lia.
Qed.

Lemma ucost_free_group_solo : forall (REC : mstate -> aptr -> Z -> (mstate -> mapinfo -> M mstate) -> M mstate -> M mstate)
    (st cs0 : mstate) (g b : aptr) C U,
  m_mem (get_meta_rec st g) = Some b -> m_last_idx (get_meta_rec st g) = 0 -> m_maplen (get_meta_rec st g) <> 0 ->
  c_free_meta_head (ctx st) = None ->
  ucost (free_group mstate dec_slots REC st g
            (fun st2 mi => match mi with
               | Some (base, len) =>
                   if negb (len =? 0) then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret cs0))
                   else ret st2
               | None => ret st2 end) (ret cs0)) C U (fun _ c u => c <= C /\ u <= U).
Proof.
  intros REC st cs0 g b C U Hmem Hli Hml Hfl. unfold free_group. rewrite Hmem, Hli.
  replace (m_maplen (get_meta_rec st g) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml). cbn [negb].
  unfold free_meta, queue.
  match goal with |- context [put_meta g meta0 ?s3] => set (st3 := s3) end.
  rewrite gmr_put_same. cbn [m_next m_prev meta0 optr_eqb]. unfold guard.
  assert (EH : get_head (put_meta g meta0 st3) LFree = None).
  { subst st3. unfold record_seq, step_seq. destruct (m_sizeclass (get_meta_rec st g) <? 48); destruct (sc_in_seq_range _);
      match goal with |- context [c_seq ?c =? 255] => destruct (c_seq c =? 255) end; exact Hfl. }
  rewrite EH.
  replace (m_maplen (get_meta_rec st g) * 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  cbn [ucost]. intros ru. destruct (munmap_answer_ok ru); [cbn; lia | exact I].
Qed.

Theorem cfree_cost d cs a44 bl g b C U :
  KST d cs a44 None bl -> In (g, b) bl ->
  ucost (cfree cs (Some (aadd b UNIT))) C U (fun _ c u => c <= C /\ u <= U).
Proof.
  intros K Hin. destruct (ks_blk _ _ _ _ _ K g b Hin) as (HS & HRID & HB0 & HREC).
  unfold cfree. rewrite HS.
  eapply ucost_sbind with (P := fun _ c u => c <= C /\ u <= U); [|intros r c u H; exact H].
  assert (SOLO : solo_rec (get_meta_rec cs g) b /\
                 ((m_sizeclass (get_meta_rec cs g) = 63 /\ m_next (get_meta_rec cs g) = None)
                  \/ (m_sizeclass (get_meta_rec cs g) = 44 /\ m_next (get_meta_rec cs g) = Some g /\ a44 = Some g))).
  { destruct HREC as [(HS0 & H63 & HN) | HA].
    - split; [exact HS0|]. left. auto.
    - destruct (ks_a44 _ _ _ _ _ K g HA) as (b0 & Hb0 & (HS0 & H44 & HN & _)).
      assert (b0 = b).
      { pose proof (ks_ndm _ _ _ _ _ K) as ND. cbn [fl_list] in ND. rewrite app_nil_r in ND.
        pose proof (NoDup_map_In_inj fst bl (g, b0) (g, b) ND Hb0 Hin eq_refl) as E. injection E as ->. reflexivity. }
      subst b0. split; [exact HS0|]. right. auto. }
  destruct SOLO as ((Hmem & Hav & Hfr & Hli & Hfa & Hml) & CASE).
  unfold free_tail. rewrite Hfr, Hav, Hli.
  change (negb (testbit (Z.lor 0 0) 0)) with true. unfold guard at 1.
  change (negb ((0 =? 0) || (Z.lor 0 0 + bit 0 =? mask_upto 0))) with false. cbv iota.
  unfold FUEL. change 64%nat with (S 63). rewrite ntf_S. cbv zeta. rewrite Hfr, Hav, Hli.
  change (Z.lor 0 0 + bit 0 =? mask_upto 0) with true.
  rewrite (okay_solo cs g Hfa Hml) by (destruct CASE as [(H & _) | (H & Hn & _)]; [left; exact H | right; split; assumption]).
  cbn [andb].
  destruct CASE as [(H63 & HN) | (H44 & HN & HA)]; rewrite HN.
  - apply (ucost_free_group_solo _ cs cs g b); try assumption. exact (ks_fl _ _ _ _ _ K).
  - rewrite H44. change (44 <? 48) with true. unfold guard at 1.
    rewrite (ks_act _ _ _ _ _ K 44). change (44 =? 44) with true. cbv iota. rewrite HA. cbn [optr_eqb]. rewrite aptr_eqb_refl.
    pose proof (active_dequeue_singleton 44 g cs 44 HN) as AD. change (44 =? 44) with true in AD. cbv iota in AD.
    cbv zeta. rewrite AD.
    set (st1 := dequeue (LActive 44) g cs).
    assert (DQ : st1 = upd_meta g (fun r => m_set_prev None (m_set_next None r)) (set_head (LActive 44) None cs)).
    { subst st1. unfold dequeue. rewrite HN. cbn [optr_eqb]. rewrite aptr_eqb_refl. reflexivity. }
    assert (R1 : get_meta_rec st1 g = m_set_prev None (m_set_next None (get_meta_rec cs g))) by (rewrite DQ, gmr_upd_same; reflexivity).
    apply (ucost_free_group_solo _ st1 cs g b).
    + rewrite R1. exact Hmem.
    + rewrite R1. exact Hli.
    + rewrite R1. exact Hml.
    + rewrite DQ. exact (ks_fl _ _ _ _ _ K).
Qed.
