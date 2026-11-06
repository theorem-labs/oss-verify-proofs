(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_tables MallocInv_steps MallocInv_hints MallocInv_sc.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TabReads.
  Context {R : Type}.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Lemma ts_lbu_small_cnt : forall s j (k : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 0 <= j < 27 ->
    tsafe (k (Z_to_bv 64 (small_cnt j)) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 (T_SMALL_CNT + j)) ;; k x) s) P.
  Proof.
    intros s j k P Hc HWn Hj Hk.
    destruct (read_small_cnt (ms_mem s) j Hc Hj) as (b & Hrd & Hval).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | pose proof layout_tabs; lia | lia | pose proof layout_tabs; llia] | exact Hrd |].
    rewrite Hval. exact Hk.
  Qed.

  Lemma ts_lbu_med_cnt : forall s j (k : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 0 <= j < 4 ->
    tsafe (k (Z_to_bv 64 (med_cnt j)) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 (T_MED_CNT + j)) ;; k x) s) P.
  Proof.
    intros s j k P Hc HWn Hj Hk.
    destruct (read_med_cnt (ms_mem s) j Hc Hj) as (b & Hrd & Hval).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | pose proof layout_tabs; lia | lia | pose proof layout_tabs; llia] | exact Hrd |].
    rewrite Hval. exact Hk.
  Qed.
End TabReads.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition halveW (usage : word) : nat -> word -> word :=
  fix halve (k : nat) (a3 : word) : word :=
    match k with O => a3 | S k' =>
      if negb (is0 (v_andi a3 1)) then a3
      else if negb (c_ltu usage (v_slliw a3 2)) then a3
      else halve k' (v_srliw a3 1)
    end.

Definition shrinkW (size : word) : nat -> word -> word :=
  fix shrink (k : nat) (a2 : word) : word :=
    match k with O => a2 | S k' =>
      if is0 (v_srli (v_mul size a2) 20) then a2
      else shrink k' (v_srliw a2 1)
    end.

Definition m_cnt (sc usage size : word) : M word :=
  if negb (c_lts (wlit 8) sc)
  then let tb := v_add A_SMALL_CNT_TAB (v_add (v_slli sc 1) sc) in
       t0 <- m_lbu tb ;;
       if negb (c_ltu usage (v_slli t0 2)) then mret t0
       else t1 <- m_lbu (at_ tb 1) ;;
            if negb (c_ltu usage (v_slli t1 2)) then mret t1
            else m_lbu (at_ tb 2)
  else t <- m_lbu (v_add A_MED_CNT_TAB (v_andi sc 3)) ;;
       let c0 := halveW usage 8%nat t in
       mret (shrinkW size 40%nat c0).

Lemma halveW_S : forall u k a,
  halveW u (S k) a = (if negb (is0 (v_andi a 1)) then a
                     else if negb (c_ltu u (v_slliw a 2)) then a
                     else halveW u k (v_srliw a 1)).
Proof. intros. reflexivity. Qed.

Lemma shrinkW_S : forall sz k a,
  shrinkW sz (S k) a = (if is0 (v_srli (v_mul sz a) 20) then a else shrinkW sz k (v_srliw a 1)).
Proof. intros. reflexivity. Qed.

Lemma srliw1_small : forall c, 0 <= c <= 32 -> v_srliw (Z_to_bv 64 c) 1 = Z_to_bv 64 (c / 2).
Proof.
  intros c Hc. rewrite v_srliw_Z by llia. rewrite Z.mod_small by llia. change (2^1) with 2.
  rewrite swrap32_small by llia. reflexivity.
Qed.

Lemma halveW_in : forall u k c, 0 <= c <= 32 ->
  exists c', In c' (halvings k c) /\ halveW u k (Z_to_bv 64 c) = Z_to_bv 64 c' /\ 0 <= c' <= 32.
Proof.
  intros u k. induction k as [|k IH]; intros c Hc.
  - exists c. cbn. auto.
  - rewrite halveW_S. cbn [halvings].
    rewrite v_andi_Z by llia. change 1 with (2^1 - 1) at 1. rewrite land_ones_low by llia. change (2^1) with 2.
    pose proof (Z.mod_pos_bound c 2 ltac:(llia)). rewrite is0_Z by llia.
    rewrite Zmod_odd. rewrite <- Z.negb_even.
    destruct (Z.even c) eqn:Ev; cbn [negb Z.eqb].
    + destruct (negb (c_ltu u (v_slliw (Z_to_bv 64 c) 2))).
      * exists c. split; [left; reflexivity | auto].
      * rewrite srliw1_small by llia. destruct (IH (c / 2) ltac:(llia)) as (c' & Hin & E & Hr).
        exists c'. split; [right; exact Hin | auto].
    + exists c. split; [left; reflexivity | auto].
Qed.

Lemma shrinkW_eq : forall szc k c, 0 <= c <= 32 -> 1 <= szc <= 8191 ->
  shrinkW (Z_to_bv 64 (16 * szc)) k (Z_to_bv 64 c) = Z_to_bv 64 (shrink k (16 * szc) c) /\
  0 <= shrink k (16 * szc) c <= 32.
Proof.
  intros szc k. induction k as [|k IH]; intros c Hc Hs.
  - cbn. auto.
  - rewrite shrinkW_S. cbn [shrink].
    rewrite v_mul_Z. rewrite v_srli_Z by lnia.
    rewrite is0_Z.
    2:{ split; [apply Z.div_pos; lnia|]. apply Z.div_lt_upper_bound; [llia|]. lnia. }
    replace (16 * szc * c / 2^20 =? 0) with (16 * szc * c <? 2^20).
    2:{ destruct (16 * szc * c <? 2^20) eqn:E; symmetry.
        - apply Z.ltb_lt in E. apply Z.eqb_eq. apply Z.div_small. lnia.
        - apply Z.ltb_ge in E. apply Z.eqb_neq. intros X.
          pose proof (Z.div_str_pos (16 * szc * c) (2^20) ltac:(lnia)). llia. }
    destruct (16 * szc * c <? 2^20); [auto|].
    rewrite srliw1_small by llia. apply IH; llia.
Qed.

Definition inb (c : Z) (l : list Z) : bool := existsb (Z.eqb c) l.

Lemma inb_In : forall c l, inb c l = true -> In c l.
Proof.
  intros c l H. unfold inb in H. apply existsb_exists in H. destruct H as (x & Hx & E). apply Z.eqb_eq in E. subst x. exact Hx.
Qed.

Definition chk_small_in (sc : Z) : bool :=
  inb (small_cnt (3 * sc)) (cnt_cands sc) && inb (small_cnt (3 * sc + 1)) (cnt_cands sc) && inb (small_cnt (3 * sc + 2)) (cnt_cands sc)
  && (small_cnt (3 * sc) <=? 32) && (small_cnt (3 * sc + 1) <=? 32) && (small_cnt (3 * sc + 2) <=? 32).
Lemma chk_small_ins : forallb chk_small_in (Zseq 0 9) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma small_in : forall sc, 0 <= sc < 9 ->
  In (small_cnt (3 * sc)) (cnt_cands sc) /\ In (small_cnt (3 * sc + 1)) (cnt_cands sc) /\ In (small_cnt (3 * sc + 2)) (cnt_cands sc) /\
  small_cnt (3 * sc) <= 32 /\ small_cnt (3 * sc + 1) <= 32 /\ small_cnt (3 * sc + 2) <= 32.
Proof.
  intros sc Hsc.
  pose proof (proj1 (forallb_forall _ _) chk_small_ins sc (Zseq_In 9 0 sc ltac:(llia))) as H.
  unfold chk_small_in in H. repeat (apply andb_prop in H; destruct H as [H ?X]).
  repeat match goal with G : (_ <=? _) = true |- _ => apply Z.leb_le in G | G : inb _ _ = true |- _ => apply inb_In in G end.
  repeat split; assumption.
Qed.

Lemma med_cnt_range : forall j, 0 <= j < 4 -> 20 <= med_cnt j <= 32.
Proof.
  intros j Hj.
  assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by llia.
  destruct H as [-> | [-> | [-> | ->]]];
    [change (med_cnt 0) with 28 | change (med_cnt 1) with 24 | change (med_cnt 2) with 20 | change (med_cnt 3) with 32]; llia.
Qed.

Lemma small_cnt_nonneg : forall j, 0 <= small_cnt j.
Proof.
  intros j. unfold small_cnt.
  assert (G : forall l n, Forall (fun x => 0 <= x) l -> 0 <= nth n l 0).
  { intros l n HF. revert n. induction HF; intros [|n]; cbn; try llia; apply IHHF. }
  apply G. unfold small_cnt_tab. repeat constructor; llia.
Qed.

Lemma cnt_cands_range : forall sc c, 0 <= sc < 48 -> In c (cnt_cands sc) -> 1 <= c <= 32.
Proof.
  intros sc c Hsc Hc.
  pose proof (proj1 (forallb_forall _ _) chk_cnt_ranges sc (Zseq_In 48 0 sc ltac:(llia))) as H.
  unfold chk_cnt_range in H. apply (proj1 (forallb_forall _ _)) with (x := c) in H; [| exact Hc].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. llia.
Qed.

Section Cnt.
  Context {R : Type}.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Theorem ts_alloc_cnt : forall s (sc : Z) (usage : word) (k : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 0 <= sc < 48 ->
    (forall c, In c (cnt_cands sc) -> 1 <= c <= 32 -> tsafe (k (Z_to_bv 64 c) s) P) ->
    tsafe ((x <- m_cnt (Z_to_bv 64 sc) usage (v_slli (Z_to_bv 64 (size_class sc)) 4) ;; k x) s) P.
  Proof.
    intros s sc usage k P HRO HWIN Hsc Hk.
    assert (Hk' : forall c, In c (cnt_cands sc) -> tsafe (k (Z_to_bv 64 c) s) P).
    { intros c Hc. apply Hk; [exact Hc | exact (cnt_cands_range sc c Hsc Hc)]. }
    unfold m_cnt. unfold wlit. rewrite c_lts_Z by llia.
    destruct (8 <? sc) eqn:E8; cbn [negb].
    - (* [comment removed for export] *)
      apply Z.ltb_lt in E8. reassoc.
      rewrite v_andi_Z by llia. change 3 with (2^2 - 1) at 1. rewrite land_ones_low by llia. change (2^2) with 4.
      pose proof (Z.mod_pos_bound sc 4 ltac:(llia)) as Hm4.
      rewrite A_MED_CNT_TAB_eq, v_add_Z.
      eapply ts_lbu_med_cnt; [exact HRO | exact HWIN | llia |].
      pose proof (med_cnt_range (sc mod 4) Hm4) as Hmr.
      apply ts_bind_ret.
      destruct (halveW_in usage 8 (med_cnt (sc mod 4)) ltac:(llia)) as (c1 & Hin1 & E1 & Hr1).
      rewrite E1.
      pose proof (size_class_bound sc Hsc) as Hszc.
      rewrite v_slli_Z by llia. replace (size_class sc * 2^4) with (16 * size_class sc) by llia.
      destruct (shrinkW_eq (size_class sc) 40 c1 Hr1 Hszc) as [E2 _]. rewrite E2.
      apply Hk'. unfold cnt_cands, cnt_base.
      replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; llia).
      apply in_map_iff. exists c1. split; [reflexivity|].
      replace (Z.land sc 3) with (sc mod 4); [exact Hin1|].
      change 3 with (2^2 - 1). rewrite land_ones_low by llia. reflexivity.
    - (* [comment removed for export] *)
      apply Z.ltb_ge in E8.
      destruct (small_in sc ltac:(llia)) as (I0 & I1 & I2 & B0 & B1 & B2).
      pose proof (small_cnt_nonneg (3 * sc)). pose proof (small_cnt_nonneg (3 * sc + 1)). pose proof (small_cnt_nonneg (3 * sc + 2)).
      rewrite A_SMALL_CNT_TAB_eq. rewrite v_slli_Z by llia. rewrite !v_add_Z. change (2^1) with 2.
      replace (T_SMALL_CNT + (sc * 2 + sc)) with (T_SMALL_CNT + 3 * sc) by llia.
      reassoc. eapply ts_lbu_small_cnt; [exact HRO | exact HWIN | llia |].
      destruct (negb (c_ltu usage (v_slli (Z_to_bv 64 (small_cnt (3 * sc))) 2))).
      { apply ts_bind_ret. apply Hk'. exact I0. }
      reassoc; rewrite at_Z. replace (T_SMALL_CNT + 3 * sc + 1) with (T_SMALL_CNT + (3 * sc + 1)) by llia.
      eapply ts_lbu_small_cnt; [exact HRO | exact HWIN | llia |].
      destruct (negb (c_ltu usage (v_slli (Z_to_bv 64 (small_cnt (3 * sc + 1))) 2))).
      { apply ts_bind_ret. apply Hk'. exact I1. }
      rewrite at_Z. replace (T_SMALL_CNT + 3 * sc + 2) with (T_SMALL_CNT + (3 * sc + 2)) by llia.
      eapply ts_lbu_small_cnt; [exact HRO | exact HWIN | llia |].
      apply Hk'. exact I2.
  Qed.
End Cnt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition span_args (a szc : Z) : word * word * word * word :=
  let a5 := Z_to_bv 64 a in
  let szcw := Z_to_bv 64 szc in
  let a6 := v_addi a5 2 in
  let a4 := v_addi a5 1 in
  let t0 := v_addi (v_slli a5 4) 48 in
  let size := v_slli szcw 4 in
  let a7 := v_mul t0 szcw in
  let t0' := v_mul size a6 in
  let a6' := v_addiw a7 15 in
  let t0'' := v_addiw t0' 16 in
  (a6', t0'', a4, size).

Definition span_run (a sc : Z) : option word :=
  let '(a6', t0'', a4, size) := span_args a (size_class sc) in m_span_loop 40 a6' t0'' a4 size.

Definition span_cnt (a sc : Z) : Z :=
  match span_run a sc with Some w => U w | None => 0 end.

Definition chk_span (sc : Z) : bool :=
  forallb (fun a => match span_run a sc with Some _ => true | None => false end
                    && (a + 2 <=? span_cnt a sc) && (span_cnt a sc <=? a + 42)) (Zseq 0 32).

Lemma chk_spans : forallb chk_span (Zseq 7 41) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma span_ok : forall sc a, 7 <= sc < 48 -> 0 <= a < 32 ->
  span_run a sc = Some (Z_to_bv 64 (span_cnt a sc)) /\ a + 2 <= span_cnt a sc <= a + 42.
Proof.
  intros sc a Hsc Ha.
  pose proof (proj1 (forallb_forall _ _) chk_spans sc (Zseq_In 41 7 sc ltac:(llia))) as H.
  unfold chk_span in H. apply (proj1 (forallb_forall _ _)) with (x := a) in H; [| apply Zseq_In; llia].
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3.
  split; [| llia]. unfold span_cnt in *. destruct (span_run a sc) as [w|]; [| discriminate].
  unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

End WithLayout.
