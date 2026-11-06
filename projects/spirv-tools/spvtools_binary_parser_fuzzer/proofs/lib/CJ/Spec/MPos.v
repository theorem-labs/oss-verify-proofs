(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition posz (e : ev) (z : Z) : Prop :=
  match e with
  | EBrk _ => True
  | EMmap a len prot flags => negb (Z.land flags MAP_FIXED =? 0) = true \/ is_err z = false
  | EMunmap _ _ => z = 0
  | EMprotect _ _ _ => z = 0
  | EPeek _ _ _ => False
  | EUndef _ => False
  end.

Fixpoint pos {R} (D : nat) (t : stree ev Z R) (P : R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k => match D with
                | O => False
                | S D' => forall z, posz e z -> pos D' (k z) P
                end
  end.

Lemma pos_mono {R} (P : R -> Prop) : forall t D D', (D <= D')%nat -> pos D t P -> pos D' t P.
Proof.
  induction t as [r|e k IH]; intros D D' HD H; cbn in *; [exact H|].
  destruct D as [|D]; [destruct H|]. destruct D' as [|D']; [lia|]. intros z Hz. apply (IH z D D'); [lia| exact (H z Hz)].
Qed.

Lemma pos_ret {R} D (r : R) P : P r -> pos D (SRet r) P.
Proof. intros H. destruct D; exact H. Qed.

Lemma pos_undef {R} D u (k : Z -> stree ev Z R) P : pos (S D) (SVis (EUndef u) k) P.
Proof. cbn. intros z []. Qed.

Lemma pos_bad {R} D (bail : stree ev Z R) P : pos (S D) (bad_answer bail) P.
Proof. apply pos_undef. Qed.

Lemma pos_guard {R} D tag c (k bail : stree ev Z R) P : pos (S D) k P -> pos (S D) (guard tag c k bail) P.
Proof. intros H. unfold guard. destruct c; [exact H| apply pos_undef]. Qed.

Lemma pos_S {R} D (t : stree ev Z R) P : pos D t P -> pos (S D) t P.
Proof. intros H. eapply pos_mono; [| exact H]. lia. Qed.

Lemma pos_bind {A R} P (Q : A -> Prop) : forall (t : stree ev Z A) (f : A -> stree ev Z R) D1 D2,
  pos D1 t Q -> (forall a, Q a -> pos D2 (f a) P) -> pos (D1 + D2) (sbind t f) P.
Proof.
  induction t as [r|e k IH]; intros f D1 D2 H Hf; cbn in *.
  - eapply pos_mono; [| apply Hf; exact H]. lia.
  - destruct D1 as [|D1]; [destruct H|]. cbn. intros z Hz. apply IH; [exact (H z Hz)| exact Hf].
Qed.
End AC_1.

Ltac pos_case :=
  lazymatch goal with
  | |- pos _ (match ?x with _ => _ end) _ => destruct x eqn:?
  | |- pos _ (if ?c then _ else _) _ => destruct c eqn:?
  | |- pos _ (let '(_, _) := ?x in _) _ => destruct x eqn:?
  end.
Section AC_2. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Section AM.
Context {R : Type}.
Implicit Types (k : mstate -> optr -> M R) (bail : M R) (P : R -> Prop).

Definition kpos D k P := forall st m, pos D (k st (Some m)) P.

Lemma am_take_pos D st k bail P : kpos (S D) k P -> pos (S D) (am_take st k bail) P.
Proof. intros HK. unfold am_take. pos_case; [apply HK| apply pos_undef]. Qed.

Lemma am_carve_pos D st p k bail P : kpos (S D) k P -> pos (S D) (am_carve st p k bail) P.
Proof. intros HK. unfold am_carve. apply am_take_pos. exact HK. Qed.

Lemma am_finish_pos D st nu k bail P : kpos (S D) k P -> pos (S (S D)) (am_finish st nu k bail) P.
Proof.
  intros HK. unfold am_finish. pos_case; [| apply pos_undef].
  pos_case; [| apply pos_S, am_carve_pos; exact HK].
  cbn [pos]. intros z Hz. cbn in Hz. subst z.
  cbn [mprotect_answer_ok negb Z.eqb orb Z.ltb TWO64 Z.pow Z.compare Pos.compare Z.pow_pos Pos.iter Z.mul Pos.mul Pos.compare_cont].
  apply am_carve_pos. exact HK.
Qed.

Lemma am_after_brk_pos D st nu k bail P : kpos (S D) k P -> pos (S (S (S D))) (am_after_brk st nu k bail) P.
Proof.
  intros HK. unfold am_after_brk. pos_case; [| apply pos_S, am_finish_pos; exact HK].
  cbn - [pos am_finish]. intros z Hz.
  pos_case; [apply pos_bad|]. cbn in Hz. destruct Hz as [Hz|Hz]; [discriminate|]. rewrite Hz.
  apply am_finish_pos. exact HK.
Qed.

Lemma kpos_le D D' k P st m : kpos D k P -> (D <= D')%nat -> pos D' (k st (Some m)) P.
Proof. intros HK HD. eapply pos_mono; [exact HD| apply HK]. Qed.

Lemma alloc_meta_pos D st k bail P : kpos (S D) k P -> pos (6 + D) (alloc_meta st k bail) P.
Proof.
  intros HK. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st). clearbody st0.
  cbn [Nat.add].
  pos_case; [apply (kpos_le (S D)); [exact HK| lia]|].
  pos_case; [apply pos_S, pos_S, pos_S, pos_S, pos_S, am_take_pos; exact HK|].
  pos_case.
  - pos_case.
    +
      cbn [pos]. intros cur _.
      pos_case; [apply pos_bad|]. cbn [pos]. intros r _.
      pos_case; [apply pos_bad|]. pos_case; [apply pos_S, (am_after_brk_pos D); exact HK|].
      pos_case; [apply pos_bad|].
      cbn [pos]. intros rg _.
      pos_case; [apply pos_bad|]. pos_case. apply (am_after_brk_pos D); exact HK.
    +   exfalso. clear -Heqb0. cbn in Heqb0. rewrite andb_false_r in Heqb0. discriminate.
    +
      cbn [pos]. intros r _.
      pos_case; [apply pos_bad|]. pos_case; [apply pos_S, pos_S, (am_after_brk_pos D); exact HK|].
      pos_case; [apply pos_bad|]. apply pos_S, pos_S, (am_after_brk_pos D); exact HK.
  - apply pos_S, pos_S, pos_S, am_after_brk_pos; exact HK.
Qed.
End AM.

Lemma queue_pos {R} D h m st (k : mstate -> M R) bail P : (forall st', pos (S D) (k st') P) -> pos (S D) (queue h m st k bail) P.
Proof. intros HK. unfold queue. apply pos_guard, pos_guard. pos_case; apply HK. Qed.

Lemma ta_fin_pos {R} D st m mask (k : mstate -> Z -> M R) P :
  (forall st' first, pos D (k st' first) P) -> pos D (ta_fin st m mask k) P.
Proof. intros HK. unfold ta_fin. apply HK. Qed.

Lemma activate_group_pos {R} D m st (k : mstate -> Z -> M R) bail P :
  (forall st' x, pos (S D) (k st' x) P) -> pos (S D) (activate_group m st k bail) P.
Proof. intros HK. unfold activate_group. apply pos_guard. apply HK. Qed.

Lemma try_avail_pos {R} D sc st (k : mstate -> Z -> M R) bail P :
  (forall st' first, pos (S D) (k st' first) P) -> pos (S D) (try_avail sc st k bail) P.
Proof.
  intros HK. unfold try_avail. pos_case; [| apply HK].
  pos_case; [apply ta_fin_pos; exact HK|].
  pos_case.
  - pos_case. pos_case. cbv zeta. pos_case. pos_case. apply activate_group_pos. intros st' x. apply pos_guard. apply ta_fin_pos. exact HK.
  - pos_case; [apply HK| apply pos_undef].
Qed.

Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Section SLOT.
Context {R : Type}.
Variable lay : layout_hook.

Definition skpos D (k : mstate -> Z -> M R) P := forall st idx, 0 <= idx -> pos D (k st idx) P.

Definition LVL : nat := 8.

Lemma alloc_group_pos E D (rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req (k : mstate -> optr -> M R) bail P :
  (forall st' j req' k' bail', skpos (S D) k' P -> pos (E + S D) (rec st' j req' k' bail') P) ->
  (forall st' m, pos (S D) (k st' (Some m)) P) ->
  pos (LVL + E + S D) (alloc_group R lay rec st sc req k bail) P.
Proof.
  intros HREC HK. unfold alloc_group. cbv zeta.
  replace (LVL + E + S D)%nat with (6 + S (S (E + S D)))%nat by (unfold LVL; lia).
  apply alloc_meta_pos. intros st1 m. cbv beta zeta.
  pos_case.
  -
    pos_case. cbv zeta. cbn - [pos mmap_answer_ok is_err free_meta new_region upd_meta upd_ctx ag_tail step_seq account_bounce live_ranges Z.add Z.mul Z.sub Z.div Z.shiftr u32 Nat.add].
    intros r Hr. pos_case; [apply pos_bad|]. cbn in Hr. destruct Hr as [Hr|Hr]; [discriminate|]. rewrite Hr.
    pos_case. cbv zeta. unfold ag_tail. eapply pos_mono; [| apply HK]. lia.
  -
    eapply pos_mono; [| apply HREC]; [lia|].
    intros st2 idx Hidx. cbv beta. pos_case; [apply Z.ltb_lt in Heqb0; lia|].
    pos_case; [| apply pos_undef]. cbv zeta. unfold ag_tail. apply HK.
Qed.

Lemma alloc_slot_pos : forall fuel D st sc req (k : mstate -> Z -> M R) bail P,
  skpos (S D) k P ->
  pos (LVL * fuel + S D) (alloc_slot lay fuel st sc req k bail) P.
Proof.
  induction fuel as [|f IH]; intros D st sc req k bail P HK.
  - cbn [alloc_slot]. replace (LVL * 0 + S D)%nat with (S D) by lia. apply pos_undef.
  - cbn [alloc_slot]. replace (LVL * S f + S D)%nat with (S (LVL + LVL * f + D))%nat by lia.
    apply try_avail_pos. intros st1 first.
    pos_case.
    + eapply pos_mono; [| apply HK; apply ctz32_nonneg]. lia.
    + replace (S (LVL + LVL * f + D))%nat with (LVL + LVL * f + S D)%nat by lia. apply (alloc_group_pos (LVL * f) D).
      * intros st' j req' k' bail' HK'. apply IH. exact HK'.
      * intros st' m. cbv beta. apply queue_pos. intros st''. apply HK. lia.
Qed.
End SLOT.

Definition MALLOC_DEPTH : nat := LVL * FUEL + 16.

Lemma malloc_small_pos {R} lay st n (k : mstate -> option (aptr * Z) -> M R) bail P :
  (forall st' g idx, pos 10 (k st' (Some (g, idx))) P) ->
  pos (LVL * FUEL + 10) (malloc_small_ctrl lay st n k bail) P.
Proof.
  intros HK. unfold malloc_small_ctrl.
  set (sc := match active st (size_to_class n) with Some _ => _ | None => _ end). clearbody sc.
  pos_case. 1: pos_case. 1: eapply pos_mono; [| apply HK]; lia.
  all: clear -HK; apply (alloc_slot_pos lay FUEL 9);
       intros st1 idx Hidx; cbv beta; (destruct (idx <? 0) eqn:Hlt; [apply Z.ltb_lt in Hlt; exfalso; lia |]);
       (pos_case; [apply HK| apply pos_undef]).
Qed.

Lemma malloc_core_pos lay st n : size_overflows n = false ->
  pos MALLOC_DEPTH (malloc_core lay st n) (fun r => snd r <> None).
Proof.
  intros Hov. unfold malloc_core. rewrite Hov. unfold MALLOC_DEPTH.
  pos_case.
  -
    replace (LVL * FUEL + 16)%nat with (S (6 + (LVL * FUEL + 9)))%nat by lia.
    cbn [pos]. intros r Hr. pos_case; [apply pos_bad|]. destruct Hr as [Hr|Hr]; [discriminate|]. rewrite Hr.
    pos_case. apply alloc_meta_pos. intros st3 g. cbv beta iota zeta. apply pos_ret. cbn. discriminate.
  - eapply pos_mono; [| apply malloc_small_pos]; [lia|]. intros st' g idx. apply pos_ret. cbn. discriminate.
Qed.

Theorem cmalloc_pos cs n : size_overflows n = false ->
  pos (MALLOC_DEPTH + 0) (cmalloc cs n) (fun r => snd r <> None).
Proof.
  intros Hov. unfold cmalloc. eapply pos_bind; [apply malloc_core_pos; exact Hov|].
  intros [st1 [[g idx]|]] H; apply pos_ret; cbn in *; [discriminate| exfalso; apply H; reflexivity].
Qed.

End AC_2.
