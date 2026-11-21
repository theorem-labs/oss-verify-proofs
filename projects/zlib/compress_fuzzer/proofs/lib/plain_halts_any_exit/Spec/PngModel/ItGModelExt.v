(** * ItGModelExt — [it_model] reads its [lens] only on [[0, codes)).

    OWNER: an earlier development run (TABLE-chain value walk, 2026-08-20).  The machine
    runs [inflate_table] on its LENS ARRAY; the declarative theory (the
    ZReproQ6K keystone, [decode_dynamic_tables]) is stated over LISTS via
    [zlens].  This file is the one bridge: two lens arrays that agree on
    the live window produce the SAME [it_model] result — as a term
    equality, axiom-free: the pre-phase derived arrays (count, offs,
    work) are REWRITTEN to shared terms, after which the loop differs in
    the context's [x_lens] field alone, and the loop body reads that
    field at [x_work] values only, which [sort_zzero_range] keeps inside
    the window.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees GtLenProv.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** [it_count] over agreeing windows. *)
Lemma it_count_win : forall n i lens lens' cnt,
  (forall j, i <= j < i + Z.of_nat n -> lens j = lens' j) ->
  it_count n i lens cnt = it_count n i lens' cnt.
Proof.
  induction n as [|n IH]; intros i lens lens' cnt Hag; cbn [it_count];
    [reflexivity|].
  rewrite (Hag i) by lia.
  apply IH. intros j Hj. apply Hag. lia.
Qed.

(** [it_sort] over agreeing windows. *)
Lemma it_sort_win : forall n i lens lens' offs work,
  (forall j, i <= j < i + Z.of_nat n -> lens j = lens' j) ->
  it_sort n i lens offs work = it_sort n i lens' offs work.
Proof.
  induction n as [|n IH]; intros i lens lens' offs work Hag;
    cbn [it_sort]; [reflexivity|].
  rewrite (Hag i) by lia.
  destruct (Z.eqb (lens' i) 0); apply IH; intros j Hj; apply Hag; lia.
Qed.

(** One loop trip only reads [x_lens] at an [x_work] value; with every
    other context field equal, the trip cannot see the difference. *)
Lemma it_step_lens_ext : forall c c' st,
  x_type c = x_type c' ->
  x_codes c = x_codes c' ->
  x_root c = x_root c' ->
  x_max c = x_max c' ->
  x_mask c = x_mask c' ->
  x_work c = x_work c' ->
  x_base c = x_base c' ->
  x_extra c = x_extra c' ->
  x_match c = x_match c' ->
  (forall j, 0 <= j < x_codes c -> x_lens c j = x_lens c' j) ->
  (forall s, 0 <= x_work c s < x_codes c) ->
  it_step c st = it_step c' st.
Proof.
  intros c c' st Hty Hcod Hroot Hmx Hmask Hwork Hbase Hextra Hmatch
    Hlens Hwr.
  unfold it_step, it_here. cbv zeta.
  rewrite <- Hty, <- Hroot, <- Hmx, <- Hmask, <- Hwork, <- Hbase,
    <- Hextra, <- Hmatch.
  rewrite <- (Hlens (x_work c (s_sym st + 1)) (Hwr (s_sym st + 1))).
  reflexivity.
Qed.

Lemma it_loop_lens_ext : forall n c c' st,
  x_type c = x_type c' ->
  x_codes c = x_codes c' ->
  x_root c = x_root c' ->
  x_max c = x_max c' ->
  x_mask c = x_mask c' ->
  x_work c = x_work c' ->
  x_base c = x_base c' ->
  x_extra c = x_extra c' ->
  x_match c = x_match c' ->
  (forall j, 0 <= j < x_codes c -> x_lens c j = x_lens c' j) ->
  (forall s, 0 <= x_work c s < x_codes c) ->
  it_loop n c st = it_loop n c' st.
Proof.
  induction n as [|n IH]; intros c c' st Hty Hcod Hroot Hmx Hmask Hwork
    Hbase Hextra Hmatch Hlens Hwr; cbn [it_loop]; [reflexivity|].
  rewrite <- (it_step_lens_ext c c' st Hty Hcod Hroot Hmx Hmask Hwork
                Hbase Hextra Hmatch Hlens Hwr).
  destruct (it_step c st) as [st1|st1|t1]; [|reflexivity|reflexivity].
  apply IH; assumption.
Qed.

(** THE BRIDGE. *)
Theorem it_model_lens_ext : forall ty lens lens' codes root0 t0,
  0 < codes ->
  arr_eq_on lens lens' 0 codes ->
  it_model ty lens codes root0 t0 = it_model ty lens' codes root0 t0.
Proof.
  intros ty lens lens' codes root0 t0 Hc Hag.
  assert (Hwin : forall j, 0 <= j < 0 + Z.of_nat (Z.to_nat codes) ->
            lens j = lens' j)
    by (intros j Hj; apply Hag; lia).
  assert (Hcnt : it_count (Z.to_nat codes) 0 lens zzero
                 = it_count (Z.to_nat codes) 0 lens' zzero)
    by (apply it_count_win; exact Hwin).
  unfold it_model, it_pre. cbv zeta.
  rewrite <- Hcnt.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [reflexivity|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|reflexivity].
  destruct (it_incomplete ty lft _); [reflexivity|].
  assert (Hsort : it_sort (Z.to_nat codes) 0 lens
                    (it_offs 14%nat 1
                       (it_count (Z.to_nat codes) 0 lens zzero)
                       (zset zzero 1 0)) zzero
                  = it_sort (Z.to_nat codes) 0 lens'
                      (it_offs 14%nat 1
                         (it_count (Z.to_nat codes) 0 lens zzero)
                         (zset zzero 1 0)) zzero)
    by (apply it_sort_win; exact Hwin).
  rewrite <- Hsort.
  destruct (it_enough ty _); [reflexivity|].
  match goal with
  | |- match it_loop ?n ?c1 ?s1 with _ => _ end
       = match it_loop ?n2 ?c2 ?s2 with _ => _ end =>
      replace (it_loop n2 c2 s2) with (it_loop n c1 s1);
        [reflexivity|]
  end.
  apply it_loop_lens_ext;
    cbn [x_type x_codes x_root x_max x_mask x_work x_base x_extra
         x_match x_lens];
    try reflexivity.
  - exact Hag.
  - intro s. apply sort_zzero_range. exact Hc.
Qed.

Print Assumptions it_model_lens_ext.
