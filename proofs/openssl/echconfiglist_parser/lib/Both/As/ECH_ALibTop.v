(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_ARep ECH_ALib ECH_Iface
     ECH_ATraces ECH_APF_C4 ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C7 ECH_AStmt_C9 ECH_AStmt_C14 ECH_AStmt_C15 ECH_AC15_top ECH_ACerts
     F_time AsIfaceMemalign AInstFacts N6_strspn ECH_AC14_dec ECH_AC14_readcfg ECH_AC14_entry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section G.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  Hypothesis CERTA : asan_rt_hyps_x H -> getdefctx_fresh_stmt H.
  Hypothesis CERTO3 : asan_rt_hyps_x H -> egs_fresh_stmt H.
  Hypothesis RCFG : asan_rt_hyps_x H -> getdefctx_fresh_stmt H -> egs_fresh_stmt H -> C3_stmts H -> C4_stmts H -> araise_stmt H ->
                    readcfg_stmt H PF9new PF9free.
  Hypothesis HFC : asan_rt_hyps_x H -> atr_ok H -> fuzz_closed_ok H PF9new PF9free.

  Theorem readcfg_closed : asan_rt_hyps_x H -> readcfg_stmt H PF9new PF9free.
  Proof.
    intros HX. exact (RCFG HX (CERTA HX) (CERTO3 HX) (C3_spec_x H CERTA HX) (C4_spec_x H CERTO3 HX) (araise_spec_x H CERTO3 HX)).
  Qed.

  Theorem fuzz_closed_x : asan_rt_hyps_x H -> fuzz_stmt H ECHL.
  Proof. intros HX. exact (fuzz_spec_x H PF9new PF9free CERTA CERTO3 HX (readcfg_closed HX) (HFC HX)). Qed.
End G.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zl_eqb (a b : list Z) : bool := if list_eq_dec Z.eq_dec a b then true else false.
Definition row_eqb (r r' : Z * list Z) : bool := Z.eqb (fst r) (fst r') && zl_eqb (snd r) (snd r').
Definition rows_inclb (small big : list (Z * list Z)) : bool := forallb (fun r => existsb (row_eqb r) big) small.
Lemma row_eqb_eq : forall r r', row_eqb r r' = true -> r = r'.
Proof.
  intros [a l] [a' l'] E. unfold row_eqb, zl_eqb in E. cbn [fst snd] in E. apply Bool.andb_true_iff in E. destruct E as [E1 E2].
  apply Z.eqb_eq in E1. destruct (list_eq_dec Z.eq_dec l l') as [->|NE]; [subst; reflexivity| discriminate].
Qed.
Lemma Forall_of_inclb : forall (P : Z * list Z -> Prop) small big, rows_inclb small big = true -> Forall P big -> Forall P small.
Proof.
  intros P small big E F. unfold rows_inclb in E. rewrite forallb_forall in E. apply Forall_forall. intros r Hr.
  specialize (E r Hr). rewrite existsb_exists in E. destruct E as (r' & Hr' & Q). apply row_eqb_eq in Q. subst r'.
  exact (proj1 (Forall_forall _ _) F r Hr').
Qed.

Section T.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Theorem fuzz_rows_closed : atr_ok H -> fuzz_closed_ok H PF9newC PF9freeC.
  Proof.
    intros TR. unfold atr_ok in TR. unfold fuzz_closed_ok, TOK.
    assert (INC : forall small, rows_inclb small LIB_TRACES = true -> Forall (fun r : Z * list Z => trace_ok (as_TR H) (fst r) (snd r)) small)
      by (intros small E; exact (Forall_of_inclb _ small LIB_TRACES E TR)).
    split. { intros [f [|cx] [|ec] E v] x; unfold parse_closed_ok; cbn [mid_ctx mid_err];
             (match goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end; apply INC; vm_compute; reflexivity). }
    split; [unfold ctxph_closed_ok; apply INC; vm_compute; reflexivity|].
    split; [unfold errph_closed_ok; apply INC; vm_compute; reflexivity|].
    repeat match goal with |- _ /\ _ => split end;
      try (intros eph; destruct eph);
      (match goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end; apply INC; vm_compute; reflexivity).
  Qed.
End T.

(* [comment removed for export] *)
Theorem fuzz_closed :
  forall (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)),
  (forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> getdefctx_fresh_stmt H) ->
  (forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> egs_fresh_stmt H) ->
  (forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> getdefctx_fresh_stmt H -> egs_fresh_stmt H -> C3_stmts H -> C4_stmts H -> araise_stmt H ->
                                        readcfg_stmt H PF9new PF9free) ->
  (forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> atr_ok H -> fuzz_closed_ok H PF9new PF9free) ->
  forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> fuzz_stmt H ECHL.
Proof.
  intros PF9new PF9free CA CO RC FC HCEIL H HX.
  exact (fuzz_closed_x H PF9new PF9free (CA HCEIL H) (CO HCEIL H) (RC HCEIL H) (FC HCEIL H) HX).
Qed.

(* [comment removed for export] *)
Theorem fuzz_closed3 :
  (forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> getdefctx_fresh_stmt H) ->
  (forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> egs_fresh_stmt H) ->
  (forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> getdefctx_fresh_stmt H -> egs_fresh_stmt H -> C3_stmts H -> C4_stmts H -> araise_stmt H ->
                                        readcfg_stmt H PF9newC PF9freeC) ->
  forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> fuzz_stmt H ECHL.
Proof.
  intros CA CO RC HCEIL H HX.
  exact (fuzz_closed PF9newC PF9freeC CA CO RC (fun HC H' _ TR => fuzz_rows_closed H' TR) HCEIL H HX).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section G4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  (* [comment removed for export] *)
  Hypothesis AENTRY : asan_rt_hyps_x H -> araise_stmt H -> atime_stmt H -> rp_entry_shape H.

  Theorem rp_entry_closed4 : asan_rt_hyps_x H -> ainst_facts H -> rp_entry_shape H.
  Proof. intros HX AIF. exact (AENTRY HX (araise_spec_i H HX AIF) (ainst_time H AIF)). Qed.

  Theorem readcfg_closed4 : asan_rt_hyps_x H -> ainst_facts H -> readcfg_stmt H PF9newC PF9freeC.
  Proof.
    intros HX AIF.
    exact (readcfg_spec H HX (araise_spec_i H HX AIF) strspn_icpt_ok
             (newmembuf_spec_i H HX AIF) (bionew_b64_spec_i H HX AIF) (biopush_spec_i H HX AIF) (bioread_b64_spec_i H HX AIF)
             (biofreeall_spec_i H HX AIF) (rp_entry_closed4 HX AIF)
             PF9newC PF9freeC (fun xq => eq_refl) eq_refl).
  Qed.

  Theorem fuzz_closed4_x : asan_rt_hyps_x H -> ainst_facts H -> fuzz_stmt H ECHL.
  Proof. intros HX AIF. exact (fuzz_spec_i H PF9newC PF9freeC HX AIF (readcfg_closed4 HX AIF) (fuzz_rows_closed H)). Qed.
End G4.

(* [comment removed for export] *)
Theorem fuzz_closed4 :
  (forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> araise_stmt H -> atime_stmt H -> rp_entry_shape H) ->
  forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> ainst_facts H -> fuzz_stmt H ECHL.
Proof.
  intros AE HCEIL H HX AIF. exact (fuzz_closed4_x H (AE HCEIL H) HX AIF).
Qed.

Print Assumptions fuzz_closed4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fuzz_closed5 :
  forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> ainst_facts H -> fuzz_stmt H ECHL.
Proof.
  exact (fuzz_closed4 (fun HCEIL H => @aentry_shape HCEIL H)).
Qed.

Print Assumptions fuzz_closed5.
