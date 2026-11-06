(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit D_iface D_defs
  Gq_numa Numa_kit Gq_gaps Gq_iface Gq_thr_iface Gq_parse_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section ApartX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma live_chunk_apart : forall Σ' (m : mem) l1 p n l2 live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ (p, n) :: l2 -> (forall e, In e live0 -> In e (l1 ++ l2)) -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m l1 p n l2 live0 frs usp a HA LV SUB FRS SPL Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    pose proof (af_live_disj RT AF Σ' m p n p' n' l1 l2 HA LV (SUB _ Hin)) as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.
End ApartX.

(* [comment removed for export] *)
Lemma live_apart2 : forall (RT : rt_sig) (AF : art_facts RT) Σ (m : mem) p n q k, ART RT Σ m ->
  In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) -> (p, n) <> (q, k) -> p + n <= q \/ q + k <= p.
Proof.
  intros RT AF Σ m p n q k HA Hp Hq NE. destruct (in_split _ _ Hp) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p n q k l1 l2 HA E).
  rewrite E in Hq. apply in_app_or in Hq. apply in_or_app. destruct Hq as [H|[H|H]]; [left; exact H| | right; exact H].
  exfalso. apply NE. exact H.
Qed.

(* [comment removed for export] *)
Lemma live_after_free : forall (RT : rt_sig) (AF : art_facts RT) Σ (m : mem) p n (l lv' : list (Z * Z)), ART RT Σ m ->
  rt_live RT Σ = (p, n) :: l -> 0 < n -> (forall q k, In (q, k) l -> 0 < k) -> lv' = live_remove p (rt_live RT Σ) -> lv' = l.
Proof.
  intros RT AF Σ m p n l lv' HA LV Hn LP ->. rewrite LV. rewrite lrm_cons. cbn [fst]. rewrite Z.eqb_refl.
  assert (FRESH : forall e, In e l -> fst e <> p).
  { intros [q k] He. cbn [fst]. pose proof (LP q k He) as Hk.
    pose proof (af_live_disj RT AF Σ m p n q k [] l HA LV He) as D. clear - D Hk Hn. lia. }
  clear - FRESH. induction l as [|e l IH]; [reflexivity|].
  rewrite lrm_cons. replace (fst e =? p) with false by (symmetry; apply Z.eqb_neq; apply FRESH; left; reflexivity).
  f_equal. apply IH. intros e' He'. apply FRESH. right. exact He'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac credit_tac :=
  repeat match goal with H : context [rt_credit] |- _ => revert H end;
  clear; intros; lia.
(* [comment removed for export] *)
Ltac ctx_gc RT :=
  lazymatch goal with
  | |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      repeat match goal with
      | H : ART RT _ ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : mem_inv asegs ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : stk asegs ?m' _ _ |- _ => tryif constr_eq m' mc then fail else clear H
      | H : LIBH ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : io_ssp ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : acc asegs ?m' _ _ |- _ => tryif constr_eq m' mc then fail else clear H
      | H : wmono asegs _ _ |- _ => clear H
      | H : True |- _ => clear H
      end;
      repeat match goal with x : word |- _ => clear x end;
      repeat match goal with x : bvmap 5 word |- _ => clear x end;
      repeat match goal with x : bv 32 |- _ => clear x end;
      repeat match goal with x : list byte |- _ => clear x end;
      repeat match goal with x : mem |- _ => clear x end
  end.
