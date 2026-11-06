(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore FxBase.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module AX2H.

Definition same_fast (bc : bctx) (ub : expr) : bool :=
  if shares_var ub ub then
    if lin_nowrapRB bc ub then match lsub_e (snd (lin_of ub)) (snd (lin_of ub)) with [] => true | _ => false end else false
  else false.
Definition apart_c (uk m1 k m2 : Z) : bool := let d := k - uk in if Z.leb m1 d then true else Z.leb d (- m2).

Definition quick (m1o : option Z) (ub : expr) (uk : Z) (K : kentry) : bool :=
  match m1o with
  | Some m1 =>
      match K with
      | KWord (SA b k) w _ => if Nat.leb w 8 then if BASF.expr_eqbF b ub then apart_c uk m1 k (zlit64 (Z.of_nat w)) else false else false
      | KZero (SA b k) (ELit z2) | KBlob (SA b k) (ELit z2) _ | KFill (SA b k) (ELit z2) _ | KUnk (SA b k) (ELit z2) =>
          if BASF.expr_eqbF b ub then apart_c uk m1 k (zlit64 z2) else false
      | _ => false
      end
  | None => false
  end.
Definition mk_m1o (bc : bctx) (ub : expr) (un : expr) : option Z :=
  match un with ELit z1 => if same_fast bc ub then Some (zlit64 z1) else None | _ => None end.

Lemma same_apart : forall bc sp ub uk z1 k z2,
  same_fast bc ub = true -> apart_c uk (zlit64 z1) k (zlit64 z2) = true ->
  ranges_apart_pB bc sp ub uk (ELit z1) ub k (ELit z2) = true.
Proof.
  intros bc sp ub uk z1 k z2 HS HA. unfold same_fast in HS.
  destruct (shares_var ub ub) eqn:SV; [|discriminate]. destruct (lin_nowrapRB bc ub) eqn:NW; [|discriminate].
  destruct (lsub_e (snd (lin_of ub)) (snd (lin_of ub))) eqn:LS; [|discriminate].
  unfold ranges_apart_pB. cbv zeta.
  match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
  match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
  unfold lin_apartB. rewrite SV. unfold lin_apart0B. rewrite NW. cbv zeta. rewrite LS. cbn [andb].
  unfold lin_testB. cbn [lin_range].
  replace (fst (lin_of ub) + k - fst (lin_of ub) - uk) with (k - uk) by ring.
  unfold apart_c in HA. cbv zeta in HA. destruct (Z.leb (zlit64 z1) (k - uk)); [reflexivity|]. rewrite HA. reflexivity.
Qed.
Lemma quick_sound : forall bc sp ub uk un K, quick (mk_m1o bc ub un) ub uk K = true -> APC.kentry_apart_bpB bc sp ub uk un K = true.
Proof.
  intros bc sp ub uk un K H. unfold mk_m1o in H. destruct un as [z1| | | | | | |]; try discriminate H.
  destruct (same_fast bc ub) eqn:HS; [|discriminate H]. cbn [quick] in H.
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] len|a1 n1 a2 n2|[b k] len c|[b k] len]; try discriminate H; cbn [APC.kentry_apart_bpB].
  - destruct (Nat.leb w 8); [|discriminate H]. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
    apply BASF.expr_eqbF_true in E. subst b. cbn [andb]. apply same_apart; assumption.
  - destruct len as [z2| | | | | | |]; try discriminate H. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
    apply BASF.expr_eqbF_true in E. subst b. apply same_apart; assumption.
  - destruct len as [z2| | | | | | |]; try discriminate H. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
    apply BASF.expr_eqbF_true in E. subst b. apply same_apart; assumption.
  - destruct len as [z2| | | | | | |]; try discriminate H. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
    apply BASF.expr_eqbF_true in E. subst b. apply same_apart; assumption.
  - destruct len as [z2| | | | | | |]; try discriminate H. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
    apply BASF.expr_eqbF_true in E. subst b. apply same_apart; assumption.
Qed.

Definition havoc1pF (bc : bctx) (sp : sprep) (m1o : option Z) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if quick m1o ub uk K then [K] else APC.havoc1pB bc sp ub uk un K.
Lemma havoc1pF_eq : forall bc sp ub uk un K, havoc1pF bc sp (mk_m1o bc ub un) ub uk un K = APC.havoc1pB bc sp ub uk un K.
Proof.
  intros. unfold havoc1pF. destruct (quick (mk_m1o bc ub un) ub uk K) eqn:Q; [|reflexivity].
  unfold APC.havoc1pB. rewrite (quick_sound _ sp _ _ _ _ Q). rewrite orb_true_r. reflexivity.
Qed.
Definition kn_havocF (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  let m1o := mk_m1o bc ub un in
  List.flat_map (havoc1pF bc sp m1o ub uk un) (bc_fk bc).
Lemma kn_havocF_eq : forall bc ub uk un, kn_havocF bc ub uk un = APC.kn_havocB bc ub uk un.
Proof.
  intros. unfold kn_havocF, APC.kn_havocB. cbv zeta. f_equal.
  apply functional_extensionality; intros K. apply havoc1pF_eq.
Qed.
Definition kn_havocMF (k : list kentry) := kn_havocF (mkbc k).
Lemma kn_havocMF_eq : kn_havocMF = APC.kn_havoc.
Proof.
  apply functional_extensionality; intros k. unfold kn_havocMF.
  repeat (apply functional_extensionality; intros ?). rewrite kn_havocF_eq. rewrite APC.kn_havocB_eqf. reflexivity.
Qed.
End AX2H.
