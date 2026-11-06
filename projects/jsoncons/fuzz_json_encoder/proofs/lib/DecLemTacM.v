(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutOpsD.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DLT.
Lemma u_range : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. pose proof (bv_unsigned_in_range _ x) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Lemma s_of_u : forall x : word, bv_signed x = if bv_unsigned x <? 2 ^ 63 then bv_unsigned x else bv_unsigned x - 2 ^ 64.
Proof.
  intros x. pose proof (u_range x) as B. unfold bv_signed, bv_swrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_wrap 64) with (fun z => z mod 2 ^ 64).
  cbv beta. destruct (Z.ltb_spec (bv_unsigned x) (2 ^ 63)).
  - rewrite Z.mod_small by lia. lia.
  - replace (bv_unsigned x + 2 ^ 63) with (bv_unsigned x - 2 ^ 63 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
Ltac prem_split H :=
  repeat match type of H with
         | Forall _ (_ :: _) => let H1 := fresh "P" in apply Forall_cons_iff in H as [H1 H]
         end.
Ltac to_z :=
  cbn [kentry_ok edenot] in *;
  repeat rewrite ?u_sltu64, ?u_slt64, ?u_add64, ?u_sub64, ?u_lit64, ?s_of_u in *;
  change two64 with (2 ^ 64) in *.
Ltac gen_u :=
  repeat match goal with
         | |- context [bv_unsigned (ev ?E ?n)] => let x := fresh "x" in let Hx := fresh "Hx" in
             pose proof (u_range (ev E n)) as Hx; set (x := bv_unsigned (ev E n)) in *; clearbody x
         | H : context [bv_unsigned (ev ?E ?n)] |- _ => let x := fresh "x" in let Hx := fresh "Hx" in
             pose proof (u_range (ev E n)) as Hx; set (x := bv_unsigned (ev E n)) in *; clearbody x
         end.
(* [comment removed for export] *)
Ltac ifs :=
  repeat match goal with
         | H : context [if ?c then _ else _] |- _ => let Q := fresh "Q" in destruct c eqn:Q; [apply Z.ltb_lt in Q | apply Z.ltb_ge in Q]; try lia
         | |- context [if ?c then _ else _] => let Q := fresh "Q" in destruct c eqn:Q; [apply Z.ltb_lt in Q | apply Z.ltb_ge in Q]; try lia
         end.
Ltac lem := let E := fresh "E" in let M := fresh "M" in let HP := fresh "HP" in
  intros E M HP; prem_split HP; to_z; gen_u; ifs; Z.div_mod_to_equations; lia.
(* [comment removed for export] *)
Ltac lem_sext := let E := fresh "E" in let M := fresh "M" in let HP := fresh "HP" in
  intros E M HP; prem_split HP; cbn [kentry_ok edenot] in *;
  match goal with |- _ <= bv_unsigned ?t <= _ =>
    let B := fresh "B" in let H0 := fresh "H0" in pose proof (u_range t) as B;
    destruct (Z.eq_dec (bv_unsigned t) 0) as [H0|]; [exfalso|lia];
    unfold ext_val, ext_Z in H0; rewrite u_lit64 in H0; change two64 with (2 ^ 64) in H0;
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H0; cbn in H0; gen_u; Z.div_mod_to_equations; lia
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint blobfree (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => blobfree a && blobfree b
  | EExt _ _ _ a => blobfree a
  | EBlob _ _ _ _ => false
  end.
Fixpoint evars (e : expr) : list nat :=
  match e with
  | ELit _ | EBlob _ _ _ _ => []
  | EVar n => [n]
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars a ++ evars b
  | EExt _ _ _ a => evars a
  end.
Definition envz (f : nat -> Z) : env := Env (fun n => Z_to_bv 64 (f n)) (fun _ => []).
Lemma edenot_ext : forall f g e, blobfree e = true -> (forall n, In n (evars e) -> f n = g n) -> edenot (envz f) e = edenot (envz g) e.
Proof.
  intros f g e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros Hb Hv; cbn [blobfree evars edenot] in *;
    try reflexivity; try discriminate.
  - cbn [envz ev]. rewrite (Hv n (or_introl eq_refl)). reflexivity.
  - apply andb_prop in Hb as [H1 H2]. rewrite (IHa H1), (IHb H2); [reflexivity | |]; intros m Hm; apply Hv; apply in_or_app; auto.
  - apply andb_prop in Hb as [H1 H2]. rewrite (IHa H1), (IHb H2); [reflexivity | |]; intros m Hm; apply Hv; apply in_or_app; auto.
  - apply andb_prop in Hb as [H1 H2]. rewrite (IHa H1), (IHb H2); [reflexivity | |]; intros m Hm; apply Hv; apply in_or_app; auto.
  - apply andb_prop in Hb as [H1 H2]. rewrite (IHa H1), (IHb H2); [reflexivity | |]; intros m Hm; apply Hv; apply in_or_app; auto.
  - rewrite (IHa Hb Hv). reflexivity.
Qed.
Lemma edenot_envz : forall E e, blobfree e = true -> edenot E e = edenot (envz (fun n => bv_unsigned (ev E n))) e.
Proof.
  intros E e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros Hb; cbn [blobfree edenot] in *;
    try reflexivity; try discriminate.
  - cbn [envz ev]. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. apply bv_unsigned_in_range.
  - apply andb_prop in Hb as [H1 H2]. rewrite <- (IHa H1), <- (IHb H2). reflexivity.
  - apply andb_prop in Hb as [H1 H2]. rewrite <- (IHa H1), <- (IHb H2). reflexivity.
  - apply andb_prop in Hb as [H1 H2]. rewrite <- (IHa H1), <- (IHb H2). reflexivity.
  - apply andb_prop in Hb as [H1 H2]. rewrite <- (IHa H1), <- (IHb H2). reflexivity.
  - rewrite <- (IHa Hb). reflexivity.
Qed.
(* [comment removed for export] *)
Definition kexpr (K : kentry) : option (expr * Z * Z) := match K with KRange e lo hi => Some (e, lo, hi) | _ => None end.
Definition kb (f : nat -> Z) (K : kentry) : bool :=
  match K with KRange e lo hi => let u := bv_unsigned (edenot (envz f) e) in (Z.leb lo u && Z.leb u hi)%bool | _ => false end.
Definition kpure (K : kentry) : bool := match K with KRange e _ _ => blobfree e | _ => false end.
Definition kvars (K : kentry) : list nat := match K with KRange e _ _ => evars e | _ => [] end.
Fixpoint zrange (n : nat) (l : Z) : list Z := match n with O => [] | S m => l :: zrange m (l + 1) end.
Lemma zrange_In : forall n l z, l <= z < l + Z.of_nat n -> In z (zrange n l).
Proof. induction n as [|n IH]; intros l z H; [lia|]. cbn [zrange]. destruct (Z.eq_dec z l) as [->|Hne]; [left; reflexivity | right; apply IH; lia]. Qed.
Definition upd (f : nat -> Z) (v : nat) (z : Z) : nat -> Z := fun n => if Nat.eqb n v then z else f n.
Fixpoint enum (vars : list (nat * Z * Z)) (f : nat -> Z) (P : (nat -> Z) -> bool) : bool :=
  match vars with
  | [] => P f
  | (v, l, h) :: r => forallb (fun z => enum r (upd f v z) P) (zrange (Z.to_nat (h - l + 1)) l)
  end.
Lemma enum_sound : forall vars f P g, enum vars f P = true ->
  (forall v l h, In (v, l, h) vars -> l <= g v <= h) -> (forall n, ~ In n (map (fun x => fst (fst x)) vars) -> g n = f n) ->
  exists f', P f' = true /\ forall n, f' n = g n.
Proof.
  induction vars as [|[[v l] h] r IH]; intros f P g H Hr Ho; cbn [enum] in H.
  - exists f. split; [exact H|]. intros n. symmetry. apply Ho. intros [].
  - rewrite forallb_forall in H. specialize (H (g v)).
    assert (Hin : In (g v) (zrange (Z.to_nat (h - l + 1)) l)).
    { apply zrange_In. specialize (Hr v l h (or_introl eq_refl)). lia. }
    specialize (H Hin). apply (IH (upd f v (g v)) P g H).
    + intros v' l' h' Hx. apply (Hr v' l' h'). right. exact Hx.
    + intros n Hn. unfold upd. destruct (Nat.eqb n v) eqn:En; [apply Nat.eqb_eq in En; subst n; reflexivity|].
      apply Ho. cbn [map fst]. intros [Hx|Hx]; [apply Nat.eqb_neq in En; congruence | exact (Hn Hx)].
Qed.
(* [comment removed for export] *)
Definition bvars (Ps : list kentry) : list (nat * Z * Z) :=
  flat_map (fun K => match K with KRange (EVar v) l h => if Z.leb (h - l) 70000 then [(v, l, h)] else [] | _ => [] end) Ps.
Fixpoint dedupv (l : list (nat * Z * Z)) : list (nat * Z * Z) :=
  match l with [] => [] | x :: r => if existsb (fun y : nat * Z * Z => Nat.eqb (fst (fst y)) (fst (fst x))) r then dedupv r else x :: dedupv r end.
Definition lem_chk (Ps : list kentry) (K : kentry) : bool :=
  let vars := dedupv (bvars Ps) in
  (forallb kpure (K :: Ps)
   && forallb (fun n => existsb (fun x : nat * Z * Z => Nat.eqb (fst (fst x)) n) vars) (flat_map kvars (K :: Ps))
   && enum vars (fun _ => 0) (fun f => implb (forallb (kb f) Ps) (kb f K)))%bool.
Lemma kb_sound : forall segs E M K f, kpure K = true -> (forall n, In n (kvars K) -> f n = bv_unsigned (ev E n)) -> (kb f K = true <-> kentry_ok segs E M K).
Proof.
  intros segs E M K f Hp Hf. destruct K as [| | | | |e lo hi| | | |]; try discriminate. cbn [kpure kvars kb kentry_ok] in *.
  rewrite (edenot_envz E e Hp). rewrite (edenot_ext f (fun n => bv_unsigned (ev E n)) e Hp Hf).
  rewrite andb_true_iff, !Z.leb_le. reflexivity.
Qed.
Lemma dedupv_In : forall l x, In x (dedupv l) -> In x l.
Proof. induction l as [|y r IH]; intros x H; [exact H|]. cbn [dedupv] in H. destruct (existsb _ r); [right; exact (IH x H)|]. destruct H as [<-|H]; [left; reflexivity | right; exact (IH x H)]. Qed.
Theorem lem_chk_sound : forall segs Ps K, lem_chk Ps K = true -> CXD.lemma_ok segs Ps K.
Proof.
  intros segs Ps K H E M HP. unfold lem_chk in H. apply andb_prop in H as [H He]. apply andb_prop in H as [Hpure Hcov].
  set (vars := dedupv (bvars Ps)) in *.
  set (cov := fun n => existsb (fun x : nat * Z * Z => Nat.eqb (fst (fst x)) n) vars).
  set (g := fun n => if cov n then bv_unsigned (ev E n) else 0).
  destruct (enum_sound vars (fun _ => 0) _ g He) as (f' & Hf' & Heq).
  - intros v l h Hin. assert (Hc : cov v = true).
    { unfold cov. apply existsb_exists. exists (v, l, h). split; [exact Hin | cbn; apply Nat.eqb_refl]. }
    unfold g. rewrite Hc. apply dedupv_In in Hin. unfold bvars in Hin. apply in_flat_map in Hin as (K0 & HK0 & Hx).
    destruct K0 as [| | | | |e0 l0 h0| | | |]; try contradiction. destruct e0; try contradiction. destruct (Z.leb (h0 - l0) 70000); [|contradiction].
    destruct Hx as [Hx|[]]. injection Hx as <- <- <-. pose proof (proj1 (Forall_forall _ _) HP _ HK0) as HK. cbn [kentry_ok edenot] in HK. exact HK.
  - intros n Hn. unfold g. destruct (cov n) eqn:Hc; [|reflexivity]. exfalso. apply Hn. unfold cov in Hc. apply existsb_exists in Hc as (x & Hx & Hxe).
    apply Nat.eqb_eq in Hxe. subst n. exact (in_map (fun x0 : nat * Z * Z => fst (fst x0)) vars x Hx).
  - (* [comment removed for export] *)
    assert (Hag : forall K0, In K0 (K :: Ps) -> forall n, In n (kvars K0) -> f' n = bv_unsigned (ev E n)).
    { intros K0 HK0 n Hn. rewrite Heq. unfold g. rewrite forallb_forall in Hcov.
      assert (Hc : cov n = true) by (apply Hcov; apply in_flat_map; exists K0; split; assumption). rewrite Hc. reflexivity. }
    rewrite forallb_forall in Hpure.
    apply (proj1 (kb_sound segs E M K f' (Hpure K (or_introl eq_refl)) (Hag K (or_introl eq_refl)))).
    destruct (forallb (kb f') Ps) eqn:HPs; cbn [implb] in Hf'; [exact Hf'|].
    exfalso. assert (X : forallb (kb f') Ps = true); [|congruence].
    apply forallb_forall. intros P HPin. apply (proj2 (kb_sound segs E M P f' (Hpure P (or_intror HPin)) (Hag P (or_intror HPin)))).
    exact (proj1 (Forall_forall _ _) HP P HPin).
Qed.
(* [comment removed for export] *)
Ltac lem_enum := apply lem_chk_sound; vm_compute; reflexivity.
End DLT.
