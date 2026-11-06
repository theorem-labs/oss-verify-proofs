(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Uint63.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff FxDrive FxDrive3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma int_eqb_ok (a b : int) : (a =? b)%uint63 = true -> a = b.
Proof. exact (proj1 (Uint63.eqb_spec a b)). Qed.

Section ListEq.
Context {T : Type} (eqb : T -> T -> bool) (eqb_ok : forall a b, eqb a b = true -> a = b).
Fixpoint list_eqb (l m : list T) : bool :=
  match l, m with
  | [], [] => true
  | a :: l', b :: m' => if eqb a b then list_eqb l' m' else false
  | _, _ => false
  end.
Lemma list_eqb_ok : forall l m, list_eqb l m = true -> l = m.
Proof.
  induction l as [|a l IH]; intros [|b m] H; cbn [list_eqb] in H; try discriminate; [reflexivity|].
  destruct (eqb a b) eqn:E; [|discriminate]. apply eqb_ok in E. subst b. rewrite (IH m H). reflexivity.
Qed.
End ListEq.

Section TrieEq.
Context {T : Type} (eqb : T -> T -> bool) (eqb_ok : forall a b, eqb a b = true -> a = b).
Fixpoint itrie_eqb (s t : itrie T) : bool :=
  match s, t with
  | IEmpty, IEmpty => true
  | ILeaf k v, ILeaf k' v' => if (k =? k')%uint63 then eqb v v' else false
  | INode l r, INode l' r' => if itrie_eqb l l' then itrie_eqb r r' else false
  | _, _ => false
  end.
Lemma itrie_eqb_ok : forall s t, itrie_eqb s t = true -> s = t.
Proof.
  induction s as [|k v|l IHl r IHr]; intros [|k' v'|l' r'] H; cbn [itrie_eqb] in H; try discriminate; [reflexivity| |].
  - destruct (k =? k')%uint63 eqn:E; [|discriminate]. apply int_eqb_ok in E. apply eqb_ok in H. subst. reflexivity.
  - destruct (itrie_eqb l l') eqn:E; [|discriminate]. rewrite (IHl _ E), (IHr _ H). reflexivity.
Qed.
End TrieEq.

Definition option_eqb {T : Type} (eqb : T -> T -> bool) (a b : option T) : bool :=
  match a, b with Some x, Some y => eqb x y | None, None => true | _, _ => false end.
Lemma option_eqb_ok {T : Type} (eqb : T -> T -> bool) (eqb_ok : forall a b, eqb a b = true -> a = b) a b :
  option_eqb eqb a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; [rewrite (eqb_ok _ _ H)|]; reflexivity. Qed.

Definition bool_eqb (a b : bool) : bool := if a then b else negb b.
Lemma bool_eqb_ok a b : bool_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; reflexivity. Qed.

Definition pkind_eqb (a b : pkind) : bool :=
  match a, b with PKZero, PKZero | PKImage, PKImage | PKUnk, PKUnk => true | _, _ => false end.
Lemma pkind_eqb_ok a b : pkind_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; reflexivity. Qed.

Definition rkind_eqb (a b : rkind) : bool :=
  match a, b with RK_plain, RK_plain => true | RK_shadow p, RK_shadow q => (p =? q)%uint63 | _, _ => false end.
Lemma rkind_eqb_ok a b : rkind_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; [|apply int_eqb_ok in H; subst]; reflexivity. Qed.

Definition slot_eqb (a b : slot) : bool :=
  match a, b with
  | SK x, SK y => (x =? y)%uint63
  | SV v j, SV w k => if fval_eqb v w then (j =? k)%uint63 else false
  | SU, SU => true
  | _, _ => false
  end.
Lemma slot_eqb_ok a b : slot_eqb a b = true -> a = b.
Proof.
  destruct a as [x|v j|], b as [y|w k|]; cbn; intros H; try discriminate; [| |reflexivity].
  - apply int_eqb_ok in H. subst. reflexivity.
  - destruct (fval_eqb v w) eqn:E; [|discriminate]. apply fval_eqb_eq in E. apply int_eqb_ok in H. subst. reflexivity.
Qed.

Definition slots_eqb (a b : slots) : bool :=
  if slot_eqb (sl0 a) (sl0 b) then if slot_eqb (sl1 a) (sl1 b) then if slot_eqb (sl2 a) (sl2 b) then if slot_eqb (sl3 a) (sl3 b) then
  if slot_eqb (sl4 a) (sl4 b) then if slot_eqb (sl5 a) (sl5 b) then if slot_eqb (sl6 a) (sl6 b) then slot_eqb (sl7 a) (sl7 b)
  else false else false else false else false else false else false else false.
Lemma slots_eqb_ok a b : slots_eqb a b = true -> a = b.
Proof.
  destruct a as [a0 a1 a2 a3 a4 a5 a6 a7], b as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold slots_eqb. cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7].
  intros H.
  destruct (slot_eqb a0 b0) eqn:E0; [|discriminate]. destruct (slot_eqb a1 b1) eqn:E1; [|discriminate].
  destruct (slot_eqb a2 b2) eqn:E2; [|discriminate]. destruct (slot_eqb a3 b3) eqn:E3; [|discriminate].
  destruct (slot_eqb a4 b4) eqn:E4; [|discriminate]. destruct (slot_eqb a5 b5) eqn:E5; [|discriminate].
  destruct (slot_eqb a6 b6) eqn:E6; [|discriminate].
  apply slot_eqb_ok in E0, E1, E2, E3, E4, E5, E6, H. subst. reflexivity.
Qed.

Definition cell_eqb (a b : cell) : bool :=
  match a, b with CV v, CV w => fval_eqb v w | CU, CU => true | CB s, CB t => slots_eqb s t | _, _ => false end.
Lemma cell_eqb_ok a b : cell_eqb a b = true -> a = b.
Proof.
  destruct a as [v| |s], b as [w| |t]; cbn; intros H; try discriminate; [|reflexivity|].
  - apply fval_eqb_eq in H. subst. reflexivity.
  - apply slots_eqb_ok in H. subst. reflexivity.
Qed.

Definition page_eqb (p q : page) : bool :=
  if bool_eqb (pg_wr p) (pg_wr q) then if pkind_eqb (pg_kind p) (pg_kind q) then itrie_eqb cell_eqb (pg_cells p) (pg_cells q)
  else false else false.
Lemma page_eqb_ok p q : page_eqb p q = true -> p = q.
Proof.
  destruct p as [w k c], q as [w' k' c']. unfold page_eqb. cbn [pg_wr pg_kind pg_cells]. intros H.
  destruct (bool_eqb w w') eqn:E1; [|discriminate]. destruct (pkind_eqb k k') eqn:E2; [|discriminate].
  apply bool_eqb_ok in E1. apply pkind_eqb_ok in E2. apply (itrie_eqb_ok cell_eqb cell_eqb_ok) in H. subst. reflexivity.
Qed.

Definition region_eqb (r s : region) : bool :=
  if (rg_lo r =? rg_lo s)%uint63 then if (rg_len r =? rg_len s)%uint63 then if (rg_align r =? rg_align s)%uint63 then
  if option_eqb pkind_eqb (rg_dflt r) (rg_dflt s) then if (rg_clo r =? rg_clo s)%uint63 then if (rg_chi r =? rg_chi s)%uint63 then
  if rkind_eqb (rg_kind r) (rg_kind s) then itrie_eqb page_eqb (rg_pages r) (rg_pages s)
  else false else false else false else false else false else false else false.
Lemma region_eqb_ok r s : region_eqb r s = true -> r = s.
Proof.
  destruct r as [a1 a2 a3 a4 a5 a6 a7 a8], s as [b1 b2 b3 b4 b5 b6 b7 b8]. unfold region_eqb.
  cbn [rg_lo rg_len rg_align rg_dflt rg_pages rg_clo rg_chi rg_kind]. intros H.
  destruct (a1 =? b1)%uint63 eqn:E1; [|discriminate]. destruct (a2 =? b2)%uint63 eqn:E2; [|discriminate].
  destruct (a3 =? b3)%uint63 eqn:E3; [|discriminate]. destruct (option_eqb pkind_eqb a4 b4) eqn:E4; [|discriminate].
  destruct (a6 =? b6)%uint63 eqn:E6; [|discriminate]. destruct (a7 =? b7)%uint63 eqn:E7; [|discriminate].
  destruct (rkind_eqb a8 b8) eqn:E8; [|discriminate].
  apply int_eqb_ok in E1, E2, E3, E6, E7. apply (option_eqb_ok pkind_eqb pkind_eqb_ok) in E4. apply rkind_eqb_ok in E8.
  apply (itrie_eqb_ok page_eqb page_eqb_ok) in H. subst. reflexivity.
Qed.

Definition fstate_eqb (F G : fstate) : bool :=
  if (f_pc F =? f_pc G)%uint63 then if option_eqb fval_eqb (f_resv F) (f_resv G) then
  if itrie_eqb fval_eqb (f_regs F) (f_regs G) then itrie_eqb region_eqb (f_mem F) (f_mem G) else false else false else false.
Lemma fstate_eqb_ok F G : fstate_eqb F G = true -> F = G.
Proof.
  destruct F as [a1 a2 a3 a4], G as [b1 b2 b3 b4]. unfold fstate_eqb. cbn [f_pc f_regs f_mem f_resv]. intros H.
  destruct (a1 =? b1)%uint63 eqn:E1; [|discriminate]. destruct (option_eqb fval_eqb a4 b4) eqn:E4; [|discriminate].
  destruct (itrie_eqb fval_eqb a2 b2) eqn:E2; [|discriminate].
  apply int_eqb_ok in E1. apply (option_eqb_ok fval_eqb fval_eqb_eq) in E4. apply (itrie_eqb_ok fval_eqb fval_eqb_eq) in E2.
  apply (itrie_eqb_ok region_eqb region_eqb_ok) in H. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Definition opk_eqb (a b : opk) : bool :=
  match a, b with OpCut, OpCut | OpLazy, OpLazy | OpGrant, OpGrant | OpShadow, OpShadow | OpCommit, OpCommit => true | _, _ => false end.
Lemma opk_eqb_ok a b : opk_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; reflexivity. Qed.
Definition vop_eqb (a b : vop) : bool := if opk_eqb (fst a) (fst b) then fent_eqb (snd a) (snd b) else false.
Lemma vop_eqb_ok a b : vop_eqb a b = true -> a = b.
Proof.
  destruct a as [o e], b as [o' e']. unfold vop_eqb. cbn [fst snd]. intros H. destruct (opk_eqb o o') eqn:E; [|discriminate].
  apply opk_eqb_ok in E. apply fent_eqb_eq in H. subst. reflexivity.
Qed.
Definition iiz_eqb (a b : int * int * Z) : bool :=
  if (fst (fst a) =? fst (fst b))%uint63 then if (snd (fst a) =? snd (fst b))%uint63 then Z.eqb (snd a) (snd b) else false else false.
Lemma iiz_eqb_ok a b : iiz_eqb a b = true -> a = b.
Proof.
  destruct a as [[a1 a2] a3], b as [[b1 b2] b3]. unfold iiz_eqb. cbn [fst snd]. intros H.
  destruct (a1 =? b1)%uint63 eqn:E1; [|discriminate]. destruct (a2 =? b2)%uint63 eqn:E2; [|discriminate].
  apply int_eqb_ok in E1, E2. apply Z.eqb_eq in H. subst. reflexivity.
Qed.
Definition izz_eqb (a b : int * Z * Z) : bool :=
  if (fst (fst a) =? fst (fst b))%uint63 then if Z.eqb (snd (fst a)) (snd (fst b)) then Z.eqb (snd a) (snd b) else false else false.
Lemma izz_eqb_ok a b : izz_eqb a b = true -> a = b.
Proof.
  destruct a as [[a1 a2] a3], b as [[b1 b2] b3]. unfold izz_eqb. cbn [fst snd]. intros H.
  destruct (a1 =? b1)%uint63 eqn:E1; [|discriminate]. destruct (Z.eqb a2 b2) eqn:E2; [|discriminate].
  apply int_eqb_ok in E1. apply Z.eqb_eq in E2, H. subst. reflexivity.
Qed.

Definition fledger_eqb (a b : fledger) : bool :=
  if list_eqb fent_eqb (fl_maps a) (fl_maps b) then if list_eqb fent_eqb (fl_na a) (fl_na b) then
  if (fl_brk a =? fl_brk b)%uint63 then if Z.eqb (fl_c a) (fl_c b) then Z.eqb (fl_S a) (fl_S b) else false else false else false else false.
Lemma fledger_eqb_ok a b : fledger_eqb a b = true -> a = b.
Proof.
  destruct a as [a1 a2 a3 a4 a5], b as [b1 b2 b3 b4 b5]. unfold fledger_eqb. cbn [fl_maps fl_na fl_brk fl_c fl_S]. intros H.
  destruct (list_eqb fent_eqb a1 b1) eqn:E1; [|discriminate]. destruct (list_eqb fent_eqb a2 b2) eqn:E2; [|discriminate].
  destruct (a3 =? b3)%uint63 eqn:E3; [|discriminate]. destruct (Z.eqb a4 b4) eqn:E4; [|discriminate].
  apply (list_eqb_ok fent_eqb fent_eqb_eq) in E1, E2. apply int_eqb_ok in E3. apply Z.eqb_eq in E4, H. subst. reflexivity.
Qed.

Definition fledger3_eqb (a b : fledger3) : bool :=
  if fledger_eqb (fl3 a) (fl3 b) then if list_eqb fent_eqb (fl_all a) (fl_all b) then if list_eqb vop_eqb (fl_ops a) (fl_ops b) then
  if list_eqb fent_eqb (fl_lazy a) (fl_lazy b) then if list_eqb fent_eqb (fl_allow a) (fl_allow b) then
  if Z.eqb (fl_Ab a) (fl_Ab b) then if Z.eqb (fl_E a) (fl_E b) then if list_eqb fent_eqb (fl_ex a) (fl_ex b) then
  if list_eqb iiz_eqb (fl_ord a) (fl_ord b) then list_eqb izz_eqb (fl_res a) (fl_res b)
  else false else false else false else false else false else false else false else false else false.
Lemma fledger3_eqb_ok a b : fledger3_eqb a b = true -> a = b.
Proof.
  destruct a as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10], b as [b1 b2 b3 b4 b5 b6 b7 b8 b9 b10]. unfold fledger3_eqb.
  cbn [fl3 fl_all fl_ops fl_lazy fl_allow fl_Ab fl_E fl_ex fl_ord fl_res]. intros H.
  destruct (fledger_eqb a1 b1) eqn:E1; [|discriminate]. destruct (list_eqb fent_eqb a2 b2) eqn:E2; [|discriminate].
  destruct (list_eqb vop_eqb a3 b3) eqn:E3; [|discriminate]. destruct (list_eqb fent_eqb a4 b4) eqn:E4; [|discriminate].
  destruct (list_eqb fent_eqb a5 b5) eqn:E5; [|discriminate]. destruct (Z.eqb a6 b6) eqn:E6; [|discriminate].
  destruct (Z.eqb a7 b7) eqn:E7; [|discriminate]. destruct (list_eqb fent_eqb a8 b8) eqn:E8; [|discriminate].
  destruct (list_eqb iiz_eqb a9 b9) eqn:E9; [|discriminate].
  apply fledger_eqb_ok in E1. apply (list_eqb_ok fent_eqb fent_eqb_eq) in E2, E4, E5, E8. apply (list_eqb_ok vop_eqb vop_eqb_ok) in E3.
  apply Z.eqb_eq in E6, E7. apply (list_eqb_ok iiz_eqb iiz_eqb_ok) in E9. apply (list_eqb_ok izz_eqb izz_eqb_ok) in H.
  subst. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lkey : Type := (fstate * fledger3 * int)%type.
Definition lkey_eqb (a b : lkey) : bool :=
  if (snd a =? snd b)%uint63 then if fledger3_eqb (snd (fst a)) (snd (fst b)) then fstate_eqb (fst (fst a)) (fst (fst b)) else false else false.
Lemma lkey_eqb_ok a b : lkey_eqb a b = true -> a = b.
Proof.
  destruct a as [[F L] n], b as [[F' L'] n']. unfold lkey_eqb. cbn [fst snd]. intros H.
  destruct (n =? n')%uint63 eqn:E1; [|discriminate]. destruct (fledger3_eqb L L') eqn:E2; [|discriminate].
  apply int_eqb_ok in E1. apply fledger3_eqb_ok in E2. apply fstate_eqb_ok in H. subst. reflexivity.
Qed.
