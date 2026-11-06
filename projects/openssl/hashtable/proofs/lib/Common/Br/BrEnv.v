(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3Sound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma br_u64 (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range _ w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.

Lemma br_lit_small z : 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). exact H. Qed.

(* [comment removed for export] *)
Lemma br_eqm_small a b : AX2S.eqm a b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof. intros [q H] Ha Hb. assert (q = 0) by nia. subst q. lia. Qed.

Lemma br_eqm_word (x : word) z : AX2S.eqm (bv_unsigned x) z -> x = Z_to_bv 64 z.
Proof.
  intros H. rewrite <- (Z_to_bv_bv_unsigned _ x) at 1. apply AX2S.eqm_Z_to_bv. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive vdef : Type :=
| VVal (v : fval)
| VDiv (t : int) (c d m : Z)
| VExt.

Definition vtab : Type := list (nat * vdef).

Fixpoint vt_get (VT : vtab) (x : nat) : option vdef :=
  match VT with
  | [] => None
  | (y, d) :: r => if Nat.eqb x y then Some d else vt_get r x
  end.

(* [comment removed for export] *)
Definition digit (z d m : Z) : Z := (if m =? 0 then z else z mod m) / d.

Section Env.
Variable rho : int -> word.
Variable xv : nat -> word.
Variable xb : nat -> list byte.
Variable VT : vtab.

Definition vden (x : nat) (d : vdef) : word :=
  match d with
  | VVal v => dv rho v
  | VDiv t c d m => Z_to_bv 64 (digit (bv_unsigned (rho t) + c) d m)
  | VExt => xv x
  end.

Definition env_of : AX2.env :=
  AX2.Env (fun x => match vt_get VT x with Some d => vden x d | None => xv x end) xb.

Lemma ev_env_of x : AX2.ev env_of x = match vt_get VT x with Some d => vden x d | None => xv x end.
Proof. reflexivity. Qed.

Lemma eb_env_of k : AX2.eb env_of k = xb k.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition var_is_tag (x : nat) (t : int) : bool :=
  match vt_get VT x with
  | Some (VDiv t' c d m) => (t' =? t)%uint63 && (c =? 0) && (d =? 1) && (m =? 0)
  | _ => false
  end.

Lemma var_is_tag_sound x t : var_is_tag x t = true -> AX2.ev env_of x = rho t.
Proof.
  unfold var_is_tag. intros H. rewrite ev_env_of.
  destruct (vt_get VT x) as [[|t' c d m|]|]; try discriminate.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Uint63.eqb_spec in H1. apply Z.eqb_eq in H2, H3, H4. subst t' c d m.
  cbn [vden]. unfold digit. cbn [Z.eqb]. rewrite Z.add_0_r, Z.div_1_r. apply Z_to_bv_bv_unsigned.
Qed.

Definition var_is_ext (x : nat) : bool :=
  match vt_get VT x with None | Some VExt => true | _ => false end.

Lemma var_is_ext_sound x : var_is_ext x = true -> AX2.ev env_of x = xv x.
Proof.
  unfold var_is_ext. intros H. rewrite ev_env_of. destruct (vt_get VT x) as [[| |]|]; try discriminate; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record tdesc : Type := TD { td_c : Z; td_digits : list (Z * nat) }.
Definition ttab : Type := list (int * tdesc).

Fixpoint tl_get (TL : ttab) (t : int) : option tdesc :=
  match TL with
  | [] => None
  | (t', d) :: r => if (t' =? t)%uint63 then Some d else tl_get r t
  end.

Definition vdef_is_div (o : option vdef) (t : int) (c d m : Z) : bool :=
  match o with
  | Some (VDiv t' c' d' m') => (t' =? t)%uint63 && (c' =? c) && (d' =? d) && (m' =? m)
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint chain_ok (t : int) (c m : Z) (ds : list (Z * nat)) : bool :=
  match ds with
  | [] => false
  | (d, x) :: rest =>
      vdef_is_div (vt_get VT x) t c d m && (0 <? d) && ((m =? 0) || ((0 <? m) && (m mod d =? 0)))
      && match rest with [] => true | _ => chain_ok t c d rest end
  end.

Fixpoint last_div (ds : list (Z * nat)) : Z :=
  match ds with
  | [] => 1
  | [(d, _)] => d
  | _ :: rest => last_div rest
  end.

(* [comment removed for export] *)
Definition align_ok (M : itrie region) (t : int) (c d : Z) : bool :=
  (d =? 1)
  || match iget t M with
     | Some rg => (to_Z (rg_align rg) <=? 62) && ((2 ^ to_Z (rg_align rg)) mod d =? 0) && (c mod d =? 0)
     | None => false
     end.

Definition td_ok (M : itrie region) (t : int) (td : tdesc) : bool :=
  (0 <=? td_c td) && (td_c td <? 2 ^ 62)
  && ((td_c td =? 0) || match iget t M with Some _ => true | None => false end)
  && chain_ok t (td_c td) 0 (td_digits td)
  && align_ok M t (td_c td) (last_div (td_digits td)).

Definition tag_terms (ds : list (Z * nat)) : list (Z * AX2.expr) :=
  fold_right (fun dx acc => AX2.lins (fst dx) (AX2.EVar (snd dx)) acc) [] ds.

Definition tag_lin (td : tdesc) : AX2.lin := (AX2.snorm (- td_c td), tag_terms (td_digits td)).

(* [comment removed for export] *)
Fixpoint dsum (z m : Z) (ds : list (Z * nat)) : Z :=
  match ds with
  | [] => 0
  | (d, _) :: rest => d * digit z d m + dsum z d rest
  end.

Lemma digit_range z d m : 0 <= z -> 0 < d -> 0 <= m -> 0 <= digit z d m <= z.
Proof.
  intros Hz Hd Hm. unfold digit. destruct (m =? 0) eqn:Em.
  - split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia.
  - apply Z.eqb_neq in Em. assert (H : 0 < m) by lia. pose proof (Z.mod_pos_bound z m H) as B.
    split; [apply Z.div_pos; lia|].
    apply Z.div_le_upper_bound; [lia|]. pose proof (Z.mod_le z m Hz H). nia.
Qed.


(* [comment removed for export] *)
Lemma dsum_chain : forall ds z m,
  0 <= z -> 0 <= m ->
  (forall t c, chain_ok t c m ds = true -> z mod last_div ds = 0 ->
     dsum z m ds = if m =? 0 then z else z mod m).
Proof.
  induction ds as [|[d x] rest IH]; intros z m Hz Hm t c Hc Hal; [discriminate|].
  cbn [chain_ok] in Hc. apply andb_prop in Hc as [Hc Hrest]. apply andb_prop in Hc as [Hc Hmd].
  apply andb_prop in Hc as [_ Hd]. apply Z.ltb_lt in Hd.
  set (zm := if m =? 0 then z else z mod m).
  assert (Hzm : zm mod d = z mod d).
  { unfold zm. destruct (m =? 0) eqn:Em; [reflexivity|].
    apply orb_prop in Hmd as [Hmd|Hmd]; [congruence|].
    apply andb_prop in Hmd as [Hm0 Hmd]. apply Z.ltb_lt in Hm0. apply Z.eqb_eq in Hmd.
    apply Z.mod_divide in Hmd; [|lia]. apply Z.mod_mod_divide. exact Hmd. }
  cbn [dsum]. fold zm. unfold digit. fold zm.
  destruct rest as [|p rest'].
  - cbn [dsum last_div] in *. rewrite <- Hzm in Hal.
    pose proof (Z.div_mod zm d ltac:(lia)). lia.
  - assert (Hl : last_div ((d, x) :: p :: rest') = last_div (p :: rest')) by reflexivity.
    rewrite Hl in Hal.
    rewrite (IH z d Hz ltac:(lia) t c Hrest Hal).
    assert (Ed : (d =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Ed.
    rewrite <- Hzm. pose proof (Z.div_mod zm d ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma chain_tden : forall ds t c m z,
  chain_ok t c m ds = true -> z = bv_unsigned (rho t) + c -> 0 <= z < 2 ^ 64 -> 0 <= m ->
  AX2S.eqm (AX2S.tden env_of (tag_terms ds)) (dsum z m ds).
Proof.
  induction ds as [|[d x] rest IH]; intros t c m z Hc Ez Hz Hm; [discriminate|].
  cbn [chain_ok] in Hc. apply andb_prop in Hc as [Hc Hrest]. apply andb_prop in Hc as [Hc Hmd].
  apply andb_prop in Hc as [Hv Hd]. apply Z.ltb_lt in Hd.
  unfold vdef_is_div in Hv. destruct (vt_get VT x) as [[v|t' c' d' m'|]|] eqn:Ex; try discriminate.
  apply andb_prop in Hv as [Hv E4]. apply andb_prop in Hv as [Hv E3]. apply andb_prop in Hv as [E1 E2].
  apply Uint63.eqb_spec in E1. apply Z.eqb_eq in E2, E3, E4. subst t' c' d' m'.
  cbn [tag_terms fold_right fst snd dsum].
  eapply AX2S.eqm_trans; [apply AX2S.lins_sound|].
  apply AX2S.eqm_add.
  - unfold AX2S.uE. cbn [AX2.edenot]. rewrite ev_env_of, Ex. cbn [vden]. rewrite <- Ez.
    rewrite br_lit_small; [apply AX2S.eqm_refl|].
    pose proof (digit_range z d m ltac:(lia) Hd Hm). lia.
  - destruct rest as [|p rest']; [cbn; apply AX2S.eqm_refl|].
    exact (IH t c d z Hrest Ez Hz ltac:(lia)).
Qed.

Section TagLin.
Variable M : itrie region.
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.

Lemma td_ok_z t td :
  td_ok M t td = true ->
  0 <= bv_unsigned (rho t) + td_c td < 2 ^ 64
  /\ (bv_unsigned (rho t) + td_c td) mod last_div (td_digits td) = 0.
Proof.
  intros H. unfold td_ok in H. apply andb_prop in H as [H Hal]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H Hreg]. apply andb_prop in H as [Hc0 Hc1].
  apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc1. pose proof (br_u64 (rho t)) as Hr.
  split.
  - apply orb_prop in Hreg as [Hreg|Hreg]; [apply Z.eqb_eq in Hreg; lia|].
    destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
    destruct (HM t rg Hg) as (_ & _ & Hb & _). pose proof (i63_range (rg_len rg)). lia.
  - unfold align_ok in Hal. apply orb_prop in Hal as [Hal|Hal].
    + apply Z.eqb_eq in Hal. rewrite Hal. apply Z.mod_1_r.
    + destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
      apply andb_prop in Hal as [Hal Hcd]. apply andb_prop in Hal as [Ha62 Hpd].
      apply Z.leb_le in Ha62. apply Z.eqb_eq in Hpd, Hcd.
      destruct (HM t rg Hg) as (_ & _ & _ & _ & Hmod & _).
      set (d := last_div (td_digits td)) in *.
      destruct (Z.eq_dec d 0) as [E0|E0].
      { rewrite E0. rewrite Z.mod_0_r. rewrite E0, Z.mod_0_r in Hcd, Hpd.
        pose proof (i63_range (rg_align rg)).
        assert (0 < 2 ^ to_Z (rg_align rg)) by (apply Z.pow_pos_nonneg; lia). lia. }
      apply Z.mod_divide in Hpd; [|exact E0]. apply Z.mod_divide in Hcd; [|exact E0].
      assert (Hp0 : 2 ^ to_Z (rg_align rg) <> 0).
      { pose proof (i63_range (rg_align rg)). assert (0 < 2 ^ to_Z (rg_align rg)) by (apply Z.pow_pos_nonneg; lia). lia. }
      apply Z.mod_divide in Hmod; [|exact Hp0].
      apply Z.mod_divide; [exact E0|]. apply Z.divide_add_r; [|exact Hcd].
      exact (Z.divide_trans _ _ _ Hpd Hmod).
Qed.

Theorem tag_lin_sound t td :
  td_ok M t td = true -> AX2S.eqm (AX2S.lden env_of (tag_lin td)) (bv_unsigned (rho t)).
Proof.
  intros H. destruct (td_ok_z t td H) as [Hz Hal].
  pose proof H as H'. unfold td_ok in H'. apply andb_prop in H' as [H' _]. apply andb_prop in H' as [_ Hch].
  unfold AX2S.lden, tag_lin. cbn [fst snd].
  assert (H00 : 0 <= 0) by lia.
  pose proof (chain_tden (td_digits td) t (td_c td) 0 (bv_unsigned (rho t) + td_c td) Hch eq_refl Hz H00) as Ht.
  rewrite (dsum_chain (td_digits td) _ 0 (proj1 Hz) H00 t (td_c td) Hch Hal) in Ht.
  cbn [Z.eqb] in Ht.
  replace (bv_unsigned (rho t)) with (- td_c td + (bv_unsigned (rho t) + td_c td)) by lia.
  apply AX2S.eqm_add; [apply AX2S.eqm_snorm | exact Ht].
Qed.
End TagLin.


(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint terms_eqb (a b : list (Z * AX2.expr)) : bool :=
  match a, b with
  | [], [] => true
  | (k, e) :: a', (k', e') :: b' => (k =? k') && AX2.expr_eqb e e' && terms_eqb a' b'
  | _, _ => false
  end.

Lemma terms_eqb_eq : forall a b, terms_eqb a b = true -> a = b.
Proof.
  induction a as [|[k e] a IH]; intros [|[k' e'] b] H; try discriminate; [reflexivity|].
  cbn [terms_eqb] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply AX2S.expr_eqb_eq in H2. subst. f_equal. apply IH. exact H3.
Qed.

(* [comment removed for export] *)
Definition lin_match (le l : AX2.lin) (k : Z) : bool :=
  terms_eqb (snd le) (snd l) && (AX2.snorm (fst le - fst l - k) =? 0).

Lemma lin_match_sound E le l k :
  lin_match le l k = true -> AX2S.eqm (AX2S.lden E le) (AX2S.lden E l + k).
Proof.
  intros H. apply andb_prop in H as [H1 H2]. apply terms_eqb_eq in H1. apply Z.eqb_eq in H2.
  unfold AX2S.lden. rewrite H1. destruct (AX2S.eqm_snorm (fst le - fst l - k)) as [q Hq].
  rewrite H2 in Hq. exists (- q). lia.
Qed.

(* [comment removed for export] *)
Definition vt_const (x : nat) : option Z :=
  match vt_get VT x with
  | Some (VVal (FV t w)) => if (t =? 0)%uint63 then Some (wZ w) else None
  | _ => None
  end.

Fixpoint norm_terms (ts : list (Z * AX2.expr)) : Z * list (Z * AX2.expr) :=
  match ts with
  | [] => (0, [])
  | (k, a) :: rest =>
      let (c, r) := norm_terms rest in
      match a with
      | AX2.EVar x => match vt_const x with Some z => (k * z + c, r) | None => (c, (k, a) :: r) end
      | _ => (c, (k, a) :: r)
      end
  end.

Definition lin_norm (l : AX2.lin) : AX2.lin :=
  let (c, r) := norm_terms (snd l) in (AX2.snorm (fst l + c), r).

Lemma norm_terms_sound : rho 0%uint63 = Z_to_bv 64 0 -> forall ts,
  AX2S.tden env_of ts = fst (norm_terms ts) + AX2S.tden env_of (snd (norm_terms ts)).
Proof.
  intros Hrho0. induction ts as [|[k a] rest IH]; [reflexivity|].
  cbn [norm_terms]. destruct (norm_terms rest) as [c r] eqn:En. cbn [fst snd] in IH.
  assert (Hdef : AX2S.tden env_of ((k, a) :: rest) = c + AX2S.tden env_of ((k, a) :: r)).
  { cbn [AX2S.tden]. rewrite IH. lia. }
  destruct a as [z | x | | | | | |]; try exact Hdef.
  unfold vt_const. destruct (vt_get VT x) as [[[t w]| |]|] eqn:Ex; try exact Hdef.
  destruct (t =? 0)%uint63 eqn:Et; [|exact Hdef].
  apply Uint63.eqb_spec in Et. subst t. cbn [fst snd AX2S.tden]. rewrite IH.
  unfold AX2S.uE. cbn [AX2.edenot]. rewrite ev_env_of, Ex. cbn [vden].
  rewrite (fk_dv_conc rho w Hrho0), wbv_unsigned. lia.
Qed.

Lemma lin_norm_sound : rho 0%uint63 = Z_to_bv 64 0 -> forall l,
  AX2S.eqm (AX2S.lden env_of (lin_norm l)) (AX2S.lden env_of l).
Proof.
  intros Hrho0 l. unfold lin_norm, AX2S.lden. pose proof (norm_terms_sound Hrho0 (snd l)) as H.
  destruct (norm_terms (snd l)) as [c r]. cbn [fst snd] in *. rewrite H.
  destruct (AX2S.eqm_snorm (fst l + c)) as [q Hq]. exists q. lia.
Qed.

(* [comment removed for export] *)
Definition elin (e : AX2.expr) : AX2.lin := lin_norm (AX2.lin_of e).

Lemma elin_sound : rho 0%uint63 = Z_to_bv 64 0 -> forall e,
  AX2S.eqm (AX2S.lden env_of (elin e)) (AX2S.uE env_of e).
Proof.
  intros Hrho0 e. eapply AX2S.eqm_trans; [apply lin_norm_sound; exact Hrho0 | apply AX2S.lin_of_sound].
Qed.

(* [comment removed for export] *)
Definition teq : Type := (int * Z * list (Z * int))%type.

Fixpoint teq_sum (ts : list (Z * int)) : Z :=
  match ts with [] => 0 | (k, t) :: r => k * bv_unsigned (rho t) + teq_sum r end.

Definition teq_holds (q : teq) : Prop :=
  let '(t, c, ts) := q in AX2S.eqm (bv_unsigned (rho t)) (c + teq_sum ts).

Definition teq_ok (TEQ : list teq) : Prop := Forall teq_holds TEQ.

Fixpoint teq_get (TEQ : list teq) (t : int) : option (Z * list (Z * int)) :=
  match TEQ with
  | [] => None
  | (t', c, ts) :: r => if (t' =? t)%uint63 then Some (c, ts) else teq_get r t
  end.

Lemma teq_get_sound : forall TEQ t c ts, teq_ok TEQ -> teq_get TEQ t = Some (c, ts) ->
  AX2S.eqm (bv_unsigned (rho t)) (c + teq_sum ts).
Proof.
  induction TEQ as [|[[t' c'] ts'] r IH]; intros t c ts Hok Hg; [discriminate|].
  cbn [teq_get] in Hg. pose proof (Forall_inv Hok) as Hh. pose proof (Forall_inv_tail Hok) as Hr.
  destruct (t' =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t'. injection Hg as <- <-. exact Hh.
  - exact (IH t c ts Hr Hg).
Qed.

Section Tags.
Variable M : itrie region.
Variable TL : ttab.
Variable XT : list (int * AX2.lin).   (* [comment removed for export] *)
Variable TEQ : list teq.
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

Definition tl_ok : bool := forallb (fun p => td_ok M (fst p) (snd p)) TL.
Hypothesis HTL : tl_ok = true.
Definition xt_ok : Prop := Forall (fun p => AX2S.eqm (AX2S.lden env_of (snd p)) (bv_unsigned (rho (fst p)))) XT.
Hypothesis HXT : xt_ok.
Hypothesis HTEQ : teq_ok TEQ.

Lemma tl_get_In : forall t td, tl_get TL t = Some td -> In (t, td) TL.
Proof.
  induction TL as [|[t' d] r IH]; intros t td H; [discriminate|]. cbn [tl_get] in H.
  destruct (t' =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. injection H as <-. subst t'. left. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma tl_In_ok t td : In (t, td) TL -> td_ok M t td = true.
Proof. intros H. unfold tl_ok in HTL. rewrite forallb_forall in HTL. exact (HTL (t, td) H). Qed.

(* [comment removed for export] *)
Definition all_lins : list (int * AX2.lin) := map (fun p => (fst p, tag_lin (snd p))) TL ++ XT.

Lemma all_lins_sound : Forall (fun p => AX2S.eqm (AX2S.lden env_of (snd p)) (bv_unsigned (rho (fst p)))) all_lins.
Proof.
  unfold all_lins. apply Forall_app. split; [|exact HXT].
  apply Forall_forall. intros p Hp. apply in_map_iff in Hp as ([t td] & <- & Hin). cbn [fst snd].
  exact (tag_lin_sound M HM t td (tl_In_ok t td Hin)).
Qed.

Fixpoint lin_get (ls : list (int * AX2.lin)) (t : int) : option AX2.lin :=
  match ls with
  | [] => None
  | (t', l) :: r => if (t' =? t)%uint63 then Some l else lin_get r t
  end.

Lemma lin_get_In : forall ls t l, lin_get ls t = Some l -> In (t, l) ls.
Proof.
  induction ls as [|[t' l'] r IH]; intros t l H; [discriminate|]. cbn [lin_get] in H.
  destruct (t' =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. injection H as <-. subst t'. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Definition tl_lin0 (t : int) : option AX2.lin :=
  if (t =? 0)%uint63 then Some (0, []) else lin_get all_lins t.

Lemma tl_lin0_sound t l : tl_lin0 t = Some l -> AX2S.eqm (AX2S.lden env_of l) (bv_unsigned (rho t)).
Proof.
  unfold tl_lin0. destruct (t =? 0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t. intros H. injection H as <-. rewrite Hrho0.
    cbn. apply AX2S.eqm_refl.
  - intros H. apply lin_get_In in H.
    exact (proj1 (Forall_forall _ _) all_lins_sound (t, l) H).
Qed.

(* [comment removed for export] *)
Fixpoint teq_lin (ts : list (Z * int)) (acc : AX2.lin) : option AX2.lin :=
  match ts with
  | [] => Some acc
  | (k, t) :: r =>
      match tl_lin0 t with
      | Some l => teq_lin r (AX2.ladd acc (AX2.lscale k l))
      | None => None
      end
  end.

Lemma teq_lin_sound : forall ts acc l, teq_lin ts acc = Some l ->
  AX2S.eqm (AX2S.lden env_of l) (AX2S.lden env_of acc + teq_sum ts).
Proof.
  induction ts as [|[k t] r IH]; intros acc l H; cbn [teq_lin teq_sum] in *.
  - injection H as <-. rewrite Z.add_0_r. apply AX2S.eqm_refl.
  - destruct (tl_lin0 t) as [lt|] eqn:Hl; [|discriminate].
    eapply AX2S.eqm_trans; [exact (IH _ _ H)|].
    replace (AX2S.lden env_of acc + (k * bv_unsigned (rho t) + teq_sum r))
      with ((AX2S.lden env_of acc + k * bv_unsigned (rho t)) + teq_sum r) by lia.
    apply AX2S.eqm_add; [|apply AX2S.eqm_refl].
    eapply AX2S.eqm_trans; [apply AX2S.ladd_sound|]. apply AX2S.eqm_add; [apply AX2S.eqm_refl|].
    eapply AX2S.eqm_trans; [apply AX2S.lscale_sound|]. apply AX2S.eqm_mul_l. exact (tl_lin0_sound t lt Hl).
Qed.

Definition tl_lin (t : int) : option AX2.lin :=
  match tl_lin0 t with
  | Some l => Some l
  | None => match teq_get TEQ t with
            | Some (c, ts) => teq_lin ts (AX2.snorm c, [])
            | None => None
            end
  end.

Lemma tl_lin_sound t l : tl_lin t = Some l -> AX2S.eqm (AX2S.lden env_of l) (bv_unsigned (rho t)).
Proof.
  unfold tl_lin. destruct (tl_lin0 t) as [l0|] eqn:H0.
  - intros H. injection H as <-. exact (tl_lin0_sound t l0 H0).
  - destruct (teq_get TEQ t) as [[c ts]|] eqn:Hq; [|discriminate]. intros H.
    eapply AX2S.eqm_trans; [exact (teq_lin_sound ts _ l H)|].
    apply AX2S.eqm_sym. eapply AX2S.eqm_trans; [exact (teq_get_sound TEQ t c ts HTEQ Hq)|].
    apply AX2S.eqm_add; [|apply AX2S.eqm_refl]. unfold AX2S.lden. cbn [fst snd AX2S.tden].
    rewrite Z.add_0_r. apply AX2S.eqm_sym. apply AX2S.eqm_snorm.
Qed.

Definition val_match (e : AX2.expr) (v : fval) : bool :=
  (is_plain (vtag v) &&
     match tl_lin (vtag v) with
     | Some l => lin_match (elin e) l (wZ (vw v))
     | None => false
     end)
  || match e with
     | AX2.EVar x => match vt_get VT x with Some (VVal v') => fv_eqb v' v | _ => false end
     | _ => false
     end.

Lemma fv_eqb_dv a b : fv_eqb a b = true -> dv rho a = dv rho b.
Proof.
  destruct a as [ta wa], b as [tb wb]. unfold fv_eqb. cbn [vtag vw]. intros H.
  apply andb_prop in H as [H1 H2]. apply Uint63.eqb_spec in H1. subst tb.
  apply w_eqb_true_bv in H2. unfold dv. cbn [vtag vw]. rewrite H2. reflexivity.
Qed.

Lemma is_plain_lt60 t : is_plain t = true -> to_Z t < 2 ^ 60.
Proof. unfold is_plain. rewrite Uint63.ltb_spec, fk_kind_lim. tauto. Qed.

Theorem val_match_sound e v : val_match e v = true -> AX2.edenot env_of e = dv rho v.
Proof.
  unfold val_match. intros H. apply orb_prop in H as [H|H].
  - apply andb_prop in H as [Hpl H]. destruct (tl_lin (vtag v)) as [l|] eqn:Hl; [|discriminate].
    rewrite (fk_dv_plain rho v (is_plain_lt60 _ Hpl)).
    apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned.
    pose proof (elin_sound Hrho0 e) as H1.
    pose proof (lin_match_sound env_of _ _ _ H) as H2.
    pose proof (tl_lin_sound _ _ Hl) as H3.
    assert (H4 : AX2S.eqm (AX2S.uE env_of e) (bv_unsigned (rho (vtag v)) + wZ (vw v))).
    { eapply AX2S.eqm_trans; [apply AX2S.eqm_sym; exact H1|].
      eapply AX2S.eqm_trans; [exact H2|]. apply AX2S.eqm_add; [exact H3 | apply AX2S.eqm_refl]. }
    unfold AX2S.uE in H4. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply br_eqm_small.
    + eapply AX2S.eqm_trans; [exact H4|]. apply AX2S.eqm_sym. apply AX2S.eqm_mod.
    + apply br_u64.
    + apply Z.mod_pos_bound. lia.
  - destruct e as [| x | | | | | |]; try discriminate.
    destruct (vt_get VT x) as [[v'| |]|] eqn:Ex; try discriminate.
    cbn [AX2.edenot]. rewrite ev_env_of, Ex. cbn [vden]. apply fv_eqb_dv. exact H.
Qed.

(* [comment removed for export] *)
Definition find_tag (ts : list (Z * AX2.expr)) : option (int * AX2.lin) :=
  List.find (fun p => terms_eqb ts (snd (snd p))) all_lins.

(* [comment removed for export] *)
Definition aview0 (a : AX2.saddr) : option (int * Z) :=
  let l := elin (AX2.a_base a) in
  match snd l with
  | [] => let c0 := AX2.snorm (fst l) in
          if (0 <=? c0) then Some (0%uint63, c0 + AX2.a_off a) else None
  | ts =>
      match find_tag ts with
      | Some (t, lt) =>
          let delta := AX2.snorm (fst l - fst lt) in
          match iget t M with
          | Some rg => if (0 <=? delta) && (delta <=? to_Z (rg_len rg))
                       then Some (t, delta + AX2.a_off a) else None
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition strict_tag (c off : Z) (ts : list (Z * AX2.expr)) : option (int * AX2.lin) :=
  List.find (fun p => terms_eqb ts (snd (snd p))
                      && match iget (fst p) M with
                         | Some rg => let delta := AX2.snorm (c - fst (snd p)) in
                                      (0 <=? delta) && (delta <=? to_Z (rg_len rg))
                                      && (to_Z (rg_lo rg) <=? delta + off) && (delta + off <=? to_Z (rg_len rg))
                         | None => false
                         end) all_lins.

Definition aview (a : AX2.saddr) : option (int * Z) :=
  let l := elin (AX2.a_base a) in
  match strict_tag (fst l) (AX2.a_off a) (snd l) with
  | Some (t, lt) => Some (t, AX2.snorm (fst l - fst lt) + AX2.a_off a)
  | None => aview0 a
  end.

Lemma snorm_range k : - 2 ^ 63 <= AX2.snorm k < 2 ^ 63.
Proof.
  rewrite AX2.snorm_eq. unfold AX2.snorm_ref, AX2.two64z.
  pose proof (Z.mod_pos_bound k (2 ^ 64) ltac:(lia)).
  destruct (Z.leb_spec (2 ^ 63) (k mod 2 ^ 64)); lia.
Qed.

Theorem aview0_sound a t o :
  aview0 a = Some (t, o) -> AX2S.estart env_of a = bv_unsigned (rho t) + o.
Proof.
  unfold aview0, AX2S.estart. intros H.
  pose proof (elin_sound Hrho0 (AX2.a_base a)) as Hl. unfold AX2S.lden, AX2S.uE in Hl.
  pose proof (br_u64 (AX2.edenot env_of (AX2.a_base a))) as Hu.
  destruct (snd (elin (AX2.a_base a))) as [|p ts] eqn:Ets.
  - set (c0 := AX2.snorm (fst (elin (AX2.a_base a)))) in *.
    destruct (0 <=? c0) eqn:E0; [|discriminate].
    apply Z.leb_le in E0. injection H as <- <-. rewrite Hrho0. cbn [AX2S.tden] in Hl.
    change (bv_unsigned (Z_to_bv 64 0)) with 0.
    pose proof (snorm_range (fst (elin (AX2.a_base a)))) as Hr. fold c0 in Hr.
    assert (E : bv_unsigned (AX2.edenot env_of (AX2.a_base a)) = c0).
    { apply br_eqm_small; [|exact Hu|lia].
      apply AX2S.eqm_sym. eapply AX2S.eqm_trans; [|exact Hl].
      rewrite Z.add_0_r. apply AX2S.eqm_snorm. }
    lia.
  - destruct (find_tag (p :: ts)) as [[t' lt]|] eqn:Hf; [|discriminate].
    unfold find_tag in Hf. apply List.find_some in Hf as [Hin Hte]. cbn [snd] in Hte.
    apply terms_eqb_eq in Hte.
    destruct (iget t' M) as [rg|] eqn:Hg; [|discriminate].
    set (delta := AX2.snorm (fst (elin (AX2.a_base a)) - fst lt)) in *.
    destruct ((0 <=? delta) && (delta <=? to_Z (rg_len rg))) eqn:Ed; [|discriminate].
    apply andb_prop in Ed as [Ed0 Ed1]. apply Z.leb_le in Ed0, Ed1.
    injection H as <- <-.
    pose proof (proj1 (Forall_forall _ _) all_lins_sound (t', lt) Hin) as Ht.
    unfold AX2S.lden in Ht. cbn [fst snd] in Ht. rewrite <- Hte in Ht.
    destruct (HM t' rg Hg) as (_ & _ & Hb & _).
    pose proof (br_u64 (rho t')) as Hrt.
    assert (E : bv_unsigned (AX2.edenot env_of (AX2.a_base a)) = bv_unsigned (rho t') + delta).
    { apply br_eqm_small; [|exact Hu|lia].
      apply AX2S.eqm_sym. eapply AX2S.eqm_trans; [|exact Hl].
      destruct Ht as [q Hq].
      destruct (AX2S.eqm_snorm (fst (elin (AX2.a_base a)) - fst lt)) as [q2 Hq2]. fold delta in Hq2.
      exists (q2 - q). lia. }
    lia.
Qed.

Theorem aview_sound a t o :
  aview a = Some (t, o) -> AX2S.estart env_of a = bv_unsigned (rho t) + o.
Proof.
  unfold aview. destruct (strict_tag (fst (elin (AX2.a_base a))) (AX2.a_off a) (snd (elin (AX2.a_base a)))) as [[t' lt]|] eqn:Hf;
    [|exact (aview0_sound a t o)].
  intros Hq. injection Hq as <- <-. unfold AX2S.estart.
  unfold strict_tag in Hf. apply List.find_some in Hf as [Hin Hc]. cbn [fst snd] in Hc.
  apply andb_prop in Hc as [Hte Hb]. apply terms_eqb_eq in Hte.
  destruct (iget t' M) as [rg|] eqn:Hg; [|discriminate].
  set (delta := AX2.snorm (fst (elin (AX2.a_base a)) - fst lt)) in *.
  apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Ed0 Ed1]. apply Z.leb_le in Ed0, Ed1.
  pose proof (elin_sound Hrho0 (AX2.a_base a)) as Hl. unfold AX2S.lden, AX2S.uE in Hl.
  pose proof (br_u64 (AX2.edenot env_of (AX2.a_base a))) as Hu.
  pose proof (proj1 (Forall_forall _ _) all_lins_sound (t', lt) Hin) as Ht.
  unfold AX2S.lden in Ht. cbn [fst snd] in Ht. rewrite <- Hte in Ht.
  destruct (HM t' rg Hg) as (_ & _ & Hb63 & _).
  pose proof (br_u64 (rho t')) as Hrt.
  assert (E : bv_unsigned (AX2.edenot env_of (AX2.a_base a)) = bv_unsigned (rho t') + delta).
  { apply br_eqm_small; [|exact Hu|lia].
    apply AX2S.eqm_sym. eapply AX2S.eqm_trans; [|exact Hl].
    destruct Ht as [q Hq].
    destruct (AX2S.eqm_snorm (fst (elin (AX2.a_base a)) - fst lt)) as [q2 Hq2]. fold delta in Hq2.
    exists (q2 - q). lia. }
  lia.
Qed.

End Tags.
End Env.
