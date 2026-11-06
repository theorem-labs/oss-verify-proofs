(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State Step ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model OpsBridge PkOps GLib.
Import ListNotations.
Import W64 Val Mem St Step ValP MemP UB HeapOp UG PK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkU.

Definition BASE_F : int := 4611686018427387904%uint63.
Definition BASE_N : int := 4683743612465315840%uint63.
Definition UMAX : w64 := wlit 2199023255552%uint63.
Lemma BASE_F_val : to_Z BASE_F = PKU_BASE. Proof. reflexivity. Qed.
Lemma BASE_N_val : to_Z BASE_N = PKU_BASE + PKU_ST. Proof. reflexivity. Qed.

Definition pku_of (fs : list fact) (w : sv * sv * sv) : option (bool * int) :=
  match w with
  | (VP u off, VL z, VL k) =>
      if weqb z wzero && weqb k wzero
         && match find_range fs u with Some (_, hi) => wleu hi UMAX | None => false end
      then if weqb off (wlit BASE_F) then Some (true, u) else if weqb off (wlit BASE_N) then Some (false, u) else None
      else None
  | _ => None
  end.

Definition TOPW : w64 := wlit 4683748010511826944%uint63.
Definition not_pku (fs : list fact) (w : sv * sv * sv) : bool :=
  match w with
  | (lo, len, kd) =>
      if match kd with VL k => negb (weqb k wzero) | _ => false end then true
      else if match len with VL z => negb (weqb z wzero) | _ => false end then true
      else match lo with
           | VL a => wltu a (wlit BASE_F)
           | _ => let '(l, h) := sv_bounds fs lo in if wltu h (wlit BASE_F) then true else wltu TOPW l
           end
  end.

Fixpoint scan (fs : list fact) (ws : list (sv * sv * sv)) : option (option (list (sv * sv * sv) * (bool * int) * list (sv * sv * sv))) :=
  match ws with
  | [] => Some None
  | w :: ws' =>
      if not_pku fs w then
        match scan fs ws' with
        | Some None => Some None
        | Some (Some (pre, x, post)) => Some (Some (w :: pre, x, post))
        | None => None
        end
      else match pku_of fs w with
           | Some x => if forallb (not_pku fs) ws' then Some (Some ([], x, ws')) else None
           | None => None
           end
  end.
Definition mk_pku (fr : bool) (u : int) : sv * sv * sv := (VP u (wlit (if fr then BASE_F else BASE_N)), VL wzero, VL wzero).

Definition pku_flip (fs : list fact) (ok : bool -> bool) (fr' : bool) (ws : list (sv * sv * sv)) : option (list (sv * sv * sv)) :=
  match scan fs ws with
  | Some None => Some ws
  | Some (Some (pre, (fr, u), post)) => if ok fr then Some (pre ++ mk_pku fr' u :: post) else None
  | None => None
  end.

Definition pku_move (fs : list fact) (ok : bool -> bool) (fr' : bool) (u' : int) (ws : list (sv * sv * sv)) : option (option int * list (sv * sv * sv)) :=
  match scan fs ws with
  | Some None => Some (None, ws)
  | Some (Some (pre, (fr, u), post)) => if ok fr then Some (Some u, pre ++ mk_pku fr' u' :: post) else None
  | None => None
  end.

Definition pku_drop (fs : list fact) (ws : list (sv * sv * sv)) : option (list (sv * sv * sv)) :=
  match scan fs ws with
  | Some None => Some ws
  | Some (Some (pre, _, post)) => Some (pre ++ post)
  | None => None
  end.

Section Sem.
Variable E : env.
Variable fs : list fact.
Hypothesis Hfs : facts_hold E fs.

Lemma w2Z_wlit_small : forall i, to_Z i < 2 ^ 63 -> w2Z (wlit i) = to_Z i.
Proof. intros i H. apply wlit_ok. Qed.

Lemma not_pku_sound : forall w, not_pku fs w = true -> pku_val (wden E w) = None.
Proof.
  intros [[lo len] kd] H. unfold not_pku in H. unfold pku_val. cbn [wden w_kind w_len w_lo].
  destruct (match kd with VL k => negb (weqb k wzero) | _ => false end) eqn:HK.
  { destruct kd as [k| | | | | | | | | |]; try discriminate. apply negb_true_iff in HK.
    destruct (Z.eqb_spec (bv_unsigned (den E (VL k))) 0) as [X|_]; [| reflexivity]. exfalso.
    rewrite den_VL in X. assert (k = wzero) by (apply w2Z_inj; rewrite X; reflexivity). subst k. rewrite weqb_refl in HK. discriminate. }
  destruct (match len with VL z => negb (weqb z wzero) | _ => false end) eqn:HL.
  { destruct len as [z| | | | | | | | | |]; try discriminate. apply negb_true_iff in HL.
    destruct (Z.eqb_spec (bv_unsigned (den E (VL z))) 0) as [X|_]; [| rewrite andb_false_r; reflexivity]. exfalso.
    rewrite den_VL in X. assert (z = wzero) by (apply w2Z_inj; rewrite X; reflexivity). subst z. rewrite weqb_refl in HL. discriminate. }
  assert (OUT : bv_unsigned (den E lo) < PKU_BASE \/ PKU_BASE + PKU_ST + PKU_SPAN < bv_unsigned (den E lo)).
  { destruct lo as [a| | | | | | | | | |];
      try (pose proof (sv_bounds_sound E fs Hfs) as B;
           match type of H with (let '(l, h) := sv_bounds fs ?v in _) = true => specialize (B v); destruct (sv_bounds fs v) as [l h] end;
           unfold inb in B; cbn [fst snd] in B;
           destruct (wltu h (wlit BASE_F)) eqn:Q; [left; rewrite wltu_w2Z in Q; apply Z.ltb_lt in Q; rewrite wlit_ok, BASE_F_val in Q; lia|];
           right; rewrite wltu_w2Z in H; apply Z.ltb_lt in H; change (w2Z TOPW) with (PKU_BASE + PKU_ST + PKU_SPAN) in H; lia).
    left. rewrite wltu_w2Z in H. apply Z.ltb_lt in H. rewrite wlit_ok, BASE_F_val in H. rewrite den_VL. exact H. }
  destruct ((_ =? 0) && (_ =? 0)); [| reflexivity].
  assert (P : PKU_BASE + PKU_ST > PKU_BASE) by (unfold PKU_ST; lia). assert (P2 : PKU_SPAN > 0) by (unfold PKU_SPAN; lia).
  destruct OUT as [LT|GT].
  - destruct (Z.leb_spec PKU_BASE (bv_unsigned (den E lo))) as [X|_]; [lia|]. cbn [andb].
    destruct (Z.leb_spec (PKU_BASE + PKU_ST) (bv_unsigned (den E lo))) as [X|_]; [lia|]. reflexivity.
  - destruct (Z.ltb_spec (bv_unsigned (den E lo)) (PKU_BASE + PKU_SPAN)) as [X|_]; [lia|]. rewrite andb_false_r.
    destruct (Z.ltb_spec (bv_unsigned (den E lo)) (PKU_BASE + PKU_ST + PKU_SPAN)) as [X|_]; [lia|]. rewrite andb_false_r. reflexivity.
Qed.

Lemma pku_of_sound : forall w fr u, pku_of fs w = Some (fr, u) ->
  w = mk_pku fr u /\ bv_unsigned (ev E u) <= 2 ^ 41 /\
  pku_val (wden E w) = Some (fr, bv_unsigned (ev E u)).
Proof.
  intros [[lo len] kd] fr u H. unfold pku_of in H.
  destruct lo as [|u0 off| | | | | | | | |]; try discriminate. destruct len as [z| | | | | | | | | |]; try discriminate.
  destruct kd as [k| | | | | | | | | |]; try discriminate.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [| discriminate] end.
  apply andb_prop in C as [C RG]. apply andb_prop in C as [Z0 K0]. apply (proj1 (weqb_ok _ _)) in Z0. apply (proj1 (weqb_ok _ _)) in K0. subst z k.
  destruct (find_range fs u0) as [[lo hi]|] eqn:FR; [| discriminate]. rewrite wleu_w2Z in RG. apply Z.leb_le in RG.
  pose proof (find_range_sound_gen E fs Hfs u0 lo hi FR) as [_ HI].
  assert (UM : w2Z UMAX = 2 ^ 41) by reflexivity. rewrite UM in RG.
  pose proof (bv_unsigned_in_range _ (ev E u0)) as R0. rewrite bv_modulus_64 in R0.
  assert (T64 : two64 = 2 ^ 64) by reflexivity.
  assert (CASE : forall b, weqb off (wlit b) = true -> to_Z b = PKU_BASE \/ to_Z b = PKU_BASE + PKU_ST ->
            bv_unsigned (den E (VP u0 off)) = bv_unsigned (ev E u0) + to_Z b).
  { intros b Hb Vb. apply (proj1 (weqb_ok _ _)) in Hb. subst off. rewrite den_VPu, wlit_ok. apply Z.mod_small. unfold PKU_BASE, PKU_ST in Vb. lia. }
  destruct (weqb off (wlit BASE_F)) eqn:OF.
  - injection H as <- <-. split; [apply (proj1 (weqb_ok _ _)) in OF; subst off; reflexivity|]. split; [lia|].
    unfold pku_val. cbn [wden w_kind w_len w_lo]. rewrite !den_VL. change (w2Z wzero) with 0. cbn [Z.eqb andb].
    rewrite (CASE BASE_F OF (or_introl BASE_F_val)), BASE_F_val.
    destruct (Z.leb_spec PKU_BASE (bv_unsigned (ev E u0) + PKU_BASE)) as [_|X]; [| lia]. cbn [andb].
    destruct (Z.ltb_spec (bv_unsigned (ev E u0) + PKU_BASE) (PKU_BASE + PKU_SPAN)) as [_|X]; [| unfold PKU_SPAN in X; lia].
    f_equal. f_equal. lia.
  - destruct (weqb off (wlit BASE_N)) eqn:ON; [| discriminate]. injection H as <- <-.
    split; [apply (proj1 (weqb_ok _ _)) in ON; subst off; reflexivity|]. split; [lia|].
    unfold pku_val. cbn [wden w_kind w_len w_lo]. rewrite !den_VL. change (w2Z wzero) with 0. cbn [Z.eqb andb].
    rewrite (CASE BASE_N ON (or_intror BASE_N_val)), BASE_N_val.
    destruct (Z.leb_spec PKU_BASE (bv_unsigned (ev E u0) + (PKU_BASE + PKU_ST))) as [_|X]; [| unfold PKU_ST in X; lia]. cbn [andb].
    destruct (Z.ltb_spec (bv_unsigned (ev E u0) + (PKU_BASE + PKU_ST)) (PKU_BASE + PKU_SPAN)) as [X|_]; [unfold PKU_ST, PKU_SPAN in X; lia|].
    destruct (Z.leb_spec (PKU_BASE + PKU_ST) (bv_unsigned (ev E u0) + (PKU_BASE + PKU_ST))) as [_|X]; [| lia]. cbn [andb].
    destruct (Z.ltb_spec (bv_unsigned (ev E u0) + (PKU_BASE + PKU_ST)) (PKU_BASE + PKU_ST + PKU_SPAN)) as [_|X]; [| unfold PKU_SPAN in X; lia].
    f_equal. f_equal. lia.
Qed.

Lemma mk_pku_val : forall fr u, bv_unsigned (ev E u) <= 2 ^ 41 -> pku_val (wden E (mk_pku fr u)) = Some (fr, bv_unsigned (ev E u)).
Proof.
  intros fr u UB. pose proof (bv_unsigned_in_range _ (ev E u)) as R0. rewrite bv_modulus_64 in R0.
  unfold mk_pku, pku_val. cbn [wden w_kind w_len w_lo]. rewrite !den_VL. change (w2Z wzero) with 0. cbn [Z.eqb andb].
  rewrite den_VPu, wlit_ok. assert (T64 : two64 = 2 ^ 64) by reflexivity.
  destruct fr.
  - rewrite BASE_F_val, Z.mod_small by (unfold PKU_BASE; lia).
    destruct (Z.leb_spec PKU_BASE (bv_unsigned (ev E u) + PKU_BASE)) as [_|X]; [| lia]. cbn [andb].
    destruct (Z.ltb_spec (bv_unsigned (ev E u) + PKU_BASE) (PKU_BASE + PKU_SPAN)) as [_|X]; [| unfold PKU_SPAN in X; lia].
    f_equal. f_equal. lia.
  - rewrite BASE_N_val, Z.mod_small by (unfold PKU_BASE, PKU_ST; lia).
    destruct (Z.leb_spec PKU_BASE (bv_unsigned (ev E u) + (PKU_BASE + PKU_ST))) as [_|X]; [| unfold PKU_ST in X; lia]. cbn [andb].
    destruct (Z.ltb_spec (bv_unsigned (ev E u) + (PKU_BASE + PKU_ST)) (PKU_BASE + PKU_SPAN)) as [X|_]; [unfold PKU_ST, PKU_SPAN in X; lia|].
    destruct (Z.leb_spec (PKU_BASE + PKU_ST) (bv_unsigned (ev E u) + (PKU_BASE + PKU_ST))) as [_|X]; [| lia]. cbn [andb].
    destruct (Z.ltb_spec (bv_unsigned (ev E u) + (PKU_BASE + PKU_ST)) (PKU_BASE + PKU_ST + PKU_SPAN)) as [_|X]; [| unfold PKU_SPAN in X; lia].
    f_equal. f_equal. lia.
Qed.

Lemma forallb_not_pku : forall ws, forallb (not_pku fs) ws = true -> forall w, In w ws -> pku_val (wden E w) = None.
Proof. intros ws H w Hw. apply not_pku_sound. exact (proj1 (forallb_forall _ _) H w Hw). Qed.

Lemma scan_none : forall ws, scan fs ws = Some None -> forall w, In w ws -> pku_val (wden E w) = None.
Proof.
  induction ws as [|w0 ws IH]; intros H w Hw; [destruct Hw|]. cbn [scan] in H.
  destruct (not_pku fs w0) eqn:NP.
  - destruct (scan fs ws) as [[[[pre x] post]|]|]; try discriminate. destruct Hw as [<-|Hw]; [exact (not_pku_sound _ NP)| exact (IH eq_refl w Hw)].
  - destruct (pku_of fs w0); [destruct (forallb (not_pku fs) ws)|]; discriminate.
Qed.

Lemma scan_some : forall ws pre fr u post, scan fs ws = Some (Some (pre, (fr, u), post)) ->
  ws = pre ++ mk_pku fr u :: post /\ bv_unsigned (ev E u) <= 2 ^ 41 /\
  pku_val (wden E (mk_pku fr u)) = Some (fr, bv_unsigned (ev E u)) /\
  (forall w, In w (pre ++ post) -> pku_val (wden E w) = None).
Proof.
  induction ws as [|w0 ws IH]; intros pre fr u post H; [discriminate|]. cbn [scan] in H.
  destruct (not_pku fs w0) eqn:NP.
  - destruct (scan fs ws) as [[[[pre' x'] post']|]|] eqn:SC; try discriminate. injection H as E1 E2 E3. subst pre x' post.
    destruct (IH pre' fr u post' eq_refl) as (-> & UB & PV & NO). split; [reflexivity|]. split; [exact UB|]. split; [exact PV|].
    intros w [<-|Hw]; [exact (not_pku_sound _ NP)| exact (NO w Hw)].
  - destruct (pku_of fs w0) as [x|] eqn:PO; [| discriminate]. destruct (forallb (not_pku fs) ws) eqn:FA; [| discriminate]. injection H as E1 E2 E3. subst pre x post.
    destruct (pku_of_sound w0 fr u PO) as (-> & UB & PV). split; [reflexivity|]. split; [exact UB|]. split; [exact PV|].
    cbn [app]. exact (forallb_not_pku ws FA).
Qed.

Lemma pku_drop_spec : forall ws ws0, pku_drop fs ws = Some ws0 ->
  (forall x, In x ws0 -> In x ws) /\ (forall x, In x ws -> In x ws0 \/ exists q, pku_val (wden E x) = Some q) /\ (length ws0 <= length ws)%nat.
Proof.
  intros ws ws0 H. unfold pku_drop in H. destruct (scan fs ws) as [[[[pre [fr u]] post]|]|] eqn:SC; [| | discriminate].
  - injection H as <-. destruct (scan_some ws pre fr u post SC) as (-> & UB & PV & NO).
    split; [| split].
    + intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx| right; right; exact Hx].
    + intros x Hx. apply in_app_iff in Hx as [Hx|[<-|Hx]]; [left; apply in_app_iff; left; exact Hx| right; eexists; exact PV| left; apply in_app_iff; right; exact Hx].
    + rewrite !length_app. cbn [length]. lia.
  - injection H as <-. split; [auto| split; [auto| lia]].
Qed.
End Sem.
End PkU.
