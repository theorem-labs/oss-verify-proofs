(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SP0 : sym := 1%positive.
Definition DATA : sym := 2%positive.
Definition SIZE : sym := 3%positive.
Definition RA : sym := 4%positive.
Definition SREG (i : Z) : sym := Z.to_pos (5 + i).      (* [comment removed for export] *)
Definition TP : sym := 17%positive.
Definition GP : sym := 18%positive.
Definition LAST_FIXED : sym := 63%positive.
Definition FIRST_FRESH : positive := 64%positive.
Definition is_fixed (s : sym) : bool := Pos.leb s LAST_FIXED.

Definition absval := option lin.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cell := (Z * absval)%type.            (* [comment removed for export] *)
Definition cellmap := list (Z * cell).

Fixpoint cm_get (m : cellmap) (k : Z) : option cell :=
  match m with
  | [] => None
  | (k', c) :: t =>
      match Z.compare k' k with
      | Lt => cm_get t k
      | Eq => Some c
      | Gt => None
      end
  end.

(* [comment removed for export] *)
Fixpoint cm_kill (m : cellmap) (lo hi : Z) : cellmap :=
  match m with
  | [] => []
  | (k, (w, v)) :: t =>
      if (if Z.ltb k hi then Z.ltb lo (k + w) else false) then cm_kill t lo hi   (* [comment removed for export] *)
      else (k, (w, v)) :: cm_kill t lo hi
  end.

(* [comment removed for export] *)
Fixpoint cm_set (m : cellmap) (k : Z) (c : cell) : cellmap :=
  match m with
  | [] => [(k, c)]
  | (k', c') :: t =>
      match Z.compare k' k with
      | Lt => (k', c') :: cm_set t k c
      | Eq => (k, c) :: t
      | Gt => (k, c) :: m
      end
  end.

(* [comment removed for export] *)
Fixpoint cm_overlapping (m : cellmap) (lo hi : Z) : list (Z * cell) :=
  match m with
  | [] => []
  | (k, (w, v)) :: t =>
      if (if Z.ltb k hi then Z.ltb lo (k + w) else false) then (k, (w, v)) :: cm_overlapping t lo hi   (* [comment removed for export] *)
      else cm_overlapping t lo hi
  end.

Lemma cm_get_in m k c : cm_get m k = Some c -> In (k, c) m.
Proof.
  induction m as [|[k' c'] t IH]; simpl; [discriminate|].
  destruct (Z.compare_spec k' k); intros X; try discriminate; auto.
  inversion X; subst; auto.
Qed.

Lemma cm_kill_sub m lo hi x : In x (cm_kill m lo hi) -> In x m.
Proof.
  induction m as [|[k [w v]] t IH]; simpl; auto. rewrite ?if_andb.
  destruct (Z.ltb k hi && Z.ltb lo (k + w)); simpl; intros H; [right; auto|].
  destruct H; auto.
Qed.

Lemma cm_kill_disjoint m lo hi k w v :
  In (k, (w, v)) (cm_kill m lo hi) -> ~ (k < hi /\ lo < k + w).
Proof.
  induction m as [|[k' [w' v']] t IH]; simpl; [tauto|]. rewrite ?if_andb.
  destruct (Z.ltb k' hi && Z.ltb lo (k' + w')) eqn:E; simpl; intros H; auto.
  destruct H as [H|H]; auto. inversion H; subst.
  rewrite andb_false_iff, !Z.ltb_ge in E. lia.
Qed.

Lemma cm_set_in m k c x : In x (cm_set m k c) -> x = (k, c) \/ In x m.
Proof.
  induction m as [|[k' c'] t IH]; simpl; [intuition|].
  destruct (Z.compare_spec k' k); simpl; intros X; intuition.
Qed.

Lemma cm_overlapping_in m lo hi x : In x (cm_overlapping m lo hi) -> In x m.
Proof.
  induction m as [|[k [w v]] t IH]; simpl; auto. rewrite ?if_andb.
  destruct (Z.ltb k hi && Z.ltb lo (k + w)); simpl; intros H; intuition.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive ckind : Type := CK_lt | CK_ltu | CK_eq.

Definition ckind_eqb (a b : ckind) : bool :=
  match a, b with CK_lt, CK_lt | CK_ltu, CK_ltu | CK_eq, CK_eq => true | _, _ => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record vstate := mkVS {
  vs_pc : Z ;
  vs_regs : pmap lin ;                       (* [comment removed for export] *)
  vs_slots : cellmap ;                       (* [comment removed for export] *)
  vs_globs : cellmap ;                       (* [comment removed for export] *)
  vs_store : store ;
  vs_next : positive ;                       (* [comment removed for export] *)
  vs_conddef : pmap (ckind * lin * lin) ;    (* [comment removed for export] *)
  vs_moddef : pmap (lin * Z) ;               (* [comment removed for export] *)
  vs_valset : pmap (list Z) ;                (* [comment removed for export] *)
  vs_nul : list (Z * Z) ;                    (* [comment removed for export] *)
  vs_ctx : list Z ;                          (* [comment removed for export] *)
  vs_ghosts : pmap lin                       (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition set_pc (A : vstate) (pc : Z) : vstate :=
  mkVS pc (vs_regs A) (vs_slots A) (vs_globs A) (vs_store A) (vs_next A)
       (vs_conddef A) (vs_moddef A) (vs_valset A) (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_regs (A : vstate) (r : pmap lin) : vstate :=
  mkVS (vs_pc A) r (vs_slots A) (vs_globs A) (vs_store A) (vs_next A)
       (vs_conddef A) (vs_moddef A) (vs_valset A) (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_slots (A : vstate) (m : cellmap) : vstate :=
  mkVS (vs_pc A) (vs_regs A) m (vs_globs A) (vs_store A) (vs_next A)
       (vs_conddef A) (vs_moddef A) (vs_valset A) (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_globs (A : vstate) (m : cellmap) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) m (vs_store A) (vs_next A)
       (vs_conddef A) (vs_moddef A) (vs_valset A) (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_store (A : vstate) (S : store) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) (vs_globs A) S (vs_next A)
       (vs_conddef A) (vs_moddef A) (vs_valset A) (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_next (A : vstate) (n : positive) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) (vs_globs A) (vs_store A) n
       (vs_conddef A) (vs_moddef A) (vs_valset A) (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_conddef (A : vstate) (m : pmap (ckind * lin * lin)) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) (vs_globs A) (vs_store A) (vs_next A)
       m (vs_moddef A) (vs_valset A) (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_moddef (A : vstate) (m : pmap (lin * Z)) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) (vs_globs A) (vs_store A) (vs_next A)
       (vs_conddef A) m (vs_valset A) (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_valset (A : vstate) (m : pmap (list Z)) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) (vs_globs A) (vs_store A) (vs_next A)
       (vs_conddef A) (vs_moddef A) m (vs_nul A) (vs_ctx A) (vs_ghosts A).
Definition set_nul (A : vstate) (l : list (Z * Z)) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) (vs_globs A) (vs_store A) (vs_next A)
       (vs_conddef A) (vs_moddef A) (vs_valset A) l (vs_ctx A) (vs_ghosts A).
Definition set_ctx (A : vstate) (c : list Z) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) (vs_globs A) (vs_store A) (vs_next A)
       (vs_conddef A) (vs_moddef A) (vs_valset A) (vs_nul A) c (vs_ghosts A).
Definition set_ghosts (A : vstate) (g : pmap lin) : vstate :=
  mkVS (vs_pc A) (vs_regs A) (vs_slots A) (vs_globs A) (vs_store A) (vs_next A)
       (vs_conddef A) (vs_moddef A) (vs_valset A) (vs_nul A) (vs_ctx A) g.

(* [comment removed for export] *)
Definition reg_key (r : Z) : positive := Z.to_pos r.

Definition get_reg (A : vstate) (r : Z) : absval :=
  if Z.eqb r 0 then Some lzero else pm_get (reg_key r) (vs_regs A).

Definition set_reg (A : vstate) (r : Z) (v : absval) : vstate :=
  if Z.eqb r 0 then A
  else set_regs A (match v with
                  | Some e => pm_set (reg_key r) e (vs_regs A)
                  | None => pm_remove (reg_key r) (vs_regs A)
                  end).

(* [comment removed for export] *)
Definition fresh_sym (A : vstate) : sym * vstate := (vs_next A, set_next A (Pos.succ (vs_next A))).

(* [comment removed for export] *)
Definition fresh_lin (A : vstate) (b : itv) : lin * vstate :=
  match b with
  | (Some lo, Some hi) =>
      if Z.eqb lo hi then (lconst lo, A)
      else let s := vs_next A in
           (lsym s, set_next (set_store A (store_set_box (vs_store A) s b)) (Pos.succ s))
  | (None, None) => let s := vs_next A in (lsym s, set_next A (Pos.succ s))
  | _ => let s := vs_next A in
         (lsym s, set_next (set_store A (store_set_box (vs_store A) s b)) (Pos.succ s))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record vparams := mkVP {
  vp_frame : Z ;                (* [comment removed for export] *)
  vp_wstack : list (Z * Z) ;    (* [comment removed for export] *)
  vp_wcells : list (Z * Z) ;    (* [comment removed for export] *)
  vp_fcells : list (Z * Z) ;    (* [comment removed for export] *)
  vp_segs : list (Z * Z) ;      (* [comment removed for export] *)
  vp_pristine : list (Z * Z) ;  (* [comment removed for export] *)
  vp_rom : pmap Z ;             (* [comment removed for export] *)
  vp_nmax : Z ;                 (* [comment removed for export] *)
  vp_splo : Z ; vp_sphi : Z     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition vstate_init (pc : Z) : vstate :=
  mkVS pc pm_empty [] [] store_top FIRST_FRESH pm_empty pm_empty pm_empty [] [] pm_empty.
