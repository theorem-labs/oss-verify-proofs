(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool String Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SP8 : sym := 64%positive.          (* [comment removed for export] *)
Definition DATA8 : sym := 65%positive.        (* [comment removed for export] *)
Definition FSB : sym := 66%positive.          (* [comment removed for export] *)
Definition FS8 : sym := 67%positive.          (* [comment removed for export] *)
Definition ASYM2 (i : Z) : sym := Z.to_pos (19 + i).      (* [comment removed for export] *)
Definition ASYM8 (i : Z) : sym := Z.to_pos (68 + i).      (* [comment removed for export] *)
Definition LAST_FIXED2 : sym := 95%positive.
Definition FIRST_FRESH2 : positive := 96%positive.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_comp (s : sym) : option sym :=
  if Pos.eqb s SP0 then Some SP8
  else if Pos.eqb s DATA then Some DATA8
  else if Pos.eqb s FSB then Some FS8
  else if Pos.leb 19 s && Pos.leb s 26 then Some (Pos.add s 49)   (* [comment removed for export] *)
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive rkind : Type :=
| RK_fake (cid : Z) (flag : sym)    (* [comment removed for export] *)
| RK_arg                           (* [comment removed for export] *)
| RK_flag (owner : sym)            (* [comment removed for export] *)
| RK_shadow (of_ : sym)            (* [comment removed for export] *)
| RK_fs.                           (* [comment removed for export] *)

Record vregion := mkVR {
  vr_base : sym ;            (* [comment removed for export] *)
  vr_disp : Z ;              (* [comment removed for export] *)
  vr_kind : rkind ;
  vr_lo : Z ; vr_hi : Z ;    (* [comment removed for export] *)
  vr_w : list (Z * Z) ;      (* [comment removed for export] *)
  vr_cells : cellmap ;       (* [comment removed for export] *)
  vr_nul : list (Z * Z) ;    (* [comment removed for export] *)
  vr_b8 : option sym         (* [comment removed for export] *)
}.

Definition fake_size (cid : Z) : Z := Z.shiftl 64 cid.

Definition is_shadow (r : vregion) : bool :=
  match vr_kind r with RK_shadow _ => true | _ => false end.

Definition rkind_eqb (a b : rkind) : bool :=
  match a, b with
  | RK_fake c1 f1, RK_fake c2 f2 => Z.eqb c1 c2 && Pos.eqb f1 f2
  | RK_arg, RK_arg => true
  | RK_flag o1, RK_flag o2 => Pos.eqb o1 o2
  | RK_shadow s1, RK_shadow s2 => Pos.eqb s1 s2
  | RK_fs, RK_fs => true
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record vstate2 := mkVS2 {
  v1 : vstate ;                      (* [comment removed for export] *)
  vs_rgn : list vregion ;            (* [comment removed for export] *)
  vs_live : list sym ;               (* [comment removed for export] *)
  vs_divdef : pmap (lin * Z) ;       (* [comment removed for export] *)
  vs_memo : list (lin * (Z * lin))   (* [comment removed for export] *)
}.

Definition of_v1 (A : vstate) : vstate2 := mkVS2 A [] [] pm_empty [].
Definition with_v1 (A : vstate2) (B : vstate) : vstate2 := mkVS2 B (vs_rgn A) (vs_live A) (vs_divdef A) (vs_memo A).
Definition set_rgn (A : vstate2) (l : list vregion) : vstate2 := mkVS2 (v1 A) l (vs_live A) (vs_divdef A) (vs_memo A).
Definition set_live (A : vstate2) (l : list sym) : vstate2 := mkVS2 (v1 A) (vs_rgn A) l (vs_divdef A) (vs_memo A).
Definition set_divdef (A : vstate2) (m : pmap (lin * Z)) : vstate2 := mkVS2 (v1 A) (vs_rgn A) (vs_live A) m (vs_memo A).
Definition set_memo (A : vstate2) (m : list (lin * (Z * lin))) : vstate2 := mkVS2 (v1 A) (vs_rgn A) (vs_live A) (vs_divdef A) m.
(* [comment removed for export] *)
Definition clear_memo (A : vstate2) : vstate2 := mkVS2 (v1 A) (vs_rgn A) (vs_live A) (vs_divdef A) [].
(* [comment removed for export] *)
Definition with_v1c (A : vstate2) (B : vstate) : vstate2 := mkVS2 B (vs_rgn A) (vs_live A) (vs_divdef A) [].

(* [comment removed for export] *)
Definition vs2_pc (A : vstate2) : Z := vs_pc (v1 A).
Definition vs2_next (A : vstate2) : positive := vs_next (v1 A).
Definition get_reg2 (A : vstate2) (r : Z) : absval := get_reg (v1 A) r.
Definition set_reg2 (A : vstate2) (r : Z) (v : absval) : vstate2 := with_v1 A (set_reg (v1 A) r v).
Definition set_pc2 (A : vstate2) (pc : Z) : vstate2 := with_v1 A (set_pc (v1 A) pc).

(* [comment removed for export] *)
Fixpoint rgn_get (l : list vregion) (b : sym) : option vregion :=
  match l with
  | [] => None
  | r :: t => if Pos.eqb (vr_base r) b then Some r else rgn_get t b
  end.

Fixpoint rgn_upd (l : list vregion) (r : vregion) : list vregion :=
  match l with
  | [] => [r]
  | r' :: t => if Pos.eqb (vr_base r') (vr_base r) then r :: t else r' :: rgn_upd t r
  end.

Fixpoint rgn_remove (l : list vregion) (b : sym) : list vregion :=
  match l with
  | [] => []
  | r :: t => if Pos.eqb (vr_base r) b then rgn_remove t b else r :: rgn_remove t b
  end.

Definition rgn_bases (l : list vregion) : list sym := map vr_base l.

Definition is_base (A : vstate2) (s : sym) : bool := existsb (Pos.eqb s) (rgn_bases (vs_rgn A)).

Definition set_cells (r : vregion) (m : cellmap) : vregion :=
  mkVR (vr_base r) (vr_disp r) (vr_kind r) (vr_lo r) (vr_hi r) (vr_w r) m (vr_nul r) (vr_b8 r).
Definition set_rnul (r : vregion) (l : list (Z * Z)) : vregion :=
  mkVR (vr_base r) (vr_disp r) (vr_kind r) (vr_lo r) (vr_hi r) (vr_w r) (vr_cells r) l (vr_b8 r).

(* [comment removed for export] *)
Definition env_comp (s : sym) : option sym :=
  if Pos.eqb s SP0 then Some SP8
  else if Pos.eqb s DATA then Some DATA8
  else if Pos.eqb s FSB then Some FS8
  else None.

Definition divdef_is (A : vstate2) (q : sym) (x : lin) (m : Z) : bool :=
  match pm_get q (vs_divdef A) with
  | Some (x', m') => Z.eqb m' m && lin_eqb x' x
  | None => false
  end.

Definition comp (A : vstate2) (s : sym) : option sym :=
  match env_comp s with
  | Some c => Some c
  | None =>
      let cand := match fixed_comp s with
                  | Some c => Some c                       (* [comment removed for export] *)
                  | None => match rgn_get (vs_rgn A) s with Some r => vr_b8 r | None => None end
                  end in
      match cand with
      | Some c => if divdef_is A c (lsym s) 8 then Some c else None
      | None => None
      end
  end.

Definition rgn_add (A : vstate2) (r : vregion) : vstate2 := set_rgn A (r :: vs_rgn A).

(* [comment removed for export] *)
Fixpoint rgn_shadow_of (l : list vregion) (of_ : sym) : option vregion :=
  match l with
  | [] => None
  | r :: t => match vr_kind r with
              | RK_shadow s => if Pos.eqb s of_ then Some r else rgn_shadow_of t of_
              | _ => rgn_shadow_of t of_
              end
  end.

Lemma rgn_get_in l b r : rgn_get l b = Some r -> In r l /\ vr_base r = b.
Proof.
  induction l as [|x t IH]; simpl; [discriminate|].
  destruct (Pos.eqb_spec (vr_base x) b).
  - intros H; injection H as <-. auto.
  - intros H. destruct (IH H); auto.
Qed.

Lemma rgn_remove_sub l b r : In r (rgn_remove l b) -> In r l /\ vr_base r <> b.
Proof.
  induction l as [|x t IH]; simpl; [tauto|].
  destruct (Pos.eqb_spec (vr_base x) b); simpl; intros H.
  - destruct (IH H); auto.
  - destruct H as [<-|H]; [auto|]. destruct (IH H); auto.
Qed.

Lemma rgn_upd_in l r x : In x (rgn_upd l r) -> x = r \/ In x l.
Proof.
  induction l as [|y t IH]; simpl; [intuition|].
  destruct (Pos.eqb_spec (vr_base y) (vr_base r)); simpl; intros H; [intuition|].
  destruct H as [<-|H]; [auto|]. destruct (IH H); auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record fzone := mkFZ { fz_base : sym ; fz_disp : Z ; fz_lo : lin ; fz_hi : lin ; fz_rw : bool }.

Record vparams2 := mkVP2 {
  p1 : vparams ;
  vp_shoff : Z ;                       (* [comment removed for export] *)
  vp_kcells : list (Z * (Z * Z)) ;     (* [comment removed for export] *)
  vp_kruns : list (Z * (Z * Z)) ;      (* [comment removed for export] *)
  vp_fzones : list fzone ;
  vp_fs : option (Z * Z) ;             (* [comment removed for export] *)
  vp_datal : Z ;                       (* [comment removed for export] *)
  vp_wrgn : list (Z * (Z * Z)) ;       (* [comment removed for export] *)
  vp_fdepth : Z ;                      (* [comment removed for export] *)
  vp_tp : Z ;                          (* [comment removed for export] *)
  vp_imgend : Z                        (* [comment removed for export] *)
}.

Definition of_p1 (P : vparams) : vparams2 := mkVP2 P 0 [] [] [] None 1 [] 0 0 0.
Definition of_p1_tp (P : vparams) (tp : Z) : vparams2 := mkVP2 P 0 [] [] [] None 1 [] 0 tp 0.

(* [comment removed for export] *)
Definition asan_mode (P : vparams2) : bool := match vp_fs P with Some _ => true | None => false end.

Fixpoint krun_get (l : list (Z * (Z * Z))) (a : Z) : option Z :=
  match l with
  | [] => None
  | (lo, (hi, b)) :: t => if Z.leb lo a && Z.ltb a hi then Some b else krun_get t a
  end.

Lemma krun_get_in l a b : krun_get l a = Some b -> exists lo hi, In (lo, (hi, b)) l /\ lo <= a < hi.
Proof.
  induction l as [|[lo [hi b']] t IH]; simpl; [discriminate|].
  destruct (Z.leb lo a && Z.ltb a hi) eqn:C; intros H.
  - injection H as <-. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. exists lo, hi. auto.
  - destruct (IH H) as (lo' & hi' & Hin & R). exists lo', hi'. auto.
Qed.

Fixpoint kcell_get (l : list (Z * (Z * Z))) (a n : Z) : option Z :=
  match l with
  | [] => None
  | (a', (w, v)) :: t => if Z.eqb a' a && Z.eqb w n then Some v else kcell_get t a n
  end.

Lemma kcell_get_in l a n v : kcell_get l a n = Some v -> In (a, (n, v)) l.
Proof.
  induction l as [|[a' [w v']] t IH]; simpl; [discriminate|].
  destruct (Z.eqb_spec a' a); destruct (Z.eqb_spec w n); simpl; intros H; try (right; exact (IH H)).
  injection H as <-. subst. auto.
Qed.
