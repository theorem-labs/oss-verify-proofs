(* SPDX-License-Identifier: MIT *)
(* One fixed rule that makes a recorded symbolic state of the old start-up run again over the
   start state the build computes (LPS 727298f3: one start state per CONFIG_RSEQ, its auxv
   [auxv_size r] bytes long).  It is this unit's form, over [sstate], of the rule the run record
   names [relaunch D L (ash hand_f S)]: the recorded state, with the parts it still holds from
   the start state replaced by the computed start state's.

   Given the recorded start state [R], the start state [N] computed in the build (the same point
   of the run, for one value of the flag) and a recorded state [X] of the old run reached from
   [R], [relaunch R N X] is [X] with
   - each object that [X] still holds as [R] held it replaced by [N]'s object at the same index;
     in every other object, its base, low and high bounds taken from [N] where they are still
     [R]'s, and its cells that are still [R]'s kept where [N] holds them too, else replaced by
     [N]'s cell at the same offset and width, with [N]'s cells at offsets that neither [R] nor [X]
     has added;
   - each register that still holds [R]'s value given [N]'s value;
   - the facts on start variables (below [ss_next R]) that [R] holds and [N] does not dropped,
     and the facts on start variables that [N] holds and [R] does not added.
   Everything else of [X] is kept.  Nothing here is trusted: each state it makes is checked by
   the symbolic run that consumes it (an entailment or a CFG check computed in the build).

   Where the pair is taken.  For a state the run reaches by way of memory, keying the rule on the
   two START states is not enough: the run copies start values from memory into registers and
   overwrites start cells (in the ASan chain, the auxv words __init_libc copied to the stack are
   loaded into registers and then zeroed, so the recorded exit holds 0 where the recorded start
   held 0, and the start-keyed rule put the new start's words there, which the new run no longer
   holds).  So an exit or hand-off state [X] of a recorded check is remade by the same rule keyed
   on the two LEAVES of the source that reaches it: [relaunch_src] runs the check's recorded
   sources, takes the first one with a leaf matching [X] ([leaf_matches1A], the check's own
   test), and applies [relaunchA] to that leaf, the leaf of the same index of the matching
   computed source, and [X].  The choice depends on the recorded states only, so it is the same
   for every computed run; with the recorded sources given for the computed ones it returns [X]
   (the rule with [N = R]); if no source matches, [X] is returned unchanged. *)
From Stdlib Require Import ZArith PArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
Import ListNotations.

Definition rl_cell_eqb (c d : cell) : bool :=
  sv_eqb (c_off c) (c_off d) && Z.eqb (c_width c) (c_width d) && sv_eqb (c_val c) (c_val d).

Fixpoint rl_cells_eqb (a b : list cell) : bool :=
  match a, b with
  | [], [] => true
  | c :: a', d :: b' => rl_cell_eqb c d && rl_cells_eqb a' b'
  | _, _ => false
  end.

Definition rl_dflt_eqb (d e : odefault) : bool :=
  match d, e with
  | DUnknown, DUnknown => true
  | DZero, DZero => true
  | DImage, DImage => true
  | DList l, DList k => Pos.eqb l k
  | DRom l, DRom k => Pos.eqb l k
  | _, _ => false
  end.

Definition rl_obj_eqb (o p : sobj) : bool :=
  sv_eqb (ob_base o) (ob_base p) && sv_eqb (ob_lo o) (ob_lo p) && sv_eqb (ob_hi o) (ob_hi p)
  && rl_dflt_eqb (ob_dflt o) (ob_dflt p) && rl_cells_eqb (ob_cells o) (ob_cells p).

Definition rl_in (c : cell) (l : list cell) : bool := List.existsb (rl_cell_eqb c) l.
Definition rl_same_off (c d : cell) : bool := sv_eqb (c_off c) (c_off d).
(* The same place: offset and width.  A state may hold cells of several widths at one offset (a
   word and the bytes read out of it), so a cell is matched on both, never on its offset alone. *)
Definition rl_same_at (c d : cell) : bool := sv_eqb (c_off c) (c_off d) && Z.eqb (c_width c) (c_width d).

Definition rl_cells (R N X : list cell) : list cell :=
  List.flat_map (fun c => if rl_in c R
                     then if rl_in c N then [c]
                          else match List.find (rl_same_at c) N with Some n => [n] | None => [] end
                     else [c]) X
  ++ List.filter (fun n => negb (List.existsb (rl_same_off n) R) && negb (List.existsb (rl_same_off n) X)) N.

Definition rl_obj (R N X : sobj) : sobj :=
  if rl_obj_eqb X R then N
  else mkObj (if sv_eqb (ob_base X) (ob_base R) then ob_base N else ob_base X)
             (if sv_eqb (ob_lo X) (ob_lo R) then ob_lo N else ob_lo X)
             (if sv_eqb (ob_hi X) (ob_hi R) then ob_hi N else ob_hi X)
             (rl_cells (ob_cells R) (ob_cells N) (ob_cells X))
             (ob_dflt X).

Fixpoint rl_objs (R N X : list sobj) : list sobj :=
  match R, N, X with
  | r :: R', n :: N', x :: X' => rl_obj r n x :: rl_objs R' N' X'
  | _, _, _ => X
  end.

Fixpoint rl_svs (R N X : list sv) : list sv :=
  match R, N, X with
  | r :: R', n :: N', x :: X' => (if sv_eqb x r then n else x) :: rl_svs R' N' X'
  | _, _, _ => X
  end.

Definition rl_pin (p : sprop) (l : list sprop) : bool := List.existsb (sprop_eqb p) l.

Definition rl_facts (nb : positive) (R N X : list sprop) : list sprop :=
  List.filter (fun p => negb (sprop_below nb p && rl_pin p R && negb (rl_pin p N))) X
  ++ List.filter (fun p => sprop_below nb p && negb (rl_pin p R) && negb (rl_pin p X)) N.

(* The remade state keeps [X]'s next variable when that is enough for it ([swf]); else it takes
   [N]'s too.  (A source's leaf may have used more variables than the cut state it reaches, so taking
   the larger one always would change [X] even when [N] is [R].) *)
Definition rl_core (R N X : sstate) (nx : positive) : sstate :=
  mkSS (ss_pc X)
       (rl_svs (ss_regs R) (ss_regs N) (ss_regs X))
       (rl_svs (ss_fregs R) (ss_fregs N) (ss_fregs X))
       (ss_fcsr X) (ss_resv X)
       (rl_objs (ss_objs R) (ss_objs N) (ss_objs X))
       (rl_facts (ss_next R) (ss_facts R) (ss_facts N) (ss_facts X))
       nx
       (ss_lenient X).

Definition relaunch (R N X : sstate) : sstate :=
  let S := rl_core R N X (ss_next X) in
  if swf S then S else rl_core R N X (Pos.max (ss_next X) (ss_next N)).

Definition relaunchA (R N : sstate) (A : axst) : axst := ax_setS A (relaunch R N (ax_S A)).

(* The leaves of a run, the index of the first one matching [X], and the first source with one. *)
Definition rl_leaves segs (fuel : nat) (cutpcs : list Z) (S : axst) : list axst :=
  match sym_runA segs fuel cutpcs S true with Some ls => List.map la_state ls | None => [] end.

Fixpoint rl_find (g : positive) (X : axst) (ls : list axst) (i : nat) : option nat :=
  match ls with
  | [] => None
  | L :: ls' => if leaf_matches1A g L X then Some i else rl_find g X ls' (S i)
  end.

Fixpoint rl_pick segs (fuel : nat) (cutpcs : list Z) (g : positive) (X : axst) (srcs : list axst) (k : nat)
  : option (nat * nat) :=
  match srcs with
  | [] => None
  | Sr :: srcs' =>
      match rl_find g X (rl_leaves segs fuel cutpcs Sr) 0 with
      | Some i => Some (k, i)
      | None => rl_pick segs fuel cutpcs g X srcs' (S k)
      end
  end.

(* [X] remade over the computed run, keyed on the leaves of the source that reaches it. *)
Definition relaunch_src segs (fuel : nat) (cutpcs : list Z) (g : positive)
  (Rsrcs Nsrcs : list axst) (X : axst) : axst :=
  match rl_pick segs fuel cutpcs g X Rsrcs 0 with
  | Some (k, i) =>
      match nth_error Rsrcs k, nth_error Nsrcs k with
      | Some Rs, Some Ns =>
          match nth_error (rl_leaves segs fuel cutpcs Rs) i, nth_error (rl_leaves segs fuel cutpcs Ns) i with
          | Some Rl, Some Nl => relaunchA (ax_S Rl) (ax_S Nl) X
          | _, _ => X
          end
      | _, _ => X
      end
  | None => X
  end.
