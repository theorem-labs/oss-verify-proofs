(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM03.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Notation CEIL_MIN := 140735332483072%Z (only parsing).
Notation CEIL_MAX := 140737479966720%Z (only parsing).
Lemma CEIL_MIN_eq : 140735332483072 = sp_window_lo - stack_max_size.
Proof. reflexivity. Qed.
Lemma CEIL_MAX_eq : 140737479966720 = sp_window_hi - stack_max_size.
Proof. reflexivity. Qed.
Class RunCeil := {
alloc_ceiling : Z;
alloc_ceiling_val : CEIL_MIN <= alloc_ceiling <= CEIL_MAX /\ alloc_ceiling mod 4096 = 0
}.
Lemma alloc_ceiling_value {rc : RunCeil} : CEIL_MIN <= alloc_ceiling <= CEIL_MAX /\ alloc_ceiling mod 4096 = 0.
Proof. exact alloc_ceiling_val. Qed.
Lemma alloc_ceiling_lt {rc : RunCeil} : alloc_ceiling < 2 ^ 47.
Proof. pose proof alloc_ceiling_val. lia. Qed.
Definition page_floor (x : Z) : Z := x / 4096 * 4096.
Lemma page_floor_le : forall x, page_floor x <= x.
Proof. intros x. unfold page_floor. pose proof (Z.mul_div_le x 4096). lia. Qed.
Lemma page_floor_mod : forall x, page_floor x mod 4096 = 0.
Proof. intros x. unfold page_floor. apply Z.mod_mul. lia. Qed.
Lemma page_floor_ge : forall x y, y mod 4096 = 0 -> y <= x -> y <= page_floor x.
Proof.
intros x y Hy Hle. unfold page_floor.
pose proof (Z.div_mod y 4096 ltac:(lia)) as E. rewrite Hy, Z.add_0_r in E.
assert (y / 4096 <= x / 4096) by (apply Z.div_le_mono; lia). nia.
Qed.
Lemma page_floor_mono : forall x y, x <= y -> page_floor x <= page_floor y.
Proof. intros x y H. unfold page_floor. assert (x / 4096 <= y / 4096) by (apply Z.div_le_mono; lia). lia. Qed.
Definition run_ceil (sp0 : Z) : Z := page_floor (sp0 - stack_max_size).
Lemma run_ceil_ok : forall sp0,
sp_window_lo <= sp0 <= sp_window_hi ->
CEIL_MIN <= run_ceil sp0 <= CEIL_MAX /\ run_ceil sp0 mod 4096 = 0.
Proof.
intros sp0 Hsp. unfold run_ceil. split; [|apply page_floor_mod].
split.
- rewrite CEIL_MIN_eq. apply page_floor_ge; [reflexivity| lia].
- rewrite CEIL_MAX_eq. etransitivity; [apply page_floor_le|]. lia.
Qed.
Definition RunCeilOf (sp0 : Z) (H : sp_window_lo <= sp0 <= sp_window_hi) : RunCeil :=
{| alloc_ceiling := run_ceil sp0 ; alloc_ceiling_val := run_ceil_ok sp0 H |}.
Definition ceil_of_top {rc : RunCeil} (top : Z) : Prop := alloc_ceiling = page_floor top.
Lemma grant_below_ceil {rc : RunCeil} : forall top e,
ceil_of_top top -> e mod 4096 = 0 -> e <= top -> e <= alloc_ceiling.
Proof. intros top e -> He Hle. apply page_floor_ge; assumption. Qed.
Lemma ceil_le_top {rc : RunCeil} : forall top, ceil_of_top top -> alloc_ceiling <= top.
Proof. intros top ->. apply page_floor_le. Qed.
Lemma ceil_of_top_run {sp0 : Z} (H : sp_window_lo <= sp0 <= sp_window_hi) :
@ceil_of_top (RunCeilOf sp0 H) (sp0 - stack_max_size).
Proof. reflexivity. Qed.
Ltac rc_inst :=
repeat match goal with
| |- context [@alloc_ceiling ?e] => is_evar e; let i := constr:(_ : RunCeil) in unify e i
end.
Ltac Lia.lia ::=
rc_inst;
tryif lf_arith_goal
then first [ solve [lf_prune0; lf_lia_orig] | solve [lf_prune1; lf_lia_orig] | lf_lia_orig ]
else first [ solve [lf_prune0; lf_lia_orig] | lf_lia_orig ].
Ltac Lia.nia ::=
rc_inst;
tryif lf_arith_goal
then first [ solve [lf_prune0; lf_nia_orig] | solve [lf_prune1; lf_nia_orig] | lf_nia_orig ]
else first [ solve [lf_prune0; lf_nia_orig] | lf_nia_orig ].
From Ltac2 Require Ltac2.
Module BvWfFast.
Import Ltac2.
Ltac2 rec body_of (x : ident) (hs : (ident * constr option * constr) list) : constr option :=
match hs with
| [] => None
| h :: rest => let (id, b, _) := h in if Ident.equal id x then b else body_of x rest
end.
Ltac2 rec novar (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var _ => false
| Constr.Unsafe.Rel _ => true
| Constr.Unsafe.Sort _ => true
| Constr.Unsafe.Constant _ _ => true
| Constr.Unsafe.Ind _ _ => true
| Constr.Unsafe.Constructor _ _ => true
| Constr.Unsafe.Uint63 _ => true
| Constr.Unsafe.Float _ => true
| Constr.Unsafe.String _ => true
| Constr.Unsafe.Cast c _ t => if novar c then novar t else false
| Constr.Unsafe.App f args => if novar f then Array.for_all novar args else false
| _ => false
end.
Ltac2 rec status (hs : (ident * constr option * constr) list) (c : constr) : int :=
let max2 (a : int) (f : unit -> int) := if Int.equal a 2 then 2 else (let b := f () in if Int.lt a b then b else a) in
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var x => (match body_of x hs with Some b => status hs b | None => 1 end)
| Constr.Unsafe.Rel _ => 0
| Constr.Unsafe.Sort _ => 0
| Constr.Unsafe.Constant _ _ => 0
| Constr.Unsafe.Ind _ _ => 0
| Constr.Unsafe.Constructor _ _ => 0
| Constr.Unsafe.Uint63 _ => 0
| Constr.Unsafe.Float _ => 0
| Constr.Unsafe.String _ => 0
| Constr.Unsafe.Cast c _ t => max2 (status hs c) (fun () => status hs t)
| Constr.Unsafe.Prod b c => max2 (status hs (Constr.Binder.type b)) (fun () => status hs c)
| Constr.Unsafe.Lambda b c => max2 (status hs (Constr.Binder.type b)) (fun () => status hs c)
| Constr.Unsafe.LetIn b v c => max2 (max2 (status hs (Constr.Binder.type b)) (fun () => status hs v)) (fun () => status hs c)
| Constr.Unsafe.App f args =>
Array.fold_left (fun (a : int) (x : constr) => max2 a (fun () => status hs x)) (status hs f) args
| _ => 2
end.
Ltac2 bvwf_closed (n : constr) (v : constr) : bool :=
if (if novar n then novar v else false) then true else
let hs := Control.hyps () in
let s := (let a := status hs n in if Int.equal a 2 then 2 else let b := status hs v in if Int.lt a b then b else a) in
if Int.equal s 1 then Control.zero (Tactic_failure (Some (Message.of_string "BvWf: open term"))) else Int.equal s 0.
Ltac2 solve_bvwf_fast () : unit :=
lazy_match! goal with
| [ |- stdpp.bitvector.definitions.BvWf ?n ?v ] =>
if bvwf_closed n v
then ltac1:(first [ vm_compute; exact I | fail "Bitvector constant does not fit (fast path)" ])
else ltac1:(lazymatch goal with |- stdpp.bitvector.definitions.BvWf ?n ?v =>
stdpp.tactics.is_closed_term n; stdpp.tactics.is_closed_term v; try (vm_compute; exact I);
fail "Bitvector constant" v "does not fit into" n "bits" end)
end.
End BvWfFast.
Ltac stdpp.bitvector.definitions.solve_BvWf ::= ltac2:(BvWfFast.solve_bvwf_fast ()).
