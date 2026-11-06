(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan CxPlanSound CxOpt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.

Definition vbase (v : nat) : expr := EMd M_MUL (ELit 4096) (EVar v).
Fixpoint ehas (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar n => Nat.eqb n v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (ehas v a || ehas v b)%bool
  | EExt _ _ _ a => ehas v a
  | EBlob _ _ _ _ => false
  end.
Definition ahas (v : nat) (a : saddr) : bool := ehas v (a_base a).
Definition khas (v : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ x => (ahas v a || ehas v x)%bool
  | KZero a n | KWr a n | KUnk a n => (ahas v a || ehas v n)%bool
  | KBlob a n _ => (ahas v a || ehas v n)%bool
  | KFill a n _ => (ahas v a || ehas v n)%bool
  | KImg _ _ => false
  | KAlign x _ => ehas v x
  | KRange x _ _ => ehas v x
  | KDisj a1 n1 a2 n2 => (ahas v a1 || ehas v n1 || ahas v a2 || ehas v n2)%bool
  end.
Definition side_is (v : nat) (len : Z) (a : saddr) (n : expr) : bool :=
  (expr_eqb (a_base a) (vbase v) && Z.eqb (a_off a) 0 && expr_eqb n (ELit len))%bool.
(* [comment removed for export] *)
Definition gen_k (v : nat) (len : Z) (d l : nat) (K : kentry) : list kentry :=
  match K with
  | KDisj a1 n1 a2 n2 =>
      if (side_is v len a1 n1 && negb (ahas v a2 || ehas v n2))%bool then [KDisj (SA (vbase d) 0) (EVar l) a2 n2]
      else if (side_is v len a2 n2 && negb (ahas v a1 || ehas v n1))%bool then [KDisj a1 n1 (SA (vbase d) 0) (EVar l)]
      else if khas v K then [] else [K]
  | KRange (EVar x) lo hi => if Nat.eqb x v then [KRange (EVar d) 0 hi] else [K]
  | _ => if khas v K then [] else [K]
  end.
Definition is_ent (v : nat) (len : Z) (m : amap) : bool := (expr_eqb (am_base m) (vbase v) && expr_eqb (am_len m) (ELit len))%bool.
Definition is_vis (v : nat) (len : Z) (p : expr * expr) : bool := (expr_eqb (fst p) (vbase v) && expr_eqb (snd p) (ELit len))%bool.

(* [comment removed for export] *)
Definition gen_opt (S : acs) (v : nat) (len : Z) (d l : nat) (slack : Z) : acs :=
  ACS (mk_ss (pc S) (s_regs (a_ss S)) (KRange (EVar l) 8 len :: flat_map (gen_k v len d l) (kn S)) (Nat.max (nxt S) (Datatypes.S (Nat.max d l))))
      (map (fun m => if is_ent v len m then AM (vbase d) (EVar l) KRW else m) (a_maps S)) (a_totsz S) (a_ylo S) (a_eager S)
      (map (fun p => if is_vis v len p then (vbase d, EVar l) else p) (a_vis S)) (a_ghost S) (a_abytes S + slack) (a_brk S) (a_fd S) (a_tidset S).
Definition gen_opts (S : acs) (cs : list (nat * Z * nat * nat)) (slack : Z) : acs :=
  fold_left (fun T c => let '(v, len, d, l) := c in gen_opt T v len d l slack) cs S.
Definition drop_opt (S : acs) (v : nat) (len : Z) : acs :=
  ACS (mk_ss (pc S) (s_regs (a_ss S)) (List.filter (fun K => negb (khas v K)) (kn S)) (nxt S))
      (List.filter (fun m => negb (is_ent v len m)) (a_maps S)) (a_totsz S) (a_ylo S) (a_eager S)
      (List.filter (fun p => negb (is_vis v len p)) (a_vis S)) (a_ghost S) (a_abytes S) (a_brk S) (a_fd S) (a_tidset S).
(* [comment removed for export] *)
Definition gen_ok (S : acs) (v : nat) : bool :=
  (forallb (fun e => negb (ehas v e)) (s_regs (a_ss S)) && negb (ehas v (a_brk S))
   && match a_fd S with FdFile _ a b => negb (ehas v a || ehas v b) | _ => true end)%bool.

(* [comment removed for export] *)
Definition pair_eqb' (p q : expr * expr) : bool := (expr_eqb (fst p) (fst q) && expr_eqb (snd p) (snd q))%bool.
Fixpoint find_from {T} (f : T -> bool) (l : list T) (i : nat) : option nat :=
  match l with [] => None | x :: r => if f x then Some i else find_from f r (Datatypes.S i) end.
(* [comment removed for export] *)
Fixpoint absent_ixs (ms : list amap) (i : nat) : list nat :=
  match ms with [] => [] | m :: r => if is_absent_lit m then i :: absent_ixs r (Datatypes.S i) else absent_ixs r (Datatypes.S i) end.
(* [comment removed for export] *)
Fixpoint vis_ops (fuel : nat) (pos : nat) (cur tgt : list (expr * expr)) : list (bool * nat * nat) :=
  match fuel, tgt with
  | Datatypes.S f, t :: tr =>
      match find_from (pair_eqb' t) (skipn pos cur) pos with
      | Some q =>
          if Nat.eqb q pos then vis_ops f (Datatypes.S pos) cur tr
          else (true, q, pos) :: vis_ops f (Datatypes.S pos) (list_insert_nth pos t (remove_nth q cur)) tr
      | None =>
          match find_from (pair_eqb' t) cur 0%nat with
          | Some j => (false, pos, j) :: vis_ops f (Datatypes.S pos) (list_insert_nth pos t cur) tr
          | None => []          (* [comment removed for export] *)
          end
      end
  | _, _ => []
  end.
Definition pads (leaf tgt : acs) : list kentry := List.filter (fun K => negb (existsb (kentry_eqb K) (kn leaf))) (kn tgt).

Definition orS (d : acs) (o : option acs) : acs := match o with Some c => c | None => d end.
Definition hop_plan (A : atable) (LIMIT : Z) (S HS : acs) (h : nat) : plan :=
  let ixs := absent_ixs (a_maps HS) 0%nat in
  let S1 := fold_left (fun s i => orS s (node_opt_absent [ELit (Z.of_nat i)] s)) ixs S in
  let needph := existsb is_phantom_vis (a_vis HS) && negb (existsb is_phantom_vis (a_vis S1)) in
  let S2 := if needph then orS S1 (node_vis_phantom A LIMIT [] S1) else S1 in
  let ops := vis_ops (Datatypes.S (length (a_vis HS))) 0%nat (a_vis S2) (a_vis HS) in
  let S3 := fold_left (fun s o => let '(mv, i, j) := o in
                                  orS s (if mv : bool then node_vis_move [ELit (Z.of_nat i); ELit (Z.of_nat j)] s
                                         else node_vis_dup LIMIT [ELit (Z.of_nat i); ELit (Z.of_nat j)] s)) ops S2 in
  let tail := fold_right PFact (PHandoff h) (pads S3 HS) in
  let p3 := fold_right (fun o k => let '(mv, i, j) := o in PExt (if mv : bool then 48 else 47) [ELit (Z.of_nat i); ELit (Z.of_nat j)] k) tail ops in
  let p2 := if needph then PExt 45 [] p3 else p3 in
  fold_right (fun i k => PExt 44 [ELit (Z.of_nat i)] k) p2 ixs.
