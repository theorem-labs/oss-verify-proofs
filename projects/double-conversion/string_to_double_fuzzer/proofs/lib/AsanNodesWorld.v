(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3B AsanPlanCore AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC. Import AP. Import Instr.
Open Scope Z_scope.

Module XWD.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint erepl (c t : expr) (x : expr) : expr :=
  if expr_eqb x c then t else
  match x with
  | EAlu op a b => EAlu op (erepl c t a) (erepl c t b)
  | EAluw op a b => EAluw op (erepl c t a) (erepl c t b)
  | EMd op a b => EMd op (erepl c t a) (erepl c t b)
  | EMdw op a b => EMdw op (erepl c t a) (erepl c t b)
  | EExt sx lo n a => EExt sx lo n (erepl c t a)
  | _ => x
  end.
Definition arepl (c t : expr) (a : saddr) : saddr := SA (erepl c t (a_base a)) (a_off a).
Definition krepl (c t : expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (arepl c t a) w (erepl c t v)
  | KZero a n => KZero (arepl c t a) (erepl c t n)
  | KBlob a n k => KBlob (arepl c t a) (erepl c t n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (erepl c t x) m
  | KRange x lo hi => KRange (erepl c t x) lo hi
  | KWr a n => KWr (arepl c t a) (erepl c t n)
  | KDisj a1 n1 a2 n2 => KDisj (arepl c t a1) (erepl c t n1) (arepl c t a2) (erepl c t n2)
  | KFill a n f => KFill (arepl c t a) (erepl c t n) f
  | KUnk a n => KUnk (arepl c t a) (erepl c t n)
  end.
Definition prepl (c t : expr) (p : expr * expr) : expr * expr := (erepl c t (fst p), erepl c t (snd p)).
Definition mrepl (c t : expr) (m : amap) : amap := AM (erepl c t (am_base m)) (erepl c t (am_len m)) (am_kind m).
(* [comment removed for export] *)
Definition mlrepl (c t : expr) (m : amap) : amap := AM (am_base m) (erepl c t (am_len m)) (am_kind m).
Definition frepl (c t : expr) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (erepl c t l) (erepl c t o) | _ => f end.
Definition srepl (c t : expr) (cs : acs) : acs :=
  ACS (mk_ss (pc cs) (map (erepl c t) (s_regs (a_ss cs))) (map (krepl c t) (kn cs)) (nxt cs))
      (map (mrepl c t) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (map (prepl c t) (a_vis cs)) (map (prepl c t) (a_ghost cs)) (a_abytes cs)
      (erepl c t (a_brk cs)) (frepl c t (a_fd cs)) (a_tidset cs).
Fixpoint srepls (J : nat) (e : expr) (ts : list expr) (cs : acs) : acs :=
  match ts with [] => cs | t :: r => srepls J e r (srepl (esubst J e t) t cs) end.

Definition ss_eqb (x y : sym_state) : bool :=
  (Z.eqb (s_pc x) (s_pc y) && list_eqb expr_eqb (s_regs x) (s_regs y)
   && match s_log x, s_log y with [], [] => true | _, _ => false end
   && list_eqb kentry_eqb (s_know x) (s_know y) && Nat.eqb (s_next x) (s_next y)
   && match s_resv x, s_resv y with None, None => true | _, _ => false end)%bool.
Definition acs_eqb (x y : acs) : bool :=
  (ss_eqb (a_ss x) (a_ss y) && list_eqb amap_eqb (a_maps x) (a_maps y) && Z.eqb (a_totsz x) (a_totsz y)
   && Z.eqb (a_ylo x) (a_ylo y) && Z.eqb (a_eager x) (a_eager y)
   && list_eqb pair_eqb (a_vis x) (a_vis y) && list_eqb pair_eqb (a_ghost x) (a_ghost y)
   && Z.eqb (a_abytes x) (a_abytes y) && expr_eqb (a_brk x) (a_brk y) && afd_eqb (a_fd x) (a_fd y)
   && Bool.eqb (a_tidset x) (a_tidset y))%bool.

Definition node_gen (nx0 : nat) (cs : acs) (args : list expr) : option acs :=
  match args with
  | e :: ELit lo :: ELit hi :: ts =>
      let J := nxt cs in
      let cs1 := srepls J e ts cs in
      if (fresh_ok nx0 cs && acs_eqb (inst cs1 J e) (inst cs J e)
          && match xlo (kn cs) e, xhi (kn cs) e with Some l, Some h => Z.leb lo l && Z.leb h hi | _, _ => false end)%bool
      then Some (bump (add_kn cs1 [KRange (EVar J) lo hi]) 1)
      else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint upd_nth {T} (f : T -> T) (i : nat) (l : list T) : list T :=
  match l with
  | [] => []
  | x :: r => match i with O => f x :: r | S i' => x :: upd_nth f i' r end
  end.
Definition srepl_at (c t : expr) (sel : Z) (cs : acs) : acs :=
  if (Z.leb 0 sel && Z.ltb sel 32)%bool then
    ACS (mk_ss (pc cs) (upd_nth (erepl c t) (Z.to_nat sel) (s_regs (a_ss cs))) (kn cs) (nxt cs))
        (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
  else if (Z.leb 1000 sel && Z.ltb sel 2000)%bool then
    ACS (a_ss cs) (upd_nth (mrepl c t) (Z.to_nat (sel - 1000)) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
        (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
  else if (Z.leb 2000 sel && Z.ltb sel 3000)%bool then
    ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
        (upd_nth (prepl c t) (Z.to_nat (sel - 2000)) (a_vis cs)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
  else if (Z.leb 3000 sel && Z.ltb sel 4000)%bool then
    ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
        (a_vis cs) (upd_nth (prepl c t) (Z.to_nat (sel - 3000)) (a_ghost cs)) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
  else if Z.eqb sel 4000 then
    ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
        (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (frepl c t (a_fd cs)) (a_tidset cs)
  else if Z.eqb sel 5000 then
    ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
        (a_vis cs) (a_ghost cs) (a_abytes cs) (erepl c t (a_brk cs)) (a_fd cs) (a_tidset cs)
  else if (Z.leb 6000 sel && Z.ltb sel 7000)%bool then
    ACS (a_ss cs) (upd_nth (mlrepl c t) (Z.to_nat (sel - 6000)) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
        (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
  else if Z.leb 10000 sel then
    ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (upd_nth (krepl c t) (Z.to_nat (sel - 10000)) (kn cs)) (nxt cs))
        (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
  else cs.
Definition srepl_sels (c t : expr) (sels : list Z) (cs : acs) : acs := fold_left (fun cs0 sel => srepl_at c t sel cs0) sels cs.
Fixpoint srepls_pos (J : nat) (e : expr) (ts : list expr) (sels : list Z) (cs : acs) : acs :=
  match ts with [] => cs | t :: r => srepls_pos J e r sels (srepl_sels (esubst J e t) t sels cs) end.
Fixpoint lits_of (l : list expr) : option (list Z) :=
  match l with [] => Some [] | ELit z :: r => match lits_of r with Some zs => Some (z :: zs) | None => None end | _ => None end.
(* [comment removed for export] *)
Fixpoint split_sep (l : list expr) : option (list expr * list Z) :=
  match l with
  | [] => None
  | x :: r => if expr_eqb x (ELit (-1)) then match lits_of r with Some zs => Some ([], zs) | None => None end
              else match split_sep r with Some (ts, zs) => Some (x :: ts, zs) | None => None end
  end.
Definition node_genp (nx0 : nat) (cs : acs) (args : list expr) : option acs :=
  match args with
  | e :: ELit lo :: ELit hi :: rest =>
      match split_sep rest with
      | Some (ts, sels) =>
          let J := nxt cs in
          let cs1 := srepls_pos J e ts sels cs in
          if (fresh_ok nx0 cs && acs_eqb (inst cs1 J e) (inst cs J e)
              && match xlo (kn cs) e, xhi (kn cs) e with Some l, Some h => Z.leb lo l && Z.leb h hi | _, _ => false end)%bool
          then Some (bump (add_kn cs1 [KRange (EVar J) lo hi]) 1)
          else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition with_vis (cs : acs) (v : list (expr * expr)) (ab : Z) : acs :=
  ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) v (a_ghost cs) ab (a_brk cs) (a_fd cs) (a_tidset cs).

Definition node_visdummy (LIMIT : Z) (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit i; b; s] =>
      if (Z.leb 0 i && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) s
          && match xhi (kn cs) s with Some h => Z.eqb h 0 | None => false end
          && Z.leb (a_eager cs + a_abytes cs + vis_cost 0) LIMIT)%bool
      then Some (with_vis cs (list_insert_nth (Z.to_nat i) (b, s) (a_vis cs)) (a_abytes cs + vis_cost 0))
      else None
  | _ => None
  end.

Definition node_kdisjempty (cs : acs) (args : list expr) : option acs :=
  match args with
  | [a1; n1; a2; n2] =>
      let '(b1, o1) := split_lit a1 in
      let '(b2, o2) := split_lit a2 in
      if (Z.leb 0 o1 && Z.eqb o2 0
          && match xhi (kn cs) b2 with Some h => Z.eqb h 0 | None => false end
          && match xhi (kn cs) n2 with Some h => Z.eqb h 0 | None => false end)%bool
      then Some (add_kn cs [KDisj (SA b1 o1) n1 (SA b2 o2) n2])
      else None
  | _ => None
  end.

Definition remove_nth {T} (i : nat) (l : list T) : list T := firstn i l ++ skipn (S i) l.
Definition node_visperm (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit i; ELit j] =>
      if (Z.leb 0 i && Z.leb 0 j)%bool then
        match nth_error (a_vis cs) (Z.to_nat i) with
        | Some p => Some (with_vis cs (list_insert_nth (Z.to_nat j) p (remove_nth (Z.to_nat i) (a_vis cs))) (a_abytes cs))
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint kdisj_relB0 (bc : AX2B.bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj (SA c1 o1) m1 (SA c2 o2) m2 :: rest =>
      if (if AX2B.xinside0B bc b1 k1 n1 c1 o1 m1 then AX2B.xinside0B bc b2 k2 n2 c2 o2 m2 else false) then true
      else if (if AX2B.xinside0B bc b1 k1 n1 c2 o2 m2 then AX2B.xinside0B bc b2 k2 n2 c1 o1 m1 else false) then true
      else kdisj_relB0 bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_relB0 bc rest b1 k1 n1 b2 k2 n2
  end.
(* [comment removed for export] *)
Definition rel1 (b c : expr) : bool := if novars c then true else shares_var b c.
Fixpoint kdisj_pass1B (bc : AX2B.bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj (SA c1 o1) m1 (SA c2 o2) m2 :: rest =>
      if (if rel1 b1 c1 then if rel1 b2 c2 then
            if AX2B.xinside0B bc b1 k1 n1 c1 o1 m1 then AX2B.xinside0B bc b2 k2 n2 c2 o2 m2 else false
          else false else false) then true
      else if (if rel1 b1 c2 then if rel1 b2 c1 then
                 if AX2B.xinside0B bc b1 k1 n1 c2 o2 m2 then AX2B.xinside0B bc b2 k2 n2 c1 o1 m1 else false
               else false else false) then true
      else kdisj_pass1B bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_pass1B bc rest b1 k1 n1 b2 k2 n2
  end.
Definition kdisj_relB (bc : AX2B.bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if kdisj_pass1B bc kn b1 k1 n1 b2 k2 n2 then true else kdisj_relB0 bc kn b1 k1 n1 b2 k2 n2.
Lemma kdisj_pass1B_rel0 : forall bc kn b1 k1 n1 b2 k2 n2,
  kdisj_pass1B bc kn b1 k1 n1 b2 k2 n2 = true -> kdisj_relB0 bc kn b1 k1 n1 b2 k2 n2 = true.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; cbn [kdisj_pass1B kdisj_relB0]; [discriminate|].
  destruct K as [| | | | | | |[c1 o1] m1 [c2 o2] m2| |]; try exact IH.
  destruct (rel1 b1 c1), (rel1 b2 c2), (rel1 b1 c2), (rel1 b2 c1);
  destruct (AX2B.xinside0B bc b1 k1 n1 c1 o1 m1), (AX2B.xinside0B bc b2 k2 n2 c2 o2 m2),
    (AX2B.xinside0B bc b1 k1 n1 c2 o2 m2), (AX2B.xinside0B bc b2 k2 n2 c1 o1 m1); cbn; auto.
Qed.
(* [comment removed for export] *)
Fixpoint kdisj_batch (bc : AX2B.bctx) (kn : list kentry) (nx : nat) (args : list expr) : option (list kentry) :=
  match args with
  | [] => Some []
  | b1 :: ELit k1 :: n1 :: b2 :: ELit k2 :: n2 :: rest =>
      if (expr_vars_lt nx b1 && expr_vars_lt nx n1 && expr_vars_lt nx b2 && expr_vars_lt nx n2)%bool
      then if kdisj_relB bc kn b1 k1 n1 b2 k2 n2
           then match kdisj_batch bc kn nx rest with Some l => Some (KDisj (SA b1 k1) n1 (SA b2 k2) n2 :: l) | None => None end
           else None
      else None
  | _ => None
  end.
Definition node_kdisjrel (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] => None
  | _ => match kdisj_batch (AX2B.mkbc (kn cs)) (kn cs) (nxt cs) args with Some l => Some (add_kn cs l) | None => None end
  end.


(* [comment removed for export] *)
Definition xn (nx0 : nat) (LIMIT : Z) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if (id =? 206)%nat then node_gen nx0 cs args
  else if (id =? 207)%nat then node_visdummy LIMIT cs args
  else if (id =? 208)%nat then node_kdisjempty cs args
  else if (id =? 209)%nat then node_visperm cs args
  else if (id =? 216)%nat then node_genp nx0 cs args
  else if (id =? 218)%nat then node_kdisjrel cs args
  else None.
End XWD.
