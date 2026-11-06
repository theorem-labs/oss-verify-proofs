(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Module GN.
Definition GEN_ID : nat := 120.

(* [comment removed for export] *)
Record rrule := RR { rr_b : expr; rr_c : Z; rr_s : Z; rr_lo : Z; rr_hi : Z; rr_m : Z }.
Definition KC_CONTENT : Z := 1. Definition KC_WR : Z := 2. Definition KC_DISJ : Z := 4. Definition KC_EXPR : Z := 8. Definition KC_VIS : Z := 16.
Fixpoint parse_rules (l : list expr) : option (list rrule) :=
  match l with
  | [] => Some []
  | b :: ELit c :: ELit s :: ELit wlo :: ELit whi :: ELit m :: t =>
      match parse_rules t with Some r => Some (RR b c s wlo whi m :: r) | None => None end
  | _ => None
  end.

Fixpoint summands (fuel : nat) (x : expr) : list expr :=
  match fuel with O => [x] | S f => match x with EAlu ALU_ADD a b => summands f a ++ summands f b | _ => [x] end end.
Definition has_b0 (b0 b : expr) : bool :=
  let bs := summands 8 b in forallb (fun a => existsb (expr_eqb a) bs) (summands 8 b0).
Definition rr_hit (kc : Z) (r : rrule) (b : expr) (z : Z) : bool :=
  (Z.testbit (rr_m r) (Z.log2 kc) && has_b0 (rr_b r) b && Z.leb (rr_c r + rr_lo r) z && Z.ltb z (rr_c r + rr_hi r))%bool.
Definition rr_nbx (J : nat) (r : rrule) (b : expr) : expr := eadd b (escale (rr_s r) (EVar J)).
Fixpoint rb_find (kc : Z) (rs : list rrule) (b : expr) (z : Z) : option rrule :=
  match rs with [] => None | r :: t => if rr_hit kc r b z then Some r else rb_find kc t b z end.
Definition rb_addr (kc : Z) (J : nat) (rs : list rrule) (a : saddr) : saddr :=
  match rb_find kc rs (a_base a) (a_off a) with Some r => SA (rr_nbx J r (a_base a)) (a_off a - rr_c r) | None => a end.
Fixpoint rb_exprk (kc : Z) (J : nat) (rs : list rrule) (x : expr) : expr :=
  match x with
  | EAlu op a b =>
      match op, b with
      | ALU_ADD, ELit z => match rb_find kc rs a z with
                           | Some r => eaddz (rr_nbx J r a) (z - rr_c r)
                           | None => mkAlu op (rb_exprk kc J rs a) b
                           end
      | _, _ => mkAlu op (rb_exprk kc J rs a) (rb_exprk kc J rs b)
      end
  | EAluw op a b => mkAluw op (rb_exprk kc J rs a) (rb_exprk kc J rs b)
  | EMd op a b => mkMd op (rb_exprk kc J rs a) (rb_exprk kc J rs b)
  | EMdw op a b => mkMdw op (rb_exprk kc J rs a) (rb_exprk kc J rs b)
  | EExt sx lo n a => EExt sx lo n (rb_exprk kc J rs a)
  | _ => x
  end.
Definition rb_expr (J : nat) (rs : list rrule) (x : expr) : expr := rb_exprk KC_EXPR J rs x.
Definition rb_k (J : nat) (rs : list rrule) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (rb_addr KC_CONTENT J rs a) w (rb_expr J rs v)
  | KZero a n => KZero (rb_addr KC_CONTENT J rs a) (rb_expr J rs n)
  | KBlob a n k => KBlob (rb_addr KC_CONTENT J rs a) (rb_expr J rs n) k
  | KWr a n => KWr (rb_addr KC_WR J rs a) (rb_expr J rs n)
  | KDisj a1 n1 a2 n2 => KDisj (rb_addr KC_DISJ J rs a1) (rb_expr J rs n1) (rb_addr KC_DISJ J rs a2) (rb_expr J rs n2)
  | KFill a n c => KFill (rb_addr KC_CONTENT J rs a) (rb_expr J rs n) c
  | KUnk a n => KUnk (rb_addr KC_CONTENT J rs a) (rb_expr J rs n)
  | KRange x lo hi => KRange (rb_expr J rs x) lo hi
  | KAlign x m => KAlign (rb_expr J rs x) m
  | _ => K
  end.
Definition rb_p (J : nat) (rs : list rrule) (p : expr * expr) : expr * expr := (rb_exprk KC_VIS J rs (fst p), rb_exprk KC_VIS J rs (snd p)).
(* [comment removed for export] *)
Definition rebase (J : nat) (rs : list rrule) (cs : acs) : acs :=
  ACS (mk_ss (pc cs) (map (rb_expr J rs) (s_regs (a_ss cs))) (map (rb_k J rs) (kn cs)) (nxt cs))
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (map (rb_p J rs) (a_vis cs)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rs_addr (k0 : list kentry) (x y : saddr) : bool :=
  saddr_eqb x y ||
  (let d := a_off y - a_off x in
   Z.leb 0 d && expr_eqb (a_base x) (eaddz (a_base y) d)
   && match xhi k0 (a_base y) with Some h => Z.ltb (h + d) two64 | None => false end).
Definition rs_k (k0 : list kentry) (x y : kentry) : bool :=
  kentry_eqb x y ||
  match x, y with
  | KWord a w v, KWord a' w' v' => rs_addr k0 a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => rs_addr k0 a a' && expr_eqb n n'
  | KBlob a n b, KBlob a' n' b' => rs_addr k0 a a' && expr_eqb n n' && Nat.eqb b b'
  | KWr a n, KWr a' n' => rs_addr k0 a a' && expr_eqb n n'
  | KFill a n c, KFill a' n' c' => rs_addr k0 a a' && expr_eqb n n' && Z.eqb c c'
  | KUnk a n, KUnk a' n' => rs_addr k0 a a' && expr_eqb n n'
  | KDisj a1 n1 a2 n2, KDisj b1 m1 b2 m2 => rs_addr k0 a1 b1 && expr_eqb n1 m1 && rs_addr k0 a2 b2 && expr_eqb n2 m2
  | _, _ => false
  end.
Fixpoint rs_kn (k0 : list kentry) (xs ys : list kentry) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => rs_k k0 x y && rs_kn k0 xs' ys'
  | _, _ => false
  end.
Definition acs_rs_eqb (x y : acs) : bool :=
  (Z.eqb (pc x) (pc y) && list_eqb expr_eqb (s_regs (a_ss x)) (s_regs (a_ss y))
   && match s_log (a_ss x), s_log (a_ss y) with [], [] => true | _, _ => false end
   && rs_kn (kn y) (kn x) (kn y) && Nat.eqb (nxt x) (nxt y)
   && match s_resv (a_ss x), s_resv (a_ss y) with None, None => true | _, _ => false end
   && list_eqb amap_eqb (a_maps x) (a_maps y) && Z.eqb (a_totsz x) (a_totsz y)
   && Z.eqb (a_ylo x) (a_ylo y) && Z.eqb (a_eager x) (a_eager y)
   && list_eqb pair_eqb (a_vis x) (a_vis y) && list_eqb pair_eqb (a_ghost x) (a_ghost y)
   && Z.eqb (a_abytes x) (a_abytes y) && expr_eqb (a_brk x) (a_brk y) && afd_eqb (a_fd x) (a_fd y)
   && Bool.eqb (a_tidset x) (a_tidset y))%bool.

Definition node_rebase (nx0 : nat) (cs : acs) (args : list expr) : option acs :=
  match args with
  | ELit q :: ELit lo :: ELit hi :: rl =>
      match parse_rules rl with
      | Some rs =>
          let J := nxt cs in
          let cs1 := rebase J rs cs in
          if (fresh_ok nx0 cs && acs_rs_eqb (inst cs1 J (ELit q)) (inst cs J (ELit q))
              && Z.leb lo q && Z.leb q hi && Z.leb 0 q && Z.ltb q two64)%bool
          then Some (bump (add_kn cs1 [KRange (EVar J) lo hi]) 1)
          else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition ZSUB_ID : nat := 121.
Definition zs_covers (b : expr) (a m : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA b' o) (ELit L) => (expr_eqb b b' && Z.leb o a && Z.leb (a + m) (o + L) && Z.leb 0 L && Z.ltb L two64)%bool
  | _ => false
  end.
Definition node_zerosub (cs : acs) (args : list expr) : option acs :=
  match args with
  | [b; ELit a; ELit m] =>
      if (Z.ltb 0 m && existsb (zs_covers b a m) (kn cs))%bool then Some (set_kn cs (KZero (SA b a) (ELit m) :: kn cs)) else None
  | _ => None
  end.

Definition xn (nx0 : nat) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id GEN_ID then node_rebase nx0 cs args
  else if Nat.eqb id ZSUB_ID then node_zerosub cs args
  else None.
End GN.
