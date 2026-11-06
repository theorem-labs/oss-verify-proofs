(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan CxTmpl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import CAP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition renorm (cs : acs) : acs := inst cs 0%nat (EVar 0%nat).

(* [comment removed for export] *)
Definition compactT (vs top : nat) (cs : acs) : acs :=
  match mk_fwd (compact_map vs cs) with
  | Some fw => renorm (rename_cs fw cs top)
  | None => cs
  end.

Definition au_fold_raw (VS TOP : nat) (ls : list acs) : option acs :=
  match ls with
  | [] => None
  | l :: r => fold_left (fun ot li => match ot with
                                      | Some t => match au_state (Nat.max VS (csmaxv t)) TOP t li with Some (t', _, _) => Some t' | None => None end
                                      | None => None end) r (Some l)
  end.
Definition au_fold0 (VS TOP : nat) (ls : list acs) : option acs :=
  match au_fold_raw VS TOP ls with Some t => Some (compactT VS TOP t) | None => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sub : Type := list (nat * expr).
Definition sub_find (s : sub) (x : nat) : option expr :=
  match List.find (fun p => Nat.eqb (fst p) x) s with Some p => Some (snd p) | None => None end.

Section Match.
Variable VS : nat.
Fixpoint match_e (t e : expr) (s : sub) {struct t} : option sub :=
  match t with
  | EVar x => if Nat.leb VS x then
                match sub_find s x with
                | Some e' => if expr_eqb e e' then Some s else None
                | None => Some ((x, e) :: s)
                end
              else if expr_eqb t e then Some s else None
  | EAlu o a b => match e with
                  | EAlu o' a' b' => if aluop_eqb o o' then match match_e a a' s with Some s1 => match_e b b' s1 | None => None end else None
                  | _ => None end
  | EMd o a b => match e with
                 | EMd o' a' b' => if mulop_eqb o o' then match match_e a a' s with Some s1 => match_e b b' s1 | None => None end else None
                 | _ => None end
  | _ => if expr_eqb t e then Some s else None
  end.
(* [comment removed for export] *)
Definition match_old (t e : expr) (s : sub) : bool :=
  match match_e t e s with Some s' => Nat.eqb (length s') (length s) | None => false end.
Definition match_addr (a b : saddr) (s : sub) : bool := (Z.eqb (a_off a) (a_off b) && match_old (a_base a) (a_base b) s)%bool.

Definition match_k (T L : kentry) (s : sub) : option sub :=
  match T, L with
  | KWord a w v, KWord a' w' v' => if (Nat.eqb w w' && match_addr a a' s)%bool then match_e v v' s else None
  | KZero a n, KZero a' n' => if (match_addr a a' s && match_old n n' s)%bool then Some s else None
  | KUnk a n, KUnk a' n' => if (match_addr a a' s && match_old n n' s)%bool then Some s else None
  | KWr a n, KWr a' n' => if (match_addr a a' s && match_old n n' s)%bool then Some s else None
  | KBlob a n k, KBlob a' n' k' => if (Nat.eqb k k' && match_addr a a' s && match_old n n' s)%bool then Some s else None
  | KFill a n c, KFill a' n' c' => if (Z.eqb c c' && match_addr a a' s && match_old n n' s)%bool then Some s else None
  | KDisj a n b m, KDisj a' n' b' m' =>
      if (match_addr a a' s && match_old n n' s && match_addr b b' s && match_old m m' s)%bool then Some s else None
  | KImg lo hi, KImg lo' hi' => if (Z.eqb lo lo' && Z.eqb hi hi')%bool then Some s else None
  | _, _ => None
  end.
Fixpoint match_first (T : kentry) (l : list kentry) (s : sub) : option sub :=
  match l with
  | [] => None
  | L :: r => match match_k T L s with Some s' => Some s' | None => match_first T r s end
  end.
Definition is_pure (K : kentry) : bool := match K with KRange _ _ _ | KAlign _ _ => true | _ => false end.
(* [comment removed for export] *)
Fixpoint match_kn (tk lk : list kentry) (s : sub) (bad : list kentry) : sub * list kentry :=
  match tk with
  | [] => (s, bad)
  | T :: r => if is_pure T then match_kn r lk s bad else
              match match_first T lk s with
              | Some s' => match_kn r lk s' bad
              | None => match_kn r lk s (T :: bad)
              end
  end.
Fixpoint match_list (ts es : list expr) (s : sub) : option sub :=
  match ts, es with
  | [], [] => Some s
  | t :: tr, e :: er => match match_e t e s with Some s1 => match_list tr er s1 | None => None end
  | _, _ => None
  end.
Fixpoint match_maps (tm lm : list amap) (s : sub) : option sub :=
  match tm, lm with
  | [], [] => Some s
  | a :: r1, b :: r2 => if mkind_eqb (am_kind a) (am_kind b) then
                          match match_e (am_base a) (am_base b) s with
                          | Some s1 => match match_e (am_len a) (am_len b) s1 with Some s2 => match_maps r1 r2 s2 | None => None end
                          | None => None end
                        else None
  | _, _ => None
  end.
Fixpoint match_pairs (tp lp : list (expr * expr)) (s : sub) : option sub :=
  match tp, lp with
  | [], [] => Some s
  | a :: r1, b :: r2 => match match_e (fst a) (fst b) s with
                        | Some s1 => match match_e (snd a) (snd b) s1 with Some s2 => match_pairs r1 r2 s2 | None => None end
                        | None => None end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition match_state (T L : acs) : option (sub * list kentry) :=
  match match_maps (a_maps T) (a_maps L) [] with
  | Some s1 =>
    match match_pairs (a_vis T) (a_vis L) s1 with
    | Some s2 =>
      match match_pairs (a_ghost T) (a_ghost L) s2 with
      | Some s3 =>
        match match_list (s_regs (a_ss T)) (s_regs (a_ss L)) s3 with
        | Some s4 =>
          match match_e (a_brk T) (a_brk L) s4 with
          | Some s5 => Some (match_kn (kn T) (kn L) s5 [])
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.
End Match.

Definition sig_of (VS : nat) (T L : acs) : sub := match match_state VS T L with Some (s, _) => s | None => [] end.
Definition bad_of (VS : nat) (T L : acs) : option (list kentry) := match match_state VS T L with Some (_, b) => Some b | None => None end.

(* [comment removed for export] *)
Definition loop_inv (J : nat) (steps : list (nat * Z)) (s : acs) : acs :=
  let regs := fold_left (fun rs p => sr_upd rs (fst p) (eadd (nth (fst p) rs (ELit 0)) (escale (snd p) (EVar J)))) steps (s_regs (a_ss s)) in
  with_ss s (mk_ss (pc s) regs (kn s) (S J)).
(* [comment removed for export] *)
Definition pure_extra (VS : nat) (T l : acs) : list kentry :=
  List.filter (fun K => match K with KRange _ _ _ | KAlign _ _ => (CAP.kentry_vars_lt VS K && negb (existsb (kentry_eqb K) (kn T)))%bool | _ => false end) (kn l).
(* [comment removed for export] *)
Definition pure_of (VS : nat) (l : acs) : list kentry :=
  List.filter (fun K => match K with KRange _ _ _ | KAlign _ _ => CAP.kentry_vars_lt VS K | _ => false end) (kn l).

(* [comment removed for export] *)
Definition bad_list (VS : nat) (T : acs) (ls : list acs) : list kentry :=
  flat_map (fun l => match bad_of VS T l with Some b => b | None => [] end) ls.
Fixpoint gen_bad (bad : list kentry) (k : list kentry) (nx : nat) : list kentry * nat :=
  match k with
  | [] => ([], nx)
  | K :: r =>
      if existsb (kentry_eqb K) bad then
        match K with
        | KWord a w _ => let (r', nx') := gen_bad bad r (S nx) in (KWord a w (EVar nx) :: r', nx')
        | _ => gen_bad bad r nx
        end
      else let (r', nx') := gen_bad bad r nx in (K :: r', nx')
  end.
Definition au_fold (VS TOP : nat) (ls : list acs) : option acs :=
  match au_fold0 VS TOP ls with
  | Some t =>
      match bad_list VS t ls with
      | [] => Some t
      | bad => let (k', _) := gen_bad bad (kn t) (S (Nat.max VS (csmaxv t))) in Some (set_kn t k')
      end
  | None => None
  end.
