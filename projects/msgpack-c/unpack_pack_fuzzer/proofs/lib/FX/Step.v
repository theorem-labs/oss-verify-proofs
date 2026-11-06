(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St.
Open Scope Z_scope.

Module Step.

Fixpoint find_range (fs : list fact) (k : int) : option (w64 * w64) :=
  match fs with
  | [] => None
  | FRange k' lo hi :: fs' => if PrimInt63.eqb k k' then Some (lo, hi) else find_range fs' k
  | _ :: fs' => find_range fs' k
  end.

Fixpoint find_align (fs : list fact) (k : int) : int :=
  match fs with
  | [] => 0%uint63
  | FAlign k' m :: fs' => if PrimInt63.eqb k k' then m else find_align fs' k
  | _ :: fs' => find_align fs' k
  end.

Definition add_carries (a b : w64) : bool :=

  let s := wadd a b in wltu s a.
Definition nowrap (lo hi o : w64) : bool :=
  if wt o then add_carries lo o && add_carries hi o
  else negb (add_carries hi o) .

Definition nowrap_k (fs : list fact) (k : int) (o : w64) : bool :=
  match find_range fs k with
  | Some (lo, hi) => nowrap lo hi o
  | None => false
  end.

Definition soff_ltb (o1 o2 : w64) : bool := wlts o1 o2.

Fixpoint fact_lookup (fs : list fact) (p : fact -> bool) : bool :=
  match fs with [] => false | f :: fs' => if p f then true else fact_lookup fs' p end.

Definition is_FULt (a b : sv) (f : fact) : bool :=
  match f with FULt x y => sv_eqb x a && sv_eqb y b | _ => false end.
Definition is_FULe (a b : sv) (f : fact) : bool :=
  match f with FULe x y => sv_eqb x a && sv_eqb y b | _ => false end.
Definition is_FSLt (a b : sv) (f : fact) : bool :=
  match f with FSLt x y => sv_eqb x a && sv_eqb y b | _ => false end.
Definition is_FSLe (a b : sv) (f : fact) : bool :=
  match f with FSLe x y => sv_eqb x a && sv_eqb y b | _ => false end.
Definition is_FEq (a b : sv) (f : fact) : bool :=
  match f with FEq x y => (sv_eqb x a && sv_eqb y b) || (sv_eqb x b && sv_eqb y a) | _ => false end.
Definition is_FNe (a b : sv) (f : fact) : bool :=
  match f with FNe x y => (sv_eqb x a && sv_eqb y b) || (sv_eqb x b && sv_eqb y a) | _ => false end.

Definition lookup_ltu_lit_r (fs : list fact) (a : sv) (y : w64) : option bool :=
  if fact_lookup fs (fun f => match f with
                               | FULt x (VL y') => sv_eqb x a && wleu y' y
                               | FULe x (VL y') => sv_eqb x a && wltu y' y
                               | _ => false end)
  then Some true
  else if fact_lookup fs (fun f => match f with
                                    | FULe (VL y') x => sv_eqb x a && wleu y y'
                                    | FULt (VL y') x => sv_eqb x a && wleu y y'
                                    | FEq x (VL y') => sv_eqb x a && wleu y y'
                                    | FEq (VL y') x => sv_eqb x a && wleu y y'
                                    | _ => false end)
  then Some false
  else None.

Definition lookup_ltu_lit_l (fs : list fact) (x : w64) (b : sv) : option bool :=
  if fact_lookup fs (fun f => match f with
                               | FULt (VL x') z => sv_eqb z b && wleu x x'
                               | FULe (VL x') z => sv_eqb z b && wltu x x'
                               | _ => false end)
  then Some true
  else if fact_lookup fs (fun f => match f with
                                    | FULe z (VL x') => sv_eqb z b && wleu x' x
                                    | FULt z (VL x') => sv_eqb z b && wleu x' x
                                    | FEq z (VL x') => sv_eqb z b && wleu x' x
                                    | FEq (VL x') z => sv_eqb z b && wleu x' x
                                    | _ => false end)
  then Some false
  else None.

Definition bnd : Type := (w64 * w64)%type.
Definition full_bnd : bnd := (wzero, wones).

Definition lit_of (x : sv) : option w64 := match x with VL c => Some c | _ => None end.
Definition bump (b : bnd) (c : w64) : bnd :=
  let '(lo, hi) := b in
  ((if weqb lo c then wadd c wone else lo), (if weqb hi c then wsub c wone else hi)).
Definition fact_bnd1 (f : fact) (v : sv) (b : bnd) : bnd :=
  let '(lo, hi) := b in
  match f with
  | FULt x y =>
      match lit_of y with
      | Some c => if sv_eqb x v then (lo, wminu hi (wsub c wone)) else b
      | None => match lit_of x with
                | Some c => if sv_eqb y v then (wmaxu lo (wadd c wone), hi) else b
                | None => b
                end
      end
  | FULe x y =>
      match lit_of y with
      | Some c => if sv_eqb x v then (lo, wminu hi c) else b
      | None => match lit_of x with
                | Some c => if sv_eqb y v then (wmaxu lo c, hi) else b
                | None => b
                end
      end
  | FEq x y =>
      match lit_of y with
      | Some c => if sv_eqb x v then (wmaxu lo c, wminu hi c) else b
      | None => match lit_of x with
                | Some c => if sv_eqb y v then (wmaxu lo c, wminu hi c) else b
                | None => b
                end
      end
  | FNe x y =>
      match lit_of y with
      | Some c => if sv_eqb x v then bump b c else b
      | None => match lit_of x with
                | Some c => if sv_eqb y v then bump b c else b
                | None => b
                end
      end
  | _ => b
  end.

Definition anchored (k : int) (a : sv) : option (w64 * option sv) :=
  match a with
  | VP k' o => if PrimInt63.eqb k' k then Some (o, None) else None
  | VAlu ALU_ADD (VP k' o) y => if PrimInt63.eqb k' k then Some (o, Some y) else None
  | VAlu ALU_ADD y (VP k' o) => if PrimInt63.eqb k' k then Some (o, Some y) else None
  | _ => None
  end.
Definition anchor_of (a : sv) : option int :=
  match a with
  | VP k _ | VAlu ALU_ADD (VP k _) _ | VAlu ALU_ADD _ (VP k _) => Some k
  | _ => None
  end.

Definition anchor_norm (f : fact) : fact :=
  let norm (mk : sv -> sv -> fact) (a b : sv) :=
    match anchor_of a with
    | Some k =>
        match anchored k a, anchored k b with
        | Some (o, None), Some (o', Some y) | Some (o', Some y), Some (o, None) => mk y (VL (wsub o o'))
        | Some (o, Some y), Some (o', Some y') => if weqb o o' then mk y y' else f
        | _, _ => f
        end
    | None => f
    end in
  match f with
  | FEq a b => norm FEq a b
  | FNe a b => norm FNe a b
  | _ => f
  end.

Fixpoint fact_bounds (fs : list fact) (v : sv) (b : bnd) : bnd :=
  match fs with
  | [] => b
  | f :: fs' => fact_bounds fs' v (fact_bnd1 (anchor_norm f) v b)
  end.

Definition bnd_add (x y : bnd) : bnd :=
  let '(lx, hx) := x in let '(ly, hy) := y in
  if add_carries hx hy then full_bnd else (wadd lx ly, wadd hx hy).
Definition bnd_sub (x y : bnd) : bnd :=
  let '(lx, hx) := x in let '(ly, hy) := y in
  if wltu lx hy then full_bnd else (wsub lx hy, wsub hx ly).

Definition wneg (c : w64) : w64 := wsub wzero c.
Definition bnd_addv (rec : sv -> bnd) (x y : sv) : bnd :=
  match y with
  | VL c => if wt c then bnd_sub (rec x) (wneg c, wneg c) else bnd_add (rec x) (c, c)
  | _ => bnd_add (rec x) (rec y)
  end.

Definition bnd_below (b : bnd) (lim : w64) (dflt : bnd) : bnd :=
  if wltu (snd b) lim then b else dflt.
Definition bit31w : w64 := W64 false bit31i.
Definition bit32w : w64 := W64 false (PrimInt63.lsl 1%uint63 32%uint63).

Definition ext_lim (sx : bool) (n : int) : w64 :=
  W64 false (PrimInt63.lsl 1%uint63 (PrimInt63.sub (PrimInt63.lsl n 3%uint63) (if sx then 1%uint63 else 0%uint63))).

Definition bnd_struct (rec : sv -> bnd) (fs : list fact) (v : sv) : bnd :=
  match v with
  | VL x => (x, x)
  | VP k o =>
      match find_range fs k with
      | Some (lo, hi) => if nowrap lo hi o then (wadd lo o, wadd hi o) else full_bnd
      | None => full_bnd
      end
  | VExt sx lo n x =>
      if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 8%uint63 then rec x
      else if PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63 then
        let dflt := if sx then full_bnd
                    else match umax_of_width n with Some m => (wzero, m) | None => full_bnd end in
        if PrimInt63.eqb lo 0%uint63 then bnd_below (rec x) (ext_lim sx n) dflt else dflt
      else full_bnd
  | VBlob false _ _ n | VBg false _ _ n =>
      match umax_of_width n with Some m => (wzero, m) | None => full_bnd end
  | VAlu ALU_AND x y => (wzero, wminu (snd (rec x)) (snd (rec y)))
  | VAlu ALU_OR x y | VAlu ALU_XOR x y =>
      let hx := snd (rec x) in let hy := snd (rec y) in
      if add_carries hx hy then full_bnd else (wzero, wadd hx hy)
  | VAlu ALU_ADD x y => bnd_addv rec x y
  | VAlu ALU_SUB x y => bnd_sub (rec x) (rec y)
  | VAlu ALU_SRL x (VL s) => let '(l, h) := rec x in (wsrl l s, wsrl h s)
  | VAlu ALU_SLL x (VL s) =>
      let '(l, h) := rec x in
      if wleu h (wsrl wones s) then (wsll l s, wsll h s) else full_bnd
  | VAlu ALU_SLTU _ _ | VAlu ALU_SLT _ _ => (wzero, wone)
  | VAluw ALU_ADD x y => bnd_below (bnd_addv rec x y) bit31w full_bnd
  | VAluw ALU_SUB x y => bnd_below (bnd_sub (rec x) (rec y)) bit31w full_bnd
  | VMd M_MUL x y =>
      let '(lx, hx) := rec x in let '(ly, hy) := rec y in
      if wltu hx bit32w && wltu hy bit32w then (wmul lx ly, wmul hx hy) else full_bnd
  | _ => full_bnd
  end.

Definition align_bnd (fs : list fact) (k : int) (b : bnd) : bnd :=
  let m := find_align fs k in
  if PrimInt63.ltb 0%uint63 m && PrimInt63.leb m 62%uint63 then
    let mask := PrimInt63.sub (PrimInt63.lsl 1%uint63 m) 1%uint63 in
    let '(lo, hi) := b in
    let rh := PrimInt63.land (wl hi) mask in
    let hi' := wsub hi (W64 false rh) in
    let rl := PrimInt63.land (wl lo) mask in
    let lo' := if PrimInt63.eqb rl 0%uint63 then lo
               else let l2 := wadd lo (W64 false (PrimInt63.sub (PrimInt63.lsl 1%uint63 m) rl)) in
                    if wltu l2 lo then lo else l2 in
    (lo', hi')
  else b.

Definition bnd_meet (x y : bnd) : bnd := (wmaxu (fst x) (fst y), wminu (snd x) (snd y)).
Definition bnd_shift (b : bnd) (o : w64) : option bnd :=
  if nowrap (fst b) (snd b) o && wleu (fst b) (snd b) then Some (wadd (fst b) o, wadd (snd b) o) else None.

Definition var_bounds (fs : list fact) (k : int) : bnd :=
  let v := VP k wzero in
  align_bnd fs k (fact_bounds fs v (fact_bounds fs v (bnd_struct (fun _ => full_bnd) fs v))).

Definition nowrap_kb (fs : list fact) (k : int) (o : w64) : bool :=
  if nowrap_k fs k o then true else (let '(lo, hi) := var_bounds fs k in nowrap lo hi o).

Fixpoint sv_bounds (fs : list fact) (v : sv) {struct v} : bnd :=
  let b0 := bnd_struct (sv_bounds fs) fs v in
  match v with
  | VL _ => b0
  | VP k o =>
      if weqb o wzero then var_bounds fs k
      else let b1 := fact_bounds fs v (fact_bounds fs v b0) in
           match bnd_shift (var_bounds fs k) o with Some bs => bnd_meet b1 bs | None => b1 end
  | _ => fact_bounds fs v (fact_bounds fs v b0)
  end.

Definition bnd_ltu (fs : list fact) (a b : sv) : option bool :=
  let '(la, ha) := sv_bounds fs a in let '(lb, hb) := sv_bounds fs b in
  if wltu ha lb then Some true else if wleu hb la then Some false else None.

Definition bnd_eq0 (fs : list fact) (v : sv) : option bool :=
  let '(l, h) := sv_bounds fs v in
  if wltu wzero l then Some false else if weqb h wzero then Some true else None.

Definition lterm : Type := list (sv * Z).
Definition lin : Type := (lterm * Z)%type.

Fixpoint lt_add1 (t : lterm) (a : sv) (c : Z) : lterm :=
  match t with
  | [] => if (c =? 0)%Z then [] else [(a, c)]
  | (a', c') :: t' =>
      if sv_eqb a a' then (let c2 := (c' + c)%Z in if (c2 =? 0)%Z then t' else (a', c2) :: t')
      else (a', c') :: lt_add1 t' a c
  end.

Fixpoint lt_merge (t u : lterm) (s : Z) : lterm :=
  match u with
  | [] => t
  | (a, c) :: u' => lt_merge (lt_add1 t a (s * c)%Z) u' s
  end.
Definition l_comb (x : lin) (s : Z) (y : lin) : lin := (lt_merge (fst x) (fst y) s, (snd x + s * snd y)%Z).
Definition l_atom (v : sv) : lin := ([(v, 1%Z)], 0%Z).
Definition l_const (c : Z) : lin := ([], c).
Definition l_isconst (l : lin) : option Z := match fst l with [] => Some (snd l) | _ => None end.

Definition gapc : Type := (lin * Z * bool)%type.

Definition lt_scale (c : Z) (t : lterm) : lterm := if (c =? 0)%Z then [] else map (fun ac => (fst ac, c * snd ac)%Z) t.
Definition l_scale (c : Z) (l : lin) : lin := (lt_scale c (fst l), (c * snd l)%Z).

Definition l_nonnegb (l : lin) : bool := List.forallb (fun ac => (0 <=? snd ac)%Z) (fst l) && (0 <=? snd l)%Z.

Fixpoint lt_coeff (t : lterm) (a : sv) : option Z :=
  match t with [] => None | (a', c) :: t' => if sv_eqb a a' then Some c else lt_coeff t' a end.

Fixpoint ratio_t (dt : lterm) (gt : lterm) : Z :=
  match gt with
  | [] => 0%Z
  | (a, cg) :: gt' => match lt_coeff dt a with
                     | Some cd => if ((cg =? 0) || negb (cd mod cg =? 0))%Z then ratio_t dt gt' else (cd / cg)%Z
                     | None => ratio_t dt gt'
                     end
  end.
Definition ratio (d g : lin) : Z := ratio_t (fst d) (fst g).

Definition term_lo (s : Z) (c : gapc) : option Z :=
  let '(_, lb, e) := c in if (0 <? s)%Z then Some (s * lb)%Z else if e then Some 0%Z else None.
Definition term_hi (s : Z) (c : gapc) : option Z :=
  let '(_, lb, e) := c in if (0 <? s)%Z then (if e then Some 0%Z else None) else Some (s * lb)%Z.
Definition oadd (a b : option Z) : option Z :=
  match a, b with Some x, Some y => Some (x + y)%Z | _, _ => None end.
Fixpoint sel_rest (d : lin) (sel : list (Z * gapc)) : lin :=
  match sel with
  | [] => d
  | (s, (g, _, _)) :: sel' => sel_rest (l_comb d (- s)%Z g) sel'
  end.
Fixpoint sel_lo (sel : list (Z * gapc)) : option Z :=
  match sel with [] => Some 0%Z | (s, c) :: sel' => oadd (term_lo s c) (sel_lo sel') end.
Fixpoint sel_hi (sel : list (Z * gapc)) : option Z :=
  match sel with [] => Some 0%Z | (s, c) :: sel' => oadd (term_hi s c) (sel_hi sel') end.
Definition sel_ok (sel : list (Z * gapc)) : bool := List.forallb (fun sc => negb (fst sc =? 0)%Z) sel.

Definition lt_allb (p : Z -> bool) (t : lterm) : bool := List.forallb (fun ac => p (snd ac)) t.
Definition is_any_link (f : fact) : bool :=
  match f with
  | FEq (VP _ _) (VAlu ALU_ADD (VAlu ALU_SRL (VP _ _) (VL _)) (VL _)) => true
  | _ => false
  end.
Definition asan_on (fs : list fact) : bool := fact_lookup fs is_any_link.

Definition abtab : Type := (option (list fact) * list (sv * bnd))%type.
Definition atom_bounds (fs : list fact) (t : lterm) : abtab :=
  ((if asan_on fs then Some fs else None), map (fun ac => (fst ac, sv_bounds fs (fst ac))) t).
Fixpoint ab_find_l (fb : option (list fact)) (ab : list (sv * bnd)) (a : sv) : bnd :=
  match ab with
  | [] => match fb with Some fs => sv_bounds fs a | None => full_bnd end
  | (a', b) :: ab' => if sv_eqb a a' then b else ab_find_l fb ab' a
  end.
Definition ab_find (ab : abtab) (a : sv) : bnd := ab_find_l (fst ab) (snd ab) a.
Fixpoint lt_lo (ab : abtab) (t : lterm) : Z :=
  match t with
  | [] => 0
  | (a, c) :: t' => (let '(lo, hi) := ab_find ab a in if (0 <? c)%Z then c * w2Z lo else c * w2Z hi)%Z + lt_lo ab t'
  end.
Fixpoint lt_hi (ab : abtab) (t : lterm) : Z :=
  match t with
  | [] => 0
  | (a, c) :: t' => (let '(lo, hi) := ab_find ab a in if (0 <? c)%Z then c * w2Z hi else c * w2Z lo)%Z + lt_hi ab t'
  end.

Definition lin_bounds (ab : abtab) (d : lin) (sel : list (Z * gapc)) : option Z * option Z :=
  if sel_ok sel then
    let r := sel_rest d sel in
    (oadd (sel_lo sel) (Some (snd r + lt_lo ab (fst r))%Z), oadd (sel_hi sel) (Some (snd r + lt_hi ab (fst r))%Z))
  else (None, None).

Definition lin_try (ab : abtab) (d : lin) (sel : list (Z * gapc)) : option bool :=
  match lin_bounds ab d sel with
  | (Some l, _) => if (1 <=? l)%Z then Some true
                   else match lin_bounds ab d sel with (_, Some u) => if (u <=? 0)%Z then Some false else None | _ => None end
  | (None, Some u) => if (u <=? 0)%Z then Some false else None
  | _ => None
  end.
Definition lin_try_eq (ab : abtab) (d : lin) (sel : list (Z * gapc)) : option bool :=
  match lin_bounds ab d sel with
  | (Some l, Some u) => if ((l =? 0) && (u =? 0))%Z then Some true
                        else if ((1 <=? l) || (u <=? -1))%Z then Some false else None
  | (Some l, None) => if (1 <=? l)%Z then Some false else None
  | (None, Some u) => if (u <=? -1)%Z then Some false else None
  | (None, None) => None
  end.
Definition lin_try_nonneg (ab : abtab) (d : lin) (sel : list (Z * gapc)) : option bool :=
  match lin_bounds ab d sel with (Some l, _) => if (0 <=? l)%Z then Some true else None | _ => None end.

Fixpoint first_some {A B : Type} (f : A -> option B) (l : list A) : option B :=
  match l with [] => None | x :: l' => match f x with Some r => Some r | None => first_some f l' end end.

Definition cands1 (d : lin) (G : list gapc) : list (list (Z * gapc)) :=
  [] :: map (fun g => [(ratio d (fst (fst g)), g)]) G.
Definition cands2 (d : lin) (G : list gapc) : list (list (Z * gapc)) :=
  flat_map (fun g1 => let s1 := ratio d (fst (fst g1)) in
                      if (s1 =? 0)%Z then [] else
                      let d1 := l_comb d (- s1)%Z (fst (fst g1)) in
                      flat_map (fun g2 => let s2 := ratio d1 (fst (fst g2)) in
                                          if (s2 =? 0)%Z then [] else [[(s1, g1); (s2, g2)]]) G) G.

Definition lin_nonneg (G : list gapc) (fs : list fact) (d : lin) : bool :=
  if l_nonnegb d then true else match first_some (lin_try_nonneg (atom_bounds fs (fst d)) d) (cands1 d G) with Some true => true | _ => false end.

Definition low_mask_k (m : w64) : option int :=
  if wt m then None else
  let x := wl m in let m1 := PrimInt63.add x 1%uint63 in
  if PrimInt63.eqb (PrimInt63.land m1 x) 0%uint63 && negb (PrimInt63.eqb x 0%uint63) && PrimInt63.ltb x bit62i
  then Some (PrimInt63.sub 62%uint63 (PrimInt63.head0 m1)) else None.

Fixpoint linz (G : list gapc) (fs : list fact) (v : sv) {struct v} : lin :=
  match v with
  | VL c => l_const (w2Z c)
  | VP k o =>
      if weqb o wzero then l_atom v
      else if nowrap_kb fs k o then l_comb (l_atom (VP k wzero)) 1 (l_const (w2Zs o))
      else l_atom v
  | VAlu ALU_ADD x y =>
      match y with
      | VL c =>
          if wt c then
            (let d := l_comb (linz G fs x) (-1) (l_const (w2Z (wneg c))) in
             if (if wleu (wneg c) (fst (sv_bounds fs x)) then true else lin_nonneg G fs d) then d else l_atom v)
          else (if negb (add_carries (snd (sv_bounds fs x)) c) then l_comb (linz G fs x) 1 (l_const (w2Z c)) else l_atom v)
      | _ =>
          if negb (add_carries (snd (sv_bounds fs x)) (snd (sv_bounds fs y))) then l_comb (linz G fs x) 1 (linz G fs y)
          else l_atom v
      end
  | VAlu ALU_SUB x y =>
      let d := l_comb (linz G fs x) (-1) (linz G fs y) in
      if (if (if (if wleu (snd (sv_bounds fs y)) (fst (sv_bounds fs x)) then true
                  else fact_lookup fs (is_FULe y x)) then true else fact_lookup fs (is_FULt y x)) then true
          else lin_nonneg G fs d)
      then d else l_atom v
  | VAlu ALU_SLL x (VL s) =>
      if wleu (snd (sv_bounds fs x)) (wsrl wones s) then l_scale (2 ^ to_Z (shamt6 s)) (linz G fs x) else l_atom v
  | VAlu ALU_AND x (VL m) =>
      match low_mask_k m with
      | Some k => if PrimInt63.leb k 3%uint63 && asan_on fs
                  then l_comb (linz G fs x) (- 2 ^ to_Z k) (l_atom (VAlu ALU_SRL x (VL (wlit k)))) else l_atom v
      | None => l_atom v
      end
  | VMd M_MUL x (VL c) =>
      if wltu (snd (sv_bounds fs x)) bit32w && wltu c bit32w then l_scale (w2Z c) (linz G fs x) else l_atom v
  | VExt sx lo n x =>
      if PrimInt63.eqb lo 0%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63
         && wltu (snd (sv_bounds fs x)) (ext_lim sx n) then linz G fs x else l_atom v
  | VAluw ALU_ADD x (VL z) =>
      let hx := snd (sv_bounds fs x) in
      if negb (wt z) && negb (wt hx) && wltu (wadd hx z) bit31w then l_comb (linz G fs x) 1 (l_const (w2Z z)) else l_atom v
  | _ => l_atom v
  end.

Definition ne0_term (p q : sv) : option sv :=
  match q with
  | VL z => if weqb z wzero then Some p else None
  | _ => match p with VL z => if weqb z wzero then Some q else None | _ => None end
  end.
Definition gap_of (G : list gapc) (fs : list fact) (f : fact) : option gapc :=
  match f with
  | FULt p q => Some (l_comb (linz G fs q) (-1) (linz G fs p), 1%Z, false)
  | FULe p q => Some (l_comb (linz G fs q) (-1) (linz G fs p), 0%Z, false)
  | FEq p q => Some (l_comb (linz G fs q) (-1) (linz G fs p), 0%Z, true)
  | FNe p q => match ne0_term p q with Some t => Some (linz G fs t, 1%Z, false) | None => None end
  | _ => None
  end.
Fixpoint gaps_with (G : list gapc) (fs all : list fact) : list gapc :=
  match fs with
  | [] => []
  | f :: fs' => match gap_of G all f with Some g => g :: gaps_with G fs' all | None => gaps_with G fs' all end
  end.

Definition gaps_ref (fs : list fact) : list gapc := gaps_with (gaps_with (gaps_with [] fs fs) fs fs) fs fs.

Fixpoint needs_gaps (v : sv) : bool :=
  match v with
  | VAlu ALU_ADD x y => match y with VL c => wt c || needs_gaps x | _ => needs_gaps x || needs_gaps y end
  | VAlu ALU_SUB _ _ => true
  | VAlu ALU_SLL x (VL _) => needs_gaps x
  | VAlu ALU_AND x (VL _) => needs_gaps x
  | VMd M_MUL x (VL _) => needs_gaps x
  | VExt _ _ _ x => needs_gaps x
  | VAluw ALU_ADD x (VL _) => needs_gaps x
  | _ => false
  end.
Definition is_gap_fact (f : fact) : bool :=
  match f with FULt _ _ | FULe _ _ | FEq _ _ => true | FNe p q => match ne0_term p q with Some _ => true | None => false end | _ => false end.
Definition fact_needs_gaps (f : fact) : bool :=
  match f with FULt p q | FULe p q | FEq p q | FNe p q => needs_gaps p || needs_gaps q | _ => false end.
Fixpoint gaps_again (G : list gapc) (fs all : list fact) (prev : list gapc) : list gapc :=
  match fs with
  | [] => []
  | f :: fs' =>
      if is_gap_fact f then
          match prev with
          | g :: prev' => (if fact_needs_gaps f then match gap_of G all f with Some g' => g' | None => g end else g)
                          :: gaps_again G fs' all prev'
          | [] => match gap_of G all f with Some g' => g' :: gaps_again G fs' all [] | None => gaps_again G fs' all [] end
          end
      else gaps_again G fs' all prev
  end.
Definition gaps (fs : list fact) : list gapc :=
  let g1 := gaps_with [] fs fs in let g2 := gaps_again g1 fs fs g1 in gaps_again g2 fs fs g2.

Definition lin_ltu_G (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  let d := l_comb (linz G fs b) (-1) (linz G fs a) in
  match l_isconst d with
  | Some k => Some (0 <? k)%Z
  | None => let ab := atom_bounds fs (fst d) in
            match first_some (lin_try ab d) (cands1 d G) with
            | Some r => Some r
            | None => first_some (lin_try ab d) (cands2 d G)
            end
  end.
Definition lin_ltu (fs : list fact) (a b : sv) : option bool := lin_ltu_G (gaps fs) fs a b.
Definition lin_eq_G (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  let d := l_comb (linz G fs b) (-1) (linz G fs a) in
  match l_isconst d with
  | Some k => Some (k =? 0)%Z
  | None => let ab := atom_bounds fs (fst d) in
            match first_some (lin_try_eq ab d) (cands1 d G) with
            | Some r => Some r
            | None => first_some (lin_try_eq ab d) (cands2 d G)
            end
  end.
Definition lin_eq (fs : list fact) (a b : sv) : option bool := lin_eq_G (gaps fs) fs a b.

Fixpoint decide_eq0_s (fs : list fact) (v : sv) {struct v} : option bool :=
  if fact_lookup fs (is_FNe v (VL wzero)) then Some false
  else if fact_lookup fs (is_FEq v (VL wzero)) then Some true
  else
  match v with
  | VL x => Some (weqb x wzero)
  | VP k o =>
      match find_range fs k with
      | Some (lo, hi) =>
          if nowrap lo hi o then (if wltu wzero (wadd lo o) then Some false else None) else None
      | None => None
      end
  | VAlu ALU_XOR x y | VAlu ALU_SUB x y =>

      if sv_eqb x y then Some true
      else if fact_lookup fs (is_FNe x y) then Some false
      else if fact_lookup fs (is_FEq x y) then Some true
      else match x, y with
           | VL a, VL b => Some (weqb a b)
           | VP k1 o1, VP k2 o2 => if PrimInt63.eqb k1 k2 then Some (weqb o1 o2) else None
           | _, VL b => if weqb b wzero then decide_eq0_s fs x else None
           | _, _ => None
           end
  | _ => match sv_umax v with Some m => if weqb m wzero then Some true else None | None => None end
  end.

Definition decide_eq0_b (fs : list fact) (v : sv) : option bool :=
  match decide_eq0_s fs v with Some r => Some r | None => bnd_eq0 fs v end.

Definition decide_ltu_s (fs : list fact) (a b : sv) : option bool :=
  match a, b with
  | VL x, VL y => Some (wltu x y)
  | VP k1 o1, VP k2 o2 =>
      if PrimInt63.eqb k1 k2 then
        (if nowrap_kb fs k1 o1 && nowrap_kb fs k1 o2 then Some (soff_ltb o1 o2) else None)
      else if fact_lookup fs (is_FULt a b) then Some true
      else if fact_lookup fs (is_FULe b a) || fact_lookup fs (is_FEq a b) then Some false
      else None
  | _, _ =>
      if sv_eqb a b then Some false
      else if fact_lookup fs (is_FULt a b) then Some true
      else if fact_lookup fs (is_FULe b a) || fact_lookup fs (is_FEq a b) then Some false
      else match a, b with
           | _, VL y =>
               if weqb y wzero then Some false else
               match (if weqb y wone then decide_eq0_b fs a else None) with
               | Some r => Some r
               | None =>

               match (match sv_umax a with Some m => wltu m y | None => false end) with
               | true => Some true
               | false =>
               match a with
               | VP k o => if weqb o wzero then
                             match find_range fs k with
                             | Some (lo, hi) => if wltu hi y then Some true
                                                else if wleu y lo then Some false
                                                else lookup_ltu_lit_r fs a y
                             | None => lookup_ltu_lit_r fs a y
                             end
                           else lookup_ltu_lit_r fs a y
               | _ => lookup_ltu_lit_r fs a y
               end
               end
               end
           | VL x, _ =>
               match (if weqb x wzero then option_map negb (decide_eq0_b fs b) else None) with
               | Some r => Some r
               | None =>
               match b with
               | VP k o => if weqb o wzero then
                             match find_range fs k with
                             | Some (lo, hi) => if wltu x lo then Some true
                                                else if wleu hi x then Some false
                                                else lookup_ltu_lit_l fs x b
                             | None => lookup_ltu_lit_l fs x b
                             end
                           else lookup_ltu_lit_l fs x b
               | _ => lookup_ltu_lit_l fs x b
               end
               end
           | _, _ => None
           end
  end.

Definition decide_ltu0_G (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match decide_ltu_s fs a b with
  | Some r => Some r
  | None => match bnd_ltu fs a b with Some r => Some r | None => lin_ltu_G G fs a b end
  end.
Definition decide_ltu0 (fs : list fact) (a b : sv) : option bool := decide_ltu0_G (gaps fs) fs a b.

Definition ne_known (fs : list fact) (a b : sv) : bool :=
  fact_lookup fs (fun f => match anchor_norm f with
                           | FNe x y => (sv_eqb x a && sv_eqb y b) || (sv_eqb x b && sv_eqb y a)
                           | _ => false
                           end).
Definition decide_ltu1_G (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  if ne_known fs a b then match decide_ltu0_G G fs b a with Some false => Some true | _ => None end else None.

Definition zext_idiom (a : sv) : option sv :=
  match a with
  | VAlu ALU_SRL (VAlu ALU_SLL x (VL s)) (VL s') => if PrimInt63.eqb (shamt6 s) (shamt6 s') then Some x else None
  | VExt false lo _ x => if PrimInt63.eqb lo 0%uint63 then Some x else None
  | _ => None
  end.
Definition decide_ltu2_G (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match (match zext_idiom a with
         | Some x => match decide_ltu0_G G fs x b with Some true => Some true | _ => None end
         | None => None
         end) with
  | Some r => Some r
  | None => match zext_idiom b with
            | Some x => match decide_ltu0_G G fs a x with Some false => Some false | _ => None end
            | None => None
            end
  end.

Definition decide_ltu3_G (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match a, b with
  | VAlu ALU_SRL x (VL c), VAlu ALU_SRL y (VL c') =>
      if PrimInt63.eqb (shamt6 c) (shamt6 c') && asan_on fs then
        match decide_ltu0_G G fs x y with Some false => Some false | _ => None end
      else None
  | _, _ => None
  end.
Definition decide_ltu_G (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match decide_ltu0_G G fs a b with
  | Some r => Some r
  | None => match decide_ltu1_G G fs a b with
            | Some r => Some r
            | None => match decide_ltu2_G G fs a b with
                      | Some r => Some r
                      | None => decide_ltu3_G G fs a b
                      end
            end
  end.

Definition decide_ltu (fs : list fact) (a b : sv) : option bool :=
  match decide_ltu_s fs a b with
  | Some r => Some r
  | None => match bnd_ltu fs a b with Some r => Some r | None => decide_ltu_G (gaps fs) fs a b end
  end.

Definition below63 (fs : list fact) (k : int) (o : w64) : bool :=
  match find_range fs k with
  | Some (lo, hi) => nowrap lo hi o && negb (wt (wadd hi o)) && negb (wt (wadd lo o))
  | None => false
  end.

Definition nonneg63 (fs : list fact) (v : sv) : bool := negb (wt (snd (sv_bounds fs v))).

Definition decide_lts (fs : list fact) (a b : sv) : option bool :=
  match a, b with
  | VL x, VL y => Some (wlts x y)
  | _, _ =>
  if nonneg63 fs a && nonneg63 fs b then decide_ltu fs a b else
  match a, b with
  | VP k1 o1, VP k2 o2 =>
      if PrimInt63.eqb k1 k2 && below63 fs k1 o1 && below63 fs k1 o2 then Some (soff_ltb o1 o2)
      else if fact_lookup fs (is_FSLt a b) then Some true
      else if fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b) then Some false
      else None
  | _, _ =>
      if sv_eqb a b then Some false
      else if fact_lookup fs (is_FSLt a b) then Some true
      else if fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b) then Some false
      else None
  end
  end.

Definition decide_eq_s (fs : list fact) (a b : sv) : option bool :=
  if sv_eqb a b then Some true else
  match (match a, b with
         | _, VL y => if weqb y wzero then decide_eq0_b fs a else None
         | VL x, _ => if weqb x wzero then decide_eq0_b fs b else None
         | _, _ => None
         end) with
  | Some r => Some r
  | None =>
  match a, b with
  | VL x, VL y => Some (weqb x y)
  | VP k1 o1, VP k2 o2 =>
      if PrimInt63.eqb k1 k2 then Some (weqb o1 o2)
      else if fact_lookup fs (is_FNe a b) then Some false
      else if fact_lookup fs (is_FEq a b) then Some true
      else None
  | _, _ =>
      if fact_lookup fs (is_FNe a b) then Some false
      else if fact_lookup fs (is_FEq a b) then Some true
      else

        match a, b with
        | VP k o, VL y | VL y, VP k o =>
            match find_range fs k with
            | Some (lo, hi) =>
                if nowrap lo hi o then
                  (let vlo := wadd lo o in let vhi := wadd hi o in
                   if wltu y vlo || wltu vhi y then Some false else None)
                else None
            | None => None
            end
        | _, _ =>
            match decide_ltu fs a b with
            | Some true => Some false
            | _ => match decide_ltu fs b a with Some true => Some false | _ => None end
            end
        end
  end
  end.

Definition decide_eq (fs : list fact) (a b : sv) : option bool :=
  match decide_eq_s fs a b with
  | Some r => Some r
  | None =>
      let G := gaps fs in
      match lin_eq_G G fs a b with
      | Some r => Some r
      | None =>
          match decide_ltu_G G fs a b, decide_ltu_G G fs b a with
          | Some true, _ | _, Some true => Some false
          | Some false, Some false => Some true
          | _, _ => None
          end
      end
  end.

Definition decide_eq0 (fs : list fact) (v : sv) : option bool :=
  match decide_eq0_b fs v with Some r => Some r | None => decide_eq fs v (VL wzero) end.

Definition decide_branch (fs : list fact) (c : branch_cond) (a b : sv) : option bool :=
  match c with
  | BC_EQ => decide_eq fs a b
  | BC_NE => option_map negb (decide_eq fs a b)
  | BC_LT => decide_lts fs a b
  | BC_GE => option_map negb (decide_lts fs a b)
  | BC_LTU => decide_ltu fs a b
  | BC_GEU => option_map negb (decide_ltu fs a b)
  end.

Definition BLOBTAG : int := 4611686018427387904%uint63.
Fixpoint sv_vs (v : sv) (acc : list int) : list int :=
  match v with
  | VL _ => acc
  | VP k _ => k :: acc
  | VAlu _ a b | VAluw _ a b | VMd _ a b | VMdw _ a b => sv_vs a (sv_vs b acc)
  | VExt _ _ _ a => sv_vs a acc
  | VIns _ _ a b => sv_vs a (sv_vs b acc)
  | VBlob _ j o _ => PrimInt63.lor BLOBTAG j :: sv_vs o acc
  | VBg _ k _ _ => k :: acc
  | VF1 _ a => sv_vs a acc
  end.
Definition fact_vs (f : fact) : list int :=
  match f with
  | FRange k _ _ | FAlign k _ => [k]
  | FULt a b | FULe a b | FEq a b | FNe a b | FSLt a b | FSLe a b => sv_vs a (sv_vs b [])
  end.
Fixpoint in_vs (k : int) (vs : list int) : bool :=
  match vs with [] => false | x :: vs' => if PrimInt63.eqb k x then true else in_vs k vs' end.
Fixpoint sv_touches (vs : list int) (v : sv) : bool :=
  match v with
  | VL _ => false
  | VP k _ => in_vs k vs
  | VAlu _ a b | VAluw _ a b | VMd _ a b | VMdw _ a b => if sv_touches vs a then true else sv_touches vs b
  | VExt _ _ _ a => sv_touches vs a
  | VIns _ _ a b => if sv_touches vs a then true else sv_touches vs b
  | VBlob _ j o _ => if in_vs (PrimInt63.lor BLOBTAG j) vs then true else sv_touches vs o
  | VBg _ k _ _ => in_vs k vs
  | VF1 _ a => sv_touches vs a
  end.
Definition fact_touches (vs : list int) (f : fact) : bool :=
  match f with
  | FRange k _ _ | FAlign k _ => in_vs k vs
  | FULt a b | FULe a b | FEq a b | FNe a b | FSLt a b | FSLe a b => if sv_touches vs a then true else sv_touches vs b
  end.
Definition rel_facts (vs : list int) (fs : list fact) : list fact := List.filter (fact_touches vs) fs.

Fixpoint close_vs (fs : list fact) (vs acc : list int) : list int :=
  match fs with
  | [] => acc
  | f :: fs' => close_vs fs' vs (if fact_touches vs f then fact_vs f ++ acc else acc)
  end.
Definition decide_branch_t (fs : list fact) (c : branch_cond) (a b : sv) : option bool :=
  let vs := sv_vs a (sv_vs b []) in
  match decide_branch (rel_facts vs fs) c a b with
  | Some r => Some r
  | None => match decide_branch (rel_facts (close_vs fs vs vs) fs) c a b with
            | Some r => Some r
            | None => decide_branch fs c a b
            end
  end.

Definition fact_of_branch0 (c : branch_cond) (a b : sv) (taken : bool) : fact :=
  match c, taken with
  | BC_EQ, true => FEq a b   | BC_EQ, false => FNe a b
  | BC_NE, true => FNe a b   | BC_NE, false => FEq a b
  | BC_LT, true => FSLt a b  | BC_LT, false => FSLe b a
  | BC_GE, true => FSLe b a  | BC_GE, false => FSLt a b
  | BC_LTU, true => FULt a b | BC_LTU, false => FULe b a
  | BC_GEU, true => FULe b a | BC_GEU, false => FULt a b
  end.

Definition cmp_norm (f : fact) : fact :=
  let ne (t : sv) (z : w64) : fact :=
    if weqb z wzero then
      match t with VAlu ALU_SLTU p q => FULt p q | VAlu ALU_SLT p q => FSLt p q | _ => f end
    else f in
  let eq (t : sv) (z : w64) : fact :=
    if weqb z wzero then
      match t with VAlu ALU_SLTU p q => FULe q p | VAlu ALU_SLT p q => FSLe q p | _ => f end
    else f in
  match f with
  | FNe t (VL z) => ne t z
  | FNe (VL z) t => ne t z
  | FEq t (VL z) => eq t z
  | FEq (VL z) t => eq t z
  | _ => f
  end.
Definition fact_of_branch (c : branch_cond) (a b : sv) (taken : bool) : fact := cmp_norm (fact_of_branch0 c a b taken).

Definition low_lim (lo : int) : w64 := W64 false (PrimInt63.sub (PrimInt63.lsl 1%uint63 (PrimInt63.lsl lo 3%uint63)) 1%uint63).

Definition narrow_f0_ref (fs : list fact) (v : sv) : sv :=
  match v with
  | VExt sx lo n x =>
      if PrimInt63.eqb lo 0%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63
         && wltu (snd (sv_bounds fs x)) (ext_lim sx n)
      then x
      else if PrimInt63.ltb 0%uint63 lo && PrimInt63.ltb lo 8%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63
              && PrimInt63.leb (PrimInt63.add lo n) 8%uint63 && wleu (snd (sv_bounds fs x)) (low_lim lo)
      then VL wzero
      else if sx && PrimInt63.eqb lo 0%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63
              && wltu (snd (sv_bounds fs (VExt false 0%uint63 n x))) (ext_lim true n)
      then VExt false 0%uint63 n x
      else v
  | _ => v
  end.

Definition zext0_bounds (fs : list fact) (n : int) (x : sv) (bx : bnd) : bnd :=
  let z := VExt false 0%uint63 n x in
  fact_bounds fs z (fact_bounds fs z
    (bnd_below bx (ext_lim false n) (match umax_of_width n with Some m => (wzero, m) | None => full_bnd end))).
Definition narrow_f0 (fs : list fact) (v : sv) : sv :=
  match v with
  | VExt sx lo n x =>
      if PrimInt63.eqb lo 0%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63 then
        let bx := sv_bounds fs x in
        if wltu (snd bx) (ext_lim sx n) then x
        else if sx then (if wltu (snd (zext0_bounds fs n x bx)) (ext_lim true n) then VExt false 0%uint63 n x else v)
        else v
      else if PrimInt63.ltb 0%uint63 lo && PrimInt63.ltb lo 8%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63
              && PrimInt63.leb (PrimInt63.add lo n) 8%uint63 then
        (if wleu (snd (sv_bounds fs x)) (low_lim lo) then VL wzero else v)
      else v
  | _ => v
  end.

Definition or_silent (fs : list fact) (lo n : int) (o : sv) : bool :=
  match o with
  | VL c => weqb (wext false lo n c) wzero
  | _ => PrimInt63.ltb 0%uint63 lo && wleu (snd (sv_bounds fs o)) (low_lim lo)
  end.
Definition narrow_or (fs : list fact) (v : sv) : sv :=
  match v with
  | VExt sx lo n (VAlu ALU_OR a b) =>
      if PrimInt63.ltb lo 8%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63
         && PrimInt63.leb (PrimInt63.add lo n) 8%uint63 then
        if or_silent fs lo n b then sv_ext sx lo n a
        else if or_silent fs lo n a then sv_ext sx lo n b
        else v
      else v
  | _ => v
  end.

Definition sextw_f (fs : list fact) (v : sv) : sv :=
  match v with
  | VAluw ALU_ADD x (VL z) => if weqb z wzero && wltu (snd (sv_bounds fs x)) bit31w then x else v
  | VAluw ALU_ADD (VL z) x => if weqb z wzero && wltu (snd (sv_bounds fs x)) bit31w then x else v
  | _ => v
  end.
Definition narrow_f (fs : list fact) (v : sv) : sv := sextw_f fs (narrow_f0 fs (narrow_or fs v)).

Definition addr_of (v : sv) : option (int * w64) :=
  match v with
  | VL a => Some (0%uint63, a)
  | VP k o => Some (k, o)
  | _ => None
  end.

Definition msize_bytes (sz : msize) : int :=
  match sz with SZ1 => 1%uint63 | SZ2 => 2%uint63 | SZ4 => 4%uint63 | SZ8 => 8%uint63 end.

Definition can_read (segs : list Segment) (fs : list fact) (priv : list (int * int))
           (k : int) (r : region) (key w : int) : bool :=
  if PrimInt63.eqb k 0%uint63 then

    PrimInt63.ltb key bit62i && Mem.abs_readable segs (to_Z key) (to_Z w) && negb (in_priv_b priv key w)
  else
    kleb (rg_lo r) key && kltb key (PrimInt63.add key w) &&
    match rg_hi r with
    | VL h => match okey h with
              | Some hk => kleb (PrimInt63.add key w) hk
              | None => false
              end
    | hi =>
        PrimInt63.ltb key bit62i &&
        match decide_ltu fs hi (VL (wlit (PrimInt63.add key w))) with
        | Some false => true
        | _ => false
        end
    end.

Definition can_write (segs : list Segment) (fs : list fact) (priv : list (int * int))
           (k : int) (r : region) (key w : int) : bool :=
  if PrimInt63.eqb k 0%uint63 then
    PrimInt63.ltb key bit62i && Mem.abs_writable segs (to_Z key) (to_Z w) && negb (in_priv_b priv key w)
  else rg_w r && can_read segs fs priv k r key w.

Definition can_read_r (segs : list Segment) (rot : Mem.rotab) (fs : list fact) (priv : list (int * int))
           (k : int) (r : region) (key w : int) : bool :=
  if PrimInt63.eqb k 0%uint63 then

    PrimInt63.ltb key bit62i && Mem.abs_readable_r segs rot key w && negb (in_priv_b priv key w)
  else
    kleb (rg_lo r) key && kltb key (PrimInt63.add key w) &&
    match rg_hi r with
    | VL h => match okey h with
              | Some hk => kleb (PrimInt63.add key w) hk
              | None => false
              end
    | hi =>
        PrimInt63.ltb key bit62i &&
        match decide_ltu fs hi (VL (wlit (PrimInt63.add key w))) with
        | Some false => true
        | _ => false
        end
    end.

Definition can_write_r (segs : list Segment) (rot : Mem.rotab) (fs : list fact) (priv : list (int * int))
           (k : int) (r : region) (key w : int) : bool :=
  if PrimInt63.eqb k 0%uint63 then
    PrimInt63.ltb key bit62i && Mem.abs_writable_r segs rot key w && negb (in_priv_b priv key w)
  else rg_w r && can_read_r segs rot fs priv k r key w.

Inductive stop : Type :=
| KStopPc
| KEcall
| KBranch (c : branch_cond) (a b : sv) (off : w64)
| KJalr (t : sv)
| KLoad (why : int) (a : sv)
| KStore (why : int) (a : sv)
| KAlign (a : sv)
| KSc
| KNoInstr
| KOther
| KPc
| KFuel.

Inductive sres : Type :=
| SOk (st : sstate)
| SStop (why : stop) (st : sstate).

Inductive xres : Type :=
| XOk (st : sstate)
| XStop (why : stop).

Definition getr (st : sstate) (r : r5) : sv := rf_get (s_rf st) r.
Definition setr (st : sstate) (r : r5) (v : sv) : sstate :=
  match r with
  | X0 => st
  | _ => SS (s_pc st) (rf_set (s_rf st) r v) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st)
  end.
Definition getf (st : sstate) (r : r5) : sv := rf_get (s_ff st) r.
Definition setf (st : sstate) (r : r5) (v : sv) : sstate :=
  SS (s_pc st) (s_rf st) (rf_set (s_ff st) r v) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st).
Definition setpc (st : sstate) (pc : int) : sstate :=
  SS pc (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st).
Definition setresv (st : sstate) (rv : sresv) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) rv (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st).
Definition setregs (st : sstate) (R : IMap.t region) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) R (s_facts st) (s_ops st) (s_priv st) (s_next st).
Definition addfact (st : sstate) (f : fact) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (f :: s_facts st) (s_ops st) (s_priv st) (s_next st).

Definition pc4 (st : sstate) : int := PrimInt63.add (s_pc st) 4%uint63.

Definition pc_add (pc : int) (off : w64) : option int :=
  let t := wadd (wlit pc) off in
  if negb (wt t) && PrimInt63.ltb (wl t) bit62i then Some (wl t) else None.

Section WithSegs.
Variable segs : list Segment.

Definition sym_addr_of (R : IMap.t region) (v : sv) : option (int * region * sv) :=
  match v with
  | VAlu ALU_ADD (VP k o) x =>
      match IMap.find k R with
      | Some r => Some (k, r, sv_alu ALU_ADD x (VL o))
      | None => match x with
                | VP k2 o2 => match IMap.find k2 R with
                              | Some r => Some (k2, r, VP k (wadd o o2))
                              | None => None
                              end
                | _ => None
                end
      end
  | VAlu ALU_ADD x (VP k o) =>
      match IMap.find k R with
      | Some r => Some (k, r, sv_alu ALU_ADD x (VL o))
      | None => None
      end
  | _ => None
  end.

Definition dec_true (x : option bool) : bool := match x with Some true => true | _ => false end.
Definition dec_false (x : option bool) : bool := match x with Some false => true | _ => false end.

Definition can_read_sym (fs : list fact) (k : int) (r : region) (off : sv) (w : int) : option int :=
  if PrimInt63.eqb k 0%uint63 then None else
  match rg_cells r, rg_bg r with
  | IMap.Leaf, BGBlob j sh =>
      let last := sv_alu ALU_ADD off (VL (wlit (PrimInt63.sub w 1%uint63))) in
      if PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo r) 0%uint63
         && PrimInt63.ltb 0%uint63 w && PrimInt63.leb w 8%uint63
         && dec_true (decide_ltu fs off (rg_hi r))
         && (if PrimInt63.eqb w 1%uint63 then true
             else (if dec_true (decide_ltu fs last (rg_hi r)) then dec_false (decide_ltu fs last off) else false))
      then Some j else None
  | _, _ => None
  end.

Definition can_read_symz (fs : list fact) (k : int) (r : region) (off : sv) (w : int) : bool :=
  if PrimInt63.eqb k 0%uint63 then false else
  match rg_cells r, rg_bg r with
  | IMap.Leaf, BGZero =>
      let last := sv_alu ALU_ADD off (VL (wlit (PrimInt63.sub w 1%uint63))) in
      PrimInt63.eqb (rg_lo r) 0%uint63
         && PrimInt63.ltb 0%uint63 w && PrimInt63.leb w 8%uint63
         && dec_true (decide_ltu fs off (rg_hi r))
         && (if PrimInt63.eqb w 1%uint63 then true
             else (if dec_true (decide_ltu fs last (rg_hi r)) then dec_false (decide_ltu fs last off) else false))
  | _, _ => false
  end.

Definition do_load (st : sstate) (a : sv) (w : int) (sx : bool) : option sv + stop :=
  match addr_of a with
  | None =>
      match sym_addr_of (s_regs st) a with
      | Some (k, r, off) =>
          match can_read_sym (s_facts st) k r off w with
          | Some j => inl (Some (sv_ext sx 0%uint63 w (VBlob false j off w)))
          | None => if can_read_symz (s_facts st) k r off w then inl (Some (VL wzero)) else inr (KLoad 4%uint63 a)
          end
      | None => inr (KLoad 1%uint63 a)
      end
  | Some (k, o) =>
      match IMap.find k (s_regs st) with
      | None => inr (KLoad 2%uint63 a)
      | Some r =>
          match okey o with
          | None => inr (KLoad 3%uint63 a)
          | Some key =>
              if can_read segs (s_facts st) (s_priv st) k r key w then
                match Mem.region_load segs k r key w sx with
                | Some v => inl (Some (narrow_f (s_facts st) v))
                | None => inr (KLoad 5%uint63 a)
                end
              else inr (KLoad 4%uint63 a)
          end
      end
  end.

Definition resv_after_store (fs : list fact) (rv : sresv) (a : sv) : sresv :=
  match rv with
  | RNone => RNone
  | RUnk => RUnk
  | RAddr a' =>
      match decide_eq fs a' a with
      | Some true => RNone
      | Some false => rv
      | None => RUnk
      end
  end.

Definition do_store (st : sstate) (a : sv) (w : int) (v : sv) : sstate + stop :=
  match addr_of a with
  | None => inr (KStore 1%uint63 a)
  | Some (k, o) =>
      match IMap.find k (s_regs st) with
      | None => inr (KStore 2%uint63 a)
      | Some r =>
          match okey o with
          | None => inr (KStore 3%uint63 a)
          | Some key =>
              if can_write segs (s_facts st) (s_priv st) k r key w then
                let r' := Mem.region_store r key w v in
                inl (SS (s_pc st) (s_rf st) (s_ff st) (resv_after_store (s_facts st) (s_resv st) a)
                        (IMap.add k r' (s_regs st)) (s_facts st) (s_ops st) (s_priv st) (s_next st))
              else inr (KStore 4%uint63 a)
          end
      end
  end.

Definition aligned (fs : list fact) (a : sv) (m : int) : bool :=
  let mask := PrimInt63.sub (PrimInt63.lsl 1%uint63 m) 1%uint63 in
  match a with
  | VL x => PrimInt63.eqb (PrimInt63.land (wl x) mask) 0%uint63
  | VP k o => PrimInt63.leb m (find_align fs k) && PrimInt63.eqb (PrimInt63.land (wl o) mask) 0%uint63
  | _ => false
  end.

Definition awidth_bytes (wd : awidth) : int := match wd with AW => 4%uint63 | AD => 8%uint63 end.
Definition awidth_log (wd : awidth) : int := match wd with AW => 2%uint63 | AD => 3%uint63 end.

Definition mask_log (mask : w64) : option int :=

  let nm := wnot mask in
  if wt nm then None else
  let x := wl nm in
  let m1 := PrimInt63.add x 1%uint63 in
  if PrimInt63.eqb (PrimInt63.land m1 x) 0%uint63 && negb (PrimInt63.eqb x 0%uint63)
  then Some (PrimInt63.sub 62%uint63 (PrimInt63.head0 m1))
  else None.

Fixpoint low_bits (fs : list fact) (v : sv) (m : int) {struct v} : option int :=
  let mk := PrimInt63.sub (PrimInt63.lsl 1%uint63 m) 1%uint63 in
  match v with
  | VL x => Some (PrimInt63.land (wl x) mk)
  | VP k o => if PrimInt63.eqb k 0%uint63 then None
              else if PrimInt63.leb m (find_align fs k) then Some (PrimInt63.land (wl o) mk) else None
  | VAlu ALU_ADD a b =>
      match low_bits fs a m, low_bits fs b m with
      | Some x, Some y => Some (PrimInt63.land (PrimInt63.add x y) mk)
      | _, _ => None
      end
  | VAlu ALU_SUB a b =>
      match low_bits fs a m, low_bits fs b m with
      | Some x, Some y => Some (PrimInt63.land (PrimInt63.sub (PrimInt63.add x (PrimInt63.lsl 1%uint63 m)) y) mk)
      | _, _ => None
      end
  | VAluw ALU_ADD a b =>
      if PrimInt63.leb m 32%uint63 then
        match low_bits fs a m, low_bits fs b m with
        | Some x, Some y => Some (PrimInt63.land (PrimInt63.add x y) mk)
        | _, _ => None
        end
      else None
  | VAluw ALU_SUB a b =>
      if PrimInt63.leb m 32%uint63 then
        match low_bits fs a m, low_bits fs b m with
        | Some x, Some y => Some (PrimInt63.land (PrimInt63.sub (PrimInt63.add x (PrimInt63.lsl 1%uint63 m)) y) mk)
        | _, _ => None
        end
      else None
  | VAlu ALU_AND a (VL c) =>
      match low_bits fs a m with
      | Some x => Some (PrimInt63.land x (wl c))
      | None => None
      end
  | _ => None
  end.

Definition mask_bits (mask : w64) : option int :=
  if wt mask then None
  else if PrimInt63.leb bit62i (wl mask) then None
  else Some (PrimInt63.sub 63%uint63 (PrimInt63.head0 (wl mask))).

Definition add_lit (x : sv) (c : w64) : sv :=
  match x with
  | VL y => VL (wadd y c)
  | VP k o => VP k (wadd o c)
  | _ => if weqb c wzero then x else add_lit_fold x c
  end.

Definition split_base (v : sv) : option (int * w64 * option sv) :=
  match v with
  | VP k o => Some (k, o, None)
  | VAlu ALU_ADD (VP k o) x => Some (k, o, Some x)
  | VAlu ALU_ADD x (VP k o) => Some (k, o, Some x)
  | _ => None
  end.

Definition sub_fold (a b : sv) : option sv :=
  match split_base a, split_base b with
  | Some (k1, o1, ra), Some (k2, o2, rb) =>
      if PrimInt63.eqb k1 k2 then
        let d := wsub o1 o2 in
        let lhs := match ra with Some x => add_lit x d | None => VL d end in
        Some (match rb with Some y => VAlu ALU_SUB lhs y | None => lhs end)
      else None
  | _, _ => None
  end.

Definition sv_and_f (fs : list fact) (a b : sv) : sv :=
  let op := ALU_AND in
  match a, b with
      | VL _, VL _ => sv_alu op a b
      | VP k o, VL mask =>

          match mask_log mask with
          | Some m => if negb (PrimInt63.eqb k 0%uint63) && PrimInt63.leb m (find_align fs k)
                      then VP k (wand o mask)
                      else
                        match mask_bits mask with
                        | Some mb => match low_bits fs a mb with
                                     | Some x => VL (wlit (PrimInt63.land x (wl mask)))
                                     | None => sv_alu op a b
                                     end
                        | None => sv_alu op a b
                        end
          | None =>
              match mask_bits mask with
              | Some mb => match low_bits fs a mb with
                           | Some x => VL (wlit (PrimInt63.land x (wl mask)))
                           | None => sv_alu op a b
                           end
              | None => sv_alu op a b
              end
          end
      | _, VL mask =>
          match mask_bits mask with
          | Some mb => match low_bits fs a mb with
                       | Some x => VL (wlit (PrimInt63.land x (wl mask)))
                       | None => sv_alu op a b
                       end
          | None => sv_alu op a b
          end
      | _, _ => sv_alu op a b
      end.

Definition or_ins1 (fs : list fact) (x : sv) (s : sv) (y : sv) : option sv :=
  match s with
  | VL c =>
      let sh := shamt6 c in
      let j := PrimInt63.lsr sh 3%uint63 in
      if PrimInt63.eqb (PrimInt63.land sh 7%uint63) 0%uint63 && PrimInt63.ltb 0%uint63 j && PrimInt63.ltb j 8%uint63
         && wleu (snd (sv_bounds fs y)) (low_lim j)
      then Some (sv_ins j (PrimInt63.sub 8%uint63 j) y x) else None
  | _ => None
  end.
Definition or_ins_fold (fs : list fact) (a b : sv) : option sv :=
  match (match a with VAlu ALU_SLL x s => or_ins1 fs x s b | _ => None end) with
  | Some r => Some r
  | None => match b with VAlu ALU_SLL x s => or_ins1 fs x s a | _ => None end
  end.

Definition srlsll_fold_f (fs : list fact) (a b : sv) : option sv :=
  match a, b with
  | VAlu ALU_SLL x (VL k), VL k' =>
      if PrimInt63.eqb (shamt6 k) (shamt6 k') then
        (let u := snd (sv_bounds fs x) in
         if weqb (wsrl (wsll u k) k) u then Some x
         else match decide_ltu fs (VL (wsrl wones k)) x with Some false => Some x | _ => None end)
      else None
  | _, _ => None
  end.

Definition zero_top (ds : list BD.bsrc) : option nat :=
  let fit (k : nat) := BD.bsrcs_eqb ds (BD.brange 0 k ++ repeat BD.BZ (8 - k)) in
  if fit 1%nat then Some 1%nat else if fit 2%nat then Some 2%nat else if fit 3%nat then Some 3%nat
  else if fit 4%nat then Some 4%nat else if fit 5%nat then Some 5%nat else if fit 6%nat then Some 6%nat
  else if fit 7%nat then Some 7%nat else None.
Definition refold_f (fs : list fact) (r : sv) : sv :=
  match BD.bdesc r with
  | Some (Some y, ds) =>
      match zero_top ds with
      | Some k => if wltu (snd (sv_bounds fs y)) (ext_lim false (BD.nat2int k)) then y else r
      | None => r
      end
  | _ => r
  end.

Definition is_link (k : int) (s : w64) (f : fact) : option int :=
  match f with
  | FEq (VP sh z) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' z') (VL c)) (VL s')) =>
      if weqb z wzero && PrimInt63.eqb k' k && weqb z' wzero && PrimInt63.eqb (shamt6 c) 3%uint63 && weqb s' s then Some sh else None
  | _ => None
  end.
Fixpoint find_link (fs : list fact) (k : int) (s : w64) : option int :=
  match fs with
  | [] => None
  | f :: fs' => match is_link k s f with Some sh => Some sh | None => find_link fs' k s end
  end.
Definition shadow_fold (fs : list fact) (a b : sv) : option sv :=
  match a, b with
  | VAlu ALU_SRL (VP k o) (VL c), VL s =>
      if PrimInt63.eqb (shamt6 c) 3%uint63 && PrimInt63.leb 3%uint63 (find_align fs k) && nowrap_kb fs k o then
        match find_link fs k s with
        | Some sh => Some (VP sh (wsra o (wlit 3%uint63)))
        | None => None
        end
      else None
  | VAlu ALU_SRL (VAlu ALU_ADD (VP k o) x) (VL c), VL s =>

      let xo := sv_alu ALU_ADD x (VL o) in
      if PrimInt63.eqb (shamt6 c) 3%uint63 && PrimInt63.leb 3%uint63 (find_align fs k) && negb (wt o)
         && negb (add_carries (snd (sv_bounds fs x)) o)
         && negb (add_carries (snd (var_bounds fs k)) (snd (sv_bounds fs xo))) then
        match find_link fs k s with
        | Some sh => Some (VAlu ALU_ADD (VP sh wzero) (VAlu ALU_SRL xo (VL (wlit 3%uint63))))
        | None => None
        end
      else None
  | _, _ => None
  end.

Definition and_base_fold (fs : list fact) (a b : sv) : option sv :=
  match a, b with
  | VAlu ALU_ADD (VP k o) x, VL mask =>
      match low_mask_k mask with
      | Some m => if negb (PrimInt63.eqb k 0%uint63) && PrimInt63.leb m (find_align fs k) && asan_on fs
                  then Some (sv_alu ALU_AND (sv_alu ALU_ADD x (VL o)) (VL mask)) else None
      | None => None
      end
  | _, _ => None
  end.

Fixpoint sv_al (fs : list fact) (v : sv) (m : int) : bool :=
  match v with
  | VAlu ALU_ADD a b => sv_al fs a m && sv_al fs b m
  | VAlu ALU_SUB a b => sv_al fs a m && sv_al fs b m
  | _ => aligned fs v m
  end.
Definition is_shr (op : aluop) : bool := match op with ALU_SRA | ALU_SRL => true | _ => false end.
Definition sllsr_fold_f (fs : list fact) (a b : sv) : option sv :=
  match a, b with
  | VAlu op t (VL k), VL k' =>
      if is_shr op && PrimInt63.eqb (shamt6 k) (shamt6 k') && PrimInt63.leb (shamt6 k) 62%uint63
         && asan_on fs && sv_al fs t (shamt6 k)
      then Some t else None
  | _, _ => None
  end.

Definition sv_alu_f (fs : list fact) (op : aluop) (a b : sv) : sv :=
  match op with
  | ALU_ADD => match shadow_fold fs a b with
               | Some r => r
               | None => match shadow_fold fs b a with Some r => r | None => sv_alu op a b end
               end
  | ALU_AND => match sv_and_f fs a b with
               | VL c => VL c
               | r => match and_base_fold fs a b with Some r' => r' | None => r end
               end
  | ALU_SUB => match sub_fold a b with Some r => r | None => sv_alu op a b end
  | ALU_OR => refold_f fs (match or_ins_fold fs a b with Some r => r | None => sv_alu op a b end)
  | ALU_SRL => match srlsll_fold_f fs a b with Some r => r | None => sv_alu op a b end
  | ALU_SLL => match sllsr_fold_f fs a b with Some r => r | None => sv_alu op a b end
  | ALU_SLTU => match decide_ltu fs a b with Some r => VL (wofbool r) | None => sv_alu op a b end
  | ALU_SLT => match decide_lts fs a b with Some r => VL (wofbool r) | None => sv_alu op a b end
  | _ => sv_alu op a b
  end.

Definition sv_aluw_f (fs : list fact) (op : aluop) (a b : sv) : sv :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let r := sv_alu_f fs op a b in
      if wltu (snd (sv_bounds fs r)) bit31w then r
      else sv_aluw op a b
  | _ => sv_aluw op a b
  end.

Definition resolve_rm_b (rm : bv 3) : option rmode :=

  rmode_of_field (bv_unsigned rm) 0.

Definition exec (fi : finstr) (st : sstate) : xres :=
  let pc := s_pc st in
  let fs := s_facts st in
  match fi with
  | ILui rd v => XOk (setpc (setr st rd (VL v)) (pc4 st))
  | IAuipc rd v => XOk (setpc (setr st rd (VL (wadd (wlit pc) v))) (pc4 st))
  | IJal rd off =>
      match pc_add pc off with
      | Some t => XOk (setpc (setr st rd (VL (wlit (pc4 st)))) t)
      | None => XStop KPc
      end
  | IJalr rd rs1 off =>
      match sv_alu ALU_ADD (getr st rs1) (VL off) with
      | VL t =>
          let t' := wand t (wnot wone) in
          if negb (wt t') && PrimInt63.ltb (wl t') bit62i
          then XOk (setpc (setr st rd (VL (wlit (pc4 st)))) (wl t'))
          else XStop KPc
      | t => XStop (KJalr t)
      end
  | IBranch c rs1 rs2 off =>
      let a := getr st rs1 in let b := getr st rs2 in
      match decide_branch_t fs c a b with
      | Some true => match pc_add pc off with Some t => XOk (setpc st t) | None => XStop KPc end
      | Some false => XOk (setpc st (pc4 st))
      | None => XStop (KBranch c a b off)
      end
  | ILoad sz sx rd rs1 off =>
      let a := sv_alu ALU_ADD (getr st rs1) (VL off) in
      match do_load st a (msize_bytes sz) sx with
      | inl (Some v) => XOk (setpc (setr st rd v) (pc4 st))
      | inl None => XStop (KLoad 5%uint63 a)
      | inr k => XStop k
      end
  | IStore sz rs1 rs2 off =>
      let a := sv_alu ALU_ADD (getr st rs1) (VL off) in
      match do_store st a (msize_bytes sz) (getr st rs2) with
      | inl st' => XOk (setpc st' (pc4 st))
      | inr k => XStop k
      end
  | IOpImm op rd rs1 v => XOk (setpc (setr st rd (sv_alu_f fs op (getr st rs1) (VL v))) (pc4 st))
  | IOp op rd rs1 rs2 => XOk (setpc (setr st rd (sv_alu_f fs op (getr st rs1) (getr st rs2))) (pc4 st))
  | IOpImm32 op rd rs1 v => XOk (setpc (setr st rd (sv_aluw_f fs op (getr st rs1) (VL v))) (pc4 st))
  | IOp32 op rd rs1 rs2 => XOk (setpc (setr st rd (sv_aluw_f fs op (getr st rs1) (getr st rs2))) (pc4 st))
  | IMul op rd rs1 rs2 => XOk (setpc (setr st rd (sv_md op (getr st rs1) (getr st rs2))) (pc4 st))
  | IMul32 op rd rs1 rs2 => XOk (setpc (setr st rd (sv_mdw op (getr st rs1) (getr st rs2))) (pc4 st))
  | IFence => XOk (setpc st (pc4 st))
  | IEcall => XStop KEcall
  | ILr wd rd rs1 =>
      let a := getr st rs1 in
      if aligned fs a (awidth_log wd) then
        match do_load st a (awidth_bytes wd) true with
        | inl (Some v) => XOk (setpc (setresv (setr st rd v) (RAddr a)) (pc4 st))
        | inl None => XStop (KLoad 5%uint63 a)
        | inr k => XStop k
        end
      else XStop (KAlign a)
  | ISc wd rd rs1 rs2 =>
      let a := getr st rs1 in
      if aligned fs a (awidth_log wd) then
        match s_resv st with
        | RNone => XOk (setpc (setresv (setr st rd (VL wone)) RNone) (pc4 st))
        | RUnk => XStop KSc
        | RAddr a' =>
            match decide_eq fs a' a with
            | Some true =>
                match do_store (setresv st RNone) a (awidth_bytes wd) (getr st rs2) with
                | inl st' => XOk (setpc (setresv (setr st' rd (VL wzero)) RNone) (pc4 st))
                | inr k => XStop k
                end
            | Some false => XOk (setpc (setresv (setr st rd (VL wone)) RNone) (pc4 st))
            | None => XStop KSc
            end
        end
      else XStop (KAlign a)
  | IAmo op wd rd rs1 rs2 =>
      let a := getr st rs1 in
      if aligned fs a (awidth_log wd) then
        match do_load st a (awidth_bytes wd) true with
        | inl (Some old) =>
            let src := getr st rs2 in
            let newv := match op with
                        | AMO_SWAP => Some src
                        | AMO_ADD => Some (sv_alu ALU_ADD old src)
                        | AMO_XOR => Some (sv_alu ALU_XOR old src)
                        | AMO_AND => Some (sv_alu ALU_AND old src)
                        | AMO_OR => Some (sv_alu ALU_OR old src)
                        | _ => None
                        end in
            match newv with
            | Some nv =>

                let st1 := setresv st (resv_after_store fs (s_resv st) a) in
                match do_store st1 a (awidth_bytes wd) nv with
                | inl st' => XOk (setpc (setr (setresv st' (s_resv st1)) rd old) (pc4 st))
                | inr k => XStop k
                end
            | None => XStop KOther
            end
        | inl None => XStop (KLoad 5%uint63 a)
        | inr k => XStop k
        end
      else XStop (KAlign a)
  | IFLoad fmt rd rs1 off =>
      let a := sv_alu ALU_ADD (getr st rs1) (VL off) in
      match fmt with
      | FMT_D =>
          match do_load st a 8%uint63 false with
          | inl (Some v) => XOk (setpc (setf st rd v) (pc4 st))
          | inl None => XStop (KLoad 5%uint63 a)
          | inr k => XStop k
          end
      | FMT_S =>
          match do_load st a 4%uint63 false with
          | inl (Some v) => XOk (setpc (setf st rd (VF1 F1_NANBOX v)) (pc4 st))
          | inl None => XStop (KLoad 5%uint63 a)
          | inr k => XStop k
          end
      end
  | IFStore fmt rs1 rs2 off =>
      let a := sv_alu ALU_ADD (getr st rs1) (VL off) in
      let w := match fmt with FMT_D => 8%uint63 | FMT_S => 4%uint63 end in
      match do_store st a w (getf st rs2) with
      | inl st' => XOk (setpc st' (pc4 st))
      | inr k => XStop k
      end
  | IFmv dir fmt rd rs1 =>
      match dir, fmt with
      | FMV_X_F, FMT_D => XOk (setpc (setr st rd (getf st rs1)) (pc4 st))
      | FMV_X_F, FMT_S => XOk (setpc (setr st rd (sv_ext true 0%uint63 4%uint63 (getf st rs1))) (pc4 st))
      | FMV_F_X, FMT_D => XOk (setpc (setf st rd (getr st rs1)) (pc4 st))
      | FMV_F_X, FMT_S => XOk (setpc (setf st rd (VF1 F1_NANBOX (getr st rs1))) (pc4 st))
      end
  | IFcvtDS rd rs1 rm =>
      match resolve_rm_b rm with
      | Some md => XOk (setpc (setf st rd (VF1 (F1_FCVT FMT_S FMT_D md) (getf st rs1))) (pc4 st))
      | None => XStop KOther
      end
  | IFcvtSD rd rs1 rm =>
      match resolve_rm_b rm with
      | Some md => XOk (setpc (setf st rd (VF1 (F1_FCVT FMT_D FMT_S md) (getf st rs1))) (pc4 st))
      | None => XStop KOther
      end
  | IOther _ => XStop KOther
  end.

Definition step (it : itab) (st : sstate) : sres :=
  if PrimInt63.ltb (s_pc st) bit62i then
    match IMap.find (s_pc st) it with
    | Some fi => match exec fi st with
                 | XOk st' => SOk st'
                 | XStop why => SStop why st
                 end
    | None => SStop KNoInstr st
    end
  else SStop KPc st.

Definition take_branch (c : branch_cond) (a b : sv) (off : w64) (taken : bool) (st : sstate) : option sstate :=
  let st1 := addfact st (fact_of_branch c a b taken) in
  if taken then match pc_add (s_pc st) off with Some t => Some (setpc st1 t) | None => None end
  else Some (setpc st1 (pc4 st)).

Fixpoint in_stops (pc : int) (stops : list int) : bool :=
  match stops with [] => false | s :: ss => if PrimInt63.eqb pc s then true else in_stops pc ss end.

Definition step1 (it : itab) (stops : list int) (st : sstate) : sres :=
  if in_stops (s_pc st) stops then SStop KStopPc st else step it st.

Fixpoint runP (p : positive) (it : itab) (stops : list int) (st : sstate) : sres :=
  match p with
  | xH => step1 it stops st
  | xO q => match runP q it stops st with
            | SOk st' => runP q it stops st'
            | r => r
            end
  | xI q => match runP q it stops st with
            | SOk st' => match runP q it stops st' with
                         | SOk st'' => step1 it stops st''
                         | r => r
                         end
            | r => r
            end
  end.

Definition run (it : itab) (stops : list int) (st : sstate) : sres :=
  match runP (2^40)%positive it stops st with
  | SOk st' => SStop KFuel st'
  | r => r
  end.

Section Rot.
Variable rot : Mem.rotab.

Definition do_load_r (st : sstate) (a : sv) (w : int) (sx : bool) : option sv + stop :=
  match addr_of a with
  | None =>
      match sym_addr_of (s_regs st) a with
      | Some (k, r, off) =>
          match can_read_sym (s_facts st) k r off w with
          | Some j => inl (Some (sv_ext sx 0%uint63 w (VBlob false j off w)))
          | None => if can_read_symz (s_facts st) k r off w then inl (Some (VL wzero)) else inr (KLoad 4%uint63 a)
          end
      | None => inr (KLoad 1%uint63 a)
      end
  | Some (k, o) =>
      match IMap.find k (s_regs st) with
      | None => inr (KLoad 2%uint63 a)
      | Some r =>
          match okey o with
          | None => inr (KLoad 3%uint63 a)
          | Some key =>
              if can_read_r segs rot (s_facts st) (s_priv st) k r key w then
                match Mem.region_load_r segs rot k r key w sx with
                | Some v => inl (Some (narrow_f (s_facts st) v))
                | None => inr (KLoad 5%uint63 a)
                end
              else inr (KLoad 4%uint63 a)
          end
      end
  end.

Definition do_store_r (st : sstate) (a : sv) (w : int) (v : sv) : sstate + stop :=
  match addr_of a with
  | None => inr (KStore 1%uint63 a)
  | Some (k, o) =>
      match IMap.find k (s_regs st) with
      | None => inr (KStore 2%uint63 a)
      | Some r =>
          match okey o with
          | None => inr (KStore 3%uint63 a)
          | Some key =>
              if can_write_r segs rot (s_facts st) (s_priv st) k r key w then
                let r' := Mem.region_store r key w v in
                inl (SS (s_pc st) (s_rf st) (s_ff st) (resv_after_store (s_facts st) (s_resv st) a)
                        (IMap.add k r' (s_regs st)) (s_facts st) (s_ops st) (s_priv st) (s_next st))
              else inr (KStore 4%uint63 a)
          end
      end
  end.

Definition exec_r (fi : finstr) (st : sstate) : xres :=
  let pc := s_pc st in
  let fs := s_facts st in
  match fi with
  | ILui rd v => XOk (setpc (setr st rd (VL v)) (pc4 st))
  | IAuipc rd v => XOk (setpc (setr st rd (VL (wadd (wlit pc) v))) (pc4 st))
  | IJal rd off =>
      match pc_add pc off with
      | Some t => XOk (setpc (setr st rd (VL (wlit (pc4 st)))) t)
      | None => XStop KPc
      end
  | IJalr rd rs1 off =>
      match sv_alu ALU_ADD (getr st rs1) (VL off) with
      | VL t =>
          let t' := wand t (wnot wone) in
          if negb (wt t') && PrimInt63.ltb (wl t') bit62i
          then XOk (setpc (setr st rd (VL (wlit (pc4 st)))) (wl t'))
          else XStop KPc
      | t => XStop (KJalr t)
      end
  | IBranch c rs1 rs2 off =>
      let a := getr st rs1 in let b := getr st rs2 in
      match decide_branch_t fs c a b with
      | Some true => match pc_add pc off with Some t => XOk (setpc st t) | None => XStop KPc end
      | Some false => XOk (setpc st (pc4 st))
      | None => XStop (KBranch c a b off)
      end
  | ILoad sz sx rd rs1 off =>
      let a := sv_alu ALU_ADD (getr st rs1) (VL off) in
      match do_load_r st a (msize_bytes sz) sx with
      | inl (Some v) => XOk (setpc (setr st rd v) (pc4 st))
      | inl None => XStop (KLoad 5%uint63 a)
      | inr k => XStop k
      end
  | IStore sz rs1 rs2 off =>
      let a := sv_alu ALU_ADD (getr st rs1) (VL off) in
      match do_store_r st a (msize_bytes sz) (getr st rs2) with
      | inl st' => XOk (setpc st' (pc4 st))
      | inr k => XStop k
      end
  | IOpImm op rd rs1 v => XOk (setpc (setr st rd (sv_alu_f fs op (getr st rs1) (VL v))) (pc4 st))
  | IOp op rd rs1 rs2 => XOk (setpc (setr st rd (sv_alu_f fs op (getr st rs1) (getr st rs2))) (pc4 st))
  | IOpImm32 op rd rs1 v => XOk (setpc (setr st rd (sv_aluw_f fs op (getr st rs1) (VL v))) (pc4 st))
  | IOp32 op rd rs1 rs2 => XOk (setpc (setr st rd (sv_aluw_f fs op (getr st rs1) (getr st rs2))) (pc4 st))
  | IMul op rd rs1 rs2 => XOk (setpc (setr st rd (sv_md op (getr st rs1) (getr st rs2))) (pc4 st))
  | IMul32 op rd rs1 rs2 => XOk (setpc (setr st rd (sv_mdw op (getr st rs1) (getr st rs2))) (pc4 st))
  | IFence => XOk (setpc st (pc4 st))
  | IEcall => XStop KEcall
  | ILr wd rd rs1 =>
      let a := getr st rs1 in
      if aligned fs a (awidth_log wd) then
        match do_load_r st a (awidth_bytes wd) true with
        | inl (Some v) => XOk (setpc (setresv (setr st rd v) (RAddr a)) (pc4 st))
        | inl None => XStop (KLoad 5%uint63 a)
        | inr k => XStop k
        end
      else XStop (KAlign a)
  | ISc wd rd rs1 rs2 =>
      let a := getr st rs1 in
      if aligned fs a (awidth_log wd) then
        match s_resv st with
        | RNone => XOk (setpc (setresv (setr st rd (VL wone)) RNone) (pc4 st))
        | RUnk => XStop KSc
        | RAddr a' =>
            match decide_eq fs a' a with
            | Some true =>
                match do_store_r (setresv st RNone) a (awidth_bytes wd) (getr st rs2) with
                | inl st' => XOk (setpc (setresv (setr st' rd (VL wzero)) RNone) (pc4 st))
                | inr k => XStop k
                end
            | Some false => XOk (setpc (setresv (setr st rd (VL wone)) RNone) (pc4 st))
            | None => XStop KSc
            end
        end
      else XStop (KAlign a)
  | IAmo op wd rd rs1 rs2 =>
      let a := getr st rs1 in
      if aligned fs a (awidth_log wd) then
        match do_load_r st a (awidth_bytes wd) true with
        | inl (Some old) =>
            let src := getr st rs2 in
            let newv := match op with
                        | AMO_SWAP => Some src
                        | AMO_ADD => Some (sv_alu ALU_ADD old src)
                        | AMO_XOR => Some (sv_alu ALU_XOR old src)
                        | AMO_AND => Some (sv_alu ALU_AND old src)
                        | AMO_OR => Some (sv_alu ALU_OR old src)
                        | _ => None
                        end in
            match newv with
            | Some nv =>

                let st1 := setresv st (resv_after_store fs (s_resv st) a) in
                match do_store_r st1 a (awidth_bytes wd) nv with
                | inl st' => XOk (setpc (setr (setresv st' (s_resv st1)) rd old) (pc4 st))
                | inr k => XStop k
                end
            | None => XStop KOther
            end
        | inl None => XStop (KLoad 5%uint63 a)
        | inr k => XStop k
        end
      else XStop (KAlign a)
  | IFLoad fmt rd rs1 off =>
      let a := sv_alu ALU_ADD (getr st rs1) (VL off) in
      match fmt with
      | FMT_D =>
          match do_load_r st a 8%uint63 false with
          | inl (Some v) => XOk (setpc (setf st rd v) (pc4 st))
          | inl None => XStop (KLoad 5%uint63 a)
          | inr k => XStop k
          end
      | FMT_S =>
          match do_load_r st a 4%uint63 false with
          | inl (Some v) => XOk (setpc (setf st rd (VF1 F1_NANBOX v)) (pc4 st))
          | inl None => XStop (KLoad 5%uint63 a)
          | inr k => XStop k
          end
      end
  | IFStore fmt rs1 rs2 off =>
      let a := sv_alu ALU_ADD (getr st rs1) (VL off) in
      let w := match fmt with FMT_D => 8%uint63 | FMT_S => 4%uint63 end in
      match do_store_r st a w (getf st rs2) with
      | inl st' => XOk (setpc st' (pc4 st))
      | inr k => XStop k
      end
  | IFmv dir fmt rd rs1 =>
      match dir, fmt with
      | FMV_X_F, FMT_D => XOk (setpc (setr st rd (getf st rs1)) (pc4 st))
      | FMV_X_F, FMT_S => XOk (setpc (setr st rd (sv_ext true 0%uint63 4%uint63 (getf st rs1))) (pc4 st))
      | FMV_F_X, FMT_D => XOk (setpc (setf st rd (getr st rs1)) (pc4 st))
      | FMV_F_X, FMT_S => XOk (setpc (setf st rd (VF1 F1_NANBOX (getr st rs1))) (pc4 st))
      end
  | IFcvtDS rd rs1 rm =>
      match resolve_rm_b rm with
      | Some md => XOk (setpc (setf st rd (VF1 (F1_FCVT FMT_S FMT_D md) (getf st rs1))) (pc4 st))
      | None => XStop KOther
      end
  | IFcvtSD rd rs1 rm =>
      match resolve_rm_b rm with
      | Some md => XOk (setpc (setf st rd (VF1 (F1_FCVT FMT_D FMT_S md) (getf st rs1))) (pc4 st))
      | None => XStop KOther
      end
  | IOther _ => XStop KOther
  end.

Definition step_r (it : itab) (st : sstate) : sres :=
  if PrimInt63.ltb (s_pc st) bit62i then
    match IMap.find (s_pc st) it with
    | Some fi => match exec_r fi st with
                 | XOk st' => SOk st'
                 | XStop why => SStop why st
                 end
    | None => SStop KNoInstr st
    end
  else SStop KPc st.

Definition step1_r (it : itab) (stops : list int) (st : sstate) : sres :=
  if in_stops (s_pc st) stops then SStop KStopPc st else step_r it st.

Fixpoint runP_r (p : positive) (it : itab) (stops : list int) (st : sstate) : sres :=
  match p with
  | xH => step1_r it stops st
  | xO q => match runP_r q it stops st with
            | SOk st' => runP_r q it stops st'
            | r => r
            end
  | xI q => match runP_r q it stops st with
            | SOk st' => match runP_r q it stops st' with
                         | SOk st'' => step1_r it stops st''
                         | r => r
                         end
            | r => r
            end
  end.

Definition run_r (it : itab) (stops : list int) (st : sstate) : sres :=
  match runP_r (2^40)%positive it stops st with
  | SOk st' => SStop KFuel st'
  | r => r
  end.

End Rot.

End WithSegs.
End Step.
