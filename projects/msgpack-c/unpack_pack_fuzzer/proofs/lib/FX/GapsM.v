(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step.
Open Scope Z_scope.

Module GapsM.

Record fidx : Type := FIx {
  ix_lit : list fact;
  ix_rng : IMap.t (w64 * w64);
  ix_al : IMap.t int;
  ix_vb : IMap.t bnd;
  ix_asan : bool
}.

Definition lit_sided (f : fact) : bool :=
  match f with
  | FULt x y | FULe x y | FEq x y | FNe x y => match lit_of x, lit_of y with None, None => false | _, _ => true end
  | _ => false
  end.

Definition find_range_x (IX : fidx) (k : int) : option (w64 * w64) := IMap.find k (ix_rng IX).
Definition find_align_x (IX : fidx) (k : int) : int := match IMap.find k (ix_al IX) with Some m => m | None => 0%uint63 end.
Definition nowrap_k_x (IX : fidx) (k : int) (o : w64) : bool :=
  match find_range_x IX k with Some (lo, hi) => nowrap lo hi o | None => false end.

Fixpoint fact_bounds_l (l : list fact) (v : sv) (b : bnd) : bnd :=
  match l with
  | [] => b
  | f :: l' => fact_bounds_l l' v (fact_bnd1 f v b)
  end.
Definition fact_bounds_x (IX : fidx) (v : sv) (b : bnd) : bnd := fact_bounds_l (ix_lit IX) v b.

Definition bnd_struct_x (rec : sv -> bnd) (IX : fidx) (v : sv) : bnd :=
  match v with
  | VL x => (x, x)
  | VP k o =>
      match find_range_x IX k with
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

Definition align_bnd_x (IX : fidx) (k : int) (b : bnd) : bnd :=
  let m := find_align_x IX k in
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

Definition var_bounds_x0 (IX : fidx) (k : int) : bnd :=
  let v := VP k wzero in
  align_bnd_x IX k (fact_bounds_x IX v (fact_bounds_x IX v (bnd_struct_x (fun _ => full_bnd) IX v))).
Definition var_bounds_x (IX : fidx) (k : int) : bnd :=
  match IMap.find k (ix_vb IX) with Some b => b | None => var_bounds_x0 IX k end.

Definition nowrap_kb_x (IX : fidx) (k : int) (o : w64) : bool :=
  if nowrap_k_x IX k o then true else (let '(lo, hi) := var_bounds_x IX k in nowrap lo hi o).

Fixpoint sv_bounds_x (IX : fidx) (v : sv) {struct v} : bnd :=
  let b0 := bnd_struct_x (sv_bounds_x IX) IX v in
  match v with
  | VL _ => b0
  | VP k o =>
      if weqb o wzero then var_bounds_x IX k
      else let b1 := fact_bounds_x IX v (fact_bounds_x IX v b0) in
           match bnd_shift (var_bounds_x IX k) o with Some bs => bnd_meet b1 bs | None => b1 end
  | _ => fact_bounds_x IX v (fact_bounds_x IX v b0)
  end.

Definition bnd_ltu_x (IX : fidx) (a b : sv) : option bool :=
  let '(la, ha) := sv_bounds_x IX a in let '(lb, hb) := sv_bounds_x IX b in
  if wltu ha lb then Some true else if wleu hb la then Some false else None.
Definition bnd_eq0_x (IX : fidx) (v : sv) : option bool :=
  let '(l, h) := sv_bounds_x IX v in
  if wltu wzero l then Some false else if weqb h wzero then Some true else None.
Definition nonneg63_x (IX : fidx) (v : sv) : bool := negb (wt (snd (sv_bounds_x IX v))).

Definition abtab_x : Type := (bool * list (sv * bnd))%type.
Definition atom_bounds_x (IX : fidx) (t : lterm) : abtab_x :=
  (ix_asan IX, map (fun ac => (fst ac, sv_bounds_x IX (fst ac))) t).
Fixpoint ab_find_lx (IX : fidx) (fb : bool) (ab : list (sv * bnd)) (a : sv) : bnd :=
  match ab with
  | [] => if fb then sv_bounds_x IX a else full_bnd
  | (a', b) :: ab' => if sv_eqb a a' then b else ab_find_lx IX fb ab' a
  end.
Definition ab_find_x (IX : fidx) (ab : abtab_x) (a : sv) : bnd := ab_find_lx IX (fst ab) (snd ab) a.
Fixpoint lt_lo_x (IX : fidx) (ab : abtab_x) (t : lterm) : Z :=
  match t with
  | [] => 0
  | (a, c) :: t' => (let '(lo, hi) := ab_find_x IX ab a in if (0 <? c)%Z then c * w2Z lo else c * w2Z hi)%Z + lt_lo_x IX ab t'
  end.
Fixpoint lt_hi_x (IX : fidx) (ab : abtab_x) (t : lterm) : Z :=
  match t with
  | [] => 0
  | (a, c) :: t' => (let '(lo, hi) := ab_find_x IX ab a in if (0 <? c)%Z then c * w2Z hi else c * w2Z lo)%Z + lt_hi_x IX ab t'
  end.
Definition lin_bounds_x (IX : fidx) (ab : abtab_x) (d : lin) (sel : list (Z * gapc)) : option Z * option Z :=
  if sel_ok sel then
    let r := sel_rest d sel in
    (oadd (sel_lo sel) (Some (snd r + lt_lo_x IX ab (fst r))%Z), oadd (sel_hi sel) (Some (snd r + lt_hi_x IX ab (fst r))%Z))
  else (None, None).

Definition lin_try_x (IX : fidx) (ab : abtab_x) (d : lin) (sel : list (Z * gapc)) : option bool :=
  let lu := lin_bounds_x IX ab d sel in
  match lu with
  | (Some l, _) => if (1 <=? l)%Z then Some true
                   else match lu with (_, Some u) => if (u <=? 0)%Z then Some false else None | _ => None end
  | (None, Some u) => if (u <=? 0)%Z then Some false else None
  | _ => None
  end.
Definition lin_try_eq_x (IX : fidx) (ab : abtab_x) (d : lin) (sel : list (Z * gapc)) : option bool :=
  match lin_bounds_x IX ab d sel with
  | (Some l, Some u) => if ((l =? 0) && (u =? 0))%Z then Some true
                        else if ((1 <=? l) || (u <=? -1))%Z then Some false else None
  | (Some l, None) => if (1 <=? l)%Z then Some false else None
  | (None, Some u) => if (u <=? -1)%Z then Some false else None
  | (None, None) => None
  end.
Definition lin_try_nonneg_x (IX : fidx) (ab : abtab_x) (d : lin) (sel : list (Z * gapc)) : option bool :=
  match lin_bounds_x IX ab d sel with (Some l, _) => if (0 <=? l)%Z then Some true else None | _ => None end.

Definition lin_nonneg_x (IX : fidx) (G : list gapc) (d : lin) : bool :=
  if l_nonnegb d then true else match first_some (lin_try_nonneg_x IX (atom_bounds_x IX (fst d)) d) (cands1 d G) with Some true => true | _ => false end.

Fixpoint linz_x (IX : fidx) (G : list gapc) (fs : list fact) (v : sv) {struct v} : lin :=
  match v with
  | VL c => l_const (w2Z c)
  | VP k o =>
      if weqb o wzero then l_atom v
      else if nowrap_kb_x IX k o then l_comb (l_atom (VP k wzero)) 1 (l_const (w2Zs o))
      else l_atom v
  | VAlu ALU_ADD x y =>
      match y with
      | VL c =>
          if wt c then
            (let d := l_comb (linz_x IX G fs x) (-1) (l_const (w2Z (wneg c))) in
             if (if wleu (wneg c) (fst (sv_bounds_x IX x)) then true else lin_nonneg_x IX G d) then d else l_atom v)
          else (if negb (add_carries (snd (sv_bounds_x IX x)) c) then l_comb (linz_x IX G fs x) 1 (l_const (w2Z c)) else l_atom v)
      | _ =>
          if negb (add_carries (snd (sv_bounds_x IX x)) (snd (sv_bounds_x IX y))) then l_comb (linz_x IX G fs x) 1 (linz_x IX G fs y)
          else l_atom v
      end
  | VAlu ALU_SUB x y =>
      let d := l_comb (linz_x IX G fs x) (-1) (linz_x IX G fs y) in
      if (if (if (if wleu (snd (sv_bounds_x IX y)) (fst (sv_bounds_x IX x)) then true
                  else fact_lookup fs (is_FULe y x)) then true else fact_lookup fs (is_FULt y x)) then true
          else lin_nonneg_x IX G d)
      then d else l_atom v
  | VAlu ALU_SLL x (VL s) =>
      if wleu (snd (sv_bounds_x IX x)) (wsrl wones s) then l_scale (2 ^ to_Z (shamt6 s)) (linz_x IX G fs x) else l_atom v
  | VAlu ALU_AND x (VL m) =>
      match low_mask_k m with
      | Some k => if PrimInt63.leb k 3%uint63 && ix_asan IX
                  then l_comb (linz_x IX G fs x) (- 2 ^ to_Z k) (l_atom (VAlu ALU_SRL x (VL (wlit k)))) else l_atom v
      | None => l_atom v
      end
  | VMd M_MUL x (VL c) =>
      if wltu (snd (sv_bounds_x IX x)) bit32w && wltu c bit32w then l_scale (w2Z c) (linz_x IX G fs x) else l_atom v
  | VExt sx lo n x =>
      if PrimInt63.eqb lo 0%uint63 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n 8%uint63
         && wltu (snd (sv_bounds_x IX x)) (ext_lim sx n) then linz_x IX G fs x else l_atom v
  | VAluw ALU_ADD x (VL z) =>
      let hx := snd (sv_bounds_x IX x) in
      if negb (wt z) && negb (wt hx) && wltu (wadd hx z) bit31w then l_comb (linz_x IX G fs x) 1 (l_const (w2Z z)) else l_atom v
  | _ => l_atom v
  end.

Definition gap_of_x (IX : fidx) (G : list gapc) (fs : list fact) (f : fact) : option gapc :=
  match f with
  | FULt p q => Some (l_comb (linz_x IX G fs q) (-1) (linz_x IX G fs p), 1%Z, false)
  | FULe p q => Some (l_comb (linz_x IX G fs q) (-1) (linz_x IX G fs p), 0%Z, false)
  | FEq p q => Some (l_comb (linz_x IX G fs q) (-1) (linz_x IX G fs p), 0%Z, true)
  | FNe p q => match ne0_term p q with Some t => Some (linz_x IX G fs t, 1%Z, false) | None => None end
  | _ => None
  end.
Fixpoint gaps_with_x (IX : fidx) (G : list gapc) (fs all : list fact) : list gapc :=
  match fs with
  | [] => []
  | f :: fs' => match gap_of_x IX G all f with Some g => g :: gaps_with_x IX G fs' all | None => gaps_with_x IX G fs' all end
  end.
Fixpoint gaps_again_x (IX : fidx) (G : list gapc) (fs all : list fact) (prev : list gapc) : list gapc :=
  match fs with
  | [] => []
  | f :: fs' =>
      if is_gap_fact f then
          match prev with
          | g :: prev' => (if fact_needs_gaps f then match gap_of_x IX G all f with Some g' => g' | None => g end else g)
                          :: gaps_again_x IX G fs' all prev'
          | [] => match gap_of_x IX G all f with Some g' => g' :: gaps_again_x IX G fs' all [] | None => gaps_again_x IX G fs' all [] end
          end
      else gaps_again_x IX G fs' all prev
  end.
Definition gaps_x (IX : fidx) (fs : list fact) : list gapc :=
  let g1 := gaps_with_x IX [] fs fs in let g2 := gaps_again_x IX g1 fs fs g1 in gaps_again_x IX g2 fs fs g2.

Definition lin_ltu_Gx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  let d := l_comb (linz_x IX G fs b) (-1) (linz_x IX G fs a) in
  match l_isconst d with
  | Some k => Some (0 <? k)%Z
  | None => let ab := atom_bounds_x IX (fst d) in
            match first_some (lin_try_x IX ab d) (cands1 d G) with
            | Some r => Some r
            | None => first_some (lin_try_x IX ab d) (cands2 d G)
            end
  end.
Definition lin_eq_Gx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  let d := l_comb (linz_x IX G fs b) (-1) (linz_x IX G fs a) in
  match l_isconst d with
  | Some k => Some (k =? 0)%Z
  | None => let ab := atom_bounds_x IX (fst d) in
            match first_some (lin_try_eq_x IX ab d) (cands1 d G) with
            | Some r => Some r
            | None => first_some (lin_try_eq_x IX ab d) (cands2 d G)
            end
  end.
Definition decide_ltu0_Gx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match decide_ltu_s fs a b with
  | Some r => Some r
  | None => match bnd_ltu_x IX a b with Some r => Some r | None => lin_ltu_Gx IX G fs a b end
  end.
Definition decide_ltu1_Gx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  if ne_known fs a b then match decide_ltu0_Gx IX G fs b a with Some false => Some true | _ => None end else None.
Definition decide_ltu2_Gx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match (match zext_idiom a with
         | Some x => match decide_ltu0_Gx IX G fs x b with Some true => Some true | _ => None end
         | None => None
         end) with
  | Some r => Some r
  | None => match zext_idiom b with
            | Some x => match decide_ltu0_Gx IX G fs a x with Some false => Some false | _ => None end
            | None => None
            end
  end.
Definition decide_ltu3_Gx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match a, b with
  | VAlu ALU_SRL x (VL c), VAlu ALU_SRL y (VL c') =>
      if PrimInt63.eqb (shamt6 c) (shamt6 c') && ix_asan IX then
        match decide_ltu0_Gx IX G fs x y with Some false => Some false | _ => None end
      else None
  | _, _ => None
  end.
Definition decide_ltu_Gx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match decide_ltu0_Gx IX G fs a b with
  | Some r => Some r
  | None => match decide_ltu1_Gx IX G fs a b with
            | Some r => Some r
            | None => match decide_ltu2_Gx IX G fs a b with
                      | Some r => Some r
                      | None => decide_ltu3_Gx IX G fs a b
                      end
            end
  end.

Definition mk_lit (fs : list fact) : list fact := List.flat_map (fun f => let g := anchor_norm f in if lit_sided g then [g] else []) fs.
Definition mk_rng (fs : list fact) : IMap.t (w64 * w64) :=
  List.fold_right (fun f m => match f with FRange k lo hi => IMap.add k (lo, hi) m | _ => m end) IMap.empty fs.
Definition mk_al (fs : list fact) : IMap.t int :=
  List.fold_right (fun f m => match f with FAlign k a => IMap.add k a m | _ => m end) IMap.empty fs.
Definition ix0 (fs : list fact) : fidx := FIx (mk_lit fs) (mk_rng fs) (mk_al fs) IMap.empty (asan_on fs).
Fixpoint add_vars (IX0 : fidx) (vs : list int) (m : IMap.t bnd) : IMap.t bnd :=
  match vs with
  | [] => m
  | k :: vs' => add_vars IX0 vs' (match IMap.find k m with Some _ => m | None => IMap.add k (var_bounds_x0 IX0 k) m end)
  end.
Fixpoint mk_vb (IX0 : fidx) (fs : list fact) (m : IMap.t bnd) : IMap.t bnd :=
  match fs with
  | [] => m
  | f :: fs' => mk_vb IX0 fs' (add_vars IX0 (fact_vs f) m)
  end.
Definition mk_ix (fs : list fact) : fidx :=
  let IX0 := ix0 fs in FIx (ix_lit IX0) (ix_rng IX0) (ix_al IX0) (mk_vb IX0 fs IMap.empty) (ix_asan IX0).

Definition ix_ok (fs : list fact) (IX : fidx) : Prop :=
  ix_lit IX = mk_lit fs
  /\ (forall k, find_range_x IX k = find_range fs k)
  /\ (forall k, find_align_x IX k = find_align fs k)
  /\ (forall k b, IMap.find k (ix_vb IX) = Some b -> b = var_bounds fs k)
  /\ ix_asan IX = asan_on fs.

Lemma fact_bnd1_nolit : forall f v b, lit_sided f = false -> fact_bnd1 f v b = b.
Proof.
  intros f v [lo hi] H. destruct f as [| |x y|x y|x y|x y|x y|x y]; cbn in *; try reflexivity;
    destruct (lit_of y); try discriminate H; destruct (lit_of x); try discriminate H; reflexivity.
Qed.

Lemma fact_bounds_l_eq : forall fs v b, fact_bounds_l (mk_lit fs) v b = fact_bounds fs v b.
Proof.
  induction fs as [|f fs IH]; intros v b; cbn; [reflexivity|].
  unfold mk_lit. cbn [List.flat_map]. fold (mk_lit fs).
  destruct (lit_sided (anchor_norm f)) eqn:L; cbn [app fact_bounds_l].
  - apply IH.
  - rewrite (fact_bnd1_nolit _ v b L). apply IH.
Qed.

Section Eq.
Variable fs : list fact.
Variable IX : fidx.
Hypothesis HIX : ix_ok fs IX.

Let Hlit : ix_lit IX = mk_lit fs := proj1 HIX.
Let Hrng : forall k, find_range_x IX k = find_range fs k := proj1 (proj2 HIX).
Let Hal : forall k, find_align_x IX k = find_align fs k := proj1 (proj2 (proj2 HIX)).
Let Hvb : forall k b, IMap.find k (ix_vb IX) = Some b -> b = var_bounds fs k := proj1 (proj2 (proj2 (proj2 HIX))).
Let Hasan : ix_asan IX = asan_on fs := proj2 (proj2 (proj2 (proj2 HIX))).

Lemma fact_bounds_x_eq : forall v b, fact_bounds_x IX v b = fact_bounds fs v b.
Proof. intros. unfold fact_bounds_x. rewrite Hlit. apply fact_bounds_l_eq. Qed.

Lemma nowrap_k_x_eq : forall k o, nowrap_k_x IX k o = nowrap_k fs k o.
Proof. intros. unfold nowrap_k_x, nowrap_k. rewrite Hrng. reflexivity. Qed.

Lemma bnd_struct_x_eq : forall (r1 r2 : sv -> bnd) v,
  (forall x, r1 x = r2 x) -> bnd_struct_x r1 IX v = bnd_struct r2 fs v.
Proof.
  intros r1 r2 v R. unfold bnd_struct_x, bnd_struct, bnd_addv. rewrite ?Hrng.
  destruct v; rewrite ?Hrng, ?R; try reflexivity.
  all: try (destruct op; rewrite ?R; try reflexivity).
  all: try (destruct v2; rewrite ?R; reflexivity).
  all: try (destruct sx; rewrite ?R; reflexivity).
Qed.

Lemma align_bnd_x_eq : forall k b, align_bnd_x IX k b = align_bnd fs k b.
Proof. intros. unfold align_bnd_x, align_bnd. rewrite Hal. reflexivity. Qed.

Lemma var_bounds_x0_eq : forall k, var_bounds_x0 IX k = var_bounds fs k.
Proof.
  intros. unfold var_bounds_x0, var_bounds. rewrite align_bnd_x_eq, !fact_bounds_x_eq.
  rewrite (bnd_struct_x_eq (fun _ => full_bnd) (fun _ => full_bnd)) by reflexivity. reflexivity.
Qed.

Lemma var_bounds_x_eq : forall k, var_bounds_x IX k = var_bounds fs k.
Proof.
  intros. unfold var_bounds_x. destruct (IMap.find k (ix_vb IX)) as [b|] eqn:F; [exact (Hvb k b F)| apply var_bounds_x0_eq].
Qed.

Lemma nowrap_kb_x_eq : forall k o, nowrap_kb_x IX k o = nowrap_kb fs k o.
Proof. intros. unfold nowrap_kb_x, nowrap_kb. rewrite nowrap_k_x_eq, var_bounds_x_eq. reflexivity. Qed.

Lemma sv_bounds_x_eq : forall v, sv_bounds_x IX v = sv_bounds fs v.
Proof.
  induction v; cbn [sv_bounds_x sv_bounds bnd_struct_x bnd_struct]; unfold bnd_addv;
    rewrite ?fact_bounds_x_eq, ?var_bounds_x_eq, ?Hrng; try reflexivity.
  all: repeat match goal with H : sv_bounds_x IX ?x = sv_bounds fs ?x |- _ => rewrite ?H; clear H end; try reflexivity.
Qed.

Definition abo (abx : abtab_x) : abtab := ((if fst abx then Some fs else None), snd abx).

Lemma atom_bounds_x_eq : forall t, abo (atom_bounds_x IX t) = atom_bounds fs t.
Proof.
  intros t. unfold abo, atom_bounds_x, atom_bounds. cbn [fst snd]. rewrite Hasan. f_equal.
  induction t as [|ac t IH]; [reflexivity|]. cbn [map]. rewrite sv_bounds_x_eq, IH. reflexivity.
Qed.
Lemma ab_find_x_eq : forall abx a, ab_find_x IX abx a = ab_find (abo abx) a.
Proof.
  intros [b l] a. unfold ab_find_x, ab_find, abo. cbn [fst snd].
  induction l as [|[a' b'] l IH]; cbn; [| rewrite IH; reflexivity].
  destruct b; [apply sv_bounds_x_eq| reflexivity].
Qed.
Lemma lt_lo_x_eq : forall abx t, lt_lo_x IX abx t = lt_lo (abo abx) t.
Proof. intros abx t. induction t as [|[a c] t IH]; cbn [lt_lo_x lt_lo]; [reflexivity|]. rewrite ab_find_x_eq, IH. reflexivity. Qed.
Lemma lt_hi_x_eq : forall abx t, lt_hi_x IX abx t = lt_hi (abo abx) t.
Proof. intros abx t. induction t as [|[a c] t IH]; cbn [lt_hi_x lt_hi]; [reflexivity|]. rewrite ab_find_x_eq, IH. reflexivity. Qed.
Lemma lin_bounds_x_eq : forall abx d sel, lin_bounds_x IX abx d sel = lin_bounds (abo abx) d sel.
Proof. intros. unfold lin_bounds_x, lin_bounds. rewrite lt_lo_x_eq, lt_hi_x_eq. reflexivity. Qed.
Lemma lin_try_x_eq : forall abx d sel, lin_try_x IX abx d sel = lin_try (abo abx) d sel.
Proof. intros. unfold lin_try_x, lin_try. rewrite lin_bounds_x_eq. reflexivity. Qed.
Lemma lin_try_eq_x_eq : forall abx d sel, lin_try_eq_x IX abx d sel = lin_try_eq (abo abx) d sel.
Proof. intros. unfold lin_try_eq_x, lin_try_eq. rewrite lin_bounds_x_eq. reflexivity. Qed.
Lemma lin_try_nonneg_x_eq : forall abx d sel, lin_try_nonneg_x IX abx d sel = lin_try_nonneg (abo abx) d sel.
Proof. intros. unfold lin_try_nonneg_x, lin_try_nonneg. rewrite lin_bounds_x_eq. reflexivity. Qed.

Lemma first_some_ext : forall {A B} (f g : A -> option B) l, (forall x, f x = g x) -> first_some f l = first_some g l.
Proof. intros A B f g l E. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite E, IH. reflexivity. Qed.

Lemma lin_nonneg_x_eq : forall G d, lin_nonneg_x IX G d = lin_nonneg G fs d.
Proof.
  intros. unfold lin_nonneg_x, lin_nonneg.
  rewrite (first_some_ext _ (lin_try_nonneg (atom_bounds fs (fst d)) d)); [reflexivity|].
  intros sel. rewrite lin_try_nonneg_x_eq, atom_bounds_x_eq. reflexivity.
Qed.

Lemma linz_x_eq : forall G v, linz_x IX G fs v = linz G fs v.
Proof.
  intros G v. induction v; cbn [linz_x linz]; rewrite ?nowrap_kb_x_eq, ?sv_bounds_x_eq, ?lin_nonneg_x_eq, ?Hasan; try reflexivity.
  all: repeat match goal with H : linz_x IX ?G0 fs ?x = linz ?G0 fs ?x |- _ => rewrite ?H; clear H end; rewrite ?sv_bounds_x_eq, ?lin_nonneg_x_eq; try reflexivity.
  all: try (destruct op; rewrite ?sv_bounds_x_eq, ?lin_nonneg_x_eq, ?Hasan; try reflexivity).
  all: try (destruct v2; rewrite ?sv_bounds_x_eq, ?lin_nonneg_x_eq, ?Hasan; try reflexivity).
  all: try (destruct (low_mask_k w); rewrite ?Hasan; reflexivity).
  all: try (destruct op0; reflexivity).
Qed.

Lemma gap_of_x_eq : forall G f, gap_of_x IX G fs f = gap_of G fs f.
Proof. intros. destruct f; cbn [gap_of_x gap_of]; rewrite ?linz_x_eq; try reflexivity. destruct (ne0_term a b); rewrite ?linz_x_eq; reflexivity. Qed.
Lemma gaps_with_x_eq : forall G l, gaps_with_x IX G l fs = gaps_with G l fs.
Proof. intros G l. induction l as [|f l IH]; cbn [gaps_with_x gaps_with]; [reflexivity|]. rewrite gap_of_x_eq, IH. reflexivity. Qed.
Lemma gaps_again_x_eq : forall G l prev, gaps_again_x IX G l fs prev = gaps_again G l fs prev.
Proof.
  intros G l. induction l as [|f l IH]; intros prev; cbn [gaps_again_x gaps_again]; [reflexivity|].
  rewrite ?gap_of_x_eq, ?IH. destruct (is_gap_fact f); [|reflexivity]. destruct prev; rewrite ?IH; reflexivity.
Qed.
Lemma gaps_x_eq : gaps_x IX fs = gaps fs.
Proof. unfold gaps_x, gaps. rewrite !gaps_with_x_eq. rewrite !gaps_again_x_eq. reflexivity. Qed.

Lemma bnd_ltu_x_eq : forall a b, bnd_ltu_x IX a b = bnd_ltu fs a b.
Proof. intros. unfold bnd_ltu_x, bnd_ltu. rewrite !sv_bounds_x_eq. reflexivity. Qed.
Lemma bnd_eq0_x_eq : forall v, bnd_eq0_x IX v = bnd_eq0 fs v.
Proof. intros. unfold bnd_eq0_x, bnd_eq0. rewrite sv_bounds_x_eq. reflexivity. Qed.
Lemma nonneg63_x_eq : forall v, nonneg63_x IX v = nonneg63 fs v.
Proof. intros. unfold nonneg63_x, nonneg63. rewrite sv_bounds_x_eq. reflexivity. Qed.

Lemma lin_ltu_Gx_eq : forall G a b, lin_ltu_Gx IX G fs a b = lin_ltu_G G fs a b.
Proof.
  intros. unfold lin_ltu_Gx, lin_ltu_G. rewrite !linz_x_eq.
  set (d := l_comb (linz G fs b) (-1) (linz G fs a)). destruct (l_isconst d); [reflexivity|].
  rewrite !(first_some_ext (lin_try_x IX (atom_bounds_x IX (fst d)) d) (lin_try (atom_bounds fs (fst d)) d)); [reflexivity| |];
    intros sel; rewrite lin_try_x_eq, atom_bounds_x_eq; reflexivity.
Qed.
Lemma lin_eq_Gx_eq : forall G a b, lin_eq_Gx IX G fs a b = lin_eq_G G fs a b.
Proof.
  intros. unfold lin_eq_Gx, lin_eq_G. rewrite !linz_x_eq.
  set (d := l_comb (linz G fs b) (-1) (linz G fs a)). destruct (l_isconst d); [reflexivity|].
  rewrite !(first_some_ext (lin_try_eq_x IX (atom_bounds_x IX (fst d)) d) (lin_try_eq (atom_bounds fs (fst d)) d)); [reflexivity| |];
    intros sel; rewrite lin_try_eq_x_eq, atom_bounds_x_eq; reflexivity.
Qed.
Lemma decide_ltu0_Gx_eq : forall G a b, decide_ltu0_Gx IX G fs a b = decide_ltu0_G G fs a b.
Proof. intros. unfold decide_ltu0_Gx, decide_ltu0_G. rewrite bnd_ltu_x_eq, lin_ltu_Gx_eq. reflexivity. Qed.
Lemma decide_ltu1_Gx_eq : forall G a b, decide_ltu1_Gx IX G fs a b = decide_ltu1_G G fs a b.
Proof. intros. unfold decide_ltu1_Gx, decide_ltu1_G. rewrite decide_ltu0_Gx_eq. reflexivity. Qed.
Lemma decide_ltu2_Gx_eq : forall G a b, decide_ltu2_Gx IX G fs a b = decide_ltu2_G G fs a b.
Proof.
  intros. unfold decide_ltu2_Gx, decide_ltu2_G.
  destruct (zext_idiom a); rewrite ?decide_ltu0_Gx_eq; destruct (zext_idiom b); rewrite ?decide_ltu0_Gx_eq; reflexivity.
Qed.
Lemma decide_ltu3_Gx_eq : forall G a b, decide_ltu3_Gx IX G fs a b = decide_ltu3_G G fs a b.
Proof.
  intros. unfold decide_ltu3_Gx, decide_ltu3_G. rewrite Hasan.
  destruct a; try reflexivity. destruct op; try reflexivity. destruct a2; try reflexivity.
  destruct b; try reflexivity. destruct op; try reflexivity. destruct b2; try reflexivity.
  rewrite decide_ltu0_Gx_eq. reflexivity.
Qed.
Lemma decide_ltu_Gx_eq : forall G a b, decide_ltu_Gx IX G fs a b = decide_ltu_G G fs a b.
Proof. intros. unfold decide_ltu_Gx, decide_ltu_G. rewrite decide_ltu0_Gx_eq, decide_ltu1_Gx_eq, decide_ltu2_Gx_eq, decide_ltu3_Gx_eq. reflexivity. Qed.

End Eq.

Lemma eqb_false_sym63 : forall a b, PrimInt63.eqb a b = false -> PrimInt63.eqb b a = false.
Proof.
  intros a b E. destruct (PrimInt63.eqb b a) eqn:E2; [|reflexivity].
  apply Uint63.eqb_correct in E2. subst b. rewrite Uint63.eqb_refl in E. discriminate E.
Qed.
Lemma mk_rng_ok : forall fs, IMap.bst (mk_rng fs) /\ forall k, IMap.find k (mk_rng fs) = find_range fs k.
Proof.
  induction fs as [|f fs [B IH]]; cbn [mk_rng List.fold_right find_range].
  - split; [apply IMap.bst_empty| intros k; rewrite IMap.find_empty; reflexivity].
  - fold (mk_rng fs). destruct f; try (split; [exact B| exact IH]).
    split; [apply IMap.bst_add; exact B|]. intros k0.
    destruct (PrimInt63.eqb k0 k) eqn:E.
    + apply Uint63.eqb_correct in E. subst k0. rewrite IMap.find_add_same by exact B. reflexivity.
    + rewrite IMap.find_add_other_eqb; [apply IH| exact B|]. apply eqb_false_sym63. exact E.
Qed.
Lemma mk_al_ok : forall fs, IMap.bst (mk_al fs) /\ forall k, match IMap.find k (mk_al fs) with Some m => m | None => 0%uint63 end = find_align fs k.
Proof.
  induction fs as [|f fs [B IH]]; cbn [mk_al List.fold_right find_align].
  - split; [apply IMap.bst_empty| intros k; rewrite IMap.find_empty; reflexivity].
  - fold (mk_al fs). destruct f; try (split; [exact B| exact IH]).
    split; [apply IMap.bst_add; exact B|]. intros k0.
    destruct (PrimInt63.eqb k0 k) eqn:E.
    + apply Uint63.eqb_correct in E. subst k0. rewrite IMap.find_add_same by exact B. reflexivity.
    + rewrite IMap.find_add_other_eqb; [apply IH| exact B|]. apply eqb_false_sym63. exact E.
Qed.

Lemma ix0_ok : forall fs, ix_ok fs (ix0 fs).
Proof.
  intros fs. unfold ix_ok, ix0, find_range_x, find_align_x. cbn [ix_lit ix_rng ix_al ix_vb ix_asan].
  split; [reflexivity|]. split; [apply (proj2 (mk_rng_ok fs))|]. split; [apply (proj2 (mk_al_ok fs))|].
  split; [| reflexivity]. intros k b F. rewrite IMap.find_empty in F. discriminate F.
Qed.

Lemma add_vars_ok : forall fs IX0, (forall k, var_bounds_x0 IX0 k = var_bounds fs k) ->
  forall vs m, IMap.bst m -> (forall k b, IMap.find k m = Some b -> b = var_bounds fs k) ->
  IMap.bst (add_vars IX0 vs m) /\ (forall k b, IMap.find k (add_vars IX0 vs m) = Some b -> b = var_bounds fs k).
Proof.
  intros fs IX0 V0. induction vs as [|k vs IH]; intros m B M; cbn [add_vars]; [split; assumption|].
  destruct (IMap.find k m) as [b0|] eqn:F; [apply IH; assumption|].
  apply IH; [apply IMap.bst_add; exact B|].
  intros k' b F'. destruct (PrimInt63.eqb k k') eqn:E.
  - apply Uint63.eqb_correct in E. subst k'. rewrite IMap.find_add_same in F' by exact B. injection F' as <-. apply V0.
  - rewrite IMap.find_add_other_eqb in F'; [exact (M _ _ F')| exact B| exact E].
Qed.
Lemma mk_vb_ok : forall fs IX0, (forall k, var_bounds_x0 IX0 k = var_bounds fs k) ->
  forall l m, IMap.bst m -> (forall k b, IMap.find k m = Some b -> b = var_bounds fs k) ->
  IMap.bst (mk_vb IX0 l m) /\ (forall k b, IMap.find k (mk_vb IX0 l m) = Some b -> b = var_bounds fs k).
Proof.
  intros fs IX0 V0. induction l as [|f l IH]; intros m B M; cbn [mk_vb]; [split; assumption|].
  destruct (add_vars_ok fs IX0 V0 (fact_vs f) m B M) as [B' M']. apply IH; assumption.
Qed.

Theorem mk_ix_ok : forall fs, ix_ok fs (mk_ix fs).
Proof.
  intros fs. pose proof (ix0_ok fs) as H0.
  assert (V0 : forall k, var_bounds_x0 (ix0 fs) k = var_bounds fs k) by (intros k; apply (var_bounds_x0_eq fs (ix0 fs) H0)).
  destruct H0 as (L & R & A & _ & S).
  unfold mk_ix. cbv zeta. unfold ix_ok, find_range_x, find_align_x in *. cbn [ix_lit ix_rng ix_al ix_vb ix_asan] in *.
  split; [exact L|]. split; [exact R|]. split; [exact A|]. split; [| exact S].
  apply (proj2 (mk_vb_ok fs (ix0 fs) V0 fs IMap.empty IMap.bst_empty ltac:(intros k b F; rewrite IMap.find_empty in F; discriminate F))).
Qed.

Definition gaps_f (fs : list fact) : list gapc := gaps_x (mk_ix fs) fs.
Lemma gaps_f_eq : forall fs, gaps_f fs = gaps fs.
Proof. intros. unfold gaps_f. apply gaps_x_eq. apply mk_ix_ok. Qed.

End GapsM.
