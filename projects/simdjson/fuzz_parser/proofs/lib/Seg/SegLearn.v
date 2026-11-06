(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegSR SegSlt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SL.

(* [comment removed for export] *)
Definition rng0 (kn : list kentry) (e : expr) : Z * Z :=
  match erange kn e with
  | Some (lo, hi) => (Z.max 0 lo, Z.min (2^64 - 1) hi)
  | None => (* [comment removed for export] *)
      match SSR.srange kn e with
      | Some (lo, hi) => if Z.leb 0 lo then (lo, Z.min (2^64 - 1) hi) else (0, 2^64 - 1)
      | None => (0, 2^64 - 1)
      end
  end.

(* [comment removed for export] *)
Inductive rel := RLtu | RGeu | REq | RNe | RLt | RGe.

Definition hrel (c : branch_cond) (t : bool) : rel :=
  match c, t with
  | BC_EQ, true | BC_NE, false => REq
  | BC_EQ, false | BC_NE, true => RNe
  | BC_LT, true | BC_GE, false => RLt
  | BC_LT, false | BC_GE, true => RGe
  | BC_LTU, true | BC_GEU, false => RLtu
  | BC_LTU, false | BC_GEU, true => RGeu
  end.

Definition is_litb (e : expr) : bool := match e with ELit _ => true | _ => false end.

(* [comment removed for export] *)
Definition fk (e : expr) (lo hi : Z) : option (list kentry) :=
  if hi <? lo then None else if is_litb e then Some [] else Some [KRange e lo hi].

Definition ocat (x y : option (list kentry)) : option (list kentry) :=
  match x, y with Some l1, Some l2 => Some (l1 ++ l2) | _, _ => None end.

(* [comment removed for export] *)
Definition dnorm_fk (e : expr) (lo hi : Z) : option (list kentry) :=
  match e with
  | EAlu ALU_SUB x y => let n := mkAlu ALU_SUB x y in if expr_eqb n e then Some [] else fk n lo hi
  | _ => Some []
  end.

Definition dfact (both : bool) (e : expr) (lo hi : Z) : option (list kentry) :=
  if both then ocat (fk e lo hi) (dnorm_fk e lo hi) else if hi <? lo then None else Some [].

Definition ltu_facts0 (kn : list kentry) (a b : expr) : option (list kentry) :=
  let '(al, ah) := rng0 kn a in let '(bl, bh) := rng0 kn b in
  ocat (fk a al (Z.min ah (bh - 1)))
   (ocat (fk b (Z.max bl (al + 1)) bh)
         (dfact (negb (is_litb a) && negb (is_litb b)) (EAlu ALU_SUB b a) 1 (bh - al))).

Definition geu_facts0 (kn : list kentry) (a b : expr) : option (list kentry) :=
  let '(al, ah) := rng0 kn a in let '(bl, bh) := rng0 kn b in
  ocat (fk a (Z.max al bl) ah)
   (ocat (fk b bl (Z.min bh ah))
         (dfact (negb (is_litb a) && negb (is_litb b)) (EAlu ALU_SUB a b) 0 (ah - bl))).

Definition eq_facts (kn : list kentry) (a b : expr) : option (list kentry) :=
  let '(al, ah) := rng0 kn a in let '(bl, bh) := rng0 kn b in
  ocat (fk a (Z.max al bl) (Z.min ah bh))
   (ocat (fk b (Z.max al bl) (Z.min ah bh))
         (dfact (negb (is_litb a) && negb (is_litb b)) (EAlu ALU_SUB a b) 0 0)).


(* [comment removed for export] *)
Definition dtrue (o : option bool) : bool := match o with Some true => true | _ => false end.

Definition ltu_facts (kn : list kentry) (a b : expr) : option (list kentry) :=
  if dtrue (decide_branch kn BC_GEU a b) then None else ltu_facts0 kn a b.

Definition geu_facts (kn : list kentry) (a b : expr) : option (list kentry) :=
  if dtrue (decide_branch kn BC_GEU b a) then eq_facts kn a b else geu_facts0 kn a b.

Definition ne_facts0 (kn : list kentry) (a b : expr) : option (list kentry) :=
  let '(al, ah) := rng0 kn a in let '(bl, bh) := rng0 kn b in
  if bl =? bh then
    (if al =? bl then fk a (al + 1) ah else if ah =? bl then fk a al (ah - 1) else Some [])
  else if al =? ah then
    (if bl =? al then fk b (bl + 1) bh else if bh =? al then fk b bl (bh - 1) else Some [])
  else Some [].

(* [comment removed for export] *)
Definition ne_diff (kn : list kentry) (x y : expr) : option (list kentry) :=
  if (is_litb x || is_litb y)%bool then Some [] else
  let '(dl, dh) := rng0 kn (EAlu ALU_SUB x y) in
  if dl =? 0 then fk (EAlu ALU_SUB x y) 1 dh else Some [].

(* [comment removed for export] *)
Definition ne_diffA (kn : list kentry) (x y : expr) : option (list kentry) :=
  if (is_litb x || is_litb y)%bool then Some [] else
  let D := mkAlu ALU_SUB x y in
  let '(dl, dh) := rng0 kn D in
  if dl =? 0 then fk D (2 ^ ealign kn D) dh else Some [].

(* [comment removed for export] *)
Definition ne_alignD (kn : list kentry) (x y : expr) : option (list kentry) :=
  if (is_litb x || is_litb y)%bool then Some [] else
  let D := mkAlu ALU_SUB x y in let '(dl, dh) := rng0 kn D in fk D (Z.max dl (2 ^ ealign kn D)) dh.

Definition ne_facts (kn : list kentry) (a b : expr) : option (list kentry) :=
  if dtrue (decide_branch kn BC_GEU b a) then ocat (ltu_facts0 kn a b) (ne_alignD kn b a)
  else if dtrue (decide_branch kn BC_GEU a b) then ocat (ltu_facts0 kn b a) (ne_alignD kn a b)
  else ocat (ne_facts0 kn a b) (ocat (ne_diff kn b a) (ocat (ne_diff kn a b) (ocat (ne_diffA kn b a) (ne_diffA kn a b)))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aff_eqk (kn : list kentry) (c k : Z) (v : expr) (z : Z) (isEq : bool) : option (list kentry) :=
  if Z.eqb k 0 then Some [] else
  let '(lo, hi) := rng0 kn v in
  let m1 := c + k * lo in let m2 := c + k * hi in
  if (if Z.leb 0 (Z.min m1 m2) then Z.ltb (Z.max m1 m2) (2^64) else false) then
    if Z.eqb ((z - c) mod k) 0 then
      let x := (z - c) / k in
      if isEq then (if (if Z.leb lo x then Z.leb x hi else false) then fk v x x else None)
      else (if Z.eqb x lo then fk v (lo + 1) hi else if Z.eqb x hi then fk v lo (hi - 1) else Some [])
    else (if isEq then None else Some [])
  else Some [].

Definition aff_eq (kn : list kentry) (a : expr) (z : Z) (isEq : bool) : option (list kentry) :=
  match lin_of a with
  | (c, [(k, v)]) =>
      if (if Z.eqb k 1 then true else Z.eqb k (-1)) then
        let x := (k * (z - c)) mod 2^64 in
        let '(lo, hi) := rng0 kn v in
        if isEq then (if (if Z.leb lo x then Z.leb x hi else false) then fk v x x else None)
        else (if Z.eqb x lo then fk v (lo + 1) hi else if Z.eqb x hi then fk v lo (hi - 1) else Some [])
      else aff_eqk kn c k v z isEq
  | _ => Some []
  end.

Definition aff_lit (kn : list kentry) (isEq : bool) (a b : expr) : option (list kentry) :=
  match b with
  | ELit z => aff_eq kn a (z mod 2^64) isEq
  | _ => match a with ELit z => aff_eq kn b (z mod 2^64) isEq | _ => Some [] end
  end.

Definition nonneg (kn : list kentry) (a b : expr) : bool :=
  (snd (rng0 kn a) <? 2^63) && (snd (rng0 kn b) <? 2^63).

(* [comment removed for export] *)
Definition is_zerob (e : expr) : bool := match e with ELit z => Z.eqb z 0 | _ => false end.

Definition slt0 (kn : list kentry) (a b : expr) : option (list kentry) :=
  if is_zerob b then let '(al, ah) := rng0 kn a in fk a (Z.max al (2^63)) ah
  else if is_zerob a then let '(bl, bh) := rng0 kn b in fk b (Z.max bl 1) (Z.min bh (2^63 - 1))
  else Some [].

Definition sge0 (kn : list kentry) (a b : expr) : option (list kentry) :=
  if is_zerob b then let '(al, ah) := rng0 kn a in fk a al (Z.min ah (2^63 - 1)) else Some [].

(* [comment removed for export] *)
Definition sbias (e : expr) : expr := mkAlu ALU_ADD e (ELit (2^63)).

Definition sfact (kn : list kentry) (e : expr) (lo hi : Z) : option (list kentry) :=
  let '(l0, h0) := match SSR.srange kn e with Some r => r | None => (- 2^63, 2^63 - 1) end in
  let lo' := Z.max lo l0 in let hi' := Z.min hi h0 in
  if Z.leb lo' hi' then (if is_litb e then Some [] else Some [KRange (sbias e) (lo' + 2^63) (hi' + 2^63)]) else None.

(* [comment removed for export] *)
Definition slit_a (kn : list kentry) (islt : bool) (a b : expr) : option (list kentry) :=
  match a with
  | ELit c => if Z.eqb (c mod 2^64) 0 then Some [] else
              let cs := bv_swrap 64 c in if islt then sfact kn b (cs + 1) (2^63 - 1) else sfact kn b (- 2^63) cs
  | _ => Some []
  end.

Definition slit (kn : list kentry) (islt : bool) (a b : expr) : option (list kentry) :=
  match b with
  | ELit c => if Z.eqb (c mod 2^64) 0 then Some [] else
              let cs := bv_swrap 64 c in if islt then sfact kn a (- 2^63) (cs - 1) else sfact kn a cs (2^63 - 1)
  | _ => slit_a kn islt a b
  end.

Definition learn0 (kn : list kentry) (c : branch_cond) (t : bool) (a b : expr) : option (list kentry) :=
  match hrel c t with
  | RLtu => ltu_facts kn a b
  | RGeu => geu_facts kn a b
  | REq => ocat (eq_facts kn a b) (aff_lit kn true a b)
  | RNe => ocat (ne_facts kn a b) (aff_lit kn false a b)
  | RLt => if nonneg kn a b then ltu_facts kn a b else ocat (slt0 kn a b) (slit kn true a b)
  | RGe => if nonneg kn a b then geu_facts kn a b else ocat (sge0 kn a b) (slit kn false a b)
  end.

(* [comment removed for export] *)
Definition tight_up (kn : list kentry) (e : expr) (lo hi : Z) : option (list kentry) :=
  fold_right (fun K acc =>
    match K with
    | KRange (EAlu ALU_ADD x (ELit c)) l2 h2 =>
        if expr_eqb x e then
          let c' := c mod 2^64 in
          if hi + c' <? 2^64 then ocat (fk e (Z.max lo (l2 - c')) (Z.min hi (h2 - c'))) acc else acc
        else acc
    | _ => acc
    end) (Some []) kn.

Definition tight_dn (kn : list kentry) (e : expr) (lo hi : Z) : option (list kentry) :=
  match e with
  | EAlu ALU_ADD x (ELit c) =>
      let c' := c mod 2^64 in let '(xl, xh) := rng0 kn x in
      if xh + c' <? 2^64 then fk x (Z.max xl (lo - c')) (Z.min xh (hi - c')) else Some []
  | _ => Some []
  end.

Definition tighten (kn : list kentry) (l : list kentry) : option (list kentry) :=
  fold_right (fun K acc =>
    match K with
    | KRange e lo hi => ocat (ocat (tight_up kn e lo hi) (tight_dn kn e lo hi)) acc
    | _ => acc
    end) (Some []) l.

(* [comment removed for export] *)
Definition slt_refute (kn : list kentry) (c : branch_cond) (t : bool) (a b : expr) : bool :=
  match hrel c t with
  | RLt => match SSLT.slt_dec kn a b with Some false => true | _ => false end
  | RGe => match SSLT.slt_dec kn a b with Some true => true | _ => false end
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition al_round (j l h : Z) : Z * Z := let p := 2 ^ j in (- ((- l) / p) * p, (h / p) * p).
Definition lin_eqbL (x y : lin) : bool := if Z.eqb (fst x) (fst y) then SSR.terms_eqb (snd x) (snd y) else false.
Definition scale_kL (l l' : lin) : option Z :=
  match snd l, snd l' with
  | (c, a) :: _, (c', a') :: _ =>
      if expr_eqb a a' then if Z.eqb c' 0 then None else
        if Z.eqb (c mod c') 0 then (if Z.leb 1 (c / c') then Some (c / c') else None) else None
      else None
  | _, _ => None
  end.
Definition sc_fact (e : expr) (K : kentry) : option (Z * Z) :=
  match K with
  | KRange f l h =>
      match scale_kL (lin_of e) (lin_of f) with
      | Some k => if lin_eqbL (lin_of e) (lscale k (lin_of f)) then
                    if Z.leb 0 l then (if Z.ltb (k * h) (2 ^ 64) then Some (k * l, k * h) else None) else None
                  else None
      | None => None
      end
  | _ => None
  end.
Fixpoint sc_range (e : expr) (kn : list kentry) : option (Z * Z) :=
  match kn with [] => None | K :: r => match sc_fact e K with Some x => Some x | None => sc_range e r end end.
Definition urange (kn : list kentry) (e : expr) : option (Z * Z) :=
  match erange kn e with
  | Some r => Some r
  | None => match SSR.srange kn e with
            | Some (l, h) => let '(l', h') := al_round (ealign kn e) l h in if Z.leb 0 l' then Some (l', h') else None
            | None => sc_range e kn
            end
  end.
Definition ult_refute (kn : list kentry) (c : branch_cond) (t : bool) (a b : expr) : bool :=
  match hrel c t with
  | RLtu => match urange kn a, urange kn b with Some (la, _), Some (_, hb) => Z.leb hb la | _, _ => false end
  | RGeu => match urange kn a, urange kn b with Some (_, ha), Some (lb, _) => Z.ltb ha lb | _, _ => false end
  | _ => false
  end.

(* [comment removed for export] *)
Definition al_empty1 (kn : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      if Z.ltb 0 lo then if Z.ltb (hi - lo) 4096 then
        let '(l', h') := al_round (ealign kn e) lo hi in Z.ltb h' l'
      else false else false
  | _ => false
  end.
Fixpoint al_empty (kn : list kentry) (l : list kentry) : bool :=
  match l with [] => false | K :: r => if al_empty1 kn K then true else al_empty kn r end.

(* [comment removed for export] *)
Definition al_tight1 (kn : list kentry) (K : kentry) : option (list kentry) :=
  match K with
  | KRange e lo hi =>
      let j := ealign kn e in
      if Z.eqb j 0 then Some [] else
      let '(l', h') := al_round j lo hi in
      if Z.ltb h' l' then None
      else if (if Z.eqb l' lo then Z.eqb h' hi else false) then Some [] else Some [KRange e l' h']
  | _ => Some []
  end.
Fixpoint al_tight (kn : list kentry) (l : list kentry) : option (list kentry) :=
  match l with
  | [] => Some []
  | K :: r => match al_tight1 kn K with
              | None => None
              | Some x => match al_tight kn r with None => None | Some y => Some (x ++ y) end
              end
  end.

(* [comment removed for export] *)
Definition aff_fact (kn : list kentry) (K : kentry) : list kentry :=
  match K with
  | KRange e lo hi =>
      match lin_of e with
      | (c, [(k, v)]) =>
          if Z.leb 1 k then
            let '(vl, vh) := rng0 kn v in
            if (if Z.leb 0 (c + k * vl) then Z.ltb (c + k * vh) (2^64) else false) then
              [KRange v (Z.max vl (- ((c - lo) / k))) (Z.min vh ((hi - c) / k))]
            else []
          else []
      | _ => []
      end
  | _ => []
  end.
Definition aff_facts (kn : list kentry) : list kentry := flat_map (aff_fact kn) kn.

(* [comment removed for export] *)
Definition sub_fact1 (kn : list kentry) (n : nat) (v : Z) (K : kentry) : option (list kentry) :=
  match K with
  | KRange e lo hi =>
      let e2 := esubst (EVar n) (ELit v) e in
      if expr_eqb e2 e then Some [] else
      if (Z.leb 0 lo && Z.ltb hi (2 ^ 64))%bool then
        match lin_of e2 with
        | (c, []) => if (Z.leb lo (c mod 2 ^ 64) && Z.leb (c mod 2 ^ 64) hi)%bool then Some [] else None
        | (c, [(k, x)]) =>
            if Z.eqb k 0 then Some [] else
            let '(vl, vh) := rng0 kn x in
            let tmin := if Z.ltb 0 k then c + k * vl else c + k * vh in
            let tmax := if Z.ltb 0 k then c + k * vh else c + k * vl in
            if (Z.ltb (hi - 2 ^ 64) tmin && Z.ltb tmax (lo + 2 ^ 64))%bool then
              let L := if Z.ltb 0 k then - ((c - lo) / k) else - ((hi - c) / (- k)) in
              let H := if Z.ltb 0 k then (hi - c) / k else (c - lo) / (- k) in
              let L' := Z.max vl L in let H' := Z.min vh H in
              if Z.ltb H' L' then None else Some [KRange x L' H']
            else Some []
        | (c, ts) => if (Z.leb 0 (lo - c) && Z.ltb (hi - c) (2 ^ 64))%bool then Some [KRange (unlin (0, ts)) (lo - c) (hi - c)]
                     else Some []
        end
      else Some []
  | _ => Some []
  end.
Fixpoint sub_pass (kn0 : list kentry) (n : nat) (v : Z) (l acc : list kentry) : option (list kentry) :=
  match l with
  | [] => Some acc
  | K :: r => match sub_fact1 (acc ++ kn0) n v K with
              | None => None
              | Some d => sub_pass kn0 n v r (d ++ acc)
              end
  end.
Definition sub_facts (kn : list kentry) (n : nat) (v : Z) : option (list kentry) :=
  match sub_pass kn n v kn [] with
  | None => None
  | Some d1 => match sub_pass (d1 ++ kn) n v kn [] with None => None | Some d2 => Some (d2 ++ d1) end
  end.

(* [comment removed for export] *)
Definition and0 (kn : list kentry) (e : expr) : bool :=
  match e with
  | EAlu ALU_AND x (ELit m) => Z.ltb (m mod 2 ^ 64) (2 ^ ealign kn x)
  | EAlu ALU_AND (ELit m) x => Z.ltb (m mod 2 ^ 64) (2 ^ ealign kn x)
  | _ => false
  end.
Definition lit0 (e : expr) : bool := match e with ELit z => Z.eqb (z mod 2 ^ 64) 0 | _ => false end.
Definition andal_refute (kn : list kentry) (c : branch_cond) (t : bool) (a b : expr) : bool :=
  match hrel c t with
  | RNe => if and0 kn a then lit0 b else if and0 kn b then lit0 a else false
  | _ => false
  end.

Definition learn (kn : list kentry) (c : branch_cond) (t : bool) (a b : expr) : option (list kentry) :=
  if andal_refute kn c t a b then None else
  if slt_refute kn c t a b then None else
  if ult_refute kn c t a b then None else
  match learn0 kn c t a b with
  | Some l => match ocat (tighten kn l) (Some l) with   (* [comment removed for export] *)
              | Some l' => if al_empty kn l' then None else Some l'
              | None => None
              end
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable segs : list Segment.
Variable E : env.
Variable M : word -> option byte.

Lemma rng0_sound : forall kn e, know_ok segs E M kn ->
  fst (rng0 kn e) <= bv_unsigned (edenot E e) <= snd (rng0 kn e) /\ 0 <= fst (rng0 kn e) /\ snd (rng0 kn e) <= 2^64 - 1.
Proof.
  intros kn e HK. pose proof (bv_unsigned_in_range 64 (edenot E e)) as HR. unfold bv_modulus in HR. cbn in HR.
  unfold rng0. destruct (erange kn e) as [[lo hi]|] eqn:Er.
  - pose proof (erange_sound segs E M kn e lo hi HK Er) as H. cbn [fst snd]. lia.
  - destruct (SSR.srange kn e) as [[lo hi]|] eqn:Es; [|cbn [fst snd]; lia].
    destruct (Z.leb 0 lo) eqn:Hl; [|cbn [fst snd]; lia]. apply Z.leb_le in Hl.
    pose proof (SSR.srange_sound_u segs E M kn e lo hi HK Es Hl) as H. cbn [fst snd]. lia.
Qed.

Definition rel_den (r : rel) (x y : word) : Prop :=
  match r with
  | RLtu => bv_unsigned x < bv_unsigned y
  | RGeu => bv_unsigned y <= bv_unsigned x
  | REq => bv_unsigned x = bv_unsigned y
  | RNe => bv_unsigned x <> bv_unsigned y
  | RLt => bv_signed x < bv_signed y
  | RGe => bv_signed y <= bv_signed x
  end.

Lemma hrel_sound : forall c t (x y : word), branch_taken c x y = t -> rel_den (hrel c t) x y.
Proof.
  intros c t x y H. unfold branch_taken, bv_lts, bv_ltu, bv_eqb in H.
  destruct c, t; cbn [hrel rel_den];
    repeat match goal with
    | H : negb _ = true |- _ => apply negb_true_iff in H
    | H : negb _ = false |- _ => apply negb_false_iff in H
    | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
    | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
    end; lia.
Qed.

Lemma fk_sound : forall e lo hi l, fk e lo hi = Some l ->
  lo <= bv_unsigned (edenot E e) <= hi -> know_ok segs E M l.
Proof.
  intros e lo hi l H Hr. unfold fk in H. destruct (hi <? lo); [discriminate|].
  destruct (is_litb e); injection H as <-; [constructor|]. constructor; [|constructor]. cbn [kentry_ok]. lia.
Qed.

Lemma fk_none : forall e lo hi, fk e lo hi = None -> lo <= bv_unsigned (edenot E e) <= hi -> False.
Proof.
  intros e lo hi H Hr. unfold fk in H. destruct (hi <? lo) eqn:Hc; [apply Z.ltb_lt in Hc; lia|].
  destruct (is_litb e); discriminate.
Qed.

Lemma ocat_sound : forall x y l, ocat x y = Some l ->
  (forall lx, x = Some lx -> know_ok segs E M lx) -> (forall ly, y = Some ly -> know_ok segs E M ly) -> know_ok segs E M l.
Proof.
  intros x y l H Hx Hy. destruct x as [lx|], y as [ly|]; try discriminate. injection H as <-.
  apply Forall_app. split; [apply Hx | apply Hy]; reflexivity.
Qed.

Lemma ocat_none : forall x y, ocat x y = None -> x = None \/ y = None.
Proof. intros [x|] [y|] H; try discriminate; auto. Qed.

Lemma dnorm_fk_ok : forall e lo hi, lo <= bv_unsigned (edenot E e) <= hi ->
  (forall l, dnorm_fk e lo hi = Some l -> know_ok segs E M l) /\ dnorm_fk e lo hi <> None.
Proof.
  intros e lo hi Hr. unfold dnorm_fk.
  destruct e as [| |op x y| | | | |]; try (split; [intros l H; injection H as <-; constructor | discriminate]).
  destruct op; try (split; [intros l H; injection H as <-; constructor | discriminate]).
  destruct (expr_eqb (mkAlu ALU_SUB x y) (EAlu ALU_SUB x y)); [split; [intros l H; injection H as <-; constructor | discriminate]|].
  assert (Hn : lo <= bv_unsigned (edenot E (mkAlu ALU_SUB x y)) <= hi) by (rewrite mkAlu_denot; exact Hr).
  split; [intros l H; exact (fk_sound _ _ _ _ H Hn) | intros H; exact (fk_none _ _ _ H Hn)].
Qed.

Lemma dfact_sound : forall bth e lo hi l, dfact bth e lo hi = Some l ->
  lo <= bv_unsigned (edenot E e) <= hi -> know_ok segs E M l.
Proof.
  intros bth e lo hi l H Hr. unfold dfact in H. destruct bth.
  - eapply ocat_sound; [exact H | intros lx Hx; exact (fk_sound _ _ _ _ Hx Hr) | exact (proj1 (dnorm_fk_ok e lo hi Hr))].
  - destruct (hi <? lo); [discriminate|]. injection H as <-. constructor.
Qed.

Lemma dfact_none : forall bth e lo hi, dfact bth e lo hi = None -> lo <= bv_unsigned (edenot E e) <= hi -> False.
Proof.
  intros bth e lo hi H Hr. unfold dfact in H. destruct bth.
  - apply ocat_none in H as [H|H]; [exact (fk_none _ _ _ H Hr) | exact (proj2 (dnorm_fk_ok e lo hi Hr) H)].
  - destruct (hi <? lo) eqn:Hc; [apply Z.ltb_lt in Hc; lia | discriminate].
Qed.

Lemma sub_unsigned : forall x y : word, bv_unsigned x >= bv_unsigned y ->
  bv_unsigned (edenot E (EAlu ALU_SUB (ELit 0) (ELit 0))) = 0 /\
  bv_unsigned (bv_sub x y) = bv_unsigned x - bv_unsigned y.
Proof.
  intros x y H. split.
  - cbn [edenot]. unfold alu64, alu. rewrite bv_sub_unsigned, !Z_to_bv_unsigned. reflexivity.
  - rewrite bv_sub_unsigned. pose proof (bv_unsigned_in_range 64 x). pose proof (bv_unsigned_in_range 64 y).
    apply bv_wrap_small. lia.
Qed.

Lemma den_sub : forall a b, bv_unsigned (edenot E b) >= bv_unsigned (edenot E a) ->
  bv_unsigned (edenot E (EAlu ALU_SUB b a)) = bv_unsigned (edenot E b) - bv_unsigned (edenot E a).
Proof. intros a b H. cbn [edenot]. unfold alu64, alu. apply (proj2 (sub_unsigned _ _ H)). Qed.

Lemma ltu_facts0_ok : forall kn a b, know_ok segs E M kn -> bv_unsigned (edenot E a) < bv_unsigned (edenot E b) ->
  (forall l, ltu_facts0 kn a b = Some l -> know_ok segs E M l) /\ ltu_facts0 kn a b <> None.
Proof.
  intros kn a b HK Hlt. unfold ltu_facts0.
  pose proof (rng0_sound kn a HK) as Ra. pose proof (rng0_sound kn b HK) as Rb.
  destruct (rng0 kn a) as [al ah], (rng0 kn b) as [bl bh]. cbn [fst snd] in Ra, Rb.
  assert (H1 : al <= bv_unsigned (edenot E a) <= Z.min ah (bh - 1)) by lia.
  assert (H2 : Z.max bl (al + 1) <= bv_unsigned (edenot E b) <= bh) by lia.
  assert (H3 : 1 <= bv_unsigned (edenot E (EAlu ALU_SUB b a)) <= bh - al) by (rewrite den_sub by lia; lia).
  split.
  - intros l H. eapply ocat_sound; [exact H | intros lx Hx; exact (fk_sound _ _ _ _ Hx H1) |].
    intros ly Hy. eapply ocat_sound; [exact Hy | intros lx Hx; exact (fk_sound _ _ _ _ Hx H2) |].
    intros lz Hz. exact (dfact_sound _ _ _ _ _ Hz H3).
  - intros H. apply ocat_none in H as [H|H]; [exact (fk_none _ _ _ H H1)|].
    apply ocat_none in H as [H|H]; [exact (fk_none _ _ _ H H2)|]. exact (dfact_none _ _ _ _ H H3).
Qed.

Lemma geu_facts0_ok : forall kn a b, know_ok segs E M kn -> bv_unsigned (edenot E b) <= bv_unsigned (edenot E a) ->
  (forall l, geu_facts0 kn a b = Some l -> know_ok segs E M l) /\ geu_facts0 kn a b <> None.
Proof.
  intros kn a b HK Hge. unfold geu_facts0.
  pose proof (rng0_sound kn a HK) as Ra. pose proof (rng0_sound kn b HK) as Rb.
  destruct (rng0 kn a) as [al ah], (rng0 kn b) as [bl bh]. cbn [fst snd] in Ra, Rb.
  assert (H1 : Z.max al bl <= bv_unsigned (edenot E a) <= ah) by lia.
  assert (H2 : bl <= bv_unsigned (edenot E b) <= Z.min bh ah) by lia.
  assert (H3 : 0 <= bv_unsigned (edenot E (EAlu ALU_SUB a b)) <= ah - bl) by (rewrite den_sub by lia; lia).
  split.
  - intros l H. eapply ocat_sound; [exact H | intros lx Hx; exact (fk_sound _ _ _ _ Hx H1) |].
    intros ly Hy. eapply ocat_sound; [exact Hy | intros lx Hx; exact (fk_sound _ _ _ _ Hx H2) |].
    intros lz Hz. exact (dfact_sound _ _ _ _ _ Hz H3).
  - intros H. apply ocat_none in H as [H|H]; [exact (fk_none _ _ _ H H1)|].
    apply ocat_none in H as [H|H]; [exact (fk_none _ _ _ H H2)|]. exact (dfact_none _ _ _ _ H H3).
Qed.

Lemma eq_facts_ok : forall kn a b, know_ok segs E M kn -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b) ->
  (forall l, eq_facts kn a b = Some l -> know_ok segs E M l) /\ eq_facts kn a b <> None.
Proof.
  intros kn a b HK Heq. unfold eq_facts.
  pose proof (rng0_sound kn a HK) as Ra. pose proof (rng0_sound kn b HK) as Rb.
  destruct (rng0 kn a) as [al ah], (rng0 kn b) as [bl bh]. cbn [fst snd] in Ra, Rb.
  assert (H1 : Z.max al bl <= bv_unsigned (edenot E a) <= Z.min ah bh) by lia.
  assert (H2 : Z.max al bl <= bv_unsigned (edenot E b) <= Z.min ah bh) by lia.
  assert (H3 : 0 <= bv_unsigned (edenot E (EAlu ALU_SUB a b)) <= 0) by (rewrite den_sub by lia; lia).
  split.
  - intros l H. eapply ocat_sound; [exact H | intros lx Hx; exact (fk_sound _ _ _ _ Hx H1) |].
    intros ly Hy. eapply ocat_sound; [exact Hy | intros lx Hx; exact (fk_sound _ _ _ _ Hx H2) |].
    intros lz Hz. exact (dfact_sound _ _ _ _ _ Hz H3).
  - intros H. apply ocat_none in H as [H|H]; [exact (fk_none _ _ _ H H1)|].
    apply ocat_none in H as [H|H]; [exact (fk_none _ _ _ H H2)|]. exact (dfact_none _ _ _ _ H H3).
Qed.

Lemma ne_facts0_ok : forall kn a b, know_ok segs E M kn -> bv_unsigned (edenot E a) <> bv_unsigned (edenot E b) ->
  (forall l, ne_facts0 kn a b = Some l -> know_ok segs E M l) /\ ne_facts0 kn a b <> None.
Proof.
  intros kn a b HK Hne. unfold ne_facts0.
  pose proof (rng0_sound kn a HK) as Ra. pose proof (rng0_sound kn b HK) as Rb.
  destruct (rng0 kn a) as [al ah], (rng0 kn b) as [bl bh]. cbn [fst snd] in Ra, Rb.
  destruct (bl =? bh) eqn:C1; [apply Z.eqb_eq in C1|].
  { destruct (al =? bl) eqn:C2; [apply Z.eqb_eq in C2|].
    { assert (H1 : al + 1 <= bv_unsigned (edenot E a) <= ah) by lia.
      split; [intros l H; exact (fk_sound _ _ _ _ H H1) | intros H; exact (fk_none _ _ _ H H1)]. }
    destruct (ah =? bl) eqn:C3; [apply Z.eqb_eq in C3|].
    { assert (H1 : al <= bv_unsigned (edenot E a) <= ah - 1) by lia.
      split; [intros l H; exact (fk_sound _ _ _ _ H H1) | intros H; exact (fk_none _ _ _ H H1)]. }
    split; [intros l H; injection H as <-; constructor | discriminate]. }
  destruct (al =? ah) eqn:C2; [apply Z.eqb_eq in C2|].
  { destruct (bl =? al) eqn:C3; [apply Z.eqb_eq in C3|].
    { assert (H1 : bl + 1 <= bv_unsigned (edenot E b) <= bh) by lia.
      split; [intros l H; exact (fk_sound _ _ _ _ H H1) | intros H; exact (fk_none _ _ _ H H1)]. }
    destruct (bh =? al) eqn:C4; [apply Z.eqb_eq in C4|].
    { assert (H1 : bl <= bv_unsigned (edenot E b) <= bh - 1) by lia.
      split; [intros l H; exact (fk_sound _ _ _ _ H H1) | intros H; exact (fk_none _ _ _ H H1)]. }
    split; [intros l H; injection H as <-; constructor | discriminate]. }
  split; [intros l H; injection H as <-; constructor | discriminate].
Qed.

Lemma sub_wrap : forall x y : word, bv_unsigned x < bv_unsigned y ->
  bv_unsigned (edenot E (EAlu ALU_SUB (ELit 0) (ELit 0))) = 0 /\
  bv_unsigned (bv_sub x y) = 2^64 - (bv_unsigned y - bv_unsigned x).
Proof.
  intros x y H. split; [cbn [edenot]; unfold alu64, alu; rewrite bv_sub_unsigned, !Z_to_bv_unsigned; reflexivity|].
  rewrite bv_sub_unsigned. pose proof (bv_unsigned_in_range 64 x). pose proof (bv_unsigned_in_range 64 y).
  unfold bv_wrap, bv_modulus in *. cbn in *.
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
Qed.

Lemma dtrue_sound : forall kn c a b, know_ok segs E M kn -> dtrue (decide_branch kn c a b) = true ->
  branch_taken c (edenot E a) (edenot E b) = true.
Proof.
  intros kn c a b HK H. destruct (decide_branch kn c a b) as [[|]|] eqn:D; try discriminate.
  exact (decide_branch_sound segs E M kn c a b true HK D).
Qed.

Lemma geu_true : forall x y : word, branch_taken BC_GEU x y = true -> bv_unsigned y <= bv_unsigned x.
Proof. intros x y H. cbn [branch_taken] in H. unfold bv_ltu in H. apply negb_true_iff, Z.ltb_ge in H. exact H. Qed.

Lemma ltu_facts_ok : forall kn a b, know_ok segs E M kn -> bv_unsigned (edenot E a) < bv_unsigned (edenot E b) ->
  (forall l, ltu_facts kn a b = Some l -> know_ok segs E M l) /\ ltu_facts kn a b <> None.
Proof.
  intros kn a b HK Hlt. unfold ltu_facts.
  destruct (dtrue (decide_branch kn BC_GEU a b)) eqn:D.
  - exfalso. pose proof (geu_true _ _ (dtrue_sound kn BC_GEU a b HK D)). lia.
  - exact (ltu_facts0_ok kn a b HK Hlt).
Qed.

Lemma geu_facts_ok : forall kn a b, know_ok segs E M kn -> bv_unsigned (edenot E b) <= bv_unsigned (edenot E a) ->
  (forall l, geu_facts kn a b = Some l -> know_ok segs E M l) /\ geu_facts kn a b <> None.
Proof.
  intros kn a b HK Hge. unfold geu_facts.
  destruct (dtrue (decide_branch kn BC_GEU b a)) eqn:D.
  - pose proof (geu_true _ _ (dtrue_sound kn BC_GEU b a HK D)). apply eq_facts_ok; [exact HK | lia].
  - exact (geu_facts0_ok kn a b HK Hge).
Qed.

Lemma ne_diffA_ok : forall kn x y, know_ok segs E M kn -> bv_unsigned (edenot E x) <> bv_unsigned (edenot E y) ->
  (forall l, ne_diffA kn x y = Some l -> know_ok segs E M l) /\ ne_diffA kn x y <> None.
Proof.
  intros kn x y HK Hne. unfold ne_diffA.
  destruct (is_litb x || is_litb y)%bool; [split; [intros l H; injection H as <-; constructor | discriminate]|].
  pose proof (rng0_sound kn (mkAlu ALU_SUB x y) HK) as R. destruct (rng0 kn (mkAlu ALU_SUB x y)) as [dl dh]. cbn [fst snd] in R.
  destruct (dl =? 0) eqn:Hd; [|split; [intros l H; injection H as <-; constructor | discriminate]].
  apply Z.eqb_eq in Hd. subst dl.
  destruct (ealign_sound segs E M kn (mkAlu ALU_SUB x y) HK) as [Hr Hdiv].
  assert (H0 : bv_unsigned (edenot E (mkAlu ALU_SUB x y)) <> 0).
  { rewrite mkAlu_denot. unfold alu64, alu. intros Hz. apply Hne. rewrite bv_sub_unsigned in Hz.
    pose proof (bv_unsigned_in_range 64 (edenot E x)). pose proof (bv_unsigned_in_range 64 (edenot E y)).
    unfold bv_wrap, bv_modulus in *. cbn in *.
    apply Z.mod_divide in Hz; [|lia]. destruct Hz as [q Hq].
    assert (q = 0) by nia. subst q. lia. }
  assert (H1 : 2 ^ ealign kn (mkAlu ALU_SUB x y) <= bv_unsigned (edenot E (mkAlu ALU_SUB x y)) <= dh).
  { split; [|lia]. apply Z.divide_pos_le; [lia | exact Hdiv]. }
  split; [intros l H; exact (fk_sound _ _ _ _ H H1) | intros H; exact (fk_none _ _ _ H H1)].
Qed.

Lemma ne_alignD_ok : forall kn x y, know_ok segs E M kn -> bv_unsigned (edenot E y) < bv_unsigned (edenot E x) ->
  (forall l, ne_alignD kn x y = Some l -> know_ok segs E M l) /\ ne_alignD kn x y <> None.
Proof.
  intros kn x y HK Hlt. unfold ne_alignD.
  destruct (is_litb x || is_litb y)%bool; [split; [intros l H; injection H as <-; constructor | discriminate]|].
  pose proof (rng0_sound kn (mkAlu ALU_SUB x y) HK) as R. destruct (rng0 kn (mkAlu ALU_SUB x y)) as [dl dh]. cbn [fst snd] in R.
  destruct (ealign_sound segs E M kn (mkAlu ALU_SUB x y) HK) as [Hr Hdiv].
  assert (HD : bv_unsigned (edenot E (mkAlu ALU_SUB x y)) = bv_unsigned (edenot E x) - bv_unsigned (edenot E y)).
  { rewrite mkAlu_denot. unfold alu64, alu. rewrite bv_sub_unsigned. unfold bv_wrap, bv_modulus. cbn.
    pose proof (bv_unsigned_in_range 64 (edenot E x)). pose proof (bv_unsigned_in_range 64 (edenot E y)).
    unfold bv_modulus in *. cbn in *. apply Z.mod_small. lia. }
  assert (H1 : Z.max dl (2 ^ ealign kn (mkAlu ALU_SUB x y)) <= bv_unsigned (edenot E (mkAlu ALU_SUB x y)) <= dh).
  { split; [|lia]. apply Z.max_lub; [lia|]. apply Z.divide_pos_le; [lia | exact Hdiv]. }
  split; [intros l H; exact (fk_sound _ _ _ _ H H1) | intros H; exact (fk_none _ _ _ H H1)].
Qed.

Lemma ne_diff_ok : forall kn x y, know_ok segs E M kn -> bv_unsigned (edenot E x) <> bv_unsigned (edenot E y) ->
  (forall l, ne_diff kn x y = Some l -> know_ok segs E M l) /\ ne_diff kn x y <> None.
Proof.
  intros kn x y HK Hne. unfold ne_diff.
  destruct (is_litb x || is_litb y)%bool; [split; [intros l H; injection H as <-; constructor | discriminate]|].
  pose proof (rng0_sound kn (EAlu ALU_SUB x y) HK) as R. destruct (rng0 kn (EAlu ALU_SUB x y)) as [dl dh]. cbn [fst snd] in R.
  destruct (dl =? 0) eqn:Hd; [|split; [intros l H; injection H as <-; constructor | discriminate]].
  apply Z.eqb_eq in Hd. subst dl.
  assert (H1 : 1 <= bv_unsigned (edenot E (EAlu ALU_SUB x y)) <= dh).
  { split; [|lia]. cbn [edenot] in R |- *. unfold alu64, alu in R |- *.
    destruct (Z.eq_dec (bv_unsigned (bv_sub (edenot E x) (edenot E y))) 0) as [Hz|Hz]; [|lia].
    exfalso. apply Hne. rewrite bv_sub_unsigned in Hz.
    pose proof (bv_unsigned_in_range 64 (edenot E x)). pose proof (bv_unsigned_in_range 64 (edenot E y)).
    unfold bv_wrap, bv_modulus in *. cbn in *.
    apply Z.mod_divide in Hz; [|lia]. destruct Hz as [q Hq].
    assert (q = 0) by nia. subst q. lia. }
  split; [intros l H; exact (fk_sound _ _ _ _ H H1) | intros H; exact (fk_none _ _ _ H H1)].
Qed.

Lemma ne_facts_ok : forall kn a b, know_ok segs E M kn -> bv_unsigned (edenot E a) <> bv_unsigned (edenot E b) ->
  (forall l, ne_facts kn a b = Some l -> know_ok segs E M l) /\ ne_facts kn a b <> None.
Proof.
  intros kn a b HK Hne. unfold ne_facts.
  destruct (dtrue (decide_branch kn BC_GEU b a)) eqn:D1.
  { pose proof (geu_true _ _ (dtrue_sound kn BC_GEU b a HK D1)).
    destruct (ltu_facts0_ok kn a b HK ltac:(lia)) as [A1 A2]. destruct (ne_alignD_ok kn b a HK ltac:(lia)) as [B1 B2].
    split; [intros l H0; eapply ocat_sound; [exact H0 | exact A1 | exact B1] | intros H0; apply ocat_none in H0 as [H0|H0]; [exact (A2 H0) | exact (B2 H0)]]. }
  destruct (dtrue (decide_branch kn BC_GEU a b)) eqn:D2.
  { pose proof (geu_true _ _ (dtrue_sound kn BC_GEU a b HK D2)).
    destruct (ltu_facts0_ok kn b a HK ltac:(lia)) as [A1 A2]. destruct (ne_alignD_ok kn a b HK ltac:(lia)) as [B1 B2].
    split; [intros l H0; eapply ocat_sound; [exact H0 | exact A1 | exact B1] | intros H0; apply ocat_none in H0 as [H0|H0]; [exact (A2 H0) | exact (B2 H0)]]. }
  destruct (ne_facts0_ok kn a b HK Hne) as [A1 A2]. destruct (ne_diff_ok kn b a HK (not_eq_sym Hne)) as [B1 B2].
  destruct (ne_diff_ok kn a b HK Hne) as [C1 C2].
  destruct (ne_diffA_ok kn b a HK (not_eq_sym Hne)) as [D1' D2']. destruct (ne_diffA_ok kn a b HK Hne) as [F1 F2].
  split.
  - intros l H. eapply ocat_sound; [exact H | exact A1 |]. intros ly Hy. eapply ocat_sound; [exact Hy | exact B1 |].
    intros lz Hz. eapply ocat_sound; [exact Hz | exact C1 |]. intros lw Hw. eapply ocat_sound; [exact Hw | exact D1' | exact F1].
  - intros H. apply ocat_none in H as [H|H]; [exact (A2 H)|]. apply ocat_none in H as [H|H]; [exact (B2 H)|].
    apply ocat_none in H as [H|H]; [exact (C2 H)|]. apply ocat_none in H as [H|H]; [exact (D2' H) | exact (F2 H)].
Qed.

Lemma signed_small : forall x : word, bv_unsigned x < 2^63 -> bv_signed x = bv_unsigned x.
Proof.
  intros x H. unfold bv_signed. pose proof (bv_unsigned_in_range 64 x) as R.
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.

Lemma nonneg_sound : forall kn a b, know_ok segs E M kn -> nonneg kn a b = true ->
  bv_signed (edenot E a) = bv_unsigned (edenot E a) /\ bv_signed (edenot E b) = bv_unsigned (edenot E b).
Proof.
  intros kn a b HK H. unfold nonneg in H. apply andb_prop in H as [Ha Hb]. apply Z.ltb_lt in Ha, Hb.
  pose proof (rng0_sound kn a HK) as Ra. pose proof (rng0_sound kn b HK) as Rb.
  split; apply signed_small; lia.
Qed.

Lemma is_zerob_den : forall e, is_zerob e = true -> bv_unsigned (edenot E e) = 0 /\ bv_signed (edenot E e) = 0.
Proof.
  intros e H. destruct e; try discriminate. apply Z.eqb_eq in H. subst. cbn [edenot].
  rewrite Z_to_bv_unsigned. split; [reflexivity|]. unfold bv_signed. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma signed_neg : forall x : word, bv_signed x < 0 -> 2^63 <= bv_unsigned x.
Proof.
  intros x H. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H. pose proof (bv_unsigned_in_range 64 x) as R.
  unfold bv_modulus in R. cbn in H, R |- *.
  destruct (Z_lt_le_dec (bv_unsigned x) (2^63)) as [Hl|Hl]; [|lia].
  rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma signed_nonneg : forall x : word, 0 <= bv_signed x -> bv_unsigned x < 2^63.
Proof.
  intros x H. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H. pose proof (bv_unsigned_in_range 64 x) as R.
  unfold bv_modulus in R. cbn in H, R |- *.
  destruct (Z_lt_le_dec (bv_unsigned x) (2^63)) as [Hl|Hl]; [lia|].
  rewrite (Z.mod_eq (bv_unsigned x + 2^63)) in H by lia.
  assert ((bv_unsigned x + 2^63) / 2^64 = 1) by (symmetry; apply Z.div_unique with (r := bv_unsigned x + 2^63 - 2^64); lia). lia.
Qed.

Lemma slt0_ok : forall kn a b, know_ok segs E M kn -> bv_signed (edenot E a) < bv_signed (edenot E b) ->
  (forall l, slt0 kn a b = Some l -> know_ok segs E M l) /\ slt0 kn a b <> None.
Proof.
  intros kn a b HK H. unfold slt0.
  destruct (is_zerob b) eqn:Zb.
  - destruct (is_zerob_den b Zb) as [_ Sb]. rewrite Sb in H. pose proof (signed_neg _ H) as Ha.
    pose proof (rng0_sound kn a HK) as Ra. destruct (rng0 kn a) as [al ah]. cbn [fst snd] in Ra.
    split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
  - destruct (is_zerob a) eqn:Za; [|split; [intros l Hl; injection Hl as <-; constructor | discriminate]].
    destruct (is_zerob_den a Za) as [_ Sa]. rewrite Sa in H.
    assert (Hb : bv_unsigned (edenot E b) < 2^63) by (apply signed_nonneg; lia).
    assert (Hb1 : 1 <= bv_unsigned (edenot E b)) by (rewrite (signed_small _ Hb) in H; lia).
    pose proof (rng0_sound kn b HK) as Rb. destruct (rng0 kn b) as [bl bh]. cbn [fst snd] in Rb.
    split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
Qed.

Lemma sge0_ok : forall kn a b, know_ok segs E M kn -> bv_signed (edenot E b) <= bv_signed (edenot E a) ->
  (forall l, sge0 kn a b = Some l -> know_ok segs E M l) /\ sge0 kn a b <> None.
Proof.
  intros kn a b HK H. unfold sge0.
  destruct (is_zerob b) eqn:Zb; [|split; [intros l Hl; injection Hl as <-; constructor | discriminate]].
  destruct (is_zerob_den b Zb) as [_ Sb]. rewrite Sb in H. pose proof (signed_nonneg _ H) as Ha.
  pose proof (rng0_sound kn a HK) as Ra. destruct (rng0 kn a) as [al ah]. cbn [fst snd] in Ra.
  split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
Qed.

(* [comment removed for export] *)
Lemma sbias_den : forall e, bv_unsigned (edenot E (sbias e)) = bv_signed (edenot E e) + 2^63.
Proof.
  intros e. unfold sbias. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Zplus_mod_idemp_r. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma s_range64 : forall w : word, - 2^63 <= bv_signed w < 2^63.
Proof. intros w. exact (SSR.s_range w). Qed.

Lemma sfact_ok : forall kn e lo hi, know_ok segs E M kn -> lo <= bv_signed (edenot E e) <= hi ->
  (forall l, sfact kn e lo hi = Some l -> know_ok segs E M l) /\ sfact kn e lo hi <> None.
Proof.
  intros kn e lo hi HK H. unfold sfact.
  assert (R0 : forall l0 h0, (match SSR.srange kn e with Some r => r | None => (- 2^63, 2^63 - 1) end) = (l0, h0) ->
                 l0 <= bv_signed (edenot E e) <= h0).
  { intros l0 h0 Hr. destruct (SSR.srange kn e) as [[l1 h1]|] eqn:Es.
    - injection Hr as <- <-. exact (SSR.srange_sound segs E M kn e l1 h1 HK Es).
    - injection Hr as <- <-. pose proof (s_range64 (edenot E e)). lia. }
  destruct (match SSR.srange kn e with Some r => r | None => (- 2^63, 2^63 - 1) end) as [l0 h0] eqn:Er.
  pose proof (R0 l0 h0 eq_refl) as B.
  destruct (Z.leb (Z.max lo l0) (Z.min hi h0)) eqn:Hle; [|apply Z.leb_gt in Hle; lia].
  split; [|destruct (is_litb e); discriminate].
  intros l Hl. destruct (is_litb e); injection Hl as <-; [constructor|].
  constructor; [|constructor]. cbn [kentry_ok]. rewrite sbias_den. lia.
Qed.

Lemma slit_ok : forall kn (islt : bool) a b, know_ok segs E M kn ->
  (if islt then bv_signed (edenot E a) < bv_signed (edenot E b) else bv_signed (edenot E b) <= bv_signed (edenot E a)) ->
  (forall l, slit kn islt a b = Some l -> know_ok segs E M l) /\ slit kn islt a b <> None.
Proof.
  intros kn islt a b HK H. unfold slit.
  assert (Sl : forall c, bv_signed (edenot E (ELit c)) = bv_swrap 64 c) by (intros c; cbn [edenot]; apply SSR.s_lit).
  assert (A : (forall l, slit_a kn islt a b = Some l -> know_ok segs E M l) /\ slit_a kn islt a b <> None).
  { unfold slit_a. destruct a as [c| | | | | | |];
      [ destruct (Z.eqb (c mod 2^64) 0); [split; [intros l Hl; injection Hl as <-; constructor | discriminate]|];
        destruct islt; apply sfact_ok; try exact HK; rewrite Sl in H; pose proof (s_range64 (edenot E b)); lia | .. ];
      (split; [intros l Hl; injection Hl as <-; constructor | discriminate]). }
  destruct b as [c| | | | | | |]; try exact A.
  destruct (Z.eqb (c mod 2^64) 0); [split; [intros l Hl; injection Hl as <-; constructor | discriminate]|].
  destruct islt; apply sfact_ok; try exact HK; rewrite Sl in H; pose proof (s_range64 (edenot E a)); lia.
Qed.

(* [comment removed for export] *)
Lemma aff_eqk_ok : forall kn a c k v z q (isEq : bool), know_ok segs E M kn -> 0 <= z < 2^64 ->
  (if isEq then bv_unsigned (edenot E a) = z else bv_unsigned (edenot E a) <> z) ->
  c + (k * bv_unsigned (edenot E v) + 0) = bv_unsigned (edenot E a) + q * 2^64 ->
  (forall l, aff_eqk kn c k v z isEq = Some l -> know_ok segs E M l) /\ aff_eqk kn c k v z isEq <> None.
Proof.
  intros kn a c k v z q isEq HK Hz H Hq. unfold aff_eqk.
  destruct (Z.eqb k 0) eqn:Hk0; [split; [intros l Hl; injection Hl as <-; constructor | discriminate]|]. apply Z.eqb_neq in Hk0.
  pose proof (rng0_sound kn v HK) as Rv. destruct (rng0 kn v) as [lo hi] eqn:Er. cbn [fst snd] in Rv.
  pose proof (bv_unsigned_in_range 64 (edenot E a)) as RA. unfold bv_modulus in RA. cbn in RA.
  set (uv := bv_unsigned (edenot E v)) in *.
  destruct (if Z.leb 0 (Z.min (c + k * lo) (c + k * hi)) then Z.ltb (Z.max (c + k * lo) (c + k * hi)) (2^64) else false) eqn:Hnw;
    [|split; [intros l Hl; injection Hl as <-; constructor | discriminate]].
  destruct (Z.leb 0 (Z.min (c + k * lo) (c + k * hi))) eqn:H1; [|discriminate]. apply Z.leb_le in H1. apply Z.ltb_lt in Hnw.
  assert (B : 0 <= c + k * uv < 2^64).
  { destruct (Z.lt_ge_cases k 0) as [Hn|Hp].
    - assert (k * hi <= k * uv <= k * lo) by (split; apply Z.mul_le_mono_nonpos_l; lia). lia.
    - assert (k * lo <= k * uv <= k * hi) by (split; apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (Hq0 : q = 0) by nia. subst q.
  assert (HA : bv_unsigned (edenot E a) = c + k * uv) by lia.
  destruct (Z.eqb ((z - c) mod k) 0) eqn:Hd.
  - apply Z.eqb_eq in Hd. apply Z.mod_divide in Hd; [|exact Hk0]. destruct Hd as [x0 Hx0].
    assert (Ex : (z - c) / k = x0) by (rewrite Hx0; apply Z.div_mul; exact Hk0).
    rewrite Ex. destruct isEq.
    + assert (Huv : uv = x0) by (apply (Z.mul_reg_l _ _ k Hk0); lia).
      destruct (if Z.leb lo x0 then Z.leb x0 hi else false) eqn:Hin; [|destruct (Z.leb lo x0) eqn:A; [apply Z.leb_gt in Hin|apply Z.leb_gt in A]; lia].
      split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
    + assert (Huv : uv <> x0) by (intros C; apply H; rewrite HA, C; lia).
      destruct (Z.eqb x0 lo) eqn:E1; [apply Z.eqb_eq in E1|].
      * split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
      * destruct (Z.eqb x0 hi) eqn:E2; [apply Z.eqb_eq in E2|].
        -- split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
        -- split; [intros l Hl; injection Hl as <-; constructor | discriminate].
  - destruct isEq; [|split; [intros l Hl; injection Hl as <-; constructor | discriminate]].
    exfalso. apply Z.eqb_neq in Hd. apply Hd. apply Z.mod_divide; [exact Hk0|]. exists uv. lia.
Qed.
Lemma aff_eq_ok : forall kn a z (isEq : bool), know_ok segs E M kn -> 0 <= z < 2^64 ->
  (if isEq then bv_unsigned (edenot E a) = z else bv_unsigned (edenot E a) <> z) ->
  (forall l, aff_eq kn a z isEq = Some l -> know_ok segs E M l) /\ aff_eq kn a z isEq <> None.
Proof.
  intros kn a z isEq HK Hz H. unfold aff_eq.
  pose proof (lin_of_sound E a) as [q Hq]. unfold lden, uE in Hq.
  destruct (lin_of a) as [c ts] eqn:HL. cbn [fst snd] in Hq.
  destruct ts as [|[k v] [|t ts']]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
  cbn [tden] in Hq. unfold uE in Hq.
  destruct (if Z.eqb k 1 then true else Z.eqb k (-1)) eqn:Hk; [|exact (aff_eqk_ok kn a c k v z q isEq HK Hz H Hq)].
  assert (Hk' : k = 1 \/ k = -1) by (destruct (Z.eqb k 1) eqn:H1; [apply Z.eqb_eq in H1; lia | apply Z.eqb_eq in Hk; lia]).
  pose proof (rng0_sound kn v HK) as Rv. destruct (rng0 kn v) as [lo hi] eqn:Er. cbn [fst snd] in Rv.
  pose proof (bv_unsigned_in_range 64 (edenot E v)) as RV. unfold bv_modulus in RV. cbn in RV.
  pose proof (bv_unsigned_in_range 64 (edenot E a)) as RA. unfold bv_modulus in RA. cbn in RA.
  set (x := (k * (z - c)) mod 2^64).
  assert (KEY : bv_unsigned (edenot E a) = z <-> bv_unsigned (edenot E v) = x).
  { unfold x. split; intros Heq.
    - rewrite Heq in Hq. destruct Hk' as [-> | ->]; [apply Z.mod_unique with (- q) | apply Z.mod_unique with q]; lia.
    - rewrite Zmod_eq_full in Heq by lia.
      set (w := (k * (z - c)) / 2^64) in Heq. clearbody w.
      destruct Hk' as [-> | ->]; lia. }
  pose proof (Z.mod_pos_bound (k * (z - c)) (2^64) ltac:(lia)) as RX. fold x in RX.
  destruct isEq.
  - apply KEY in H. rewrite H in Rv.
    destruct (if Z.leb lo x then Z.leb x hi else false) eqn:Hin; [|destruct (Z.leb lo x) eqn:A; [apply Z.leb_gt in Hin|apply Z.leb_gt in A]; lia].
    split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
  - assert (Hne : bv_unsigned (edenot E v) <> x) by (intros C; apply H; apply KEY; exact C).
    destruct (Z.eqb x lo) eqn:H1; [apply Z.eqb_eq in H1|].
    + split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
    + destruct (Z.eqb x hi) eqn:H2; [apply Z.eqb_eq in H2|].
      * split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
      * split; [intros l Hl; injection Hl as <-; constructor | discriminate].
Qed.

Lemma aff_lit_ok : forall kn (isEq : bool) a b, know_ok segs E M kn ->
  (if isEq then bv_unsigned (edenot E a) = bv_unsigned (edenot E b) else bv_unsigned (edenot E a) <> bv_unsigned (edenot E b)) ->
  (forall l, aff_lit kn isEq a b = Some l -> know_ok segs E M l) /\ aff_lit kn isEq a b <> None.
Proof.
  intros kn isEq a b HK H. unfold aff_lit.
  assert (UL : forall z, bv_unsigned (edenot E (ELit z)) = z mod 2^64) by (intros z; cbn [edenot]; rewrite Z_to_bv_unsigned; apply bv_wrap64_mod).
  destruct b as [z| | | | | | |].
  - rewrite UL in H. apply aff_eq_ok; [exact HK | apply Z.mod_pos_bound; lia | exact H].
  - destruct a as [z| | | | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
    rewrite UL in H. apply aff_eq_ok; [exact HK | apply Z.mod_pos_bound; lia | destruct isEq; congruence].
  - destruct a as [z| | | | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
    rewrite UL in H. apply aff_eq_ok; [exact HK | apply Z.mod_pos_bound; lia | destruct isEq; congruence].
  - destruct a as [z| | | | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
    rewrite UL in H. apply aff_eq_ok; [exact HK | apply Z.mod_pos_bound; lia | destruct isEq; congruence].
  - destruct a as [z| | | | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
    rewrite UL in H. apply aff_eq_ok; [exact HK | apply Z.mod_pos_bound; lia | destruct isEq; congruence].
  - destruct a as [z| | | | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
    rewrite UL in H. apply aff_eq_ok; [exact HK | apply Z.mod_pos_bound; lia | destruct isEq; congruence].
  - destruct a as [z| | | | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
    rewrite UL in H. apply aff_eq_ok; [exact HK | apply Z.mod_pos_bound; lia | destruct isEq; congruence].
  - destruct a as [z| | | | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
    rewrite UL in H. apply aff_eq_ok; [exact HK | apply Z.mod_pos_bound; lia | destruct isEq; congruence].
Qed.

(* [comment removed for export] *)
Theorem learn0_sound : forall kn c t a b l,
  know_ok segs E M kn -> branch_taken c (edenot E a) (edenot E b) = t ->
  learn0 kn c t a b = Some l -> know_ok segs E M l.
Proof.
  intros kn c t a b l HK Hb Hl. pose proof (hrel_sound c t _ _ Hb) as HR. unfold learn0 in Hl.
  destruct (hrel c t); cbn [rel_den] in HR.
  - exact (proj1 (ltu_facts_ok kn a b HK HR) l Hl).
  - exact (proj1 (geu_facts_ok kn a b HK HR) l Hl).
  - exact (ocat_sound _ _ l Hl (proj1 (eq_facts_ok kn a b HK HR)) (proj1 (aff_lit_ok kn true a b HK HR))).
  - exact (ocat_sound _ _ l Hl (proj1 (ne_facts_ok kn a b HK HR)) (proj1 (aff_lit_ok kn false a b HK HR))).
  - destruct (nonneg kn a b) eqn:Hn.
    + destruct (nonneg_sound kn a b HK Hn) as [Ea Eb]. rewrite Ea, Eb in HR.
      exact (proj1 (ltu_facts_ok kn a b HK HR) l Hl).
    + exact (ocat_sound _ _ l Hl (proj1 (slt0_ok kn a b HK HR)) (proj1 (slit_ok kn true a b HK HR))).
  - destruct (nonneg kn a b) eqn:Hn.
    + destruct (nonneg_sound kn a b HK Hn) as [Ea Eb]. rewrite Ea, Eb in HR.
      exact (proj1 (geu_facts_ok kn a b HK HR) l Hl).
    + exact (ocat_sound _ _ l Hl (proj1 (sge0_ok kn a b HK HR)) (proj1 (slit_ok kn false a b HK HR))).
Qed.

(* [comment removed for export] *)
Theorem learn0_none : forall kn c t a b,
  know_ok segs E M kn -> learn0 kn c t a b = None -> branch_taken c (edenot E a) (edenot E b) <> t.
Proof.
  intros kn c t a b HK Hl Hb. pose proof (hrel_sound c t _ _ Hb) as HR. unfold learn0 in Hl.
  destruct (hrel c t); cbn [rel_den] in HR.
  - exact (proj2 (ltu_facts_ok kn a b HK HR) Hl).
  - exact (proj2 (geu_facts_ok kn a b HK HR) Hl).
  - destruct (ocat_none _ _ Hl) as [N|N]; [exact (proj2 (eq_facts_ok kn a b HK HR) N) | exact (proj2 (aff_lit_ok kn true a b HK HR) N)].
  - destruct (ocat_none _ _ Hl) as [N|N]; [exact (proj2 (ne_facts_ok kn a b HK HR) N) | exact (proj2 (aff_lit_ok kn false a b HK HR) N)].
  - destruct (nonneg kn a b) eqn:Hn; [|destruct (ocat_none _ _ Hl) as [N|N]; [exact (proj2 (slt0_ok kn a b HK HR) N) | exact (proj2 (slit_ok kn true a b HK HR) N)]].
    destruct (nonneg_sound kn a b HK Hn) as [Ea Eb]. rewrite Ea, Eb in HR.
    exact (proj2 (ltu_facts_ok kn a b HK HR) Hl).
  - destruct (nonneg kn a b) eqn:Hn; [|destruct (ocat_none _ _ Hl) as [N|N]; [exact (proj2 (sge0_ok kn a b HK HR) N) | exact (proj2 (slit_ok kn false a b HK HR) N)]].
    destruct (nonneg_sound kn a b HK Hn) as [Ea Eb]. rewrite Ea, Eb in HR.
    exact (proj2 (geu_facts_ok kn a b HK HR) Hl).
Qed.

(* [comment removed for export] *)
Lemma add_lit_den : forall x c, bv_unsigned (edenot E x) + c mod 2^64 < 2^64 ->
  bv_unsigned (edenot E (EAlu ALU_ADD x (ELit c))) = bv_unsigned (edenot E x) + c mod 2^64.
Proof.
  intros x c H. cbn [edenot]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn. pose proof (bv_unsigned_in_range 64 (edenot E x)) as R. unfold bv_modulus in R. cbn in R.
  pose proof (Z.mod_pos_bound c (2^64) ltac:(lia)).
  rewrite Z.mod_small; [reflexivity | lia].
Qed.

Lemma tight_up_ok : forall kn e lo hi, know_ok segs E M kn -> lo <= bv_unsigned (edenot E e) <= hi ->
  (forall l, tight_up kn e lo hi = Some l -> know_ok segs E M l) /\ tight_up kn e lo hi <> None.
Proof.
  intros kn e lo hi HK He. unfold tight_up. induction kn as [|K kn IH]; [split; [intros l Hl; injection Hl as <-; constructor | discriminate]|].
  inversion HK as [|K' kn' HK1 HK2]; subst. destruct (IH HK2) as [IH1 IH2]. cbn [fold_right].
  destruct K as [| | | | | | | | |]; try exact (conj IH1 IH2).
  destruct e0 as [| |op x y| | | | |]; try exact (conj IH1 IH2). destruct op; try exact (conj IH1 IH2).
  destruct y as [c| | | | | | |]; try exact (conj IH1 IH2).
  destruct (expr_eqb x e) eqn:Hx; [|exact (conj IH1 IH2)]. apply expr_eqb_eq in Hx. subst x.
  destruct (hi + c mod 2^64 <? 2^64) eqn:Hw; [|exact (conj IH1 IH2)]. apply Z.ltb_lt in Hw.
  cbn [kentry_ok] in HK1. rewrite (add_lit_den e c ltac:(lia)) in HK1.
  split.
  - intros l Hl. eapply ocat_sound; [exact Hl | | exact IH1]. intros lx Hlx. apply (fk_sound _ _ _ _ Hlx). lia.
  - intros Hn. apply ocat_none in Hn as [Hn|Hn]; [apply (fk_none _ _ _ Hn); lia | exact (IH2 Hn)].
Qed.

Lemma tight_dn_ok : forall kn e lo hi, know_ok segs E M kn -> lo <= bv_unsigned (edenot E e) <= hi ->
  (forall l, tight_dn kn e lo hi = Some l -> know_ok segs E M l) /\ tight_dn kn e lo hi <> None.
Proof.
  intros kn e lo hi HK He. unfold tight_dn.
  destruct e as [| |op x y| | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
  destruct op; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
  destruct y as [c| | | | | | |]; try (split; [intros l Hl; injection Hl as <-; constructor | discriminate]).
  pose proof (rng0_sound kn x HK) as Rx. destruct (rng0 kn x) as [xl xh]. cbn [fst snd] in Rx.
  destruct (xh + c mod 2^64 <? 2^64) eqn:Hw; [|split; [intros l Hl; injection Hl as <-; constructor | discriminate]].
  apply Z.ltb_lt in Hw. rewrite (add_lit_den x c ltac:(lia)) in He.
  split; [intros l Hl; apply (fk_sound _ _ _ _ Hl); lia | intros Hn; apply (fk_none _ _ _ Hn); lia].
Qed.

Lemma tighten_ok : forall kn l, know_ok segs E M kn -> know_ok segs E M l ->
  (forall l', tighten kn l = Some l' -> know_ok segs E M l') /\ tighten kn l <> None.
Proof.
  intros kn l HK. induction l as [|K l IH]; intros Hl; [split; [intros l' H; injection H as <-; constructor | discriminate]|].
  inversion Hl as [|K' l' HK1 HK2]; subst. destruct (IH HK2) as [IH1 IH2]. unfold tighten. cbn [fold_right]. fold (tighten kn l).
  destruct K as [e lo hi| | | | | | | | |]; try exact (conj IH1 IH2).
  cbn [kentry_ok] in HK1.
  destruct (tight_up_ok kn e lo hi HK HK1) as [U1 U2]. destruct (tight_dn_ok kn e lo hi HK HK1) as [D1 D2].
  split.
  - intros l' H. eapply ocat_sound; [exact H | | exact IH1]. intros lx Hx. eapply ocat_sound; [exact Hx | exact U1 | exact D1].
  - intros H. apply ocat_none in H as [H|H]; [apply ocat_none in H as [H|H]; [exact (U2 H) | exact (D2 H)] | exact (IH2 H)].
Qed.

Theorem learn_sound : forall kn c t a b l,
  know_ok segs E M kn -> branch_taken c (edenot E a) (edenot E b) = t ->
  learn kn c t a b = Some l -> know_ok segs E M l.
Proof.
  intros kn c t a b l HK Hb Hl. unfold learn in Hl. destruct (andal_refute kn c t a b); [discriminate|].
  destruct (slt_refute kn c t a b); [discriminate|].
  destruct (ult_refute kn c t a b); [discriminate|].
  destruct (learn0 kn c t a b) as [l0|] eqn:H0; [|discriminate].
  pose proof (learn0_sound kn c t a b l0 HK Hb H0) as K0.
  destruct (ocat (tighten kn l0) (Some l0)) as [l1|] eqn:Ho; [|discriminate].
  destruct (al_empty kn l1); [discriminate|]. injection Hl as <-.
  eapply ocat_sound; [exact Ho | exact (proj1 (tighten_ok kn l0 HK K0)) | intros lx Hx; injection Hx as <-; exact K0].
Qed.

Lemma land_al0 : forall x m j : Z, 0 <= j -> Z.divide (2 ^ j) x -> 0 <= m < 2 ^ j -> Z.land x m = 0.
Proof.
  intros x m j Hj [k Hk] Hm. subst x. apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n 0) as [Hn0|Hn0]; [rewrite Z.testbit_neg_r by lia; reflexivity|].
  destruct (Z.lt_ge_cases n j) as [Lj|Gj].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec m 0) as [->|Hm0]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 m n); [apply andb_false_r | lia |].
    apply Z.log2_lt_pow2; [lia|]. assert (2 ^ j <= 2 ^ n) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma and0_ok : forall kn e, know_ok segs E M kn -> and0 kn e = true -> bv_unsigned (edenot E e) = 0.
Proof.
  intros kn e HK H. destruct e as [| |op x y| | | | |]; try discriminate. destruct op; try discriminate.
  cbn [edenot]. rewrite u_and64.
  assert (K : forall z m, Z.ltb (m mod 2 ^ 64) (2 ^ ealign kn z) = true ->
            Z.land (bv_unsigned (edenot E z)) (bv_unsigned (Z_to_bv 64 m)) = 0).
  { intros z m Hm. apply Z.ltb_lt in Hm. destruct (ealign_sound segs E M kn z HK) as [Hj Hd]. rewrite u_lit64a.
    apply (land_al0 _ _ (ealign kn z)); [lia | exact Hd |]. split; [apply Z.mod_pos_bound; lia | exact Hm]. }
  destruct y as [m| | | | | | |];
    [ cbn [edenot]; destruct x; cbn [and0] in H; exact (K _ m H) | .. ];
    destruct x as [m| | | | | | |]; try discriminate; cbn [and0] in H; cbn [edenot]; rewrite Z.land_comm; exact (K _ m H).
Qed.
Lemma andal_refute_ok : forall kn c t a b, know_ok segs E M kn -> andal_refute kn c t a b = true ->
  branch_taken c (edenot E a) (edenot E b) <> t.
Proof.
  intros kn c t a b HK H Hb. pose proof (hrel_sound c t _ _ Hb) as HR. unfold andal_refute in H.
  destruct (hrel c t); cbn [rel_den] in HR; try discriminate.
  assert (L0 : forall e, lit0 e = true -> bv_unsigned (edenot E e) = 0).
  { intros e He. destruct e; try discriminate. cbn [lit0] in He. apply Z.eqb_eq in He. cbn [edenot]. rewrite u_lit64a. exact He. }
  destruct (and0 kn a) eqn:A.
  - apply HR. rewrite (and0_ok kn a HK A), (L0 b H). reflexivity.
  - destruct (and0 kn b) eqn:Bb; [|discriminate]. apply HR. rewrite (and0_ok kn b HK Bb), (L0 a H). reflexivity.
Qed.
Lemma slt_refute_ok : forall kn c t a b, know_ok segs E M kn -> slt_refute kn c t a b = true ->
  branch_taken c (edenot E a) (edenot E b) <> t.
Proof.
  intros kn c t a b HK H Hb. pose proof (hrel_sound c t _ _ Hb) as HR. unfold slt_refute in H.
  destruct (hrel c t); cbn [rel_den] in HR; try discriminate;
    destruct (SSLT.slt_dec kn a b) as [[|]|] eqn:D; try discriminate;
    pose proof (SSLT.slt_dec_sound segs E M kn a b _ HK D) as S.
  - apply Z.ltb_ge in S. lia.
  - apply Z.ltb_lt in S. lia.
Qed.

Lemma sc_fact_ok : forall kn e K l h, know_ok segs E M kn -> In K kn -> sc_fact e K = Some (l, h) -> l <= bv_unsigned (edenot E e) <= h.
Proof.
  intros kn e K l h HK Hin H. pose proof (proj1 (Forall_forall _ _) HK K Hin) as HK1.
  destruct K as [| | | | |f lo hi| | | |]; try discriminate. cbn [kentry_ok] in HK1. unfold sc_fact in H.
  destruct (scale_kL (lin_of e) (lin_of f)) as [k|] eqn:Hk; [|discriminate].
  assert (K1 : 1 <= k).
  { unfold scale_kL in Hk. destruct (snd (lin_of e)) as [|[c a] ?]; [discriminate|]. destruct (snd (lin_of f)) as [|[c' a'] ?]; [discriminate|].
    destruct (expr_eqb a a'); [|discriminate]. destruct (Z.eqb c' 0); [discriminate|].
    destruct (Z.eqb (c mod c') 0); [|discriminate]. destruct (Z.leb 1 (c / c')) eqn:C; [|discriminate].
    injection Hk as <-. apply Z.leb_le in C. exact C. }
  destruct (lin_eqbL (lin_of e) (lscale k (lin_of f))) eqn:Hl; [|discriminate].
  destruct (Z.leb 0 lo) eqn:C1; [|discriminate]. destruct (Z.ltb (k * hi) (2 ^ 64)) eqn:C2; [|discriminate].
  injection H as <- <-. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  assert (Hle : lin_of e = lscale k (lin_of f)).
  { unfold lin_eqbL in Hl. destruct (lin_of e) as [c1 t1], (lscale k (lin_of f)) as [c2 t2]. cbn [fst snd] in Hl.
    destruct (Z.eqb c1 c2) eqn:Hc; [|discriminate]. apply Z.eqb_eq in Hc. subst c2. apply SSR.terms_eqb_eq in Hl. subst t2. reflexivity. }
  pose proof (lin_of_sound E e) as L1. rewrite Hle in L1. pose proof (lscale_sound E k (lin_of f)) as L2.
  pose proof (lin_of_sound E f) as L3. unfold uE in *.
  assert (EQ : eqm (bv_unsigned (edenot E e)) (k * bv_unsigned (edenot E f))).
  { apply eqm_sym in L1. eapply eqm_trans; [exact L1|]. eapply eqm_trans; [exact L2|].
    destruct L3 as [q3 H3]. exists (k * q3)%Z. nia. }
  destruct EQ as [q Hq]. pose proof (bv_unsigned_in_range _ (edenot E e)) as Re. unfold bv_modulus in Re.
  change (2 ^ Z.of_N 64) with (2 ^ 64)%Z in Re.
  assert (q = 0)%Z by nia. subst q. nia.
Qed.

Lemma sc_range_ok : forall kn0 kn e l h, know_ok segs E M kn0 -> (forall K, In K kn -> In K kn0) ->
  sc_range e kn = Some (l, h) -> l <= bv_unsigned (edenot E e) <= h.
Proof.
  intros kn0 kn e l h HK Hsub. induction kn as [|K r IH]; intros H; [discriminate|]. cbn [sc_range] in H.
  destruct (sc_fact e K) as [[l0 h0]|] eqn:Hf.
  - injection H as <- <-. exact (sc_fact_ok kn0 e K l0 h0 HK (Hsub K (or_introl eq_refl)) Hf).
  - apply IH; [intros K' HK'; apply Hsub; right; exact HK' | exact H].
Qed.

Lemma al_round_ok : forall j l h x, 0 <= j -> (2 ^ j | x) -> l <= x <= h -> fst (al_round j l h) <= x <= snd (al_round j l h).
Proof.
  intros j l h x Hj [k Hk] Hx. unfold al_round. cbn [fst snd]. subst x.
  assert (P : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  split.
  - assert (- l / 2 ^ j >= - k) by (apply Z.le_ge, Z.div_le_lower_bound; lia). nia.
  - assert (h / 2 ^ j >= k) by (apply Z.le_ge, Z.div_le_lower_bound; lia). nia.
Qed.

Lemma urange_sound : forall kn e l h, know_ok segs E M kn -> urange kn e = Some (l, h) -> l <= bv_unsigned (edenot E e) <= h.
Proof.
  intros kn e l h HK H. unfold urange in H. destruct (erange kn e) as [[l0 h0]|] eqn:Er.
  - injection H as <- <-. exact (erange_sound segs E M kn e l0 h0 HK Er).
  - destruct (SSR.srange kn e) as [[l0 h0]|] eqn:Es.
    + destruct (al_round (ealign kn e) l0 h0) as [l' h'] eqn:Ha. destruct (Z.leb 0 l') eqn:C; [|discriminate].
      injection H as <- <-. apply Z.leb_le in C.
      pose proof (SSR.srange_sound segs E M kn e l0 h0 HK Es) as S.
      destruct (ealign_sound segs E M kn e HK) as [Hj Hd].
      assert (Hds : (2 ^ ealign kn e | bv_signed (edenot E e))).
      { destruct (SSR.s_eqm (edenot E e)) as [q Hq]. rewrite Hq. apply Z.divide_add_r; [exact Hd|].
        apply Z.divide_mul_r. exists (2 ^ (64 - ealign kn e)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      pose proof (al_round_ok (ealign kn e) l0 h0 _ ltac:(lia) Hds S) as R. rewrite Ha in R. cbn [fst snd] in R.
      rewrite SSR.s_u_nonneg by lia. exact R.
    + exact (sc_range_ok kn kn e l h HK (fun K HK' => HK') H).
Qed.

Lemma ult_refute_ok : forall kn c t a b, know_ok segs E M kn -> ult_refute kn c t a b = true ->
  branch_taken c (edenot E a) (edenot E b) <> t.
Proof.
  intros kn c t a b HK H Hb. pose proof (hrel_sound c t _ _ Hb) as HR. unfold ult_refute in H.
  destruct (hrel c t); cbn [rel_den] in HR; try discriminate;
    destruct (urange kn a) as [[la ha]|] eqn:Ra; try discriminate; destruct (urange kn b) as [[lb hb]|] eqn:Rb; try discriminate;
    pose proof (urange_sound kn a la ha HK Ra); pose proof (urange_sound kn b lb hb HK Rb).
  - apply Z.leb_le in H. lia.
  - apply Z.ltb_lt in H. lia.
Qed.

Lemma al_empty_ok : forall kn l, know_ok segs E M kn -> know_ok segs E M l -> al_empty kn l = false.
Proof.
  intros kn l HK Hl. induction Hl as [|K r HK1 _ IH]; [reflexivity|]. cbn [al_empty]. rewrite IH.
  destruct (al_empty1 kn K) eqn:H1; [|reflexivity]. exfalso. unfold al_empty1 in H1.
  destruct K as [ | | | | |e lo hi| | | | ]; try discriminate.
  all: try (destruct (Z.ltb 0 lo); [|discriminate]; destruct (Z.ltb (hi - lo) 4096); [|discriminate]).
  all: try discriminate.
  destruct (al_round (ealign kn e) lo hi) as [l' h'] eqn:Ha. apply Z.ltb_lt in H1.
  destruct (ealign_sound segs E M kn e HK) as [Hj Hd]. cbn [kentry_ok] in HK1.
  pose proof (al_round_ok (ealign kn e) lo hi _ ltac:(lia) Hd HK1) as R. rewrite Ha in R. cbn [fst snd] in R. lia.
Qed.

Lemma al_tight_ok : forall kn l, know_ok segs E M kn -> know_ok segs E M l ->
  (forall l', al_tight kn l = Some l' -> know_ok segs E M l') /\ al_tight kn l <> None.
Proof.
  intros kn l HK Hl. induction Hl as [|K r HK1 _ IH]; [split; [intros l' H; injection H as <-; constructor | discriminate]|].
  cbn [al_tight]. destruct IH as [IH1 IH2].
  assert (A : (forall x, al_tight1 kn K = Some x -> know_ok segs E M x) /\ al_tight1 kn K <> None).
  { unfold al_tight1. destruct K as [ | | | | |e lo hi| | | | ];
      try (split; [intros x H; injection H as <-; constructor | discriminate]).
    destruct (Z.eqb (ealign kn e) 0); [split; [intros x H; injection H as <-; constructor | discriminate]|].
    destruct (al_round (ealign kn e) lo hi) as [l' h'] eqn:Ha.
    destruct (ealign_sound segs E M kn e HK) as [Hj Hd]. cbn [kentry_ok] in HK1.
    pose proof (al_round_ok (ealign kn e) lo hi _ ltac:(lia) Hd HK1) as R. rewrite Ha in R. cbn [fst snd] in R.
    destruct (Z.ltb h' l') eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|].
    destruct (if Z.eqb l' lo then Z.eqb h' hi else false);
      [split; [intros x H; injection H as <-; constructor | discriminate]|].
    split; [intros x H; injection H as <-; constructor; [cbn [kentry_ok]; lia | constructor] | discriminate]. }
  destruct A as [A1 A2]. destruct (al_tight1 kn K) as [x|]; [|exfalso; exact (A2 eq_refl)].
  destruct (al_tight kn r) as [y|]; [|exfalso; exact (IH2 eq_refl)].
  split; [intros l' H; injection H as <-; apply Forall_app; split; [exact (A1 x eq_refl) | exact (IH1 y eq_refl)] | discriminate].
Qed.

Lemma aff_fact_ok : forall kn K, know_ok segs E M kn -> kentry_ok segs E M K -> know_ok segs E M (aff_fact kn K).
Proof.
  intros kn K HK HK1. unfold aff_fact. destruct K as [ | | | | |e lo hi| | | | ]; try constructor.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  destruct (lin_of e) as [c ts] eqn:HL. cbn [fst snd] in Hq.
  destruct ts as [|[k v] [|t ts']]; try constructor.
  cbn [tden] in Hq. unfold uE in Hq.
  destruct (Z.leb 1 k) eqn:Hk; [|constructor]. apply Z.leb_le in Hk.
  pose proof (rng0_sound kn v HK) as Rv. destruct (rng0 kn v) as [vl vh] eqn:Er. cbn [fst snd] in Rv.
  destruct (if Z.leb 0 (c + k * vl) then Z.ltb (c + k * vh) (2^64) else false) eqn:Hnw; [|constructor].
  destruct (Z.leb 0 (c + k * vl)) eqn:H1; [|discriminate]. apply Z.leb_le in H1. apply Z.ltb_lt in Hnw.
  cbn [kentry_ok] in HK1.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as RE. unfold bv_modulus in RE. cbn in RE.
  set (uv := bv_unsigned (edenot E v)) in *.
  assert (B : 0 <= c + k * uv < 2^64).
  { assert (k * vl <= k * uv <= k * vh) by (split; apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (Hq0 : q = 0) by nia. subst q.
  assert (HA : bv_unsigned (edenot E e) = c + k * uv) by lia.
  constructor; [|constructor]. cbn [kentry_ok]. fold uv. split.
  - apply Z.max_lub; [lia|].
    assert (k * uv >= lo - c) by lia.
    assert (- ((c - lo) / k) <= uv); [|lia].
    assert (Hd : (c - lo) / k >= - uv); [|lia].
    apply Z.le_ge. apply Z.div_le_lower_bound; lia.
  - apply Z.min_glb; [lia|]. apply Z.div_le_lower_bound; lia.
Qed.

Lemma aff_facts_ok : forall kn, know_ok segs E M kn -> know_ok segs E M (aff_facts kn).
Proof.
  intros kn HK. unfold aff_facts. apply Forall_forall. intros K HKin. apply in_flat_map in HKin as (K0 & Hin0 & HK0).
  exact (proj1 (Forall_forall _ _) (aff_fact_ok kn K0 HK (proj1 (Forall_forall _ _) HK K0 Hin0)) K HK0).
Qed.

Theorem learn_none : forall kn c t a b,
  know_ok segs E M kn -> learn kn c t a b = None -> branch_taken c (edenot E a) (edenot E b) <> t.
Proof.
  intros kn c t a b HK Hl Hb. unfold learn in Hl.
  destruct (andal_refute kn c t a b) eqn:Ha; [exact (andal_refute_ok kn c t a b HK Ha Hb)|].
  destruct (slt_refute kn c t a b) eqn:Hr; [exact (slt_refute_ok kn c t a b HK Hr Hb)|].
  destruct (ult_refute kn c t a b) eqn:Hu; [exact (ult_refute_ok kn c t a b HK Hu Hb)|].
  destruct (learn0 kn c t a b) as [l0|] eqn:H0; [|exact (learn0_none kn c t a b HK H0 Hb)].
  pose proof (learn0_sound kn c t a b l0 HK Hb H0) as K0.
  destruct (ocat (tighten kn l0) (Some l0)) as [l1|] eqn:Ho.
  - assert (K1 : know_ok segs E M l1)
      by (eapply ocat_sound; [exact Ho | exact (proj1 (tighten_ok kn l0 HK K0)) | intros lx Hx; injection Hx as <-; exact K0]).
    rewrite (al_empty_ok kn l1 HK K1) in Hl. discriminate.
  - apply ocat_none in Ho as [Ho|Ho]; [exact (proj2 (tighten_ok kn l0 HK K0) Ho) | discriminate].
Qed.

(* [comment removed for export] *)
Lemma sub_fact1_ok : forall kn n v K, know_ok segs E M kn -> kentry_ok segs E M K -> bv_unsigned (edenot E (EVar n)) = v ->
  match sub_fact1 kn n v K with Some d => know_ok segs E M d | None => False end.
Proof.
  intros kn n v K HK HK1 Hv. unfold sub_fact1. destruct K as [ | | | | |e lo hi| | | | ]; try constructor.
  set (e2 := esubst (EVar n) (ELit v) e).
  assert (He2 : edenot E e2 = edenot E e).
  { unfold e2. apply esubst_sound. rewrite edenot_lit, <- Hv. apply Z_to_bv_bv_unsigned. }
  destruct (expr_eqb e2 e); [constructor|].
  destruct (Z.leb 0 lo && Z.ltb hi (2 ^ 64))%bool eqn:Hlh; [|constructor].
  apply andb_prop in Hlh as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  cbn [kentry_ok] in HK1. rewrite <- He2 in HK1.
  pose proof (bv_unsigned_in_range 64 (edenot E e2)) as RE. unfold bv_modulus in RE. cbn in RE.
  pose proof (lin_of_sound E e2) as [q Hq]. unfold lden, uE in Hq.
  destruct (lin_of e2) as [c ts] eqn:HL. cbn [fst snd] in Hq.
  set (u := bv_unsigned (edenot E e2)) in *.
  destruct ts as [|[k x] [|t ts']].
  - cbn [tden] in Hq.
    assert (Hc : c mod 2 ^ 64 = u).
    { symmetry. apply Z.mod_unique with q; [left; lia | lia]. }
    rewrite Hc. destruct (Z.leb lo u && Z.leb u hi)%bool eqn:C; [constructor|].
    apply andb_false_iff in C as [C|C]; apply Z.leb_gt in C; lia.
  - cbn [tden] in Hq. unfold uE in Hq.
    destruct (Z.eqb k 0) eqn:Hk0; [constructor|]. apply Z.eqb_neq in Hk0.
    pose proof (rng0_sound kn x HK) as Rv. destruct (rng0 kn x) as [vl vh] eqn:Er. cbn [fst snd] in Rv.
    set (ux := bv_unsigned (edenot E x)) in *.
    assert (T : (if Z.ltb 0 k then c + k * vl else c + k * vh) <= c + k * ux <= (if Z.ltb 0 k then c + k * vh else c + k * vl)).
    { destruct (Z.ltb 0 k) eqn:Hk.
      - apply Z.ltb_lt in Hk. assert (k * vl <= k * ux <= k * vh) by (split; apply Z.mul_le_mono_nonneg_l; lia). lia.
      - apply Z.ltb_ge in Hk. assert (k * vh <= k * ux <= k * vl) by (split; apply Z.mul_le_mono_nonpos_l; lia). lia. }
    destruct (Z.ltb (hi - 2 ^ 64) (if Z.ltb 0 k then c + k * vl else c + k * vh) &&
              Z.ltb (if Z.ltb 0 k then c + k * vh else c + k * vl) (lo + 2 ^ 64))%bool eqn:C; [|constructor].
    apply andb_prop in C as [C1 C2]. apply Z.ltb_lt in C1, C2.
    assert (Hq0 : q = 0) by nia. subst q.
    assert (Ht : lo <= c + k * ux <= hi) by lia.
    assert (B : (if Z.ltb 0 k then - ((c - lo) / k) else - ((hi - c) / (- k))) <= ux <=
                (if Z.ltb 0 k then (hi - c) / k else (c - lo) / (- k))).
    { destruct (Z.ltb 0 k) eqn:Hk.
      - apply Z.ltb_lt in Hk. split.
        + assert (Hd : (c - lo) / k >= - ux); [|lia]. apply Z.le_ge. apply Z.div_le_lower_bound; lia.
        + apply Z.div_le_lower_bound; lia.
      - apply Z.ltb_ge in Hk. split.
        + assert (Hd : (hi - c) / (- k) >= - ux); [|lia]. apply Z.le_ge. apply Z.div_le_lower_bound; lia.
        + apply Z.div_le_lower_bound; lia. }
    destruct (Z.ltb (Z.min vh (if Z.ltb 0 k then (hi - c) / k else (c - lo) / (- k)))
                    (Z.max vl (if Z.ltb 0 k then - ((c - lo) / k) else - ((hi - c) / (- k))))) eqn:C3.
    + apply Z.ltb_lt in C3. lia.
    + constructor; [|constructor]. cbn [kentry_ok]. fold ux. lia.
  - destruct (Z.leb 0 (lo - c) && Z.ltb (hi - c) (2 ^ 64))%bool eqn:C; [|constructor].
    apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    pose proof (unlin_sound E (0, (k, x) :: t :: ts')) as [q2 Hq2]. unfold lden, uE in Hq2. cbn [fst snd] in Hq2.
    set (w := bv_unsigned (edenot E (unlin (0, (k, x) :: t :: ts')))) in *.
    assert (RU : 0 <= w < 2 ^ 64).
    { unfold w. pose proof (bv_unsigned_in_range 64 (edenot E (unlin (0, (k, x) :: t :: ts')))) as R0. unfold bv_modulus in R0. exact R0. }
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    assert (Hw : w = u - c) by lia.
    constructor; [|constructor]. cbn [kentry_ok]. fold w. lia.
Qed.

Lemma sub_pass_ok : forall n v kn0 l acc, know_ok segs E M kn0 -> know_ok segs E M l -> know_ok segs E M acc ->
  bv_unsigned (edenot E (EVar n)) = v ->
  match sub_pass kn0 n v l acc with Some d => know_ok segs E M d | None => False end.
Proof.
  intros n v kn0 l. induction l as [|K r IH]; intros acc H0 Hl Ha Hv; cbn [sub_pass]; [exact Ha|].
  inversion Hl as [|? ? HK1 Hr].
  pose proof (sub_fact1_ok (acc ++ kn0) n v K (proj2 (Forall_app _ _ _) (conj Ha H0)) HK1 Hv) as Hs.
  destruct (sub_fact1 (acc ++ kn0) n v K) as [d|]; [|exact Hs].
  apply IH; [exact H0 | exact Hr | apply Forall_app; split; [exact Hs | exact Ha] | exact Hv].
Qed.

Lemma sub_facts_ok : forall kn n v, know_ok segs E M kn -> bv_unsigned (edenot E (EVar n)) = v ->
  match sub_facts kn n v with Some d => know_ok segs E M d | None => False end.
Proof.
  intros kn n v HK Hv. unfold sub_facts.
  pose proof (sub_pass_ok n v kn kn [] HK HK (Forall_nil _) Hv) as H1.
  destruct (sub_pass kn n v kn []) as [d1|]; [|exact H1].
  assert (HK2 : know_ok segs E M (d1 ++ kn)) by (apply Forall_app; split; assumption).
  pose proof (sub_pass_ok n v (d1 ++ kn) kn [] HK2 HK (Forall_nil _) Hv) as H2.
  destruct (sub_pass (d1 ++ kn) n v kn []) as [d2|]; [|exact H2].
  apply Forall_app; split; assumption.
Qed.

End Sound.

End SL.
