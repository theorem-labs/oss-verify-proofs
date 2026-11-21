(* SPDX-License-Identifier: MIT *)
(* Remaking the main entry's recorded facts from the computed hand-off state (LPS 727298f3).  By a fixed rule
   computed in the build, each recorded fact (MainFactsAsan/Both, in the recorded numbering) that the computed
   state no longer justifies after renumbering by [mapf bps] is replaced:
   - a fact on the auxv vector (its address on the auxv base [e_auxb]) is not recorded data at LPS 727298f3:
     the launch lays the vector out and the start state's own auxv claims describe it, carried through the
     hand-offs.  Such a fact is replaced IN PLACE by the image-range fact of the state (so no later index
     moves), and the state's facts on the auxv base are appended at the end of the list: its words as
     read-only cells, and its readable range as a readable fact ([MRd], on the state's [KUnk] there, at
     the same literal length);
   - any other fact is replaced by the state's single fact of the same kind at the same address (or, when
     there is none there, on the same base expression), written back in the recorded numbering by the inverse
     map; no single candidate: the fact is dropped from the remade list (the kept lists the main-phase proofs
     read then hold a trivially true fact in its place, [kept_m] / [kept_p] of AS/MainEntry.v, so a proof that
     needs it fails at its own membership or index check).
   Nothing here is trusted: the main entry's bridge re-checks every resulting fact against the computed state
   ([mjustify] / [pjustify] after renumbering). *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan PlanRegen MainExport MainRenum.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* the inverse of [mapf bps] on its image *)
Fixpoint unmap_from (po pn : nat) (bps : list (nat * nat)) (w : nat) : option nat :=
  match bps with
  | [] => if Nat.leb pn w then Some (w - pn + po)%nat else None
  | (o, n) :: rest =>
      if (Nat.leb pn w && Nat.ltb w (pn + (o - po)))%bool then Some (w - pn + po)%nat
      else unmap_from o n rest w
  end.
Definition unmapf (bps : list (nat * nat)) (w : nat) : option nat := unmap_from 0 0 bps w.

Section Back.
  Variable g : nat -> option nat.
  Fixpoint zunsh (e : zexp) : option zexp :=
    match e with
    | ZLit z => Some (ZLit z)
    | ZV n => match g n with Some m => Some (ZV m) | None => None end
    | ZAdd a b => match zunsh a, zunsh b with Some x, Some y => Some (ZAdd x y) | _, _ => None end
    | ZMul a b => match zunsh a, zunsh b with Some x, Some y => Some (ZMul x y) | _, _ => None end
    | ZAnd a b => match zunsh a, zunsh b with Some x, Some y => Some (ZAnd x y) | _, _ => None end
    | ZLtu a b => match zunsh a, zunsh b with Some x, Some y => Some (ZLtu x y) | _, _ => None end
    end.
  Definition zof (e : expr) : option zexp := match zexp_of e with Some z => zunsh z | None => None end.
  Definition saz (sa : saddr) : option zexp :=
    match zexp_of (a_base sa) with Some bz => zunsh (mkaddr bz (a_off sa)) | None => None end.
  Definition litz (e : expr) : option Z := match e with ELit z => Some z | _ => None end.

  (* the state's fact [K] as a fact of the recorded fact [f]'s kind, in the recorded numbering *)
  Definition remake1 (f : mfact) (K : kentry) : option mfact :=
    match f, K with
    | MCell _ w _, KWord sa w' e =>
        if Nat.eqb w w' then match saz sa, zof e with Some a, Some v => Some (MCell a w v) | _, _ => None end else None
    | MRo _ w _, KWord sa w' e =>
        if Nat.eqb w w' then match saz sa, zof e with Some a, Some v => Some (MRo a w v) | _, _ => None end else None
    | MZeroC _ _, KZero sa ne => match saz sa, litz ne with Some a, Some n => Some (MZeroC a n) | _, _ => None end
    | MZero _ _, KZero sa ne => match saz sa, litz ne with Some a, Some n => Some (MZero a n) | _, _ => None end
    | MFill _ _ _, KFill sa ne c => match saz sa, litz ne with Some a, Some n => Some (MFill a n c) | _, _ => None end
    | MWr _ _, KWr sa ne => match saz sa, litz ne with Some a, Some n => Some (MWr a n) | _, _ => None end
    | MZeroS _ _, KZero sa ne => match saz sa, zof ne with Some a, Some n => Some (MZeroS a n) | _, _ => None end
    | MWrS _ _, KWr sa ne => match saz sa, zof ne with Some a, Some n => Some (MWrS a n) | _, _ => None end
    | MRd _ _, KUnk sa ne => match saz sa, litz ne with Some a, Some n => Some (MRd a n) | _, _ => None end
    | MImg _ _, KImg lo hi => Some (MImg lo hi)
    | _, _ => None
    end.

  Definition premake1 (f : pfact) (K : kentry) : option pfact :=
    match f, K with
    | PVar _ _ _, KRange (EVar n) lo hi => match g n with Some m => Some (PVar m lo hi) | None => None end
    | PRange _ _ _, KRange e lo hi => match zof e with Some z => Some (PRange z lo hi) | None => None end
    | PDisj _ _ _ _, KDisj sa1 ne1 sa2 ne2 =>
        match saz sa1, litz ne1, saz sa2, litz ne2 with Some a1, Some n1, Some a2, Some n2 => Some (PDisj a1 n1 a2 n2) | _, _, _, _ => None end
    | PDisjS _ _ _ _, KDisj sa1 ne1 sa2 ne2 =>
        match saz sa1, zof ne1, saz sa2, zof ne2 with Some a1, Some n1, Some a2, Some n2 => Some (PDisjS a1 n1 a2 n2) | _, _, _, _ => None end
    | _, _ => None
    end.
End Back.

Definition maddr (f : mfact) : option zexp :=
  match f with
  | MCell a _ _ | MZeroC a _ | MRo a _ _ | MZero a _ | MFill a _ _ | MWr a _ | MZeroS a _ | MWrS a _ | MRd a _ => Some a
  | MImg _ _ => None end.
Definition kaddr (K : kentry) : option saddr :=
  match K with KWord sa _ _ | KZero sa _ | KBlob sa _ _ | KWr sa _ | KFill sa _ _ | KUnk sa _ => Some sa | _ => None end.
Definition zbase (a : zexp) : option zexp := match a with ZAdd b (ZLit _) => Some b | ZLit _ => None | _ => Some a end.
Definition base_match (a : zexp) (sa : saddr) : bool :=
  match zbase a, zexp_of (a_base sa) with Some b, Some bz => zexp_eqb b bz | _, _ => false end.

(* the auxv vector's base expression (AsanPlanCore.e_auxb), the same in both numberings (launch variables) *)
Definition AUXB : option zexp := zexp_of (fst e_auxb).
Definition on_auxv (a : zexp) : bool :=
  match zbase a, AUXB with Some b, Some ab => zexp_eqb b ab | _, _ => false end.

Section Remake.
  Variable k : list kentry.
  Variables HLO HHI : Z.
  Variable bps : list (nat * nat).
  Let f := mapf bps.
  Let VR := var_ranges k.
  Let g := unmapf bps.

  (* the state's image-range fact: the in-place stand-in for a dropped auxv fact *)
  Definition img_fact : option mfact :=
    match find (fun K => match K with KImg lo hi => ((HLO <=? lo) && (hi <=? HHI))%bool | _ => false end) k with
    | Some (KImg lo hi) => Some (MImg lo hi) | _ => None end.
  (* the state's facts on the auxv base: its words as read-only cells, its readable range ([KUnk], a literal
     length) as a readable fact *)
  Definition auxv_facts : list mfact :=
    flat_map (fun K => match K with
                       | KWord sa w e =>
                           match saz g sa, zof g e with
                           | Some a, Some v => if on_auxv a then [MRo a w v] else []
                           | _, _ => [] end
                       | KUnk sa ne =>
                           match saz g sa, litz ne with
                           | Some a, Some n => if on_auxv a then [MRd a n] else []
                           | _, _ => [] end
                       | _ => [] end) k.

  Definition cands (F : mfact) : list mfact :=
    let pick l := flat_map (fun K => match remake1 g F K with Some G => [G] | None => [] end) l in
    match maddr F with
    | Some a =>
        let a' := zsh f a in
        match pick (filter (fun K => match kaddr K with Some sa => addr_match VR sa a' | None => false end) k) with
        | [] => pick (filter (fun K => match kaddr K with Some sa => base_match a' sa | None => false end) k)
        | l => l end
    | None => pick (filter (fun K => match K with KImg _ _ => true | _ => false end) k)
    end.
  Definition remake_fact (F : mfact) : option mfact :=
    if mjustify k VR HLO HHI (msh f F) then Some F
    else match maddr F with
         | Some a => if on_auxv a then img_fact else match cands F with [G] => Some G | _ => None end
         | None => match cands F with [G] => Some G | _ => None end
         end.
  (* a fact the rule cannot remake is dropped *)
  Fixpoint remake_list (l : list mfact) : list mfact :=
    match l with
    | [] => []
    | F :: r => match remake_fact F with Some G => G :: remake_list r | None => remake_list r end
    end.
  Definition remake_facts (l : list mfact) : list mfact := remake_list l ++ auxv_facts.

  Definition pcands (F : pfact) : list pfact :=
    let pick l := flat_map (fun K => match premake1 g F K with Some G => [G] | None => [] end) l in
    match F with
    | PVar n _ _ => pick (filter (fun K => match K with KRange (EVar n') _ _ => Nat.eqb (f n) n' | _ => false end) k)
    | PRange e _ _ => pick (filter (fun K => match K with KRange e' _ _ => val_match e' (zsh f e) | _ => false end) k)
    | PDisj a1 _ a2 _ | PDisjS a1 _ a2 _ =>
        pick (filter (fun K => match K with
                               | KDisj sa1 _ sa2 _ => (addr_match VR sa1 (zsh f a1) && addr_match VR sa2 (zsh f a2))%bool
                               | _ => false end) k)
    end.
  Definition remake_pfact (F : pfact) : option pfact :=
    if pjustify k VR (pfsh f F) then Some F else match pcands F with [G] => Some G | _ => None end.
  Fixpoint remake_pfacts (l : list pfact) : list pfact :=
    match l with
    | [] => []
    | F :: r => match remake_pfact F with Some G => G :: remake_pfacts r | None => remake_pfacts r end
    end.
End Remake.
