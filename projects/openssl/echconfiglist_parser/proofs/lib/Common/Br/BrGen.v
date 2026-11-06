(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxImage FxHandoff FxHoBuild FxHandoff2.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanPlan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv BrRev BrClass BrRevS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition odflt {T : Type} (d : T) (o : option T) : T := match o with Some x => x | None => d end.

(* [comment removed for export] *)
Definition sym_terms (v : AX2.expr) : list (Z * AX2.expr) := snd (elin [] v).

Definition has_tag (TT : ttab_e) (ts : list (Z * AX2.expr)) : bool :=
  match find_tag [] (xt_of TT) ts with Some _ => true | None => false end.

Definition gen_tt_step (acc : ttab_e * int) (K : AX2.kentry) : ttab_e * int :=
  match K with
  | AX2.KWord _ _ v =>
      let ts := sym_terms v in
      match ts with
      | [] => acc
      | _ => if has_tag (fst acc) ts then acc
             else (fst acc ++ [(snd acc, AX2.unlin (0, ts))], (snd acc + 1)%uint63)
      end
  | _ => acc
  end.

Definition gen_tt (TT0 : ttab_e) (first : int) (kn : list AX2.kentry) : ttab_e :=
  fst (fold_left gen_tt_step kn (TT0, first)).

(* [comment removed for export] *)
Definition gen_vt (nx : nat) (regs' : list AX2.expr) (F' : fstate) : vtab :=
  flat_map (fun i => match nth i regs' (AX2.ELit 0) with
                     | AX2.EVar x => if Nat.leb nx x then [(x, VVal (FxState.rget F' (of_Z (Z.of_nat i))))] else []
                     | _ => []
                     end) (seq 1 31).

(* [comment removed for export] *)
Definition gen_regions_step (acc : ttab_e * list rshape * int) (m : APC.amap) : ttab_e * list rshape * int :=
  let '(tab, shs, t) := acc in
  match APC.am_base m, APC.am_len m with
  | AX2.ELit _, _ => acc
  | b, AX2.ELit l =>
      if (0 <? l) && (l <? 2 ^ 62) && negb (has_tag tab (sym_terms b))
      then (tab ++ [(t, b)], shs ++ [(t, 0%uint63, of_Z l, 12%uint63, None)], (t + 1)%uint63)
      else acc
  | _, _ => acc
  end.

Definition gen_regions (TT0 : ttab_e) (shapes0 : list rshape) (first : int) (maps : list APC.amap)
  : ttab_e * list rshape :=
  fst (fold_left gen_regions_step maps (TT0, shapes0, first)).

(* [comment removed for export] *)
Definition gen_regions2_step (acc : ttab_e * list rshape * list (int * rclass) * int * nat) (m : APC.amap)
  : ttab_e * list rshape * list (int * rclass) * int * nat :=
  let '(tab, shs, cl, t, i) := acc in
  match APC.am_base m, APC.am_len m with
  | AX2.ELit _, _ => (tab, shs, cl, t, S i)
  | b, AX2.ELit l =>
      if (0 <? l) && (l <? 2 ^ 62) && negb (has_tag tab (sym_terms b))
      then (tab ++ [(t, b)], shs ++ [(t, 0%uint63, of_Z l, 12%uint63, None)], cl ++ [(t, RCEnt i)], (t + 1)%uint63, S i)
      else (tab, shs, cl, t, S i)
  | _, _ => (tab, shs, cl, t, S i)
  end.

Definition gen_regions2 (TT0 : ttab_e) (shapes0 : list rshape) (classes0 : list (int * rclass)) (first : int)
    (maps : list APC.amap) : ttab_e * list rshape * list (int * rclass) :=
  let '(tab, shs, cl, _, _) := fold_left gen_regions2_step maps (TT0, shapes0, classes0, first, O) in (tab, shs, cl).

(* [comment removed for export] *)
Fixpoint lit_class_from (i : nat) (maps : list APC.amap) (lo hi : Z) : option rclass :=
  match maps with
  | [] => None
  | m :: rest =>
      match APC.am_base m, APC.am_len m with
      | AX2.ELit b, AX2.ELit l => if (b <=? lo) && (hi <=? b + l) then Some (RCEnt i) else lit_class_from (S i) rest lo hi
      | _, _ => lit_class_from (S i) rest lo hi
      end
  end.
Definition lit_class (maps : list APC.amap) (lo hi : Z) : option rclass := lit_class_from O maps lo hi.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hfact_tag (f : hfact) : option int :=
  match f with
  | HCell t _ _ _ | HVal t _ _ | HBytes t _ _ _ | HZero t _ _ | HWr t _ _ | HRegion t _ _ _ => Some t
  | HClear _ _ => Some 0%uint63
  | _ => None end.
Definition hfact_rng (f : hfact) : option (int * int) :=
  match f with
  | HCell _ o n _ | HBytes _ o n _ | HZero _ o n | HWr _ o n => Some (o, (o + n)%uint63)
  | HVal _ o _ => Some (o, (o + 8)%uint63)
  | HClear lo hi => Some (lo, hi)
  | _ => None end.
Definition hfacts_of_tag (F : list hfact) (t : int) : list hfact :=
  filter (fun f => match hfact_tag f with Some t' => (t' =? t)%uint63 | None => false end) F.
Definition hfacts_of_page (F0 : list hfact) (pn : int) : list hfact :=
  filter (fun f => match hfact_rng f with
                   | Some (lo, hi) => (lo <? (pn << 12) + 4096)%uint63 && ((pn << 12) <? hi)%uint63
                   | None => false end) F0.
Definition region_fast (IM : fimage) (F : list hfact) (shape : int * int * int * int * option pkind) : rdesc :=
  let '(t, lo, len, al, dflt) := shape in
  let Ft := hfacts_of_tag F t in
  if (t =? 0)%uint63 then
    RD t lo len al dflt (map (fun pn => page_desc IM Ft 0%uint63 pn (image_page_cells IM (hfacts_of_page Ft pn) pn)) (image_pages IM Ft))
  else region_desc2 IM Ft shape.     (* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint fill_from (t : int) (o : Z) (k : nat) (w : w64) : list hfact :=
  match k with O => [] | S k' => HCell t (of_Z o) 8%uint63 w :: fill_from t (o + 8) k' w end.
Definition fill_pieces (lim : Z) (FC : list (int * Z * Z * Z)) : list hfact :=
  flat_map (fun q : int * Z * Z * Z => let '(t, o, l, c) := q in
     if (0 <? l) && (l <=? lim) then
       fill_from t o (Z.to_nat (l / 8)) (fillw c)
       ++ (if l mod 8 =? 0 then [] else [HCell t (of_Z (o + l / 8 * 8)) (of_Z (l mod 8)) (fillw c)])
     else []) FC.

Definition ho_build_fast (IM : fimage) (F : list hfact) (pc : int) (shapes : list (int * int * int * int * option pkind)) : sdesc :=
  SD pc (regs_desc F) (map (region_fast IM F) shapes).
