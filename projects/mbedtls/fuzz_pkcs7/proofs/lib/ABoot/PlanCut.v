(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
(* [comment removed for export] *)
Fixpoint psize (p : plan) : nat :=
  match p with
  | PRun _ k | PShDisj _ _ _ _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k | PBump _ k
  | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k | PEmit _ _ k | PFog _ _ k | PFogNew _ _ k
  | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k => S (psize k)
  | PSplit _ _ a b | PCase2 _ _ a b | PCaseDisj _ _ a b | PMmap a b | PMprotect a b | PBrk2 a b | PExt2 _ _ a b
  | PLoop _ _ _ a b | PVia _ _ _ a b => S (psize a + psize b)
  | PMmapIn a b c | PMmapInH a b c => S (psize a + psize b + psize c)
  | _ => 1%nat
  end.

Fixpoint psubs (d : nat) (p : plan) {struct p} : list plan :=
  match d with O => [p] | S d' =>
  match p with
  | PRun _ k | PShDisj _ _ _ _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k | PBump _ k
  | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k | PEmit _ _ k | PFog _ _ k | PFogNew _ _ k
  | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k => psubs d' k
  | PSplit _ _ a b | PCase2 _ _ a b | PCaseDisj _ _ a b | PMmap a b | PMprotect a b | PBrk2 a b | PExt2 _ _ a b
  | PLoop _ _ _ a b | PVia _ _ _ a b => psubs d' a ++ psubs d' b
  | PMmapIn a b c | PMmapInH a b c => psubs d' a ++ psubs d' b ++ psubs d' c
  | _ => []
  end end.

Fixpoint pcut (d : nat) (p : plan) (n : nat) {struct p} : plan * nat :=
  match d with O => (PHandoff (1000 + n)%nat, S n) | S d' =>
  match p with
  | PRun s k => let '(k', n') := pcut d' k n in (PRun s k', n')
  | PSplit e m k1 k2 => let '(a, n1) := pcut d' k1 n in let '(b, n2) := pcut d' k2 n1 in (PSplit e m a b, n2)
  | PCase2 e m k1 k2 => let '(a, n1) := pcut d' k1 n in let '(b, n2) := pcut d' k2 n1 in (PCase2 e m a b, n2)
  | PCaseDisj b1 b2 k1 k2 => let '(a, n1) := pcut d' k1 n in let '(b, n2) := pcut d' k2 n1 in (PCaseDisj b1 b2 a b, n2)
  | PShDisj b1 n1 b2 n2 k => let '(k', n') := pcut d' k n in (PShDisj b1 n1 b2 n2 k', n')
  | PFact K k => let '(k', n') := pcut d' k n in (PFact K k', n')
  | PJoin b o m k => let '(k', n') := pcut d' k n in (PJoin b o m k', n')
  | PForget l k => let '(k', n') := pcut d' k n in (PForget l k', n')
  | PDropRange b m k => let '(k', n') := pcut d' k n in (PDropRange b m k', n')
  | PGcKeep w k => let '(k', n') := pcut d' k n in (PGcKeep w k', n')
  | PBump m k => let '(k', n') := pcut d' k n in (PBump m k', n')
  | PHavoc rs k => let '(k', n') := pcut d' k n in (PHavoc rs k', n')
  | PHavocBig m k => let '(k', n') := pcut d' k n in (PHavocBig m k', n')
  | PFresh r l b k => let '(k', n') := pcut d' k n in (PFresh r l b k', n')
  | PSys y k => let '(k', n') := pcut d' k n in (PSys y k', n')
  | PMmap a b => let '(a', n1) := pcut d' a n in let '(b', n2) := pcut d' b n1 in (PMmap a' b', n2)
  | PMmapIn a b c => let '(a', n1) := pcut d' a n in let '(b', n2) := pcut d' b n1 in let '(c', n3) := pcut d' c n2 in (PMmapIn a' b' c', n3)
  | PMmapInH a b c => let '(a', n1) := pcut d' a n in let '(b', n2) := pcut d' b n1 in let '(c', n3) := pcut d' c n2 in (PMmapInH a' b' c', n3)
  | PMprotect a b => let '(a', n1) := pcut d' a n in let '(b', n2) := pcut d' b n1 in (PMprotect a' b', n2)
  | PBrk2 a b => let '(a', n1) := pcut d' a n in let '(b', n2) := pcut d' b n1 in (PBrk2 a' b', n2)
  | PX x args k => let '(k', n') := pcut d' k n in (PX x args k', n')
  | PExt i a k => let '(k', n') := pcut d' k n in (PExt i a k', n')
  | PEmit i a k => let '(k', n') := pcut d' k n in (PEmit i a k', n')
  | PExt2 i a k1 k2 => let '(x, n1) := pcut d' k1 n in let '(y, n2) := pcut d' k2 n1 in (PExt2 i a x y, n2)
  | PLoop j m inv b k => let '(b', n1) := pcut d' b n in let '(k', n2) := pcut d' k n1 in (PLoop j m inv b' k', n2)
  | PFog i s k => let '(k', n') := pcut d' k n in (PFog i s k', n')
  | PFogNew i s k => let '(k', n') := pcut d' k n in (PFogNew i s k', n')
  | PGhost b m k => let '(k', n') := pcut d' k n in (PGhost b m k', n')
  | PUnvis b m k => let '(k', n') := pcut d' k n in (PUnvis b m k', n')
  | PHavocBrk l h k => let '(k', n') := pcut d' k n in (PHavocBrk l h k', n')
  | PIntro l h k => let '(k', n') := pcut d' k n in (PIntro l h k', n')
  | PDiamond j rs k => let '(k', n') := pcut d' k n in (PDiamond j rs k', n')
  | PRename m k => let '(k', n') := pcut d' k n in (PRename m k', n')
  | PCompact k => let '(k', n') := pcut d' k n in (PCompact k', n')
  | PVia j js lo ka k => let '(x, n1) := pcut d' ka n in let '(y, n2) := pcut d' k n1 in (PVia j js lo x y, n2)
  | PAbstractCell b m k => let '(k', n') := pcut d' k n in (PAbstractCell b m k', n')
  | PHavocWords bs k => let '(k', n') := pcut d' k n in (PHavocWords bs k', n')
  | PRespell r e k => let '(k', n') := pcut d' k n in (PRespell r e k', n')
  | other => (other, n)
  end end.

Fixpoint pcutS (thr : nat) (d : nat) (p : plan) (n : nat) {struct p} : plan * nat :=
  match d with O => (if Nat.leb thr (psize p) then (PHandoff (1000 + n)%nat, S n) else (p, n)) | S d' =>
  match p with
  | PRun s k => let '(k', n') := pcutS thr d' k n in (PRun s k', n')
  | PSplit e m k1 k2 => let '(a, n1) := pcutS thr d' k1 n in let '(b, n2) := pcutS thr d' k2 n1 in (PSplit e m a b, n2)
  | PCase2 e mm k1 k2 => let '(a, n1) := pcutS thr d' k1 n in let '(b, n2) := pcutS thr d' k2 n in (PCase2 e mm a b, Nat.max n1 n2)
  | PCaseDisj b1 b2 k1 k2 => let '(a, n1) := pcutS thr d' k1 n in let '(b, n2) := pcutS thr d' k2 n in (PCaseDisj b1 b2 a b, Nat.max n1 n2)
  | PShDisj b1 n1 b2 n2 k => let '(k', n') := pcutS thr d' k n in (PShDisj b1 n1 b2 n2 k', n')
  | PFact K k => let '(k', n') := pcutS thr d' k n in (PFact K k', n')
  | PJoin b o m k => let '(k', n') := pcutS thr d' k n in (PJoin b o m k', n')
  | PForget l k => let '(k', n') := pcutS thr d' k n in (PForget l k', n')
  | PDropRange b m k => let '(k', n') := pcutS thr d' k n in (PDropRange b m k', n')
  | PGcKeep w k => let '(k', n') := pcutS thr d' k n in (PGcKeep w k', n')
  | PBump m k => let '(k', n') := pcutS thr d' k n in (PBump m k', n')
  | PHavoc rs k => let '(k', n') := pcutS thr d' k n in (PHavoc rs k', n')
  | PHavocBig m k => let '(k', n') := pcutS thr d' k n in (PHavocBig m k', n')
  | PFresh r l b k => let '(k', n') := pcutS thr d' k n in (PFresh r l b k', n')
  | PSys y k => let '(k', n') := pcutS thr d' k n in (PSys y k', n')
  | PMmap a b => let '(a', n1) := pcutS thr d' a n in let '(b', n2) := pcutS thr d' b n1 in (PMmap a' b', n2)
  | PMmapIn a b c => let '(a', n1) := pcutS thr d' a n in let '(b', n2) := pcutS thr d' b n1 in let '(c', n3) := pcutS thr d' c n2 in (PMmapIn a' b' c', n3)
  | PMmapInH a b c => let '(a', n1) := pcutS thr d' a n in let '(b', n2) := pcutS thr d' b n1 in let '(c', n3) := pcutS thr d' c n2 in (PMmapInH a' b' c', n3)
  | PMprotect a b => let '(a', n1) := pcutS thr d' a n in let '(b', n2) := pcutS thr d' b n1 in (PMprotect a' b', n2)
  | PBrk2 a b => let '(a', n1) := pcutS thr d' a n in let '(b', n2) := pcutS thr d' b n1 in (PBrk2 a' b', n2)
  | PX x args k => let '(k', n') := pcutS thr d' k n in (PX x args k', n')
  | PExt i a k => let '(k', n') := pcutS thr d' k n in (PExt i a k', n')
  | PEmit i a k => let '(k', n') := pcutS thr d' k n in (PEmit i a k', n')
  | PExt2 i a k1 k2 => let '(x, n1) := pcutS thr d' k1 n in let '(y, n2) := pcutS thr d' k2 n1 in (PExt2 i a x y, n2)
  | PLoop j m inv b k => let '(b', n1) := pcutS thr d' b n in let '(k', n2) := pcutS thr d' k n1 in (PLoop j m inv b' k', n2)
  | PFog i s k => let '(k', n') := pcutS thr d' k n in (PFog i s k', n')
  | PFogNew i s k => let '(k', n') := pcutS thr d' k n in (PFogNew i s k', n')
  | PGhost b m k => let '(k', n') := pcutS thr d' k n in (PGhost b m k', n')
  | PUnvis b m k => let '(k', n') := pcutS thr d' k n in (PUnvis b m k', n')
  | PHavocBrk l h k => let '(k', n') := pcutS thr d' k n in (PHavocBrk l h k', n')
  | PIntro l h k => let '(k', n') := pcutS thr d' k n in (PIntro l h k', n')
  | PDiamond j rs k => let '(k', n') := pcutS thr d' k n in (PDiamond j rs k', n')
  | PRename m k => let '(k', n') := pcutS thr d' k n in (PRename m k', n')
  | PCompact k => let '(k', n') := pcutS thr d' k n in (PCompact k', n')
  | PVia j js lo ka k => let '(x, n1) := pcutS thr d' ka n in let '(y, n2) := pcutS thr d' k n1 in (PVia j js lo x y, n2)
  | PAbstractCell b m k => let '(k', n') := pcutS thr d' k n in (PAbstractCell b m k', n')
  | PHavocWords bs k => let '(k', n') := pcutS thr d' k n in (PHavocWords bs k', n')
  | PRespell r e k => let '(k', n') := pcutS thr d' k n in (PRespell r e k', n')
  | other => (other, n)
  end end.


(* [comment removed for export] *)
Fixpoint maxby (l : list plan) (best : plan) : plan :=
  match l with [] => best | p :: l' => if Nat.ltb (psize best) (psize p) then maxby l' p else maxby l' best end.
Definition subL (d : nat) (p : plan) : plan := maxby (psubs d p) PContra.
(* [comment removed for export] *)
Fixpoint pskip (n : nat) (p : plan) {struct n} : plan :=
  match n with O => p | S n' =>
  match p with
  | PRun _ k | PShDisj _ _ _ _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k | PBump _ k
  | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k | PEmit _ _ k | PFog _ _ k | PFogNew _ _ k
  | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k => pskip n' k
  | other => other
  end end.
(* [comment removed for export] *)
Definition pkids (p : plan) : list plan :=
  match p with
  | PSplit _ _ a b | PCase2 _ _ a b | PCaseDisj _ _ a b | PMmap a b | PMprotect a b | PBrk2 a b | PExt2 _ _ a b
  | PLoop _ _ _ a b | PVia _ _ _ a b => [a; b]
  | PMmapIn a b c | PMmapInH a b c => [a; b; c]
  | _ => []
  end.
Definition pkid (i : nat) (p : plan) : plan := nth i (pkids p) PContra.
(* [comment removed for export] *)
Definition presplit (p : plan) (k : plan) : plan :=
  match p with
  | PCaseDisj b1 b2 _ _ => PCaseDisj b1 b2 k k
  | PCase2 e mm _ _ => PCase2 e mm k k
  | other => other
  end.
(* [comment removed for export] *)
Fixpoint plabels (p : plan) : list nat :=
  match p with
  | PRun _ k | PShDisj _ _ _ _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k | PBump _ k
  | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k | PEmit _ _ k | PFog _ _ k | PFogNew _ _ k
  | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k => plabels k
  | PSplit _ _ a b | PCase2 _ _ a b | PCaseDisj _ _ a b | PMmap a b | PMprotect a b | PBrk2 a b | PExt2 _ _ a b
  | PLoop _ _ _ a b | PVia _ _ _ a b => plabels a ++ plabels b
  | PMmapIn a b c | PMmapInH a b c => plabels a ++ plabels b ++ plabels c
  | PHandoff h => [h]
  | _ => []
  end.

(* [comment removed for export] *)
Fixpoint hs_tab (l : list (nat * acs)) (h : nat) : option acs :=
  match l with [] => None | (h', cs) :: l' => if Nat.eqb h h' then Some cs else hs_tab l' h end.

(* [comment removed for export] *)
Fixpoint at_handoffs (f : nat -> plan) (p : plan) {struct p} : plan :=
  match p with
  | PRun s k => PRun s (at_handoffs f k)
  | PSplit e m k1 k2 => PSplit e m (at_handoffs f k1) (at_handoffs f k2)
  | PCase2 e m k1 k2 => PCase2 e m (at_handoffs f k1) (at_handoffs f k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (at_handoffs f k1) (at_handoffs f k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (at_handoffs f k)
  | PFact K k => PFact K (at_handoffs f k)
  | PJoin b o m k => PJoin b o m (at_handoffs f k)
  | PForget l k => PForget l (at_handoffs f k)
  | PDropRange b m k => PDropRange b m (at_handoffs f k)
  | PGcKeep w k => PGcKeep w (at_handoffs f k)
  | PBump m k => PBump m (at_handoffs f k)
  | PHavoc rs k => PHavoc rs (at_handoffs f k)
  | PHavocBig m k => PHavocBig m (at_handoffs f k)
  | PFresh r l b k => PFresh r l b (at_handoffs f k)
  | PSys y k => PSys y (at_handoffs f k)
  | PMmap a b => PMmap (at_handoffs f a) (at_handoffs f b)
  | PMmapIn a b c => PMmapIn (at_handoffs f a) (at_handoffs f b) (at_handoffs f c)
  | PMmapInH a b c => PMmapInH (at_handoffs f a) (at_handoffs f b) (at_handoffs f c)
  | PMprotect a b => PMprotect (at_handoffs f a) (at_handoffs f b)
  | PBrk2 a b => PBrk2 (at_handoffs f a) (at_handoffs f b)
  | PX x args k => PX x args (at_handoffs f k)
  | PExt i a k => PExt i a (at_handoffs f k)
  | PEmit i a k => PEmit i a (at_handoffs f k)
  | PExt2 i a k1 k2 => PExt2 i a (at_handoffs f k1) (at_handoffs f k2)
  | PLoop j m inv b k => PLoop j m inv b (at_handoffs f k)
  | PFog i s k => PFog i s (at_handoffs f k)
  | PFogNew i s k => PFogNew i s (at_handoffs f k)
  | PGhost b m k => PGhost b m (at_handoffs f k)
  | PUnvis b m k => PUnvis b m (at_handoffs f k)
  | PHavocBrk l h k => PHavocBrk l h (at_handoffs f k)
  | PIntro l h k => PIntro l h (at_handoffs f k)
  | PDiamond j rs k => PDiamond j rs (at_handoffs f k)
  | PRename m k => PRename m (at_handoffs f k)
  | PCompact k => PCompact (at_handoffs f k)
  | PVia j js lo ka k => PVia j js lo ka (at_handoffs f k)
  | PAbstractCell b m k => PAbstractCell b m (at_handoffs f k)
  | PHavocWords bs k => PHavocWords bs (at_handoffs f k)
  | PRespell r e k => PRespell r e (at_handoffs f k)
  | PHandoff h => f h
  | other => other
  end.

(* [comment removed for export] *)
Fixpoint ins_main (d : nat) (f : plan -> plan) (p : plan) {struct d} : plan :=
  match d with O => f p | S d' =>
  let pick2 {T} (mk : plan -> plan -> T) (a b : plan) : T :=
    if Nat.ltb (psize a) (psize b) then mk a (ins_main d' f b) else mk (ins_main d' f a) b in
  match p with
  | PRun s k => PRun s (ins_main d' f k)
  | PSplit e m k1 k2 => pick2 (PSplit e m) k1 k2
  | PCase2 e m k1 k2 => pick2 (PCase2 e m) k1 k2
  | PCaseDisj b1 b2 k1 k2 => pick2 (PCaseDisj b1 b2) k1 k2
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (ins_main d' f k)
  | PFact K k => PFact K (ins_main d' f k)
  | PJoin b o m k => PJoin b o m (ins_main d' f k)
  | PForget l k => PForget l (ins_main d' f k)
  | PDropRange b m k => PDropRange b m (ins_main d' f k)
  | PGcKeep w k => PGcKeep w (ins_main d' f k)
  | PBump m k => PBump m (ins_main d' f k)
  | PHavoc rs k => PHavoc rs (ins_main d' f k)
  | PHavocBig m k => PHavocBig m (ins_main d' f k)
  | PFresh r l b k => PFresh r l b (ins_main d' f k)
  | PSys y k => PSys y (ins_main d' f k)
  | PMmap a b => pick2 PMmap a b
  | PMmapIn a b c => if Nat.ltb (psize a) (psize b) then PMmapIn a (ins_main d' f b) c else PMmapIn (ins_main d' f a) b c
  | PMmapInH a b c => if Nat.ltb (psize a) (psize b) then PMmapInH a (ins_main d' f b) c else PMmapInH (ins_main d' f a) b c
  | PMprotect a b => pick2 PMprotect a b
  | PBrk2 a b => pick2 PBrk2 a b
  | PX x args k => PX x args (ins_main d' f k)
  | PExt i a k => PExt i a (ins_main d' f k)
  | PEmit i a k => PEmit i a (ins_main d' f k)
  | PExt2 i a k1 k2 => pick2 (PExt2 i a) k1 k2
  | PLoop j m inv b k => PLoop j m inv b (ins_main d' f k)
  | PFog i s k => PFog i s (ins_main d' f k)
  | PFogNew i s k => PFogNew i s (ins_main d' f k)
  | PGhost b m k => PGhost b m (ins_main d' f k)
  | PUnvis b m k => PUnvis b m (ins_main d' f k)
  | PHavocBrk l h k => PHavocBrk l h (ins_main d' f k)
  | PIntro l h k => PIntro l h (ins_main d' f k)
  | PDiamond j rs k => PDiamond j rs (ins_main d' f k)
  | PRename m k => PRename m (ins_main d' f k)
  | PCompact k => PCompact (ins_main d' f k)
  | PVia j js lo ka k => PVia j js lo ka (ins_main d' f k)
  | PAbstractCell b m k => PAbstractCell b m (ins_main d' f k)
  | PHavocWords bs k => PHavocWords bs (ins_main d' f k)
  | PRespell r e k => PRespell r e (ins_main d' f k)
  | other => other
  end end.
