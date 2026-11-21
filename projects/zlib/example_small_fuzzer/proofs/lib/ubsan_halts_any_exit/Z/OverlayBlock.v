(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayLP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition xl_of_lcode (c : Z) : Z :=
  nth (Z.to_nat (c - 257)) [0;0;0;0;0;0;0;0;1;1;1;1;2;2;2;2;3;3;3;3;4;4;4;4;5;5;5;5;0] 0.
Definition xd_of_dcode (d : Z) : Z :=
  nth (Z.to_nat d) [0;0;0;0;1;1;2;2;3;3;4;4;5;5;6;6;7;7;8;8;9;9;10;10;11;11;12;12;13;13] 0.
Definition sl_of_code (c : Z) : Z :=
  if c <? 144 then 8 else if c <? 256 then 9 else if c <? 280 then 7 else 8.
Definition xb_of_bl (b : Z) : Z := if b =? 16 then 2 else if b =? 17 then 3 else if b =? 18 then 7 else 0.

Inductive lkind := KLit | KEob | KLen.
Record lclass := { lc_codes : list Z; lc_SL : Z; lc_xl : Z; lc_kind : lkind }.
Definition zrange (lo : Z) (n : nat) : list Z := map (fun k => lo + Z.of_nat k) (seq 0 n).
Definition LCLASSES : list lclass :=
  [ {| lc_codes := zrange 0 144; lc_SL := 8; lc_xl := 0; lc_kind := KLit |};
    {| lc_codes := zrange 144 112; lc_SL := 9; lc_xl := 0; lc_kind := KLit |};
    {| lc_codes := [256]; lc_SL := 7; lc_xl := 0; lc_kind := KEob |};
    {| lc_codes := zrange 257 8; lc_SL := 7; lc_xl := 0; lc_kind := KLen |};
    {| lc_codes := zrange 265 4; lc_SL := 7; lc_xl := 1; lc_kind := KLen |};
    {| lc_codes := zrange 269 4; lc_SL := 7; lc_xl := 2; lc_kind := KLen |};
    {| lc_codes := zrange 273 4; lc_SL := 7; lc_xl := 3; lc_kind := KLen |};
    {| lc_codes := zrange 277 3; lc_SL := 7; lc_xl := 4; lc_kind := KLen |};
    {| lc_codes := [280]; lc_SL := 8; lc_xl := 4; lc_kind := KLen |};
    {| lc_codes := zrange 281 4; lc_SL := 8; lc_xl := 5; lc_kind := KLen |};
    {| lc_codes := [285]; lc_SL := 8; lc_xl := 0; lc_kind := KLen |} ].
Record dclass := { dc_codes : list Z; dc_xd : Z }.
Definition DCLASSES : list dclass :=
  {| dc_codes := [0;1;2;3]; dc_xd := 0 |}
  :: map (fun x => {| dc_codes := [2 * x + 2; 2 * x + 3]; dc_xd := x |}) (zrange 1 13).

Definition nLC : nat := 11%nat.
Definition nDC : nat := 14%nat.
Definition lcl (k : nat) : lclass := nth k LCLASSES {| lc_codes := []; lc_SL := 0; lc_xl := 0; lc_kind := KLit |}.
Definition dcl (k : nat) : dclass := nth k DCLASSES {| dc_codes := []; dc_xd := 0 |}.
Definition is_lit (k : nat) : bool := match lc_kind (lcl k) with KLit => true | _ => false end.
Definition is_len (k : nat) : bool := match lc_kind (lcl k) with KLen => true | _ => false end.
Definition is_eob (k : nat) : bool := match lc_kind (lcl k) with KEob => true | _ => false end.


Inductive osym := OLit (c : Z) | OPair (lc dc : Z).

Record oblock := {
  ob_syms : list osym;
  ob_lenL : Z -> Z;
  ob_lenD : Z -> Z;
  ob_forced : list Z;
  ob_BC : Z -> Z;
  ob_BD : Z -> Z;
  ob_bforced : list Z;
  ob_blcodes : Z;
  ob_Hc1 : Z
}.

Definition countZ (P : Z -> bool) (l : list Z) : Z := lsum (fun c => if P c then 1 else 0) l.
Fixpoint ssum (f : osym -> Z) (l : list osym) : Z :=
  match l with [] => 0 | s :: r => f s + ssum f r end.
Definition scount (P : osym -> bool) (l : list osym) : Z := ssum (fun s => if P s then 1 else 0) l.

Section Val.
Variable b : oblock.

Definition fL (c : Z) : Z :=
  scount (fun s => match s with OLit c' => c' =? c | OPair lc _ => lc =? c end) (ob_syms b)
  + (if c =? 256 then 1 else 0).
Definition gD (d : Z) : Z := scount (fun s => match s with OLit _ => false | OPair _ dc => dc =? d end) (ob_syms b).
Definition forcedD (d : Z) : bool := existsb (Z.eqb d) (ob_forced b).
Definition NSYM : Z := Z.of_nat (length (ob_syms b)).
Definition vP : Z := scount (fun s => match s with OPair _ _ => true | _ => false end) (ob_syms b).
Definition vNLIT : Z := scount (fun s => match s with OLit _ => true | _ => false end) (ob_syms b).

Definition cellL (Q : Z -> bool) (k : nat) (l : Z) : Z :=
  countZ (fun c => Q c && (ob_lenL b c =? l)) (lc_codes (lcl k)).
Definition vU1 (k : nat) (l : Z) : Z := cellL (fun c => fL c =? 1) k l.
Definition vU2 (k : nat) (l : Z) : Z := cellL (fun c => fL c =? 2) k l.
Definition vU3 (k : nat) (l : Z) : Z := cellL (fun c => 3 <=? fL c) k l.
Definition vF3 (k : nat) (l : Z) : Z :=
  lsum (fun c => if (3 <=? fL c) && (ob_lenL b c =? l) then fL c else 0) (lc_codes (lcl k)).
Definition cellD (Q : Z -> bool) (k : nat) (m : Z) : Z :=
  countZ (fun d => Q d && (ob_lenD b d =? m)) (dc_codes (dcl k)).
Definition vV1 (k : nat) (m : Z) : Z := cellD (fun d => gD d =? 1) k m.
Definition vV2 (k : nat) (m : Z) : Z := cellD (fun d => gD d =? 2) k m.
Definition vV3 (k : nat) (m : Z) : Z := cellD (fun d => 3 <=? gD d) k m.
Definition vG3 (k : nat) (m : Z) : Z :=
  lsum (fun d => if (3 <=? gD d) && (ob_lenD b d =? m) then gD d else 0) (dc_codes (dcl k)).
Definition vVF (m : Z) : Z := countZ (fun d => ob_lenD b d =? m) (ob_forced b).

Definition vU : Z := countZ (fun c => 0 <? fL c) (zrange 0 286).
Definition vNLITC : Z := countZ (fun c => 0 <? fL c) (zrange 0 256).
Definition vNLENC : Z := countZ (fun c => 0 <? fL c) (zrange 257 29).
Definition vV : Z := countZ (fun d => 0 <? gD d) (zrange 0 30) + Z.of_nat (length (ob_forced b)).

Definition dcostS (s : osym) : Z :=
  match s with
  | OLit c => ob_lenL b c
  | OPair lc dc => ob_lenL b lc + xl_of_lcode lc + ob_lenD b dc + xd_of_dcode dc
  end.
Definition scostS (s : osym) : Z :=
  match s with
  | OLit c => sl_of_code c
  | OPair lc dc => sl_of_code lc + xl_of_lcode lc + 5 + xd_of_dcode dc
  end.
Definition vSV : Z := ssum (fun s => scostS s - dcostS s) (ob_syms b) + (7 - ob_lenL b 256).
Definition exS (s : osym) : Z := Z.max 0 (dcostS s - 24).
Definition vEX : Z := ssum exS (ob_syms b).
Definition pairA (s : osym) : Z := match s with OPair lc _ => ob_lenL b lc + xl_of_lcode lc | _ => -1 end.
Definition pairB (s : osym) : Z := match s with OPair _ dc => ob_lenD b dc + xd_of_dcode dc | _ => -1 end.
Definition vPI (a c : Z) : Z := scount (fun s => (pairA s =? a) && (pairB s =? c)) (ob_syms b).

Definition vBC (x : Z) : Z := ob_BC b x.
Definition vWB : Z := zsum (ob_BC b) 0 19.
Definition vB : Z := zsum (fun x => ob_BC b x * ob_BD b x) 0 19.
Definition vH : Z := ob_Hc1 b.

Fixpoint zruns_go (L : Z -> Z) (i : Z) (n : nat) (cur : Z) (acc : list Z) : list Z :=
  match n with
  | O => if cur =? 0 then acc else cur :: acc
  | S k => if L i =? 0 then zruns_go L (i + 1) k (cur + 1) acc
           else zruns_go L (i + 1) k 0 (if cur =? 0 then acc else cur :: acc)
  end.
Definition zruns (L : Z -> Z) (lo : Z) (n : nat) : list Z := zruns_go L lo n 0 [].
Definition rem138 (r : Z) : Z := if 138 <? r then r - 138 else r.
Definition nlong (r : Z) : Z := if 138 <? r then 1 else 0.
Definition is1 (r : Z) : Z := if rem138 r =? 1 then 1 else 0.
Definition is2 (r : Z) : Z := if rem138 r =? 2 then 1 else 0.
Definition isa (r : Z) : Z := if (3 <=? rem138 r) && (rem138 r <=? 10) then 1 else 0.
Definition isb (r : Z) : Z := if 11 <=? rem138 r then 1 else 0.
Definition lmaxc : Z := lmax (fun c => c) (filter (fun c => 0 <? fL c) (zrange 0 286)).
Definition dmaxc : Z := lmax (fun d => d) (filter (fun d => (0 <? gD d) || forcedD d) (zrange 0 30)).
Definition runs1 : list Z := zruns (ob_lenL b) 0 257.
Definition runs2 : list Z := zruns (ob_lenL b) 257 (Z.to_nat (lmaxc - 256)).
Definition runs3 : list Z := zruns (ob_lenD b) 0 (Z.to_nat (dmaxc + 1)).
Definition runs_of (r : Z) : list Z := if r =? 1 then runs1 else if r =? 2 then runs2 else runs3.
Definition vR1 (r : Z) : Z := lsum is1 (runs_of r).
Definition vR2 (r : Z) : Z := lsum is2 (runs_of r).
Definition vRA (r : Z) : Z := lsum isa (runs_of r).
Definition vRB (r : Z) : Z := lsum isb (runs_of r).
Definition vRLONG : Z := lsum nlong runs1 + lsum nlong runs2 + lsum nlong runs3.

End Val.


Inductive ovar :=
| OU1 (k : nat) (l : Z) | OU2 (k : nat) (l : Z) | OU3 (k : nat) (l : Z) | OF3 (k : nat) (l : Z)
| OV1 (k : nat) (m : Z) | OV2 (k : nat) (m : Z) | OV3 (k : nat) (m : Z) | OG3 (k : nat) (m : Z) | OVF (m : Z)
| OP | ONLIT | ON | OSV | OEX | OH | OU | OV | ONLITC | ONLENC
| OPI (a c : Z)
| OBC (x : Z) | OWB | OB
| OR1 (r : Z) | OR2 (r : Z) | ORA (r : Z) | ORB (r : Z) | ORLONG.

Definition oval (b : oblock) (v : ovar) : Z :=
  match v with
  | OU1 k l => vU1 b k l | OU2 k l => vU2 b k l | OU3 k l => vU3 b k l | OF3 k l => vF3 b k l
  | OV1 k m => vV1 b k m | OV2 k m => vV2 b k m | OV3 k m => vV3 b k m | OG3 k m => vG3 b k m | OVF m => vVF b m
  | OP => vP b | ONLIT => vNLIT b | ON => NSYM b | OSV => vSV b | OEX => vEX b | OH => vH b
  | OU => vU b | OV => vV b | ONLITC => vNLITC b | ONLENC => vNLENC b
  | OPI a c => vPI b a c
  | OBC x => vBC b x | OWB => vWB b | OB => vB b
  | OR1 r => vR1 b r | OR2 r => vR2 b r | ORA r => vRA b r | ORB r => vRB b r | ORLONG => vRLONG b
  end.

Definition ovar_eqb (u v : ovar) : bool :=
  match u, v with
  | OU1 k l, OU1 k' l' | OU2 k l, OU2 k' l' | OU3 k l, OU3 k' l' | OF3 k l, OF3 k' l'
  | OV1 k l, OV1 k' l' | OV2 k l, OV2 k' l' | OV3 k l, OV3 k' l' | OG3 k l, OG3 k' l' => Nat.eqb k k' && (l =? l')
  | OVF m, OVF m' => m =? m'
  | OP, OP | ONLIT, ONLIT | ON, ON | OSV, OSV | OEX, OEX | OH, OH | OU, OU | OV, OV | ONLITC, ONLITC | ONLENC, ONLENC => true
  | OPI a c, OPI a' c' => (a =? a') && (c =? c')
  | OBC x, OBC x' => x =? x'
  | OWB, OWB | OB, OB | ORLONG, ORLONG => true
  | OR1 r, OR1 r' | OR2 r, OR2 r' | ORA r, ORA r' | ORB r, ORB r' => r =? r'
  | _, _ => false
  end.

Lemma ovar_eqb_eq u v : ovar_eqb u v = true <-> u = v.
Proof.
  destruct u, v; cbn; rewrite ?Bool.andb_true_iff, ?Nat.eqb_eq, ?Z.eqb_eq; split; intros H;
    try discriminate; try (destruct H; subst; reflexivity); try (injection H; intros; subst; auto); try (subst; auto); try reflexivity.
Qed.
