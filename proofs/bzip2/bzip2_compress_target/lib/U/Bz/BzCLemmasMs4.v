(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition bigF (qoff nb : Z) (ro : zarr) (i : Z) (s : mss) : Prop :=
  let ss := zget ro i in
  0 <= ss < 256 /\
  (forall k, (k < 256)%nat -> let s' := ms_step1 k qoff nb ss 0 s in s_exit s' = false -> step1F qoff nb ss (0 + Z.of_nat k) s') /\
  (let s1 := ms_step1 256 qoff nb ss 0 s in s_exit s1 = false ->
   let ft := s_ft s1 in let a1 := s_a1 s1 in let a2 := s_a2 s1 in let bd := s_bd s1 in
   let ci := ms_copy_init 256 (s_cs s1) (s_ce s1) ft ss 0 in let cs0 := fst ci in let ce0 := snd ci in
   let j0 := clearmask (zget ft (Z.shiftl ss 8)) in
   let rf := ms_copy_fwd (S (Z.to_nat nb)) a1 cs0 a2 bd nb ss j0 in let a1F := fst (fst rf) in let csF := snd (fst rf) in
   let j1 := clearmask (zget ft (Z.shiftl (ss + 1) 8)) - 1 in
   let rb := ms_copy_bwd (S (Z.to_nat nb)) a1F ce0 a2 bd nb ss j1 in let ceB := snd (fst rb) in
   let ftm := ms_mark 256 ft ss 0 in
   zget bd ss = 0 /\ ftv ft /\
   (forall k, let '(r, jk) := ms_copy_fwd k a1 cs0 a2 bd nb ss j0 in fwdF a2 bd nb ss (fst r) (snd r) jk) /\
   zget csF ss <= snd rf /\
   (forall k, let '(r, jk) := ms_copy_bwd k a1F ce0 a2 bd nb ss j1 in bwdF a2 bd nb ss (fst r) (snd r) jk) /\
   snd rb <= zget ceB ss /\
   (zget csF ss - 1 = zget ceB ss \/ (zget csF ss = 0 /\ zget ceB ss = nb - 1)) /\
   (i < 255 -> let bbStart := clearmask (zget ftm (Z.shiftl ss 8)) in let bbEnd := clearmask (zget ftm (Z.shiftl (ss + 1) 8)) in
               bbStart <= bbEnd /\ bbEnd <= nb)).

Lemma ms_big_eq : forall ro qoff nb i s,
  ms_big ro qoff nb i s =
  (let ss := zget ro i in
   let s1 := ms_step1 256 qoff nb ss 0 s in
   if s_exit s1 then s1 else
   let ft := s_ft s1 in
   let '(cs, ce) := ms_copy_init 256 (s_cs s1) (s_ce s1) ft ss 0 in
   let '(a1, cs, _) := ms_copy_fwd (S (Z.to_nat nb)) (s_a1 s1) cs (s_a2 s1) (s_bd s1) nb ss (clearmask (zget ft (Z.shiftl ss 8))) in
   let '(a1, ce, _) := ms_copy_bwd (S (Z.to_nat nb)) a1 ce (s_a2 s1) (s_bd s1) nb ss (clearmask (zget ft (Z.shiftl (ss + 1) 8)) - 1) in
   let ft := ms_mark 256 ft ss 0 in
   let bd := zset (s_bd s1) ss 1 in
   let a2 := (if i <? 255 then
                let bbStart := clearmask (zget ft (Z.shiftl ss 8)) in
                let bbSize := clearmask (zget ft (Z.shiftl (ss + 1) 8)) - bbStart in
                let shifts := ms_shifts 40 bbSize 0 in
                ms_quad (Z.to_nat bbSize) (s_a2 s1) a1 qoff nb bbStart shifts (bbSize - 1)
              else s_a2 s1) in
   MSS a1 a2 ft bd cs ce (s_budget s1) (s_nqs s1) (s_mql s1) false).
Proof. reflexivity. Qed.

