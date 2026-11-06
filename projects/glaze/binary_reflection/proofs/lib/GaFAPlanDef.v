(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon GaFA.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition off : Type := (Z * list expr)%type.
Definition off0 (c : Z) : off := (c, []).
Definition oadd (o : off) (c : Z) (ts : list expr) : off := (fst o + c, snd o ++ ts).
Definition orender (o : off) : expr :=
  fold_left (fun e t => eadd e t) (snd o) (if Z.eqb (fst o) 0 then O else eaddz O (fst o)).
Definition rem (o : off) : expr := esub (esub EE B) (orender o).
(* [comment removed for export] *)
Definition EXK (o : off) : plan :=
  PFact (KRange (rem o) 0 BUFMAX) (PFactLe (orender o) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, orender o)])).
Definition EX (o : off) : plan := PRun [] (EXK o).
Definition ptrchk (o : off) (mid : Z) (X cont : plan) : plan := PCase2 (rem o) mid X cont.
Definition named (r v : nat) (k : plan) : plan := PBump v (PFresh r 0 None k).
Definition pbranch (kfall ktaken : plan) : plan := PBranch kfall ktaken.

(* [comment removed for export] *)
Fixpoint cases (fuel : nat) (r : nat) (arms : list (Z * plan)) : plan :=
  match fuel with
  | 0%nat => PContra
  | Datatypes.S f =>
      match arms with
      | [] => PContra
      | [a] => snd a
      | _ => let m := Nat.div (length arms) 2 in
             let left := firstn m arms in
             let right := skipn m arms in
             PCaseReg r (fst (last left (0, PContra))) (cases f r left) (cases f r right)
      end
  end.
(* [comment removed for export] *)
Definition points4 (r : nat) (arm : Z -> plan) : plan :=
  cases 8 r (map (fun c => (c, PRespell r (ELit c) (arm c))) [0; 1; 2; 3]).
(* [comment removed for export] *)
Fixpoint gaps (fuel : nat) (a b : Z) (krng : plan) : list (Z * plan) :=
  match fuel with
  | 0%nat => []
  | Datatypes.S f => if Z.ltb b a then [] else let bb := Z.min b (a / 8 * 8 + 7) in (bb, krng) :: gaps f (bb + 1) b krng
  end.
Fixpoint tsplit_arms (pts : list Z) (cur hi : Z) (kpt : Z -> plan) (krng : plan) : list (Z * plan) :=
  match pts with
  | [] => gaps 64 cur hi krng
  | p :: ps => gaps 64 cur (p - 1) krng ++ (p, kpt p) :: tsplit_arms ps (p + 1) hi kpt krng
  end.
(* [comment removed for export] *)
Definition tsplit (r : nat) (pts : list Z) (kpt : Z -> plan) (krng : plan) (lo hi : Z) : plan :=
  cases 512 r (tsplit_arms (filter (fun p => Z.leb lo p && Z.leb p hi)%bool pts) lo hi kpt krng).
Definition rsp (r : nat) (p : Z) (k : plan) : plan := PRespell r (ELit p) k.
Definition TAGPTS : list Z := map (fun k => 8 * Z.of_nat k + 4) (seq 0 32).

Definition HC (code : Z) : Z := match code with 0 => 1 | 1 => 2 | 2 => 4 | _ => 8 end.
Definition BCw (i : Z) : Z := nth (Z.to_nat i) [1; 2; 4; 8; 16; 32; 64; 128] 1.       (* [comment removed for export] *)
Definition JTW (idx : Z) : option Z :=                                                (* [comment removed for export] *)
  match idx with 0 | 1 => Some 1 | 4 | 5 => Some 2 | 8 | 9 => Some 4 | 12 | 13 => Some 8 | _ => None end.
Definition BIG : Z := 1125899906842627.

(* [comment removed for export] *)
Fixpoint elem_loopL (head : Z) (nit : nat) (o : off) (w : option Z) : plan :=
  match nit with
  | 0%nat => EX o
  | Datatypes.S n =>
      match w with
      | None => ptrchk o 0 (EX o) (EX o)
      | Some w => ptrchk o 0 (EX o) (let body := match n with 0%nat => EX (oadd o w []) | _ => PRun [head] (elem_loopL head n (oadd o w []) (Some w)) end in
                                    if Z.ltb 1 w then ptrchk o (w - 1) (EX o) body else body)
      end
  end.
Definition elemw (tag : Z) : option Z :=
  if Z.eqb (Z.land tag 248) 112 then Some 8 else let idx := Z.shiftr (Z.land (tag - 8) 4294967295) 3 in if Z.leb idx 13 then JTW idx else None.


(* [comment removed for export] *)
Definition JO : expr := EVar 200.
Definition JCNT : expr := EVar 150.
Definition JOFF : off := (0, [esub JO O]).          (* [comment removed for export] *)
Definition PADJ : expr := EVar 260.                 (* [comment removed for export] *)
Definition jpath (l : list dstep) : acs := snd (dpath ASEGS IT AASAN (XN IT NXF) XB0 BFUEL NXF tin l 0).
(* [comment removed for export] *)
Definition jarm (o : off) (r_hc : nat) (stop_cnt big_pc : Z) (big_ok_taken : bool) (c : Z) : list dstep :=
  let hc := HC c in
  [DRLo r_hc c; DRHi r_hc (c - 1)] ++ (if Z.eqb hc 1 then [] else [DHi (rem o) (hc - 1)]) ++
  (if Z.eqb hc 8 then [DRun [big_pc]; if big_ok_taken then DBrT else DBrF] else []) ++ [DRun [stop_cnt]].
Definition kmem (K : kentry) (k : list kentry) : bool := existsb (APC.kentry_eqb K) k.
Definition kcommon (s0 : acs) (ss : list acs) : list kentry := List.filter (fun K => forallb (fun s => kmem K (kn s)) ss) (kn s0).
Fixpoint jregs_slots (rs : list expr) (rss : list (list expr)) (i v : nat) (ov : list (nat * expr)) : list expr :=
  match rs with
  | [] => []
  | r :: rs' =>
      match find (fun p => Nat.eqb (fst p) i) ov with
      | Some (_, e) => e :: jregs_slots rs' rss (Datatypes.S i) v ov
      | None =>
          if forallb (fun l => expr_eqb (nth i l (ELit 0)) r) rss then r :: jregs_slots rs' rss (Datatypes.S i) v ov
          else EVar v :: jregs_slots rs' rss (Datatypes.S i) (Datatypes.S v) ov
      end
  end.
(* [comment removed for export] *)
Definition jtempl (pre : list dstep) (o : off) (r_hc : nat) (stop_cnt big_pc : Z) (big_ok_taken : bool) (ov : list (nat * expr)) (cnthi : Z) : acs :=
  let st := fun c => jpath (pre ++ jarm o r_hc stop_cnt big_pc big_ok_taken c) in
  let s0 := st 0 in let ss := map st [1; 2; 3] in
  let regs := jregs_slots (s_regs (a_ss s0)) (map (fun s => s_regs (a_ss s)) ss) 0%nat 201%nat ov in
  (* [comment removed for export] *)
  let kq := List.filter (fun K => match K with KWord (SA b 0) _ _ => negb (expr_eqb b Q) && kentry_vars_lt NXF K | _ => kentry_vars_lt NXF K end) (kcommon s0 ss) in
  let kj := [KWord (SA Q 0) 8 (eadd B JO); KRange JO 0 BUFMAX; KRange (esub (esub EE B) JO) 0 BUFMAX; KRange (esub JO (orender o)) 1 8;
             KRange JCNT 0 cnthi] in
  with_ss s0 (mk_ss stop_cnt regs (kj ++ kq) 240%nat).
(* [comment removed for export] *)
Definition count_hdr_j (j : nat) (T : acs) (o : off) (r_hc : nat) (stop_hc : Z) (r_cnt : nat) (stop_cnt : Z) (k_after : off -> plan)
           (big_pc : Z) (big_ok_taken : bool) : plan :=
  let arm (code : Z) :=
    let hc := HC code in
    let k := PRun [stop_cnt] (named r_cnt 150 (PMergeW j [(200%nat, orender (oadd o hc []))])) in
    let k := if Z.eqb hc 8
             then let kf := PFactLeR r_cnt 0 (ELit BIG) BIG k in
                  PRun [big_pc] (if big_ok_taken then pbranch (EX (oadd o hc [])) kf else pbranch kf (EX (oadd o hc [])))
             else k in
    if Z.eqb hc 1 then k else ptrchk o (hc - 1) (EX o) k in
  PVia j T 200 (PRun [stop_hc] (points4 r_hc arm)) (k_after JOFF).
(* [comment removed for export] *)
Definition pre_top (t : Z) : list dstep := [DHi (rem (off0 0)) 0; DFact (KRange (esub EE B) 1 BUFMAX); DRun [0xa19dc]; DRLo 6 t; DRHi 6 (t - 1); DRun []].
Definition pre_92 (t2 : Z) : list dstep :=
  [DHi (rem (off0 0)) 0; DFact (KRange (esub EE B) 1 BUFMAX); DRun [0xa19dc]; DRLo 6 92; DRHi 6 91; DRun []; DHi (rem (off0 1)) 0; DRun [0xa1a20];
   DRLo 7 t2; DRHi 7 (t2 - 1); DRun []].
(* [comment removed for export] *)
Definition CTAGS : list Z := List.filter (fun t => negb (Z.eqb t 116) && negb (Z.eqb t 92)) TAGPTS.
Definition T2OS : list Z := List.filter (fun t2 => negb (Z.eqb (Z.land t2 24) 24) && negb (Z.eqb t2 116)) TAGPTS.
Definition JC_tab : list (Z * acs) := Eval vm_compute in
  map (fun t => (t, jtempl (pre_top t ++ [DHi (rem (off0 1)) 0; DRun [0xa1bd4]]) (off0 1) 28 0xa2110 0xa2104 true [(6%nat, ELit t); (12%nat, JCNT)] (2 ^ 48))) CTAGS.
Definition JA_t : acs := Eval vm_compute in
  jtempl (pre_top 116 ++ [DHi (rem (off0 1)) 0; DRun [0xa1b18]]) (off0 1) 6 0xa1e5c 0xa1e50 true [(14%nat, JCNT)] (2 ^ 48).
Definition JBO_tab : list (Z * acs) := Eval vm_compute in
  map (fun t2 => (t2, jtempl (pre_92 t2 ++ [DHi (rem (off0 2)) 0; DRun [0xa1d18]]) (off0 2) 28 0xa2a4c 0xa2a44 false [(7%nat, ELit t2); (14%nat, JCNT)] (2 ^ 48))) T2OS.
Definition JBU_t : acs := Eval vm_compute in
  jtempl (pre_92 116 ++ [DHi (rem (off0 2)) 0; DRun [0xa1a88]]) (off0 2) 6 0xa28c8 0xa28c0 false [(14%nat, JCNT)] (2 ^ 48).
Definition jlook (tab : list (Z * acs)) (t : Z) : acs := match find (fun p => Z.eqb (fst p) t) tab with Some (_, a) => a | None => tin end.

(* [comment removed for export] *)
Definition planA : plan :=
  let after_cnt (o2 : off) :=
    let cnt8 := escale 8 CNT in
    let ok := PRun [] (pbranch (EX o2) (PRun [] (PExt ID_AMEMCPY [] (EX (oadd o2 0 [cnt8]))))) in   (* [comment removed for export] *)
    let ok := PCaseReg 14 0 (EX o2) ok in                                                            (* [comment removed for export] *)
    PRun [0xa1e94] (PCaseReg 14 3 ok (PRun [] (pbranch (EX o2) (EX o2)))) in                        (* [comment removed for export] *)
  ptrchk (off0 1) 0 (EX (off0 1)) (count_hdr_j 5 JA_t (off0 1) 6 0xa1b18 14 0xa1e5c after_cnt 0xa1e50 true).

(* [comment removed for export] *)
Definition planBu64 : plan :=
  let after_cnt (o2 : off) :=
    let o3 := oadd o2 1 [] in
    let padok :=
      let o4 := oadd o3 0 [PADJ] in
      let cnt8 := escale 8 CNT in
      let inner := PCaseReg 14 0 (EX o4) (PRun [] (PExt ID_AMEMCPY [] (EX (oadd o4 0 [cnt8])))) in   (* [comment removed for export] *)
      let inner := PRun [0xa2968] inner in
      let inner := PCaseReg 14 3 inner (EX o4) in                                                     (* [comment removed for export] *)
      let inner := PFactVia (rem o4) (esub (rem o3) (eadd cnt8 PADJ)) 0 (2 ^ 57)
                     (PFactLe (rem o4) (rem o3) BUFMAX (PRun [0xa294c] inner)) in
      let inner := PRun [0xa2930] (pbranch inner (EX o3)) in                                         (* [comment removed for export] *)
      named 17 260 inner in
    let k := PRun [0xa2920] (PCaseReg 17 7 padok (EX o3)) in                                         (* [comment removed for export] *)
    ptrchk o2 0 (EX o2) k in                                                                           (* [comment removed for export] *)
  ptrchk (off0 2) 0 (EX (off0 2)) (count_hdr_j 6 JBU_t (off0 2) 6 0xa1a88 14 0xa28c8 after_cnt 0xa28c0 false).

(* [comment removed for export] *)
Definition planC (tag : Z) : plan :=
  let after_cnt (o2 : off) :=
    let loop := elem_loopL 0xa21b0 3 o2 (elemw tag) in
    let ok := PRun [] (pbranch (EX o2) (PRun [0xa21b0] loop)) in                                      (* [comment removed for export] *)
    PRun [0xa2144] (PCaseReg 12 3 ok (PRun [] (pbranch (EX o2) (EX o2)))) in
  ptrchk (off0 1) 0 (EX (off0 1)) (count_hdr_j 7 (jlook JC_tab tag) (off0 1) 28 0xa1bd4 12 0xa2110 after_cnt 0xa2104 true).

(* [comment removed for export] *)
Definition planBother (t2 : Z) : plan :=
  let w := BCw (Z.shiftr t2 5) in
  let after_cnt (o2 : off) :=
    let o3 := oadd o2 1 [] in
    let padok :=
      let o4 := oadd o3 0 [PADJ] in
      let loop := elem_loopL 0xa2b14 3 o4 (elemw t2) in
      let inner := PCaseReg 14 3 (PRun [0xa2b14] loop) (EX o4) in                                     (* [comment removed for export] *)
      let fv := PFactVia (rem o4) (esub (rem o3) (eadd (escale w CNT) PADJ)) 0 (2 ^ 57)
                  (PFactLe (rem o4) (rem o3) BUFMAX (PRun [0xa2acc] inner)) in
      let inner := PRun [0xa2ab0] (pbranch fv (EX o3)) in                                            (* [comment removed for export] *)
      named 5 260 inner in
    let k := PRun [0xa2aa0] (PCaseReg 5 (w - 1) padok (EX o3)) in                                    (* [comment removed for export] *)
    ptrchk o2 0 (EX o2) k in                                                                           (* [comment removed for export] *)
  ptrchk (off0 2) 0 (EX (off0 2)) (count_hdr_j 8 (jlook JBO_tab t2) (off0 2) 28 0xa1d18 14 0xa2a4c after_cnt 0xa2a44 false).

(* [comment removed for export] *)
Definition t2pt (t2 : Z) : plan :=
  if Z.eqb (Z.land t2 24) 24 then EX (off0 1)
  else if Z.eqb t2 116 then PRun [] planBu64 else PRun [] (planBother t2).
Definition planB_arms (lo hi : Z) : plan := tsplit 7 TAGPTS (fun t2 => rsp 7 t2 (t2pt t2)) (EX (off0 1)) lo hi.
Definition planB (inner : plan) : plan := ptrchk (off0 1) 0 (EX (off0 1)) (PRun [0xa1a20] inner).

(* [comment removed for export] *)
Definition plan_pre (k : plan) : plan :=
  ptrchk (off0 0) 0 (EX (off0 0)) (PFact (KRange (esub EE B) 1 BUFMAX) (PRun [0xa19dc] k)).
Definition tagpt (b : plan) (rsp92 : bool) (t : Z) : plan :=
  if Z.eqb t 116 then rsp 6 t (PRun [] planA)
  else if Z.eqb t 92 then (if rsp92 then rsp 6 t (PRun [] (planB b)) else PRun [] (planB b))
  else rsp 6 t (PRun [] (planC t)).

(* [comment removed for export] *)
Definition plan_top : plan :=
  plan_pre (tsplit 6 TAGPTS (tagpt (PCaseReg 7 63 (PHandoffW 1 []) (PCaseReg 7 127 (PHandoffW 2 []) (PHandoffW 3 []))) false) (EX (off0 0)) 0 255).
Definition plan_cut_lo : plan := planB_arms 0 63.
Definition plan_cut_mid : plan := planB_arms 64 127.
Definition plan_cut_hi : plan := planB_arms 128 255.

(* [comment removed for export] *)
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XB0.
Definition stepsB : list dstep :=
  [DHi (rem (off0 0)) 0; DFact (KRange (esub EE B) 1 BUFMAX); DRun [0xa19dc]; DRLo 6 92; DRHi 6 91; DRun [];
   DHi (rem (off0 1)) 0; DRun [0xa1a20]].
Definition cutT (steps : list dstep) : acs := snd (dpath ASEGS IT AASAN (XN IT NXF) XB BFUEL NXF tin steps 0).
Definition CUTS : list (acs * AP.plan) :=
  [(cutT (stepsB ++ [DRLo 7 63]), plan_cut_lo); (cutT (stepsB ++ [DRHi 7 63; DRLo 7 127]), plan_cut_mid);
   (cutT (stepsB ++ [DRHi 7 127]), plan_cut_hi)].
Definition NCUTS : nat := 3.
Lemma CUTS_len : length CUTS = NCUTS. Proof. reflexivity. Qed.

Definition cut_stmt (i : nat) : Prop :=
  match nth_error CUTS i with
  | Some (T, k) => exists sh, gplan_ok k = true /\ holes_only sh = true /\
      check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh
  | None => True
  end.
Definition cut_ok (i : nat) : bool :=
  match nth_error CUTS i with
  | Some (T, k) => gplan_ok k &&
      match check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k with
      | COk sh => holes_only sh | _ => false end
  | None => true
  end%bool.
Lemma cut_ok_sound : forall i, cut_ok i = true -> cut_stmt i.
Proof.
  intros i H. unfold cut_ok in H. unfold cut_stmt. destruct (nth_error CUTS i) as [[T k]|]; [|exact I].
  destruct (gplan_ok k); [|discriminate].
  destruct (check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k) as [sh|c w cs]; try discriminate.
  exists sh. repeat split; try reflexivity. exact H.
Qed.
(* [comment removed for export] *)
Lemma top_gplan : gplan_ok plan_top = true. Proof. vm_compute. reflexivity. Qed.
