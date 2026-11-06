(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0b YQ0i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Definition p_lit (v : sv) := match v with SLit z => Some z | _ => None end.
Definition p_off (v : sv) := match v with SOff n z => Some (n, z) | _ => None end.
Definition p_alu (v : sv) := match v with SAlu o a b => Some (o, a, b) | _ => None end.
Definition p_aluw (v : sv) := match v with SAluw o a b => Some (o, a, b) | _ => None end.
Definition p_md (v : sv) := match v with SMd o a b => Some (o, a, b) | _ => None end.
Definition p_mdw (v : sv) := match v with SMdw o a b => Some (o, a, b) | _ => None end.
Definition p_ext (v : sv) := match v with SExt s w a => Some (s, w, a) | _ => None end.
Fixpoint msv (k : img) (a1 a2 : sv) {struct a1} : sv :=
if sv_eqb a1 a2 then a1 else
match a1 with
| SLit x1 => match p_lit a2 with Some x2 => SLit (zsel k x1 x2) | _ => seln k a1 a2 end
| SOff n1 z1 => match p_off a2 with Some (n2, z2) => if Nat.eqb n1 n2 then SOff n1 (zsel k z1 z2) else seln k a1 a2 | _ => seln k a1 a2 end
| SAlu o1 x1 y1 => match p_alu a2 with Some (o2, x2, y2) => if aluop_beq o1 o2 then SAlu o1 (msv k x1 x2) (msv k y1 y2) else seln k a1 a2 | _ => seln k a1 a2 end
| SAluw o1 x1 y1 => match p_aluw a2 with Some (o2, x2, y2) => if aluop_beq o1 o2 then SAluw o1 (msv k x1 x2) (msv k y1 y2) else seln k a1 a2 | _ => seln k a1 a2 end
| SMd o1 x1 y1 => match p_md a2 with Some (o2, x2, y2) => if mulop_beq o1 o2 then SMd o1 (msv k x1 x2) (msv k y1 y2) else seln k a1 a2 | _ => seln k a1 a2 end
| SMdw o1 x1 y1 => match p_mdw a2 with Some (o2, x2, y2) => if mulop_beq o1 o2 then SMdw o1 (msv k x1 x2) (msv k y1 y2) else seln k a1 a2 | _ => seln k a1 a2 end
| SExt s1 w1 x1 => match p_ext a2 with Some (s2, w2, x2) => if Bool.eqb s1 s2 && N.eqb w1 w2 then SExt s1 w1 (msv k x1 x2) else seln k a1 a2 | _ => seln k a1 a2 end
| _ => seln k a1 a2
end.
Fixpoint mlist {T : Type} (f : T -> T -> T) (a1 a2 : list T) {struct a1} : option (list T) :=
match a1, a2 with
| [], [] => Some []
| x1 :: r1, x2 :: r2 => match mlist f r1 r2 with Some r => Some (f x1 x2 :: r) | None => None end
| _, _ => None
end.
Definition mlist' {T : Type} (k : img) (f : T -> T -> T) (a1 a2 : list T) : list T :=
match mlist f a1 a2 with Some l => l | None => seln k a1 a2 end.
Definition mcval (k : img) (a1 a2 : cval) : cval :=
match a1, a2 with
| CVal w1 v1, CVal w2 v2 => if N.eqb w1 w2 then CVal w1 (msv k v1 v2) else seln k a1 a2
| CZero l1, CZero l2 => CZero (zsel k l1 l2)
| CImg l1, CImg l2 => CImg (zsel k l1 l2)
| CData d1 s1 l1, CData d2 s2 l2 => if Nat.eqb d1 d2 then CData d1 (zsel k s1 s2) (zsel k l1 l2) else seln k a1 a2
| _, _ => seln k a1 a2
end.
Definition mchunk (k : img) (a1 a2 : chunk) : chunk := mkChunk (zsel k (c_off a1) (c_off a2)) (mcval k (c_val a1) (c_val a2)).
Definition obase_eqb (x y : option nat) : bool :=
match x, y with Some n, Some m => Nat.eqb n m | None, None => true | _, _ => false end.
Definition mregion (k : img) (a1 a2 : region) : region :=
if obase_eqb (r_base a1) (r_base a2) then
mkRegion (r_base a1) (zsel k (r_lo a1) (r_lo a2)) (zsel k (r_hi a1) (r_hi a2)) (zsel k (r_wlo a1) (r_wlo a2)) (zsel k (r_whi a1) (r_whi a2)) (mlist' k (mchunk k) (r_chunks a1) (r_chunks a2))
else seln k a1 a2.
Definition msmem (k : img) (a1 a2 : smem) : smem := mlist' k (mregion k) a1 a2.
Definition mnregion (k : img) (a1 a2 : nat * region) : nat * region :=
if Nat.eqb (fst a1) (fst a2) then (fst a1, mregion k (snd a1) (snd a2)) else seln k a1 a2.
Definition mafact (k : img) (a1 a2 : afact) : afact := mkAF (zsel k (af_lo a1) (af_lo a2)) (zsel k (af_hi a1) (af_hi a2)) (zsel k (af_al2 a1) (af_al2 a2)).
Definition matom (k : img) (a1 a2 : nat * afact) : nat * afact :=
if Nat.eqb (fst a1) (fst a2) then (fst a1, mafact k (snd a1) (snd a2)) else seln k a1 a2.
Definition bc_tag (c : Instr.branch_cond) : nat :=
match c with Instr.BC_EQ => 0 | Instr.BC_NE => 1 | Instr.BC_LT => 2 | Instr.BC_GE => 3 | Instr.BC_LTU => 4 | Instr.BC_GEU => 5 end%nat.
Definition macond (k : img) (a1 a2 : acond) : acond :=
if Nat.eqb (bc_tag (ac_c a1)) (bc_tag (ac_c a2)) then mkAC (ac_c a1) (msv k (ac_a a1) (ac_a a2)) (msv k (ac_b a1) (ac_b a2)) else seln k a1 a2.
Definition malias (k : img) (a1 a2 : sv * sv) : sv * sv := (msv k (fst a1) (fst a2), msv k (snd a1) (snd a2)).
Definition mfacts (k : img) (a1 a2 : facts) : facts :=
mkFacts (mlist' k (matom k) (f_atoms a1) (f_atoms a2)) (mlist' k (macond k) (f_conds a1) (f_conds a2)) (mlist' k (malias k) (f_alias a1) (f_alias a2)).
Definition mosv (k : img) (a1 a2 : option sv) : option sv :=
match a1, a2 with Some x1, Some x2 => Some (msv k x1 x2) | None, None => None | _, _ => seln k a1 a2 end.
Definition moregion (k : img) (a1 a2 : option region) : option region :=
match a1, a2 with Some x1, Some x2 => Some (mregion k x1 x2) | None, None => None | _, _ => seln k a1 a2 end.
Definition msstate (k : img) (a1 a2 : sstate) : sstate :=
mkSST (zsel k (ss_pc a1) (ss_pc a2)) (mlist' k (msv k) (ss_regs a1) (ss_regs a2)) (mlist' k (msv k) (ss_fregs a1) (ss_fregs a2)) (msmem k (ss_mem a1) (ss_mem a2)) (mosv k (ss_resv a1) (ss_resv a2)) (mfacts k (ss_facts a1) (ss_facts a2)).
Ltac img_merge k v1 v2 :=
let T := type of v1 in
let T' := eval cbv delta [smem] in T in
lazymatch T' with
| sstate => img_cbv (msstate k v1 v2)
| Z => img_cbv (zsel k v1 v2)
| sv => img_cbv (msv k v1 v2)
| list sv => img_cbv (mlist' k (msv k) v1 v2)
| region => img_cbv (mregion k v1 v2)
| list region => img_cbv (msmem k v1 v2)
| list (nat * region) => img_cbv (mlist' k (mnregion k) v1 v2)
| facts => img_cbv (mfacts k v1 v2)
| option sv => img_cbv (mosv k v1 v2)
| chunk => img_cbv (mchunk k v1 v2)
| list chunk => img_cbv (mlist' k (mchunk k) v1 v2)
| cval => img_cbv (mcval k v1 v2)
| option region => img_cbv (moregion k v1 v2)
| _ => img_merge_gen k v1 v2
end.
Ltac img_abs ik t := let f := (eval pattern ik in t) in lazymatch f with ?g _ => g end.
Ltac img_unfold_lets ik t :=
match goal with
| x := ?b |- _ => lazymatch b with context [ik] => lazymatch t with context [x] => let t' := (eval cbv delta [x] in t) in img_unfold_lets ik t' end end
| _ => t
end.
Ltac img_ev t0 :=
lazymatch goal with
| ik := _ : img |- _ => eval vm_compute in t0
| ik : img |- _ =>
let t := img_unfold_lets ik t0 in
lazymatch t with
| context [ik] =>
let g := img_abs ik t in
let v1 := eval vm_compute in (g K_tra) in let v2 := eval vm_compute in (g K_trb) in
img_merge ik v1 v2
| _ => eval vm_compute in t
end
| _ => eval vm_compute in t0
end.
Ltac img_eval F k :=
let v1 := eval vm_compute in (F K_tra) in let v2 := eval vm_compute in (F K_trb) in
let m := img_merge k v1 v2 in exact m.
Ltac img_eval_last F := lazymatch goal with k : img |- _ => img_eval F k end.
Ltac img_eexists_vm :=
lazymatch goal with
| ik := _ : img |- _ => eexists; vm_compute; reflexivity
| ik : img |- ?G =>
lazymatch G with
| context [ik] =>
let g := img_abs ik G in
let p1 := constr:(ltac:(cbv beta; eexists; vm_compute; reflexivity) : g K_tra) in
let p2 := constr:(ltac:(cbv beta; eexists; vm_compute; reflexivity) : g K_trb) in
let w1 := lazymatch p1 with context [ex_intro _ ?w _] => w end in
let w2 := lazymatch p2 with context [ex_intro _ ?w _] => w end in
let w := img_merge ik w1 w2 in
exists w; img_case; vm_compute; reflexivity
| _ => eexists; vm_compute; reflexivity
end
| _ => eexists; vm_compute; reflexivity
end.
Ltac img_eval_sel F :=
lazymatch goal with
| k : img |- _ => let v1 := eval vm_compute in (F K_tra) in let v2 := eval vm_compute in (F K_trb) in exact (seln k v1 v2)
end.
Ltac img_eval_free F :=
let v1 := eval vm_compute in (F K_tra) in let v2 := eval vm_compute in (F K_trb) in
lazymatch v1 with v2 => exact v1 | _ => fail "img_eval_free: the images give different values" end.
