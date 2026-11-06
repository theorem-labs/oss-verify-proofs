(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk L5Defs AxSymExec3 AxSymExec3B
AxSymExec3Sound AxSymRun3 SegRun SegPlan BigLinkBase L5Kn BigLinkGlue.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PStmt.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PR.
Module P := PStmt.
Local Notation MM := BL.MM.
Lemma MM_eq : MM = 18446744073709551616. Proof. reflexivity. Qed.
Definition ivl : Type := (Z * Z)%type.
Definition inr (i : ivl) : bool := (0 <=? fst i) && (snd i <? MM).
Definition ivadd (a b : ivl) : ivl := (fst a + fst b, snd a + snd b).
Definition ivsub (a b : ivl) : ivl := (fst a - snd b, snd a - fst b).
Definition ivscale (c : Z) (b : ivl) : ivl := if 0 <=? c then (c * fst b, c * snd b) else (c * snd b, c * fst b).
Definition ivmul (a b : ivl) : option ivl :=
if (0 <=? fst a) && (0 <=? fst b) then Some (fst a * fst b, snd a * snd b)
else if Z.eqb (fst a) (snd a) then Some (ivscale (fst a) b)
else if Z.eqb (fst b) (snd b) then Some (ivscale (fst b) a)
else None.
Definition obind (o : option ivl) (f : ivl -> option ivl) : option ivl := match o with Some x => f x | None => None end.
Definition lit_of (p : P.zx) : option Z :=
match p with
| P.ZL z => Some z
| P.ZPow (P.ZL a) (P.ZL b) => if 0 <=? b then Some (a ^ b) else None
| _ => None
end.
Lemma lit_of_sound R V p c : lit_of p = Some c -> P.dz R V p = c.
Proof.
destruct p; cbn [lit_of]; try discriminate; intros H.
- inversion H; reflexivity.
- destruct p1; try discriminate. destruct p2; try discriminate. destruct (0 <=? z0); inversion H; reflexivity.
Qed.
Fixpoint zx_eqb (a b : P.zx) : bool :=
match a, b with
| P.ZV n, P.ZV m => Nat.eqb n m | P.ZL x, P.ZL y => Z.eqb x y | P.ZR k, P.ZR l => Nat.eqb k l
| P.ZAdd a1 a2, P.ZAdd b1 b2 | P.ZSub a1 a2, P.ZSub b1 b2 | P.ZMul a1 a2, P.ZMul b1 b2 | P.ZDiv a1 a2, P.ZDiv b1 b2
| P.ZMod a1 a2, P.ZMod b1 b2 | P.ZPow a1 a2, P.ZPow b1 b2 | P.ZLand a1 a2, P.ZLand b1 b2 | P.ZLor a1 a2, P.ZLor b1 b2
| P.ZLxor a1 a2, P.ZLxor b1 b2 | P.ZLtbIf a1 a2, P.ZLtbIf b1 b2 | P.ZDivu a1 a2, P.ZDivu b1 b2 | P.ZRemu a1 a2, P.ZRemu b1 b2 =>
zx_eqb a1 b1 && zx_eqb a2 b2
| _, _ => false
end.
Lemma zx_eqb_eq a : forall b, zx_eqb a b = true -> a = b.
Proof.
induction a; destruct b; cbn [zx_eqb]; intros H; try discriminate;
try (apply Nat.eqb_eq in H; subst; reflexivity); try (apply Z.eqb_eq in H; subst; reflexivity);
try (apply andb_prop in H; destruct H as [H1 H2]; rewrite (IHa1 _ H1), (IHa2 _ H2); reflexivity).
Qed.
Fixpoint iv (bd : P.zx -> option ivl) (p : P.zx) : option ivl :=
match bd p with
| Some i => Some i
| None =>
match p with
| P.ZV n => None
| P.ZL z => Some (z, z)
| P.ZR _ => Some (0, MM - 1)
| P.ZAdd a b => obind (iv bd a) (fun x => obind (iv bd b) (fun y => Some (ivadd x y)))
| P.ZSub a b => obind (iv bd a) (fun x => obind (iv bd b) (fun y => Some (ivsub x y)))
| P.ZMul a b => obind (iv bd a) (fun x => obind (iv bd b) (fun y => ivmul x y))
| P.ZDiv a b => match lit_of b with
| Some c => if 0 <? c then obind (iv bd a) (fun x => Some (fst x / c, snd x / c)) else None
| None => obind (iv bd a) (fun x => obind (iv bd b) (fun y =>
if (0 <=? fst x) && (0 <? fst y) then Some (fst x / snd y, snd x / fst y) else None)) end
| P.ZMod a b => match lit_of b with Some m => if 0 <? m then Some (0, m - 1) else None | None => None end
| P.ZPow a b => match lit_of p with
| Some c => Some (c, c)
| None => match lit_of a with
| Some c => if 1 <=? c then obind (iv bd b) (fun y => if (0 <=? fst y) && (snd y <=? 128) then Some (c ^ fst y, c ^ snd y) else None)
else None
| None => None end end
| P.ZLand a b => obind (iv bd a) (fun x => obind (iv bd b) (fun y =>
if (0 <=? fst x) && (0 <=? fst y) then Some (0, Z.min (snd x) (snd y)) else None))
| P.ZLtbIf _ _ => Some (0, 1)
| _ => None
end end.
Definition bd_ok (bd : P.zx -> option ivl) (R : bvmap 5 word) (V : nat -> Z) : Prop :=
forall p l h, bd p = Some (l, h) -> l <= P.dz R V p <= h.
Lemma land_le_l' a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof. intros Ha Hm. rewrite Z.land_comm. apply (L5K.land_le_r m a Hm Ha). Qed.
Lemma ivscale_sound c l h x : l <= x <= h -> fst (ivscale c (l, h)) <= c * x <= snd (ivscale c (l, h)).
Proof.
intros [H1 H2]. unfold ivscale. cbn [fst snd]. destruct (0 <=? c) eqn:C.
- apply Z.leb_le in C. split; apply Z.mul_le_mono_nonneg_l; lia.
- apply Z.leb_gt in C. split; apply Z.mul_le_mono_nonpos_l; lia.
Qed.
Lemma ivmul_sound a b l1 h1 l2 h2 l h : l1 <= a <= h1 -> l2 <= b <= h2 -> ivmul (l1, h1) (l2, h2) = Some (l, h) -> l <= a * b <= h.
Proof.
intros Ha Hb H. unfold ivmul in H. cbn [fst snd] in H.
destruct ((0 <=? l1) && (0 <=? l2)) eqn:S.
- apply andb_prop in S. destruct S as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2. inversion H; subst.
split; apply Z.mul_le_mono_nonneg; lia.
- destruct (Z.eqb l1 h1) eqn:E1.
+ apply Z.eqb_eq in E1. subst h1. assert (a = l1) by lia. subst a. injection H as E.
pose proof (ivscale_sound l1 l2 h2 b Hb) as X. rewrite E in X. exact X.
+ destruct (Z.eqb l2 h2) eqn:E2; [|discriminate].
apply Z.eqb_eq in E2. subst h2. assert (b = l2) by lia. subst b. injection H as E.
pose proof (ivscale_sound l2 l1 h1 a Ha) as X. rewrite E in X. rewrite Z.mul_comm. exact X.
Qed.
Lemma div_iv a b la ha lb hb : la <= a <= ha -> lb <= b <= hb -> 0 <= la -> 0 < lb -> la / hb <= a / b <= ha / lb.
Proof.
intros [Ha1 Ha2] [Hb1 Hb2] H0 H1. split.
- apply Z.le_trans with (a / hb). apply Z.div_le_mono; lia. apply Z.div_le_compat_l; lia.
- apply Z.le_trans with (a / lb). apply Z.div_le_compat_l; lia. apply Z.div_le_mono; lia.
Qed.
Lemma pow_iv c e le he : 1 <= c -> le <= e <= he -> 0 <= le -> c ^ le <= c ^ e <= c ^ he.
Proof. intros Hc [H1 H2] H0. split; apply Z.pow_le_mono_r; lia. Qed.
Ltac ob_destr H :=
repeat match type of H with
| context [obind (iv ?bd ?q) _] => let E := fresh "E" in destruct (iv bd q) as [[? ?]|] eqn:E; cbn [obind] in H; [|discriminate]
end.
Lemma iv_sound bd V R : bd_ok bd R V -> forall p l h, iv bd p = Some (l, h) -> l <= P.dz R V p <= h.
Proof.
intros HB. induction p; intros l h Hp; cbn [iv] in Hp;
(destruct (bd _) as [i|] eqn:Hbd; [inversion Hp; subst; apply (HB _ _ _ Hbd)|]).
- discriminate.
- inversion Hp; subst. cbn. lia.
- inversion Hp; subst. cbn [P.dz]. pose proof (BL.bvu_range (getr R (Z_to_bv 5 (Z.of_nat k)))) as X. unfold BL.inrange in X. lia.
- ob_destr Hp. inversion Hp; subst. cbn [P.dz]. specialize (IHp1 _ _ eq_refl). specialize (IHp2 _ _ eq_refl). cbn. lia.
- ob_destr Hp. inversion Hp; subst. cbn [P.dz]. specialize (IHp1 _ _ eq_refl). specialize (IHp2 _ _ eq_refl). cbn. lia.
- ob_destr Hp. specialize (IHp1 _ _ eq_refl). specialize (IHp2 _ _ eq_refl). cbn [P.dz].
exact (ivmul_sound _ _ _ _ _ _ _ _ IHp1 IHp2 Hp).
- destruct (lit_of p2) as [c|] eqn:L.
+ destruct (0 <? c) eqn:C; [|discriminate]. apply Z.ltb_lt in C. ob_destr Hp. inversion Hp; subst. cbn [P.dz].
rewrite (lit_of_sound R V p2 c L). specialize (IHp1 _ _ eq_refl). cbn. split; apply Z.div_le_mono; lia.
+ ob_destr Hp. cbn [fst snd] in Hp.
match type of Hp with context [(0 <=? ?x) && (0 <? ?y)] => destruct ((0 <=? x) && (0 <? y)) eqn:S; [|discriminate] end.
apply andb_prop in S. destruct S as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2. inversion Hp; subst. cbn [P.dz].
specialize (IHp1 _ _ eq_refl). specialize (IHp2 _ _ eq_refl).
apply div_iv; [exact IHp1 | exact IHp2 | lia | lia].
- destruct (lit_of p2) as [c|] eqn:L; [|discriminate].
destruct (0 <? c) eqn:C; [|discriminate]. apply Z.ltb_lt in C. inversion Hp; subst. cbn [P.dz].
rewrite (lit_of_sound R V p2 c L). pose proof (Z.mod_pos_bound (P.dz R V p1) c C). lia.
- destruct (lit_of (P.ZPow p1 p2)) as [c|] eqn:L.
+ pose proof (lit_of_sound R V _ c L) as X. inversion Hp; subst. lia.
+ destruct (lit_of p1) as [c|] eqn:L1; [|discriminate].
destruct (1 <=? c) eqn:C; [|discriminate]. apply Z.leb_le in C. ob_destr Hp. cbn [fst snd] in Hp.
match type of Hp with context [(0 <=? ?x) && (?y <=? 128)] => destruct ((0 <=? x) && (y <=? 128)) eqn:S; [|discriminate] end.
apply andb_prop in S. destruct S as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2. inversion Hp; subst. cbn [P.dz].
rewrite (lit_of_sound R V p1 c L1). specialize (IHp2 _ _ eq_refl).
apply pow_iv; [lia | exact IHp2 | lia].
- ob_destr Hp.
match type of Hp with context [(0 <=? ?x) && (0 <=? ?y)] => destruct ((0 <=? x) && (0 <=? y)) eqn:S; [|discriminate] end.
apply andb_prop in S. destruct S as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2. inversion Hp; subst. cbn [P.dz].
specialize (IHp1 _ _ eq_refl). specialize (IHp2 _ _ eq_refl). cbn [fst snd] in *.
split. apply Z.land_nonneg; lia.
apply Z.min_glb. eapply Z.le_trans. apply land_le_l'; lia. lia. eapply Z.le_trans. apply L5K.land_le_r; lia. lia.
- discriminate.
- discriminate.
- inversion Hp; subst. cbn [P.dz]. destruct (P.dz R V p1 <? P.dz R V p2); lia.
- discriminate.
- discriminate.
Qed.
Definition inrO (o : option ivl) : bool := match o with Some i => inr i | None => false end.
Definition isMM (o : option Z) : bool := match o with Some z => Z.eqb z MM | None => false end.
Definition isZ (o : option Z) (c : Z) : bool := match o with Some z => Z.eqb z c | None => false end.
Definition isP2_64 (q : P.zx) : bool := isMM (lit_of q).
Definition env_ok (vl : nat -> bool) (W : nat -> Z) (V : nat -> Z) (R : bvmap 5 word) : Prop :=
forall n, (vl n = true -> W n = V n /\ 0 <= V n < MM) /\ (vl n = false -> W n = bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat n)))).
Fixpoint zm (vl : nat -> bool) (bd : P.zx -> option ivl) (b : bool) (p : P.zx) (t : BL.za) {struct t} : bool :=
let rng := inrO (iv bd p) in
match t with
| BL.ZV m => match p with P.ZV n => Nat.eqb n m && vl n | P.ZR k => Nat.eqb k m && negb (vl k) | _ => false end
| BL.ZL z' => match p with P.ZL z => if b then Z.eqb z z' else Z.eqb (z mod MM) z' | _ => false end
| BL.ZAddM a' c' => match p with
| P.ZAdd a c => zm vl bd false a a' && zm vl bd false c c' && (negb b || rng)
| P.ZSub a c =>
((match c with P.ZL k => match c' with BL.ZL k' => Z.eqb k' ((- k) mod MM) | _ => false end | _ => false end)
|| zm vl bd false (P.ZMul (P.ZL (MM - 1)) c) c')
&& zm vl bd false a a' && (negb b || rng)
| P.ZMod (P.ZAdd a c) mm => isP2_64 mm && zm vl bd false a a' && zm vl bd false c c'
| _ => false end
| BL.ZSubM a' c' => match p with
| P.ZSub a c => zm vl bd false a a' && zm vl bd false c c' && (negb b || rng)
| P.ZMod (P.ZSub a c) mm => isP2_64 mm && zm vl bd false a a' && zm vl bd false c c'
| _ => false end
| BL.ZMulM a' c' => match p with
| P.ZMul a c => zm vl bd false a a' && zm vl bd false c c' && (negb b || rng)
| P.ZMod (P.ZMul a c) mm => isP2_64 mm && zm vl bd false a a' && zm vl bd false c c'
| _ => false end
| BL.ZMulHU a' c' => match p with P.ZDiv (P.ZMul a c) mm => isP2_64 mm && zm vl bd true a a' && zm vl bd true c c' && (b || rng) | _ => false end
| BL.ZDivC a' c => match p with
| P.ZDiv (P.ZMod a mm) q => (isP2_64 mm && isZ (lit_of q) c && zm vl bd false a a'
|| isZ (lit_of q) c && zm vl bd true (P.ZMod a mm) a') && (b || rng)
| P.ZDiv a q => isZ (lit_of q) c && zm vl bd true a a' && (b || rng)
| _ => false end
| BL.ZShlC a' c => match p with P.ZMod (P.ZMul a q) mm => isP2_64 mm && isZ (lit_of q) c && zm vl bd false a a' | _ => false end
| BL.ZSrl a' c' => match p with
| P.ZDiv a (P.ZPow (P.ZL 2) (P.ZMod c q)) => isZ (lit_of q) 64 && zm vl bd true a a' && zm vl bd true c c' && (b || rng)
| _ => false end
| BL.ZSll a' c' => match p with
| P.ZMod (P.ZMul a (P.ZPow (P.ZL 2) (P.ZMod c q))) mm => isP2_64 mm && isZ (lit_of q) 64 && zm vl bd false a a' && zm vl bd true c c'
| _ => false end
| BL.ZLtu a' c' => match p with P.ZLtbIf a c => zm vl bd true a a' && zm vl bd true c c' | _ => false end
| BL.ZAnd a' c' => match p with P.ZLand a c => zm vl bd true a a' && zm vl bd true c c' && (b || rng) | _ => false end
| BL.ZOr a' c' => match p with P.ZLor a c => zm vl bd true a a' && zm vl bd true c c' && (b || rng) | _ => false end
| BL.ZXor a' c' => match p with P.ZLxor a c => zm vl bd true a a' && zm vl bd true c c' && (b || rng) | _ => false end
| BL.ZDivU a' c' => match p with P.ZDivu a c => zm vl bd true a a' && zm vl bd true c c' && (b || rng) | _ => false end
| BL.ZRemU a' c' => match p with P.ZRemu a c => zm vl bd true a a' && zm vl bd true c c' && (b || rng) | _ => false end
end.
Lemma isP2_64_sound R V q : isP2_64 q = true -> P.dz R V q = MM.
Proof. unfold isP2_64, isMM. destruct (lit_of q) as [z|] eqn:L; [|discriminate]. intros H. apply Z.eqb_eq in H. subst. apply (lit_of_sound R V q _ L). Qed.
Lemma isZ_sound R V q c : isZ (lit_of q) c = true -> P.dz R V q = c.
Proof. unfold isZ. destruct (lit_of q) as [z|] eqn:L; [|discriminate]. intros H. apply Z.eqb_eq in H. subst. apply (lit_of_sound R V q _ L). Qed.
Lemma inrO_sound bd V R p : bd_ok bd R V -> inrO (iv bd p) = true -> 0 <= P.dz R V p < MM.
Proof.
intros HB. unfold inrO. destruct (iv bd p) as [[l h]|] eqn:E; [|discriminate]. unfold inr. cbn [fst snd]. intros H.
apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. pose proof (iv_sound bd V R HB p l h E). lia.
Qed.
Ltac andb_all := repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
Definition zsem (R : bvmap 5 word) (V : nat -> Z) (W : nat -> Z) (b : bool) (p : P.zx) (t : BL.za) : Prop :=
if b then P.dz R V p = BL.zden W t else P.dz R V p mod MM = BL.zden W t.
Lemma zsem_mod R V W b p t : zsem R V W b p t -> P.dz R V p mod MM = BL.zden W t mod MM.
Proof. unfold zsem. destruct b; intros H. rewrite H. reflexivity. rewrite <- H. rewrite Zmod_mod. reflexivity. Qed.
Lemma zsem_of_exact R V W b p t : 0 <= P.dz R V p < MM -> P.dz R V p = BL.zden W t -> zsem R V W b p t.
Proof. unfold zsem. destruct b; intros Hr H. exact H. rewrite Z.mod_small by exact Hr. exact H. Qed.
Lemma zsem_of_mod R V W b p t : (b = true -> 0 <= P.dz R V p < MM) -> P.dz R V p mod MM = BL.zden W t -> zsem R V W b p t.
Proof. unfold zsem. destruct b; intros Hr H. rewrite <- H. symmetry. apply Z.mod_small. apply Hr; reflexivity. exact H. Qed.
Ltac pr_facts R V HB :=
repeat match goal with
| H : isP2_64 ?q = true |- _ => rewrite (isP2_64_sound R V q H) in *; clear H
| H : isZ (lit_of ?q) ?c = true |- _ => rewrite (isZ_sound R V q c H) in *; clear H
| H : inrO (iv ?bd ?p) = true |- _ => pose proof (inrO_sound bd V R p HB H); clear H
end.
Ltac ih_all :=
repeat match goal with
| H : zm ?vl ?bd ?b ?q ?t = true, IH : forall (b0 : bool) (p0 : P.zx), zm ?vl ?bd b0 p0 ?t = true -> zsem _ _ _ b0 p0 ?t |- _ =>
let Z := fresh "Z" in pose proof (IH _ _ H) as Z; clear H; unfold zsem in Z; cbv iota in Z
end.
Ltac mode_facts :=
repeat match goal with
| H : (negb ?b || ?x) = true |- _ => destruct b; cbn [negb orb] in H; [|clear H]
| H : (?b || ?x) = true |- _ => destruct b; cbn [orb] in H; [clear H|]
end.
Ltac rw_z :=
repeat match goal with
| Zh : P.dz _ _ ?q mod MM = BL.zden _ ?t |- _ => rewrite <- Zh in *; clear Zh
| Zh : P.dz _ _ ?q = BL.zden _ ?t |- _ => rewrite <- Zh in *; clear Zh
end.
Ltac fin_exact R V HB Hx :=
match goal with bb : bool |- _ =>
destruct bb; [unfold zsem; exact Hx |
cbn [orb] in *; try discriminate; pr_facts R V HB; apply zsem_of_exact; [assumption | exact Hx]] end.
Lemma zm_sound vl bd W V R : env_ok vl W V R -> bd_ok bd R V -> forall t b p, zm vl bd b p t = true -> zsem R V W b p t.
Proof.
intros HE HB. induction t; intros bb p Hm; cbn [zm] in Hm.
- destruct p; try discriminate; andb_all.
+ apply Nat.eqb_eq in H. subst. destruct (proj1 (HE n) H0) as [Hw Hr]. apply zsem_of_exact. cbn [P.dz]. exact Hr.
cbn [P.dz BL.zden]. rewrite Hw. reflexivity.
+ apply Nat.eqb_eq in H. subst. apply negb_true_iff in H0. apply zsem_of_exact. cbn [P.dz]. apply BL.bvu_range.
cbn [P.dz BL.zden]. rewrite (proj2 (HE n) H0). reflexivity.
- destruct p; try discriminate. unfold zsem. cbn [P.dz BL.zden]. destruct bb; apply Z.eqb_eq in Hm; exact Hm.
- destruct p; try discriminate.
+ andb_all. ih_all. mode_facts; pr_facts R V HB; [apply zsem_of_mod; [intros _; assumption|] | apply zsem_of_mod; [discriminate|]];
cbn [P.dz BL.zden] in *; rewrite Zplus_mod; rewrite <- Z, <- Z0; reflexivity.
+ andb_all. apply orb_prop in H. ih_all.
assert (Hm0 : (P.dz R V p1 - P.dz R V p2) mod MM = BL.zden W (BL.ZAddM t1 t2)).
{ cbn [BL.zden]. destruct H as [H|Z1].
- destruct p2; try discriminate. destruct t2; try discriminate. apply Z.eqb_eq in H. subst. cbn [P.dz BL.zden].
rewrite <- Z, <- Zplus_mod. reflexivity.
- ih_all. cbn [P.dz] in *. rewrite <- Z, <- Z0, <- Zplus_mod.
replace (P.dz R V p1 + (MM - 1) * P.dz R V p2) with ((P.dz R V p1 - P.dz R V p2) + P.dz R V p2 * MM) by lia.
rewrite Z_mod_plus_full. reflexivity. }
mode_facts; pr_facts R V HB; apply zsem_of_mod; try (intros _; assumption); try discriminate; exact Hm0.
+ destruct p1; try discriminate. andb_all. ih_all. apply zsem_of_exact; cbn [P.dz BL.zden]; pr_facts R V HB.
* apply Z.mod_pos_bound. reflexivity.
* rw_z. rewrite <- Zplus_mod. reflexivity.
- destruct p; try discriminate.
+ andb_all. ih_all. mode_facts; pr_facts R V HB; [apply zsem_of_mod; [intros _; assumption|] | apply zsem_of_mod; [discriminate|]];
cbn [P.dz BL.zden] in *; rewrite Zminus_mod; rewrite <- Z, <- Z0; reflexivity.
+ destruct p1; try discriminate. andb_all. ih_all. apply zsem_of_exact; cbn [P.dz BL.zden]; pr_facts R V HB.
* apply Z.mod_pos_bound. reflexivity.
* rw_z. rewrite <- Zminus_mod. reflexivity.
- destruct p; try discriminate.
+ andb_all. ih_all. mode_facts; pr_facts R V HB; [apply zsem_of_mod; [intros _; assumption|] | apply zsem_of_mod; [discriminate|]];
cbn [P.dz BL.zden] in *; rewrite Zmult_mod; rewrite <- Z, <- Z0; reflexivity.
+ destruct p1; try discriminate. andb_all. ih_all. apply zsem_of_exact; cbn [P.dz BL.zden]; pr_facts R V HB.
* apply Z.mod_pos_bound. reflexivity.
* rw_z. rewrite <- Zmult_mod. reflexivity.
- destruct p; try discriminate. destruct p1; try discriminate. andb_all. ih_all.
assert (Hx : P.dz R V (P.ZDiv (P.ZMul p1_1 p1_2) p2) = BL.zden W (BL.ZMulHU t1 t2)).
{ cbn [P.dz BL.zden]. pr_facts R V HB. rewrite Z, Z0. reflexivity. }
fin_exact R V HB Hx.
- destruct p; try discriminate. destruct p1; andb_all; ih_all.
all: try (match goal with |- zsem _ _ _ _ ?p ?t => assert (Hx : P.dz R V p = BL.zden W t) end;
[cbn [P.dz BL.zden]; pr_facts R V HB; rw_z; reflexivity | fin_exact R V HB Hx]).
match goal with H : ((_ && _) || (_ && _)) = true |- _ => apply orb_prop in H; destruct H as [H|H] end; andb_all; ih_all.
+ assert (Hx : P.dz R V (P.ZDiv (P.ZMod p1_1 p1_2) p2) = BL.zden W (BL.ZDivC t c))
by (cbn [P.dz BL.zden]; pr_facts R V HB; rw_z; reflexivity). fin_exact R V HB Hx.
+ assert (Hx : P.dz R V (P.ZDiv (P.ZMod p1_1 p1_2) p2) = BL.zden W (BL.ZDivC t c))
by (cbn [P.dz BL.zden]; pr_facts R V HB; rw_z; reflexivity). fin_exact R V HB Hx.
- destruct p; try discriminate. destruct p1; try discriminate. andb_all. ih_all.
apply zsem_of_exact; cbn [P.dz BL.zden]; pr_facts R V HB.
+ apply Z.mod_pos_bound. reflexivity.
+ rw_z. rewrite Zmult_mod_idemp_l. reflexivity.
- destruct p; try discriminate. destruct p2; try discriminate. destruct p2_1; try discriminate.
destruct z as [|[q|q|]|]; try discriminate. destruct q as [q|q|]; try discriminate.
destruct p2_2; try discriminate. andb_all. ih_all.
assert (Hx : P.dz R V (P.ZDiv p1 (P.ZPow (P.ZL 2) (P.ZMod p2_2_1 p2_2_2))) = BL.zden W (BL.ZSrl t1 t2))
by (cbn [P.dz BL.zden]; pr_facts R V HB; rw_z; reflexivity). fin_exact R V HB Hx.
- destruct p; try discriminate. destruct p1; try discriminate. destruct p1_2; try discriminate. destruct p1_2_1; try discriminate.
destruct z as [|[q|q|]|]; try discriminate. destruct q as [q|q|]; try discriminate.
destruct p1_2_2; try discriminate. andb_all. ih_all.
apply zsem_of_exact; cbn [P.dz BL.zden]; pr_facts R V HB.
+ apply Z.mod_pos_bound. reflexivity.
+ rw_z. rewrite Zmult_mod_idemp_l. reflexivity.
- destruct p; try discriminate. andb_all. ih_all.
assert (Hx : P.dz R V (P.ZLtbIf p1 p2) = BL.zden W (BL.ZLtu t1 t2)) by (cbn [P.dz BL.zden]; rw_z; reflexivity).
apply zsem_of_exact; [|exact Hx]. cbn [P.dz]. destruct (P.dz R V p1 <? P.dz R V p2); unfold MM, BL.MM; lia.
- destruct p; try discriminate. andb_all. ih_all.
assert (Hx : P.dz R V (P.ZLand p1 p2) = BL.zden W (BL.ZAnd t1 t2)) by (cbn [P.dz BL.zden]; rw_z; reflexivity). fin_exact R V HB Hx.
- destruct p; try discriminate. andb_all. ih_all.
assert (Hx : P.dz R V (P.ZLor p1 p2) = BL.zden W (BL.ZOr t1 t2)) by (cbn [P.dz BL.zden]; rw_z; reflexivity). fin_exact R V HB Hx.
- destruct p; try discriminate. andb_all. ih_all.
assert (Hx : P.dz R V (P.ZLxor p1 p2) = BL.zden W (BL.ZXor t1 t2)) by (cbn [P.dz BL.zden]; rw_z; reflexivity). fin_exact R V HB Hx.
- destruct p; try discriminate. andb_all. ih_all.
assert (Hx : P.dz R V (P.ZDivu p1 p2) = BL.zden W (BL.ZDivU t1 t2)) by (cbn [P.dz BL.zden]; rw_z; reflexivity). fin_exact R V HB Hx.
- destruct p; try discriminate. andb_all. ih_all.
assert (Hx : P.dz R V (P.ZRemu p1 p2) = BL.zden W (BL.ZRemU t1 t2)) by (cbn [P.dz BL.zden]; rw_z; reflexivity). fin_exact R V HB Hx.
Qed.
Definition is_rng (n : nat) (h : P.px) : bool :=
match h with P.PLeLt (P.ZL Z0) (P.ZV m) q => Nat.eqb n m && isP2_64 q | _ => false end.
Definition vl_of (hs : list P.px) (n : nat) : bool := existsb (is_rng n) hs.
Definition meet (acc : option ivl) (i : ivl) : option ivl :=
match acc with None => Some i | Some j => Some (Z.max (fst i) (fst j), Z.min (snd i) (snd j)) end.
Definition ref1 (p : P.zx) (acc : option ivl) (h : P.px) : option ivl :=
match h with
| P.PLeLe q1 q q2 => if zx_eqb q p then match lit_of q1, lit_of q2 with Some lo, Some hi => meet acc (lo, hi) | _, _ => acc end else acc
| P.PLeLt q1 q q2 => if zx_eqb q p then match lit_of q1, lit_of q2 with Some lo, Some hi => meet acc (lo, hi - 1) | _, _ => acc end else acc
| _ => acc
end.
Definition bd_of (hs : list P.px) (p : P.zx) : option ivl := fold_left (ref1 p) hs None.
Definition mkE (vl : nat -> bool) (V : nat -> Z) (R : bvmap 5 word) : env :=
Env (fun j => if vl j then Z_to_bv 64 (V j) else getr R (Z_to_bv 5 (Z.of_nat j))) (fun _ => []).
Section Prem.
Variable segs : list Segment.
Variable al : Z -> Z -> Prop.
Variable sr : Z -> Z -> Z -> Z -> Prop.
Variable za : (word -> option byte) -> Z -> Z -> Prop.
Variable ks : list (list nat).
Variable fx : FPState.
Variable R : bvmap 5 word.
Variable M : word -> option byte.
Variable V : nat -> Z.
Definition Hp (h : P.px) : Prop := P.dp segs al sr za ks fx R M V fx R M h.
Lemma dhyps_intro hs C : (Forall Hp hs -> C) -> P.dhyps segs al sr za ks fx R M V hs C.
Proof.
induction hs as [|h t IH]; cbn [P.dhyps]; intros H. apply H; constructor.
intros Hh. apply IH. intros Ht. apply H. constructor; assumption.
Qed.
Lemma rng_of hs n : Forall Hp hs -> vl_of hs n = true -> 0 <= V n < MM.
Proof.
intros HF Hv. unfold vl_of in Hv. apply existsb_exists in Hv. destruct Hv as [h [Hin Hr]].
rewrite Forall_forall in HF. specialize (HF h Hin). unfold Hp in HF.
destruct h; try discriminate. destruct a; try discriminate. destruct z; try discriminate. destruct b; try discriminate.
apply andb_prop in Hr. destruct Hr as [H1 H2]. apply Nat.eqb_eq in H1. subst.
cbn [P.dp P.dz] in HF. rewrite (isP2_64_sound R V c H2) in HF. exact HF.
Qed.
Lemma fold_ref1_ok hs p : Forall Hp hs -> forall acc, (forall l h, acc = Some (l, h) -> l <= P.dz R V p <= h) ->
forall l h, fold_left (ref1 p) hs acc = Some (l, h) -> l <= P.dz R V p <= h.
Proof.
induction hs as [|x t IH]; intros HF acc Ha; cbn [fold_left]. exact Ha.
inversion HF; subst. apply IH. assumption. intros l h E. unfold ref1 in E.
unfold Hp in H1. destruct x; try (apply Ha; exact E).
- destruct (zx_eqb b p) eqn:Q; [|apply Ha; exact E]. apply zx_eqb_eq in Q. subst b.
destruct (lit_of a) as [lo|] eqn:L1; [|apply Ha; exact E]. destruct (lit_of c) as [hi|] eqn:L2; [|apply Ha; exact E].
cbn [P.dp] in H1. rewrite (lit_of_sound R V a lo L1), (lit_of_sound R V c hi L2) in H1.
unfold meet in E. destruct acc as [[l0 h0]|]; inversion E; subst; cbn [fst snd]; [pose proof (Ha _ _ eq_refl) |]; lia.
- destruct (zx_eqb b p) eqn:Q; [|apply Ha; exact E]. apply zx_eqb_eq in Q. subst b.
destruct (lit_of a) as [lo|] eqn:L1; [|apply Ha; exact E]. destruct (lit_of c) as [hi|] eqn:L2; [|apply Ha; exact E].
cbn [P.dp] in H1. rewrite (lit_of_sound R V a lo L1), (lit_of_sound R V c hi L2) in H1.
unfold meet in E. destruct acc as [[l0 h0]|]; inversion E; subst; cbn [fst snd]; [pose proof (Ha _ _ eq_refl) |]; lia.
Qed.
Lemma bd_of_ok hs : Forall Hp hs -> bd_ok (bd_of hs) R V.
Proof. intros HF p l h Hb. unfold bd_of in Hb. eapply fold_ref1_ok; [exact HF | | exact Hb]. intros l0 h0 E; discriminate. Qed.
Lemma env_ok_mkE hs : Forall Hp hs -> env_ok (vl_of hs) (BL.uv (mkE (vl_of hs) V R)) V R.
Proof.
intros HF n. unfold BL.uv, mkE. cbn [ev]. split; intros Hv; rewrite Hv.
- pose proof (rng_of hs n HF Hv) as X. split; [|exact X]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with MM. apply Z.mod_small. exact X.
- reflexivity.
Qed.
End Prem.
Definition zmE (vl : nat -> bool) (bd : P.zx -> option ivl) (p : P.zx) (e : expr) : bool :=
match BL.zcomp e with Some t => zm vl bd true p t | None => false end.
Lemma zmE_sound vl bd V R E p e : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> zmE vl bd p e = true -> bv_unsigned (edenot E e) = P.dz R V p.
Proof.
unfold zmE. destruct (BL.zcomp e) as [t|] eqn:C; [|discriminate]. intros HE HB H.
rewrite (BL.zcomp_sound E e t C). symmetry. exact (zm_sound vl bd (BL.uv E) V R HE HB t true p H).
Qed.
Definition zmW (vl : nat -> bool) (bd : P.zx -> option ivl) (p : P.zx) (e : expr) : bool :=
match BL.zcomp e with Some t => zm vl bd false p t | None => false end.
Lemma Z_to_bv_mod64 z : Z_to_bv 64 (z mod MM) = Z_to_bv 64 z.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with MM. apply Zmod_mod. Qed.
Lemma zmW_sound vl bd V R E p e : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> zmW vl bd p e = true -> edenot E e = Z_to_bv 64 (P.dz R V p).
Proof.
unfold zmW. destruct (BL.zcomp e) as [t|] eqn:C; [|discriminate]. intros HE HB H.
pose proof (zm_sound vl bd (BL.uv E) V R HE HB t false p H) as Z. unfold zsem in Z. cbv iota in Z.
rewrite <- Z_to_bv_mod64, Z. rewrite <- (BL.zcomp_sound E e t C). apply BG.word_of_unsigned. reflexivity.
Qed.
Definition addr_ok vl bd (pa : P.zx) (b : expr) (off : Z) : bool :=
(match pa with
| P.ZAdd pb (P.ZL k) => Z.eqb k off && zmE vl bd pb b
| P.ZSub pb (P.ZL k) => Z.eqb (- k) off && zmE vl bd pb b
| P.ZL k => Z.eqb k off && (match b with ELit z => Z.eqb z 0 | _ => false end)
| _ => false end) || (Z.eqb off 0 && zmE vl bd pa b).
Lemma addr_ok_sound vl bd V R E pa b off : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> addr_ok vl bd pa b off = true ->
bv_unsigned (edenot E b) + off = P.dz R V pa.
Proof.
intros HE HB H. unfold addr_ok in H. apply orb_prop in H. destruct H as [H|H].
- destruct pa; try discriminate.
+ apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst. cbn [P.dz]. destruct b; try discriminate.
apply Z.eqb_eq in H2. subst. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity.
+ destruct pa2; try discriminate. apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst. cbn [P.dz].
rewrite (zmE_sound vl bd V R E pa1 b HE HB H2). reflexivity.
+ destruct pa2; try discriminate. apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst. cbn [P.dz].
rewrite (zmE_sound vl bd V R E pa1 b HE HB H2). lia.
- apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst. rewrite (zmE_sound vl bd V R E pa b HE HB H2). lia.
Qed.
Definition rng_an (ia inn : option ivl) : bool :=
match ia, inn with Some (la, ha), Some (ln, hn) => (0 <=? la) && (0 <? ln) && (ha + hn <=? MM) | _, _ => false end.
Definition rng_aw (ia : option ivl) (w : Z) : bool :=
match ia with Some (la, ha) => (0 <=? la) && (ha + w <=? MM) | None => false end.
Definition rng_byte (iv0 : option ivl) : bool :=
match iv0 with Some (l, h) => (0 <=? l) && (h <? 256) | None => false end.
Lemma rng_an_sound bd V R pa pn : bd_ok bd R V -> rng_an (iv bd pa) (iv bd pn) = true ->
0 <= P.dz R V pa /\ 0 < P.dz R V pn /\ P.dz R V pa + P.dz R V pn <= MM.
Proof.
intros HB. unfold rng_an. destruct (iv bd pa) as [[la ha]|] eqn:E1; [|discriminate]. destruct (iv bd pn) as [[ln hn]|] eqn:E2; [|discriminate].
intros H. andb_all. apply Z.leb_le in H. apply Z.ltb_lt in H1. apply Z.leb_le in H0.
pose proof (iv_sound bd V R HB pa la ha E1). pose proof (iv_sound bd V R HB pn ln hn E2). lia.
Qed.
Lemma rng_aw_sound bd V R pa w : bd_ok bd R V -> rng_aw (iv bd pa) w = true -> 0 <= P.dz R V pa /\ P.dz R V pa + w <= MM.
Proof.
intros HB. unfold rng_aw. destruct (iv bd pa) as [[la ha]|] eqn:E1; [|discriminate].
intros H. andb_all. apply Z.leb_le in H. apply Z.leb_le in H0. pose proof (iv_sound bd V R HB pa la ha E1). lia.
Qed.
Lemma rng_byte_sound bd V R p : bd_ok bd R V -> rng_byte (iv bd p) = true -> 0 <= P.dz R V p < 256.
Proof.
intros HB. unfold rng_byte. destruct (iv bd p) as [[l h]|] eqn:E1; [|discriminate].
intros H. andb_all. apply Z.leb_le in H. apply Z.ltb_lt in H0. pose proof (iv_sound bd V R HB p l h E1). lia.
Qed.
Definition is_sltu (e : expr) : option (expr * expr) := match e with EAlu ALU_SLTU x y => Some (x, y) | _ => None end.
Definition tbchk (m k : Z) (bt : bool) (lo : Z) : bool :=
((Z.eqb m 1 && Z.eqb k 0) || (Z.eqb m 2 && Z.eqb k 1)) && Z.eqb lo (if bt then m else 0).
Lemma tbchk_m m k bt lo : tbchk m k bt lo = true -> 0 <= m < 2 ^ 64.
Proof.
unfold tbchk. intros H. apply andb_prop in H. destruct H as [H _]. apply orb_prop in H.
destruct H as [H|H]; apply andb_prop in H; destruct H as [H _]; apply Z.eqb_eq in H; subst m; lia.
Qed.
Lemma tb_land_entry v m k bt lo : 0 <= v -> tbchk m k bt lo = true -> Z.testbit v k = bt -> Z.land v m = lo.
Proof.
intros Hv H Ht. unfold tbchk in H. apply andb_prop in H. destruct H as [H Hl]. apply Z.eqb_eq in Hl. subst lo.
apply orb_prop in H. destruct H as [H|H]; apply andb_prop in H; destruct H as [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_eq in H2;
subst m k; destruct bt.
- apply L5K.land1_bit0_true; assumption.
- apply L5K.land1_bit0_false; assumption.
- apply L5K.land2_bit1_true; assumption.
- apply L5K.land2_bit1_false; assumption.
Qed.
Lemma tb_land_exit v m k bt lo : tbchk m k bt lo = true -> Z.land v m = lo -> Z.testbit v k = bt.
Proof.
intros H Hl. unfold tbchk in H. apply andb_prop in H. destruct H as [H Hlo]. apply Z.eqb_eq in Hlo. subst lo.
apply orb_prop in H. destruct H as [H|H]; apply andb_prop in H; destruct H as [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_eq in H2; subst m k.
- replace (Z.testbit v 0) with (Z.testbit (Z.land v 1) 0)
by (rewrite Z.land_spec; change (Z.testbit 1 0) with true; apply andb_true_r).
rewrite Hl. destruct bt; reflexivity.
- replace (Z.testbit v 1) with (Z.testbit (Z.land v 2) 1)
by (rewrite Z.land_spec; change (Z.testbit 2 1) with true; apply andb_true_r).
rewrite Hl. destruct bt; reflexivity.
Qed.
Lemma kr_tb_entry segs E M x m lo hi k bt v : bv_unsigned (edenot E x) = v -> lo = hi -> tbchk m k bt lo = true -> Z.testbit v k = bt ->
kentry_ok segs E M (KRange (EAlu ALU_AND x (ELit m)) lo hi).
Proof.
intros Hv Hlh Hc Ht. subst hi.
assert (Hv0 : 0 <= v) by (pose proof (BL.bvu_range (edenot E x)) as X; unfold BL.inrange in X; lia).
eapply L5K.kentry_KRange_andlit; [exact Hv | exact (tbchk_m m k bt lo Hc) | ].
rewrite (tb_land_entry v m k bt lo Hv0 Hc Ht). lia.
Qed.
Lemma kr_tb_exit segs E M x m lo hi k bt v : kentry_ok segs E M (KRange (EAlu ALU_AND x (ELit m)) lo hi) ->
bv_unsigned (edenot E x) = v -> lo = hi -> tbchk m k bt lo = true -> Z.testbit v k = bt.
Proof.
intros HK Hv Hlh Hc. subst hi. cbn [kentry_ok edenot] in HK. rewrite L5K.and_lit_val in HK by exact (tbchk_m m k bt lo Hc).
rewrite Hv in HK. apply (tb_land_exit v m k bt lo Hc). lia.
Qed.
Definition krchk vl bd (e : expr) (lo hi : Z) (h : P.px) : bool :=
match h with
| P.PLeLe q1 p q2 => isZ (lit_of q1) lo && isZ (lit_of q2) hi && zmE vl bd p e
| P.PLt a b => match is_sltu e with Some (x, y) => Z.eqb lo 1 && Z.eqb hi 1 && zmE vl bd a x && zmE vl bd b y | None => false end
| P.PLe b a => match is_sltu e with Some (x, y) => Z.eqb lo 0 && Z.eqb hi 0 && zmE vl bd a x && zmE vl bd b y | None => false end
| P.PTestbit p k bt => match e with EAlu ALU_AND x (ELit m) => Z.eqb lo hi && tbchk m k bt lo && zmE vl bd p x | _ => false end
| _ => false
end.
Definition kchk vl bd (K : kentry) (h : P.px) : bool :=
match K, h with
| KRange e lo hi, _ => krchk vl bd e lo hi h
| KAlign e m, P.PAligned p q => isZ (lit_of q) m && (0 <? m) && zmE vl bd p e
| KWr (SA b off) ne, P.PWr pa pn => addr_ok vl bd pa b off && zmE vl bd pn ne && rng_an (iv bd pa) (iv bd pn)
| KUnk (SA b off) ne, P.PDef P.MM0 pa pn => addr_ok vl bd pa b off && zmE vl bd pn ne && rng_an (iv bd pa) (iv bd pn)
| KZero (SA b off) ne, P.PZero P.MM0 pa pn => addr_ok vl bd pa b off && zmE vl bd pn ne && rng_an (iv bd pa) (iv bd pn)
| KWord (SA b off) w v, P.PU64 P.MM0 pa pv => Nat.eqb w 8 && addr_ok vl bd pa b off && zmE vl bd pv v && rng_aw (iv bd pa) 8
| KWord (SA b off) w v, P.PU32 P.MM0 pa pv => Nat.eqb w 4 && addr_ok vl bd pa b off && zmE vl bd pv v && rng_aw (iv bd pa) 4
| KWord (SA b off) w v, P.PU8 P.MM0 pa pv => Nat.eqb w 1 && addr_ok vl bd pa b off && zmE vl bd pv v && rng_aw (iv bd pa) 1
&& rng_byte (iv bd pv)
| KDisj (SA b1 o1) n1 (SA b2 o2) n2, P.PDisj pa1 pn1 pa2 pn2 =>
addr_ok vl bd pa1 b1 o1 && zmE vl bd pn1 n1 && addr_ok vl bd pa2 b2 o2 && zmE vl bd pn2 n2
| KImg lo hi, P.PImg q1 q2 => isZ (lit_of q1) lo && isZ (lit_of q2) hi && (0 <=? lo) && (hi <=? MM)
| _, _ => false
end.
Lemma sltu_val E x y : bv_unsigned (edenot E (EAlu ALU_SLTU x y)) = if bv_unsigned (edenot E x) <? bv_unsigned (edenot E y) then 1 else 0.
Proof. cbn [edenot]. apply BL.zalu_sound. reflexivity. Qed.
Ltac pr_entry vl bd V R E HE HB :=
repeat match goal with
| H : addr_ok vl bd ?pa ?b ?off = true |- _ => pose proof (addr_ok_sound vl bd V R E pa b off HE HB H); clear H
| H : zmE vl bd ?p ?e = true |- _ => pose proof (zmE_sound vl bd V R E p e HE HB H); clear H
| H : rng_an (iv bd ?pa) (iv bd ?pn) = true |- _ => pose proof (rng_an_sound bd V R pa pn HB H); clear H
| H : rng_aw (iv bd ?pa) ?w = true |- _ => pose proof (rng_aw_sound bd V R pa w HB H); clear H
| H : rng_byte (iv bd ?p) = true |- _ => pose proof (rng_byte_sound bd V R p HB H); clear H
| H : isZ (lit_of ?q) ?c = true |- _ => pose proof (isZ_sound R V q c H); clear H
| H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
end.
Ltac nums := repeat (rewrite BL.MM_val in * ); try change (2 ^ 64) with 18446744073709551616 in *.
Section Entry.
Variable segs : list Segment.
Variable al : Z -> Z -> Prop.
Variable sr : Z -> Z -> Z -> Z -> Prop.
Variable za : (word -> option byte) -> Z -> Z -> Prop.
Hypothesis AL : forall a m, al a m -> a mod m = 0.
Hypothesis ZA : forall Mx a n, za Mx a n -> forall i, 0 <= i < n -> Mx (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
Variable ks : list (list nat).
Variable fx : FPState.
Variable R : bvmap 5 word.
Variable M : word -> option byte.
Variable V : nat -> Z.
Lemma kchk_sound vl bd E K h : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> kchk vl bd K h = true ->
Hp segs al sr za ks fx R M V h -> kentry_ok segs E M K.
Proof.
intros HE HB Hk Hh. unfold Hp in Hh.
destruct K; try discriminate; cbn [kchk] in Hk.
- match goal with |- kentry_ok _ _ _ (_ ?sa _) => destruct sa as [b off] | |- kentry_ok _ _ _ (_ ?sa _ _) => destruct sa as [b off] end. destruct h; try discriminate; destruct m; try discriminate; andb_all;
pr_entry vl bd V R E HE HB; subst; cbn [P.dp P.msel_of] in Hh; nums.
+ eapply L5K.kentry_KWord8; [reflexivity | eassumption | lia | lia | ].
match goal with A : bv_unsigned (edenot E b) + off = _ |- _ => rewrite A end. exact Hh.
+ eapply L5K.kentry_KWord4; [reflexivity | eassumption | lia | lia | ].
match goal with A : bv_unsigned (edenot E b) + off = _ |- _ => rewrite A end. exact Hh.
+ eapply L5K.kentry_KWord1; [reflexivity | eassumption | lia | lia | | ].
* assumption.
* match goal with A : bv_unsigned (edenot E b) + off = _ |- _ => rewrite A end. exact Hh.
- match goal with |- kentry_ok _ _ _ (_ ?sa _) => destruct sa as [b off] | |- kentry_ok _ _ _ (_ ?sa _ _) => destruct sa as [b off] end. destruct h; try discriminate; destruct m; try discriminate; andb_all.
pr_entry vl bd V R E HE HB. cbn [P.dp P.msel_of] in Hh. nums.
cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off].
match goal with A : bv_unsigned (edenot E b) + off = _ |- _ => rewrite A end.
match goal with N : bv_unsigned (edenot E ?x) = P.dz R V ?q, Hz : za M _ (P.dz R V ?q) |- _ => rewrite N end.
split. lia. intros i Hi. apply (ZA M _ _ Hh i Hi).
- destruct h; try discriminate. andb_all. pr_entry vl bd V R E HE HB. cbn [P.dp] in Hh.
repeat match goal with H : P.dz R V ?q = _ |- _ => rewrite H in Hh; clear H end.
eapply L5K.kentry_KImg; [assumption | assumption | exact Hh].
- destruct h; try discriminate. andb_all. pr_entry vl bd V R E HE HB. cbn [P.dp] in Hh.
match goal with H : P.dz R V ?q = _ |- _ => rewrite H in Hh end.
eapply L5K.kentry_KAlign; [eassumption | assumption | apply AL; exact Hh].
- unfold krchk in Hk. destruct h; try discriminate.
+ andb_all. pr_entry vl bd V R E HE HB. cbn [P.dp] in Hh.
cbn [kentry_ok]. repeat match goal with A : P.dz R V ?q = _ |- _ => rewrite A in Hh; clear A end.
match goal with A : bv_unsigned (edenot E e) = _ |- _ => rewrite A end. exact Hh.
+ destruct (is_sltu e) as [[x y]|] eqn:S; [|discriminate]. destruct e; try discriminate. destruct op; try discriminate.
inversion S; subst. andb_all. pr_entry vl bd V R E HE HB. subst. cbn [P.dp] in Hh.
cbn [kentry_ok]. rewrite sltu_val. repeat match goal with A : bv_unsigned (edenot E ?x) = _ |- _ => rewrite A; clear A end.
apply Z.ltb_lt in Hh. rewrite Hh. lia.
+ destruct (is_sltu e) as [[x y]|] eqn:S; [|discriminate]. destruct e; try discriminate. destruct op; try discriminate.
inversion S; subst. andb_all. pr_entry vl bd V R E HE HB. subst. cbn [P.dp] in Hh.
cbn [kentry_ok]. rewrite sltu_val. repeat match goal with A : bv_unsigned (edenot E ?x) = _ |- _ => rewrite A; clear A end.
apply Z.ltb_ge in Hh. rewrite Hh. lia.
+ destruct e as [ | | op x y | | | | | ]; try discriminate. destruct op; try discriminate. destruct y; try discriminate.
andb_all. pr_entry vl bd V R E HE HB. cbn [P.dp] in Hh.
eapply kr_tb_entry; [eassumption | eassumption | eassumption | exact Hh].
- match goal with |- kentry_ok _ _ _ (_ ?sa _) => destruct sa as [b off] | |- kentry_ok _ _ _ (_ ?sa _ _) => destruct sa as [b off] end. destruct h; try discriminate. andb_all.
pr_entry vl bd V R E HE HB. cbn [P.dp] in Hh. nums.
eapply L5K.kentry_KWr; [reflexivity | eassumption | lia | lia | lia | ].
match goal with A : bv_unsigned (edenot E b) + off = _ |- _ => rewrite A end. exact Hh.
- match goal with |- kentry_ok _ _ _ (KDisj ?s1 _ ?s2 _) => destruct s1 as [b1 o1]; destruct s2 as [b2 o2] end. destruct h; try discriminate. andb_all.
pr_entry vl bd V R E HE HB. cbn [P.dp] in Hh.
eapply L5K.kentry_KDisj; [reflexivity | eassumption | reflexivity | eassumption | ].
repeat match goal with A : bv_unsigned (edenot E ?b) + ?o = _ |- _ => rewrite A; clear A end. exact Hh.
- match goal with |- kentry_ok _ _ _ (_ ?sa _) => destruct sa as [b off] | |- kentry_ok _ _ _ (_ ?sa _ _) => destruct sa as [b off] end. destruct h; try discriminate; destruct m; try discriminate; andb_all.
pr_entry vl bd V R E HE HB. cbn [P.dp P.msel_of] in Hh. nums.
eapply L5K.kentry_KUnk; [reflexivity | eassumption | lia | lia | lia | ].
match goal with A : bv_unsigned (edenot E b) + off = _ |- _ => rewrite A end. exact Hh.
Qed.
Definition slot_chk vl bd (hs : list P.px) (e : expr) (i : nat) : bool :=
(match e with EVar j => Nat.eqb j i && negb (vl i) | _ => false end)
|| existsb (fun h => match h with P.PG k p => Nat.eqb k i && zmW vl bd p e | _ => false end) hs.
Fixpoint slots_chk vl bd hs (l : list expr) (i : nat) : bool :=
match l with [] => true | e :: t => slot_chk vl bd hs e i && slots_chk vl bd hs t (S i) end.
Lemma slots_chk_sound hs : Forall (Hp segs al sr za ks fx R M V) hs ->
forall l i, slots_chk (vl_of hs) (bd_of hs) hs l i = true -> BG.slots (mkE (vl_of hs) V R) R l i.
Proof.
intros HF. pose proof (env_ok_mkE segs al sr za ks fx R M V hs HF) as HE. pose proof (bd_of_ok segs al sr za ks fx R M V hs HF) as HB.
induction l as [|e t IH]; intros i Hs; cbn [slots_chk BG.slots] in *. exact I.
apply andb_prop in Hs. destruct Hs as [H1 H2]. split; [|apply IH; exact H2].
unfold slot_chk in H1. apply orb_prop in H1. destruct H1 as [H1|H1].
- destruct e; try discriminate. apply andb_prop in H1. destruct H1 as [H1 H3]. apply Nat.eqb_eq in H1. subst.
apply negb_true_iff in H3. cbn [edenot mkE ev]. rewrite H3. reflexivity.
- apply existsb_exists in H1. destruct H1 as [h [Hin Hh]]. destruct h; try discriminate.
apply andb_prop in Hh. destruct Hh as [H3 H4]. apply Nat.eqb_eq in H3. subst.
rewrite Forall_forall in HF. specialize (HF _ Hin). unfold Hp in HF. cbn [P.dp] in HF. rewrite HF.
symmetry. apply (zmW_sound (vl_of hs) (bd_of hs) V R _ _ _ HE HB H4).
Qed.
Definition echk (hs : list P.px) (regs0 : list expr) (kn0 : list kentry) : bool :=
(Nat.eqb (length regs0) 32) && slots_chk (vl_of hs) (bd_of hs) hs (tl regs0) 1
&& forallb (fun K => existsb (kchk (vl_of hs) (bd_of hs) K) hs) kn0.
Lemma entry_sound hs regs0 kn0 : echk hs regs0 kn0 = true -> Forall (Hp segs al sr za ks fx R M V) hs ->
regs_ok (mkE (vl_of hs) V R) regs0 R /\ know_ok segs (mkE (vl_of hs) V R) M kn0.
Proof.
intros Hc HF. unfold echk in Hc. andb_all.
pose proof (env_ok_mkE segs al sr za ks fx R M V hs HF) as HE. pose proof (bd_of_ok segs al sr za ks fx R M V hs HF) as HB.
split.
- apply BG.regs_ok_of_slots. apply Nat.eqb_eq. assumption. apply slots_chk_sound; assumption.
- unfold know_ok. rewrite Forall_forall. intros K HK. rewrite forallb_forall in H0. specialize (H0 K HK).
apply existsb_exists in H0. destruct H0 as [h [Hin Hk]]. rewrite Forall_forall in HF.
apply (kchk_sound (vl_of hs) (bd_of hs) _ K h HE HB Hk (HF h Hin)).
Qed.
End Entry.
Fixpoint find_reg (k : nat) (l : list (nat * expr)) : option expr :=
match l with [] => None | (i, e) :: t => if Nat.eqb i k then Some e else find_reg k t end.
Lemma find_reg_in k l e : find_reg k l = Some e -> In (k, e) l.
Proof.
induction l as [|[i x] t IH]; cbn [find_reg]; intros H. discriminate.
destruct (Nat.eqb i k) eqn:E. inversion H; subst. apply Nat.eqb_eq in E. subst. left; reflexivity. right; auto.
Qed.
Definition kept1 (nx0 : nat) (regs0 : list expr) (ps : SR.post_spec) (x : nat) : bool :=
(Nat.ltb 0 x) && (Nat.ltb x 32) &&
match find_reg x (SR.ps_regs ps) with Some e => expr_eqb e (nth x regs0 (ELit 0)) && expr_vars_lt nx0 e | None => false end.
Definition xcell vl bd (nx0 : nat) (K : kentry) (p : P.px) : bool :=
match K, p with
| KWord (SA b off) w v, P.PU64 P.MM1 pa pv => Nat.eqb w 8 && expr_vars_lt nx0 b && expr_vars_lt nx0 v && addr_ok vl bd pa b off && zmE vl bd pv v
| KWord (SA b off) w v, P.PU32 P.MM1 pa pv => Nat.eqb w 4 && expr_vars_lt nx0 b && expr_vars_lt nx0 v && addr_ok vl bd pa b off && zmE vl bd pv v
| KWord (SA b off) w v, P.PU8 P.MM1 pa pv => Nat.eqb w 1 && expr_vars_lt nx0 b && expr_vars_lt nx0 v && addr_ok vl bd pa b off && zmE vl bd pv v
&& rng_byte (iv bd pv)
| KUnk (SA b off) ne, P.PDef P.MM1 pa pn => expr_vars_lt nx0 b && expr_vars_lt nx0 ne && addr_ok vl bd pa b off && zmE vl bd pn ne
| KZero (SA b off) ne, P.PZero P.MM1 pa pn => expr_vars_lt nx0 b && expr_vars_lt nx0 ne && addr_ok vl bd pa b off && zmE vl bd pn ne
| KRange e lo hi, _ => expr_vars_lt nx0 e && krchk vl bd e lo hi p
| KAlign e m, P.PAligned q qm => expr_vars_lt nx0 e && isZ (lit_of qm) m && zmE vl bd q e
| _, _ => false
end.
Lemma u8_of_KWord1_lit segs E M b off c : kentry_ok segs E M (KWord (SA b off) 1 (ELit c)) ->
L5.u8_at segs M (bv_unsigned (edenot E b) + off) ((c mod MM) mod 256).
Proof.
intros K. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u8_at.
rewrite L5K.adenot_e in Rd. cbn [edenot] in Rd.
unfold word_to_le_bytes in Rd. rewrite Z_to_bv_unsigned in Rd. unfold bv_wrap in Rd. change (bv_modulus 64) with MM in Rd.
cbn [Z_to_le_bytes] in Rd. rewrite Rd. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
Lemma u8x2_of_KWord2_lit segs E M b off c : kentry_ok segs E M (KWord (SA b off) 2 (ELit c)) ->
L5.u8_at segs M (bv_unsigned (edenot E b) + off) ((c mod MM) mod 256) /\
L5.u8_at segs M (bv_unsigned (edenot E b) + off + 1) (((c mod MM) / 256) mod 256).
Proof.
intros K. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd).
rewrite L5K.adenot_e in Rd. cbn [edenot] in Rd.
set (a := bv_unsigned (edenot E b) + off) in *.
unfold word_to_le_bytes in Rd. rewrite Z_to_bv_unsigned in Rd. unfold bv_wrap in Rd. change (bv_modulus 64) with MM in Rd.
cbn [Z_to_le_bytes rdn] in Rd. unfold L5.u8_at.
assert (E1 : (Z_to_bv 64 a + 1 = Z_to_bv 64 (a + 1))%bv).
{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_unsigned (1 : bv 64)) with 1. apply Z.add_mod_idemp_l. clear; lia. }
rewrite E1 in Rd.
destruct (match M (Z_to_bv 64 a) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 a) end) as [x|] eqn:X; [|discriminate].
destruct (match M (Z_to_bv 64 (a + 1)) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 (a + 1)) end) as [y|] eqn:Y; [|discriminate].
injection Rd as Ex Ey. split.
- cbn [rdn]. rewrite X. subst x. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by (clear; lia). reflexivity.
- cbn [rdn]. rewrite Y. subst y. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 8) with 256. rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
Definition u8b (p : P.px) : option (P.zx * P.zx) := match p with P.PU8 P.MM1 a v => Some (a, v) | _ => None end.
Definition andp (p : P.px) : option (P.px * P.px) := match p with P.PAnd p1 p2 => Some (p1, p2) | _ => None end.
Definition xcellb vl bd (nx0 : nat) (K : kentry) (p : P.px) : bool :=
match K, u8b p with
| KWord (SA b off) w (ELit c), Some (pa, pv) =>
expr_vars_lt nx0 b &&
((Nat.eqb w 1 && addr_ok vl bd pa b off && isZ (lit_of pv) ((c mod MM) mod 256))
|| (Nat.eqb w 2 && addr_ok vl bd pa b off && isZ (lit_of pv) ((c mod MM) mod 256))
|| (Nat.eqb w 2 && (match pa with P.ZAdd pa0 (P.ZL 1) => addr_ok vl bd pa0 b off | _ => false end)
&& isZ (lit_of pv) (((c mod MM) / 256) mod 256)))
| _, _ => false end.
Definition xcellw2 vl bd (nx0 : nat) (K : kentry) (p : P.px) : bool :=
match K, andp p with
| KWord (SA b off) w (ELit c), Some (p1, p2) =>
match u8b p1, u8b p2 with
| Some (pa0, pv0), Some (pa1, pv1) =>
Nat.eqb w 2 && expr_vars_lt nx0 b && addr_ok vl bd pa0 b off && zx_eqb pa1 (P.ZAdd pa0 (P.ZL 1))
&& isZ (lit_of pv0) ((c mod MM) mod 256) && isZ (lit_of pv1) (((c mod MM) / 256) mod 256)
| _, _ => false end
| _, _ => false end.
Definition xcellA vl bd (nx0 : nat) (K : kentry) (p : P.px) : bool :=
xcell vl bd nx0 K p || xcellb vl bd nx0 K p || xcellw2 vl bd nx0 K p.
Definition xpart vl bd (nx0 : nat) (regs0 : list expr) (pc0 : Z) (ks : list (list nat)) (k : nat) (ps : SR.post_spec) (p : P.px) : bool :=
match p with
| P.PSteps a b => Z.eqb a pc0 && Z.eqb b (SR.ps_pc ps)
| P.PKept e => Nat.eqb e k && forallb (kept1 nx0 regs0 ps) (nth e ks nil)
| P.PG' i q => match find_reg i (SR.ps_regs ps) with Some e => expr_vars_lt nx0 e && zmW vl bd q e | None => false end
| P.PGR i j => match find_reg i (SR.ps_regs ps) with Some (EVar j') => Nat.eqb j j' && negb (vl j) && Nat.ltb j nx0 | _ => false end
| P.PUns' i q => match find_reg i (SR.ps_regs ps) with Some e => expr_vars_lt nx0 e && zmE vl bd q e | None => false end
| P.PTrue => true
| _ => existsb (fun K => xcellA vl bd nx0 K p) (SR.ps_cells ps)
end.
Section Exit.
Variable segs : list Segment.
Variable al : Z -> Z -> Prop.
Variable sr : Z -> Z -> Z -> Z -> Prop.
Variable za : (word -> option byte) -> Z -> Z -> Prop.
Hypothesis ALi : forall a m, al a m <-> a mod m = 0.
Hypothesis ZAi : forall Mx a n, za Mx a n <-> (forall i, 0 <= i < n -> Mx (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)).
Variable ks : list (list nat).
Variable fx : FPState.
Variable R : bvmap 5 word.
Variable M : word -> option byte.
Variable V : nat -> Z.
Variables (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte).
Lemma edenot_kept nx0 E E' e : env_agree nx0 E E' -> expr_vars_lt nx0 e = true -> edenot E' e = edenot E e.
Proof. intros HA Hv. symmetry. apply (edenot_agree nx0 E E' e HA Hv). Qed.
Lemma xcell_sound vl bd nx0 E E' K p : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> env_agree nx0 E E' ->
xcell vl bd nx0 K p = true -> kentry_ok segs E' M' K -> P.dp segs al sr za ks fx R M V fx' R' M' p.
Proof.
intros HE HB HA Hx HK. destruct K; try discriminate; cbn [xcell] in Hx.
- match goal with |- _ => destruct a as [b off] end.
destruct p; try discriminate; destruct m; try discriminate; andb_all; pr_entry vl bd V R E HE HB; subst;
cbn [P.dp P.msel_of];
repeat match goal with H : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA H) in *; clear H end.
+ match goal with A : bv_unsigned (edenot E' b) + off = _ |- _ => rewrite <- A end.
eapply L5K.u64_of_KWord8; [exact HK | reflexivity | eassumption].
+ match goal with A : bv_unsigned (edenot E' b) + off = _ |- _ => rewrite <- A end.
eapply L5K.u32_of_KWord4; [exact HK | reflexivity | eassumption].
+ match goal with A : bv_unsigned (edenot E' b) + off = _ |- _ => rewrite <- A end.
eapply L5K.u8_of_KWord1; [exact HK | reflexivity | eassumption | assumption].
- match goal with |- _ => destruct a as [b off] end.
destruct p; try discriminate; destruct m; try discriminate; andb_all; pr_entry vl bd V R E HE HB; subst; cbn [P.dp P.msel_of].
repeat match goal with H : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA H) in *; clear H end.
apply ZAi. cbn [kentry_ok] in HK. destruct HK as [_ HZ]. unfold elenZ, estart in HZ. cbn [a_base a_off] in HZ.
match goal with A : bv_unsigned (edenot E' b) + off = _, N : bv_unsigned (edenot E' ?n) = P.dz R V ?q |- _ =>
rewrite A, N in HZ end. exact HZ.
- destruct p; try discriminate. andb_all. pr_entry vl bd V R E HE HB. cbn [P.dp].
repeat match goal with H : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA H) in *; clear H end.
apply ALi. cbn [kentry_ok] in HK. destruct HK as [_ HK].
repeat match goal with A : P.dz R V ?q = _ |- _ => rewrite A; clear A end.
match goal with N : bv_unsigned (edenot E' e) = P.dz R V ?q |- _ => rewrite <- N end. exact HK.
- andb_all. unfold krchk in *. destruct p; try discriminate.
+ andb_all. pr_entry vl bd V R E HE HB. cbn [P.dp].
repeat match goal with H : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA H) in *; clear H end.
cbn [kentry_ok] in HK. repeat match goal with A : P.dz R V ?q = _ |- _ => rewrite A; clear A end.
match goal with N : bv_unsigned (edenot E' e) = P.dz R V ?q |- _ => rewrite <- N end. exact HK.
+ destruct (is_sltu e) as [[x y]|] eqn:S; [|discriminate]. destruct e; try discriminate. destruct op; try discriminate.
inversion S; subst. andb_all. pr_entry vl bd V R E HE HB. subst. cbn [P.dp].
cbn [expr_vars_lt] in *. andb_all.
repeat match goal with H : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA H) in *; clear H end.
cbn [kentry_ok] in HK. rewrite sltu_val in HK. repeat match goal with A : bv_unsigned (edenot E' ?x) = _ |- _ => rewrite A in HK; clear A end.
destruct (_ <? _) eqn:C in HK. apply Z.ltb_lt in C. exact C. lia.
+ destruct (is_sltu e) as [[x y]|] eqn:S; [|discriminate]. destruct e; try discriminate. destruct op; try discriminate.
inversion S; subst. andb_all. pr_entry vl bd V R E HE HB. subst. cbn [P.dp].
cbn [expr_vars_lt] in *. andb_all.
repeat match goal with H : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA H) in *; clear H end.
cbn [kentry_ok] in HK. rewrite sltu_val in HK. repeat match goal with A : bv_unsigned (edenot E' ?x) = _ |- _ => rewrite A in HK; clear A end.
destruct (_ <? _) eqn:C in HK. lia. apply Z.ltb_ge in C. exact C.
+ destruct e as [ | | op x y | | | | | ]; try discriminate. destruct op; try discriminate. destruct y; try discriminate.
andb_all. pr_entry vl bd V R E HE HB. cbn [P.dp]. cbn [expr_vars_lt] in *. andb_all.
repeat match goal with H : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA H) in *; clear H end.
eapply kr_tb_exit; [exact HK | eassumption | eassumption | eassumption].
- match goal with |- _ => destruct a as [b off] end.
destruct p; try discriminate; destruct m; try discriminate; andb_all; pr_entry vl bd V R E HE HB; subst; cbn [P.dp P.msel_of].
repeat match goal with H : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA H) in *; clear H end.
match goal with A : bv_unsigned (edenot E' b) + off = _ |- _ => rewrite <- A end.
eapply L5K.defined_of_KUnk; [exact HK | reflexivity | eassumption].
Qed.
Lemma u8b_dp p a v : u8b p = Some (a, v) -> P.dp segs al sr za ks fx R M V fx' R' M' p = L5.u8_at segs M' (P.dz R V a) (P.dz R V v).
Proof. intros H. destruct p; try discriminate H. destruct m; try discriminate H. cbn [u8b] in H. inversion H; subst. reflexivity. Qed.
Lemma andp_dp p p1 p2 : andp p = Some (p1, p2) ->
P.dp segs al sr za ks fx R M V fx' R' M' p = (P.dp segs al sr za ks fx R M V fx' R' M' p1 /\ P.dp segs al sr za ks fx R M V fx' R' M' p2).
Proof. intros H. destruct p; try discriminate H. cbn [andp] in H. inversion H; subst. reflexivity. Qed.
Lemma xcellb_sound vl bd nx0 E E' K p : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> env_agree nx0 E E' ->
xcellb vl bd nx0 K p = true -> kentry_ok segs E' M' K -> P.dp segs al sr za ks fx R M V fx' R' M' p.
Proof.
intros HE HB HA Hx HK. unfold xcellb in Hx.
destruct K; try discriminate. destruct a as [b off]. destruct v; try discriminate.
destruct (u8b p) as [[pa pv]|] eqn:U; [|discriminate].
rewrite (u8b_dp p pa pv U). apply andb_prop in Hx. destruct Hx as [Hv Hx].
assert (Kb : edenot E' b = edenot E b) by exact (edenot_kept nx0 E E' b HA Hv).
apply orb_prop in Hx. destruct Hx as [Hx|Hx]; [apply orb_prop in Hx; destruct Hx as [Hx|Hx]|].
- andb_all. pr_entry vl bd V R E HE HB. subst.
pose proof (u8_of_KWord1_lit segs E' M' b off z HK) as U8. rewrite Kb in U8.
match goal with A : bv_unsigned (edenot E b) + off = _, HZ : P.dz R V pv = _ |- _ => rewrite <- A, HZ end. exact U8.
- andb_all. pr_entry vl bd V R E HE HB. subst.
destruct (u8x2_of_KWord2_lit segs E' M' b off z HK) as [U8 _]. rewrite Kb in U8.
match goal with A : bv_unsigned (edenot E b) + off = _, HZ : P.dz R V pv = _ |- _ => rewrite <- A, HZ end. exact U8.
- andb_all. destruct pa; try discriminate. destruct pa2; try discriminate. destruct z0; try discriminate. destruct p0; try discriminate.
pr_entry vl bd V R E HE HB. subst.
destruct (u8x2_of_KWord2_lit segs E' M' b off z HK) as [_ U8]. rewrite Kb in U8. cbn [P.dz].
match goal with A : bv_unsigned (edenot E b) + off = _, HZ : P.dz R V pv = _ |- _ => rewrite <- A, HZ end. exact U8.
Qed.
Lemma xcellw2_sound vl bd nx0 E E' K p : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> env_agree nx0 E E' ->
xcellw2 vl bd nx0 K p = true -> kentry_ok segs E' M' K -> P.dp segs al sr za ks fx R M V fx' R' M' p.
Proof.
intros HE HB HA Hx HK. unfold xcellw2 in Hx.
destruct K; try discriminate. destruct a as [b off]. destruct v; try discriminate.
destruct (andp p) as [[p1 p2]|] eqn:A; [|discriminate].
destruct (u8b p1) as [[pa0 pv0]|] eqn:U1; [|discriminate]. destruct (u8b p2) as [[pa1 pv1]|] eqn:U2; [|discriminate].
rewrite (andp_dp p p1 p2 A), (u8b_dp p1 pa0 pv0 U1), (u8b_dp p2 pa1 pv1 U2).
andb_all. match goal with H : zx_eqb _ _ = true |- _ => apply zx_eqb_eq in H; subst pa1 end.
pr_entry vl bd V R E HE HB. subst.
destruct (u8x2_of_KWord2_lit segs E' M' b off z HK) as [U8a U8b].
match goal with Hv : expr_vars_lt nx0 b = true |- _ => rewrite (edenot_kept nx0 E E' b HA Hv) in U8a, U8b end.
cbn [P.dz].
match goal with A : bv_unsigned (edenot E b) + off = _ |- _ => rewrite <- A end.
repeat match goal with HZ : P.dz R V ?q = _ |- _ => rewrite HZ; clear HZ end.
split; assumption.
Qed.
Lemma xcellA_sound vl bd nx0 E E' K p : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> env_agree nx0 E E' ->
xcellA vl bd nx0 K p = true -> kentry_ok segs E' M' K -> P.dp segs al sr za ks fx R M V fx' R' M' p.
Proof.
intros HE HB HA Hx HK. unfold xcellA in Hx. apply orb_prop in Hx. destruct Hx as [Hx|Hx]. apply orb_prop in Hx. destruct Hx as [Hx|Hx].
- exact (xcell_sound vl bd nx0 E E' K p HE HB HA Hx HK).
- exact (xcellb_sound vl bd nx0 E E' K p HE HB HA Hx HK).
- exact (xcellw2_sound vl bd nx0 E E' K p HE HB HA Hx HK).
Qed.
Lemma xpart_sound vl bd nx0 regs0 pc0 k ps E E' p :
env_ok vl (BL.uv E) V R -> bd_ok bd R V -> env_agree nx0 E E' -> E = mkE vl V R -> regs_ok E regs0 R ->
msteps segs (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom segs)) ->
(forall i0 e, In (i0, e) (SR.ps_regs ps) -> (0 < i0 < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i0)) = edenot E' e) ->
(forall K, In K (SR.ps_cells ps) -> kentry_ok segs E' M' K) ->
xpart vl bd nx0 regs0 pc0 ks k ps p = true -> P.dp segs al sr za ks fx R M V fx' R' M' p.
Proof.
intros HE HB HA HEq HR HM HG HC Hx. destruct p; cbn [xpart] in Hx;
try (apply existsb_exists in Hx; destruct Hx as [K [Hin Hk]]; exact (xcellA_sound vl bd nx0 E E' K _ HE HB HA Hk (HC K Hin))).
- cbn [P.dp]. exact I.
- destruct (find_reg k0 (SR.ps_regs ps)) as [e|] eqn:F; [|discriminate]. andb_all. cbn [P.dp].
destruct (HG _ _ (find_reg_in _ _ _ F)) as [_ ->]. rewrite (edenot_kept nx0 E E' e HA H).
apply (zmW_sound vl bd V R E _ _ HE HB H0).
- destruct (find_reg k0 (SR.ps_regs ps)) as [e|] eqn:F; [|discriminate]. destruct e; try discriminate. andb_all.
apply Nat.eqb_eq in H. subst. apply Nat.ltb_lt in H0. apply negb_true_iff in H1. cbn [P.dp].
destruct (HG _ _ (find_reg_in _ _ _ F)) as [_ ->]. cbn [edenot]. destruct HA as [HA _]. rewrite <- (HA n H0).
cbn [mkE ev]. rewrite H1. reflexivity.
- destruct (find_reg k0 (SR.ps_regs ps)) as [e|] eqn:F; [|discriminate]. andb_all. cbn [P.dp].
destruct (HG _ _ (find_reg_in _ _ _ F)) as [_ ->]. rewrite (edenot_kept nx0 E E' e HA H).
apply (zmE_sound vl bd V R E _ _ HE HB H0).
- andb_all. apply Z.eqb_eq in H. apply Z.eqb_eq in H0. subst. cbn [P.dp]. exact HM.
- andb_all. apply Nat.eqb_eq in H. subst. cbn [P.dp]. intros x Hx. rewrite forallb_forall in H0. specialize (H0 x Hx).
unfold kept1 in H0. andb_all. apply Nat.ltb_lt in H. apply Nat.ltb_lt in H1.
destruct (find_reg x (SR.ps_regs ps)) as [e|] eqn:F; [|discriminate]. andb_all.
destruct (HG _ _ (find_reg_in _ _ _ F)) as [_ ->]. rewrite (edenot_kept nx0 _ E' e HA H2).
apply AX2S.expr_eqb_eq in H0. subst e. rewrite (HR (Z_to_bv 5 (Z.of_nat x))). rewrite BG.sr_get_reg by lia. reflexivity.
Qed.
Definition xexit vl bd nx0 regs0 pc0 ks k ps (es : list P.px) : bool := forallb (xpart vl bd nx0 regs0 pc0 ks k ps) es.
Lemma dparts_of (es : list P.px) : Forall (P.dp segs al sr za ks fx R M V fx' R' M') es -> P.dparts segs al sr za ks fx R M V fx' R' M' es.
Proof.
induction es as [|p t IH]; intros HF; cbn [P.dparts]. exact I.
inversion HF; subst. destruct t. exact H1. split. exact H1. apply IH. exact H2.
Qed.
Lemma dexits_of (xs : list (list P.px)) i es : nth_error xs i = Some es -> P.dparts segs al sr za ks fx R M V fx' R' M' es ->
P.dexits segs al sr za ks fx R M V fx' R' M' xs.
Proof.
revert i. induction xs as [|x t IH]; intros i Hn Hd. destruct i; discriminate.
cbn [P.dexits]. destruct i as [|i].
- cbn in Hn. inversion Hn; subst. destruct t. exact Hd. left. exact Hd.
- cbn in Hn. destruct t. destruct i; discriminate. right. eapply IH; eauto.
Qed.
Fixpoint fchk vl bd nx0 (fr : list (P.zx * P.zx)) (F0 : list SGP.region) : bool :=
match fr, F0 with
| [], [] => true
| (pa, pn) :: t, (b, off, ne) :: t' =>
expr_vars_lt nx0 b && expr_vars_lt nx0 ne && addr_ok vl bd pa b off && zmE vl bd pn ne && fchk vl bd nx0 t t'
| _, _ => false
end.
Lemma fchk_a vl bd nx0 E E' : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> env_agree nx0 E E' ->
forall fr F0, fchk vl bd nx0 fr F0 = true -> forall (a : word) (C : Prop), (SGP.outside E' F0 a -> C) -> P.dfa R V a fr C.
Proof.
intros HE HB HA. induction fr as [|[pa pn] t IH]; intros F0 Hf a C H; destruct F0 as [|[[b off] ne] t']; cbn [fchk] in Hf; try discriminate.
- cbn [P.dfa]. apply H. constructor.
- andb_all. cbn [P.dfa]. intros Hn. match goal with Hf : fchk _ _ _ t t' = true |- _ => apply (IH t' Hf a C) end. intros Ho. apply H. constructor; [|exact Ho].
pr_entry vl bd V R E HE HB.
repeat match goal with Hv : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA Hv) in *; clear Hv end.
unfold estart, elenZ. cbn [a_base a_off].
match goal with A1 : bv_unsigned (edenot E' b) + off = _, A2 : bv_unsigned (edenot E' ne) = _ |- _ => rewrite A1, A2 end. lia.
Qed.
Lemma fchk_i vl bd nx0 E E' : env_ok vl (BL.uv E) V R -> bd_ok bd R V -> env_agree nx0 E E' ->
forall fr F0, fchk vl bd nx0 fr F0 = true -> forall (i : Z) (C : Prop), 0 <= i < 2 ^ 64 ->
(SGP.outside E' F0 (Z_to_bv 64 i) -> C) -> P.dfi R V i fr C.
Proof.
intros HE HB HA. induction fr as [|[pa pn] t IH]; intros F0 Hf i C Hi H; destruct F0 as [|[[b off] ne] t']; cbn [fchk] in Hf; try discriminate.
- cbn [P.dfi]. apply H. constructor.
- andb_all. cbn [P.dfi]. intros Hn. match goal with Hf : fchk _ _ _ t t' = true |- _ => apply (IH t' Hf i C Hi) end. intros Ho. apply H. constructor; [|exact Ho].
pr_entry vl bd V R E HE HB.
repeat match goal with Hv : expr_vars_lt nx0 ?x = true |- _ => rewrite <- (edenot_kept nx0 E E' x HA Hv) in *; clear Hv end.
unfold estart, elenZ. cbn [a_base a_off]. rewrite (BG.unsigned_lit i Hi).
match goal with A1 : bv_unsigned (edenot E' b) + off = _, A2 : bv_unsigned (edenot E' ne) = _ |- _ => rewrite A1, A2 end. lia.
Qed.
End Exit.
Fixpoint xall vl bd nx0 regs0 pc0 ks (k : nat) (xs : list (list P.px)) (pss : list SR.post_spec) : bool :=
match xs, pss with
| [], [] => true
| es :: t, ps :: t' => xexit vl bd nx0 regs0 pc0 ks k ps es && xall vl bd nx0 regs0 pc0 ks (S k) t t'
| _, _ => false
end.
Lemma xall_nth vl bd nx0 regs0 pc0 ks : forall xs pss k i ps, xall vl bd nx0 regs0 pc0 ks k xs pss = true -> nth_error pss i = Some ps ->
exists es, nth_error xs i = Some es /\ xexit vl bd nx0 regs0 pc0 ks (k + i) ps es = true.
Proof.
induction xs as [|es t IH]; intros pss k i ps Hx Hn; destruct pss as [|ps0 t']; cbn [xall] in Hx; try discriminate.
- destruct i; discriminate.
- andb_all. destruct i as [|i].
+ cbn in Hn. inversion Hn; subst. exists es. split. reflexivity. rewrite Nat.add_0_r. assumption.
+ cbn in Hn. match goal with Hx : xall _ _ _ _ _ _ (S k) t t' = true |- _ => destruct (IH t' (S k) i ps Hx Hn) as [es' [H1 H2]] end.
exists es'. split. exact H1.
replace (k + S i)%nat with (S k + i)%nat by lia. exact H2.
Qed.
Definition SEG (segs : list Segment) (regs0 : list expr) (kn0 : list kentry) (BR : list SGP.bfact) (PSS : list SR.post_spec)
(nx0 : nat) (F0 : list SGP.region) (pc0 : Z) : Prop :=
forall (fx : FPState) (E : env) (R : bvmap 5 word) (M : word -> option byte),
regs_ok E regs0 R -> know_ok segs E M kn0 -> SGP.bfacts_ok BR E ->
exists (fx' : FPState) (E' : env) (R' : bvmap 5 word) (M' : word -> option byte) (i : nat) (ps : SR.post_spec),
nth_error PSS i = Some ps /\ env_agree nx0 E E' /\
msteps segs (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom segs)) /\
(forall (i0 : nat) (e : expr), In (i0, e) (SR.ps_regs ps) -> (0 < i0 < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i0)) = edenot E' e) /\
getr R' (Z_to_bv 5 0) = Z_to_bv 64 0 /\ SGP.regions_ok E' F0 /\
(forall a : word, SGP.outside E' F0 a -> M' a = M a) /\
(forall K : kentry, In K (SR.ps_cells ps) -> kentry_ok segs E' M' K) /\ mem_grows M M'.
Definition pcheck (regs0 : list expr) (kn0 : list kentry) (BR : list SGP.bfact) (PSS : list SR.post_spec) (nx0 : nat)
(F0 : list SGP.region) (pc0 : Z) (ks : list (list nat)) (s : P.stmt) : bool :=
let hs := P.s_hyps s in
echk hs regs0 kn0 && (match BR with [] => true | _ => false end)
&& fchk (vl_of hs) (bd_of hs) nx0 (P.s_frames s) F0 && xall (vl_of hs) (bd_of hs) nx0 regs0 pc0 ks 0 (P.s_exits s) PSS.
Theorem conc_sound segs (al : Z -> Z -> Prop) (sr : Z -> Z -> Z -> Z -> Prop) (za : (word -> option byte) -> Z -> Z -> Prop)
(ALi : forall a m, al a m <-> a mod m = 0)
(ZAi : forall Mx a n, za Mx a n <-> (forall i, 0 <= i < n -> Mx (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)))
ks regs0 kn0 BR PSS nx0 F0 pc0 s :
pcheck regs0 kn0 BR PSS nx0 F0 pc0 ks s = true -> SEG segs regs0 kn0 BR PSS nx0 F0 pc0 ->
forall fx R M V, P.dstmt segs al sr za ks fx R M V s.
Proof.
intros Hc HS fx R M V. unfold P.dstmt. apply dhyps_intro. intros HF.
unfold pcheck in Hc. cbv zeta in Hc. andb_all.
set (hs := P.s_hyps s) in *.
pose proof (env_ok_mkE segs al sr za ks fx R M V hs HF) as HE. pose proof (bd_of_ok segs al sr za ks fx R M V hs HF) as HB.
assert (AL : forall a m, al a m -> a mod m = 0) by (intros a m; apply ALi).
assert (ZA : forall Mx a n, za Mx a n -> forall i, 0 <= i < n -> Mx (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) by (intros Mx a n; apply ZAi).
destruct (entry_sound segs al sr za AL ZA ks fx R M V hs regs0 kn0 ltac:(assumption) HF) as [HR HK].
destruct BR; [|discriminate].
destruct (HS fx (mkE (vl_of hs) V R) R M HR HK (Forall_nil _)) as (fx' & E' & R' & M' & i & ps & Hn & HA & HM & HG & _ & _ & HO & HC & Hgr).
exists fx', R', M'. split; [exact Hgr|]. split; [|split].
- intros a. eapply (fchk_a sr R M V M'); [exact HE | exact HB | exact HA | eassumption | apply HO].
- intros i0 Hi0. eapply (fchk_i sr R V); [exact HE | exact HB | exact HA | eassumption | exact Hi0 | apply HO].
- match goal with Hx : xall _ _ _ _ _ _ 0 _ _ = true |- _ => destruct (xall_nth _ _ _ _ _ _ _ _ 0 i ps Hx Hn) as [es [Hes Hxe]] end.
eapply dexits_of; [exact Hes|]. apply dparts_of. rewrite Forall_forall. intros p Hp. unfold xexit in Hxe. rewrite forallb_forall in Hxe.
eapply (xpart_sound segs al sr za ALi ZAi ks fx R M V fx' R' M' (vl_of hs) (bd_of hs) nx0 regs0 pc0 (0 + i)%nat ps _ E');
[exact HE | exact HB | exact HA | reflexivity | exact HR | exact HM | exact HG | exact HC | apply Hxe; exact Hp].
Qed.
Definition zeros_r (Mx : word -> option byte) (a n : Z) : Prop := forall i, 0 <= i < n -> Mx (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
Ltac solve segs al sr za ks regs0 kn0 BR PSS nx0 F0 pc0 seg fx R M V str :=
let s := eval vm_compute in (PStmt.dec str) in
exact (conc_sound segs al sr za (fun a m => iff_refl _) (fun Mx a n => iff_refl _) ks regs0 kn0 BR PSS nx0 F0 pc0 s
(@eq_refl bool true <: pcheck regs0 kn0 BR PSS nx0 F0 pc0 ks s = true) seg fx R M V).
Ltac solve2 segs al sr za ks regs0 kn0 BR PSS nx0 F0 pc0 seg fx R M V str :=
change_no_check (P.dstmt segs al sr za ks fx R M V (P.dec str));
exact (conc_sound segs al sr za (fun a m => iff_refl _) (fun Mx a n => iff_refl _) ks regs0 kn0 BR PSS nx0 F0 pc0 (P.dec str)
(@eq_refl bool true <: pcheck regs0 kn0 BR PSS nx0 F0 pc0 ks (P.dec str) = true) seg fx R M V).
End PR.
