(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition scale_fact (fs : list fact) (l : lin) (s : Z) : option fact :=
  let k := 2 ^ s in
  let '(lo, hi) := irange fs (lscale k l) in
  let '(llo, lhi) := irange fs l in
  if (Z.leb 1 s && Z.leb s 63 && Z.leb 0 llo && Z.ltb (k * lhi) two64 && Z.leb 0 lo)%bool
  then Some (FRange l ((lo + k - 1) / k) (hi / k)) else None.
Definition hx_scale (l : lin) (s : Z) (S : sst) : option sst :=
  match scale_fact (s_facts S) l s with
  | Some f => if fwf (s_next S) f then Some (add_fact S f) else None
  | None => None
  end.

Lemma scale_fact_ok : forall E fs l s f, Forall (fact_ok E) fs -> scale_fact fs l s = Some f -> fact_ok E f.
Proof.
  intros E fs l s f HF H. unfold scale_fact in H.
  destruct (irange fs (lscale (2 ^ s) l)) as [lo hi] eqn:Hig. destruct (irange fs l) as [llo lhi] eqn:Hir.
  destruct (Z.leb 1 s && Z.leb s 63 && Z.leb 0 llo && Z.ltb (2 ^ s * lhi) two64 && Z.leb 0 lo)%bool eqn:Hc; [|discriminate].
  injection H as <-.
  repeat match goal with Hx : (_ && _)%bool = true |- _ => apply andb_prop in Hx as [? ?] end.
  repeat match goal with Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx end.
  pose proof (irange_sound E fs l HF) as Hr. rewrite Hir in Hr. cbn [fst snd] in Hr.
  pose proof (irange_sound E fs (lscale (2 ^ s) l) HF) as Hf0. rewrite Hig in Hf0. cbn [fst snd] in Hf0. cbn [fact_ok].
  set (u := bv_unsigned (lden E l)) in *.
  assert (Hk : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Hu : bv_unsigned (lden E (lscale (2 ^ s) l)) = 2 ^ s * u).
  { rewrite lden_lscale, u_Z_to_bv. unfold bv_wrap. change (bv_modulus 64) with two64. apply Z.mod_small. nia. }
  rewrite Hu in Hf0. destruct Hf0 as [Hlo Hhi]. split.
  - apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. nia.
  - apply Z.div_le_lower_bound; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Fixpoint frange_sub (fs : list fact) (l : lin) (lo hi : Z) : bool :=
  match fs with
  | [] => false
  | FRange g lo' hi' :: fs' =>
      if terms_eqb (l_t g) (l_t l) then
        let d := sgn64 (w64 (l_c l - l_c g)) in
        if (Z.leb 0 (lo' + d) && Z.ltb (hi' + d) two64 && Z.leb lo (lo' + d) && Z.leb (hi' + d) hi)%bool then true else frange_sub fs' l lo hi
      else frange_sub fs' l lo hi
  | _ :: fs' => frange_sub fs' l lo hi
  end.
Lemma frange_sub_ok : forall E fs l lo hi, Forall (fact_ok E) fs -> frange_sub fs l lo hi = true -> lo <= bv_unsigned (lden E l) <= hi.
Proof.
  intros E fs l lo hi HF. induction HF as [|f fs Hok HF IH]; intros H; cbn [frange_sub] in H; [discriminate|].
  destruct f as [c a b tk|g lo' hi'|g k' r'|g m' v'|x' v' j'|xb bsb]; try exact (IH H).
  destruct (terms_eqb (l_t g) (l_t l)) eqn:Ht; [|exact (IH H)].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|exact (IH H)] end.
  repeat match goal with Hx : (_ && _)%bool = true |- _ => apply andb_prop in Hx as [? ?] end.
  repeat match goal with Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx end.
  cbn [fact_ok] in Hok. apply terms_eqb_eq in Ht.
  pose proof (same_terms_eqm E l g (eq_sym Ht)) as He.
  set (d := sgn64 (w64 (l_c l - l_c g))) in *.
  assert (He1 : eqm (bv_unsigned (lden E l)) (bv_unsigned (lden E g) + d)).
  { eapply eqm_trans; [exact He|]. apply eqm_add; [apply eqm_refl|]. unfold d.
    eapply eqm_trans; [|apply eqm_sym, sgn64_eqm]. apply eqm_sym, eqm_w64. }
  pose proof (u_range E l) as Rl. unfold eqm in He1.
  rewrite (Z.mod_small (bv_unsigned (lden E l))) in He1 by exact Rl.
  rewrite (Z.mod_small (bv_unsigned (lden E g) + d)) in He1 by lia. lia.
Qed.

(* [comment removed for export] *)
Definition fsum_sub1 (fs : list fact) (l : lin) (lo hi : Z) (f : fact) : bool :=
  match f with
  | FRange g lo' hi' =>
      if (shares (l_t l) (l_t g) && Z.leb hi' hi)%bool then
        let r := irange fs (lsub l g) in
        (Z.leb lo (lo' + fst r) && Z.leb (hi' + snd r) hi && Z.ltb (hi' + snd r) two64)%bool
      else false
  | _ => false
  end.
Definition fsum_sub (fs : list fact) (l : lin) (lo hi : Z) : bool := existsb (fsum_sub1 fs l lo hi) fs.
Definition frange_sub2 (fs : list fact) (l : lin) (lo hi : Z) : bool := if frange_sub fs l lo hi then true else fsum_sub fs l lo hi.
Lemma frange_sub2_ok : forall E fs l lo hi, Forall (fact_ok E) fs -> frange_sub2 fs l lo hi = true -> lo <= bv_unsigned (lden E l) <= hi.
Proof.
  intros E fs l lo hi HF H. unfold frange_sub2 in H. destruct (frange_sub fs l lo hi) eqn:H1; [exact (frange_sub_ok E fs l lo hi HF H1)|].
  unfold fsum_sub in H. apply existsb_exists in H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) HF f Hin) as Hok.
  destruct f as [c a b tk|g lo' hi'|g k' r'|g m' v'|x' v' j'|xb bsb]; try discriminate Hf. cbn [fsum_sub1] in Hf.
  destruct (shares (l_t l) (l_t g) && Z.leb hi' hi)%bool; [|discriminate Hf].
  repeat match goal with Hx : (_ && _)%bool = true |- _ => apply andb_prop in Hx as [? ?] end.
  repeat match goal with Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx end.
  cbn [fact_ok] in Hok.
  pose proof (irange_sound E fs (lsub l g) HF) as Hr.
  pose proof (u_range E l) as Rl. pose proof (u_range E g) as Rg.
  rewrite lden_lsub, bv_sub_unsigned in Hr. unfold bv_wrap in Hr. change (bv_modulus 64) with two64 in Hr.
  set (ul := bv_unsigned (lden E l)) in *. set (ug := bv_unsigned (lden E g)) in *.
  destruct (Z_le_gt_dec ug ul) as [Hle|Hgt].
  - rewrite Z.mod_small in Hr by lia. lia.
  - exfalso. assert (Hm : (ul - ug) mod two64 = ul - ug + two64).
    { symmetry. apply (Z.mod_unique _ _ (-1)); [left; lia | lia]. }
    rewrite Hm in Hr. lia.
Qed.
(* [comment removed for export] *)
Definition hx_ixf (l : lin) (S : sst) : option sst :=
  let r := irange_x (s_facts S) l in      (* [comment removed for export] *)
  let f := FRange l (fst r) (snd r) in
  if fwf (s_next S) f then Some (add_fact S f) else None.
(* [comment removed for export] *)
Definition low_ok (y : positive) (k : Z) (l : lin) : bool :=
  (Z.eqb (l_c l mod 2 ^ k) 0 &&
   forallb (fun '(x, c) => if Pos.eqb x y then Z.eqb c 1 else Z.eqb (c mod 2 ^ k) 0) (l_t l) &&
   Nat.eqb (List.length (List.filter (fun '(x, _) => Pos.eqb x y) (l_t l))) 1)%bool.
Fixpoint lowbits_find (fs : list fact) (y : positive) (k : Z) : option Z :=
  match fs with
  | [] => None
  | FBits l m v :: fs' => if (low_ok y k l && Z.eqb (Z.land m (2 ^ k - 1)) (2 ^ k - 1))%bool then Some (Z.land v (2 ^ k - 1)) else lowbits_find fs' y k
  | _ :: fs' => lowbits_find fs' y k
  end.
Definition hx_lowbits (y : positive) (k : Z) (S : sst) : option sst :=
  match lowbits_find (s_facts S) y k with
  | Some c => let f := FRange (lvar y) c c in
              if (Z.leb 0 k && Z.leb k 63 && Z.leb (snd (irange (s_facts S) (lvar y))) (2 ^ k - 1) && fwf (s_next S) f)%bool then Some (add_fact S f) else None
  | None => None
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint frange_syn (fs : list fact) (l : lin) : option (Z * Z) :=
  match fs with
  | [] => None
  | FRange l' lo hi :: fs' => if lin_eqb l' l then Some (lo, hi) else frange_syn fs' l
  | _ :: fs' => frange_syn fs' l
  end.
Definition frange_best (fs : list fact) (l : lin) : Z * Z := match frange_syn fs l with Some r => r | None => irange_x fs l end.
Definition hx_fsum (l1 l2 : lin) (S : sst) : option sst :=
  let r1 := frange_best (s_facts S) l1 in let r2 := frange_best (s_facts S) l2 in
  let f := FRange (ladd l1 l2) (fst r1 + fst r2) (snd r1 + snd r2) in
  if (Z.ltb (snd r1 + snd r2) two64 && fwf (s_next S) f)%bool then Some (add_fact S f) else None.
(* [comment removed for export] *)
Definition hx_namer (k : positive) (S : sst) : option sst :=
  let l := rget (s_regs S) k in let n := s_next S in
  if (lwf n l && negb (Pos.eqb k xH))%bool
  then Some (SST (s_pc S) (rset (s_regs S) k (lvar n)) (s_rgs S) (FRange (lsub (lvar n) l) 0 0 :: s_facts S) (Pos.succ n) (s_resv S))
  else None.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition frange_nm (fs : list fact) (l : lin) : Z * Z := match is_const l with Some c => (c, c) | None => frange_best fs l end.
Definition hx_namel (l : lin) (S : sst) : option sst :=
  let n := s_next S in let r := frange_nm (s_facts S) l in
  if lwf n l
  then Some (SST (s_pc S) (s_regs S) (s_rgs S) (FRange (lsub (lvar n) l) 0 0 :: FRange (lvar n) (fst r) (snd r) :: s_facts S) (Pos.succ n) (s_resv S))
  else None.
Definition hx_subf (f : fact) (S : sst) : option sst :=
  match f with
  | FRange l lo hi => if (frange_sub2 (s_facts S) l lo hi && fwf (s_next S) f)%bool then Some (add_fact S f) else None
  | _ => None
  end.
(* [comment removed for export] *)
Fixpoint hx_subfs (l : list fact) (S : sst) : sst :=
  match l with [] => S | f :: l' => hx_subfs l' (match hx_subf f S with Some S' => S' | None => S end) end.

Section Rule.
Variable segs : list Segment.
Definition hcall_rule1 (S K : sst) : Prop :=
  forall E ms, sden segs E S ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next S) E E'' /\
    (forall x, fr_pt E (s_rgs S) x -> ms_mem ms'' x = ms_mem ms x).

#[using="Type"] Theorem hx_scale_ok : forall l s S K, hx_scale l s S = Some K ->
  hcall_rule1 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l s S K H. unfold hx_scale in H.
  destruct (scale_fact (s_facts S) l s) as [f|] eqn:Hf; [|discriminate].
  destruct (fwf (s_next S) f) eqn:Hw; [|discriminate]. injection H as <-.
  split; [|split; [cbn [s_next add_fact]; apply Pos.le_refl | reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  apply (fx_add_fact segs E S ms f Hd Hw).
  destruct (Hd E (agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & HF & _).
  exact (scale_fact_ok E (s_facts S) l s f HF Hf).
Qed.
#[using="Type"] Theorem hx_subf_ok : forall f S K, hx_subf f S = Some K ->
  hcall_rule1 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f S K H. unfold hx_subf in H. destruct f as [c a b tk|l lo hi|g k' r'|g m' v'|x' v' j'|xb bsb]; try discriminate.
  destruct (frange_sub2 (s_facts S) l lo hi && fwf (s_next S) (FRange l lo hi))%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hs Hw].
  split; [|split; [cbn [s_next add_fact]; apply Pos.le_refl | reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  apply (fx_add_fact segs E S ms (FRange l lo hi) Hd Hw).
  destruct (Hd E (agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [fact_ok].
  exact (frange_sub2_ok E (s_facts S) l lo hi HF Hs).
Qed.
#[using="Type"] Theorem hx_ixf_ok : forall l S K, hx_ixf l S = Some K ->
  hcall_rule1 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l S K H. unfold hx_ixf in H. cbv zeta in H.
  destruct (fwf (s_next S) (FRange l (fst (irange_x (s_facts S) l)) (snd (irange_x (s_facts S) l)))) eqn:Hw; [|discriminate]. injection H as <-.
  split; [|split; [cbn [s_next add_fact]; apply Pos.le_refl | reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  apply (fx_add_fact segs E S ms _ Hd Hw).
  destruct (Hd E (agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [fact_ok].
  exact (irange_x_sound E (s_facts S) l HF).
Qed.
#[using="Type"] Lemma tsum_low : forall E y k t, 0 <= k ->
  forallb (fun '(x, c) => if Pos.eqb x y then Z.eqb c 1 else Z.eqb (c mod 2 ^ k) 0) t = true ->
  (tsum E t) mod 2 ^ k = (Z.of_nat (List.length (List.filter (fun '(x, _) => Pos.eqb x y) t)) * bv_unsigned (E y)) mod 2 ^ k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E y k t Hk. assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  induction t as [|[x c] t IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [Hx Ht]. specialize (IH Ht). cbn [tsum List.filter].
  destruct (Pos.eqb x y) eqn:Exy.
  - apply Z.eqb_eq in Hx. apply Pos.eqb_eq in Exy. subst x c. cbn [List.length]. unfold vz.
    rewrite Nat2Z.inj_succ. rewrite Z.add_mod by lia. rewrite IH. rewrite <- Z.add_mod by lia. f_equal. lia.
  - apply Z.eqb_eq in Hx. unfold vz. rewrite Z.add_mod by lia. rewrite IH.
    rewrite <- (Z.mul_mod_idemp_l c) by lia. rewrite Hx. rewrite Z.mul_0_l. rewrite Z.mod_0_l by lia. rewrite Z.add_0_l. apply Z.mod_mod. lia.
Qed.
#[using="Type"] Lemma lowbits_find_ok : forall E fs y k c, 0 <= k <= 63 -> Forall (fact_ok E) fs -> lowbits_find fs y k = Some c ->
  bv_unsigned (E y) mod 2 ^ k = c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs y k c Hk HF. induction HF as [|f fs Hok HF IH]; intros H; cbn [lowbits_find] in H; [discriminate|].
  destruct f as [cc a b tk|l lo hi|g k' r'|l m v|x' v' j'|xb bsb]; try exact (IH H).
  destruct (low_ok y k l && Z.eqb (Z.land m (2 ^ k - 1)) (2 ^ k - 1))%bool eqn:Hc; [|exact (IH H)].
  injection H as <-. apply andb_prop in Hc as [Hl Hm]. apply Z.eqb_eq in Hm.
  unfold low_ok in Hl. apply andb_prop in Hl as [Hl Hn]. apply andb_prop in Hl as [Hc0 Hts].
  apply Z.eqb_eq in Hc0. apply Nat.eqb_eq in Hn. cbn [fact_ok] in Hok.
  assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : (2 ^ k | two64)).
  { rewrite two64_eq. exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  assert (Hul : bv_unsigned (lden E l) mod 2 ^ k = bv_unsigned (E y) mod 2 ^ k).
  { unfold lden. rewrite u_Z_to_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    rewrite <- (Znumtheory.Zmod_div_mod (2 ^ k) two64 (lz E l) Hp ltac:(rewrite two64_eq; lia) Hdiv).
    unfold lz. rewrite Z.add_mod by lia. rewrite Hc0, Z.add_0_l, Z.mod_mod by lia.
    rewrite (tsum_low E y k (l_t l) (proj1 Hk) Hts). rewrite Hn. f_equal. lia. }
  rewrite <- Hul. rewrite <- Hok.
  rewrite <- Z.land_assoc, Hm.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. reflexivity.
Qed.
#[using="Type"] Theorem hx_lowbits_ok : forall y k S K, hx_lowbits y k S = Some K ->
  hcall_rule1 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros y k S K H. unfold hx_lowbits in H.
  destruct (lowbits_find (s_facts S) y k) as [c|] eqn:Hf; [|discriminate].
  destruct (Z.leb 0 k && Z.leb k 63 && Z.leb (snd (irange (s_facts S) (lvar y))) (2 ^ k - 1) && fwf (s_next S) (FRange (lvar y) c c))%bool eqn:Hb; [|discriminate].
  injection H as <-. apply andb_prop in Hb as [Hb Hw]. apply andb_prop in Hb as [Hb Hr]. apply andb_prop in Hb as [Hk0 Hk1].
  apply Z.leb_le in Hk0, Hk1, Hr.
  split; [|split; [cbn [s_next add_fact]; apply Pos.le_refl | reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  apply (fx_add_fact segs E S ms _ Hd Hw).
  destruct (Hd E (agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [fact_ok]. rewrite lden_lvar.
  pose proof (lowbits_find_ok E (s_facts S) y k c (conj Hk0 Hk1) HF Hf) as Hm.
  pose proof (irange_sound E (s_facts S) (lvar y) HF) as Ry. rewrite lden_lvar in Ry.
  pose proof (bv_unsigned_in_range _ (E y)) as Ru.
  assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mod_small in Hm by lia. lia.
Qed.
#[using="Type"] Lemma frange_best_sound : forall E fs l, Forall (fact_ok E) fs -> fst (frange_best fs l) <= bv_unsigned (lden E l) <= snd (frange_best fs l).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs l HF. unfold frange_best. destruct (frange_syn fs l) as [[lo hi]|] eqn:Hs; [|exact (irange_x_sound E fs l HF)].
  cbn [fst snd]. induction fs as [|f fs IH]; cbn [frange_syn] in Hs; [discriminate|].
  inversion HF as [|f0 fs0 Hf HFr]; subst.
  destruct f as [c a b tk|l' lo' hi'|l' k0 r0|l' m0 v0|x0 v0 j0|x0 bs0]; try exact (IH HFr Hs).
  destruct (lin_eqb l' l) eqn:Hl; [|exact (IH HFr Hs)]. injection Hs as <- <-. apply lin_eqb_eq in Hl. subst l'. exact Hf.
Qed.
#[using="Type"] Theorem hx_fsum_ok : forall l1 l2 S K, hx_fsum l1 l2 S = Some K ->
  hcall_rule1 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l1 l2 S K H. unfold hx_fsum in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hb; [|discriminate] end. injection H as <-.
  apply andb_prop in Hb as [Hlt Hw]. apply Z.ltb_lt in Hlt.
  split; [|split; [cbn [s_next add_fact]; apply Pos.le_refl | reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  apply (fx_add_fact segs E S ms _ Hd Hw).
  destruct (Hd E (agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [fact_ok].
  pose proof (frange_best_sound E (s_facts S) l1 HF) as R1. pose proof (frange_best_sound E (s_facts S) l2 HF) as R2.
  pose proof (bv_unsigned_in_range _ (lden E l1)) as U1. pose proof (bv_unsigned_in_range _ (lden E l2)) as U2.
  rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite Z.mod_small by lia. lia.
Qed.
#[using="Type"] Theorem hx_namer_ok : forall k S K, hx_namer k S = Some K ->
  hcall_rule1 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k S K H. unfold hx_namer in H.
  destruct (lwf (s_next S) (rget (s_regs S) k) && negb (Pos.eqb k xH))%bool eqn:Hb; [|discriminate]. injection H as <-.
  apply andb_prop in Hb as [Hw Hk]. apply negb_true_iff in Hk. apply Pos.eqb_neq in Hk.
  set (n := s_next S) in *. set (l := rget (s_regs S) k) in *.
  split; [|split; [cbn [s_next]; lia | reflexivity]].
  intros E ms Hd. set (E2 := upd E n (lden E l)).
  assert (Ha : agree n E E2) by apply agree_upd.
  exists ms, E2. split; [apply ist_refl|]. split; [|split; [exact Ha | intros x _; reflexivity]].
  intros E' HE'. cbn [s_next] in HE'.
  assert (Ha' : agree n E E').
  { intros x Hx. rewrite (Ha x Hx). apply HE'. lia. }
  destruct (Hd E' Ha') as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  assert (Hy : E' n = lden E' l).
  { rewrite <- (HE' n ltac:(lia)). unfold E2, upd. rewrite Pos.eqb_refl. apply (lden_agree n E E' l Hw Ha'). }
  unfold sden0. cbn [s_pc s_resv s_regs s_rgs s_facts].
  refine (conj P1 (conj P2 (conj P3 (conj _ (conj P5 (conj P6 (conj _ P8))))))).
  - intros r. destruct (Pos.eq_dec (rkey r) k) as [Hr|Hr].
    + rewrite Hr, rget_rset_same by exact Hk. rewrite lden_lvar, Hy. rewrite (P4 r), Hr. reflexivity.
    + rewrite rget_rset_other by exact Hr. exact (P4 r).
  - constructor; [|exact P7]. cbn [fact_ok]. rewrite lden_lsub, lden_lvar, Hy.
    rewrite bv_sub_unsigned. unfold bv_wrap. rewrite Z.sub_diag. rewrite Z.mod_0_l by (unfold bv_modulus; cbn; lia). lia.
Qed.
#[using="Type"] Theorem hx_namel_ok : forall l S K, hx_namel l S = Some K ->
  hcall_rule1 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l S K H. unfold hx_namel in H.
  destruct (lwf (s_next S) l) eqn:Hw; [|discriminate]. injection H as <-.
  set (n := s_next S) in *.
  split; [|split; [cbn [s_next]; lia | reflexivity]].
  intros E ms Hd. set (E2 := upd E n (lden E l)).
  assert (Ha : agree n E E2) by apply agree_upd.
  exists ms, E2. split; [apply ist_refl|]. split; [|split; [exact Ha | intros x _; reflexivity]].
  intros E' HE'. cbn [s_next] in HE'.
  assert (Ha' : agree n E E').
  { intros x Hx. rewrite (Ha x Hx). apply HE'. lia. }
  destruct (Hd E' Ha') as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  assert (Hy : E' n = lden E' l).
  { rewrite <- (HE' n ltac:(lia)). unfold E2, upd. rewrite Pos.eqb_refl. apply (lden_agree n E E' l Hw Ha'). }
  unfold sden0. cbn [s_pc s_resv s_regs s_rgs s_facts].
  refine (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj _ P8))))))).
  constructor; [|constructor; [|exact P7]].
  - cbn [fact_ok]. rewrite lden_lsub, lden_lvar, Hy.
    rewrite bv_sub_unsigned. unfold bv_wrap. rewrite Z.sub_diag. rewrite Z.mod_0_l by (unfold bv_modulus; cbn; lia). lia.
  - cbn [fact_ok]. rewrite lden_lvar, Hy. unfold frange_nm. destruct (is_const l) as [c|] eqn:Hc.
    + cbn [fst snd]. rewrite (is_const_u E' l c Hc). lia.
    + exact (frange_best_sound E' (s_facts S) l P7).
Qed.
#[using="Type"] Lemma hx_subf_den : forall f S K, hx_subf f S = Some K ->
  (forall E ms, sden segs E S ms -> sden segs E K ms) /\ s_next K = s_next S /\ s_rgs K = s_rgs S.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f S K H. unfold hx_subf in H. destruct f as [c a b tk|l lo hi|g k' r'|g m' v'|x' v' j'|xb bsb]; try discriminate.
  destruct (frange_sub2 (s_facts S) l lo hi && fwf (s_next S) (FRange l lo hi))%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hs Hw]. split; [|split; reflexivity].
  intros E ms Hd. apply (fx_add_fact segs E S ms (FRange l lo hi) Hd Hw).
  destruct (Hd E (agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [fact_ok].
  exact (frange_sub2_ok E (s_facts S) l lo hi HF Hs).
Qed.
#[using="Type"] Lemma hx_subfs_den : forall l S,
  (forall E ms, sden segs E S ms -> sden segs E (hx_subfs l S) ms) /\ s_next (hx_subfs l S) = s_next S /\ s_rgs (hx_subfs l S) = s_rgs S.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction l as [|f l IH]; intros S; cbn [hx_subfs]; [split; [intros E ms Hd; exact Hd | split; reflexivity]|].
  destruct (hx_subf f S) as [S1|] eqn:H1; [|exact (IH S)].
  destruct (hx_subf_den f S S1 H1) as (D1 & N1 & R1). destruct (IH S1) as (D2 & N2 & R2).
  split; [intros E ms Hd; exact (D2 E ms (D1 E ms Hd)) | split; [rewrite N2; exact N1 | rewrite R2; exact R1]].
Qed.
#[using="Type"] Theorem hx_subfs_ok : forall l S, hcall_rule1 S (hx_subfs l S) /\ (s_next S <= s_next (hx_subfs l S))%positive /\ shape (s_rgs (hx_subfs l S)) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l S. destruct (hx_subfs_den l S) as (D & N & R).
  split; [|split; [rewrite N; apply Pos.le_refl | rewrite R; reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [exact (D E ms Hd)|]. split; [intros x Hx; reflexivity | intros x _; reflexivity].
Qed.
End Rule.
(* [comment removed for export] *)
