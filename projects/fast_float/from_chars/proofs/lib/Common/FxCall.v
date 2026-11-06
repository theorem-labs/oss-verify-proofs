(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.

Module HxDerive.
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
Local Open Scope Z_scope.

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
End HxDerive.

Module HxListNodes.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.HxDerive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition syn_range (fs : list fact) (l : lin) : option (Z * Z) :=
  match l with
  | LIN 0 [(z, 1)] => Some (var_range fs z)
  | _ => frange_syn fs l
  end.
Definition tighter (r d : Z * Z) : bool := if Z.ltb (snd r) (snd d) then true else Z.ltb (fst d) (fst r).
Definition ixf1 (l : lin) (S : sst) : sst :=
  let fs := s_facts S in
  let r := irange_x fs l in
  if (match syn_range fs l with Some d => tighter r d | None => true end)
  then (let f := FRange l (fst r) (snd r) in if fwf (s_next S) f then add_fact S f else S)
  else S.
Fixpoint ixfl_go (ls : list lin) (S : sst) : sst := match ls with [] => S | l :: ls' => ixfl_go ls' (ixf1 l S) end.
Definition hx_ixfl (ls : list lin) (S : sst) : option sst := Some (ixfl_go ls S).

Definition fsum1 (p : lin * lin) (S : sst) : sst := match hx_fsum (fst p) (snd p) S with Some K => K | None => S end.
Fixpoint fsuml_go (ps : list (lin * lin)) (S : sst) : sst := match ps with [] => S | p :: ps' => fsuml_go ps' (fsum1 p S) end.
Definition hx_fsuml (ps : list (lin * lin)) (S : sst) : option sst := Some (fsuml_go ps S).

Section Rule.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition adds (S K : sst) : Prop :=
  (forall E ms, sden segs E S ms -> sden segs E K ms) /\ s_next K = s_next S /\ s_rgs K = s_rgs S.
#[using="Type"] Lemma adds_refl : forall S, adds S S.
Proof. LiaFast.lf_pins LiaFast.u0. intros S. split; [intros E ms H; exact H | split; reflexivity]. Qed.
#[using="Type"] Lemma adds_trans : forall S K L, adds S K -> adds K L -> adds S L.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S K L (H1 & N1 & R1) (H2 & N2 & R2). split; [intros E ms H; exact (H2 E ms (H1 E ms H))|].
  split; [rewrite N2; exact N1 | rewrite R2; exact R1].
Qed.
#[using="Type"] Lemma adds_rule : forall S K, adds S K ->
  hcall_rule1 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S K (H & N & R). split; [|split; [rewrite N; apply Pos.le_refl | rewrite R; reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [exact (H E ms Hd)|].
  split; [intros x Hx; reflexivity | intros x _; reflexivity].
Qed.
#[using="Type"] Lemma adds_fact : forall S f, fwf (s_next S) f = true ->
  (forall E, Forall (fact_ok E) (s_facts S) -> fact_ok E f) -> adds S (add_fact S f).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S f Hw Hf. split; [|split; reflexivity].
  intros E ms Hd. apply (fx_add_fact segs E S ms f Hd Hw).
  destruct (Hd E (agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & HF & _). exact (Hf E HF).
Qed.

#[using="Type"] Lemma ixf1_adds : forall l S, adds S (ixf1 l S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l S. unfold ixf1. cbv zeta.
  destruct (match syn_range (s_facts S) l with Some d => tighter (irange_x (s_facts S) l) d | None => true end); [|apply adds_refl].
  destruct (fwf (s_next S) (FRange l (fst (irange_x (s_facts S) l)) (snd (irange_x (s_facts S) l)))) eqn:Hw; [|apply adds_refl].
  apply (adds_fact S _ Hw). intros E HF. cbn [fact_ok]. exact (irange_x_sound E (s_facts S) l HF).
Qed.
#[using="Type"] Lemma ixfl_go_adds : forall ls S, adds S (ixfl_go ls S).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction ls as [|l ls IH]; intros S; cbn [ixfl_go]; [apply adds_refl|].
  exact (adds_trans _ _ _ (ixf1_adds l S) (IH (ixf1 l S))).
Qed.
#[using="Type"] Theorem hx_ixfl_ok : forall ls S K, hx_ixfl ls S = Some K ->
  hcall_rule1 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0. intros ls S K H. unfold hx_ixfl in H. injection H as <-. exact (adds_rule _ _ (ixfl_go_adds ls S)). Qed.

#[using="Type"] Lemma fsum1_adds : forall p S, adds S (fsum1 p S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [l1 l2] S. unfold fsum1. cbn [fst snd]. destruct (hx_fsum l1 l2 S) as [K|] eqn:H; [|apply adds_refl].
  unfold hx_fsum in H. cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hb; [|discriminate] end. injection H as <-.
  apply andb_prop in Hb as [Hlt Hw]. apply Z.ltb_lt in Hlt.
  apply (adds_fact S _ Hw). intros E HF. cbn [fact_ok].
  pose proof (frange_best_sound E (s_facts S) l1 HF) as R1. pose proof (frange_best_sound E (s_facts S) l2 HF) as R2.
  pose proof (bv_unsigned_in_range _ (lden E l1)) as U1. pose proof (bv_unsigned_in_range _ (lden E l2)) as U2.
  rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite Z.mod_small by lia. lia.
Qed.
#[using="Type"] Lemma fsuml_go_adds : forall ps S, adds S (fsuml_go ps S).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction ps as [|p ps IH]; intros S; cbn [fsuml_go]; [apply adds_refl|].
  exact (adds_trans _ _ _ (fsum1_adds p S) (IH (fsum1 p S))).
Qed.
#[using="Type"] Theorem hx_fsuml_ok : forall ps S K, hx_fsuml ps S = Some K ->
  hcall_rule1 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0. intros ps S K H. unfold hx_fsuml in H. injection H as <-. exact (adds_rule _ _ (fsuml_go_adds ps S)). Qed.
End Rule.
End HxListNodes.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition all_fin (fin : sst -> bool) (o : option (list sst)) : bool :=
  match o with Some l => forallb fin l | None => false end.

Lemma all_fin_sound : forall fin o, all_fin fin o = true -> exists l, o = Some l /\ (forall L, In L l -> fin L = true).
Proof.
  intros fin [l|] H; [|discriminate]. exists l. split; [reflexivity|]. intros L HL. unfold all_fin in H.
  rewrite forallb_forall in H. exact (H L HL).
Qed.

(* [comment removed for export] *)
Fixpoint tfold_acc {A B} (f : positive -> A -> B -> B) (t : tree A) (k : positive -> positive) (acc : B) : B :=
  match t with
  | TEmpty => acc
  | TNode l v r =>
      let acc1 := match v with Some x => f (k xH) x acc | None => acc end in
      tfold_acc f r (fun p => k (xI p)) (tfold_acc f l (fun p => k (xO p)) acc1)
  end.
Definition tfold {A B} (f : positive -> A -> B -> B) (t : tree A) (acc : B) : B := tfold_acc f t (fun p => p) acc.

(* [comment removed for export] *)
Definition bind_bv (vp vs : bval) (σ : tree lin) : tree lin :=
  match vp, vs with BV lp j, BV ls j' => if Z.eqb j j' then bind_bare lp ls σ else σ | _, _ => σ end.
Definition bind_cont (cs cp : tree bval) (σ : tree lin) : tree lin :=
  tfold (fun p vp acc => match tget p cs with Some vs => bind_bv vp vs acc | None => acc end) cp σ.
Fixpoint bind_rgs (rs rp : list region) (σ : tree lin) : tree lin :=
  match rs, rp with
  | R :: rs', R' :: rp' => bind_rgs rs' rp' (bind_cont (rg_cont R) (rg_cont R') σ)
  | _, _ => σ
  end.
Definition mq (s Q : sst) : tree lin := bind_rgs (s_rgs s) (s_rgs Q) (match_st s Q).
(* [comment removed for export] *)
Fixpoint bind_sizes (rs rp : list region) (σ : tree lin) : tree lin :=
  match rs, rp with
  | R :: rs', R' :: rp' => bind_sizes rs' rp' (bind_any (rg_size R') (rg_size R) σ)
  | _, _ => σ
  end.
Definition mcall (Lw P0 : sst) : tree lin := bind_sizes (s_rgs Lw) (s_rgs P0) (mq Lw P0).

(* [comment removed for export] *)
Definition fin_q (Q : sst) (rets : list Z) (n0 : positive) (L : sst) : bool :=
  let σ := mq L (with_pc Q (s_pc L)) in
  (existsb (Z.eqb (s_pc L)) rets && match s_resv L with RNone => true | _ => false end &&
   entails L (with_pc Q (s_pc L)) σ && fixed_below σ n0)%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint pos_rng (k : nat) (p : positive) (acc : list positive) : list positive :=
  match k with O => acc | S k' => pos_rng k' (Pos.succ p) (p :: acc) end.
Definition vars_below (n0 : positive) : list positive := pos_rng (Pos.to_nat n0 - 1) 1 [].
Lemma in_pos_rng : forall k p acc x, In x (pos_rng k p acc) <-> ((Pos.to_nat p <= Pos.to_nat x < Pos.to_nat p + k)%nat \/ In x acc).
Proof.
  induction k as [|k IH]; intros p acc x; cbn [pos_rng].
  - split; [intros H; right; exact H | intros [H|H]; [lia | exact H]].
  - rewrite IH. rewrite Pos2Nat.inj_succ. split.
    + intros [H|[<-|H]]; [left; lia | left; lia | right; exact H].
    + intros [H|H]; [|right; right; exact H].
      destruct (Pos.eq_dec x p) as [->|Hne]; [right; left; reflexivity|]. left.
      assert (Pos.to_nat x <> Pos.to_nat p) by (intros E; apply Hne; apply Pos2Nat.inj; exact E). lia.
Qed.
Lemma in_vars_below : forall n0 x, (x < n0)%positive -> In x (vars_below n0).
Proof. intros n0 x H. unfold vars_below. apply in_pos_rng. left. rewrite Pos2Nat.inj_1. pose proof (Pos2Nat.is_pos x). lia. Qed.
Lemma vars_below_lt : forall n0 x, In x (vars_below n0) -> (x < n0)%positive.
Proof.
  intros n0 x H. unfold vars_below in H. apply in_pos_rng in H as [H|H]; [|destruct H]. rewrite Pos2Nat.inj_1 in H.
  apply Pos2Nat.inj_lt. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Fn.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition is_ret (p : Z) : Prop :=
  exists w, fetch_word segs (Z_to_bv 64 p) = Some w /\ is_ecall w = false /\ decode_any w = Some (Jalr (0%bv) (1%bv) (0%bv), 4%Z).

(* [comment removed for export] *)
Definition fn_ok (P0 Q : sst) (rets : list Z) : Prop :=
  forall E ms, sden segs E P0 ms ->
  exists ms' E' p, isteps segs ms ms' /\ In p rets /\ is_ret p /\ sden segs E' (with_pc Q p) ms' /\ agree (s_next P0) E E' /\
    (forall x, fr_pt E (s_rgs P0) x -> ms_mem ms' x = ms_mem ms x).

(* [comment removed for export] *)
Definition fp_inv (Φ : machine_state -> machine_state -> Prop) : Prop :=
  forall a b c, ms_fregs c = ms_fregs b -> ms_fcsr c = ms_fcsr b -> Φ a b -> Φ a c.
#[using="Type"] Lemma fp_inv_true : fp_inv (fun _ _ => True).
Proof. LiaFast.lf_pins LiaFast.u0. intros a b c _ _ _. exact I. Qed.
#[using="Type"] Lemma fp_inv_fpeq : fp_inv fpeq.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b c H1 H2 [H3 H4]. split; [intros r; rewrite H1; apply H3 | congruence]. Qed.
Definition fn_okP (Φ : machine_state -> machine_state -> Prop) (P0 Q : sst) (rets : list Z) : Prop :=
  forall E ms, sden segs E P0 ms ->
  exists ms' E' p, isteps segs ms ms' /\ In p rets /\ is_ret p /\ sden segs E' (with_pc Q p) ms' /\ agree (s_next P0) E E' /\
    (forall x, fr_pt E (s_rgs P0) x -> ms_mem ms' x = ms_mem ms x) /\ Φ ms ms'.
Definition fn_ok_fp (P0 Q : sst) (rets : list Z) : Prop := fn_okP fpeq P0 Q rets.
#[using="Type"] Lemma fn_ok_P : forall P0 Q rets, fn_ok P0 Q rets -> fn_okP (fun _ _ => True) P0 Q rets.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P0 Q rets H E ms Hd. destruct (H E ms Hd) as (ms' & E' & p & H1 & H2 & H3 & H4 & H5 & H6).
  exists ms', E', p. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 I)))))).
Qed.
#[using="Type"] Lemma fn_okP_ok : forall Φ P0 Q rets, fn_okP Φ P0 Q rets -> fn_ok P0 Q rets.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ P0 Q rets H E ms Hd. destruct (H E ms Hd) as (ms' & E' & p & H1 & H2 & H3 & H4 & H5 & H6 & _).
  exists ms', E', p. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

#[using="Type"] Lemma img_ok_empty : img_ok segs TEmpty.
Proof. LiaFast.lf_pins LiaFast.u0. intros p w H. rewrite tget_empty in H. discriminate. Qed.

#[using="Type"] Lemma state_wf_with_pc : forall s p, state_wf (with_pc s p) = state_wf s.
Proof. LiaFast.lf_pins LiaFast.u0. intros s p. reflexivity. Qed.

#[using="Type"] Theorem fn_ok_of_cert : forall t img depth p P0 Q rets,
  tbl_ok segs t -> img_ok segs img ->
  all_fin (fin_q Q rets (s_next P0)) (check t img (vars_below (s_next P0)) depth p P0) = true ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  Forall is_ret rets -> fn_ok P0 Q rets.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth p P0 Q rets Ht Himg Hc Hw1 Hw2 HwQ Hrets E ms Hd.
  destruct (all_fin_sound _ _ Hc) as (finals & Hck & Hfin).
  destruct (check_frame_fr segs t img (vars_below (s_next P0)) depth p P0 finals Ht Himg Hck E ms Hd Hw1 Hw2)
    as (L & ms' & E1 & HL & Hst & Hd1 & Hins & Hfr & _ & _ & _).
  pose proof (Hfin L HL) as HfL. unfold fin_q in HfL.
  set (σ := mq L (with_pc Q (s_pc L))) in HfL.
  apply andb_prop in HfL as [HfL Hfix]. apply andb_prop in HfL as [HfL Hent]. apply andb_prop in HfL as [Hp Hr].
  apply existsb_exists in Hp as (p0 & Hp0 & Hpe). apply Z.eqb_eq in Hpe.
  exists ms', (ecomp E1 σ), (s_pc L). split; [exact Hst|]. split; [rewrite Hpe; exact Hp0|].
  split; [rewrite Forall_forall in Hrets; apply Hrets; rewrite Hpe; exact Hp0|].
  split; [apply (entails_sden segs E1 L (with_pc Q (s_pc L)) σ ms' (sden_0 _ _ _ _ Hd1) Hent); rewrite state_wf_with_pc; exact HwQ|].
  split; [|exact Hfr].
  intros x Hx. rewrite <- (fixed_below_agree E1 σ (s_next P0) Hfix x Hx). symmetry. apply Hins. apply in_vars_below. exact Hx.
Qed.
End Fn.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint telems_acc {A} (t : tree A) (k : positive -> positive) (acc : list (positive * A)) : list (positive * A) :=
  match t with
  | TEmpty => acc
  | TNode l v r =>
      telems_acc l (fun p => k (xO p)) (telems_acc r (fun p => k (xI p)) (match v with Some x => (k xH, x) :: acc | None => acc end))
  end.
Definition telems {A} (t : tree A) : list (positive * A) := telems_acc t (fun p => p) [].

Lemma telems_acc_spec : forall {A} (t : tree A) k acc p x, In (p, x) (telems_acc t k acc) ->
  In (p, x) acc \/ exists q, p = k q /\ tget q t = Some x.
Proof.
  intros A t. induction t as [|l IHl v r IHr]; intros k acc p x H; cbn [telems_acc] in H; [left; exact H|].
  destruct (IHl _ _ p x H) as [H1|(q & -> & Hq)]; [|right; exists (xO q); split; [reflexivity | exact Hq]].
  destruct (IHr _ _ p x H1) as [H2|(q & -> & Hq)]; [|right; exists (xI q); split; [reflexivity | exact Hq]].
  destruct v as [y|]; [|left; exact H2].
  destruct H2 as [E|H2]; [injection E as <- <-; right; exists xH; split; reflexivity | left; exact H2].
Qed.
Lemma telems_spec : forall {A} (t : tree A) p x, In (p, x) (telems t) -> tget p t = Some x.
Proof.
  intros A t p x H. destruct (telems_acc_spec t (fun p => p) [] p x H) as [[]|(q & -> & Hq)]. exact Hq.
Qed.
Lemma telems_acc_mono : forall {A} (t : tree A) k acc y, In y acc -> In y (telems_acc t k acc).
Proof.
  intros A t. induction t as [|l IHl v r IHr]; intros k acc y H; cbn [telems_acc]; [exact H|].
  apply IHl. apply IHr. destruct v; [right; exact H | exact H].
Qed.
Lemma telems_acc_complete : forall {A} (t : tree A) k acc p x, tget p t = Some x -> In (k p, x) (telems_acc t k acc).
Proof.
  intros A t. induction t as [|l IHl v r IHr]; intros k acc p x H.
  - rewrite tget_empty in H. discriminate.
  - cbn [telems_acc]. destruct p as [p|p|]; cbn [tget] in H.
    + apply telems_acc_mono. exact (IHr (fun q => k (xI q)) _ p x H).
    + exact (IHl (fun q => k (xO q)) _ p x H).
    + subst v. apply telems_acc_mono. apply telems_acc_mono. left. reflexivity.
Qed.
Lemma telems_complete : forall {A} (t : tree A) p x, tget p t = Some x -> In (p, x) (telems t).
Proof. intros A t p x H. exact (telems_acc_complete t (fun p => p) [] p x H). Qed.

Fixpoint tfilter_acc {A} (f : positive -> bool) (t : tree A) (k : positive -> positive) : tree A :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r => TNode (tfilter_acc f l (fun p => k (xO p))) (if f (k xH) then v else None) (tfilter_acc f r (fun p => k (xI p)))
  end.
Definition tfilter {A} (f : positive -> bool) (t : tree A) : tree A := tfilter_acc f t (fun p => p).

Lemma tget_tfilter_acc : forall {A} f (t : tree A) k p, tget p (tfilter_acc f t k) = if f (k p) then tget p t else None.
Proof.
  intros A f t. induction t as [|l IHl v r IHr]; intros k p; cbn [tfilter_acc].
  - rewrite !tget_empty. destruct (f (k p)); reflexivity.
  - destruct p as [p|p|]; cbn [tget]; [exact (IHr (fun q => k (xI q)) p) | exact (IHl (fun q => k (xO q)) p) | reflexivity].
Qed.
Lemma tget_tfilter : forall {A} f (t : tree A) p, tget p (tfilter f t) = if f p then tget p t else None.
Proof. intros A f t p. exact (tget_tfilter_acc f t (fun p => p) p). Qed.

Definition put_list {A} (acc : tree A) (l : list (positive * A)) : tree A := fold_left (fun a '(p, v) => tset p v a) l acc.

Lemma tget_put_list : forall {A} (l : list (positive * A)) acc p v, tget p (put_list acc l) = Some v -> In (p, v) l \/ tget p acc = Some v.
Proof.
  intros A l. induction l as [|[q w] l IH]; intros acc p v H; cbn [put_list fold_left] in H; [right; exact H|].
  destruct (IH _ p v H) as [H1|H1]; [left; right; exact H1|].
  destruct (Pos.eq_dec p q) as [->|Hne]; [rewrite tget_tset_same in H1; injection H1 as ->; left; left; reflexivity|].
  rewrite tget_tset_other in H1 by (intros Hc; apply Hne; symmetry; exact Hc). right. exact H1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive vop : Type := VCopy (i : nat) | VSub (i : nat) (o : Z).
Definition vop_src (v : vop) : nat := match v with VCopy i | VSub i _ => i end.

Definition cont_sub (c' c : tree bval) : bool :=
  tforall (fun p v => match tget p c with Some v' => bval_eqb v v' | None => false end) c'.
Definition view1_ok (rgs : list region) (R' : region) (v : vop) : bool :=
  match v with
  | VCopy i => match nth_error rgs i with
               | Some R => (lin_eqb (rg_base R') (rg_base R) && lin_eqb (rg_size R') (rg_size R) && rkind_eqb (rg_kind R') (rg_kind R) &&
                            cont_sub (rg_cont R') (rg_cont R) &&
                            match rg_kind R with RZ | RI => cont_sub (rg_cont R) (rg_cont R') | _ => true end)%bool
               | None => false end
  | VSub i o => match nth_error rgs i with Some R => rg_sub_ok R R' o | None => false end
  end.
Fixpoint views_ok (rgs rgs_w : list region) (vs : list vop) : bool :=
  match rgs_w, vs with
  | [], [] => true
  | R' :: rs', v :: vs' => (view1_ok rgs R' v && views_ok rgs rs' vs')%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition vpair_ok (a b : vop * region) : bool :=
  let '(v1, R1) := a in let '(v2, R2) := b in
  match v1, v2 with
  | VSub i o, VSub j p => (negb (Nat.eqb i j) || Z.leb (o + csz R1) p || Z.leb (p + csz R2) o)%bool
  | _, _ => negb (Nat.eqb (vop_src v1) (vop_src v2))
  end.
Fixpoint vpairs_ok (l : list (vop * region)) : bool :=
  match l with [] => true | a :: l' => (forallb (vpair_ok a) l' && vpairs_ok l')%bool end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Fixpoint sigq_acc (σc : tree lin) (n0 nL : positive) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => let y := Pos.of_nat k in
            sigq_acc σc n0 nL k' (tset y (if Pos.ltb y n0 then svar σc y else lvar (nL + y - n0)) acc)
  end.
Definition sigq (σc : tree lin) (n0 nQ nL : positive) : tree lin := sigq_acc σc n0 nL (Pos.to_nat nQ - 1) TEmpty.

(* [comment removed for export] *)
Fixpoint wviews (P0 : list region) (vs : list vop) (k : nat) (i : nat) : list (nat * Z) :=
  match P0, vs with
  | R :: P', v :: vs' =>
      let rest := wviews P' vs' (S k) i in
      if (wkind (rg_kind R) && Nat.eqb (vop_src v) i)%bool then (k, match v with VCopy _ => 0 | VSub _ o => o end) :: rest else rest
  | _, _ => []
  end.
(* [comment removed for export] *)
Definition imp_cont (Q : list region) (σ' : tree lin) (ks : list (nat * Z)) (base : tree bval) : tree bval :=
  put_list base
    (flat_map (fun '(k, o) => match nth_error Q k with
                              | Some RQ => List.map (fun '(q, v) => (okey (o + (Zpos q - 1)), bsubst σ' v)) (telems (rg_cont RQ))
                              | None => [] end) ks).

(* [comment removed for export] *)
Definition rz_keep (Q : list region) (R : region) (ks : list (nat * Z)) : bool :=
  (match rg_kind R with RZ => true | _ => false end &&
   tforall (fun _ v => match v with BK z => Z.eqb z 0 | _ => false end) (rg_cont R) &&
   forallb (fun '(k, _) => match nth_error Q k with Some RQ => match rg_kind RQ with RZ => true | _ => false end | None => false end) ks)%bool.
(* [comment removed for export] *)
Definition view_win (σc : tree lin) (P0 : list region) (vs : list vop) (k : nat) : option (Z * Z) :=
  match nth_error vs k, nth_error P0 k with
  | Some (VSub _ o), Some P => match is_const (lsubst σc (rg_size P)) with Some n => Some (o, n) | None => None end
  | _, _ => None
  end.
Definition out_wins (σc : tree lin) (P0 : list region) (vs : list vop) (ks : list (nat * Z)) (j : Z) : bool :=
  forallb (fun '(k, _) => match view_win σc P0 vs k with Some (o, n) => (Z.ltb j o || Z.leb (o + n) j)%bool | None => false end) ks.
Definition keep_out (σc : tree lin) (P0 : list region) (vs : list vop) (ks : list (nat * Z)) (c : tree bval) : tree bval :=
  tfilter (fun p => out_wins σc P0 vs ks (Zpos p - 1)) c.
Definition new_rg (Q P0 : list region) (σc σ' : tree lin) (vs : list vop) (i : nat) (R : region) : region :=
  match wviews P0 vs 0 i with
  | [] => R
  | ks => RG (rg_base R) (rg_size R) (if rz_keep Q R ks then RZ else RW) (imp_cont Q σ' ks (keep_out σc P0 vs ks (rg_cont R)))
  end.

Fixpoint regs_cont (RL RQ : tree lin) (σ' : tree lin) (keep qk : list positive) (nx : positive) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' =>
      let key := Pos.of_succ_nat k in
      regs_cont RL RQ σ' keep qk nx k'
        (rset acc key (if existsb (Pos.eqb key) keep then rget RL key
                       else if existsb (Pos.eqb key) qk then lsubst σ' (rget RQ key) else lvar (nx + Pos.of_nat k)))
  end.

Definition cont_st (L P0 Q : sst) (σc : tree lin) (keep qk : list positive) (vs : list vop) (ret : Z) : sst :=
  let nL := s_next L in let n0 := s_next P0 in let nQ := s_next Q in
  let σ' := sigq σc n0 nQ nL in
  let nx := (nL + nQ - n0)%positive in
  SST ret (regs_cont (s_regs L) (s_regs Q) σ' keep qk nx 31 TEmpty) (map_i (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs) 0 (s_rgs L))
      (s_facts L ++ List.map (fsubst σ') (s_facts Q)) (nx + 32) RNone.

(* [comment removed for export] *)
Definition ra_key : positive := 2.
Definition kinds_ok (P0 Q : list region) : bool :=
  forallb (fun '(R, R') => match rg_kind R, rg_kind R' with
                          | RO, RO | RT, RT => true
                          | RW, k | RZ, k | RI, k => wkind k
                          | _, _ => false end) (combine P0 Q).
Definition call_ok (L P0 Q : sst) (keep qk : list positive) (vs : list vop) (rgs_w : list region) (ret : Z) : bool :=
  let Lw := with_rgs L rgs_w in
  let σc := mcall Lw P0 in
  (views_ok (s_rgs L) rgs_w vs && vpairs_ok (combine vs rgs_w) && state_wf L && state_wf Lw && state_wf P0 && state_wf Q &&
   entails Lw P0 σc && Pos.leb (s_next P0) (s_next Q) &&
   shape_eqb (s_rgs P0) (s_rgs Q) && Nat.eqb (length (s_rgs P0)) (length (s_rgs Q)) && kinds_ok (s_rgs P0) (s_rgs Q) &&
   forallb (fun y => lwf (s_next L) (svar σc y)) (vars_below (s_next P0)) &&
   forallb (fun k => lin_eqb (rget (s_regs Q) k) (rget (s_regs P0) k)) keep && existsb (Pos.eqb ra_key) keep &&
   forallb (fun k => negb (Pos.eqb k xH)) (keep ++ qk) &&
   lin_eqb (rget (s_regs L) ra_key) (lconst ret) && Z.leb 0 ret && Z.ltb ret two64 && Z.eqb (Z.land ret 1) 0 &&
   match s_resv Q with RNone => true | _ => false end && state_wf (cont_st L P0 Q σc keep qk vs ret))%bool.

Definition call_cont (L P0 Q : sst) (keep qk : list positive) (vs : list vop) (rgs_w : list region) (ret : Z) : option sst :=
  if call_ok L P0 Q keep qk vs rgs_w ret then Some (cont_st L P0 Q (mcall (with_rgs L rgs_w) P0) keep qk vs ret) else None.

(* [comment removed for export] *)
Definition frag_ok (L P0 Q : sst) (keep qk : list positive) (vs : list vop) (rgs_w : list region) (pcQ : Z) : bool :=
  let Lw := with_rgs L rgs_w in
  let σc := mcall Lw P0 in
  (views_ok (s_rgs L) rgs_w vs && vpairs_ok (combine vs rgs_w) && state_wf L && state_wf Lw && state_wf P0 && state_wf Q &&
   entails Lw P0 σc && Pos.leb (s_next P0) (s_next Q) &&
   shape_eqb (s_rgs P0) (s_rgs Q) && Nat.eqb (length (s_rgs P0)) (length (s_rgs Q)) && kinds_ok (s_rgs P0) (s_rgs Q) &&
   forallb (fun y => lwf (s_next L) (svar σc y)) (vars_below (s_next P0)) &&
   forallb (fun k => lin_eqb (rget (s_regs Q) k) (rget (s_regs P0) k)) keep &&
   forallb (fun k => negb (Pos.eqb k xH)) (keep ++ qk) &&
   match s_resv Q with RNone => true | _ => false end && state_wf (cont_st L P0 Q σc keep qk vs pcQ))%bool.
Definition frag_cont (L P0 Q : sst) (keep qk : list positive) (vs : list vop) (rgs_w : list region) (pcQ : Z) : option sst :=
  if frag_ok L P0 Q keep qk vs rgs_w pcQ then Some (cont_st L P0 Q (mcall (with_rgs L rgs_w) P0) keep qk vs pcQ) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable segs : list Segment.

#[using="Type"] Lemma cont_sub_spec : forall c' c p v, cont_sub c' c = true -> tget p c' = Some v -> tget p c = Some v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c' c p v H Hp. unfold cont_sub in H. pose proof (tforall_spec _ _ H p v Hp) as Hx. cbv beta in Hx.
  destruct (tget p c) as [v'|]; [|discriminate]. apply bval_eqb_eq in Hx. subst. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma view1_sound : forall E m rgs R' v, Forall (rg_ok segs E m) rgs -> view1_ok rgs R' v = true ->
  exists R, nth_error rgs (vop_src v) = Some R /\ rg_ok segs E m R' /\
    ((exists o, v = VSub (vop_src v) o /\ 0 <= o /\ bv_unsigned (lden E (rg_base R')) = bv_unsigned (lden E (rg_base R)) + o /\
                o + rsz E R' <= rsz E R /\ rsz E R' = csz R') \/
     (v = VCopy (vop_src v) /\ rg_base R' = rg_base R /\ rg_size R' = rg_size R /\ rg_kind R' = rg_kind R)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m rgs R' v HF H. rewrite Forall_nth' in HF. destruct v as [i|i o]; cbn [view1_ok vop_src] in *.
  - destruct (nth_error rgs i) as [R|] eqn:Hi; [|discriminate]. exists R. split; [reflexivity|].
    apply andb_prop in H as [H Hc2]. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hb Hs].
    apply lin_eqb_eq in Hb, Hs. assert (Hk' : rg_kind R' = rg_kind R) by (destruct (rg_kind R'), (rg_kind R); cbn in Hk; try discriminate; reflexivity).
    split; [|right; split; [reflexivity | split; [exact Hb | split; [exact Hs | exact Hk']]]].
    pose proof (HF i R Hi) as HR. unfold rg_ok in HR |- *. cbv zeta in HR |- *. unfold rsz in HR |- *. rewrite Hb, Hs, Hk'.
    destruct HR as (H1 & H2 & H3 & H4). refine (conj H1 (conj H2 (conj _ _))).
    + intros j Hj. specialize (H3 j Hj). destruct (rg_kind R) eqn:EK; try exact H3.
      * destruct H3 as [H3a H3b]. split; [exact H3a|]. intros Hn. apply H3b.
        destruct (tget (okey j) (rg_cont R)) as [w|] eqn:Ew; [|reflexivity].
        pose proof (cont_sub_spec _ _ _ w Hc2 Ew) as X. rewrite Hn in X. discriminate.
      * destruct H3 as [H3a H3b]. split; [exact H3a|]. intros Hn. apply H3b.
        destruct (tget (okey j) (rg_cont R)) as [w|] eqn:Ew; [|reflexivity].
        pose proof (cont_sub_spec _ _ _ w Hc2 Ew) as X. rewrite Hn in X. discriminate.
    + intros p v' Hp. exact (H4 p v' (cont_sub_spec _ _ p v' Hc Hp)).
  - destruct (nth_error rgs i) as [R|] eqn:Hi; [|discriminate]. exists R. split; [reflexivity|].
    destruct (rg_sub_sound segs E m R R' o (HF i R Hi) H) as (HR' & HA & Ho & Hz & Hn & Hq).
    split; [exact HR'|]. left. exists o. split; [reflexivity|]. split; [exact Ho|]. split; [exact HA|]. split; [exact Hn | exact Hq].
Qed.

#[using="Type"] Lemma views_nth : forall rgs rgs_w vs, views_ok rgs rgs_w vs = true ->
  length vs = length rgs_w /\ forall k R' v, nth_error rgs_w k = Some R' -> nth_error vs k = Some v -> view1_ok rgs R' v = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rgs rgs_w. induction rgs_w as [|R' rs IH]; intros [|v vs] H; cbn [views_ok] in H; try discriminate.
  - split; [reflexivity|]. intros [|k]; discriminate.
  - apply andb_prop in H as [H1 H2]. destruct (IH vs H2) as [Hl Hn]. split; [cbn; lia|].
    intros [|k] R0 v0 Hk Hv; cbn [nth_error] in Hk, Hv; [injection Hk as <-; injection Hv as <-; exact H1 | exact (Hn k R0 v0 Hk Hv)].
Qed.

#[using="Type"] Lemma vpairs_nth : forall l, vpairs_ok l = true -> forall k k' a b, (k < k')%nat -> nth_error l k = Some a -> nth_error l k' = Some b -> vpair_ok a b = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction l as [|x l IH]; intros H k k' a b Hkk Ha Hb; [destruct k; discriminate|]. cbn [vpairs_ok] in H. apply andb_prop in H as [H1 H2].
  destruct k as [|k]; destruct k' as [|k']; try lia; cbn [nth_error] in Ha, Hb.
  - injection Ha as <-. rewrite forallb_forall in H1. exact (H1 b (nth_error_In _ _ Hb)).
  - exact (IH H2 k k' a b ltac:(lia) Ha Hb).
Qed.

#[using="Type"] Theorem views_sound : forall E L ms rgs_w vs, sden segs E L ms -> views_ok (s_rgs L) rgs_w vs = true ->
  vpairs_ok (combine vs rgs_w) = true -> state_wf (with_rgs L rgs_w) = true -> sden segs E (with_rgs L rgs_w) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L ms rgs_w vs Hd Hv Hp Hwf. apply sden0_sden; [exact Hwf|].
  destruct (sden_0 _ _ _ _ Hd) as (A & B & C & D & F & G & I & J).
  destruct (views_nth _ _ _ Hv) as [Hl Hn].
  refine (conj A (conj B (conj C (conj D (conj _ (conj _ (conj I J))))))); cbn [s_rgs with_rgs].
  - apply Forall_nth'. intros k R' Hk.
    destruct (nth_error vs k) as [v|] eqn:Hvk; [|apply nth_error_None in Hvk; pose proof (nth_error_Some rgs_w k) as Hs; rewrite Hk in Hs; specialize (proj1 Hs ltac:(discriminate)); lia].
    destruct (view1_sound E _ _ R' v F (Hn k R' v Hk Hvk)) as (R & _ & HR' & _). exact HR'.
  - apply rgs_disj_nth_inv. intros k k' R1 R2 Hkk H1 H2.
    destruct (nth_error vs k) as [v1|] eqn:Hv1; [|apply nth_error_None in Hv1; pose proof (nth_error_Some rgs_w k) as Hs; rewrite H1 in Hs; specialize (proj1 Hs ltac:(discriminate)); lia].
    destruct (nth_error vs k') as [v2|] eqn:Hv2; [|apply nth_error_None in Hv2; pose proof (nth_error_Some rgs_w k') as Hs; rewrite H2 in Hs; specialize (proj1 Hs ltac:(discriminate)); lia].
    pose proof (vpairs_nth _ Hp k k' (v1, R1) (v2, R2) Hkk ltac:(rewrite nth_error_combine', Hv1, H1; reflexivity)
                  ltac:(rewrite nth_error_combine', Hv2, H2; reflexivity)) as Hpr.
    destruct (view1_sound E _ _ R1 v1 F (Hn k R1 v1 H1 Hv1)) as (P1 & HP1 & _ & Hs1).
    destruct (view1_sound E _ _ R2 v2 F (Hn k' R2 v2 H2 Hv2)) as (P2 & HP2 & _ & Hs2).
    unfold vpair_ok in Hpr.
    assert (Hin1 : bv_unsigned (lden E (rg_base P1)) <= bv_unsigned (lden E (rg_base R1)) /\
                   bv_unsigned (lden E (rg_base R1)) + rsz E R1 <= bv_unsigned (lden E (rg_base P1)) + rsz E P1).
    { destruct Hs1 as [(o & _ & Ho & HA & Hn' & _)|(_ & Hb & Hsz & _)]; [lia|]. unfold rsz. rewrite Hb, Hsz. lia. }
    assert (Hin2 : bv_unsigned (lden E (rg_base P2)) <= bv_unsigned (lden E (rg_base R2)) /\
                   bv_unsigned (lden E (rg_base R2)) + rsz E R2 <= bv_unsigned (lden E (rg_base P2)) + rsz E P2).
    { destruct Hs2 as [(o & _ & Ho & HA & Hn' & _)|(_ & Hb & Hsz & _)]; [lia|]. unfold rsz. rewrite Hb, Hsz. lia. }
    destruct (Nat.eq_dec (vop_src v1) (vop_src v2)) as [Heq|Hne].
    + (* [comment removed for export] *)
      rewrite Heq in HP1. rewrite HP1 in HP2. injection HP2 as <-.
      destruct Hs1 as [(oa & Eo1 & Ho1 & HA1 & Hn1 & Hq1)|(Eo1 & _)]; destruct Hs2 as [(ob & Eo2 & Ho2 & HA2 & Hn2 & Hq2)|(Eo2 & _)];
        rewrite Eo1, Eo2 in Hpr; cbn [vop_src] in Hpr; rewrite Heq, Nat.eqb_refl in Hpr; cbn [negb orb] in Hpr; try discriminate.
      unfold rg_disj. rewrite HA1, HA2, Hq1, Hq2. apply orb_prop in Hpr as [Hx|Hx]; apply Z.leb_le in Hx; lia.
    + pose proof (rgs_disj_nth E (s_rgs L) _ _ P1 P2 G Hne HP1 HP2) as Hd12. unfold rg_disj in *. lia.
Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma regs_cont_spec : forall RL RQ σ' keep qk nx k acc key,
  (forall j, (k < j <= 31)%nat -> tget (Pos.of_succ_nat j) acc =
     Some (if existsb (Pos.eqb (Pos.of_succ_nat j)) keep then rget RL (Pos.of_succ_nat j)
           else if existsb (Pos.eqb (Pos.of_succ_nat j)) qk then lsubst σ' (rget RQ (Pos.of_succ_nat j)) else lvar (nx + Pos.of_nat j))) ->
  (k <= 31)%nat ->
  forall j, (1 <= j <= 31)%nat -> key = Pos.of_succ_nat j ->
  rget (regs_cont RL RQ σ' keep qk nx k acc) key
  = if existsb (Pos.eqb key) keep then rget RL key else if existsb (Pos.eqb key) qk then lsubst σ' (rget RQ key) else lvar (nx + Pos.of_nat j).
Proof.
  intros RL RQ σ' keep qk nx k. induction k as [|k IH]; intros acc key Hacc Hk j Hj Hkey; cbn [regs_cont].
  - subst key. rewrite rget_nonxH by (apply succ_nat_nonxH; lia). rewrite (Hacc j ltac:(lia)). reflexivity.
  - apply IH; [| lia | exact Hj | exact Hkey].
    intros j' Hj'. unfold rset.
    assert (Hnx : Pos.of_succ_nat (S k) <> xH) by (apply succ_nat_nonxH; lia).
    destruct (Pos.of_succ_nat (S k)) eqn:E; [| | exfalso; exact (Hnx eq_refl)];
    rewrite <- E; destruct (Nat.eq_dec j' (S k)) as [->|Hne];
      [ rewrite tget_tset_same; reflexivity
      | rewrite tget_tset_other; [apply Hacc; lia|]; intros Hc; apply SuccNat2Pos.inj in Hc; lia
      | rewrite tget_tset_same; reflexivity
      | rewrite tget_tset_other; [apply Hacc; lia|]; intros Hc; apply SuccNat2Pos.inj in Hc; lia ].
Qed.

Lemma regs_cont_get : forall RL RQ σ' keep qk nx j, (1 <= j <= 31)%nat ->
  rget (regs_cont RL RQ σ' keep qk nx 31 TEmpty) (Pos.of_succ_nat j)
  = if existsb (Pos.eqb (Pos.of_succ_nat j)) keep then rget RL (Pos.of_succ_nat j)
    else if existsb (Pos.eqb (Pos.of_succ_nat j)) qk then lsubst σ' (rget RQ (Pos.of_succ_nat j)) else lvar (nx + Pos.of_nat j).
Proof.
  intros RL RQ σ' keep qk nx j Hj. apply (regs_cont_spec RL RQ σ' keep qk nx 31 TEmpty); [| lia | exact Hj | reflexivity].
  intros j' Hj'. lia.
Qed.

Lemma sigq_acc_spec : forall σc n0 nL k acc y,
  (forall y', (k < Pos.to_nat y')%nat -> tget y' acc = tget y' (sigq_acc σc n0 nL k acc)) /\
  ((1 <= Pos.to_nat y <= k)%nat -> tget y (sigq_acc σc n0 nL k acc) = Some (if Pos.ltb y n0 then svar σc y else lvar (nL + y - n0))).
Proof.
  intros σc n0 nL k. induction k as [|k IH]; intros acc y; cbn [sigq_acc].
  - split; [reflexivity | lia].
  - destruct (IH (tset (Pos.of_nat (S k)) (if Pos.ltb (Pos.of_nat (S k)) n0 then svar σc (Pos.of_nat (S k)) else lvar (nL + Pos.of_nat (S k) - n0)) acc) y)
      as [IH1 IH2].
    split.
    + intros y' Hy'. rewrite <- (proj1 (IH (tset (Pos.of_nat (S k)) _ acc) y') y' ltac:(lia)).
      rewrite tget_tset_other; [reflexivity|]. intros Hc. subst y'. rewrite Nat2Pos.id in Hy' by lia. lia.
    + intros Hy. destruct (Nat.eq_dec (Pos.to_nat y) (S k)) as [Hyk|Hyk].
      * rewrite <- (proj1 (IH (tset (Pos.of_nat (S k)) _ acc) y) y ltac:(lia)).
        assert (Hy' : y = Pos.of_nat (S k)) by (rewrite <- Hyk, Pos2Nat.id; reflexivity). subst y.
        rewrite tget_tset_same. reflexivity.
      * apply IH2. lia.
Qed.

Lemma sigq_get : forall σc n0 nQ nL y, (y < nQ)%positive ->
  svar (sigq σc n0 nQ nL) y = if Pos.ltb y n0 then svar σc y else lvar (nL + y - n0).
Proof.
  intros σc n0 nQ nL y Hy. unfold svar at 1, sigq.
  rewrite (proj2 (sigq_acc_spec σc n0 nL (Pos.to_nat nQ - 1) TEmpty y)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Call.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma ret_isteps : forall E L ms, sden segs E L ms -> s_resv L = RNone -> is_ret segs (s_pc L) ->
  isteps segs ms (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (jalr_tgt (getr (ms_regs ms) 1) 0) (ms_mem ms) (ms_rom ms)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L ms Hd Hr (w & Hf & He & Hdec). pose proof (sden_svc segs _ _ _ Hd) as Hs.
  eapply ist_step; [exact Hs| |apply ist_refl].
  rewrite (sden_mkst segs E L ms Hd Hr) at 1.
  rewrite (step_jalr_gen segs (ms_regs ms) (Z_to_bv 64 (s_pc L)) (ms_mem ms) (ms_rom ms) w 0%bv 1%bv 0%bv Hf He Hdec).
  rewrite bv_eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma land_m2_even : forall r, Z.land r 1 = 0 -> Z.land r (-2) = r.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  change (-2) with (Z.lnot 1). rewrite Z.lnot_spec by exact Hn.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - pose proof (f_equal (fun z => Z.testbit z 0) H) as X. cbn beta in X. rewrite Z.land_spec, Z.bits_0 in X.
    change (Z.testbit 1 0) with true in X. rewrite andb_true_r in X. rewrite X. reflexivity.
  - replace (Z.testbit 1 n) with false; [rewrite andb_true_r; reflexivity|].
    symmetry. apply Z.bits_above_log2; [lia | cbn; lia].
Qed.

#[using="Type"] Lemma jalr_tgt_even : forall ret, 0 <= ret < two64 -> Z.land ret 1 = 0 -> jalr_tgt (Z_to_bv 64 ret) 0 = Z_to_bv 64 ret.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ret Hr He. unfold jalr_tgt, jalr_tgtZ. rewrite u_small64 by exact Hr. rewrite Z.add_0_r. f_equal. exact (land_m2_even ret He).
Qed.
End Call.

Section Call2.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_mem : forall E m m' R, rg_ok segs E m R ->
  (forall j, 0 <= j < rsz E R -> m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + j)) = m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + j))) ->
  rg_ok segs E m' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m m' R HR Hm. unfold rg_ok in *. cbv zeta in *. destruct HR as (H1 & H2 & H3 & H4).
  refine (conj H1 (conj H2 (conj _ _))).
  - intros j Hj. specialize (H3 j Hj). unfold rd1, wview in *. rewrite (Hm j Hj). exact H3.
  - intros p v Hp. destruct (H4 p v Hp) as [Hl Hr]. split; [exact Hl|]. unfold rd1 in *. rewrite (Hm (Zpos p - 1) ltac:(lia)). exact Hr.
Qed.

#[using="Type"] Lemma wviews_spec : forall P0s vs k0 i k o, In (k, o) (wviews P0s vs k0 i) ->
  exists Pk v, nth_error P0s (k - k0) = Some Pk /\ nth_error vs (k - k0) = Some v /\ (k0 <= k)%nat /\
    wkind (rg_kind Pk) = true /\ vop_src v = i /\ o = match v with VCopy _ => 0 | VSub _ o' => o' end.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction P0s as [|R P' IH]; intros [|v vs] k0 i k o H; cbn [wviews] in H; try destruct H.
  destruct (wkind (rg_kind R) && Nat.eqb (vop_src v) i)%bool eqn:Hw.
  - destruct H as [E|H].
    + injection E as <- <-. apply andb_prop in Hw as [Hw Hs]. apply Nat.eqb_eq in Hs.
      exists R, v. rewrite Nat.sub_diag. cbn [nth_error]. refine (conj eq_refl (conj eq_refl (conj (le_n _) (conj Hw (conj Hs eq_refl))))).
    + destruct (IH vs (S k0) i k o H) as (Pk & v' & H1 & H2 & H3 & H4 & H5 & H6). exists Pk, v'.
      assert (Ek : (k - k0)%nat = S (k - S k0)) by (clear - H3; lia). rewrite Ek. cbn [nth_error]. refine (conj H1 (conj H2 (conj _ (conj H4 (conj H5 H6))))). clear - H3; lia.
  - destruct (IH vs (S k0) i k o H) as (Pk & v' & H1 & H2 & H3 & H4 & H5 & H6). exists Pk, v'.
    assert (Ek : (k - k0)%nat = S (k - S k0)) by (clear - H3; lia). rewrite Ek. cbn [nth_error]. refine (conj H1 (conj H2 (conj _ (conj H4 (conj H5 H6))))). clear - H3; lia.
Qed.

#[using="Type"] Lemma wviews_nil : forall P0s vs k0 i, wviews P0s vs k0 i = [] ->
  forall k Pk v, nth_error P0s k = Some Pk -> nth_error vs k = Some v -> wkind (rg_kind Pk) = true -> vop_src v <> i.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction P0s as [|R P' IH]; intros [|v0 vs] k0 i H k Pk v HP Hv Hw; try (destruct k; discriminate).
  cbn [wviews] in H. destruct (wkind (rg_kind R) && Nat.eqb (vop_src v0) i)%bool eqn:Hb; [discriminate|].
  destruct k as [|k]; cbn [nth_error] in HP, Hv.
  - injection HP as <-. injection Hv as <-. rewrite Hw in Hb. cbn [andb] in Hb. apply Nat.eqb_neq in Hb. exact Hb.
  - exact (IH vs (S k0) i H k Pk v HP Hv Hw).
Qed.

#[using="Type"] Lemma wviews_in : forall P0s vs k0 i k Pk v, nth_error P0s k = Some Pk -> nth_error vs k = Some v -> wkind (rg_kind Pk) = true -> vop_src v = i ->
  In ((k0 + k)%nat, match v with VCopy _ => 0 | VSub _ o' => o' end) (wviews P0s vs k0 i).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction P0s as [|R P' IH]; intros [|v0 vs] k0 i k Pk v HP Hv Hw Hs; try (destruct k; discriminate).
  cbn [wviews]. destruct k as [|k]; cbn [nth_error] in HP, Hv.
  - injection HP as <-. injection Hv as <-. rewrite Hw, Hs, Nat.eqb_refl. cbn [andb]. left. rewrite Nat.add_0_r. reflexivity.
  - replace (k0 + S k)%nat with (S k0 + k)%nat by lia.
    destruct (wkind (rg_kind R) && Nat.eqb (vop_src v0) i)%bool; [right|]; exact (IH vs (S k0) i k Pk v HP Hv Hw Hs).
Qed.

#[using="Type"] Lemma put_list_some : forall {A} (l : list (positive * A)) acc p v, In (p, v) l -> tget p (put_list acc l) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A l. induction l as [|[q w] l IH]; intros acc p v H; [destruct H|].
  change (put_list acc ((q, w) :: l)) with (put_list (tset q w acc) l).
  destruct H as [H|H].
  - injection H as Hq Hw. subst q w. destruct (in_dec Pos.eq_dec p (List.map fst l)) as [Hin|Hnin].
    + apply in_map_iff in Hin as ([p' v'] & Ep & Hin). cbn in Ep. subst p'. exact (IH _ p v' Hin).
    + assert (G : forall (l' : list (positive * A)) (acc' : tree A), ~ In p (List.map fst l') -> tget p (put_list acc' l') = tget p acc').
      { intros l'. induction l' as [|[q' w'] l' IH']; intros acc' Hn; [reflexivity|].
        change (put_list acc' ((q', w') :: l')) with (put_list (tset q' w' acc') l').
        rewrite IH' by (intros X; apply Hn; right; exact X). apply tget_tset_other. intros X; apply Hn; left; cbn; exact X. }
      rewrite G by exact Hnin. rewrite tget_tset_same. discriminate.
  - exact (IH _ p v H).
Qed.
#[using="Type"] Lemma imp_cont_some : forall Qs σ' ks base k o RQ q w, In (k, o) ks -> nth_error Qs k = Some RQ -> tget q (rg_cont RQ) = Some w ->
  tget (okey (o + (Zpos q - 1))) (imp_cont Qs σ' ks base) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Qs σ' ks base k o RQ q w Hko HQ Hq. unfold imp_cont. apply (put_list_some _ _ _ (bsubst σ' w)).
  apply in_flat_map. exists (k, o). split; [exact Hko|]. rewrite HQ. apply in_map_iff. exists (q, w). split; [reflexivity|].
  exact (telems_complete _ _ _ Hq).
Qed.
#[using="Type"] Lemma in_imp_cont : forall Qs σ' ks base p v, tget p (imp_cont Qs σ' ks base) = Some v ->
  (exists k o RQ q w, In (k, o) ks /\ nth_error Qs k = Some RQ /\ tget q (rg_cont RQ) = Some w /\ p = okey (o + (Zpos q - 1)) /\ v = bsubst σ' w) \/
  tget p base = Some v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Qs σ' ks base p v H. unfold imp_cont in H. destruct (tget_put_list _ _ p v H) as [Hin|Hn]; [left|right; exact Hn].
  apply in_flat_map in Hin as ((k & o) & Hko & Hin). destruct (nth_error Qs k) as [RQ|] eqn:HQ; [|destruct Hin].
  apply in_map_iff in Hin as ((q & w) & E & Hqw). injection E as <- <-.
  exists k, o, RQ, q, w. refine (conj Hko (conj HQ (conj (telems_spec _ _ _ Hqw) (conj eq_refl eq_refl)))).
Qed.
End Call2.

Section Call3.
Variable segs : list Segment.

#[using="Type"] Lemma nth_map_i' : forall {A B} (f : nat -> A -> B) l k y, nth_error (map_i f 0 l) k = Some y -> exists x, nth_error l k = Some x /\ y = f k x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A B f l. assert (G : forall i k y, nth_error (map_i f i l) k = Some y -> exists x, nth_error l k = Some x /\ y = f (i + k)%nat x).
  { induction l as [|x l IH]; intros i k y H; [destruct k; discriminate|]. destruct k as [|k]; cbn [map_i nth_error] in H.
    - injection H as <-. exists x. split; [reflexivity|]. rewrite Nat.add_0_r. reflexivity.
    - destruct (IH (S i) k y H) as (x' & H1 & H2). exists x'. split; [exact H1|]. rewrite H2. f_equal. lia. }
  intros k y H. destruct (G 0%nat k y H) as (x & H1 & H2). exists x. split; [exact H1 | exact H2].
Qed.

#[using="Type"] Lemma length_map_i : forall {A B} (f : nat -> A -> B) i l, length (map_i f i l) = length l.
Proof. LiaFast.lf_pins LiaFast.u0. intros A B f i l. revert i. induction l as [|x l IH]; intros i; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cs_unchanged : forall E1 Eq P0s Qs m m' x,
  Forall (rg_ok segs E1 m) P0s -> Forall (rg_ok segs Eq m') Qs ->
  shape_eqb P0s Qs = true -> length P0s = length Qs -> kinds_ok P0s Qs = true ->
  (forall k R, nth_error P0s k = Some R -> lden E1 (rg_base R) = lden Eq (rg_base R) /\ rsz E1 R = rsz Eq R) ->
  (forall x, fr_pt E1 P0s x -> m' x = m x) ->
  (forall k R, nth_error P0s k = Some R -> wkind (rg_kind R) = true -> ~ FxStep.in_rg E1 R x) ->
  m' x = m x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E1 Eq P0s Qs m m' x HP HQ Hsh Hlen Hk Hbs Hfr Hno.
  destruct (Exists_dec (fun R => FxStep.in_rg E1 R x) P0s) as [Hin|Hout].
  { intros R. unfold FxStep.in_rg. destruct (Z_le_dec (bv_unsigned (lden E1 (rg_base R))) (bv_unsigned x)); [|right; lia].
    destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned (lden E1 (rg_base R)) + rsz E1 R)); [left; lia | right; lia]. }
  - apply Exists_exists in Hin as (R & HR & Hx). apply In_nth_error in HR as (k & Hk0).
    destruct (rg_kind R) eqn:EK.
    + exfalso. exact (Hno k R Hk0 ltac:(rewrite EK; reflexivity) Hx).
    + (* [comment removed for export] *)
      assert (HQk : exists RQ, nth_error Qs k = Some RQ /\ rg_base RQ = rg_base R /\ rg_size RQ = rg_size R /\ rg_kind RQ = RO).
      { clear - Hk0 Hsh Hlen Hk EK. revert Qs k Hk0 Hsh Hlen Hk. induction P0s as [|R0 P' IH]; intros [|RQ Qs] k Hk0 Hsh Hlen Hk; try (destruct k; discriminate); try discriminate.
        cbn [shape_eqb] in Hsh. apply andb_prop in Hsh as [Hsh Hs']. apply andb_prop in Hsh as [Hb Hz]. apply lin_eqb_eq in Hb, Hz.
        unfold kinds_ok in Hk. cbn [combine forallb] in Hk. apply andb_prop in Hk as [Hk1 Hk2].
        destruct k as [|k]; cbn [nth_error] in Hk0 |- *.
        - injection Hk0 as <-. exists RQ. split; [reflexivity|]. split; [symmetry; exact Hb|]. split; [symmetry; exact Hz|].
          rewrite EK in Hk1. destruct (rg_kind RQ); try discriminate; reflexivity.
        - apply (IH Qs k Hk0 Hs' ltac:(cbn in Hlen; lia) Hk2). }
      destruct HQk as (RQ & HQk & Eb & Ez & EkQ).
      rewrite Forall_nth' in HP, HQ. pose proof (HP k R Hk0) as HR0. pose proof (HQ k RQ HQk) as HRQ.
      destruct (Hbs k R Hk0) as [Hb' Hz'].
      unfold rg_ok in HR0, HRQ. cbv zeta in HR0, HRQ. destruct HR0 as (_ & _ & H3 & _). destruct HRQ as (_ & _ & H3' & _).
      rewrite EK in H3. rewrite EkQ in H3'.
      assert (Bq : bv_unsigned (lden Eq (rg_base RQ)) = bv_unsigned (lden E1 (rg_base R))) by (rewrite Eb, <- Hb'; reflexivity).
      assert (Sq : rsz Eq RQ = rsz E1 R) by (unfold rsz in *; rewrite Ez; symmetry; exact Hz').
      unfold FxStep.in_rg in Hx.
      specialize (H3 (bv_unsigned x - bv_unsigned (lden E1 (rg_base R))) ltac:(lia)).
      specialize (H3' (bv_unsigned x - bv_unsigned (lden E1 (rg_base R))) ltac:(rewrite Sq; lia)).
      rewrite Bq in H3'.
      replace (bv_unsigned (lden E1 (rg_base R)) + (bv_unsigned x - bv_unsigned (lden E1 (rg_base R)))) with (bv_unsigned x) in H3, H3' by lia.
      rewrite Z_to_bv_bv_unsigned in H3, H3'. rewrite (proj1 H3), (proj1 H3'). reflexivity.
    + exfalso. exact (Hno k R Hk0 ltac:(rewrite EK; reflexivity) Hx).
    + exfalso. exact (Hno k R Hk0 ltac:(rewrite EK; reflexivity) Hx).
    + (* [comment removed for export] *)
      apply Hfr. right. apply Exists_exists. exists R. split; [exact (nth_error_In _ _ Hk0)|]. rewrite EK. split; [reflexivity | exact Hx].
  - apply Hfr. left. unfold FxStep.outside. apply Forall_forall. intros R HR.
    assert (Hn : ~ FxStep.in_rg E1 R x) by (intros Hc; apply Hout; apply Exists_exists; exists R; split; assumption).
    unfold FxStep.in_rg in Hn. lia.
Qed.
End Call3.

Lemma rg_sub_kind : forall R W o, rg_sub_ok R W o = true -> wkind (rg_kind W) = true -> wkind (rg_kind R) = true.
Proof.
  intros R W o H Hw. unfold rg_sub_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  destruct (rg_kind R), (rg_kind W); cbn in Hw, H |- *; first [reflexivity | discriminate].
Qed.
Lemma rkind_le_w : forall a b, rkind_le a b = true -> wkind b = true -> wkind a = true.
Proof. intros [] [] H Hw; cbn in *; first [reflexivity | discriminate]. Qed.

Section Call4.
Variable segs : list Segment.

#[using="Type"] Lemma in_rg_dec : forall E R x, {FxStep.in_rg E R x} + {~ FxStep.in_rg E R x}.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E R x. unfold FxStep.in_rg.
  destruct (Z_le_dec (bv_unsigned (lden E (rg_base R))) (bv_unsigned x)) as [H1|H1]; [|right; lia].
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [H2|H2]; [left; lia | right; lia].
Qed.

#[using="Type"] Lemma in_rg_transfer : forall E1 E2 R1 R2 x, bv_unsigned (lden E1 (rg_base R1)) = bv_unsigned (lden E2 (rg_base R2)) -> rsz E1 R1 = rsz E2 R2 ->
  FxStep.in_rg E1 R1 x -> FxStep.in_rg E2 R2 x.
Proof. LiaFast.lf_pins LiaFast.u0. intros E1 E2 R1 R2 x Hb Hz H. unfold FxStep.in_rg in *. rewrite <- Hb, <- Hz. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_at_w : forall E m R x, rg_ok segs E m R -> FxStep.in_rg E R x -> wkind (rg_kind R) = true ->
  rd1 segs m x <> None /\ wview segs m x <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R x HR Hx Hw. unfold rg_ok in HR. cbv zeta in HR. destruct HR as (_ & _ & H3 & _). unfold FxStep.in_rg in Hx.
  specialize (H3 (bv_unsigned x - bv_unsigned (lden E (rg_base R))) ltac:(lia)).
  replace (bv_unsigned (lden E (rg_base R)) + (bv_unsigned x - bv_unsigned (lden E (rg_base R)))) with (bv_unsigned x) in H3 by lia.
  rewrite Z_to_bv_bv_unsigned in H3. destruct (rg_kind R); cbn in Hw; try discriminate; first [exact H3 | exact (proj1 H3)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_in_off : forall E m R j, rg_ok segs E m R -> 0 <= j < rsz E R ->
  FxStep.in_rg E R (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + j)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R j HR Hj. unfold rg_ok in HR. cbv zeta in HR. destruct HR as (X1 & X2 & _). pose proof (u_range E (rg_base R)) as X3.
  unfold FxStep.in_rg. rewrite u_small64 by (unfold two64 in *; lia). lia.
Qed.

#[using="Type"] Lemma rgs_ent_nth : forall rs rp σ, rgs_ent rs rp σ = true -> length rs = length rp /\
  forall k R P, nth_error rs k = Some R -> nth_error rp k = Some P -> rg_ent R P σ = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction rs as [|R rs IH]; intros [|P rp] σ H; cbn [rgs_ent] in H; try discriminate.
  - split; [reflexivity|]. intros [|k]; discriminate.
  - apply andb_prop in H as [H1 H2]. destruct (IH rp σ H2) as [Hl Hn]. split; [cbn; lia|].
    intros [|k] R0 P0 HR HP; cbn [nth_error] in HR, HP; [injection HR as <-; injection HP as <-; exact H1 | exact (Hn k R0 P0 HR HP)].
Qed.

#[using="Type"] Lemma shape_nth : forall a b, shape_eqb a b = true -> forall k R, nth_error a k = Some R ->
  exists R', nth_error b k = Some R' /\ rg_base R' = rg_base R /\ rg_size R' = rg_size R.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|R a IH]; intros [|R' b] H k R0 Hk; try (destruct k; discriminate); cbn [shape_eqb] in H; try discriminate.
  apply andb_prop in H as [H Hs]. apply andb_prop in H as [Hb Hz]. apply lin_eqb_eq in Hb, Hz.
  destruct k as [|k]; cbn [nth_error] in Hk |- *.
  - injection Hk as <-. exists R'. split; [reflexivity|]. split; symmetry; assumption.
  - exact (IH b Hs k R0 Hk).
Qed.

#[using="Type"] Lemma kinds_nth : forall a b, kinds_ok a b = true -> forall k R R', nth_error a k = Some R -> nth_error b k = Some R' ->
  (wkind (rg_kind R) = true -> wkind (rg_kind R') = true).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|R a IH]; intros [|R' b] H k R0 R0' Hk Hk'; try (destruct k; discriminate).
  unfold kinds_ok in H. cbn [combine forallb] in H. apply andb_prop in H as [H1 H2].
  destruct k as [|k]; cbn [nth_error] in Hk, Hk'.
  - injection Hk as <-. injection Hk' as <-. intros Hw. destruct (rg_kind R), (rg_kind R'); cbn in *; try discriminate; first [reflexivity | exact H1].
  - exact (IH b H2 k R0 R0' Hk Hk').
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem call_sound_P : forall (Φ : machine_state -> machine_state -> Prop), fp_inv Φ -> forall P0 Q rets keep qk vs rgs_w ret L K E ms,
  fn_okP segs Φ P0 Q rets -> call_cont L P0 Q keep qk vs rgs_w ret = Some K -> sden segs E L ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next L) E E'' /\
    (forall x, fr_pt E (s_rgs L) x -> ms_mem ms'' x = ms_mem ms x) /\ Φ ms ms''.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦ P0 Q rets keep qk vs rgs_w ret L K E ms Hfn Hcc Hd.
  unfold call_cont in Hcc. destruct (call_ok L P0 Q keep qk vs rgs_w ret) eqn:Hok; [|discriminate]. injection Hcc as <-.
  unfold call_ok in Hok. cbv zeta in Hok.
  set (Lw := with_rgs L rgs_w) in *. set (σc := mcall Lw P0) in *.
  apply andb_prop in Hok as [Hok HwK]. apply andb_prop in Hok as [Hok HQr]. apply andb_prop in Hok as [Hok Hr3].
  apply andb_prop in Hok as [Hok Hr2]. apply andb_prop in Hok as [Hok Hr1]. apply andb_prop in Hok as [Hok Hra].
  apply andb_prop in Hok as [Hok Hnx]. apply andb_prop in Hok as [Hok Hrak]. apply andb_prop in Hok as [Hok Hkeq].
  apply andb_prop in Hok as [Hok Hlw]. apply andb_prop in Hok as [Hok Hkd]. apply andb_prop in Hok as [Hok Hlen].
  apply andb_prop in Hok as [Hok Hsh]. apply andb_prop in Hok as [Hok Hnq]. apply andb_prop in Hok as [Hok Hent].
  apply andb_prop in Hok as [Hok HwQ]. apply andb_prop in Hok as [Hok HwP]. apply andb_prop in Hok as [Hok HwW].
  apply andb_prop in Hok as [Hok HwL]. apply andb_prop in Hok as [Hv Hvp].
  apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2. apply Z.eqb_eq in Hr3. apply Nat.eqb_eq in Hlen. apply Pos.leb_le in Hnq.
  apply lin_eqb_eq in Hra. rewrite forallb_forall in Hlw, Hkeq.
  assert (HQr' : s_resv Q = RNone) by (destruct (s_resv Q); [reflexivity | discriminate..]).
  set (n0 := s_next P0) in *. set (nQ := s_next Q) in *. set (nL := s_next L) in *.
  set (σ' := sigq σc n0 nQ nL) in *. set (nx := (nL + nQ - n0)%positive) in *.
  (* [comment removed for export] *)
  pose proof (views_sound segs E L ms rgs_w vs Hd Hv Hvp HwW) as HdW.
  pose proof (entails_sden segs E Lw P0 σc ms (sden_0 _ _ _ _ HdW) Hent HwP) as Hd0.
  destruct (Hfn _ _ Hd0) as (ms' & Eq & p & Hst & Hp & Hret & HdQ & Hag & Hfr & HΦ0).
  pose proof (ret_isteps segs Eq (with_pc Q p) ms' HdQ HQr' Hret) as Hrs.
  destruct (sden_0 _ _ _ _ Hd) as (A1 & B1 & C1 & D1 & F1 & G1 & I1 & J1).
  destruct (sden_0 _ _ _ _ Hd0) as (A0 & B0 & C0 & D0 & F0 & G0 & I0 & J0).
  destruct (sden_0 _ _ _ _ HdQ) as (AQ & BQ & CQ & DQ & FQ & GQ & IQ & JQ).
  cbn [with_pc s_regs s_rgs s_facts s_resv s_pc] in AQ, BQ, CQ, DQ, FQ, GQ, IQ.
  (* [comment removed for export] *)
  pose proof HwP as HwP'. unfold state_wf in HwP'. apply andb_prop in HwP' as [HwP' _]. apply andb_prop in HwP' as [HwP' _].
  apply andb_prop in HwP' as [HrP HgP]. rewrite forallb_forall in HgP.
  pose proof HwQ as HwQ'. unfold state_wf in HwQ'. apply andb_prop in HwQ' as [HwQ' _]. apply andb_prop in HwQ' as [HwQ' HfQ].
  apply andb_prop in HwQ' as [HrQ HgQ]. rewrite forallb_forall in HgQ, HfQ.
  pose proof HwL as HwL'. unfold state_wf in HwL'. apply andb_prop in HwL' as [HwL' _]. apply andb_prop in HwL' as [HwL' HfL].
  apply andb_prop in HwL' as [HrL HgL]. rewrite forallb_forall in HgL, HfL.
  (* [comment removed for export] *)
  assert (Hkv : forall j, (1 <= j <= 31)%nat -> existsb (Pos.eqb (Pos.of_succ_nat j)) keep = true ->
            lden Eq (rget (s_regs Q) (Pos.of_succ_nat j)) = lden E (rget (s_regs L) (Pos.of_succ_nat j))).
  { intros j Hj Hk. apply existsb_exists in Hk as (key & Hkey & Hke). apply Pos.eqb_eq in Hke. subst key.
    pose proof (Hkeq _ Hkey) as He. apply lin_eqb_eq in He. rewrite He.
    rewrite <- (lden_agree n0 (ecomp E σc) Eq _ (regs_wf_n_spec _ _ _ HrP j Hj) Hag).
    rewrite <- lden_lsubst. unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _].
    apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hre].
    rewrite <- (regs_ent_n_spec _ _ _ _ Hre j Hj). reflexivity. }
  (* [comment removed for export] *)
  assert (Hra1 : getr (ms_regs ms') 1 = Z_to_bv 64 ret).
  { rewrite (DQ 1%bv). change (rkey 1%bv) with (Pos.of_succ_nat 1).
    rewrite (Hkv 1%nat ltac:(lia) ltac:(change (Pos.of_succ_nat 1) with ra_key; exact Hrak)).
    change (Pos.of_succ_nat 1) with ra_key. rewrite Hra. unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r.
    apply Z_to_bv_eqm. apply eqm_w64. }
  rewrite Hra1, (jalr_tgt_even ret ltac:(unfold two64 in *; lia) Hr3) in Hrs.
  set (ms'' := @mkst (mkFP (ms_fregs ms') (ms_fcsr ms')) (ms_regs ms') (Z_to_bv 64 ret) (ms_mem ms') (ms_rom ms')) in Hrs.
  (* [comment removed for export] *)
  set (E'' := fun x : positive => if Pos.ltb x nL then E x else if Pos.ltb x nx then Eq (x + n0 - nL)%positive
                                 else if Pos.ltb x (nx + 32) then getr (ms_regs ms') (Z_to_bv 5 (Zpos x - Zpos nx)) else E x).
  assert (HaL : agree nL E E'').
  { intros x Hx. unfold E''. rewrite (proj2 (Pos.ltb_lt x nL) Hx). reflexivity. }
  assert (HaQ : forall y, (y < nQ)%positive -> ecomp E'' σ' y = Eq y).
  { intros y Hy. unfold ecomp. unfold σ'. rewrite sigq_get by exact Hy. destruct (Pos.ltb y n0) eqn:Hy0.
    - apply Pos.ltb_lt in Hy0. rewrite <- (lden_agree nL E E'' _ (Hlw y (in_vars_below _ _ Hy0)) HaL). exact (Hag y Hy0).
    - apply Pos.ltb_ge in Hy0. rewrite lden_lvar. unfold E''.
      rewrite (proj2 (Pos.ltb_ge (nL + y - n0) nL)) by lia. rewrite (proj2 (Pos.ltb_lt (nL + y - n0) nx)) by (unfold nx; lia).
      f_equal. lia. }
  assert (HaQ' : agree nQ Eq (ecomp E'' σ')) by (intros y Hy; symmetry; exact (HaQ y Hy)).
  (* [comment removed for export] *)
  destruct (views_nth _ _ _ Hv) as [HlV Hvw].
  unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _].
  apply andb_prop in Hent as [Hent Hrge]. cbn [s_rgs with_rgs Lw] in Hrge.
  destruct (rgs_ent_nth _ _ _ Hrge) as [HlW Hwk].
  assert (Hbs0 : forall k R, nth_error (s_rgs P0) k = Some R -> lden (ecomp E σc) (rg_base R) = lden Eq (rg_base R) /\ rsz (ecomp E σc) R = rsz Eq R).
  { intros k R Hk. pose proof (HgP R (nth_error_In _ _ Hk)) as HR. unfold rwf in HR. apply andb_prop in HR as [HR _]. apply andb_prop in HR as [Hb Hs].
    split; [exact (lden_agree n0 _ _ _ Hb Hag) | unfold rsz; rewrite (lden_agree n0 _ _ _ Hs Hag); reflexivity]. }
  assert (HPW : forall k P, nth_error (s_rgs P0) k = Some P -> exists W v R, nth_error rgs_w k = Some W /\ nth_error vs k = Some v /\
             nth_error (s_rgs L) (vop_src v) = Some R /\ rg_ent W P σc = true /\
             bv_unsigned (lden (ecomp E σc) (rg_base P)) = bv_unsigned (lden E (rg_base W)) /\ rsz (ecomp E σc) P = rsz E W /\
             bv_unsigned (lden E (rg_base R)) <= bv_unsigned (lden E (rg_base W)) /\
             bv_unsigned (lden E (rg_base W)) + rsz E W <= bv_unsigned (lden E (rg_base R)) + rsz E R /\
             ((exists o, v = VSub (vop_src v) o /\ 0 <= o /\ bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o /\
                         o + rsz E W <= rsz E R /\ rsz E W = csz W /\ rg_sub_ok R W o = true) \/
              (v = VCopy (vop_src v) /\ rg_base W = rg_base R /\ rg_size W = rg_size R /\ rg_kind W = rg_kind R))).
  { intros k P Hk. destruct (nth_error rgs_w k) as [W|] eqn:HW; [|apply nth_error_None in HW; pose proof (nth_error_Some (s_rgs P0) k) as X; rewrite Hk in X; specialize (proj1 X ltac:(discriminate)); lia].
    destruct (nth_error vs k) as [v|] eqn:Hvk; [|apply nth_error_None in Hvk; pose proof (nth_error_Some rgs_w k) as X; rewrite HW in X; specialize (proj1 X ltac:(discriminate)); lia].
    pose proof (Hvw k W v HW Hvk) as Hv1. destruct (view1_sound segs E (ms_mem ms) (s_rgs L) W v F1 Hv1) as (R & HR & _ & Hs1).
    pose proof (Hwk k W P HW Hk) as He. destruct (rg_ent_parts _ _ _ He) as (Eb & Ez & _ & _ & _).
    exists W, v, R. split; [first [exact HW | reflexivity]|]. split; [first [exact Hvk | reflexivity]|]. split; [exact HR|]. split; [exact He|].
    split; [rewrite <- lden_lsubst, <- Eb; reflexivity|]. split; [unfold rsz; rewrite <- lden_lsubst, <- Ez; reflexivity|].
    destruct Hs1 as [(o & Eo & Ho & HA & Hn & Hq)|(Eo & Eb' & Ez' & Ek)].
    - split; [lia|]. split; [lia|]. left. exists o. refine (conj Eo (conj Ho (conj HA (conj Hn (conj Hq _))))).
      rewrite Eo in Hv1. cbn [view1_ok vop_src] in Hv1. rewrite HR in Hv1. exact Hv1.
    - split; [rewrite Eb'; lia|]. split; [unfold rsz; rewrite Eb', Ez'; lia|]. right. exact (conj Eo (conj Eb' (conj Ez' Ek))). }
  (* [comment removed for export] *)
  assert (Hsrc : forall i R x k P, nth_error (s_rgs L) i = Some R -> FxStep.in_rg E R x -> nth_error (s_rgs P0) k = Some P ->
             FxStep.in_rg (ecomp E σc) P x -> exists W v, nth_error rgs_w k = Some W /\ nth_error vs k = Some v /\ vop_src v = i).
  { intros i R x k P HR Hx Hk Hxp. destruct (HPW k P Hk) as (W & v & R' & HW & Hvk & HR' & _ & HbP & HzP & Hlo & Hhi & _).
    exists W, v. split; [exact HW|]. split; [exact Hvk|].
    destruct (Nat.eq_dec (vop_src v) i) as [Heq|Hne]; [exact Heq|]. exfalso.
    pose proof (rgs_disj_nth E (s_rgs L) _ _ R' R G1 Hne HR' HR) as Hd12. unfold rg_disj, FxStep.in_rg in *. lia. }
  (* [comment removed for export] *)
  assert (Hunch : forall x, (forall k P, nth_error (s_rgs P0) k = Some P -> wkind (rg_kind P) = true -> ~ FxStep.in_rg (ecomp E σc) P x) ->
             ms_mem ms' x = ms_mem ms x).
  { intros x Hno. exact (cs_unchanged segs (ecomp E σc) Eq (s_rgs P0) (s_rgs Q) (ms_mem ms) (ms_mem ms') x F0 FQ Hsh Hlen Hkd Hbs0 Hfr Hno). }
  (* [comment removed for export] *)
  assert (HwR : forall i R, nth_error (s_rgs L) i = Some R -> rwf nL R = true) by (intros i R Hi; exact (HgL R (nth_error_In _ _ Hi))).
  (* [comment removed for export] *)
  assert (keep_out_ok : forall i R k0 ks pk v, nth_error (s_rgs L) i = Some R -> rg_ok segs E (ms_mem ms) R -> rg_ok segs E'' (ms_mem ms) R ->
            lden E (rg_base R) = lden E'' (rg_base R) -> rsz E R = rsz E'' R -> wviews (s_rgs P0) vs 0 i = k0 :: ks ->
            tget pk (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R)) = Some v ->
            Zpos pk - 1 < rsz E'' R /\ rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + (Zpos pk - 1))) = Some (bden E'' v)).
  { intros i R k0 ks pk v HR HRok HRok'' HbR HzR Hwv Hkeep.
    unfold keep_out in Hkeep. rewrite tget_tfilter in Hkeep.
    destruct (out_wins σc (s_rgs P0) vs (k0 :: ks) (Zpos pk - 1)) eqn:Hout; [|discriminate].
    pose proof HRok'' as X. unfold rg_ok in X. cbv zeta in X. destruct X as (_ & _ & _ & X4).
    destruct (X4 pk v Hkeep) as [Hp1 Hp2]. split; [exact Hp1|].
    set (j := Zpos pk - 1) in *.
    set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) in *.
    assert (Hj : 0 <= j < rsz E R) by (unfold j; rewrite HzR; lia).
    assert (Hxr : FxStep.in_rg E R x).
    { pose proof (rg_in_off E _ R j HRok Hj) as Y. unfold x. rewrite <- HbR. exact Y. }
    assert (Hm : ms_mem ms' x = ms_mem ms x).
    { apply Hunch. intros k P Hk Hwp Hxp.
      destruct (Hsrc i R x k P HR Hxr Hk Hxp) as (W & v0 & HW & Hvk & Hs).
      pose proof (wviews_in (s_rgs P0) vs 0 i k P v0 Hk Hvk Hwp Hs) as Hko. rewrite Hwv in Hko. cbn [Nat.add] in Hko.
      unfold out_wins in Hout. rewrite forallb_forall in Hout. pose proof (Hout _ Hko) as Ho. cbv beta iota in Ho.
      unfold view_win in Ho. rewrite Hvk, Hk in Ho. destruct v0 as [i0|i0 o0]; [discriminate|].
      destruct (is_const (lsubst σc (rg_size P))) as [nc|] eqn:Hnc; [|discriminate].
      destruct (HPW k P Hk) as (W' & v' & R' & HW' & Hv' & HR' & _ & HbP & HzP & _ & _ & Hcase).
      rewrite HW in HW'. injection HW' as <-. rewrite Hvk in Hv'. injection Hv' as <-. rewrite Hs in HR'. rewrite HR in HR'. injection HR' as <-.
      destruct Hcase as [(o1 & Eo1 & _ & HA & _ & _ & _)|(Eo1 & _)]; [|discriminate Eo1].
      cbn [vop_src] in Eo1. injection Eo1 as Eo2. rewrite <- Eo2 in HA.
      pose proof (is_const_u E (lsubst σc (rg_size P)) nc Hnc) as Hzn. rewrite lden_lsubst in Hzn.
      unfold FxStep.in_rg in Hxp. unfold rsz in Hxp. rewrite Hzn in Hxp. rewrite HbP, HA in Hxp.
      assert (Hxu : bv_unsigned x = bv_unsigned (lden E (rg_base R)) + j).
      { unfold x. rewrite <- HbR. rewrite u_small64; [reflexivity|]. pose proof HRok as Y. unfold rg_ok in Y. cbv zeta in Y. destruct Y as (Y1 & Y2 & _).
        pose proof (u_range E (rg_base R)) as Y3. unfold two64 in *. lia. }
      rewrite Hxu in Hxp. apply Bool.orb_true_iff in Ho as [Ho|Ho]; [apply Z.ltb_lt in Ho | apply Z.leb_le in Ho]; lia. }
    unfold rd1 in Hp2 |- *. fold x in Hp2 |- *. rewrite Hm. exact Hp2. }
  assert (HRK : Forall (rg_ok segs E'' (ms_mem ms')) (map_i (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs) 0 (s_rgs L))).
  { apply Forall_nth'. intros i RK Hi. destruct (nth_map_i' _ _ _ _ Hi) as (R & HR & ->).
    rewrite Forall_nth' in F1. pose proof (F1 i R HR) as HRok.
    pose proof (rg_ok_agree segs nL E E'' (ms_mem ms) R (HwR i R HR) HaL HRok) as HRok''.
    assert (HbR : lden E (rg_base R) = lden E'' (rg_base R)).
    { pose proof (HwR i R HR) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. exact (lden_agree nL _ _ _ X HaL). }
    assert (HzR : rsz E R = rsz E'' R).
    { pose proof (HwR i R HR) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. unfold rsz. rewrite (lden_agree nL _ _ _ X HaL). reflexivity. }
    unfold new_rg. destruct (wviews (s_rgs P0) vs 0 i) as [|k0 ks] eqn:Hwv.
    - (* [comment removed for export] *)
      apply (rg_ok_mem segs E'' (ms_mem ms) (ms_mem ms') R HRok''). intros j Hj. apply Hunch. intros k P Hk Hwkp Hxp.
      rewrite <- HbR in Hxp. rewrite <- HzR in Hj.
      assert (Hxr : FxStep.in_rg E R (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + j))).
      { pose proof HRok as X. unfold rg_ok in X. cbv zeta in X. destruct X as (X1 & X2 & _). pose proof (u_range E (rg_base R)) as X3.
        unfold FxStep.in_rg. rewrite u_small64 by (unfold two64 in *; lia). lia. }
      destruct (Hsrc i R _ k P HR Hxr Hk Hxp) as (W & v & HW & Hvk & Hs).
      exact (wviews_nil _ _ _ _ Hwv k P v Hk Hvk Hwkp Hs).
    - (* [comment removed for export] *)
      destruct (wviews_spec (s_rgs P0) vs 0 i (fst k0) (snd k0) ltac:(rewrite Hwv; left; destruct k0; reflexivity))
        as (Pk & vk & HPk & Hvk & _ & HwPk & Hsk & _). rewrite Nat.sub_0_r in HPk, Hvk.
      (* [comment removed for export] *)
      assert (HwkR : wkind (rg_kind R) = true).
      { destruct (HPW _ Pk HPk) as (W & v & R' & HW & Hv' & HR' & He & _ & _ & _ & _ & Hcase).
        rewrite Hvk in Hv'. injection Hv' as <-. rewrite Hsk in HR'. rewrite HR in HR'. injection HR' as <-.
        destruct (rg_ent_parts _ _ _ He) as (_ & _ & Hkle & _ & _). pose proof (rkind_le_w _ _ Hkle HwPk) as HwWk.
        destruct Hcase as [(o & _ & _ & _ & _ & _ & Hsub)|(_ & _ & _ & Ek)].
        - exact (rg_sub_kind R W o Hsub HwWk).
        - rewrite <- Ek. exact HwWk. }
      (* [comment removed for export] *)
      assert (HRW : forall j, 0 <= j < rsz E'' R ->
                rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) <> None /\
                wview segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) <> None).
      { intros j Hj. set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)).
        assert (Hxr : FxStep.in_rg E R x).
        { pose proof (rg_in_off E _ R j HRok ltac:(rewrite HzR; exact Hj)) as X. unfold x. rewrite <- HbR. exact X. }
        destruct (Exists_dec (fun P => wkind (rg_kind P) = true /\ FxStep.in_rg (ecomp E σc) P x) (s_rgs P0)) as [Hin|Hout].
        { intros P. destruct (wkind (rg_kind P)) eqn:Hwp; [|right; intros [X _]; discriminate].
          destruct (in_rg_dec (ecomp E σc) P x) as [X|X]; [left; split; [reflexivity | exact X] | right; intros [_ Y]; exact (X Y)]. }
        * apply Exists_exists in Hin as (P & HP & HwP0 & Hxp). apply In_nth_error in HP as (k & Hk).
          destruct (shape_nth _ _ Hsh k P Hk) as (RQ & HQk & EbQ & EzQ).
          rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ.
          destruct (Hbs0 k P Hk) as [Hb0 Hz0].
          assert (HxQ : FxStep.in_rg Eq RQ x).
          { apply (in_rg_transfer (ecomp E σc) Eq P RQ x); [rewrite Hb0, EbQ; reflexivity | unfold rsz; rewrite EzQ; exact Hz0 | exact Hxp]. }
          exact (rg_at_w Eq _ RQ x HRQ HxQ (kinds_nth _ _ Hkd k P RQ Hk HQk HwP0)).
        * assert (Hm : ms_mem ms' x = ms_mem ms x).
          { apply Hunch. intros k P Hk Hw' Hxp. apply Hout. apply Exists_exists. exists P. split; [exact (nth_error_In _ _ Hk) | split; assumption]. }
          destruct (rg_at_w E _ R x HRok Hxr HwkR) as [Y1 Y2]. unfold rd1, wview in Y1, Y2 |- *. rewrite Hm. split; assumption. }
      (* [comment removed for export] *)
      assert (HIMP : forall pk v, tget pk (imp_cont (s_rgs Q) σ' (k0 :: ks) (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R))) = Some v ->
                Zpos pk - 1 < rsz E'' R /\ rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + (Zpos pk - 1))) = Some (bden E'' v)).
      { intros pk v Hpk. destruct (in_imp_cont _ _ _ _ _ _ Hpk) as [(k & o & RQ & q & w & Hko & HQk & Hqw & Ep & Ev)|Hkeep];
          [|exact (keep_out_ok i R k0 ks pk v HR HRok HRok'' HbR HzR Hwv Hkeep)].
        rewrite <- Hwv in Hko.
        destruct (wviews_spec (s_rgs P0) vs 0 i k o Hko) as (P & v' & HP & Hv' & _ & HwP0 & Hs' & Eo). rewrite Nat.sub_0_r in HP, Hv'.
        destruct (HPW k P HP) as (W & v'' & R' & HW & Hv'' & HR' & _ & HbP & HzP & Hlo & Hhi & Hcase).
        rewrite Hv' in Hv''. injection Hv'' as <-. rewrite Hs' in HR'. rewrite HR in HR'. injection HR' as <-.
        destruct (shape_nth _ _ Hsh k P HP) as (RQ' & HQk' & EbQ & EzQ). rewrite HQk in HQk'. injection HQk' as <-.
        rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ. unfold rg_ok in HRQ. cbv zeta in HRQ. destruct HRQ as (_ & _ & _ & HQ4).
        destruct (HQ4 q w Hqw) as [Hq1 Hq2].
        destruct (Hbs0 k P HP) as [Hb0 Hz0].
        assert (Hoff : 0 <= o /\ bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o /\ o + rsz E W <= rsz E R).
        { destruct Hcase as [(o' & Eo' & Ho' & HA & Hn' & _)|(Eo' & Eb' & Ez' & _)].
          - rewrite Eo' in Eo. cbn in Eo. subst o. clear - Ho' HA Hn'. lia.
          - rewrite Eo' in Eo. cbn in Eo. subst o. rewrite Eb'. unfold rsz. rewrite Ez'. clear. lia. }
        destruct Hoff as (Ho0 & HbW & HzW).
        assert (HbQ : bv_unsigned (lden Eq (rg_base RQ)) = bv_unsigned (lden E (rg_base R)) + o) by (rewrite EbQ, <- Hb0, HbP; exact HbW).
        assert (HzQ : rsz Eq RQ = rsz E W) by (unfold rsz; rewrite EzQ; fold (rsz Eq P); rewrite <- Hz0; exact HzP).
        assert (Hp1 : Zpos pk - 1 = o + (Zpos q - 1)) by (rewrite Ep; unfold okey; rewrite Z2Pos.id by (clear - Ho0; lia); clear; lia).
        rewrite Hp1. split; [rewrite <- HzR; clear - Hq1 HzQ HzW; lia|].
        rewrite <- HbR. rewrite Z.add_assoc. rewrite <- HbQ. rewrite Hq2. rewrite Ev. f_equal.
        rewrite bden_bsubst. apply (bden_agree nQ Eq (ecomp E'' σ') w); [|exact HaQ'].
        pose proof (HgQ RQ (nth_error_In _ _ HQk)) as X. unfold rwf in X. apply andb_prop in X as [_ X].
        exact (tforall_spec _ _ X q w Hqw). }
      unfold rg_ok. cbv zeta. rewrite rsz_RG_eq. cbn [rg_base rg_kind rg_cont].
      pose proof HRok'' as HRok3. unfold rg_ok in HRok3. cbv zeta in HRok3. destruct HRok3 as (H1 & H2 & _ & _).
      refine (conj H1 (conj H2 (conj _ HIMP))).
      destruct (rz_keep (s_rgs Q) R (k0 :: ks)) eqn:Hrz; [|exact HRW].
      (* [comment removed for export] *)
      intros j Hj. split; [exact (HRW j Hj)|]. intros Hnone.
      set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)).
      assert (Hxr : FxStep.in_rg E R x).
      { pose proof (rg_in_off E _ R j HRok ltac:(rewrite HzR; exact Hj)) as X. unfold x. rewrite <- HbR. exact X. }
      unfold rz_keep in Hrz. apply andb_prop in Hrz as [Hrz Hzv]. apply andb_prop in Hrz as [HkR Hc0].
      rewrite forallb_forall in Hzv.
      destruct (Exists_dec (fun P => wkind (rg_kind P) = true /\ FxStep.in_rg (ecomp E σc) P x) (s_rgs P0)) as [Hin|Hout].
      { intros P. destruct (wkind (rg_kind P)) eqn:Hwp; [|right; intros [X _]; discriminate].
        destruct (in_rg_dec (ecomp E σc) P x) as [X|X]; [left; split; [reflexivity | exact X] | right; intros [_ Y]; exact (X Y)]. }
      + apply Exists_exists in Hin as (P & HP & HwP0 & Hxp). apply In_nth_error in HP as (k & Hk).
        destruct (Hsrc i R x k P HR Hxr Hk Hxp) as (W & v & HW & Hvk' & Hs).
        pose proof (wviews_in (s_rgs P0) vs 0 i k P v Hk Hvk' HwP0 Hs) as Hko. rewrite Hwv in Hko. cbn [Nat.add] in Hko.
        destruct (shape_nth _ _ Hsh k P Hk) as (RQ & HQk & EbQ & EzQ).
        pose proof (Hzv _ Hko) as HzQ. cbv beta iota in HzQ. rewrite HQk in HzQ.
        rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ.
        destruct (Hbs0 k P Hk) as [Hb0 Hz0].
        destruct (HPW k P Hk) as (W' & v' & R' & HW' & Hv' & HR' & _ & HbP & HzP & Hlo & Hhi & Hcase).
        rewrite HW in HW'. injection HW' as <-. rewrite Hvk' in Hv'. injection Hv' as <-. rewrite Hs in HR'. rewrite HR in HR'. injection HR' as <-.
        set (o := match v with VCopy _ => 0 | VSub _ o' => o' end) in *.
        assert (HbW : bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o).
        { unfold o. destruct Hcase as [(o' & Eo' & _ & HA & _)|(Eo' & Eb' & _ & _)]; rewrite Eo'; [exact HA | rewrite Eb'; lia]. }
        assert (HbQ : bv_unsigned (lden Eq (rg_base RQ)) = bv_unsigned (lden E (rg_base R)) + o) by (rewrite EbQ, <- Hb0, HbP; exact HbW).
        assert (HxQ : FxStep.in_rg Eq RQ x).
        { apply (in_rg_transfer (ecomp E σc) Eq P RQ x); [rewrite Hb0, EbQ; reflexivity | unfold rsz; rewrite EzQ; exact Hz0 | exact Hxp]. }
        unfold rg_ok in HRQ. cbv zeta in HRQ. destruct HRQ as (_ & _ & HQ3 & _).
        unfold FxStep.in_rg in HxQ. rewrite HbQ in HxQ.
        assert (Hxu : bv_unsigned x = bv_unsigned (lden E (rg_base R)) + j).
        { unfold x. rewrite <- HbR. rewrite u_small64; [reflexivity|]. pose proof HRok as X. unfold rg_ok in X. cbv zeta in X. destruct X as (X1 & X2 & _).
          pose proof (u_range E (rg_base R)) as X3. rewrite <- HzR in Hj. unfold two64 in *. lia. }
        specialize (HQ3 (j - o) ltac:(rewrite Hxu in HxQ; lia)).
        destruct (rg_kind RQ) eqn:EkQ; try discriminate. destruct HQ3 as [_ HQ3].
        replace (bv_unsigned (lden Eq (rg_base RQ)) + (j - o)) with (bv_unsigned x) in HQ3 by (rewrite HbQ, Hxu; lia).
        rewrite Z_to_bv_bv_unsigned in HQ3. apply HQ3.
        destruct (tget (okey (j - o)) (rg_cont RQ)) as [w|] eqn:Hw; [|reflexivity]. exfalso.
        pose proof (imp_cont_some (s_rgs Q) σ' (k0 :: ks) (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R)) k o RQ (okey (j - o)) w Hko HQk Hw) as X.
        replace (o + (Zpos (okey (j - o)) - 1)) with j in X by (unfold okey; rewrite Z2Pos.id by lia; lia).
        exact (X Hnone).
      + assert (Hm : ms_mem ms' x = ms_mem ms x).
        { apply Hunch. intros k P Hk Hw' Hxp. apply Hout. apply Exists_exists. exists P. split; [exact (nth_error_In _ _ Hk) | split; assumption]. }
        pose proof HRok'' as X. unfold rg_ok in X. cbv zeta in X. destruct X as (_ & _ & X3 & X4).
        destruct (rg_kind R) eqn:EkR; try discriminate.
        specialize (X3 j Hj). destruct X3 as [_ X3]. unfold rd1 in X3 |- *. fold x in X3 |- *. rewrite Hm.
        destruct (tget (okey j) (rg_cont R)) as [w|] eqn:Hw; [|exact (X3 eq_refl)].
        pose proof (tforall_spec _ _ Hc0 _ _ Hw) as Hw0. cbv beta in Hw0. destruct w as [z|l jj]; [|discriminate]. apply Z.eqb_eq in Hw0. subst z.
        destruct (X4 (okey j) (BK 0) Hw) as [_ X5]. replace (Zpos (okey j) - 1) with j in X5 by (unfold okey; rewrite Z2Pos.id by lia; lia).
        fold x in X5. unfold rd1 in X5. exact X5. }
  (* [comment removed for export] *)
  exists ms'', E''. split; [exact (isteps_trans segs _ _ _ Hst Hrs)|]. split; [|split; [exact HaL| split; [|exact (HΦ ms ms' ms'' eq_refl eq_refl HΦ0)]]].
  - apply sden0_sden; [exact HwK|].
    unfold sden0. cbn [cont_st s_pc s_regs s_rgs s_facts s_resv]. fold nL n0 nQ. fold σ'. fold nx.
    cbn [ms'' mkst ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr fp_csr].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      intros r. destruct (decide (r = 0%bv)) as [->|Hr0].
      - change (rkey 0%bv) with xH. unfold rget. reflexivity.
      - destruct (rkey_succ r Hr0) as (j & Hj & Hkey). rewrite Hkey, regs_cont_get by exact Hj.
        destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) keep) eqn:Hk.
        + rewrite (DQ r). cbn [with_pc s_regs]. rewrite Hkey. rewrite (Hkv j Hj Hk).
          apply (lden_agree nL E E''); [exact (regs_wf_n_spec _ _ _ HrL j Hj) | exact HaL].
        + destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) qk) eqn:Hq.
          * rewrite (DQ r). cbn [with_pc s_regs]. rewrite Hkey. rewrite lden_lsubst.
            apply (lden_agree nQ Eq (ecomp E'' σ')); [exact (regs_wf_n_spec _ _ _ HrQ j Hj) | exact HaQ'].
          * rewrite lden_lvar. unfold E''. rewrite (proj2 (Pos.ltb_ge (nx + Pos.of_nat j) nL)) by (unfold nx; lia).
            rewrite (proj2 (Pos.ltb_ge (nx + Pos.of_nat j) nx)) by lia. rewrite (proj2 (Pos.ltb_lt (nx + Pos.of_nat j) (nx + 32))) by lia.
            f_equal.
            pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 5) with 32 in Rr.
            assert (Hu : bv_unsigned r = Z.of_nat j).
            { apply (f_equal Zpos) in Hkey. unfold rkey, bv_key in Hkey. rewrite Z2Pos.id in Hkey by lia. rewrite Zpos_P_of_succ_nat in Hkey. lia. }
            assert (Ej : Zpos (Pos.of_nat j) = Z.of_nat j) by (rewrite <- positive_nat_Z, Nat2Pos.id by lia; reflexivity).
            apply bv_eq. rewrite Z_to_bv_unsigned, Hu. rewrite Pos2Z.inj_add, Ej.
            replace (Zpos nx + Z.of_nat j - Zpos nx) with (Z.of_nat j) by lia. symmetry. apply bv_wrap_small. unfold bv_modulus. lia. }
    split; [exact HRK|].
    split.
    { (* [comment removed for export] *)
      apply rgs_disj_nth_inv. intros k k' R1 R2 Hkk H1 H2.
      destruct (nth_map_i' _ _ _ _ H1) as (S1 & HS1 & ->). destruct (nth_map_i' _ _ _ _ H2) as (S2 & HS2 & ->).
      pose proof (rgs_disj_nth E (s_rgs L) k k' S1 S2 G1 ltac:(lia) HS1 HS2) as Hd12.
      assert (Hbz : forall i S, nth_error (s_rgs L) i = Some S -> bv_unsigned (lden E'' (rg_base (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs i S))) = bv_unsigned (lden E (rg_base S)) /\
                 rsz E'' (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs i S) = rsz E S).
      { intros i S HS. pose proof (HwR i S HS) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [Xb Xs].
        unfold new_rg. destruct (wviews (s_rgs P0) vs 0 i); cbn [rg_base]; unfold rsz; cbn [rg_size];
          rewrite (lden_agree nL E E'' _ Xb HaL), (lden_agree nL E E'' _ Xs HaL); split; reflexivity. }
      destruct (Hbz k S1 HS1) as [B1' Z1']. destruct (Hbz k' S2 HS2) as [B2' Z2']. unfold rg_disj in *. rewrite B1', Z1', B2', Z2'. exact Hd12. }
    split.
    { (* [comment removed for export] *)
      apply Forall_app. split.
      - rewrite Forall_forall in I1 |- *. intros f Hf. exact (fact_ok_agree nL E E'' f (HfL f Hf) HaL (I1 f Hf)).
      - apply Forall_map. rewrite Forall_forall in IQ |- *. intros f Hf. apply (proj2 (fact_ok_fsubst E'' σ' f)).
        exact (fact_ok_agree nQ Eq (ecomp E'' σ') f (HfQ f Hf) HaQ' (IQ f Hf)). }
    exact JQ.
  - (* [comment removed for export] *)
    intros x Hx. cbn [ms'' mkst ms_mem]. apply Hunch. intros k P Hk HwP0 Hxp.
    destruct (HPW k P Hk) as (W & v & R' & HW & Hvk & HR' & He & HbP & HzP & Hlo & Hhi & Hcase).
    assert (HxW : FxStep.in_rg E R' x) by (unfold FxStep.in_rg in *; rewrite HbP, HzP in Hxp; lia).
    destruct (rg_ent_parts _ _ _ He) as (_ & _ & Hkle & _ & _). pose proof (rkind_le_w _ _ Hkle HwP0) as HwW0.
    assert (HwR' : wkind (rg_kind R') = true).
    { destruct Hcase as [(o & _ & _ & _ & _ & _ & Hsub)|(_ & _ & _ & Ek)]; [exact (rg_sub_kind R' W o Hsub HwW0) | rewrite <- Ek; exact HwW0]. }
    destruct Hx as [Hout|Hrt].
    + unfold FxStep.outside in Hout. rewrite Forall_forall in Hout. pose proof (Hout R' (nth_error_In _ _ HR')) as X.
      unfold FxStep.in_rg in HxW. lia.
    + apply Exists_exists in Hrt as (R2 & HR2 & Hrt2 & Hx2). apply In_nth_error in HR2 as (i2 & Hi2).
      destruct (Nat.eq_dec i2 (vop_src v)) as [Heq|Hne].
      * rewrite Heq in Hi2. rewrite HR' in Hi2. injection Hi2 as <-. destruct (rg_kind R'); cbn in Hrt2, HwR'; discriminate.
      * pose proof (rgs_disj_nth E (s_rgs L) _ _ R2 R' G1 Hne Hi2 HR') as Hd12. unfold rg_disj, FxStep.in_rg in *. lia.
Qed.
#[using="Type"] Theorem call_sound : forall P0 Q rets keep qk vs rgs_w ret L K E ms,
  fn_ok segs P0 Q rets -> call_cont L P0 Q keep qk vs rgs_w ret = Some K -> sden segs E L ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next L) E E'' /\
    (forall x, fr_pt E (s_rgs L) x -> ms_mem ms'' x = ms_mem ms x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P0 Q rets keep qk vs rgs_w ret L K E ms Hfn Hcc Hd.
  destruct (call_sound_P (fun _ _ => True) fp_inv_true P0 Q rets keep qk vs rgs_w ret L K E ms (fn_ok_P segs P0 Q rets Hfn) Hcc Hd)
    as (ms'' & E'' & H1 & H2 & H3 & H4 & _).
  exists ms'', E''. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* [comment removed for export] *)
Definition kfn_ok (P0 Q : sst) : Prop :=
  forall E ms, sden segs E P0 ms ->
  exists ms' E', isteps segs ms ms' /\ sden segs E' (with_pc Q (bv_unsigned (lden E (rget (s_regs P0) ra_key)))) ms' /\
    agree (s_next P0) E E' /\ (forall x, fr_pt E (s_rgs P0) x -> ms_mem ms' x = ms_mem ms x).
(* [comment removed for export] *)
Definition kfn_okP (Φ : machine_state -> machine_state -> Prop) (P0 Q : sst) : Prop :=
  forall E ms, sden segs E P0 ms ->
  exists ms' E', isteps segs ms ms' /\ sden segs E' (with_pc Q (bv_unsigned (lden E (rget (s_regs P0) ra_key)))) ms' /\
    agree (s_next P0) E E' /\ (forall x, fr_pt E (s_rgs P0) x -> ms_mem ms' x = ms_mem ms x) /\ Φ ms ms'.
Definition kfn_ok_fp (P0 Q : sst) : Prop := kfn_okP fpeq P0 Q.
#[using="Type"] Lemma kfn_ok_P : forall P0 Q, kfn_ok P0 Q -> kfn_okP (fun _ _ => True) P0 Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P0 Q H E ms Hd. destruct (H E ms Hd) as (ms' & E' & H1 & H2 & H3 & H4).
  exists ms', E'. exact (conj H1 (conj H2 (conj H3 (conj H4 I)))).
Qed.
#[using="Type"] Lemma kfn_okP_ok : forall Φ P0 Q, kfn_okP Φ P0 Q -> kfn_ok P0 Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ P0 Q H E ms Hd. destruct (H E ms Hd) as (ms' & E' & H1 & H2 & H3 & H4 & _).
  exists ms', E'. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem call_sound_kP : forall (Φ : machine_state -> machine_state -> Prop), fp_inv Φ -> forall P0 Q keep qk vs rgs_w ret L K E ms,
  kfn_okP Φ P0 Q -> call_cont L P0 Q keep qk vs rgs_w ret = Some K -> sden segs E L ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next L) E E'' /\
    (forall x, fr_pt E (s_rgs L) x -> ms_mem ms'' x = ms_mem ms x) /\ Φ ms ms''.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦ P0 Q keep qk vs rgs_w ret L K E ms Hfn Hcc Hd.
  unfold call_cont in Hcc. destruct (call_ok L P0 Q keep qk vs rgs_w ret) eqn:Hok; [|discriminate]. injection Hcc as <-.
  unfold call_ok in Hok. cbv zeta in Hok.
  set (Lw := with_rgs L rgs_w) in *. set (σc := mcall Lw P0) in *.
  apply andb_prop in Hok as [Hok HwK]. apply andb_prop in Hok as [Hok HQr]. apply andb_prop in Hok as [Hok Hr3].
  apply andb_prop in Hok as [Hok Hr2]. apply andb_prop in Hok as [Hok Hr1]. apply andb_prop in Hok as [Hok Hra].
  apply andb_prop in Hok as [Hok Hnx]. apply andb_prop in Hok as [Hok Hrak]. apply andb_prop in Hok as [Hok Hkeq].
  apply andb_prop in Hok as [Hok Hlw]. apply andb_prop in Hok as [Hok Hkd]. apply andb_prop in Hok as [Hok Hlen].
  apply andb_prop in Hok as [Hok Hsh]. apply andb_prop in Hok as [Hok Hnq]. apply andb_prop in Hok as [Hok Hent].
  apply andb_prop in Hok as [Hok HwQ]. apply andb_prop in Hok as [Hok HwP]. apply andb_prop in Hok as [Hok HwW].
  apply andb_prop in Hok as [Hok HwL]. apply andb_prop in Hok as [Hv Hvp].
  apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2. apply Z.eqb_eq in Hr3. apply Nat.eqb_eq in Hlen. apply Pos.leb_le in Hnq.
  apply lin_eqb_eq in Hra. rewrite forallb_forall in Hlw, Hkeq.
  assert (HQr' : s_resv Q = RNone) by (destruct (s_resv Q); [reflexivity | discriminate..]).
  set (n0 := s_next P0) in *. set (nQ := s_next Q) in *. set (nL := s_next L) in *.
  set (σ' := sigq σc n0 nQ nL) in *. set (nx := (nL + nQ - n0)%positive) in *.
  (* [comment removed for export] *)
  pose proof (views_sound segs E L ms rgs_w vs Hd Hv Hvp HwW) as HdW.
  pose proof (entails_sden segs E Lw P0 σc ms (sden_0 _ _ _ _ HdW) Hent HwP) as Hd0.
  destruct (Hfn _ _ Hd0) as (ms' & Eq & Hst & HdQ & Hag & Hfr & HΦ0).
  set (retv := bv_unsigned (lden (ecomp E σc) (rget (s_regs P0) ra_key))) in HdQ.
  destruct (sden_0 _ _ _ _ Hd) as (A1 & B1 & C1 & D1 & F1 & G1 & I1 & J1).
  destruct (sden_0 _ _ _ _ Hd0) as (A0 & B0 & C0 & D0 & F0 & G0 & I0 & J0).
  destruct (sden_0 _ _ _ _ HdQ) as (AQ & BQ & CQ & DQ & FQ & GQ & IQ & JQ).
  cbn [with_pc s_regs s_rgs s_facts s_resv s_pc] in AQ, BQ, CQ, DQ, FQ, GQ, IQ.
  (* [comment removed for export] *)
  pose proof HwP as HwP'. unfold state_wf in HwP'. apply andb_prop in HwP' as [HwP' _]. apply andb_prop in HwP' as [HwP' _].
  apply andb_prop in HwP' as [HrP HgP]. rewrite forallb_forall in HgP.
  pose proof HwQ as HwQ'. unfold state_wf in HwQ'. apply andb_prop in HwQ' as [HwQ' _]. apply andb_prop in HwQ' as [HwQ' HfQ].
  apply andb_prop in HwQ' as [HrQ HgQ]. rewrite forallb_forall in HgQ, HfQ.
  pose proof HwL as HwL'. unfold state_wf in HwL'. apply andb_prop in HwL' as [HwL' _]. apply andb_prop in HwL' as [HwL' HfL].
  apply andb_prop in HwL' as [HrL HgL]. rewrite forallb_forall in HgL, HfL.
  (* [comment removed for export] *)
  assert (Hkv : forall j, (1 <= j <= 31)%nat -> existsb (Pos.eqb (Pos.of_succ_nat j)) keep = true ->
            lden Eq (rget (s_regs Q) (Pos.of_succ_nat j)) = lden E (rget (s_regs L) (Pos.of_succ_nat j))).
  { intros j Hj Hk. apply existsb_exists in Hk as (key & Hkey & Hke). apply Pos.eqb_eq in Hke. subst key.
    pose proof (Hkeq _ Hkey) as He. apply lin_eqb_eq in He. rewrite He.
    rewrite <- (lden_agree n0 (ecomp E σc) Eq _ (regs_wf_n_spec _ _ _ HrP j Hj) Hag).
    rewrite <- lden_lsubst. unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _].
    apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hre].
    rewrite <- (regs_ent_n_spec _ _ _ _ Hre j Hj). reflexivity. }
  (* [comment removed for export] *)
  assert (Hretv : retv = ret).
  { unfold retv. change ra_key with (Pos.of_succ_nat 1). assert (HinR : In ra_key keep).
    { pose proof Hrak as X. apply existsb_exists in X as (y & Hy & Hye). apply Pos.eqb_eq in Hye. subst y. exact Hy. }
    pose proof (Hkeq _ HinR) as He. apply lin_eqb_eq in He.
    rewrite (lden_agree n0 (ecomp E σc) Eq (rget (s_regs P0) (Pos.of_succ_nat 1)) (regs_wf_n_spec _ _ _ HrP 1%nat ltac:(lia)) Hag).
    change (Pos.of_succ_nat 1) with ra_key. rewrite <- He. change ra_key with (Pos.of_succ_nat 1).
    rewrite (Hkv 1%nat ltac:(lia) ltac:(change (Pos.of_succ_nat 1) with ra_key; exact Hrak)).
    change (Pos.of_succ_nat 1) with ra_key. rewrite Hra. unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite w64_mod.
    rewrite Z.mod_mod by (unfold two64; lia). apply Z.mod_small. unfold two64 in *; lia. }
  assert (Hrs : isteps segs ms' (@mkst (mkFP (ms_fregs ms') (ms_fcsr ms')) (ms_regs ms') (Z_to_bv 64 ret) (ms_mem ms') (ms_rom ms'))).
  { rewrite (sden_mkst segs Eq (with_pc Q retv) ms' HdQ HQr') at 1. cbn [with_pc s_pc]. rewrite Hretv. apply ist_refl. }
  set (ms'' := @mkst (mkFP (ms_fregs ms') (ms_fcsr ms')) (ms_regs ms') (Z_to_bv 64 ret) (ms_mem ms') (ms_rom ms')) in Hrs.
  (* [comment removed for export] *)
  set (E'' := fun x : positive => if Pos.ltb x nL then E x else if Pos.ltb x nx then Eq (x + n0 - nL)%positive
                                 else if Pos.ltb x (nx + 32) then getr (ms_regs ms') (Z_to_bv 5 (Zpos x - Zpos nx)) else E x).
  assert (HaL : agree nL E E'').
  { intros x Hx. unfold E''. rewrite (proj2 (Pos.ltb_lt x nL) Hx). reflexivity. }
  assert (HaQ : forall y, (y < nQ)%positive -> ecomp E'' σ' y = Eq y).
  { intros y Hy. unfold ecomp. unfold σ'. rewrite sigq_get by exact Hy. destruct (Pos.ltb y n0) eqn:Hy0.
    - apply Pos.ltb_lt in Hy0. rewrite <- (lden_agree nL E E'' _ (Hlw y (in_vars_below _ _ Hy0)) HaL). exact (Hag y Hy0).
    - apply Pos.ltb_ge in Hy0. rewrite lden_lvar. unfold E''.
      rewrite (proj2 (Pos.ltb_ge (nL + y - n0) nL)) by lia. rewrite (proj2 (Pos.ltb_lt (nL + y - n0) nx)) by (unfold nx; lia).
      f_equal. lia. }
  assert (HaQ' : agree nQ Eq (ecomp E'' σ')) by (intros y Hy; symmetry; exact (HaQ y Hy)).
  (* [comment removed for export] *)
  destruct (views_nth _ _ _ Hv) as [HlV Hvw].
  unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _].
  apply andb_prop in Hent as [Hent Hrge]. cbn [s_rgs with_rgs Lw] in Hrge.
  destruct (rgs_ent_nth _ _ _ Hrge) as [HlW Hwk].
  assert (Hbs0 : forall k R, nth_error (s_rgs P0) k = Some R -> lden (ecomp E σc) (rg_base R) = lden Eq (rg_base R) /\ rsz (ecomp E σc) R = rsz Eq R).
  { intros k R Hk. pose proof (HgP R (nth_error_In _ _ Hk)) as HR. unfold rwf in HR. apply andb_prop in HR as [HR _]. apply andb_prop in HR as [Hb Hs].
    split; [exact (lden_agree n0 _ _ _ Hb Hag) | unfold rsz; rewrite (lden_agree n0 _ _ _ Hs Hag); reflexivity]. }
  assert (HPW : forall k P, nth_error (s_rgs P0) k = Some P -> exists W v R, nth_error rgs_w k = Some W /\ nth_error vs k = Some v /\
             nth_error (s_rgs L) (vop_src v) = Some R /\ rg_ent W P σc = true /\
             bv_unsigned (lden (ecomp E σc) (rg_base P)) = bv_unsigned (lden E (rg_base W)) /\ rsz (ecomp E σc) P = rsz E W /\
             bv_unsigned (lden E (rg_base R)) <= bv_unsigned (lden E (rg_base W)) /\
             bv_unsigned (lden E (rg_base W)) + rsz E W <= bv_unsigned (lden E (rg_base R)) + rsz E R /\
             ((exists o, v = VSub (vop_src v) o /\ 0 <= o /\ bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o /\
                         o + rsz E W <= rsz E R /\ rsz E W = csz W /\ rg_sub_ok R W o = true) \/
              (v = VCopy (vop_src v) /\ rg_base W = rg_base R /\ rg_size W = rg_size R /\ rg_kind W = rg_kind R))).
  { intros k P Hk. destruct (nth_error rgs_w k) as [W|] eqn:HW; [|apply nth_error_None in HW; pose proof (nth_error_Some (s_rgs P0) k) as X; rewrite Hk in X; specialize (proj1 X ltac:(discriminate)); lia].
    destruct (nth_error vs k) as [v|] eqn:Hvk; [|apply nth_error_None in Hvk; pose proof (nth_error_Some rgs_w k) as X; rewrite HW in X; specialize (proj1 X ltac:(discriminate)); lia].
    pose proof (Hvw k W v HW Hvk) as Hv1. destruct (view1_sound segs E (ms_mem ms) (s_rgs L) W v F1 Hv1) as (R & HR & _ & Hs1).
    pose proof (Hwk k W P HW Hk) as He. destruct (rg_ent_parts _ _ _ He) as (Eb & Ez & _ & _ & _).
    exists W, v, R. split; [first [exact HW | reflexivity]|]. split; [first [exact Hvk | reflexivity]|]. split; [exact HR|]. split; [exact He|].
    split; [rewrite <- lden_lsubst, <- Eb; reflexivity|]. split; [unfold rsz; rewrite <- lden_lsubst, <- Ez; reflexivity|].
    destruct Hs1 as [(o & Eo & Ho & HA & Hn & Hq)|(Eo & Eb' & Ez' & Ek)].
    - split; [lia|]. split; [lia|]. left. exists o. refine (conj Eo (conj Ho (conj HA (conj Hn (conj Hq _))))).
      rewrite Eo in Hv1. cbn [view1_ok vop_src] in Hv1. rewrite HR in Hv1. exact Hv1.
    - split; [rewrite Eb'; lia|]. split; [unfold rsz; rewrite Eb', Ez'; lia|]. right. exact (conj Eo (conj Eb' (conj Ez' Ek))). }
  (* [comment removed for export] *)
  assert (Hsrc : forall i R x k P, nth_error (s_rgs L) i = Some R -> FxStep.in_rg E R x -> nth_error (s_rgs P0) k = Some P ->
             FxStep.in_rg (ecomp E σc) P x -> exists W v, nth_error rgs_w k = Some W /\ nth_error vs k = Some v /\ vop_src v = i).
  { intros i R x k P HR Hx Hk Hxp. destruct (HPW k P Hk) as (W & v & R' & HW & Hvk & HR' & _ & HbP & HzP & Hlo & Hhi & _).
    exists W, v. split; [exact HW|]. split; [exact Hvk|].
    destruct (Nat.eq_dec (vop_src v) i) as [Heq|Hne]; [exact Heq|]. exfalso.
    pose proof (rgs_disj_nth E (s_rgs L) _ _ R' R G1 Hne HR' HR) as Hd12. unfold rg_disj, FxStep.in_rg in *. lia. }
  (* [comment removed for export] *)
  assert (Hunch : forall x, (forall k P, nth_error (s_rgs P0) k = Some P -> wkind (rg_kind P) = true -> ~ FxStep.in_rg (ecomp E σc) P x) ->
             ms_mem ms' x = ms_mem ms x).
  { intros x Hno. exact (cs_unchanged segs (ecomp E σc) Eq (s_rgs P0) (s_rgs Q) (ms_mem ms) (ms_mem ms') x F0 FQ Hsh Hlen Hkd Hbs0 Hfr Hno). }
  (* [comment removed for export] *)
  assert (HwR : forall i R, nth_error (s_rgs L) i = Some R -> rwf nL R = true) by (intros i R Hi; exact (HgL R (nth_error_In _ _ Hi))).
  (* [comment removed for export] *)
  assert (keep_out_ok : forall i R k0 ks pk v, nth_error (s_rgs L) i = Some R -> rg_ok segs E (ms_mem ms) R -> rg_ok segs E'' (ms_mem ms) R ->
            lden E (rg_base R) = lden E'' (rg_base R) -> rsz E R = rsz E'' R -> wviews (s_rgs P0) vs 0 i = k0 :: ks ->
            tget pk (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R)) = Some v ->
            Zpos pk - 1 < rsz E'' R /\ rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + (Zpos pk - 1))) = Some (bden E'' v)).
  { intros i R k0 ks pk v HR HRok HRok'' HbR HzR Hwv Hkeep.
    unfold keep_out in Hkeep. rewrite tget_tfilter in Hkeep.
    destruct (out_wins σc (s_rgs P0) vs (k0 :: ks) (Zpos pk - 1)) eqn:Hout; [|discriminate].
    pose proof HRok'' as X. unfold rg_ok in X. cbv zeta in X. destruct X as (_ & _ & _ & X4).
    destruct (X4 pk v Hkeep) as [Hp1 Hp2]. split; [exact Hp1|].
    set (j := Zpos pk - 1) in *.
    set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) in *.
    assert (Hj : 0 <= j < rsz E R) by (unfold j; rewrite HzR; lia).
    assert (Hxr : FxStep.in_rg E R x).
    { pose proof (rg_in_off E _ R j HRok Hj) as Y. unfold x. rewrite <- HbR. exact Y. }
    assert (Hm : ms_mem ms' x = ms_mem ms x).
    { apply Hunch. intros k P Hk Hwp Hxp.
      destruct (Hsrc i R x k P HR Hxr Hk Hxp) as (W & v0 & HW & Hvk & Hs).
      pose proof (wviews_in (s_rgs P0) vs 0 i k P v0 Hk Hvk Hwp Hs) as Hko. rewrite Hwv in Hko. cbn [Nat.add] in Hko.
      unfold out_wins in Hout. rewrite forallb_forall in Hout. pose proof (Hout _ Hko) as Ho. cbv beta iota in Ho.
      unfold view_win in Ho. rewrite Hvk, Hk in Ho. destruct v0 as [i0|i0 o0]; [discriminate|].
      destruct (is_const (lsubst σc (rg_size P))) as [nc|] eqn:Hnc; [|discriminate].
      destruct (HPW k P Hk) as (W' & v' & R' & HW' & Hv' & HR' & _ & HbP & HzP & _ & _ & Hcase).
      rewrite HW in HW'. injection HW' as <-. rewrite Hvk in Hv'. injection Hv' as <-. rewrite Hs in HR'. rewrite HR in HR'. injection HR' as <-.
      destruct Hcase as [(o1 & Eo1 & _ & HA & _ & _ & _)|(Eo1 & _)]; [|discriminate Eo1].
      cbn [vop_src] in Eo1. injection Eo1 as Eo2. rewrite <- Eo2 in HA.
      pose proof (is_const_u E (lsubst σc (rg_size P)) nc Hnc) as Hzn. rewrite lden_lsubst in Hzn.
      unfold FxStep.in_rg in Hxp. unfold rsz in Hxp. rewrite Hzn in Hxp. rewrite HbP, HA in Hxp.
      assert (Hxu : bv_unsigned x = bv_unsigned (lden E (rg_base R)) + j).
      { unfold x. rewrite <- HbR. rewrite u_small64; [reflexivity|]. pose proof HRok as Y. unfold rg_ok in Y. cbv zeta in Y. destruct Y as (Y1 & Y2 & _).
        pose proof (u_range E (rg_base R)) as Y3. unfold two64 in *. lia. }
      rewrite Hxu in Hxp. apply Bool.orb_true_iff in Ho as [Ho|Ho]; [apply Z.ltb_lt in Ho | apply Z.leb_le in Ho]; lia. }
    unfold rd1 in Hp2 |- *. fold x in Hp2 |- *. rewrite Hm. exact Hp2. }
  assert (HRK : Forall (rg_ok segs E'' (ms_mem ms')) (map_i (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs) 0 (s_rgs L))).
  { apply Forall_nth'. intros i RK Hi. destruct (nth_map_i' _ _ _ _ Hi) as (R & HR & ->).
    rewrite Forall_nth' in F1. pose proof (F1 i R HR) as HRok.
    pose proof (rg_ok_agree segs nL E E'' (ms_mem ms) R (HwR i R HR) HaL HRok) as HRok''.
    assert (HbR : lden E (rg_base R) = lden E'' (rg_base R)).
    { pose proof (HwR i R HR) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. exact (lden_agree nL _ _ _ X HaL). }
    assert (HzR : rsz E R = rsz E'' R).
    { pose proof (HwR i R HR) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. unfold rsz. rewrite (lden_agree nL _ _ _ X HaL). reflexivity. }
    unfold new_rg. destruct (wviews (s_rgs P0) vs 0 i) as [|k0 ks] eqn:Hwv.
    - (* [comment removed for export] *)
      apply (rg_ok_mem segs E'' (ms_mem ms) (ms_mem ms') R HRok''). intros j Hj. apply Hunch. intros k P Hk Hwkp Hxp.
      rewrite <- HbR in Hxp. rewrite <- HzR in Hj.
      assert (Hxr : FxStep.in_rg E R (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + j))).
      { pose proof HRok as X. unfold rg_ok in X. cbv zeta in X. destruct X as (X1 & X2 & _). pose proof (u_range E (rg_base R)) as X3.
        unfold FxStep.in_rg. rewrite u_small64 by (unfold two64 in *; lia). lia. }
      destruct (Hsrc i R _ k P HR Hxr Hk Hxp) as (W & v & HW & Hvk & Hs).
      exact (wviews_nil _ _ _ _ Hwv k P v Hk Hvk Hwkp Hs).
    - (* [comment removed for export] *)
      destruct (wviews_spec (s_rgs P0) vs 0 i (fst k0) (snd k0) ltac:(rewrite Hwv; left; destruct k0; reflexivity))
        as (Pk & vk & HPk & Hvk & _ & HwPk & Hsk & _). rewrite Nat.sub_0_r in HPk, Hvk.
      (* [comment removed for export] *)
      assert (HwkR : wkind (rg_kind R) = true).
      { destruct (HPW _ Pk HPk) as (W & v & R' & HW & Hv' & HR' & He & _ & _ & _ & _ & Hcase).
        rewrite Hvk in Hv'. injection Hv' as <-. rewrite Hsk in HR'. rewrite HR in HR'. injection HR' as <-.
        destruct (rg_ent_parts _ _ _ He) as (_ & _ & Hkle & _ & _). pose proof (rkind_le_w _ _ Hkle HwPk) as HwWk.
        destruct Hcase as [(o & _ & _ & _ & _ & _ & Hsub)|(_ & _ & _ & Ek)].
        - exact (rg_sub_kind R W o Hsub HwWk).
        - rewrite <- Ek. exact HwWk. }
      (* [comment removed for export] *)
      assert (HRW : forall j, 0 <= j < rsz E'' R ->
                rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) <> None /\
                wview segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) <> None).
      { intros j Hj. set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)).
        assert (Hxr : FxStep.in_rg E R x).
        { pose proof (rg_in_off E _ R j HRok ltac:(rewrite HzR; exact Hj)) as X. unfold x. rewrite <- HbR. exact X. }
        destruct (Exists_dec (fun P => wkind (rg_kind P) = true /\ FxStep.in_rg (ecomp E σc) P x) (s_rgs P0)) as [Hin|Hout].
        { intros P. destruct (wkind (rg_kind P)) eqn:Hwp; [|right; intros [X _]; discriminate].
          destruct (in_rg_dec (ecomp E σc) P x) as [X|X]; [left; split; [reflexivity | exact X] | right; intros [_ Y]; exact (X Y)]. }
        * apply Exists_exists in Hin as (P & HP & HwP0 & Hxp). apply In_nth_error in HP as (k & Hk).
          destruct (shape_nth _ _ Hsh k P Hk) as (RQ & HQk & EbQ & EzQ).
          rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ.
          destruct (Hbs0 k P Hk) as [Hb0 Hz0].
          assert (HxQ : FxStep.in_rg Eq RQ x).
          { apply (in_rg_transfer (ecomp E σc) Eq P RQ x); [rewrite Hb0, EbQ; reflexivity | unfold rsz; rewrite EzQ; exact Hz0 | exact Hxp]. }
          exact (rg_at_w Eq _ RQ x HRQ HxQ (kinds_nth _ _ Hkd k P RQ Hk HQk HwP0)).
        * assert (Hm : ms_mem ms' x = ms_mem ms x).
          { apply Hunch. intros k P Hk Hw' Hxp. apply Hout. apply Exists_exists. exists P. split; [exact (nth_error_In _ _ Hk) | split; assumption]. }
          destruct (rg_at_w E _ R x HRok Hxr HwkR) as [Y1 Y2]. unfold rd1, wview in Y1, Y2 |- *. rewrite Hm. split; assumption. }
      (* [comment removed for export] *)
      assert (HIMP : forall pk v, tget pk (imp_cont (s_rgs Q) σ' (k0 :: ks) (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R))) = Some v ->
                Zpos pk - 1 < rsz E'' R /\ rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + (Zpos pk - 1))) = Some (bden E'' v)).
      { intros pk v Hpk. destruct (in_imp_cont _ _ _ _ _ _ Hpk) as [(k & o & RQ & q & w & Hko & HQk & Hqw & Ep & Ev)|Hkeep];
          [|exact (keep_out_ok i R k0 ks pk v HR HRok HRok'' HbR HzR Hwv Hkeep)].
        rewrite <- Hwv in Hko.
        destruct (wviews_spec (s_rgs P0) vs 0 i k o Hko) as (P & v' & HP & Hv' & _ & HwP0 & Hs' & Eo). rewrite Nat.sub_0_r in HP, Hv'.
        destruct (HPW k P HP) as (W & v'' & R' & HW & Hv'' & HR' & _ & HbP & HzP & Hlo & Hhi & Hcase).
        rewrite Hv' in Hv''. injection Hv'' as <-. rewrite Hs' in HR'. rewrite HR in HR'. injection HR' as <-.
        destruct (shape_nth _ _ Hsh k P HP) as (RQ' & HQk' & EbQ & EzQ). rewrite HQk in HQk'. injection HQk' as <-.
        rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ. unfold rg_ok in HRQ. cbv zeta in HRQ. destruct HRQ as (_ & _ & _ & HQ4).
        destruct (HQ4 q w Hqw) as [Hq1 Hq2].
        destruct (Hbs0 k P HP) as [Hb0 Hz0].
        assert (Hoff : 0 <= o /\ bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o /\ o + rsz E W <= rsz E R).
        { destruct Hcase as [(o' & Eo' & Ho' & HA & Hn' & _)|(Eo' & Eb' & Ez' & _)].
          - rewrite Eo' in Eo. cbn in Eo. subst o. clear - Ho' HA Hn'. lia.
          - rewrite Eo' in Eo. cbn in Eo. subst o. rewrite Eb'. unfold rsz. rewrite Ez'. clear. lia. }
        destruct Hoff as (Ho0 & HbW & HzW).
        assert (HbQ : bv_unsigned (lden Eq (rg_base RQ)) = bv_unsigned (lden E (rg_base R)) + o) by (rewrite EbQ, <- Hb0, HbP; exact HbW).
        assert (HzQ : rsz Eq RQ = rsz E W) by (unfold rsz; rewrite EzQ; fold (rsz Eq P); rewrite <- Hz0; exact HzP).
        assert (Hp1 : Zpos pk - 1 = o + (Zpos q - 1)) by (rewrite Ep; unfold okey; rewrite Z2Pos.id by (clear - Ho0; lia); clear; lia).
        rewrite Hp1. split; [rewrite <- HzR; clear - Hq1 HzQ HzW; lia|].
        rewrite <- HbR. rewrite Z.add_assoc. rewrite <- HbQ. rewrite Hq2. rewrite Ev. f_equal.
        rewrite bden_bsubst. apply (bden_agree nQ Eq (ecomp E'' σ') w); [|exact HaQ'].
        pose proof (HgQ RQ (nth_error_In _ _ HQk)) as X. unfold rwf in X. apply andb_prop in X as [_ X].
        exact (tforall_spec _ _ X q w Hqw). }
      unfold rg_ok. cbv zeta. rewrite rsz_RG_eq. cbn [rg_base rg_kind rg_cont].
      pose proof HRok'' as HRok3. unfold rg_ok in HRok3. cbv zeta in HRok3. destruct HRok3 as (H1 & H2 & _ & _).
      refine (conj H1 (conj H2 (conj _ HIMP))).
      destruct (rz_keep (s_rgs Q) R (k0 :: ks)) eqn:Hrz; [|exact HRW].
      (* [comment removed for export] *)
      intros j Hj. split; [exact (HRW j Hj)|]. intros Hnone.
      set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)).
      assert (Hxr : FxStep.in_rg E R x).
      { pose proof (rg_in_off E _ R j HRok ltac:(rewrite HzR; exact Hj)) as X. unfold x. rewrite <- HbR. exact X. }
      unfold rz_keep in Hrz. apply andb_prop in Hrz as [Hrz Hzv]. apply andb_prop in Hrz as [HkR Hc0].
      rewrite forallb_forall in Hzv.
      destruct (Exists_dec (fun P => wkind (rg_kind P) = true /\ FxStep.in_rg (ecomp E σc) P x) (s_rgs P0)) as [Hin|Hout].
      { intros P. destruct (wkind (rg_kind P)) eqn:Hwp; [|right; intros [X _]; discriminate].
        destruct (in_rg_dec (ecomp E σc) P x) as [X|X]; [left; split; [reflexivity | exact X] | right; intros [_ Y]; exact (X Y)]. }
      + apply Exists_exists in Hin as (P & HP & HwP0 & Hxp). apply In_nth_error in HP as (k & Hk).
        destruct (Hsrc i R x k P HR Hxr Hk Hxp) as (W & v & HW & Hvk' & Hs).
        pose proof (wviews_in (s_rgs P0) vs 0 i k P v Hk Hvk' HwP0 Hs) as Hko. rewrite Hwv in Hko. cbn [Nat.add] in Hko.
        destruct (shape_nth _ _ Hsh k P Hk) as (RQ & HQk & EbQ & EzQ).
        pose proof (Hzv _ Hko) as HzQ. cbv beta iota in HzQ. rewrite HQk in HzQ.
        rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ.
        destruct (Hbs0 k P Hk) as [Hb0 Hz0].
        destruct (HPW k P Hk) as (W' & v' & R' & HW' & Hv' & HR' & _ & HbP & HzP & Hlo & Hhi & Hcase).
        rewrite HW in HW'. injection HW' as <-. rewrite Hvk' in Hv'. injection Hv' as <-. rewrite Hs in HR'. rewrite HR in HR'. injection HR' as <-.
        set (o := match v with VCopy _ => 0 | VSub _ o' => o' end) in *.
        assert (HbW : bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o).
        { unfold o. destruct Hcase as [(o' & Eo' & _ & HA & _)|(Eo' & Eb' & _ & _)]; rewrite Eo'; [exact HA | rewrite Eb'; lia]. }
        assert (HbQ : bv_unsigned (lden Eq (rg_base RQ)) = bv_unsigned (lden E (rg_base R)) + o) by (rewrite EbQ, <- Hb0, HbP; exact HbW).
        assert (HxQ : FxStep.in_rg Eq RQ x).
        { apply (in_rg_transfer (ecomp E σc) Eq P RQ x); [rewrite Hb0, EbQ; reflexivity | unfold rsz; rewrite EzQ; exact Hz0 | exact Hxp]. }
        unfold rg_ok in HRQ. cbv zeta in HRQ. destruct HRQ as (_ & _ & HQ3 & _).
        unfold FxStep.in_rg in HxQ. rewrite HbQ in HxQ.
        assert (Hxu : bv_unsigned x = bv_unsigned (lden E (rg_base R)) + j).
        { unfold x. rewrite <- HbR. rewrite u_small64; [reflexivity|]. pose proof HRok as X. unfold rg_ok in X. cbv zeta in X. destruct X as (X1 & X2 & _).
          pose proof (u_range E (rg_base R)) as X3. rewrite <- HzR in Hj. unfold two64 in *. lia. }
        specialize (HQ3 (j - o) ltac:(rewrite Hxu in HxQ; lia)).
        destruct (rg_kind RQ) eqn:EkQ; try discriminate. destruct HQ3 as [_ HQ3].
        replace (bv_unsigned (lden Eq (rg_base RQ)) + (j - o)) with (bv_unsigned x) in HQ3 by (rewrite HbQ, Hxu; lia).
        rewrite Z_to_bv_bv_unsigned in HQ3. apply HQ3.
        destruct (tget (okey (j - o)) (rg_cont RQ)) as [w|] eqn:Hw; [|reflexivity]. exfalso.
        pose proof (imp_cont_some (s_rgs Q) σ' (k0 :: ks) (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R)) k o RQ (okey (j - o)) w Hko HQk Hw) as X.
        replace (o + (Zpos (okey (j - o)) - 1)) with j in X by (unfold okey; rewrite Z2Pos.id by lia; lia).
        exact (X Hnone).
      + assert (Hm : ms_mem ms' x = ms_mem ms x).
        { apply Hunch. intros k P Hk Hw' Hxp. apply Hout. apply Exists_exists. exists P. split; [exact (nth_error_In _ _ Hk) | split; assumption]. }
        pose proof HRok'' as X. unfold rg_ok in X. cbv zeta in X. destruct X as (_ & _ & X3 & X4).
        destruct (rg_kind R) eqn:EkR; try discriminate.
        specialize (X3 j Hj). destruct X3 as [_ X3]. unfold rd1 in X3 |- *. fold x in X3 |- *. rewrite Hm.
        destruct (tget (okey j) (rg_cont R)) as [w|] eqn:Hw; [|exact (X3 eq_refl)].
        pose proof (tforall_spec _ _ Hc0 _ _ Hw) as Hw0. cbv beta in Hw0. destruct w as [z|l jj]; [|discriminate]. apply Z.eqb_eq in Hw0. subst z.
        destruct (X4 (okey j) (BK 0) Hw) as [_ X5]. replace (Zpos (okey j) - 1) with j in X5 by (unfold okey; rewrite Z2Pos.id by lia; lia).
        fold x in X5. unfold rd1 in X5. exact X5. }
  (* [comment removed for export] *)
  exists ms'', E''. split; [exact (isteps_trans segs _ _ _ Hst Hrs)|]. split; [|split; [exact HaL| split; [|exact (HΦ ms ms' ms'' eq_refl eq_refl HΦ0)]]].
  - apply sden0_sden; [exact HwK|].
    unfold sden0. cbn [cont_st s_pc s_regs s_rgs s_facts s_resv]. fold nL n0 nQ. fold σ'. fold nx.
    cbn [ms'' mkst ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr fp_csr].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      intros r. destruct (decide (r = 0%bv)) as [->|Hr0].
      - change (rkey 0%bv) with xH. unfold rget. reflexivity.
      - destruct (rkey_succ r Hr0) as (j & Hj & Hkey). rewrite Hkey, regs_cont_get by exact Hj.
        destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) keep) eqn:Hk.
        + rewrite (DQ r). cbn [with_pc s_regs]. rewrite Hkey. rewrite (Hkv j Hj Hk).
          apply (lden_agree nL E E''); [exact (regs_wf_n_spec _ _ _ HrL j Hj) | exact HaL].
        + destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) qk) eqn:Hq.
          * rewrite (DQ r). cbn [with_pc s_regs]. rewrite Hkey. rewrite lden_lsubst.
            apply (lden_agree nQ Eq (ecomp E'' σ')); [exact (regs_wf_n_spec _ _ _ HrQ j Hj) | exact HaQ'].
          * rewrite lden_lvar. unfold E''. rewrite (proj2 (Pos.ltb_ge (nx + Pos.of_nat j) nL)) by (unfold nx; lia).
            rewrite (proj2 (Pos.ltb_ge (nx + Pos.of_nat j) nx)) by lia. rewrite (proj2 (Pos.ltb_lt (nx + Pos.of_nat j) (nx + 32))) by lia.
            f_equal.
            pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 5) with 32 in Rr.
            assert (Hu : bv_unsigned r = Z.of_nat j).
            { apply (f_equal Zpos) in Hkey. unfold rkey, bv_key in Hkey. rewrite Z2Pos.id in Hkey by lia. rewrite Zpos_P_of_succ_nat in Hkey. lia. }
            assert (Ej : Zpos (Pos.of_nat j) = Z.of_nat j) by (rewrite <- positive_nat_Z, Nat2Pos.id by lia; reflexivity).
            apply bv_eq. rewrite Z_to_bv_unsigned, Hu. rewrite Pos2Z.inj_add, Ej.
            replace (Zpos nx + Z.of_nat j - Zpos nx) with (Z.of_nat j) by lia. symmetry. apply bv_wrap_small. unfold bv_modulus. lia. }
    split; [exact HRK|].
    split.
    { (* [comment removed for export] *)
      apply rgs_disj_nth_inv. intros k k' R1 R2 Hkk H1 H2.
      destruct (nth_map_i' _ _ _ _ H1) as (S1 & HS1 & ->). destruct (nth_map_i' _ _ _ _ H2) as (S2 & HS2 & ->).
      pose proof (rgs_disj_nth E (s_rgs L) k k' S1 S2 G1 ltac:(lia) HS1 HS2) as Hd12.
      assert (Hbz : forall i S, nth_error (s_rgs L) i = Some S -> bv_unsigned (lden E'' (rg_base (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs i S))) = bv_unsigned (lden E (rg_base S)) /\
                 rsz E'' (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs i S) = rsz E S).
      { intros i S HS. pose proof (HwR i S HS) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [Xb Xs].
        unfold new_rg. destruct (wviews (s_rgs P0) vs 0 i); cbn [rg_base]; unfold rsz; cbn [rg_size];
          rewrite (lden_agree nL E E'' _ Xb HaL), (lden_agree nL E E'' _ Xs HaL); split; reflexivity. }
      destruct (Hbz k S1 HS1) as [B1' Z1']. destruct (Hbz k' S2 HS2) as [B2' Z2']. unfold rg_disj in *. rewrite B1', Z1', B2', Z2'. exact Hd12. }
    split.
    { (* [comment removed for export] *)
      apply Forall_app. split.
      - rewrite Forall_forall in I1 |- *. intros f Hf. exact (fact_ok_agree nL E E'' f (HfL f Hf) HaL (I1 f Hf)).
      - apply Forall_map. rewrite Forall_forall in IQ |- *. intros f Hf. apply (proj2 (fact_ok_fsubst E'' σ' f)).
        exact (fact_ok_agree nQ Eq (ecomp E'' σ') f (HfQ f Hf) HaQ' (IQ f Hf)). }
    exact JQ.
  - (* [comment removed for export] *)
    intros x Hx. cbn [ms'' mkst ms_mem]. apply Hunch. intros k P Hk HwP0 Hxp.
    destruct (HPW k P Hk) as (W & v & R' & HW & Hvk & HR' & He & HbP & HzP & Hlo & Hhi & Hcase).
    assert (HxW : FxStep.in_rg E R' x) by (unfold FxStep.in_rg in *; rewrite HbP, HzP in Hxp; lia).
    destruct (rg_ent_parts _ _ _ He) as (_ & _ & Hkle & _ & _). pose proof (rkind_le_w _ _ Hkle HwP0) as HwW0.
    assert (HwR' : wkind (rg_kind R') = true).
    { destruct Hcase as [(o & _ & _ & _ & _ & _ & Hsub)|(_ & _ & _ & Ek)]; [exact (rg_sub_kind R' W o Hsub HwW0) | rewrite <- Ek; exact HwW0]. }
    destruct Hx as [Hout|Hrt].
    + unfold FxStep.outside in Hout. rewrite Forall_forall in Hout. pose proof (Hout R' (nth_error_In _ _ HR')) as X.
      unfold FxStep.in_rg in HxW. lia.
    + apply Exists_exists in Hrt as (R2 & HR2 & Hrt2 & Hx2). apply In_nth_error in HR2 as (i2 & Hi2).
      destruct (Nat.eq_dec i2 (vop_src v)) as [Heq|Hne].
      * rewrite Heq in Hi2. rewrite HR' in Hi2. injection Hi2 as <-. destruct (rg_kind R'); cbn in Hrt2, HwR'; discriminate.
      * pose proof (rgs_disj_nth E (s_rgs L) _ _ R2 R' G1 Hne Hi2 HR') as Hd12. unfold rg_disj, FxStep.in_rg in *. lia.
Qed.
#[using="Type"] Theorem call_sound_k : forall P0 Q keep qk vs rgs_w ret L K E ms,
  kfn_ok P0 Q -> call_cont L P0 Q keep qk vs rgs_w ret = Some K -> sden segs E L ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next L) E E'' /\
    (forall x, fr_pt E (s_rgs L) x -> ms_mem ms'' x = ms_mem ms x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P0 Q keep qk vs rgs_w ret L K E ms Hfn Hcc Hd.
  destruct (call_sound_kP (fun _ _ => True) fp_inv_true P0 Q keep qk vs rgs_w ret L K E ms (kfn_ok_P P0 Q Hfn) Hcc Hd)
    as (ms'' & E'' & H1 & H2 & H3 & H4 & _).
  exists ms'', E''. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* [comment removed for export] *)
Definition kfrag_ok (P0 Q : sst) (pcQ : Z) : Prop :=
  forall E ms, sden segs E P0 ms ->
  exists ms' E', isteps segs ms ms' /\ sden segs E' (with_pc Q pcQ) ms' /\
    agree (s_next P0) E E' /\ (forall x, fr_pt E (s_rgs P0) x -> ms_mem ms' x = ms_mem ms x).
(* [comment removed for export] *)
Definition kfrag_okP (Φ : machine_state -> machine_state -> Prop) (P0 Q : sst) (pcQ : Z) : Prop :=
  forall E ms, sden segs E P0 ms ->
  exists ms' E', isteps segs ms ms' /\ sden segs E' (with_pc Q pcQ) ms' /\
    agree (s_next P0) E E' /\ (forall x, fr_pt E (s_rgs P0) x -> ms_mem ms' x = ms_mem ms x) /\ Φ ms ms'.
Definition kfrag_ok_fp (P0 Q : sst) (pcQ : Z) : Prop := kfrag_okP fpeq P0 Q pcQ.
#[using="Type"] Lemma kfrag_ok_P : forall P0 Q pcQ, kfrag_ok P0 Q pcQ -> kfrag_okP (fun _ _ => True) P0 Q pcQ.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P0 Q pcQ H E ms Hd. destruct (H E ms Hd) as (ms' & E' & H1 & H2 & H3 & H4).
  exists ms', E'. exact (conj H1 (conj H2 (conj H3 (conj H4 I)))).
Qed.
#[using="Type"] Lemma kfrag_okP_ok : forall Φ P0 Q pcQ, kfrag_okP Φ P0 Q pcQ -> kfrag_ok P0 Q pcQ.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ P0 Q pcQ H E ms Hd. destruct (H E ms Hd) as (ms' & E' & H1 & H2 & H3 & H4 & _).
  exists ms', E'. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem frag_sound_kP : forall (Φ : machine_state -> machine_state -> Prop), fp_inv Φ -> forall P0 Q keep qk vs rgs_w ret L K E ms,
  kfrag_okP Φ P0 Q ret -> frag_cont L P0 Q keep qk vs rgs_w ret = Some K -> sden segs E L ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next L) E E'' /\
    (forall x, fr_pt E (s_rgs L) x -> ms_mem ms'' x = ms_mem ms x) /\ Φ ms ms''.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦ P0 Q keep qk vs rgs_w ret L K E ms Hfn Hcc Hd.
  unfold frag_cont in Hcc. destruct (frag_ok L P0 Q keep qk vs rgs_w ret) eqn:Hok; [|discriminate]. injection Hcc as <-.
  unfold frag_ok in Hok. cbv zeta in Hok.
  set (Lw := with_rgs L rgs_w) in *. set (σc := mcall Lw P0) in *.
  apply andb_prop in Hok as [Hok HwK]. apply andb_prop in Hok as [Hok HQr].
  apply andb_prop in Hok as [Hok Hnx]. apply andb_prop in Hok as [Hok Hkeq].
  apply andb_prop in Hok as [Hok Hlw]. apply andb_prop in Hok as [Hok Hkd]. apply andb_prop in Hok as [Hok Hlen].
  apply andb_prop in Hok as [Hok Hsh]. apply andb_prop in Hok as [Hok Hnq]. apply andb_prop in Hok as [Hok Hent].
  apply andb_prop in Hok as [Hok HwQ]. apply andb_prop in Hok as [Hok HwP]. apply andb_prop in Hok as [Hok HwW].
  apply andb_prop in Hok as [Hok HwL]. apply andb_prop in Hok as [Hv Hvp].
  apply Nat.eqb_eq in Hlen. apply Pos.leb_le in Hnq.
  rewrite forallb_forall in Hlw, Hkeq.
  assert (HQr' : s_resv Q = RNone) by (destruct (s_resv Q); [reflexivity | discriminate..]).
  set (n0 := s_next P0) in *. set (nQ := s_next Q) in *. set (nL := s_next L) in *.
  set (σ' := sigq σc n0 nQ nL) in *. set (nx := (nL + nQ - n0)%positive) in *.
  (* [comment removed for export] *)
  pose proof (views_sound segs E L ms rgs_w vs Hd Hv Hvp HwW) as HdW.
  pose proof (entails_sden segs E Lw P0 σc ms (sden_0 _ _ _ _ HdW) Hent HwP) as Hd0.
  destruct (Hfn _ _ Hd0) as (ms' & Eq & Hst & HdQ & Hag & Hfr & HΦ0).
  destruct (sden_0 _ _ _ _ Hd) as (A1 & B1 & C1 & D1 & F1 & G1 & I1 & J1).
  destruct (sden_0 _ _ _ _ Hd0) as (A0 & B0 & C0 & D0 & F0 & G0 & I0 & J0).
  destruct (sden_0 _ _ _ _ HdQ) as (AQ & BQ & CQ & DQ & FQ & GQ & IQ & JQ).
  cbn [with_pc s_regs s_rgs s_facts s_resv s_pc] in AQ, BQ, CQ, DQ, FQ, GQ, IQ.
  (* [comment removed for export] *)
  pose proof HwP as HwP'. unfold state_wf in HwP'. apply andb_prop in HwP' as [HwP' _]. apply andb_prop in HwP' as [HwP' _].
  apply andb_prop in HwP' as [HrP HgP]. rewrite forallb_forall in HgP.
  pose proof HwQ as HwQ'. unfold state_wf in HwQ'. apply andb_prop in HwQ' as [HwQ' _]. apply andb_prop in HwQ' as [HwQ' HfQ].
  apply andb_prop in HwQ' as [HrQ HgQ]. rewrite forallb_forall in HgQ, HfQ.
  pose proof HwL as HwL'. unfold state_wf in HwL'. apply andb_prop in HwL' as [HwL' _]. apply andb_prop in HwL' as [HwL' HfL].
  apply andb_prop in HwL' as [HrL HgL]. rewrite forallb_forall in HgL, HfL.
  (* [comment removed for export] *)
  assert (Hkv : forall j, (1 <= j <= 31)%nat -> existsb (Pos.eqb (Pos.of_succ_nat j)) keep = true ->
            lden Eq (rget (s_regs Q) (Pos.of_succ_nat j)) = lden E (rget (s_regs L) (Pos.of_succ_nat j))).
  { intros j Hj Hk. apply existsb_exists in Hk as (key & Hkey & Hke). apply Pos.eqb_eq in Hke. subst key.
    pose proof (Hkeq _ Hkey) as He. apply lin_eqb_eq in He. rewrite He.
    rewrite <- (lden_agree n0 (ecomp E σc) Eq _ (regs_wf_n_spec _ _ _ HrP j Hj) Hag).
    rewrite <- lden_lsubst. unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _].
    apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hre].
    rewrite <- (regs_ent_n_spec _ _ _ _ Hre j Hj). reflexivity. }
  (* [comment removed for export] *)
  assert (Hrs : isteps segs ms' (@mkst (mkFP (ms_fregs ms') (ms_fcsr ms')) (ms_regs ms') (Z_to_bv 64 ret) (ms_mem ms') (ms_rom ms'))).
  { rewrite (sden_mkst segs Eq (with_pc Q ret) ms' HdQ HQr') at 1. cbn [with_pc s_pc]. apply ist_refl. }
  set (ms'' := @mkst (mkFP (ms_fregs ms') (ms_fcsr ms')) (ms_regs ms') (Z_to_bv 64 ret) (ms_mem ms') (ms_rom ms')) in Hrs.
  (* [comment removed for export] *)
  set (E'' := fun x : positive => if Pos.ltb x nL then E x else if Pos.ltb x nx then Eq (x + n0 - nL)%positive
                                 else if Pos.ltb x (nx + 32) then getr (ms_regs ms') (Z_to_bv 5 (Zpos x - Zpos nx)) else E x).
  assert (HaL : agree nL E E'').
  { intros x Hx. unfold E''. rewrite (proj2 (Pos.ltb_lt x nL) Hx). reflexivity. }
  assert (HaQ : forall y, (y < nQ)%positive -> ecomp E'' σ' y = Eq y).
  { intros y Hy. unfold ecomp. unfold σ'. rewrite sigq_get by exact Hy. destruct (Pos.ltb y n0) eqn:Hy0.
    - apply Pos.ltb_lt in Hy0. rewrite <- (lden_agree nL E E'' _ (Hlw y (in_vars_below _ _ Hy0)) HaL). exact (Hag y Hy0).
    - apply Pos.ltb_ge in Hy0. rewrite lden_lvar. unfold E''.
      rewrite (proj2 (Pos.ltb_ge (nL + y - n0) nL)) by lia. rewrite (proj2 (Pos.ltb_lt (nL + y - n0) nx)) by (unfold nx; lia).
      f_equal. lia. }
  assert (HaQ' : agree nQ Eq (ecomp E'' σ')) by (intros y Hy; symmetry; exact (HaQ y Hy)).
  (* [comment removed for export] *)
  destruct (views_nth _ _ _ Hv) as [HlV Hvw].
  unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _].
  apply andb_prop in Hent as [Hent Hrge]. cbn [s_rgs with_rgs Lw] in Hrge.
  destruct (rgs_ent_nth _ _ _ Hrge) as [HlW Hwk].
  assert (Hbs0 : forall k R, nth_error (s_rgs P0) k = Some R -> lden (ecomp E σc) (rg_base R) = lden Eq (rg_base R) /\ rsz (ecomp E σc) R = rsz Eq R).
  { intros k R Hk. pose proof (HgP R (nth_error_In _ _ Hk)) as HR. unfold rwf in HR. apply andb_prop in HR as [HR _]. apply andb_prop in HR as [Hb Hs].
    split; [exact (lden_agree n0 _ _ _ Hb Hag) | unfold rsz; rewrite (lden_agree n0 _ _ _ Hs Hag); reflexivity]. }
  assert (HPW : forall k P, nth_error (s_rgs P0) k = Some P -> exists W v R, nth_error rgs_w k = Some W /\ nth_error vs k = Some v /\
             nth_error (s_rgs L) (vop_src v) = Some R /\ rg_ent W P σc = true /\
             bv_unsigned (lden (ecomp E σc) (rg_base P)) = bv_unsigned (lden E (rg_base W)) /\ rsz (ecomp E σc) P = rsz E W /\
             bv_unsigned (lden E (rg_base R)) <= bv_unsigned (lden E (rg_base W)) /\
             bv_unsigned (lden E (rg_base W)) + rsz E W <= bv_unsigned (lden E (rg_base R)) + rsz E R /\
             ((exists o, v = VSub (vop_src v) o /\ 0 <= o /\ bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o /\
                         o + rsz E W <= rsz E R /\ rsz E W = csz W /\ rg_sub_ok R W o = true) \/
              (v = VCopy (vop_src v) /\ rg_base W = rg_base R /\ rg_size W = rg_size R /\ rg_kind W = rg_kind R))).
  { intros k P Hk. destruct (nth_error rgs_w k) as [W|] eqn:HW; [|apply nth_error_None in HW; pose proof (nth_error_Some (s_rgs P0) k) as X; rewrite Hk in X; specialize (proj1 X ltac:(discriminate)); lia].
    destruct (nth_error vs k) as [v|] eqn:Hvk; [|apply nth_error_None in Hvk; pose proof (nth_error_Some rgs_w k) as X; rewrite HW in X; specialize (proj1 X ltac:(discriminate)); lia].
    pose proof (Hvw k W v HW Hvk) as Hv1. destruct (view1_sound segs E (ms_mem ms) (s_rgs L) W v F1 Hv1) as (R & HR & _ & Hs1).
    pose proof (Hwk k W P HW Hk) as He. destruct (rg_ent_parts _ _ _ He) as (Eb & Ez & _ & _ & _).
    exists W, v, R. split; [first [exact HW | reflexivity]|]. split; [first [exact Hvk | reflexivity]|]. split; [exact HR|]. split; [exact He|].
    split; [rewrite <- lden_lsubst, <- Eb; reflexivity|]. split; [unfold rsz; rewrite <- lden_lsubst, <- Ez; reflexivity|].
    destruct Hs1 as [(o & Eo & Ho & HA & Hn & Hq)|(Eo & Eb' & Ez' & Ek)].
    - split; [lia|]. split; [lia|]. left. exists o. refine (conj Eo (conj Ho (conj HA (conj Hn (conj Hq _))))).
      rewrite Eo in Hv1. cbn [view1_ok vop_src] in Hv1. rewrite HR in Hv1. exact Hv1.
    - split; [rewrite Eb'; lia|]. split; [unfold rsz; rewrite Eb', Ez'; lia|]. right. exact (conj Eo (conj Eb' (conj Ez' Ek))). }
  (* [comment removed for export] *)
  assert (Hsrc : forall i R x k P, nth_error (s_rgs L) i = Some R -> FxStep.in_rg E R x -> nth_error (s_rgs P0) k = Some P ->
             FxStep.in_rg (ecomp E σc) P x -> exists W v, nth_error rgs_w k = Some W /\ nth_error vs k = Some v /\ vop_src v = i).
  { intros i R x k P HR Hx Hk Hxp. destruct (HPW k P Hk) as (W & v & R' & HW & Hvk & HR' & _ & HbP & HzP & Hlo & Hhi & _).
    exists W, v. split; [exact HW|]. split; [exact Hvk|].
    destruct (Nat.eq_dec (vop_src v) i) as [Heq|Hne]; [exact Heq|]. exfalso.
    pose proof (rgs_disj_nth E (s_rgs L) _ _ R' R G1 Hne HR' HR) as Hd12. unfold rg_disj, FxStep.in_rg in *. lia. }
  (* [comment removed for export] *)
  assert (Hunch : forall x, (forall k P, nth_error (s_rgs P0) k = Some P -> wkind (rg_kind P) = true -> ~ FxStep.in_rg (ecomp E σc) P x) ->
             ms_mem ms' x = ms_mem ms x).
  { intros x Hno. exact (cs_unchanged segs (ecomp E σc) Eq (s_rgs P0) (s_rgs Q) (ms_mem ms) (ms_mem ms') x F0 FQ Hsh Hlen Hkd Hbs0 Hfr Hno). }
  (* [comment removed for export] *)
  assert (HwR : forall i R, nth_error (s_rgs L) i = Some R -> rwf nL R = true) by (intros i R Hi; exact (HgL R (nth_error_In _ _ Hi))).
  (* [comment removed for export] *)
  assert (keep_out_ok : forall i R k0 ks pk v, nth_error (s_rgs L) i = Some R -> rg_ok segs E (ms_mem ms) R -> rg_ok segs E'' (ms_mem ms) R ->
            lden E (rg_base R) = lden E'' (rg_base R) -> rsz E R = rsz E'' R -> wviews (s_rgs P0) vs 0 i = k0 :: ks ->
            tget pk (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R)) = Some v ->
            Zpos pk - 1 < rsz E'' R /\ rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + (Zpos pk - 1))) = Some (bden E'' v)).
  { intros i R k0 ks pk v HR HRok HRok'' HbR HzR Hwv Hkeep.
    unfold keep_out in Hkeep. rewrite tget_tfilter in Hkeep.
    destruct (out_wins σc (s_rgs P0) vs (k0 :: ks) (Zpos pk - 1)) eqn:Hout; [|discriminate].
    pose proof HRok'' as X. unfold rg_ok in X. cbv zeta in X. destruct X as (_ & _ & _ & X4).
    destruct (X4 pk v Hkeep) as [Hp1 Hp2]. split; [exact Hp1|].
    set (j := Zpos pk - 1) in *.
    set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) in *.
    assert (Hj : 0 <= j < rsz E R) by (unfold j; rewrite HzR; lia).
    assert (Hxr : FxStep.in_rg E R x).
    { pose proof (rg_in_off E _ R j HRok Hj) as Y. unfold x. rewrite <- HbR. exact Y. }
    assert (Hm : ms_mem ms' x = ms_mem ms x).
    { apply Hunch. intros k P Hk Hwp Hxp.
      destruct (Hsrc i R x k P HR Hxr Hk Hxp) as (W & v0 & HW & Hvk & Hs).
      pose proof (wviews_in (s_rgs P0) vs 0 i k P v0 Hk Hvk Hwp Hs) as Hko. rewrite Hwv in Hko. cbn [Nat.add] in Hko.
      unfold out_wins in Hout. rewrite forallb_forall in Hout. pose proof (Hout _ Hko) as Ho. cbv beta iota in Ho.
      unfold view_win in Ho. rewrite Hvk, Hk in Ho. destruct v0 as [i0|i0 o0]; [discriminate|].
      destruct (is_const (lsubst σc (rg_size P))) as [nc|] eqn:Hnc; [|discriminate].
      destruct (HPW k P Hk) as (W' & v' & R' & HW' & Hv' & HR' & _ & HbP & HzP & _ & _ & Hcase).
      rewrite HW in HW'. injection HW' as <-. rewrite Hvk in Hv'. injection Hv' as <-. rewrite Hs in HR'. rewrite HR in HR'. injection HR' as <-.
      destruct Hcase as [(o1 & Eo1 & _ & HA & _ & _ & _)|(Eo1 & _)]; [|discriminate Eo1].
      cbn [vop_src] in Eo1. injection Eo1 as Eo2. rewrite <- Eo2 in HA.
      pose proof (is_const_u E (lsubst σc (rg_size P)) nc Hnc) as Hzn. rewrite lden_lsubst in Hzn.
      unfold FxStep.in_rg in Hxp. unfold rsz in Hxp. rewrite Hzn in Hxp. rewrite HbP, HA in Hxp.
      assert (Hxu : bv_unsigned x = bv_unsigned (lden E (rg_base R)) + j).
      { unfold x. rewrite <- HbR. rewrite u_small64; [reflexivity|]. pose proof HRok as Y. unfold rg_ok in Y. cbv zeta in Y. destruct Y as (Y1 & Y2 & _).
        pose proof (u_range E (rg_base R)) as Y3. unfold two64 in *. lia. }
      rewrite Hxu in Hxp. apply Bool.orb_true_iff in Ho as [Ho|Ho]; [apply Z.ltb_lt in Ho | apply Z.leb_le in Ho]; lia. }
    unfold rd1 in Hp2 |- *. fold x in Hp2 |- *. rewrite Hm. exact Hp2. }
  assert (HRK : Forall (rg_ok segs E'' (ms_mem ms')) (map_i (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs) 0 (s_rgs L))).
  { apply Forall_nth'. intros i RK Hi. destruct (nth_map_i' _ _ _ _ Hi) as (R & HR & ->).
    rewrite Forall_nth' in F1. pose proof (F1 i R HR) as HRok.
    pose proof (rg_ok_agree segs nL E E'' (ms_mem ms) R (HwR i R HR) HaL HRok) as HRok''.
    assert (HbR : lden E (rg_base R) = lden E'' (rg_base R)).
    { pose proof (HwR i R HR) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. exact (lden_agree nL _ _ _ X HaL). }
    assert (HzR : rsz E R = rsz E'' R).
    { pose proof (HwR i R HR) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. unfold rsz. rewrite (lden_agree nL _ _ _ X HaL). reflexivity. }
    unfold new_rg. destruct (wviews (s_rgs P0) vs 0 i) as [|k0 ks] eqn:Hwv.
    - (* [comment removed for export] *)
      apply (rg_ok_mem segs E'' (ms_mem ms) (ms_mem ms') R HRok''). intros j Hj. apply Hunch. intros k P Hk Hwkp Hxp.
      rewrite <- HbR in Hxp. rewrite <- HzR in Hj.
      assert (Hxr : FxStep.in_rg E R (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + j))).
      { pose proof HRok as X. unfold rg_ok in X. cbv zeta in X. destruct X as (X1 & X2 & _). pose proof (u_range E (rg_base R)) as X3.
        unfold FxStep.in_rg. rewrite u_small64 by (unfold two64 in *; lia). lia. }
      destruct (Hsrc i R _ k P HR Hxr Hk Hxp) as (W & v & HW & Hvk & Hs).
      exact (wviews_nil _ _ _ _ Hwv k P v Hk Hvk Hwkp Hs).
    - (* [comment removed for export] *)
      destruct (wviews_spec (s_rgs P0) vs 0 i (fst k0) (snd k0) ltac:(rewrite Hwv; left; destruct k0; reflexivity))
        as (Pk & vk & HPk & Hvk & _ & HwPk & Hsk & _). rewrite Nat.sub_0_r in HPk, Hvk.
      (* [comment removed for export] *)
      assert (HwkR : wkind (rg_kind R) = true).
      { destruct (HPW _ Pk HPk) as (W & v & R' & HW & Hv' & HR' & He & _ & _ & _ & _ & Hcase).
        rewrite Hvk in Hv'. injection Hv' as <-. rewrite Hsk in HR'. rewrite HR in HR'. injection HR' as <-.
        destruct (rg_ent_parts _ _ _ He) as (_ & _ & Hkle & _ & _). pose proof (rkind_le_w _ _ Hkle HwPk) as HwWk.
        destruct Hcase as [(o & _ & _ & _ & _ & _ & Hsub)|(_ & _ & _ & Ek)].
        - exact (rg_sub_kind R W o Hsub HwWk).
        - rewrite <- Ek. exact HwWk. }
      (* [comment removed for export] *)
      assert (HRW : forall j, 0 <= j < rsz E'' R ->
                rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) <> None /\
                wview segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)) <> None).
      { intros j Hj. set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)).
        assert (Hxr : FxStep.in_rg E R x).
        { pose proof (rg_in_off E _ R j HRok ltac:(rewrite HzR; exact Hj)) as X. unfold x. rewrite <- HbR. exact X. }
        destruct (Exists_dec (fun P => wkind (rg_kind P) = true /\ FxStep.in_rg (ecomp E σc) P x) (s_rgs P0)) as [Hin|Hout].
        { intros P. destruct (wkind (rg_kind P)) eqn:Hwp; [|right; intros [X _]; discriminate].
          destruct (in_rg_dec (ecomp E σc) P x) as [X|X]; [left; split; [reflexivity | exact X] | right; intros [_ Y]; exact (X Y)]. }
        * apply Exists_exists in Hin as (P & HP & HwP0 & Hxp). apply In_nth_error in HP as (k & Hk).
          destruct (shape_nth _ _ Hsh k P Hk) as (RQ & HQk & EbQ & EzQ).
          rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ.
          destruct (Hbs0 k P Hk) as [Hb0 Hz0].
          assert (HxQ : FxStep.in_rg Eq RQ x).
          { apply (in_rg_transfer (ecomp E σc) Eq P RQ x); [rewrite Hb0, EbQ; reflexivity | unfold rsz; rewrite EzQ; exact Hz0 | exact Hxp]. }
          exact (rg_at_w Eq _ RQ x HRQ HxQ (kinds_nth _ _ Hkd k P RQ Hk HQk HwP0)).
        * assert (Hm : ms_mem ms' x = ms_mem ms x).
          { apply Hunch. intros k P Hk Hw' Hxp. apply Hout. apply Exists_exists. exists P. split; [exact (nth_error_In _ _ Hk) | split; assumption]. }
          destruct (rg_at_w E _ R x HRok Hxr HwkR) as [Y1 Y2]. unfold rd1, wview in Y1, Y2 |- *. rewrite Hm. split; assumption. }
      (* [comment removed for export] *)
      assert (HIMP : forall pk v, tget pk (imp_cont (s_rgs Q) σ' (k0 :: ks) (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R))) = Some v ->
                Zpos pk - 1 < rsz E'' R /\ rd1 segs (ms_mem ms') (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + (Zpos pk - 1))) = Some (bden E'' v)).
      { intros pk v Hpk. destruct (in_imp_cont _ _ _ _ _ _ Hpk) as [(k & o & RQ & q & w & Hko & HQk & Hqw & Ep & Ev)|Hkeep];
          [|exact (keep_out_ok i R k0 ks pk v HR HRok HRok'' HbR HzR Hwv Hkeep)].
        rewrite <- Hwv in Hko.
        destruct (wviews_spec (s_rgs P0) vs 0 i k o Hko) as (P & v' & HP & Hv' & _ & HwP0 & Hs' & Eo). rewrite Nat.sub_0_r in HP, Hv'.
        destruct (HPW k P HP) as (W & v'' & R' & HW & Hv'' & HR' & _ & HbP & HzP & Hlo & Hhi & Hcase).
        rewrite Hv' in Hv''. injection Hv'' as <-. rewrite Hs' in HR'. rewrite HR in HR'. injection HR' as <-.
        destruct (shape_nth _ _ Hsh k P HP) as (RQ' & HQk' & EbQ & EzQ). rewrite HQk in HQk'. injection HQk' as <-.
        rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ. unfold rg_ok in HRQ. cbv zeta in HRQ. destruct HRQ as (_ & _ & _ & HQ4).
        destruct (HQ4 q w Hqw) as [Hq1 Hq2].
        destruct (Hbs0 k P HP) as [Hb0 Hz0].
        assert (Hoff : 0 <= o /\ bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o /\ o + rsz E W <= rsz E R).
        { destruct Hcase as [(o' & Eo' & Ho' & HA & Hn' & _)|(Eo' & Eb' & Ez' & _)].
          - rewrite Eo' in Eo. cbn in Eo. subst o. clear - Ho' HA Hn'. lia.
          - rewrite Eo' in Eo. cbn in Eo. subst o. rewrite Eb'. unfold rsz. rewrite Ez'. clear. lia. }
        destruct Hoff as (Ho0 & HbW & HzW).
        assert (HbQ : bv_unsigned (lden Eq (rg_base RQ)) = bv_unsigned (lden E (rg_base R)) + o) by (rewrite EbQ, <- Hb0, HbP; exact HbW).
        assert (HzQ : rsz Eq RQ = rsz E W) by (unfold rsz; rewrite EzQ; fold (rsz Eq P); rewrite <- Hz0; exact HzP).
        assert (Hp1 : Zpos pk - 1 = o + (Zpos q - 1)) by (rewrite Ep; unfold okey; rewrite Z2Pos.id by (clear - Ho0; lia); clear; lia).
        rewrite Hp1. split; [rewrite <- HzR; clear - Hq1 HzQ HzW; lia|].
        rewrite <- HbR. rewrite Z.add_assoc. rewrite <- HbQ. rewrite Hq2. rewrite Ev. f_equal.
        rewrite bden_bsubst. apply (bden_agree nQ Eq (ecomp E'' σ') w); [|exact HaQ'].
        pose proof (HgQ RQ (nth_error_In _ _ HQk)) as X. unfold rwf in X. apply andb_prop in X as [_ X].
        exact (tforall_spec _ _ X q w Hqw). }
      unfold rg_ok. cbv zeta. rewrite rsz_RG_eq. cbn [rg_base rg_kind rg_cont].
      pose proof HRok'' as HRok3. unfold rg_ok in HRok3. cbv zeta in HRok3. destruct HRok3 as (H1 & H2 & _ & _).
      refine (conj H1 (conj H2 (conj _ HIMP))).
      destruct (rz_keep (s_rgs Q) R (k0 :: ks)) eqn:Hrz; [|exact HRW].
      (* [comment removed for export] *)
      intros j Hj. split; [exact (HRW j Hj)|]. intros Hnone.
      set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + j)).
      assert (Hxr : FxStep.in_rg E R x).
      { pose proof (rg_in_off E _ R j HRok ltac:(rewrite HzR; exact Hj)) as X. unfold x. rewrite <- HbR. exact X. }
      unfold rz_keep in Hrz. apply andb_prop in Hrz as [Hrz Hzv]. apply andb_prop in Hrz as [HkR Hc0].
      rewrite forallb_forall in Hzv.
      destruct (Exists_dec (fun P => wkind (rg_kind P) = true /\ FxStep.in_rg (ecomp E σc) P x) (s_rgs P0)) as [Hin|Hout].
      { intros P. destruct (wkind (rg_kind P)) eqn:Hwp; [|right; intros [X _]; discriminate].
        destruct (in_rg_dec (ecomp E σc) P x) as [X|X]; [left; split; [reflexivity | exact X] | right; intros [_ Y]; exact (X Y)]. }
      + apply Exists_exists in Hin as (P & HP & HwP0 & Hxp). apply In_nth_error in HP as (k & Hk).
        destruct (Hsrc i R x k P HR Hxr Hk Hxp) as (W & v & HW & Hvk' & Hs).
        pose proof (wviews_in (s_rgs P0) vs 0 i k P v Hk Hvk' HwP0 Hs) as Hko. rewrite Hwv in Hko. cbn [Nat.add] in Hko.
        destruct (shape_nth _ _ Hsh k P Hk) as (RQ & HQk & EbQ & EzQ).
        pose proof (Hzv _ Hko) as HzQ. cbv beta iota in HzQ. rewrite HQk in HzQ.
        rewrite Forall_nth' in FQ. pose proof (FQ k RQ HQk) as HRQ.
        destruct (Hbs0 k P Hk) as [Hb0 Hz0].
        destruct (HPW k P Hk) as (W' & v' & R' & HW' & Hv' & HR' & _ & HbP & HzP & Hlo & Hhi & Hcase).
        rewrite HW in HW'. injection HW' as <-. rewrite Hvk' in Hv'. injection Hv' as <-. rewrite Hs in HR'. rewrite HR in HR'. injection HR' as <-.
        set (o := match v with VCopy _ => 0 | VSub _ o' => o' end) in *.
        assert (HbW : bv_unsigned (lden E (rg_base W)) = bv_unsigned (lden E (rg_base R)) + o).
        { unfold o. destruct Hcase as [(o' & Eo' & _ & HA & _)|(Eo' & Eb' & _ & _)]; rewrite Eo'; [exact HA | rewrite Eb'; lia]. }
        assert (HbQ : bv_unsigned (lden Eq (rg_base RQ)) = bv_unsigned (lden E (rg_base R)) + o) by (rewrite EbQ, <- Hb0, HbP; exact HbW).
        assert (HxQ : FxStep.in_rg Eq RQ x).
        { apply (in_rg_transfer (ecomp E σc) Eq P RQ x); [rewrite Hb0, EbQ; reflexivity | unfold rsz; rewrite EzQ; exact Hz0 | exact Hxp]. }
        unfold rg_ok in HRQ. cbv zeta in HRQ. destruct HRQ as (_ & _ & HQ3 & _).
        unfold FxStep.in_rg in HxQ. rewrite HbQ in HxQ.
        assert (Hxu : bv_unsigned x = bv_unsigned (lden E (rg_base R)) + j).
        { unfold x. rewrite <- HbR. rewrite u_small64; [reflexivity|]. pose proof HRok as X. unfold rg_ok in X. cbv zeta in X. destruct X as (X1 & X2 & _).
          pose proof (u_range E (rg_base R)) as X3. rewrite <- HzR in Hj. unfold two64 in *. lia. }
        specialize (HQ3 (j - o) ltac:(rewrite Hxu in HxQ; lia)).
        destruct (rg_kind RQ) eqn:EkQ; try discriminate. destruct HQ3 as [_ HQ3].
        replace (bv_unsigned (lden Eq (rg_base RQ)) + (j - o)) with (bv_unsigned x) in HQ3 by (rewrite HbQ, Hxu; lia).
        rewrite Z_to_bv_bv_unsigned in HQ3. apply HQ3.
        destruct (tget (okey (j - o)) (rg_cont RQ)) as [w|] eqn:Hw; [|reflexivity]. exfalso.
        pose proof (imp_cont_some (s_rgs Q) σ' (k0 :: ks) (keep_out σc (s_rgs P0) vs (k0 :: ks) (rg_cont R)) k o RQ (okey (j - o)) w Hko HQk Hw) as X.
        replace (o + (Zpos (okey (j - o)) - 1)) with j in X by (unfold okey; rewrite Z2Pos.id by lia; lia).
        exact (X Hnone).
      + assert (Hm : ms_mem ms' x = ms_mem ms x).
        { apply Hunch. intros k P Hk Hw' Hxp. apply Hout. apply Exists_exists. exists P. split; [exact (nth_error_In _ _ Hk) | split; assumption]. }
        pose proof HRok'' as X. unfold rg_ok in X. cbv zeta in X. destruct X as (_ & _ & X3 & X4).
        destruct (rg_kind R) eqn:EkR; try discriminate.
        specialize (X3 j Hj). destruct X3 as [_ X3]. unfold rd1 in X3 |- *. fold x in X3 |- *. rewrite Hm.
        destruct (tget (okey j) (rg_cont R)) as [w|] eqn:Hw; [|exact (X3 eq_refl)].
        pose proof (tforall_spec _ _ Hc0 _ _ Hw) as Hw0. cbv beta in Hw0. destruct w as [z|l jj]; [|discriminate]. apply Z.eqb_eq in Hw0. subst z.
        destruct (X4 (okey j) (BK 0) Hw) as [_ X5]. replace (Zpos (okey j) - 1) with j in X5 by (unfold okey; rewrite Z2Pos.id by lia; lia).
        fold x in X5. unfold rd1 in X5. exact X5. }
  (* [comment removed for export] *)
  exists ms'', E''. split; [exact (isteps_trans segs _ _ _ Hst Hrs)|]. split; [|split; [exact HaL| split; [|exact (HΦ ms ms' ms'' eq_refl eq_refl HΦ0)]]].
  - apply sden0_sden; [exact HwK|].
    unfold sden0. cbn [cont_st s_pc s_regs s_rgs s_facts s_resv]. fold nL n0 nQ. fold σ'. fold nx.
    cbn [ms'' mkst ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr fp_csr].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      intros r. destruct (decide (r = 0%bv)) as [->|Hr0].
      - change (rkey 0%bv) with xH. unfold rget. reflexivity.
      - destruct (rkey_succ r Hr0) as (j & Hj & Hkey). rewrite Hkey, regs_cont_get by exact Hj.
        destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) keep) eqn:Hk.
        + rewrite (DQ r). cbn [with_pc s_regs]. rewrite Hkey. rewrite (Hkv j Hj Hk).
          apply (lden_agree nL E E''); [exact (regs_wf_n_spec _ _ _ HrL j Hj) | exact HaL].
        + destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) qk) eqn:Hq.
          * rewrite (DQ r). cbn [with_pc s_regs]. rewrite Hkey. rewrite lden_lsubst.
            apply (lden_agree nQ Eq (ecomp E'' σ')); [exact (regs_wf_n_spec _ _ _ HrQ j Hj) | exact HaQ'].
          * rewrite lden_lvar. unfold E''. rewrite (proj2 (Pos.ltb_ge (nx + Pos.of_nat j) nL)) by (unfold nx; lia).
            rewrite (proj2 (Pos.ltb_ge (nx + Pos.of_nat j) nx)) by lia. rewrite (proj2 (Pos.ltb_lt (nx + Pos.of_nat j) (nx + 32))) by lia.
            f_equal.
            pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 5) with 32 in Rr.
            assert (Hu : bv_unsigned r = Z.of_nat j).
            { apply (f_equal Zpos) in Hkey. unfold rkey, bv_key in Hkey. rewrite Z2Pos.id in Hkey by lia. rewrite Zpos_P_of_succ_nat in Hkey. lia. }
            assert (Ej : Zpos (Pos.of_nat j) = Z.of_nat j) by (rewrite <- positive_nat_Z, Nat2Pos.id by lia; reflexivity).
            apply bv_eq. rewrite Z_to_bv_unsigned, Hu. rewrite Pos2Z.inj_add, Ej.
            replace (Zpos nx + Z.of_nat j - Zpos nx) with (Z.of_nat j) by lia. symmetry. apply bv_wrap_small. unfold bv_modulus. lia. }
    split; [exact HRK|].
    split.
    { (* [comment removed for export] *)
      apply rgs_disj_nth_inv. intros k k' R1 R2 Hkk H1 H2.
      destruct (nth_map_i' _ _ _ _ H1) as (S1 & HS1 & ->). destruct (nth_map_i' _ _ _ _ H2) as (S2 & HS2 & ->).
      pose proof (rgs_disj_nth E (s_rgs L) k k' S1 S2 G1 ltac:(lia) HS1 HS2) as Hd12.
      assert (Hbz : forall i S, nth_error (s_rgs L) i = Some S -> bv_unsigned (lden E'' (rg_base (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs i S))) = bv_unsigned (lden E (rg_base S)) /\
                 rsz E'' (new_rg (s_rgs Q) (s_rgs P0) σc σ' vs i S) = rsz E S).
      { intros i S HS. pose proof (HwR i S HS) as X. unfold rwf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [Xb Xs].
        unfold new_rg. destruct (wviews (s_rgs P0) vs 0 i); cbn [rg_base]; unfold rsz; cbn [rg_size];
          rewrite (lden_agree nL E E'' _ Xb HaL), (lden_agree nL E E'' _ Xs HaL); split; reflexivity. }
      destruct (Hbz k S1 HS1) as [B1' Z1']. destruct (Hbz k' S2 HS2) as [B2' Z2']. unfold rg_disj in *. rewrite B1', Z1', B2', Z2'. exact Hd12. }
    split.
    { (* [comment removed for export] *)
      apply Forall_app. split.
      - rewrite Forall_forall in I1 |- *. intros f Hf. exact (fact_ok_agree nL E E'' f (HfL f Hf) HaL (I1 f Hf)).
      - apply Forall_map. rewrite Forall_forall in IQ |- *. intros f Hf. apply (proj2 (fact_ok_fsubst E'' σ' f)).
        exact (fact_ok_agree nQ Eq (ecomp E'' σ') f (HfQ f Hf) HaQ' (IQ f Hf)). }
    exact JQ.
  - (* [comment removed for export] *)
    intros x Hx. cbn [ms'' mkst ms_mem]. apply Hunch. intros k P Hk HwP0 Hxp.
    destruct (HPW k P Hk) as (W & v & R' & HW & Hvk & HR' & He & HbP & HzP & Hlo & Hhi & Hcase).
    assert (HxW : FxStep.in_rg E R' x) by (unfold FxStep.in_rg in *; rewrite HbP, HzP in Hxp; lia).
    destruct (rg_ent_parts _ _ _ He) as (_ & _ & Hkle & _ & _). pose proof (rkind_le_w _ _ Hkle HwP0) as HwW0.
    assert (HwR' : wkind (rg_kind R') = true).
    { destruct Hcase as [(o & _ & _ & _ & _ & _ & Hsub)|(_ & _ & _ & Ek)]; [exact (rg_sub_kind R' W o Hsub HwW0) | rewrite <- Ek; exact HwW0]. }
    destruct Hx as [Hout|Hrt].
    + unfold FxStep.outside in Hout. rewrite Forall_forall in Hout. pose proof (Hout R' (nth_error_In _ _ HR')) as X.
      unfold FxStep.in_rg in HxW. lia.
    + apply Exists_exists in Hrt as (R2 & HR2 & Hrt2 & Hx2). apply In_nth_error in HR2 as (i2 & Hi2).
      destruct (Nat.eq_dec i2 (vop_src v)) as [Heq|Hne].
      * rewrite Heq in Hi2. rewrite HR' in Hi2. injection Hi2 as <-. destruct (rg_kind R'); cbn in Hrt2, HwR'; discriminate.
      * pose proof (rgs_disj_nth E (s_rgs L) _ _ R2 R' G1 Hne Hi2 HR') as Hd12. unfold rg_disj, FxStep.in_rg in *. lia.
Qed.
#[using="Type"] Theorem frag_sound_k : forall P0 Q keep qk vs rgs_w ret L K E ms,
  kfrag_ok P0 Q ret -> frag_cont L P0 Q keep qk vs rgs_w ret = Some K -> sden segs E L ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next L) E E'' /\
    (forall x, fr_pt E (s_rgs L) x -> ms_mem ms'' x = ms_mem ms x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P0 Q keep qk vs rgs_w ret L K E ms Hfn Hcc Hd.
  destruct (frag_sound_kP (fun _ _ => True) fp_inv_true P0 Q keep qk vs rgs_w ret L K E ms (kfrag_ok_P P0 Q ret Hfn) Hcc Hd)
    as (ms'' & E'' & H1 & H2 & H3 & H4 & _).
  exists ms'', E''. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.
End Call4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record csite : Type := CSite { cs_p0 : sst; cs_q : sst; cs_keep : list positive; cs_qk : list positive; cs_vs : list vop;
                               cs_w : sst -> list region }.

(* [comment removed for export] *)
Inductive cplan : Type := CPlan (p : plan) (calls : list (Z * csite * cplan)).

Definition ret_of (L : sst) : Z := match is_const (rget (s_regs L) ra_key) with Some c => c | None => -1 end.

Fixpoint find_site (calls : list (Z * csite * cplan)) (pc : Z) : option (csite * cplan) :=
  match calls with [] => None | (a, c, k) :: cs => if Z.eqb a pc then Some (c, k) else find_site cs pc end.

Fixpoint sites_list (cp : cplan) : list (sst * sst) :=
  match cp with
  | CPlan _ calls => (fix go (cs : list (Z * csite * cplan)) : list (sst * sst) :=
                        match cs with [] => [] | (_, c, k) :: cs' => (cs_p0 c, cs_q c) :: sites_list k ++ go cs' end) calls
  end.

Section CCheck.
Variable t : tree xi.
Variable img : tree Z.
Variable ins : list positive.
Variable depth : nat.

Fixpoint call_all (chk : cplan -> sst -> option (list sst)) (calls : list (Z * csite * cplan)) (ls : list sst) : option (list sst) :=
  match ls with
  | [] => Some []
  | L :: ls' =>
      match call_all chk calls ls' with
      | None => None
      | Some fs =>
          match find_site calls (s_pc L) with
          | None => Some (L :: fs)
          | Some (c, k) =>
              match call_cont L (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c L) (ret_of L) with
              | None => None
              | Some K => if bases_wf (s_next K) (s_rgs K) then
                            match chk k K with Some f1 => Some (f1 ++ fs) | None => None end
                          else None
              end
          end
      end
  end.

Fixpoint ccheck (d : nat) (cp : cplan) (s : sst) : option (list sst) :=
  match d with
  | O => None
  | S d' => match cp with CPlan p calls => match check t img ins depth p s with Some ls => call_all (ccheck d') calls ls | None => None end end
  end.
End CCheck.

Section CSound.
Variable segs : list Segment.

#[using="Type"] Lemma find_site_sound : forall calls pc c k, find_site calls pc = Some (c, k) -> In (pc, c, k) calls.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction calls as [|[[a c0] k0] cs IH]; intros pc c k H; cbn [find_site] in H; [discriminate|].
  destruct (Z.eqb a pc) eqn:E; [injection H as <- <-; apply Z.eqb_eq in E; subst; left; reflexivity | right; exact (IH pc c k H)].
Qed.

#[using="Type"] Lemma sites_list_in : forall p calls pc c k, In (pc, c, k) calls ->
  In (cs_p0 c, cs_q c) (sites_list (CPlan p calls)) /\ (forall x, In x (sites_list k) -> In x (sites_list (CPlan p calls))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p calls. induction calls as [|[[a c0] k0] cs IH]; intros pc c k H; [destruct H|]. cbn [sites_list].
  destruct H as [E|H].
  - injection E as -> <- <-. split; [left; reflexivity|]. intros x Hx. right. apply in_or_app. left. exact Hx.
  - destruct (IH pc c k H) as [H1 H2]. cbn [sites_list] in H1, H2.
    split; [right; apply in_or_app; right; exact H1|]. intros x Hx. right. apply in_or_app. right. exact (H2 x Hx).
Qed.

#[using="Type"] Lemma call_all_sound : forall chk calls ls fs, call_all chk calls ls = Some fs -> forall L, In L ls ->
  (find_site calls (s_pc L) = None /\ In L fs) \/
  (exists c k K f1, find_site calls (s_pc L) = Some (c, k) /\
     call_cont L (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c L) (ret_of L) = Some K /\
     bases_wf (s_next K) (s_rgs K) = true /\ chk k K = Some f1 /\ (forall x, In x f1 -> In x fs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros chk calls. induction ls as [|L0 ls IH]; intros fs H L HL; [destruct HL|]. cbn [call_all] in H.
  destruct (call_all chk calls ls) as [fs0|] eqn:H0; [|discriminate].
  assert (Hsub : forall x, In x fs0 -> In x fs).
  { intros x Hx. destruct (find_site calls (s_pc L0)) as [[c k]|].
    - destruct (call_cont _ _ _ _ _ _ _ _) as [K|]; [|discriminate]. destruct (bases_wf (s_next K) (s_rgs K)); [|discriminate].
      destruct (chk k K) as [f1|]; [|discriminate]. injection H as <-. apply in_or_app. right. exact Hx.
    - injection H as <-. right. exact Hx. }
  destruct HL as [->|HL].
  - destruct (find_site calls (s_pc L)) as [[c k]|] eqn:Hf.
    + destruct (call_cont _ _ _ _ _ _ _ _) as [K|] eqn:Hc; [|discriminate].
      destruct (bases_wf (s_next K) (s_rgs K)) eqn:Hb; [|discriminate].
      destruct (chk k K) as [f1|] eqn:Hk; [|discriminate]. injection H as <-.
      right. exists c, k, K, f1. refine (conj eq_refl (conj Hc (conj Hb (conj Hk _)))). intros x Hx. apply in_or_app. left. exact Hx.
    + injection H as <-. left. split; [reflexivity | left; reflexivity].
  - destruct (IH fs0 ltac:(first [exact H0 | reflexivity]) L HL) as [(Hn & Hin)|(c & k & K & f1 & Hf & Hc & Hb & Hk & Hs)].
    + left. split; [exact Hn | exact (Hsub L Hin)].
    + right. exists c, k, K, f1. refine (conj Hf (conj Hc (conj Hb (conj Hk _)))). intros x Hx. exact (Hsub x (Hs x Hx)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma new_rg_shape : forall Qs P0s σc σ' vs i R, rg_base (new_rg Qs P0s σc σ' vs i R) = rg_base R /\ rg_size (new_rg Qs P0s σc σ' vs i R) = rg_size R.
Proof. LiaFast.lf_pins LiaFast.u0. intros Qs P0s σc σ' vs i R. unfold new_rg. destruct (wviews P0s vs 0 i); split; reflexivity. Qed.

#[using="Type"] Lemma shape_map_new_rg : forall Qs P0s σc σ' vs l i, shape (map_i (new_rg Qs P0s σc σ' vs) i l) = shape l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Qs P0s σc σ' vs l. induction l as [|R l IH]; intros i; cbn [map_i shape List.map]; [reflexivity|].
  destruct (new_rg_shape Qs P0s σc σ' vs i R) as [Hb Hs]. rewrite Hb, Hs. f_equal. exact (IH (S i)).
Qed.

#[using="Type"] Lemma call_cont_shape : forall L P0 Q keep qk vs rgs_w ret K, call_cont L P0 Q keep qk vs rgs_w ret = Some K ->
  shape (s_rgs K) = shape (s_rgs L) /\ (s_next L < s_next K)%positive /\ rtm (s_rgs K) = rtm (s_rgs L).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L P0 Q keep qk vs rgs_w ret K H. unfold call_cont in H. destruct (call_ok L P0 Q keep qk vs rgs_w ret) eqn:Hok; [|discriminate].
  injection H as <-. cbn [cont_st s_rgs s_next].
  unfold call_ok in Hok. cbv zeta in Hok.
  repeat match type of Hok with (?a && ?b)%bool = true => apply andb_prop in Hok as [Hok ?] end.
  split; [apply shape_map_new_rg|].
  split; [match goal with Hq : Pos.leb (s_next P0) (s_next Q) = true |- _ => apply Pos.leb_le in Hq; lia end|].
  (* [comment removed for export] *)
  set (Lw := with_rgs L rgs_w) in *. set (σc := mcall Lw P0) in *.
  match goal with Hv : views_ok _ _ _ = true |- _ => destruct (views_nth _ _ _ Hv) as [HlV Hvw] end.
  match goal with He : entails _ _ _ = true |- _ => pose proof He as Hent end.
  unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _].
  apply andb_prop in Hent as [Hent Hrge]. cbn [s_rgs with_rgs Lw] in Hrge. destruct (rgs_ent_nth _ _ _ Hrge) as [HlW Hwk].
  unfold rtm. set (f := new_rg (s_rgs Q) (s_rgs P0) σc (sigq σc (s_next P0) (s_next Q) (s_next L)) vs).
  assert (G : forall i l, (forall j R, nth_error l j = Some R -> nth_error (s_rgs L) (i + j) = Some R) ->
             List.map (fun R => is_rt (rg_kind R)) (map_i f i l) = List.map (fun R => is_rt (rg_kind R)) l).
  { intros i l. revert i. induction l as [|R l IH]; intros i Hl; cbn [map_i List.map]; [reflexivity|]. f_equal.
    - unfold f, new_rg. destruct (wviews (s_rgs P0) vs 0 i) as [|[k o] ks] eqn:Hwv; [reflexivity|].
      destruct (wviews_spec (s_rgs P0) vs 0 i k o ltac:(rewrite Hwv; left; reflexivity)) as (P & v & HP & Hv & _ & HwP & Hs & _).
      rewrite Nat.sub_0_r in HP, Hv.
      destruct (nth_error rgs_w k) as [W|] eqn:HW; [|apply nth_error_None in HW; pose proof (nth_error_Some (s_rgs P0) k) as X; rewrite HP in X; specialize (proj1 X ltac:(discriminate)); lia].
      pose proof (Hvw k W v HW Hv) as Hv1. destruct (rg_ent_parts _ _ _ (Hwk k W P HW HP)) as (_ & _ & Hkle & _ & _).
      pose proof (rkind_le_w _ _ Hkle HwP) as HwW. pose proof (Hl 0%nat R eq_refl) as HR. rewrite Nat.add_0_r in HR.
      assert (HwR : wkind (rg_kind R) = true).
      { destruct v as [j|j o']; cbn [view1_ok vop_src] in Hv1, Hs; subst j; rewrite HR in Hv1.
        - apply andb_prop in Hv1 as [Hv1 _]. apply andb_prop in Hv1 as [Hv1 _]. apply andb_prop in Hv1 as [_ Hk].
          destruct (rg_kind W), (rg_kind R); cbn in Hk, HwW |- *; first [reflexivity | discriminate].
        - exact (rg_sub_kind R W o' Hv1 HwW). }
      cbn [rg_kind]. destruct (rz_keep (s_rgs Q) R ((k, o) :: ks)); destruct (rg_kind R); cbn in HwR |- *; first [reflexivity | discriminate].
    - apply IH. intros j R0 Hj. rewrite <- (Hl (S j) R0 Hj). f_equal. lia. }
  apply G. intros j R Hj. exact Hj.
Qed.
#[using="Type"] Lemma frag_cont_shape : forall L P0 Q keep qk vs rgs_w ret K, frag_cont L P0 Q keep qk vs rgs_w ret = Some K ->
  shape (s_rgs K) = shape (s_rgs L) /\ (s_next L < s_next K)%positive /\ rtm (s_rgs K) = rtm (s_rgs L).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L P0 Q keep qk vs rgs_w ret K H. unfold frag_cont in H. destruct (frag_ok L P0 Q keep qk vs rgs_w ret) eqn:Hok; [|discriminate].
  injection H as <-. cbn [cont_st s_rgs s_next].
  unfold frag_ok in Hok. cbv zeta in Hok.
  repeat match type of Hok with (?a && ?b)%bool = true => apply andb_prop in Hok as [Hok ?] end.
  split; [apply shape_map_new_rg|].
  split; [match goal with Hq : Pos.leb (s_next P0) (s_next Q) = true |- _ => apply Pos.leb_le in Hq; lia end|].
  (* [comment removed for export] *)
  set (Lw := with_rgs L rgs_w) in *. set (σc := mcall Lw P0) in *.
  match goal with Hv : views_ok _ _ _ = true |- _ => destruct (views_nth _ _ _ Hv) as [HlV Hvw] end.
  match goal with He : entails _ _ _ = true |- _ => pose proof He as Hent end.
  unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _].
  apply andb_prop in Hent as [Hent Hrge]. cbn [s_rgs with_rgs Lw] in Hrge. destruct (rgs_ent_nth _ _ _ Hrge) as [HlW Hwk].
  unfold rtm. set (f := new_rg (s_rgs Q) (s_rgs P0) σc (sigq σc (s_next P0) (s_next Q) (s_next L)) vs).
  assert (G : forall i l, (forall j R, nth_error l j = Some R -> nth_error (s_rgs L) (i + j) = Some R) ->
             List.map (fun R => is_rt (rg_kind R)) (map_i f i l) = List.map (fun R => is_rt (rg_kind R)) l).
  { intros i l. revert i. induction l as [|R l IH]; intros i Hl; cbn [map_i List.map]; [reflexivity|]. f_equal.
    - unfold f, new_rg. destruct (wviews (s_rgs P0) vs 0 i) as [|[k o] ks] eqn:Hwv; [reflexivity|].
      destruct (wviews_spec (s_rgs P0) vs 0 i k o ltac:(rewrite Hwv; left; reflexivity)) as (P & v & HP & Hv & _ & HwP & Hs & _).
      rewrite Nat.sub_0_r in HP, Hv.
      destruct (nth_error rgs_w k) as [W|] eqn:HW; [|apply nth_error_None in HW; pose proof (nth_error_Some (s_rgs P0) k) as X; rewrite HP in X; specialize (proj1 X ltac:(discriminate)); lia].
      pose proof (Hvw k W v HW Hv) as Hv1. destruct (rg_ent_parts _ _ _ (Hwk k W P HW HP)) as (_ & _ & Hkle & _ & _).
      pose proof (rkind_le_w _ _ Hkle HwP) as HwW. pose proof (Hl 0%nat R eq_refl) as HR. rewrite Nat.add_0_r in HR.
      assert (HwR : wkind (rg_kind R) = true).
      { destruct v as [j|j o']; cbn [view1_ok vop_src] in Hv1, Hs; subst j; rewrite HR in Hv1.
        - apply andb_prop in Hv1 as [Hv1 _]. apply andb_prop in Hv1 as [Hv1 _]. apply andb_prop in Hv1 as [_ Hk].
          destruct (rg_kind W), (rg_kind R); cbn in Hk, HwW |- *; first [reflexivity | discriminate].
        - exact (rg_sub_kind R W o' Hv1 HwW). }
      cbn [rg_kind]. destruct (rz_keep (s_rgs Q) R ((k, o) :: ks)); destruct (rg_kind R); cbn in HwR |- *; first [reflexivity | discriminate].
    - apply IH. intros j R0 Hj. rewrite <- (Hl (S j) R0 Hj). f_equal. lia. }
  apply G. intros j R Hj. exact Hj.
Qed.
End CSound.

Section CSound2.
Variable segs : list Segment.

#[using="Type"] Theorem ccheck_sound : forall t img ins depth d cp s finals,
  tbl_ok segs t -> img_ok segs img -> ccheck t img ins depth d cp s = Some finals ->
  (forall P0 Q, In (P0, Q) (sites_list cp) -> exists rets, fn_ok segs P0 Q rets) ->
  forall E ms, sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true -> bases_ins ins (s_rgs s) = true ->
  forallb (fun x => Pos.ltb x (s_next s)) ins = true ->
  exists L ms' E', In L finals /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x ins -> E' x = E x) /\
    (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\
    (s_next s <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs s).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth d. induction d as [|d IH]; intros cp s finals Ht Himg Hc Hsites E ms Hd Hw1 Hw2 Hib; cbn [ccheck] in Hc; [discriminate|].
  destruct cp as [p calls]. destruct (check t img ins depth p s) as [ls|] eqn:Hck; [|discriminate].
  destruct (check_frame_fr segs t img ins depth p s ls Ht Himg Hck E ms Hd Hw1 Hw2)
    as (L & ms1 & E1 & HL & Hst1 & Hd1 & Hins1 & Hfr1 & Hsh1 & Hn1 & Hrt1).
  destruct (call_all_sound _ _ _ _ Hc L HL) as [(Hn & Hin)|(c & k & K & f1 & Hf & Hcc & HbK & Hk & Hsub)].
  - exists L, ms1, E1. refine (conj Hin (conj Hst1 (conj Hd1 (conj Hins1 (conj Hfr1 (conj Hsh1 (conj Hn1 Hrt1))))))).
  - pose proof (find_site_sound _ _ _ _ Hf) as Hin.
    destruct (sites_list_in p calls _ _ _ Hin) as [Hs1 Hs2].
    destruct (Hsites _ _ Hs1) as (rets & Hfn).
    destruct (call_sound segs _ _ rets _ _ _ _ _ L K E1 ms1 Hfn Hcc Hd1) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2).
    destruct (call_cont_shape _ _ _ _ _ _ _ _ _ Hcc) as (HshK & HnK & HrtK).
    assert (Hw2K : bases_ins ins (s_rgs K) = true).
    { apply (bases_ins_shape ins (s_rgs s) (s_rgs K)); [rewrite HshK; exact Hsh1 | exact Hw2]. }
    rewrite forallb_forall in Hib.
    assert (Hins2 : forall x, In x ins -> E2 x = E x).
    { intros x Hx. rewrite <- (Ha2 x ltac:(pose proof (Hib x Hx) as X; apply Pos.ltb_lt in X; lia)). exact (Hins1 x Hx). }
    assert (HibK : forallb (fun x => Pos.ltb x (s_next K)) ins = true).
    { apply forallb_forall. intros x Hx. pose proof (Hib x Hx) as X. apply Pos.ltb_lt in X. apply Pos.ltb_lt. lia. }
    destruct (IH k K f1 Ht Himg Hk (fun P0 Q H => Hsites P0 Q (Hs2 _ H)) E2 ms2 Hd2 HbK Hw2K HibK)
      as (L2 & ms3 & E3 & HL2 & Hst3 & Hd3 & Hins3 & Hfr3 & Hsh3 & Hn3 & Hrt3).
    exists L2, ms3, E3. split; [exact (Hsub L2 HL2)|].
    split; [exact (isteps_trans segs _ _ _ Hst1 (isteps_trans segs _ _ _ Hst2 Hst3))|]. split; [exact Hd3|].
    split; [intros x Hx; rewrite (Hins3 x Hx); exact (Hins2 x Hx)|].
    split.
    + intros x Hx.
      assert (X1 : fr_pt E1 (s_rgs L) x).
      { apply (fr_pt_shape E1 (s_rgs s) (s_rgs L) x Hsh1 Hrt1). apply (proj1 (fr_pt_params E E1 ins (s_rgs s) x Hw2 Hins1)). exact Hx. }
      assert (X2 : fr_pt E2 (s_rgs K) x).
      { apply (fr_pt_shape E2 (s_rgs s) (s_rgs K) x ltac:(rewrite HshK; exact Hsh1) ltac:(rewrite HrtK; exact Hrt1)).
        apply (proj1 (fr_pt_params E E2 ins (s_rgs s) x Hw2 Hins2)). exact Hx. }
      rewrite (Hfr3 x X2), (Hfr2 x X1), (Hfr1 x Hx). reflexivity.
    + split; [rewrite Hsh3, HshK; exact Hsh1|]. split; [lia|]. rewrite Hrt3, HrtK. exact Hrt1.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem fn_ok_of_ccert : forall t img depth d cp P0 Q rets,
  tbl_ok segs t -> img_ok segs img ->
  all_fin (fin_q Q rets (s_next P0)) (ccheck t img (vars_below (s_next P0)) depth d cp P0) = true ->
  (forall P0' Q', In (P0', Q') (sites_list cp) -> exists rets', fn_ok segs P0' Q' rets') ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  Forall (is_ret segs) rets -> fn_ok segs P0 Q rets.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth d cp P0 Q rets Ht Himg Hc Hsites Hw1 Hw2 HwQ Hrets E ms Hd.
  destruct (all_fin_sound _ _ Hc) as (finals & Hck & Hfin).
  assert (Hib : forallb (fun x => Pos.ltb x (s_next P0)) (vars_below (s_next P0)) = true).
  { apply forallb_forall. intros x Hx. apply Pos.ltb_lt. exact (vars_below_lt _ x Hx). }
  destruct (ccheck_sound t img (vars_below (s_next P0)) depth d cp P0 finals Ht Himg Hck Hsites E ms Hd Hw1 Hw2 Hib)
    as (L & ms' & E1 & HL & Hst & Hd1 & Hins & Hfr & _ & _ & _).
  pose proof (Hfin L HL) as HfL. unfold fin_q in HfL.
  set (σ := mq L (with_pc Q (s_pc L))) in HfL.
  apply andb_prop in HfL as [HfL Hfix]. apply andb_prop in HfL as [HfL Hent]. apply andb_prop in HfL as [Hp Hr].
  apply existsb_exists in Hp as (p0 & Hp0 & Hpe). apply Z.eqb_eq in Hpe.
  exists ms', (ecomp E1 σ), (s_pc L). split; [exact Hst|]. split; [rewrite Hpe; exact Hp0|].
  split; [rewrite Forall_forall in Hrets; apply Hrets; rewrite Hpe; exact Hp0|].
  split; [apply (entails_sden segs E1 L (with_pc Q (s_pc L)) σ ms' (sden_0 _ _ _ _ Hd1) Hent); rewrite state_wf_with_pc; exact HwQ|].
  split; [|exact Hfr].
  intros x Hx. rewrite <- (fixed_below_agree E1 σ (s_next P0) Hfix x Hx). symmetry. apply Hins. apply in_vars_below. exact Hx.
Qed.
End CSound2.
