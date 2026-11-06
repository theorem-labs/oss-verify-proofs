(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GPotHR.

Fixpoint flat (v : sv) (acc : list sv) : list sv :=
  match v with
  | VAlu ALU_ADD a b => flat a (flat b acc)
  | _ => v :: acc
  end.
Fixpoint refold (l : list sv) : sv :=
  match l with
  | [] => VL wzero
  | [a] => a
  | a :: l' => VAlu ALU_ADD a (refold l')
  end.

Fixpoint take_mul (c : w64) (l : list sv) : option (sv * list sv) :=
  match l with
  | [] => None
  | a :: l' =>
      match a with
      | VMd M_MUL t (VL c') =>
          if weqb c' c then Some (t, l')
          else match take_mul c l' with Some (t2, r) => Some (t2, a :: r) | None => None end
      | _ => match take_mul c l' with Some (t2, r) => Some (t2, a :: r) | None => None end
      end
  end.
Definition hiZ (fs : list fact) (a : sv) : Z := w2Z (snd (sv_bounds fs a)).
Fixpoint sum_hi (fs : list fact) (l : list sv) : Z :=
  match l with [] => 0 | a :: l' => hiZ fs a + sum_hi fs l' end.

Section WithPc.
Variable C_PC : int.
Variable C : w64.

Definition weaken_core (fs : list fact) (f : fact) : option (list sv * list sv) :=
  match f with
  | FULe L R =>
      match take_mul C (flat L []) with
      | Some (tL, restL) =>
          let flatR := flat R [] in
          let tRr := match take_mul C flatR with Some (tR, restR) => (Some tR, restR) | None => (None, flatR) end in
          let okR := match fst tRr with
                     | Some tR => match decide_ltu fs tL tR with Some false => true | _ => false end
                     | None => true
                     end in
          let sL := sum_hi fs restL + w2Z C * hiZ fs tL in
          let sR := sum_hi fs (snd tRr) + match fst tRr with Some tR => w2Z C * hiZ fs tR | None => 0 end in
          if okR && (sL <? two64) && (sR <? two64) then Some (restL, snd tRr) else None
      | None => None
      end
  | _ => None
  end.
Definition weaken (fs : list fact) (f : fact) : option fact :=
  match weaken_core fs f with Some (l, r) => Some (FULe (refold l) (refold r)) | None => None end.

Fixpoint lower (fs : list fact) (l : list sv) : list sv :=
  match l with
  | [] => []
  | a :: l' => match a with VP _ _ => VL (fst (sv_bounds fs a)) | _ => a end :: lower fs l'
  end.
Fixpoint svl_eqb (a b : list sv) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => sv_eqb x y && svl_eqb a' b' | _, _ => false end.
Definition weaken2 (fs : list fact) (f : fact) : list fact :=
  match weaken_core fs f with
  | Some (l, r) => let low := lower fs l in FULe (refold l) (refold r) :: (if svl_eqb low l then [] else [FULe (refold low) (refold r)])
  | None => []
  end.
Fixpoint weaken_all (fs : list fact) (l : list fact) : list fact :=
  match l with
  | [] => []
  | f :: l' => List.filter (fun g => negb (existsb (fact_eqb g) fs)) (weaken2 fs f) ++ weaken_all fs l'
  end.
Fixpoint addfacts (st : sstate) (l : list fact) : sstate :=
  match l with [] => st | f :: l' => addfacts (addfact st f) l' end.

Definition gpothr_apply (st : sstate) : option (list sstate) :=
  match weaken_all (s_facts st) (s_facts st) with
  | [] => None
  | gs => Some [addfacts st gs]
  end.

Definition gpothr_contract : contract := Contract C_PC gpothr_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Section WithEnv.
Variable E : env.
Variable fs : list fact.
Hypothesis FH : facts_hold E fs.
Local Notation U v := (bv_unsigned (den E v)).

Fixpoint sumU (l : list sv) : Z := match l with [] => 0 | a :: l' => U a + sumU l' end.

Lemma U_range v : 0 <= U v < two64.
Proof. pose proof (bv_unsigned_in_range _ (den E v)) as R. rewrite bv_modulus_64 in R. unfold two64. exact R. Qed.

Lemma sumU_nonneg l : 0 <= sumU l.
Proof. induction l as [|a l IH]; cbn [sumU]; [lia|]. pose proof (U_range a). lia. Qed.

Lemma den_add_u a b : U (VAlu ALU_ADD a b) = (U a + U b) mod two64.
Proof.
  change (den E (VAlu ALU_ADD a b)) with (alu64 ALU_ADD (den E a) (den E b)). cbn [alu64 alu].
  rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
Qed.

Lemma flat_sum : forall v acc, (sumU (flat v acc)) mod two64 = (U v + sumU acc) mod two64.
Proof.
  induction v as [| |op a IHa b IHb| | | | | | | |]; intros acc; try reflexivity.
  destruct op; try reflexivity. cbn [flat]. rewrite IHa.
  rewrite <- Zplus_mod_idemp_r, IHb, Zplus_mod_idemp_r. rewrite den_add_u.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma refold_sum : forall l, U (refold l) = (sumU l) mod two64.
Proof.
  induction l as [|a l IH].
  - cbn [refold sumU]. rewrite den_VL, wzero_ok. reflexivity.
  - destruct l as [|b l'].
    + cbn [refold sumU]. rewrite Z.add_0_r. symmetry. apply Z.mod_small. apply U_range.
    + change (refold (a :: b :: l')) with (VAlu ALU_ADD a (refold (b :: l'))). rewrite den_add_u, IH.
      change (sumU (a :: b :: l')) with (U a + sumU (b :: l')). rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma take_mul_sum : forall c l t r, take_mul c l = Some (t, r) -> sumU l = U (VMd M_MUL t (VL c)) + sumU r.
Proof.
  intros c. induction l as [|a l IH]; intros t r H; [discriminate H|].
  cbn [take_mul] in H.
  assert (GEN : forall a', match take_mul c l with Some (t2, r0) => Some (t2, a' :: r0) | None => None end = Some (t, r) ->
                 sumU (a' :: l) = U (VMd M_MUL t (VL c)) + sumU r).
  { intros a' H'. destruct (take_mul c l) as [[t2 r0]|] eqn:TM; [|discriminate H']. injection H' as <- <-.
    cbn [sumU]. rewrite (IH t2 r0 eq_refl). lia. }
  destruct a as [| | | |mo x y| | | | | |]; try exact (GEN _ H).
  destruct mo; try exact (GEN _ H). destruct y as [c'| | | | | | | | | |]; try exact (GEN _ H).
  destruct (weqb c' c) eqn:WC; [|exact (GEN _ H)]. injection H as <- <-.
  apply (proj1 (weqb_ok _ _)) in WC. subst c'. reflexivity.
Qed.

Lemma den_mul_lit t c : U (VMd M_MUL t (VL c)) = (U t * w2Z c) mod two64.
Proof.
  change (den E (VMd M_MUL t (VL c))) with (bv_mul (den E t) (den E (VL c))).
  rewrite bv_mul_unsigned, den_VL. unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
Qed.

Lemma hiZ_ok a : U a <= hiZ fs a.
Proof. unfold hiZ. pose proof (sv_bounds_sound E fs FH a) as I0. unfold inb in I0. lia. Qed.

Lemma sum_hi_ok l : sumU l <= sum_hi fs l.
Proof. induction l as [|a l IH]; cbn [sumU sum_hi]; [lia|]. pose proof (hiZ_ok a). lia. Qed.

Lemma w2Z_nonneg c : 0 <= w2Z c.
Proof. unfold w2Z. pose proof (int_range (wl c)). destruct (wt c); unfold two63; lia. Qed.

Lemma weaken_core_sound : forall L R l r, fact_holds E (FULe L R) -> weaken_core fs (FULe L R) = Some (l, r) ->
  sumU l <= sumU r /\ sumU r < two64.
Proof.
  intros L R l r Hf W. unfold weaken_core in W.
  destruct (take_mul C (flat L [])) as [[tL restL]|] eqn:TL; [|discriminate W].
  cbn zeta in W.
  pose proof (w2Z_nonneg C) as C0.
  pose proof (hiZ_ok tL) as HtL. pose proof (U_range tL) as RtL.
  assert (PL : 0 <= w2Z C * hiZ fs tL) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (sum_hi_ok restL) as SLr. pose proof (sumU_nonneg restL) as NLr.
  cbn [fact_holds] in Hf.
  assert (HL : sum_hi fs restL + w2Z C * hiZ fs tL < two64 -> U L = U tL * w2Z C + sumU restL).
  { intros SL. pose proof (flat_sum L []) as F0. cbn [sumU] in F0. rewrite Z.add_0_r in F0.
    rewrite (take_mul_sum C _ _ _ TL), den_mul_lit in F0.
    assert (B1 : U tL * w2Z C <= hiZ fs tL * w2Z C) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (B0 : 0 <= U tL * w2Z C) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite (Z.mod_small (U tL * w2Z C)) in F0 by lia.
    rewrite (Z.mod_small (U tL * w2Z C + sumU restL)) in F0 by lia.
    rewrite (Z.mod_small (U L)) in F0 by (apply U_range). lia. }
  destruct (take_mul C (flat R [])) as [[tR restR]|] eqn:TR; cbn [fst snd] in W.
  - destruct (decide_ltu fs tL tR) as [[|]|] eqn:DL; try discriminate W.
    destruct (sum_hi fs restL + w2Z C * hiZ fs tL <? two64) eqn:SL; [|discriminate W].
    destruct (sum_hi fs restR + w2Z C * hiZ fs tR <? two64) eqn:SR; [|discriminate W].
    cbn [andb] in W. injection W as <- <-. apply Z.ltb_lt in SL. apply Z.ltb_lt in SR.
    pose proof (decide_ltu_sound E fs FH tL tR false DL) as LE. apply (proj1 (ltu_iff _ _ false)) in LE.
    pose proof (hiZ_ok tR) as HtR. pose proof (U_range tR) as RtR.
    assert (PR : 0 <= w2Z C * hiZ fs tR) by (apply Z.mul_nonneg_nonneg; lia).
    pose proof (sum_hi_ok restR) as SRr. pose proof (sumU_nonneg restR) as NRr.
    assert (HR : U R = U tR * w2Z C + sumU restR).
    { pose proof (flat_sum R []) as F0. cbn [sumU] in F0. rewrite Z.add_0_r in F0.
      rewrite (take_mul_sum C _ _ _ TR), den_mul_lit in F0.
      assert (B1 : U tR * w2Z C <= hiZ fs tR * w2Z C) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (B0 : 0 <= U tR * w2Z C) by (apply Z.mul_nonneg_nonneg; lia).
      rewrite (Z.mod_small (U tR * w2Z C)) in F0 by lia.
      rewrite (Z.mod_small (U tR * w2Z C + sumU restR)) in F0 by lia.
      rewrite (Z.mod_small (U R)) in F0 by (apply U_range). lia. }
    assert (M : U tR * w2Z C <= U tL * w2Z C) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (B1 : U tL * w2Z C <= hiZ fs tL * w2Z C) by (apply Z.mul_le_mono_nonneg_r; lia).
    specialize (HL SL). lia.
  - destruct (sum_hi fs restL + w2Z C * hiZ fs tL <? two64) eqn:SL; [|discriminate W].
    destruct (sum_hi fs (flat R []) + 0 <? two64) eqn:SR; [|discriminate W].
    cbn [andb] in W. injection W as <- <-. apply Z.ltb_lt in SL. apply Z.ltb_lt in SR.
    pose proof (sum_hi_ok (flat R [])) as SRr. pose proof (sumU_nonneg (flat R [])) as NRr.
    pose proof (flat_sum R []) as F0. cbn [sumU] in F0. rewrite Z.add_0_r in F0.
    rewrite (Z.mod_small (U R)) in F0 by (apply U_range). rewrite (Z.mod_small (sumU (flat R []))) in F0 by lia.
    assert (B1 : U tL * w2Z C <= hiZ fs tL * w2Z C) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (B0 : 0 <= U tL * w2Z C) by (apply Z.mul_nonneg_nonneg; lia).
    specialize (HL SL). lia.
Qed.

Lemma lower_le : forall l, 0 <= sumU (lower fs l) <= sumU l.
Proof.
  induction l as [|a l IH]; cbn [lower sumU]; [lia|].
  pose proof (U_range a) as RA.
  destruct a as [|k o| | | | | | | | |]; cbn [sumU]; try lia.
  pose proof (sv_bounds_sound E fs FH (VP k o)) as I0. unfold inb in I0. rewrite den_VL.
  pose proof (w2Z_nonneg (fst (sv_bounds fs (VP k o)))). lia.
Qed.

Lemma weaken2_sound : forall f, fact_holds E f -> Forall (fact_holds E) (weaken2 fs f).
Proof.
  intros f Hf. unfold weaken2. destruct (weaken_core fs f) as [[l r]|] eqn:W; [|constructor].
  destruct f as [| | |L R| | | |]; try discriminate W.
  destruct (weaken_core_sound L R l r Hf W) as [LE RB].
  pose proof (sumU_nonneg l) as NL. pose proof (sumU_nonneg r) as NR. pose proof (lower_le l) as LL.
  constructor.
  - cbn [fact_holds]. rewrite !refold_sum. rewrite !Z.mod_small by lia. exact LE.
  - destruct (svl_eqb (lower fs l) l); [constructor|]. constructor; [|constructor].
    cbn [fact_holds]. rewrite !refold_sum. rewrite !Z.mod_small by lia. lia.
Qed.

Lemma weaken_all_sound : forall l, Forall (fact_holds E) l -> Forall (fact_holds E) (weaken_all fs l).
Proof.
  induction l as [|f l IH]; intros H; cbn [weaken_all]; [constructor|].
  inversion H as [|f' l' Hf Hl]; subst. apply Forall_app. split; [|exact (IH Hl)].
  apply incl_Forall with (l1 := weaken2 fs f); [apply incl_filter| exact (weaken2_sound f Hf)].
Qed.
End WithEnv.

Lemma addfacts_sound : forall E st ms model l,
  st_ok segs OPS E st ms model -> Forall (fact_holds E) l -> st_ok segs OPS E (addfacts st l) ms model.
Proof.
  intros E st ms model l. revert st. induction l as [|f l IH]; intros st HS HL; cbn [addfacts]; [exact HS|].
  inversion HL as [|f' l' Hf Hl]; subst. apply IH; [|exact Hl]. apply addfact_sound; [exact HS| exact Hf].
Qed.

Theorem gpothr_sound : contract_sound segs OPS MP PB gpothr_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gpothr_contract c_apply] in HA. unfold gpothr_apply in HA.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  destruct (weaken_all (s_facts st) (s_facts st)) as [|g gs] eqn:WA; [discriminate|]. injection HA as <-.
  refine (Hk _ (or_introl eq_refl) E ms model _ HMP _).
  - apply env_ext_refl.
  - assert (FA : Forall (fact_holds E) (g :: gs)). { rewrite <- WA. apply weaken_all_sound; [exact FH|]. exact FH. }
    pose proof (addfacts_sound E st ms model (g :: gs) HS FA) as H2. cbn [addfacts] in H2 |- *. exact H2.
Qed.

End Sound.
End WithPc.
End GPotHR.
