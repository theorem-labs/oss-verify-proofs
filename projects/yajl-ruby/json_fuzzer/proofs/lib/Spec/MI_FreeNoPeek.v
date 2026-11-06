(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_Ext MI_Shadow MI_Pres1 MI_Pres2 MI_WFree MI_WFree2 MI_WGroup MI_WNtf2 MI_Sim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Fixpoint nopeek {R} (t : M R) : Prop :=
  match t with
  | SRet _ => True
  | SVis (EPeek _ _ _) _ => False
  | SVis (EUndef _) _ => True
  | SVis _ k => forall z, nopeek (k z)
  end.

Lemma nopeek_bind {R S} (t : M R) (f : R -> M S) : nopeek t -> (forall r, nopeek (f r)) -> nopeek (sbind t f).
Proof.
  revert f. induction t as [r|e k IH]; intros f Ht Hf; cbn; [apply Hf|].
  destruct e; cbn in Ht |- *; auto.
Qed.

Theorem free_nopeek st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  nopeek (free st (Some (aadd c (UNIT * off)))).
Proof.
  intros INV Hk.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  unfold free. rewrite (free_hdr_eq st c off n m bm i ai a ar ka BF). cbn [sbind].
  set (p := aadd c (UNIT * off)).
  set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).
  assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
  assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _].
  assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
  { change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
    - intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
      subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
        intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ; unfold UNIT, IB in *; lia.
    - subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
      change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
      assert (HP : P (fst bm)) by (destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Hkr); exists r; auto).
      assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
    - subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }
  unfold free_tail.
  assert (MR1' : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; reflexivity).
  assert (MR1 : forall x, get_meta_rec st1 x = get_meta_rec st x) by exact MR1'.
  rewrite !MR1.
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  rewrite (guard_true 60) by (unfold testbit; rewrite Z.lor_spec; fold (MR st m); rewrite NA, NF; reflexivity).
  fold (MR st m).
  destruct (negb ((m_freed (MR st m) =? 0) || (Z.lor (m_freed (MR st m)) (m_avail (MR st m)) + bit i =? mask_upto (m_last_idx (MR st m))))) eqn:BR.
  - exact I.
  - pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hb.
    assert (Hsc0 : 0 <= m_sizeclass (MR st m)).
    { pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as [[? _]|(E63 & _)]; lia. }
    destruct (ntf_spec mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1)
      as (st' & mi & LS' & EQ & POST).
    + apply (hosts_ext st st1); [reflexivity|]. exists ai. exact Hb.
    + rewrite MR1'. exact Hi.
    + cbn [x_pend xpend]. rewrite MR1', Ec. reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold FUEL. lia.
    + rewrite MR1'. unfold FUEL. lia.
    + rewrite EQ. destruct mi as [[base len]|]; [| exact I].
      destruct (negb (len =? 0)); [| exact I]. cbn. intros z. destruct (munmap_answer_ok z); exact I.
Qed.
End RC__1.
