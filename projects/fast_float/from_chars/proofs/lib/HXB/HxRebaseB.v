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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition hx_rebase (pc k : Z) (X : xst) : option (list xst) :=
  let L := xs_st X in
  let l := rget (s_regs L) (rkz k) in
  let w := swin (s_facts L) l in
  let n := s_next L in
  if (Z.eqb (s_pc L) pc && Z.leb 1 k && Z.leb k 31 && Z.leb (fst w) (snd w) && Z.ltb (snd w - fst w) two64)%bool then
    Some [XST (SST (s_pc L) (rset (s_regs L) (rkz k) (laddc (lvar n) (fst w))) (s_rgs L)
                   (FRange (lvar n) 0 (snd w - fst w) :: FRange (lsub l (laddc (lvar n) (fst w))) 0 0 :: s_facts L) (Pos.succ n) (s_resv L)) (xs_x X)]
  else None.

Section HxRebaseB.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.

#[using="Type"] Theorem hx_rebase_okP : forall (Φ : machine_state -> machine_state -> Prop), (forall a, Φ a a) -> forall pc k, hand_okxP segs xok Φ (hx_rebase pc k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦr pc k X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_rebase in Hf. cbn [xs_st xs_x] in *.
  set (l := rget (s_regs L) (rkz k)) in *. set (w := swin (s_facts L) l) in *. set (n := s_next L) in *.
  destruct (Z.eqb (s_pc L) pc && Z.leb 1 k && Z.leb k 31 && Z.leb (fst w) (snd w) && Z.ltb (snd w - fst w) two64)%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [Hc Hw1]. apply andb_prop in Hc as [Hc Hk2]. apply andb_prop in Hc as [_ Hk1].
  apply Z.leb_le in Hk1, Hk2, Hw1. apply Z.ltb_lt in Hw2.
  pose proof (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _ & _ & HF & _).
  destruct (swin_sound E (s_facts L) l HF) as (v & Hv & Hr). fold w in Hr.
  set (E1 := updv E n (Z_to_bv 64 (v - fst w))).
  assert (Hag : agree n E E1).
  { intros x Hx. unfold E1, updv. destruct (Pos.eqb x n) eqn:Hxn; [apply Pos.eqb_eq in Hxn; lia | reflexivity]. }
  assert (HE1n : E1 n = Z_to_bv 64 (v - fst w)) by (unfold E1, updv; rewrite Pos.eqb_refl; reflexivity).
  eexists. exists ms, E1. split; [left; reflexivity|]. split; [apply ist_refl|].
  cbn [xs_st xs_x s_pc s_regs s_rgs s_facts s_next s_resv].
  split; [|split; [exact Hag | split; [intros; reflexivity | split; [reflexivity | split; [fold n; lia | split; [reflexivity |
           split; [rewrite Forall_forall in *; intros f0 Hf0; rewrite forallb_forall in Hxw; exact (xfact_ok_agree xok _ E E1 _ f0 (Hxw f0 Hf0) Hag (HxF f0 Hf0)) |
           split; [apply (xwf_mono n); [lia | exact Hxw] | apply HΦr]]]]]]]].
  intros E' Ha'. cbn [s_next] in Ha'.
  assert (Ha0 : agree n E E').
  { intros x Hx. rewrite (Hag x Hx). apply Ha'. lia. }
  pose proof (Hd E' Ha0) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  assert (HEn : E' n = Z_to_bv 64 (v - fst w)) by (rewrite <- HE1n; symmetry; apply Ha'; lia).
  assert (Hll : lden E' l = lden E l).
  { pose proof (HR0 (Z_to_bv 5 k)) as X1. pose proof (HR (Z_to_bv 5 k)) as X2. unfold l, rkz. rewrite <- X1, <- X2. reflexivity. }
  assert (Hnew : lden E' (laddc (lvar n) (fst w)) = lden E' l).
  { rewrite lden_laddc, lden_lvar, HEn, Hll. apply bv_eq. rewrite !u_Z_to_bv.
    rewrite (Z.mod_small (v - fst w)) by lia. replace (v - fst w + fst w) with v by ring. unfold eqm in Hv. rewrite Hv. apply Z.mod_small, u_range. }
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj _ (conj HG0 (conj HD0 (conj _ Hfrm0))))))).
  - unfold regs_ok. intros r. destruct (Pos.eq_dec (rkey r) (rkz k)) as [Hq|Hq].
    + rewrite Hq. rewrite rget_rset_same by (apply rkz_ne1; lia). rewrite Hnew. rewrite (HR0 r), Hq. reflexivity.
    + rewrite rget_rset_other by exact Hq. exact (HR0 r).
  - constructor; [|constructor; [|exact HF0]]; cbn [fact_ok].
    + rewrite lden_lvar, HEn, u_Z_to_bv, Z.mod_small by lia. lia.
    + rewrite lden_lsub, Hnew.
      assert (Hz : bv_unsigned (bv_sub (lden E' l) (lden E' l)) = 0) by (rewrite bv_sub_unsigned, Z.sub_diag; reflexivity).
      rewrite Hz. lia.
Qed.
#[using="Type"] Theorem hx_rebase_ok : forall pc k, hand_okx segs xok (hx_rebase pc k).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc k. exact (hand_okxP_ok segs xok _ _ (hx_rebase_okP (fun _ _ => True) (fun _ => I) pc k)). Qed.
#[using="Type"] Theorem hx_rebase_ok_fp : forall pc k, hand_okx_fp segs xok (hx_rebase pc k).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc k. exact (hx_rebase_okP fpeq fpeq_refl pc k). Qed.
End HxRebaseB.
