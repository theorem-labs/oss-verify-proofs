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
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxGenFp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition hx_ssplitc (pc k c : Z) (X : xst) : option (list xst) :=
  let L := xs_st X in
  let l := rget (s_regs L) (rkz k) in
  let w := swin (s_facts L) l in
  if (Z.eqb (s_pc L) pc && Z.ltb (fst w) c && Z.leb c (snd w) && Z.ltb (snd w - fst w) two64)%bool then
    Some [XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- fst w)) 0 (c - 1 - fst w) :: s_facts L) (s_next L) (s_resv L)) (xs_x X);
          XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- c)) 0 (snd w - c) :: s_facts L) (s_next L) (s_resv L)) (xs_x X)]
  else if Z.eqb (s_pc L) pc then Some [X] else None.

Section HxSplitB.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.

#[using="Type"] Theorem hx_ssplitc_ok_fp : forall pc k c, hand_okx_fp segs xok (hx_ssplitc pc k c).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc k c X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_ssplitc in Hf. cbn [xs_st xs_x] in *.
  set (l := rget (s_regs L) (rkz k)) in *. set (w := swin (s_facts L) l) in *.
  destruct (Z.eqb (s_pc L) pc && Z.ltb (fst w) c && Z.leb c (snd w) && Z.ltb (snd w - fst w) two64)%bool eqn:Hc.
  2: { destruct (Z.eqb (s_pc L) pc); [|discriminate]. injection Hf as <-.
       exists (XST L XL), ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
       split; [exact Hd|]. split; [intros x Hx; reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|].
       split; [apply Pos.le_refl|]. split; [reflexivity|]. split; [exact HxF|]. split; [exact Hxw | apply fpeq_refl]. }
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Hw3]. apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [_ Hw1].
  apply Z.ltb_lt in Hw1, Hw3. apply Z.leb_le in Hw2.
  pose proof (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _ & _ & HF & _).
  destruct (swin_sound E (s_facts L) l HF) as (v & Hv & Hr). fold w in Hr.
  assert (SH : forall x, 0 <= v - x < two64 -> forall E', lden E' l = lden E l -> bv_unsigned (lden E' (laddc l (- x))) = v - x).
  { intros x Hx E' He. rewrite lden_laddc, He, u_Z_to_bv. unfold eqm in Hv.
    rewrite Z.add_mod by (unfold two64; lia). rewrite <- Hv. rewrite <- Z.add_mod by (unfold two64; lia). apply Z.mod_small. replace (v + - x) with (v - x) by ring. exact Hx. }
  assert (Hcase : {v < c} + {c <= v}) by (destruct (Z_lt_ge_dec v c); [left | right]; lia).
  set (K1 := XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- fst w)) 0 (c - 1 - fst w) :: s_facts L) (s_next L) (s_resv L)) XL).
  set (K2 := XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- c)) 0 (snd w - c) :: s_facts L) (s_next L) (s_resv L)) XL).
  assert (GEN : forall f, (forall E', lden E' l = lden E l -> fact_ok E' f) ->
                  sden segs E (SST (s_pc L) (s_regs L) (s_rgs L) (f :: s_facts L) (s_next L) (s_resv L)) ms).
  { intros f Hfo E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
    refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj HG0 (conj HD0 (conj _ Hfrm0))))))).
    constructor; [|exact HF0]. apply Hfo.
    pose proof (HR0 (Z_to_bv 5 k)) as X1. pose proof (HR (Z_to_bv 5 k)) as X2. unfold l, rkz. rewrite <- X1, <- X2. reflexivity. }
  destruct Hcase as [Hlt|Hge].
  - exists K1, ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
    split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [reflexivity|split; [unfold K1; cbn [xs_st s_next]; apply Pos.le_refl|split; [reflexivity|split; [exact HxF | split; [exact Hxw | apply fpeq_refl]]]]]]]].
    apply GEN. intros E' He. cbn [fact_ok]. rewrite (SH (fst w) ltac:(lia) E' He). lia.
  - exists K2, ms, E. split; [right; left; reflexivity|]. split; [apply ist_refl|].
    split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [reflexivity|split; [unfold K2; cbn [xs_st s_next]; apply Pos.le_refl|split; [reflexivity|split; [exact HxF | split; [exact Hxw | apply fpeq_refl]]]]]]]].
    apply GEN. intros E' He. cbn [fact_ok]. rewrite (SH c ltac:(lia) E' He). lia.
Qed.
End HxSplitB.
