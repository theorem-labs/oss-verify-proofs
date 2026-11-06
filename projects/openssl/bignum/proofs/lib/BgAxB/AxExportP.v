(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Mem. 
From OSSVerify.Proofs.openssl.bignum.lib.Common Require PropExec.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface RT_state RT_main_shape.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxEntryS AxModelRel.
From OSSVerify.Proofs.openssl.bignum.lib.AxA Require Import AxExport AxExportH AxExportQ AxExportV AxExportI.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxB Require Import AxExportS AxExportF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Pristine.
Variable pc0 : N.
Hypothesis Himg : img_ok bgbsegs pc0 = true.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R bgbsegs amodel (MR bgbsegs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable W : list (lin * Z).
Variable J : Z.
Variable F : bforms.
Variable maps0 : list (word * word).

Local Notation L := (Lm ρ W J F maps0).
Local Notation m := (mM ρ ms model W J F maps0).

Definition chk_pristine (top : Z) (r : Z * Z) : bool :=
  let n := snd r - fst r in
  (0 <? n) &&& (n <? 1099511627776) &&& vis_ok B W top (fst r, []) n &&&
  match q_at B (fst r, []) n with Some (Rq, x) => pristine_ok bgbsegs Rq (to_Z x) n | None => false end.

Theorem chk_pristine_sound (top : Z) (r : Z * Z) : chk_pristine top r = true ->
  forall a, fst r <= a < snd r -> mrd bgbsegs m (wa a) = Common.PropExec.seg_rom bgbsegs (wa a).
Proof.
  unfold chk_pristine. cbv zeta. intros H a Ha. apply land_true in H as [H Hq]. apply land_true in H as [H Hv]. apply land_true in H as [N1 N2].
  apply Z.ltb_lt in N1. apply Z.ltb_lt in N2.
  destruct (vis_ok_sound bgbsegs fs0 LIM ρ B ms model HR W J (allow_main L) top (fst r, []) _ Hv) as (V1 & V2 & V3).
  assert (El : leval ρ (fst r, []) = fst r) by (unfold leval; cbn [fst snd teval]; lia). rewrite El in V1, V2, V3.
  destruct (q_at B (fst r, []) (snd r - fst r)) as [[Rq x]|] eqn:Eq; [|discriminate Hq].
  destruct (q_at_spec fs0 LIM ρ B ms model HR (fst r, []) (snd r - fst r) Rq x ltac:(lia) ltac:(rewrite El; lia) Eq) as (Q1 & Q2 & Q3 & Q4).
  rewrite El in Q3. pose proof (to_Z_bounded x) as Bx.
  apply (export_pristine bgbsegs pc0 Himg fs0 LIM ρ B ms model HR (AFull ρ W J F maps0) Rq (to_Z x) (snd r - fst r) Q1 Hq ltac:(lia) Q4);
    [rewrite <- Q3; replace (fst r + (snd r - fst r)) with (snd r) by lia; replace (snd r) with (fst r + (snd r - fst r)) by lia; exact V3 | lia].
Qed.

End Pristine.
