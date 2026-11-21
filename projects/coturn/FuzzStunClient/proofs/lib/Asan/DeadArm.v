(* The dead-arm check of the ASan plans: a function apart from the plan checker [AsanPlan.AP.check], so that no
   stored certificate is computed again.

   [dead_ok hf p] is true when every [PSpin] of [p], and every [PHandoff h] with [hf h = false], sits under an arm
   the flagged plan soundness ([AsanPlanSound.APS.check_sound]) may leave at the flag [false]: the refused arm of
   [PMmap], [PMprotect] and [PMunmap2], and the kept and destroyed arms of [PMmapIn], [PMmapInH] and [PMmapInS].
   Each such arm is a refusal of mmap, mprotect or munmap -- an ENOMEM answer -- at a node whose soundness lemma
   also shows the arm that is no refusal ([Corpus/HaltsFO.dead_sib]); under [forced_only_cfg] the refusal is no
   step.  Every other arm is checked.  An encoded plan ([PlanCodec.dec_plan]) is decoded where [vm_compute] meets
   it. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanPlan.
Import AP.

Fixpoint dead_ok (hf : nat -> bool) (p : plan) : bool :=
  match p with
  | PRun _ k => dead_ok hf k
  | PSplit _ _ k1 k2 => dead_ok hf k1 && dead_ok hf k2
  | PCase2 _ _ k1 k2 => dead_ok hf k1 && dead_ok hf k2
  | PCaseDisj _ _ k1 k2 => dead_ok hf k1 && dead_ok hf k2
  | PShDisj _ _ _ _ k => dead_ok hf k
  | PContra => true
  | PFact _ k => dead_ok hf k
  | PJoin _ _ _ k => dead_ok hf k
  | PForget _ k => dead_ok hf k
  | PDropRange _ _ k => dead_ok hf k
  | PGcKeep _ k => dead_ok hf k
  | PBump _ k => dead_ok hf k
  | PHavoc _ k => dead_ok hf k
  | PHavocBig _ k => dead_ok hf k
  | PFresh _ _ _ k => dead_ok hf k
  | PSys _ k => dead_ok hf k
  | PMmap _ kgranted => dead_ok hf kgranted
  | PMmapIn _ kok _ => dead_ok hf kok
  | PMprotect _ kgranted => dead_ok hf kgranted
  | PBrk2 ka kb => dead_ok hf ka && dead_ok hf kb
  | PMunmap2 _ kgranted => dead_ok hf kgranted
  | PX _ _ k => dead_ok hf k
  | PExt _ _ k => dead_ok hf k
  | PEmit _ _ k => dead_ok hf k
  | PExt2 _ _ k1 k2 => dead_ok hf k1 && dead_ok hf k2
  | PLoop _ _ _ body k => dead_ok hf body && dead_ok hf k
  | PNext => true
  | PHandoff h => hf h
  | PExit => true
  | PSpin => false
  | PFog _ _ k => dead_ok hf k
  | PFogNew _ _ k => dead_ok hf k
  | PGhost _ _ k => dead_ok hf k
  | PUnvis _ _ k => dead_ok hf k
  | PHavocBrk _ _ k => dead_ok hf k
  | PIntro _ _ k => dead_ok hf k
  | PDiamond _ _ k => dead_ok hf k
  | PRename _ k => dead_ok hf k
  | PCompact k => dead_ok hf k
  | PVia _ _ _ karms k => dead_ok hf karms && dead_ok hf k
  | PMerge _ => true
  | PAbstractCell _ _ k => dead_ok hf k
  | PHavocWords _ k => dead_ok hf k
  | PRespell _ _ k => dead_ok hf k
  | PMmapInH _ kok _ => dead_ok hf kok
  | PCaseDisjJ _ _ _ _ k => dead_ok hf k
  | PCaseP k1 k2 => dead_ok hf k1 && dead_ok hf k2
  | PCaseNJ _ _ _ _ _ k => dead_ok hf k
  | PVisAbsorb _ _ k => dead_ok hf k
  | PFreshCell _ _ k => dead_ok hf k
  | PVisSplit _ _ _ k => dead_ok hf k
  | PVisHead _ _ _ k => dead_ok hf k
  | PUnvisHead _ _ k => dead_ok hf k
  | PGhostDedup k => dead_ok hf k
  | PHavocBrkP _ _ k => dead_ok hf k
  | PKeep _ _ k => dead_ok hf k
  | PFactMem _ k => dead_ok hf k
  | PVisRespell _ _ _ _ k => dead_ok hf k
  | PMapRespell _ _ _ _ k => dead_ok hf k
  | PMemRespell _ _ _ _ _ k => dead_ok hf k
  | PSrlSplit _ _ k => dead_ok hf k
  | PAndRange _ _ _ k => dead_ok hf k
  | PAndRangeR _ _ _ k => dead_ok hf k
  | PSrlSplitAll _ _ k => dead_ok hf k
  | PFdHavoc _ _ k => dead_ok hf k
  | PFreshCellK _ _ k => dead_ok hf k
  | PVisPerm _ k => dead_ok hf k
  | PHandoffM _ => true
  | PFdRespell _ _ k => dead_ok hf k
  | PDisjNth _ _ _ k => dead_ok hf k
  | PMmapInS _ kok _ => dead_ok hf kok
  end.

(* The hole flags of the plans: [hf_all] for the start-up and post plans, whose holes are all live; [hf26] for the
   main trees, whose hole 26 is filled by a plan that spins ([W0Plans.rep26], [ArgleafPlansAsan.argda1o_tospin1]). *)
Definition hf_all (h : nat) : bool := true.
Definition hf26 (h : nat) : bool := negb (Nat.eqb h 26).

Lemma dead_l : forall fl a b, (fl = true -> (a && b)%bool = true) -> fl = true -> a = true.
Proof. intros fl a b H Hf. destruct (andb_prop _ _ (H Hf)) as [Ha _]. exact Ha. Qed.
Lemma dead_r : forall fl a b, (fl = true -> (a && b)%bool = true) -> fl = true -> b = true.
Proof. intros fl a b H Hf. destruct (andb_prop _ _ (H Hf)) as [_ Hb]. exact Hb. Qed.
Lemma dead_ff : forall (P : Prop), false = true -> P.
Proof. intros P H. discriminate H. Qed.
