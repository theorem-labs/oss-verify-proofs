(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ShadowRwOn.v 3412525be9c (the blob this tree had at release c5e779efe8c) (a working branch ea8776b2302): character-identical to this tree's A apart from the image prefix (A.AsanRT / A.Img0 -> B.AsanRT / B.Img0; lib/A/ -> lib/B/ in the comment).  The comment's line references are A's text unchanged: AsanRT.v:28-29 is the same in B; B's twin of ProgWorldRtShadow.v:57-60 is lib/B/ProgWorldRtShadow.v:58-61. *)
(* lib/B/ShadowRwOn.v -- route (C) (a Theorem Labs lane DECISION 09:20Z): the region-restricted form of B.AsanRT.shadow_rw, as a LEAF
   file so callee contracts (lib/B/Prog/*_c.v, *F.v) can state it without Requiring the walk (a Theorem Labs lane 09:23Z, wave
   lead).  ONE WRITER: a Theorem Labs lane.  Moved text-unchanged from lib/B/ACtlCutC.v, which now Requires this file.
   rule 24: no function proved.

   shadow_rw_on P m is B.AsanRT.shadow_rw's body (AsanRT.v:28-29) under the guard P, guard FIRST.  Narrowing a premise
   `shadow_rw m` to `shadow_rw_on R m` weakens it, so every existing caller still closes it with one
   shadow_rw_on_of_shadow_rw. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Local Open Scope Z_scope.

(* B.AsanRT.shadow_rw (AsanRT.v:28-29), restricted to the shadow bytes P names. *)
Definition shadow_rw_on (P : Z -> Prop) (m : word -> option byte) : Prop :=
  forall a, P a -> B.AsanRT.in_shadow a ->
    wview B.Img0.rsegs m (lib.Lib.Mem.wa a) <> None /\ exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa a) = Some b.

(* The universal form gives every restricted one. *)
Lemma shadow_rw_on_of_shadow_rw : forall P m, B.AsanRT.shadow_rw m -> shadow_rw_on P m.
Proof. intros P m H a _ Ha. exact (H a Ha). Qed.

(* The whole-shadow region gives the universal form back (a Theorem Labs lane 09:38Z: old-name corollaries of narrowed posts). *)
Lemma shadow_rw_of_on_all : forall m, shadow_rw_on (fun _ => True) m -> B.AsanRT.shadow_rw m.
Proof. intros m H a Ha. exact (H a I Ha). Qed.

(* A smaller region is implied. *)
Lemma shadow_rw_on_mono : forall (P Q : Z -> Prop) m, (forall a, Q a -> P a) -> shadow_rw_on P m -> shadow_rw_on Q m.
Proof. intros P Q m HQP H a Ha Hs. exact (H a (HQP a Ha) Hs). Qed.

(* Two regions give their union. *)
Lemma shadow_rw_on_union : forall (P Q : Z -> Prop) m,
  shadow_rw_on P m -> shadow_rw_on Q m -> shadow_rw_on (fun a => P a \/ Q a) m.
Proof. intros P Q m HP HQ a [Ha|Ha] Hs; [exact (HP a Ha Hs) | exact (HQ a Ha Hs)]. Qed.

(* A present byte at a shadow address is a shadow_rw byte (ProgWorldRtShadow.v:57-60). *)
Lemma srw_byte_of_mem : forall (m : word -> option byte) a, m (Z_to_bv 64 a) <> None ->
  wview B.Img0.rsegs m (lib.Lib.Mem.wa a) <> None /\ exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros m a Hm. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exfalso; exact (Hm eq_refl)].
  split.
  - unfold wview, lib.Lib.Mem.wa. rewrite Em. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Em. reflexivity.
Qed.

Print Assumptions shadow_rw_on_union.
