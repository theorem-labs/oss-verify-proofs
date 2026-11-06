(* lib/A/ShadowRwOn.v -- route (C) (a Theorem Labs lane DECISION 09:20Z): the region-restricted form of A.AsanRT.shadow_rw, as a LEAF
   file so callee contracts (lib/A/Prog/*_c.v, *F.v) can state it without Requiring the walk (a Theorem Labs lane 09:23Z, wave
   lead).  ONE WRITER: a Theorem Labs lane.  Moved text-unchanged from lib/A/ACtlCutC.v, which now Requires this file.
   rule 24: no function proved.

   shadow_rw_on P m is A.AsanRT.shadow_rw's body (AsanRT.v:28-29) under the guard P, guard FIRST.  Narrowing a premise
   `shadow_rw m` to `shadow_rw_on R m` weakens it, so every existing caller still closes it with one
   shadow_rw_on_of_shadow_rw. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRT A.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Local Open Scope Z_scope.

(* A.AsanRT.shadow_rw (AsanRT.v:28-29), restricted to the shadow bytes P names. *)
Definition shadow_rw_on (P : Z -> Prop) (m : word -> option byte) : Prop :=
  forall a, P a -> A.AsanRT.in_shadow a ->
    wview A.Img0.rsegs m (lib.Lib.Mem.wa a) <> None /\ exists b, lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa a) = Some b.

(* The universal form gives every restricted one. *)
Lemma shadow_rw_on_of_shadow_rw : forall P m, A.AsanRT.shadow_rw m -> shadow_rw_on P m.
Proof. intros P m H a _ Ha. exact (H a Ha). Qed.

(* The whole-shadow region gives the universal form back (a Theorem Labs lane 09:38Z: old-name corollaries of narrowed posts). *)
Lemma shadow_rw_of_on_all : forall m, shadow_rw_on (fun _ => True) m -> A.AsanRT.shadow_rw m.
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
  wview A.Img0.rsegs m (lib.Lib.Mem.wa a) <> None /\ exists b, lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros m a Hm. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exfalso; exact (Hm eq_refl)].
  split.
  - unfold wview, lib.Lib.Mem.wa. rewrite Em. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Em. reflexivity.
Qed.

Print Assumptions shadow_rw_on_union.
