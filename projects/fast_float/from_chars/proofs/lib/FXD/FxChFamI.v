(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep.FxKeep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition amod_f {A : Type} (M M' : smodel) (a : A) : bool := false.

Section FamI.
Context {N1 A1 N2 A2 : Type}.
Variable apost1 : N1 -> sst -> smodel -> A1 -> option (sst * smodel * A1).
Variable anil2 : A2 -> bool.
Variable apost2 : N2 -> sst -> smodel -> A2 -> option (sst * smodel * A2).

Definition apostI (nk : N1 + N2) (S : sst) (M : smodel) (a : A1 * A2) : option (sst * smodel * (A1 * A2)) :=
  match nk with
  | inl n => if anil2 (snd a) then
               match apost1 n S M (fst a) with Some (S', M', a1) => Some (S', M', (a1, snd a)) | None => None end
             else None
  | inr n => match apost2 n S M (snd a) with Some (S', M', a2) => Some (S', M', (fst a, a2)) | None => None end
  end.
End FamI.

Section StrongNode.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Context {N A : Type}.
Variable apost : N -> sst -> smodel -> A -> option (sst * smodel * A).
Variable awf : positive -> A -> bool.
Variable HA : valu -> smodel -> A -> (word -> option byte) -> Prop.

(* [comment removed for export] *)
Definition anode_okS (nk : N) : Prop :=
  forall S M a S' M' a', apost nk S M a = Some (S', M', a') ->
  forall model0 mem0 E ms model T, DEN segs LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN segs LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> keep_ok model' M M' mem0 mem0' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.

#[using="Type"] Lemma anode_okS_ok : forall nk, anode_okS nk -> anode_ok segs cfg LIMIT apost awf HA nk.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros nk H S M a S' M' a' Hp model0 mem0 E ms model T Hd Hw HHA Hk.
  apply (H S M a S' M' a' Hp model0 mem0 E ms model T Hd Hw HHA).
  intros E' mem0' ms' model' Ha Hfs Hd' HHA' _. exact (Hk E' mem0' ms' model' Ha Hfs Hd' HHA').
Qed.
End StrongNode.

(* [comment removed for export] *)
Section PureS.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Context {N A P : Type}.
Variable apost : N -> sst -> smodel -> A -> option (sst * smodel * A).
Variable awf : positive -> A -> bool.
Variable HA : valu -> smodel -> A -> (word -> option byte) -> Prop.
Variable ppost : P -> sst -> smodel -> option sst.
Hypothesis HA_agree : forall n E E' M a m0, sm_wf n M = true -> awf n a = true -> agree n E E' -> HA E M a m0 -> HA E' M a m0.
Hypothesis HanodeS : forall nk, anode_okS segs cfg LIMIT apost awf HA nk.
Hypothesis Hpnode : forall p, pnode_ok segs cfg LIMIT ppost p.

#[using="HA_agree HanodeS Hpnode"] Theorem anodeP_okS : forall nk, anode_okS segs cfg LIMIT (apostP apost ppost) awf HA nk.
Proof. LiaFast.lf_pins (fun (HA_agree HanodeS Hpnode : LiaFast.U) => LiaFast.u0).
  intros [n|p] S M a S' M' a' Hp model0 mem0 E ms model T Hd Hw HAa Hk; cbn [apostP] in Hp.
  - exact (HanodeS n S M a S' M' a' Hp model0 mem0 E ms model T Hd Hw HAa Hk).
  - destruct (ppost p S M) as [S1|] eqn:Hp1; [|discriminate]. injection Hp as <- <- <-.
    apply (Hpnode p S M S1 Hp1 model0 mem0 E ms model T Hd).
    intros E' ms' model' Ha Hd'. apply (Hk E' mem0 ms' model' Ha); [intros q _ w _; reflexivity | exact Hd' | | apply keep_ok_refl].
    exact (HA_agree (s_next S) E E' M a mem0 (dn_wf _ _ _ _ _ _ _ _ _ Hd) Hw Ha HAa).
Qed.
End PureS.

(* [comment removed for export] *)
Section FamISound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Context {N1 A1 N2 A2 : Type}.
Variable apost1 : N1 -> sst -> smodel -> A1 -> option (sst * smodel * A1).
Variables (anil1 : A1 -> bool) (awf1 : positive -> A1 -> bool).
Variable HA1 : valu -> smodel -> A1 -> (word -> option byte) -> Prop.
Variable apost2 : N2 -> sst -> smodel -> A2 -> option (sst * smodel * A2).
Variables (anil2 : A2 -> bool) (awf2 : positive -> A2 -> bool).
Variable HA2 : valu -> smodel -> A2 -> (word -> option byte) -> Prop.
Hypothesis HA2_nil : forall E M a m0, anil2 a = true -> HA2 E M a m0.
Hypothesis HA1_agree : forall n E E' M a m0, sm_wf n M = true -> awf1 n a = true -> agree n E E' -> HA1 E M a m0 -> HA1 E' M a m0.
(* [comment removed for export] *)
Hypothesis HA1_keep : forall model0 E S M M' ms model a m0 m0', DEN segs LIMIT model0 m0' E S M' ms model ->
  keep_ok model M M' m0 m0' -> HA1 E M a m0 -> HA1 E M' a m0'.
Hypothesis Hanode1 : forall nk, anode_ok segs cfg LIMIT apost1 awf1 HA1 nk.
Hypothesis Hanode2 : forall nk, anode_okS segs cfg LIMIT apost2 awf2 HA2 nk.

#[using="HA2_nil HA1_agree HA1_keep Hanode1 Hanode2"] Theorem anodeI_ok : forall nk, anode_ok segs cfg LIMIT (apostI apost1 anil2 apost2) (awfX awf1 awf2) (HAsum HA1 HA2) nk.
Proof. LiaFast.lf_pins (fun (HA2_nil HA1_agree HA1_keep Hanode1 Hanode2 : LiaFast.U) => LiaFast.u0).
  intros [n|n] S M [a1 a2] S' M' a' Hp model0 mem0 E ms model T Hd Hw [HA1a HA2a] Hk;
    unfold apostI in Hp; cbn [fst snd] in Hp; unfold awfX in Hw; cbn [fst snd] in Hw; apply andb_prop in Hw as [Hw1 Hw2].
  - destruct (anil2 a2) eqn:Hn2; [|discriminate]. destruct (apost1 n S M a1) as [[[S1 M1] a1']|] eqn:Hp1; [|discriminate].
    injection Hp as <- <- <-.
    apply (Hanode1 n S M a1 S1 M1 a1' Hp1 model0 mem0 E ms model T Hd Hw1 HA1a).
    intros E' mem0' ms' model' Ha Hfs Hd' HA1'. apply (Hk E' mem0' ms' model' Ha Hfs Hd').
    split; [exact HA1' | exact (HA2_nil E' M1 a2 mem0' Hn2)].
  - destruct (apost2 n S M a2) as [[[S1 M1] a2']|] eqn:Hp2; [|discriminate].
    injection Hp as <- <- <-.
    apply (Hanode2 n S M a2 S1 M1 a2' Hp2 model0 mem0 E ms model T Hd Hw2 HA2a).
    intros E' mem0' ms' model' Ha Hfs Hd' HA2' Hkeep. apply (Hk E' mem0' ms' model' Ha Hfs Hd').
    split; [|exact HA2'].
    pose proof (HA1_agree (s_next S) E E' M a1 mem0 (dn_wf _ _ _ _ _ _ _ _ _ Hd) Hw1 Ha HA1a) as HA1e.
    exact (HA1_keep model0 E' S1 M M1 ms' model' a1 mem0 mem0' Hd' Hkeep HA1e).
Qed.
End FamISound.
