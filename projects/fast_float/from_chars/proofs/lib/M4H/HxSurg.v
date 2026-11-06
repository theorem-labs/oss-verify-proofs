(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst FxEnt FxFrame FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChSplit FxChSplitS FxChBlob.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcSteps AcCarveP AcMALp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition STOP : Z := 0x63a000.   (* [comment removed for export] *)
Lemma asegs_below_h : segs_below_b Asan.M.loaded_segments STOP = true.
Proof. vm_compute. reflexivity. Qed.

Inductive surg : Type :=
| SSteps (f : sst -> option (list rstep))       (* [comment removed for export] *)
| SSplit (f : sst -> option (nat * lin * lin))   (* [comment removed for export] *)
| SMerge (f : sst -> option (nat * nat))         (* [comment removed for export] *)
| SRetype (f : sst -> option (nat * rkind))      (* [comment removed for export] *)
| SFront (f : sst -> option nat).               (* [comment removed for export] *)

Definition surg_post (h : surg) (S : sst) : option sst :=
  match h with
  | SSteps f => match f S with
                | Some sts => match steps_rgs (s_next S) (s_facts S) (s_rgs S) sts with Some l => Some (with_rgs S l) | None => None end
                | None => None
                end
  | SSplit f => match f S with Some (i, p, m) => split_s_post S i p m | None => None end
  | SMerge f => match f S with Some (i, n) => merge_s_post S i n | None => None end
  | SRetype f => match f S with Some (i, k) => retype_post STOP S i k | None => None end
  | SFront f => match f S with Some i => Some (with_rgs' S (nth_front i (s_rgs S))) | None => None end
  end.

Lemma merge2_next : forall S i S', merge2_post S i = Some S' -> s_next S' = s_next S.
Proof.
  intros S i S' H. unfold merge2_post in H. destruct (nth_error (s_rgs S) i), (nth_error (s_rgs S) (Datatypes.S i)); try discriminate.
  destruct (merge2_chk _ _ _); [|discriminate]. injection H as <-. reflexivity.
Qed.

Section Den.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Abbreviation ASEGS := Asan.M.loaded_segments.

#[using="Type"] Theorem surg_den : forall h E S M ms model S', DEN ASEGS LIMIT model0 mem0 E S M ms model -> surg_post h S = Some S' ->
  DEN ASEGS LIMIT model0 mem0 E S' M ms model /\ s_next S' = s_next S.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [f|f|f|f|f] E S M ms model S' Hd Hp; cbn [surg_post] in Hp.
  - destruct (f S) as [sts|]; [|discriminate].
    destruct (steps_rgs (s_next S) (s_facts S) (s_rgs S) sts) as [l|] eqn:Hl; [|discriminate]. injection Hp as <-.
    split; [exact (den_steps ASEGS LIMIT model0 mem0 sts E S M ms model l Hd Hl) | reflexivity].
  - destruct (f S) as [[[i p] m]|]; [|discriminate].
    split; [exact (den_split_s ASEGS LIMIT mem0 model0 E S M ms model i p m S' Hd Hp)|].
    unfold split_s_post in Hp. destruct (nth_error (s_rgs S) i); [|discriminate].
    destruct (split_s_chk _ _ _ _ _); [|discriminate]. injection Hp as <-. reflexivity.
  - destruct (f S) as [[i n]|]; [|discriminate].
    split; [exact (den_merge_s ASEGS LIMIT mem0 model0 E S M ms model i n S' Hd Hp)|].
    unfold merge_s_post in Hp. destruct n as [|[|[|[|n]]]]; try discriminate.
    + exact (merge2_next S i S' Hp).
    + destruct (merge2_post S (Datatypes.S i)) as [S1|] eqn:H1; [|discriminate].
      rewrite (merge2_next S1 i S' Hp). exact (merge2_next S (Datatypes.S i) S1 H1).
  - destruct (f S) as [[i k]|]; [|discriminate].
    split; [exact (den_retype ASEGS LIMIT mem0 STOP asegs_below_h model0 E S M ms model i k S' Hd Hp)|].
    unfold retype_post in Hp. destruct (nth_error (s_rgs S) i); [|discriminate].
    destruct (retype_ok _ _ _ _); [|discriminate]. injection Hp as <-. reflexivity.
  - destruct (f S) as [i|]; [|discriminate]. injection Hp as <-.
    split; [exact (den_rgs_front ASEGS LIMIT model0 mem0 E S M ms model i Hd) | reflexivity].
Qed.
End Den.
