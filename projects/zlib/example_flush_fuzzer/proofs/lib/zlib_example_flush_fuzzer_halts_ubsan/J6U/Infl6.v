(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvLoop.
From Stdlib Require Import NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.Riscv Require Import Decode.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvApi.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvCall.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import HarnessKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6c.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6d.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import UpdWin6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateRc.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateCall.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflLoop6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import Callee6i.

Module InflLv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarb.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvLoop.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope am_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition pk5 (w : iw) : Z * Z * Z * Z * Z :=
  (is_check (w_s w), is_wrap (w_s w), is_flags (w_s w), ir_out (w_r w), ir_left (w_r w)).
Definition ol (w : iw) : Z * Z := (ir_out (w_r w), ir_left (w_r w)).
Definition eqo (w : iw) : Prop := ir_out (w_r w) = ir_left (w_r w).
Definition LVR (w w' : iw) : Prop := eqo w' \/ pk5 w' = pk5 w.

Lemma LVR_trans : forall w1 w2 w3, LVR w1 w2 -> LVR w2 w3 -> LVR w1 w3.
Proof.
  intros w1 w2 w3 [A|A] [B|B]; try (left; exact B).
  - left. unfold eqo, pk5 in *. congruence.
  - right. congruence.
Qed.
Lemma eqo_of_ol : forall w w', ol w' = ol w -> eqo w -> eqo w'.
Proof. intros w w' E H. unfold ol, eqo in *. congruence. Qed.
Lemma LVR_eqo : forall w w', eqo w -> LVR w w' -> eqo w'.
Proof. intros w w' H [A|A]; [exact A|]. unfold eqo, pk5 in *. congruence. Qed.

Definition KP {A} (m : AM A) : Prop :=
  forall w, match m w with ARun _ w' => pk5 w' = pk5 w | ALeave w' => pk5 w' = pk5 w | ARet _ _ => True end.
Definition KO {A} (m : AM A) : Prop :=
  forall w, match m w with ARun _ w' => ol w' = ol w | ALeave w' => ol w' = ol w | ARet _ _ => True end.
Definition GD {A} (m : AM A) : Prop :=
  forall w, match m w with ARun _ w' => LVR w w' | ALeave w' => LVR w w' | ARet _ _ => True end.
Definition GE {A} (m : AM A) : Prop :=
  forall w, match m w with ARun _ w' => eqo w' | ALeave w' => eqo w' | ARet _ _ => True end.
Definition NL {A} (m : AM A) : Prop := forall w w', m w <> ALeave w'.
Definition LV {A} (m : AM A) : Prop := forall w w', m w = ALeave w' -> LVR w w'.
Definition LE {A} (m : AM A) : Prop := forall w w', eqo w -> m w = ALeave w' -> eqo w'.

Lemma KO_of_KP : forall {A} (m : AM A), KP m -> KO m.
Proof. intros A m H w. specialize (H w). unfold pk5, ol in *. destruct (m w); [congruence|congruence|exact I]. Qed.
Lemma GD_of_KP : forall {A} (m : AM A), KP m -> GD m.
Proof. intros A m H w. specialize (H w). destruct (m w); [right; exact H|right; exact H|exact I]. Qed.
Lemma GD_of_GE : forall {A} (m : AM A), GE m -> GD m.
Proof. intros A m H w. specialize (H w). destruct (m w); [left; exact H|left; exact H|exact I]. Qed.
Lemma LV_of_GD : forall {A} (m : AM A), GD m -> LV m.
Proof. intros A m H w w' E. specialize (H w). rewrite E in H. exact H. Qed.
Lemma LV_of_KP : forall {A} (m : AM A), KP m -> LV m.
Proof. intros A m H. apply LV_of_GD, GD_of_KP, H. Qed.
Lemma LV_of_NL : forall {A} (m : AM A), NL m -> LV m.
Proof. intros A m H w w' E. exfalso. exact (H w w' E). Qed.
Lemma LE_of_KO : forall {A} (m : AM A), KO m -> LE m.
Proof. intros A m H w w' He E. specialize (H w). rewrite E in H. exact (eqo_of_ol w w' H He). Qed.
Lemma LE_of_LV : forall {A} (m : AM A), LV m -> LE m.
Proof. intros A m H w w' He E. exact (LVR_eqo w w' He (H w w' E)). Qed.
Lemma LE_of_NL : forall {A} (m : AM A), NL m -> LE m.
Proof. intros A m H w w' He E. exfalso. exact (H w w' E). Qed.

Lemma KP_bind : forall {A B} (m : AM A) (f : A -> AM B), KP m -> (forall a, KP (f a)) -> KP (abind m f).
Proof.
  intros A B m f Hm Hf w. unfold abind. specialize (Hm w). destruct (m w) as [a w'|w'|rc w']; [| exact Hm | exact I].
  specialize (Hf a w'). destruct (f a w'); congruence.
Qed.
Lemma KO_bind : forall {A B} (m : AM A) (f : A -> AM B), KO m -> (forall a, KO (f a)) -> KO (abind m f).
Proof.
  intros A B m f Hm Hf w. unfold abind. specialize (Hm w). destruct (m w) as [a w'|w'|rc w']; [| exact Hm | exact I].
  specialize (Hf a w'). destruct (f a w'); congruence.
Qed.
Lemma GD_bind : forall {A B} (m : AM A) (f : A -> AM B), GD m -> (forall a, GD (f a)) -> GD (abind m f).
Proof.
  intros A B m f Hm Hf w. unfold abind. specialize (Hm w). destruct (m w) as [a w'|w'|rc w']; [| exact Hm | exact I].
  specialize (Hf a w'). destruct (f a w') as [b w''|w''|rc w'']; [| | exact I]; exact (LVR_trans _ _ _ Hm Hf).
Qed.
Lemma GE_bind1 : forall {A B} (m : AM A) (f : A -> AM B), GE m -> (forall a, KO (f a)) -> GE (abind m f).
Proof.
  intros A B m f Hm Hf w. unfold abind. specialize (Hm w). destruct (m w) as [a w'|w'|rc w']; [| exact Hm | exact I].
  specialize (Hf a w'). destruct (f a w') as [b w''|w''|rc w'']; [| | exact I]; exact (eqo_of_ol _ _ Hf Hm).
Qed.
Lemma GE_bind2 : forall {A B} (m : AM A) (f : A -> AM B), NL m -> (forall a, GE (f a)) -> GE (abind m f).
Proof.
  intros A B m f Hm Hf w. unfold abind. destruct (m w) as [a w'|w'|rc w'] eqn:E; [apply Hf | exact (False_ind _ (Hm w w' E)) | exact I].
Qed.
Lemma NL_bind : forall {A B} (m : AM A) (f : A -> AM B), NL m -> (forall a, NL (f a)) -> NL (abind m f).
Proof.
  intros A B m f Hm Hf w w'. unfold abind. destruct (m w) as [a w1|w1|rc w1] eqn:E; [apply Hf | intros X; exact (Hm w w1 E) | discriminate].
Qed.
Lemma LV_bindG : forall {A B} (m : AM A) (f : A -> AM B), GD m -> (forall a, LV (f a)) -> LV (abind m f).
Proof.
  intros A B m f Hm Hf w w' E. unfold abind in E. specialize (Hm w). destruct (m w) as [a w1|w1|rc w1]; [| | discriminate].
  - exact (LVR_trans _ _ _ Hm (Hf a w1 w' E)).
  - injection E as <-. exact Hm.
Qed.
Lemma LV_bindN : forall {A B} (m : AM A) (f : A -> AM B), LV m -> (forall a, NL (f a)) -> LV (abind m f).
Proof.
  intros A B m f Hm Hf w w' E. unfold abind in E. destruct (m w) as [a w1|w1|rc w1] eqn:Em; [| | discriminate].
  - exfalso. exact (Hf a w1 w' E).
  - injection E as <-. exact (Hm w w1 Em).
Qed.
Lemma LE_bind : forall {A B} (m : AM A) (f : A -> AM B), KO m -> (forall a, LE (f a)) -> LE (abind m f).
Proof.
  intros A B m f Hm Hf w w' He E. unfold abind in E. specialize (Hm w). destruct (m w) as [a w1|w1|rc w1]; [| | discriminate].
  - exact (Hf a w1 w' (eqo_of_ol _ _ Hm He) E).
  - injection E as <-. exact (eqo_of_ol _ _ Hm He).
Qed.
Lemma KP_if : forall {A} (b : bool) (m1 m2 : AM A), KP m1 -> KP m2 -> KP (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
Lemma KO_if : forall {A} (b : bool) (m1 m2 : AM A), KO m1 -> KO m2 -> KO (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
Lemma GD_if : forall {A} (b : bool) (m1 m2 : AM A), GD m1 -> GD m2 -> GD (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
Lemma GE_if : forall {A} (b : bool) (m1 m2 : AM A), GE m1 -> GE m2 -> GE (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
Lemma NL_if : forall {A} (b : bool) (m1 m2 : AM A), NL m1 -> NL m2 -> NL (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
Lemma LV_if : forall {A} (b : bool) (m1 m2 : AM A), LV m1 -> LV m2 -> LV (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
Lemma LE_if : forall {A} (b : bool) (m1 m2 : AM A), LE m1 -> LE m2 -> LE (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.

Lemma KP_aret : forall {A} (a : A), KP (aret a). Proof. intros A a w; reflexivity. Qed.
Lemma KP_gs : forall {A} (f : inflate_state -> A), KP (gs f). Proof. intros A f w; reflexivity. Qed.
Lemma KP_gc : forall {A} (f : icall -> A), KP (gc f). Proof. intros A f w; reflexivity. Qed.
Lemma KP_gr : forall {A} (f : iregs -> A), KP (gr f). Proof. intros A f w; reflexivity. Qed.
Lemma KP_agets : forall {A} (f : iw -> A), KP (agets f). Proof. intros A f w; reflexivity. Qed.
Lemma KP_aget : KP aget. Proof. intros w; reflexivity. Qed.
Lemma KP_uc : forall f, KP (uc f). Proof. intros f w; reflexivity. Qed.
Lemma KP_us : forall f,
  (forall s, is_check (f s) = is_check s /\ is_wrap (f s) = is_wrap s /\ is_flags (f s) = is_flags s) -> KP (us f).
Proof. intros f H w. unfold us, pk5. cbn. destruct (H (w_s w)) as (-> & -> & ->). reflexivity. Qed.
Lemma KP_ur : forall f, (forall r, ir_out (f r) = ir_out r /\ ir_left (f r) = ir_left r) -> KP (ur f).
Proof. intros f H w. unfold ur, pk5. cbn. destruct (H (w_r w)) as (-> & ->). reflexivity. Qed.
Lemma KP_aleave : forall {A}, KP (@aleave A). Proof. intros A w; reflexivity. Qed.
Lemma KP_areturn : forall {A} rc, KP (@areturn A rc). Proof. intros A rc w; exact I. Qed.
Lemma KP_fun_run : forall {A} (g : iw -> A), KP (fun w => ARun (g w) w). Proof. intros A g w; reflexivity. Qed.
Lemma KP_PULLBYTE : KP PULLBYTE.
Proof. intros w. unfold PULLBYTE. destruct (ir_have (w_r w) =? 0); [reflexivity|]. unfold pk5; cbn. destruct (w_r w); reflexivity. Qed.
Lemma KP_NEEDBITS_k : forall k n, KP (NEEDBITS_k k n).
Proof.
  induction k as [|k IH]; intros n; cbn [NEEDBITS_k]; [apply KP_aret|].
  apply KP_bind; [apply KP_gr|]. intros b. apply KP_if; [| apply KP_aret].
  apply KP_bind; [apply KP_PULLBYTE | intros ?; apply IH].
Qed.
Lemma KP_NEEDBITS : forall n, KP (NEEDBITS n). Proof. intros n. apply KP_NEEDBITS_k. Qed.
Lemma KP_BITS : forall n, KP (BITS n). Proof. intros n. apply KP_gr. Qed.
Lemma KP_HOLD : KP HOLD. Proof. apply KP_gr. Qed.
Lemma KP_DROPBITS : forall n, KP (DROPBITS n). Proof. intros n. apply KP_ur. intros []; split; reflexivity. Qed.
Lemma KP_INITBITS : KP INITBITS. Proof. apply KP_ur. intros []; split; reflexivity. Qed.
Lemma KP_BYTEBITS : KP BYTEBITS. Proof. apply KP_ur. intros []; split; reflexivity. Qed.
Lemma KP_set_mode : forall m, KP (set_mode m). Proof. intros m. apply KP_us. intros []; repeat split; reflexivity. Qed.
Lemma KP_set_msg : forall m, KP (set_msg m). Proof. intros m. apply KP_uc. Qed.
Lemma KP_go_bad : forall m, KP (go_bad m).
Proof. intros m. unfold go_bad. apply KP_bind; [apply KP_set_msg | intros ?; apply KP_set_mode]. Qed.
Lemma KP_set_lens : forall i v, KP (set_lens i v). Proof. intros i v. apply KP_us. intros []; repeat split; reflexivity. Qed.
Lemma KP_lens_repeat : forall copy len, KP (lens_repeat copy len).
Proof. intros copy len. apply KP_us. intros s. unfold lens_repeat. destruct (loopZ _ _ _) as [[lens have] x]. destruct s; repeat split; reflexivity. Qed.
Lemma KP_DECODE_k : forall k p index need, KP (DECODE_k k p index need).
Proof.
  induction k as [|k IH]; intros p index need; cbn [DECODE_k].
  - apply KP_bind; [apply KP_HOLD | intros h; apply KP_gs].
  - apply KP_bind; [apply KP_HOLD | intros h]. apply KP_bind; [apply KP_gr | intros b]. apply KP_bind; [apply KP_gs | intros here].
    apply KP_if; [apply KP_aret|]. apply KP_bind; [apply KP_PULLBYTE | intros ?; apply IH].
Qed.
Lemma KP_DECODE1 : forall p n, KP (DECODE1 p n). Proof. intros. apply KP_DECODE_k. Qed.
Lemma KP_DECODE2 : forall p l, KP (DECODE2 p l). Proof. intros. apply KP_DECODE_k. Qed.
Lemma KP_aux : forall iv f,
  (forall s, is_check (f s) = is_check s /\ is_wrap (f s) = is_wrap s /\ is_flags (f s) = is_flags s) -> KP (aux iv f).
Proof. intros iv f H. unfold aux. destruct (iv_aux iv); [apply KP_us; exact H | apply KP_aret]. Qed.
Lemma KP_set_back : forall iv v, KP (set_back iv v). Proof. intros iv v. apply KP_aux. intros []; repeat split; reflexivity. Qed.
Lemma KP_add_back : forall iv v, KP (add_back iv v). Proof. intros iv v. apply KP_aux. intros []; repeat split; reflexivity. Qed.

Lemma KO_us : forall f, KO (us f). Proof. intros f w; reflexivity. Qed.
Lemma KO_uc : forall f, KO (uc f). Proof. intros f w; reflexivity. Qed.
Lemma KO_ur : forall f, (forall r, ir_out (f r) = ir_out r /\ ir_left (f r) = ir_left r) -> KO (ur f).
Proof. intros f H w. unfold ur, ol. cbn. destruct (H (w_r w)) as (-> & ->). reflexivity. Qed.
Lemma KO_amodify : forall F, (forall w, w_r (F w) = w_r w) -> KO (amodify F).
Proof. intros F H w. unfold amodify, ol. rewrite H. reflexivity. Qed.
Lemma KO_RESTORE : KO (amodify RESTORE). Proof. apply KO_amodify. intros w; reflexivity. Qed.
Lemma KO_crc_input : forall copy, KO (crc_input copy). Proof. intros copy w; reflexivity. Qed.
Lemma KO_CRC2 : forall v, KO (CRC2 v). Proof. intros v. apply KO_us. Qed.
Lemma KO_CRC4 : forall v, KO (CRC4 v). Proof. intros v. apply KO_us. Qed.
Lemma KO_set_adler_check : forall v, KO (set_adler_check v).
Proof. intros v. unfold set_adler_check. apply KO_bind; [apply KO_us | intros ?; apply KO_uc]. Qed.
Lemma KO_aux : forall iv f, KO (aux iv f).
Proof. intros iv f. unfold aux. destruct (iv_aux iv); [apply KO_us | apply KO_of_KP, KP_aret]. Qed.

Lemma GE_outleft : GE (ur (fun r => irset_out r (ir_left r))).
Proof. intros w. unfold ur, eqo. cbn. destruct (w_r w); reflexivity. Qed.

Lemma NL_aret : forall {A} (a : A), NL (aret a). Proof. intros A a w w' X; discriminate X. Qed.
Lemma NL_gs : forall {A} (f : inflate_state -> A), NL (gs f). Proof. intros A f w w' X; discriminate X. Qed.
Lemma NL_gc : forall {A} (f : icall -> A), NL (gc f). Proof. intros A f w w' X; discriminate X. Qed.
Lemma NL_gr : forall {A} (f : iregs -> A), NL (gr f). Proof. intros A f w w' X; discriminate X. Qed.
Lemma NL_agets : forall {A} (f : iw -> A), NL (agets f). Proof. intros A f w w' X; discriminate X. Qed.
Lemma NL_aget : NL aget. Proof. intros w w' X; discriminate X. Qed.
Lemma NL_us : forall f, NL (us f). Proof. intros f w w' X; discriminate X. Qed.
Lemma NL_uc : forall f, NL (uc f). Proof. intros f w w' X; discriminate X. Qed.
Lemma NL_ur : forall f, NL (ur f). Proof. intros f w w' X; discriminate X. Qed.
Lemma NL_amodify : forall F, NL (amodify F). Proof. intros F w w' X; discriminate X. Qed.
Lemma NL_areturn : forall {A} rc, NL (@areturn A rc). Proof. intros A rc w w' X; discriminate X. Qed.
Lemma NL_set_mode : forall m, NL (set_mode m). Proof. intros m. apply NL_us. Qed.
Lemma NL_set_msg : forall m, NL (set_msg m). Proof. intros m. apply NL_uc. Qed.
Lemma NL_go_bad : forall m, NL (go_bad m).
Proof. intros m. unfold go_bad. apply NL_bind; [apply NL_set_msg | intros ?; apply NL_set_mode]. Qed.
Lemma NL_set_adler_check : forall v, NL (set_adler_check v).
Proof. intros v. unfold set_adler_check. apply NL_bind; [apply NL_us | intros ?; apply NL_uc]. Qed.
Lemma NL_DROPBITS : forall n, NL (DROPBITS n). Proof. intros n. apply NL_ur. Qed.
Lemma NL_INITBITS : NL INITBITS. Proof. apply NL_ur. Qed.
Lemma NL_BYTEBITS : NL BYTEBITS. Proof. apply NL_ur. Qed.
Lemma NL_BITS : forall n, NL (BITS n). Proof. intros n. apply NL_gr. Qed.
Lemma NL_HOLD : NL HOLD. Proof. apply NL_gr. Qed.
Lemma NL_CRC2 : forall v, NL (CRC2 v). Proof. intros v. apply NL_us. Qed.
Lemma NL_CRC4 : forall v, NL (CRC4 v). Proof. intros v. apply NL_us. Qed.
Lemma NL_aux : forall iv f, NL (aux iv f). Proof. intros iv f. unfold aux. destruct (iv_aux iv); [apply NL_us | apply NL_aret]. Qed.
Lemma NL_set_back : forall iv v, NL (set_back iv v). Proof. intros iv v. apply NL_aux. Qed.
Lemma NL_add_back : forall iv v, NL (add_back iv v). Proof. intros iv v. apply NL_aux. Qed.
Lemma NL_match_copy_step : forall from copy,
  NL (fun w => let '(ob, put, _, _) := match_copy (is_window (w_s w)) (ic_outbuf (w_c w), ir_put (w_r w), from, copy) in
               ARun tt (wset_r (wset_c w (icset_outbuf (w_c w) ob)) (irset_put (w_r w) put))).
Proof. intros from copy w w'. cbv beta. destruct (match_copy _ _) as [[[ob put] x3] x4]. intros X; discriminate X. Qed.
Lemma NL_fun_run : forall {A} (g : iw -> A), NL (fun w => ARun (g w) w).
Proof. intros A g w w' X; discriminate X. Qed.

End FXG.
Create HintDb lvdb discriminated.
#[export] Hint Resolve KP_aret KP_gs KP_gc KP_gr KP_agets KP_aget KP_uc KP_aleave KP_areturn KP_fun_run KP_PULLBYTE KP_NEEDBITS_k
  KP_NEEDBITS KP_BITS KP_HOLD KP_DROPBITS KP_INITBITS KP_BYTEBITS KP_set_mode KP_set_msg KP_go_bad KP_set_lens KP_lens_repeat
  KP_DECODE_k KP_DECODE1 KP_DECODE2 KP_set_back KP_add_back : lvdb.
#[export] Hint Resolve KO_us KO_uc KO_RESTORE KO_crc_input KO_CRC2 KO_CRC4 KO_set_adler_check KO_aux : lvdb.
#[export] Hint Resolve GE_outleft : lvdb.
#[export] Hint Resolve NL_aret NL_gs NL_gc NL_gr NL_agets NL_aget NL_us NL_uc NL_ur NL_amodify NL_areturn NL_set_mode NL_set_msg
  NL_go_bad NL_set_adler_check NL_DROPBITS NL_INITBITS NL_BYTEBITS NL_BITS NL_HOLD NL_CRC2 NL_CRC4 NL_aux NL_set_back NL_add_back
  NL_match_copy_step NL_fun_run : lvdb.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac kp1 :=
  lazymatch goal with
  | |- KP (abind _ _) => apply KP_bind; [ | intros ? ]
  | |- KP (if _ then _ else _) => apply KP_if
  | |- KP (match ?x with _ => _ end) => destruct x
  | |- KP (us _) => apply KP_us; intros []; repeat split; reflexivity
  | |- KP (aux _ _) => apply KP_aux; intros []; repeat split; reflexivity
  | |- KP (ur _) => apply KP_ur; intros []; split; reflexivity
  | |- KP _ => solve [auto 2 with lvdb nocore]
  end.
Ltac kpcrush := repeat kp1.
Ltac nl1 :=
  lazymatch goal with
  | |- NL (abind _ _) => apply NL_bind; [ | intros ? ]
  | |- NL (if _ then _ else _) => apply NL_if
  | |- NL (match ?x with _ => _ end) => destruct x
  | |- NL _ => solve [auto 2 with lvdb nocore]
  end.
Ltac nlcrush := repeat nl1.
Ltac ko1 :=
  lazymatch goal with
  | |- KO (abind _ _) => apply KO_bind; [ | intros ? ]
  | |- KO (if _ then _ else _) => apply KO_if
  | |- KO (match ?x with _ => _ end) => destruct x
  | |- KO (ur _) => apply KO_ur; intros []; split; reflexivity
  | |- KO _ => first [ solve [auto 2 with lvdb nocore] | apply KO_of_KP; solve [kpcrush] ]
  end.
Ltac kocrush := repeat ko1.
Ltac ge1 :=
  lazymatch goal with
  | |- GE (abind _ _) => first [ apply GE_bind1; [ solve [auto 2 with lvdb nocore] | intros ?; solve [kocrush] ]
                               | apply GE_bind2; [ solve [nlcrush] | intros ? ] ]
  | |- GE (if _ then _ else _) => apply GE_if
  | |- GE (match ?x with _ => _ end) => destruct x
  | |- GE _ => solve [auto 2 with lvdb nocore]
  end.
Ltac gecrush := repeat ge1.
Ltac gd1 :=
  lazymatch goal with
  | |- GD (abind _ _) => first [ apply GD_bind; [ solve [repeat gd1] | intros ? ] | apply GD_of_GE; solve [gecrush] ]
  | |- GD (if _ then _ else _) => apply GD_if
  | |- GD (match ?x with _ => _ end) => destruct x
  | |- GD _ => first [ apply GD_of_KP; solve [kpcrush] | apply GD_of_GE; solve [gecrush] | solve [auto 2 with lvdb nocore] ]
  end.
Ltac gdcrush := repeat gd1.
Ltac lv1 :=
  lazymatch goal with
  | |- LV (abind _ _) =>
      first [ apply LV_bindG; [ solve [gdcrush] | intros ? ]
            | apply LV_bindN; [ | intros ?; solve [nlcrush] ]
            | apply LV_of_NL; solve [nlcrush] ]
  | |- LV (if _ then _ else _) => apply LV_if
  | |- LV (match ?x with _ => _ end) => destruct x
  | |- LV _ => first [ solve [auto 2 with lvdb nocore] | apply LV_of_KP; solve [kpcrush] | apply LV_of_NL; solve [nlcrush] ]
  end.
Ltac lvcrush := repeat lv1.
Ltac le1 :=
  lazymatch goal with
  | |- LE (abind _ _) =>
      first [ apply LE_bind; [ solve [kocrush] | intros ? ]
            | apply LE_of_LV; solve [lvcrush]
            | apply LE_of_NL; solve [nlcrush] ]
  | |- LE (if _ then _ else _) => apply LE_if
  | |- LE (match ?x with _ => _ end) => destruct x
  | |- LE _ => first [ solve [auto 2 with lvdb nocore] | apply LE_of_KO; solve [kocrush] | apply LE_of_LV; solve [lvcrush]
                     | apply LE_of_NL; solve [nlcrush] ]
  end.
Ltac lecrush := repeat le1.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section Arms.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma KP_codelens_body : KP codelens_body.
  Proof. unfold codelens_body. kpcrush. Qed.
  Lemma KP_codelens_while : forall k, KP (codelens_while k).
  Proof.
    induction k as [|k IH]; cbn [codelens_while]; [apply KP_aret|].
    apply KP_bind; [apply KP_gs | intros s]. apply KP_if; [| apply KP_aret].
    apply KP_bind; [apply KP_codelens_body | intros c]. apply KP_if; [exact IH | apply KP_aret].
  Qed.
  Lemma KP_lenlens_while1 : forall k, KP (lenlens_while1 k).
  Proof.
    induction k as [|k IH]; cbn [lenlens_while1]; [apply KP_aret|].
    apply KP_bind; [apply KP_gs | intros s]. apply KP_if; [| apply KP_aret]. kpcrush.
  Qed.
  Lemma KP_lenlens_while2 : forall k, KP (lenlens_while2 k).
  Proof.
    induction k as [|k IH]; cbn [lenlens_while2]; [apply KP_aret|].
    apply KP_bind; [apply KP_gs | intros s]. apply KP_if; [| apply KP_aret]. kpcrush.
  Qed.
  Lemma KO_name_like : forall flag, KO (name_like flag).
  Proof. intros flag. unfold name_like. kocrush. Qed.
  Hint Resolve KP_codelens_body KP_codelens_while KP_lenlens_while1 KP_lenlens_while2 KO_name_like : lvdb.

  Lemma lv_DONE : LV (arm_DONE). Proof. unfold arm_DONE. lvcrush. Qed.
  Lemma kp_LENGTH : KP (arm_LENGTH). Proof. unfold arm_LENGTH. kpcrush. Qed.
  Hint Resolve kp_LENGTH : lvdb.
  Lemma lv_LENGTH : LV (arm_LENGTH). Proof. apply LV_of_KP. apply kp_LENGTH. Qed.
  Lemma lv_CHECK : LV arm_CHECK. Proof. unfold arm_CHECK. lvcrush. Qed.
  Lemma lv_LIT : LV (arm_LIT). Proof. unfold arm_LIT. lvcrush. Qed.
  Lemma lv_MATCH : LV (arm_MATCH iv). Proof. unfold arm_MATCH. lvcrush. Qed.
  Hint Resolve lv_MATCH : lvdb.
  Lemma lv_DISTEXT : LV (arm_DISTEXT iv). Proof. unfold arm_DISTEXT. lvcrush. Qed.
  Hint Resolve lv_DISTEXT : lvdb.
  Lemma lv_DIST : LV (arm_DIST iv). Proof. unfold arm_DIST. lvcrush. Qed.
  Hint Resolve lv_DIST : lvdb.
  Lemma lv_LENEXT : LV (arm_LENEXT iv). Proof. unfold arm_LENEXT. lvcrush. Qed.
  Hint Resolve lv_LENEXT : lvdb.
  Lemma lv_LEN : LV (arm_LEN iv). Proof. unfold arm_LEN. lvcrush. Qed.
  Hint Resolve lv_LEN : lvdb.
  Lemma lv_LEN_ : LV (arm_LEN_ iv). Proof. unfold arm_LEN_. lvcrush. Qed.
  Hint Resolve lv_LEN_ : lvdb.
  Lemma lv_CODELENS : LV (arm_CODELENS iv flush). Proof. unfold arm_CODELENS. lvcrush. Qed.
  Hint Resolve lv_CODELENS : lvdb.
  Lemma lv_LENLENS : LV (arm_LENLENS iv flush). Proof. unfold arm_LENLENS. lvcrush. Qed.
  Hint Resolve lv_LENLENS : lvdb.
  Lemma lv_TABLE : LV (arm_TABLE iv flush). Proof. unfold arm_TABLE. lvcrush. Qed.
  Lemma lv_COPY : LV (arm_COPY). Proof. unfold arm_COPY. lvcrush. Qed.
  Hint Resolve lv_COPY : lvdb.
  Lemma lv_COPY_ : LV (arm_COPY_). Proof. unfold arm_COPY_. lvcrush. Qed.
  Hint Resolve lv_COPY_ : lvdb.
  Lemma lv_STORED : LV (arm_STORED iv flush). Proof. unfold arm_STORED. lvcrush. Qed.
  Lemma kp_TYPEDO : KP (arm_TYPEDO iv flush). Proof. unfold arm_TYPEDO. kpcrush. Qed.
  Hint Resolve kp_TYPEDO : lvdb.
  Lemma kp_TYPE : KP (arm_TYPE iv flush). Proof. unfold arm_TYPE. kpcrush. Qed.
  Hint Resolve kp_TYPE : lvdb.
  Lemma lv_TYPEDO : LV (arm_TYPEDO iv flush). Proof. apply LV_of_KP, kp_TYPEDO. Qed.
  Lemma lv_TYPE : LV (arm_TYPE iv flush). Proof. apply LV_of_KP, kp_TYPE. Qed.
  Lemma lv_BAD : LV (arm_BAD). Proof. unfold arm_BAD. lvcrush. Qed.
  Lemma lv_MEM : LV (arm_MEM). Proof. unfold arm_MEM. lvcrush. Qed.
  Lemma lv_SYNC : LV (arm_SYNC). Proof. unfold arm_SYNC. lvcrush. Qed.

  Lemma ko_HCRC : KO (arm_HCRC). Proof. unfold arm_HCRC. kocrush. Qed.
  Hint Resolve ko_HCRC : lvdb.
  Lemma ko_COMMENT : KO (arm_COMMENT). Proof. unfold arm_COMMENT. kocrush. Qed.
  Hint Resolve ko_COMMENT : lvdb.
  Lemma ko_NAME : KO (arm_NAME). Proof. unfold arm_NAME. kocrush. Qed.
  Hint Resolve ko_NAME : lvdb.
  Lemma ko_EXTRA : KO (arm_EXTRA). Proof. unfold arm_EXTRA. kocrush. Qed.
  Hint Resolve ko_EXTRA : lvdb.
  Lemma ko_EXLEN : KO (arm_EXLEN). Proof. unfold arm_EXLEN. kocrush. Qed.
  Hint Resolve ko_EXLEN : lvdb.
  Lemma ko_OS : KO (arm_OS). Proof. unfold arm_OS. kocrush. Qed.
  Hint Resolve ko_OS : lvdb.
  Lemma ko_TIME : KO (arm_TIME). Proof. unfold arm_TIME. kocrush. Qed.
  Hint Resolve ko_TIME : lvdb.
  Lemma ko_FLAGS : KO (arm_FLAGS). Proof. unfold arm_FLAGS. kocrush. Qed.
  Hint Resolve ko_FLAGS : lvdb.
  Lemma ko_HEAD : KO (arm_HEAD iv). Proof. unfold arm_HEAD. kocrush. Qed.
  Lemma ko_DICT : KO (arm_DICT iv flush). Proof. unfold arm_DICT. kocrush. Qed.
  Hint Resolve ko_DICT : lvdb.
  Lemma ko_DICTID : KO (arm_DICTID iv flush). Proof. unfold arm_DICTID. kocrush. Qed.

  Hint Resolve lv_DONE lv_LENGTH lv_CHECK lv_LIT lv_TABLE lv_STORED lv_TYPEDO lv_TYPE lv_BAD lv_MEM lv_SYNC : lvdb.
  Hint Resolve ko_HEAD ko_DICTID : lvdb.

  Ltac mode_le := cbv; discriminate.

  Theorem dispatch_leave : forall w w',
    (is_mode (w_s w) <= DICT -> eqo w) ->
    dispatch iv flush w = ALeave w' -> LVR w w'.
  Proof.
    intros w w' Heq. cbn [dispatch abind gs].
    repeat lazymatch goal with
      | |- (if is_mode (w_s w) =? ?c then _ else _) w = _ -> _ => destruct (Z.eqb_spec (is_mode (w_s w)) c) as [?Em|?Nm]
      end.
    all: intros E.
    all: first [ refine ((_ : LV _) w w' E); solve [auto 2 with lvdb nocore]
               | left; refine (LE_of_KO _ (_ : KO _) w w' (Heq _) E); [solve [auto 2 with lvdb nocore] | rewrite Em; mode_le] ].
  Qed.
End Arms.

Section LoopCk.
  Variables (iv : ivariant) (flush NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Abbreviation pinv := (pinv NI NO WN TOT0).

  Definition CKA (w : iw) : Prop :=
    ir_out (w_r w) <> ir_left (w_r w) -> Z.land (is_wrap (w_s w)) 4 <> 0 -> is_flags (w_s w) = 0 -> ck_adl (is_check (w_s w)).

  Lemma CKA_of_pinv : forall w, pinv w -> CKA w.
  Proof.
    intros w (_ & _ & _ & _ & _ & CI). unfold cinv in CI. destruct CI as (_ & _ & _ & H & _).
    intros A B C. apply H; [| exact B | exact C]. intros X; apply A; symmetry; exact X.
  Qed.
  Lemma eqo_of_pinv : forall w, pinv w -> is_mode (w_s w) <= DICT -> eqo w.
  Proof. intros w (_ & _ & _ & _ & _ & CI) Hm. unfold cinv in CI. destruct CI as (_ & H & _). exact (H Hm). Qed.
  Lemma CKA_LVR : forall w w', CKA w -> LVR w w' -> CKA w'.
  Proof.
    intros w w' H [E|E].
    - intros A; exfalso; exact (A E).
    - unfold pk5 in E. injection E as E1 E2 E3 E4 E5. unfold CKA in *. rewrite E1, E2, E3, E4, E5. exact H.
  Qed.

  Theorem inf_loop_leave : forall w w', pinv w -> inf_loop iv flush w = (SLeave, w') -> CKA w'.
  Proof.
    intros w w' PI. rewrite (inf_loop_iter iv flush). generalize (Z.to_nat (gfuel w)) as n. intros n. revert w w' PI.
    induction n as [|n IH]; intros w w' PI E.
    - cbn in E. injection E as <-. exact (CKA_of_pinv w PI).
    - rewrite iterK_gstep_S in E. destruct (dispatch_ok iv flush NI NO WN TOT0 NI32 NO32 w PI) as [_ A].
      destruct (dispatch iv flush w) as [u w1|w1|rc w1] eqn:ED; cbn [apost] in A.
      + exact (IH w1 w' (proj1 A) E).
      + injection E as <-. exact (CKA_LVR w w1 (CKA_of_pinv w PI) (dispatch_leave iv flush w w1 (eqo_of_pinv w PI) ED)).
      + discriminate E.
  Qed.
End LoopCk.
End FXG.
End InflLv.
Export InflLv.

Module Infl6A.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvApi.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvCall.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.HarnessKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.HarnessFacts.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Callee6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma zrange : forall (P : Z -> Prop) (lo : Z) (n : nat),
  (forall i : nat, (i < n)%nat -> P (lo + Z.of_nat i)) -> forall m, lo <= m < lo + Z.of_nat n -> P m.
Proof.
  intros P lo n H m Hm. replace m with (lo + Z.of_nat (Z.to_nat (m - lo))) by lia. apply H. lia.
Qed.

Lemma mod16_mod8 : forall a, a mod 16 = 0 -> a mod 2 ^ 3 = 0.
Proof.
  intros a H. change (2 ^ 3) with 8. apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. subst a.
  replace (k * 16) with ((k * 2) * 8) by lia. apply Z.mod_mul. lia.
Qed.
End FXG.
Ltac ub_align_side :=
  lazymatch goal with
  | |- ?a mod 2 ^ 3 = 0 => first [change (2 ^ 3) with 8; lia | apply mod16_mod8; lia]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma saved_slots_bv : forall (P : reg -> Z -> Prop),
  P 1%bv 248 -> P 8%bv 240 -> P 9%bv 232 -> P 18%bv 224 -> P 19%bv 216 -> P 20%bv 208 -> P 21%bv 200 ->
  P 22%bv 192 -> P 23%bv 184 -> P 24%bv 176 -> P 25%bv 168 -> P 26%bv 160 -> P 27%bv 152 ->
  forall r o, In (r, o) saved_slots -> P (Z_to_bv 5 r) o.
Proof.
  intros P A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 r o Hin. cbn in Hin.
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin as <- <-;
      lazymatch goal with |- P (Z_to_bv 5 ?k) _ =>
        first [ replace (Z_to_bv 5 k : reg) with (1%bv : reg) by (apply bv_eq; reflexivity); exact A1
              | replace (Z_to_bv 5 k : reg) with (8%bv : reg) by (apply bv_eq; reflexivity); exact A2
              | replace (Z_to_bv 5 k : reg) with (9%bv : reg) by (apply bv_eq; reflexivity); exact A3
              | replace (Z_to_bv 5 k : reg) with (18%bv : reg) by (apply bv_eq; reflexivity); exact A4
              | replace (Z_to_bv 5 k : reg) with (19%bv : reg) by (apply bv_eq; reflexivity); exact A5
              | replace (Z_to_bv 5 k : reg) with (20%bv : reg) by (apply bv_eq; reflexivity); exact A6
              | replace (Z_to_bv 5 k : reg) with (21%bv : reg) by (apply bv_eq; reflexivity); exact A7
              | replace (Z_to_bv 5 k : reg) with (22%bv : reg) by (apply bv_eq; reflexivity); exact A8
              | replace (Z_to_bv 5 k : reg) with (23%bv : reg) by (apply bv_eq; reflexivity); exact A9
              | replace (Z_to_bv 5 k : reg) with (24%bv : reg) by (apply bv_eq; reflexivity); exact A10
              | replace (Z_to_bv 5 k : reg) with (25%bv : reg) by (apply bv_eq; reflexivity); exact A11
              | replace (Z_to_bv 5 k : reg) with (26%bv : reg) by (apply bv_eq; reflexivity); exact A12
              | replace (Z_to_bv 5 k : reg) with (27%bv : reg) by (apply bv_eq; reflexivity); exact A13 ]
      end
    |]).
  destruct Hin.
Qed.


Section Call.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition LXS (s : inflate_state) : Prop :=
    (is_wrap s = 5 \/ is_wrap s = 1) /\ is_wbits s = 15 /\ live_mode (is_mode s)
    /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD)))
    /\ is_havedict s = 0
    /\ bk_ok (is_mode s) (is_back s).

  Record CMEM (s : inflate_state) (c : icall) (M : word -> option byte) : Prop := CM {
    cm_rod : rod6_clear M;
    cm_sc : is6_scalars M (cv_S v) (ISP (cv_ZP v) (cv_WB v)) s;
    cm_lens : cells s6u_segs M (cv_S v + 168) 2 2 320 (arr_get (is_lens s));
    cm_work : cells s6u_segs M (cv_S v + 808) 2 2 288 (arr_get (is_work s));
    cm_codes : cells s6u_segs M (cv_S v + 1384) 4 4 1444 (arr_get (is_codes s));
    cm_win : cv_WN v <> 0 -> cells s6u_segs M (cv_WB v) 1 1 (cv_WN v) (arr_get (is_window s));
    cm_in : cells s6u_segs M (cv_I0 v) 1 1 (cv_NI v) (arr_get (ic_input c));
    cm_out : cells s6u_segs M (cv_P0 v) 1 1 (ic_next_out c) (arr_get (ic_outbuf c));
    cm_zs : izs6 v M c;
    cm_map_f : mapped M (cv_sp v - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH);
    cm_map_Z : mapped M (cv_ZP v) 112;
    cm_map_S : mapped M (cv_S v) 7176;
    cm_map_P : mapped M (cv_P0 v) (cv_NO v);
    cm_map_W : cv_WN v <> 0 -> mapped M (cv_WB v) (cv_WN v) }.

  Lemma LMEM_of_CMEM : forall s c r M,
    CMEM s c M -> iframe6 v M ->
    cell s6u_segs M (cv_sp v - INF_FRAME + 88) 8 (ir_out r) ->
    cell s6u_segs M (cv_sp v - INF_FRAME + 112) 8 (ir_left r) ->
    ir_put r = ic_next_out c -> LMEM v (mkW s c r) M.
  Proof.
    intros s c r M HM HF HO HL Hp. destruct HM. constructor; cbn [w_s w_c w_r]; rewrite ?Hp; assumption.
  Qed.

  Ltac open_cmem HM :=
    pose proof (cm_rod _ _ _ HM) as Mrod; pose proof (cm_sc _ _ _ HM) as Msc; pose proof (cm_lens _ _ _ HM) as Mlens;
    pose proof (cm_work _ _ _ HM) as Mwork; pose proof (cm_codes _ _ _ HM) as Mcodes; pose proof (cm_win _ _ _ HM) as Mwin;
    pose proof (cm_in _ _ _ HM) as Minp; pose proof (cm_out _ _ _ HM) as Mout; pose proof (cm_zs _ _ _ HM) as Mzs;
    pose proof (cm_map_f _ _ _ HM) as Mmap_f; pose proof (cm_map_Z _ _ _ HM) as Mmap_Z; pose proof (cm_map_S _ _ _ HM) as Mmap_S;
    pose proof (cm_map_P _ _ _ HM) as Mmap_P; pose proof (cm_map_W _ _ _ HM) as Mmap_W;
    unfold INF_FRAME, INF_SCRATCH in Mmap_f.

  Lemma CMEM_agree_frame : forall s c M M',
    CMEM s c M -> 0 <= ic_next_out c <= cv_NO v ->
    agree_out [(cv_sp v - INF_FRAME, INF_FRAME)] M M' -> (forall x, M x <> None -> M' x <> None) ->
    CMEM s c M'.
  Proof.
    intros s c M M' HM Hput Hag Hg.
    open_ictx C. open_cmem HM. unfold INF_FRAME in Hag.
    assert (DJ : forall a n, (cv_sp v <= a \/ a + n <= cv_sp v - 256) -> disj_franges [(cv_sp v - 256, 256)] a n).
    { intros a n Ha x Hx [Hin|Hin]; [cbn in Hin; lia | exact Hin]. }
    constructor.
    - intros x Hx. rewrite (Hag x); [exact (Mrod x Hx)|]. intros [Hin|Hin]; [| exact Hin]. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx Hin Csp. lia.
    - unfold is6_scalars in *. eapply (fields_agree_out s6u_segs _ M M' _ is6_layout _ is6_SIZE Msc is6_layout_within Hag); [| lia | unfold is6_SIZE; lia].
      apply DJ. unfold sep in CfS. unfold is6_SIZE. clear - CfS CS. lia.
    - eapply (cells_agree_out s6u_segs _ M M'); [exact Hag | apply DJ; unfold sep in CfS; clear - CfS CS; lia | cbn; lia | lia | lia | exact Mlens].
    - eapply (cells_agree_out s6u_segs _ M M'); [exact Hag | apply DJ; unfold sep in CfS; clear - CfS CS; lia | cbn; lia | lia | lia | exact Mwork].
    - eapply (cells_agree_out s6u_segs _ M M'); [exact Hag | apply DJ; unfold sep in CfS; clear - CfS CS; lia | cbn; lia | lia | lia | exact Mcodes].
    - intros HW. eapply (cells_agree_out s6u_segs _ M M'); [exact Hag | apply DJ; unfold sep in CfW; clear - CfW CWB HW; lia | cbn; lia | lia | lia | exact (Mwin HW)].
    - destruct (Z.eq_dec (cv_NI v) 0) as [E|E].
      + intros i Hi. exfalso. lia.
      + eapply (cells_agree_out s6u_segs _ M M'); [exact Hag | apply DJ; specialize (CfI ltac:(lia)); unfold sep in CfI; clear - CfI CI0 E; lia | cbn; lia | lia | lia | exact Minp].
    - destruct (Z.eq_dec (cv_NO v) 0) as [E|E].
      + intros i Hi. exfalso. lia.
      + eapply (cells_agree_out s6u_segs _ M M'); [exact Hag | apply DJ; specialize (CfP ltac:(lia)); unfold sep in CfP; clear - CfP CP0 E Hput; lia | cbn; lia | lia | lia | exact Mout].
    - eapply (izs6_agree v C _ M M' c Mzs Hag). apply DJ. unfold sep in CfZ. clear - CfZ CZP. lia.
    - intros x Hx. apply Hg. apply Mmap_f. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_Z. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_S. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_P. exact Hx.
    - intros HW x Hx. apply Hg. apply (Mmap_W HW). exact Hx.
  Qed.

  Lemma CMEM_mode : forall s c M m,
    CMEM s c M -> 0 <= ic_next_out c <= cv_NO v ->
    CMEM (iset_mode s m) c (wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 m)).
  Proof.
    intros s c M m HM Hput. open_ictx C. open_cmem HM. unfold mapped in *.
    constructor.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoS. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoS CS. cbn. lia.
    - apply (is6_upd_mode M (cv_S v) _ s m Msc); [clear - CS; lia | unfold is6_SIZE; clear - CS; lia].
    - replace (is_lens (iset_mode s m)) with (is_lens s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); cbn; lia.
    - replace (is_work (iset_mode s m)) with (is_work s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); cbn; lia.
    - replace (is_codes (iset_mode s m)) with (is_codes s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); cbn; lia.
    - intros HW. replace (is_window (iset_mode s m)) with (is_window s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin HW)); cbn; try lia. unfold sep in CSW. clear - CSW CS CWB HW. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E|E]; [intros i Hi; exfalso; lia|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); cbn; try lia. specialize (CSI ltac:(lia)). unfold sep in CSI. clear - CSI CS CI0. lia.
    - destruct (Z.eq_dec (cv_NO v) 0) as [E|E]; [intros i Hi; exfalso; lia|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); cbn; try lia. specialize (CSP ltac:(lia)). unfold sep in CSP. clear - CSP CS CP0 Hput. lia.
    - open_zs Mzs. unfold izs6. repeat match goal with |- _ /\ _ => split end;
        (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | unfold sep in CZS; clear - CZS CS CZP; cbn; lia]).
    - intros x Hx. apply wbytes_grows. apply Mmap_f. exact Hx.
    - intros x Hx. apply wbytes_grows. apply Mmap_Z. exact Hx.
    - intros x Hx. apply wbytes_grows. apply Mmap_S. exact Hx.
    - intros x Hx. apply wbytes_grows. apply Mmap_P. exact Hx.
    - intros HW x Hx. apply wbytes_grows. apply (Mmap_W HW). exact Hx.
  Qed.

  Definition FRM : franges := [(cv_sp v - INF_FRAME, INF_FRAME)].
  Lemma agree_frame_store : forall F M M' (b : Z) bs,
    agree_out ((cv_sp v - INF_FRAME, INF_FRAME) :: F) M M' ->
    cv_sp v - INF_FRAME <= b -> b + Z.of_nat (length bs) <= cv_sp v ->
    agree_out ((cv_sp v - INF_FRAME, INF_FRAME) :: F) M (wbytes M' (zw b) bs).
  Proof.
    intros F M M' b bs Hag H1 H2. pose proof (ic_sp _ C) as Csp. unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in *.
    apply agree_out_wbytes; [exact Hag | lia | lia |]. apply sub_franges_here; lia.
  Qed.
  Lemma agree_mode_store : forall M M' bs,
    agree_out [(cv_sp v - INF_FRAME, INF_FRAME); (cv_S v + 8, 4)] M M' -> Z.of_nat (length bs) = 4 ->
    agree_out [(cv_sp v - INF_FRAME, INF_FRAME); (cv_S v + 8, 4)] M (wbytes M' (zw (cv_S v + 8)) bs).
  Proof.
    intros M M' bs Hag Hl. pose proof (ic_S _ C) as CS.
    apply agree_out_wbytes; [exact Hag | lia | lia |]. apply sub_franges_later. apply sub_franges_here; lia.
  Qed.
  Ltac agree_tower :=
    rewrite ?word_le_Z;
    lazymatch goal with
    | |- agree_out _ ?a ?a => apply agree_out_refl
    | |- agree_out _ _ (wbytes _ (zw (cv_S _ + 8)) _) => apply agree_mode_store; [agree_tower | reflexivity]
    | |- agree_out _ _ (wbytes _ _ _) =>
        apply agree_frame_store; [agree_tower | unfold INF_FRAME; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                             | unfold INF_FRAME; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
    end.
  Ltac grows_loop Hx :=
    lazymatch type of Hx with ?m0 ?x <> None =>
      lazymatch goal with
      | |- m0 x <> None => exact Hx
      | |- wbytes _ _ _ x <> None => apply wbytes_grows; grows_loop Hx
      end
    end.
  Ltac grows_tower := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; grows_loop Hx.

  Ltac iframe_tower :=
    unfold iframe6, INF_FRAME; split;
    [ lazymatch goal with |- forall r o, In (r, o) saved_slots -> cell s6u_segs ?Mx (?base + o) 8 _ =>
        apply (saved_slots_bv (fun (r : reg) (o : Z) => cell s6u_segs Mx (base + o) 8 (bv_unsigned (getr (cv_R0 v) r)))) end;
      first [tower_cell | match goal with |- ?G => idtac "IFRS LEFT" G end]
    | repeat match goal with |- _ /\ _ => split end; rewrite ?Z.add_0_r; first [tower_cell | match goal with |- ?G => idtac "IFR LEFT" G end] ].


  Definition pro_pins : list (Z * expr) := [(2, EAdd (EVar 32%nat) (ELit 256)); (10, EVar 34%nat); (11, EVar 35%nat)].
  Definition pro_rds : list (option expr) :=
    [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 33%nat); RVal (EVar 34%nat); RVal (EVar 45%nat);
     RVal (EAdd (EVar 37%nat) (EVar 38%nat)); RVal (EAdd (EVar 43%nat) (EVar 44%nat));
     RVal (EVar 36%nat); RVal (EVar 39%nat); RVal (EVar 40%nat); RVal (EVar 41%nat)].

  Lemma pro_run : forall s (c : icall) M,
    CMEM s c M ->
    HEAD <= is_mode s <= MEM -> 0 <= is_bits s < 64 -> 0 <= is_hold s < 2 ^ 64 ->
    ic_avail_in c = cv_NI v -> ic_avail_out c = cv_NO v -> ic_next_in c = 0 -> ic_next_out c = 0 ->
    0 < cv_fa v -> 0 < cv_ff v ->
    getr (cv_R0 v) 2 = zw (cv_sp v) -> getr (cv_R0 v) 10 = zw (cv_ZP v) -> getr (cv_R0 v) 11 = zw (cv_flush v) ->
    let s1 := s_entryM s in
    let w1 := W1M s c in
    exists R1 M1,
      msteps s6u_segs (mkst (cv_R0 v) (Z_to_bv 64 pc6_inflate) M s6u_rom) (mkst R1 (Z_to_bv 64 (arm6_pc (is_mode s1))) M1 s6u_rom)
      /\ LMEM v w1 M1 /\ RETC v w1 M1 /\ LFIX v R1 /\ LVARS v w1 R1 /\ getr R1 27 = zw (-3)
      /\ agree_out [(cv_sp v - INF_FRAME, INF_FRAME); (cv_S v + 8, 4)] M M1
      /\ (forall x, M x <> None -> M1 x <> None).
  Proof.
    intros s c M HM Hmode Hbits Hhold Hai Hao Hni Hno HFA HFF G2 G10 G11. cbv zeta.
    open_ictx C. pose proof HM as HM0. open_cmem HM. open_zs Mzs. unfold mapped in *.
    pose proof (is6_strm _ _ _ _ Msc) as C0. cbn [q_strm] in C0. rewrite Z.add_0_r in C0. rewrite Z.add_0_r in Z0.
    unfold HEAD, MEM in Hmode.
    pose proof (is6_mode _ _ _ _ Msc) as C8. pose proof (is6_hold _ _ _ _ Msc) as C80. pose proof (is6_bits _ _ _ _ Msc) as C88.
    assert (P2 : getr (cv_R0 v) 2 = zw (cv_sp v - 256 + 256)) by (rewrite G2; f_equal; lia).
    pose proof (s_entryM_fields s) as (Eh & Eb & Ew & Ewb & Ewbits & Ews).
    assert (Hput : 0 <= ic_next_out c <= cv_NO v) by (clear - Hno CP0; lia).
    assert (MAIN : forall bm : bool, (if bm then is_mode s <> TYPE else is_mode s = TYPE) ->
      exists R1 M1,
        msteps s6u_segs (mkst (cv_R0 v) (Z_to_bv 64 pc6_inflate) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_disp) M1 s6u_rom)
        /\ CMEM (s_entryM s) c M1 /\ LMEM v (W1M s c) M1 /\ RETC v (W1M s c) M1 /\ LFIX v R1 /\ LVARS v (W1M s c) R1
        /\ agree_out [(cv_sp v - INF_FRAME, INF_FRAME); (cv_S v + 8, 4)] M M1
        /\ (forall x, M x <> None -> M1 x <> None)).
    { intros bm Hbm.
      assert (Es : s_entryM s = if bm then s else iset_mode s TYPEDO).
      { unfold s_entryM. destruct bm; [rewrite (proj2 (Z.eqb_neq _ _) Hbm) | rewrite (proj2 (Z.eqb_eq _ _) Hbm)]; reflexivity. }
      destruct bm.
      - arm_symexP pro_pins ilS 90%nat [true; true; true; true; true; true; true; true; true; true; true] pro_rds
          (@nil (Z * expr)) [(45%nat, 16211); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)] v
          (mkIR (ic_next_in c) (ic_avail_in c) (ic_next_out c) (ic_avail_out c) (is_hold s) (is_bits s) (ic_avail_in c) (ic_avail_out c) Z_OK)
          [is_mode s; cv_fa v; cv_ff v] NoVals F0
          (mkst (cv_R0 v) (Z_to_bv 64 pc6_inflate) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
        all: try arm_side.
        all: try ub_align_side.
        all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFTP1" G end.
        replace (Z.lxor (cv_S v + 168) (-1)) with (- (cv_S v + 169)) in Hms1 by (rewrite Z.lxor_m1_r; unfold Z.lnot; lia).
        lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?Mx _) =>
          assert (A1 : agree_out [(cv_sp v - INF_FRAME, INF_FRAME)] M Mx) by (unfold INF_FRAME; agree_tower);
          assert (Gr1 : forall x, M x <> None -> Mx x <> None) by grows_tower;
          pose proof (CMEM_agree_frame s c M Mx HM0 Hput A1 Gr1) as HM1;
          set (M1 := Mx) in *
        end.
        exists R1, M1. split; [subst M1; by_run Hms1|]. rewrite Es. split; [exact HM1|].
        assert (HL : LMEM v (W1M s c) M1).
        { unfold W1M. rewrite Es. apply (LMEM_of_CMEM _ c _ M1 HM1); [| | | reflexivity]; subst M1.
          - rewrite ?szwrap32_small by (clear - Cflush; lia). rewrite Hai. clear - CS Csp CfS. unfold sep in CfS. iframe_tower.
          - cbn [ir_out]. rewrite Hao. unfold INF_FRAME. clear - CS Csp CfS CP0. unfold sep in CfS. tower_cell.
          - cbn [ir_left]. rewrite Hao. unfold INF_FRAME. clear - CS Csp CfS CP0. unfold sep in CfS. tower_cell. }
        split; [exact HL|].
        split. { unfold RETC, W1M, INF_FRAME. cbn [w_r ir_ret]. subst M1. unfold Z_OK. tower_cell. }
        split.
        { unfold LFIX, INF_FRAME. repeat match goal with |- _ /\ _ => split end;
            first [ lazymatch goal with |- getr _ ?n = _ => symex_reg HR1 n as Q; rewrite Q; first [reflexivity | f_equal; lia] end
                  | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); first [assumption | reflexivity] end
                  | match goal with |- ?G => idtac "LFIX LEFT" G end ]. }
        split.
        { unfold LVARS, W1M. cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next]. rewrite Es.
          repeat match goal with |- _ /\ _ => split end;
            first [ lazymatch goal with |- getr _ ?n = _ => symex_reg HR1 n as Q; rewrite Q; first [reflexivity | f_equal; lia] end
                  | match goal with |- ?G => idtac "LVARS LEFT" G end ]. }
        split; [subst M1; unfold INF_FRAME | subst M1; grows_tower].
        apply (agree_out_weaken [(cv_sp v - INF_FRAME, INF_FRAME)]); [agree_tower | intros x Hx; cbn [in_franges] in Hx |- *; tauto].
      - arm_symexP pro_pins ilS 90%nat [true; true; true; true; true; true; true; true; true; true; false] pro_rds
          (@nil (Z * expr)) [(45%nat, 16211); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)] v
          (mkIR (ic_next_in c) (ic_avail_in c) (ic_next_out c) (ic_avail_out c) (is_hold s) (is_bits s) (ic_avail_in c) (ic_avail_out c) Z_OK)
          [is_mode s; cv_fa v; cv_ff v] NoVals F0
          (mkst (cv_R0 v) (Z_to_bv 64 pc6_inflate) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
        all: try arm_side.
        all: try ub_align_side.
        all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFTP2" G end.
        replace (Z.lxor (cv_S v + 168) (-1)) with (- (cv_S v + 169)) in Hms1 by (rewrite Z.lxor_m1_r; unfold Z.lnot; lia).
        lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?Mx _) =>
          lazymatch Mx with context [wbytes ?Mm (zw (cv_S v + 8)) ?bsm] =>
            assert (A1 : agree_out [(cv_sp v - INF_FRAME, INF_FRAME)] M Mm) by (unfold INF_FRAME; agree_tower);
            assert (Gr1 : forall x, M x <> None -> Mm x <> None) by grows_tower;
            pose proof (CMEM_mode _ c Mm TYPEDO (CMEM_agree_frame s c M Mm HM0 Hput A1 Gr1) Hput) as HMb;
            change (Z_to_le_bytes 4 TYPEDO) with bsm in HMb;
            assert (A2 : agree_out [(cv_sp v - INF_FRAME, INF_FRAME)] (wbytes Mm (zw (cv_S v + 8)) bsm) Mx) by (unfold INF_FRAME; agree_tower);
            assert (Gr2 : forall x, wbytes Mm (zw (cv_S v + 8)) bsm x <> None -> Mx x <> None) by grows_tower;
            pose proof (CMEM_agree_frame _ c _ Mx HMb Hput A2 Gr2) as HM1;
            set (M1 := Mx) in *
          end
        end.
        exists R1, M1. split; [subst M1; by_run Hms1|]. rewrite Es. split; [exact HM1|].
        assert (HL : LMEM v (W1M s c) M1).
        { unfold W1M. rewrite Es. apply (LMEM_of_CMEM _ c _ M1 HM1); [| | | reflexivity]; subst M1.
          - rewrite ?szwrap32_small by (clear - Cflush; lia). rewrite Hai. clear - CS Csp CfS. unfold sep in CfS. iframe_tower.
          - cbn [ir_out]. rewrite Hao. unfold INF_FRAME. clear - CS Csp CfS CP0. unfold sep in CfS. tower_cell.
          - cbn [ir_left]. rewrite Hao. unfold INF_FRAME. clear - CS Csp CfS CP0. unfold sep in CfS. tower_cell. }
        split; [exact HL|].
        split. { unfold RETC, W1M, INF_FRAME. cbn [w_r ir_ret]. subst M1. unfold Z_OK. tower_cell. }
        split.
        { unfold LFIX, INF_FRAME. repeat match goal with |- _ /\ _ => split end;
            first [ lazymatch goal with |- getr _ ?n = _ => symex_reg HR1 n as Q; rewrite Q; first [reflexivity | f_equal; lia] end
                  | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); first [assumption | reflexivity] end
                  | match goal with |- ?G => idtac "LFIX LEFT" G end ]. }
        split.
        { unfold LVARS, W1M. cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next]. rewrite Es.
          replace (is_hold (iset_mode s TYPEDO)) with (is_hold s) by (destruct s; reflexivity).
          replace (is_bits (iset_mode s TYPEDO)) with (is_bits s) by (destruct s; reflexivity).
          repeat match goal with |- _ /\ _ => split end;
            first [ lazymatch goal with |- getr _ ?n = _ => symex_reg HR1 n as Q; rewrite Q; first [reflexivity | f_equal; lia] end
                  | match goal with |- ?G => idtac "LVARS LEFT" G end ]. }
        split; [subst M1; unfold INF_FRAME; agree_tower | subst M1; grows_tower]. }
    destruct (Z.eq_dec (is_mode s) TYPE) as [ET|NT];
      [destruct (MAIN false ET) as (R1 & M1 & Hms1 & HM1 & HL & HRC & HF & HV & AG & Gr)
      |destruct (MAIN true NT) as (R1 & M1 & Hms1 & HM1 & HL & HRC & HF & HV & AG & Gr)]; clear MAIN.
    all: assert (Hm1 : HEAD <= is_mode (s_entryM s) <= HEAD + 30)
           by (unfold s_entryM; destruct (is_mode s =? TYPE); [destruct s; cbn; unfold HEAD, TYPEDO; lia | unfold HEAD; lia]).
    all: pose proof HF as HF'; unfold LFIX in HF'; destruct HF' as (Q2 & Q27 & _).
    all: destruct (disp6u v (s_entryM s) _ _ R1 M1 C HL Q2 Q27 Hm1) as (R2 & Hms2 & G26 & Hfr2).
    all: exists R2, M1; split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    all: split; [exact HL|]; split; [exact HRC|].
    all: split; [unfold LFIX in HF |- *; repeat match goal with |- _ /\ _ => split end;
                 (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr2 n eq_refl) end; first [exact (proj1 HF) | apply HF | tauto | match goal with |- ?G => idtac "LFIX2 LEFT" G end])|].
    all: split; [unfold LVARS in HV |- *; repeat match goal with |- _ /\ _ => split end;
                 (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr2 n eq_refl) end; first [apply HV | tauto | match goal with |- ?G => idtac "LVARS2 LEFT" G end])|].
    all: split; [exact G26|]; split; [exact AG | exact Gr].
  Qed.


  Lemma iframe6_slots : forall M, iframe6 v M ->
    cell s6u_segs M (cv_sp v - 256 + 248) 8 (bv_unsigned (getr (cv_R0 v) 1))
    /\ cell s6u_segs M (cv_sp v - 256 + 240) 8 (bv_unsigned (getr (cv_R0 v) 8))
    /\ cell s6u_segs M (cv_sp v - 256 + 232) 8 (bv_unsigned (getr (cv_R0 v) 9))
    /\ cell s6u_segs M (cv_sp v - 256 + 224) 8 (bv_unsigned (getr (cv_R0 v) 18))
    /\ cell s6u_segs M (cv_sp v - 256 + 216) 8 (bv_unsigned (getr (cv_R0 v) 19))
    /\ cell s6u_segs M (cv_sp v - 256 + 208) 8 (bv_unsigned (getr (cv_R0 v) 20))
    /\ cell s6u_segs M (cv_sp v - 256 + 200) 8 (bv_unsigned (getr (cv_R0 v) 21))
    /\ cell s6u_segs M (cv_sp v - 256 + 192) 8 (bv_unsigned (getr (cv_R0 v) 22))
    /\ cell s6u_segs M (cv_sp v - 256 + 184) 8 (bv_unsigned (getr (cv_R0 v) 23))
    /\ cell s6u_segs M (cv_sp v - 256 + 176) 8 (bv_unsigned (getr (cv_R0 v) 24))
    /\ cell s6u_segs M (cv_sp v - 256 + 168) 8 (bv_unsigned (getr (cv_R0 v) 25))
    /\ cell s6u_segs M (cv_sp v - 256 + 160) 8 (bv_unsigned (getr (cv_R0 v) 26))
    /\ cell s6u_segs M (cv_sp v - 256 + 152) 8 (bv_unsigned (getr (cv_R0 v) 27)).
  Proof.
    intros M HF. unfold iframe6, INF_FRAME in HF. destruct HF as [Fsv _].
    repeat match goal with |- _ /\ _ => split end;
      lazymatch goal with |- cell _ _ (_ + ?o) 8 (bv_unsigned (getr _ ?r)) =>
        let X := fresh in let k := eval vm_compute in (bv_unsigned r) in
        pose proof (Fsv k o) as X;
        replace (Z_to_bv 5 k : reg) with r in X by (apply bv_eq; reflexivity);
        apply X; cbn; tauto
      end.
  Qed.

  Definition epi_rds : list (option expr) :=
    [RVal (EVar 33%nat); RVal (EVar 34%nat); RVal (EVar 35%nat); RVal (EVar 36%nat); RVal (EVar 37%nat); RVal (EVar 38%nat);
     RVal (EVar 39%nat); RVal (EVar 40%nat); RVal (EVar 41%nat); RVal (EVar 42%nat); RVal (EVar 43%nat); RVal (EVar 44%nat); RVal (EVar 45%nat)].
  Lemma epi_run : forall R M (rc : Z),
    iframe6 v M -> getr R 2 = zw (cv_sp v - INF_FRAME) -> getr R 10 = zw rc ->
    exists R',
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_ret) M s6u_rom) (mkst R' (getr (cv_R0 v) 1) M s6u_rom)
      /\ getr R' 10 = zw rc /\ getr R' 2 = zw (cv_sp v)
      /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr (cv_R0 v) r)
      /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4.
  Proof.
    intros R M rc HF G2 G10. open_ictx C. unfold INF_FRAME in G2.
    pose proof (iframe6_slots M HF) as (F248 & F240 & F232 & F224 & F216 & F208 & F200 & F192 & F184 & F176 & F168 & F160 & F152).
    pose proof (fun r : reg => u64_range (getr (cv_R0 v) r)) as Hrr.
    pose proof (Hrr 1%bv) as B1. pose proof (Hrr 8%bv) as B8. pose proof (Hrr 9%bv) as B9. pose proof (Hrr 18%bv) as B18.
    pose proof (Hrr 19%bv) as B19. pose proof (Hrr 20%bv) as B20. pose proof (Hrr 21%bv) as B21. pose proof (Hrr 22%bv) as B22.
    pose proof (Hrr 23%bv) as B23. pose proof (Hrr 24%bv) as B24. pose proof (Hrr 25%bv) as B25. pose proof (Hrr 26%bv) as B26.
    pose proof (Hrr 27%bv) as B27.
    assert (G10' : getr R 10 = zw (rc mod 2 ^ 64)) by (rewrite zw_mod; exact G10).
    symex s6u_segs (CFG [] [] [EVar 33%nat] [] []) 20%nat (@nil bool) epi_rds
      [(2, EVar 32%nat); (10, EVar 46%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64); (35%nat, 2 ^ 64); (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64);
       (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64)]
      NoRegions
      [cv_sp v - 256; bv_unsigned (getr (cv_R0 v) 1); bv_unsigned (getr (cv_R0 v) 8); bv_unsigned (getr (cv_R0 v) 9);
       bv_unsigned (getr (cv_R0 v) 18); bv_unsigned (getr (cv_R0 v) 19); bv_unsigned (getr (cv_R0 v) 20); bv_unsigned (getr (cv_R0 v) 21);
       bv_unsigned (getr (cv_R0 v) 22); bv_unsigned (getr (cv_R0 v) 23); bv_unsigned (getr (cv_R0 v) 24); bv_unsigned (getr (cv_R0 v) 25);
       bv_unsigned (getr (cv_R0 v) 26); bv_unsigned (getr (cv_R0 v) 27); rc mod 2 ^ 64]
      NoVals F0 F0'
      (mkst R (Z_to_bv 64 pc6_ret) M s6u_rom) R' HR' Hfr Hms.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTE" G end.
    exists R'. split; [by_run Hms|].
    split; [rewrite (Hfr (10%bv : reg) eq_refl); exact G10|].
    split; [symex_reg HR' (2%bv : reg) as Q2; rewrite Q2; f_equal; lia|].
    split.
    { intros r Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [lazymatch goal with |- getr _ ?n = _ => symex_reg HR' n as Q; rewrite Q; first [reflexivity | apply zw_u] end|]).
      destruct Hr. }
    split; [rewrite (Hfr (3%bv : reg) eq_refl); reflexivity | rewrite (Hfr (4%bv : reg) eq_refl); reflexivity].
  Qed.
End Call.
End FXG.
End Infl6A.

