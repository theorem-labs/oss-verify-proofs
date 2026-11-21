(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only Require Import TopLevel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import ShapeAlg SpinAlg ShapeHaltsA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import HaltsA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require FOCore.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad Stdio Adapter Driver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.


Definition node_exit_ok (C : Z -> Prop) (n : node) : Prop :=
  match n with NExit c => C c | _ => True end.

Section ExitsIn.
Variable C : Z -> Prop.

Fixpoint exits_in {R : Type} (P : R -> Prop) (t : itree node R) : Prop :=
  match t with
  | Ret r => P r
  | Vis n k => node_exit_ok C n /\ forall rsp, exits_in P (k rsp)
  end.

Lemma exits_in_mono {R} : forall (t : itree node R) (P P' : R -> Prop),
  exits_in P t -> (forall r, P r -> P' r) -> exits_in P' t.
Proof.
  induction t as [r|n k IH]; intros P P' H HP; cbn in *; [apply HP, H|].
  destruct H as [Hn Hk]. split; [exact Hn|]. intros rsp. eapply IH; [apply Hk| exact HP].
Qed.

Lemma exits_in_bind {A B} : forall (t : itree node A) (f : A -> itree node B) (P : B -> Prop),
  exits_in (fun a => exits_in P (f a)) t -> exits_in P (ITree.bind node t f).
Proof.
  induction t as [r|n k IH]; intros f P H; cbn in *; [exact H|].
  destruct H as [Hn Hk]. split; [exact Hn|]. intros rsp. apply IH. apply Hk.
Qed.

Definition eP {A} (Q : A -> Prop) (x : exc A) : Prop :=
  match x with Unr => True | Ok a => Q a end.

Lemma exits_in_ebind {A B} : forall (t : itree node (exc A)) (f : A -> itree node (exc B)) (Q : B -> Prop),
  exits_in (eP (fun a => exits_in (eP Q) (f a))) t -> exits_in (eP Q) (ebind t f).
Proof.
  intros t f Q H. unfold ebind. apply exits_in_bind. eapply exits_in_mono; [exact H|].
  intros [|a] Hr; cbn in *; [exact I| exact Hr].
Qed.

Lemma exits_in_enode {A} : forall n (pl : resp -> option A) (Q : A -> Prop),
  node_exit_ok C n -> (forall rsp a, pl rsp = Some a -> Q a) -> exits_in (eP Q) (enode n pl).
Proof.
  intros n pl Q Hn HQ. cbn. split; [exact Hn|]. intros rsp. specialize (HQ rsp).
  destruct (pl rsp) as [a|]; cbn; [apply HQ; reflexivity| exact I].
Qed.


Lemma exits_in_ttrace {R} : forall (t : itree node R) P mo tr,
  exits_in P t -> ttrace nstep nexit t mo tr ->
  forall code fs, In (ExitEv code fs) tr -> exists c, C c /\ code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).
Proof.
  induction t as [r|n k IH]; intros P mo tr HE Htr code fs Hin.
  - cbn in Htr. subst tr. destruct Hin.
  - cbn [exits_in] in HE. destruct HE as [Hn Hk]. cbn [ttrace] in Htr.
    destruct Htr as [(code' & mo' & Hex & ->) | (rsp & mo' & evs & tr' & Hst & Htr' & ->)].
    + destruct Hin as [H | []]. injection H as -> _.
      destruct n; cbn [nexit] in Hex; try contradiction. destruct Hex as [-> _]. cbn in Hn. exists code0. split; [exact Hn| reflexivity].
    + apply in_app_or in Hin as [Hin | Hin].
      * exfalso. exact (nstep_no_exit _ _ _ _ _ Hst code fs Hin).
      * exact (IH rsp P mo' tr' (Hk rsp) Htr' code fs Hin).
Qed.

Theorem exits_in_ends_in {R} : forall (S : list word) (t : itree node R) P mo,
  (forall c, C c -> In (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) S) ->
  exits_in P t -> ends_in S (tree_traces t mo).
Proof.
  intros S t P mo HS HE. split.
  - intros tr code fs (full & Hf & Hp).
    destruct (exits_in_ttrace t P mo full HE Hf code fs) as (c & Hc & ->).
    + apply (in_is_prefix_full _ _ _ Hp). apply in_or_app. right. left. reflexivity.
    + apply HS. exact Hc.
  - intros tr sig fs H. apply (tree_traces_no_kill t mo _ H sig fs). apply in_or_app. right. left. reflexivity.
Qed.
End ExitsIn.

Lemma node_exit_ok_mono : forall (C C' : Z -> Prop) n, node_exit_ok C n -> (forall c, C c -> C' c) -> node_exit_ok C' n.
Proof. intros C C' n H HC. destruct n; cbn in *; auto. Qed.

Lemma exits_in_monoC {R} : forall (C C' : Z -> Prop) (t : itree node R) P,
  exits_in C P t -> (forall c, C c -> C' c) -> exits_in C' P t.
Proof.
  intros C C' t. induction t as [r|n k IH]; intros P H HC; cbn in *; [exact H|].
  destruct H as [Hn Hk]. split; [exact (node_exit_ok_mono C C' n Hn HC)|]. intros rsp. apply IH; [apply Hk| exact HC].
Qed.


Section MExits.
Context {St : Type}.
Variable C : Z -> Prop.

Definition mexits {A} (m : M St A) (Q : A -> Prop) : Prop :=
  forall s, exits_in C (eP (fun p => Q (fst p))) (m s).

Lemma mexits_ret {A} : forall (a : A) (Q : A -> Prop), Q a -> mexits (mret a) Q.
Proof. intros a Q H s. exact H. Qed.

Lemma mexits_unr {A} : forall (Q : A -> Prop), mexits (munr (A:=A)) Q.
Proof. intros Q s. exact I. Qed.

Lemma mexits_get : forall (Q : St -> Prop), (forall s, Q s) -> mexits mget Q.
Proof. intros Q H s. cbn. apply H. Qed.

Lemma mexits_get_true : mexits mget (fun _ => True).
Proof. intros s. exact I. Qed.

Lemma mexits_upd : forall (f : St -> St) (Q : unit -> Prop), Q tt -> mexits (mupd f) Q.
Proof. intros f Q H s. exact H. Qed.

Lemma mexits_mono {A} : forall (m : M St A) (Q Q' : A -> Prop),
  mexits m Q -> (forall a, Q a -> Q' a) -> mexits m Q'.
Proof.
  intros m Q Q' H HQ s. eapply exits_in_mono; [exact (H s)|]. intros [|[a s']]; cbn; auto.
Qed.

Lemma mexits_bind {A B} : forall (m : M St A) (f : A -> M St B) (Q1 : A -> Prop) (Q : B -> Prop),
  mexits m Q1 -> (forall a, Q1 a -> mexits (f a) Q) -> mexits (mbind m f) Q.
Proof.
  intros m f Q1 Q Hm Hf s. unfold mbind. apply exits_in_ebind.
  eapply exits_in_mono; [exact (Hm s)|]. intros [|[a s']] H; cbn in *; [exact I|]. exact (Hf a H s').
Qed.

Lemma mexits_seq {A B} : forall (m : M St A) (f : A -> M St B) (Q : B -> Prop),
  mexits m (fun _ => True) -> (forall a, mexits (f a) Q) -> mexits (mbind m f) Q.
Proof. intros m f Q Hm Hf. eapply mexits_bind; [exact Hm|]. intros a _. exact (Hf a). Qed.

Lemma mexits_sys {A} : forall n (dec : resp -> option A) (Q : A -> Prop),
  node_exit_ok C n -> (forall rsp a, dec rsp = Some a -> Q a) -> mexits (msys n dec) Q.
Proof.
  intros n dec Q Hn HQ s. unfold msys. apply exits_in_enode; [exact Hn|].
  intros rsp [a s'] E. cbn. specialize (HQ rsp). destruct (dec rsp) as [a'|]; [|discriminate]. injection E as <- _. apply HQ. reflexivity.
Qed.

Lemma mexits_sys_true {A} : forall n (dec : resp -> option A),
  node_exit_ok C n -> mexits (msys n dec) (fun _ => True).
Proof. intros n dec Hn. apply mexits_sys; [exact Hn|]. intros; exact I. Qed.

Lemma mexits_exit : forall c (Q : Empty_set -> Prop), C c -> mexits (msys (NExit c) dec_exit) Q.
Proof. intros c Q Hc. apply mexits_sys; [exact Hc|]. intros rsp a E. discriminate E. Qed.

Lemma mexits_if {A} : forall (b : bool) (m1 m2 : M St A) (Q : A -> Prop),
  (b = true -> mexits m1 Q) -> (b = false -> mexits m2 Q) -> mexits (if b then m1 else m2) Q.
Proof. intros b m1 m2 Q H1 H2. destruct b; [apply H1| apply H2]; reflexivity. Qed.

Lemma mexits_when : forall (b : bool) (m : M St unit), mexits m (fun _ => True) -> mexits (mwhen b m) (fun _ => True).
Proof. intros b m H. unfold mwhen. destruct b; [exact H| apply mexits_ret; exact I]. Qed.

Lemma mexits_loop {X R} : forall (body : X -> M St (X + R)) (Q : R -> Prop),
  (forall x, mexits (body x) (fun r => match r with inl _ => True | inr v => Q v end)) ->
  forall fuel x, mexits (mloop fuel body x) Q.
Proof.
  intros body Q Hb. induction fuel as [|fuel IH]; intros x; cbn [mloop]; [apply mexits_unr|].
  eapply mexits_bind; [exact (Hb x)|]. intros [x'|v] H; [apply IH| apply mexits_ret; exact H].
Qed.

Lemma mexits_loop_inv {X R} : forall (body : X -> M St (X + R)) (I : X -> Prop) (Q : R -> Prop),
  (forall x, I x -> mexits (body x) (fun r => match r with inl x' => I x' | inr v => Q v end)) ->
  forall fuel x, I x -> mexits (mloop fuel body x) Q.
Proof.
  intros body I Q Hb. induction fuel as [|fuel IH]; intros x Hx; cbn [mloop]; [apply mexits_unr|].
  eapply mexits_bind; [exact (Hb x Hx)|]. intros [x'|v] H; [apply IH; exact H| apply mexits_ret; exact H].
Qed.
End MExits.

Arguments mexits {St} C {A} m Q.

Lemma mexits_monoC {St A} : forall (C C' : Z -> Prop) (m : M St A) Q,
  mexits C m Q -> (forall c, C c -> C' c) -> mexits C' m Q.
Proof. intros C C' m Q H HC s. eapply exits_in_monoC; [exact (H s)| exact HC]. Qed.

Ltac mex_step :=
  first [ apply mexits_ret; exact I
        | apply mexits_unr
        | apply mexits_upd; exact I
        | apply mexits_get_true
        | apply mexits_sys_true; exact I
        | apply mexits_if; intros _
        | apply mexits_seq; [| intros ?] ].
Ltac mex_auto := repeat mex_step.


Section StdioExits.
Context {St : Type}.
Variable C : Z -> Prop.

Lemma stdio_write_loop_exits : forall fuel fd iov, mexits C (stdio_write_loop (St:=St) fuel fd iov) (fun _ => True).
Proof.
  induction fuel as [|fuel IH]; intros fd iov; cbn [stdio_write_loop]; [apply mexits_unr|].
  apply mexits_seq; [apply mexits_sys_true; exact I|]. intros cnt. apply mexits_if; intros _; [apply mexits_ret; exact I| apply IH].
Qed.

Lemma stdio_write_exits : forall fd buf s, mexits C (stdio_write (St:=St) fd buf s) (fun _ => True).
Proof. intros fd buf s. unfold stdio_write. apply mexits_if; intros _; [apply mexits_unr| apply stdio_write_loop_exits]. Qed.

Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Lemma upd_so_exits : forall f, mexits C (upd_so get_so set_so f) (fun _ => True).
Proof. intros f. unfold upd_so. apply mexits_upd. exact I. Qed.

Lemma rd_so_exits : mexits C (rd_so get_so) (fun _ => True).
Proof. unfold rd_so. mex_auto. Qed.

Lemma stdout_stdio_write_exits : forall s, mexits C (stdout_stdio_write get_so set_so s) (fun _ => True).
Proof. intros s. unfold stdout_stdio_write. apply mexits_seq; [apply rd_so_exits|]. intros so. apply mexits_seq; [apply stdio_write_exits|]. intros _. apply upd_so_exits. Qed.

Lemma stdout_writefn_exits : forall s, mexits C (stdout_writefn get_so set_so s) (fun _ => True).
Proof.
  intros s. unfold stdout_writefn. apply mexits_seq; [apply rd_so_exits|]. intros so.
  apply mexits_seq; [| intros ?; apply stdout_stdio_write_exits].
  apply mexits_if; intros _; [| apply mexits_ret; exact I].
  apply mexits_seq; [apply upd_so_exits|]. intros _. apply mexits_seq; [apply mexits_sys_true; exact I|].
  intros [e|v]; [apply upd_so_exits| apply mexits_unr].
Qed.

Lemma stdout_towrite_exits : mexits C (stdout_towrite get_so set_so) (fun _ => True).
Proof. unfold stdout_towrite. apply upd_so_exits. Qed.

Lemma stdout_fwritex_exits : forall s, mexits C (stdout_fwritex get_so set_so s) (fun _ => True).
Proof.
  intros s. unfold stdout_fwritex. apply mexits_seq; [apply stdout_towrite_exits|]. intros _.
  apply mexits_seq; [apply rd_so_exits|]. intros so.
  apply mexits_if; intros _; [apply stdout_writefn_exits|].
  apply mexits_if; intros _; [| apply upd_so_exits].
  apply mexits_seq; [| intros ?; apply upd_so_exits].
  apply mexits_if; intros _; [apply stdout_writefn_exits| apply mexits_ret; exact I].
Qed.

Lemma out_pieces_exits : forall ps, mexits C (out_pieces get_so set_so ps) (fun _ => True).
Proof.
  induction ps as [|p ps IH]; cbn [out_pieces]; [apply mexits_ret; exact I|].
  apply mexits_seq; [apply stdout_fwritex_exits|]. intros _. exact IH.
Qed.

Lemma stdout_vprintf_exits : forall ps, mexits C (stdout_vprintf get_so set_so ps) (fun _ => True).
Proof. intros ps. unfold stdout_vprintf. apply mexits_seq; [apply stdout_towrite_exits|]. intros _. apply out_pieces_exits. Qed.

Lemma stdout_exit_flush_exits : mexits C (stdout_exit_flush get_so set_so) (fun _ => True).
Proof.
  unfold stdout_exit_flush. apply mexits_seq; [apply rd_so_exits|]. intros so.
  apply mexits_if; intros _; [apply stdout_writefn_exits| apply mexits_ret; exact I].
Qed.

Lemma stderr_pieces_exits : forall ps buf, mexits C (stderr_pieces (St:=St) buf ps) (fun _ => True).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [apply mexits_ret; exact I|].
  apply mexits_if; intros _; [| apply IH].
  apply mexits_seq; [apply stdio_write_exits|]. intros _. apply IH.
Qed.

Lemma stderr_fprintf_exits : forall ps, mexits C (stderr_fprintf (St:=St) ps) (fun _ => True).
Proof. intros ps. unfold stderr_fprintf. apply mexits_seq; [apply stderr_pieces_exits|]. intros buf. apply stdio_write_exits. Qed.

Lemma stderr_fwrite_exits : forall s, mexits C (stderr_fwrite (St:=St) s) (fun _ => True).
Proof. intros s. unfold stderr_fwrite. apply mexits_if; intros _; [apply stdio_write_exits| apply mexits_ret; exact I]. Qed.

Lemma s_diag_exits : forall d, mexits C (s_diag (St:=St) d) (fun _ => True).
Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_exits | apply stderr_fwrite_exits]. Qed.

Lemma s_emit_exits : forall v, mexits C (s_emit get_so set_so v) (fun _ => True).
Proof. intros v. unfold s_emit. apply stdout_vprintf_exits. Qed.

Lemma io_S_diag_exits : forall d, mexits C (io_diag (io_S get_so set_so) d) (fun _ => True).
Proof. exact s_diag_exits. Qed.
Lemma io_S_emit_exits : forall v, mexits C (io_emit (io_S get_so set_so) v) (fun _ => True).
Proof. exact s_emit_exits. Qed.
Lemma io_S_exit_exits : mexits C (io_exit (io_S get_so set_so)) (fun _ => True).
Proof. exact stdout_exit_flush_exits. Qed.
End StdioExits.


Section DriverExits.
Context {St ptr : Type}.
Variable C : Z -> Prop.
Variable io : IOStyle St.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> M St unit.
Variable run : Z -> list Z -> M St Z.
Variable alloc_count : M St Z.

Hypothesis Hdiag : forall d, mexits C (io_diag io d) (fun _ => True).
Hypothesis Hemit : forall v, mexits C (io_emit io v) (fun _ => True).
Hypothesis Hexit : mexits C (io_exit io) (fun _ => True).
Hypothesis Hdm : forall n, mexits C (drv_malloc n) (fun _ => True).
Hypothesis Hdf : forall p, mexits C (drv_free p) (fun _ => True).

Lemma read_loop_body_exits : forall fd path st,
  mexits C (read_loop_body io drv_malloc drv_free read_stage fd path st) (fun _ => True).
Proof.
  intros fd path st. unfold read_loop_body.
  apply mexits_seq.
  - apply mexits_if; intros _; [| apply mexits_ret; exact I].
    apply mexits_if; intros _.
    + apply mexits_seq; [apply Hdiag|]. intros _. apply mexits_ret; exact I.
    + apply mexits_seq; [apply Hdm|]. intros [nb'|].
      * apply mexits_seq; [apply Hdf|]. intros _. apply mexits_ret; exact I.
      * apply mexits_seq; [apply Hdiag|]. intros _. apply mexits_ret; exact I.
  - intros [st1|]; [| apply mexits_ret; exact I].
    apply mexits_seq; [apply mexits_sys_true; exact I|]. intros [e|bs].
    + apply mexits_seq; [apply Hdiag|]. intros _. apply mexits_ret; exact I.
    + apply mexits_if; intros _; apply mexits_ret; exact I.
Qed.

Lemma read_all_exits : forall path, mexits C (read_all io drv_malloc drv_free read_stage path) (fun _ => True).
Proof.
  intros path. unfold read_all.
  apply mexits_seq; [apply mexits_sys_true; exact I|]. intros [e|fd].
  - apply mexits_seq; [apply Hdiag|]. intros _. apply mexits_ret; exact I.
  - apply mexits_seq; [apply Hdm|]. intros [buf|].
    + apply mexits_seq; [apply mexits_loop; intros x; eapply mexits_mono; [apply read_loop_body_exits| intros [?|?] _; exact I]|].
      intros [|buf' content]; [apply mexits_ret; exact I|].
      apply mexits_seq; [apply mexits_sys_true; exact I|]. intros _. apply mexits_ret; exact I.
    + apply mexits_seq; [apply Hdiag|]. intros _. apply mexits_ret; exact I.
Qed.

Variable K : Z -> Prop.
Hypothesis K2 : K 2.
Hypothesis Hinit : forall b, mexits C (alloc_init b) (fun _ => True).
Hypothesis Hrun : forall cfg pl, mexits C (run cfg pl) K.
Hypothesis Hcount : mexits C alloc_count (fun n => K (if n <? COUNT_MAX then n else COUNT_MAX)).

Theorem main_model_exits : forall argv,
  mexits C (main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv) K.
Proof.
  intros argv. unfold main_model.
  apply mexits_if; intros _.
  { apply mexits_seq; [apply Hdiag|]. intros _. apply mexits_ret. exact K2. }
  apply mexits_seq; [apply read_all_exits|]. intros [|buf content]; [apply mexits_ret; exact K2|].
  apply mexits_if; intros _.
  { apply mexits_seq; [apply Hdiag|]. intros _. apply mexits_seq; [apply Hdf|]. intros _. apply mexits_ret. exact K2. }
  apply mexits_if; intros _.
  { apply mexits_seq; [apply Hdiag|]. intros _. apply mexits_seq; [apply Hdf|]. intros _. apply mexits_ret. exact K2. }
  apply mexits_seq; [apply Hinit|]. intros _.
  apply (mexits_bind C _ _ K); [apply Hrun|]. intros status Hst.
  apply (mexits_bind C _ _ K).
  - destruct (Z.testbit _ 15); [| apply mexits_ret; exact Hst].
    eapply mexits_bind; [apply Hcount|]. intros n Hn. apply mexits_ret. exact Hn.
  - intros status' Hst'. apply mexits_seq; [apply Hdf|]. intros _. apply mexits_ret. exact Hst'.
Qed.

Theorem exit_model_exits : forall code (Q : Empty_set -> Prop), C code -> mexits C (exit_model io code) Q.
Proof.
  intros code Q Hc. unfold exit_model. apply mexits_seq; [apply Hexit|]. intros _. apply mexits_exit. exact Hc.
Qed.
End DriverExits.


Section AdapterExits.
Context {St ptr : Type}.
Variable C : Z -> Prop.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable fuzz_one : list Z -> M St Z.
Variable emit : Z -> M St unit.
Hypothesis Hdm : forall n, mexits C (drv_malloc n) (fun _ => True).
Hypothesis Hdf : forall p, mexits C (drv_free p) (fun _ => True).
Hypothesis Hemit : forall v, mexits C (emit v) (fun _ => True).
Hypothesis Hfuzz : forall pl, mexits C (fuzz_one pl) (fun rc => rc = 0).

Lemma run_calls_exits : forall n pl b, b = 0 -> mexits C (run_calls fuzz_one emit n pl b) (fun r => r = 0).
Proof.
  induction n as [|n IH]; intros pl b Hb; cbn [run_calls]; [apply mexits_ret; exact Hb|].
  apply (mexits_bind C _ _ (fun rc => rc = 0)); [apply Hfuzz|]. intros rc Hrc.
  apply mexits_seq; [apply Hemit|]. intros _. apply IH. subst. reflexivity.
Qed.

Theorem target_run_exits : forall cfg pl,
  mexits C (target_run drv_malloc drv_free fuzz_one emit cfg pl) (fun c => c = 0 \/ c = 2).
Proof.
  intros cfg pl. unfold target_run.
  apply mexits_seq.
  - apply mexits_if; intros _; [apply mexits_ret; exact I|]. apply mexits_seq; [apply Hdm|]. intros ?. apply mexits_ret; exact I.
  - intros [owned|]; [| apply mexits_ret; right; reflexivity].
    apply (mexits_bind C _ _ (fun r => r = 0)); [apply run_calls_exits; reflexivity|]. intros b ->.
    apply mexits_seq; [destruct owned; [apply Hdf| apply mexits_ret; exact I]|]. intros _.
    apply mexits_ret. left. reflexivity.
Qed.

Lemma target_alloc_init_exits : forall b, mexits C (target_alloc_init (St:=St) b) (fun _ => True).
Proof. intros b. apply mexits_ret. exact I. Qed.

Lemma target_alloc_count_exits : forall K : Z -> Prop, K 0 -> mexits C (target_alloc_count (St:=St)) (fun n => K (if n <? COUNT_MAX then n else COUNT_MAX)).
Proof. intros K HK. apply mexits_ret. cbn. exact HK. Qed.
End AdapterExits.


Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m. unfold refusal_decided. intros _.
  match goal with |- ?A \/ _ => destruct (classic A) as [H|H]; [left; exact H| right] end.
  intros eff' m' evs' Hs. destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity|].
  exfalso. apply H. exists eff', m', evs'. split; [exact Hs| exact E].
Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof.
  intros cfg [segs pc ph] lim [sp brk mb dr] inp. cbn [run_decided]. intros tr c' x8 _ _. apply refusal_decided_classic.
Qed.

Theorem halts_T_of_srealizes : forall segs pc ph (T : ProcInput -> ExecEntry -> TSet) (S : list word),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
     (* over the run's list run_segments = segs ++ the vDSO pair (HaltsA's form) *)
     let vsegs := run_segments segs inp (en_sp en) (en_mmap_base en) in
     srealizes vsegs (init_config vsegs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) (T inp en)
     /\ ends_in S (T inp en)) ->
  FOCore.halts_core FOCore.alloc_forced_cfg source_alloc_limit S (mkImage segs pc ph).
Proof.
  intros segs pc ph T S H en inp Hve Hvi.
  pose proof (H en inp Hve (valid_input_either_of_valid_input inp Hvi)) as HH. cbv zeta in HH.
  destruct HH as [Hsrz Hend].
  destruct en as [sp brk mb dr]. cbn [must_exit_in_scfg]. cbn [en_sp en_brk en_mmap_base en_draw] in Hsrz.
  set (vsegs := run_segments segs inp sp mb) in *.
  apply (realizes_must_exit_init vsegs S _ (T inp (mkEntry sp brk mb dr)) (realizes_of_srealizes vsegs _ _ Hsrz) Hend).
  change (init_config vsegs pc ph sp brk mb dr source_alloc_limit inp)
    with (init_config vsegs pc ph (en_sp (mkEntry sp brk mb dr)) (en_brk (mkEntry sp brk mb dr))
                      (en_mmap_base (mkEntry sp brk mb dr)) (en_draw (mkEntry sp brk mb dr)) source_alloc_limit inp).
  rewrite (init_config_eq vsegs pc ph source_alloc_limit (mkEntry sp brk mb dr) inp).
  apply mo0_not_halted.
Qed.

Lemma halts_scfg_of_T : forall cfg S img, halts_allowed_T S img -> halts_allowed_T_scfg cfg S img.
Proof.
  intros cfg S img H en inp Hve Hvi.
  apply must_exit_in_scfg_of_must_exit_in; [apply run_decided_classic| exact (H en inp Hve Hvi)].
Qed.

Theorem halts_B_of_srealizes : forall segs pc ph (T : ProcInput -> ExecEntry -> TSet) (S : list word),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
     let vsegs := run_segments segs inp (en_sp en) (en_mmap_base en) in
     srealizes vsegs (init_config vsegs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) (T inp en)
     /\ ends_in S (T inp en)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source S (mkImage segs pc ph).
Proof.
  intros segs pc ph T S H. apply FOCore.halts_allowed_T_scfg_budgets_of_core.
  exact (FOCore.halts_core_mono forced_only_cfg FOCore.alloc_forced_cfg _ _ _ (forced_only_cfg_least _)
           (halts_T_of_srealizes segs pc ph T S H)).
Qed.
