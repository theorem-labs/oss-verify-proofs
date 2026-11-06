(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
Module ImplSCPS.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => alloc_node n = true /\ nsafe n mo /\
               forall rsp mo', anstep n mo rsp mo' -> twf (k rsp) mo' P
  end.

Lemma twf_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twf t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twf t mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as (Hn & Hs & Hk). split; [exact Hn|]. split; [exact Hs|]. intros rsp mo' Hst. eapply IH; eauto.
Qed.

Lemma twf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twf t mo (fun a mo1 => twf (f a) mo1 P) -> twf (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as (Hn & Hs & Hk). split; [exact Hn|]. split; [exact Hs|]. intros rsp mo' Hst. apply IH. eapply Hk; eauto.
Qed.

(* [comment removed for export] *)
Definition etwf {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twf t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwf_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwf t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwf t mo Q'.
Proof.
  intros A t mo Q Q' H HQ. unfold etwf in *. eapply twf_mono; [exact H|].
  intros [|a] mo1; cbn; auto.
Qed.

Lemma etwf_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etwf t mo (fun a mo1 => etwf (f a) mo1 Q) -> etwf (ebind t f) mo Q.
Proof.
  intros A B t f mo Q H. unfold etwf, ebind in *. apply twf_bind.
  eapply twf_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.

Lemma etwf_ret : forall {A} (a : A) mo (Q : A -> Model -> Prop), Q a mo -> etwf (Ret (Ok a)) mo Q.
Proof. intros A a mo Q H. exact H. Qed.

Lemma etwf_enode : forall {A} n (pl : resp -> option A) mo (Q : A -> Model -> Prop),
  alloc_node n = true -> nsafe n mo ->
  (forall rsp mo', anstep n mo rsp mo' -> exists a, pl rsp = Some a /\ Q a mo') ->
  etwf (enode n pl) mo Q.
Proof.
  intros A n pl mo Q Hn Hs Hk. unfold etwf, enode. cbn. split; [exact Hn|]. split; [exact Hs|].
  intros rsp mo' Hst. destruct (Hk rsp mo' Hst) as (a & -> & HQ). exact HQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Theorem impl_scps : forall {A} (t : itree node (exc A)) (Q : A -> machine_state -> Prop)
                           (R : A -> Model -> Prop) ms mo,
  impl segs (at_node segs) t (epost Q) ms -> MOK mo -> etwf t mo R ->
  SCPS segs (fun ms' mo' => exists a, Q a ms' /\ R a mo' /\ MOK mo') ms mo.
Proof.
  intros A t. unfold etwf.
  induction t as [r|n k IH]; intros Q R ms mo Himpl HM Hwf; cbn in Himpl, Hwf.
  - destruct r as [|a]; [destruct Hwf|].
    intros T K. eapply rz_evt; [exact HM | exact Himpl |].
    intros ms' HQ. apply K; [| apply vm_only_refl]. exists a. cbn in HQ. auto.
  - destruct Hwf as (Hn & Hs & Hk).
    intros T K. eapply rz_evt; [exact HM | exact Himpl |].
    intros ms1 [Hat Hk1].
    apply (rz_alloc_node segs n ms1 mo T Hn Hat HM Hs).
    intros rsp mo' Ha.
    apply (IH rsp Q R (nret ms1 rsp) mo' (Hk1 rsp) (anstep_MOK n mo rsp mo' HM Ha) (Hk rsp mo' Ha)).
    intros ms2 mo2 HP HV. apply K; [exact HP | eapply vm_only_trans; [eapply anstep_vm_only; exact Ha | exact HV]].
Qed.

Theorem implM_scps : forall {St A} (c : M St A) (s : St) (Q : A -> St -> machine_state -> Prop)
                            (R : A * St -> Model -> Prop) ms mo,
  implM segs c s Q ms -> MOK mo -> etwf (c s) mo R ->
  SCPS segs (fun ms' mo' => exists a s', Q a s' ms' /\ R (a, s') mo' /\ MOK mo') ms mo.
Proof.
  intros St A c s Q R ms mo Hc HM Hwf.
  eapply scps_mono; [apply (impl_scps (c s) (fun p => Q (fst p) (snd p)) R ms mo Hc HM Hwf)|].
  intros ms' mo' ([a s'] & HQ & HR & HM'). exists a, s'. auto.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSpec.
Context {St : Type}.

Definition assn : Type := St -> Model -> Prop.

Definition mspec {A} (P : assn) (m : M St A) (Q : A -> assn) : Prop :=
  forall s mo, P s mo -> etwf (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspec_ret {A} (a : A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo -> Q a s mo) -> mspec P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspec_bind {A B} (m : M St A) (f : A -> M St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
  mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etwf_ebind.
  eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

Lemma mspec_conseq {A} (m : M St A) (P P' : assn) (Q Q' : A -> assn) :
  mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply etwf_mono; [exact (Hm s mo (HP _ _ HP'))|].
  intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspec_pre {A} (m : M St A) (P P' : assn) (Q : A -> assn) :
  mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> mspec P' m Q.
Proof. intros Hm HP. eapply mspec_conseq; eauto. Qed.

Lemma mspec_post {A} (m : M St A) (P : assn) (Q Q' : A -> assn) :
  mspec P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P m Q'.
Proof. intros Hm HQ. eapply mspec_conseq; eauto. Qed.

Lemma mspec_munr {A} (Q : A -> assn) : mspec (fun _ _ => False) munr Q.
Proof. intros s mo []. Qed.

Lemma mspec_false {A} (m : M St A) (Q : A -> assn) : mspec (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

Lemma mspec_get (P : assn) : mspec P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

Lemma mspec_put (P : assn) (s1 : St) : mspec P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd (P : assn) (f : St -> St) : mspec P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd' (P : assn) (Q : unit -> assn) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspec P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

(* [comment removed for export] *)
Lemma mspec_sys {A} (n : node) (dec : resp -> option A) (P : assn) (Q : A -> assn) :
  alloc_node n = true ->
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo', anstep n mo rsp mo' -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspec P (msys n dec) Q.
Proof.
  intros Hn H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hn|]. split; [exact Hs|].
  intros rsp mo' Hst. destruct (Hk rsp mo' Hst) as (a & -> & HQ). exact HQ.
Qed.

Lemma mspec_if {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  (b = true -> mspec P m1 Q) -> (b = false -> mspec P m2 Q) -> mspec P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma mspec_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  mspec (fun s mo => P s mo /\ b = true) m1 Q -> mspec (fun s mo => P s mo /\ b = false) m2 Q ->
  mspec P (if b then m1 else m2) Q.
Proof. intros H1 H2 s mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

Lemma mspec_exI {A X} (P : X -> assn) (m : M St A) (Q : A -> assn) :
  (forall x, mspec (P x) m Q) -> mspec (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

Lemma mspec_pure {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspec P m Q) -> mspec (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.

Lemma mspec_pure_l {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspec P m Q) -> mspec (fun s mo => phi /\ P s mo) m Q.
Proof. intros H s mo [Hphi HP]. exact (H Hphi s mo HP). Qed.

Lemma mspec_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
  (forall s mo, P s mo -> mspec (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspec P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

Lemma mspec_when (b : bool) (m : M St unit) (P : assn) (Q : unit -> assn) :
  (b = true -> mspec P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspec P (mwhen b m) Q.
Proof. intros H1 H2. unfold mwhen. destruct b; [apply H1; reflexivity|]. apply mspec_ret. apply H2. reflexivity. Qed.

Lemma mspec_loop {X R} (body : X -> M St (X + R)) (I : X -> assn) (Q : R -> assn) (meas : X -> nat) :
  (forall x, mspec (I x) (body x)
     (fun r s mo => match r with
                    | inl x' => I x' s mo /\ (meas x' < meas x)%nat
                    | inr v => Q v s mo
                    end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspec (I x) (mloop fuel body x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x Hf; [lia|].
  cbn [mloop]. eapply mspec_bind; [apply Hb|].
  intros [x'|v]; cbn.
  - intros s mo [HI Hm]. apply (IH x'); [lia| exact HI].
  - apply mspec_ret. auto.
Qed.

Lemma mspec_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn) (Q : B -> assn) :
  mspec P m (fun _ => R) -> (forall a, mspec R (f a) Q) -> mspec P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspec_bind; [exact Hm|]. intros a. apply Hf. Qed.

(* [comment removed for export] *)
Theorem implM_mspec_scps : forall segs {A} (c : M St A) (P : assn) (R : A -> assn) s (Q : A -> St -> machine_state -> Prop) ms mo,
  mspec P c R -> P s mo ->
  implM segs c s Q ms -> MOK mo ->
  SCPS segs (fun ms' mo' => exists a s', Q a s' ms' /\ R a s' mo' /\ MOK mo') ms mo.
Proof.
  intros segs A c P R s Q ms mo Hspec HP Hc HM.
  eapply scps_mono; [apply (implM_scps segs c s Q (fun p mo' => R (fst p) (snd p) mo') ms mo Hc HM (Hspec s mo HP))|].
  intros ms' mo' (a & s' & HQ & HR & HM'). exists a, s'. auto.
Qed.

End MSpec.

Arguments assn St : clear implicits.
Arguments mspec {St A} P m Q.
End ImplSCPS.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
Module NodesSoundDec.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_vmmaps_with_vmmaps : forall h mo, m_vmmaps (with_vmmaps h mo) = h.
Proof. reflexivity. Qed.

Lemma m_vmmaps_with_vm_backing : forall l p mo, m_vmmaps (with_vm_backing l p mo) = m_vmmaps mo.
Proof. reflexivity. Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi mo, m_vmmaps (vm_forget_range lo hi mo) = m_vmmaps mo.
Proof. reflexivity. Qed.

Lemma m_vmmaps_forget_vm_ranges : forall rs mo, m_vmmaps (forget_vm_ranges rs mo) = m_vmmaps mo.
Proof.
  induction rs as [|[a n] rs IH]; intros mo; cbn [forget_vm_ranges]; [reflexivity|].
  rewrite IH. apply m_vmmaps_vm_forget_range.
Qed.

(* [comment removed for export] *)
Lemma anstep_init_sp : forall n mo rsp mo', anstep n mo rsp mo' ->
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo).
Proof.
  intros n mo rsp mo' H; destruct n; cbn [anstep] in H; try contradiction.
  - destruct H as (r & _ & _ & ->). unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges. reflexivity.
  - destruct H as [(e & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | (_ & _ & [(_ & ->) | (e & _ & _ & ->)])]]];
      reflexivity.
  - destruct H as [_ ->]. reflexivity.
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; reflexivity.
  - destruct H as [(_ & _ & ->) | (_ & [(e & _ & _ & ->) | [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & d & _ & _ & ->)]]])];
      reflexivity.
Qed.

Lemma anstep_alloc_top : forall n mo rsp mo', anstep n mo rsp mo' ->
  alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).
Proof. intros n mo rsp mo' H. unfold alloc_top. rewrite (anstep_init_sp n mo rsp mo' H). reflexivity. Qed.

Lemma errno_range_ENOMEM : 1 <= ENOMEM <= 4095.
Proof. unfold ENOMEM. lia. Qed.

Lemma In_single_ENOMEM : forall e l, l = [ENOMEM] -> In e l -> e = ENOMEM.
Proof. intros e l -> [<-|[]]. reflexivity. Qed.

(* [comment removed for export] *)
Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
  exists e sz, In (e, sz) maps /\ bv_unsigned e <= fst iv /\ snd iv <= bv_unsigned e + bv_unsigned sz.

Lemma region_free_In_disj : forall maps (a n : word) e sz,
  region_free maps a n = true -> In (e, sz) maps ->
  bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
  inversion E; subst. unfold iv_overlap in H1.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
  destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma avoids_of_region_free : forall maps (a n : word) avoid,
  region_free maps a n = true ->
  Forall (covered maps) avoid ->
  avoids (bv_unsigned a) (bv_unsigned n) avoid = true.
Proof.
  intros maps a n avoid Hrf Hc. unfold avoids. apply forallb_forall. intros [lo hi] Hin.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (e & sz & He & H1 & H2). cbn in H1, H2. cbn [fst snd].
  pose proof (region_free_In_disj _ _ _ _ _ Hrf He) as [H|H].
  - apply orb_true_intro. left. apply Z.leb_le. lia.
  - apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

Lemma mmap_addr_ok_intro : forall len avoid (a : word) maps,
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + mmap_len len <= alloc_ceiling ->
  region_free maps a (Z_to_bv 64 (mmap_len len)) = true -> 0 <= mmap_len len < 2^64 ->
  Forall (covered maps) avoid ->
  mmap_addr_ok len avoid (bv_unsigned a) = true.
Proof.
  intros len avoid a maps Hal Hpos Hce Hrf Hn Hcov. unfold mmap_addr_ok.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos), (proj2 (Z.leb_le _ _) Hce). cbn [andb].
  rewrite <- (u64_of_Z (mmap_len len)) at 1 by lia.
  apply (avoids_of_region_free maps); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Brk.
  Variable mo : Model.
  Let h := m_vmmaps mo.

  (* [comment removed for export] *)
  Lemma anstep_dec_brk0 : forall rsp mo',
    anstep (NBrk 0) mo rsp mo' ->
    dec_brk0 rsp = Some (bv_unsigned (vm_brk h)) /\
    m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
  Proof.
    intros rsp mo' H. cbn [anstep] in H. destruct H as (r & Hok & -> & ->).
    assert (Hr : r = vm_brk h).
    { unfold brk_r_ok in Hok. change (w_is0 (Z_to_bv 64 0)) with true in Hok. cbn [orb] in Hok. apply bv_eqb_eq in Hok. exact Hok. }
    subst r. split.
    - unfold dec_brk0. unfold brk_zeros, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb].
      unfold brk_unmaps. cbv zeta. unfold brk_page_range. rewrite Z.ltb_irrefl.
      destruct (0 <? bv_unsigned (vm_brk (m_vmmaps mo))); reflexivity.
    - unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges, m_vmmaps_with_vmmaps.
      unfold brk_model_next, brk_maps_next. fold h. rewrite Z.ltb_irrefl, andb_false_r.
      unfold brk_grants, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb app].
      unfold brk_unmaps. cbv zeta. unfold brk_page_range. rewrite Z.ltb_irrefl.
      destruct (0 <? bv_unsigned (vm_brk h)); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma anstep_dec_brk : forall (req : Z) rsp mo',
    let b := bv_unsigned (vm_brk h) in
    0 < b -> bv_unsigned (vm_start_brk h) <= b -> b < req < 2^64 ->
    anstep (NBrk req) mo rsp mo' ->
    exists a, dec_brk b req rsp = Some a /\
    match a with
    | BrkSame =>
        rsp = eff0 (vm_brk h) /\
        m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
    | BrkGrown =>
        brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true /\
        rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages b req)) /\
        m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((vm_brk h, (Z_to_bv 64 req - vm_brk h)%bv) :: vm_maps h) (vm_noaccess h)
                         (vm_start_brk h) (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
    end.
  Proof.
    intros req rsp mo'. cbv zeta. intros Hb Hsb Hreq H. cbn [anstep] in H. destruct H as (r & Hok & -> & ->).
    set (bw := vm_brk h) in *. set (b := bv_unsigned bw) in *.
    assert (E1 : w_is0 (Z_to_bv 64 req) = false) by (apply w_is0_false; lia).
    unfold brk_r_ok in Hok. rewrite E1 in Hok. cbn [orb] in Hok. unfold min_brk in Hok. fold h in Hok. fold bw in Hok.
    rewrite (u64_of_Z req) in Hok by lia. fold b in Hok.
    rewrite (proj2 (Z.ltb_ge req (bv_unsigned (vm_start_brk h)))) in Hok by lia.
    rewrite (proj2 (Z.ltb_ge req b)) in Hok by lia.
    apply andb_prop in Hok as [Hr Hg].
    assert (Hmono : page_round_up_Z b <= page_round_up_Z req).
    { unfold page_round_up_Z, page_size. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
    assert (Hnu : brk_unmaps r bw = [] /\ (r = Z_to_bv 64 req \/ r = bw)).
    { apply orb_prop in Hr as [Hr|Hr]; apply bv_eqb_eq in Hr; subst r; (split; [|auto]);
        unfold brk_unmaps; cbv zeta; unfold brk_page_range; fold b; rewrite ?(u64_of_Z req) by lia.
      - rewrite (proj2 (Z.ltb_ge (page_round_up_Z req) (page_round_up_Z b)) Hmono). destruct (0 <? b); reflexivity.
      - rewrite Z.ltb_irrefl. destruct (0 <? b); reflexivity. }
    destruct Hnu as [Hum Hr']. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges, m_vmmaps_with_vmmaps.
    fold h. fold bw. rewrite Hum.
    destruct Hr' as [-> | ->].
    - (* [comment removed for export] *)
      exists BrkGrown.
      assert (Hz : brk_zeros (Z_to_bv 64 req) (Z_to_bv 64 req) bw = zeros_of (brk_new_pages b req)).
      { unfold brk_zeros, brk_is_grow. rewrite E1. cbn [negb andb]. fold b.
        rewrite (proj2 (Z.ltb_lt 0 b) Hb), (u64_of_Z req) by lia. rewrite (proj2 (Z.ltb_lt b req)) by lia. cbn [andb].
        unfold brk_page_range, brk_new_pages, zeros_of. cbv zeta.
        destruct (page_round_up_Z b <? page_round_up_Z req); reflexivity. }
      split.
      + unfold dec_brk. rewrite (u64_of_Z req) by lia.
        replace (req =? b) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
        rewrite Z.eqb_refl, Hz. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
      + split; [exact Hg|]. split; [rewrite Hz; reflexivity|].
        unfold brk_model_next, brk_maps_next. fold h. fold bw. fold b. rewrite (u64_of_Z req) by lia.
        rewrite (proj2 (Z.ltb_ge req b)) by lia. rewrite andb_false_r.
        unfold brk_grants, brk_is_grow. rewrite E1. cbn [negb andb]. fold b.
        rewrite (proj2 (Z.ltb_lt 0 b) Hb), (u64_of_Z req) by lia. rewrite (proj2 (Z.ltb_lt b req)) by lia. cbn [andb app].
        rewrite Hum. unfold maps_subtract_ranges. cbn [fold_left]. reflexivity.
    - (* [comment removed for export] *)
      exists BrkSame.
      assert (Hz : brk_zeros (Z_to_bv 64 req) bw bw = []).
      { unfold brk_zeros, brk_is_grow. fold b. rewrite Z.ltb_irrefl, !andb_false_r. reflexivity. }
      split.
      + unfold dec_brk. rewrite Hz. fold b. rewrite Z.eqb_refl. reflexivity.
      + split; [rewrite Hz; reflexivity|].
        unfold brk_model_next, brk_maps_next. fold h. fold bw. fold b. rewrite Z.ltb_irrefl, andb_false_r.
        unfold brk_grants, brk_is_grow. fold b. rewrite Z.ltb_irrefl, !andb_false_r. cbn [app].
        rewrite Hum. unfold maps_subtract_ranges. cbn [fold_left]. reflexivity.
  Qed.
End Brk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Mmap.
  Variable mo : Model.
  Let h := m_vmmaps mo.

  Lemma mmap_len_u64 : forall len, 0 < len -> mmap_len len <= alloc_ceiling -> 0 <= mmap_len len < 2^64.
  Proof.
    intros len Hl Hc. pose proof (mmap_len_ge len).
    pose proof (@alloc_ceiling_lt ACEIL). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma anstep_dec_mmap : forall len avoid rsp mo',
    0 < len -> Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
    alloc_top h <= alloc_ceiling ->   (* [comment removed for export] *)
    anstep (NMmap 0 len mm_prot_rw mm_flags_anon) mo rsp mo' ->
    exists x, dec_mmap len avoid rsp = Some x /\
    match x with
    | MmErr e => e = ENOMEM /\ mo' = mo
    | MmOk a =>
        let aw := Z_to_bv 64 a in let n := Z_to_bv 64 (mmap_len len) in
        mmap_addr_ok len avoid a = true /\ 0 < a /\ a + mmap_len len <= alloc_ceiling /\
        region_free (vm_reserved h ++ vm_maps h) aw n = true /\
        vm_backing_used mo + mmap_len len <= vm_limit h /\
        m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((aw, n) :: vm_maps h) (vm_noaccess h)
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
    end.
  Proof.
    intros len avoid rsp mo' Hlen Hcov Hlink H. cbn [anstep] in H.
    destruct H as [(e & He & -> & ->) | [(_ & _ & a & Hg & -> & ->) | [(Hc & _) | (Hc & _)]]];
      [| | exfalso; unfold mm_prot_rw, mm_prot_none in Hc; discriminate | exfalso; unfold mm_prot_rw, mm_prot_none in Hc; discriminate].
    - destruct He as [He _]. apply (In_single_ENOMEM e) in He; [|reflexivity]. subst e.
      exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap, efferr, eff0. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    - destruct Hg as (Hal & Hpos & Hce & Hrf & Hbud). fold h in Hce. assert (Hce' : bv_unsigned a + mmap_len len <= alloc_ceiling) by lia.
      assert (Hok : mmap_addr_ok len avoid (bv_unsigned a) = true).
      { apply (mmap_addr_ok_intro len avoid a (vm_reserved h ++ vm_maps h)); try assumption.
        pose proof (mmap_len_ge len). pose proof (@alloc_ceiling_lt ACEIL).
        pose proof (bv_unsigned_in_range 64 a). lia. }
      exists (MmOk (bv_unsigned a)). split.
      + unfold dec_mmap. cbn [eff_ret]. rewrite !bv_eqb_refl, Hok. reflexivity.
      + cbv zeta. rewrite Z_to_bv_bv_unsigned. repeat split; try assumption.
        all: try (apply Z.leb_le; exact Hbud).
  Qed.

  (* [comment removed for export] *)
  Lemma anstep_dec_mmap_none : forall len avoid rsp mo',
    0 < len -> Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
    alloc_top h <= alloc_ceiling ->   (* [comment removed for export] *)
    anstep (NMmap 0 len mm_prot_none mm_flags_anon) mo rsp mo' ->
    exists x, dec_mmap_none len avoid rsp = Some x /\
    match x with
    | MmErr e => e = ENOMEM /\ mo' = mo
    | MmOk a =>
        let aw := Z_to_bv 64 a in let n := Z_to_bv 64 (mmap_len len) in
        mmap_addr_ok len avoid a = true /\ 0 < a /\ a + mmap_len len <= alloc_ceiling /\
        region_free (vm_reserved h ++ vm_maps h) aw n = true /\
        m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((aw, n) :: vm_maps h) ((aw, n) :: vm_noaccess h)
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
    end.
  Proof.
    intros len avoid rsp mo' Hlen Hcov Hlink H. cbn [anstep] in H.
    destruct H as [(e & He & -> & ->) | [(Hc & _) | [(_ & _ & a & Hg & -> & ->) | (_ & Hc & _)]]];
      [| exfalso; unfold mm_prot_rw, mm_prot_none in Hc; discriminate | | exfalso; unfold mm_flags_anon, mm_flags_fixed in Hc; discriminate].
    - destruct He as [He _]. apply (In_single_ENOMEM e) in He; [|reflexivity]. subst e.
      exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap_none, efferr, eff0. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    - destruct Hg as (Hal & Hpos & Hce & Hrf). fold h in Hce. assert (Hce' : bv_unsigned a + mmap_len len <= alloc_ceiling) by lia.
      assert (Hok : mmap_addr_ok len avoid (bv_unsigned a) = true).
      { apply (mmap_addr_ok_intro len avoid a (vm_reserved h ++ vm_maps h)); try assumption.
        pose proof (mmap_len_ge len). pose proof (@alloc_ceiling_lt ACEIL).
        pose proof (bv_unsigned_in_range 64 a). lia. }
      exists (MmOk (bv_unsigned a)). split.
      + unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
      + cbv zeta. rewrite Z_to_bv_bv_unsigned. repeat split; try assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma anstep_mmap_fixed_cases : forall addr len rsp mo',
    anstep (NMmap addr len mm_prot_none mm_flags_fixed) mo rsp mo' ->
    let aw := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
    let lo := bv_unsigned aw in let hi := lo + bv_unsigned n in
       (exists e, e = ENOMEM /\ rsp = efferr e /\ mo' = mo)
    \/ (rsp = mkEffectU aw [] [] [(aw, n)] [] [] /\
        m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, n) :: maps_subtract (vm_noaccess h) lo hi)
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))
    \/ (exists e, e = ENOMEM /\ rsp = mkEffectU (errno_ret e) [] [] [(aw, n)] [] [] /\
        m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) lo hi) (maps_subtract (vm_noaccess h) lo hi)
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
    (* [comment removed for export] *)
  Proof.
    intros addr len rsp mo' H. cbn [anstep] in H. cbv zeta.
    destruct H as [(e & He & -> & ->) | [(Hc & _) | [(_ & Hc & _) | (_ & _ & [(-> & ->) | (e & He & -> & ->)])]]];
      [| exfalso; unfold mm_prot_rw, mm_prot_none in Hc; discriminate | exfalso; unfold mm_flags_anon, mm_flags_fixed in Hc; discriminate | | ].
    - left. exists e. split; [exact (In_single_ENOMEM e _ eq_refl (proj1 He))|]. auto.
    - right; left. split; [reflexivity|]. unfold mm_fixed_model. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - destruct He.   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma anstep_mmap_fixed_only : forall addr len rsp mo',
    anstep (NMmap addr len mm_prot_none mm_flags_fixed) mo rsp mo' ->
    let aw := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
    let lo := bv_unsigned aw in let hi := lo + bv_unsigned n in
    rsp = mkEffectU aw [] [] [(aw, n)] [] [] /\
    m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, n) :: maps_subtract (vm_noaccess h) lo hi)
                     (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
  Proof.
    intros addr len rsp mo' H. cbn [anstep] in H. cbv zeta.
    destruct H as [(e & [_ Hc] & _) | [(Hc & _) | [(_ & Hc & _) | (_ & _ & [(-> & ->) | (e & [] & _)])]]];
      [ rewrite mm_refusable_fixed in Hc; discriminate Hc
      | exfalso; unfold mm_prot_rw, mm_prot_none in Hc; discriminate
      | exfalso; unfold mm_flags_anon, mm_flags_fixed in Hc; discriminate | ].
    split; [reflexivity|]. unfold mm_fixed_model. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma anstep_mmap_rw_forced : forall len rsp mo',
    anstep (NMmap 0 len mm_prot_rw mm_flags_anon) mo rsp mo' ->
    (mm_refusable mo mm_prot_rw mm_flags_anon (mmap_len len) = true /\ rsp = efferr ENOMEM /\ mo' = mo)
    \/ (mm_refusable mo mm_prot_rw mm_flags_anon (mmap_len len) = false /\
        exists a, mm_grant_rw mo (Z_to_bv 64 0) a (mmap_len len) /\ rsp = mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))]).
  Proof.
    intros len rsp mo' H. cbn [anstep] in H.
    destruct H as [(e & [He Hf] & -> & ->) | [(_ & _ & a & Hg & -> & ->) | [(Hc & _) | (Hc & _)]]];
      [| | exfalso; unfold mm_prot_rw, mm_prot_none in Hc; discriminate | exfalso; unfold mm_prot_rw, mm_prot_none in Hc; discriminate].
    - left. rewrite (In_single_ENOMEM e _ eq_refl He). auto.
    - right. split; [exact (mm_grant_rw_not_refusable _ _ _ _ Hg)|]. exists a. auto.
  Qed.

  Lemma anstep_mmap_none_forced : forall len rsp mo',
    anstep (NMmap 0 len mm_prot_none mm_flags_anon) mo rsp mo' ->
    (mm_refusable mo mm_prot_none mm_flags_anon (mmap_len len) = true /\ rsp = efferr ENOMEM /\ mo' = mo)
    \/ (mm_refusable mo mm_prot_none mm_flags_anon (mmap_len len) = false /\
        exists a, mm_grant_none mo (Z_to_bv 64 0) a (mmap_len len) /\ rsp = mkEffectU a [] [] [(a, Z_to_bv 64 (mmap_len len))] [] []).
  Proof.
    intros len rsp mo' H. cbn [anstep] in H.
    destruct H as [(e & [He Hf] & -> & ->) | [(Hc & _) | [(_ & _ & a & Hg & -> & ->) | (_ & Hc & _)]]];
      [| exfalso; unfold mm_prot_rw, mm_prot_none in Hc; discriminate | | exfalso; unfold mm_flags_anon, mm_flags_fixed in Hc; discriminate].
    - left. rewrite (In_single_ENOMEM e _ eq_refl He). auto.
    - right. split; [exact (mm_grant_none_not_refusable _ _ _ _ Hg)|]. exists a. auto.
  Qed.
End Mmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma anstep_dec_munmap : forall mo addr len rsp mo',
  anstep (NMunmap addr len) mo rsp mo' ->
  let h := m_vmmaps mo in
  let aw := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  dec_munmap addr len rsp = Some (RgDone true) /\
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw)
                   (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros mo addr len rsp mo' H. cbn [anstep] in H. destruct H as [-> ->]. cbv zeta. split.
  - unfold dec_munmap. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.eqb_refl, !bv_eqb_refl. reflexivity.
  - unfold mm_unmapped_model. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
Qed.

Lemma anstep_dec_mprotect : forall mo addr len rsp mo',
  anstep (NMprotect addr len mm_prot_rw) mo rsp mo' ->
  let h := m_vmmaps mo in
  let aw := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => e = ENOMEM /\ mo' = mo
  | RgDone false => False
  | RgDone true =>
      mprotect_budget_ok mo aw n = true /\
      m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                       (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros mo addr len rsp mo' H. cbn [anstep] in H. cbv zeta.
  destruct H as [(e & He & -> & ->) | (Hb & -> & ->)].
  - destruct He as [He _]. apply (In_single_ENOMEM e) in He; [|reflexivity]. subst e. exists (RgErr ENOMEM). split; [|auto].
    unfold dec_mprotect, efferr, eff0. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - exists (RgDone true). split.
    + unfold dec_mprotect. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.eqb_refl, !bv_eqb_refl. reflexivity.
    + split; [exact Hb|]. unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma anstep_dec_mremap : forall mo old ol nl avoid rsp mo',
  let h := m_vmmaps mo in
  let onZ := mmap_len ol in let nnZ := mmap_len nl in
  let o := Z_to_bv 64 old in let on := Z_to_bv 64 onZ in let nn := Z_to_bv 64 nnZ in
  0 <= old -> 0 < ol -> 0 < nl -> old + onZ <= alloc_ceiling ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  alloc_top h <= alloc_ceiling ->   (* [comment removed for export] *)
  anstep (NMremap old ol nl MREMAP_MAYMOVE) mo rsp mo' ->
  exists x, dec_mremap old ol nl avoid rsp = Some x /\
  match x with
  | MrErr e => e = ENOMEM /\ mo' = mo /\ onZ <> nnZ
  | MrInPlace =>
      (onZ = nnZ /\ mo' = mo)
      \/ (onZ <> nnZ /\ (onZ < nnZ -> mremap_inplace_grow_b mo o on nn onZ nnZ = true) /\
          m_vmmaps mo' = mremap_maps_next h o o nn)
  | MrMoved d =>
      onZ < nnZ /\ d <> old /\ mmap_addr_ok nnZ avoid d = true /\
      mremap_fresh_b mo onZ nnZ o on (Z_to_bv 64 d) nn = true /\
      m_vmmaps mo' = mremap_maps_next h o (Z_to_bv 64 d) nn
  end.
Proof.
  intros mo old ol nl avoid rsp mo'. cbv zeta. intros Hold Hol Hnl Hce Hcov Hlink H. cbn [anstep] in H.
  pose proof (@alloc_ceiling_lt ACEIL) as Hcv.
  pose proof (mmap_len_ge ol) as Hge1. pose proof (mmap_len_ge nl) as Hge2.
  assert (Hmm : forall o' on' d nn', m_vmmaps (mremap_model_next mo o' on' d nn') = mremap_maps_next (m_vmmaps mo) o' d nn').
  { intros. unfold mremap_model_next, vm_resize_backing. rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps. reflexivity. }
  assert (Hnn : mmap_len (mmap_len nl) = mmap_len nl) by (apply mmap_len_of_aligned, mmap_len_aligned).
  destruct H as [(E & -> & ->) | (Ene & [(e & He & -> & ->) | [(Hlt & -> & ->) | [(Hlt & Hig & -> & ->) | (Hlt & d & Hd & -> & ->)]]])].
  - (* [comment removed for export] *)
    exists MrInPlace. split; [|left; auto].
    unfold dec_mremap, eff0. cbv zeta. rewrite errno_of_lit by lia.
    rewrite bv_eqb_refl, (proj2 (Z.eqb_eq _ _) E). reflexivity.
  - (* [comment removed for export] *)
    apply (In_single_ENOMEM e) in He; [|reflexivity]. subst e.
    exists (MrErr ENOMEM). split; [|auto]. unfold dec_mremap, efferr, eff0. cbv zeta.
    rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - (* [comment removed for export] *)
    exists MrInPlace. split; [|right; split; [exact Ene|]; split; [intros; lia | apply Hmm]].
    unfold dec_mremap. cbv zeta.
    replace ((Z_to_bv 64 old + Z_to_bv 64 (mmap_len nl))%bv) with (Z_to_bv 64 (old + mmap_len nl) : word) by (symmetry; apply lit_add_lit).
    rewrite !bv_eqb_refl, (proj2 (Z.ltb_lt _ _) Hlt). reflexivity.
  - (* [comment removed for export] *)
    exists MrInPlace. split; [|right; split; [exact Ene|]; split; [intros; exact Hig | apply Hmm]].
    unfold dec_mremap. cbv zeta. rewrite lit_add_lit, !bv_eqb_refl, (proj2 (Z.ltb_lt _ _) Hlt). reflexivity.
  - (* [comment removed for export] *)
    pose proof Hd as Hd'. unfold mremap_fresh_b in Hd. cbv zeta in Hd.
    apply andb_prop in Hd as [Hd H6]. apply andb_prop in Hd as [Hd H5].
    apply andb_prop in Hd as [Hd H4]. apply andb_prop in Hd as [Hd H3]. apply andb_prop in Hd as [H1 H2].
    apply Z.eqb_eq in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
    assert (H4c : bv_unsigned d + mmap_len nl <= alloc_ceiling) by (unfold mmap_len in *; lia).
    assert (Hne : bv_unsigned d <> old).
    { intros E. apply Bool.negb_true_iff in H1. apply (proj1 (bv_eqb_neq' _ _)) in H1 || idtac.
      assert (d = Z_to_bv 64 old) by (rewrite <- E, Z_to_bv_bv_unsigned; reflexivity).
      subst d. rewrite bv_eqb_refl in H1. discriminate. }
    assert (Hok : mmap_addr_ok (mmap_len nl) avoid (bv_unsigned d) = true).
    { unfold mmap_addr_ok. rewrite Hnn, (proj2 (Z.eqb_eq _ _) H2), (proj2 (Z.ltb_lt _ _) H3), (proj2 (Z.leb_le _ _) H4c). cbn [andb].
      rewrite <- (u64_of_Z (mmap_len nl)) at 1 by lia. apply (avoids_of_region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))); assumption. }
    exists (MrMoved (bv_unsigned d)). split.
    + unfold dec_mremap. cbv zeta.
      replace ((d + Z_to_bv 64 (mmap_len ol))%bv) with (Z_to_bv 64 (bv_unsigned d + mmap_len ol) : word)
        by (rewrite <- (Z_to_bv_bv_unsigned d) at 2; symmetry; apply lit_add_lit).
      rewrite !bv_eqb_refl, (proj2 (Z.ltb_lt _ _) Hlt), Hok.
      replace (bv_unsigned d =? old) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hlt|]. split; [exact Hne|]. split; [exact Hok|]. split; [exact Hd'| apply Hmm].
Qed.


End CeilWrap.
End NodesSoundDec.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mprotect.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
Module KStep2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound NodesSoundDec ImplSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_ge' : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. split; [apply NodesSound.mmap_len_ge| apply NodesSound.mmap_len_lt]. Qed.

Lemma mmap_len_pos_pg : forall l, 0 < l -> PGSZ <= mmap_len l.
Proof.
  intros l Hl. pose proof (mmap_len_ge' l Hl). pose proof (NodesSound.mmap_len_aligned l).
  pose proof (Z_div_mod_eq_full (mmap_len l) 4096). unfold PGSZ. nia.
Qed.

Lemma u64_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> elo (went b n) = b /\ ehi (went b n) = b + n.
Proof. intros. unfold elo, ehi, went. cbn [fst snd]. rewrite !unsigned_lit by assumption. split; reflexivity. Qed.

Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

Lemma is_errno_form_neg : forall e, 1 <= e <= 4095 -> is_errno_form (neg_errno e) = true.
Proof. intros e He. unfold is_errno_form, neg_errno, TWO64. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
Lemma is_err_neg : forall e, 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof. intros e He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pwdisj_In : forall l e1 e2, pwdisj l -> In e1 l -> In e2 l -> e1 = e2 \/ edisj e1 e2.
Proof.
  induction l as [|e l IH]; intros e1 e2 Hp H1 H2; [destruct H1|].
  inversion Hp; subst. destruct H1 as [<-|H1], H2 as [<-|H2].
  - left; reflexivity.
  - right. apply H3. exact H2.
  - right. pose proof (H3 _ H1) as D. unfold edisj in *. lia.
  - apply IH; assumption.
Qed.

Lemma region_free_app_l : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [reflexivity|]. cbn in H |- *. apply andb_prop in H as [H1 H]. rewrite H1, (IH _ _ _ H). reflexivity. Qed.

Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|]. cbn in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
  bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn [fst snd]. eapply region_free_In_disj; eauto. Qed.

Lemma region_free_intro_Z : forall maps a n,
  (forall e, In e maps -> bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a) ->
  region_free maps a n = true.
Proof.
  intros maps a n H. apply region_free_intro. intros b sz Hin. specialize (H _ Hin). unfold elo, ehi in H. cbn in H.
  unfold iv_overlap. apply andb_false_iff.
  destruct H as [H|H]; [right| left]; apply Z.ltb_ge; lia.
Qed.

Lemma region_free_shrink : forall maps a n n', region_free maps a n' = true ->
  bv_unsigned n <= bv_unsigned n' -> region_free maps a n = true.
Proof.
  intros maps a n n' H Hle. apply region_free_intro_Z. intros e Hin.
  pose proof (region_free_disj _ _ _ _ H Hin) as D. lia.
Qed.

Lemma vmwf_cons : forall maps a n, vmwf maps ->
  bv_unsigned a < bv_unsigned a + bv_unsigned n <= 2^64 ->
  region_free maps a n = true ->
  vmwf ((a, n) :: maps).
Proof.
  intros maps a n [Hb Hp] Hn Hrf. split.
  - intros e [<-|Hin]; [unfold elo, ehi; cbn; lia| apply Hb; exact Hin].
  - constructor; [|exact Hp]. intros e' Hin. pose proof (region_free_disj _ _ _ _ Hrf Hin). unfold edisj, elo, ehi in *. cbn [fst snd]. lia.
Qed.

Lemma pwdisj_filter : forall (f : word * word -> bool) l, pwdisj l -> pwdisj (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
  - constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply IH; assumption.
Qed.

Lemma vmwf_remove : forall maps a, vmwf maps -> vmwf (map_remove maps a).
Proof.
  intros maps a [Hb Hp]. unfold map_remove. split.
  - intros e Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply pwdisj_filter. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
  intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn [fst snd]. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In : forall maps lo hi e, In e (maps_subtract maps lo hi) ->
  exists e0, In e0 maps /\ In e (iv_subtract (fst e0) (snd e0) lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
  cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity| exact Hin].
  - destruct (IH _ _ _ Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0| exact H1].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall a sz lo hi,
  bv_unsigned a < bv_unsigned a + bv_unsigned sz <= 2^64 -> lo < hi ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hwf Hlh Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [app]. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keep : forall maps lo hi e, (forall e, In e maps -> elo e < ehi e <= 2^64) -> lo < hi ->
  In e maps -> (ehi e <= lo \/ hi <= elo e) -> In e (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hb Hlh Hin Hd; [destruct Hin|].
  cbn. apply in_or_app. destruct Hin as [<-|Hin].
  - left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + unfold elo, ehi in Hd. cbn in Hd. lia.
  - right. apply IH; auto. intros e' H'; apply Hb; right; exact H'.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_contains : forall a sz lo hi x y,
  lo < hi < 2^64 ->
  bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz ->
  (y <= lo \/ hi <= x) ->
  exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
  intros a sz lo hi x y Hlh Hax Hxy Hy Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; left; left; reflexivity|]. unfold elo, ehi; cbn [fst snd].
    destruct (Z.le_gt_cases (lo - bv_unsigned a) (bv_unsigned sz)).
    + rewrite Z.min_r by lia. rewrite unsigned_lit by lia. lia.
    + rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. lia.
  - replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; right; left; reflexivity|]. unfold elo, ehi; cbn [fst snd].
    destruct (Z.le_gt_cases hi (bv_unsigned a)).
    + rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
      rewrite !Z_to_bv_bv_unsigned. lia.
    + rewrite Z.max_r by lia. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In_intro : forall maps lo hi e e', In e maps -> In e' (iv_subtract (fst e) (snd e) lo hi) ->
  In e' (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e e' Hin H'; [destruct Hin|].
  cbn. apply in_or_app. destruct Hin as [<-|Hin]; [left; exact H'| right; eapply IH; eauto].
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_contains : forall maps lo hi e x y,
  lo < hi < 2^64 -> In e maps -> elo e <= x -> x < y -> y <= ehi e -> (y <= lo \/ hi <= x) ->
  exists e', In e' (maps_subtract maps lo hi) /\ elo e' <= x /\ y <= ehi e'.
Proof.
  intros maps lo hi e x y Hlh He H1 H2 H3 H4.
  destruct (iv_subtract_contains (fst e) (snd e) lo hi x y Hlh H1 H2 H3 H4) as (e' & He' & Hr).
  exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
Qed.

Lemma pwdisj_app : forall P R, pwdisj P -> pwdisj R -> (forall p r, In p P -> In r R -> edisj p r) -> pwdisj (P ++ R).
Proof.
  induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
  - intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
  - apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.

Lemma iv_subtract_pwdisj : forall a sz lo hi, lo < hi < 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlh. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn [fst snd]. left.
    rewrite Z.min_r by lia. rewrite Z.max_r by lia. rewrite !unsigned_lit by lia. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, lo < hi < 2^64 -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlh Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; exact Hlh| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
    destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.

(* [comment removed for export] *)
Lemma wcov_rf_disj : forall maps lo hi aw nw,
  wcov maps lo hi -> region_free maps aw nw = true -> 0 < bv_unsigned nw -> lo < hi ->
  bv_unsigned aw + bv_unsigned nw <= lo \/ hi <= bv_unsigned aw.
Proof.
  intros maps lo hi aw nw Hc Hrf Hn Hlh.
  destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
  destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
  destruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr).
  pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.

Lemma region_free_above : forall maps aw nw, (forall e, In e maps -> ehi e <= bv_unsigned aw) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi in H; cbn in H.
  replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kl_open HK := destruct HK as [Klazy Kmat Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kna Klim Kcov Kph Ktop].

Lemma went_In_bounds : forall L pbrk mo b l, KL L pbrk mo ->
  (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
  0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))
  /\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
  intros L pbrk mo b l K Hin. pose proof alloc_ceiling_lt.
  assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))) as (Hl & Hb & Hc & Hm).
  { destruct Hin as [Hin|[k Hin]].
    - pose proof (kl_groups _ _ _ K _ _ Hin) as (A1 & A2 & A3 & A4 & A5 & _). auto.
    - pose proof (kl_metas _ _ _ K _ _ _ Hin) as (A1 & A2 & A3 & A4 & _ & _ & A5 & _). auto. }
  pose proof (mmap_len_ge' l ltac:(lia)). destruct (u64_went b (mmap_len l) ltac:(lia) ltac:(lia)) as [E1 E2].
  splits; auto; lia.
Qed.

Lemma In_lranges : forall L x, In x (lranges L) ->
  In x (ld_resv L)
  \/ (exists b l, In (b, l) (ld_groups L) /\ x = (b, round_up_pg l))
  \/ (exists b l k, In (b, l, k) (ld_metas L) /\ x = (b, round_up_pg l))
  \/ (exists b l, ld_brkreg L = Some (b, l) /\ x = (b + PGSZ, round_up_pg l - PGSZ)).
Proof.
  intros L x Hin. unfold lranges in Hin. rewrite !in_app_iff in Hin. destruct Hin as [H|[H|[H|H]]].
  - left; exact H.
  - right; left. apply in_map_iff in H as ([b l] & <- & H). exists b, l. auto.
  - right; right; left. apply in_map_iff in H as ([[b l] k] & <- & H). exists b, l, k. auto.
  - right; right; right. destruct (ld_brkreg L) as [[b l]|]; [|destruct H]. destruct H as [<-|[]]. exists b, l. auto.
Qed.

(* [comment removed for export] *)
Lemma lranges_rf_disj : forall L pbrk mo lo m aw nw,
  KL L pbrk mo ->
  let h := m_vmmaps mo in
  region_free (vm_reserved h ++ vm_maps h) aw nw = true -> 0 < bv_unsigned nw ->
  (forall b l, ld_brkreg L = Some (b, l) -> bv_unsigned aw + bv_unsigned nw <= b + PGSZ \/ b + l <= bv_unsigned aw) ->
  In (lo, m) (lranges L) -> bv_unsigned aw + bv_unsigned nw <= lo \/ lo + m <= bv_unsigned aw.
Proof.
  intros L pbrk mo lo m aw nw HK h Hrf Hnw Hbrk Hin. pose proof alloc_ceiling_lt as Hcl.
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    pose proof (region_free_disj _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. unfold elo, ehi in D. cbn in D. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6 in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6 in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. pose proof (kl_brkreg _ _ _ HK b1 l1 H) as (R1 & R2 & R3 & R4 & R5 & _).
    rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Hbrk b1 l1 H). lia.
Qed.

(* [comment removed for export] *)
Lemma KL_lbrk_pages_ok : forall L pbrk mo lo len,
  KL L pbrk mo ->
  let h := m_vmmaps mo in
  0 < lo -> 0 < len -> lo + len <= alloc_ceiling ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 lo) (Z_to_bv 64 len) = true ->
  (forall b l, ld_brkreg L = Some (b, l) -> b + l <= lo \/ lo + len <= b + PGSZ) ->
  lbrk_pages_ok L lo len = true.
Proof.
  intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof alloc_ceiling_lt as Hcl.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  pose proof (lranges_rf_disj L pbrk mo b0 m0 (Z_to_bv 64 lo) (Z_to_bv 64 len) HK Hrf ltac:(rewrite Ulen; lia)) as D.
  rewrite Ulo, Ulen in D. apply D; [|exact Hin]. intros b l E. pose proof (Hbrk b l E). lia.
Qed.

(* [comment removed for export] *)
Lemma KL_vm_eq : forall L pbrk mo mo',
  KL L pbrk mo -> m_vm_lazy mo' = [] -> m_vm_materialized mo' = [] ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
  vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) ->   (* [comment removed for export] *)
  KL L pbrk mo'.
Proof.
  intros L pbrk mo mo' K Hl Hm H1 H2 H3 H4 H5 H6 H7. kl_open K; constructor; unfold phase_inv, resv_disj, alloc_top in *; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6, ?H7; auto.
Qed.

Lemma brk_piece_rephase : forall L ph e, (forall cur, ld_brk L <> BPGuard cur) -> brk_piece L e -> brk_piece (set_brkph ph L) e.
Proof.
  intros L ph e Hng H. unfold brk_piece in *. cbn [ld_brkreg ld_brk set_brkph] in *.
  destruct (ld_brkreg L) as [[b l]|]; [exact H|]. destruct (ld_brk L); try contradiction. exfalso. eapply Hng. reflexivity.
Qed.

Lemma KL_rephase : forall L ph pbrk pbrk' mo,
  KL L pbrk mo -> (forall cur, ld_brk L <> BPGuard cur) -> phase_inv ph (set_brkph ph L) pbrk' mo -> KL (set_brkph ph L) pbrk' mo.
Proof.
  intros L ph pbrk pbrk' mo K Hng Hph. kl_open K; constructor; cbn; auto.
  intros e He. destruct (Kcov e He) as [G|[M|B]]; [left; exact G| right; left; exact M| right; right; apply brk_piece_rephase; auto].
Qed.

Lemma KL_dead : forall L pbrk pbrk' mo, KL L pbrk mo -> (forall cur, ld_brk L <> BPGuard cur) -> KL (set_brkph BPDead L) pbrk' mo.
Proof. intros. eapply KL_rephase; [eassumption| assumption| exact I]. Qed.

Lemma phase_quiet : forall L L' pbrk mo mo',
  KL L pbrk mo -> brk_quiet L -> ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) -> vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  phase_inv (ld_brk L') L' pbrk mo'.
Proof.
  intros L L' pbrk mo mo' HK Hq E1 E2 E3 E4. pose proof (kl_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv in *.
  rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

(* [comment removed for export] *)
Lemma anstep_books : forall n mo rsp mo', m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  anstep n mo rsp mo' -> m_vm_lazy mo' = [] /\ m_vm_materialized mo' = [] /\ vm_only mo mo'.
Proof.
  intros n mo rsp mo' Hl Hm Ha. split; [eapply anstep_lazy_nil; eauto|]. split; [eapply anstep_materialized_nil; eauto|].
  eapply anstep_vm_only; eauto.
Qed.

Lemma mspec_get_bind_eq {St A} (s0 : St) (P : assn St) (f : St -> Monad.M St A) Q :
  mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof. intros H s mo [-> HP]. unfold mbind, mget. cbn. apply H. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk0_ok : forall L s0 mo0, ld_brk L = BPUntried ->
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
        (ev_step_post L (EBrk 0) s0 mo0).
Proof.
  intros L s0 mo0 Hph.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ vm_only mo0 mo /\ brk0_answer_ok r = true /\ KL (set_brkph (BPQueried r) L) r mo)).
    { reflexivity. }
    intros s mo (-> & -> & HK). split; [cbn; lia|].
    intros rsp mo' Hst.
    pose proof (anstep_books _ _ _ _ (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK) Hst) as (Hl' & Hm' & Hvo).
    pose proof (anstep_dec_brk0 mo0 rsp mo' Hst) as [Hdec Evm].
    exists (bv_unsigned (vm_brk (m_vmmaps mo0))). split; [exact Hdec|].
    assert (HK' : KL L (ps_brk s0) mo').
    { eapply KL_vm_eq; [exact HK| exact Hl'| exact Hm'| | | | | | |]; rewrite Evm; reflexivity. }
    pose proof (kl_phase _ _ _ HK') as Kph. unfold phase_inv in Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
    pose proof (kl_start _ _ _ HK') as (S1 & S2 & S3 & S4).
    assert (Eb : vm_brk (m_vmmaps mo0) = vm_brk (m_vmmaps mo')) by (rewrite Evm; reflexivity). rewrite Eb.
    splits.
    - reflexivity.
    - exact Hvo.
    - unfold brk0_answer_ok. rewrite Ebrk. pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo'))) as R. unfold bv_modulus in R.
      unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - eapply KL_rephase; [exact HK'| intros cur E; rewrite Hph in E; discriminate|]. cbn [phase_inv set_brkph ld_brkreg]. rewrite Ebrk. splits; auto. }
  intros r. cbn beta. eapply mspec_bind.
  { apply mspec_upd. }
  intros []. apply mspec_ret. intros s mo (s1 & -> & -> & Hvo & Hans & HK). unfold ev_step_post. cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post Z.eqb].
  splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_sub_went : forall (w : word) req, bv_unsigned w < req < 2^64 ->
  (w, (Z_to_bv 64 req - w)%bv) = went (bv_unsigned w) (req - bv_unsigned w).
Proof.
  intros w req Hr. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. unfold went. f_equal.
  - symmetry. apply Z_to_bv_bv_unsigned.
  - apply bv_eq. rewrite bv_sub_unsigned, !unsigned_lit by lia. apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_facts : forall mo0 req,
  let h := m_vmmaps mo0 in
  let b := bv_unsigned (vm_brk h) in
  alloc_top h = alloc_ceiling ->
  0 < b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  brk_grow_ok mo0 (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  req <= alloc_ceiling /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req - b)) = true.
Proof.
  intros mo0 req h b Htop Hb Hreq Hba Hra H. unfold brk_grow_ok in H. fold h in H. rewrite unsigned_lit in H by lia. fold b in H.
  replace (0 <? b) with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. rewrite page_size_eq in H.
  replace ((b + 4096 - 1) / 4096 * 4096) with b in H.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req in H.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. rewrite Htop in H1.
  split; [exact H1|]. eapply region_free_shrink; [exact H2|].
  pose proof (alloc_ceiling_lt).
  rewrite !unsigned_lit by (unfold page_size in *; lia). unfold page_size. lia.
Qed.

Lemma ev_brk_grow1_ok : forall L s0 mo0 cur, ld_brk L = BPQueried cur ->
  let req := round_up_pg cur + 2 * PGSZ in
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) s0 mo0).
Proof.
  intros L s0 mo0 cur Hph req. pose proof alloc_ceiling_lt as Hcl.
  intros s mo (-> & -> & HK0). revert HK0.
  enough (H : mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (a <- msys (NBrk req) (dec_brk (ps_brk s0) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s0) end)
        (ev_step_post L (EBrk req) s0 mo0)).
  { intros HK0. apply (H s0 mo0). auto. }
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ vm_only mo0 mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
                match a with
                | BrkGrown => KL (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
                | BrkSame => KL (set_brkph BPDead L) cur mo
                end)).
    { reflexivity. }
    intros s mo (-> & -> & HK).
    pose proof (kl_phase _ _ _ HK) as Kph. unfold phase_inv in Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    split; [cbn; unfold PGSZ in *; lia|].
    intros rsp mo' Hst.
    pose proof (anstep_books _ _ _ _ (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK) Hst) as (Hl' & Hm' & Hvo).
    set (h := m_vmmaps mo0) in *.
    pose proof (anstep_dec_brk mo0 req rsp mo' ltac:(unfold h in *; lia) ltac:(unfold h in *; lia) ltac:(unfold h, PGSZ in *; lia) Hst) as (a & Hdec & Ha).
    fold h in Hdec, Ha. rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [exact Hvo|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    destruct a.
    - (* [comment removed for export] *)
      destruct Ha as (Hgo & _ & Evm).
      apply brk_grow_ok_facts in Hgo; [| exact (kl_top _ _ _ HK) | unfold h in *; lia| unfold h, PGSZ in *; lia| fold h; rewrite Ebrk, Ecur; exact S2| rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity].
      fold h in Hgo. destruct Hgo as [Hceil Hrf]. rewrite Ebrk in Hrf.
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KL_lbrk_pages_ok L (ps_brk s0) mo0 cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace (2 * PGSZ) with (req - cur) by lia. exact Hrf. }
      rewrite (bv_sub_went (vm_brk h) req) in Evm by (unfold h, PGSZ in *; lia). rewrite Ebrk in Evm.
      replace (req - cur) with (2 * PGSZ) in Hrf, Evm by lia.
      destruct (u64_went cur (2 * PGSZ) ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia)) as [U1 U2].
      assert (Ua : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; unfold PGSZ in *; lia).
      assert (Un : bv_unsigned (Z_to_bv 64 (2 * PGSZ)) = 2 * PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
      split; [|exact HPG]. subst h.
      kl_open HK. constructor; try assumption; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; try assumption.
      + apply vmwf_cons; [exact Kwf| rewrite Ua, Un; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; unfold PGSZ in *; lia.
      + intros b l Hin. specialize (Kgr b l Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). splits; auto. right; exact G5.
      + intros b l k Hin. specialize (Kme b l k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; auto. right; exact G7.
      + intros b l Hb. rewrite Ereg in Hb. discriminate.
      + intros e He. destruct (Kna e He) as [W [(b & l & k & Hin & Hlo & Hhi)|(b & l & E & _)]]; [| rewrite Ereg in E; discriminate].
        split; [exact W|]. left. exists b, l, k. auto.
      + intros e [<-|He]; [right; right; unfold brk_piece; cbn [ld_brkreg ld_brk set_brkph]; rewrite Ereg; reflexivity|].
        destruct (Kcov e He) as [G|[M|B]]; [left; exact G| right; left; exact M|].
        exfalso. unfold brk_piece in B. rewrite Ereg, Hph in B. exact B.
      + unfold phase_inv. cbn [ld_brkreg ld_groups ld_metas ld_brk set_brkph]. rewrite Evm. cbn [vm_maps vm_brk vm_start_brk].
        rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
        * left. reflexivity.
        * intros b l Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Klazy Kmat Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kna Klim Kcov Kph Ktop) (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Ua, Un in D. lia.
        * intros b l k Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Klazy Kmat Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kna Klim Kcov Kph Ktop) (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Ua, Un in D. lia.
    - (* [comment removed for export] *)
      destruct Ha as [_ Evm].
      apply KL_dead with (pbrk := ps_brk s0); [| intros cur' E; rewrite Hph in E; discriminate].
      eapply KL_vm_eq; [exact HK| exact Hl'| exact Hm'| | | | | | |]; rewrite Evm; reflexivity. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & Hvo & [Hne Hpos] & Ecur & [HK HPG]). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
  - apply mspec_ret. intros s mo (-> & Hvo & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ecur.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk_grow2_ok : forall L s0 mo0 b l, ld_brk L = BPLive -> ld_brkreg L = Some (b, l) ->
  let req := b + l + PGSZ in
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) s0 mo0).
Proof.
  intros L s0 mo0 b l Hph Ereg req. pose proof alloc_ceiling_lt as Hcl.
  intros s mo (-> & -> & HK0). revert HK0.
  enough (H : mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (a <- msys (NBrk req) (dec_brk (ps_brk s0) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s0) end)
        (ev_step_post L (EBrk req) s0 mo0)).
  { intros HK0. apply (H s0 mo0). auto. }
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ vm_only mo0 mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
                match a with
                | BrkGrown => KL (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
                | BrkSame => KL (set_brkph BPDead L) (b + l) mo
                end)).
    { reflexivity. }
    intros s mo (-> & -> & HK).
    pose proof (kl_phase _ _ _ HK) as Kph. unfold phase_inv in Kph. rewrite Hph in Kph. destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    pose proof (kl_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & R6 & Rcov).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    split; [cbn; unfold PGSZ in *; lia|].
    intros rsp mo' Hst.
    pose proof (anstep_books _ _ _ _ (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK) Hst) as (Hl' & Hm' & Hvo).
    pose proof (anstep_dec_brk mo0 req rsp mo' ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (a & Hdec & Ha).
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [exact Hvo|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    destruct a.
    - (* [comment removed for export] *)
      destruct Ha as (Hgo & _ & Evm).
      apply brk_grow_ok_facts in Hgo; [| exact (kl_top _ _ _ HK) | lia| unfold PGSZ in *; lia| rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity| subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf]. rewrite Ebrk in Hrf.
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KL_lbrk_pages_ok L (ps_brk s0) mo0 (b + l) PGSZ HK); [lia| unfold PGSZ; lia| subst req; lia| |].
        - replace (req - (b + l)) with PGSZ in Hrf by lia. exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. left; lia. }
      rewrite (bv_sub_went (vm_brk (m_vmmaps mo0)) req) in Evm by (unfold PGSZ in *; lia). rewrite Ebrk in Evm.
      replace (req - (b + l)) with PGSZ in Hrf, Evm by lia.
      assert (Ua : bv_unsigned (Z_to_bv 64 (b + l)) = b + l) by (apply unsigned_lit; unfold PGSZ in *; lia).
      assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      split; [|exact HPG].
      kl_open HK. constructor; try assumption; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; try assumption.
      + apply vmwf_cons; [exact Kwf| rewrite Ua, Un; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; unfold PGSZ in *; lia.
      + intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Ua, Un in D.
        specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
      + intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Ua, Un in D.
        specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
      + intros b1 l1 E. injection E as <- <-. splits; auto.
        * clear -R3. unfold PGSZ in *; lia.
        * unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
        * clear -Hceil. subst req. lia.
        * intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
          -- destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
          -- exists (went (b + l) PGSZ). split; [left; reflexivity|]. unfold elo, ehi, went. cbn [fst snd]. rewrite Ua, Un. lia.
      + intros e He. destruct (Kna e He) as [W [(b0 & l0 & k & Hin & Hlo & Hhi)|(b0 & l0 & E & Hlo & Hhi & Hin)]]; split; try exact W.
        * left. exists b0, l0, k. auto.
        * right. rewrite Ereg in E. injection E as <- <-. exists b, (l + PGSZ). splits; auto. right; exact Hin.
      + intros e [<-|He].
        * right; right. unfold brk_piece. cbn [ld_brkreg set_brkreg]. right. exists (l / PGSZ).
          assert (El : l = l / PGSZ * PGSZ) by (unfold PGSZ in *; lia).
          splits; [unfold PGSZ in *; lia| lia| rewrite <- El; reflexivity].
        * destruct (Kcov e He) as [G|[M|B]]; [left; exact G| right; left; exact M| right; right].
          unfold brk_piece in *. cbn [ld_brkreg set_brkreg]. rewrite Ereg in B. destruct B as [B|(j & J1 & J2 & B)]; [left; exact B| right].
          exists j. splits; auto. clear -J2. unfold PGSZ in *. lia.
      + unfold phase_inv. cbn [ld_brk ld_brkreg set_brkreg]. rewrite Hph. rewrite Evm. cbn [vm_brk].
        exists b, (l + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; lia.
    - (* [comment removed for export] *)
      destruct Ha as [_ Evm].
      apply KL_dead with (pbrk := ps_brk s0); [| intros cur' E; rewrite Hph in E; discriminate].
      eapply KL_vm_eq; [exact HK| exact Hl'| exact Hm'| | | | | | |]; rewrite Evm; reflexivity. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & Hvo & [Hne Hpos] & Ecur & [HK HPG]). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    splits; auto.
    unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
  - apply mspec_ret. intros s mo (-> & Hvo & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Ecur.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma MAPF_eq : MAPF = mm_flags_anon. Proof. reflexivity. Qed.
Lemma MAPFX_eq : MAPFX = mm_flags_fixed. Proof. reflexivity. Qed.
Lemma PROT_NONE_eq : PROT_NONE = mm_prot_none. Proof. reflexivity. Qed.
Lemma PROT_RW_eq : PROT_RW = mm_prot_rw. Proof. reflexivity. Qed.

Lemma KL_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
  KL L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  0 < a -> a + n <= alloc_ceiling -> a mod 4096 = 0 ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  m_vm_lazy mo' = [] -> m_vm_materialized mo' = [] ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
  /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false.
Proof.
  intros L pbrk mo mo' a len isnone HK Hq Hlen h n A2 A3 A1 Hrf Hl' Hm' Evm. pose proof alloc_ceiling_lt as Hcl.
  pose proof (mmap_len_ge' len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm. pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
  (* [comment removed for export] *)
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & R6 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      pose proof (lranges_rf_disj L pbrk mo lo m (Z_to_bv 64 a) (Z_to_bv 64 n) HK Hrf ltac:(rewrite Un; lia)) as D. rewrite Ua, Un in D.
      apply D; [exact Dbrk| exact Hin]. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L -> ld_groups L = ld_groups L' \/ True ->
            phase_inv (ld_brk L') L' pbrk mo' ->  phase_inv (ld_brk L') L' pbrk mo') by auto.
  subst h. kl_open HK.
  assert (PH : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L -> phase_inv (ld_brk L') L' pbrk mo').
  { intros L' E1 E2. unfold phase_inv in *. rewrite E1, E2, Evm. cbn [vm_brk vm_start_brk vm_maps]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  destruct isnone; constructor;
    first [ apply PH; reflexivity
          | rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). unfold brk_disj in *; cbn. splits; auto.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n in Hq2. unfold PGSZ in *. lia.
    + specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & R6 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - intros e [<-|He].
    + rewrite elo_pair, ehi_pair, Ua, Un. split; [lia|]. left. exists a, len, 0. split; [left; reflexivity|]. fold n. lia.
    + destruct (Kna e He) as [W [(b0 & l0 & k & Hin & Hlo & Hhi)|(b0 & l0 & E & Hlo & Hhi & Hin)]]; split; try exact W.
      * left. exists b0, l0, k. split; [right; exact Hin|]. auto.
      * right. exists b0, l0. splits; auto. right; exact Hin.
  - intros e [<-|He]; [right; left; exists a, len, 0; split; [left; reflexivity| reflexivity]|].
    destruct (Kcov e He) as [(b0 & l0 & Hin & ->)|[(b0 & l0 & k & Hin & ->)|B]]; [left; exists b0, l0; auto| right; left; exists b0, l0, k; split; [right; exact Hin| reflexivity]| right; right; exact B].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj, resv_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
      * intros e He. pose proof (region_free_disj _ _ _ _ Hrfr He) as D. rewrite Ua, Un in D. exact D.
    + specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). unfold brk_disj in *; cbn. splits; auto.
  - intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & R6 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - intros e He. destruct (Kna e He) as [W [(b0 & l0 & k & Hin & Hlo & Hhi)|(b0 & l0 & E & Hlo & Hhi & Hin)]]; split; try exact W.
    + left. exists b0, l0, k. auto.
    + right. exists b0, l0. splits; auto. right; exact Hin.
  - intros e [<-|He]; [left; exists a, len; split; [left; reflexivity| reflexivity]|].
    destruct (Kcov e He) as [(b0 & l0 & Hin & ->)|[(b0 & l0 & k & Hin & ->)|B]]; [left; exists b0, l0; split; [right; exact Hin| reflexivity]| right; left; exists b0, l0, k; auto| right; right; exact B].
Qed.

Lemma ev_mmap_core : forall L s0 mo0 len (isnone : bool), brk_quiet L -> 0 < len < LEN_MAX ->
  let prot := if isnone then PROT_NONE else PROT_RW in
  let dec := if isnone then dec_mmap_none len [] else dec_mmap len [] in
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (a <- msys (NMmap 0 len prot MAPF) dec ;; mret match a with MmErr e => neg_errno e | MmOk x => x end)
        (ev_step_post L (EMmap 0 len prot MAPF) s0 mo0).
Proof.
  intros L s0 mo0 len isnone Hq Hlen prot dec.
  pose proof (mmap_len_ge' len ltac:(lia)) as Hn1.
  eapply mspec_bind.
  { apply (mspec_sys (NMmap 0 len prot MAPF) dec _
             (fun x s mo => s = s0 /\ vm_only mo0 mo /\
                match x with
                | MmErr e => e = ENOMEM /\ KL L (ps_brk s0) mo
                | MmOk a => KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) (ps_brk s0) mo
                            /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false
                end)).
    { reflexivity. }
    intros s mo (-> & -> & HK). split.
    { cbn [nsafe]. split; [lia|]. split; [unfold LEN_MAX in Hlen; lia|].
      subst prot. destruct isnone; [right; left| left]; split; reflexivity. }
    intros rsp mo' Hst.
    pose proof (anstep_books _ _ _ _ (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK) Hst) as (Hl' & Hm' & Hvo).
    assert (Hcase : exists x, dec rsp = Some x /\
              match x with
              | MmErr e => e = ENOMEM /\ mo' = mo0
              | MmOk a => 0 < a /\ a + mmap_len len <= alloc_ceiling /\ a mod 4096 = 0
                  /\ region_free (vm_reserved (m_vmmaps mo0) ++ vm_maps (m_vmmaps mo0)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
                  /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo0)) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo0))
                       (if isnone then (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo0) else vm_noaccess (m_vmmaps mo0))
                       (vm_start_brk (m_vmmaps mo0)) (vm_brk (m_vmmaps mo0)) (vm_limit (m_vmmaps mo0)) (vm_mmap_base (m_vmmaps mo0)) (vm_init_sp (m_vmmaps mo0))
              end).
    { subst prot dec. destruct isnone.
      - rewrite PROT_NONE_eq, MAPF_eq in Hst.
        pose proof (anstep_dec_mmap_none mo0 len [] rsp mo' ltac:(lia) (Forall_nil _) ltac:(rewrite (kl_top _ _ _ HK); lia) Hst) as (x & Hd & Hx).
        exists x. split; [exact Hd|]. destruct x as [e|a]; [exact Hx|]. cbv zeta in Hx. destruct Hx as (Hok & A2 & A3 & Hrf & Evm).
        unfold mmap_addr_ok in Hok. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _]. apply Z.eqb_eq in Hok.
        rewrite page_size_eq in Hok. splits; auto.
      - rewrite PROT_RW_eq, MAPF_eq in Hst.
        pose proof (anstep_dec_mmap mo0 len [] rsp mo' ltac:(lia) (Forall_nil _) ltac:(rewrite (kl_top _ _ _ HK); lia) Hst) as (x & Hd & Hx).
        exists x. split; [exact Hd|]. destruct x as [e|a]; [exact Hx|]. cbv zeta in Hx. destruct Hx as (Hok & A2 & A3 & Hrf & _ & Evm).
        unfold mmap_addr_ok in Hok. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _]. apply Z.eqb_eq in Hok.
        rewrite page_size_eq in Hok. splits; auto. }
    destruct Hcase as (x & Hd & Hx). exists x. split; [exact Hd|].
    split; [reflexivity|]. split; [exact Hvo|].
    destruct x as [e|a].
    - destruct Hx as [-> ->]. split; [reflexivity| exact HK].
    - destruct Hx as (A2 & A3 & A1 & Hrf & Evm). apply (KL_mmap_new L (ps_brk s0) mo0 mo' a len isnone HK Hq Hlen A2 A3 A1 Hrf Hl' Hm' Evm). }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & Hvo & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPF MAP_FIXED =? 0) with true. cbv iota.
  destruct x as [e|a].
  - destruct Hx as [-> HK]. rewrite is_err_neg by (unfold ENOMEM; lia).
    unfold mmap_answer_ok. rewrite is_errno_form_neg by (unfold ENOMEM; lia). splits; auto.
  - destruct Hx as (HK & Hans & Herr). rewrite Herr. subst prot. destruct isnone.
    + change (PROT_NONE =? PROT_NONE) with true. cbv iota. splits; auto.
    + change (PROT_RW =? PROT_NONE) with false. cbv iota. splits; auto.
Qed.

Lemma ev_mmap_ok : forall L s0 mo0 len prot, brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX ->
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (ev_step (EMmap 0 len prot MAPF))
        (ev_step_post L (EMmap 0 len prot MAPF) s0 mo0).
Proof.
  intros L s0 mo0 len prot Hq Hprot Hlen. unfold ev_step.
  change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
  destruct Hprot as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota. apply (ev_mmap_core L s0 mo0 len true Hq Hlen).
  - change (PROT_RW =? 0) with false. cbv iota. apply (ev_mmap_core L s0 mo0 len false Hq Hlen).
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac kl_open HK := destruct HK as [Klazy Kmat Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kna Klim Kcov Kph Ktop].
End KStep2.

(* [comment removed for export] *)
Module KStep3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound NodesSoundDec ImplSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 KStep2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma iv_subtract_guard : forall a, 0 < a -> a + 2 * PGSZ < 2^64 ->
  iv_subtract (fst (went a (2 * PGSZ))) (snd (went a (2 * PGSZ))) a (a + PGSZ) = [went (a + PGSZ) PGSZ].
Proof.
  intros a Ha Hb. unfold iv_subtract, went. cbn [fst snd]. rewrite !unsigned_lit by (unfold PGSZ in *; lia).
  rewrite Z.ltb_irrefl. rewrite (proj2 (Z.ltb_lt _ _)) by (unfold PGSZ; lia). cbn [app].
  rewrite Z.max_r by (unfold PGSZ; lia). f_equal. f_equal. f_equal. unfold PGSZ. lia.
Qed.

Lemma ev_mmap_fixed_ok : forall L s0 mo0 cur, ld_brk L = BPGuard cur ->
  let a := round_up_pg cur in
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (ev_step (EMmap a PGSZ PROT_NONE MAPFX))
        (ev_step_post L (EMmap a PGSZ PROT_NONE MAPFX) s0 mo0).
Proof.
  intros L s0 mo0 cur Hph a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
  set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
  eapply mspec_bind.
  { apply (mspec_sys (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
             (fun x s mo => s = s0 /\ vm_only mo0 mo /\ KL L' (ps_brk s0) mo /\ match x with FxKept e => e = ENOMEM | FxDone => True | FxLost e => e = ENOMEM end)).
    { reflexivity. }
    intros s mo (-> & -> & HK).
    pose proof (kl_phase _ _ _ HK) as Kph. unfold phase_inv in Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & He0 & Dg & Dm).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
    set (h := m_vmmaps mo0) in *. set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 PGSZ).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    destruct (u64_went cur (2 * PGSZ) ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia)) as [U1 U2].
    assert (Hrf : region_free (vm_reserved h) aw nw = true).
    { apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kl_resv_top _ _ _ HK). exact He. }
    assert (Uc : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; unfold PGSZ in *; lia).
    assert (U2p : bv_unsigned (Z_to_bv 64 (2 * PGSZ)) = 2 * PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
    assert (Hmc : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went cur (2 * PGSZ)). split; [exact He0|]. rewrite Ua, Un. unfold went. cbn [fst snd].
      rewrite Uc, U2p. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    assert (Hml : mmap_len PGSZ = PGSZ) by reflexivity.
    split.
    { cbn [nsafe]. split; [unfold PGSZ in *; lia|]. split; [unfold PGSZ; lia|]. right; right.
      split; [reflexivity|]. split; [reflexivity|]. rewrite page_size_eq, (kl_top _ _ _ HK). change (page_round_up_Z PGSZ) with PGSZ. fold aw nw.
      splits; [rewrite Ha, Ecur; exact S2| lia| lia| exact Hrf| exact Hmc]. }
    intros rsp mo' Hst.
    pose proof (anstep_books _ _ _ _ (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK) Hst) as (Hl' & Hm' & Hvo).
    rewrite PROT_NONE_eq, MAPFX_eq in Hst.
    pose proof (anstep_mmap_fixed_cases mo0 a PGSZ rsp mo' Hst) as Hx. cbv zeta in Hx. rewrite Hml in Hx. fold h aw nw in Hx. rewrite Ua, Un in Hx.
    (* [comment removed for export] *)
    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (Hlohi : a < a + PGSZ < 2^64) by (unfold PGSZ in *; lia).
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> (ehi e <= a \/ a + PGSZ <= elo e) -> In e maps') ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (forall e, In e noacc' -> (e = (aw, nw) /\ In (went a (2 * PGSZ)) maps') \/ In e (vm_noaccess h) \/ In e (maps_subtract (vm_noaccess h) a (a + PGSZ))) ->
              (exists e', In e' maps' /\ elo e' <= a + PGSZ /\ a + 2 * PGSZ <= ehi e') ->
              (forall e, In e maps' -> In e (vm_maps h) \/ In e (maps_subtract (vm_maps h) a (a + PGSZ))) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hna Hna' Hcov' Hmaps' Evm. subst L' h.
      kl_open HK. constructor; try assumption; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; try assumption.
      - intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + rewrite Ha, Ecur. reflexivity.
        + intros z Hz. destruct Hcov' as (e' & He' & H1 & H2). exists e'. split; [exact He'|]. lia.
      - intros e He. destruct (Hna' e He) as [[-> Hin]|[He1|He1]].
        + rewrite elo_pair, ehi_pair, Ua, Un. split; [lia|]. right. exists a, (2 * PGSZ). splits; [reflexivity| lia| lia| exact Hin].
        + destruct (Kna e He1) as [W [(b0 & l0 & k & Hin & Hlo & Hhi)|(b0 & l0 & E & _)]]; [| rewrite Ereg in E; discriminate].
          split; [exact W|]. left. exists b0, l0, k. auto.
        + destruct (maps_subtract_In _ _ _ _ He1) as (e0 & He0' & Hp).
          destruct (Kna e0 He0') as [W [(b0 & l0 & k & Hin & Hlo & Hhi)|(b0 & l0 & E & _)]]; [| rewrite Ereg in E; discriminate].
          pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (iv_subtract_sub (fst e0) (snd e0) a (a + PGSZ) e ltac:(unfold elo, ehi in W; lia) ltac:(unfold ehi in Hhi; lia) Hp) as (P1 & P2 & P3).
          split; [exact P3|]. left. exists b0, l0, k. unfold elo, ehi in *. splits; [exact Hin| lia| lia].
      - intros e He. unfold brk_piece. cbn [ld_brkreg ld_groups ld_metas set_brkph set_brkreg].
        assert (Hold : forall e0, In e0 (vm_maps (m_vmmaps mo0)) ->
                  (exists b0 l0, In (b0, l0) (ld_groups L) /\ e0 = went b0 (mmap_len l0) /\ (b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0))
                  \/ (exists b0 l0 k, In (b0, l0, k) (ld_metas L) /\ e0 = went b0 (mmap_len l0) /\ (b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0))
                  \/ e0 = went a (2 * PGSZ)).
        { intros e0 He0'. destruct (Kcov e0 He0') as [(b0 & l0 & Hin & ->)|[(b0 & l0 & k & Hin & ->)|B]].
          - left. exists b0, l0. splits; auto; (apply (Dgm b0 l0); left; exact Hin).
          - right; left. exists b0, l0, k. splits; auto; (apply (Dgm b0 l0); right; exists k; exact Hin).
          - right; right. unfold brk_piece in B. rewrite Ereg, Hph in B. rewrite Ha. exact B. }
        destruct (Hmaps' e He) as [He1|He1].
        + destruct (Hold e He1) as [(b0 & l0 & Hin & -> & _)|[(b0 & l0 & k & Hin & -> & _)| ->]]; [left; exists b0, l0; auto| right; left; exists b0, l0, k; auto| right; right; left; reflexivity].
        + destruct (maps_subtract_In _ _ _ _ He1) as (e0 & He0' & Hp).
          destruct (Hold e0 He0') as [(b0 & l0 & Hin & -> & D)|[(b0 & l0 & k & Hin & -> & D)| ->]].
          * pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
            assert (G1 : elo (went b0 (mmap_len l0)) < ehi (went b0 (mmap_len l0)) <= 2^64) by (rewrite B5, B6; lia).
            assert (G3 : ehi (went b0 (mmap_len l0)) <= a \/ a + PGSZ <= elo (went b0 (mmap_len l0))) by (rewrite B5, B6; clear -D; unfold PGSZ in *; lia).
            rewrite (iv_subtract_disjoint _ _ a (a + PGSZ) G1 ltac:(unfold PGSZ; lia) G3) in Hp.
            destruct Hp as [Hp|[]]. rewrite <- surjective_pairing in Hp. subst e. left. exists b0, l0. auto.
          * pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
            assert (G1 : elo (went b0 (mmap_len l0)) < ehi (went b0 (mmap_len l0)) <= 2^64) by (rewrite B5, B6; lia).
            assert (G3 : ehi (went b0 (mmap_len l0)) <= a \/ a + PGSZ <= elo (went b0 (mmap_len l0))) by (rewrite B5, B6; clear -D; unfold PGSZ in *; lia).
            rewrite (iv_subtract_disjoint _ _ a (a + PGSZ) G1 ltac:(unfold PGSZ; lia) G3) in Hp.
            destruct Hp as [Hp|[]]. rewrite <- surjective_pairing in Hp. subst e. right; left. exists b0, l0, k. auto.
          * rewrite iv_subtract_guard in Hp by (unfold PGSZ in *; lia). destruct Hp as [<-|[]].
            right; right; right. exists 1. splits; [lia| lia| f_equal; lia].
      - unfold phase_inv. cbn [ld_brk ld_brkreg set_brkph set_brkreg]. rewrite Evm. cbn [vm_brk]. exists a, (2 * PGSZ). splits; [reflexivity| lia| lia]. }
    assert (Hback : forall x, dec_mmap_fixed a PGSZ rsp = Some x ->
              (match x with FxKept e => e = ENOMEM | FxDone => True | FxLost e => e = ENOMEM end) -> KL L' (ps_brk s0) mo' ->
              exists x', dec_mmap_fixed a PGSZ rsp = Some x' /\ s0 = s0 /\ vm_only mo0 mo' /\ KL L' (ps_brk s0) mo' /\
                match x' with FxKept e => e = ENOMEM | FxDone => True | FxLost e => e = ENOMEM end).
    { intros x Hd Hm HK'. exists x. auto. }
    destruct Hx as [(e & -> & -> & ->)|[(-> & Evm)|(e & -> & -> & Evm)]].
    - apply (Hback (FxKept ENOMEM)); [| reflexivity|].
      + unfold dec_mmap_fixed, efferr, eff0. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
      + apply (KLnew (vm_maps h) (vm_noaccess h)); auto.
        * exact (kl_wf _ _ _ HK).
        * intros e x y He H1 H2 H3 H4. exists e. auto.
        * exists (went cur (2 * PGSZ)). split; [exact He0|]. rewrite U1, U2. unfold PGSZ in *; lia.
        * subst h. destruct mo0 as [? ? ? ? ? ? ? ?]; cbn. destruct m_vm; cbn. destruct vmst_maps; reflexivity.
    - apply (Hback FxDone); [| exact I|].
      + unfold dec_mmap_fixed. subst aw nw. rewrite Hml, !bv_eqb_refl. cbn [andb].
        rewrite errno_of_small by (rewrite Ua; lia). reflexivity.
      + apply (KLnew (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
        * exact (kl_wf _ _ _ HK).
        * intros e x y He H1 H2 H3 H4. destruct (maps_subtract_contains (vm_noaccess h) a (a + PGSZ) e x y Hlohi He H1 H2 H3 H4) as (e' & He' & Hr).
          exists e'. split; [right; exact He'| exact Hr].
        * intros e [<-|He]; [left| right; right; exact He]. split; [reflexivity|]. rewrite Ha. exact He0.
        * exists (went cur (2 * PGSZ)). split; [exact He0|]. rewrite U1, U2. unfold PGSZ in *; lia.
    - (* [comment removed for export] *)
      apply (Hback (FxLost ENOMEM)); [| reflexivity|].
      + unfold dec_mmap_fixed. subst aw nw. rewrite Hml, !bv_eqb_refl. cbn [andb].
        rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
      + pose proof (kl_wf _ _ _ HK) as Hwf0.
        apply (KLnew (maps_subtract (vm_maps h) a (a + PGSZ)) (maps_subtract (vm_noaccess h) a (a + PGSZ))).
        * apply vmwf_subtract; [exact Hlohi| exact Hwf0].
        * intros e He D. apply maps_subtract_keep; [exact (proj1 Hwf0)| lia| exact He| exact D].
        * intros e x y He H1 H2 H3 H4. exact (maps_subtract_contains (vm_noaccess h) a (a + PGSZ) e x y Hlohi He H1 H2 H3 H4).
        * intros e He. right; right; exact He.
        * exists (went (a + PGSZ) PGSZ). split.
          -- apply (maps_subtract_In_intro (vm_maps h) a (a + PGSZ) (went a (2 * PGSZ)) (went (a + PGSZ) PGSZ)).
             ++ rewrite Ha. exact He0.
             ++ rewrite (iv_subtract_guard a) by (rewrite Ha; unfold PGSZ in *; lia). left; reflexivity.
          -- destruct (u64_went (a + PGSZ) PGSZ ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia)) as [V1 V2].
             rewrite V1, V2. unfold PGSZ in *; lia.
        * intros e He. right. exact He.
        * rewrite Evm. reflexivity. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & Hvo & HK & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota. fold L'.
  splits; auto. unfold mmap_fixed_answer_ok. destruct x as [e| |e]; try subst e.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
  - rewrite Z.eqb_refl. apply orb_true_r.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma g_remove_split : forall a l0 (l : list (Z * Z)) (M : list Z), In (a, l0) l -> List.NoDup (map fst l ++ M) ->
  exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
  intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
    exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
    exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

Lemma ev_munmap_ok : forall L s0 mo0 a l0 len, brk_quiet L -> In (a, l0) (ld_groups L) ->
  (len = l0 \/ len = round_up_pg l0) ->
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (ev_step (EMunmap a len))
        (ev_step_post L (EMunmap a len) s0 mo0).
Proof.
  intros L s0 mo0 a l0 len Hq Hin Hlen. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  set (L' := set_groups (g_remove a (ld_groups L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMunmap a len) (dec_munmap a len) _
             (fun x s mo => s = s0 /\ vm_only mo0 mo /\ KL L' (ps_brk s0) mo /\ x = RgDone true)).
    { reflexivity. }
    intros s mo (-> & -> & HK).
    pose proof (kl_groups _ _ _ HK a l0 Hin) as ([A0 A1] & A2 & A3 & A4 & A5 & A6 & A7).
    pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
    set (n := mmap_len l0) in *. set (h := m_vmmaps mo0) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
    assert (Hnn : mmap_len n = n) by (subst n; apply NodesSound.mmap_len_of_aligned; apply NodesSound.mmap_len_aligned).
    assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
    { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
    destruct Hlen3 as [Hlen1 Hlen2].
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
    assert (Hhas : map_has (vm_maps h) aw nw = true).
    { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    split.
    { cbn [nsafe]. rewrite page_size_eq. unfold PGSZ in A3. fold (mmap_len len). rewrite Hlen2. fold h nw aw. splits; [lia| exact A3| lia| unfold TASK_SIZE; lia| exact Hhas]. }
    intros rsp mo' Hst.
    pose proof (anstep_books _ _ _ _ (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK) Hst) as (Hl' & Hmat' & Hvo).
    pose proof (anstep_dec_munmap mo0 a len rsp mo' Hst) as [Hd Evm]. cbv zeta in Evm. rewrite Hlen2 in Evm. fold h aw nw in Evm. rewrite Ua, Un in Evm.
    exists (RgDone true). split; [exact Hd|]. split; [reflexivity|]. split; [exact Hvo|]. split; [|reflexivity].
    (* [comment removed for export] *)
    pose proof (kl_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    (* [comment removed for export] *)
    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + n < 2^64) by lia.
    assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
    assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
    { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_lit, Ua in E by lia. exact E. }
    assert (Hkeep : forall e, In e (vm_maps h) -> fst e <> aw -> In e (map_remove (vm_maps h) aw)).
    { intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction. }
    subst L' h. kl_open HK. constructor; try exact Hph'; try assumption; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; try assumption.
    - apply vmwf_remove. exact Kwf.
    - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). splits; try assumption.
      apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge' l1 G0). lia.
    - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
      + apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge' l1 G0). lia.
      + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
        pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
        apply (maps_subtract_contains _ a (a + n) e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi He Hel ltac:(unfold PGSZ; lia) Heh). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
    - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
    - intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & R6 & Rcov). splits; auto.
      intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
      intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
      destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
      + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
      + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. fold aw nw in D. rewrite Un in D. clear -D W Hlohi. lia.  (* [comment removed for export] *)
    - intros e He. destruct (maps_subtract_In _ _ _ _ He) as (e0 & He0 & Hp).
      destruct (Kna e0 He0) as [W Hc].
      assert (W2 : ehi e0 <= 2^64).
      { destruct Hc as [(b0 & l9 & k & Hin0 & Hlo & Hhi)|(b0 & l9 & E & Hlo & Hhi & Hin0)].
        - pose proof (went_In_bounds _ _ _ b0 l9 (mkKL _ _ _ Klazy Kmat Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kna Klim Kcov Kph Ktop) (or_intror (ex_intro _ k Hin0))) as (C1 & C2 & C3 & _). clear -C1 C2 C3 Hhi Hcl. lia.
        - pose proof (Kreg b0 l9 E) as (R1 & R2 & R3 & R4 & R5 & _). clear -R3 R5 Hhi Hcl. unfold PGSZ in *. lia. }
      pose proof (iv_subtract_sub (fst e0) (snd e0) a (a + n) e ltac:(unfold elo, ehi in W; lia) ltac:(unfold ehi in W2; exact W2) Hp) as (P1 & P2 & P3).
      change (bv_unsigned (fst e0)) with (elo e0) in P1.
      change (bv_unsigned (fst e0) + bv_unsigned (snd e0)) with (ehi e0) in P2.
      split; [exact P3|]. destruct Hc as [(b0 & l9 & k & Hin0 & Hlo & Hhi)|(b0 & l9 & E & Hlo & Hhi & Hin0)].
      + left. exists b0, l9, k. splits; [exact Hin0| lia| lia].
      + right. exists b0, l9. splits; [exact E| lia| lia|].
        apply Hkeep; [exact Hin0|]. intros Efst. unfold brk_disj in A6. specialize (A6 b0 l9 E).
        pose proof (Kreg b0 l9 E) as (R1 & R2 & R3 & R4 & R5 & _).
        destruct (u64_went b0 (2 * PGSZ) ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia)) as [U1 U2].
        assert (Eb : b0 = a).
        { apply (f_equal bv_unsigned) in Efst. change (elo (went b0 (2 * PGSZ)) = bv_unsigned aw) in Efst. rewrite U1, Ua in Efst. exact Efst. }
        destruct (pwdisj_In _ _ _ (proj2 Kwf) Hin0 A5) as [Ee|D].
        * apply (f_equal ehi) in Ee. rewrite B6, U2 in Ee. clear -Ee Eb A6 R3 B2. unfold PGSZ in *. lia.
        * unfold edisj in D. rewrite U1, U2, B5, B6 in D. clear -D Eb R3 B2. unfold PGSZ in *. lia.
    - intros e He. unfold map_remove in He. apply filter_In in He as [He Hne].
      destruct (Kcov e He) as [(b0 & l1 & Hin0 & ->)|[(b0 & l1 & k & Hin0 & ->)|B]]; [| right; left; exists b0, l1, k; auto| right; right; exact B].
      left. exists b0, l1. split; [|reflexivity]. rewrite Ezz. rewrite Eg in Hin0. apply in_app_or in Hin0 as [H0|[H0|H0]]; [apply in_or_app; left; exact H0| | apply in_or_app; right; exact H0].
      exfalso. injection H0 as -> ->. cbn [fst went] in Hne. fold aw in Hne. rewrite bv_eqb_refl in Hne. discriminate. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & Hvo & HK & ->). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'.
  splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma map_base_bump : forall a ms, map (fun m : Z * Z * Z => fst (fst m)) (map (bump_meta a) ms) = map (fun m => fst (fst m)) ms.
Proof.
  intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

Lemma ev_mprotect_ok : forall L s0 mo0 b l k, brk_quiet L -> In (b, l, k) (ld_metas L) ->
  (2 + k) * PGSZ <= round_up_pg l ->
  let a := b + (1 + k) * PGSZ in
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (ev_step (EMprotect a PGSZ PROT_RW))
        (ev_step_post L (EMprotect a PGSZ PROT_RW) s0 mo0).
Proof.
  intros L s0 mo0 b l k Hq Hin Hk2 a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
             (fun x s mo => s = s0 /\ vm_only mo0 mo /\ match x with RgErr e => e = ENOMEM /\ KL L (ps_brk s0) mo | RgDone _ => KL L' (ps_brk s0) mo end)).
    { reflexivity. }
    intros s mo (-> & -> & HK).
    pose proof (kl_metas _ _ _ HK b l k Hin) as ([A0 A1] & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (nb := mmap_len l) in *. set (h := m_vmmaps mo0) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hml : mmap_len PGSZ = PGSZ) by reflexivity.
    assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
    { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un.
      change ((elo (went b nb) <=? a) && (a + PGSZ <=? ehi (went b nb)) = true). rewrite B5, B6.
      rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    split.
    { cbn [nsafe]. rewrite page_size_eq. change (page_round_up_Z PGSZ) with PGSZ. fold h aw nw.
      splits; [reflexivity| unfold PGSZ in *; lia| exact Hamod| unfold PGSZ; lia| unfold PGSZ in *; lia| exact Hcn| exact Hcm]. }
    intros rsp mo' Hst.
    pose proof (anstep_books _ _ _ _ (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK) Hst) as (Hl' & Hm' & Hvo).
    rewrite PROT_RW_eq in Hst.
    pose proof (anstep_dec_mprotect mo0 a PGSZ rsp mo' Hst) as (x & Hd & Hx). cbv zeta in Hx. rewrite Hml in Hx. fold h aw nw in Hx. rewrite Ua, Un in Hx.
    assert (HdRW : dec_mprotect_rw a PGSZ rsp = Some x).
    { destruct x as [e|[|]].
      - destruct Hx as [-> _]. unfold dec_mprotect_rw. rewrite Hd. reflexivity.
      - unfold dec_mprotect_rw. rewrite Hd. reflexivity.
      - destruct Hx. }
    exists x. split; [exact HdRW|]. split; [reflexivity|]. split; [exact Hvo|].
    pose proof (kl_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    (* [comment removed for export] *)
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + PGSZ < 2^64) by (unfold PGSZ in *; lia).
    assert (KLnew : forall noacc',
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (forall e, In e noacc' -> In e (vm_noaccess h) \/ In e (maps_subtract (vm_noaccess h) a (a + PGSZ))) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros noacc' Hna Hna' Evm.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      subst L' h. kl_open HK. constructor; try exact Hph'; try assumption; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; try assumption.
      - intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
        specialize (Kme b1 l1 k0 Hin1). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
        unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
        + (* [comment removed for export] *)
          assert (Eb0 : b0 = b).
          { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
            pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge' l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
          subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
          splits; try assumption; try lia.
          intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b + q * PGSZ) (b + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). right. subst a. clear -Hq1. unfold PGSZ in *. nia.
        + splits; try assumption.
          intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh).
          destruct (Z.eq_dec b0 b) as [->|Hne].
          { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite map_base_bump. exact Kdis.
      - intros e He.
        assert (Hmeta : forall e0, In e0 (vm_noaccess (m_vmmaps mo0)) -> elo e0 <= elo e -> ehi e <= ehi e0 -> elo e < ehi e ->
                  elo e < ehi e /\
                  ((exists b2 l2 k2, In (b2, l2, k2) (map (bump_meta a) (ld_metas L)) /\ b2 <= elo e /\ ehi e <= b2 + mmap_len l2)
                   \/ (exists b2 l2, ld_brkreg L = Some (b2, l2) /\ b2 <= elo e /\ ehi e <= b2 + PGSZ /\ In (went b2 (2 * PGSZ)) (vm_maps (m_vmmaps mo0))))).
        { intros e0 He0 H1 H2 H3. split; [exact H3|]. destruct (Kna e0 He0) as [W [(b2 & l2 & k2 & Hin2 & Hlo & Hhi)|(b2 & l2 & E & Hlo & Hhi & Hin2)]].
          - left. exists b2, l2, (if b2 + (1 + k2) * PGSZ =? a then k2 + 1 else k2). split; [| split; lia].
            apply in_map_iff. exists (b2, l2, k2). split; [| exact Hin2]. unfold bump_meta. destruct (_ =? _); reflexivity.
          - right. exists b2, l2. splits; auto; lia. }
        destruct (Hna' e He) as [He1|He1].
        + destruct (Kna e He1) as [W _]. apply (Hmeta e He1); lia.
        + destruct (maps_subtract_In _ _ _ _ He1) as (e0 & He0 & Hp). destruct (Kna e0 He0) as [W Hc].
          assert (W2 : ehi e0 <= 2^64).
          { destruct Hc as [(b2 & l2 & k2 & Hin2 & Hlo & Hhi)|(b2 & l2 & E & Hlo & Hhi & Hin2)].
            - pose proof (went_In_bounds _ _ _ b2 l2 (mkKL _ _ _ Klazy Kmat Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kna Klim Kcov Kph Ktop) (or_intror (ex_intro _ k2 Hin2))) as (C1 & C2 & C3 & _). clear -C1 C2 C3 Hhi Hcl. lia.
            - pose proof (Kreg b2 l2 E) as (R1 & R2 & R3 & R4 & R5 & _). clear -R3 R5 Hhi Hcl. unfold PGSZ in *. lia. }
          pose proof (iv_subtract_sub (fst e0) (snd e0) a (a + PGSZ) e ltac:(unfold elo, ehi in W; lia) ltac:(unfold ehi in W2; exact W2) Hp) as (P1 & P2 & P3).
          change (bv_unsigned (fst e0)) with (elo e0) in P1.
          change (bv_unsigned (fst e0) + bv_unsigned (snd e0)) with (ehi e0) in P2.
          apply (Hmeta e0 He0); lia.
      - intros e He. destruct (Kcov e He) as [G|[(b0 & l0 & k0 & Hin0 & ->)|B]]; [left; exact G| right; left| right; right; exact B].
        exists b0, l0, (if b0 + (1 + k0) * PGSZ =? a then k0 + 1 else k0). split; [|reflexivity].
        apply in_map_iff. exists (b0, l0, k0). split; [| exact Hin0]. unfold bump_meta. destruct (_ =? _); reflexivity. }
    destruct x as [e|[|]].
    - destruct Hx as [He ->]. split; [exact He| exact HK].
    - destruct Hx as (_ & Evm). apply (KLnew (maps_subtract (vm_noaccess h) a (a + PGSZ))); [| | exact Evm].
      + intros e x y He H1 H2 H3 H4. apply (maps_subtract_contains (vm_noaccess h) a (a + PGSZ) e x y Hlohi He H1 H2 H3 H4).
      + intros e He. right. exact He.
    - destruct Hx. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & Hvo & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'. unfold mprotect_answer_ok.
  destruct x as [e|bb].
  - destruct Hx as [-> HK]. rewrite is_errno_form_neg by (unfold ENOMEM; lia).
    replace (neg_errno ENOMEM =? 0) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno, ENOMEM; lia).
    replace (neg_errno ENOMEM =? TWO64 - ENOSYS) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno, TWO64, ENOSYS, ENOMEM; lia).
    cbn [orb]. splits; auto.
  - cbn [Z.eqb orb]. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros x. unfold round_up_pg. pose proof (Z.land_nonneg (-x) (PGSZ - 1)). unfold PGSZ in *. lia. Qed.

Theorem ev_step_spec : forall L e s0 mo0,
  event_pre L e ->
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo) (ev_step e) (ev_step_post L e s0 mo0).
Proof.
  intros L e s0 mo0 Hpre. destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
    + unfold ev_step. cbn [Z.eqb]. apply ev_brk0_ok; assumption.
    + destruct (Z.eqb_spec (round_up_pg cur + 2 * PGSZ) 0) as [E|NE].
      * intros s mo (-> & -> & HK). exfalso. pose proof (kl_phase _ _ _ HK) as Kph. unfold phase_inv in Kph. rewrite Hph in Kph. destruct Kph as (Ecur & _).
        pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow1_ok; assumption.
    + destruct (Z.eqb_spec (b + l + PGSZ) 0) as [E|NE].
      * intros s mo (-> & -> & HK). exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow2_ok; assumption.
  - destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + apply ev_mmap_ok; assumption.
    + apply ev_mmap_fixed_ok; assumption.
  - destruct Hpre as (Hq & l0 & Hin & Hlen). apply (ev_munmap_ok L s0 mo0 addr l0 len); assumption.
  - destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). apply (ev_mprotect_ok L s0 mo0 b l k); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem membed_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) L s0 mo0,
  ctree_ok L t Post ->
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0 /\ vm_only mo0 mo).
Proof.
  intros t. induction t as [r|e k IH]; intros Post L s0 mo0 Hok.
  - cbn [membed]. apply mspec_ret. intros s mo (-> & -> & HK). exists L.
    split; [constructor|]. cbn in Hok. splits; auto. apply vm_only_refl.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk].
    eapply mspec_bind; [apply (ev_step_spec L e s0 mo0 Hpre)|].
    intros z. unfold ev_step_post. apply mspec_pointwise. intros s1 mo1 (Hans & HK1 & Hm & Hfa & Hso & Hvo).
    eapply mspec_conseq; [apply (IH z Post (event_post L e z) s1 mo1 (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & Hm' & Hfa' & Hso' & Hvo'). exists L'. split; [econstructor; eauto|].
      splits; auto; try congruence. eapply vm_only_trans; eauto.
Qed.


End CeilWrap.
End KStep3.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes Decode SCPS NodesSound.
Import ImplSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad STree Malloc MallocCtrl Prog KInv KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KInv2.
Import KStep2.
Import KStep3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KB_Simrel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raw_malloc_postc (L : mled) (s0 : PState) (mo0 : Model) (n : Z) (Post : mled -> mstate * option cptr -> Prop)
  : option bptr -> PState -> Model -> Prop :=
  fun r s' mo' =>
    exists L' rc, cpath L (cmalloc (ps_m s0) n) L' (ps_m s', rc) /\ Post L' (ps_m s', rc) /\ KL L' (ps_brk s') mo'
      /\ r = match rc with Some c => Some (c, fresh_off (ps_m s') c n) | None => None end
      /\ ps_fa s' = ps_fa s0 /\ ps_so s' = ps_so s0 /\ vm_only mo0 mo'.

Theorem raw_malloc_spec : forall L s0 mo0 n Post,
  ctree_ok L (cmalloc (ps_m s0) n) Post ->
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo) (raw_malloc n) (raw_malloc_postc L s0 mo0 n Post).
Proof.
  intros L s0 mo0 n Post Hok. unfold raw_malloc.
  apply mspec_get_bind_eq.
  eapply mspec_bind; [apply (membed_spec _ Post L s0 mo0 Hok)|].
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & Hm & Hfa & Hso & Hvo).
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros []. apply mspec_ret. intros s mo [-> ->].
  exists L', p. cbn [ps_m ps_brk ps_fa ps_so set_m]. splits; auto.
Qed.

Definition raw_free_postc (L : mled) (s0 : PState) (mo0 : Model) (c : cptr)
  : unit -> PState -> Model -> Prop :=
  fun _ s' mo' =>
    exists L', cpath L (cfree (ps_m s0) (Some c)) L' (ps_m s') /\ KL L' (ps_brk s') mo'
      /\ ps_fa s' = ps_fa s0 /\ ps_so s' = ps_so s0 /\ vm_only mo0 mo'.

Theorem raw_free_spec : forall L s0 mo0 (p : bptr) Post,
  ctree_ok L (cfree (ps_m s0) (Some (fst p))) Post ->
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo) (raw_free p) (raw_free_postc L s0 mo0 (fst p)).
Proof.
  intros L s0 mo0 p Post Hok. unfold raw_free.
  apply mspec_get_bind_eq.
  eapply mspec_bind; [apply (membed_spec _ Post L s0 mo0 Hok)|].
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & Hm & Hfa & Hso & Hvo).
  apply mspec_upd'. intros s mo [-> ->].
  exists L'. cbn [ps_m ps_brk ps_fa ps_so set_m]. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AOWN (X : list cptr) (s : PState) (mo : Model) : Prop :=
  (exists L, MI_Contracts.SIMREL (ps_m s) L /\ KL L (ps_brk s) mo /\ incl X (ld_live L)) /\ List.NoDup X.

Lemma KL_set_live : forall L v pbrk mo, KL L pbrk mo -> KL (set_live v L) pbrk mo.
Proof. intros L v pbrk mo K. destruct K; constructor; cbn; auto. Qed.

Lemma event_post_live : forall L e z, ld_live (event_post L e z) = ld_live L.
Proof.
  intros L e z. destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

Lemma cpath_live {R} : forall L (t : stree ev Z R) L' r, cpath L t L' r -> ld_live L' = ld_live L.
Proof. intros L t L' r H. induction H; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

Lemma in_ap_remove : forall x c l, In x l -> x <> c -> In x (ap_remove c l).
Proof.
  intros x c l. induction l as [|y l IH]; intros Hin Hne; [destruct Hin|].
  cbn. destruct (aptr_eqb y c) eqn:E.
  - apply MI_Kit.aptr_eqb_eq in E. subst y. destruct Hin as [->|Hin]; [congruence| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.

Lemma ap_remove_In : forall x c l, In x (ap_remove c l) -> In x l.
Proof.
  intros x c l. induction l as [|y l IH]; intros Hin; [destruct Hin|].
  cbn in Hin. destruct (aptr_eqb y c); [right; exact Hin|]. destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; exact Hin].
Qed.

Lemma NoDup_ap_remove : forall c l, List.NoDup l -> List.NoDup (ap_remove c l).
Proof.
  intros c l. induction l as [|y l IH]; intros ND; [constructor|]. inversion ND; subst. cbn. destruct (aptr_eqb y c); [assumption|].
  constructor; [| apply IH; assumption]. intros Hin. apply H1. eapply ap_remove_In. exact Hin.
Qed.

Lemma ap_remove_notin_self : forall c l, List.NoDup l -> ~ In c (ap_remove c l).
Proof.
  intros c l. induction l as [|y l IH]; intros ND Hin; [destruct Hin|]. inversion ND; subst. cbn in Hin.
  destruct (aptr_eqb y c) eqn:E.
  - apply MI_Kit.aptr_eqb_eq in E. subst y. exact (H1 Hin).
  - destruct Hin as [->|Hin]; [rewrite MI_Kit.aptr_eqb_refl in E; discriminate| exact (IH H2 Hin)].
Qed.

Lemma cmalloc_overflow : forall cs n, size_overflows n = true -> cmalloc cs n = SRet (strip cs, None).
Proof. intros cs n H. unfold cmalloc, malloc_core. rewrite H. reflexivity. Qed.

Definition raw_malloc_post (X : list cptr) (s0 : PState) (mo0 : Model) (n : Z) : option bptr -> PState -> Model -> Prop :=
  fun r s' mo' =>
    match r with
    | Some q => AOWN (fst q :: X) s' mo' /\ ~ In (fst q) X /\ n < 2^63 /\ snd q = fresh_off (ps_m s') (fst q) n
    | None => AOWN X s' mo'
    end
    /\ ps_fa s' = ps_fa s0 /\ ps_so s' = ps_so s0 /\ vm_only mo0 mo'.

Theorem raw_malloc_own : forall X s0 mo0 n, AOWN X s0 mo0 -> 0 <= n ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_malloc n) (raw_malloc_post X s0 mo0 n).
Proof.
  intros X s0 mo0 n [(L & Hc & HK & Hi) Hnd] Hn.
  eapply mspec_conseq; [apply (raw_malloc_spec L s0 mo0 n _ (simrel_malloc_contract _ _ _ Hc Hn))| |].
  - intros s mo [-> ->]. auto.
  - intros r s mo (L' & rc & Hp & HPost & HK' & -> & Hfa & Hso & Hvo). cbn [snd] in HPost.
    pose proof (cpath_live _ _ _ _ Hp) as Hlive.
    pose proof (simrel_malloc_step _ _ _ _ _ _ Hc Hn Hp) as Hcr.
    split; [| auto].
    destruct rc as [c|]; cbn [fst snd].
    + split; [| split; [| split; [| reflexivity]]].
      * split.
        -- exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
           cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
        -- constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
      * intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
      * destruct (size_overflows n) eqn:E.
        -- exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
        -- unfold size_overflows in E. apply Z.leb_gt in E. lia.
    + split; [|exact Hnd]. exists L'. split; [exact Hcr|]. split; [exact HK'|]. rewrite Hlive. exact Hi.
Qed.

Corollary raw_malloc_etwf : forall X s mo n, AOWN X s mo -> 0 <= n ->
  etwf (raw_malloc n s) mo (fun p mo' => raw_malloc_post X s mo n (fst p) (snd p) mo').
Proof. intros X s mo n HO Hn. apply (raw_malloc_own X s mo n HO Hn). auto. Qed.

Definition raw_free_post (X : list cptr) (s0 : PState) (mo0 : Model) (c : cptr) : unit -> PState -> Model -> Prop :=
  fun _ s' mo' => AOWN (ap_remove c X) s' mo' /\ ~ In c (ap_remove c X)
                  /\ ps_fa s' = ps_fa s0 /\ ps_so s' = ps_so s0 /\ vm_only mo0 mo'.

Theorem raw_free_own : forall X s0 mo0 (p : bptr), AOWN X s0 mo0 -> In (fst p) X ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_free p) (raw_free_post X s0 mo0 (fst p)).
Proof.
  intros X s0 mo0 p [(L & Hc & HK & Hi) Hnd] HinX.
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; exact HinX).
  eapply mspec_conseq; [apply (raw_free_spec L s0 mo0 p _ (simrel_free_contract _ _ _ Hc Hin))| |].
  - intros s mo [-> ->]. auto.
  - intros r s mo (L' & Hp & HK' & Hfa & Hso & Hvo).
    pose proof (cpath_live _ _ _ _ Hp) as Hlive.
    pose proof (simrel_free_step _ _ _ _ _ Hc Hin Hp) as Hcr.
    split; [| split; [apply ap_remove_notin_self; exact Hnd| auto]].
    split; [| apply NoDup_ap_remove; exact Hnd].
    exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
    cbn. intros x Hx. rewrite Hlive. apply in_ap_remove.
    + apply Hi. eapply ap_remove_In. exact Hx.
    + intros ->. exact (ap_remove_notin_self _ _ Hnd Hx).
Qed.

Corollary raw_free_etwf : forall X s mo (p : bptr), AOWN X s mo -> In (fst p) X ->
  etwf (raw_free p s) mo (fun q mo' => raw_free_post X s mo (fst p) (fst q) (snd q) mo').
Proof. intros X s mo p HO Hin. apply (raw_free_own X s mo p HO Hin). auto. Qed.

(* [comment removed for export] *)
Lemma AOWN_lazy : forall X s mo, AOWN X s mo -> m_vm_lazy mo = [] /\ m_vm_materialized mo = [].
Proof. intros X s mo [(L & _ & HK & _) _]. split; [exact (kl_lazy _ _ _ HK)| exact (kl_mat _ _ _ HK)]. Qed.

Lemma AOWN_perm : forall X Y s mo, Permutation X Y -> AOWN X s mo -> AOWN Y s mo.
Proof.
  intros X Y s mo HP [(L & Hc & HK & Hi) Hnd]. split.
  - exists L. split; [exact Hc|]. split; [exact HK|]. intros c Hc'. apply Hi. eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hc'].
  - eapply Permutation_NoDup; [exact HP| exact Hnd].
Qed.

Lemma AOWN_ext : forall X s s' mo, AOWN X s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> AOWN X s' mo.
Proof. intros X s s' mo [(L & Hc & HK & Hi) Hnd] E1 E2. split; [|exact Hnd]. exists L. rewrite E1, E2. auto. Qed.

(* [comment removed for export] *)
Lemma AOWN_vm_eq : forall X s mo mo', AOWN X s mo -> m_vm mo' = m_vm mo -> AOWN X s mo'.
Proof.
  intros X s mo mo' [(L & Hc & HK & Hi) Hnd] E. split; [|exact Hnd]. exists L. split; [exact Hc|]. split; [|exact Hi].
  assert (E1 : m_vmmaps mo' = m_vmmaps mo) by (unfold m_vmmaps; rewrite E; reflexivity).
  eapply KL_vm_eq; [exact HK| | | | | | | | |]; try (rewrite E1; reflexivity).
  - unfold m_vm_lazy. rewrite E. exact (kl_lazy _ _ _ HK).
  - unfold m_vm_materialized. rewrite E. exact (kl_mat _ _ _ HK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reserved_top_ge : forall l e, In e l -> ehi e <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|]. cbn [reserved_top]. destruct Hin as [<-|Hin].
  - unfold ehi. cbn [fst snd]. lia.
  - pose proof (IH e Hin). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem KL_init : forall (reserved : list (word * word)) (brk : word) mo lim mbase sp,
  m_vmmaps mo = mkVmMapsFull reserved [] [] brk brk lim mbase sp ->
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  0 < bv_unsigned brk -> bv_unsigned brk mod 4096 = 0 -> bv_unsigned brk + 4 * 4096 <= alloc_ceiling ->
  (forall e, In e reserved -> ehi e <= bv_unsigned brk) -> drv_limit <= lim ->
  bv_unsigned sp - stack_max_size = alloc_ceiling ->
  KL (led_init (map wwZ reserved)) 0 mo.
Proof.
  intros reserved brk mo lim mbase sp Evm Hl Hm B1 B2 B3 Btop Hlim Htop.
  constructor; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit led_init ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
  - split; [intros e []| constructor].
  - unfold PGSZ. splits; auto; lia.
  - intros b l [].
  - intros b l k [].
  - constructor.
  - intros b l H. discriminate.
  - intros e [].
  - unfold phase_inv. rewrite Evm. cbn. split; reflexivity.
Qed.

Theorem AOWN_init : forall (reserved : list (word * word)) (brk : word) mo lim mbase sp,
  m_vmmaps mo = mkVmMapsFull reserved [] [] brk brk lim mbase sp ->
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  0 < bv_unsigned brk -> bv_unsigned brk mod 4096 = 0 -> bv_unsigned brk + 4 * 4096 <= alloc_ceiling ->
  (forall e, In e reserved -> ehi e <= bv_unsigned brk) -> drv_limit <= lim ->
  bv_unsigned sp - stack_max_size = alloc_ceiling ->
  AOWN [] (ps_init (map wwZ reserved)) mo.
Proof.
  intros reserved brk mo lim mbase sp Evm Hl Hm B1 B2 B3 Btop Hlim Htop. split; [|constructor].
  exists (led_init (map wwZ reserved)). split; [apply simrel_init|]. split; [|intros c []].
  cbn [ps_brk ps_init]. eapply KL_init; eauto.
Qed.

Lemma reservedZ_wwZ : forall segs, reservedZ segs = map wwZ (segments_reserved segs).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wwZ_inj : forall e1 e2, wwZ e1 = wwZ e2 -> e1 = e2.
Proof.
  intros [a1 n1] [a2 n2] H. unfold wwZ in H. cbn [fst snd] in H. injection H as H1 H2.
  f_equal; apply bv_eq; assumption.
Qed.

Lemma map_wwZ_inj : forall l1 l2, map wwZ l1 = map wwZ l2 -> l1 = l2.
Proof.
  induction l1 as [|e1 l1 IH]; intros [|e2 l2] H; cbn [map] in H; try discriminate; [reflexivity|].
  pose proof (f_equal (hd (0, 0)) H) as H1. pose proof (f_equal (@tl _) H) as H2. cbn [hd tl] in H1, H2.
  f_equal; [apply wwZ_inj; exact H1| apply IH; exact H2].
Qed.

Lemma KL_resv_eq : forall L pbrk mo L' pbrk' mo',
  KL L pbrk mo -> KL L' pbrk' mo' -> ld_resv L' = ld_resv L -> vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo).
Proof.
  intros L pbrk mo L' pbrk' mo' HK HK' E. apply map_wwZ_inj.
  rewrite <- (kl_resv _ _ _ HK), <- (kl_resv _ _ _ HK'). exact E.
Qed.


End CeilWrap.
