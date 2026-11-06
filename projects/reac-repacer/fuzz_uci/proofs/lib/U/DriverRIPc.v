From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import
  YK11 YM05 YM02 YO0i YO0f YO0g YO0e YO0d YO05 YO06 YO09 YO0m YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import
  AllocFree AllocPack SlotPack FrameSlotP AllocPackGSF AllocPackGSFm SlotAgreeV.
Import ListNotations.
Open Scope Z_scope.

(* The walk slot RI_Pc CS (RI_P CS plus GSF) at the run leaves of the driver tree: RI_P from FrameSlotP.driver_RI_P,
   GSF because the driver tree is made of malloc and free, which keep GSF (gf_malloc, kr_free), from GSF_init. And
   RI_Pc gives II, the resource fact the cut-free walk twins *_cfwi need. *)

Lemma gf_free_some : forall p, presI GSF (free (Some p)).
Proof. intros p. exact (gf_of_KR (free (Some p)) (kr_free (Some p))). Qed.

Lemma gf_read_phase : forall fuel L cap buf, presI GSF (read_phase fuel L cap buf).
Proof.
  induction fuel as [|fuel IH]; intros L cap buf; cbn [read_phase].
  - apply presI_ret.
  - destruct (L <? cap); [apply presI_ret|].
    destruct (MAX_INPUT <=? cap); [apply presI_ret|].
    apply presI_bind; [apply gf_malloc|]. intros [nb|]; cbv beta iota; [|apply presI_ret].
    apply presI_bind; [apply gf_free_some|]. intros _. cbv beta iota. apply IH.
Qed.

Lemma gf_driver_m : forall data, presI GSF (driver_m data).
Proof.
  intros data. unfold driver_m.
  apply presI_bind; [apply gf_malloc|]. intros [b0|]; cbv beta iota; [|apply presI_ret].
  apply presI_bind; [apply gf_read_phase|]. intros [ | | buf cap]; cbv beta iota; [apply presI_ret | apply presI_ret |].
  repeat match goal with |- presI _ (if ?b then _ else _) => destruct b; [apply presI_ret|] end.
  apply presI_bind; [apply gf_malloc|]. intros [q|]; cbv beta iota; apply presI_ret.
Qed.

Lemma tall_leaves {A : Type} : forall (P : A -> Prop) (t : itree astate A), tall P t -> leaves P t.
Proof.
  intros P t. induction t as [a | q s k IH | e]; cbn; intros H; [exact H | | exact I].
  intros z _. apply IH. apply H.
Qed.

Lemma driver_GSF : forall data, leaves (fun r => GSF (snd r)) (driver_tree data).
Proof. intros data. apply tall_leaves. exact (gf_driver_m data init_state GSF_init). Qed.

Lemma driver_RI_Pc : forall CS, CS_ok CS -> forall data, leaves (run_RI (RI_Pc CS) (YO06.payload data)) (driver_tree data).
Proof.
  intros CS HCS data.
  eapply leaves_mono; [| exact (leaves_and _ _ _ (driver_RI_P CS HCS data) (driver_GSF data))].
  intros [dl A] [H1 H2]. unfold run_RI in *. cbn [fst snd] in *.
  destruct dl; try exact I. exact (conj H1 H2).
Qed.

Lemma RI_Pc_II : forall CS pl j T A, RI_Pc CS pl j T A -> II A.
Proof. intros CS pl j T A [(d & caps & _ & _ & _ & HR) _]. exact (proj1 HR). Qed.
