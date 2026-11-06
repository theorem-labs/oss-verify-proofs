(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_StepB () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib4Spec5StepB2NFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Nodes:pure_inputC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indK59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5StepB7nf_nodeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib4Spec5StepB6nstepBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or02c59OSSVerify5KrLib4Spec5StepB8NF_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5StepB3tnfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5StepB5tliveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01K4ELinuxProcessSemantics?LinuxProcessSem5State5event03C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition nf_node (n : node) : Prop :=
  match n with NMmap _ _ _ _ | NMprotect _ _ _ => True | _ => False end.

(* [comment removed for export] *)
Definition NF (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap _ _ _ _ | NMprotect _ _ _ =>
      forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
  | _ => True
  end.

Lemma NF_other : forall n mo, ~ nf_node n -> NF n mo.
Proof. intros n mo H. destruct n; cbn in *; auto; exfalso; exact (H I). Qed.

Definition nstepB (B : Z) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs
  /\ (vm_live_bytes (m_vmmaps mo') <= B \/ vm_live_bytes (m_vmmaps mo') <= vm_live_bytes (m_vmmaps mo))
  /\ NF n mo.

Lemma nstepB_nstep : forall B n mo rsp mo' evs, nstepB B n mo rsp mo' evs -> nstep n mo rsp mo' evs.
Proof. intros B n mo rsp mo' evs [H _]. exact H. Qed.

Lemma nstepB_NF : forall B n mo rsp mo' evs, nstepB B n mo rsp mo' evs -> NF n mo.
Proof. intros B n mo rsp mo' evs (_ & _ & H). exact H. Qed.

(* [comment removed for export] *)
Lemma nstepB_no_errno : forall B n mo rsp mo' evs,
  nf_node n -> nstepB B n mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros B n mo rsp mo' evs Hn (Hst & _ & HNF). destruct n; cbn in Hn; try contradiction; exact (HNF _ _ _ Hst).
Qed.

(* [comment removed for export] *)
Lemma nstepB_same : forall B n mo rsp mo' evs,
  ~ nf_node n -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> nstepB B n mo rsp mo' evs.
Proof. intros B n mo rsp mo' evs Hn H E. split; [exact H|]. split; [right; rewrite E; lia| apply NF_other; exact Hn]. Qed.

(* [comment removed for export] *)
Fixpoint tlive {R} (B : Z) (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> vm_live_bytes (m_vmmaps mo') <= B /\ tlive B (k rsp) mo'
  end.

(* [comment removed for export] *)
Fixpoint tnf {R} (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => NF n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tnf (k rsp) mo'
  end.

Lemma tnf_bind : forall {A R} (t : itree node A) (f : A -> itree node R) mo,
  tnf t mo -> (forall a mo', tnf (f a) mo') -> tnf (ITree.bind node t f) mo.
Proof.
  intros A R t. induction t as [r|n k IH]; intros f mo H Hf; cbn in *; [apply Hf|].
  destruct H as [Hn Hk]. split; [exact Hn|]. intros rsp mo' evs Hst. apply IH; [apply (Hk _ _ _ Hst)| exact Hf].
Qed.

Lemma texit_nstepB_of_tlive : forall {R} B (t : itree node R) mo tr,
  tlive B t mo -> tnf t mo -> texit nstep nexit t mo tr -> texit (nstepB B) nexit t mo tr.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo tr Hl Hn Hx; [destruct Hx|].
  cbn [texit] in *. destruct Hx as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & Hst & Hx & ->)].
  - left. exists code, mo'. auto.
  - right. destruct (Hl _ _ _ Hst) as [Hb Hl']. cbn in Hn. destruct Hn as [HNF Hn'].
    exists rsp, mo', evs, tr'. split; [split; [exact Hst| split; [left; exact Hb| exact HNF]]|].
    split; [apply IH; [assumption| apply (Hn' _ _ _ Hst)| assumption]| reflexivity].
Qed.

Lemma texit_nstep_of_nstepB : forall {R} B (t : itree node R) mo tr,
  texit (nstepB B) nexit t mo tr -> texit nstep nexit t mo tr.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo tr Hx; [destruct Hx|].
  cbn [texit] in *. destruct Hx as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & [Hst _] & Hx & ->)].
  - left. exists code, mo'. auto.
  - right. exists rsp, mo', evs, tr'. split; [exact Hst|]. split; [apply IH; assumption| reflexivity].
Qed.

Lemma tpath_nstep_of_nstepB : forall {R} B (t : itree node R) mo tr r mo',
  tpath (nstepB B) t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof.
  intros R B t. induction t as [x|n k IH]; intros mo tr r mo' Hp; cbn [tpath] in *; [exact Hp|].
  destruct Hp as (rsp & mo1 & evs & tr' & [Hst _] & Hp & ->). exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [apply IH; exact Hp| reflexivity].
Qed.
