(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (39 recorded proofs replaced by written proofs (TS_acct, TS_unfold_vis, TS_tsafeA and 36 more); nstep_io_shape re-proved). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad RSimProg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AProto.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ATsafeCore () := "c59OSSVerify5KrLib5BothW:ATsafeCore5postTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib5BothW:ATsafeCore2TSC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA7acct_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nsafeAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4LibA6NodesA6nstepAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6alw_leC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA3alwC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib5BothW:ATsafeCore7TS_acctC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indC47Corelib4Init5Logic3iffc59OSSVerify5KrLib5BothW:ATsafeCore=TS_unfold_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6tsafeAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5BothW:ATsafeCore9TS_tsafeAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore7TS_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore6TS_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore7TS_bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore2EQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore8TS_ebindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore9TS_ret_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore:TS_ret_unrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore:TS_EQ_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC59OSSVerify5KrLib4LibA5ExecF<footprint_okC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C46Stdlib5Lists4List2InC59OSSVerify5KrLib4LibA8AcctCore=nonlazy_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC56Stdlib6ZArith6BinInt1Z2leC4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib5BothW:ATsafeCore:acct_ok_vmC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidc59OSSVerify5KrLib5BothW:ATsafeCore4preTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore5postMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore5TS_ioC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib5BothW:ATsafeCore3TSMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore2MQC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib5BothW:ATsafeCore:TSM_conseqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore7TSM_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore8TSM_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore7TSM_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore8TSM_munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore8TSM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib5BothW:ATsafeCore<TSM_bind_getC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib5BothW:ATsafeCore6TSM_ifC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore8TSM_pureC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore7TSM_exIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib5BothW:ATsafeCore8TSM_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore;TSM_msys_ioC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore4abudC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic2or01c59OSSVerify5KrLib5BothW:ATsafeCore6aunionC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2or00C47Corelib4Init3Nat3addK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions9bv_eq_decC46Stdlib5Lists4List6in_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K47Corelib7Numbers7BinNums1Z02C46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic6eq_indK46Stdlib5Lists4List5NoDup02C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succI47Corelib4Init5Logic5False00c59OSSVerify5KrLib5BothW:ATsafeCore<nodup_extendC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib5BothW:ATsafeCore:pages_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6to_natK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06c59OSSVerify5KrLib5BothW:ATsafeCoreApages_from_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore;range_pagesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith6BinInt1Z;div_le_monoK46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib5BothW:ATsafeCore=pages_from_inC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC56Stdlib6ZArith6BinInt1Z3powC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib4LibA5ExecF9rng_fp_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore@range_pages_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ATsafeCore?rng_fp_ok_unionC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Core.
Variable NMAX : nat.

(* [comment removed for export] *)
Definition postT (R : Type) : Type := R -> footprint -> alw -> Model -> Prop.

Fixpoint TS {R} (RNG : footprint) (A : alw) (t : itree node R) (mo : Model) (Q : postT R) {struct t} : Prop :=
  acct_ok NMAX RNG A mo /\
  match t with
  | Ret r => Q r RNG A mo
  | Vis n k => nsafeA NMAX n mo /\
      forall rsp mo' evs, nstepA n mo rsp mo' evs ->
        exists RNG' A', fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (k rsp) mo' Q
  end.

Lemma TS_acct : forall {R} RNG A (t : itree node R) mo Q, TS RNG A t mo Q -> acct_ok NMAX RNG A mo.
Proof. intros R RNG A [r|n k] mo Q H; exact (proj1 H). Qed.

Lemma TS_unfold_vis : forall {R} RNG A n (k : resp -> itree node R) mo Q,
  TS RNG A (Vis n k) mo Q <->
  (acct_ok NMAX RNG A mo /\ nsafeA NMAX n mo /\
   forall rsp mo' evs, nstepA n mo rsp mo' evs ->
     exists RNG' A', fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (k rsp) mo' Q).
Proof. intros. cbn. tauto. Qed.

(* [comment removed for export] *)
Lemma TS_tsafeA : forall {R} (t : itree node R) RNG A mo Q,
  TS RNG A t mo Q -> tsafeA nstepA (nsafeA NMAX) fstepS NMAX RNG A t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros RNG A mo Q H; cbn in H |- *.
  - split; [exact (proj1 H)| exact I].
  - destruct H as (HA & HS & HK). split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
    exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH. exact HT.
Qed.

Lemma TS_mono : forall {R} (t : itree node R) RNG A mo (Q Q' : postT R),
  TS RNG A t mo Q -> (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q r RNG' A' mo' -> Q' r RNG' A' mo') -> TS RNG A t mo Q'.
Proof.
  intros R t. induction t as [r|n k IH]; intros RNG A mo Q Q' H HQ; cbn in H |- *.
  - destruct H as [HA HQ1]. split; [exact HA| apply HQ; assumption].
  - destruct H as (HA & HS & HK). split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
    exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH; [exact HT| exact HQ].
Qed.

Lemma TS_ret : forall {R} (r : R) RNG A mo (Q : postT R),
  acct_ok NMAX RNG A mo -> Q r RNG A mo -> TS RNG A (Ret r) mo Q.
Proof. intros. cbn. split; assumption. Qed.

Lemma TS_bind : forall {X Y} (t : itree node X) (k : X -> itree node Y) RNG A mo (Q1 : postT X) (Q : postT Y),
  TS RNG A t mo Q1 ->
  (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 r RNG' A' mo' -> TS RNG' A' (k r) mo' Q) ->
  TS RNG A (bind node t k) mo Q.
Proof.
  intros X Y t. induction t as [r|n k0 IH]; intros k RNG A mo Q1 Q H HK; cbn in H.
  - destruct H as [HA H1]. cbn. apply HK; assumption.
  - destruct H as (HA & HS & HC). cbn. split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HC rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
    exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH; [exact HT| exact HK].
Qed.

(* [comment removed for export] *)
Definition EQ {X} (Q : postT X) : postT (exc X) :=
  fun r RNG A mo => match r with Unr => True | Ok x => Q x RNG A mo end.

Lemma TS_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) RNG A mo (Q1 : postT X) (Q : postT Y),
  TS RNG A t mo (EQ Q1) ->
  (forall x RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 x RNG' A' mo' -> TS RNG' A' (f x) mo' (EQ Q)) ->
  TS RNG A (ebind t f) mo (EQ Q).
Proof.
  intros X Y t f RNG A mo Q1 Q H HK. unfold ebind. eapply TS_bind; [exact H|].
  intros [|x] RNG' A' mo' HA H1; cbn in H1.
  - apply TS_ret; [exact HA| exact I].
  - apply HK; assumption.
Qed.

Lemma TS_ret_ok : forall {X} (x : X) RNG A mo (Q : postT X),
  acct_ok NMAX RNG A mo -> Q x RNG A mo -> TS RNG A (Ret (Ok x)) mo (EQ Q).
Proof. intros. apply TS_ret; assumption. Qed.

Lemma TS_ret_unr : forall {X} RNG A mo (Q : postT X), acct_ok NMAX RNG A mo -> TS RNG A (Ret Unr) mo (EQ Q).
Proof. intros. apply TS_ret; [assumption| exact I]. Qed.

Lemma TS_EQ_mono : forall {X} (t : itree node (exc X)) RNG A mo (Q Q' : postT X),
  TS RNG A t mo (EQ Q) -> (forall x RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q x RNG' A' mo' -> Q' x RNG' A' mo') ->
  TS RNG A t mo (EQ Q').
Proof. intros X t RNG A mo Q Q' H HQ. eapply TS_mono; [exact H|]. intros [|x] RNG' A' mo' HA H1; cbn in *; [exact I| apply HQ; assumption]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma acct_ok_vm : forall RNG A mo mo',
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_vm_materialized mo' = m_vm_materialized mo ->
  acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A mo'.
Proof.
  intros RNG A mo mo' E1 E2 E3 (F & L & R). unfold acct_ok. rewrite E2, E1.
  split; [exact F|]. split; [exact L|]. unfold nonlazy_bytes in *. rewrite E1, E2. exact R.
Qed.

Lemma acct_ok_with_fds : forall RNG A f mo, acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A (with_fds f mo).
Proof. intros. eapply acct_ok_vm; [ | | | eassumption]; reflexivity. Qed.
Lemma acct_ok_with_tid : forall RNG A t mo, acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A (with_tid t mo).
Proof. intros. eapply acct_ok_vm; [ | | | eassumption]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_io_shape : forall n mo eff mo' evs,
  io_node n -> nstep n mo eff mo' evs -> mo' = mo \/ (exists f, mo' = with_fds f mo) \/ (exists t, mo' = with_tid t mo).
Proof.
  intros n mo eff mo' evs Hio H. destruct n; cbn in Hio; try contradiction; cbn [nstep] in H.
  - destruct H as (k & _ & _ & -> & _). left; reflexivity.
  - destruct H as [-> _]. left; reflexivity.
  - destruct H as [_ H]. destruct (Nat.leb path_max (length path)); [destruct H as [_ ->]; left; reflexivity|].
    assert (OR : forall ent, open_result mo ent eff mo' -> mo' = mo \/ (exists f, mo' = with_fds f mo) \/ (exists t, mo' = with_tid t mo)).
    { intros ent [(e & _ & _ & ->)|(_ & _ & ->)]; [left; reflexivity| right; left; eexists; reflexivity]. }
    destruct path; [destruct H as [_ ->]; left; reflexivity|].
    match type of H with (if ?c then _ else _) => destruct c; [apply (OR _ H)|] end.
    destruct (fs_lookup _ _); [apply (OR _ H)| destruct H as [_ ->]; left; reflexivity].
  - destruct H as [_ H]. destruct (fd_lookup _ _) as [[ch|p off|p1 off1|p2 off2|p3 off3| |sk|pid pw|dnr dnw| |sid sd sst|ectx|fam|aid af]|]; try contradiction;
      try (destruct H as [_ ->]; left; reflexivity).
    destruct (fs_lookup _ _); [|contradiction]. destruct H as [_ ->]. right; left; eexists; reflexivity.
  - destruct H as (_ & _ & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [right; left; eexists; reflexivity| left; reflexivity].
  - destruct H as (_ & _ & ->). left; reflexivity.
  - destruct H as (_ & t & _ & H). destruct (m_tid mo); destruct H as [_ ->]; [left; reflexivity| right; right; eexists; reflexivity].
Qed.

Lemma acct_ok_io : forall n mo eff mo' evs RNG A,
  io_node n -> nstep n mo eff mo' evs -> acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A mo'.
Proof.
  intros n mo eff mo' evs RNG A Hio Hst HA.
  destruct (nstep_io_shape n mo eff mo' evs Hio Hst) as [-> | [(f & ->) | (t & ->)]];
    [exact HA| apply acct_ok_with_fds; exact HA| apply acct_ok_with_tid; exact HA].
Qed.

(* [comment removed for export] *)
Lemma TS_io : forall {R} n (k : resp -> itree node R) RNG A mo (Q : postT R),
  io_node n -> acct_ok NMAX RNG A mo ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> acct_ok NMAX RNG A mo' -> TS RNG A (k rsp) mo' Q) ->
  TS RNG A (Vis n k) mo Q.
Proof.
  intros R n k RNG A mo Q Hio HA HK. cbn. split; [exact HA|]. split.
  { split; [destruct n; cbn in Hio |- *; try contradiction; exact I | destruct n; cbn in Hio |- *; try contradiction; exact I]. }
  intros rsp mo' evs Hst.
  assert (Hst' : nstep n mo rsp mo' evs) by (destruct n; cbn in Hio; try contradiction; exact Hst).
  exists RNG, A. split; [apply fstepS_id; destruct n; cbn in Hio |- *; try contradiction; exact I|].
  split; [apply alw_le_refl|]. apply (HK rsp mo' evs); [exact Hst'| eapply (acct_ok_io n mo rsp mo' evs); eauto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Triples.
Context {St : Type}.

Definition preT : Type := footprint -> alw -> St -> Model -> Prop.
Definition postM (X : Type) : Type := X -> footprint -> alw -> St -> Model -> Prop.

(* [comment removed for export] *)
Definition MQ {X} (Q : postM X) : postT (exc (X * St)) := EQ (fun p RNG A mo => Q (fst p) RNG A (snd p) mo).

Definition TSM {X} (P : preT) (m : M St X) (Q : postM X) : Prop :=
  forall RNG A s mo, P RNG A s mo -> TS RNG A (m s) mo (MQ Q).

Lemma TSM_conseq : forall {X} (P P' : preT) (m : M St X) (Q Q' : postM X),
  TSM P m Q -> (forall RNG A s mo, P' RNG A s mo -> P RNG A s mo) ->
  (forall x RNG A s mo, acct_ok NMAX RNG A mo -> Q x RNG A s mo -> Q' x RNG A s mo) -> TSM P' m Q'.
Proof.
  intros X P P' m Q Q' H HP HQ RNG A s mo Hp. eapply TS_EQ_mono; [apply H; apply HP; exact Hp|].
  intros [x s'] RNG' A' mo' HA H1. cbn in *. apply HQ; assumption.
Qed.
Lemma TSM_pre : forall {X} (P P' : preT) (m : M St X) (Q : postM X),
  TSM P m Q -> (forall RNG A s mo, P' RNG A s mo -> P RNG A s mo) -> TSM P' m Q.
Proof. intros. eapply TSM_conseq; eauto. Qed.
Lemma TSM_post : forall {X} (P : preT) (m : M St X) (Q Q' : postM X),
  TSM P m Q -> (forall x RNG A s mo, acct_ok NMAX RNG A mo -> Q x RNG A s mo -> Q' x RNG A s mo) -> TSM P m Q'.
Proof. intros. eapply TSM_conseq; eauto. Qed.

Lemma TSM_ret : forall {X} (x : X) (P : preT) (Q : postM X),
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo /\ Q x RNG A s mo) -> TSM P (mret x) Q.
Proof. intros X x P Q H RNG A s mo Hp. destruct (H _ _ _ _ Hp) as [HA HQ]. apply TS_ret_ok; [exact HA| exact HQ]. Qed.

Lemma TSM_munr : forall {X} (P : preT) (Q : postM X),
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) -> TSM P (munr (A:=X)) Q.
Proof. intros X P Q H RNG A s mo Hp. apply TS_ret_unr. apply (H _ _ _ _ Hp). Qed.

Lemma TSM_bind : forall {X Y} (P : preT) (m : M St X) (f : X -> M St Y) (Q1 : postM X) (Q : postM Y),
  TSM P m Q1 -> (forall x, TSM (fun RNG A s mo => acct_ok NMAX RNG A mo /\ Q1 x RNG A s mo) (f x) Q) -> TSM P (mbind m f) Q.
Proof.
  intros X Y P m f Q1 Q Hm Hf RNG A s mo Hp. unfold mbind. eapply TS_ebind; [apply Hm; exact Hp|].
  intros [x s'] RNG' A' mo' HA H1. cbn in H1. apply Hf. split; assumption.
Qed.

Lemma TSM_get : forall (P : preT),
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
  TSM P mget (fun s' RNG A s mo => s' = s /\ P RNG A s mo).
Proof. intros P H RNG A s mo Hp. apply TS_ret_ok; [apply (H _ _ _ _ Hp)|]. cbn. auto. Qed.

Lemma TSM_upd : forall (f : St -> St) (P : preT),
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
  TSM P (mupd f) (fun _ RNG A s' mo => exists s, s' = f s /\ P RNG A s mo).
Proof. intros f P H RNG A s mo Hp. apply TS_ret_ok; [apply (H _ _ _ _ Hp)|]. cbn. eauto. Qed.

(* [comment removed for export] *)
Lemma TSM_bind_get : forall {X} (P : preT) (k : St -> M St X) (Q : postM X),
  (forall s0, TSM (fun RNG A s mo => s = s0 /\ P RNG A s mo) (k s0) Q) ->
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
  TSM P (mbind mget k) Q.
Proof.
  intros X P k Q Hk HA RNG A s mo Hp. unfold mbind, mget. cbn. apply Hk. auto.
Qed.

Lemma TSM_if : forall {X} (b : bool) (P : preT) (m1 m2 : M St X) (Q : postM X),
  (b = true -> TSM P m1 Q) -> (b = false -> TSM P m2 Q) -> TSM P (if b then m1 else m2) Q.
Proof. intros X [|] P m1 m2 Q H1 H2; [apply H1| apply H2]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma TSM_pure : forall {X} (P : preT) (phi : Prop) (m : M St X) (Q : postM X),
  (forall RNG A s mo, P RNG A s mo -> phi) -> (phi -> TSM P m Q) -> TSM P m Q.
Proof. intros X P phi m Q Hphi H RNG A s mo Hp. apply (H (Hphi _ _ _ _ Hp)). exact Hp. Qed.

(* [comment removed for export] *)
Lemma TSM_exI : forall {X T} (P : T -> preT) (m : M St X) (Q : postM X),
  (forall x, TSM (P x) m Q) -> TSM (fun RNG A s mo => exists x, P x RNG A s mo) m Q.
Proof. intros X T P m Q H RNG A s mo (x & Hp). apply (H x). exact Hp. Qed.

(* [comment removed for export] *)
Lemma TSM_loop : forall {X R} (I : X -> preT) (Q : postM R) (body : X -> M St (X + R)),
  (forall x, TSM (I x) (body x) (fun r RNG A s mo => match r with inl x' => I x' RNG A s mo | inr r => Q r RNG A s mo end)) ->
  (forall x RNG A s mo, I x RNG A s mo -> acct_ok NMAX RNG A mo) ->
  forall fuel x, TSM (I x) (mloop fuel body x) Q.
Proof.
  intros X R I Q body HB HA fuel. induction fuel as [|fuel IH]; intros x.
  - cbn. apply TSM_munr. apply HA.
  - cbn [mloop]. eapply TSM_bind; [apply HB|]. intros [x'|r].
    + eapply TSM_pre; [apply IH|]. cbv beta. intros RNG A s mo [_ H]; exact H.
    + apply TSM_ret. cbv beta. intros RNG A s mo [H1 H2]. auto.
Qed.

(* [comment removed for export] *)
Lemma TSM_msys_io : forall {X} n (dec : resp -> option X) (P : preT) (Q : postM X),
  io_node n ->
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
  (forall RNG A s mo rsp mo' evs x, P RNG A s mo -> nstep n mo rsp mo' evs -> dec rsp = Some x -> Q x RNG A s mo') ->
  TSM P (msys n dec) Q.
Proof.
  intros X n dec P Q Hio HA HQ RNG A s mo Hp. unfold msys, enode.
  apply TS_io; [exact Hio| apply (HA _ _ _ _ Hp)|].
  intros rsp mo' evs Hst HA'. destruct (dec rsp) as [x|] eqn:E.
  - apply TS_ret_ok; [exact HA'|]. cbn. eapply HQ; eauto.
  - apply TS_ret_unr. exact HA'.
Qed.
End Triples.
End Core.

End CANSEC1.
Arguments TS NMAX {R} RNG A t mo Q.
Arguments TSM NMAX {St X} P m Q.
Arguments MQ {St X} Q.
Arguments EQ {X} Q.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition abud (A : alw) (k : Z) : Prop :=
  exists L : list word, List.NoDup L /\ Z.of_nat (length L) <= k /\ forall p, A p -> In p L.

Lemma abud_mono : forall A k k', abud A k -> k <= k' -> abud A k'.
Proof. intros A k k' (L & N & Hl & HL) Hk. exists L. split; [exact N|]. split; [lia| exact HL]. Qed.

Lemma abud_le : forall (A B : alw) k, abud B k -> alw_le A B -> abud A k.
Proof. intros A B k (L & N & Hl & HL) HAB. exists L. split; [exact N|]. split; [exact Hl|]. intros p Hp. apply HL, HAB, Hp. Qed.

(* [comment removed for export] *)
Definition aunion (A : alw) (ps : list word) : alw := fun p => A p \/ In p ps.

Lemma aunion_le : forall A ps, alw_le A (aunion A ps).
Proof. intros A ps p H. left; exact H. Qed.
Lemma aunion_in : forall A ps p, In p ps -> aunion A ps p.
Proof. intros A ps p H. right; exact H. Qed.

Lemma nodup_extend : forall (L ps : list word), List.NoDup L ->
  exists L', List.NoDup L' /\ (length L' <= length L + length ps)%nat /\ (forall p, In p L \/ In p ps -> In p L').
Proof.
  intros L ps N. induction ps as [|q ps IH].
  - exists L. split; [exact N|]. split; [cbn; lia|]. intros p [H|[]]; exact H.
  - destruct IH as (L' & N' & Hlen & HL').
    destruct (in_dec (fun x y => bv_eq_dec _ x y) q L') as [Hin|Hnin].
    + exists L'. split; [exact N'|]. split; [cbn; lia|].
      intros p [H|[<-|H]]; [apply HL'; left; exact H| exact Hin| apply HL'; right; exact H].
    + exists (q :: L'). split; [constructor; [exact Hnin| exact N']|]. split; [cbn; lia|].
      intros p [H|[<-|H]]; [right; apply HL'; left; exact H| left; reflexivity| right; apply HL'; right; exact H].
Qed.

Lemma abud_union : forall A k ps, abud A k -> abud (aunion A ps) (k + Z.of_nat (length ps)).
Proof.
  intros A k ps (L & N & Hl & HL). destruct (nodup_extend L ps N) as (L' & N' & Hlen & HL').
  exists L'. split; [exact N'|]. split; [lia|]. intros p [H|H]; apply HL'; [left; apply HL; exact H| right; exact H].
Qed.

(* [comment removed for export] *)
Fixpoint pages_from (p0 : Z) (n : nat) : list word :=
  match n with O => [] | S n' => Z_to_bv 64 p0 :: pages_from (p0 + 4096) n' end.

Lemma pages_from_length : forall p0 n, length (pages_from p0 n) = n.
Proof. intros p0 n. revert p0. induction n; intros; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma pages_from_in : forall p0 n (i : nat), (i < n)%nat -> In (Z_to_bv 64 (p0 + 4096 * Z.of_nat i)) (pages_from p0 n).
Proof.
  intros p0 n. revert p0. induction n as [|n IH]; intros p0 i Hi; [lia|]. cbn. destruct i as [|i].
  - left. f_equal. lia.
  - right. replace (p0 + 4096 * Z.of_nat (S i)) with (p0 + 4096 + 4096 * Z.of_nat i) by lia. apply IH. lia.
Qed.

(* [comment removed for export] *)
Definition range_pages (lo len : Z) : list word :=
  pages_from (lo / 4096 * 4096) (Z.to_nat ((lo + len - 1) / 4096 - lo / 4096 + 1)).

Lemma range_pages_length : forall lo len, 0 <= lo -> 0 < len ->
  Z.of_nat (length (range_pages lo len)) <= len / 4096 + 2.
Proof.
  intros lo len Hlo Hlen. unfold range_pages. rewrite pages_from_length.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
  pose proof (Z.div_mod len 4096 ltac:(lia)). pose proof (Z.mod_pos_bound len 4096 ltac:(lia)). lia.
Qed.

Lemma range_pages_spec : forall lo len z, 0 <= lo -> lo <= z < lo + len ->
  In (page_base_of z) (range_pages lo len).
Proof.
  intros lo len z Hlo Hz. unfold range_pages, page_base_of, page_size.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod z 4096 ltac:(lia)). pose proof (Z.mod_pos_bound z 4096 ltac:(lia)).
  pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
  assert (D1 : lo / 4096 <= z / 4096) by (apply Z.div_le_mono; lia).
  assert (D2 : z / 4096 <= (lo + len - 1) / 4096) by (apply Z.div_le_mono; lia).
  replace (z / 4096 * 4096) with (lo / 4096 * 4096 + 4096 * Z.of_nat (Z.to_nat (z / 4096 - lo / 4096))) by lia.
  apply pages_from_in. lia.
Qed.

(* [comment removed for export] *)
Lemma rng_fp_ok_union : forall lz A lo len ps,
  0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> In (page_base_of z) ps) ->
  rng (fp_ok lz (aunion A ps)) lo len.
Proof.
  intros lz A lo len ps Hlo Hhi H. apply rng_fp_ok; [exact Hlo| exact Hhi|]. intros z Hz. right. right. apply H. exact Hz.
Qed.

Lemma rng_fp_ok_range : forall lz A lo len, 0 <= lo -> lo + len <= 2^64 ->
  rng (fp_ok lz (aunion A (range_pages lo len))) lo len.
Proof. intros. apply rng_fp_ok_union; auto. intros z Hz. apply range_pages_spec; lia. Qed.

(* [comment removed for export] *)
Lemma rng_fp_ok_allowed : forall lz (A : alw) lo len,
  0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> A (page_base_of z)) -> rng (fp_ok lz A) lo len.
Proof. intros lz A lo len Hlo Hhi H. apply rng_fp_ok; auto. intros z Hz. right. apply H. exact Hz. Qed.
End CANSEC2.
