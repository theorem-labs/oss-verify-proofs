(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvShape.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Top Require Import HaltsLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.LimSim Require Import LimSimSys.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module HaltsKitB.
Import DrvShape.
Import HaltsLib.HaltsLib.

(* [comment removed for export] *)
Definition S02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

(* [comment removed for export] *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m Hoff.
  destruct (classic (exists eff' m' evs', syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H|H];
    [left; exact H | right].
  intros eff' m' evs' Hs. destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity|].
  exfalso. apply H. exists eff', m', evs'. split; [exact Hs | exact E].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof. intros cfg [segs pc ph] lim [sp brk0 mb rnd] inp. cbn [run_decided]. apply decided_from_classic. Qed.

(* [comment removed for export] *)
Fixpoint sx02 (s : shp) : Prop :=
  match s with
  | SWr _ _ k => sx02 k
  | SX c => c = 0 \/ c = 2
  | SALT a b => sx02 a /\ sx02 b
  end.

Lemma in_S02 : forall c, c = 0 \/ c = 2 -> In (Z_to_bv 64 c) S02.
Proof. intros c [-> | ->]; [left; reflexivity | right; left; reflexivity]. Qed.

Lemma D_exits_in02 : forall fs0 a0 p1 s, sx02 s -> exits_in S02 (D fs0 a0 p1 s).
Proof.
  intros fs0 a0 p1 s. induction s as [fd cs k IH | c | a IHa b IHb]; cbn [sx02 D]; intros Hs.
  - unfold W. apply exits_in_t_emit; [| exact (IH Hs)].
    intros e Hin. apply in_map_iff in Hin. destruct Hin as (x & <- & _). exact I.
  - unfold X. apply exits_in_t_exit. apply in_S02. exact Hs.
  - destruct Hs as [Ha Hb]. apply exits_in_t_alt2; [exact (IHa Ha) | exact (IHb Hb)].
Qed.

Lemma sx_MSG : forall zs, sx02 (MSG zs). Proof. intros zs. cbn. lia. Qed.
Lemma sx_USAGE : sx02 USAGE. Proof. cbn. lia. Qed.
Lemma sx_OPENFAIL : sx02 OPENFAIL. Proof. cbn. lia. Qed.
Lemma sx_OOM : sx02 OOM. Proof. cbn. lia. Qed.
Lemma sx_RDERR : sx02 RDERR. Proof. cbn. lia. Qed.
Lemma sx_FIN : forall w, sx02 (FIN w). Proof. intros [|[|k]]; cbn; lia. Qed.
Lemma sx_CALLS : forall n w, sx02 (CALLS n w).
Proof. induction n as [|n IH]; intros w; [exact (sx_FIN w)|]. destruct w as [|k]; cbn [CALLS sx02]; apply IH. Qed.
Lemma sx_XC : forall file, sx02 (XC file).
Proof. intros file. unfold XC, xcode. destruct (count_bit file); cbn; lia. Qed.
Local Ltac sx_ifs := repeat match goal with |- sx02 (if ?b then _ else _) => destruct b end.
Local Ltac sx_split := cbn [sx02]; repeat match goal with |- _ /\ _ => split end.
Local Ltac sx_leaf :=
  lazymatch goal with
  | |- sx02 (MSG _) => apply sx_MSG
  | |- sx02 USAGE => apply sx_USAGE
  | |- sx02 OPENFAIL => apply sx_OPENFAIL
  | |- sx02 OOM => apply sx_OOM
  | |- sx02 RDERR => apply sx_RDERR
  | |- sx02 (XC _) => apply sx_XC
  | |- sx02 (CALLS _ _) => apply sx_CALLS
  | |- sx02 (FIN _) => apply sx_FIN
  | |- _ = 0 \/ _ = 2 => lia
  end.
Lemma sx_POST : forall file, sx02 (POST file).
Proof. intros file. unfold POST. sx_ifs; sx_split; sx_leaf. Qed.
Lemma sx_RDn : forall file d cap, sx02 (RDn file d cap).
Proof.
  intros file d. induction d as [|d IH]; intros cap; cbn [RDn]; sx_ifs; sx_split;
    first [ lazymatch goal with |- sx02 (POST _) => apply sx_POST | |- sx02 (RDn _ _ _) => apply IH end | sx_leaf ].
Qed.
Lemma sx_FILE : forall file, sx02 (FILE file).
Proof. intros file. unfold FILE. sx_split; first [ lazymatch goal with |- sx02 (RDn _ _ _) => apply sx_RDn end | sx_leaf ]. Qed.
Lemma sx_DIR : sx02 DIR.
Proof. unfold DIR. sx_split; sx_leaf. Qed.
Lemma sx_K2 : forall fs0 p1, sx02 (K2 fs0 p1).
Proof.
  intros fs0 p1. unfold K2. sx_ifs; try (lazymatch goal with |- sx02 OPENFAIL => apply sx_OPENFAIL | |- sx02 DIR => apply sx_DIR end).
  destruct (fs_lookup fs0 p1); [apply sx_FILE | apply sx_OPENFAIL].
Qed.

Theorem K_exits02 : forall inp, exits_in S02 (K inp).
Proof.
  intros inp. unfold K. destruct (in_argv inp) as [|a0 [|p1 [|? ?]]]; apply D_exits_in02;
    first [apply sx_USAGE | apply sx_K2].
Qed.

(* [comment removed for export] *)
Section OfRz.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo).
Variables (Lbig Lsmall : Z).
Variable S : list word.
Variable KK : ProcInput -> TSet.
Hypothesis KK_exits : forall inp, valid_input inp -> exits_in S (KK inp).
Hypothesis HL : Lsmall <= Lbig.
Hypothesis RZ : forall sp brk0 mb rnd inp,
  valid_input inp -> valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mb rnd) inp ->
  realizes segs (init_config segs pc ph sp brk0 mb rnd Lbig inp) (KK inp).

Theorem must_exit_big : forall en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  must_exit_in_scfg fcfg S (mkImage segs pc ph) Lbig en inp.
Proof using segs pc ph Lbig S KK KK_exits RZ.
  intros [sp brk0 mb rnd] inp Hen Hv.
  cbn [must_exit_in_scfg].
  eapply realizes_must_exit_in_at; [exact (RZ sp brk0 mb rnd inp Hv Hen) | exact (KK_exits inp Hv) | reflexivity].
Qed.

Theorem must_exit_big_fo : forall en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) Lbig en inp.
Proof using segs pc ph Lbig S KK KK_exits RZ.
  intros en inp Hen Hv.
  apply (must_exit_in_scfg_mono forced_only_cfg fcfg S (mkImage segs pc ph) Lbig en inp
           (forced_only_cfg_least fcfg) (run_decided_classic _ _ _ _ _)).
  exact (must_exit_big en inp Hen Hv).
Qed.

Theorem haltsB_of_rz : halts_allowed_T_scfg_budgets forced_only_cfg Lsmall S (mkImage segs pc ph).
Proof.
  intros en inp Hen Hv HB.
  apply (must_exit_in_scfg_relim_closed forced_only_cfg S (mkImage segs pc ph) Lbig Lsmall en inp HL HB).
  exact (must_exit_big_fo en inp Hen Hv).
Qed.
End OfRz.

End HaltsKitB.
