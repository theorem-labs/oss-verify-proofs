(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeEFA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvShape.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module HaltsLib.
Import DrvShape.

Definition exits_in (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> forall e, In e tr ->
    match e with
    | ExitEv k _ => In k S
    | KillEv _ _ => False
    | _ => True
    end.

Lemma exits_in_t_eq : forall S T T', t_eq T T' -> exits_in S T -> exits_in S T'.
Proof. intros S T T' Heq H tr HT e Hin. apply (H tr); [apply Heq; exact HT | exact Hin]. Qed.

Lemma exits_in_mono : forall S1 S2 T, (forall k, In k S1 -> In k S2) -> exits_in S1 T -> exits_in S2 T.
Proof.
  intros S1 S2 T Hsub H tr HT e Hin. pose proof (H tr HT e Hin) as X. destruct e; try exact X. apply Hsub. exact X.
Qed.

Lemma exits_in_t_nil : forall S, exits_in S t_nil.
Proof. intros S tr HT e Hin. unfold t_nil in HT. subst tr. destruct Hin. Qed.

Lemma exits_in_t_emit : forall S evs T,
  (forall e, In e evs -> match e with ExitEv k _ => In k S | KillEv _ _ => False | _ => True end) ->
  exits_in S T -> exits_in S (t_emit evs T).
Proof.
  intros S evs T Hevs HT tr Htr e Hin. unfold t_emit in Htr.
  destruct Htr as [Hpre | (tr' & -> & HT')].
  - apply Hevs. clear Hevs HT T. revert evs Hpre Hin. induction tr as [|x xs IH]; intros evs Hpre Hin; [destruct Hin|].
    destruct evs as [|y ys]; [destruct Hpre|]. destruct Hpre as [<- Hpre].
    destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH ys Hpre Hin)].
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (Hevs e Hin) | exact (HT tr' HT' e Hin)].
Qed.

Lemma exits_in_t_exit : forall S code fs, In code S -> exits_in S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply exits_in_t_emit; [| apply exits_in_t_nil].
  intros e [<-|[]]. exact Hin.
Qed.

Lemma exits_in_t_alt2 : forall S A B, exits_in S A -> exits_in S B -> exits_in S (t_alt2 A B).
Proof. intros S A B HA HB tr [H|H]; [exact (HA tr H) | exact (HB tr H)]. Qed.

Lemma exits_in_t_alt : forall S (I : Type) (f : I -> TSet), (forall i, exits_in S (f i)) -> exits_in S (t_alt f).
Proof. intros S I f Hf tr (i & Hi). exact (Hf i tr Hi). Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma realizes_must_exit_in_at : forall S c T,
  realizes segs c T ->
  exits_in S T ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg fcfg segs S c.
Proof using segs.
  intros S c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Honly Hrun.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running; [exact Hrun | | |].
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Habs). discriminate Habs.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & -> & Heqc). injection Heqc as Heqc. subst c'.
      assert (Honly_i : exits_in S (T i)).
      { intros tr HT ev Hin. apply (Honly (evs i ++ tr)); [| apply in_app_iff; right; exact Hin].
        exists i. right. exists tr. split; [reflexivity | exact HT]. }
      destruct (m_halted (cfg_model (nx i))) as [k |] eqn:Hh.
      *
        assert (HTi : T i []) by (eapply realizes_nonempty; apply Hcont).
        assert (Hin_all : forall ev, In ev (evs i) ->
                  match ev with ExitEv k _ => In k S | KillEv _ _ => False | _ => True end).
        { intros ev Hin. apply (Honly (evs i ++ [])); [| rewrite app_nil_r; exact Hin].
          exists i. right. exists []. split; [reflexivity | exact HTi]. }
        destruct (sstep_cfg_next_halts_by_exit segs _ _ _ _ Hss)
          as [Hnone | [(evs0 & code0 & Hevs & Hcode0 & Hk) | (evs0 & sig & Hevs & Hsig)]].
        -- congruence.
        -- pose proof (Hin_all (ExitEv code0 (m_fs (cfg_model (nx i))))) as Hc.
           rewrite Hevs in Hc.
           specialize (Hc (proj2 (in_app_iff _ _ _) (or_intror (in_eq _ _)))).
           cbn in Hc.
           apply (must_exit_in_at_cfg_halted fcfg segs S _ code0); [exact Hcode0 | exact Hc | exact Hk].
        -- pose proof (Hin_all (KillEv sig (m_fs (cfg_model (nx i))))) as Hc.
           rewrite Hevs in Hc.
           specialize (Hc (proj2 (in_app_iff _ _ _) (or_intror (in_eq _ _)))).
           destruct Hc.
      * exact (IH i Honly_i Hh).
  - exfalso. apply Hh. exact Hrun.
  - apply IH; [| exact Hrun]. eapply exits_in_t_eq; [apply t_eq_sym; exact Heq | exact Honly].
Qed.

End WithSegs.

Fixpoint sx_ok (s : shp) : Prop :=
  match s with
  | SWr _ _ k => sx_ok k
  | SX c => 0 <= c < 256
  | SALT a b => sx_ok a /\ sx_ok b
  end.

Lemma D_exits_in : forall fs0 a0 p1 s, sx_ok s -> exits_in byte_codes (D fs0 a0 p1 s).
Proof.
  intros fs0 a0 p1 s. induction s as [fd cs k IH | c | a IHa b IHb]; cbn [sx_ok D]; intros Hs.
  - unfold W. apply exits_in_t_emit; [| exact (IH Hs)].
    intros e Hin. apply in_map_iff in Hin. destruct Hin as (x & <- & _). exact I.
  - unfold X. apply exits_in_t_exit. apply in_byte_codes. exact Hs.
  - destruct Hs as [Ha Hb]. apply exits_in_t_alt2; [exact (IHa Ha) | exact (IHb Hb)].
Qed.

Lemma sx_MSG : forall zs, sx_ok (MSG zs). Proof. intros zs. cbn. lia. Qed.
Lemma sx_USAGE : sx_ok USAGE. Proof. cbn. lia. Qed.
Lemma sx_OPENFAIL : sx_ok OPENFAIL. Proof. cbn. lia. Qed.
Lemma sx_OOM : sx_ok OOM. Proof. cbn. lia. Qed.
Lemma sx_RDERR : sx_ok RDERR. Proof. cbn. lia. Qed.
Lemma sx_FIN : forall w, sx_ok (FIN w). Proof. intros [|[|k]]; cbn; lia. Qed.
Lemma sx_CALLS : forall n w, sx_ok (CALLS n w).
Proof. induction n as [|n IH]; intros w; [exact (sx_FIN w)|]. destruct w as [|k]; cbn [CALLS sx_ok]; apply IH. Qed.
Lemma sx_XC : forall file, sx_ok (XC file).
Proof. intros file. unfold XC, xcode. destruct (count_bit file); cbn; lia. Qed.
Local Ltac sx_ifs := repeat match goal with |- sx_ok (if ?b then _ else _) => destruct b end.
Local Ltac sx_split := cbn [sx_ok]; repeat match goal with |- _ /\ _ => split end.

Local Ltac sx_leaf :=
  lazymatch goal with
  | |- sx_ok (MSG _) => apply sx_MSG
  | |- sx_ok USAGE => apply sx_USAGE
  | |- sx_ok OPENFAIL => apply sx_OPENFAIL
  | |- sx_ok OOM => apply sx_OOM
  | |- sx_ok RDERR => apply sx_RDERR
  | |- sx_ok (XC _) => apply sx_XC
  | |- sx_ok (CALLS _ _) => apply sx_CALLS
  | |- sx_ok (FIN _) => apply sx_FIN
  | |- 0 <= _ < 256 => lia
  end.
Lemma sx_POST : forall file, sx_ok (POST file).
Proof. intros file. unfold POST. sx_ifs; sx_split; sx_leaf. Qed.
Lemma sx_RDn : forall file d cap, sx_ok (RDn file d cap).
Proof.
  intros file d. induction d as [|d IH]; intros cap; cbn [RDn]; sx_ifs; sx_split;
    first [ lazymatch goal with |- sx_ok (POST _) => apply sx_POST | |- sx_ok (RDn _ _ _) => apply IH end | sx_leaf ].
Qed.
Lemma sx_FILE : forall file, sx_ok (FILE file).
Proof. intros file. unfold FILE. sx_split; first [ lazymatch goal with |- sx_ok (RDn _ _ _) => apply sx_RDn end | sx_leaf ]. Qed.
Lemma sx_DIR : sx_ok DIR.
Proof. unfold DIR. sx_split; sx_leaf. Qed.
Lemma sx_K2 : forall fs0 p1, sx_ok (K2 fs0 p1).
Proof.
  intros fs0 p1. unfold K2. sx_ifs; try (lazymatch goal with |- sx_ok OPENFAIL => apply sx_OPENFAIL | |- sx_ok DIR => apply sx_DIR end).
  destruct (fs_lookup fs0 p1); [apply sx_FILE | apply sx_OPENFAIL].
Qed.

Theorem K_exits_byte : forall inp, exits_in byte_codes (K inp).
Proof.
  intros inp. unfold K. destruct (in_argv inp) as [|a0 [|p1 [|? ?]]]; apply D_exits_in;
    first [apply sx_USAGE | apply sx_K2].
Qed.

Theorem K_exits : forall inp, exits_in AnyExit.codes (K inp).
Proof. exact K_exits_byte. Qed.

End HaltsLib.
