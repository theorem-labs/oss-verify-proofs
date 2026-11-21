(** * Lib.MustExitTreeFO — [Lib.MustExitTree] over the filtered step relation

    [MustExitTree.tree_at_must_exit_in] turns a node tree's facts into [MustExit.must_exit_in_at] through
    the unfiltered [ITree.node_sound].  Here the same induction, step for step, over
    [ITreeFO.node_sound_cfg cfg], ending in [MustExit.must_exit_in_at_cfg cfg]. *)

From Stdlib Require Import List ZArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Exec ITree MustExitTree ITreeFO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section MustExitTreeFO.
Variable cfg : SpuriousCfg.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : node_sound_cfg cfg node segs at_node nstep nexit minv nsafe.
Variable S : list word.
Hypothesis EX : exits_ok node at_node nexit minv nsafe S.

Local Notation ME c := (must_exit_in_at_cfg cfg segs S c).
Local Notation tree_at := (ITree.tree_at segs at_node nstep minv nsafe).

Lemma msteps_must_exit_cfg : forall ms ms1 mo,
  m_halted mo = None -> minv mo ->
  msteps segs ms ms1 -> ME (mkCfg ms1 mo) -> ME (mkCfg ms mo).
Proof.
  intros ms ms1 mo Hh Hinv Hm. induction Hm as [ms|ms msa msb Hstep Hrest IH]; intros Hend; [exact Hend|].
  pose proof (nsc_lazy _ _ _ _ _ _ _ _ NS mo Hinv) as Hlz.
  apply must_exit_in_at_cfg_running.
  - exact Hh.
  - exists [], (SNext (mkCfg msa mo)). exact (mstep_sstep_cfg cfg segs ms msa mo Hh Hlz Hstep).
  - intros evs Herr. destruct (sstep_cfg_mstep_inv cfg segs ms mo msa evs SError Hlz Hstep Herr) as [_ H].
    discriminate H.
  - intros evs c' Hss. destruct (sstep_cfg_mstep_inv cfg segs ms mo msa evs (SNext c') Hlz Hstep Hss) as [_ H].
    injection H as ->. apply IH. exact Hend.
Qed.

Theorem tree_at_must_exit_in_cfg : forall (R : Type) (t : itree node R) Q ms mo,
  tree_at t Q ms mo -> ME (mkCfg ms mo).
Proof.
  intros R t. induction t as [r|n k IH]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret _ nstep r mo Hl).
  - pose proof HT as (Himpl & Hl & Hh & Hinv & Hsf).
    cbn [ITree.impl] in Himpl. destruct Himpl as (ms1 & Hrun & Hat & Hk).
    apply (msteps_must_exit_cfg ms ms1 mo Hh Hinv Hrun).
    apply must_exit_in_at_cfg_running.
    + exact Hh.
    + destruct (nsc_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv (proj1 Hsf))
        as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
      * destruct (nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss).
        eexists _, _. exact Hss.
      * destruct (nsc_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as [_ Hss].
        eexists _, _. exact Hss.
    + intros evs Herr.
      destruct (nsc_complete _ _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv (proj1 Hsf) Herr)
        as [(rsp & mo' & HX & _)|(code & mo' & HX & _ & _)]; discriminate HX.
    + intros evs c' Hss.
      destruct (nsc_complete _ _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv (proj1 Hsf) Hss)
        as [(rsp & mo' & HX & Hst)|(code & mo' & HX & Hex & _)].
      * injection HX as ->.
        destruct (tree_at_step_cfg _ _ _ _ _ _ _ _ NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst)
          as [HT' _].
        exact (IH rsp Q (nret ms1 rsp) mo' HT').
      * injection HX as ->.
        destruct (nsc_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as [Hh' _].
        destruct (EX n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as [Hin Hk0].
        apply (must_exit_in_at_cfg_halted cfg segs S (mkCfg ms1 mo') code); [exact Hh'| exact Hin| exact Hk0].
Qed.
End MustExitTreeFO.
