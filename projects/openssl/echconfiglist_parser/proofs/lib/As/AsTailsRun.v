(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the three tail statements of As/AsMainTop.v (usage, cannot
   open, read error: walks over the binary's own segments that never call time(), proved by
   As/AsMainTails.v for an instance with the binary's driver laws) at the run instance [KHr] of
   As/AsSRRun.v, from the same statements at the binary instance [KHp p].  The main phase over the
   run's list takes them as hypotheses at its instance and lifts each whole at its call site
   (As/AsDrvRun.v [rz_lift_rt]).  Every field of [KHr] the statements read is [KHp p]'s, by
   conversion, except the kernel relation, whose first conjunct is [KHp p]'s, and the budget
   [as_AL], which is [KHp p]'s less 4096 ([AsSRRun.al_kr]); the library [L] is abstract, so its
   cost and its trace check at the two instances are related by the section hypotheses [LCOST]
   and [LTR] (for the ECH library As/ECH_ALib.v [ECHL] they hold by [eq_refl] and [fun T => T]:
   its cost reads [as_Cm]/[as_Cf] and its trace check [as_TR]); so the main precondition
   [AsMainPre.AMpre] and the statics [AsMainLoop.mstatics] at [KHr] give those at [KHp p] field
   by field, the budget bound by arithmetic. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsIface ECH_Iface.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require AsMainPre AsMainLoop AsMainTop AS_InstDefs AsSRRun AsDrvDefs.
Import ListNotations.
Open Scope Z_scope.

Section TailsRun.
  Context {HCEIL : HeapCeil}.
  Variable p : AS_InstDefs.iparams.
  Variable tail : list Segment.
  Variables vlo vb vhi : Z.
  Variable L : alib.

  Local Notation KP := (AS_InstDefs.KHp p) (only parsing).
  Local Notation KR := (AsSRRun.KHr p tail vlo vb vhi) (only parsing).

  (* the library reads the instance only through fields [KHr] shares with [KHp p] *)
  Hypothesis LCOST : forall N, al_cost L KR N = al_cost L KP N.
  Hypothesis LTR : al_tr_ok L KR -> al_tr_ok L KP.

  (* the main precondition at the run instance is the binary instance's, but for the kernel
     relation's second and third conjuncts (the pair's invariant and the marker and window of
     the vDSO text's shadow), the budget, 4096 lower at the run instance, and the library's
     cost and trace check, which are its at the run instance *)
  Lemma ampre_khp : forall sp0 argv s0 msF mo regs mem B tid can,
    AsMainPre.AMpre KR L sp0 argv s0 msF mo regs mem B tid can ->
    AsMainPre.AMpre KP L sp0 argv s0 msF mo regs mem B tid can.
  Proof.
    intros sp0 argv s0 msF mo regs mem B tid can PRE.
    destruct PRE as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24
                     f25 f26 f27 f28 f29 f30 f31 f32].
    destruct f2 as [f2a _].
    (* am_al: [as_AL KR s0] is [as_AL KP s0 - 4096]; the cost is the same at both, the
       library's part by [LCOST] *)
    assert (f28' : AsMainPre.AMAIN_COST KP L <= as_AL KP s0).
    { pose proof (AsSRRun.al_kr p tail vlo vb vhi s0) as E.
      assert (EC : AsMainPre.AMAIN_COST KR L = AsMainPre.AMAIN_COST KP L).
      { unfold AsMainPre.AMAIN_COST, fuzz_cost. rewrite LCOST. reflexivity. }
      rewrite EC in f28. lia. }
    (* am_tr: the six call-site traces and the printf traces read [as_TR], [KHp p]'s; the
       library's own trace check by [LTR] *)
    assert (f29' : AsDrvDefs.adrv_traces KP L).
    { destruct f29 as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
      exact (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj T6 (conj T7 (LTR T8)))))))). }
    clear f28 f29.
    constructor; assumption.
  Qed.

  Lemma mst_khp : forall sp0 tid can mem0 m,
    AsMainLoop.mstatics KR L sp0 tid can mem0 m -> AsMainLoop.mstatics KP L sp0 tid can mem0 m.
  Proof.
    intros sp0 tid can mem0 m ST.
    destruct ST as [g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18].
    constructor; assumption.
  Qed.

  Theorem atail_usage_run : AsMainTop.atail_usage_stmt KP L -> AsMainTop.atail_usage_stmt KR L.
  Proof.
    intros T sp0 argv s0 msF0 mo0 regs0 mem0 B tid can s msF mo regs mem Hva PRE Hargc HV HA R2 R4 R8 R10 R11 ST
           Hfds Hrds.
    destruct HA as [HA1 _].
    exact (T sp0 argv s0 msF0 mo0 regs0 mem0 B tid can s msF mo regs mem Hva
             (ampre_khp sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE) Hargc HV HA1 R2 R4 R8 R10 R11
             (mst_khp sp0 tid can mem0 mem ST) Hfds Hrds).
  Qed.

  Theorem atail_open_run : AsMainTop.atail_open_stmt KP L -> AsMainTop.atail_open_stmt KR L.
  Proof.
    intros T sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s msF mo regs mem Hva PRE Hargv Hpw Hstr HV HA
           R2 R4 R18 ST Hfd2 Hrd2.
    destruct HA as [HA1 _].
    exact (T sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s msF mo regs mem Hva
             (ampre_khp sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE) Hargv Hpw Hstr HV HA1 R2 R4 R18
             (mst_khp sp0 tid can mem0 mem ST) Hfd2 Hrd2).
  Qed.

  Theorem atail_rderr_run : AsMainTop.atail_rderr_stmt KP L -> AsMainTop.atail_rderr_stmt KR L.
  Proof.
    intros T sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s msF mo regs mem Hva PRE Hargv Hpw Hstr HV HA
           R2 R4 R18 ST Hfd2 Hrd2.
    destruct HA as [HA1 _].
    exact (T sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s msF mo regs mem Hva
             (ampre_khp sp0 argv s0 msF0 mo0 regs0 mem0 B tid can PRE) Hargv Hpw Hstr HV HA1 R2 R4 R18
             (mst_khp sp0 tid can mem0 mem ST) Hfd2 Hrd2).
  Qed.
End TailsRun.
