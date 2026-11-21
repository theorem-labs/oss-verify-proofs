(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the ASan+UBSan copy of As/AS_InstX.v, over this binary's
   [asegs] and [KHp]: the binary instance with one more conjunct in its kernel
   relation.  [KHX p X] is [AS_InstDefs.KHp p] whose kernel relation also holds [X] of the state and
   the configuration; every other field is [KHp p]'s.  The heap calls' theorems
   (AS_InstHeap.inst_malloc_stmt_X, AS_InstFree.inst_free_null_stmt_X and inst_free_stmt_X,
   AS_InstRealloc.inst_realloc_stmt_X, AS_InstMemalign.inst_memalign_stmt_X) prove the statements at
   [KHX p X] for every [X] that a call keeps ([XKEEP]): [X] of the caller's state and configuration,
   and an invariant [Iv] of configurations that every reach keeps ([ikeep]) holding where the call
   ends, give [X] of the new state there.  [XKEEP] may use what those proofs know of the two states:
   their model relations, their window views ([AllocRepX.awin_vis]), the placement of the caller's
   state and of its depot, and that the call changes the writable view only inside its write set
   ([awkeep], from [AG_WriteSet.acompl]).  The statements at [KHp p] are those at
   [X = fun _ _ => True] ([malloc_of_X] and the four lemmas after it). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil Scfg SReach LazyRestrict.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsIface AsIfaceX AsIfaceMemalign AsSR
     AllocRep AllocRepX AsDepotInv AG_WriteSet AG_Malloc2 AS_InstDefs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section InstX.
  Context {HCEIL : HeapCeil}.

  (** * The write set: a call changes the writable view only inside [awrit] *)

  Definition awkeep (s s' : ast) (d : depot) (lo SP : Z) (m m' : mem) : Prop :=
    forall a : word, ~ awrit s s' d lo SP (bv_unsigned a) ->
         (wview asegs m a = None -> wview asegs m' a = None)
      /\ (wview asegs m a <> None -> wview asegs m' a <> None).

  Lemma awkeep_of_compl : forall s s' d lo SP (m m' : mem),
    acompl s s' d lo SP m m' -> awkeep s s' d lo SP m m'.
  Proof.
    intros s s' d lo SP m m' AC a NW.
    pose proof (bv_unsigned_in_range _ a) as Ha. change (bv_modulus 64) with (2^64) in Ha.
    pose proof (AC (bv_unsigned a) Ha NW) as E.
    assert (Ea : wa (bv_unsigned a) = a) by (unfold wa; apply Z_to_bv_bv_unsigned).
    rewrite Ea in E.
    assert (EV : wview asegs m' a = wview asegs m a) by (unfold wview; rewrite E; reflexivity).
    rewrite EV. split; intros H; exact H.
  Qed.

  (* a call that also stores [bs] at [P], where the caller's view is writable (posix_memalign's
     result cell) *)
  Lemma awkeep_write : forall s s' d lo SP (m m1 : mem) (P : Z) (bs : list byte),
    acompl s s' d lo SP m m1 -> 0 <= P -> P + Z.of_nat (length bs) <= 2 ^ 64 ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> wview asegs m (wa (P + i)) <> None) ->
    awkeep s s' d lo SP m (write_to_mem m1 (wa P) bs).
  Proof.
    intros s s' d lo SP m m1 P bs AC P0 P1 WR a NW.
    pose proof (awkeep_of_compl s s' d lo SP m m1 AC a NW) as [K1 K2].
    pose proof (write_to_mem_spec bs m1 P a P0 P1) as E.
    assert (Ea : wa (bv_unsigned a) = a) by (unfold wa; apply Z_to_bv_bv_unsigned).
    split.
    - intros W0.
      destruct ((P <=? bv_unsigned a) && (bv_unsigned a <? P + Z.of_nat (length bs)))%bool eqn:IN.
      + exfalso. apply andb_prop in IN. destruct IN as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
        apply (WR (bv_unsigned a - P)); [lia|].
        replace (P + (bv_unsigned a - P)) with (bv_unsigned a) by lia.
        rewrite Ea. exact W0.
      + assert (EV : wview asegs (write_to_mem m1 (wa P) bs) a = wview asegs m1 a)
          by (unfold wview; rewrite E; try rewrite IN; reflexivity).
        rewrite EV. exact (K1 W0).
    - intros W0. apply wview_write_mono. exact (K2 W0).
  Qed.

  (** * What a call keeps *)

  (* an invariant of configurations that every reach over the binary's segments carries *)
  Definition ikeep (Iv : config -> Prop) : Prop :=
    forall (Q : config -> Prop) c, sreach asegs Q c -> Iv c -> sreach asegs (fun c' => Q c' /\ Iv c') c.

  Lemma sr_keep_imp : forall (Iv Q : config -> Prop) c,
    ikeep Iv -> Iv c -> sreach asegs (fun c' => Iv c' -> Q c') c -> sreach asegs Q c.
  Proof.
    intros Iv Q c K Ic S.
    apply (sreach_mono asegs (fun c' => (Iv c' -> Q c') /\ Iv c') Q c (K _ c S Ic)).
    intros c' [H1 H2]. exact (H1 H2).
  Qed.

  Lemma ikeep_true : ikeep (fun _ => True).
  Proof. intros Q c S _. apply (sreach_mono asegs Q _ c S). intros c' H. split; [exact H | exact I]. Qed.

  (* [X] of the caller's state and configuration gives [X] of the callee's new state where the
     call ends, from the facts every heap call's proof holds there *)
  Definition XKEEP (Iv : config -> Prop) (X : ist -> config -> Prop) : Prop :=
    forall (s s' : ast) (d d' : depot) (msF : machine_state) (mo : Model) (msF' : machine_state) (mo' : Model)
           (m m' : mem) (lo SP : Z),
      X (IST s d) (mkCfg msF mo) -> Iv (mkCfg msF' mo') ->
      AMODELX s mo -> awin_vis s m -> placed_ok s -> depot_placed s d ->
      ms_mem (restrict (a_L s) (a_S s) msF) = m ->
      AMODELX s' mo' -> awin_vis s' m' -> placed_ok s' ->
      ms_mem (restrict (a_L s') (a_S s') msF') = m' ->
      awkeep s s' d lo SP m m' -> aceil <= lo ->
      X (IST s' d') (mkCfg msF' mo').

  Lemma xkeep_true : XKEEP (fun _ => True) (fun _ _ => True).
  Proof. unfold XKEEP. intros. exact I. Qed.

  (** * The instance *)

  Variable p : iparams.

  Definition KHX (X : ist -> config -> Prop) : asr :=
    {| as_St := as_St (KHp p);
       as_SR := as_SR (KHp p);
       as_VIS := as_VIS (KHp p);
       as_AKREL := fun s c => as_AKREL (KHp p) s c /\ X s c;
       as_MPRES := as_MPRES (KHp p);
       as_RHEAP := as_RHEAP (KHp p);
       as_RFS := as_RFS (KHp p);
       as_rauxv_ok := as_rauxv_ok (KHp p);
       as_lb_remove := as_lb_remove (KHp p);
       as_alloc_ok := as_alloc_ok (KHp p);
       as_LIVE_MAX := as_LIVE_MAX (KHp p); as_LIVE_CNT_MAX := as_LIVE_CNT_MAX (KHp p);
       as_AL := as_AL (KHp p);
       as_Cm := as_Cm (KHp p); as_Cf := as_Cf (KHp p);
       as_chain := as_chain (KHp p);
       as_TR := as_TR (KHp p);
       as_FSB := as_FSB (KHp p) |}.

  Lemma srx_p : forall (X : ist -> config -> Prop) (Q : config -> Prop) c, as_SR (KHX X) Q c -> as_SR (KHp p) Q c.
  Proof. intros X Q c S. exact S. Qed.

  Lemma sr_mono_p : forall (Q Q' : config -> Prop) c,
    as_SR (KHp p) Q c -> (forall c', Q c' -> Q' c') -> as_SR (KHp p) Q' c.
  Proof. intros Q Q' c S K. exact (sreach_mono asegs Q Q' c S K). Qed.

  (** * The statements at [KHp p] from those at [KHX p X] with [X] always true *)

  Lemma malloc_of_X : forall X : ist -> config -> Prop, (forall x c, X x c) ->
    malloc_stmt (KHX X) -> malloc_stmt (KHp p).
  Proof.
    intros X XT M. unfold malloc_stmt, malloc_stmt_at in *.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB n lo B errv mo CH
           HV HR HK HAO HCm HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 HN.
    pose proof (M ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB n lo B errv mo CH
                  HV HR (conj HK (XT s (mkCfg msF mo))) HAO HCm HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 HN) as S0.
    apply (sr_mono_p _ _ (mkCfg msF mo) (srx_p X _ _ S0)).
    intros c HP. unfold malloc_post in HP |- *.
    destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & A & junk & q & s'
                    & E & [K _] & R).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv', A, junk, q, s'.
    exact (conj E (conj K R)).
  Qed.

  Lemma free_of_X : forall X : ist -> config -> Prop, (forall x c, X x c) ->
    free_stmt (KHX X) -> free_stmt (KHp p).
  Proof.
    intros X XT M. unfold free_stmt, free_stmt_at in *.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB q A n lo B errv mo CH bs sbs
           HV HR HK HIN HCf HRW HSH HLS HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0.
    pose proof (M ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB q A n lo B errv mo CH bs sbs
                  HV HR (conj HK (XT s (mkCfg msF mo))) HIN HCf HRW HSH HLS HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0) as S0.
    apply (sr_mono_p _ _ (mkCfg msF mo) (srx_p X _ _ S0)).
    intros c HP. unfold free_post in HP |- *.
    destruct HP as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & s' & E & [K _] & R).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', s'.
    exact (conj E (conj K R)).
  Qed.

  Lemma free_null_of_X : forall X : ist -> config -> Prop, (forall x c, X x c) ->
    free_null_stmt_at (KHX X) AFREE_STUB -> free_null_stmt_at (KHp p) AFREE_STUB.
  Proof.
    intros X XT M. unfold free_null_stmt_at in *.
    intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB lo B errv mo CH
           HV HR HK HCf HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH.
    pose proof (M ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB lo B errv mo CH
                  HV HR (conj HK (XT s (mkCfg msF mo))) HCf HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH) as S0.
    apply (sr_mono_p _ _ (mkCfg msF mo) (srx_p X _ _ S0)).
    intros c HP. unfold free_null_post in HP |- *.
    destruct HP as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & s' & E & [K _] & R).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', s'.
    exact (conj E (conj K R)).
  Qed.

  Lemma realloc_of_X : forall X : ist -> config -> Prop, (forall x c, X x c) ->
    realloc_stmt (KHX X) -> realloc_stmt (KHp p).
  Proof.
    intros X XT M. unfold realloc_stmt, realloc_stmt_at in *.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB q A old n lo B errv mo CH bs sbs
           HV HR HK HIN HAO HCm HRW HSH HLS HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 Ha1 HN HOLD.
    pose proof (M ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB q A old n lo B errv mo CH bs sbs
                  HV HR (conj HK (XT s (mkCfg msF mo))) HIN HAO HCm HRW HSH HLS HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 Ha1 HN HOLD) as S0.
    apply (sr_mono_p _ _ (mkCfg msF mo) (srx_p X _ _ S0)).
    intros c HP. unfold realloc_post in HP |- *.
    destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & A' & junk & q' & s'
                    & E & [K _] & R).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv', A', junk, q', s'.
    exact (conj E (conj K R)).
  Qed.

  Lemma memalign_of_X : forall (X : ist -> config -> Prop) (entry pc0 : Z), (forall x c, X x c) ->
    memalign_stmt (KHX X) entry pc0 -> memalign_stmt (KHp p) entry pc0.
  Proof.
    intros X entry pc0 XT M. unfold memalign_stmt in *.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc msF m s LB P al n lo B errv mo CH pjunk
           HV HR HK HAO HCm HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 HP8 HPW HCW HACW HPOFF Ha1 HAL Ha2 HN.
    pose proof (M ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc msF m s LB P al n lo B errv mo CH pjunk
                  HV HR (conj HK (XT s (mkCfg msF mo))) HAO HCm HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 HP8 HPW HCW HACW HPOFF Ha1 HAL Ha2 HN) as S0.
    apply (sr_mono_p _ _ (mkCfg msF mo) (srx_p X _ _ S0)).
    intros c HP. unfold memalign_post in HP |- *.
    destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ab & junk & q & s'
                    & E & [K _] & R).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv', Ab, junk, q, s'.
    exact (conj E (conj K R)).
  Qed.
End InstX.
