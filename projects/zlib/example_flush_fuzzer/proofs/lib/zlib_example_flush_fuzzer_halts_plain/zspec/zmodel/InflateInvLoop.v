(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit
  InflateInvArms1 InflateInvArms2 InflateInvArms3 InflateInvArms4 InflateInvArms5 InflateInvArms6 InflateInvArms7
  InflateInvFastA InflateInvFastB InflateInvFastC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma mrank_range : forall m, 0 <= mrank m <= 7.
Proof. intros m. unfold mrank. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.
Lemma PHI_nonneg : forall NI NO WN TOT0 w, pinv NI NO WN TOT0 w -> 0 <= PHI w.
Proof.
  intros NI NO WN TOT0 [s c r] (_ & LR & _). apply LRNGq_R in LR. unfold RINV in LR. unfold PHI. cbn [w_r w_s].
  pose proof (mrank_range (is_mode s)). lia.
Qed.
Lemma PHI_fuel : forall NI NO WN TOT0 w, pinv NI NO WN TOT0 w -> PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64).
Proof.
  intros NI NO WN TOT0 [s c r] (_ & LR & _ & _ & _ & KI). apply LRNGq_R in LR. unfold RINV in LR. unfold cinv in KI. cbn [w_s w_c w_r] in KI.
  destruct KI as (_ & _ & _ & _ & Hv & Hl). unfold PHI. cbn [w_r w_s w_c]. pose proof (mrank_range (is_mode s)). lia.
Qed.

Section Loop.
  Variables (iv : ivariant) (flush : Z) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Local Notation apost := (apost NI NO WN TOT0).

  Let FAST := fast_ok iv NI NO WN TOT0 NO32.

  Ltac arm P :=
    first [ (eapply P; try eassumption; try (left; eassumption); try (right; eassumption))
          | (split; [reflexivity|]; eapply P; try eassumption; try (left; eassumption)) ].

  Theorem dispatch_ok : forall w, pinv w -> gok iv flush w = true /\ apost w (dispatch iv flush w).
  Proof.
    intros w PI.
    pose proof FAST as F.
    unfold gok, dispatch, gsel. unfold abind, gs. set (m := is_mode (w_s w)) in *.
    assert (Em : is_mode (w_s w) = m) by reflexivity. clearbody m.
    destruct (Z.eqb_spec m HEAD) as [E|NE1]; [subst m; arm P_HEAD|].
    destruct (Z.eqb_spec m FLAGS) as [E|NE2]; [subst m; arm P_FLAGS|].
    destruct (Z.eqb_spec m TIME) as [E|NE3]; [subst m; arm P_TIME|].
    destruct (Z.eqb_spec m OS) as [E|NE4]; [subst m; arm P_OS|].
    destruct (Z.eqb_spec m EXLEN) as [E|NE5]; [subst m; arm P_EXLEN|].
    destruct (Z.eqb_spec m EXTRA) as [E|NE6]; [subst m; arm P_EXTRA|].
    destruct (Z.eqb_spec m NAME) as [E|NE7]; [subst m; arm P_NAME|].
    destruct (Z.eqb_spec m COMMENT) as [E|NE8]; [subst m; arm P_COMMENT|].
    destruct (Z.eqb_spec m HCRC) as [E|NE9]; [subst m; arm P_HCRC|].
    destruct (Z.eqb_spec m DICTID) as [E|NE10]; [subst m; arm P_DICTID|].
    destruct (Z.eqb_spec m DICT) as [E|NE11]; [subst m; arm P_DICT|].
    destruct (Z.eqb_spec m TYPE) as [E|NE12]; [subst m; arm P_TYPE|].
    destruct (Z.eqb_spec m TYPEDO) as [E|NE13]; [subst m; arm P_TYPEDO|].
    destruct (Z.eqb_spec m STORED) as [E|NE14]; [subst m; arm P_STORED|].
    destruct (Z.eqb_spec m COPY_) as [E|NE15]; [subst m; arm P_COPY_|].
    destruct (Z.eqb_spec m COPY) as [E|NE16]; [subst m; arm P_COPY|].
    destruct (Z.eqb_spec m TABLE) as [E|NE17]; [subst m; arm P_TABLE|].
    destruct (Z.eqb_spec m LENLENS) as [E|NE18]; [subst m; arm P_LENLENS|].
    destruct (Z.eqb_spec m CODELENS) as [E|NE19]; [subst m; arm P_CODELENS|].
    destruct (Z.eqb_spec m LEN_) as [E|NE20]; [subst m; arm P_LEN_|].
    destruct (Z.eqb_spec m LEN) as [E|NE21]; [subst m; arm P_LEN|].
    destruct (Z.eqb_spec m LENEXT) as [E|NE22]; [subst m; arm P_LENEXT|].
    destruct (Z.eqb_spec m DIST) as [E|NE23]; [subst m; arm P_DIST|].
    destruct (Z.eqb_spec m DISTEXT) as [E|NE24]; [subst m; arm P_DISTEXT|].
    destruct (Z.eqb_spec m MATCH) as [E|NE25]; [subst m; arm P_MATCH|].
    destruct (Z.eqb_spec m LIT) as [E|NE26]; [subst m; arm P_LIT|].
    destruct (Z.eqb_spec m CHECK) as [E|NE27]; [subst m; arm P_CHECK|].
    destruct (Z.eqb_spec m LENGTH) as [E|NE28]; [subst m; arm P_LENGTH|].
    destruct (Z.eqb_spec m DONE) as [E|NE29]; [subst m; arm P_DONE|].
    destruct (Z.eqb_spec m BAD) as [E|NE30]; [subst m; arm P_BAD|].
    destruct (Z.eqb_spec m MEM) as [E|NE31]; [subst m; arm P_MEM|].
    assert (HM : HEAD <= m <= SYNC).
    { subst m. destruct w as [s c r]. destruct PI as (_ & LR & _). apply LRNGq_S in LR. destruct LR as (M & _). exact M. }
    pose proof mode_consts as (Khead & Kflags & Ktime & Kos & Kexlen & Kextra & Kname & Kcomment & Khcrc & Kdictid & Kdict & Ktype & Ktypedo & Kstored & Kcopy_ & Kcopy & Ktable & Klenlens & Kcodelens & Klen_ & Klen & Klenext & Kdist & Kdistext & Kmatch & Klit & Kcheck & Klength & Kdone & Kbad & Kmem & Ksync).
    assert (G0 : HEAD <= m) by (clear - HM; lia).
    assert (G1 : FLAGS <= m) by (clear - G0 NE1 Khead Kflags; lia).
    assert (G2 : TIME <= m) by (clear - G1 NE2 Kflags Ktime; lia).
    assert (G3 : OS <= m) by (clear - G2 NE3 Ktime Kos; lia).
    assert (G4 : EXLEN <= m) by (clear - G3 NE4 Kos Kexlen; lia).
    assert (G5 : EXTRA <= m) by (clear - G4 NE5 Kexlen Kextra; lia).
    assert (G6 : NAME <= m) by (clear - G5 NE6 Kextra Kname; lia).
    assert (G7 : COMMENT <= m) by (clear - G6 NE7 Kname Kcomment; lia).
    assert (G8 : HCRC <= m) by (clear - G7 NE8 Kcomment Khcrc; lia).
    assert (G9 : DICTID <= m) by (clear - G8 NE9 Khcrc Kdictid; lia).
    assert (G10 : DICT <= m) by (clear - G9 NE10 Kdictid Kdict; lia).
    assert (G11 : TYPE <= m) by (clear - G10 NE11 Kdict Ktype; lia).
    assert (G12 : TYPEDO <= m) by (clear - G11 NE12 Ktype Ktypedo; lia).
    assert (G13 : STORED <= m) by (clear - G12 NE13 Ktypedo Kstored; lia).
    assert (G14 : COPY_ <= m) by (clear - G13 NE14 Kstored Kcopy_; lia).
    assert (G15 : COPY <= m) by (clear - G14 NE15 Kcopy_ Kcopy; lia).
    assert (G16 : TABLE <= m) by (clear - G15 NE16 Kcopy Ktable; lia).
    assert (G17 : LENLENS <= m) by (clear - G16 NE17 Ktable Klenlens; lia).
    assert (G18 : CODELENS <= m) by (clear - G17 NE18 Klenlens Kcodelens; lia).
    assert (G19 : LEN_ <= m) by (clear - G18 NE19 Kcodelens Klen_; lia).
    assert (G20 : LEN <= m) by (clear - G19 NE20 Klen_ Klen; lia).
    assert (G21 : LENEXT <= m) by (clear - G20 NE21 Klen Klenext; lia).
    assert (G22 : DIST <= m) by (clear - G21 NE22 Klenext Kdist; lia).
    assert (G23 : DISTEXT <= m) by (clear - G22 NE23 Kdist Kdistext; lia).
    assert (G24 : MATCH <= m) by (clear - G23 NE24 Kdistext Kmatch; lia).
    assert (G25 : LIT <= m) by (clear - G24 NE25 Kmatch Klit; lia).
    assert (G26 : CHECK <= m) by (clear - G25 NE26 Klit Kcheck; lia).
    assert (G27 : LENGTH <= m) by (clear - G26 NE27 Kcheck Klength; lia).
    assert (G28 : DONE <= m) by (clear - G27 NE28 Klength Kdone; lia).
    assert (G29 : BAD <= m) by (clear - G28 NE29 Kdone Kbad; lia).
    assert (G30 : MEM <= m) by (clear - G29 NE30 Kbad Kmem; lia).
    assert (G31 : SYNC <= m) by (clear - G30 NE31 Kmem Ksync; lia).
    assert (E : m = SYNC) by (clear - G31 HM; lia). subst m. arm P_SYNC.
  Qed.



  Theorem inf_loop_exit : forall w, pinv w ->
    let r := inf_loop iv flush w in let w' := snd r in
    LRNGq NI NO WN TOT0 w' /\ sinv (w_s w') /\ binv w' /\ cks (w_s w')
    /\ (forall rc, fst r = SRet rc -> is_hold (w_s w') = ir_hold (w_r w') /\ is_bits (w_s w') = ir_bits (w_r w')).
  Proof.
    intros w PI. cbv zeta. rewrite (inf_loop_iter iv flush). generalize (Z.to_nat (gfuel w)) as n. intros n. revert PI. revert w.
    induction n as [|n IH]; intros w PI.
    - cbn. destruct PI as (_ & LR & SI & _ & BI & KI). split; [exact LR|]. split; [exact SI |]. split; [exact BI|]. split; [exact (proj1 KI)|].
      intros rc X; discriminate X.
    - rewrite iterK_gstep_S. destruct (dispatch_ok w PI) as [_ A].
      destruct (dispatch iv flush w) as [u w'|w'|rc w']; cbn [apost] in A.
      + apply IH. exact (proj1 A).
      + cbn [fst snd]. destruct A as (A0 & A1 & A2 & A4). split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split; [exact A4|].
        intros rc X; discriminate X.
      + cbn [fst snd]. destruct A as (A0 & A1 & A2 & A3 & A4). split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split; [exact A4|].
        intros _ _; exact A3.
  Qed.

  Section RunOk.
    Variable ok : Z -> iw -> bool.
    Hypothesis OK : forall w, pinv w -> ok flush w = true.

    Fixpoint run_okM (n : nat) (w : iw) : bool :=
      match n with
      | O => false
      | S n' => ok flush w && match dispatch iv flush w with
                              | ARun _ w' => run_okM n' w'
                              | _ => true
                              end
      end.


  End RunOk.
End Loop.
