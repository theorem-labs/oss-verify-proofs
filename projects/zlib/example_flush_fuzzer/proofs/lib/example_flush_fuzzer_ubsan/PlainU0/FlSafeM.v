(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface FL4Inst FlLibStmtU FlLibIfaceU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import FlLinks FlLinksM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import DeflInst6u TFlush_MU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Deflate InflateState Inflate InflateSync InflateInv InflateInvCall
  HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessSmallInfl Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec Require Import FlushStages FlushBound FlushLinks FlushSafeL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section M.
  Context {fx : PropExec.FPState}.
  Variable FL : @fl_lib fx.
  Variable d : list Z.
  Hypothesis Hn : 4 <= zlength d <= 2 ^ 20.
  Hypothesis Hb : Forall (fun b => 0 <= b < 256) d.
  Hypothesis Hds0 : fl_ds0 FL = ds0.
  Hypothesis His0 : fl_is0 FL = is0 KI.
  Hypothesis Hdsafe : fl_dsafe FL = FL_DSAFE.
  Hypothesis Hisafe : fl_isafe FL = FL_ISAFE.

  Lemma safe_d1 : fl_dsafe FL (DSV1 FL d) 3.
  Proof.
    rewrite Hdsafe. destruct (safe_terms FL d Hn Hb Hds0 His0) as (-> & _).
    split; [exact (dfl1_safeU d Hn Hb) | split; [lia | exact (flush1_dpost d Hn Hb)]].
  Qed.
  Lemma safe_d2 : fl_dsafe FL (DSV2 FL d) 4.
  Proof.
    rewrite Hdsafe. destruct (safe_terms FL d Hn Hb Hds0 His0) as (_ & -> & _).
    split; [exact (dfl2_safeU d Hn Hb) | split; [lia | exact (flush2_dpost d Hn Hb)]].
  Qed.

  Lemma safe_isf1 : fl_isafe FL (fl_is0 FL) (IZC1 FL4 d) 0.
  Proof.
    rewrite Hisafe, His0. destruct (safe_terms FL d Hn Hb Hds0 His0) as (_ & _ & -> & _).
    destruct (zc1_ok d Hn Hb) as (ZC & _ & _).
    split; [apply UI_is0|]. split; [exact ZC|]. split; [| split; [| lia]].
    - unfold LXS4, live_mode. destruct is0_facts as (M & W & _ & _ & WB & _ & _). rewrite M, W, WB.
      assert (F : is_flags (is0 KI) = -1) by (vm_compute; reflexivity). assert (HD : is_havedict (is0 KI) = 0) by (vm_compute; reflexivity).
      rewrite F, HD. unfold HEAD, BAD, FLAGS, HCRC, SYNC.
      split; [left; reflexivity|]. split; [reflexivity|]. split; [split; lia|]. split; [right; split; [reflexivity | left; reflexivity] |].
      split; [reflexivity|]. unfold bk_ok, LENEXT, DIST. split; intros E; exfalso; lia.
    - change (zs_msg (zc_strm (L_IZC1 d))) with MSG_NULL. unfold MSG_NULL. lia.
  Qed.

  Lemma safe_ssf :
    let s := IS1 FL FL4 8%N d in let zc := IZC2 FL FL4 8%N d in
    0 <= is_bits s < 40 /\ 0 <= is_hold s < 2 ^ 64 /\ 0 <= is_have s < 2 ^ 31 /\
    - 2 ^ 31 <= is_flags s < 2 ^ 31 /\ 0 <= is_wrap s < 2 ^ 31 /\ 0 <= is_mode s < 2 ^ 31 /\
    Forall (fun b => 0 <= b < 256) (zc_input zc) /\ zlength (zc_input zc) < 2 ^ 31.
  Proof.
    cbv zeta. destruct (safe_terms FL d Hn Hb Hds0 His0) as (_ & _ & _ & -> & -> & _).
    exact (ssf_facts d Hn Hb).
  Qed.

  (* 1.4: the state inflateSync sees has read its zlib header (flags 0), keeps wrap 5 and wbits 15;
     Sync6.SYNC14 asks exactly this, so the 1.3.1 model's sync agrees with 1.4's code *)
  Lemma safe_sy14 : ZI.zr_rc (IR1 FL FL4 8%N d) = Z_OK ->
    is_flags (IS1 FL FL4 8%N d) <> -1 /\ is_wrap (IS1 FL FL4 8%N d) = 5 /\ is_wbits (IS1 FL FL4 8%N d) = 15.
  Proof.
    rewrite (IR1_eqM FL d His0). destruct (safe_terms FL d Hn Hb Hds0 His0) as (_ & _ & _ & -> & _). intros R1.
    destruct (is1_shape d Hn Hb) as (_ & _ & _ & W & WB & _ & K). destruct (K R1) as (F & _).
    rewrite F, W, WB. split; [discriminate | split; reflexivity].
  Qed.

  Lemma safe_isf3 : ZI.zr_rc (IR1 FL FL4 8%N d) = Z_OK -> ZI.zr_rc (IR2 FL FL4 8%N d) = Z_OK ->
    fl_isafe FL (IS2 FL FL4 8%N d) (IZC3 FL FL4 8%N d) 4.
  Proof.
    rewrite Hisafe, (IR1_eqM FL d His0), (IR2_eqM FL d His0).
    destruct (safe_terms FL d Hn Hb Hds0 His0) as (_ & _ & _ & _ & _ & -> & ->). intros R1 R2.
    destruct (isf3_facts d Hn Hb R1 R2) as (U & ZC & M & F & W & WB & HD & MSG).
    split; [exact U|]. split; [exact ZC|]. split; [| split; [rewrite MSG; unfold MSG_NULL; lia | lia]].
    unfold LXS4, live_mode. rewrite M, F, W, WB, HD. unfold TYPE, FLAGS, HCRC, SYNC.
    split; [right; reflexivity|]. split; [reflexivity|]. split; [split; lia|]. split; [left; reflexivity |].
    split; [reflexivity|]. unfold bk_ok, LENEXT, DIST. split; intros E; exfalso; lia.
  Qed.
End M.
