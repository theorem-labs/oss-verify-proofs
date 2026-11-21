(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface FL4Inst.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel
  InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop InflateInvCall
  HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessSmallInfl InflateLeave InflateCall InflateFirst2 InflateSync InflateSyncPost.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec Require Import FlushStages FlushM FlushBound FlushLinks FlushSafe.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section L.
  Variable d : list Z.
  Hypothesis Hn : 4 <= zlength d <= 2 ^ 20.
  Hypothesis Hb : Forall (fun b => 0 <= b < 256) d.

  Lemma is0_more : is_have (is0 KI) = 0 /\ is_havedict (is0 KI) = 0.
  Proof. split; vm_compute; reflexivity. Qed.

  Lemma is1_shape :
    0 <= is_bits (L_IS1 d) <= 16 /\ 0 <= is_hold (L_IS1 d) < 2 ^ 64 /\ is_have (L_IS1 d) = 0 /\ is_wrap (L_IS1 d) = 5 /\ is_wbits (L_IS1 d) = 15
    /\ is_havedict (L_IS1 d) = 0
    /\ (zr_rc (L_IR1 d) = Z_OK -> is_flags (L_IS1 d) = 0 /\ is_bits (L_IS1 d) = 0 /\ is_hold (L_IS1 d) = 0
                               /\ (is_mode (L_IS1 d) = TYPE \/ is_mode (L_IS1 d) = DICTID)).
  Proof.
    destruct (is0_facts) as (M & W & Ho & Bi & Wb & La & Ws). destruct is0_more as [Hv Hd].
    destruct (zc1_ok d Hn Hb) as (_ & L2 & AO).
    pose proof (inflate1_shape ivar_ref WANS8 (is0 KI) (L_IZC1 d) M W Ho Bi Wb La Ws L2 ltac:(rewrite AO; lia)) as X.
    rewrite Hv, Hd in X.
    unfold L_IS1, L_IR1, L_ICALL1.
    change (inflate_p ivar_ref WANS8 (is0 KI) (L_IZC1 d) 0) with (inflate_p ivar_ref WANS8 (is0 KI) (L_IZC1 d) Z_NO_FLUSH).
    destruct (inflate_p ivar_ref WANS8 (is0 KI) (L_IZC1 d) Z_NO_FLUSH) as [[s1 r1] asked]. exact X.
  Qed.

  Theorem ssf_facts :
    0 <= is_bits (L_IS1 d) < 40 /\ 0 <= is_hold (L_IS1 d) < 2 ^ 64 /\ 0 <= is_have (L_IS1 d) < 2 ^ 31 /\
    - 2 ^ 31 <= is_flags (L_IS1 d) < 2 ^ 31 /\ 0 <= is_wrap (L_IS1 d) < 2 ^ 31 /\ 0 <= is_mode (L_IS1 d) < 2 ^ 31 /\
    Forall (fun b => 0 <= b < 256) (zc_input (L_IZC2 d)) /\ zlength (zc_input (L_IZC2 d)) < 2 ^ 31.
  Proof.
    destruct is1_shape as (B & H & HV & W & _ & _ & _).
    destruct (call1_post d Hn Hb) as [U _]. destruct U as (UR1 & _). destruct UR1 as (SR & _).
    destruct SR as (Rm & _ & Rw & _ & Rf & _).
    destruct (zc2_ok d Hn Hb) as (_ & L2 & _). pose proof (clen_range d) as CR. pose proof (cl0_range d Hn) as C0.
    destruct (c_facts d Hn Hb) as (CB & _).
    split; [lia|]. split; [exact H|]. split; [rewrite HV; lia|]. split; [exact Rf|]. split; [lia|].
    split; [unfold HEAD, SYNC in Rm; lia|].
    split.
    - unfold L_IZC2. cbn [zc_input]. apply Forall_firstn_. apply Forall_skipn_. exact CB.
    - rewrite L2. lia.
  Qed.

  Theorem isf3_facts : zr_rc (L_IR1 d) = Z_OK -> zr_rc (L_IR2 d) = Z_OK ->
    UI (L_IS2 d) /\ InflateInvCall.zcall_ok (L_IZC3 d)
    /\ is_mode (L_IS2 d) = TYPE /\ is_flags (L_IS2 d) = 0 /\ is_wrap (L_IS2 d) = 1 /\ is_wbits (L_IS2 d) = 15 /\ is_havedict (L_IS2 d) = 0
    /\ zs_msg (zc_strm (L_IZC3 d)) = MSG_NULL.
  Proof.
    intros R1 R2.
    destruct is1_shape as (_ & _ & _ & W1 & WB1 & _ & K). destruct (K R1) as (F1 & _ & _ & _).
    destruct (sync_post d Hn Hb) as [U2 _]. pose proof (zc3_ok d Hn Hb) as ZC3.
    split; [exact U2|]. split; [exact ZC3|].
    pose proof (sync_ok_shape ivar_ref (L_IS1 d) (L_IZC2 d)) as X.
    rewrite F1, W1, WB1 in X. change (0 =? -1) with false in X. change (Z.land 5 (Z.lnot 4)) with 1 in X.
    revert R2. unfold L_IZC3. cbn [zc_strm]. unfold L_IS2, L_IR2, L_ISYNC.
    destruct (inflateSync_m ivar_ref (L_IS1 d) (L_IZC2 d)) as [s2 r2]. intros R2.
    destruct (X R2) as (M2 & F2 & B2 & D2 & W2 & MSG). repeat split; assumption.
  Qed.
End L.
