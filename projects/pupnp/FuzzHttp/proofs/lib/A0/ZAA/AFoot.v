(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim APrimLem APrimSpec APrimSpec2 APrimQ APrimPopR ASec.
Import ListNotations.
Open Scope Z_scope.

Section F.
Context {HC : HasCeiling}.
Variable AL : alayout.
Notation THR := (at_thr (al_thread AL)).
Notation PARR := (al_parr AL).

Definition sub_iv (lo hi : Z) (iv : Z * Z) : Prop := lo <= fst iv /\ snd iv <= hi.

Definition atouch (lo q : Z) (P0 : prim) (S0 : asec) (tc : list (Z * Z)) (tsc : list schunk) (iv : Z * Z) : Prop :=
  sub_iv lo q iv
  \/ sub_iv SEC (GSTATS_A + 16) iv
  \/ sub_iv (THR + CACHE_OFF) (THR + 3168) iv
  \/ (exists c, 1 <= c <= 31 /\
        (sub_iv (ri_addr AL c) (ri_addr AL c + 128) iv
         \/ sub_iv (region AL c + p_au (get_cls P0 c)) (region AL (c + 1)) iv
         \/ sub_iv (sh (region AL c + p_au (get_cls P0 c))) (sh (region AL (c + 1))) iv))
  \/ (exists cv, In cv tc /\ (chunk_iv AL (fst cv) (snd cv) iv \/ chunk_sh_iv AL (fst cv) (snd cv) iv))
  \/ (exists sc, In sc tsc /\ (sub_iv (sc_beg sc) (sc_beg sc + sc_msize sc) iv
                               \/ sub_iv (sh (sc_beg sc)) (sh (sc_beg sc) + sc_msize sc / 8) iv))
  \/ (exists sc, In sc (se_chunks S0) /\ sub_iv (sc_beg sc) (sc_beg sc + 32) iv)
  \/ sub_iv PARR (PARR + 2^23) iv.

#[using="Type"] Lemma atouch_mono : forall lo q P0 S0 tc tsc lo1 q1 P1 S1 tc1 tsc1 iv,
  lo <= lo1 -> q1 <= q ->
  (forall c, 1 <= c <= 31 -> p_au (get_cls P0 c) <= p_au (get_cls P1 c)) ->
  incl (se_chunks S1) (se_chunks S0) -> incl tc1 tc -> incl tsc1 tsc ->
  atouch lo1 q1 P1 S1 tc1 tsc1 iv -> atouch lo q P0 S0 tc tsc iv.
Proof.
  intros lo q P0 S0 tc tsc lo1 q1 P1 S1 tc1 tsc1 iv HL HQ HP HS HT HTS A. unfold atouch, sub_iv in *.
  destruct A as [A|[A|[A|[A|[A|[A|[A|A]]]]]]].
  - left. lia.
  - right; left. exact A.
  - right; right; left. exact A.
  - right; right; right; left. destruct A as (c & Hc & A). exists c. split; [exact Hc|]. specialize (HP c Hc).
    destruct A as [A|[A|A]]; [left; exact A| right; left; lia| right; right].
    pose proof (sh_le (region AL c + p_au (get_cls P0 c)) (region AL c + p_au (get_cls P1 c)) ltac:(lia)). lia.
  - right; right; right; right; left. destruct A as (cv & Hin & A). exists cv. split; [apply HT; exact Hin| exact A].
  - right; right; right; right; right; left. destruct A as (sc & Hin & A). exists sc. split; [apply HTS; exact Hin| exact A].
  - right; right; right; right; right; right; left. destruct A as (sc & Hin & A). exists sc. split; [apply HS; exact Hin| exact A].
  - right; right; right; right; right; right; right. exact A.
Qed.

#[using="Type"] Lemma Forall_atouch_mono : forall lo q P0 S0 tc tsc lo1 q1 P1 S1 tc1 tsc1 W,
  lo <= lo1 -> q1 <= q ->
  (forall c, 1 <= c <= 31 -> p_au (get_cls P0 c) <= p_au (get_cls P1 c)) ->
  incl (se_chunks S1) (se_chunks S0) -> incl tc1 tc -> incl tsc1 tsc ->
  Forall (atouch lo1 q1 P1 S1 tc1 tsc1) W -> Forall (atouch lo q P0 S0 tc tsc) W.
Proof. intros. eapply Forall_impl; [| eassumption]. intros iv A. eapply atouch_mono; eassumption. Qed.

#[using="Type"] Lemma atouch_prim_W : forall lo q P0 S0 tc tsc c k k',
  1 <= c <= 31 ->
  p_au (get_cls P0 c) <= p_mu k -> p_mu k' <= FA_OFF -> 0 <= p_nf k -> 0 <= p_nf k' -> p_mfa k' <= K_FA_SIZE -> 0 <= p_mfa k ->
  p_au (get_cls P0 c) <= FA_OFF ->
  Forall (atouch lo q P0 S0 tc tsc) (prim_W AL lo q c k k').
Proof.
  intros lo q P0 S0 tc tsc c k k' Hc H1 H2 H3 H4 H5 H6 H7. unfold prim_W.
  assert (R1 : region AL (c + 1) = region AL c + K_REGION) by (unfold region; lia).
  assert (CL : forall a b, region AL c + p_au (get_cls P0 c) <= a -> b <= region AL c + K_REGION -> atouch lo q P0 S0 tc tsc (a, b)).
  { intros a b A B. right; right; right; left. exists c. split; [exact Hc|]. right; left. unfold sub_iv. cbn [fst snd]. rewrite R1. lia. }
  assert (CS : forall a b, region AL c + p_au (get_cls P0 c) <= a -> b <= region AL c + K_REGION -> atouch lo q P0 S0 tc tsc (sh a, sh b)).
  { intros a b A B. right; right; right; left. exists c. split; [exact Hc|]. right; right. unfold sub_iv. cbn [fst snd]. rewrite R1.
    pose proof (sh_le _ _ A). pose proof (sh_le _ _ B). lia. }
  repeat (apply Forall_cons || apply Forall_nil).
  - left. unfold sub_iv. cbn [fst snd]. lia.
  - right; right; right; left. exists c. split; [exact Hc|]. left. unfold sub_iv. cbn [fst snd]. lia.
  - apply CL; unfold fa_base; lia.
  - apply CL; lia.
  - apply CS; lia.
  - apply CS; unfold fa_base; lia.
  - right; right; left. unfold sub_iv. cbn [fst snd]. lia.
  - right; right; left. unfold sub_iv. cbn [fst snd]. lia.
Qed.
End F.
