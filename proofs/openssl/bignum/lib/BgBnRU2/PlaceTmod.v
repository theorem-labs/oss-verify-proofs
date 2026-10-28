(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BgPlace.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition pl_place_tmod (PL : placement) (a d : Z) : placement := pl_set PL RTmod (Some (PFrameBuf a d)).

Lemma stored_tmod : stored_ref RTmod.
Proof. unfold stored_ref, RTmod, NFIX, ROne. split; [lia|]. split; [lia| reflexivity]. Qed.

Lemma pl_bn_place_tmod_same : forall PL a d, pl_bn (pl_place_tmod PL a d) RTmod = Some (PFrameBuf a d).
Proof. intros. apply pl_set_same. Qed.
Lemma pl_bn_place_tmod_other : forall PL a d r, r <> RTmod -> pl_bn (pl_place_tmod PL a d) r = pl_bn PL r.
Proof. intros. apply pl_set_other. assumption. Qed.
Lemma pl_of_place_tmod_same : forall PL a d, pl_of (pl_place_tmod PL a d) RTmod = Some (PFrameBuf a d).
Proof. intros. apply pl_of_set_same. exact stored_tmod. Qed.
Lemma pl_of_place_tmod_other : forall PL a d r, r <> RTmod -> pl_of (pl_place_tmod PL a d) r = pl_of PL r.
Proof. intros. apply pl_of_set_other. assumption. Qed.

Lemma ref_at_place_tmod : forall st OW PL a d r x, r <> RTmod -> ref_at st OW PL r x -> ref_at st OW (pl_place_tmod PL a d) r x.
Proof. intros st OW PL a d r x NE H. apply ref_at_pl_other; assumption. Qed.
Lemma ref_at_place_tmod_same : forall st OW PL a d, ref_at st OW (pl_place_tmod PL a d) RTmod a.
Proof.
  intros. apply ref_at_fixed; [unfold RTmod, NFIX; lia|]. exists (PFrameBuf a d). split; [apply pl_of_place_tmod_same| reflexivity].
Qed.

Lemma pl_bn_ids_place_tmod : forall PL a d n, pl_bn PL RTmod = None -> pl_bn_ids (pl_place_tmod PL a d) n = pl_bn_ids PL n.
Proof.
  intros PL a d n E. induction n as [|n IH]; [reflexivity|]. cbn [pl_bn_ids]. rewrite IH.
  destruct (Nat.eq_dec n RTmod) as [->|NE]; [rewrite pl_bn_place_tmod_same, E; reflexivity| rewrite pl_bn_place_tmod_other by exact NE; reflexivity].
Qed.
Lemma pl_ids_place_tmod : forall PL a d, pl_bn PL RTmod = None -> pl_ids (pl_place_tmod PL a d) = pl_ids PL.
Proof. intros PL a d E. unfold pl_ids. rewrite pl_bn_ids_place_tmod by exact E. reflexivity. Qed.

Lemma pl_frames_place_tmod_In : forall PL a d iv, In iv (pl_frames (pl_place_tmod PL a d)) ->
  iv = (a, a + 24) \/ iv = (d, d + 16) \/ In iv (pl_frames PL).
Proof.
  intros PL a d iv H. apply pl_frames_In in H. destruct H as [(r & Hr & Hiv)|H].
  - destruct (Nat.eq_dec r RTmod) as [->|NE].
    + rewrite pl_bn_place_tmod_same in Hiv. cbn [fr_ivs In] in Hiv. unfold BN_STRUCT_SZ, TMOD_BUF_SZ in Hiv. destruct Hiv as [<-|[<-|[]]]; auto.
    + rewrite pl_bn_place_tmod_other in Hiv by exact NE. right; right. apply pl_frames_In. left. exists r. auto.
  - right; right. apply pl_frames_In. right. exact H.
Qed.

Lemma xw_place_tmod : forall PL a d x, rin_ivs (XW (pl_place_tmod PL a d)) x -> rin_ivs (XW PL) x \/ a <= x < a + 24 \/ d <= x < d + 16.
Proof.
  intros PL a d x H. unfold XW in *. apply rin_ivs_app in H. destruct H as [H|H]; [left; apply rin_ivs_app; left; exact H|].
  apply rin_ivs_In in H. destruct H as (iv & Hin & Hx). apply pl_frames_place_tmod_In in Hin. destruct Hin as [->|[->|Hin]]; cbn [fst snd] in Hx.
  - right; left. exact Hx.
  - right; right. exact Hx.
  - left. apply rin_ivs_app. right. apply rin_ivs_In. exists iv. auto.
Qed.

Lemma frames_ok_place_tmod : forall PL a d SPX BX SP',
  frames_ok PL SPX BX -> alloc_ceiling <= SP' -> SP' <= a -> SP' <= d -> a + 24 <= SPX -> d + 16 <= SPX -> SPX <= BX -> frames_ok (pl_place_tmod PL a d) SP' BX.
Proof.
  intros PL a d SPX BX SP' (PF & CSP & BXB) C1 C2 C3 C4 C5 C6. split; [| split; [exact C1| exact BXB]].
  intros iv Hiv. apply pl_frames_place_tmod_In in Hiv. destruct Hiv as [->|[->|Hin]]; cbn [fst snd]; try lia.
  destruct (PF iv Hin). lia.
Qed.

Lemma pl_wf_place_tmod : forall PL a d SPX BX,
  pl_wf PL -> frames_ok PL SPX BX -> pl_bn PL RTmod = None -> 0 < a -> 0 < d -> a + 24 <= SPX -> d + 16 <= SPX -> (a + 24 <= d \/ d + 16 <= a) ->
  a mod 8 = 0 -> d mod 8 = 0 ->
  pl_wf (pl_place_tmod PL a d).
Proof.
  intros PL a d SPX BX (W1 & W2 & W3) (PF & _) E A0 D0 ASP DSP AP AL DL.
  assert (OLD : forall r p iv, pl_bn PL r = Some p -> In iv (fr_ivs (Some p)) -> SPX <= fst iv /\ fst iv <= snd iv).
  { intros r p iv Ep Hiv. destruct (W1 r p Ep) as (Hr & _ & _ & K). split.
    - apply (PF iv). apply pl_frames_In. left. exists r. rewrite Ep. split; [exact Hr| exact Hiv].
    - destruct p as [| | |]; cbn [fr_ivs In] in Hiv; [destruct Hiv| destruct Hiv as [<-|[]]; unfold BN_STRUCT_SZ; cbn; lia
        | destruct Hiv as [<-|[<-|[]]]; unfold BN_STRUCT_SZ, TMOD_BUF_SZ; cbn; lia| destruct Hiv]. }
  assert (NEW : forall r p iv, pl_bn (pl_place_tmod PL a d) r = Some p -> In iv (fr_ivs (Some p)) ->
            (r = RTmod /\ (iv = (a, a + 24) \/ iv = (d, d + 16))) \/ (r <> RTmod /\ pl_bn PL r = Some p /\ SPX <= fst iv /\ fst iv <= snd iv)).
  { intros r p iv Ep Hiv. destruct (Nat.eq_dec r RTmod) as [->|NE].
    - left. split; [reflexivity|]. rewrite pl_bn_place_tmod_same in Ep. injection Ep as <-. cbn [fr_ivs In] in Hiv. unfold BN_STRUCT_SZ, TMOD_BUF_SZ in Hiv.
      destruct Hiv as [<-|[<-|[]]]; auto.
    - right. rewrite pl_bn_place_tmod_other in Ep by exact NE. split; [exact NE|]. split; [exact Ep| exact (OLD r p iv Ep Hiv)]. }
  split; [|split].
  - intros r p Ep. destruct (Nat.eq_dec r RTmod) as [->|NE].
    + rewrite pl_bn_place_tmod_same in Ep. injection Ep as <-. destruct stored_tmod as (S1 & S2 & S3).
      split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact A0|]. split; [exact D0|]. unfold iv_apart, BN_STRUCT_SZ, TMOD_BUF_SZ. cbn [fst snd].
      split; [exact AP|]. split; [exact AL| exact DL].
    + rewrite pl_bn_place_tmod_other in Ep by exact NE. exact (W1 r p Ep).
  - intros r r' p p' iv iv' NE Ep Ep' Hiv Hiv'. unfold iv_apart.
    destruct (NEW r p iv Ep Hiv) as [[-> HI]|(N1 & E1 & S1 & L1)]; destruct (NEW r' p' iv' Ep' Hiv') as [[-> HI']|(N1' & E1' & S1' & L1')].
    + exfalso. apply NE. reflexivity.
    + destruct HI as [->| ->]; cbn [fst snd]; lia.
    + destruct HI' as [->| ->]; cbn [fst snd]; lia.
    + exact (W2 r r' p p' iv iv' NE E1 E1' Hiv Hiv').
  - change (pl_recp (pl_place_tmod PL a d)) with (pl_recp PL). destruct (pl_recp PL) as [c|] eqn:ERC; [|exact I].
    destruct W3 as [C0 W3]. split; [exact C0|]. intros r p iv Ep Hiv.
    destruct (NEW r p iv Ep Hiv) as [[-> HI]|(N1 & E1 & S1 & L1)]; [|exact (W3 r p iv E1 Hiv)].
    assert (CS : SPX <= c) by (apply (PF (c, c + RECP_SC_SZ)); apply pl_frames_recp; exact ERC).
    unfold iv_apart. destruct HI as [->| ->]; cbn [fst snd]; lia.
Qed.

Theorem lib_state_place_tmod : forall cxo hs st m OW PL EA a d SPX BX (tm : BN),
  lib_state_hc cxo hs st m OW PL EA -> frames_ok PL SPX BX ->
  pl_bn PL RTmod = None -> 0 < a -> 0 < d -> a + 24 <= SPX -> d + 16 <= SPX -> (a + 24 <= d \/ d + 16 <= a) -> a mod 8 = 0 -> d mod 8 = 0 ->
  bn_d tm = None -> length (bn_buf tm) = 2%nat -> bg_ok tm ->
  rw_cells bgusegs m a (bn_cells d tm) -> u64arr bgusegs m d (wlimbs (bn_buf tm)) ->
  lib_state_hc cxo hs (setbn RTmod tm st) m OW (pl_place_tmod PL a d) EA.
Proof.
  intros cxo hs st m OW PL EA a d SPX BX tm (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) FROK E A0 D0 ASP DSP AP AL DL ED EL OK CELLS ARR.
  pose proof stored_tmod as SR. pose proof SR as (RN & RO & RM).
  assert (EO : pl_of PL RTmod = None) by (rewrite pl_of_stored by exact SR; exact E).
  assert (G : getbn RTmod st = bn_nil 0) by (apply M2; [exact RN| exact EO]).
  assert (HV : vref RTmod st) by (unfold vref; destruct WF as (ELn & _); rewrite ELn; unfold RTmod, NFIX; lia).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split. { apply st_wf_setbn; [exact WF| exact RO| exact OK]. }
  split. { exact (pl_wf_place_tmod PL a d SPX BX PWF FROK E A0 D0 ASP DSP AP AL DL). }
  split.
  { unfold ids_ok, all_ids in *. rewrite pl_ids_place_tmod by exact E.
    rewrite (blocks_of_setbn_same RTmod _ st HV) by (rewrite G; unfold bn_blocks; rewrite ED; reflexivity). exact IDS. }
  split; [|split; [|split; [|split]]].
  - intros r' p Hr' Ep. destruct (Nat.eq_dec r' RTmod) as [->|NE].
    + rewrite pl_of_place_tmod_same in Ep. injection Ep as <-. split; [exact I|].
      right. cbn [place_addr]. rewrite getbn_setbn_same by exact HV. rewrite pl_of_place_tmod_same.
      exists d. split; [exact CELLS|]. unfold bn_arr. rewrite ED. split; [reflexivity|]. split; [exact ARR| exact EL].
    + rewrite pl_of_place_tmod_other in Ep by exact NE. destruct (M1 r' p Hr' Ep) as [PO HR]. split; [exact PO|].
      rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). unfold holeR in *. rewrite pl_of_place_tmod_other by exact NE. exact HR.
  - intros r' Hr' Ep. destruct (Nat.eq_dec r' RTmod) as [->|NE]; [rewrite pl_of_place_tmod_same in Ep; discriminate Ep|].
    rewrite pl_of_place_tmod_other in Ep by exact NE. rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). exact (M2 r' Hr' Ep).
  - change (pl_ctx (pl_place_tmod PL a d)) with (pl_ctx PL). rewrite st_ctx_setbn, skipn_setbn_fixed by exact RN.
    destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hinc (Hs & Ia & HL & HCX & HIT)]. split; [exact Hinc|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a0 b0 i [Hh|HR]; [left; exact Hh| right]. rewrite pl_of_pool in *. exact HR.
  - change (pl_mont (pl_place_tmod PL a d)) with (pl_mont PL). destruct (pl_mont PL) as [[am qm]|]; [|exact I]. exact M4.
  - change (pl_recp (pl_place_tmod PL a d)) with (pl_recp PL). destruct (pl_recp PL) as [c|]; [|exact I]. exact M5.
Qed.

Theorem lib_state_unplace_tmod : forall cxo hs hs' st m OW PL EA a d,
  lib_state_hc cxo hs st m OW (pl_place_tmod PL a d) EA -> pl_wf PL -> pl_bn PL RTmod = None ->
  bn_d (getbn RTmod st) = None ->
  (forall r, In r hs -> r = RTmod \/ In r hs') ->
  lib_state_hc cxo hs' (setbn RTmod (bn_nil 0) st) m OW PL EA.
Proof.
  intros cxo hs hs' st m OW PL EA a d (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) PWF0 E ED HH.
  pose proof stored_tmod as SR. pose proof SR as (RN & RO & RM).
  assert (EO : pl_of PL RTmod = None) by (rewrite pl_of_stored by exact SR; exact E).
  assert (HV : vref RTmod st) by (unfold vref; destruct WF as (ELn & _); rewrite ELn; unfold RTmod, NFIX; lia).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split. { apply st_wf_setbn; [exact WF| exact RO| apply bg_ok_nil; left; reflexivity]. }
  split; [exact PWF0|].
  split.
  { unfold ids_ok, all_ids in *. rewrite pl_ids_place_tmod in IDS by exact E.
    rewrite (blocks_of_setbn_same RTmod _ st HV) by (unfold bn_blocks; rewrite ED; reflexivity). exact IDS. }
  split; [|split; [|split; [|split]]].
  - intros r' p Hr' Ep.
    assert (NE : r' <> RTmod) by (intros ->; rewrite EO in Ep; discriminate Ep).
    rewrite <- (pl_of_place_tmod_other PL a d r' NE) in Ep. destruct (M1 r' p Hr' Ep) as [PO HR]. split; [exact PO|].
    rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). unfold holeR in *. rewrite pl_of_place_tmod_other in HR by exact NE.
    destruct HR as [Hh|HR]; [|right; exact HR]. destruct (HH r' Hh) as [E'|Hh']; [contradiction| left; exact Hh'].
  - intros r' Hr' Ep. destruct (Nat.eq_dec r' RTmod) as [->|NE]; [apply getbn_setbn_same; exact HV|].
    rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). apply M2; [exact Hr'|]. rewrite pl_of_place_tmod_other by exact NE. exact Ep.
  - change (pl_ctx (pl_place_tmod PL a d)) with (pl_ctx PL) in M3. rewrite st_ctx_setbn, skipn_setbn_fixed by exact RN.
    destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hinc (Hs & Ia & HL & HCX & HIT)]. split; [exact Hinc|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a0 b0 i [Hh|HR]; [|right; rewrite pl_of_pool in *; exact HR].
    destruct (HH _ Hh) as [E'|Hh']; [exfalso; unfold RPool, NFIX, RTmod in E'; lia| left; exact Hh'].
  - change (pl_mont (pl_place_tmod PL a d)) with (pl_mont PL) in M4. destruct (pl_mont PL) as [[am qm]|]; [|exact I]. exact M4.
  - change (pl_recp (pl_place_tmod PL a d)) with (pl_recp PL) in M5. destruct (pl_recp PL) as [c|]; [|exact I]. exact M5.
Qed.

End WithCeiling0.
