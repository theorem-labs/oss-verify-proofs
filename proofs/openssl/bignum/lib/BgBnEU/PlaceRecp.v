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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pl_place_recp (PL : placement) (an : Z) : placement :=
  pl_set_recp (pl_set (pl_set PL RRecpN (Some (PFrame an))) RRecpNr (Some (PFrame (an + 24)))) (Some (an + 48)).

Definition st_recp_init (st : ST) : ST := setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) (set_recp 0 0 st)).

Lemma pl_bn_place_recp_N : forall PL an, pl_bn (pl_place_recp PL an) RRecpN = Some (PFrame an).
Proof. reflexivity. Qed.
Lemma pl_bn_place_recp_Nr : forall PL an, pl_bn (pl_place_recp PL an) RRecpNr = Some (PFrame (an + 24)).
Proof. reflexivity. Qed.
Lemma pl_bn_place_recp_other : forall PL an r, r <> RRecpN -> r <> RRecpNr -> pl_bn (pl_place_recp PL an) r = pl_bn PL r.
Proof.
  intros PL an r N1 N2. unfold pl_place_recp. cbn [pl_bn pl_set_recp pl_set].
  replace (r =? RRecpNr)%nat with false by (symmetry; apply Nat.eqb_neq; exact N2).
  replace (r =? RRecpN)%nat with false by (symmetry; apply Nat.eqb_neq; exact N1). reflexivity.
Qed.
Lemma pl_of_place_recp_other : forall PL an r, r <> RRecpN -> r <> RRecpNr -> pl_of (pl_place_recp PL an) r = pl_of PL r.
Proof. intros PL an r N1 N2. unfold pl_place_recp. rewrite pl_of_set_recp, !pl_of_set_other by assumption. reflexivity. Qed.
Lemma pl_of_place_recp_N : forall PL an, pl_of (pl_place_recp PL an) RRecpN = Some (PFrame an).
Proof. reflexivity. Qed.
Lemma pl_of_place_recp_Nr : forall PL an, pl_of (pl_place_recp PL an) RRecpNr = Some (PFrame (an + 24)).
Proof. reflexivity. Qed.

Lemma ref_at_place_recp : forall st OW PL an r a, r <> RRecpN -> r <> RRecpNr ->
  (ref_at st OW (pl_place_recp PL an) r a <-> ref_at st OW PL r a).
Proof.
  intros st OW PL an r a N1 N2. unfold ref_at. destruct (r <? NFIX)%nat; [|reflexivity].
  rewrite pl_of_place_recp_other by assumption. reflexivity.
Qed.

Lemma ref_at_not_recp : forall st OW PL r a, pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> ref_at st OW PL r a -> r <> RRecpN /\ r <> RRecpNr.
Proof.
  intros st OW PL r a E1 E2 H. split; intros ->; unfold ref_at in H; cbn in H; destruct H as (p & Ep & _); unfold pl_of in Ep; cbn in Ep;
    [rewrite E1 in Ep| rewrite E2 in Ep]; discriminate Ep.
Qed.

Lemma recp_at_place : forall PL an, recp_at (pl_place_recp PL an) an.
Proof. intros PL an. split; [reflexivity|]. split; reflexivity. Qed.

Lemma pl_frames_place_recp_In : forall PL an iv, In iv (pl_frames (pl_place_recp PL an)) ->
  iv = (an, an + 24) \/ iv = (an + 24, an + 48) \/ iv = (an + 48, an + 60) \/ In iv (pl_frames PL).
Proof.
  intros PL an iv H. unfold pl_place_recp in H. apply pl_frames_set_recp_In in H. destruct H as [[<-|[]]|H].
  - right; right; left. unfold RECP_SC_SZ. f_equal. lia.
  - apply pl_frames_set_In in H. destruct H as [[<-|[]]|H].
    + right; left. unfold BN_STRUCT_SZ. f_equal. lia.
    + apply pl_frames_set_In in H. destruct H as [[<-|[]]|H]; [left; unfold BN_STRUCT_SZ; reflexivity| right; right; right; exact H].
Qed.

Lemma xw_place_recp : forall PL an x, rin_ivs (XW (pl_place_recp PL an)) x -> rin_ivs (XW PL) x \/ an <= x < an + 60.
Proof.
  intros PL an x H. unfold XW in *. apply rin_ivs_app in H. destruct H as [H|H]; [left; apply rin_ivs_app; left; exact H|].
  apply rin_ivs_In in H. destruct H as (iv & Hin & Hx). apply pl_frames_place_recp_In in Hin.
  destruct Hin as [->|[->|[->|Hin]]]; cbn [fst snd] in Hx; try (right; lia).
  left. apply rin_ivs_app. right. apply rin_ivs_In. exists iv. split; assumption.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma frames_ok_place_recp : forall PL an SPX BX SP',
  frames_ok PL SPX BX -> alloc_ceiling <= SP' -> SP' <= an -> an + 60 <= SPX -> SPX <= BX -> frames_ok (pl_place_recp PL an) SP' BX.
Proof.
  intros PL an SPX BX SP' (PF & CSP & BXB) C1 C2 C3 C4. split; [| split; [exact C1| exact BXB]].
  intros iv Hiv. apply pl_frames_place_recp_In in Hiv. destruct Hiv as [->|[->|[->|Hin]]]; cbn [fst snd]; try lia.
  destruct (PF iv Hin). lia.
Qed.

Lemma pl_wf_place_recp : forall PL an SPX BX,
  pl_wf PL -> frames_ok PL SPX BX -> 0 < an -> an mod 8 = 0 -> an + 60 <= SPX -> pl_wf (pl_place_recp PL an).
Proof.
  intros PL an SPX BX (W1 & W2 & W3) (PF & _) A0 A8 ASP.
  assert (OLD : forall r p iv, pl_bn PL r = Some p -> In iv (fr_ivs (Some p)) -> SPX <= fst iv).
  { intros r p iv E Hiv. destruct (W1 r p E) as (Hr & _). apply (PF iv). apply pl_frames_In. left. exists r. rewrite E. split; [exact Hr| exact Hiv]. }
  assert (CASES : forall r p, pl_bn (pl_place_recp PL an) r = Some p ->
            (r = RRecpN /\ p = PFrame an) \/ (r = RRecpNr /\ p = PFrame (an + 24)) \/ (r <> RRecpN /\ r <> RRecpNr /\ pl_bn PL r = Some p)).
  { intros r p E. destruct (Nat.eq_dec r RRecpN) as [->|N1]; [left; rewrite pl_bn_place_recp_N in E; injection E as <-; auto|].
    destruct (Nat.eq_dec r RRecpNr) as [->|N2]; [right; left; rewrite pl_bn_place_recp_Nr in E; injection E as <-; auto|].
    right; right. rewrite pl_bn_place_recp_other in E by assumption. auto. }
  assert (NEW : forall r p iv, pl_bn (pl_place_recp PL an) r = Some p -> In iv (fr_ivs (Some p)) ->
            (r = RRecpN /\ iv = (an, an + 24)) \/ (r = RRecpNr /\ iv = (an + 24, an + 48)) \/ (r <> RRecpN /\ r <> RRecpNr /\ SPX <= fst iv /\ pl_bn PL r = Some p)).
  { intros r p iv E Hiv. destruct (CASES r p E) as [[-> ->]|[[-> ->]|(N1 & N2 & E')]].
    - left. cbn [fr_ivs In] in Hiv. destruct Hiv as [<-|[]]. unfold BN_STRUCT_SZ. auto.
    - right; left. cbn [fr_ivs In] in Hiv. destruct Hiv as [<-|[]]. unfold BN_STRUCT_SZ. split; [reflexivity| f_equal; lia].
    - right; right. split; [exact N1|]. split; [exact N2|]. split; [exact (OLD r p iv E' Hiv)| exact E']. }
  split; [|split].
  - intros r p E. destruct (CASES r p E) as [[-> ->]|[[-> ->]|(N1 & N2 & E')]]; [| | exact (W1 r p E')].
    + split; [unfold RRecpN, NFIX; lia|]. split; [unfold RRecpN, ROne; lia|]. split; [reflexivity| split; [exact A0| exact A8]].
    + split; [unfold RRecpNr, NFIX; lia|]. split; [unfold RRecpNr, ROne; lia|]. split; [reflexivity| split; [lia| Z.div_mod_to_equations; lia]].
  - intros r r' p p' iv iv' NE E E' Hiv Hiv'. unfold iv_apart.
    destruct (NEW r p iv E Hiv) as [[-> ->]|[[-> ->]|(N1 & N2 & S1 & E1)]];
      destruct (NEW r' p' iv' E' Hiv') as [[-> ->]|[[-> ->]|(N1' & N2' & S1' & E1')]]; cbn [fst snd];
      first [ exfalso; apply NE; reflexivity | exact (W2 r r' p p' iv iv' NE E1 E1' Hiv Hiv') | idtac ].
    all: try lia.
    all: try (assert (X : fst iv <= snd iv) by (destruct (W1 _ _ E1) as (_ & _ & _ & K); destruct p as [| | |]; cbn [fr_ivs In] in Hiv;
                 [destruct Hiv| destruct Hiv as [<-|[]]; unfold BN_STRUCT_SZ; cbn; lia
                 | destruct Hiv as [<-|[<-|[]]]; unfold BN_STRUCT_SZ, TMOD_BUF_SZ; cbn; lia| destruct Hiv]); lia).
    all: try (assert (X : fst iv' <= snd iv') by (destruct (W1 _ _ E1') as (_ & _ & _ & K); destruct p' as [| | |]; cbn [fr_ivs In] in Hiv';
                 [destruct Hiv'| destruct Hiv' as [<-|[]]; unfold BN_STRUCT_SZ; cbn; lia
                 | destruct Hiv' as [<-|[<-|[]]]; unfold BN_STRUCT_SZ, TMOD_BUF_SZ; cbn; lia| destruct Hiv']); lia).
  - cbn [pl_recp pl_place_recp pl_set_recp]. split; [lia|]. intros r p iv E Hiv. unfold iv_apart, RECP_SC_SZ. cbn [fst snd].
    destruct (NEW r p iv E Hiv) as [[-> ->]|[[-> ->]|(N1 & N2 & S1 & E1)]]; cbn [fst snd]; lia.
Qed.

Theorem lib_state_frame_above : forall s LB SPX BX cxo hs st m m' OW PL EA W,
  RHEAP s (OW ++ LB) m -> lib_state_hc cxo hs st m OW PL EA -> munch W m m' -> wmono bgusegs m m' -> frames_ok PL SPX BX ->
  Forall (fun iv : Z * Z => GLOBALS_TOP <= fst iv /\ alloc_ceiling <= fst iv /\ forall x, fst iv <= x < snd iv -> ~ rin_ivs (pl_frames PL) x) W ->
  lib_state_hc cxo hs st m' OW PL EA.
Proof.
  intros s LB SPX BX cxo hs st m m' OW PL EA W HEAP HS MU WM FROK HW.
  pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS.
  eapply lib_state_hc_agree; [exact HS|]. eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|].
  intros a Ha. clear MU. induction HW as [|[x y] W' (G1 & G2 & G3) HW' IH]; [exact I|]. cbn [outside fst snd] in *. split; [|exact IH].
  intros Hin.
  destruct (own_fp_block OW st PL EA PARTS cxo hs a Ha) as [HL|[(q & A & n & Hq & Hr & _)|(iv & Hiv & Hx)]].
  - revert HL. unfold libw, LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold GLOBALS_TOP in G1. clear - Hin G1. lia.
  - pose proof (RH_range _ _ _ _ _ _ _ HEAP Hq) as (_ & _ & _ & BC & _). clear - BC Hr Hin G2. lia.
  - apply (G3 a Hin). apply rin_ivs_In. exists iv. split; assumption.
Qed.

Lemma pl_ids_place_recp : forall PL an, pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> pl_ids (pl_place_recp PL an) = pl_ids PL.
Proof.
  intros PL an E1 E2. unfold pl_ids. cbn [pl_ctx pl_mont pl_place_recp pl_set_recp pl_set]. f_equal.
  assert (G : forall n, pl_bn_ids (pl_place_recp PL an) n = pl_bn_ids PL n).
  { induction n as [|n IH]; cbn [pl_bn_ids]; [reflexivity|]. rewrite IH. f_equal.
    destruct (Nat.eq_dec n RRecpN) as [->|N1]; [rewrite pl_bn_place_recp_N, E1; reflexivity|].
    destruct (Nat.eq_dec n RRecpNr) as [->|N2]; [rewrite pl_bn_place_recp_Nr, E2; reflexivity|].
    rewrite pl_bn_place_recp_other by assumption. reflexivity. }
  apply G.
Qed.

Theorem lib_state_place_recp : forall cxo hs st m OW PL EA an SPX BX,
  lib_state_hc cxo hs st m OW PL EA -> frames_ok PL SPX BX ->
  pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> pl_recp PL = None ->
  0 < an -> an mod 8 = 0 -> an + 60 <= SPX ->
  rw_cells bgusegs m an (bn_cells 0 (bn_nil 0)) -> rw_cells bgusegs m (an + 24) (bn_cells 0 (bn_nil 0)) ->
  rw_cells bgusegs m (an + 48) [C4 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  lib_state_hc cxo hs (st_recp_init st) m OW (pl_place_recp PL an) EA.
Proof.
  intros cxo hs st m OW PL EA an SPX BX (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) FROK E1 E2 E3 A0 A8 ASP C1 C2 C3.
  assert (G8 : getbn RRecpN st = bn_nil 0) by (apply M2; [unfold RRecpN, NFIX; lia| exact E1]).
  assert (G9 : getbn RRecpNr st = bn_nil 0) by (apply M2; [unfold RRecpNr, NFIX; lia| exact E2]).
  assert (EST : st_recp_init st = set_recp 0 0 st).
  { unfold st_recp_init.
    replace (setbn RRecpN (bn_nil 0) (set_recp 0 0 st)) with (set_recp 0 0 st).
    - rewrite <- G9 at 1. change (getbn RRecpNr st) with (getbn RRecpNr (set_recp 0 0 st)). apply setbn_getbn_id.
    - rewrite <- G8 at 1. change (getbn RRecpN st) with (getbn RRecpN (set_recp 0 0 st)). symmetry. apply setbn_getbn_id. }
  rewrite EST.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [exact WF|]. split; [exact (pl_wf_place_recp PL an SPX BX PWF FROK A0 A8 ASP)|].
  split. { unfold ids_ok, all_ids in *. rewrite pl_ids_place_recp by assumption. exact IDS. }
  split; [|split; [|split; [|split]]].
  - intros r p Hr Ep.
    destruct (Nat.eq_dec r RRecpN) as [->|N1].
    { rewrite pl_of_place_recp_N in Ep. injection Ep as <-. split; [exact I|]. right. cbn [place_addr].
      change (getbn RRecpN (set_recp 0 0 st)) with (getbn RRecpN st). rewrite G8. exists 0. split; [exact C1|]. cbn. split; reflexivity. }
    destruct (Nat.eq_dec r RRecpNr) as [->|N2].
    { rewrite pl_of_place_recp_Nr in Ep. injection Ep as <-. split; [exact I|]. right. cbn [place_addr].
      change (getbn RRecpNr (set_recp 0 0 st)) with (getbn RRecpNr st). rewrite G9. exists 0. split; [exact C2|]. cbn. split; reflexivity. }
    rewrite pl_of_place_recp_other in Ep by assumption. destruct (M1 r p Hr Ep) as [PO HR]. split; [exact PO|].
    change (getbn r (set_recp 0 0 st)) with (getbn r st). unfold holeR in *. rewrite pl_of_place_recp_other by assumption. exact HR.
  - intros r Hr Ep.
    destruct (Nat.eq_dec r RRecpN) as [->|N1]; [rewrite pl_of_place_recp_N in Ep; discriminate Ep|].
    destruct (Nat.eq_dec r RRecpNr) as [->|N2]; [rewrite pl_of_place_recp_Nr in Ep; discriminate Ep|].
    rewrite pl_of_place_recp_other in Ep by assumption. exact (M2 r Hr Ep).
  - change (pl_ctx (pl_place_recp PL an)) with (pl_ctx PL). destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hin (Hs & Ia & HL & HCX & HIT)]. split; [exact Hin|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a b i [Hh|HR]; [left; exact Hh| right; exact HR].
  - change (pl_mont (pl_place_recp PL an)) with (pl_mont PL). destruct (pl_mont PL) as [[am qm]|]; [|exact I]. exact M4.
  - cbn [pl_recp pl_place_recp pl_set_recp]. exact C3.
Qed.

Theorem lib_state_unplace_recp : forall cxo hs hs' st m OW PL EA an x y,
  lib_state_hc cxo hs st m OW (pl_place_recp PL an) EA -> pl_wf PL ->
  pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> pl_recp PL = None ->
  getbn RRecpN st = bn_nil 0 -> getbn RRecpNr st = bn_nil 0 ->
  (forall r, In r hs -> r = RRecpN \/ r = RRecpNr \/ In r hs') ->
  lib_state_hc cxo hs' (set_recp x y st) m OW PL EA.
Proof.
  intros cxo hs hs' st m OW PL EA an x y (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) PWF0 E1 E2 E3 G8 G9 HH.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [exact WF|]. split; [exact PWF0|].
  split. { unfold ids_ok, all_ids in *. rewrite pl_ids_place_recp in IDS by assumption. exact IDS. }
  split; [|split; [|split; [|split]]].
  - intros r p Hr Ep. change (getbn r (set_recp x y st)) with (getbn r st).
    assert (N1 : r <> RRecpN).
    { intros ->. unfold pl_of in Ep. cbn in Ep. rewrite E1 in Ep. discriminate Ep. }
    assert (N2 : r <> RRecpNr).
    { intros ->. unfold pl_of in Ep. cbn in Ep. rewrite E2 in Ep. discriminate Ep. }
    rewrite <- (pl_of_place_recp_other PL an r N1 N2) in Ep. destruct (M1 r p Hr Ep) as [PO HR]. split; [exact PO|].
    unfold holeR in *. rewrite pl_of_place_recp_other in HR by assumption.
    destruct HR as [Hh|HR]; [|right; exact HR]. destruct (HH r Hh) as [E|[E|Hh']]; [contradiction| contradiction| left; exact Hh'].
  - intros r Hr Ep. change (getbn r (set_recp x y st)) with (getbn r st).
    destruct (Nat.eq_dec r RRecpN) as [->|N1]; [exact G8|].
    destruct (Nat.eq_dec r RRecpNr) as [->|N2]; [exact G9|].
    apply M2; [exact Hr|]. rewrite pl_of_place_recp_other by assumption. exact Ep.
  - change (pl_ctx (pl_place_recp PL an)) with (pl_ctx PL) in M3. destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hin (Hs & Ia & HL & HCX & HIT)]. split; [exact Hin|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a b i [Hh|HR]; [|right; exact HR].
    destruct (HH _ Hh) as [E|[E|Hh']]; [exfalso; unfold RPool, NFIX, RRecpN in E; lia| exfalso; unfold RPool, NFIX, RRecpNr in E; lia| left; exact Hh'].
  - change (pl_mont (pl_place_recp PL an)) with (pl_mont PL) in M4. destruct (pl_mont PL) as [[am qm]|]; [|exact I]. exact M4.
  - rewrite E3. exact I.
Qed.

End WithCeiling0.
