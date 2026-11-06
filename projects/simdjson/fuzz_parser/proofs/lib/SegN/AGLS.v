(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module AGS.
Section S.
Variable segs : list Segment.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.
Variables (hmH : (word -> option byte) -> Prop) (hmA : Z -> Prop) (hmC : Z -> Z -> Prop) (hmR : (word -> option byte) -> Prop).
Variable hmF : ExecF.footprint.
Variable hmS : Z -> Z -> Prop.
Local Notation sokC := (SP.summ_okHSC segs GP hmH hmA hmC hmR hmF hmS).

(* [comment removed for export] *)
Lemma tm_okF_same : forall T1 T2 E M rom ms, ST.tstate T1 = ST.tstate T2 -> ST.tm_okF segs T1 E M rom ms -> ST.tm_okF segs T2 E M rom ms.
Proof. intros T1 T2 E M rom ms H (HZ & HF & HT). split; [exact HZ|]. split; [exact HF|]. unfold ST.tm_ok in *. rewrite <- H. exact HT. Qed.

(* [comment removed for export] *)
Definition ps_le (P1 P2 : option expr) : Prop := P1 = None \/ P1 = P2.
Lemma frame_ok_weak : forall E W P1 P2 M M', ps_le P1 P2 -> SP.frame_ok hmA E W P1 M M' -> SP.frame_ok hmA E W P2 M M'.
Proof.
  intros E W P1 P2 M M' [ -> | -> ] H; [|exact H].
  destruct P2 as [spe|]; cbn [SP.frame_ok] in *; [intros x Hx _; exact (H x Hx) | exact H].
Qed.
Lemma hs_ok_weak : forall E W P1 P2, ps_le P1 P2 -> SP.hs_ok hmS E P2 W -> SP.hs_ok hmS E P1 W.
Proof. intros E W P1 P2 [ -> | -> ] H; [unfold SP.hs_ok; cbn [SP.dstk]; exact I | exact H]. Qed.
Lemma crs_law_incl : forall E CR CR', incl CR CR' -> SP.crs_law hmA E CR' -> SP.crs_law hmA E CR.
Proof. intros E CR CR' Hi H w Hw. exact (H w (Hi w Hw)). Qed.
Lemma crs_law_gagree : forall G E E' CR, SP.gagree G E E' -> eb E = eb E' -> forallb (SP.win_closed G) CR = true ->
  SP.crs_law hmA E CR -> SP.crs_law hmA E' CR.
Proof.
  intros G E E' CR Hg Hb Hc H w Hw. rewrite <- (SP.win_den_gagree G E E' w Hg Hb (proj1 (forallb_forall _ _) Hc w Hw)).
  exact (H w Hw).
Qed.
Lemma wins_client_gagree : forall G E E' W, SP.gagree G E E' -> eb E = eb E' -> forallb (SP.win_closed G) W = true ->
  SP.wins_client hmC E W -> SP.wins_client hmC E' W.
Proof.
  intros G E E' W Hg Hb Hc H. unfold SP.wins_client in *. apply Forall_forall. intros w Hw.
  rewrite <- (SP.win_den_gagree G E E' w Hg Hb (proj1 (forallb_forall _ _) Hc w Hw)). exact (proj1 (Forall_forall _ _) H w Hw).
Qed.

(* [comment removed for export] *)
Theorem summ_seq : forall (S1 S2 : SP.summ) (X : ST.tmpl) (PS : option expr) (CR : list SP.win) (Ps : list ST.tmpl),
  sokC S1 -> sokC S2 ->
  ST.tstate X = ST.tstate (SP.sm_pre S2) -> ST.t_ghost X = ST.t_ghost (SP.sm_pre S2) ->
  SP.sm_G S2 = SP.sm_G S1 -> SP.sm_W S2 = SP.sm_W S1 -> SP.sm_A S2 = SP.sm_A S1 ->
  forallb (SP.win_closed (SP.sm_G S1)) (SP.sm_W S1) = true -> SX.aw_closed (SP.sm_G S1) (SP.sm_A S1) = true ->
  forallb (SP.win_closed (SP.sm_G S1)) (SP.sm_CR S2) = true -> SP.ps_closed (SP.sm_G S1) PS = true ->
  ps_le (SP.sm_PS S1) PS -> ps_le (SP.sm_PS S2) PS -> incl (SP.sm_CR S1) CR -> incl (SP.sm_CR S2) CR ->
  (forall Y, In Y (SP.sm_post S1) -> Y = X \/ In Y Ps) -> (forall Y, In Y (SP.sm_post S2) -> In Y Ps) ->
  sokC (SP.SUMY (SP.sm_G S1) (SP.sm_pre S1) Ps (SP.sm_W S1) (SP.sm_A S1) PS false CR).
Proof.
  intros S1 S2 X PS CR Ps H1 H2 HX HXg HG HW HA CW CA CR2 CPS P1 P2 I1 I2 Q1 Q2.
  intros E M rom ms HR HAg HWc HS HCR HH HT HGh.
  cbn [SP.sm_G SP.sm_pre SP.sm_post SP.sm_W SP.sm_A SP.sm_PS SP.sm_CR] in *.
  destruct (H1 E M rom ms HR HAg HWc (hs_ok_weak E _ _ _ P1 HS) (crs_law_incl E _ _ I1 HCR) HH HT HGh)
    as (ms1 & X1 & E1 & M1 & Hm1 & HX1 & HT1 & HG1 & Hg1 & Hb1 & HH1 & FR1).
  destruct (Q1 X1 HX1) as [->|HY].
  2:{ exists ms1, X1, E1, M1. split; [exact Hm1|]. split; [exact HY|]. split; [exact HT1|]. split; [exact HG1|].
      split; [exact Hg1|]. split; [exact Hb1|]. split; [exact HH1|]. exact (frame_ok_weak E _ _ _ M M1 P1 FR1). }
  assert (Hb1' : eb E = eb E1) by (symmetry; exact Hb1).
  assert (HA2 : SX.aw_genuine E1 (SP.sm_A S2)) by (rewrite HA; exact (SP.aw_genuine_gagree _ E E1 _ Hg1 Hb1' CA HAg)).
  assert (HW2 : SP.wins_client hmC E1 (SP.sm_W S2)) by (rewrite HW; exact (wins_client_gagree _ E E1 _ Hg1 Hb1' CW HWc)).
  assert (HS2 : SP.hs_ok hmS E1 (SP.sm_PS S2) (SP.sm_W S2)).
  { apply (hs_ok_weak E1 _ _ PS P2). rewrite HW. exact (SP.hs_ok_gagree hmS _ E E1 PS _ Hg1 Hb1' CPS HS). }
  assert (HCR2 : SP.crs_law hmA E1 (SP.sm_CR S2)).
  { apply (crs_law_gagree _ E E1 _ Hg1 Hb1' CR2). exact (crs_law_incl E _ _ I2 HCR). }
  destruct (H2 E1 M1 rom ms1 HR HA2 HW2 HS2 HCR2 HH1 (tm_okF_same X _ E1 M1 rom ms1 HX HT1) ltac:(rewrite <- HXg; exact HG1))
    as (ms2 & X2 & E2 & M2 & Hm2 & HX2 & HT2 & HG2 & Hg2 & Hb2 & HH2 & FR2).
  exists ms2, X2, E2, M2.
  split.
  { eapply ExecF.mstepsF_trans; [exact Hm1|]. rewrite HA in Hm2.
    exact (ExecF.mstepsF_weaken segs _ _ _ _ (SP.fpu_gagree hmF _ E E1 _ Hg1 Hb1' CA) Hm2). }
  split; [exact (Q2 X2 HX2)|]. split; [exact HT2|]. split; [exact HG2|].
  split; [rewrite HG in Hg2; exact (SP.gagree_trans _ E E1 E2 Hg1 Hg2)|].
  split; [rewrite Hb2; exact Hb1|]. split; [exact HH2|].
  rewrite HW in FR2.
  exact (SP.frame_ok_trans_g hmA _ E E1 _ PS M M1 M2 Hg1 Hb1' CW CPS (frame_ok_weak E _ _ _ M M1 P1 FR1)
           (frame_ok_weak E1 _ _ _ M1 M2 P2 FR2)).
Qed.

(* [comment removed for export] *)
Theorem summ_weak : forall (S : SP.summ) (PS : option expr) (CR : list SP.win) (Ps : list ST.tmpl),
  sokC S -> ps_le (SP.sm_PS S) PS -> incl (SP.sm_CR S) CR -> incl (SP.sm_post S) Ps ->
  sokC (SP.SUMY (SP.sm_G S) (SP.sm_pre S) Ps (SP.sm_W S) (SP.sm_A S) PS false CR).
Proof.
  intros S PS CR Ps H P1 I1 Q1 E M rom ms HR HAg HWc HS HCR HH HT HGh.
  cbn [SP.sm_G SP.sm_pre SP.sm_post SP.sm_W SP.sm_A SP.sm_PS SP.sm_CR] in *.
  destruct (H E M rom ms HR HAg HWc (hs_ok_weak E _ _ _ P1 HS) (crs_law_incl E _ _ I1 HCR) HH HT HGh)
    as (ms1 & X1 & E1 & M1 & Hm1 & HX1 & HT1 & HG1 & Hg1 & Hb1 & HH1 & FR1).
  exists ms1, X1, E1, M1. split; [exact Hm1|]. split; [exact (Q1 X1 HX1)|]. split; [exact HT1|]. split; [exact HG1|].
  split; [exact Hg1|]. split; [exact Hb1|]. split; [exact HH1|]. exact (frame_ok_weak E _ _ _ M M1 P1 FR1).
Qed.

End S.

(* [comment removed for export] *)
Theorem summ_ghostfree : forall segs (GP1 GP2 : nat -> list word -> (word -> option byte) -> Prop) hmH hmA hmC hmR hmF hmS S,
  ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  SP.summ_okHSC segs GP1 hmH hmA hmC hmR hmF hmS S -> SP.summ_okHSC segs GP2 hmH hmA hmC hmR hmF hmS S.
Proof.
  intros segs GP1 GP2 hmH hmA hmC hmR hmF hmS S H0 HX H E M rom ms HR HA HW HS HCR HH HT _.
  destruct (H E M rom ms HR HA HW HS HCR HH HT) as (ms' & X & E' & M' & H1 & H2 & H3 & _ & H5); [rewrite H0; constructor|].
  exists ms', X, E', M'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  rewrite (proj1 (Forall_forall _ _) HX X H2). constructor.
Qed.
End AGS.
