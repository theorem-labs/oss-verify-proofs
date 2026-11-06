(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase ADepot_iface ADepot.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ext (L : alayout) (u : list Z) : alayout := mkALayout (al_V L) (al_w L) (u :: al_U L).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition dwfw (U : list (list Z)) (D : dstate) (w : Z) : Prop :=
  dwf U D /\ 0 <= w <= DWMAX
  /\ dtf D + BUD U (dhs D) (Z.to_nat (dN D)) + 256 * (DWMAX - w) < 1048576
  /\ dN D + CNT U (dhs D) (Z.to_nat (dN D)) + (DWMAX - w) < 65536.

Definition ADEPOTk (L : alayout) (k : Z) (m : amem) : Prop :=
  exists D w, dwfw (al_U L) D w /\ w <= k <= DWMAX /\ Z.of_nat (length (al_U L)) + (DWMAX - k) <= 4000
    /\ dcells L D m /\ dlayout L.

Lemma adepotk_adepoti : forall L k m, ADEPOTk L k m -> ADEPOTi L m.
Proof. intros L k m (D & w & (WF & _) & _ & _ & DC & LY). exists D. split; [exact WF|]. split; [exact DC| exact LY]. Qed.

Lemma adepotk_mono : forall L k k' m, k <= k' <= DWMAX -> ADEPOTk L k m -> ADEPOTk L k' m.
Proof. intros L k k' m Hk (D & w & WF & Hw & HL & DC & LY). exists D, w. split; [exact WF|]. split; [lia|]. split; [lia|]. split; [exact DC| exact LY]. Qed.

(* [comment removed for export] *)
Lemma dcells_frame : forall U L D m m' (W : list (Z * Z)),
    dwf U D -> dlayout L -> dcells L D m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
                         ~ (ADEPOT_LO <= a < ADEPOT_HI) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                         /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    dcells L D m'.
Proof.
  intros U L D m m' W WF LY DC MU WM FA.
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & _). unfold AIMG_HI in *.
  pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
  pose proof (CNT_nonneg U (dhs D) (Z.to_nat (dN D))) as CN.
  assert (OUT : forall x, (0x1ed548 <= x < 0x63d590 \/ al_nodes L <= x < al_nodes L + 1048576 \/ al_store L <= x < al_store L + 8388608) ->
                         m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point W m m' x MU); [lia|].
    clear - FA Hx. induction FA as [| [lo hi] W Hiv FA IH]; cbn; [exact I|]. split; [| exact IH].
    intros Hin. destruct (Hiv x Hin) as (A & B & C). cbn in *. lia. }
  destruct DC as (C1 & C2 & C3 & C4 & C5 & CT & CN' & SK1 & SK2).
  unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in *.
  split; [eapply rw_cells_agree; [exact C1| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split; [eapply rw_cells_agree; [exact C2| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split; [eapply rw_cells_agree; [exact C3| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split; [eapply rw_cells_agree; [exact C4| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split; [eapply rw_cells_agree; [exact C5| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split. { intros b Hb. eapply rw_cells_agree; [exact (CT b Hb)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]. }
  split. { intros i Hi. eapply rw_cells_agree; [exact (CN' i Hi)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]. }
  split. { eapply stk_agree; [exact SK1| intros x Hx; apply OUT; lia| exact WM]. }
  eapply stk_agree; [exact SK2| intros x Hx; apply OUT; lia| exact WM].
Qed.

Lemma adepotk_frame : forall L k m m' (W : list (Z * Z)),
    ADEPOTk L k m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
                         ~ (ADEPOT_LO <= a < ADEPOT_HI) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                         /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    ADEPOTk L k m'.
Proof.
  intros L k m m' W (D & w & WFW & Hw & HL & DC & LY) MU WM FA.
  exists D, w. split; [exact WFW|]. split; [exact Hw|]. split; [exact HL|]. split; [| exact LY].
  exact (dcells_frame (al_U L) L D m m' W (proj1 WFW) LY DC MU WM FA).
Qed.

(* [comment removed for export] *)
Lemma BUD_cons_le : forall u U hs n, BUD (u :: U) hs n <= ucost u + BUD U hs n.
Proof. intros. cbn [BUD]. unfold ucost. destruct (has_hash hs n (hashU u)); lia. Qed.
Lemma BUD_cons_ge : forall u U hs n, BUD U hs n <= BUD (u :: U) hs n.
Proof. intros. cbn [BUD]. unfold ucost. destruct (has_hash hs n (hashU u)); lia. Qed.
Lemma CNT_cons_le : forall u U hs n, CNT (u :: U) hs n <= 1 + CNT U hs n.
Proof. intros. cbn [CNT]. destruct (has_hash hs n (hashU u)); lia. Qed.
Lemma CNT_cons_ge : forall u U hs n, CNT U hs n <= CNT (u :: U) hs n.
Proof. intros. cbn [CNT]. destruct (has_hash hs n (hashU u)); lia. Qed.

(* [comment removed for export] *)
Lemma dwf_univ : forall U U' D, dwf U D ->
  dtf D + BUD U' (dhs D) (Z.to_nat (dN D)) < 1048576 -> dN D + CNT U' (dhs D) (Z.to_nat (dN D)) < 65536 -> dwf U' D.
Proof.
  intros U U' D (N1 & LK & HD & ND & CMP & TF0 & TFB & NB) B1 B2. unfold dwf. repeat (split; [assumption|]); assumption.
Qed.

(* [comment removed for export] *)
Lemma adepotk_ext : forall L k m u, ADEPOTk L k m -> k < DWMAX -> (length u <= 255)%nat -> ADEPOTk (ext L u) (k + 1) m.
Proof.
  intros L k m u (D & w & (WF & Hw0 & B1 & B2) & Hw & HL & DC & LY) Hk Hu.
  pose proof (BUD_cons_le u (al_U L) (dhs D) (Z.to_nat (dN D))) as BU.
  pose proof (CNT_cons_le u (al_U L) (dhs D) (Z.to_nat (dN D))) as CU.
  pose proof (BUD_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as BN.
  pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CN.
  assert (UC : ucost u <= 256) by (unfold ucost; lia).
  exists D, (w + 1). cbn [ext al_U].
  assert (B1' : dtf D + BUD (u :: al_U L) (dhs D) (Z.to_nat (dN D)) + 256 * (DWMAX - (w + 1)) < 1048576) by lia.
  assert (B2' : dN D + CNT (u :: al_U L) (dhs D) (Z.to_nat (dN D)) + (DWMAX - (w + 1)) < 65536) by lia.
  split. { split; [eapply dwf_univ; [exact WF| unfold DWMAX in *; lia| unfold DWMAX in *; lia]|]. split; [lia|]. split; assumption. }
  split; [lia|]. split; [cbn [length]; lia|]. split; [exact DC| exact LY].
Qed.

(* [comment removed for export] *)
Lemma adepotk_shrink : forall L k m u, ADEPOTk (ext L u) k m -> ADEPOTk L k m.
Proof.
  intros L k m u (D & w & (WF & Hw0 & B1 & B2) & Hw & HL & DC & LY). cbn [ext al_U length] in *.
  pose proof (BUD_cons_ge u (al_U L) (dhs D) (Z.to_nat (dN D))) as BU.
  pose proof (CNT_cons_ge u (al_U L) (dhs D) (Z.to_nat (dN D))) as CU.
  exists D, w. split.
  { split; [eapply dwf_univ; [exact WF| pose proof (BUD_nonneg (u :: al_U L) (dhs D) (Z.to_nat (dN D))); unfold DWMAX in *; lia
                              | pose proof (CNT_nonneg (u :: al_U L) (dhs D) (Z.to_nat (dN D))); unfold DWMAX in *; lia]|].
    split; [lia|]. split; lia. }
  split; [lia|]. split; [lia|]. split; [exact DC| exact LY].
Qed.

(* [comment removed for export] *)
Lemma dwfw_insert : forall U D w u h v sid,
  dwfw U D w -> In u U -> hashU u = h ->
  v = dhd D (bkt h) ->
  Forall (fun j => dhs D j <> h) (chain (dlk D) v) ->
  0 <= sid < 2^32 ->
  dwfw U (dins D (bkt h) h v sid (Z.of_nat (length u))) w.
Proof.
  intros U D w u h v sid (WF & Hw & B1 & B2) IN HU Hv FA SID.
  pose proof (dwf_insert U D u h v sid WF IN HU Hv FA SID) as WF'.
  split; [exact WF'|]. split; [exact Hw|].
  pose proof (hashU_range u) as HR. rewrite HU in HR.
  subst v. pose proof (absent_has_hash U D h WF ltac:(lia) FA) as AB.
  set (N := dN D) in *. set (D' := dins D (bkt h) (h) (dhd D (bkt h)) sid (Z.of_nat (length u))).
  assert (EN : dN D' = N + 1) by reflexivity.
  assert (EHS : forall i, 1 <= i <= Z.of_nat (Z.to_nat N) -> dhs D' i = dhs D i).
  { intros i Hi. cbn. fold N. destruct (Z.eqb_spec i (N + 1)); [lia| reflexivity]. }
  assert (EH1 : dhs D' (Z.of_nat (S (Z.to_nat N))) = h).
  { pose proof WF as (N1 & _). replace (Z.of_nat (S (Z.to_nat N))) with (N + 1) by lia. cbn. fold N. rewrite Z.eqb_refl. reflexivity. }
  pose proof (BUD_insert U (dhs D) (dhs D') (Z.to_nat N) h EHS EH1 u IN HU AB) as BI.
  pose proof (CNT_insert U (dhs D) (dhs D') (Z.to_nat N) h EHS EH1 u IN HU AB) as CI.
  pose proof WF as (N1 & _).
  rewrite EN. replace (Z.to_nat (N + 1)) with (S (Z.to_nat N)) by lia.
  change (dtf D') with (dtf D + Z.of_nat (length u) + 1). unfold ucost in BI. split; lia.
Qed.

End CANSEC1.
