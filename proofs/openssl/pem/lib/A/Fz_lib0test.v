(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import A_Chain.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg HandoffKit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_libiface D_libiface_pem HandoffImage HandoffCells HandoffLIB RT_state RT_rep D_agree Fz_kit Fz_lib0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LIB0_TAB : list (Z * list cell) :=
  ltac:(let statics := eval cbv delta [lib0_statics] in lib0_statics in
        lazymatch statics with
        | fun _ => Forall _ ?rows => exact rows
        end).

Lemma lib0_statics_of_tab : forall m : mem, Forall (fun p => rw_cells asegs m (fst p) (snd p)) LIB0_TAB -> lib0_statics m.
Proof.
  intros mm rows_hold.
  unfold lib0_statics.
  exact rows_hold.
Qed.

Lemma lib0_statics_tab : forall m : mem, lib0_statics m -> Forall (fun p => rw_cells asegs m (fst p) (snd p)) LIB0_TAB.
Proof.
  intro mm. unfold LIB0_TAB. intro statics_hold. assumption.
Qed.

(* [comment removed for export] *)
Definition TEST_keys (ch : acs) : bool :=
  let w := hs_word ch 0xbc4e58 8 in
  (hs_rw_cells ch 0xbc5258 [C4 (Z_to_bv 64 0)] && hs_rw_cells ch 0xbc5260 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] && seg_rw_ok asegs 0xbc5268 4
   && negb (Z.eqb (bv_unsigned w) 0) && hs_rw_cells ch (0xbc4e58 + 8 * 0) [C8 w]
   && hs_rw_cells ch (0xbc4e58 + 8 * 1) [C8 (Z_to_bv 64 0)] && hs_rw_cells ch (0xbc4e58 + 8 * (1 + 1)) [C8 (Z_to_bv 64 0)]
   && hs_rw_cells ch (0xbc4e58 + 8 * (1 + 2)) [C8 (Z_to_bv 64 0)] && hs_rw_cells ch (0xbc4e58 + 8 * (1 + 3)) [C8 (Z_to_bv 64 0)]
   && hs_rw_cells ch (0xbc5298 + 8 * 1) [C8 (Z_to_bv 64 0)] && hs_rw_cells ch (0xbc5298 + 8 * (1 + 2)) [C8 (Z_to_bv 64 0)]
   && hs_rw_cells ch (0xbc5298 + 8 * (1 + 3)) [C8 (Z_to_bv 64 0)]
   && seg_rw_ok asegs (0xba3ef0 + -96) 8 && seg_rw_ok asegs (0xba3ef0 + -150) 1)%bool.

Definition TEST_A (ch : acs) : bool := (forallb (fun p => hs_rw_cells ch (fst p) (snd p)) LIB0_TAB && TEST_keys ch)%bool.

(* [comment removed for export] *)
Lemma seg_rw_c8 : forall (m : mem) a, seg_rw_ok asegs a 8 = true -> exists v, rw_cells asegs m a [C8 v].
Proof.
  intros mm base window_ok.
  destruct (seg_rw_ok_sound asegs base 8 window_ok mm) as [span_wr _].
  destruct (I_lkit.wr_at_rw_CB mm base 8 span_wr ltac:(lia)) as [raw [[raw_wf raw_at] _]].
  cbn [cells_wf cell_wf cells_bytes cbytes] in raw_wf, raw_at.
  rewrite app_nil_r in raw_at.
  destruct (cells_c8_of asegs mm base raw (proj1 raw_wf) raw_at) as [v v_at].
  exists v. split; [exact v_at | exact span_wr].
Qed.
Lemma seg_rw_c4 : forall (m : mem) a, seg_rw_ok asegs a 4 = true -> exists v, rw_cells asegs m a [C4 v].
Proof.
  intros mm base window_ok.
  destruct (seg_rw_ok_sound asegs base 4 window_ok mm) as [span_wr _].
  destruct (I_lkit.wr_at_rw_CB mm base 4 span_wr ltac:(lia)) as [raw [[raw_wf raw_at] _]].
  cbn [cells_wf cell_wf cells_bytes cbytes] in raw_wf, raw_at.
  rewrite app_nil_r in raw_at.
  destruct (cells_c4_of asegs mm base raw (proj1 raw_wf) raw_at) as [v v_at].
  exists v. split; [exact v_at | exact span_wr].
Qed.
Lemma seg_rw_c1 : forall (m : mem) a, seg_rw_ok asegs a 1 = true -> exists v, rw_cells asegs m a [C1 v].
Proof.
  intros mm base window_ok.
  apply wr_at_rw_C1.
  exact (proj1 (seg_rw_ok_sound asegs base 1 window_ok mm)).
Qed.

Theorem lib0_at_main_A : lib0_at_main TEST_A LIB0_A.
Proof.
  intros A LIMIT SINV argH ISP FS0 E ch R FULL model A' H1 H2 H3 HC HA' Hhi Hlo HT.
  pose proof (fun a cs => hi_rw_cells A LIMIT SINV argH ISP FS0 H1 H2 H3 E ch R FULL model HC A' HA' a cs) as HI.
  set (m := mH FULL model A') in *.
  unfold TEST_A in HT. apply andb_prop in HT as [HS HK].
  split.
  - apply lib0_statics_of_tab. apply Forall_forall. intros p Hp. apply HI. exact (proj1 (forallb_forall _ _) HS p Hp).
  - unfold TEST_keys in HK. cbv zeta in HK.
    repeat lazymatch type of HK with ((_ && _)%bool = true) => apply andb_prop in HK; destruct HK as [HK ?] end.
    set (w := hs_word ch 12340824 8) in *.
    lazymatch goal with K : negb _ = true |- _ => apply negb_true_iff in K; apply Z.eqb_neq in K; rename K into NZ end.
    lazymatch goal with K : seg_rw_ok asegs 12341864 4 = true |- _ => destruct (seg_rw_c4 m _ K) as [sh SH] end.
    lazymatch goal with K : seg_rw_ok asegs (12205808 + -96) 8 = true |- _ => destruct (seg_rw_c8 m _ K) as [ocb OCB] end.
    lazymatch goal with K : seg_rw_ok asegs (12205808 + -150) 1 = true |- _ => destruct (seg_rw_c1 m _ K) as [u U] end.
    exists 0, 1, w, sh, ocb, u.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply HI; exact HK|].
    split. { lazymatch goal with K : hs_rw_cells ch 12341856 _ = true |- _ => pose proof (HI _ _ K) as KL end.
             apply (proj2 (Fz_kit.rw_cells_app m 12341856 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] [C4 sh])). split; [exact KL| exact SH]. }
    split; [apply HI; assumption|].
    split; [right; split; [reflexivity| exact NZ]|].
    split; [apply HI; assumption|]. split; [apply HI; assumption|]. split; [apply HI; assumption|]. split; [apply HI; assumption|].
    split; [apply HI; assumption|]. split; [apply HI; assumption|]. split; [apply HI; assumption|].
    split; [exact OCB| exact U].
Qed.

(* [comment removed for export] *)
Lemma in_rangesI : forall (l : list (Z * Z)) lo hi x, In (lo, hi) l -> lo <= x < hi -> in_ranges l x.
Proof. intros l lo hi x H R. exists lo, hi. exact (conj H R). Qed.
Local Ltac inD lo hi := apply (in_rangesI LIB_D lo hi); [unfold LIB_D; repeat first [left; reflexivity | right] | lia].
Local Ltac inLIBD :=
  let rec try_ranges spans :=
    lazymatch spans with
    | (?lo, ?hi) :: ?later => first [inD lo hi | try_ranges later]
    end in
  let spans := eval cbv delta [LIB_D] in LIB_D in
  try_ranges spans.
Local Ltac keepD AG := eapply rw_cells_agree_nw; [eassumption| intros a Ha; cbv beta in Ha; cbn [cells_size csize Nat.add] in Ha; apply AG; inLIBD].

Theorem lib0_local_A : lib0_local_d LIB0_A.
Proof.
  intros m m' [HS HK] AG. split.
  - apply lib0_statics_tab in HS. apply lib0_statics_of_tab. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) HS p Hp) as C.
    unfold LIB0_TAB in Hp. cbn [In] in Hp.
    repeat (destruct Hp as [<-|Hp]; [cbn [fst snd] in *; keepD AG|]). all: try contradiction.
  - destruct HK as (nk & j1 & w & sh & ocb & u & NK & L1 & J1 & K1 & K2 & K3 & KJ & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
    exists nk, j1, w, sh, ocb, u. split; [exact NK|]. split; [exact L1|]. split; [exact J1|].
    assert (JJ : j1 = nk \/ j1 = nk + 1) by (destruct KJ as [[X _]|[X _]]; [left| right]; exact X).
    repeat split; try exact KJ; keepD AG.
Qed.

(* [comment removed for export] *)
Lemma test_A_2 : TEST_A (inst A_HSm 45%nat (ELit 2)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma test_A_3 : TEST_A (inst A_HSm 45%nat (ELit 3)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
