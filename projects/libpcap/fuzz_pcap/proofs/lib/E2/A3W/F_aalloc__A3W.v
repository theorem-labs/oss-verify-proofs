(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_aalloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Lemma poison_cells_frame_b : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, AIMG_LO <= A -> A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA HB. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells, AIMG_HI, AIMG_LO in *.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.
#[using="Type"] Lemma lt_pow2_of_log2 : forall a k, 0 <= a -> Z.log2 a < k -> a < 2 ^ k.
Proof.
  intros a k Ha Hl. destruct (Z.eq_dec a 0) as [->|]. { cbn in Hl. apply Z.pow_pos_nonneg; lia. }
  assert (K : 0 <= k) by (pose proof (Z.log2_nonneg a); lia).
  destruct (Z.lt_ge_cases a (2 ^ k)) as [L|G]; [exact L|]. exfalso.
  assert (k <= Z.log2 a). { rewrite <- (Z.log2_pow2 k) by lia. apply Z.log2_le_mono. lia. } lia.
Qed.
#[using="Type"] Lemma hdr_b1_mid_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid b1 < 256.
Proof.
  intros b1 Hb. unfold hdr_b1_mid.
  set (x := Z.lor (Z.land b1 18446744073709551612) 1).
  assert (X0 : 0 <= x) by (subst x; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]).
  assert (A0 : 0 <= Z.land x 143) by (apply Z.land_nonneg; right; lia).
  split. { apply Z.lor_nonneg. lia. }
  change 256 with (2^8). apply lt_pow2_of_log2. { apply Z.lor_nonneg; lia. }
  rewrite Z.log2_lor by lia.
  pose proof (Z.log2_land x 143 X0 ltac:(lia)) as L1.
  replace (Z.log2 143) with 7 in L1 by reflexivity. replace (Z.log2 16) with 4 by reflexivity. lia.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.


(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Lemma poison_cells_frame_b : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, AIMG_LO <= A -> A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA HB. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells, AIMG_HI, AIMG_LO in *.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.
#[using="Type"] Lemma lt_pow2_of_log2 : forall a k, 0 <= a -> Z.log2 a < k -> a < 2 ^ k.
Proof.
  intros a k Ha Hl. destruct (Z.eq_dec a 0) as [->|]. { cbn in Hl. apply Z.pow_pos_nonneg; lia. }
  assert (K : 0 <= k) by (pose proof (Z.log2_nonneg a); lia).
  destruct (Z.lt_ge_cases a (2 ^ k)) as [L|G]; [exact L|]. exfalso.
  assert (k <= Z.log2 a). { rewrite <- (Z.log2_pow2 k) by lia. apply Z.log2_le_mono. lia. } lia.
Qed.
#[using="Type"] Lemma hdr_b1_mid_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid b1 < 256.
Proof.
  intros b1 Hb. unfold hdr_b1_mid.
  set (x := Z.lor (Z.land b1 18446744073709551612) 1).
  assert (X0 : 0 <= x) by (subst x; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]).
  assert (A0 : 0 <= Z.land x 143) by (apply Z.land_nonneg; right; lia).
  split. { apply Z.lor_nonneg. lia. }
  change 256 with (2^8). apply lt_pow2_of_log2. { apply Z.lor_nonneg; lia. }
  rewrite Z.log2_lor by lia.
  pose proof (Z.log2_land x 143 X0 ltac:(lia)) as L1.
  replace (Z.log2 143) with 7 in L1 by reflexivity. replace (Z.log2 16) with 4 by reflexivity. lia.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.


(* [comment removed for export] *)
End TwB.
End F_aalloc.

(* [comment removed for export] *)
Module F_adealloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition dealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S b1 actx lo : Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaaf98) (Z_to_bv 64 hm) (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 S)
                  a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x37e7c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 18446744069414584320)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat.

Definition dealloc_spec__stmt : Prop := forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  tclr hm 24 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF asegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x338cc) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable t : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 0).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 1).
Variable S : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 38).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 39).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 40).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 42).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 43).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 44).
#[using="Type"] Lemma dealloc_spec__body : ltac:(let T := type of (fun (h : dealloc_spec__stmt) => h t hm S RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n b1 actx ctx lo uw sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (t, (hm, (S, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (b1, (actx, (ctx, (lo, (uw, sj))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> HD UW B1 B13 N AL H0 H1 TCH HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RTLS RSTK RCTX RT RH. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI in H0. tclr_int TCH. fold AIMG_HI in H0.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  do 4 step. zstep. do 5 step.                 (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  do 6 step. zstep. step.                      (* [comment removed for export] *)
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. step. step. step.              (* [comment removed for export] *)
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.
  (* [comment removed for export] *)
  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO. rewrite sx32_lit by lia.      (* [comment removed for export] *)
  zstep. rewrite (byte0_of_word 2 b1) by lia.  (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.                               (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.                           (* [comment removed for export] *)
  lstep. zstep. rewrite B13.                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. step. step. if_lit.                   (* [comment removed for export] *)
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.                                (* [comment removed for export] *)
  aload STATS 4 (t + 2800 + 32).               (* [comment removed for export] *)
  aload STATS 3 (t + 2800 + 24).               (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.   (* [comment removed for export] *)
  astore STATS 3.                              (* [comment removed for export] *)
  astore STATS 4.                              (* [comment removed for export] *)
  step. step. step. step.                      (* [comment removed for export] *)
  do 10 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed.
End Zd1.
#[using="Type"] Lemma dealloc_spec : ltac:(let t := eval cbv delta [dealloc_spec__stmt] in dealloc_spec__stmt in exact t).
Proof. exact dealloc_spec__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition dealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S b1 actx lo : Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xab398) (Z_to_bv 64 hm) (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 S)
                  a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x37ee4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 18446744069414584320)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat.

Definition dealloc_spec__stmt : Prop := forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  tclr hm 24 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF asegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33934) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable t : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 0).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 1).
Variable S : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 38).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 39).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 40).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 42).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 43).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'dealloc_spec__stmt 44).
#[using="Type"] Lemma dealloc_spec__body : ltac:(let T := type of (fun (h : dealloc_spec__stmt) => h t hm S RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n b1 actx ctx lo uw sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (t, (hm, (S, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (b1, (actx, (ctx, (lo, (uw, sj))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> HD UW B1 B13 N AL H0 H1 TCH HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RTLS RSTK RCTX RT RH. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI in H0. tclr_int TCH. fold AIMG_HI in H0.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  do 4 step. zstep. do 5 step.                 (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  do 6 step. zstep. step.                      (* [comment removed for export] *)
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. step. step. step.              (* [comment removed for export] *)
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.
  (* [comment removed for export] *)
  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO. rewrite sx32_lit by lia.      (* [comment removed for export] *)
  zstep. rewrite (byte0_of_word 2 b1) by lia.  (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.                               (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.                           (* [comment removed for export] *)
  lstep. zstep. rewrite B13.                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. step. step. if_lit.                   (* [comment removed for export] *)
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.                                (* [comment removed for export] *)
  aload STATS 4 (t + 2800 + 32).               (* [comment removed for export] *)
  aload STATS 3 (t + 2800 + 24).               (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.   (* [comment removed for export] *)
  astore STATS 3.                              (* [comment removed for export] *)
  astore STATS 4.                              (* [comment removed for export] *)
  step. step. step. step.                      (* [comment removed for export] *)
  do 10 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed.
End Zd1.
#[using="Type"] Lemma dealloc_spec : ltac:(let t := eval cbv delta [dealloc_spec__stmt] in dealloc_spec__stmt in exact t).
Proof. exact dealloc_spec__body. Qed.
End CANSEC1.
End TwB.
End F_adealloc.

(* [comment removed for export] *)
Module F_adeallocfn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_adealloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition dealloc_fn_spec__stmt : Prop := forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  tclr hm 24 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF asegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x338f4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable t : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 0).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 1).
Variable S : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 38).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 39).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 40).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 42).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 43).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 44).
#[using="Type"] Lemma dealloc_fn_spec__body : ltac:(let T := type of (fun (h : dealloc_fn_spec__stmt) => h t hm S RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n b1 actx ctx lo uw sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (t, (hm, (S, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (b1, (actx, (ctx, (lo, (uw, sj))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> -> -> -> HD UW B1 B13 N AL H0 H1 TCH HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RTLS RSTK RCTX RT RH. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI in H0. tclr_int TCH. fold AIMG_HI in H0.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  do 6 step. zstep. step.                      (* [comment removed for export] *)
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. step. step. step.              (* [comment removed for export] *)
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.
  (* [comment removed for export] *)
  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO. rewrite sx32_lit by lia.      (* [comment removed for export] *)
  zstep. rewrite (byte0_of_word 2 b1) by lia.  (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.                               (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.                           (* [comment removed for export] *)
  lstep. zstep. rewrite B13.                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. step. step. if_lit.                   (* [comment removed for export] *)
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.                                (* [comment removed for export] *)
  aload STATS 4 (t + 2800 + 32).               (* [comment removed for export] *)
  aload STATS 3 (t + 2800 + 24).               (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.   (* [comment removed for export] *)
  astore STATS 3.                              (* [comment removed for export] *)
  astore STATS 4.                              (* [comment removed for export] *)
  step. step. step. step.                      (* [comment removed for export] *)
  do 10 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed.
End Zd1.
#[using="Type"] Lemma dealloc_fn_spec : ltac:(let t := eval cbv delta [dealloc_fn_spec__stmt] in dealloc_fn_spec__stmt in exact t).
Proof. exact dealloc_fn_spec__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_adealloc.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition dealloc_fn_spec__stmt : Prop := forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  tclr hm 24 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF asegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3395c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable t : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 0).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 1).
Variable S : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 38).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 39).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 40).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 42).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 43).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'dealloc_fn_spec__stmt 44).
#[using="Type"] Lemma dealloc_fn_spec__body : ltac:(let T := type of (fun (h : dealloc_fn_spec__stmt) => h t hm S RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n b1 actx ctx lo uw sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (t, (hm, (S, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (b1, (actx, (ctx, (lo, (uw, sj))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> -> -> -> HD UW B1 B13 N AL H0 H1 TCH HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RTLS RSTK RCTX RT RH. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI in H0. tclr_int TCH. fold AIMG_HI in H0.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  do 6 step. zstep. step.                      (* [comment removed for export] *)
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. step. step. step.              (* [comment removed for export] *)
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.
  (* [comment removed for export] *)
  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO. rewrite sx32_lit by lia.      (* [comment removed for export] *)
  zstep. rewrite (byte0_of_word 2 b1) by lia.  (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.                               (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.                           (* [comment removed for export] *)
  lstep. zstep. rewrite B13.                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. step. step. if_lit.                   (* [comment removed for export] *)
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.                                (* [comment removed for export] *)
  aload STATS 4 (t + 2800 + 32).               (* [comment removed for export] *)
  aload STATS 3 (t + 2800 + 24).               (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.   (* [comment removed for export] *)
  astore STATS 3.                              (* [comment removed for export] *)
  astore STATS 4.                              (* [comment removed for export] *)
  step. step. step. step.                      (* [comment removed for export] *)
  do 10 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed.
End Zd1.
#[using="Type"] Lemma dealloc_fn_spec : ltac:(let t := eval cbv delta [dealloc_fn_spec__stmt] in dealloc_fn_spec__stmt in exact t).
Proof. exact dealloc_fn_spec__body. Qed.
End CANSEC1.
End TwB.
End F_adeallocfn.

(* [comment removed for export] *)
Module F_amalloc_icpt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma rw_cells_of_u64arr : forall m A ws,
  u64arr asegs m A ws -> rw_cells asegs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u64s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.


End CANSEC1.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma rw_cells_of_u64arr : forall m A ws,
  u64arr asegs m A ws -> rw_cells asegs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u64s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.


End CANSEC1.
(* [comment removed for export] *)
End TwB.
End F_amalloc_icpt.
