(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec AgentLib AsanAcct BackingAlgebra AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK HandoffBridgeK HandoffLedgerK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition AM_DUMMY : amap := {| am_base := ELit 0; am_len := ELit 0; am_kind := KRW |}.
Definition role (cs : acs) (i : nat) : amap := nth i (rev (a_maps cs)) AM_DUMMY.
Definition rbase (E : env) (cs : acs) (i : nat) : Z := uE E (am_base (role cs i)).
Definition rlen (E : env) (cs : acs) (i : nat) : Z := uE E (am_len (role cs i)).

Lemma role_in : forall cs i, (i < length (a_maps cs))%nat -> In (role cs i) (a_maps cs).
Proof. intros cs i Hi. unfold role. apply in_rev. apply nth_In. rewrite length_rev. exact Hi. Qed.

Lemma seps_rev_nth_apart : forall l, seps l -> (forall q, In q l -> 0 < bv_unsigned (snd q)) ->
  forall d i j, (i < length l)%nat -> (j < length l)%nat -> i <> j ->
    iv_disjoint (nth i (rev l) d) (nth j (rev l) d).
Proof.
  intros l Hs Hpos d i j Hi Hj Hne.
  pose proof (hl_seps_nodup l Hs Hpos) as ND. apply NoDup_rev in ND.
  assert (Hq : nth i (rev l) d <> nth j (rev l) d).
  { intros Heq. apply Hne. apply (proj1 (NoDup_nth (rev l) d) ND i j); rewrite ?length_rev; assumption. }
  pose proof (hl_seps_apart l Hs (nth i (rev l) d) (nth j (rev l) d)) as Hap.
  unfold iv_disjoint. unfold BackingAlgebra.B, BackingAlgebra.S in Hap.
  apply Hap; [apply in_rev; apply nth_In; rewrite length_rev; assumption | apply in_rev; apply nth_In; rewrite length_rev; assumption | exact Hq].
Qed.

Section Roles.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

Lemma role_den : forall E cs R FULL model i, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  nth i (rev (vm_maps (m_vmmaps model))) (amap_den E AM_DUMMY) = amap_den E (role cs i).
Proof.
  intros E cs R FULL model i HC Hnf. rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf).
  rewrite <- map_rev. unfold role. apply map_nth.
Qed.

Lemma role_geo : forall E cs R FULL model i, CSOK E cs R FULL model -> no_fog (a_maps cs) = true -> (i < length (a_maps cs))%nat ->
  0 < rlen E cs i /\ rbase E cs i mod 4096 = 0 /\ rlen E cs i mod 4096 = 0
  /\ (rbase E cs i + rlen E cs i <= img_lo A \/ img_hi A <= rbase E cs i)
  /\ rbase E cs i + rlen E cs i <= uE E e_sp0 - 8388608
  /\ 0 <= rbase E cs i /\ rbase E cs i + rlen E cs i <= 2 ^ 64.
Proof.
  intros E cs R FULL model i HC Hnf Hi.
  assert (Hin : In (amap_den E (role cs i)) (vm_maps (m_vmmaps model))).
  { rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply in_map. apply role_in. exact Hi. }
  pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as (P1 & P2 & P3 & P4 & P5).
  pose proof (utop_bounds E) as UT.
  destruct (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W & _). pose proof (W _ Hin) as Wq.
  unfold BackingAlgebra.iv_wf, BackingAlgebra.B, BackingAlgebra.S in Wq.
  unfold amap_den in *. cbn [fst snd] in *. unfold rbase, rlen, uE in *.
  pose proof (u64_range (edenot E (am_base (role cs i)))). repeat split; try assumption; lia.
Qed.

Lemma role_apart : forall E cs R FULL model i j, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  (i < length (a_maps cs))%nat -> (j < length (a_maps cs))%nat -> i <> j ->
  rbase E cs i + rlen E cs i <= rbase E cs j \/ rbase E cs j + rlen E cs j <= rbase E cs i.
Proof.
  intros E cs R FULL model i j HC Hnf Hi Hj Hne.
  assert (Hlen : length (vm_maps (m_vmmaps model)) = length (a_maps cs)).
  { rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply length_map. }
  pose proof (seps_rev_nth_apart _ (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)
                (fun q Hq => proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq))
                (amap_den E AM_DUMMY) i j ltac:(rewrite Hlen; exact Hi) ltac:(rewrite Hlen; exact Hj) Hne) as D.
  rewrite !(role_den E cs R FULL model _ HC Hnf) in D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
  unfold rbase, rlen, uE. exact D.
Qed.
End Roles.

Lemma role_lit : forall E cs i L, am_len (role cs i) = ELit L -> 0 <= L < 2 ^ 64 -> rlen E cs i = L.
Proof. intros E cs i L H HL. unfold rlen, uE. rewrite H. cbn [edenot]. apply u64_lit. exact HL. Qed.
