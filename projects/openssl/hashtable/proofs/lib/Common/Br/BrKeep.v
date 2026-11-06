(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxHandoff.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Keep.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Variable M : itrie region.
Variable keep : list int.
Variable KF : list hfact.
Variable ms0 : machine_state.
Variable mem : word -> option byte.
Hypothesis HIM : image_ok segs IM.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Hypothesis Hfacts : Forall (hholds segs rho ms0) KF.
Hypothesis Hframe : forall t, In t keep -> forall rg x, iget t M = Some rg ->
  bv_unsigned (rho t) + to_Z (rg_lo rg) <= bv_unsigned x < bv_unsigned (rho t) + to_Z (rg_len rg) ->
  mem x = ms_mem ms0 x.

Definition keptb (t : int) : bool := existsb (fun x => (x =? t)%uint63) keep.

Lemma keptb_In t : keptb t = true -> In t keep.
Proof.
  unfold keptb. intros H. apply existsb_exists in H as (x & Hx & E). apply Uint63.eqb_spec in E. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
Fixpoint sv_find (fs : list hfact) (t a : int) : option (fval * int) :=
  match fs with
  | [] => None
  | f :: r =>
      match f with
      | HVal t' o v => if ((t' =? t) && (o <=? a) && (a <? o + 8))%uint63 then Some (v, (a - o)%uint63) else sv_find r t a
      | HBytes t' o n v => if ((t' =? t) && (o <=? a) && (a <? o + n))%uint63 then Some (v, (a - o)%uint63) else sv_find r t a
      | _ => sv_find r t a
      end
  end.

Definition kf_slot (t a : int) : slot :=
  match byte_known_in IM KF t a with
  | Some b => SK b
  | None => match sv_find KF t a with
            | Some (v, j) => if sv_cov KF t a v j then SV v j else SU
            | None => SU
            end
  end.

Lemma kf_slot_sound t a :
  slot_val rho (kf_slot t a) (rview segs (ms_mem ms0) (adr rho t (to_Z a))).
Proof.
  unfold kf_slot. destruct (byte_known_in IM KF t a) as [b|] eqn:Hb.
  - cbn [slot_val]. exact (byte_known_in_sound segs IM HIM rho ms0 Hrho0 KF t a b Hfacts Hb).
  - destruct (sv_find KF t a) as [[v j]|]; [|exact I].
    destruct (sv_cov KF t a v j) eqn:Hc; [|exact I].
    cbn [slot_val]. exact (sv_cov_sound segs KF rho ms0 Hfacts t a v j Hc).
Qed.

Definition in_reg (t : int) (o n : Z) : bool :=
  match iget t M with
  | Some rg => (to_Z (rg_lo rg) <=? o) && (o + n <=? to_Z (rg_len rg))
  | None => false
  end.

Definition kf_slots (t : int) (o : Z) : option slots :=
  if keptb t && (0 <=? o) && (o <? 2 ^ 61) && in_reg t (o / 8 * 8) 8 then
    let a := of_Z (o / 8 * 8) in
    Some (SL (kf_slot t a) (kf_slot t (a + 1)%uint63) (kf_slot t (a + 2)%uint63) (kf_slot t (a + 3)%uint63)
             (kf_slot t (a + 4)%uint63) (kf_slot t (a + 5)%uint63) (kf_slot t (a + 6)%uint63) (kf_slot t (a + 7)%uint63))
  else None.

Lemma frame_rview t rg z :
  In t keep -> iget t M = Some rg -> to_Z (rg_lo rg) <= z < to_Z (rg_len rg) ->
  rview segs mem (adr rho t z) = rview segs (ms_mem ms0) (adr rho t z)
  /\ wview segs mem (adr rho t z) = wview segs (ms_mem ms0) (adr rho t z).
Proof.
  intros Hk Hg Hz. pose proof (region_ok_nowrap' rho t rg (HM t rg Hg)) as Hnw.
  pose proof (i63_range (rg_lo rg)). pose proof (br_u64 (rho t)).
  assert (E : mem (adr rho t z) = ms_mem ms0 (adr rho t z)).
  { apply (Hframe t Hk rg _ Hg). rewrite (adr_unsigned rho t z) by lia. lia. }
  unfold rview, wview. rewrite E. split; reflexivity.
Qed.

Theorem kf_slots_sound t o sls : kf_slots t o = Some sls ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o / 8 * 8 /\ o / 8 * 8 + 8 <= to_Z (rg_len rg) /\ 0 <= o
    /\ slots_val rho sls (fun j => rview segs mem (adr rho t (o / 8 * 8 + Z.of_nat j))).
Proof.
  unfold kf_slots. intros H.
  destruct (keptb t && (0 <=? o) && (o <? 2 ^ 61) && in_reg t (o / 8 * 8) 8) eqn:Ec; [|discriminate].
  injection H as <-.
  apply andb_prop in Ec as [Ec Hir]. apply andb_prop in Ec as [Ec H61]. apply andb_prop in Ec as [Hk Ho].
  apply keptb_In in Hk. apply Z.leb_le in Ho. apply Z.ltb_lt in H61.
  unfold in_reg in Hir. destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  apply andb_prop in Hir as [Hlo Hhi]. apply Z.leb_le in Hlo, Hhi.
  exists rg. split; [reflexivity|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Ho|].
  set (o8 := o / 8 * 8) in *.
  assert (Ho8 : 0 <= o8 < 2 ^ 61) by (unfold o8; Z.div_mod_to_equations; lia).
  assert (Ha : to_Z (of_Z o8) = o8) by (apply of_Z_small; lia).
  assert (Haj : forall k : int, 0 <= to_Z k < 8 -> to_Z (of_Z o8 + k)%uint63 = o8 + to_Z k).
  { intros k Hk8. rewrite add_spec, Ha. apply Z.mod_small. rewrite i63_wB. lia. }
  assert (Hs : forall k : int, 0 <= to_Z k < 8 ->
            slot_val rho (kf_slot t (of_Z o8 + k)%uint63) (rview segs mem (adr rho t (o8 + to_Z k)))).
  { intros k Hk8. rewrite (proj1 (frame_rview t rg (o8 + to_Z k) Hk Hg ltac:(lia))).
    rewrite <- (Haj k Hk8). apply kf_slot_sound. }
  unfold slots_val. cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7].
  pose proof (Hs 0%uint63 ltac:(cbn; lia)) as H0. pose proof (Hs 1%uint63 ltac:(cbn; lia)) as H1.
  pose proof (Hs 2%uint63 ltac:(cbn; lia)) as H2. pose proof (Hs 3%uint63 ltac:(cbn; lia)) as H3.
  pose proof (Hs 4%uint63 ltac:(cbn; lia)) as H4. pose proof (Hs 5%uint63 ltac:(cbn; lia)) as H5.
  pose proof (Hs 6%uint63 ltac:(cbn; lia)) as H6. pose proof (Hs 7%uint63 ltac:(cbn; lia)) as H7.
  assert (E0 : (of_Z o8 + 0)%uint63 = of_Z o8).
  { apply to_Z_inj. rewrite (Haj 0%uint63 ltac:(cbn; lia)). change (to_Z 0) with 0. lia. }
  rewrite E0 in H0.
  change (to_Z 0) with 0 in H0. change (to_Z 1) with 1 in H1. change (to_Z 2) with 2 in H2.
  change (to_Z 3) with 3 in H3. change (to_Z 4) with 4 in H4. change (to_Z 5) with 5 in H5.
  change (to_Z 6) with 6 in H6. change (to_Z 7) with 7 in H7.
  change (Z.of_nat 0) with 0. change (Z.of_nat 1) with 1. change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3.
  change (Z.of_nat 4) with 4. change (Z.of_nat 5) with 5. change (Z.of_nat 6) with 6. change (Z.of_nat 7) with 7.
  repeat split; assumption.
Qed.

Definition kf_wr (t : int) (o n : Z) : bool :=
  keptb t && (0 <=? o) && (0 <=? n) && (o + n <? 2 ^ 61) && in_reg t o n
  && wr_cov KF t (of_Z o) (of_Z n).

Theorem kf_wr_sound t o n : kf_wr t o n = true ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + n <= to_Z (rg_len rg)
    /\ forall x, o <= x < o + n -> wview segs mem (adr rho t x) <> None.
Proof.
  unfold kf_wr. intros H. apply andb_prop in H as [H Hcov]. apply andb_prop in H as [H Hir].
  apply andb_prop in H as [H H61]. apply andb_prop in H as [H Hn]. apply andb_prop in H as [Hk Ho].
  apply keptb_In in Hk. apply Z.leb_le in Ho, Hn. apply Z.ltb_lt in H61.
  unfold in_reg in Hir. destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  apply andb_prop in Hir as [Hlo Hhi]. apply Z.leb_le in Hlo, Hhi.
  exists rg. split; [reflexivity|]. split; [exact Hlo|]. split; [exact Hhi|].
  intros x Hx. rewrite (proj2 (frame_rview t rg x Hk Hg ltac:(lia))).
  pose proof (wr_cov_sound segs KF rho ms0 Hfacts t (of_Z o) (of_Z n) Hcov (x - o)) as Hw.
  rewrite !of_Z_small in Hw by lia. replace (o + (x - o)) with x in Hw by lia. apply Hw. lia.
Qed.

End Keep.
