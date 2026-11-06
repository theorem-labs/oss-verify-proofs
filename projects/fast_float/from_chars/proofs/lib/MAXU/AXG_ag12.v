(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngGM MngNtfPre MngNtfC MngCtx MngCtx2 MngShape MngTake.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngNtfM MngNtfS MngMWP MngMW0 MngMW1 MngMW2 MngMW3 MngTakeX AXF_efbz AXG_as1 AXG_amr0 AXG_ag0 AXG_ag1 AXG_ag3p AXG_ag5 AXG_ag6 AXG_ag10 AXG_ag11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac side12 := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

(* [comment removed for export] *)
Definition efw (m : word -> option byte) (idx mem st : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m (wa (st - 3)) (word_to_le_bytes 1 (wa idx))) (wa (st - 2)) (word_to_le_bytes 2 (wa ((st - mem - 16) / 16))))
    (wa (st - 3)) (word_to_le_bytes 1 (wa idx)).

Lemma efb_whole : forall m idx mem sz st, efb_mem m idx (16 * sz - 4) mem sz st 0 = efw m idx mem st.
Proof.
  intros m idx mem sz st. unfold efb_mem, efw. cbv zeta. unfold efb_rsv, efb_code.
  replace (16 * sz - 4 - 16 * 0 - (16 * sz - 4)) with 0 by ring. cbn [Z.eqb]. rewrite Z.mul_0_r, !Z.add_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition nn_mem (m : word -> option byte) (idx mem st mt sc cnt usage hb : Z) : word -> option byte :=
  nt_mem (efw m idx mem st) mt st sc cnt usage hb idx.

Lemma nn_grows : forall m idx mem st mt sc cnt usage hb, mem_grows m (nn_mem m idx mem st mt sc cnt usage hb).
Proof.
  intros. unfold nn_mem, nt_mem, mp_ins2, nt_ins1, nt_hdr, efw.
  do 11 (eapply mem_grows_trans; [|apply wbytes_grows]). eapply mem_grows_trans; [|apply nzm_grows].
  do 5 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

Section NNM.
Variables (m : word -> option byte) (idx mem st mt sc cnt usage hb : Z).
Hypothesis Hsc : 0 <= sc <= 47.
Hypothesis Hcnt : 1 <= cnt <= 32.
Hypothesis Hsize : 16 <= class_size sc <= 2032.
Hypothesis Hst : 4096 <= st.
Hypothesis Hend : st + 16 + class_size sc * cnt <= 2^47.
Hypothesis Hmt : 1 <= mt.
Hypothesis Hmt47 : mt + 40 <= 2^47.
Hypothesis Dmt : mt + 40 <= 0x10000 \/ 0x99000 <= mt.
Hypothesis Dst : st + 16 + class_size sc * cnt <= 0x10000 \/ 0x99000 <= st - 4.
Hypothesis Dms : mt + 40 <= st - 4 \/ st + 16 + class_size sc * cnt <= mt.

Local Notation size := (class_size sc).
Local Notation M := (nn_mem m idx mem st mt sc cnt usage hb).

#[using="st mt Hcnt Hsize Hst Hend Hmt Hmt47 Dmt Dst Dms"] Lemma Hsc0 : 16 <= size * cnt <= 2032 * 32.
Proof. LiaFast.lf_pins (fun (st mt Hcnt Hsize Hst Hend Hmt Hmt47 Dmt Dst Dms : LiaFast.U) => LiaFast.u0). nia. Qed.

(* [comment removed for export] *)
Definition nn_written (x : Z) : Prop :=
  (mt <= x < mt + 40) \/ (8 * sc + 622184 <= x < 8 * sc + 622192) \/ (8 * sc + 621800 <= x < 8 * sc + 621808) \/
  (st - 3 <= x < st) \/ (st <= x < st + 9) \/ (exists k, 0 <= k <= cnt /\ x = st + 12 + size * k).

#[using="Hsc Hcnt Hsize Hst Hend Hmt Hmt47 Dmt Dst Dms"] Lemma nn_out : forall x, 0 <= x < 2^64 -> ~ nn_written x -> M (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hsc Hcnt Hsize Hst Hend Hmt Hmt47 Dmt Dst Dms : LiaFast.U) => LiaFast.u0).
  intros x Hx Hn. pose proof Hsc0 as H0.
  assert (N1 : ~ (mt <= x < mt + 40)) by (intros H; apply Hn; left; exact H).
  assert (N3 : ~ (8 * sc + 622184 <= x < 8 * sc + 622192)) by (intros H; apply Hn; right; left; exact H).
  assert (N4 : ~ (8 * sc + 621800 <= x < 8 * sc + 621808)) by (intros H; apply Hn; right; right; left; exact H).
  assert (N5 : ~ (st - 3 <= x < st)) by (intros H; apply Hn; right; right; right; left; exact H).
  assert (N6 : ~ (st <= x < st + 9)) by (intros H; apply Hn; right; right; right; right; left; exact H).
  assert (N7 : forall k, 0 <= k <= cnt -> x <> st + 12 + size * k) by (intros k Hk E; apply Hn; right; right; right; right; right; exists k; auto).
  unfold nn_mem, nt_mem, mp_ins2, nt_ins1. rewrite !MngWb.wbytes_out by (clear - Hx N1 N3 N4 N6 Hmt Hmt47 Hsc Hst Hend H0; side12).
  rewrite nzm_out; [| exact Hx | clear - Hst; lia | clear - Hsize; lia | rewrite Z2Nat.id by (clear - Hcnt; lia); clear - Hend Hcnt Hsize Hst; nia |].
  - unfold nt_hdr, efw. rewrite !MngWb.wbytes_out by (clear - Hx N1 N5 Hmt Hmt47 Hst Hend H0; side12). reflexivity.
  - intros k Hk E. apply (N7 (Z.of_nat k)); [lia | rewrite E; ring].
Qed.
(* [comment removed for export] *)
#[using="Hsc Hcnt Hsize Hst Hend Hmt Hmt47 Dmt Dst Dms"] Lemma nn_reads :
  (forall k, (k < 8)%nat -> M (wa (mt + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mt)) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> M (wa (mt + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mt)) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> M (wa (mt + 16 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa st)) (Z_to_bv 8 0))) /\
  (forall k, (k < 4)%nat -> M (wa (mt + 24 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (2 ^ (cnt - 1 + 1) - 2))) (Z_to_bv 8 0))) /\
  (forall k, (k < 4)%nat -> M (wa (mt + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa ((2 ^ cnt - 1) - (2 ^ (cnt - 1 + 1) - 1)))) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> M (wa (mt + 32 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa (64 * sc + cnt + 31))) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> M (wa (8 * sc + 622184 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa (cnt + usage))) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> M (wa (8 * sc + 621800 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mt)) (Z_to_bv 8 0))) /\
  (forall k, (k < 8)%nat -> M (wa (st + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa mt)) (Z_to_bv 8 0))) /\
  M (wa (st + 8)) = Some (nth 0 (word_to_le_bytes 1 (wa (cnt - 1 + 32 * Z.shiftr hb 5))) (Z_to_bv 8 0)) /\
  M (wa (st + -3)) = Some (nth 0 (word_to_le_bytes 1 (wa (idx + 192))) (Z_to_bv 8 0)) /\
  (forall k, (k < 2)%nat -> M (wa (st - 2 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 2 (wa ((st - mem - 16) / 16))) (Z_to_bv 8 0))) /\
  (forall k, 0 <= k <= cnt -> M (wa (st + 12 + size * k)) = Some (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsc Hcnt Hsize Hst Hend Hmt Hmt47 Dmt Dst Dms : LiaFast.U) => LiaFast.u0).
  pose proof Hsc0 as H0. unfold nn_mem, nt_mem, mp_ins2, nt_ins1.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]].
  all: try (intros k Hk; rewrite ?MngWb.wbytes_out by (clear - Hk Hsc Hmt Hmt47 Dmt Hst Hend Dst Dms H0; side12);
            apply MngWb.wbytes_at_wa; [clear - Hsc Hmt Hst Hend H0; lia | side12 | rewrite length_N_to_le_bytes; exact Hk]).
  - rewrite ?MngWb.wbytes_out by (clear - Hsc Hmt Hmt47 Dmt Hst Hend Dst Dms H0; side12). apply MngWb.wbytes_at_wa0; [lia | side12 | cbn; lia].
  - rewrite !MngWb.wbytes_out by (clear - Hsc Hmt Hmt47 Dmt Hst Hend Dst Dms H0; side12).
    rewrite nzm_out; [| lia | lia | lia | rewrite Z2Nat.id by lia; nia | intros k Hk E; nia].
    unfold nt_hdr. apply MngWb.wbytes_at_wa0; [lia | side12 | cbn; lia].
  - intros k Hk. rewrite !MngWb.wbytes_out by (clear - Hk Hsc Hmt Hmt47 Dmt Hst Hend Dst Dms H0; side12).
    rewrite nzm_out; [| lia | lia | lia | rewrite Z2Nat.id by lia; nia | intros j Hj E; nia].
    unfold nt_hdr, efw. rewrite !MngWb.wbytes_out by (clear - Hk Hsc Hmt Hmt47 Dmt Hst Hend Dst Dms H0; side12).
    apply MngWb.wbytes_at_wa; [lia | side12 | rewrite length_N_to_le_bytes; exact Hk].
  - intros k Hk. assert (Hk' : 0 <= size * k <= size * cnt) by nia.
    rewrite !MngWb.wbytes_out by (clear - Hk Hk' Hsc Hmt Hmt47 Dmt Hst Hend Dst Dms H0; side12).
    replace (st + 12 + size * k) with ((st + 12) + size * Z.of_nat (Z.to_nat k)) by (rewrite Z2Nat.id by lia; ring).
    apply nzm_at; [lia | lia | rewrite Z2Nat.id by lia; nia | lia].
Qed.
End NNM.
