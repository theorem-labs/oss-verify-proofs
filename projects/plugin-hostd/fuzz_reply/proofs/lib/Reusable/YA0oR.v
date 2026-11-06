(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YA0oInv.v, with its module paths changed; 95 of its 119 lines of code are new or changed and 114 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK18 YK0j YP0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YG0n YG0d YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(* Facts carried across a world step that may hide MORE at the addresses of a set DS (wle_in segs DS W W', YA0nH.v;
   wle' = wle_in RZ). Each fact moves when every byte it reads lies outside DS: such a byte that is visible at W stays
   visible at W', and a byte the fact reads is visible at W because the fact reads it as Some (a hidden byte reads as
   None, H_off_segments). At DS := RZ_cf these are the post-call transports of the cf driver at R := wle'. *)
Section d.
Variable segs : list Segment.
Context {fx : FPState}.

Lemma vis_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) (x : word),
  wle_in segs DS W W' -> ~ DS (bv_unsigned x) -> w_H W x = false -> w_H W' x = false.
Proof.
  intros DS W W' x H Hn Hx. destruct (w_H W' x) eqn:E; [|reflexivity].
  destruct (H x E) as [H1 | H2]; [rewrite H1 in Hx; discriminate | contradiction].
Qed.

Lemma mrestrict_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) m x b,
  wle_in segs DS W W' -> ~ DS (bv_unsigned x) ->
  mrestrict (w_H W) m x = Some b -> mrestrict (w_H W') m x = Some b.
Proof.
  intros DS W W' m x b H Hn Hb. unfold mrestrict in *.
  destruct (w_H W x) eqn:E; [discriminate|].
  rewrite (vis_wle_in_off DS W W' x H Hn E). exact Hb.
Qed.

Lemma mbyte_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) m a b,
  wle_in segs DS W W' -> ~ DS (bv_unsigned (Z_to_bv 64 a)) ->
  mbyte segs (mrestrict (w_H W) m) a = Some b -> mbyte segs (mrestrict (w_H W') m) a = Some b.
Proof.
  intros DS W W' m a b H Hn Hb.
  destruct (mbyte_mrestrict_some segs (w_H W) m a b (w_Hoff W) Hb) as [Hm Hv].
  rewrite (mbyte_mrestrict_visible segs (w_H W') m a (vis_wle_in_off DS W W' _ H Hn Hv)). exact Hm.
Qed.

(* The view read of one byte, the form every aview fact takes (aview reads, stk_up, rom_view). *)
Lemma aview_some_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) m a v,
  wle_in segs DS W W' -> ~ DS (bv_unsigned (Z_to_bv 64 a)) ->
  aview segs (w_H W) m a = Some v -> aview segs (w_H W') m a = Some v.
Proof.
  intros DS W W' m a v H Hn Hv. unfold aview in *.
  destruct (mbyte segs (mrestrict (w_H W) m) a) as [b|] eqn:E; [|discriminate Hv].
  rewrite (mbyte_wle_in_off DS W W' m a b H Hn E). exact Hv.
Qed.

Lemma aview_wle_in_off' : forall (DS : Z -> Prop) (W W' : world segs) m a,
  wle_in segs DS W W' -> ~ DS (bv_unsigned (Z_to_bv 64 a)) ->
  aview segs (w_H W) m a <> None -> aview segs (w_H W') m a <> None.
Proof.
  intros DS W W' m a H Hn Hv. destruct (aview segs (w_H W) m a) as [v|] eqn:E; [|contradiction].
  rewrite (aview_some_wle_in_off DS W W' m a v H Hn E). discriminate.
Qed.

Lemma val_mem_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) m a n v,
  wle_in segs DS W W' -> (forall k, (k < n)%nat -> ~ DS (bv_unsigned (Z_to_bv 64 (a + Z.of_nat k)))) ->
  val_mem segs (mrestrict (w_H W) m) a n v -> val_mem segs (mrestrict (w_H W') m) a n v.
Proof.
  intros DS W W' m a n v H Hn Hv k Hk. exact (mbyte_wle_in_off DS W W' m _ _ H (Hn k Hk) (Hv k Hk)).
Qed.

Lemma writable_at_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) m a,
  wle_in segs DS W W' -> ~ DS (bv_unsigned (Z_to_bv 64 a)) ->
  writable_at segs (mrestrict (w_H W) m) a -> writable_at segs (mrestrict (w_H W') m) a.
Proof.
  intros DS W W' m a H Hn Hw. unfold writable_at, wview in *.
  destruct (mrestrict (w_H W') m (Z_to_bv 64 a)) as [b'|] eqn:E'; [discriminate|].
  destruct (mrestrict (w_H W) m (Z_to_bv 64 a)) as [b|] eqn:E.
  - rewrite (mrestrict_wle_in_off DS W W' m _ b H Hn E) in E'. discriminate.
  - exact Hw.
Qed.

(* The symbolic memory's regions read no byte of DS: every byte of each region's [lo, hi). *)
Definition regions_off (DS : Z -> Prop) (E : env) (rs : smem) : Prop :=
  forall r a, In r rs -> base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r -> ~ DS a.

Lemma mem_ok_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) E m rs,
  wle_in segs DS W W' -> regions_off DS E rs ->
  mem_ok segs E (mrestrict (w_H W) m) rs -> mem_ok segs E (mrestrict (w_H W') m) rs.
Proof.
  intros DS W W' E m rs H Hoff (Hwf & Hok & Hpd). split; [exact Hwf|]. split; [|exact Hpd].
  rewrite Forall_forall in Hok |- *. intros r Hr. destruct (Hok r Hr) as (H1 & H2 & H3 & H4).
  pose proof (regions_wf_In _ _ Hwf Hr) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hw & Hci).
  assert (Hd : forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r ->
    ~ DS (bv_unsigned (Z_to_bv 64 a))).
  { intros a Ha.
    assert (E1 : bv_unsigned (Z_to_bv 64 a) = a)
      by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
    rewrite E1. exact (Hoff r a Hr Ha). }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros o Ho. apply (writable_at_wle_in_off DS W W' m); [exact H | apply Hd; lia | exact (H3 o Ho)].
  - rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
    destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
    pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
    apply (mbyte_wle_in_off DS W W' m); [exact H | apply Hd; lia | exact Hb2].
Qed.

(* st_ok_wle (YA0o.v) at a wle_in step: the regions of the symbolic state read no byte of DS. *)
Lemma st_ok_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) E ss ms,
  wle_in segs DS W W' -> regions_off DS E (ss_mem ss) ->
  st_ok segs E ss (restrict (w_H W) ms) -> st_ok segs E ss (restrict (w_H W') ms).
Proof.
  intros DS W W' E ss ms H Hoff (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  unfold st_ok. cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem] in *.
  repeat (split; [assumption|]). split; [|exact H9].
  exact (mem_ok_wle_in_off DS W W' E (ms_mem ms) (ss_mem ss) H Hoff H8).
Qed.

(* rom_view (YG0d.v) at a wle_in step: the read-only bytes lie outside DS (and below 2^64). A read-only byte is never
   hidden (H_off_segments), so its view is the same at W and W'. *)
Lemma rom_view_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) mem,
  wle_in segs DS W W' -> (forall a, in_rom segs a -> 0 <= a < 2 ^ 64 /\ ~ DS a) ->
  rom_view segs W mem -> rom_view segs W' mem.
Proof.
  intros DS W W' mem H Hr Hv a Ha. destruct (Hr a Ha) as [Hb Hn].
  assert (E1 : bv_unsigned (Z_to_bv 64 a) = a)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  assert (Hvis : w_H W (Z_to_bv 64 a) = false).
  { destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
    pose proof (w_Hoff W _ E) as Hf. rewrite E1 in Hf.
    destruct Ha as (sg & Hsg & _ & Hs1 & Hs2).
    apply (find_segment_none_spec segs a 1 Hf sg Hsg). split; lia. }
  assert (Hn' : ~ DS (bv_unsigned (Z_to_bv 64 a))) by (rewrite E1; exact Hn).
  rewrite <- (Hv a Ha). unfold aview, mbyte, mrestrict.
  rewrite Hvis, (vis_wle_in_off DS W W' _ H Hn' Hvis). reflexivity.
Qed.
End d.
