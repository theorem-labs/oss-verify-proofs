(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_gp.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Section INVSTEP.
Variables (m m' : word -> option byte) (CA SB c sz nc newc j SP : Z).
Hypothesis I : INV_G m CA SB c sz nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 4194304 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\ SP <= 2^47.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis G : mem_grows m m'.

Ltac frm FR := apply (rd_frame m m'); [slia | znq; slia | intros x Hx; znq; apply FR; unfold owned_C; slia | ].

#[using="I Hj HCA HSB HSEP G"] Lemma inv_pop : 1 <= cnt_of nc j ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (REC CA c <= x < REC CA c + 4) -> ~ (CA + 2576 <= x < CA + 2584) -> m' (wa x) = m (wa x)) ->
  rd m' (REC CA c) 4 (cnt_of nc j - 1) -> (exists st, 0 <= st < 2^64 /\ rd m' (CA + 2576) 8 st) ->
  INV_G m' CA SB c sz nc newc (j + 1).
Proof. LiaFast.lf_pins (fun (I Hj HCA HSB HSEP G : LiaFast.U) => LiaFast.u0).
  intros Hc FR Rc Rst. destruct I as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (pop_step nc j ltac:(slia) ltac:(slia) Hc) as [Eb Ec].
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb. pose proof (b_of_bounds nc j ltac:(slia) ltac:(slia)) as Hbb.
  pose proof (cnt_of_range nc j ltac:(slia) ltac:(slia)) as Hcr.
  constructor.
  - slia.
  - frm FR. exact ISB.
  - frm FR. exact IRIB.
  - rewrite Ec. exact Rc.
  - frm FR. exact Imc.
  - frm FR. exact Isz.
  - intros i Hi. rewrite Ec in Hi |- *. replace (j + 1 + (cnt_of nc j - 1) - 1 - i) with (j + cnt_of nc j - 1 - i) by ring.
    frm FR. apply Ich. slia.
  - frm FR. exact Imu.
  - rewrite Eb. frm FR. exact Inf.
  - destruct Ina as (na & Hna & Rna). exists na. split; [exact Hna|]. frm FR. exact Rna.
  - intros k Hk. rewrite Eb in Hk. assert (Hnb : nc * b_of nc j <= newc) by slia.
    frm FR. apply Ifa. exact Hk.
  - exact Rst.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwrec; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwri; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwst; assumption.
Qed.

#[using="I Hj HCA HSB HSEP G"] Lemma inv_refill : cnt_of nc j = 0 ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) ->
  rd m' (REC CA c) 4 (nc - 1) -> rd m' (REC CA c + 4) 4 (2 * nc) -> rd m' (REC CA c + 8) 8 sz ->
  (forall i, 0 <= i < nc -> rd m' (REC CA c + 16 + 4 * i) 4 ((j + nc - 1 - i) * (sz / 16))) ->
  rd m' (RIX SB c) 8 0 -> rd m' (RIX SB c + 16) 8 (newc - nc * b_of nc j - nc) ->
  (exists na, 0 <= na < 2^64 /\ rd m' (RIX SB c + 72) 8 na) ->
  (exists st, 0 <= st < 2^64 /\ rd m' (CA + 2576) 8 st) ->
  INV_G m' CA SB c sz nc newc (j + 1).
Proof. LiaFast.lf_pins (fun (I Hj HCA HSB HSEP G : LiaFast.U) => LiaFast.u0).
  intros Hc FR Rc Rmc Rsz Rch Rmu Rnf Rna Rst. destruct I as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (refill_step nc j ltac:(slia) ltac:(slia) Hc) as (Ej & Eb & Ec).
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb.
  constructor.
  - slia.
  - frm FR. exact ISB.
  - frm FR. exact IRIB.
  - rewrite Ec. exact Rc.
  - exact Rmc.
  - exact Rsz.
  - intros i Hi. rewrite Ec in Hi |- *. replace (j + 1 + (nc - 1) - 1 - i) with (j + nc - 1 - i) by ring. apply Rch. slia.
  - exact Rmu.
  - rewrite Eb. replace (newc - nc * (b_of nc j + 1)) with (newc - nc * b_of nc j - nc) by ring. exact Rnf.
  - exact Rna.
  - intros k Hk. rewrite Eb in Hk. assert (Hnb : nc * b_of nc j <= newc) by slia.
    frm FR. apply Ifa. slia.
  - exact Rst.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwrec; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwri; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwst; assumption.
Qed.
End INVSTEP.
