(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the discharge of W_contract.v's rg_place record at the pinned placement
   PB_fr and RG := fr_globals.  The geometry half (the A_OBJ equalities, the three alignments, in_img, apart from
   A_OBJ 0/1/32) is vm_compute on PB_fr and proved here; the three B-abstract facts (not as_owned_static, not the
   errno cell, apart from as_uar_cell B) are a fact about the image's start-up data and are taken as hypotheses,
   discharged at the top where the concrete fuzz_reply B lives (ReplyTFIB over the generated AF0m).  fr_rg_place
   assembles the two halves so a caller cites one name. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG0d YG0n YK04 YP09 YC5d YI00 YI16 YM05 YK11 YA0n YP0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_tbl W_place W_listing W_img W_kit W_rep W_contract.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms. Variable MT : ameter_ops. Variable MMAX : Z.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* The geometry, all by vm_compute on the pinned placement. *)
Lemma fr_rg_lock : rg_lock fr_globals = VAL (A_OBJ 6). Proof. vm_compute. reflexivity. Qed.
Lemma fr_rg_nsrc : rg_nsrc fr_globals = VAL (A_OBJ 7). Proof. vm_compute. reflexivity. Qed.
Lemma fr_rg_src : rg_src fr_globals = VAL (A_OBJ 8). Proof. vm_compute. reflexivity. Qed.
(* fr_rg_place assembles the geometry (proved here) with the three B-abstract facts (taken as hypotheses) and the
   writable half (a segment fact, taken as a hypothesis) into W_contract.v's rg_place at PB_fr / fr_globals. *)
Lemma fr_rg_place :
  (forall a, rg_rng fr_globals a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  (forall (H : word -> bool) (m : word -> option byte) a,
     (rg_lock fr_globals <= a < rg_lock fr_globals + 12 \/ rg_nsrc fr_globals <= a < rg_nsrc fr_globals + 4) ->
     H (Z_to_bv 64 a) = false -> writable_at SEGS (mrestrict H m) a) ->
  (forall a, rg_rng fr_globals a -> ~ (VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8) /\ ~ (VAL (A_OBJ 1) <= a < VAL (A_OBJ 1) + 8) /\
     ~ (VAL (A_OBJ 32) <= a < VAL (A_OBJ 32) + 8) /\ ~ (as_uar_cell B <= a < as_uar_cell B + 4)) ->
  @rg_place _ PB_fr B fr_globals.
Proof.
intros HIMG HWR HSEP. unfold rg_place.
split; [exact fr_rg_lock|]. split; [exact fr_rg_nsrc|]. split; [exact fr_rg_src|].
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
split; [exact HIMG|]. split; [exact HWR | exact HSEP].
Qed.
End a.
