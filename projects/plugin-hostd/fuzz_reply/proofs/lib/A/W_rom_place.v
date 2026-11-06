(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the placement fact of the check_no_loss -> gesture_model -> list_drop chain:
   W_journal.v rom_out at the callee's own G, [(HA + 80, 16)] with HA = g_s + ASRC * j (j < 4), the held list's
   head of source j (a .bss field), and gx_ok / gx_rt there.  Generic over the placement PI and the sink head SK;
   W_rom_place_fr.v discharges the two placement premises at PB_fr. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YP0b YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_kit W_journal W_rep W_contract.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
Variable B : asyms.

(* rom_out at any G whose bytes are not read-only image bytes: ROMNS (W_check_no_loss.v's form) gives the errno and
   pinned-owned clauses, the sink's overflow head out of the read-only image the fourth. *)
Lemma rom_out_of_place : forall G,
(forall a, inG G a -> ~ in_rom SEGS a) ->
(forall a, in_rom SEGS a -> ~ (AOFL_HEAD <= a < AOFL_HEAD + 8)) ->
(forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a)) ->
rom_out SEGS B G.
Proof.
intros G HG HOH HNS a Ha. destruct (HNS a Ha) as [He Hp].
split; [intros Hin; exact (HG a Hin Ha)|]. split; [exact Hp|]. split; [exact He | exact (HOH a Ha)].
Qed.

(* The held list's head of source j lies inside g_s's 384 bytes. *)
Lemma cnl_g_in_src : forall HA (j : nat), HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
forall a, inG [(HA + 80, 16)] a -> VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384.
Proof.
intros HA j EHA Hj a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
unfold in_zr in Ha. cbn [fst snd] in Ha. unfold ASRC in EHA. lia.
Qed.

Lemma cnl_g_rom_out : forall HA (j : nat), HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> ~ in_rom SEGS a) ->
(forall a, in_rom SEGS a -> ~ (AOFL_HEAD <= a < AOFL_HEAD + 8)) ->
(forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a)) ->
rom_out SEGS B [(HA + 80, 16)].
Proof.
intros HA j EHA Hj HS HOH HNS. apply rom_out_of_place; [|exact HOH | exact HNS].
intros a Ha. exact (HS a (cnl_g_in_src HA j EHA Hj a Ha)).
Qed.

Lemma cnl_g_sub : forall HA (j : nat) G0, HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
In (VAL (A_OBJ 22), 384) G0 -> forall a, inG [(HA + 80, 16)] a -> inG G0 a.
Proof.
intros HA j G0 EHA Hj Hin a Ha. unfold inG. apply Exists_exists. exists (VAL (A_OBJ 22), 384).
split; [exact Hin|]. unfold in_zr. cbn [fst snd]. exact (cnl_g_in_src HA j EHA Hj a Ha).
Qed.

Lemma cnl_g_gx_ok : forall HA (j : nat) G0, HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
In (VAL (A_OBJ 22), 384) G0 -> gx_ok SEGS B G0 -> gx_ok SEGS B [(HA + 80, 16)].
Proof.
intros HA j G0 EHA Hj Hin HG0. exact (gx_ok_sub SEGS B _ G0 (cnl_g_sub HA j G0 EHA Hj Hin) HG0).
Qed.

Lemma cnl_g_gx_rt : forall HA (j : nat) G0, HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
In (VAL (A_OBJ 22), 384) G0 -> gx_rt (PI := PI) B G0 -> gx_rt (PI := PI) B [(HA + 80, 16)].
Proof.
intros HA j G0 EHA Hj Hin HG0. exact (gx_rt_sub B _ G0 (cnl_g_sub HA j G0 EHA Hj Hin) HG0).
Qed.
End b.
End a.
