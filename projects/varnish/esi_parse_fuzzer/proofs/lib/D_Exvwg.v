(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WalkTac StoreOk Stre9ts MmapSim LibAvhx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Nodes.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibAvhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Export SumW496 RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require SegScan.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wseg_ok_all : forall segs n (a : word), (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall u, (bv_unsigned a <= u < bv_unsigned a + Z.of_nat n)%Z ->
     exists seg, find_segment segs u 1 = Some seg /\ seg_writable seg = true /\
                 segment_byte_at (seg_bytes seg) (Z.to_N (u - Z.of_N (seg_base seg))) <> None) ->
  wseg_ok segs a n = true.
Proof.
  intros segs n. induction n as [|n IH]; intros a Hn HS; [reflexivity|].
  cbn [wseg_ok]. destruct (HS (bv_unsigned a)) as (seg & F & W & B); [rewrite Nat2Z.inj_succ; lia|].
  rewrite F, W. destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))); [|congruence]. cbn [andb].
  destruct n as [|n']; [reflexivity|].
  assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; rewrite !Nat2Z.inj_succ in Hn; lia).
  apply IH; [rewrite Hu1; rewrite (Nat2Z.inj_succ (S n')) in Hn; lia|].
  intros u Hu. rewrite Hu1 in Hu. apply HS. rewrite (Nat2Z.inj_succ (S n')). lia.
Qed.
Lemma wseg_ok_of_range : forall segs n a, (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  SegScan.SEGSCAN.range_okI seg_writable segs a n = true -> wseg_ok segs (Z_to_bv 64 a) n = true.
Proof.
  intros segs n a Ha Hn H. destruct n as [|n']; [reflexivity|].
  assert (E : bv_unsigned (Z_to_bv 64 a) = a)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64)%Z; rewrite Nat2Z.inj_succ in Hn; lia).
  apply wseg_ok_all; rewrite E; [exact Hn|]. exact (SegScan.SEGSCAN.range_okI_spec _ _ _ _ H).
Qed.
Lemma ref_wseg_1c : wseg_ok RSEGS (0x31000 : word) 204800%nat = true.
Proof.
  apply (wseg_ok_of_range RSEGS 204800%nat 0x31000%Z).
  - discriminate.
  - vm_compute. discriminate.
  - (lazymatch goal with |- @eq ?T _ ?r => vm_cast_no_check (@eq_refl T r) end).
Qed.

Lemma store_ok_data : forall m (a : word) n,
  (0x31000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x63000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x31000 : word) a 204800%nat n 0x31000 0x63000);
    [reflexivity | reflexivity | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

(* [comment removed for export] *)
Definition stdio_globals (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x623eb) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x62840) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x62830) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x31780) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x31698)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x31690) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x315a8)). (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atexit_st (mem : word -> option byte) (reg : bool) : Prop :=
  if reg then
    rdn RSEGS mem (Z_to_bv 64 0x621b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x621b8))
    /\ rdn RSEGS mem (Z_to_bv 64 0x621a8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
    /\ rdn RSEGS mem (Z_to_bv 64 0x621c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22948))
    /\ rdn RSEGS mem (Z_to_bv 64 0x622c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17f8c))
    /\ rdn RSEGS mem (Z_to_bv 64 0x621b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn RSEGS mem (Z_to_bv 64 0x41804) 1%nat = Some [Z_to_bv 8 0]
  else rdn RSEGS mem (Z_to_bv 64 0x621b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
