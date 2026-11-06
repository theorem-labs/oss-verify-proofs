(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module LibLib.
Section Run.
Variable segs : list Segment.
Variable R : drun.
Let MP := r_MP R.
Let PB := r_PB R.

Variables (N : int) (E0 : env) (K : TSet).
Hypothesis HPB : PB (eb E0).

Definition LNODE (T : sstate) : Prop :=
  forall E ms m, eb E = eb E0 -> stable N E0 E -> MP m -> st_ok segs (OPS R) E T ms m -> realizes segs (mkCfg ms m) K.

Lemma stable_trans : forall E1 E2, stable N E0 E1 -> stable N E1 E2 -> stable N E0 E2.
Proof.
  intros E1 E2 H1 H2 k Hk. destruct (H1 k Hk) as [A1 B1]. destruct (H2 k Hk) as [A2 B2].
  split; [rewrite A2; exact A1 | rewrite B2; exact B1].
Qed.

Theorem lnode_cert : forall (C : ctx) (p : plan) (T : sstate) (obls : list obligation) (cutl : list (int * template)),
  ctx_wfb C = true -> itab_ok segs (c_itab C) -> contracts_ok segs (OPS R) C MP PB ->
  check segs C p T = Some obls -> obls_hold PB obls -> c_mroot C = VL wzero ->
  plan_stable N p = true -> PrimInt63.leb N (s_next T) = true ->
  c_cuts C = imap_of cutl -> Forall (fun kv => LNODE (t_st (snd kv))) cutl ->
  c_ecalls C = imap_of [] ->
  LNODE T.
Proof.
  intros C p T obls cutl HWF HIT HCO HCHK HOB HM HP HN Hc HNc He E ms m Heb HST HMP HS.
  apply leb_spec in HN.
  eapply (check_sound_stable segs (OPS R) N C MP PB p T obls HWF HIT HCO (r_MPA R) HCHK HOB ltac:(rewrite HM; reflexivity) HP HN K E ms m HS);
    [rewrite Heb; exact HPB | exact HMP |].
  split.
  - intros tid T' Hf E' ms' m' Heb' HST' HMP' HS' _. rewrite Hc in Hf.
    exact (Forall_imap_of _ _ cutl tid T' HNc Hf E' ms' m' ltac:(rewrite Heb'; exact Heb) (stable_trans E E' HST HST') HMP' HS').
  - intros eid T' Hf. exfalso. rewrite He in Hf. apply imap_of_find_in in Hf. exact Hf.
Qed.

End Run.

Theorem lib_ok_of : forall segs R (GEN RET : sstate),
  (forall E0 K, r_PB R (eb E0) -> LNODE segs R (s_next GEN) E0 K RET -> LNODE segs R (s_next GEN) E0 K GEN) ->
  lib_ok segs R GEN RET.
Proof.
  intros segs R GEN RET H K E ms m HPB HMP HS Hret.
  refine (H E K HPB _ E ms m eq_refl (stable_refl _ _) HMP HS).
  intros E' ms' m' Heb HST HMP' HS'. apply (Hret E' ms' m'); [| exact HMP' | exact HS'].
  split; [exact Heb|]. intros k Hk. exact (HST k Hk).
Qed.

End LibLib.
