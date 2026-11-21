(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require MmapSim RefNodes AsanCeil.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrFeasLift2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition room (B : Z) (mo : Model) : Prop :=
  AsanCeil.init_sp_ok (m_vmmaps mo) /\
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) /\
  Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) <= 40000 /\
  vm_backing_used mo + B + 4096 <= vm_limit (m_vmmaps mo).

Lemma room_grantable {rc : runConstT} : forall B mo, 0 <= B -> B + 4096 <= 2 ^ 30 -> room B mo -> grantable B mo.
Proof.
  intros B mo HB0 HB (Hisp & Hsz & Hcnt & Hbud) len Hlen.
  assert (Hr : 0 <= page_round_up_Z len <= len + 4095).
  { unfold page_round_up_Z. change page_size with 4096. Z.div_mod_to_equations. lia. }
  (* a grant is Linux's placement, which takes a positive, page-aligned length. *)
  assert (Hr0 : 0 < page_round_up_Z len) by (apply AsanCeil.page_round_up_Z_pos'; lia).
  assert (Hral : page_round_up_Z len mod page_size = 0) by (unfold page_round_up_Z; apply Z_mod_mult).
  apply RefNodes.grant_exists; try assumption; lia.
Qed.
