(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPU_sum PFFU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import U2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPCU_sum PFFCU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require PC_s12iface ROpNew_nt RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require PU2_main.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require NUMU_sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Theorem stage2_closed_modnum :
  (forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPSU) ->
  (forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFSU) ->
  (forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPCSU) ->
  (forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFCSU) ->
  forall rc : runConstT, @Ubsan.PC_s12iface.stage2_stmt rc.
Proof.
  intros H1 H2 H3 H4 rc.
  exact (PU2_main.stage2_proof (Ubsan.ROpNew_nt.opnew_nt_proof Ubsan.RF_malloc_spec.rmalloc_spec)
                               (Ubsan.ROpNew_nt.opdelete_arr_proof Ubsan.RF_free_spec.rfree_spec_proof) H1 H2 H3 H4).
Qed.

Print Assumptions stage2_closed_modnum.

(* [comment removed for export] *)
Theorem stage2_closed : forall rc : runConstT, @Ubsan.PC_s12iface.stage2_stmt rc.
Proof.
  exact (stage2_closed_modnum NUMU_sound.NUMU.sfpu_okG NUMU_sound.NUMU.pffu_okG NUMU_sound.NUMU.sfpcu_okG NUMU_sound.NUMU.pffcu_okG).
Qed.

Print Assumptions stage2_closed.
