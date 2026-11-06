(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac gshow_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "STUCK AT PC =" pc end.
Ltac ngexp_dbg cuts fin := ngrun_cut cuts; first [ fin | (ngbranch; ngexp_dbg cuts fin) | gshow_pc ].
Ltac ngexp_f_dbg cuts fin keep := ngrun_cut_f cuts keep; first [ fin | (ngbranch; ngexp_f_dbg cuts fin keep) | gshow_pc ].

Ltac intro_words := repeat lazymatch goal with |- forall y : ?T, _ => lazymatch T with bv 64 => intro | word => intro end end.

Ltac ntape_norm :=
  repeat match goal with
  | H : context [(e_TAPE ?E + 8 * W ?s + 16)%Z] |- _ => replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z in H by lia
  end.
Ltac nclose := ntape_norm; s2_close_mem0.

Ltac nz_lt_by tac := apply B_nz_lt; tac.
Ltac nopen H := s2_open_mem H.
Ltac nexit0 KX := gexit KX.
Ltac nexit KX := ngrun_to 0xc43a8%Z; nexit0 KX.
