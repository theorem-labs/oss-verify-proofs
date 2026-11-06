(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk Zp9.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zpm Zwd Z103 Z104 Zwk Z107 Zwm Zxc Zxd Zxe Zxf
  Zyi Zyj Zyn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow_cp | s2_load_shadow | s2_load_cp | s2_load_sown | s2_load_pow | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumR6.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).
  Notation o s := 0%Z.

  Lemma seg_numr_cmpB : forall (Q : machine_state -> Prop) (s : st) neg,
    numr_write_k E Q CP s neg -> numr_fbcall_k E Q CP s ->
    numr_cmpB_k E Q CP s neg.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg KW KFB. unfold numr_cmpB_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngexp_f ltac:(fun pc => lazymatch pc with 0xa5b04%Z => fail | 0xa70ac%Z => fail | _ => idtac end)
            ltac:(idtac; lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                    lazymatch pc with
                    | 0xa5b04%Z => ngrun_to 0xa5b04%Z; kapply KW; nclose
                    | 0xa70ac%Z => ngrun_to 0xd7204%Z; kapply KFB; nclose
                    end end)
            ltac:(nkeep ltac:(fun n => idtac)).
  Qed.
End NumR6.
