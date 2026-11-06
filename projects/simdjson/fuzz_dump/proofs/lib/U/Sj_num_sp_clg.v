(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_cl Sj_num_sp_ce Sj_num_sp_cf2 Sj_num_sp_cf1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac num_abstract_data ::= num_abstract_data_u.
Local Ltac nnorm ::= nnorm_u.

Section SPUCLG.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.
  Hypothesis HSET : spu_memset_stmt.
  Hypothesis HPM : spu_pm_stmt.
  Hypothesis HPDC : spu_pdc_stmt.
  Hypothesis HNDC : spu_ndc_stmt.

  Lemma spu_890 : forall (q : Z) (wv xa7 : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> spu_tmd E xa7 wv IP IL FPT FL ->
    evt usegs (spu_post E) (SPS E 0x57888 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 xa2 xa3 wv xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK HSET HPM HPDC HNDC.
    intros until FL. intros INV FRM Hq HTM. pose proof INV as INV0. spu_open INV0. spu_env OK.
    assert (D3 : IsData xa3) by exact I. assert (D4 : IsData wv) by exact I.
    destruct (image_readable_b usegs mm 4 0xd82e0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (fmin & FML & FMIN).
    destruct (image_readable_b usegs mm 184 0x1a0e0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (mxm & MXL & MXM).
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x58158%Z => u_trap pc
      | 0x57928%Z => first [ eapply evt_eq; [| eapply (spu_930 E OK HSET HPM HPDC HNDC q wv xa7)]; [num_st_eq | exact INV | assumption | lia | exact HTM] | fail 100 "cut" pc ]
      | 0x578c0%Z => first [ eapply evt_eq; [| eapply (spu_8c8 E OK q)]; [num_st_eq | exact INV | assumption | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      | 0x58038%Z => first [ eapply evt_eq; [| eapply (spu_040 E OK q)]; [num_st_eq | exact INV | assumption | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      end).
  Qed.
End SPUCLG.
