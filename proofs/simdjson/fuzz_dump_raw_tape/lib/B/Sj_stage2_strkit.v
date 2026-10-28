(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_hooks.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac s2_dig_lit c :=
  let b := eval vm_compute in (andb (Z.leb 148064 c) (Z.ltb c 151608)) in
  lazymatch b with true => idtac end.

Ltac s2_dig_idx2 Ea :=
  lazymatch Ea with
  | Z.add (Z.mul 4 ?x) ?c => let _ := constr:(ltac:(s2_dig_lit c; exact I) : True) in
                            let q := eval vm_compute in ((c - 148064) / 4)%Z in constr:((q + x)%Z)
  | Z.add ?c (Z.mul 4 ?x) => let _ := constr:(ltac:(s2_dig_lit c; exact I) : True) in
                            let q := eval vm_compute in ((c - 148064) / 4)%Z in constr:((q + x)%Z)
  end.
Ltac s2_load_dig2 :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 4] =>
      lazymatch goal with
      | MIh : mem_inv segs m |- _ =>
          let Ea := addr_expr a in
          let idx := s2_dig_idx2 Ea in
          rewrite (dig_read m idx a MIh ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia))
      end
  end;
  load_post.

Ltac s2_load_shadow_dig :=
  match goal with
  | |- context [ov_read_bytes bsegs ?m ?a 1] =>
      let Ea := addr_expr a in
      let x := lazymatch Ea with (Z.shiftr ?x 3 + 2147450880)%Z => x end in
      lazymatch x with
      | Z.add (Z.mul 4 _) ?c => s2_dig_lit c
      | Z.add ?c (Z.mul 4 _) => s2_dig_lit c
      end;
      lazymatch goal with
      | SHZh : a_shz ?E, MUh : munch _ (e_m0 ?E) m, WMh : wmono bsegs (e_m0 ?E) m |- _ =>
          rewrite (shzr_dig E m x a (SHZh m MUh WMh) ltac:(s2_shz_side) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.
