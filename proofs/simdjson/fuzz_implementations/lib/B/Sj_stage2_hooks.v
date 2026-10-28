(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma sown_read_at : forall (m : word -> option byte) c a, mem_inv bsegs m -> (0 <= c < 256)%Z -> a = wa (T_SOWN + c) ->
  ov_read_bytes bsegs m a 1 = Some [Z_to_bv 8 (sown c)].
Proof. intros m c a MI Hc ->. apply sown_read; assumption. Qed.
Ltac s2_load_sown :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1] =>
      lazymatch goal with
      | MIh : mem_inv segs m |- _ =>
          let Ea := addr_expr a in
          let idx := lazymatch Ea with
                     | Z.add 152640%Z ?i => i
                     | Z.add ?i 152640%Z => i
                     end in
          rewrite (sown_read_at m idx a MIh ltac:(lia) ltac:(unfold wa, T_SOWN; f_equal; lia))
      end
  end;
  load_post.

Lemma esc_read_at : forall (m : word -> option byte) c a, mem_inv bsegs m -> (0 <= c < 256)%Z -> a = wa (T_ESC + c) ->
  ov_read_bytes bsegs m a 1 = Some [Z_to_bv 8 (esc c)].
Proof. intros m c a MI Hc ->. apply esc_read; assumption. Qed.
Ltac s2_load_esc :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1] =>
      lazymatch goal with
      | MIh : mem_inv segs m |- _ =>
          let Ea := addr_expr a in
          let idx := lazymatch Ea with
                     | Z.add 184096%Z ?i => i
                     | Z.add ?i 184096%Z => i
                     end in
          rewrite (esc_read_at m idx a MIh ltac:(lia) ltac:(unfold wa, T_ESC; f_equal; lia))
      end
  end;
  load_post.

Ltac s2_dig_norm x :=
  lazymatch x with
  | Z.add ?b ?lit => let _ := constr:(eq_refl : Z.leb 0 lit = true) in constr:((lit + b)%Z)
  | _ => constr:((0 + x)%Z)
  end.
Ltac s2_dig_idx Ea :=
  lazymatch Ea with
  | Z.add 152960%Z (Z.mul 4 ?x) => s2_dig_norm x
  | Z.add (Z.mul 4 ?x) 152960%Z => s2_dig_norm x
  | Z.add (Z.add (Z.mul 4 ?x) 152960%Z) ?c => let q := eval vm_compute in (c / 4)%Z in constr:((q + x)%Z)
  | Z.add (Z.add 152960%Z (Z.mul 4 ?x)) ?c => let q := eval vm_compute in (c / 4)%Z in constr:((q + x)%Z)
  end.
Ltac s2_load_dig :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 4] =>
      lazymatch goal with
      | MIh : mem_inv segs m |- _ =>
          let Ea := addr_expr a in
          let idx := s2_dig_idx Ea in
          rewrite (dig_read m idx a MIh ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia))
      end
  end;
  load_post.
