(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep ZBridge.
Import ListNotations.
Open Scope Z_scope.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) (seg_rom ?segs)) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; bn_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store_opt ::=
  lazymatch goal with
  | |- ?EVHD (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) (seg_rom ?segs)) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.


Ltac ifc b :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "C" in
      assert (H : c = b) by (unfold_cond; rewrite ?MState.unsigned_lit by lia; fold_lit_ux; solve_cond_rec);
      rewrite H; clear H
  end.

Ltac ifc2 b :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "C" in
      assert (H : c = b) by (rewrite ?bv_lts_zero_r, ?bv_lts_zero_l; unfold_cond; rewrite ?MState.unsigned_lit by lia; fold_lit_ux; solve_cond_rec);
      rewrite H; clear H
  end.

Ltac norm_getr :=
  repeat match goal with
  | |- context [getr (TNode ?a ?b ?c) ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let v := eval cbn [tget] in (match tget p (TNode a b c) with Some v => v | None => w0 end) in
      change (getr (TNode a b c) r) with v
  end.

Ltac lit_store :=
  match goal with
  | |- _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (Mem.le8 (Z_to_bv 64 z)); mem_after_store
  | |- _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (Mem.le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
