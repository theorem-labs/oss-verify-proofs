(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit Fz_G_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wg_keep_live_nw : forall live frames sp W (m m' : mem) p n X cs, rw_cells asegs m X cs -> rt_pres_fp live frames sp W m m' ->
  In (p, n) live -> p <= X -> X + Z.of_nat (cells_size cs) <= p + n ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' X cs.
Proof.
  intros live frames sp W m m' p n X cs src_cells frame_pres blk_live blk_lo blk_hi rng_unwritten.
  refine (rw_cells_agree_nw asegs m m' X cs src_cells _).
  intros w w_in; cbv beta in w_in.
  assert (w_live : in_live live (bv_unsigned w)).
  { exists p, n. split; [exact blk_live | lia]. }
  apply frame_pres.
  - right; right; left; exact w_live.
  - exact (rng_unwritten (bv_unsigned w) w_in).
Qed.

Lemma wg_keep_static_nw : forall live frames sp W (m m' : mem) X cs, rw_cells asegs m X cs -> rt_pres_fp live frames sp W m m' ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> client_static x /\ outside W x) -> rw_cells asegs m' X cs.
Proof.
  intros live frames sp W m m' X cs src_cells frame_pres rng_static.
  apply (rw_cells_agree_nw asegs m m' X cs src_cells).
  intros w w_in.
  destruct (rng_static _ w_in) as [w_static w_out].
  exact (frame_pres w (or_intror (or_introl w_static)) w_out).
Qed.

Lemma wg_keep_seg_nw : forall W (m m' : mem) X cs, rw_cells asegs m X cs -> munch W m m' ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' X cs.
Proof.
  intros W m m' X cs src_cells unwritten rng_out.
  apply (rw_cells_agree_nw asegs m m' X cs src_cells).
  intros w w_in.
  apply unwritten, rng_out, w_in.
Qed.

(* [comment removed for export] *)
Ltac cl_keep_nw src agr dst :=
  let kept := fresh "kept" in
  lazymatch type of src with
  | rw_cells ?segs ?m0 ?A ?cs =>
      eassert (kept : rw_cells segs _ A cs);
      [ eapply (rw_cells_agree_nw segs m0 _ A cs src)
      | ]
  | ro_cells ?segs ?m0 ?A ?cs =>
      eassert (kept : ro_cells segs _ A cs);
      [ eapply (ro_cells_agree segs m0 _ A cs src)
      | ]
  end;
  [ first
      [ eapply agr;
        solve [ cbn [cells_size csize Nat.add]; lia
              | cbn [cells_size csize Nat.add] in *; unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia
              | intros ? ?; cbv beta in *; cbn [cells_size csize Nat.add] in *; lia ]
      | eapply agree_sub;
        [ exact agr
        | intros ? ?; cbv beta in *; cbn [cells_size csize Nat.add] in *;
          solve [ lia | unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia ] ] ]
  | first [ rename kept into dst | clear src; rename kept into dst ] ].
