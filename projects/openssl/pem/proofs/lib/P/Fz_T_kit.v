(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Ltac th_frame n sizes ST :=
  carve_frame n ST;
  lazymatch goal with
  | FRh : rw_cells ?segs ?mm ?A [CB n ?jk] |- _ =>
      apply (rw_cells_split_CB segs mm A [] n jk [] sizes) in FRh; [|reflexivity];
      cbn [mk_CB_cells app firstn skipn] in FRh
  end.


(* [comment removed for export] *)
Ltac th_release FR hi :=
  lazymatch goal with STh : stk _ _ _ _ |- _ => release_frame FR STh hi end.

(* [comment removed for export] *)
Lemma t_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac th_ret_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* [comment removed for export] *)
Ltac th_strip_ulit_in H := repeat (rewrite unsigned_lit in H by lia).
Ltac th_strip_ulit := repeat (rewrite unsigned_lit by lia).
Tactic Notation "tcall" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut;
      [ eapply SPEC; th_strip_ulit
      | let ms' := fresh "ms'" in let PO := fresh "POST" in
        intros ms' PO; hnf in PO; th_strip_ulit_in PO; revert ms' PO; post_call segs m ]
  end.
