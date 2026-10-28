(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Export RunDraw.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac atop_facts :=
  lazymatch goal with
  | _ : (0x7fff7f800000 <= @ATOP _ <= 0x7FFFFF800000)%Z |- _ => idtac
  | |- context [@ATOP _] => pose proof atop_range as ATOPR
  | _ : context [@ATOP _] |- _ => pose proof atop_range as ATOPR
  | _ => idtac
  end.
Ltac sec_facts :=
  lazymatch goal with
  | _ : (0 <= @SECRET _ < 2^64)%Z |- _ => idtac
  | _ => pose proof sec_range as SECR
  end.

(* [comment removed for export] *)
Definition pstage_len_sig : { n : nat | Z.of_nat n = 65536 }.
Proof. exists (Z.to_nat 65536). apply Z2Nat.id. apply Z.leb_le. reflexivity. Qed.
Definition PSTAGE_LEN : nat := proj1_sig pstage_len_sig.
Lemma PSTAGE_LEN_Z : Z.of_nat PSTAGE_LEN = 65536.
Proof. exact (proj2_sig pstage_len_sig). Qed.
Ltac stage_facts :=
  lazymatch goal with
  | _ : Z.of_nat PSTAGE_LEN = 65536 |- _ => idtac
  | |- context [PSTAGE_LEN] => pose proof PSTAGE_LEN_Z as PSTAGER
  | _ : context [PSTAGE_LEN] |- _ => pose proof PSTAGE_LEN_Z as PSTAGER
  | _ => idtac
  end.
Ltac lia := atop_facts; stage_facts; Stdlib.micromega.Lia.lia.
Ltac nia := atop_facts; stage_facts; Stdlib.micromega.Lia.nia.
