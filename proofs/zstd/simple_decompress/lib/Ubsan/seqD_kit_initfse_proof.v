(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdSeqW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg seqD_kit_initfse seqD_kit_initfse_c1 seqD_kit_initfse_c2 seqD_kit_initfse_c3 seqD_kit_initfse_c4 seqD_kit_initfse_c5.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem zd_initfse_proof : zd_initfse_stmt.
Proof.
  unfold zd_initfse_stmt, zd_initfse_stmt_if. intros until t.
  intros MI HBD HST TB OK SQB LN N1 R1 R2 R3 R4 R5 R5b R6 R7 A1 A2 A3 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB _.
  pose proof (seq_tl_range k t OK) as RT.
  assert (CASES : 65 <= bc + st_log t \/ (bc + st_log t <= 64 /\ ptr = SEQ) \/
                  (bc + st_log t <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8) \/
                  (bc + st_log t <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8 /\ (bc + st_log t) / 8 <= ptr - SEQ) \/
                  (bc + st_log t <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8 /\ ptr - SEQ < (bc + st_log t) / 8)).
  { clear - IB RT RB.
    destruct (Z_le_gt_dec (bc + st_log t) 64) as [Bq|Bq]; [|left; lia]. destruct (IB ltac:(lia)) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia|].
    destruct (Z_le_gt_dec ((bc + st_log t) / 8) (ptr - SEQ)); [right; right; right; left; lia | right; right; right; right; lia]. }
  destruct CASES as [C|[C|[C|[C|C]]]];
    [ eapply ifs_c1 | eapply ifs_c2 | eapply ifs_c3 | eapply ifs_c4 | eapply ifs_c5 ]; try eassumption; exact C.
Qed.
