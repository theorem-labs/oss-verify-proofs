(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import ZdSeqW.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg AZ_seq_bit_iface AZ_seq_initfse_c1 AZ_seq_initfse_c2 AZ_seq_initfse_c3 AZ_seq_initfse_c4 AZ_seq_initfse_c5.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem zd_initfse_proofA : zd_initfse_stmtA.
Proof.
  unfold zd_initfse_stmtA, zd_initfse_stmtA_if. intros until t.
  intros HBD HST TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 A1 A2 A3 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB STK LOS SPB OS1 OS2 OS3 OS4 APB AROB APS AROS AROQ AROT ACL ART AST MI _.
  pose proof (seq_tl_range k t OK) as RT.
  assert (CASES : 65 <= bc + st_log t \/ (bc + st_log t <= 64 /\ ptr = SEQ) \/
                  (bc + st_log t <= 64 /\ 8 <= Z.of_nat (length sqb) /\ SEQ + 8 <= ptr <= SEQ + Z.of_nat (length sqb) - 8) \/
                  (bc + st_log t <= 64 /\ 8 <= Z.of_nat (length sqb) /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + Z.of_nat (length sqb) - 8 /\ (bc + st_log t) / 8 <= ptr - SEQ) \/
                  (bc + st_log t <= 64 /\ 8 <= Z.of_nat (length sqb) /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + Z.of_nat (length sqb) - 8 /\ ptr - SEQ < (bc + st_log t) / 8)).
  { unfold bit_okS in IB. clear - IB RT RB.
    destruct (Z_le_gt_dec (bc + st_log t) 64) as [Bq|Bq]; [|left; lia]. destruct (IB ltac:(lia)) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia|].
    destruct (Z_le_gt_dec ((bc + st_log t) / 8) (ptr - SEQ)); [right; right; right; left; lia | right; right; right; right; lia]. }
  destruct CASES as [C|[C|[C|[C|C]]]];
    [ eapply ifs_c1 | eapply ifs_c2 | eapply ifs_c3 | eapply ifs_c4 | eapply ifs_c5 ]; try eassumption; exact C.
Qed.
End CANSEC1.
