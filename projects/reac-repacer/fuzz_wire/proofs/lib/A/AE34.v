(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AE34.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan build; icpt_ranges adds __asan_memmove (0x51310, 220 words), which fuzz_wire.asan places inside fuzz_grant's 1009-word range at 0x517f4, now the two ranges (0x50c2c, 441) and (0x51680, 568). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table tfibsegs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok tfibsegs t -> table_ok tfibsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition musl_sel_ranges : list (Z * nat) :=
[ (0x88570, 71%nat); (0x8d99c, 25%nat); (0x8da00, 87%nat); (0x8d80c, 435%nat); (0x8e350, 1146%nat); (0x91460, 47%nat);
(0x926e0, 10%nat); (0x97138, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x41568, 38%nat);  (0x4188c, 165%nat); (0x42338, 549%nat); (0x42bcc, 94%nat); (0x42d44, 180%nat);
(0x4328c, 156%nat); (0x434fc, 157%nat); (0x43e54, 729%nat); (0x449b8, 45%nat); (0x44d84, 54%nat);
(0x470b4, 102%nat); (0x50c2c, 441%nat); (0x51310, 220%nat); (0x51680, 568%nat); (0x53694, 79%nat); (0x53b20, 209%nat); (0x580a4, 6%nat);
(0x58fb4, 40%nat);  (0x633e4, 13%nat);  (0x63484, 7%nat);   (0x636e8, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x51970 = Some 0x81010113 /\ clookup tbl_icpt 0x91b14 = None /\ clookup tbl_icpt 0x63860 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
