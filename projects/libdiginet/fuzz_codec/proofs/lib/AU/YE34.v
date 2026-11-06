(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AE34.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_scene/proofs/lib/A/AE34.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to libdiginet/fuzz_codec's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AE34.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libdiginet/fuzz_codec's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AE34.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YB1v.
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
[ (0x8de8c, 71%nat); (0x932b8, 25%nat); (0x9331c, 87%nat); (0x93128, 125%nat); (0x9331c, 258%nat); (0x93c6c, 1146%nat); (0x96d7c, 47%nat);
(0x97ffc, 10%nat); (0x9ca54, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x4241c, 24%nat); (0x4247c, 1%nat); (0x42480, 11%nat);  (0x42740, 165%nat); (0x431ec, 549%nat); (0x43a80, 94%nat); (0x43bf8, 180%nat);
(0x44140, 156%nat); (0x443b0, 157%nat); (0x44d08, 729%nat); (0x4586c, 45%nat); (0x45c38, 54%nat);
(0x47f68, 102%nat); (0x51ae0, 1009%nat); (0x541d8, 79%nat); (0x54664, 209%nat); (0x58be8, 6%nat);
(0x59af8, 40%nat);  (0x63f28, 13%nat);  (0x63fc8, 7%nat);   (0x6422c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x524b4 = Some 0x81010113 /\ clookup tbl_icpt 0x97430 = None /\ clookup tbl_icpt 0x643a4 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
