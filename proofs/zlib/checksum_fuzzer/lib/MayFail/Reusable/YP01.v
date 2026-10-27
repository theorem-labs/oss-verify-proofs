(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP01.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition regs32 : list Z := map Z.of_nat (seq 0 32).
Lemma reg_cases : forall (P : reg -> Prop),
(forall z, In z regs32 -> P (Z_to_bv 5 z)) -> forall r, P r.
Proof.
intros P H r. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H.
pose proof (u5_range r) as Hr. unfold regs32.
apply in_map_iff. exists (Z.to_nat (bv_unsigned r)). split; [lia|]. apply in_seq. lia.
Qed.
Definition all_regs : list reg :=
[0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.
Lemma In_bv_eq : forall (r : reg) (l : list reg), In (bv_unsigned r) (map bv_unsigned l) -> In r l.
Proof.
intros r l H. apply in_map_iff in H as (r' & Heq & Hin). apply bv_eq in Heq. subst. exact Hin.
Qed.
Lemma all_regs_in : forall r : reg, In r all_regs.
Proof.
intros r. apply In_bv_eq. pose proof (u5_range r) as Hr.
set (z := bv_unsigned r) in *. clearbody z.
assert (Hm : map bv_unsigned all_regs = regs32) by (vm_compute; reflexivity). rewrite Hm.
unfold regs32. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Lemma reg_cases_lit : forall (P : reg -> Prop),
(forall r, In r all_regs -> P r) -> forall r, P r.
Proof. intros P H r. apply H. apply all_regs_in. Qed.
Lemma regs_ok_by_cases : forall E sr regs,
(forall r, In r all_regs -> getr regs r = sv_denot E (sr_get sr r)) ->
regs_ok E sr regs.
Proof. intros E sr regs H. exact (reg_cases_lit _ H). Qed.
Fixpoint atom_regs (k n : nat) : list sv :=
match n with O => [] | S n' => SOff k 0 :: atom_regs (S k) n' end.
Ltac regs_ok_cases :=
apply regs_ok_by_cases;
let z := fresh "z" in let Hz := fresh "Hz" in
intros z Hz; cbv [all_regs In] in Hz;
repeat (destruct Hz as [<-|Hz];
[ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn -[Z_to_bv getr];
repeat match goal with |- context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v end;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; try reflexivity
| ]);
try (exfalso; exact Hz).
Ltac regs_ok_cases_pre tac :=
apply regs_ok_by_cases;
let z := fresh "z" in let Hz := fresh "Hz" in
intros z Hz; cbv [all_regs In] in Hz;
repeat (destruct Hz as [<-|Hz];
[ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
first [ tac
| cbn -[Z_to_bv getr];
repeat match goal with |- context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v end;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; try reflexivity ]
| ]);
try (exfalso; exact Hz).
