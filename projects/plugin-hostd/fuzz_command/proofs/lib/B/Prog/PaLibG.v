(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1g.v, walk helpers over fuzz_command's listing: module paths, csym. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/PaLibG.v for fuzz_command.asan-ubsan: module paths. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Fixpoint sv_atom_bound_lo (lim : nat) (v : sv) : nat :=
match v with
| SLit _ => 0
| SOff n _ => if (lim <=? n)%nat then 0 else S n
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => Nat.max (sv_atom_bound_lo lim a) (sv_atom_bound_lo lim b)
| SExt _ _ a => sv_atom_bound_lo lim a
| SData _ _ _ => 0
| SF1 _ a => sv_atom_bound_lo lim a
| SF2 _ a b => Nat.max (sv_atom_bound_lo lim a) (sv_atom_bound_lo lim b)
| SF3 _ a b c => Nat.max (sv_atom_bound_lo lim a) (Nat.max (sv_atom_bound_lo lim b) (sv_atom_bound_lo lim c))
end.
Definition cval_atom_bound_lo (lim : nat) (cv : cval) : nat := match cv with CVal _ v => sv_atom_bound_lo lim v | _ => 0%nat end.
Definition atom_lo (lim n : nat) : nat := if (lim <=? n)%nat then 0%nat else S n.
Definition region_atom_bound_lo (lim : nat) (r : YP09.region) : nat :=
Nat.max (match YP09.r_base r with Some n => atom_lo lim n | None => 0%nat end)
(list_max_map (fun c => cval_atom_bound_lo lim (YP09.c_val c)) (YP09.r_chunks r)).
Definition facts_atom_bound_lo (lim : nat) (G : facts) : nat :=
Nat.max (list_max_map (fun p => atom_lo lim (fst p)) (f_atoms G))
(Nat.max (list_max_map (fun c => Nat.max (sv_atom_bound_lo lim (ac_a c)) (sv_atom_bound_lo lim (ac_b c))) (f_conds G))
(list_max_map (fun p => Nat.max (sv_atom_bound_lo lim (fst p)) (sv_atom_bound_lo lim (snd p))) (f_alias G))).
Definition ss_atom_bound_lo (lim : nat) (ss : sstate) : nat :=
Nat.max (list_max_map (sv_atom_bound_lo lim) (ss_regs ss))
(Nat.max (list_max_map (region_atom_bound_lo lim) (ss_mem ss))
(Nat.max (facts_atom_bound_lo lim (ss_facts ss))
(match ss_resv ss with Some a => sv_atom_bound_lo lim a | None => 0%nat end))).
Definition run_K_lo (floor : nat) (Bx : sv) (SH : list shent) (ss : sstate) : nat :=
Nat.max floor (Nat.max (ss_atom_bound_lo A_TEXT ss) (Nat.max (sv_atom_bound_lo A_TEXT Bx) (list_max_map (fun e => atom_lo A_TEXT (she_m e)) SH))).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {L : ptable csym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
Lemma st_ok_pi_set_reg : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> r <> 0%bv -> getr (ms_regs ms) r = sv_denot E e ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
exact (st_ok_set_reg SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms r e HS Hr He).
Qed.
Lemma st_ok_pi_region_nth : forall E ss ms i r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.
Lemma ew_Eimg_Ereg_nat : forall (regs : bvmap 5 word) extra n (r : bv 5),
Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
End f.
End d.
Ltac ppcs := try (lazymatch goal with T : PALib ?Bv |- _ => rewrite ?(pal_free Bv T), ?(pal_malloc Bv T) end).
