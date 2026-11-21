(* Modified by Theorem Labs, 2026-11: made from A/AD1t.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1t.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AD2j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AD2i_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition drv_ranges : list (Z * nat) :=
[((symaddr Symbols.Asan.s_main), (symwords Symbols.Asan.s_main (Symbols.Asan.s_emit_printf + 0x48)%Z))  ; ((symaddr Symbols.Asan.s_open), (symwords Symbols.Asan.s_open (Symbols.Asan.s___syscall_ret + 0x38)%Z))  ;
((symaddr Symbols.Asan.s_sccp), (symwords Symbols.Asan.s_sccp (Symbols.Asan.s___syscall_cp + 0x4)%Z))  ; ((symaddr Symbols.Asan.s_close), (symwords Symbols.Asan.s_close (Symbols.Asan.s_read + 0x34)%Z))  ;
((symaddr Symbols.Asan.s_atexit), 49%nat); ((symaddr Symbols.Asan.s___lock), 3%nat); ((symaddr (Symbols.Asan.s___lock + 0x1f8)%Z), 1%nat); ((symaddr Symbols.Asan.s___unlock), 3%nat)].
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table tfibsegs lo n t) end.
Definition tfibtbl_drv : ctable := Eval vm_compute in build_ranges drv_ranges TEmpty.
Lemma tfibtbl_drv_eq : tfibtbl_drv = build_ranges drv_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tfibtbl_drv). Qed.
Lemma build_ranges_ok : forall rs t, Forall (fun r => 0 <= fst r) rs -> table_ok tfibsegs t -> table_ok tfibsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Lemma tfibtbl_drv_ok : table_ok tfibsegs tfibtbl_drv.
Proof. rewrite tfibtbl_drv_eq. apply build_ranges_ok; [repeat constructor; cbn; lia | apply table_ok_empty]. Qed.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. exact AB1h_w.tfib_wx. Qed.
Definition run_ (ss : sstate) : sstate := fst (sym_runN tfibsegs tfibtbl_drv FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN tfibsegs tfibtbl_drv FUEL pc ss).
Definition A_argc_test : Z := (symaddr (Symbols.Asan.s_main + 0x2c)%Z).
Definition A_m1_call : Z := (symaddr (Symbols.Asan.s_main + 0x50)%Z).
Definition ss_pro_t : sstate := Eval vm_compute in (run_ (ss_main true)).
Definition ss_pro_f : sstate := Eval vm_compute in (run_ (ss_main false)).
Definition ss_open : sstate := Eval vm_compute in (run_ (add_cond ss_pro_t (mkAC (neg_bc BC_NE) (SOff 3 0) (SLit 2)))).
Definition ss_m1 : sstate := Eval vm_compute in
(runto_ A_m1_call (resume ss_open (SLit 3) (ss_mem ss_open) (ss_facts ss_open))).
Definition K_M1 : nat := 42.
Definition ss_m1c : sstate := Eval vm_compute in (run_ ss_m1).
Definition keep_drv (cut : Z) (rs : smem) : smem :=
match rs with
| r0 :: rest => trim_lo r0 cut :: List.filter (fun r => forallb (fun c => match c_val c with CData _ _ _ => false | _ => true end) (r_chunks r)) rest
| [] => []
end.
Definition rs_m1 : smem := Eval vm_compute in keep_drv (-128) (ss_mem ss_m1c).
Definition WIN (spo : Z) : YP09.region := mkRegion (Some 0%nat) (-65536) spo (-65536) spo [].
Definition drv_after (ss : sstate) (rs : smem) (k : nat) (retpc spo : Z) : sstate :=
mkSS retpc (sr_sets (ss_regs ss) (junk_upd k CLOB)) (WIN spo :: rs) None (ss_facts ss).
Definition ss_m1r : sstate := Eval vm_compute in drv_after ss_m1c rs_m1 K_M1 (symaddr (Symbols.Asan.s_main + 0x54)%Z) (-128).
Definition A_RD : Z := (symaddr (Symbols.Asan.s_main + 0xcc)%Z).
Definition ss_rd0 : sstate := Eval vm_compute in runto_ A_RD (add_cond ss_m1r (mkAC Instr.BC_NE (SOff 46 0) (SLit 0))).
