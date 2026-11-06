(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0b YQ03 YQ0i YQ09 YQ04 YQ0e YQ0a YO3p YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YB0z YD15 YD14.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition drv_ranges : list (Z * nat) :=
[(0x80b0c, 296%nat)  ; (0x91a74, 71%nat)  ;
(0x9c05c, 10%nat)  ; (0xa0ab4, 69%nat)  ;
(0x916e8, 49%nat); (0x9bd60, 3%nat); (0x9bf58, 1%nat); (0x9bfe8, 3%nat)].
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table trasegs lo n t) end.
Definition tratbl_drv : ctable := Eval vm_compute in build_ranges drv_ranges TEmpty.
Lemma tratbl_drv_eq : tratbl_drv = build_ranges drv_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tratbl_drv). Qed.
Lemma build_ranges_ok : forall rs t, Forall (fun r => 0 <= fst r) rs -> table_ok trasegs t -> table_ok trasegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Lemma tratbl_drv_ok : table_ok trasegs tratbl_drv.
Proof. rewrite tratbl_drv_eq. apply build_ranges_ok; [repeat constructor; cbn; lia | apply table_ok_empty]. Qed.
Lemma Hwx_tfa : wx_segs_nowrap trasegs.
Proof. exact YB0l.tra_wx. Qed.
Definition run_ (ss : sstate) : sstate := fst (sym_runN trasegs tratbl_drv FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN trasegs tratbl_drv FUEL pc ss).
Definition A_main : Z := 0x80b0c.
Definition A_argc_test : Z := 0x80b38.
Definition A_m1_call : Z := 0x80b5c.
Definition A_open_fail : Z := 0x80b4c.
Definition ss_pro_t : sstate := Eval vm_compute in (run_ (ss_main true)).
Definition ss_pro_f : sstate := Eval vm_compute in (run_ (ss_main false)).
Definition ss_pro (two : bool) : sstate := if two then ss_pro_t else ss_pro_f.
Definition ss_open : sstate := Eval vm_compute in (run_ (add_cond ss_pro_t (mkAC (neg_bc BC_NE) (SOff 3 0) (SLit 2)))).
Definition ss_m1 : sstate := Eval vm_compute in
(runto_ A_m1_call (resume ss_open (SLit 3) (ss_mem ss_open) (ss_facts ss_open))).



Example ss_m1_regs : sr_get (ss_regs ss_m1) 10%bv = SLit 65536 /\ sr_get (ss_regs ss_m1) 20%bv = SLit 3.
Proof. vm_compute. split; reflexivity. Qed.
Definition A_wrap_malloc : Z := 0x53104.   Definition A_wrap_free : Z := 0x53100.
Definition A_icpt_read : Z := 0x420e4.     Definition A_icpt_fwrite : Z := 0x420e8.   Definition A_icpt_memcpy : Z := 0x51dac.
Definition K_M1 : nat := 42.
Definition ss_m1c : sstate := Eval vm_compute in (run_ ss_m1).

Definition keep_drv (cut : Z) (rs : smem) : smem :=
match rs with
| r0 :: rest => trim_lo r0 cut :: List.filter (fun r => forallb (fun c => match c_val c with CData _ _ _ => false | _ => true end) (r_chunks r)) rest
| [] => []
end.
Definition rs_m1 : smem := Eval vm_compute in keep_drv (-128) (ss_mem ss_m1c).
Definition WIN (spo : Z) : YQ0b.region := mkRegion (Some 0%nat) (-65536) spo (-65536) spo [].
Definition drv_after (ss : sstate) (rs : smem) (k : nat) (retpc spo : Z) : sstate :=
mkSS retpc (sr_sets (ss_regs ss) (junk_upd k CLOB)) (WIN spo :: rs) None (ss_facts ss).
Definition ss_m1r : sstate := Eval vm_compute in drv_after ss_m1c rs_m1 K_M1 0x80b60 (-128).
Definition ss_oom1 : sstate := Eval vm_compute in run_ (add_cond ss_m1r (mkAC Instr.BC_EQ (SOff 46 0) (SLit 0))).
Definition A_RD : Z := 0x80bd8.
Definition ss_rd0 : sstate := Eval vm_compute in runto_ A_RD (add_cond ss_m1r (mkAC Instr.BC_NE (SOff 46 0) (SLit 0))).


Example ss_rd0_regs : sr_get (ss_regs ss_rd0) 9%bv = SOff 46 0 /\ sr_get (ss_regs ss_rd0) 19%bv = SLit 0
/\ sr_get (ss_regs ss_rd0) 21%bv = SLit 65536 /\ sr_get (ss_regs ss_rd0) 22%bv = SLit 0x5cc810 /\ sr_get (ss_regs ss_rd0) 23%bv = SOff 46 0
/\ sr_get (ss_regs ss_rd0) 20%bv = SLit 3 /\ ss_mem ss_rd0 = ss_mem ss_m1r.
Proof. vm_compute. repeat split; reflexivity. Qed.
