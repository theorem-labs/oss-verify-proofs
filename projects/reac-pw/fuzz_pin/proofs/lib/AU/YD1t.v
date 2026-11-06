(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1t.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AD1t.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AD1t.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_pin's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AD1t.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_pw.fuzz_pin.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YD2j YD2i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition drv_ranges : list (Z * nat) :=
[(0x80214, 296%nat)  ; (0x87d7c, 71%nat)  ;
(0x92064, 10%nat)  ; (0x96abc, 69%nat)  ;
(0x879f0, 49%nat); (0x91d68, 3%nat); (0x91f60, 1%nat); (0x91ff0, 3%nat)].
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
Proof. exact YB1h.tfib_wx. Qed.
Definition run_ (ss : sstate) : sstate := fst (sym_runN tfibsegs tfibtbl_drv FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN tfibsegs tfibtbl_drv FUEL pc ss).
Definition A_main : Z := 0x80214.
Definition A_argc_test : Z := 0x80240.
Definition A_m1_call : Z := 0x80264.
Definition A_open_fail : Z := 0x80254.
Definition ss_pro_t : sstate := Eval vm_compute in (run_ (ss_main true)).
Definition ss_pro_f : sstate := Eval vm_compute in (run_ (ss_main false)).
Definition ss_pro (two : bool) : sstate := if two then ss_pro_t else ss_pro_f.
Definition ss_open : sstate := Eval vm_compute in (run_ (add_cond ss_pro_t (mkAC (neg_bc BC_NE) (SOff 3 0) (SLit 2)))).
Definition ss_m1 : sstate := Eval vm_compute in
(runto_ A_m1_call (resume ss_open (SLit 3) (ss_mem ss_open) (ss_facts ss_open))).
Lemma ss_pro_t_pc : ss_pc ss_pro_t = A_argc_test.  Proof. reflexivity. Qed.
Lemma ss_open_pc : ss_pc ss_open = 0x92080.     Proof. reflexivity. Qed.
Lemma ss_m1_pc : ss_pc ss_m1 = A_m1_call.        Proof. reflexivity. Qed.
Example ss_m1_regs : sr_get (ss_regs ss_m1) 10%bv = SLit 65536 /\ sr_get (ss_regs ss_m1) 20%bv = SLit 3.
Proof. vm_compute. split; reflexivity. Qed.
Definition A_wrap_malloc : Z := 0x52b54.   Definition A_wrap_free : Z := 0x52b50.
Definition A_icpt_read : Z := 0x41930.     Definition A_icpt_fwrite : Z := 0x41934.   Definition A_icpt_memcpy : Z := 0x51a3c.
Definition K_M1 : nat := 42.
Definition ss_m1c : sstate := Eval vm_compute in (run_ ss_m1).
Lemma ss_m1c_pc : ss_pc ss_m1c = A_wrap_malloc. Proof. reflexivity. Qed.
Definition keep_drv (cut : Z) (rs : smem) : smem :=
match rs with
| r0 :: rest => trim_lo r0 cut :: List.filter (fun r => forallb (fun c => match c_val c with CData _ _ _ => false | _ => true end) (r_chunks r)) rest
| [] => []
end.
Definition rs_m1 : smem := Eval vm_compute in keep_drv (-128) (ss_mem ss_m1c).
Definition WIN (spo : Z) : YP09.region := mkRegion (Some 0%nat) (-65536) spo (-65536) spo [].
Definition drv_after (ss : sstate) (rs : smem) (k : nat) (retpc spo : Z) : sstate :=
mkSS retpc (sr_sets (ss_regs ss) (junk_upd k CLOB)) (WIN spo :: rs) None (ss_facts ss).
Definition ss_m1r : sstate := Eval vm_compute in drv_after ss_m1c rs_m1 K_M1 0x80268 (-128).
Definition ss_oom1 : sstate := Eval vm_compute in run_ (add_cond ss_m1r (mkAC Instr.BC_EQ (SOff 46 0) (SLit 0))).
Definition A_RD : Z := 0x802e0.
Definition ss_rd0 : sstate := Eval vm_compute in runto_ A_RD (add_cond ss_m1r (mkAC Instr.BC_NE (SOff 46 0) (SLit 0))).
Lemma ss_oom1_pc : ss_pc ss_oom1 = A_icpt_fwrite. Proof. reflexivity. Qed.
Lemma ss_rd0_pc : ss_pc ss_rd0 = A_RD. Proof. reflexivity. Qed.
Example ss_rd0_regs : sr_get (ss_regs ss_rd0) 9%bv = SOff 46 0 /\ sr_get (ss_regs ss_rd0) 19%bv = SLit 0
/\ sr_get (ss_regs ss_rd0) 21%bv = SLit 65536 /\ sr_get (ss_regs ss_rd0) 22%bv = SLit 0x5c3d50 /\ sr_get (ss_regs ss_rd0) 23%bv = SOff 46 0
/\ sr_get (ss_regs ss_rd0) 20%bv = SLit 3 /\ ss_mem ss_rd0 = ss_mem ss_m1r.
Proof. vm_compute. repeat split; reflexivity. Qed.
