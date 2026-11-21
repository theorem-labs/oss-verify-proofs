(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD20.v at theorem-labs/oss-verify-proofs@6b32741d849a, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AD20.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD20.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04 YL09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD1y_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition lp_ranges : list (Z * nat) :=
drv_ranges ++
[(0x41588, 1%nat)     ;
(0x4328c, 22%nat)    ;
(0x4333c, 9%nat)     ;
(0x58fb4, 13%nat)    ;
(0x8d6bc, 1%nat)     ;
(0x87ff0, 3%nat)     ].
Definition tfibtbl_lp : ctable := Eval vm_compute in build_ranges lp_ranges TEmpty.
Lemma tfibtbl_lp_eq : tfibtbl_lp = build_ranges lp_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tfibtbl_lp). Qed.
Lemma tfibtbl_lp_ok : table_ok tfibsegs tfibtbl_lp.
Proof. rewrite tfibtbl_lp_eq. apply build_ranges_ok; [repeat constructor; cbn; lia | apply table_ok_empty]. Qed.
Definition run_lp (ss : sstate) : sstate := fst (sym_runN tfibsegs tfibtbl_lp FUEL ss).
Definition runto_lp (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN tfibsegs tfibtbl_lp FUEL pc ss).
Definition RDPC : Z := 0x7fa84.
Definition RWPC : Z := 0x7fa94.
Definition A_icpt_fprintf : Z := 0x415a4.
Definition R_inited : YP09.region := mkRegion None 0xa1458 0xa1459 0 0 [mkChunk 0xa1458 (CVal 1 (SLit 1))].
Definition R_realrd : YP09.region := mkRegion None 0x9a520 0x9a528 0 0 [mkChunk 0x9a520 (CVal 8 (SLit 0x97218))].
Definition R_errno : YP09.region := mkRegion None 0x5d366c 0x5d3670 0x5d366c 0x5d3670 [].
Definition RT_REGIONS : smem := [R_inited; R_realrd; R_errno].
Definition A_BUF : nat := 46.   Definition A_LEN : nat := 58.   Definition A_CAP : nat := 59.   Definition J0 : nat := 60.
Definition A_WANT : nat := 77.
Definition Jregs : list reg := map (fun n => Z_to_bv 5 (Z.of_nat n)) [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat.
Definition fact_len : afact := mkAF 0 (2 ^ 26) 0.
Definition fact_cap : afact := mkAF 65536 (2 ^ 26) 16.
Definition fact_want : afact := mkAF 1 65536 0.
Definition X0 : sstate := ss_rd0.
Definition RD_regs : list sv :=
Eval vm_compute in (sr_set (sr_set (sr_sets (ss_regs X0) (junk_upd J0 Jregs)) 19%bv (SOff A_LEN 0)) 21%bv (SOff A_CAP 0)).
Definition RD_facts : facts :=
Eval vm_compute in (mkFacts ((A_LEN, fact_len) :: (A_CAP, fact_cap) :: f_atoms (ss_facts X0))
(List.filter (fun c => negb (acond_eqb c (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0)))) (f_conds (ss_facts X0)))
(f_alias (ss_facts X0))).
Definition LH_mem : smem := Eval vm_compute in (ss_mem X0 ++ RT_REGIONS).
Definition S_RD : sstate := mkSS RDPC RD_regs LH_mem None RD_facts.
Definition sv_want : sv := SAlu ALU_ADD (SMd M_MUL (SOff A_LEN 0) (SLit (-1))) (SOff A_CAP 0).
Definition cWb : acond := mkAC BC_GEU sv_want (SLit 65536).
Definition S_W : sstate := Eval vm_compute in (run_lp S_RD).
Definition S_Wb : sstate := Eval vm_compute in (runto_lp RWPC (add_cond S_W cWb)).
Definition RW_regs : list sv := Eval vm_compute in (sr_set (ss_regs S_Wb) 12%bv (SOff A_WANT 0)).
Definition RW_facts : facts := Eval vm_compute in (mkFacts ((A_WANT, fact_want) :: f_atoms RD_facts) (f_conds RD_facts) (f_alias RD_facts)).
Definition S_RW : sstate := mkSS RWPC RW_regs LH_mem None RW_facts.
Definition S_RE : sstate := Eval vm_compute in (run_lp S_RW).
Definition S_CL : sstate := Eval vm_compute in (run_lp (resume S_RE (SLit 0) (ss_mem S_RE) (ss_facts S_RE))).
Definition S_HDR : sstate := Eval vm_compute in (run_lp (resume S_CL (SLit 0) (ss_mem S_CL) (ss_facts S_CL))).
