(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0b YQ03 YQ0i YQ09 YQ04 YQ0e YQ0a YO3p YO3v YI00 YL07 YL09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YB0z YF90 YD15 YD14 YD0f YD0j YD0l YD0p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition with_rt (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss ++ RT_REGIONS) (ss_resv ss) (ss_facts ss).
Definition ss_rd0_rt : sstate := Eval vm_compute in with_rt ss_rd0.
Definition S_RDn_rt : sstate := Eval vm_compute in with_rt S_RDn.
Definition S_RD'_rt : sstate := Eval vm_compute in with_rt S_RD'.
Lemma with_rt_eqs : with_rt ss_rd0 = ss_rd0_rt /\ with_rt S_RDn = S_RDn_rt /\ with_rt S_RD' = S_RD'_rt.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rt_wf : regions_wf RT_REGIONS = true. Proof. reflexivity. Qed.
Lemma reabs_chk_RD : reabs_check LT42 ss_rd0_rt RD_regs RD_facts = true /\ reabs_check LT42 S_RDn_rt RD_regs RD_facts = true
/\ reabs_check LT42 S_RD'_rt RD_regs RD_facts = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma mem_RD_rt : ss_mem ss_rd0_rt = LH_mem /\ ss_mem S_RDn_rt = LH_mem /\ ss_mem S_RD'_rt = LH_mem
/\ ss_pc ss_rd0_rt = RDPC /\ ss_pc S_RDn_rt = RDPC /\ ss_pc S_RD'_rt = RDPC.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition ext_chk (r1 r2 : YQ0b.region) : bool :=
match r_base r1, r_base r2 with
| None, None => (r_hi r1 <=? r_lo r2) || (r_hi r2 <=? r_lo r1)
| Some 0%nat, None => (-65536 <=? r_lo r1) | _, _ => false end%bool.
Lemma rt_abs : forallb (fun r => match r_base r with None => (0 <=? r_lo r) && (r_hi r <=? 0x5ff000) | _ => false end)%bool RT_REGIONS = true.
Proof. reflexivity. Qed.
Lemma rd0_ext : forallb (fun r1 => forallb (ext_chk r1) RT_REGIONS) (ss_mem ss_rd0) = true
/\ forallb (fun r1 => forallb (ext_chk r1) RT_REGIONS) (ss_mem S_RDn) = true
/\ forallb (fun r1 => forallb (ext_chk r1) RT_REGIONS) (ss_mem S_RD') = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition LT77 (j : nat) : bool := (j <? 77)%nat.
Lemma reabs_chk_RW : reabs_check LT77 S_Wa RW_regs RW_facts = true /\ reabs_check LT77 S_Wb RW_regs RW_facts = true
/\ fact_obls LT77 RW_facts = [(A_WANT, fact_want)]
/\ ss_mem S_Wa = LH_mem /\ ss_mem S_Wb = LH_mem /\ ss_pc S_Wa = RWPC /\ ss_pc S_Wb = RWPC
/\ mem_atoms_lt 77 LH_mem = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma S_RE_shape : ss_pc S_RE = 0x9c078 /\ ss_resv S_RE = None /\ ss_atoms_lt A_N S_RE = true
/\ sr_get (ss_regs S_RE) 17%bv = SLit 63 /\ sr_get (ss_regs S_RE) 10%bv = SLit 3
/\ sr_get (ss_regs S_RE) 11%bv = SLit RS_LO /\ sr_get (ss_regs S_RE) 12%bv = SOff A_WANT 0.
Proof. vm_compute. repeat split; reflexivity. Qed.


Definition S_DIR : sstate := Eval vm_compute in (run_lp (resume S_RE (SLit (2 ^ 64 - 21)) (ss_mem S_RE) (ss_facts S_RE))).

Lemma S_DIR_facts : ss_pc S_DIR = A_icpt_fprintf /\ sr_get (ss_regs S_DIR) 10%bv = SLit 0xa6750 /\ sr_get (ss_regs S_DIR) 11%bv = SLit 0x1d7e2
/\ sr_get (ss_regs S_DIR) 12%bv = SOff 2 0 /\ sr_get (ss_regs S_DIR) 1%bv = SLit 0x80d70 /\ sr_get (ss_regs S_DIR) 2%bv = SOff 0 (-128)
/\ ss_resv S_DIR = None /\ skeleton (ss_mem S_DIR) = skeleton LH_mem.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rs_win_check : win_check (ss_mem S_RE) RS_LO 65536 = true /\ seg_win_check trasegs RS_LO (Z.to_nat 65536) = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma skel_iter : skeleton (ss_mem S_RE) = skeleton LH_mem /\ skeleton (ss_mem S_CHK) = skeleton LH_mem /\ skeleton (ss_mem S_CHK') = skeleton LH_mem
/\ skeleton (ss_mem S_CP) = skeleton LH_mem /\ skeleton (ss_mem S_CL) = skeleton LH_mem /\ skeleton (ss_mem S_HDR) = skeleton LH_mem
/\ skeleton (ss_mem S_Wa) = skeleton LH_mem /\ skeleton (ss_mem S_Wb) = skeleton LH_mem.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma wbs_iter : wr_below_sp (ss_facts S_RE) LH_mem = true /\ wr_below_sp (ss_facts S_CHK) (ss_mem S_RE) = true
/\ wr_below_sp (ss_facts S_CP) (ss_mem S_CHK') = true /\ wr_below_sp (ss_facts S_CL) (ss_mem S_RE) = true
/\ wr_below_sp (ss_facts S_HDR) (ss_mem S_CL) = true /\ wr_below_sp (ss_facts S_DIR) (ss_mem S_RE) = true
/\ wr_below_sp (ss_facts S_Wa) LH_mem = true /\ wr_below_sp (ss_facts S_Wb) LH_mem = true
/\ wr_below_sp (ss_facts S_T) (ss_mem S_CPp) = true /\ wr_below_sp (ss_facts S_RDn) (ss_mem S_CPp) = true
/\ wr_below_sp (ss_facts S_G) (ss_mem S_CPp) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma win_ok_iter : forallb drv_win_ok LH_mem = true /\ forallb drv_win_ok (ss_mem S_RE) = true /\ forallb drv_win_ok (ss_mem S_CHK') = true
/\ forallb drv_win_ok (ss_mem S_CPp) = true /\ forallb drv_win_ok (ss_mem S_CL) = true.
Proof. repeat split; reflexivity. Qed.
Lemma S_T_shape : ss_mem S_T = ss_mem S_CPp /\ ss_mem S_RDn = ss_mem S_CPp /\ ss_mem S_G = ss_mem S_CPp /\ ss_resv S_T = None
/\ ss_resv S_RDn = None /\ ss_resv S_G = None /\ ss_pc S_CPp = RA_CP /\ ss_resv S_CPp = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma wbs_iter2 : wr_below_sp (ss_facts S_RW) LH_mem = true /\ wr_below_sp RD_facts LH_mem = true
/\ wr_below_sp (ss_facts S_T) (ss_mem S_CPp) = true /\ wr_below_sp (ss_facts S_RDn) (ss_mem S_CPp) = true
/\ wr_below_sp (ss_facts S_G) (ss_mem S_CPp) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
