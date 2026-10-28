(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04 YL09 YL02 YL04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1y AD24.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition A_H1 : Z := 0x8010c.
Definition A_P : Z := 0x80118.
Definition A_HDR_RET : Z := 0x801e4.
Definition cond_SH : acond := mkAC BC_GEU (SLit 5) (SOff A_LEN 0).
Definition cond_H6 : acond := mkAC BC_LTU (SLit 5) (SOff A_LEN 0).
Definition S_SHORT : sstate := Eval vm_compute in run_lp (add_cond S_HDR cond_SH).
Definition blkreg6 : YP09.region := YP09.mkRegion (Some A_BUF) 0 6 0 0 [mkChunk 0 (CData 2 0 6)].
Definition S_H0c : sstate := Eval vm_compute in (add_cond S_HDR cond_H6).
Definition S_H6 : sstate := mkSS (ss_pc S_H0c) (ss_regs S_H0c) (ss_mem S_H0c ++ [blkreg6]) None (ss_facts S_H0c).
Definition S_H1 : sstate := Eval vm_compute in run_lp S_H6.
Definition cond_OV : acond := mkAC BC_LTU (SOff A_LEN 0) sv_cl6.
Definition cond_OK : acond := mkAC BC_GEU (SOff A_LEN 0) sv_cl6.
Definition S_OVR : sstate := Eval vm_compute in run_lp (add_cond S_H1 cond_OV).
Definition S_P : sstate := Eval vm_compute in run_lp (add_cond S_H1 cond_OK).
Lemma S_SHORT_eq : run_lp (add_cond S_HDR cond_SH) = S_SHORT. Proof. vm_compute. reflexivity. Qed.
Lemma S_H1_eq : run_lp S_H6 = S_H1. Proof. vm_compute. reflexivity. Qed.
Lemma S_OVR_eq : run_lp (add_cond S_H1 cond_OV) = S_OVR. Proof. vm_compute. reflexivity. Qed.
Lemma S_P_eq : run_lp (add_cond S_H1 cond_OK) = S_P. Proof. vm_compute. reflexivity. Qed.
Lemma S_SHORT_regs : ss_pc S_SHORT = A_icpt_fwrite /\ sr_get (ss_regs S_SHORT) 10%bv = SLit 0x1f889 /\ sr_get (ss_regs S_SHORT) 11%bv = SLit 31
/\ sr_get (ss_regs S_SHORT) 12%bv = SLit 1 /\ sr_get (ss_regs S_SHORT) 13%bv = SLit 0xa2578 /\ sr_get (ss_regs S_SHORT) 1%bv = SLit A_HDR_RET
/\ sr_get (ss_regs S_SHORT) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs S_SHORT) 8%bv = SLit 2 /\ sr_get (ss_regs S_SHORT) 9%bv = SOff A_BUF 0
/\ ss_resv S_SHORT = None /\ ss_mem S_SHORT = ss_mem S_HDR.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_OVR_regs : ss_pc S_OVR = A_icpt_fwrite /\ sr_get (ss_regs S_OVR) 10%bv = SLit 0x1586a /\ sr_get (ss_regs S_OVR) 11%bv = SLit 31
/\ sr_get (ss_regs S_OVR) 12%bv = SLit 1 /\ sr_get (ss_regs S_OVR) 13%bv = SLit 0xa2578 /\ sr_get (ss_regs S_OVR) 1%bv = SLit A_HDR_RET
/\ sr_get (ss_regs S_OVR) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs S_OVR) 8%bv = SLit 2 /\ sr_get (ss_regs S_OVR) 9%bv = SOff A_BUF 0
/\ ss_resv S_OVR = None /\ ss_mem S_OVR = ss_mem S_H6.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_H1_regs : ss_pc S_H1 = A_H1 /\ sr_get (ss_regs S_H1) 10%bv = sv_cl6 /\ sr_get (ss_regs S_H1) 18%bv = sv_cl
/\ sr_get (ss_regs S_H1) 19%bv = SOff A_LEN 0 /\ sr_get (ss_regs S_H1) 21%bv = sv_b1s /\ sr_get (ss_regs S_H1) 9%bv = SOff A_BUF 0
/\ ss_resv S_H1 = None /\ ss_mem S_H1 = ss_mem S_H6 /\ ss_pc S_H0c = A_HDR /\ ss_resv S_H0c = None /\ ss_mem S_H0c = ss_mem S_HDR.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_P_regs : ss_pc S_P = A_P /\ sr_get (ss_regs S_P) 8%bv = SOff A_BUF 2 /\ sr_get (ss_regs S_P) 9%bv = SOff A_BUF 0
/\ sr_get (ss_regs S_P) 10%bv = SAlu ALU_ADD (SOff A_BUF 2) sv_cl /\ sr_get (ss_regs S_P) 18%bv = sv_cl /\ sr_get (ss_regs S_P) 19%bv = SOff A_LEN 0
/\ sr_get (ss_regs S_P) 20%bv = SLit 3 /\ sr_get (ss_regs S_P) 21%bv = sv_b1s /\ sr_get (ss_regs S_P) 22%bv = SLit RS_LO
/\ sr_get (ss_regs S_P) 2%bv = SOff 0 (-128) /\ ss_resv S_P = None /\ ss_mem S_P = ss_mem S_H6.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_H0c_data2 : ss_atoms_pd (fun _ => true) (not_in [2%nat]) S_H0c = true. Proof. vm_compute. reflexivity. Qed.
Lemma blkreg6_wf : regions_wf [blkreg6] = true. Proof. reflexivity. Qed.
Definition hext_chk (r : YP09.region) : bool :=
match r_base r with
| Some 0%nat => (-65536 <=? r_lo r) | Some 6%nat => (0 <=? r_lo r) | None => (r_hi r <=? 0x5fb000) | _ => false
end%bool.
Lemma S_HDR_hext : forallb hext_chk (ss_mem S_HDR) = true. Proof. vm_compute. reflexivity. Qed.
Lemma S_HDR_win_ok : forallb drv_win_ok (ss_mem S_HDR) = true. Proof. reflexivity. Qed.
Lemma S_H6_win_ok : forallb drv_win_ok (ss_mem S_H6) = true. Proof. reflexivity. Qed.
Lemma img_sub_SHORT : submem IMG_REGIONS (ss_mem S_SHORT).
Proof.
change (ss_mem S_SHORT) with (firstn 3 (ss_mem S_SHORT) ++ IMG_REGIONS ++ skipn 36 (ss_mem S_SHORT)).
do 3 apply submem_drop. induction IMG_REGIONS as [|r rs IH]; cbn; [constructor|]. apply submem_keep; [repeat split; try lia; auto | exact IH].
Qed.
Lemma img_sub_OVR : submem IMG_REGIONS (ss_mem S_OVR).
Proof.
change (ss_mem S_OVR) with (firstn 3 (ss_mem S_OVR) ++ IMG_REGIONS ++ skipn 36 (ss_mem S_OVR)).
do 3 apply submem_drop. induction IMG_REGIONS as [|r rs IH]; cbn; [constructor|]. apply submem_keep; [repeat split; try lia; auto | exact IH].
Qed.
Lemma wbs_SHORT : wr_below_sp (ss_facts S_SHORT) (ss_mem S_HDR) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wbs_H1 : wr_below_sp (ss_facts S_H1) (ss_mem S_H6) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wbs_OVR : wr_below_sp (ss_facts S_OVR) (ss_mem S_H6) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wbs_P : wr_below_sp (ss_facts S_P) (ss_mem S_H6) = true. Proof. vm_compute. reflexivity. Qed.
