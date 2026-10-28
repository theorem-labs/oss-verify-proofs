(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YK0v YK02 YQ0k YN06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YP0b YO2i YO2n.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO0j UO1s UO1u.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition PS_RAS : Z := ubs2_A_alloc_slot + 0x3e0.
Definition PS_RAE : Z := ubs2_A_alloc_slot + 0x410.
Definition PS_ZL : Z := ubs2_A_alloc_slot + 0x438.
Definition PS_ZE : Z := ubs2_A_alloc_slot + 0x448.
Definition DEB : Z := ubs2_D_debruijn32.
Definition R_tabs : region := mkRegion None DEB (DEB + 155) 0 0 [mkChunk DEB (CImg 155)].
Definition ssN1 (k : Z) : sstate :=
let ss := add_cond ss_g4 C_nest in
add_alias (mkSS (ss_pc ss) (ss_regs ss) (R_tabs :: ss_mem ss) None
(mkFacts ((62%nat, mkAF (16 * k) (16 * k) 4) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))))
(SAlu ALU_SRL (SOff 62 0) (SLit 4)) (SLit k).
Definition nrun_ (ss : sstate) : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL ubs2_A_alloc_slot ss).
Definition strip (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) None (ss_facts (add_cond ss_g4 C_nest)).
Definition ss_NC15 : sstate := Eval vm_compute in strip (nrun_ (ssN1 30)).
Definition ss_NC19 : sstate := Eval vm_compute in strip (nrun_ (ssN1 54)).
Definition ss_NC23 : sstate := Eval vm_compute in strip (nrun_ (ssN1 126)).
Definition ss_NC (j : Z) : sstate := if j =? 15 then ss_NC15 else if j =? 19 then ss_NC19 else ss_NC23.
Definition jof (k : Z) : Z := if k <? 32 then 15 else if k <? 64 then 19 else 23.
Lemma run_N1 : forall k, In k [28; 30; 54; 56; 60; 62; 120; 124; 125; 126] ->
sym_run_toN ubs2segs ubs2tbl FUEL ubs2_A_alloc_slot (ssN1 k) =
(mkSS ubs2_A_alloc_slot (ss_regs (ss_NC (jof k))) (ss_mem (ss_NC (jof k))) None (ss_facts (ssN1 k)), RS_running).
Proof.
intros k Hk. cbn in Hk.
destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma NC_regs : forall j, j = 15 \/ j = 19 \/ j = 23 ->
regs_at (ss_NC j) [1; 2; 4; 10; 11; 18; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SLit PS_RAS; SOff 2 (-144); SLit TP; SLit j; SOff 62 12; SLit j; SOff 10 0; SOff 40 0; SOff 61 0; SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0;
SAlu ALU_SLL (SOff 35 0) (SLit 4); SLit SCT; SOff 26 0; SOff 27 0]
/\ ss_mem (ss_NC j) = R_tabs :: ss_mem ss_g4 /\ ss_pc (ss_NC j) = ubs2_A_alloc_slot.
Proof. intros j [->|[->| ->]]; vm_compute; repeat split; reflexivity. Qed.
Definition NR_JUNK : list reg := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition F_idx : afact := mkAF 0 31 0.
Definition F_hg : afact := mkAF 4096 (CEIL_MAX - 40) 3.
Definition R_hj (j : Z) : region := mkRegion None (LOCK + 88 + 8 * j) (LOCK + 96 + 8 * j) 0 0 [mkChunk (LOCK + 88 + 8 * j) (CVal 8 (SOff 80 0))].
Definition R_ctrN : region := mkRegion None (LOCK + 20) (LOCK + 24) 0 0 [mkChunk (LOCK + 20) (CVal 4 (SOff 81 0))].
Definition mem_NR : smem := R_mslot :: tl (ss_mem ss_g4) ++ [R_tabs].
Definition facts_NR : facts := mkFacts ((64%nat, F_idx) :: (80%nat, F_hg) :: (81%nat, F_ctr) :: f_atoms (ss_facts ss_g4)) (f_conds (ss_facts ss_g4)) [].
Definition facts_NRf : facts := mkFacts (f_atoms (ss_facts ss_g4)) (f_conds (ss_facts ss_g4)) [].
Definition regs_NR : list sv := Eval vm_compute in ss_regs (junk_regs NR_JUNK 65 ss_NC15).
Definition ss_NRf : sstate := mkSS PS_RAS (sr_set (sr_set regs_NR 10 (SLit (2 ^ 64 - 1))) 18 (SOff 80 0)) mem_NR None facts_NRf.
Definition ss_NRs (j : Z) : sstate := mkSS PS_RAS (sr_set (sr_set regs_NR 10 (SOff 64 0)) 18 (SLit j)) (R_hj j :: R_ctrN :: mem_NR) None facts_NR.

Definition NRf_JUNK : list reg := NR_JUNK ++ [18%bv].
Lemma NR_shapes : forall j, j = 15 \/ j = 19 \/ j = 23 ->
ss_regs (junk_regs NR_JUNK 65 (mkSS PS_RAS (sr_set (ss_regs (ss_NC j)) 10 (SOff 64 0)) [] None (mkFacts [] [] []))) = ss_regs (ss_NRs j)
/\ ss_regs (junk_regs NRf_JUNK 65 (mkSS PS_RAS (sr_set (ss_regs (ss_NC j)) 10 (SLit (2 ^ 64 - 1))) [] None (mkFacts [] [] []))) = ss_regs ss_NRf
/\ regs_atoms_lt 64 (ss_regs (ss_NC j)) = true
/\ ss_mem (ss_NRs j) = [R_hj j; R_ctrN; R_mslot; R_frame; R_got; R_guard; R_pgsz; R_tabs] /\ ss_mem ss_NRf = [R_mslot; R_frame; R_got; R_guard; R_pgsz; R_tabs]
/\ f_conds facts_NR = [mkAC BC_EQ (SOff 34 0) (SLit 0)] /\ f_conds facts_NRf = f_conds facts_NR
/\ ss_facts (ssN1 (if j =? 15 then 30 else if j =? 19 then 54 else 126)) = ss_facts (ssN1 (if j =? 15 then 30 else if j =? 19 then 54 else 126)).
Proof. intros j [->|[->| ->]]; vm_compute; repeat split; reflexivity. Qed.
Lemma facts_g4 : forall k, ss_facts (ssN1 k) = mkFacts ((62%nat, mkAF (16 * k) (16 * k) 4) :: f_atoms (ss_facts ss_g4)) (C_nest :: f_conds (ss_facts ss_g4)) [(SAlu ALU_SRL (SOff 62 0) (SLit 4), SLit k)]
/\ facts_NR = mkFacts ((64%nat, F_idx) :: (80%nat, F_hg) :: (81%nat, F_ctr) :: f_atoms (ss_facts ss_g4)) (f_conds (ss_facts ss_g4)) []
/\ facts_atoms_lt 64 facts_NRf = true.
Proof. intros k. split; [reflexivity|]. split; [reflexivity|]. vm_compute. reflexivity. Qed.
Definition ss_nf0 : sstate := Eval vm_compute in run_ ss_NRf.
Lemma run_NRf : sym_runN ubs2segs ubs2tbl FUEL ss_NRf = (ss_nf0, RS_stopped (SR_load None (LOCK + 24))). Proof. vm_compute. reflexivity. Qed.
Definition ss_NF1 : sstate := Eval vm_compute in mkSS (ss_pc ss_nf0) (ss_regs ss_nf0) (R_fmh :: ss_mem ss_nf0) None (addfact 87 F_ptr0 (ss_facts ss_nf0)).
Definition ss_nf1 : sstate := Eval vm_compute in run_ ss_NF1.
Lemma run_NF1 : sym_runN ubs2segs ubs2tbl FUEL ss_NF1 = (ss_nf1, RS_stopped (SR_branch BC_EQ (SOff 87 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition ss_nfeE : sstate := Eval vm_compute in run_ (add_cond ss_nf1 C_fe).
Lemma run_nfe : sym_runN ubs2segs ubs2tbl FUEL (add_cond ss_nf1 C_fe) = (ss_nfeE, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition ss_nf2 : sstate := Eval vm_compute in run_ (add_cond ss_nf1 C_fne).
Lemma run_nfne : sym_runN ubs2segs ubs2tbl FUEL (add_cond ss_nf1 C_fne) = (ss_nf2, RS_stopped (SR_load (Some 87%nat) 0)). Proof. vm_compute. reflexivity. Qed.
Definition ss_NF2 : sstate := Eval vm_compute in mkSS (ss_pc ss_nf2) (ss_regs ss_nf2) (R_hd :: R_hp :: ss_mem ss_nf2) None (addfact 88 F_ptr0 (ss_facts ss_nf2)).
Definition ss_nfneE : sstate := Eval vm_compute in run_ ss_NF2.
Lemma run_NF2 : sym_runN ubs2segs ubs2tbl FUEL ss_NF2 = (ss_nfneE, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.





Definition erun_ (ss : sstate) : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL ubs2_A_enframe ss).
Definition ss_NE15 : sstate := Eval vm_compute in erun_ (ss_NRs 15).
Definition ss_NE19 : sstate := Eval vm_compute in erun_ (ss_NRs 19).
Definition ss_NE23 : sstate := Eval vm_compute in erun_ (ss_NRs 23).
Definition ss_NE (j : Z) : sstate := if j =? 15 then ss_NE15 else if j =? 19 then ss_NE19 else ss_NE23.
Lemma run_NRs : forall j, j = 15 \/ j = 19 \/ j = 23 -> sym_run_toN ubs2segs ubs2tbl FUEL ubs2_A_enframe (ss_NRs j) = (ss_NE j, RS_running).
Proof. intros j [->|[->| ->]]; vm_compute; reflexivity. Qed.
Definition csz (j : Z) : Z := if j =? 15 then 496 else if j =? 19 then 1008 else 2032.
Lemma NE_regs : forall j, j = 15 \/ j = 19 \/ j = 23 ->
regs_at (ss_NE j) [1; 2; 4; 10; 11; 12; 13; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SLit PS_RAE; SOff 2 (-144); SLit TP; SOff 80 0; SOff 64 0; SLit (csz j - 4); SExt true 32 (SOff 81 0);
SOff 10 0; SOff 40 0; SOff 61 0; SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0; SAlu ALU_SLL (SOff 35 0) (SLit 4); SLit SCT; SOff 26 0; SOff 27 0]
/\ ss_mem (ss_NE j) = ss_mem (ss_NRs j) /\ ss_pc (ss_NE j) = ubs2_A_enframe /\ ss_facts (ss_NE j) = facts_NR /\ ss_resv (ss_NE j) = None.
Proof. intros j [->|[->| ->]]; vm_compute; repeat split; reflexivity. Qed.
Definition NE_JUNK : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18]%bv.
Definition F_q : afact := mkAF 4096 (CEIL_MAX - 16) 4.
Definition F_h16 : afact := mkAF 0 65535 0.
Definition F_b8 : afact := mkAF 0 255 0.
Definition R_q : region := mkRegion (Some 82%nat) (-3) 9 (-3) 9 [mkChunk (-3) (CVal 1 (SOff 64 0)); mkChunk (-2) (CVal 2 (SOff 94 0)); mkChunk 8 (CVal 1 (SOff 95 0))].
Definition facts_NF : facts := addfact 95 F_b8 (addfact 94 F_h16 (addfact 82 F_q facts_NR)).
Definition ss_NF : sstate := Eval vm_compute in
junk_regs NE_JUNK 83 (mkSS PS_RAE (sr_set (ss_regs ss_NE15) 10 (SOff 82 0)) (R_q :: mem_NR) None facts_NF).

Definition ss_nz : sstate := Eval vm_compute in run_ ss_NF.
Lemma run_NF : sym_runN ubs2segs ubs2tbl FUEL ss_NF = (ss_nz, RS_stopped (SR_store (Some 82%nat) 12)). Proof. vm_compute. reflexivity. Qed.
Lemma ss_nz_pc : ss_pc ss_nz = PS_ZL. Proof. reflexivity. Qed.
Lemma nz_regs : regs_at ss_nz [10; 11; 12; 24]%bv = [SOff 82 0; SOff 61 1; SOff 82 12; SAlu ALU_SLL (SOff 35 0) (SLit 4)]
/\ ss_mem ss_nz = mkRegion (Some 82%nat) (-3) 9 (-3) 9 [mkChunk (-3) (CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 64 0) (SLit 31)) (SLit 192))); mkChunk (-2) (CVal 2 (SOff 94 0)); mkChunk 8 (CVal 1 (SOff 95 0))]
:: mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 32 (CVal 8 (SLit 0)); mkChunk 0 (CVal 8 (SLit 0)); mkChunk 8 (CVal 8 (SLit 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SLit 0))]
:: tl mem_NR
/\ ss_facts ss_nz = facts_NF.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition ss_NL : sstate := Eval vm_compute in mkSS PS_ZE (sr_set (sr_set (ss_regs ss_nz) 11 (SLit 0)) 12 (SOff 96 0)) (ss_mem ss_nz) None (ss_facts ss_nz).

Definition ss_nt0 : sstate := Eval vm_compute in run_ ss_NL.
Lemma run_NL : sym_runN ubs2segs ubs2tbl FUEL ss_NL = (ss_nt0, RS_stopped (SR_load (Some 33%nat) 472)). Proof. vm_compute. reflexivity. Qed.
Definition R_useN : region := mkRegion (Some 33%nat) 472 480 472 480 [mkChunk 472 (CVal 8 (SOff 97 0))].
Definition F_useN : afact := mkAF 0 (2 ^ 48 - 1) 0.
Definition ss_NT : sstate := Eval vm_compute in mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_useN :: R_actW :: ss_mem ss_nt0) None (addfact 97 F_useN (ss_facts ss_nt0)).
Lemma NT_shape : ss_NT = mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_useN :: R_actW :: ss_mem ss_nt0) None (addfact 97 F_useN (ss_facts ss_nt0)) /\ ss_mem ss_nt0 = ss_mem ss_nz /\ ss_facts ss_nt0 = ss_facts ss_nz /\ ss_pc ss_nt0 = PS_TL.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition ss_nE : sstate := Eval vm_compute in run_ ss_NT.
Lemma run_NT : sym_runN ubs2segs ubs2tbl FUEL ss_NT = (ss_nE, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.

Definition AVAILN : sv := SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 61 (-1))) (SLit (-1)).
Definition BITSN : sv := SAlu ALU_ADD (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 10 0) (SLit 6)) (SAlu ALU_AND (SOff 61 (-1)) (SLit 31))) (SLit 0)) (SLit 32).
Lemma nE_facts : final_regs_of ss_nE = final_regs_of ss_kE /\
firstn 4 (ss_mem ss_nE) =
[mkRegion (Some 33%nat) 472 480 472 480 [mkChunk 472 (CVal 8 (SAlu ALU_ADD (SOff 61 0) (SOff 97 0)))];
mkRegion (Some 33%nat) 88 96 88 96 [mkChunk 88 (CVal 8 (SOff 40 0))];
mkRegion (Some 82%nat) (-3) 9 (-3) 9 [mkChunk 8 (CVal 1 (SAlu ALU_OR (SAlu ALU_AND (SOff 95 0) (SLit 224)) (SAlu ALU_AND (SOff 61 (-1)) (SLit 31)))); mkChunk 0 (CVal 8 (SOff 40 0));
mkChunk (-3) (CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 64 0) (SLit 31)) (SLit 192))); mkChunk (-2) (CVal 2 (SOff 94 0))];
mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 24 (CVal 4 (SAlu ALU_ADD (SExt true 32 AVAILN) (SLit (-1))));
mkChunk 32 (CVal 8 BITSN); mkChunk 16 (CVal 8 (SOff 82 0));
mkChunk 28 (CVal 4 (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 61 (-1))) (SAlu ALU_XOR (SExt true 32 AVAILN) (SLit (-1)))))]]
/\ skipn 4 (ss_mem ss_nE) = tl mem_NR
/\ (exists rstk, nth_error (ss_mem ss_nE) 4 = Some rstk /\ r_base rstk = Some 2%nat /\ r_wlo rstk = - ASF /\ r_whi rstk = 0)
/\ nth_error (ss_mem ss_nE) 6 = Some R_guard.
Proof. vm_compute. repeat (split; [reflexivity|]). split; [eexists; repeat split; reflexivity|]. reflexivity. Qed.
End a.
