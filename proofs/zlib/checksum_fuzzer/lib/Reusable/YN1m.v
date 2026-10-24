(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YN2e YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN0j YN1k YN1l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_MK : sstate := Eval vm_compute in run_ ss_MM.
Lemma run_MM : sym_runN src0segs src0tbl FUEL ss_MM = (ss_MK, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Lemma ss_MK_pc : ss_pc ss_MK = src0_A_mmap + 0xc4. Proof. reflexivity. Qed.
Lemma MK_regs : regs_at ss_MK [2; 10; 11; 12; 13; 14; 15; 17]%bv = [SOff 2 (-208); SLit 0; SOff 81 0; SLit 3; SLit 34; SLit 18446744073709551615; SLit 0; SLit 222].
Proof. vm_compute. reflexivity. Qed.
Definition R_errnoS : region := mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [].
Definition R_mslot : region := mkRegion (Some 40%nat) 0 40 0 40
[mkChunk 0 (CVal 8 (SLit 0)); mkChunk 8 (CVal 8 (SLit 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))].
Definition F_map : afact := mkAF 4096 (CEIL_MAX - 4096) 12.
Definition R_grp : region := mkRegion (Some 86%nat) 0 16 0 16 [mkChunk 0 (CZero 16)].
Definition F_ptr0 : afact := mkAF 0 (CEIL_MAX - 40) 3.
Definition R_fmh : region := mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 87 0))].
Definition R_hd : region := mkRegion (Some 87%nat) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff 88 0))].
Definition R_hp : region := mkRegion (Some 88%nat) 8 16 8 16 [].
Definition R_ctr : region := mkRegion None (LOCK + 20) (LOCK + 24) (LOCK + 20) (LOCK + 24) [mkChunk (LOCK + 20) (CVal 4 (SOff 89 0))].
Definition F_ctr : afact := mkAF 0 (2 ^ 32 - 1) 0.
Definition R_useW : region := mkRegion (Some 33%nat) 472 480 472 480 [mkChunk 472 (CVal 8 (SOff 56 0))].
Definition R_actW : region := mkRegion (Some 33%nat) 88 96 88 96 [mkChunk 88 (CVal 8 (SOff 34 0))].
Definition addfact (n : nat) (f : afact) (G : facts) : facts := mkFacts ((n, f) :: f_atoms G) (f_conds G) (f_alias G).
Definition ss_Kf : sstate := Eval vm_compute in resume ss_MK (SLit (2 ^ 64 - 12)) (R_errnoS :: R_mslot :: ss_mem ss_MK) (ss_facts ss_MK).
Definition ss_fm0 : sstate := Eval vm_compute in run_ ss_Kf.
Lemma run_Kf : sym_runN src0segs src0tbl FUEL ss_Kf = (ss_fm0, RS_stopped (SR_load None (LOCK + 24))). Proof. vm_compute. reflexivity. Qed.
Definition ss_FM1 : sstate := Eval vm_compute in mkSS (ss_pc ss_fm0) (ss_regs ss_fm0) (R_fmh :: ss_mem ss_fm0) None (addfact 87 F_ptr0 (ss_facts ss_fm0)).
Definition ss_fm1 : sstate := Eval vm_compute in run_ ss_FM1.
Lemma run_FM1 : sym_runN src0segs src0tbl FUEL ss_FM1 = (ss_fm1, RS_stopped (SR_branch BC_EQ (SOff 87 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition C_fe : acond := mkAC BC_EQ (SOff 87 0) (SLit 0).
Definition C_fne : acond := mkAC BC_NE (SOff 87 0) (SLit 0).
Definition ss_feE : sstate := Eval vm_compute in run_ (add_cond ss_fm1 C_fe).
Lemma run_fe : sym_runN src0segs src0tbl FUEL (add_cond ss_fm1 C_fe) = (ss_feE, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition ss_fm2 : sstate := Eval vm_compute in run_ (add_cond ss_fm1 C_fne).
Lemma run_fne : sym_runN src0segs src0tbl FUEL (add_cond ss_fm1 C_fne) = (ss_fm2, RS_stopped (SR_load (Some 87%nat) 0)). Proof. vm_compute. reflexivity. Qed.
Definition ss_FM2 : sstate := Eval vm_compute in mkSS (ss_pc ss_fm2) (ss_regs ss_fm2) (R_hd :: R_hp :: ss_mem ss_fm2) None (addfact 88 F_ptr0 (ss_facts ss_fm2)).
Definition ss_fneE : sstate := Eval vm_compute in run_ ss_FM2.
Lemma run_FM2 : sym_runN src0segs src0tbl FUEL ss_FM2 = (ss_fneE, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Lemma ss_feE_pc : ss_pc ss_feE = PS_JR. Proof. reflexivity. Qed.
Lemma ss_fneE_pc : ss_pc ss_fneE = PS_JR. Proof. reflexivity. Qed.
Definition ss_Kg : sstate := Eval vm_compute in
resume ss_MK (SOff 86 0) (R_grp :: R_mslot :: ss_mem ss_MK) (addfact 86 F_map (ss_facts ss_MK)).
Definition ss_kg0 : sstate := Eval vm_compute in run_ ss_Kg.
Definition C_mapok : acond := mkAC BC_NE (SAlu ALU_OR (SLit 0) (SAlu ALU_XOR (SOff 86 0) (SLit (-1)))) (SLit 0).
Lemma run_Kg : sym_runN src0segs src0tbl FUEL ss_Kg = (ss_kg0, RS_stopped (SR_branch (ac_c C_mapok) (ac_a C_mapok) (ac_b C_mapok))). Proof. vm_compute. reflexivity. Qed.
Definition ss_kg1 : sstate := Eval vm_compute in run_ (add_cond ss_kg0 C_mapok).
Lemma run_kg0 : sym_runN src0segs src0tbl FUEL (add_cond ss_kg0 C_mapok) = (ss_kg1, RS_stopped (SR_load None (LOCK + 20))). Proof. vm_compute. reflexivity. Qed.
Definition ss_G1 : sstate := Eval vm_compute in mkSS (ss_pc ss_kg1) (ss_regs ss_kg1) (R_ctr :: ss_mem ss_kg1) None (addfact 89 F_ctr (ss_facts ss_kg1)).
Definition ss_kg2 : sstate := Eval vm_compute in run_ ss_G1.
Definition QV : sv := SMd M_DIVU (SLit 4080) (SAlu ALU_SLL (SOff 35 0) (SLit 4)).
Lemma run_G1 : sym_runN src0segs src0tbl FUEL ss_G1 = (ss_kg2, RS_stopped (SR_branch BC_LTU (SOff 82 0) QV)). Proof. vm_compute. reflexivity. Qed.
Definition C_aT : acond := mkAC BC_LTU (SOff 82 0) QV.
Definition C_aF : acond := mkAC BC_GEU (SOff 82 0) QV.
Definition PS_TL : Z := src0_A_alloc_slot + 0x708.
Definition tlrun_ (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL PS_TL ss).
Definition ss_kT3 : sstate := Eval vm_compute in tlrun_ (add_cond ss_kg2 C_aT).
Definition ss_kF3 : sstate := Eval vm_compute in tlrun_ (add_cond ss_kg2 C_aF).
Lemma run_aT : sym_run_toN src0segs src0tbl FUEL PS_TL (add_cond ss_kg2 C_aT) = (ss_kT3, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma run_aF : sym_run_toN src0segs src0tbl FUEL PS_TL (add_cond ss_kg2 C_aF) = (ss_kF3, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition F_aidx : afact := mkAF 0 31 0.
Definition facts_TL : facts := addfact 90 F_aidx (ss_facts ss_kg2).
Definition ss_TL0 : sstate := Eval vm_compute in setfacts facts_TL (junk_regs [12%bv] 90 ss_kT3).
Definition tl_check (ss : sstate) : bool := ss_atoms_lt 90 ss && mergeb ss_TL0 (setfacts facts_TL (junk_regs [12%bv] 90 ss)).
Lemma tl_T : tl_check ss_kT3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tl_F : tl_check ss_kF3 = true. Proof. vm_compute. reflexivity. Qed.
Definition QV0 : sv := SAlu ALU_ADD QV (SLit 0).
Definition AIDX_F : sv := SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU QV0 (SAlu ALU_ADD QV0 (SLit (-1)))) (SLit (-1))) (SAlu ALU_ADD QV0 (SLit (-1))).
Lemma aidx_regs : sr_get (ss_regs ss_kT3) 12 = SOff 82 (-1) /\ sr_get (ss_regs ss_kF3) 12 = AIDX_F /\
sr_get (ss_regs (junk_regs [12%bv] 90 ss_kT3)) 12 = SOff 90 0 /\ sr_get (ss_regs (junk_regs [12%bv] 90 ss_kF3)) 12 = SOff 90 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition swap_useW (m : smem) : smem := R_useW :: List.filter (fun rg => negb (match r_base rg with Some 33%nat => Z.eqb (r_lo rg) 472 | _ => false end)) m.
Definition ss_TL : sstate := Eval vm_compute in mkSS (ss_pc ss_TL0) (ss_regs ss_TL0) (R_actW :: swap_useW (ss_mem ss_TL0)) None (ss_facts ss_TL0).
Definition ss_kE : sstate := Eval vm_compute in run_ ss_TL.
Lemma run_TL : sym_runN src0segs src0tbl FUEL ss_TL = (ss_kE, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Lemma ss_kE_pc : ss_pc ss_kE = PS_JR. Proof. reflexivity. Qed.
Lemma TL_skel : map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) (ss_mem ss_TL0) =
[(None, LOCK + 20, LOCK + 24, LOCK + 20, LOCK + 24); (Some 86%nat, 0, 16, 0, 16); (Some 40%nat, 0, 40, 0, 40); (Some 33%nat, 472, 480, 0, 0); (Some 2%nat, -ASF, 0, -ASF, 0);
(None, GOT, GOT + 8, 0, 0); (None, GUARD, GUARD + 8, 0, 0); (None, LIBC + 48, LIBC + 56, 0, 0)]
/\ ss_mem ss_TL = R_actW :: R_useW :: firstn 3 (ss_mem ss_TL0) ++ skipn 4 (ss_mem ss_TL0).
Proof. vm_compute. split; reflexivity. Qed.
Definition final_regs_of (ss : sstate) : list sv := regs_at ss [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma finals :
final_regs_of ss_feE = [SOff 1 0; SOff 2 0; SOff 3 0; SLit TP; SOff 8 0; SOff 9 0; SLit (2 ^ 64 - 1); SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
final_regs_of ss_fneE = final_regs_of ss_feE /\
final_regs_of ss_kE = [SOff 1 0; SOff 2 0; SOff 3 0; SLit TP; SOff 8 0; SOff 9 0; SLit 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma feE_mem : firstn 3 (ss_mem ss_feE) =
[mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 40 0))];
mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [mkChunk ERRNO (CVal 4 (SLit 12))];
mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))]].
Proof. vm_compute. reflexivity. Qed.
Lemma fneE_mem : firstn 5 (ss_mem ss_fneE) =
[mkRegion (Some 87%nat) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff 40 0))];
mkRegion (Some 88%nat) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff 40 0))];
mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 87 0))];
mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [mkChunk ERRNO (CVal 4 (SLit 12))];
mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 0 (CVal 8 (SOff 88 0)); mkChunk 8 (CVal 8 (SOff 87 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))]].
Proof. vm_compute. reflexivity. Qed.
Definition BITS : sv := SAlu ALU_ADD (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 10 0) (SLit 6)) (SAlu ALU_AND (SOff 82 (-1)) (SLit 31))) (SAlu ALU_AND (SAlu ALU_OR (SLit 0) (SOff 81 0)) (SLit (-4096)))) (SLit 32).
Definition AVAIL0 : sv := SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 90 0)) (SLit (-1)).
Lemma kE_mem : firstn 5 (ss_mem ss_kE) =
[mkRegion (Some 33%nat) 88 96 88 96 [mkChunk 88 (CVal 8 (SOff 40 0))];
mkRegion (Some 33%nat) 472 480 472 480 [mkChunk 472 (CVal 8 (SAlu ALU_ADD (SOff 56 0) (SOff 82 0)))];
mkRegion None (LOCK + 20) (LOCK + 24) (LOCK + 20) (LOCK + 24) [mkChunk (LOCK + 20) (CVal 4 (SAlu ALU_ADD (SExt true 32 (SOff 89 0)) (SLit 1)))];
mkRegion (Some 86%nat) 0 16 0 16 [mkChunk 8 (CVal 1 (SAlu ALU_OR (SLit 0) (SAlu ALU_AND (SOff 90 0) (SLit 31)))); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 9 (CZero 7)];
mkRegion (Some 40%nat) 0 40 0 40
[mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0));
mkChunk 24 (CVal 4 (SAlu ALU_ADD (SExt true 32 AVAIL0) (SLit (-1))));
mkChunk 32 (CVal 8 BITS); mkChunk 16 (CVal 8 (SOff 86 0));
mkChunk 28 (CVal 4 (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 82 (-1))) (SAlu ALU_XOR (SExt true 32 AVAIL0) (SLit (-1)))))]].
Proof. vm_compute. reflexivity. Qed.
End a.
