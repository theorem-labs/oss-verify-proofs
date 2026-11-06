(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFif.v, with its module paths changed; relocated to fuzz_preset asan-ubsan (pin f8f98a95bc52), map sha256 69a6a2e91fb7, checker port_addr_check.py 39e67a7eb166. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0d YB1v YB1q YF0m YF0x YFl0 YFhy YFhz YFi0 YFi4 YFi9 YFid YFie.
Import ListNotations. Open Scope Z_scope.
Definition S_V0 : sstate := Eval vm_compute in runto B_MAPORDIE_PC (arm BC_EQ true (SOff aNCH 0) (SOff aRES 0) S_X).
Definition S_V : sstate := Eval vm_compute in runtoC B_INTERNAL_MMAP_PC_OFF_4 S_V0.
Definition S_V2 : sstate := Eval vm_compute in runtoC B_ALLOCATORSTATS_PC_OFF_45C (mkSS B_INTERNAL_MMAP_PC_OFF_8 (ss_regs S_V) (ss_mem S_V) None (ss_facts S_V)).
Definition S_V3 : sstate := Eval vm_compute in runto B_ALLOCATORSTATS_PC_OFF_278 S_V2.
Definition RES2T : sv := SAlu ALU_ADD (SOff aRES 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff aNCH 0) (SOff aRES 0)) (SLit 1)) (SLit 14)).
Definition dropchunks (lo : Z) (m : smem) : smem :=
map (fun r => if (match YP09.r_base r with None => Z.eqb (YP09.r_lo r) lo | Some _ => false end)
then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r) [] else r) m.
Definition setchunks (lo : Z) (cs : list YP09.chunk) (m : smem) : smem :=
map (fun r => if (match YP09.r_base r with None => Z.eqb (YP09.r_lo r) lo | Some _ => false end)
then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r) cs else r) m.
Definition trimscratch (cut : Z) (m : smem) : smem :=
map (fun r => match YP09.r_base r with
| Some 2%nat => if Z.ltb (YP09.r_lo r) cut
then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(List.filter (fun c => Z.leb cut (YP09.c_off c)) (YP09.r_chunks r))
else r
| _ => r end) m.
Definition sJY : nat := 124.
Definition joinY (ss : sstate) : sstate :=
let ss1 := mkSS (ss_pc ss) (sr_set (ss_regs ss) 12%bv (SOff aQS 0))
(trimscratch (-2416) (setchunks (TFIB_INST + o_sec_reserved) [YP09.mkChunk (TFIB_INST + o_sec_reserved) (CVal 8 RES2T)] (ss_mem ss))) (ss_resv ss) (ss_facts ss) in
addreg R_qs (noconds (forget ss1 sJY [1; 15; 17; 20]%bv)).
Definition S_YJ : sstate := Eval vm_compute in joinY S_Y0.
Lemma S_VY_join : joinY S_V3 = S_YJ. Proof. vm_compute. reflexivity. Qed.
Definition S_ZJ0 : sstate := Eval vm_compute in runto B_ALLOCATORSTATS_PC_OFF_2A4 S_YJ.
Definition S_ZJt : sstate := Eval vm_compute in runto B_ALLOCATORSTATS_PC_OFF_2AC (arm BC_LTU true (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_ZJ0).
Definition S_ZJf : sstate := Eval vm_compute in runto B_ALLOCATORSTATS_PC_OFF_2AC (arm BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_ZJ0).
Definition S_ZJ : sstate := Eval vm_compute in noconds (forget S_ZJt sMX [12]%bv).
Lemma S_ZJ_f : noconds (forget S_ZJf sMX [12]%bv) = S_ZJ. Proof. vm_compute. reflexivity. Qed.
Definition S_ZJ1 : sstate := Eval vm_compute in pin (runto B_ALLOCATORSTATS_PC_OFF_2B4 S_ZJ) 11%bv (SOff aBSL (-104)).
Definition MUTCH : list YP09.chunk :=
[YP09.mkChunk (TFIB_INST + o_sec_mutex) (CVal 1 (SLit 1)); YP09.mkChunk (TFIB_INST + o_sec_mutex + 1) (CVal 1 (SLit 0));
YP09.mkChunk (TFIB_INST + o_sec_mutex + 2) (CVal 2 (SLit 0))].
Definition S_ZJ1s : sstate := Eval vm_compute in
mkSS (ss_pc S_ZJ1) (ss_regs S_ZJ1) (setchunks (TFIB_INST + o_sec_mutex) MUTCH (ss_mem S_ZJ1)) (ss_resv S_ZJ1) (ss_facts S_ZJ1).
Definition S_TJ0 : sstate := Eval vm_compute in runto B_ALLOCTYPE_PC_OFF_2C4 S_ZJ1s.
Definition T_J : sstate := Eval vm_compute in arm BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SAlu ALU_ADD (SOff 10 6144) (SOff aMAP 0)) S_TJ0.
Definition T_K : sstate := Eval vm_compute in arm BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0) (runto B_ALLOCTYPE_PC_OFF_2EC T_J).
Definition T_PD : sstate := Eval vm_compute in runto B_STACKDEPOTPUT_STACKTRACE_PC T_K.
Definition trs_D : smem := match ss_mem T_PD with rq :: rm :: rb :: r1 :: rest => rq :: rm :: rb :: trim_lo r1 (-2272) :: rest | l => l end.
Definition T_2 : sstate := Eval vm_compute in addreg R_scr2 (ss_after_call T_PD trs_D sD1 B_ALLOCTYPE_PC_OFF_3AC).
Definition T_M0 : sstate := Eval vm_compute in runto B_ALLOCTYPE_PC_OFF_3E0 T_2.
Definition T_Ma : sstate := Eval vm_compute in runto B_ALLOCTYPE_PC_OFF_418 (arm BC_LTU true (SOff aMAP 4096) (SOff aSB 0) T_M0).
Definition T_Mb : sstate := Eval vm_compute in runto B_ALLOCTYPE_PC_OFF_418 (arm BC_GEU true (SOff aMAP 4096) (SOff aSB 137438953472) (runto B_ALLOCTYPE_PC_OFF_3F0 (arm BC_LTU false (SOff aMAP 4096) (SOff aSB 0) T_M0))).
Definition T_N : sstate := Eval vm_compute in noconds (forget T_Ma sGA [11]%bv).
Lemma T_N_b : noconds (forget T_Mb sGA [11]%bv) = T_N. Proof. vm_compute. reflexivity. Qed.
Definition T_L3 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_58 T_N.
Definition T_L3l : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_240 (armR BC_GEU true 14 10 T_L3).
Definition T_L3lo : sstate := Eval vm_compute in runto B_MEMSET_PC (armR BC_GEU true 14 11 T_L3l).
Definition T_L3h : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_98 (armR BC_GEU false 14 10 T_L3).
Definition T_L3h2 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_240 (armR BC_LTU true 7 10 T_L3h).
Definition T_L3h3 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_280 (armR BC_GEU false 14 11 T_L3h2).
Definition T_L3hi : sstate := Eval vm_compute in runto B_MEMSET_PC (armR BC_GEU false 5 11 T_L3h3).
Definition T_M3 : sstate := Eval vm_compute in psJ sL3 T_L3lo.
Lemma T_M3_h : psJ sL3 T_L3hi = T_M3. Proof. vm_compute. reflexivity. Qed.
Definition T_P3 : sstate := Eval vm_compute in ss_after_stretch T_M3 (ss_mem T_M3) sM3 CLOB_MS B_ALLOCTYPE_PC_OFF_484.
Definition T_P4 : sstate := Eval vm_compute in pin (pin T_P3 22%bv (SOff aUE 0)) 8%bv (SOff aMS (-4096)).
Definition T_P5 : sstate := Eval vm_compute in pin (runto B_ALLOCTYPE_PC_OFF_494 T_P4) 11%bv (SOff aRL 0).
Definition T_L4 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_58 T_P5.
Definition T_L4l : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_240 (armR BC_GEU true 14 10 T_L4).
Definition T_L4lo : sstate := Eval vm_compute in runto B_MEMSET_PC (armR BC_GEU true 14 11 T_L4l).
Definition T_L4h : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_98 (armR BC_GEU false 14 10 T_L4).
Definition T_L4h2 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_240 (armR BC_LTU true 7 10 T_L4h).
Definition T_L4h3 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_280 (armR BC_GEU false 14 11 T_L4h2).
Definition T_L4hi : sstate := Eval vm_compute in runto B_MEMSET_PC (armR BC_GEU false 5 11 T_L4h3).
Definition T_M4 : sstate := Eval vm_compute in psJ sL4 T_L4lo.
Lemma T_M4_h : psJ sL4 T_L4hi = T_M4. Proof. vm_compute. reflexivity. Qed.
Definition T_P6 : sstate := Eval vm_compute in ss_after_stretch T_M4 (ss_mem T_M4) sM4 CLOB_MS B_ALLOCTYPE_PC_OFF_498.
Definition T_P7 : sstate := Eval vm_compute in pin (runto B_ALLOCTYPE_PC_OFF_4A4 T_P6) 22%bv (SOff aN8DS 0).
Definition T_L5 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_58 T_P7.
Definition T_L5l : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_240 (armR BC_GEU true 14 10 T_L5).
Definition T_L5lo : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_2A8 (armR BC_GEU true 14 11 T_L5l).
Definition T_L5h : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_98 (armR BC_GEU false 14 10 T_L5).
Definition T_L5h2 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_240 (armR BC_LTU true 7 10 T_L5h).
Definition T_L5h3a : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_27C (armR BC_GEU false 14 11 T_L5h2).
Definition T_L5h3 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_280 (armR BC_LTU false 6 11 T_L5h3a).
Definition T_L5hi : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_2A8 (armR BC_GEU false 5 11 T_L5h3).
Definition T_R : sstate := Eval vm_compute in psJt sL5 T_L5lo.
Lemma T_R_h : psJt sL5 T_L5hi = T_R. Proof. vm_compute. reflexivity. Qed.
Lemma segS3_stops :
ss_pc S_V0 = B_MAPORDIE_PC /\ ss_pc S_V = B_INTERNAL_MMAP_PC_OFF_4 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 S_V0) = RS_ecall /\
map (sr_get (ss_regs S_V)) [1; 10; 11; 12; 13; 14; 15; 17]%bv =
[SLit B_MMAPFIXEDIMPL_PC_OFF_AC; SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SOff aQ 0) (SAlu ALU_SLL (SOff aNCH 0) (SLit 3))) (SLit 18446744073709547520)) (SLit 0);
SLit 131072; SLit 3; SLit 50; SLit 18446744073709551615; SLit 0; SLit 222] /\
ss_pc S_V2 = B_ALLOCATORSTATS_PC_OFF_45C /\ ss_pc S_V3 = B_ALLOCATORSTATS_PC_OFF_278 /\ ss_pc S_YJ = B_ALLOCATORSTATS_PC_OFF_278 /\ ss_pc S_TJ0 = B_ALLOCTYPE_PC_OFF_2C4 /\
map (sr_get (ss_regs S_TJ0)) [2; 18; 19; 20; 21]%bv = [SOff 2 (-2272); SOff aMAP 4096; SOff aND 0; SOff aMAP 6144; SOff 10 0] /\
ss_pc T_PD = B_STACKDEPOTPUT_STACKTRACE_PC /\ map (sr_get (ss_regs T_PD)) [1; 10; 11]%bv = [SLit B_ALLOCTYPE_PC_OFF_3AC; SOff 2 (-2112); SOff aLEN 0] /\
ss_pc T_M0 = B_ALLOCTYPE_PC_OFF_3E0 /\ ss_pc T_N = B_ALLOCTYPE_PC_OFF_418 /\ ss_pc T_M3 = B_MEMSET_PC /\
map (sr_get (ss_regs T_M3)) [1; 10; 11; 12]%bv =
[SLit B_ALLOCTYPE_PC_OFF_484; SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aMAP 4096) (SLit 3)); SLit 250;
SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SOff aMAP 6136) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aMAP 4096) (SLit 3))) (SLit 0)] /\
sr_get (ss_regs T_P3) 22%bv = SAlu ALU_AND (SAlu ALU_ADD (SOff 10 6151) (SOff aMAP 0)) (SLit (-8)) /\
sr_get (ss_regs T_P3) 8%bv = SAlu ALU_AND (SOff aND 4095) (SLit 18446744073709547520) /\
sr_get (ss_regs (runto B_ALLOCTYPE_PC_OFF_494 T_P4)) 11%bv = SAlu ALU_ADD (SAlu ALU_ADD (SOff aMS 0) (SOff aMAP 0)) (SMd M_MUL (SOff aUE 0) (SLit 18446744073709551615)) /\
ss_pc T_M4 = B_MEMSET_PC /\
map (sr_get (ss_regs T_M4)) [1; 10; 11]%bv = [SLit B_ALLOCTYPE_PC_OFF_498; SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aUE 0) (SLit 3)); SLit 250] /\
sr_get (ss_regs (runto B_ALLOCTYPE_PC_OFF_4A4 T_P6)) 22%bv = SAlu ALU_AND (SOff 10 0) (SLit 281474976710648) /\
ss_pc T_R = B_POISONSHADOW_PC_OFF_2A8 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 T_P7) = RS_stopped (SR_branch BC_GEU (SOff aSHB (-1)) (SOff aMAP 6144))   /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 T_R) =
RS_stopped (SR_branch BC_LTU (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aMAP 6136) (SOff aN8DS 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aMAP 6144) (SLit 3))) (SLit 18446744073709551615)).
Proof. vm_compute. repeat split; reflexivity. Qed.
