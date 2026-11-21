(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFif.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFif.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w AFhy_w AFhz_w AFi0_w AFi4_w AFi9_w AFid_w AFie_w.
Import ListNotations. Open Scope Z_scope.
Definition S_V0 : sstate := Eval vm_compute in runto 0x6e480 (arm BC_EQ true (SOff aNCH 0) (SOff aRES 0) S_X).
Definition S_V : sstate := Eval vm_compute in runtoC 0x643e8 S_V0.
Definition S_V2 : sstate := Eval vm_compute in runtoC 0x367c4 (mkSS 0x643ec (ss_regs S_V) (ss_mem S_V) None (ss_facts S_V)).
Definition S_V3 : sstate := Eval vm_compute in runto 0x365e0 S_V2.
Definition RES2T : sv := SAlu ALU_ADD (SOff aRES 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff aNCH 0) (SOff aRES 0)) (SLit 1)) (SLit 14)).
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
Definition S_ZJ0 : sstate := Eval vm_compute in runto 0x3660c S_YJ.
Definition S_ZJt : sstate := Eval vm_compute in runto 0x36614 (arm BC_LTU true (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_ZJ0).
Definition S_ZJf : sstate := Eval vm_compute in runto 0x36614 (arm BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_ZJ0).
Definition S_ZJ : sstate := Eval vm_compute in noconds (forget S_ZJt sMX [12]%bv).
Definition S_ZJ1 : sstate := Eval vm_compute in pin (runto 0x3661c S_ZJ) 11%bv (SOff aBSL (-104)).
Definition MUTCH : list YP09.chunk :=
[YP09.mkChunk (TFIB_INST + o_sec_mutex) (CVal 1 (SLit 1)); YP09.mkChunk (TFIB_INST + o_sec_mutex + 1) (CVal 1 (SLit 0));
YP09.mkChunk (TFIB_INST + o_sec_mutex + 2) (CVal 2 (SLit 0))].
Definition S_ZJ1s : sstate := Eval vm_compute in
mkSS (ss_pc S_ZJ1) (ss_regs S_ZJ1) (setchunks (TFIB_INST + o_sec_mutex) MUTCH (ss_mem S_ZJ1)) (ss_resv S_ZJ1) (ss_facts S_ZJ1).
Definition S_TJ0 : sstate := Eval vm_compute in runto 0x31ec0 S_ZJ1s.
Definition T_J : sstate := Eval vm_compute in arm BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SAlu ALU_ADD (SOff 10 6144) (SOff aMAP 0)) S_TJ0.
Definition T_K : sstate := Eval vm_compute in arm BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0) (runto 0x31ee8 T_J).
Definition T_PD : sstate := Eval vm_compute in runto 0x7272c T_K.
Definition trs_D : smem := match ss_mem T_PD with rq :: rm :: rb :: r1 :: rest => rq :: rm :: rb :: trim_lo r1 (-2272) :: rest | l => l end.
Definition T_2 : sstate := Eval vm_compute in addreg R_scr2 (ss_after_call T_PD trs_D sD1 0x31fa8).
Definition T_M0 : sstate := Eval vm_compute in runto 0x31fdc T_2.
Definition T_Ma : sstate := Eval vm_compute in runto 0x32014 (arm BC_LTU true (SOff aMAP 4096) (SOff aSB 0) T_M0).
Definition T_Mb : sstate := Eval vm_compute in runto 0x32014 (arm BC_GEU true (SOff aMAP 4096) (SOff aSB 137438953472) (runto 0x31fec (arm BC_LTU false (SOff aMAP 4096) (SOff aSB 0) T_M0))).
Definition T_N : sstate := Eval vm_compute in noconds (forget T_Ma sGA [11]%bv).
Definition T_L3 : sstate := Eval vm_compute in runto 0x53aa4 T_N.
Definition T_L3l : sstate := Eval vm_compute in runto 0x53c8c (armR BC_GEU true 14 10 T_L3).
Definition T_L3lo : sstate := Eval vm_compute in runto 0x94a18 (armR BC_GEU true 14 11 T_L3l).
Definition T_L3h : sstate := Eval vm_compute in runto 0x53ae4 (armR BC_GEU false 14 10 T_L3).
Definition T_L3h2 : sstate := Eval vm_compute in runto 0x53c8c (armR BC_LTU true 7 10 T_L3h).
Definition T_L3h3 : sstate := Eval vm_compute in runto 0x53ccc (armR BC_GEU false 14 11 T_L3h2).
Definition T_L3hi : sstate := Eval vm_compute in runto 0x94a18 (armR BC_GEU false 5 11 T_L3h3).
Definition T_M3 : sstate := Eval vm_compute in psJ sL3 T_L3lo.
Definition T_P3 : sstate := Eval vm_compute in ss_after_stretch T_M3 (ss_mem T_M3) sM3 CLOB_MS 0x32080.
Definition T_P4 : sstate := Eval vm_compute in pin (pin T_P3 22%bv (SOff aUE 0)) 8%bv (SOff aMS (-4096)).
Definition T_P5 : sstate := Eval vm_compute in pin (runto 0x32090 T_P4) 11%bv (SOff aRL 0).
Definition T_L4 : sstate := Eval vm_compute in runto 0x53aa4 T_P5.
Definition T_L4l : sstate := Eval vm_compute in runto 0x53c8c (armR BC_GEU true 14 10 T_L4).
Definition T_L4lo : sstate := Eval vm_compute in runto 0x94a18 (armR BC_GEU true 14 11 T_L4l).
Definition T_L4h : sstate := Eval vm_compute in runto 0x53ae4 (armR BC_GEU false 14 10 T_L4).
Definition T_L4h2 : sstate := Eval vm_compute in runto 0x53c8c (armR BC_LTU true 7 10 T_L4h).
Definition T_L4h3 : sstate := Eval vm_compute in runto 0x53ccc (armR BC_GEU false 14 11 T_L4h2).
Definition T_L4hi : sstate := Eval vm_compute in runto 0x94a18 (armR BC_GEU false 5 11 T_L4h3).
Definition T_M4 : sstate := Eval vm_compute in psJ sL4 T_L4lo.
Definition T_P6 : sstate := Eval vm_compute in ss_after_stretch T_M4 (ss_mem T_M4) sM4 CLOB_MS 0x32094.
Definition T_P7 : sstate := Eval vm_compute in pin (runto 0x320a0 T_P6) 22%bv (SOff aN8DS 0).
Definition T_L5 : sstate := Eval vm_compute in runto 0x53aa4 T_P7.
Definition T_L5l : sstate := Eval vm_compute in runto 0x53c8c (armR BC_GEU true 14 10 T_L5).
Definition T_L5lo : sstate := Eval vm_compute in runto 0x53cf4 (armR BC_GEU true 14 11 T_L5l).
Definition T_L5h : sstate := Eval vm_compute in runto 0x53ae4 (armR BC_GEU false 14 10 T_L5).
Definition T_L5h2 : sstate := Eval vm_compute in runto 0x53c8c (armR BC_LTU true 7 10 T_L5h).
Definition T_L5h3a : sstate := Eval vm_compute in runto 0x53cc8 (armR BC_GEU false 14 11 T_L5h2).
Definition T_L5h3 : sstate := Eval vm_compute in runto 0x53ccc (armR BC_LTU false 6 11 T_L5h3a).
Definition T_L5hi : sstate := Eval vm_compute in runto 0x53cf4 (armR BC_GEU false 5 11 T_L5h3).
Definition T_R : sstate := Eval vm_compute in psJt sL5 T_L5lo.
