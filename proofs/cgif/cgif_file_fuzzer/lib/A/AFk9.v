(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0f YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhy AFhz AFkp AFk6 AFk8.
Import ListNotations. Open Scope Z_scope.
Definition hMSF : nat := 115.
Definition hPF : nat := 121.
Definition CLOB_PF : list (bv 5) := [10; 12; 14; 15]%bv.
Definition hCP : nat := 125.
Definition CLOB_CP3 : list (bv 5) := [12; 13; 20]%bv.
Definition R3_De1 : sstate := Eval vm_compute in pin (runto 0x3668c R3_Ke) 19%bv (SOff rNCe 0).
Definition R3_De2 : sstate := Eval vm_compute in pin (runto 0x36690 R3_De1) 9%bv (SOff rNFe 0).
Definition R3_De3 : sstate := Eval vm_compute in runto 0x341f4 R3_De2.
Definition R3_FILLee : sstate := Eval vm_compute in
runto 0x366c8 (arm BC_LTU false (SAlu ALU_ADD (SMd M_MUL (SOff rAU 0) (SLit (-1))) (SOff rMU 0)) (SOff rCSZ 0) (runto 0x366a8 (arm BC_GEU true (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) R3_De3))).
Definition R3_Fe1 : sstate := Eval vm_compute in pin (runto 0x3420c (arm BC_GEU false (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) R3_De3)) 8%bv (SOff rMF2 0).
Definition R3_Fe2 : sstate := Eval vm_compute in pin (runto 0x3422c (arm BC_GEU false (SOff rMF2 0) (SLit 536870913) (runto 0x34214 R3_Fe1))) 9%bv (SOff rFADR 0).
Definition R3_Fe3 : sstate := Eval vm_compute in pin (runto 0x3425c R3_Fe2) 18%bv (SLit 262144).
Definition R3_Fe4 : sstate := Eval vm_compute in runto 0x6e0b8 R3_Fe3.
Definition R3_NFe : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_Fe4.
Definition R3_NFer : sstate := Eval vm_compute in setpc (pin R3_NFe 10%bv (SLit ENOMEM_RET)) 0x64170.
Definition R3_NFeg : sstate := Eval vm_compute in setpc (pin R3_NFe 10%bv (SOff rFADR 0)) 0x64170.
Definition R3_NRFe : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NFer.
Definition R3_NRFee : sstate := Eval vm_compute in setpc (pin R3_NRFe 10%bv (SLit ENOMEM_RET)) 0x64170.
Definition R3_NRFex : sstate := Eval vm_compute in setpc (pin R3_NRFe 10%bv (SLit EEXIST_RET)) 0x64170.
Definition R3_NRFeg : sstate := Eval vm_compute in setpc (pin R3_NRFe 10%bv (SOff rFADR 0)) 0x64170.
Definition R3_SPFee : sstate := Eval vm_compute in runtoC A_RESTORE_SPIN R3_NRFee.
Definition R3_SPFex : sstate := Eval vm_compute in runtoC A_RESTORE_SPIN R3_NRFex.
Definition R3_FFe1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NRFeg.
Definition R3_FFRETe : sstate := Eval vm_compute in runto 0x7ffffff0 R3_FFe1.
Definition R3_FGe1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NFeg.
Definition R3_FGe2 : sstate := Eval vm_compute in runto 0x7ffffff0 R3_FGe1.
Definition R3_MSFe : sstate := Eval vm_compute in pin (pin R3_FGe2 10%bv (SOff rSHF 0)) 12%bv (SLit 32768).
Definition R3_FGe3 : sstate := Eval vm_compute in ss_after_stretch R3_MSFe (ss_mem R3_MSFe) hMSF CLOB_MS 0x3428c.
Definition R3_FILLeg : sstate := Eval vm_compute in
runto 0x366c8 (arm BC_LTU false (SAlu ALU_ADD (SMd M_MUL (SOff rAU 0) (SLit (-1))) (SOff rMU 0)) (SOff rCSZ 0) (runto 0x366a8 R3_FGe3)).
Definition R3_Dg1 : sstate := Eval vm_compute in pin (runto 0x3668c R3_Kg) 19%bv (SOff rNCg 0).
Definition R3_Dg2 : sstate := Eval vm_compute in pin (runto 0x36690 R3_Dg1) 9%bv (SOff rNFg 0).
Definition R3_Dg3 : sstate := Eval vm_compute in runto 0x341f4 R3_Dg2.
Definition R3_FILLge : sstate := Eval vm_compute in
runto 0x366c8 (arm BC_LTU false (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff rAU 0) (SLit (-1))) (SLit 262144)) (SOff rMU 0)) (SOff rCSZ 0) (runto 0x366a8 (arm BC_GEU true (SOff rMF 0) (SAlu ALU_SLL (SOff rNFg 0) (SLit 2)) R3_Dg3))).
Definition R3_Fg1 : sstate := Eval vm_compute in pin (runto 0x3420c (arm BC_GEU false (SOff rMF 0) (SAlu ALU_SLL (SOff rNFg 0) (SLit 2)) R3_Dg3)) 8%bv (SOff rMF2 0).
Definition R3_Fg2 : sstate := Eval vm_compute in pin (runto 0x3422c (arm BC_GEU false (SOff rMF2 0) (SLit 536870913) (runto 0x34214 R3_Fg1))) 9%bv (SOff rFADR 0).
Definition R3_Fg3 : sstate := Eval vm_compute in pin (runto 0x3425c R3_Fg2) 18%bv (SLit 262144).
Definition R3_Fg4 : sstate := Eval vm_compute in runto 0x6e0b8 R3_Fg3.
Definition R3_NFg : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_Fg4.
Definition R3_NFgr : sstate := Eval vm_compute in setpc (pin R3_NFg 10%bv (SLit ENOMEM_RET)) 0x64170.
Definition R3_NFgg : sstate := Eval vm_compute in setpc (pin R3_NFg 10%bv (SOff rFADR 0)) 0x64170.
Definition R3_NRFg : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NFgr.
Definition R3_NRFge : sstate := Eval vm_compute in setpc (pin R3_NRFg 10%bv (SLit ENOMEM_RET)) 0x64170.
Definition R3_NRFgx : sstate := Eval vm_compute in setpc (pin R3_NRFg 10%bv (SLit EEXIST_RET)) 0x64170.
Definition R3_NRFgg : sstate := Eval vm_compute in setpc (pin R3_NRFg 10%bv (SOff rFADR 0)) 0x64170.
Definition R3_SPFge : sstate := Eval vm_compute in runtoC A_RESTORE_SPIN R3_NRFge.
Definition R3_SPFgx : sstate := Eval vm_compute in runtoC A_RESTORE_SPIN R3_NRFgx.
Definition R3_FFg1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NRFgg.
Definition R3_FFRETg : sstate := Eval vm_compute in runto 0x7ffffff0 R3_FFg1.
Definition R3_FGg1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NFgg.
Definition R3_FGg2 : sstate := Eval vm_compute in runto 0x7ffffff0 R3_FGg1.
Definition R3_MSFg : sstate := Eval vm_compute in pin (pin R3_FGg2 10%bv (SOff rSHF 0)) 12%bv (SLit 32768).
Definition R3_FGg3 : sstate := Eval vm_compute in ss_after_stretch R3_MSFg (ss_mem R3_MSFg) hMSF CLOB_MS 0x3428c.
Definition R3_FILLgg : sstate := Eval vm_compute in
runto 0x366c8 (arm BC_LTU false (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff rAU 0) (SLit (-1))) (SLit 262144)) (SOff rMU 0)) (SOff rCSZ 0) (runto 0x366a8 R3_FGg3)).
Definition R3_Tee0 : sstate := Eval vm_compute in ss_after_stretch R3_FILLee (ss_mem R3_FILLee) hPF CLOB_PF 0x366e8.
Definition R3_Tee1 : sstate := Eval vm_compute in pin (runto 0x366f8 R3_Tee0) 13%bv (SOff rAUe 0).
Definition R3_Tee2 : sstate := Eval vm_compute in pin (runto 0x366fc R3_Tee1) 10%bv (SOff rNFe 0).
Definition R3_Tee3 : sstate := Eval vm_compute in runto 0x36704 R3_Tee2.
Definition R3_Tee4 : sstate := Eval vm_compute in runto 0x364cc (arm BC_LTU false (SOff rMU 0) (SOff rAUe 0) R3_Tee3).
Definition R3_Cee0 : sstate := Eval vm_compute in runto 0x36378 (arm BC_LTU false (SOff rNFe 0) (SOff rN 0) R3_Tee4).
Definition R3_Cee : sstate := Eval vm_compute in ss_after_stretch R3_Cee0 (ss_mem R3_Cee0) hCP CLOB_CP3 0x3638c.
Definition R3_RETee : sstate := Eval vm_compute in runto 0x7ffffff0 R3_Cee.
Definition R3_Teg0 : sstate := Eval vm_compute in ss_after_stretch R3_FILLeg (ss_mem R3_FILLeg) hPF CLOB_PF 0x366e8.
Definition R3_Teg1 : sstate := Eval vm_compute in pin (runto 0x366f8 R3_Teg0) 13%bv (SOff rAUe 0).
Definition R3_Teg2 : sstate := Eval vm_compute in pin (runto 0x366fc R3_Teg1) 10%bv (SOff rNFe 0).
Definition R3_Teg3 : sstate := Eval vm_compute in runto 0x36704 R3_Teg2.
Definition R3_Teg4 : sstate := Eval vm_compute in runto 0x364cc (arm BC_LTU false (SOff rMU 0) (SOff rAUe 0) R3_Teg3).
Definition R3_Ceg0 : sstate := Eval vm_compute in runto 0x36378 (arm BC_LTU false (SOff rNFe 0) (SOff rN 0) R3_Teg4).
Definition R3_Ceg : sstate := Eval vm_compute in ss_after_stretch R3_Ceg0 (ss_mem R3_Ceg0) hCP CLOB_CP3 0x3638c.
Definition R3_RETeg : sstate := Eval vm_compute in runto 0x7ffffff0 R3_Ceg.
Definition R3_Tge0 : sstate := Eval vm_compute in ss_after_stretch R3_FILLge (ss_mem R3_FILLge) hPF CLOB_PF 0x366e8.
Definition R3_Tge1 : sstate := Eval vm_compute in pin (runto 0x366f8 R3_Tge0) 13%bv (SOff rAUg 0).
Definition R3_Tge2 : sstate := Eval vm_compute in pin (runto 0x366fc R3_Tge1) 10%bv (SOff rNFg 0).
Definition R3_Tge3 : sstate := Eval vm_compute in runto 0x36704 R3_Tge2.
Definition R3_Tge4 : sstate := Eval vm_compute in runto 0x364cc (arm BC_LTU false (SOff rMU 262144) (SOff rAUg 0) R3_Tge3).
Definition R3_Cge0 : sstate := Eval vm_compute in runto 0x36378 (arm BC_LTU false (SOff rNFg 0) (SOff rN 0) R3_Tge4).
Definition R3_Cge : sstate := Eval vm_compute in ss_after_stretch R3_Cge0 (ss_mem R3_Cge0) hCP CLOB_CP3 0x3638c.
Definition R3_RETge : sstate := Eval vm_compute in runto 0x7ffffff0 R3_Cge.
Definition R3_Tgg0 : sstate := Eval vm_compute in ss_after_stretch R3_FILLgg (ss_mem R3_FILLgg) hPF CLOB_PF 0x366e8.
Definition R3_Tgg1 : sstate := Eval vm_compute in pin (runto 0x366f8 R3_Tgg0) 13%bv (SOff rAUg 0).
Definition R3_Tgg2 : sstate := Eval vm_compute in pin (runto 0x366fc R3_Tgg1) 10%bv (SOff rNFg 0).
Definition R3_Tgg3 : sstate := Eval vm_compute in runto 0x36704 R3_Tgg2.
Definition R3_Tgg4 : sstate := Eval vm_compute in runto 0x364cc (arm BC_LTU false (SOff rMU 262144) (SOff rAUg 0) R3_Tgg3).
Definition R3_Cgg0 : sstate := Eval vm_compute in runto 0x36378 (arm BC_LTU false (SOff rNFg 0) (SOff rN 0) R3_Tgg4).
Definition R3_Cgg : sstate := Eval vm_compute in ss_after_stretch R3_Cgg0 (ss_mem R3_Cgg0) hCP CLOB_CP3 0x3638c.
Definition R3_RETgg : sstate := Eval vm_compute in runto 0x7ffffff0 R3_Cgg.
Definition pcs3b : list Z := Eval vm_compute in map ss_pc
[R3_De1; R3_De2; R3_De3; R3_FILLee; R3_Fe1; R3_Fe2; R3_Fe3; R3_Fe4; R3_NFe; R3_FFe1; R3_FFRETe; R3_FGe1; R3_FGe2; R3_FILLeg;
R3_Dg1; R3_Dg2; R3_Dg3; R3_FILLge; R3_Fg1; R3_Fg2; R3_Fg3; R3_Fg4; R3_NFg; R3_FFg1; R3_FFRETg; R3_FGg1; R3_FGg2; R3_FILLgg;
R3_Tee0; R3_Tee1; R3_Tee2; R3_Tee3; R3_Tee4; R3_Cee0; R3_Cee; R3_RETee;
R3_Tgg0; R3_Tgg1; R3_Tgg2; R3_Tgg3; R3_Tgg4; R3_Cgg0; R3_Cgg; R3_RETgg].
Lemma pcs3b_val : pcs3b = pcs3b. Proof. reflexivity. Qed.
Lemma st2_restore_stops :
ss_pc R3_NRFe = 0x6416c /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 R3_NFer) = RS_ecall /\
ss_pc R3_NRFg = 0x6416c /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 R3_NFgr) = RS_ecall /\
map (fun ss => (sr_get (ss_regs ss) 10%bv, sr_get (ss_regs ss) 11%bv, sr_get (ss_regs ss) 12%bv, sr_get (ss_regs ss) 13%bv, sr_get (ss_regs ss) 14%bv, sr_get (ss_regs ss) 15%bv, sr_get (ss_regs ss) 17%bv)) [R3_NRFe; R3_NRFg]
= [(SOff rFADR 0, SLit 262144, SLit 0, SLit 0x104022, SLit 18446744073709551615, SLit 0, SLit 222); (SOff rFADR 0, SLit 262144, SLit 0, SLit 0x104022, SLit 18446744073709551615, SLit 0, SLit 222)] /\
map ss_pc [R3_SPFee; R3_SPFex; R3_SPFge; R3_SPFgx] = [0x6e1ec; 0x6e1ec; 0x6e1ec; 0x6e1ec] /\
map (fun ss => (sr_get (ss_regs ss) 10%bv, sr_get (ss_regs ss) 1%bv, sr_get (ss_regs ss) 2%bv)) [R3_FFRETe; R3_FFRETg] = [(SLit 0, SOff 1 0, SOff 2 0); (SLit 0, SOff 1 0, SOff 2 0)].
Proof. vm_compute. repeat split; reflexivity. Qed.
Eval vm_compute in pcs3b.
Eval vm_compute in (map (fun ss => (sr_get (ss_regs ss) 10%bv, sr_get (ss_regs ss) 12%bv, sr_get (ss_regs ss) 1%bv)) [R3_FGe2; R3_FGg2]).
Eval vm_compute in (map (fun ss => (sr_get (ss_regs ss) 19%bv, sr_get (ss_regs ss) 9%bv)) [runto 0x3668c R3_Ke; runto 0x36690 R3_De1; runto 0x3668c R3_Kg]).
Eval vm_compute in (map (fun ss => (sr_get (ss_regs ss) 10%bv, sr_get (ss_regs ss) 11%bv, sr_get (ss_regs ss) 12%bv, sr_get (ss_regs ss) 19%bv, sr_get (ss_regs ss) 21%bv)) [R3_FILLee; R3_FILLgg]).
Eval vm_compute in (map (fun ss => (sr_get (ss_regs ss) 13%bv, sr_get (ss_regs ss) 10%bv)) [runto 0x366f8 R3_Tee0; runto 0x366fc R3_Tee1]).
Eval vm_compute in (map (fun ss => (sr_get (ss_regs ss) 20%bv, sr_get (ss_regs ss) 13%bv, sr_get (ss_regs ss) 11%bv)) [R3_Cee0; R3_Cgg0]).
Eval vm_compute in (map (fun ss => (sr_get (ss_regs ss) 10%bv, sr_get (ss_regs ss) 1%bv, sr_get (ss_regs ss) 2%bv)) [R3_RETee; R3_RETgg; R3_FFRETe]).
