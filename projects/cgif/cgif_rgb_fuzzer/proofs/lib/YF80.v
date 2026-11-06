(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0h YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF3w YF8g YF7x YF7z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition hMSF : nat := 115.
Definition hPF : nat := 121.
Definition CLOB_PF : list (bv 5) := [10; 12; 14; 15]%bv.
Definition hCP : nat := 125.
Definition CLOB_CP3 : list (bv 5) := [12; 13; 20]%bv.
Definition R3_De1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36c94 + D_150) R3_Ke) 19%bv (SOff rNCe 0)))).
Definition R3_De2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36c98 + D_150) R3_De1) 9%bv (SOff rNFe 0)))).
Definition R3_De3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x347fc + D_150) R3_De2))).
Definition R3_FILLee {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36cd0 + D_150) (arm BC_LTU false (SAlu ALU_ADD (SMd M_MUL (SOff rAU 0) (SLit (-1))) (SOff rMU 0)) (SOff rCSZ 0) (runto (0x36cb0 + D_150) (arm BC_GEU true (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) R3_De3)))))).
Definition R3_Fe1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x34814 + D_150) (arm BC_GEU false (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) R3_De3)) 8%bv (SOff rMF2 0)))).
Definition R3_Fe2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x34834 + D_150) (arm BC_GEU false (SOff rMF2 0) (SLit 536870913) (runto (0x3481c + D_150) R3_Fe1))) 9%bv (SOff rFADR 0)))).
Definition R3_Fe3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x34864 + D_150) R3_Fe2) 18%bv (SLit 262144)))).
Definition R3_Fe4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x6ebd4 + D_2c4) R3_Fe3))).
Definition R3_NFe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_Fe4))).
Definition R3_NFer {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NFe 10%bv (SLit ENOMEM_RET)) (0x64c8c + D_2c4)))).
Definition R3_NFeg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NFe 10%bv (SOff rFADR 0)) (0x64c8c + D_2c4)))).
Definition R3_NRFe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NFer))).
Definition R3_NRFee {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NRFe 10%bv (SLit ENOMEM_RET)) (0x64c8c + D_2c4)))).
Definition R3_NRFex {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NRFe 10%bv (SLit EEXIST_RET)) (0x64c8c + D_2c4)))).
Definition R3_NRFeg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NRFe 10%bv (SOff rFADR 0)) (0x64c8c + D_2c4)))).
Definition R3_SPFee {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC A_RESTORE_SPIN R3_NRFee))).
Definition R3_SPFex {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC A_RESTORE_SPIN R3_NRFex))).
Definition R3_FFe1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NRFeg))).
Definition R3_FFRETe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_FFe1))).
Definition R3_FGe1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NFeg))).
Definition R3_FGe2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_FGe1))).
Definition R3_MSFe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin R3_FGe2 10%bv (SOff rSHF 0)) 12%bv (SLit 32768)))).
Definition R3_FGe3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_MSFe (ss_mem R3_MSFe) hMSF CLOB_MS (0x34894 + D_150)))).
Definition R3_FILLeg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36cd0 + D_150) (arm BC_LTU false (SAlu ALU_ADD (SMd M_MUL (SOff rAU 0) (SLit (-1))) (SOff rMU 0)) (SOff rCSZ 0) (runto (0x36cb0 + D_150) R3_FGe3))))).
Definition R3_Dg1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36c94 + D_150) R3_Kg) 19%bv (SOff rNCg 0)))).
Definition R3_Dg2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36c98 + D_150) R3_Dg1) 9%bv (SOff rNFg 0)))).
Definition R3_Dg3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x347fc + D_150) R3_Dg2))).
Definition R3_FILLge {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36cd0 + D_150) (arm BC_LTU false (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff rAU 0) (SLit (-1))) (SLit 262144)) (SOff rMU 0)) (SOff rCSZ 0) (runto (0x36cb0 + D_150) (arm BC_GEU true (SOff rMF 0) (SAlu ALU_SLL (SOff rNFg 0) (SLit 2)) R3_Dg3)))))).
Definition R3_Fg1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x34814 + D_150) (arm BC_GEU false (SOff rMF 0) (SAlu ALU_SLL (SOff rNFg 0) (SLit 2)) R3_Dg3)) 8%bv (SOff rMF2 0)))).
Definition R3_Fg2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x34834 + D_150) (arm BC_GEU false (SOff rMF2 0) (SLit 536870913) (runto (0x3481c + D_150) R3_Fg1))) 9%bv (SOff rFADR 0)))).
Definition R3_Fg3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x34864 + D_150) R3_Fg2) 18%bv (SLit 262144)))).
Definition R3_Fg4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x6ebd4 + D_2c4) R3_Fg3))).
Definition R3_NFg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_Fg4))).
Definition R3_NFgr {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NFg 10%bv (SLit ENOMEM_RET)) (0x64c8c + D_2c4)))).
Definition R3_NFgg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NFg 10%bv (SOff rFADR 0)) (0x64c8c + D_2c4)))).
Definition R3_NRFg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NFgr))).
Definition R3_NRFge {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NRFg 10%bv (SLit ENOMEM_RET)) (0x64c8c + D_2c4)))).
Definition R3_NRFgx {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NRFg 10%bv (SLit EEXIST_RET)) (0x64c8c + D_2c4)))).
Definition R3_NRFgg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NRFg 10%bv (SOff rFADR 0)) (0x64c8c + D_2c4)))).
Definition R3_SPFge {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC A_RESTORE_SPIN R3_NRFge))).
Definition R3_SPFgx {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC A_RESTORE_SPIN R3_NRFgx))).
Definition R3_FFg1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NRFgg))).
Definition R3_FFRETg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_FFg1))).
Definition R3_FGg1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NFgg))).
Definition R3_FGg2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_FGg1))).
Definition R3_MSFg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin R3_FGg2 10%bv (SOff rSHF 0)) 12%bv (SLit 32768)))).
Definition R3_FGg3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_MSFg (ss_mem R3_MSFg) hMSF CLOB_MS (0x34894 + D_150)))).
Definition R3_FILLgg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36cd0 + D_150) (arm BC_LTU false (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff rAU 0) (SLit (-1))) (SLit 262144)) (SOff rMU 0)) (SOff rCSZ 0) (runto (0x36cb0 + D_150) R3_FGg3))))).
Definition R3_Tee0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_FILLee (ss_mem R3_FILLee) hPF CLOB_PF (0x36cf0 + D_150)))).
Definition R3_Tee1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36d00 + D_150) R3_Tee0) 13%bv (SOff rAUe 0)))).
Definition R3_Tee2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36d04 + D_150) R3_Tee1) 10%bv (SOff rNFe 0)))).
Definition R3_Tee3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36d0c + D_150) R3_Tee2))).
Definition R3_Tee4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36ad4 + D_150) (arm BC_LTU false (SOff rMU 0) (SOff rAUe 0) R3_Tee3)))).
Definition R3_Cee0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36980 + D_150) (arm BC_LTU false (SOff rNFe 0) (SOff rN 0) R3_Tee4)))).
Definition R3_Cee {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_Cee0 (ss_mem R3_Cee0) hCP CLOB_CP3 (0x36994 + D_150)))).
Definition R3_RETee {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_Cee))).
Definition R3_Teg0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_FILLeg (ss_mem R3_FILLeg) hPF CLOB_PF (0x36cf0 + D_150)))).
Definition R3_Teg1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36d00 + D_150) R3_Teg0) 13%bv (SOff rAUe 0)))).
Definition R3_Teg2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36d04 + D_150) R3_Teg1) 10%bv (SOff rNFe 0)))).
Definition R3_Teg3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36d0c + D_150) R3_Teg2))).
Definition R3_Teg4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36ad4 + D_150) (arm BC_LTU false (SOff rMU 0) (SOff rAUe 0) R3_Teg3)))).
Definition R3_Ceg0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36980 + D_150) (arm BC_LTU false (SOff rNFe 0) (SOff rN 0) R3_Teg4)))).
Definition R3_Ceg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_Ceg0 (ss_mem R3_Ceg0) hCP CLOB_CP3 (0x36994 + D_150)))).
Definition R3_RETeg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_Ceg))).
Definition R3_Tge0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_FILLge (ss_mem R3_FILLge) hPF CLOB_PF (0x36cf0 + D_150)))).
Definition R3_Tge1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36d00 + D_150) R3_Tge0) 13%bv (SOff rAUg 0)))).
Definition R3_Tge2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36d04 + D_150) R3_Tge1) 10%bv (SOff rNFg 0)))).
Definition R3_Tge3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36d0c + D_150) R3_Tge2))).
Definition R3_Tge4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36ad4 + D_150) (arm BC_LTU false (SOff rMU 262144) (SOff rAUg 0) R3_Tge3)))).
Definition R3_Cge0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36980 + D_150) (arm BC_LTU false (SOff rNFg 0) (SOff rN 0) R3_Tge4)))).
Definition R3_Cge {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_Cge0 (ss_mem R3_Cge0) hCP CLOB_CP3 (0x36994 + D_150)))).
Definition R3_RETge {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_Cge))).
Definition R3_Tgg0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_FILLgg (ss_mem R3_FILLgg) hPF CLOB_PF (0x36cf0 + D_150)))).
Definition R3_Tgg1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36d00 + D_150) R3_Tgg0) 13%bv (SOff rAUg 0)))).
Definition R3_Tgg2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36d04 + D_150) R3_Tgg1) 10%bv (SOff rNFg 0)))).
Definition R3_Tgg3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36d0c + D_150) R3_Tgg2))).
Definition R3_Tgg4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36ad4 + D_150) (arm BC_LTU false (SOff rMU 262144) (SOff rAUg 0) R3_Tgg3)))).
Definition R3_Cgg0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36980 + D_150) (arm BC_LTU false (SOff rNFg 0) (SOff rN 0) R3_Tgg4)))).
Definition R3_Cgg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_Cgg0 (ss_mem R3_Cgg0) hCP CLOB_CP3 (0x36994 + D_150)))).
Definition R3_RETgg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_Cgg))).
Definition pcs3b {imgk : img} : list Z := ltac:(img_eval_last (fun imgk : img => (map ss_pc
[R3_De1; R3_De2; R3_De3; R3_FILLee; R3_Fe1; R3_Fe2; R3_Fe3; R3_Fe4; R3_NFe; R3_FFe1; R3_FFRETe; R3_FGe1; R3_FGe2; R3_FILLeg;
R3_Dg1; R3_Dg2; R3_Dg3; R3_FILLge; R3_Fg1; R3_Fg2; R3_Fg3; R3_Fg4; R3_NFg; R3_FFg1; R3_FFRETg; R3_FGg1; R3_FGg2; R3_FILLgg;
R3_Tee0; R3_Tee1; R3_Tee2; R3_Tee3; R3_Tee4; R3_Cee0; R3_Cee; R3_RETee;
R3_Tgg0; R3_Tgg1; R3_Tgg2; R3_Tgg3; R3_Tgg4; R3_Cgg0; R3_Cgg; R3_RETgg]))).


