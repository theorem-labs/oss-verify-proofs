(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface Pm_iface2 Cf_iface RT_fk RT_fk_iface D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_rows Po_iface Po_rop_defs Po_ropl_iface Po_rop1_clr0 Po_rop1_clr16 Po_rop1_two0 Po_rop1_two16 Po_ropu1_top Po_ropl_top.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_rasterop1 () := "C69OSSVerify5KrLib2K53A23<Po_ropu1_topFrasteropUniLow_clr1_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_ropl_ifaceGrasteropUniLow_clr1_cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_rop1_clr0CpixRasterop_po_clr0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_rop1_clr16DpixRasterop_po_clr16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_rop1_two0CpixRasterop_po_two0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_rop1_two16DpixRasterop_po_two16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_ropl_ifaceDpixRasterop_po_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_ropl_topArasteropLow_po_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_ropl_iface>rasteropLow_poC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ROPTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis TABR : In (A_RMASK, 132) ACC_LITS.
Hypothesis TABL : In (A_LMASK, 132) ACC_LITS.

Theorem pixRasterop_po1_ok : pixRasterop_po_cps RT.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rasterop1 ()) ["ROPTOP"] "h04ROPLh14ROPUp;6p;1p;5p;7g0000j66Tg001?j15Tg002Pj50Tg003\j51Tg004jj74Tg0066j72Tg007Dj53Tp,2RTR0p,2AFR1p,2GPR2p,3FKCR3p,4TABRR4p,4TABLR5E6%50g008Rg009[P0P0P1P2P3f1R6D0P0P1P2P3P6D1P0P1P2P3P4P5f0R6F4P0P1P2P3P4P5P6F2D3b0b1o"). Qed.
End ROPTOP.
