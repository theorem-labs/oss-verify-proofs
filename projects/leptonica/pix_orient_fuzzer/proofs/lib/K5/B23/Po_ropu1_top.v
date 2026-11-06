(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface RT_fk RT_fk_iface D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Po_rows Po_iface Po_ropl_iface Po_ropu1_defs Po_ropu1 Po_ropu1_arms Po_ropu1_wa Po_ropu1_gen.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_ropu1_top () := "C69OSSVerify5KrLib2K53B23;Po_ropu1_wa;ropu1_wa_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<Po_ropu1_gen<ropu1_gen_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=Po_ropu1_arms=ropu1_arms_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_ropu19ropu_clr1C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ROPU1TOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis TABR : In (A_RMASK, 132) ACC_LITS.
Hypothesis TABL : In (A_LMASK, 132) ACC_LITS.

Theorem rasteropUniLow_clr1_ok : rasteropUniLow_clr1_cps RT.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropu1_top ()) ["ROPU1TOP"] "p;5p;4p;7g0000j53Tg0013j52Tg0028j40Tg003?j71Tp,2RTR0p,2AFR1p,2GPR2p,3FKCp,4TABRR3p,4TABLR4P0P1P0P1P2P3P4D3P0P1P2P3P4D2C0F1o"). Qed.
End ROPU1TOP.
