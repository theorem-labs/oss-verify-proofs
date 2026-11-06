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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface RT_fk D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Po_rows Po_iface Po_rop_defs Po_ropl_iface Po_ropl1_defs Po_ropl_topw Po_ropl_g12 Po_ropl_g3 Po_ropl_g2 Po_ropl_g8 Po_ropl_g14.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_ropl_top () := "C46Stdlib5Lists4List2InI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53B23=Po_ropl1_defs9ropl1_genC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53B238Po_iface;PIX_NOT_SRCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface?PIX_SRC_AND_DSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_ifaceBPIX_NOTSRC_AND_DSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface>PIX_SRC_OR_DSTC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53B238Po_iface6PO_OPSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface7PIX_SRCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Po_ropl_g12<ropl1_gen_12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_ropl_g3;ropl1_gen_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_ropl_g8;ropl1_gen_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_ropl_g2;ropl1_gen_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Po_ropl_g14<ropl1_gen_14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<Po_ropl_topwErasteropLow_po_of_genC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23;Po_ropl_top=ropl1_gen_allC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ropl1_gen_all : forall op, In op PO_OPS -> ropl1_gen op.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_top ()) [] "h01Hh12oph22INp;3p;2p;1p;6g0000j39Tg000Gj34Tg000aR0j20Tg001;j13Tg002>j66Tg002ZR1g0038R2f0R334p=7g0048R4=413p=5g005<R5=413p=2g006CR6=413g007FR7'0p=1A4163p=8g007c9913P0g008^R8f1R9541%79%59%29%19'0'0'0f2R9#3P3A4189P1P8%33X11R8g009Zf3R:P3E6W0P3O1%79%59%29%19'0'0'0P0%7:%5:%2:%1:'0'0f4R:#3P3%7:P1P2P8g00:^f5R2P3E6W0P3O1%5:%2:%1:'0'0P0%52%22%12'0f6R2#3P3%52P1P4P8g00;`f7R4P3E6W0P3O1%22%12'0P0%24%14f8R4#3P3%24P1P5P8g00<bf9R5P3E6W0P3O1%14P0%85P7f:R5#3P3%85P1P6P8g00=df;P3E6W0P3O1P7f<#3P3n010000000X07P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W2X11o"). Qed.

(* [comment removed for export] *)
Theorem rasteropLow_po_ok : rasteropLow_po.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_top ()) [] "p;1g00>hj10Tg00@6#0o"). Qed.
