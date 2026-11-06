(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Km_setelem Km_iface Km_kit Bi_ropkit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_rows Po_iface Po_rop_defs Po_ropl_iface Po_clipkit Po_ropukit Po_ropl1_defs Po_ropl1 Po_ropl1_arms Po_ropl_wa12 Po_ropl_wa3 Po_ropl_wa14 Po_ropl_wa2 Po_ropl_wa8 Po_ropl_g12 Po_ropl_g3 Po_ropl_g14 Po_ropl_g2 Po_ropl_g8.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_ropl_top () := "C46Stdlib5Lists4List2InI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53A23=Po_ropl1_defs8ropl1_waC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53A238Po_iface;PIX_NOT_SRCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface?PIX_SRC_AND_DSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_ifaceBPIX_NOTSRC_AND_DSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface>PIX_SRC_OR_DSTC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A238Po_iface6PO_OPSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface7PIX_SRCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_ropl_wa12;ropl1_wa_12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_ropl_wa3:ropl1_wa_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_ropl_wa8:ropl1_wa_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_ropl_wa2:ropl1_wa_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_ropl_wa14;ropl1_wa_14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_ropl1_defs9ropl1_genC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;Po_ropl_top<ropl1_wa_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_ropl1_arms=ropl1_arms_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_ropl1;ropl1_frontC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;Po_ropl_topErasteropLow_d1_of_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_ropl_iface>rasteropLow_poC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_ropl_g12<ropl1_gen_12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Po_ropl_g3;ropl1_gen_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Po_ropl_g8;ropl1_gen_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Po_ropl_g2;ropl1_gen_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_ropl_g14<ropl1_gen_14C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;Po_ropl_topErasteropLow_po_of_genC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;Po_ropl_top=ropl1_gen_allC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ropl1_wa_all : forall op, In op PO_OPS -> ropl1_wa op.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_top ()) [] "h01Hh12oph22INp;3p;2p;1p;6g0000j39Tg000Gj34Tg000aR0j20Tg001;j13Tg002=j66Tg002YR1g0037R2f0R334p=7g0047R4=413p=5g005;R5=413p=2g006BR6=413g007ER7'0p=1A4163p=8g007b9913P0g008]R8f1R9541%79%59%29%19'0'0'0f2R9#3P3A4189P1P8%33X11R8g009Yf3R:P3E6W0P3O1%79%59%29%19'0'0'0P0%7:%5:%2:%1:'0'0f4R:#3P3%7:P1P2P8g00:]f5R2P3E6W0P3O1%5:%2:%1:'0'0P0%52%22%12'0f6R2#3P3%52P1P4P8g00;_f7R4P3E6W0P3O1%22%12'0P0%24%14f8R4#3P3%24P1P5P8g00<af9R5P3E6W0P3O1%14P0%85P7f:R5#3P3%85P1P6P8g00=cf;P3E6W0P3O1P7f<#3P3n010000000X07P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W2X11o"). Qed.

Lemma rasteropLow_d1_of_gen : forall op, In op PO_OPS -> ropl1_gen op -> rasteropLow_d1 op.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_top ()) [] "h03GENh12INh22opp;3p;1p;2g0000j34Tg00>gj13Tg00?jj20Tg00@nj31Tg00B5j22Tg002YR0f0R1g007b540f1R0#3f2R21020=121'2W0W1W2o"). Qed.

Lemma rasteropLow_po_of_gen : (forall op, In op PO_OPS -> ropl1_gen op) -> rasteropLow_po.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_top ()) [] "h02oph13GENh22INp;3p;1g0000j32Tg00>gj11Tg00C5j30Tg002YR0f0R1g007b520R2f1R3#1[]0f2P3P1O29031X22X00g00DBeW1o"). Qed.

(* [comment removed for export] *)
Lemma rasteropLow_po_of_gen3 : ropl1_gen PIX_SRC_OR_DST -> ropl1_gen PIX_NOTSRC_AND_DST -> ropl1_gen PIX_SRC_AND_DST -> rasteropLow_po.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_top ()) [] "h01Hh12oph23G14h32G2h42G8h52INp;1p;3p;2p;6g00>gj11Tg0000j3:Tg000Gj34Tg000aR0j20Tg002=j66Tg00C5j39Tg002YR1g0037R2f0R334p=7g0047R4=413p=5g005;R5=413p=3g006BR6=413g007ER7'0p=2A4163p=8%16%15%14g007b9:13f1R8P0g008]R9=418%78%58%38%28'0'0'0f2R8#1P3A4198P1P9%13X11R9g00EJf3R:P3E6W0P3O1%78%58%38%28'0'0'0P0%7:%5:%3:%2:'0'0f4R:#1P3%7:P1P2P9g00FNf5R2P3E6W0P3O1%5:%3:%2:'0'0P0%52%32%22'0f6R2#1P3%52P1P4P9f8R4f7R:P3E6W0P3O1%32%22'0P0%3:%2:%14P3%34P1P5P9f;R5f9R:P3E6W0P3O1%24P0%8:P7f:R:#1P3%8:P1P6P9f>P5P3E6W0P3O1P7f<#1P3n010000000X07P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000793W5X11g00DBeW4W3W2o"). Qed.

Lemma ropl1_gen_all : forall op, In op PO_OPS -> ropl1_gen op.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_top ()) [] "h01Hh12oph22INp;3p;2p;1p;6g0000j39Tg000Gj34Tg000aR0j20Tg00>gj13Tg002=j66Tg002YR1g0037R2f0R334p=7g0047R4=413p=5g005;R5=413p=2g006BR6=413g007ER7'0p=1A4163p=8g007b9913P0g008]R8f1R9541%79%59%29%19'0'0'0f2R9#3P3A4189P1P8%33X11R8g00EJf3R:P3E6W0P3O1%79%59%29%19'0'0'0P0%7:%5:%2:%1:'0'0f4R:#3P3%7:P1P2P8g00FNf5R2P3E6W0P3O1%5:%2:%1:'0'0P0%52%22%12'0f6R2#3P3%52P1P4P8g00GPf7R4P3E6W0P3O1%22%12'0P0%24%14f8R4#3P3%24P1P5P8g00HRf9R5P3E6W0P3O1%14P0%85P7f:R5#3P3%85P1P6P8g00ITf;P3E6W0P3O1P7f<#3P3n010000000X07P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W0P3O1n200100000021000010000W2X11o"). Qed.

(* [comment removed for export] *)
Theorem rasteropLow_po_ok : rasteropLow_po.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_top ()) [] "p;1g00JXj10Tg00Ke#0o"). Qed.
