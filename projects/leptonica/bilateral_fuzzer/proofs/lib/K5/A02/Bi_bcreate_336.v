(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_pixakit Bi_addkit Bi_relkit Bi_restore Bi_lskit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bcreate_defs Bi_bckit Bi_bcreate_cut Bi_bcreate_cut2 Bi_bckit2 Bi_bcreate_defs2 Bi_bcreate_cut336 Bi_bcreate_cut2_336 Bi_bcreate_a336 Bi_bcreate_b336 Bi_bcreate_c336.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_bcreate_336 () := "C46Stdlib5Lists4List2hdC69OSSVerify5KrLib2K53A02?Bi_bcreate_c336=bc_cutB336_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02?Bi_bcreate_b336=bc_cutA336_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02?Bi_bcreate_a336=bc_twin336_okC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BC336.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PCLONE : pixClone_cpsF RT.
Hypothesis PAMB : pixAddMirroredBorder_cps2 RT.
Hypothesis PGEV : pixGetExtremeValue_cps RT.
Hypothesis PDRC : pixDestroy_rc_cpsF RT.
Hypothesis PXD : pixDestroy_cpsF RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorPtr.
Hypothesis EXPF : expf_cps RT.
Hypothesis PACR : pixaCreate_n_cps RT.
Hypothesis PCOPY : pixCopy_nn_cpsF RT.
Hypothesis PCREATE : pixCreate_nn_cpsF RT.
Hypothesis PAADD : pixaAddPix_ins_cps RT.
Hypothesis PAGLP : pixaGetLinePtrs_cps RT.
Hypothesis LIT_MSG : exists l, In (0x2b060, l) LEPT_LITS.
Hypothesis LIT_FN : exists l, In (0x2b040, l) LEPT_LITS.
Hypothesis NCLOOP : bc_nc_loop_stmt.
Hypothesis KIDXLOOP : bc_kidx_stmt.
Hypothesis KFRLOOP : bc_kfr_stmt.
Hypothesis HPASS : bc_hpass_stmt.
Hypothesis VPASS : bc_vpass_stmt.

Theorem bc_twin336_full : bc_twin336_stmt RT.
Proof using AF GP FKC PCLONE PAMB PGEV PDRC PXD RERR EXPF PACR PCOPY PCREATE PAADD PAGLP LIT_MSG LIT_FN NCLOOP KIDXLOOP KFRLOOP HPASS VPASS.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_336 ()) ["BC336"] "p;Dp;7p;Fp-1p10000p4p710p8g000GlD2Tg001Pj71Tg002YlF0Tp,2RTR0p,2AFR1p,2GPR2p,3FKCR3p,6PCLONER4p,4PAMBR5p,4PGEVR6p,4PDRCR7p,3PXDR8p,4RERRR9p,4EXPFR:p,4PACRR;p,5PCOPYR<p,7PCREATER=p,5PAADDR>p,5PAGLPR?p,7LIT_MSGR@p,6LIT_FNRAp,6NCLOOPp,8KIDXLOOPp,7KFRLOOPP0P1P2P3P:P;P0P1P2P3P4P5P6P7P8P9P:P;P<P=P>P?p,5HPASSp,5VPASSP@PAMD2F1MF0o"). Qed.
End BC336.
