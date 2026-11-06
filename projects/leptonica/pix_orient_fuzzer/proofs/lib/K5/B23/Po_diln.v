(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_env Pm_iface Cf_iface RT_fk RT_fk_iface
  Bi_iface Bi_fktw Bi_iface2 D_iface D_defs Po_rows Po_iface Po_null_defs Po_diln_c0 Po_diln_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_diln () := "C69OSSVerify5KrLib2K53B23:Po_diln_c07diln_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Po_diln_c168diln_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<Po_null_defsDmorph_null0_of_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface;e_pixDilateC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section MORPHN.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PMAN : pma1_null_cps RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorPtr.

Theorem pixDilate_null0_ok : pixDilate_null0_cps RT.
Proof using AF GP FKC PMAN RERR.
ltac2:(KReplay.run1 (kr_t_Po_diln ()) ["MORPHN"] "p;6p;4g0000j62Tg000nj61Tg001nj40Tp,2RTR0g003;P0p,2AFR1p,2GPR2p,3FKCR3p,4PMANR4p,4RERRR5E2P0P1P2P3P4P5E1C0o"). Qed.
End MORPHN.
