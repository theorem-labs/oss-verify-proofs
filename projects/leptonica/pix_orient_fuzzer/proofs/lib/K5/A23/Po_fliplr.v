(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_env Pm_iface Cf_iface RT_fk RT_fk_iface
  Bi_iface Bi_fktw Bi_iface2 D_iface D_defs Po_rows Po_iface Po_hip_defs Po_fliptb_defs Po_fliplr_defs Po_fliplr_c0 Po_fliplr_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_fliplr () := "C69OSSVerify5KrLib2K53A23<Po_fliplr_c09fliplr_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_fliplr_c16:fliplr_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>Po_fliplr_defsBpixFlipLR_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section FLIPLR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PCS : pixCopy_same_cps RT.
Hypothesis HIP : rasteropHipLow2_cps RT.

Theorem pixFlipLR_ok : pixFlipLR2_cps RT.
Proof using AF GP FKC PCS HIP.
ltac2:(KReplay.run1 (kr_t_Po_fliplr ()) ["FLIPLR"] "p;6p;3g0000j62Tg0012j61Tg0026j30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3PCSR4p,3HIPR5E2P0P1P2P3P4P5E130o"). Qed.
End FLIPLR.
