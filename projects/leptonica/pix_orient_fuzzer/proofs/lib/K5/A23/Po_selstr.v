(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface RT_fk RT_fk_iface Po_rows Po_iface Po_selcreate Po_selstr_defs Po_selstr_k1 Po_selstr_k2 Po_selstr_k3 Po_selstr_k4.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_selstr () := "C69OSSVerify5KrLib2K53A23<Po_selstr_k19selstr_k1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_selstr_k29selstr_k2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_selstr_k39selstr_k3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_selstr_k49selstr_k4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>Po_selstr_defsLselCreateFromString_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SELSTR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis SCR : selCreate2_cps RT.
Hypothesis SSE : selSetElement_cps RT.
Hypothesis ACCTSEL : forall k Σ m, 1 <= k <= 4 -> ART RT Σ m -> acc asegs m (A_TSEL k) 31.

Theorem selCreateFromString_ok : selCreateFromString_cps RT.
Proof using AF GP FKC SCR SSE ACCTSEL.
ltac2:(KReplay.run1 (kr_t_Po_selstr ()) ["SELSTR"] "p;7p;5g0000j74Tg0012j73Tg0024j70Tg0036j71Tg0048j52Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3SCRR4p,3SSER5p,7ACCTSELR6F4P0P1P2P3P4P5P6F3P0P1P2P3P4P5P6F0P0P1P2P3P4P5P6F1D2o"). Qed.

End SELSTR.
