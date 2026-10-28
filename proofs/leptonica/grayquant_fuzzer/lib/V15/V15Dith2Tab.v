(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab DitherTabW.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

(* [comment removed for export] *)
Definition ui_hyps (tabval tab38 tab14 : Z) : Prop :=
  (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z.
Section UI.
Variable rom : word -> option byte.
Variables (tabval tab38 tab14 : Z).
Hypothesis HYP : ui_hyps tabval tab38 tab14.
Ltac dl_facts := pose proof HYP as (R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14); idtac.
(* [comment removed for export] *)
Lemma ui_1c75c : forall (fx : FPState) regs m ,
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c860) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8e0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 1
    /\ getr regs' 5 = Z_to_bv 64 0
    /\ getr regs' 6 = Z_to_bv 64 3
    /\ getr regs' 7 = Z_to_bv 64 87
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 13 = Z_to_bv 64 1
    /\ getr regs' 14 = Z_to_bv 64 1
    /\ getr regs' 15 = Z_to_bv 64 1
    /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0
    /\ getr regs' 19 = Z_to_bv 64 1
    /\ getr regs' 27 = Z_to_bv 64 1
    /\ getr regs' 28 = Z_to_bv 64 1024
    /\ getr regs' 29 = Z_to_bv 64 42
    /\ getr regs' 30 = Z_to_bv 64 2
    /\ getr regs' 31 = Z_to_bv 64 2
    /\ regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 24; 27; 28; 29; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  H20 H21 H22.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4]) by (ex_know regs).
  dl_run 400%nat [116960%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End UI.

Definition ul_1c7dc_cells_def (tabval tab38 tab14 i4 : Z) : list (Z * Z) := [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)].
(* [comment removed for export] *)
Definition ul_hyps (tabval tab38 tab14 i4 : Z) : Prop :=
  (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z /\ (0 <= i4 <= 1020)%Z /\ (i4 mod 4 = 0)%Z /\ dapart tabval 1024 tab38 1024 /\ dapart tabval 1024 tab14 1024 /\ dapart tab38 1024 tab14 1024.
Section UL.
Variable rom : word -> option byte.
Variables (tabval tab38 tab14 i4 : Z).
Hypothesis HYP : ul_hyps tabval tab38 tab14 i4.
Ltac dl_facts := pose proof HYP as (R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14 & R_i4 & A_i4 & AP_0_38 & AP_0_14 & AP_38_14); idtac.
(* [comment removed for export] *)
Lemma ul_1c7d8f : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (i4 + 4)) (Z_to_bv 64 1024) = false ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 (i4 + 4) ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c8dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8e0) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H1 H5 H10 H12 H13 H14 H15 H16 H17 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ul_1c7d8t : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (i4 + 4)) (Z_to_bv 64 1024) = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 (i4 + 4) ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c8dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1cc94) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H1 H5 H10 H12 H13 H14 H15 H16 H17 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ul_1c7dcf : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 26) (getr regs 11) = false ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c8e0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8e4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H1 H5 H10 H12 H13 H14 H15 H16 H17 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ul_1c7dct : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 26) (getr regs 11) = true ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c8e0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 31]%list) regs regs'
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v)
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v).
Proof using All.
  intros fx regs m  BT S0 S1 S2 H1 H5 H10 H12 H13 H14 H15 H16 H17 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [true; false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [ex_agree HR HR'|].
  split; [(eexists; split; [dl_saved0 | dl_tvw])|].
  (eexists; split; [dl_saved0 | dl_tvw]).
Qed.

(* [comment removed for export] *)
Lemma ul_1c7e0f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 29) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c8e4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 19 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 31]%list) regs regs'
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v)
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v).
Proof using All.
  intros fx regs m  BT S0 S1 S2 H1 H5 H10 H12 H13 H14 H15 H16 H17 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [ex_agree HR HR'|].
  split; [(eexists; split; [dl_saved0 | dl_tvw])|].
  (eexists; split; [dl_saved0 | dl_tvw]).
Qed.

(* [comment removed for export] *)
Lemma ul_1c7e0t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 29) (getr regs 11) = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c8e4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c994) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 19 = Z_to_bv 64 84
    /\ regs_agree (fun r => In r [19]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H1 H5 H10 H12 H13 H14 H15 H16 H17 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ul_1c890f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (Z_to_bv 64 84) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 84 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c994) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 19 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 31]%list) regs regs'
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v)
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v).
Proof using All.
  intros fx regs m  BT S0 S1 S2 H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [ex_agree HR HR'|].
  split; [(eexists; split; [dl_saved0 | dl_tvw])|].
  (eexists; split; [dl_saved0 | dl_tvw]).
Qed.

(* [comment removed for export] *)
Lemma ul_1c890t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (Z_to_bv 64 84) (getr regs 11) = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 84 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c994) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c9f4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 19 = Z_to_bv 64 127
    /\ regs_agree (fun r => In r [19]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ul_1c8f0f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (Z_to_bv 64 127) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 127 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c9f4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 19 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 31]%list) regs regs'
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v)
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v).
Proof using All.
  intros fx regs m  BT S0 S1 S2 H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [ex_agree HR HR'|].
  split; [(eexists; split; [dl_saved0 | dl_tvw])|].
  (eexists; split; [dl_saved0 | dl_tvw]).
Qed.

(* [comment removed for export] *)
Lemma ul_1c8f0t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (Z_to_bv 64 127) (getr regs 11) = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 127 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c9f4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ca58) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 19 = Z_to_bv 64 169
    /\ regs_agree (fun r => In r [19]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ul_1c954f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (Z_to_bv 64 169) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 169 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ca58) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 19 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 31]%list) regs regs'
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v)
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v).
Proof using All.
  intros fx regs m  BT S0 S1 S2 H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [ex_agree HR HR'|].
  split; [(eexists; split; [dl_saved0 | dl_tvw])|].
  (eexists; split; [dl_saved0 | dl_tvw]).
Qed.

(* [comment removed for export] *)
Lemma ul_1c954t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (Z_to_bv 64 169) (getr regs 11) = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 169 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ca58) m rom) (@mkst fx regs' (Z_to_bv 64 0x1cac0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 19 = Z_to_bv 64 212
    /\ regs_agree (fun r => In r [19]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ul_1c9bcf : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (Z_to_bv 64 212) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 212 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cac0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 19 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 31]%list) regs regs'
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v)
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v).
Proof using All.
  intros fx regs m  BT S0 S1 S2 H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [ex_agree HR HR'|].
  split; [(eexists; split; [dl_saved0 | dl_tvw])|].
  (eexists; split; [dl_saved0 | dl_tvw]).
Qed.

(* [comment removed for export] *)
Lemma ul_1c9bct : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (Z_to_bv 64 212) (getr regs 11) = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 212 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cac0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1cb38) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 19 = Z_to_bv 64 (tabval + i4)
    /\ getr regs' 23 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [19; 23; 30]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ul_1ca34f : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 11) (getr regs 30) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 (tabval + i4) ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 23 = Z_to_bv 64 1 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cb38) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 19 = Z_to_bv 64 (tab14 + i4)
    /\ getr regs' 30 = Z_to_bv 64 2
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 30; 31]%list) regs regs'
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v)
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v).
Proof using All.
  intros fx regs m  BT S0 S1 S2 H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H23 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [ex_agree HR HR'|].
  split; [(eexists; split; [dl_saved0 | dl_tvw])|].
  (eexists; split; [dl_saved0 | dl_tvw]).
Qed.

(* [comment removed for export] *)
Lemma ul_1ca34t : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 11) (getr regs 30) = true ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 (tabval + i4) ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 23 = Z_to_bv 64 1 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cb38) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 19 = Z_to_bv 64 (tab14 + i4)
    /\ getr regs' 23 = Z_to_bv 64 3
    /\ getr regs' 30 = Z_to_bv 64 2
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 30; 31]%list) regs regs'
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v)
    /\ (exists v : word, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some (word_to_le_bytes 4 v) /\ tvw_ok v).
Proof using All.
  intros fx regs m  BT S0 S1 S2 H1 H5 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H23 H27 H28.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [116956%Z; 116960%Z; 117908%Z] (SCR [true; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [dl_reg regs HR'|].
  split; [ex_agree HR HR'|].
  split; [(eexists; split; [dl_saved0 | dl_tvw])|].
  (eexists; split; [dl_saved0 | dl_tvw]).
Qed.

(* [comment removed for export] *)
Local Abbreviation ul_1c7dc_cells := (ul_1c7dc_cells_def tabval tab38 tab14 i4).
Lemma ul_1c7dc_path : forall (fx : FPState) regs m,
  cells_ok SEGS m ul_1c7dc_cells ->
  getr regs 1 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0 ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 12 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 0 ->
  getr regs 17 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c8e0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c8dc) m' rom)
    /\ mframe ul_1c7dc_cells m m'
    /\ (exists bs, rdn SEGS m' (Z_to_bv 64 (tab38 + i4)) 4 = Some bs /\ tv_ok (rdv true 4 bs))
    /\ (exists bs, rdn SEGS m' (Z_to_bv 64 (tab14 + i4)) 4 = Some bs /\ tv_ok (rdv true 4 bs))
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m CK  H1 H5 H10 H12 H13 H14 H15 H16 H17 H20 H21 H22 H27 H28.
  pose proof (mframe_refl ul_1c7dc_cells m) as FK0.
  destruct (branch_taken BC_GEU (getr regs 26) (getr regs 11)) eqn:B0.
  - (* [comment removed for export] *)
    destruct (ul_1c7dct fx regs m  B0 (cells_ok_sok SEGS m m ul_1c7dc_cells (tabval + i4)%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) (cells_ok_sok SEGS m m ul_1c7dc_cells (tab38 + i4)%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) (cells_ok_sok SEGS m m ul_1c7dc_cells (tab14 + i4)%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_10 & E1_23 & AG1 & TS1_0 & TS1_1).
    assert (FK1 : mframe ul_1c7dc_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold ul_1c7dc_cells_def; dl_incl).
    exists r1, m1. split; [exact RUN1|]. split; [exact FK1|].
    split; [destruct TS1_0 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
    split; [destruct TS1_1 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (ul_1c7dcf fx regs m  B0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & AG1).
    assert (FK1 : mframe ul_1c7dc_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold ul_1c7dc_cells_def; dl_incl).
    destruct (branch_taken BC_LTU (getr r1 29) (getr r1 11)) eqn:B1.
    + (* [comment removed for export] *)
      destruct (ul_1c7e0t fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_19 & AG2).
      assert (FK2 : mframe ul_1c7dc_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold ul_1c7dc_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (Z_to_bv 64 84) (getr r2 11)) eqn:B2.
      * (* [comment removed for export] *)
        destruct (ul_1c890t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_19 & AG3).
        assert (FK3 : mframe ul_1c7dc_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold ul_1c7dc_cells_def; dl_incl).
        destruct (branch_taken BC_LTU (Z_to_bv 64 127) (getr r3 11)) eqn:B3.
        -- (* [comment removed for export] *)
          destruct (ul_1c8f0t fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_19 & AG4).
          assert (FK4 : mframe ul_1c7dc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold ul_1c7dc_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (Z_to_bv 64 169) (getr r4 11)) eqn:B4.
          ++ (* [comment removed for export] *)
            destruct (ul_1c954t fx r4 m4  B4 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_19 & AG5).
            assert (FK5 : mframe ul_1c7dc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold ul_1c7dc_cells_def; dl_incl).
            destruct (branch_taken BC_LTU (Z_to_bv 64 212) (getr r5 11)) eqn:B5.
            ** (* [comment removed for export] *)
              destruct (ul_1c9bct fx r5 m5  B5 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_19 & E6_23 & AG6).
              assert (FK6 : mframe ul_1c7dc_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold ul_1c7dc_cells_def; dl_incl).
              destruct (branch_taken BC_GEU (getr r6 11) (getr r6 30)) eqn:B6.
              --- (* [comment removed for export] *)
                destruct (ul_1ca34t fx r6 m6  B6 (cells_ok_sok SEGS m m6 ul_1c7dc_cells (tabval + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) (cells_ok_sok SEGS m m6 ul_1c7dc_cells (tab38 + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) (cells_ok_sok SEGS m m6 ul_1c7dc_cells (tab14 + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r7 & m7 & RUN7 & FR7 & E7_10 & E7_19 & E7_23 & E7_30 & AG7 & TS7_0 & TS7_1).
                assert (FK7 : mframe ul_1c7dc_cells m m7) by (apply (mframe_step _ _ _ _ _ FK6 FR7); unfold ul_1c7dc_cells_def; dl_incl).
                exists r7, m7. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6 RUN7))))))|]. split; [exact FK7|].
                split; [destruct TS7_0 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
                split; [destruct TS7_1 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
                repeat split; [dl_get .. | ra_chain].
              --- (* [comment removed for export] *)
                destruct (ul_1ca34f fx r6 m6  B6 (cells_ok_sok SEGS m m6 ul_1c7dc_cells (tabval + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) (cells_ok_sok SEGS m m6 ul_1c7dc_cells (tab38 + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) (cells_ok_sok SEGS m m6 ul_1c7dc_cells (tab14 + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r7 & m7 & RUN7 & FR7 & E7_10 & E7_19 & E7_30 & AG7 & TS7_0 & TS7_1).
                assert (FK7 : mframe ul_1c7dc_cells m m7) by (apply (mframe_step _ _ _ _ _ FK6 FR7); unfold ul_1c7dc_cells_def; dl_incl).
                exists r7, m7. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6 RUN7))))))|]. split; [exact FK7|].
                split; [destruct TS7_0 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
                split; [destruct TS7_1 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
                repeat split; [dl_get .. | ra_chain].
            ** (* [comment removed for export] *)
              destruct (ul_1c9bcf fx r5 m5  B5 (cells_ok_sok SEGS m m5 ul_1c7dc_cells (tabval + i4)%Z 4%Z CK (proj1 FK5) ltac:(dl_in0)) (cells_ok_sok SEGS m m5 ul_1c7dc_cells (tab38 + i4)%Z 4%Z CK (proj1 FK5) ltac:(dl_in0)) (cells_ok_sok SEGS m m5 ul_1c7dc_cells (tab14 + i4)%Z 4%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_10 & E6_19 & AG6 & TS6_0 & TS6_1).
              assert (FK6 : mframe ul_1c7dc_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold ul_1c7dc_cells_def; dl_incl).
              exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
              split; [destruct TS6_0 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
              split; [destruct TS6_1 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
              repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (ul_1c954f fx r4 m4  B4 (cells_ok_sok SEGS m m4 ul_1c7dc_cells (tabval + i4)%Z 4%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 ul_1c7dc_cells (tab38 + i4)%Z 4%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 ul_1c7dc_cells (tab14 + i4)%Z 4%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_10 & E5_19 & AG5 & TS5_0 & TS5_1).
            assert (FK5 : mframe ul_1c7dc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold ul_1c7dc_cells_def; dl_incl).
            exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
            split; [destruct TS5_0 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
            split; [destruct TS5_1 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
            repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (ul_1c8f0f fx r3 m3  B3 (cells_ok_sok SEGS m m3 ul_1c7dc_cells (tabval + i4)%Z 4%Z CK (proj1 FK3) ltac:(dl_in0)) (cells_ok_sok SEGS m m3 ul_1c7dc_cells (tab38 + i4)%Z 4%Z CK (proj1 FK3) ltac:(dl_in0)) (cells_ok_sok SEGS m m3 ul_1c7dc_cells (tab14 + i4)%Z 4%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_10 & E4_19 & AG4 & TS4_0 & TS4_1).
          assert (FK4 : mframe ul_1c7dc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold ul_1c7dc_cells_def; dl_incl).
          exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
          split; [destruct TS4_0 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
          split; [destruct TS4_1 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
          repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (ul_1c890f fx r2 m2  B2 (cells_ok_sok SEGS m m2 ul_1c7dc_cells (tabval + i4)%Z 4%Z CK (proj1 FK2) ltac:(dl_in0)) (cells_ok_sok SEGS m m2 ul_1c7dc_cells (tab38 + i4)%Z 4%Z CK (proj1 FK2) ltac:(dl_in0)) (cells_ok_sok SEGS m m2 ul_1c7dc_cells (tab14 + i4)%Z 4%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_19 & AG3 & TS3_0 & TS3_1).
        assert (FK3 : mframe ul_1c7dc_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold ul_1c7dc_cells_def; dl_incl).
        exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
        split; [destruct TS3_0 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
        split; [destruct TS3_1 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
        repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (ul_1c7e0f fx r1 m1  B1 (cells_ok_sok SEGS m m1 ul_1c7dc_cells (tabval + i4)%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) (cells_ok_sok SEGS m m1 ul_1c7dc_cells (tab38 + i4)%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) (cells_ok_sok SEGS m m1 ul_1c7dc_cells (tab14 + i4)%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_10 & E2_19 & AG2 & TS2_0 & TS2_1).
      assert (FK2 : mframe ul_1c7dc_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold ul_1c7dc_cells_def; dl_incl).
      exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
      split; [destruct TS2_0 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
      split; [destruct TS2_1 as (v_ & RV_ & TW_); exists (word_to_le_bytes 4 v_); split; [exact RV_ | exact TW_]|].
      repeat split; [dl_get .. | ra_chain].
Qed.

End UL.
