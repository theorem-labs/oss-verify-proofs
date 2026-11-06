(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

(* [comment removed for export] *)
Definition ti_hyps (tabval tab38 tab14 : Z) : Prop :=
  (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z.
Section TI.
Variable rom : word -> option byte.
Variables (tabval tab38 tab14 : Z).
Hypothesis HYP : ti_hyps tabval tab38 tab14.
Ltac dl_facts := pose proof HYP as (R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14); idtac.
(* [comment removed for export] *)
Lemma ti_1af90 : forall (fx : FPState) regs m ,
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b08c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b104) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 1
    /\ getr regs' 6 = Z_to_bv 64 127
    /\ getr regs' 7 = Z_to_bv 64 169
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 2
    /\ getr regs' 14 = Z_to_bv 64 87
    /\ getr regs' 15 = Z_to_bv 64 3
    /\ getr regs' 16 = Z_to_bv 64 42
    /\ getr regs' 17 = Z_to_bv 64 84
    /\ getr regs' 28 = Z_to_bv 64 212
    /\ getr regs' 29 = Z_to_bv 64 1024
    /\ getr regs' 30 = Z_to_bv 64 3
    /\ getr regs' 31 = Z_to_bv 64 2
    /\ regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  H19 H20 H21.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4]) by (ex_know regs).
  dl_run 400%nat [110852%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End TI.

Definition tl_1b008_cells_def (tabval tab38 tab14 i4 : Z) : list (Z * Z) := [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)].
(* [comment removed for export] *)
Definition tl_hyps (tabval tab38 tab14 i4 : Z) : Prop :=
  (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z /\ (0 <= i4 <= 1020)%Z /\ (i4 mod 4 = 0)%Z.
Section TL.
Variable rom : word -> option byte.
Variables (tabval tab38 tab14 i4 : Z).
Hypothesis HYP : tl_hyps tabval tab38 tab14 i4.
Ltac dl_facts := pose proof HYP as (R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14 & R_i4 & A_i4); idtac.
(* [comment removed for export] *)
Lemma tl_1b004f : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (i4 + 4)) (Z_to_bv 64 1024) = false ->
  getr regs 10 = Z_to_bv 64 (i4 + 4) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b100) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b104) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H19 H20 H21 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b004t : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (i4 + 4)) (Z_to_bv 64 1024) = true ->
  getr regs 10 = Z_to_bv 64 (i4 + 4) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b100) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b2b4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H19 H20 H21 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b008f : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 26) (getr regs 11) = false ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b104) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b10c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 22 = Z_to_bv 64 (tabval + i4)
    /\ regs_agree (fun r => In r [22]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H19 H20 H21 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b008t : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 26) (getr regs 11) = true ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b104) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 22 = Z_to_bv 64 0
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H10 H19 H20 H21 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b010f : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 16) (getr regs 11) = false ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b10c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b110) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b010t : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 16) (getr regs 11) = true ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b10c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b014f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 17) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b110) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b014t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 17) (getr regs 11) = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b110) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b150) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b054f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 6) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b150) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b054t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 6) (getr regs 11) = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b150) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b174) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b078f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 7) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b174) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b078t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 7) (getr regs 11) = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b174) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b1a4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b0a8f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 28) (getr regs 11) = false ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b1a4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z); ((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b0a8t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 28) (getr regs 11) = true ->
  store_ok SEGS m (Z_to_bv 64 (tabval + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b1a4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b1cc) m' rom)
    /\ mframe [((tabval + i4)%Z, 4%Z)] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b0d0f : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 11) (getr regs 12) = false ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b1cc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe [((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma tl_1b0d0t : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 11) (getr regs 12) = true ->
  store_ok SEGS m (Z_to_bv 64 (tab38 + i4)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (tab14 + i4)) 4 = true ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 22 = Z_to_bv 64 (tabval + i4) ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b1cc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe [((tab38 + i4)%Z, 4%Z); ((tab14 + i4)%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 22 = Z_to_bv 64 0
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 H10 H19 H20 H21 H22 H29.
  dl_facts.
  ex_entry regs [tabval; tab38; tab14; i4; (tabval + i4)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [tabval; tab38; tab14; i4; (tabval + i4)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 1020; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488356348]) by (ex_know regs).
  dl_run 400%nat [110848%Z; 110852%Z; 111284%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation tl_1b008_cells := (tl_1b008_cells_def tabval tab38 tab14 i4).
Lemma tl_1b008_path : forall (fx : FPState) regs m,
  cells_ok SEGS m tl_1b008_cells ->
  getr regs 10 = Z_to_bv 64 i4 ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 29 = Z_to_bv 64 1024 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b104) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b100) m' rom)
    /\ mframe tl_1b008_cells m m'
    /\ getr regs' 10 = Z_to_bv 64 (i4 + 4)
    /\ getr regs' 23 = Z_to_bv 64 (tab14 + i4)
    /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m CK  H10 H19 H20 H21 H29.
  pose proof (mframe_refl tl_1b008_cells m) as FK0.
  destruct (branch_taken BC_GEU (getr regs 26) (getr regs 11)) eqn:B0.
  - (* [comment removed for export] *)
    destruct (tl_1b008t fx regs m  B0 (cells_ok_sok SEGS m m tl_1b008_cells (tabval + i4)%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) (cells_ok_sok SEGS m m tl_1b008_cells (tab38 + i4)%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) (cells_ok_sok SEGS m m tl_1b008_cells (tab14 + i4)%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_10 & E1_22 & E1_23 & AG1).
    assert (FK1 : mframe tl_1b008_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold tl_1b008_cells_def; dl_incl).
    exists r1, m1. split; [exact RUN1|]. split; [exact FK1|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (tl_1b008f fx regs m  B0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_22 & AG1).
    assert (FK1 : mframe tl_1b008_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold tl_1b008_cells_def; dl_incl).
    destruct (branch_taken BC_GEU (getr r1 16) (getr r1 11)) eqn:B1.
    + (* [comment removed for export] *)
      destruct (tl_1b010t fx r1 m1  B1 (cells_ok_sok SEGS m m1 tl_1b008_cells (tabval + i4)%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) (cells_ok_sok SEGS m m1 tl_1b008_cells (tab38 + i4)%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) (cells_ok_sok SEGS m m1 tl_1b008_cells (tab14 + i4)%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_10 & E2_23 & AG2).
      assert (FK2 : mframe tl_1b008_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold tl_1b008_cells_def; dl_incl).
      exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (tl_1b010f fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
      assert (FK2 : mframe tl_1b008_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold tl_1b008_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (getr r2 17) (getr r2 11)) eqn:B2.
      * (* [comment removed for export] *)
        destruct (tl_1b014t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
        assert (FK3 : mframe tl_1b008_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold tl_1b008_cells_def; dl_incl).
        destruct (branch_taken BC_LTU (getr r3 6) (getr r3 11)) eqn:B3.
        -- (* [comment removed for export] *)
          destruct (tl_1b054t fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & AG4).
          assert (FK4 : mframe tl_1b008_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold tl_1b008_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r4 7) (getr r4 11)) eqn:B4.
          ++ (* [comment removed for export] *)
            destruct (tl_1b078t fx r4 m4  B4 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & AG5).
            assert (FK5 : mframe tl_1b008_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold tl_1b008_cells_def; dl_incl).
            destruct (branch_taken BC_LTU (getr r5 28) (getr r5 11)) eqn:B5.
            ** (* [comment removed for export] *)
              destruct (tl_1b0a8t fx r5 m5  B5 (cells_ok_sok SEGS m m5 tl_1b008_cells (tabval + i4)%Z 4%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & AG6).
              assert (FK6 : mframe tl_1b008_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold tl_1b008_cells_def; dl_incl).
              destruct (branch_taken BC_GEU (getr r6 11) (getr r6 12)) eqn:B6.
              --- (* [comment removed for export] *)
                destruct (tl_1b0d0t fx r6 m6  B6 (cells_ok_sok SEGS m m6 tl_1b008_cells (tab38 + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) (cells_ok_sok SEGS m m6 tl_1b008_cells (tab14 + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r7 & m7 & RUN7 & FR7 & E7_10 & E7_22 & E7_23 & AG7).
                assert (FK7 : mframe tl_1b008_cells m m7) by (apply (mframe_step _ _ _ _ _ FK6 FR7); unfold tl_1b008_cells_def; dl_incl).
                exists r7, m7. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6 RUN7))))))|]. split; [exact FK7|].
                repeat split; [dl_get .. | ra_chain].
              --- (* [comment removed for export] *)
                destruct (tl_1b0d0f fx r6 m6  B6 (cells_ok_sok SEGS m m6 tl_1b008_cells (tab38 + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) (cells_ok_sok SEGS m m6 tl_1b008_cells (tab14 + i4)%Z 4%Z CK (proj1 FK6) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r7 & m7 & RUN7 & FR7 & E7_10 & E7_23 & AG7).
                assert (FK7 : mframe tl_1b008_cells m m7) by (apply (mframe_step _ _ _ _ _ FK6 FR7); unfold tl_1b008_cells_def; dl_incl).
                exists r7, m7. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6 RUN7))))))|]. split; [exact FK7|].
                repeat split; [dl_get .. | ra_chain].
            ** (* [comment removed for export] *)
              destruct (tl_1b0a8f fx r5 m5  B5 (cells_ok_sok SEGS m m5 tl_1b008_cells (tabval + i4)%Z 4%Z CK (proj1 FK5) ltac:(dl_in0)) (cells_ok_sok SEGS m m5 tl_1b008_cells (tab38 + i4)%Z 4%Z CK (proj1 FK5) ltac:(dl_in0)) (cells_ok_sok SEGS m m5 tl_1b008_cells (tab14 + i4)%Z 4%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_10 & E6_23 & AG6).
              assert (FK6 : mframe tl_1b008_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold tl_1b008_cells_def; dl_incl).
              exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
              repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (tl_1b078f fx r4 m4  B4 (cells_ok_sok SEGS m m4 tl_1b008_cells (tabval + i4)%Z 4%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 tl_1b008_cells (tab38 + i4)%Z 4%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 tl_1b008_cells (tab14 + i4)%Z 4%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_10 & E5_23 & AG5).
            assert (FK5 : mframe tl_1b008_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold tl_1b008_cells_def; dl_incl).
            exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
            repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (tl_1b054f fx r3 m3  B3 (cells_ok_sok SEGS m m3 tl_1b008_cells (tabval + i4)%Z 4%Z CK (proj1 FK3) ltac:(dl_in0)) (cells_ok_sok SEGS m m3 tl_1b008_cells (tab38 + i4)%Z 4%Z CK (proj1 FK3) ltac:(dl_in0)) (cells_ok_sok SEGS m m3 tl_1b008_cells (tab14 + i4)%Z 4%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_10 & E4_23 & AG4).
          assert (FK4 : mframe tl_1b008_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold tl_1b008_cells_def; dl_incl).
          exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
          repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (tl_1b014f fx r2 m2  B2 (cells_ok_sok SEGS m m2 tl_1b008_cells (tabval + i4)%Z 4%Z CK (proj1 FK2) ltac:(dl_in0)) (cells_ok_sok SEGS m m2 tl_1b008_cells (tab38 + i4)%Z 4%Z CK (proj1 FK2) ltac:(dl_in0)) (cells_ok_sok SEGS m m2 tl_1b008_cells (tab14 + i4)%Z 4%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_23 & AG3).
        assert (FK3 : mframe tl_1b008_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold tl_1b008_cells_def; dl_incl).
        exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
        repeat split; [dl_get .. | ra_chain].
Qed.

End TL.

(* [comment removed for export] *)
Definition la_hyps (s datad datat bufs1 bufs2 w h wplt wpld cf : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wplt <= 5000)%Z /\ (1 <= wpld <= 1250)%Z /\ (0 <= cf <= 1)%Z.
Section LA.
Variable rom : word -> option byte.
Variables (s datad datat bufs1 bufs2 w h wplt wpld cf : Z).
Hypothesis HYP : la_hyps s datad datat bufs1 bufs2 w h wplt wpld cf.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_datat & A_datat & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_w & R_h & R_wplt & R_wpld & R_cf); idtac.
(* [comment removed for export] *)
Lemma la_1b1b8 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 cf) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b2b4) m rom) (@mkst fx regs' (Z_to_bv 64 0x2ac48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 111324
    /\ getr regs' 8 = Z_to_bv 64 h
    /\ getr regs' 10 = Z_to_bv 64 bufs2
    /\ getr regs' 11 = Z_to_bv 64 datat
    /\ getr regs' 12 = Z_to_bv 64 (wplt * 4)
    /\ getr regs' 23 = Z_to_bv 64 w
    /\ getr regs' 26 = Z_to_bv 64 (wplt * 4)
    /\ getr regs' 27 = Z_to_bv 64 268435455
    /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 23; 26; 27]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 KC4 KC5 KC6 H2 H9 H18.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; bufs2; w; h; wplt; wpld; cf] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; bufs2; w; h; wplt; wpld; cf]) m [KWord (SA (EVar 32) (-108)) 4 (EVar 37); KWord (SA (EVar 32) (-112)) 4 (EVar 38); KWord (SA (EVar 32) (-144)) 8 (EVar 41); KWord (SA (EVar 32) (-152)) 8 (EVar 33); KWord (SA (EVar 32) (-160)) 8 (EVar 40); KWord (SA (EVar 32) (-168)) 8 (EVar 34); KWord (SA (EVar 32) (-176)) 8 (EVar 39); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 1 20000; KRange (EVar 39) 1 5000; KRange (EVar 40) 1 1250; KRange (EVar 41) 0 1]) by (ex_know regs).
  dl_run 400%nat [175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LA.

(* [comment removed for export] *)
Definition lb_hyps (s w wplt : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= wplt <= 5000)%Z.
Section LB.
Variable rom : word -> option byte.
Variables (s w wplt : Z).
Hypothesis HYP : lb_hyps s w wplt.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_w & R_wplt); idtac.
(* [comment removed for export] *)
Lemma lb_1b1e0 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 184)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 w ->
  getr regs 26 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b2dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b510) m' rom)
    /\ mframe [((s - 184)%Z, 8%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 (w - 1)
    /\ getr regs' 10 = Z_to_bv 64 1
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ rdn SEGS m' (Z_to_bv 64 (s - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ regs_agree (fun r => In r [8; 10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 H2 H8 H23 H26.
  dl_facts.
  ex_entry regs [s; w; wplt] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; wplt]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 1 20000; KRange (EVar 34) 1 5000]) by (ex_know regs).
  dl_run 400%nat [111888%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

End LB.

(* [comment removed for export] *)
Definition lc_hyps (s w wplt h2 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= wplt <= 5000)%Z /\ (2 <= h2 <= 20000)%Z.
Section LC.
Variable rom : word -> option byte.
Variables (s w wplt h2 : Z).
Hypothesis HYP : lc_hyps s w wplt h2.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_w & R_wplt & R_h2); idtac.
(* [comment removed for export] *)
Lemma lc_1b1e0 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 184)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 192)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 h2 ->
  getr regs 23 = Z_to_bv 64 w ->
  getr regs 26 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b2dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b314) m' rom)
    /\ mframe [((s - 184)%Z, 8%Z); ((s - 192)%Z, 8%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 (w - 1)
    /\ getr regs' 10 = Z_to_bv 64 1
    /\ getr regs' 11 = Z_to_bv 64 (h2 - 1)
    /\ getr regs' 22 = Z_to_bv 64 0
    /\ getr regs' 25 = Z_to_bv 64 18446744072635809792
    /\ rdn SEGS m' (Z_to_bv 64 (s - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (h2 - 1)))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 192)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w - 1)))
    /\ regs_agree (fun r => In r [8; 10; 11; 22; 25]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 H2 H8 H23 H26.
  dl_facts.
  ex_entry regs [s; w; wplt; h2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; wplt; h2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 1 20000; KRange (EVar 34) 1 5000; KRange (EVar 35) 2 20000]) by (ex_know regs).
  dl_run 400%nat [111380%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End LC.

(* [comment removed for export] *)
Definition lr_hyps (s datat bufs1 bufs2 wplt i : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (1 <= wplt <= 5000)%Z /\ (0 <= i <= 19998)%Z /\ (0 <= (i + 1) * wplt < 2 ^ 24)%Z.
Section LR.
Variable rom : word -> option byte.
Variables (s datat bufs1 bufs2 wplt i : Z).
Hypothesis HYP : lr_hyps s datat bufs1 bufs2 wplt i.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datat & A_datat & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_wplt & R_i & Hps); idtac.
(* [comment removed for export] *)
Lemma lr_1b218 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 22 = Z_to_bv 64 i ->
  getr regs 26 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b314) m rom) (@mkst fx regs' (Z_to_bv 64 0x2ac48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 111400
    /\ getr regs' 10 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 bufs2
    /\ getr regs' 12 = Z_to_bv 64 (wplt * 4)
    /\ getr regs' 24 = Z_to_bv 64 i
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 24]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H9 H18 H22 H26.
  dl_facts.
  ex_entry regs [s; datat; bufs1; bufs2; wplt; i] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datat; bufs1; bufs2; wplt; i]) m [KWord (SA (EVar 32) (-168)) 8 (EVar 33); KWord (SA (EVar 32) (-176)) 8 (EVar 36); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 5000; KRange (EVar 37) 0 19998]) by (ex_know regs).
  dl_run 400%nat [175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma lr_1b22c : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 22 = Z_to_bv 64 i ->
  getr regs 24 = Z_to_bv 64 i ->
  getr regs 26 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b328) m rom) (@mkst fx regs' (Z_to_bv 64 0x2ac48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 111436
    /\ getr regs' 10 = Z_to_bv 64 bufs2
    /\ getr regs' 11 = Z_to_bv 64 (datat + (4 * ((i + 1) * wplt)))
    /\ getr regs' 12 = Z_to_bv 64 (wplt * 4)
    /\ getr regs' 22 = Z_to_bv 64 (i + 1)
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 22]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H9 H18 H22 H24 H26.
  dl_facts.
  ex_entry regs [s; datat; bufs1; bufs2; wplt; i] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datat; bufs1; bufs2; wplt; i]) m [KWord (SA (EVar 32) (-168)) 8 (EVar 33); KWord (SA (EVar 32) (-176)) 8 (EVar 36); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 5000; KRange (EVar 37) 0 19998]) by (ex_know regs).
  dl_run 400%nat [175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LR.

(* [comment removed for export] *)
Definition ld_hyps (s datad bufs1 bufs2 wpld i : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (1 <= wpld <= 1250)%Z /\ (0 <= i <= 19998)%Z /\ (0 <= i * wpld < 2 ^ 24)%Z.
Section LD.
Variable rom : word -> option byte.
Variables (s datad bufs1 bufs2 wpld i : Z).
Hypothesis HYP : ld_hyps s datad bufs1 bufs2 wpld i.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_wpld & R_i & Hpd); idtac.
(* [comment removed for export] *)
Lemma ld_1b250 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 23 = Z_to_bv 64 1 ->
  getr regs 24 = Z_to_bv 64 i ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b34c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b47c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 (datad + (4 * (i * wpld)))
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H9 H18 H23 H24.
  dl_facts.
  ex_entry regs [s; datad; bufs1; bufs2; wpld; i] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; bufs1; bufs2; wpld; i]) m [KWord (SA (EVar 32) (-152)) 8 (EVar 33); KWord (SA (EVar 32) (-160)) 8 (EVar 36); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 1250; KRange (EVar 37) 0 19998]) by (ex_know regs).
  dl_run 400%nat [111740%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LD.

(* [comment removed for export] *)
Definition le_hyps (s datad bufs1 bufs2 wpld i w2 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (1 <= wpld <= 1250)%Z /\ (0 <= i <= 19998)%Z /\ (2 <= w2 <= 20000)%Z /\ (0 <= i * wpld < 2 ^ 24)%Z.
Section LE.
Variable rom : word -> option byte.
Variables (s datad bufs1 bufs2 wpld i w2 : Z).
Hypothesis HYP : le_hyps s datad bufs1 bufs2 wpld i w2.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_wpld & R_i & R_w2 & Hpd); idtac.
(* [comment removed for export] *)
Lemma le_1b250 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 23 = Z_to_bv 64 w2 ->
  getr regs 24 = Z_to_bv 64 i ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b34c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b3b8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 (datad + (4 * (i * wpld)))
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 bufs1
    /\ getr regs' 14 = Z_to_bv 64 bufs2
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H9 H18 H23 H24.
  dl_facts.
  ex_entry regs [s; datad; bufs1; bufs2; wpld; i; w2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; bufs1; bufs2; wpld; i; w2]) m [KWord (SA (EVar 32) (-152)) 8 (EVar 33); KWord (SA (EVar 32) (-160)) 8 (EVar 36); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 1250; KRange (EVar 37) 0 19998; KRange (EVar 38) 2 20000]) by (ex_know regs).
  dl_run 400%nat [111544%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LE.

(* [comment removed for export] *)
Definition lw_hyps (s h1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (0 <= h1 <= 19999)%Z.
Section LW.
Variable rom : word -> option byte.
Variables (s h1 : Z).
Hypothesis HYP : lw_hyps s h1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_h1); idtac.
(* [comment removed for export] *)
Lemma lw_1b37c : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b478) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b47c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 11 = Z_to_bv 64 h1
    /\ regs_agree (fun r => In r [11]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2.
  dl_facts.
  ex_entry regs [s; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h1]) m [KWord (SA (EVar 32) (-192)) 8 (EVar 33); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111740%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LW.

(* [comment removed for export] *)
Definition ll_hyps (s i h1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (0 <= i <= 19998)%Z /\ (0 <= h1 <= 19999)%Z /\ (0 <= i < h1)%Z.
Section LL.
Variable rom : word -> option byte.
Variables (s i h1 : Z).
Hypothesis HYP : ll_hyps s i h1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_i & R_h1 & Hi); idtac.
(* [comment removed for export] *)
Lemma ll_1b210 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 22 = Z_to_bv 64 (i + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b30c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b310) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 h1
    /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2 H22.
  dl_facts.
  ex_entry regs [s; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; h1]) m [KWord (SA (EVar 32) (-184)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 0 19998; KRange (EVar 34) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111380%Z; 111884%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ll_1b214f : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h1) = false ->
  rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 10 = Z_to_bv 64 h1 ->
  getr regs 22 = Z_to_bv 64 (i + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b310) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b314) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 H2 H10 H22.
  dl_facts.
  ex_entry regs [s; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; h1]) m [KWord (SA (EVar 32) (-184)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 0 19998; KRange (EVar 34) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111380%Z; 111884%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ll_1b214t : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (i + 1)) (Z_to_bv 64 h1) = true ->
  rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 10 = Z_to_bv 64 h1 ->
  getr regs 22 = Z_to_bv 64 (i + 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b310) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b50c) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 H2 H10 H22.
  dl_facts.
  ex_entry regs [s; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; h1]) m [KWord (SA (EVar 32) (-184)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 0 19998; KRange (EVar 34) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111380%Z; 111884%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End LL.

(* [comment removed for export] *)
Definition lx_hyps (s h1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (0 <= h1 <= 19999)%Z.
Section LX.
Variable rom : word -> option byte.
Variables (s h1 : Z).
Hypothesis HYP : lx_hyps s h1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_h1); idtac.
(* [comment removed for export] *)
Lemma lx_1b410 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b50c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b510) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 8 = Z_to_bv 64 h1
    /\ regs_agree (fun r => In r [8]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 H2.
  dl_facts.
  ex_entry regs [s; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h1]) m [KWord (SA (EVar 32) (-192)) 8 (EVar 33); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 0 19999]) by (ex_know regs).
  dl_run 400%nat [111888%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LX.

(* [comment removed for export] *)
Definition lm_hyps (s bufs1 bufs2 wplt : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (1 <= wplt <= 5000)%Z.
Section LM.
Variable rom : word -> option byte.
Variables (s bufs1 bufs2 wplt : Z).
Hypothesis HYP : lm_hyps s bufs1 bufs2 wplt.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_wplt); idtac.
(* [comment removed for export] *)
Lemma lm_1b414 : forall (fx : FPState) regs m ,
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 26 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b510) m rom) (@mkst fx regs' (Z_to_bv 64 0x2ac48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 111904
    /\ getr regs' 10 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 bufs2
    /\ getr regs' 12 = Z_to_bv 64 (wplt * 4)
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  H2 H9 H18 H26.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; wplt] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; wplt]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 5000]) by (ex_know regs).
  dl_run 400%nat [175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LM.

(* [comment removed for export] *)
Definition ln_hyps (s datad bufs1 wpld h1 cf : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (1 <= wpld <= 1250)%Z /\ (0 <= h1 <= 19999)%Z /\ (0 <= cf <= 1)%Z /\ (0 <= h1 * wpld < 2 ^ 24)%Z.
Section LN.
Variable rom : word -> option byte.
Variables (s datad bufs1 wpld h1 cf : Z).
Hypothesis HYP : ln_hyps s datad bufs1 wpld h1 cf.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_bufs1 & A_bufs1 & R_wpld & R_h1 & R_cf & Hpd); idtac.
(* [comment removed for export] *)
Lemma ln_1b424 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 cf) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 23 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b520) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b600) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 8 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 (datad + (4 * (h1 * wpld)))
    /\ getr regs' 11 = Z_to_bv 64 cf
    /\ getr regs' 12 = Z_to_bv 64 datad
    /\ regs_agree (fun r => In r [8; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H9 H23.
  dl_facts.
  ex_entry regs [s; datad; bufs1; wpld; h1; cf] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; bufs1; wpld; h1; cf]) m [KWord (SA (EVar 32) (-144)) 8 (EVar 37); KWord (SA (EVar 32) (-152)) 8 (EVar 33); KWord (SA (EVar 32) (-160)) 8 (EVar 35); KWord (SA (EVar 32) (-184)) 8 (EVar 36); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 1250; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 1]) by (ex_know regs).
  dl_run 400%nat [112128%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LN.

(* [comment removed for export] *)
Definition lo_hyps (s datad bufs1 wpld h1 cf w2 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (1 <= wpld <= 1250)%Z /\ (0 <= h1 <= 19999)%Z /\ (0 <= cf <= 1)%Z /\ (2 <= w2 <= 20000)%Z /\ (0 <= h1 * wpld < 2 ^ 24)%Z.
Section LO.
Variable rom : word -> option byte.
Variables (s datad bufs1 wpld h1 cf w2 : Z).
Hypothesis HYP : lo_hyps s datad bufs1 wpld h1 cf w2.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_bufs1 & A_bufs1 & R_wpld & R_h1 & R_cf & R_w2 & Hpd); idtac.
(* [comment removed for export] *)
Lemma lo_1b424 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 cf) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 (w2 - 1) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 23 = Z_to_bv 64 w2 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b520) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b570) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 (datad + (4 * (h1 * wpld)))
    /\ getr regs' 11 = Z_to_bv 64 cf
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 14 = Z_to_bv 64 (w2 - 1)
    /\ getr regs' 15 = Z_to_bv 64 18446744072635809792
    /\ getr regs' 16 = Z_to_bv 64 bufs1
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H23.
  dl_facts.
  ex_entry regs [s; datad; bufs1; wpld; h1; cf; w2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; bufs1; wpld; h1; cf; w2]) m [KWord (SA (EVar 32) (-144)) 8 (EVar 37); KWord (SA (EVar 32) (-152)) 8 (EVar 33); KWord (SA (EVar 32) (-160)) 8 (EVar 35); KWord (SA (EVar 32) (-184)) 8 (EVar 36); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 1250; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 1; KRange (EVar 38) 2 20000]) by (ex_know regs).
  dl_run 400%nat [111984%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End LO.
