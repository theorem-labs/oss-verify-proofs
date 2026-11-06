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

Definition pf_1b2bc_cells_def (lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld : Z) : list (Z * Z) := [((bytea (bufs1 + j))%Z, 1%Z); ((lined + (4 * (j / 16)))%Z, 4%Z); ((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)].
(* [comment removed for export] *)
Definition pf_hyps (lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z /\ (0 <= j <= 19999)%Z /\ (1 <= w1 <= 19999)%Z /\ (0 <= j < w1)%Z /\ (w1 + 1 <= 4 * wpl)%Z /\ (w1 + 1 <= 16 * wpld)%Z /\ dapart lined (4 * wpld) bufs1 (4 * wpl) /\ dapart lined (4 * wpld) bufs2 (4 * wpl) /\ dapart lined (4 * wpld) tab38 1024 /\ dapart lined (4 * wpld) tab14 1024.
Section PF.
Variable rom : word -> option byte.
Variables (lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld : Z).
Hypothesis HYP : pf_hyps lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14 & R_j & R_w1 & Hj & Hwpl & Hwpld & AP_l1 & AP_l2 & AP_l38 & AP_l14); pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1]; destruct (al4_ex _ A_bufs2) as [cb2 Ecb2].
(* [comment removed for export] *)
Lemma pf_1b2b8f : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w1) = false ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 (j + 1) ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b3b4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b3b8) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H10 H12 H13 H14 H19 H20 H21 H27.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b2b8t : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w1) = true ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 (j + 1) ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b3b4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b478) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H10 H12 H13 H14 H19 H20 H21 H27.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b2bc : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte) (bs5 : list byte) (bs6 : list byte) (bs7 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 16)))) 4 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (tabval + (4 * (rdv false 1 bs0)))) 4 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some bs4 ->
  rdn SEGS m (Z_to_bv 64 (tab38 + (4 * (rdv false 1 bs0)))) 4 = Some bs5 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some bs6 ->
  rdn SEGS m (Z_to_bv 64 (tab14 + (4 * (rdv false 1 bs0)))) 4 = Some bs7 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 16)))) 4 = true ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b3b8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b440) m' rom)
    /\ mframe [((lined + (4 * (j / 16)))%Z, 4%Z)] m m'
    /\ getr regs' 13 = Z_to_bv 64 (bufs1 + j + 1)
    /\ getr regs' 14 = Z_to_bv 64 (bufs2 + j + 1)
    /\ getr regs' 15 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ getr regs' 16 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 17 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ getr regs' 28 = Z_to_bv 64 (rdv true 4 bs5)
    /\ getr regs' 29 = Z_to_bv 64 (rdv false 1 bs6)
    /\ getr regs' 30 = Z_to_bv 64 (rdv true 4 bs7)
    /\ regs_agree (fun r => In r [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 bs5 bs6 bs7 R0 R1 R2 R3 R4 R5 R6 R7 S0 H8 H10 H12 H13 H14 H19 H20 H21 H27.
  dl_facts.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  pose proof (rdv_u8 SEGS _ _ _ R3) as U3.
  pose proof (rdv_u8 SEGS _ _ _ R4) as U4.
  pose proof (rdv_u8 SEGS _ _ _ R6) as U6.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv false 1 bs3; rdv false 1 bs4; rdv true 4 bs5; rdv false 1 bs6; rdv true 4 bs7] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv false 1 bs3; rdv false 1 bs4; rdv true 4 bs5; rdv false 1 bs6; rdv true 4 bs7]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [] [EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48; EVar 49] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b344f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 28) (Z_to_bv 64 0) = false ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b440) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b448) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 28 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [28]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b344t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 28) (Z_to_bv 64 0) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b440) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b3b4) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 12 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 28]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b34cf : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 5) (Z_to_bv 64 255) = false ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b448) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b450) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [5]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b34ct : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 5) (Z_to_bv 64 255) = true ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b448) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b45c) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b354f : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 6) (Z_to_bv 64 255) = false ->
  getr regs 5 = Z_to_bv 64 255 ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b450) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b454) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b354t : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (getr regs 6) (Z_to_bv 64 255) = true ->
  getr regs 5 = Z_to_bv 64 255 ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b450) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b464) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 6 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [6]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b358f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 7) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b454) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b3b4) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 7 = Z_to_bv 64 255
    /\ getr regs' 12 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [7; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b358t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 7) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b454) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b3b4) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 12 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b360f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 6) (Z_to_bv 64 255) = false ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b45c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b464) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 6 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [6]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b360t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 6) (Z_to_bv 64 255) = true ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b45c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b454) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b368f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 7) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 6 = Z_to_bv 64 255 ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b464) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b3b4) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 7 = Z_to_bv 64 255
    /\ getr regs' 12 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [7; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H6 H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma pf_1b368t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 7) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 6 = Z_to_bv 64 255 ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j + 1) ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 16 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  getr regs 28 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b464) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b3b4) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 12 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H6 H8 H10 H12 H13 H14 H15 H16 H17 H19 H20 H21 H27 H28.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; (bufs1 + j)%Z; (bufs2 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 40) 4096 140737488375327; KRange (EVar 41) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [111540%Z; 111544%Z; 111736%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation pf_1b2bc_cells := (pf_1b2bc_cells_def lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld).
Lemma pf_1b2bc_path : forall (fx : FPState) regs m,
  cells_ok SEGS m pf_1b2bc_cells ->
  tab_rd SEGS false (fun _ => True) pf_1b2bc_cells m tabval ->
  tab_rd SEGS true (fun _ => True) pf_1b2bc_cells m tab38 ->
  tab_rd SEGS true (fun _ => True) pf_1b2bc_cells m tab14 ->
  getr regs 8 = Z_to_bv 64 w1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 j ->
  getr regs 13 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 14 = Z_to_bv 64 (bufs2 + j) ->
  getr regs 19 = Z_to_bv 64 tabval ->
  getr regs 20 = Z_to_bv 64 tab38 ->
  getr regs 21 = Z_to_bv 64 tab14 ->
  getr regs 27 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b3b8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b3b4) m' rom)
    /\ mframe pf_1b2bc_cells m m'
    /\ getr regs' 12 = Z_to_bv 64 (j + 1)
    /\ getr regs' 13 = Z_to_bv 64 (bufs1 + j + 1)
    /\ getr regs' 14 = Z_to_bv 64 (bufs2 + j + 1)
    /\ getr regs' 15 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ getr regs' 16 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 17 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_tabval_false TR_tab38_true TR_tab14_true H8 H10 H12 H13 H14 H19 H20 H21 H27.
  pose proof (mframe_refl pf_1b2bc_cells m) as FK0.
  destruct (cells_ok_read SEGS m m pf_1b2bc_cells (bytea (bufs1 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (cells_ok_read SEGS m m pf_1b2bc_cells (lined + (4 * (j / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_1 Rd1_1].
  destruct (TR_tabval_false m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_2 & Rd1_2 & TV1_2).
  destruct (cells_ok_read SEGS m m pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_3 Rd1_3].
  destruct (cells_ok_read SEGS m m pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_4 Rd1_4].
  destruct (TR_tab38_true m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_5 & Rd1_5 & TV1_5).
  destruct (cells_ok_read SEGS m m pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_6 Rd1_6].
  destruct (TR_tab14_true m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_7 & Rd1_7 & TV1_7).
  destruct (pf_1b2bc fx regs m bs1_0 bs1_1 bs1_2 bs1_3 bs1_4 bs1_5 bs1_6 bs1_7 Rd1_0 Rd1_1 Rd1_2 Rd1_3 Rd1_4 Rd1_5 Rd1_6 Rd1_7 (cells_ok_sok SEGS m m pf_1b2bc_cells (lined + (4 * (j / 16)))%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_13 & E1_14 & E1_15 & E1_16 & E1_17 & E1_28 & E1_29 & E1_30 & AG1).
  assert (FK1 : mframe pf_1b2bc_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold pf_1b2bc_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 28) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (pf_1b344t fx r1 m1  B1 (cells_ok_sok SEGS m m1 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK1) ltac:(dl_in0)) (cells_ok_sok SEGS m m1 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK1) ltac:(dl_in0)) (cells_ok_sok SEGS m m1 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_12 & AG2).
    assert (FK2 : mframe pf_1b2bc_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold pf_1b2bc_cells_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (pf_1b344f fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_28 & AG2).
    assert (FK2 : mframe pf_1b2bc_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold pf_1b2bc_cells_def; dl_incl).
    destruct (branch_taken BC_LTU (getr r2 5) (Z_to_bv 64 255)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (pf_1b34ct fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe pf_1b2bc_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pf_1b2bc_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (getr r3 6) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (pf_1b360t fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & AG4).
        assert (FK4 : mframe pf_1b2bc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold pf_1b2bc_cells_def; dl_incl).
        destruct (branch_taken BC_LT (getr r4 7) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (pf_1b358t fx r4 m4  B4 (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_12 & AG5).
          assert (FK5 : mframe pf_1b2bc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold pf_1b2bc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (pf_1b358f fx r4 m4  B4 (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_7 & E5_12 & AG5).
          assert (FK5 : mframe pf_1b2bc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold pf_1b2bc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (pf_1b360f fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_6 & AG4).
        assert (FK4 : mframe pf_1b2bc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold pf_1b2bc_cells_def; dl_incl).
        destruct (branch_taken BC_LT (getr r4 7) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (pf_1b368t fx r4 m4  B4 (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_12 & AG5).
          assert (FK5 : mframe pf_1b2bc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold pf_1b2bc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (pf_1b368f fx r4 m4  B4 (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_7 & E5_12 & AG5).
          assert (FK5 : mframe pf_1b2bc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold pf_1b2bc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (pf_1b34cf fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_5 & AG3).
      assert (FK3 : mframe pf_1b2bc_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold pf_1b2bc_cells_def; dl_incl).
      destruct (branch_taken BC_GEU (getr r3 6) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (pf_1b354t fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_6 & AG4).
        assert (FK4 : mframe pf_1b2bc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold pf_1b2bc_cells_def; dl_incl).
        destruct (branch_taken BC_LT (getr r4 7) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (pf_1b368t fx r4 m4  B4 (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_12 & AG5).
          assert (FK5 : mframe pf_1b2bc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold pf_1b2bc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (pf_1b368f fx r4 m4  B4 (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_7 & E5_12 & AG5).
          assert (FK5 : mframe pf_1b2bc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold pf_1b2bc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (pf_1b354f fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & AG4).
        assert (FK4 : mframe pf_1b2bc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold pf_1b2bc_cells_def; dl_incl).
        destruct (branch_taken BC_LT (getr r4 7) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (pf_1b358t fx r4 m4  B4 (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_12 & AG5).
          assert (FK5 : mframe pf_1b2bc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold pf_1b2bc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (pf_1b358f fx r4 m4  B4 (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 pf_1b2bc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_7 & E5_12 & AG5).
          assert (FK5 : mframe pf_1b2bc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold pf_1b2bc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
Qed.

End PF.
