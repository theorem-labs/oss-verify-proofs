(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac.
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

Definition v0_1bcc0_cells_def (lined bufs1 bufs2 j w1 lc uc wpl : Z) : list (Z * Z) := [((bytea (bufs1 + j))%Z, 1%Z); ((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z); ((lined + (4 * (j / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition v0_hyps (lined bufs1 bufs2 j w1 lc uc wpl : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (0 <= j <= 19999)%Z /\ (1 <= w1 <= 19999)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (0 <= j < w1)%Z /\ (bufs1 + 4 * wpl <= bufs2 \/ bufs2 + 4 * wpl <= bufs1)%Z /\ (w1 + 1 <= 4 * wpl)%Z.
Section V0.
Variable rom : word -> option byte.
Variables (lined bufs1 bufs2 j w1 lc uc wpl : Z).
Hypothesis HYP : v0_hyps lined bufs1 bufs2 j w1 lc uc wpl.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_j & R_w1 & R_lc & R_uc & Hj & DJ12 & Hwpl); pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1]; destruct (al4_ex _ A_bufs2) as [cb2 Ecb2].
(* [comment removed for export] *)
Lemma v0_1bcbcf : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = false ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 (j + 1) ->
  getr regs 17 = Z_to_bv 64 (j + 1) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bdc0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bdc4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bcbct : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 (j + 1) ->
  getr regs 17 = Z_to_bv 64 (j + 1) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bdc0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf68) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bcc0 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j))) 1 = Some bs0 ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bdc4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bde8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bufs1 + j)
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 1 bs0)
    /\ regs_agree (fun r => In r [8; 9; 18]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bce4f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LT (getr regs 8) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bde8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1be28) m' rom)
    /\ mframe [((lined + (4 * (j / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 19 = Z_to_bv 64 (lined + (4 * (j / 32)))
    /\ regs_agree (fun r => In r [19; 20; 21]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv true 4 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [false; false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bce4t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 8) (Z_to_bv 64 0) = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bde8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bedc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [8]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bd24f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 18) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs0 ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 19 = Z_to_bv 64 (lined + (4 * (j / 32))) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1be28) m rom) (@mkst fx regs' (Z_to_bv 64 0x1be5c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 9 = Z_to_bv 64 255
    /\ getr regs' 19 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ regs_agree (fun r => In r [9; 18; 19; 20]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H19 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [false; false; false; false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bd24t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 18) = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 19 = Z_to_bv 64 (lined + (4 * (j / 32))) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1be28) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bdc0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H19 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bd58f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LTU (getr regs 20) (Z_to_bv 64 255) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 255 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1be5c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1be90) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bufs2 + j)
    /\ getr regs' 18 = Z_to_bv 64 255
    /\ getr regs' 19 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [9; 18; 19; 20]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H19 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [false; false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bd58t : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LTU (getr regs 20) (Z_to_bv 64 255) = true ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 255 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1be5c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1be90) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bufs2 + j)
    /\ getr regs' 18 = Z_to_bv 64 255
    /\ getr regs' 19 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some (word_to_le_bytes 1 (getr regs 20))
    /\ regs_agree (fun r => In r [9; 18; 19; 20]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H19 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [true; false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bd8cf : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LTU (getr regs 20) (Z_to_bv 64 255) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bufs2 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 18 = Z_to_bv 64 255 ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1be90) m rom) (@mkst fx regs' (Z_to_bv 64 0x1becc) m' rom)
    /\ mframe [((bytea (bufs2 + j))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ getr regs' 20 = Z_to_bv 64 255
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [8; 9; 20]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [false; false; false; false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bd8ct : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LTU (getr regs 20) (Z_to_bv 64 255) = true ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bufs2 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 18 = Z_to_bv 64 255 ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1be90) m rom) (@mkst fx regs' (Z_to_bv 64 0x1becc) m' rom)
    /\ mframe [((bytea (bufs2 + j))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some (word_to_le_bytes 1 (getr regs 20))
    /\ regs_agree (fun r => In r [8; 9]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [true; false; false; false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bdc8f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 8) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 18 = Z_to_bv 64 255 ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1becc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bdc0) m' rom)
    /\ mframe [((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 255
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (j + 1)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [8; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bdc8t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 8) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 18 = Z_to_bv 64 255 ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1becc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bdc0) m' rom)
    /\ mframe [((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (j + 1)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some (word_to_le_bytes 1 (getr regs 8))
    /\ regs_agree (fun r => In r [16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bdd8f : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte),
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 8) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some bs2 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bedc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bdc0) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (j + 1)
    /\ getr regs' 19 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ regs_agree (fun r => In r [8; 9; 16; 17; 18; 19; 20]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 BT R0 R1 R2 S0 S1 S2 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0; rdv false 1 bs1; rdv false 1 bs2] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0; rdv false 1 bs1; rdv false 1 bs2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [false; false; false; false; false; false] [EVar 39; EVar 40; EVar 41] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1bdd8t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 8) = true ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bedc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bdc0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [114112%Z; 114116%Z; 114536%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation v0_1bcc0_cells := (v0_1bcc0_cells_def lined bufs1 bufs2 j w1 lc uc wpl).
Lemma v0_1bcc0_path : forall (fx : FPState) regs m,
  cells_ok SEGS m v0_1bcc0_cells ->
  getr regs 5 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 2 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 1 ->
  getr regs 30 = Z_to_bv 64 134217727 ->
  getr regs 31 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bdc4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bdc0) m' rom)
    /\ mframe v0_1bcc0_cells m m'
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [8; 9; 16; 17; 18; 19; 20; 21]%list) regs regs'.
Proof using All.
  intros fx regs m CK H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
  pose proof (mframe_refl v0_1bcc0_cells m) as FK0.
  destruct (cells_ok_read SEGS m m v0_1bcc0_cells (bytea (bufs1 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (v0_1bcc0 fx regs m bs1_0 Rd1_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_9 & E1_18 & AG1).
  assert (FK1 : mframe v0_1bcc0_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold v0_1bcc0_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 8) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (v0_1bce4t fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe v0_1bcc0_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold v0_1bcc0_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 uc) (getr r2 8)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (v0_1bdd8t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_16 & E3_17 & AG3).
      assert (FK3 : mframe v0_1bcc0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v0_1bcc0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 v0_1bcc0_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (cells_ok_read SEGS m m2 v0_1bcc0_cells (bytea (bufs2 + j))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_1 Rd3_1].
      destruct (cells_ok_read SEGS m m2 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_2 Rd3_2].
      destruct (v0_1bdd8f fx r2 m2 bs3_0 bs3_1 bs3_2 B2 Rd3_0 Rd3_1 Rd3_2 (cells_ok_sok SEGS m m2 v0_1bcc0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) (cells_ok_sok SEGS m m2 v0_1bcc0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) (cells_ok_sok SEGS m m2 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_9 & E3_16 & E3_17 & E3_19 & AG3).
      assert (FK3 : mframe v0_1bcc0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v0_1bcc0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 v0_1bcc0_cells (lined + (4 * (j / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (v0_1bce4f fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 v0_1bcc0_cells (lined + (4 * (j / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_19 & AG2).
    assert (FK2 : mframe v0_1bcc0_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold v0_1bcc0_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 lc) (getr r2 18)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (v0_1bd24t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_16 & E3_17 & AG3).
      assert (FK3 : mframe v0_1bcc0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v0_1bcc0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 v0_1bcc0_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (v0_1bd24f fx r2 m2 bs3_0 B2 Rd3_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_9 & E3_19 & AG3).
      assert (FK3 : mframe v0_1bcc0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v0_1bcc0_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (getr r3 20) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (cells_ok_read SEGS m m3 v0_1bcc0_cells (bytea (bufs2 + j))%Z 1%Z wr_readable_img CK (proj1 FK3) ltac:(dl_in0)) as [bs4_0 Rd4_0].
        destruct (v0_1bd58t fx r3 m3 bs4_0 B3 Rd4_0 (cells_ok_sok SEGS m m3 v0_1bcc0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_9 & E4_18 & E4_19 & SV4_0 & AG4).
        assert (FK4 : mframe v0_1bcc0_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold v0_1bcc0_cells_def; dl_incl).
        destruct (branch_taken BC_LTU (getr r4 20) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (cells_ok_read SEGS m m4 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK4) ltac:(dl_in0)) as [bs5_0 Rd5_0].
          destruct (v0_1bd8ct fx r4 m4 bs5_0 B4 Rd5_0 (cells_ok_sok SEGS m m4 v0_1bcc0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_9 & SV5_0 & AG5).
          assert (FK5 : mframe v0_1bcc0_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1bcc0_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r5 8) (Z_to_bv 64 255)) eqn:B5.
          ++ (* [comment removed for export] *)
            destruct (v0_1bdc8t fx r5 m5  B5 (cells_ok_sok SEGS m m5 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_16 & E6_17 & SV6_0 & AG6).
            assert (FK6 : mframe v0_1bcc0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold v0_1bcc0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (v0_1bdc8f fx r5 m5  B5 (cells_ok_sok SEGS m m5 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_8 & E6_16 & E6_17 & SV6_0 & AG6).
            assert (FK6 : mframe v0_1bcc0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold v0_1bcc0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (cells_ok_read SEGS m m4 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK4) ltac:(dl_in0)) as [bs5_0 Rd5_0].
          destruct (v0_1bd8cf fx r4 m4 bs5_0 B4 Rd5_0 (cells_ok_sok SEGS m m4 v0_1bcc0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_9 & E5_20 & SV5_0 & AG5).
          assert (FK5 : mframe v0_1bcc0_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1bcc0_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r5 8) (Z_to_bv 64 255)) eqn:B5.
          ++ (* [comment removed for export] *)
            destruct (v0_1bdc8t fx r5 m5  B5 (cells_ok_sok SEGS m m5 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_16 & E6_17 & SV6_0 & AG6).
            assert (FK6 : mframe v0_1bcc0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold v0_1bcc0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (v0_1bdc8f fx r5 m5  B5 (cells_ok_sok SEGS m m5 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_8 & E6_16 & E6_17 & SV6_0 & AG6).
            assert (FK6 : mframe v0_1bcc0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold v0_1bcc0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (cells_ok_read SEGS m m3 v0_1bcc0_cells (bytea (bufs2 + j))%Z 1%Z wr_readable_img CK (proj1 FK3) ltac:(dl_in0)) as [bs4_0 Rd4_0].
        destruct (v0_1bd58f fx r3 m3 bs4_0 B3 Rd4_0 (cells_ok_sok SEGS m m3 v0_1bcc0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_9 & E4_18 & E4_19 & SV4_0 & AG4).
        assert (FK4 : mframe v0_1bcc0_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold v0_1bcc0_cells_def; dl_incl).
        destruct (branch_taken BC_LTU (getr r4 20) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (cells_ok_read SEGS m m4 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK4) ltac:(dl_in0)) as [bs5_0 Rd5_0].
          destruct (v0_1bd8ct fx r4 m4 bs5_0 B4 Rd5_0 (cells_ok_sok SEGS m m4 v0_1bcc0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_9 & SV5_0 & AG5).
          assert (FK5 : mframe v0_1bcc0_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1bcc0_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r5 8) (Z_to_bv 64 255)) eqn:B5.
          ++ (* [comment removed for export] *)
            destruct (v0_1bdc8t fx r5 m5  B5 (cells_ok_sok SEGS m m5 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_16 & E6_17 & SV6_0 & AG6).
            assert (FK6 : mframe v0_1bcc0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold v0_1bcc0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (v0_1bdc8f fx r5 m5  B5 (cells_ok_sok SEGS m m5 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_8 & E6_16 & E6_17 & SV6_0 & AG6).
            assert (FK6 : mframe v0_1bcc0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold v0_1bcc0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (cells_ok_read SEGS m m4 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK4) ltac:(dl_in0)) as [bs5_0 Rd5_0].
          destruct (v0_1bd8cf fx r4 m4 bs5_0 B4 Rd5_0 (cells_ok_sok SEGS m m4 v0_1bcc0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_9 & E5_20 & SV5_0 & AG5).
          assert (FK5 : mframe v0_1bcc0_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1bcc0_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r5 8) (Z_to_bv 64 255)) eqn:B5.
          ++ (* [comment removed for export] *)
            destruct (v0_1bdc8t fx r5 m5  B5 (cells_ok_sok SEGS m m5 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_16 & E6_17 & SV6_0 & AG6).
            assert (FK6 : mframe v0_1bcc0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold v0_1bcc0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (v0_1bdc8f fx r5 m5  B5 (cells_ok_sok SEGS m m5 v0_1bcc0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_8 & E6_16 & E6_17 & SV6_0 & AG6).
            assert (FK6 : mframe v0_1bcc0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold v0_1bcc0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
Qed.

End V0.

Definition vt0_1be64_cells_def (lined bufs1 bufs2 w1 lc uc wpl : Z) : list (Z * Z) := [((bytea (bufs1 + w1))%Z, 1%Z); ((bytea (bufs2 + w1))%Z, 1%Z); ((lined + (4 * (w1 / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition vt0_hyps (lined bufs1 bufs2 w1 lc uc wpl : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (0 <= w1 <= 19999)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (bufs1 + 4 * wpl <= bufs2 \/ bufs2 + 4 * wpl <= bufs1)%Z /\ (w1 + 1 <= 4 * wpl)%Z.
Section VT0.
Variable rom : word -> option byte.
Variables (lined bufs1 bufs2 w1 lc uc wpl : Z).
Hypothesis HYP : vt0_hyps lined bufs1 bufs2 w1 lc uc wpl.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_w1 & R_lc & R_uc & DJ12 & Hwpl); pose proof (dl_div_bounds w1 32 ltac:(lia) ltac:(lia)) as DW; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1]; destruct (al4_ex _ A_bufs2) as [cb2 Ecb2].
(* [comment removed for export] *)
Lemma vt0_1be64 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + w1))) 1 = Some bs0 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf68) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf94) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 16 = Z_to_bv 64 (rdv true 1 bs0)
    /\ regs_agree (fun r => In r [12; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 H10 H11 H12 H13 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc; rdv true 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc; rdv true 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [false; false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1be90f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LT (getr regs 16) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (w1 / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (w1 / 32)))) 4 = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf94) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bfd8) m' rom)
    /\ mframe [((lined + (4 * (w1 / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 15 = Z_to_bv 64 (lined + (4 * (w1 / 32)))
    /\ regs_agree (fun r => In r [10; 15; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H10 H11 H13 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc; rdv true 4 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [false; false; false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1be90t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 16) (Z_to_bv 64 0) = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf94) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c02c) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H11 H13 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1bed4f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 12) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = Some bs0 ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 (lined + (4 * (w1 / 32))) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bfd8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c018) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 (bytea (bufs2 + w1))
    /\ getr regs' 12 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 H11 H13 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [false; false; false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1bed4t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 12) = true ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 (lined + (4 * (w1 / 32))) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bfd8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H11 H13 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1bf14f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 11) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = true ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w1)) ->
  getr regs 12 = Z_to_bv 64 255 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 (lined + (4 * (w1 / 32))) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c018) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe [((bytea (bufs2 + w1))%Z, 1%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 255
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [11]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H10 H12 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1bf14t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 11) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = true ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w1)) ->
  getr regs 12 = Z_to_bv 64 255 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 (lined + (4 * (w1 / 32))) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c018) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe [((bytea (bufs2 + w1))%Z, 1%Z)] m m'
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = Some (word_to_le_bytes 1 (getr regs 11))
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H10 H12 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1bf28f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 10) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = true ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c02c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe [((bytea (bufs2 + w1))%Z, 1%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 (bytea (bufs2 + w1))
    /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H11 H13 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [false; false; false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1bf28t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 10) = true ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c02c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H11 H13 H14 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation vt0_1be64_cells := (vt0_1be64_cells_def lined bufs1 bufs2 w1 lc uc wpl).
Lemma vt0_1be64_path : forall (fx : FPState) regs m,
  cells_ok SEGS m vt0_1be64_cells ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bf68) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe vt0_1be64_cells m m'
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 15; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m CK H10 H11 H12 H13 H14 H15.
  pose proof (mframe_refl vt0_1be64_cells m) as FK0.
  destruct (cells_ok_read SEGS m m vt0_1be64_cells (bytea (bufs1 + w1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (vt0_1be64 fx regs m bs1_0 Rd1_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_16 & AG1).
  assert (FK1 : mframe vt0_1be64_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold vt0_1be64_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 16) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (vt0_1be90t fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe vt0_1be64_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold vt0_1be64_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 uc) (getr r2 10)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (vt0_1bf28t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe vt0_1be64_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold vt0_1be64_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 vt0_1be64_cells (bytea (bufs2 + w1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (vt0_1bf28f fx r2 m2 bs3_0 B2 Rd3_0 (cells_ok_sok SEGS m m2 vt0_1be64_cells (bytea (bufs2 + w1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_11 & AG3).
      assert (FK3 : mframe vt0_1be64_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold vt0_1be64_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 vt0_1be64_cells (lined + (4 * (w1 / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (vt0_1be90f fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 vt0_1be64_cells (lined + (4 * (w1 / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_15 & AG2).
    assert (FK2 : mframe vt0_1be64_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold vt0_1be64_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 lc) (getr r2 12)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (vt0_1bed4t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe vt0_1be64_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold vt0_1be64_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 vt0_1be64_cells (bytea (bufs2 + w1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (vt0_1bed4f fx r2 m2 bs3_0 B2 Rd3_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_12 & AG3).
      assert (FK3 : mframe vt0_1be64_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold vt0_1be64_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (getr r3 11) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (vt0_1bf14t fx r3 m3  B3 (cells_ok_sok SEGS m m3 vt0_1be64_cells (bytea (bufs2 + w1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & SV4_0 & AG4).
        assert (FK4 : mframe vt0_1be64_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold vt0_1be64_cells_def; dl_incl).
        exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
        repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (vt0_1bf14f fx r3 m3  B3 (cells_ok_sok SEGS m m3 vt0_1be64_cells (bytea (bufs2 + w1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_11 & SV4_0 & AG4).
        assert (FK4 : mframe vt0_1be64_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold vt0_1be64_cells_def; dl_incl).
        exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
        repeat split; [dl_get .. | ra_chain].
Qed.

End VT0.
