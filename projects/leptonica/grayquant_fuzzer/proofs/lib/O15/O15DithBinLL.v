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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac.
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

Definition bl_1a6d0_cells_def (lined bufs1 bufs2 j w1 lc uc wpl : Z) : list (Z * Z) := [((bytea (bufs1 + j))%Z, 1%Z); ((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z); ((lined + (4 * (j / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition bl_hyps (lined bufs1 bufs2 j w1 lc uc wpl : Z) : Prop :=
  (4096 <= lined < 2 ^ 47)%Z /\ (4096 <= bufs1 < 2 ^ 47)%Z /\ (4096 <= bufs2 < 2 ^ 47)%Z /\ (0 <= w1 <= 19999)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (lined mod 4 = 0)%Z /\ (bufs1 mod 4 = 0)%Z /\ (bufs2 mod 4 = 0)%Z /\ (w1 + 1 <= 4 * wpl)%Z /\ (bufs1 + 4 * wpl <= bufs2 \/ bufs2 + 4 * wpl <= bufs1)%Z /\ (0 <= j < w1)%Z.
Section BL.
Variable rom : word -> option byte.
Variables (lined bufs1 bufs2 j w1 lc uc wpl : Z).
Hypothesis HYP : bl_hyps lined bufs1 bufs2 j w1 lc uc wpl.
Ltac dl_facts := pose proof HYP as (Hl & Hb1 & Hb2 & Hw1 & Hlc & Huc & ALl & ALb1 & ALb2 & Hwpl & DJ12 & Hj); pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; destruct (al4_ex _ ALb1) as [cb1 Ecb1]; destruct (al4_ex _ ALb2) as [cb2 Ecb2].
(* [comment removed for export] *)
Lemma bl_1a6ccf : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = false ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (j + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 (j + 1) ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a7c8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7cc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a6cct : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (j + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 (j + 1) ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a7c8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a928) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a6d0 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j))) 1 = Some bs0 ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a7cc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7dc) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 31 = Z_to_bv 64 (rdv false 1 bs0)
    /\ regs_agree (fun r => In r [30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a6e0f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LT (getr regs 30) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a7dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a800) m' rom)
    /\ mframe [((lined + (4 * (j / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 (lined + (4 * (j / 32)))
    /\ regs_agree (fun r => In r [8; 9; 18]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv true 4 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a6e0t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 30) (Z_to_bv 64 0) = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a7dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a878) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [30]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a704f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 31) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs0 ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 8 = Z_to_bv 64 (lined + (4 * (j / 32))) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a800) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a824) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 31 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [8; 9; 18; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a704t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 31) = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 8 = Z_to_bv 64 (lined + (4 * (j / 32))) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a800) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7c8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [11; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a728f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LTU (getr regs 18) (Z_to_bv 64 255) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 31 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a824) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a840) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 1 bs0)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [8; 9; 18]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H28 H29 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a728t : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LTU (getr regs 18) (Z_to_bv 64 255) = true ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 31 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a824) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a840) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 1 bs0)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some (word_to_le_bytes 1 (getr regs 18))
    /\ regs_agree (fun r => In r [8; 9; 18]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H28 H29 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [true] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a744f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LTU (getr regs 8) (Z_to_bv 64 255) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 31 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a840) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a868) m' rom)
    /\ mframe [((bytea (bufs2 + j))%Z, 1%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 1 bs0)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [8; 9; 30]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H28 H29 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [false] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a744t : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LTU (getr regs 8) (Z_to_bv 64 255) = true ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 31 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a840) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a868) m' rom)
    /\ mframe [((bytea (bufs2 + j))%Z, 1%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 1 bs0)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some (word_to_le_bytes 1 (getr regs 8))
    /\ regs_agree (fun r => In r [8; 9; 30]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H28 H29 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [true] [EVar 39] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a76cf : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 30) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 8 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 31 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a868) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7c8) m' rom)
    /\ mframe [((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 30 = Z_to_bv 64 255
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [11; 16; 30]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H29 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a76ct : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 30) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 8 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 31 = Z_to_bv 64 255 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a868) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7c8) m' rom)
    /\ mframe [((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some (word_to_le_bytes 1 (getr regs 30))
    /\ regs_agree (fun r => In r [11; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H29 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a77cf : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte),
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 30) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some bs2 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a878) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7c8) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 18 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ regs_agree (fun r => In r [8; 9; 11; 16; 18; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 BT R0 R1 R2 S0 S1 S2 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0; rdv false 1 bs1; rdv false 1 bs2] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc; rdv false 1 bs0; rdv false 1 bs1; rdv false 1 bs2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [false] [EVar 39; EVar 40; EVar 41] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bl_1a77ct : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 30) = true ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a878) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7c8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [11; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108488%Z; 108492%Z; 108840%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation bl_1a6d0_cells := (bl_1a6d0_cells_def lined bufs1 bufs2 j w1 lc uc wpl).
Lemma bl_1a6d0_path : forall (fx : FPState) regs m,
  cells_ok SEGS m bl_1a6d0_cells ->
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) ->
  getr regs 6 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 7 = Z_to_bv 64 134217727 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 28 = Z_to_bv 64 w1 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a7cc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7c8) m' rom)
    /\ mframe bl_1a6d0_cells m m'
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [8; 9; 11; 16; 18; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m CK H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29.
  pose proof (mframe_refl bl_1a6d0_cells m) as FK0.
  destruct (cells_ok_read SEGS m m bl_1a6d0_cells (bytea (bufs1 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (bl_1a6d0 fx regs m bs1_0 Rd1_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_31 & AG1).
  assert (FK1 : mframe bl_1a6d0_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold bl_1a6d0_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 30) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (bl_1a6e0t fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe bl_1a6d0_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bl_1a6d0_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 uc) (getr r2 30)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (bl_1a77ct fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_11 & E3_16 & AG3).
      assert (FK3 : mframe bl_1a6d0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold bl_1a6d0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 bl_1a6d0_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (cells_ok_read SEGS m m2 bl_1a6d0_cells (bytea (bufs2 + j))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_1 Rd3_1].
      destruct (cells_ok_read SEGS m m2 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_2 Rd3_2].
      destruct (bl_1a77cf fx r2 m2 bs3_0 bs3_1 bs3_2 B2 Rd3_0 Rd3_1 Rd3_2 (cells_ok_sok SEGS m m2 bl_1a6d0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) (cells_ok_sok SEGS m m2 bl_1a6d0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) (cells_ok_sok SEGS m m2 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_8 & E3_11 & E3_16 & E3_18 & AG3).
      assert (FK3 : mframe bl_1a6d0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold bl_1a6d0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 bl_1a6d0_cells (lined + (4 * (j / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (bl_1a6e0f fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 bl_1a6d0_cells (lined + (4 * (j / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_8 & AG2).
    assert (FK2 : mframe bl_1a6d0_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bl_1a6d0_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 lc) (getr r2 31)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (bl_1a704t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_11 & E3_16 & AG3).
      assert (FK3 : mframe bl_1a6d0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold bl_1a6d0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 bl_1a6d0_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (bl_1a704f fx r2 m2 bs3_0 B2 Rd3_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_9 & E3_31 & AG3).
      assert (FK3 : mframe bl_1a6d0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold bl_1a6d0_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (getr r3 18) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (cells_ok_read SEGS m m3 bl_1a6d0_cells (bytea (bufs2 + j))%Z 1%Z wr_readable_img CK (proj1 FK3) ltac:(dl_in0)) as [bs4_0 Rd4_0].
        destruct (bl_1a728t fx r3 m3 bs4_0 B3 Rd4_0 (cells_ok_sok SEGS m m3 bl_1a6d0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_9 & E4_18 & SV4_0 & AG4).
        assert (FK4 : mframe bl_1a6d0_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold bl_1a6d0_cells_def; dl_incl).
        destruct (branch_taken BC_LTU (getr r4 8) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (cells_ok_read SEGS m m4 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK4) ltac:(dl_in0)) as [bs5_0 Rd5_0].
          destruct (bl_1a744t fx r4 m4 bs5_0 B4 Rd5_0 (cells_ok_sok SEGS m m4 bl_1a6d0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_8 & E5_9 & SV5_0 & AG5).
          assert (FK5 : mframe bl_1a6d0_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold bl_1a6d0_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r5 30) (Z_to_bv 64 255)) eqn:B5.
          ++ (* [comment removed for export] *)
            destruct (bl_1a76ct fx r5 m5  B5 (cells_ok_sok SEGS m m5 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_11 & E6_16 & SV6_0 & AG6).
            assert (FK6 : mframe bl_1a6d0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold bl_1a6d0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (bl_1a76cf fx r5 m5  B5 (cells_ok_sok SEGS m m5 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_11 & E6_16 & E6_30 & SV6_0 & AG6).
            assert (FK6 : mframe bl_1a6d0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold bl_1a6d0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (cells_ok_read SEGS m m4 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK4) ltac:(dl_in0)) as [bs5_0 Rd5_0].
          destruct (bl_1a744f fx r4 m4 bs5_0 B4 Rd5_0 (cells_ok_sok SEGS m m4 bl_1a6d0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_8 & E5_9 & SV5_0 & AG5).
          assert (FK5 : mframe bl_1a6d0_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold bl_1a6d0_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r5 30) (Z_to_bv 64 255)) eqn:B5.
          ++ (* [comment removed for export] *)
            destruct (bl_1a76ct fx r5 m5  B5 (cells_ok_sok SEGS m m5 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_11 & E6_16 & SV6_0 & AG6).
            assert (FK6 : mframe bl_1a6d0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold bl_1a6d0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (bl_1a76cf fx r5 m5  B5 (cells_ok_sok SEGS m m5 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_11 & E6_16 & E6_30 & SV6_0 & AG6).
            assert (FK6 : mframe bl_1a6d0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold bl_1a6d0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (cells_ok_read SEGS m m3 bl_1a6d0_cells (bytea (bufs2 + j))%Z 1%Z wr_readable_img CK (proj1 FK3) ltac:(dl_in0)) as [bs4_0 Rd4_0].
        destruct (bl_1a728f fx r3 m3 bs4_0 B3 Rd4_0 (cells_ok_sok SEGS m m3 bl_1a6d0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_9 & E4_18 & SV4_0 & AG4).
        assert (FK4 : mframe bl_1a6d0_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold bl_1a6d0_cells_def; dl_incl).
        destruct (branch_taken BC_LTU (getr r4 8) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (cells_ok_read SEGS m m4 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK4) ltac:(dl_in0)) as [bs5_0 Rd5_0].
          destruct (bl_1a744t fx r4 m4 bs5_0 B4 Rd5_0 (cells_ok_sok SEGS m m4 bl_1a6d0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_8 & E5_9 & SV5_0 & AG5).
          assert (FK5 : mframe bl_1a6d0_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold bl_1a6d0_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r5 30) (Z_to_bv 64 255)) eqn:B5.
          ++ (* [comment removed for export] *)
            destruct (bl_1a76ct fx r5 m5  B5 (cells_ok_sok SEGS m m5 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_11 & E6_16 & SV6_0 & AG6).
            assert (FK6 : mframe bl_1a6d0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold bl_1a6d0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (bl_1a76cf fx r5 m5  B5 (cells_ok_sok SEGS m m5 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_11 & E6_16 & E6_30 & SV6_0 & AG6).
            assert (FK6 : mframe bl_1a6d0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold bl_1a6d0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (cells_ok_read SEGS m m4 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK4) ltac:(dl_in0)) as [bs5_0 Rd5_0].
          destruct (bl_1a744f fx r4 m4 bs5_0 B4 Rd5_0 (cells_ok_sok SEGS m m4 bl_1a6d0_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_8 & E5_9 & SV5_0 & AG5).
          assert (FK5 : mframe bl_1a6d0_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold bl_1a6d0_cells_def; dl_incl).
          destruct (branch_taken BC_LTU (getr r5 30) (Z_to_bv 64 255)) eqn:B5.
          ++ (* [comment removed for export] *)
            destruct (bl_1a76ct fx r5 m5  B5 (cells_ok_sok SEGS m m5 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_11 & E6_16 & SV6_0 & AG6).
            assert (FK6 : mframe bl_1a6d0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold bl_1a6d0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
          ++ (* [comment removed for export] *)
            destruct (bl_1a76cf fx r5 m5  B5 (cells_ok_sok SEGS m m5 bl_1a6d0_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK5) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r6 & m6 & RUN6 & FR6 & E6_11 & E6_16 & E6_30 & SV6_0 & AG6).
            assert (FK6 : mframe bl_1a6d0_cells m m6) by (apply (mframe_step _ _ _ _ _ FK5 FR6); unfold bl_1a6d0_cells_def; dl_incl).
            exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6)))))|]. split; [exact FK6|].
            repeat split; [dl_get .. | ra_chain].
Qed.

End BL.

Definition bc_1a82c_cells_def (lined bufs1 bufs2 w1 lc uc wpl : Z) : list (Z * Z) := [((bytea (bufs1 + w1))%Z, 1%Z); ((bytea (bufs2 + w1))%Z, 1%Z); ((lined + (4 * (w1 / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition bc_hyps (lined bufs1 bufs2 w1 lc uc wpl : Z) : Prop :=
  (4096 <= lined < 2 ^ 47)%Z /\ (4096 <= bufs1 < 2 ^ 47)%Z /\ (4096 <= bufs2 < 2 ^ 47)%Z /\ (0 <= w1 <= 19999)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (lined mod 4 = 0)%Z /\ (bufs1 mod 4 = 0)%Z /\ (bufs2 mod 4 = 0)%Z /\ (w1 + 1 <= 4 * wpl)%Z /\ (bufs1 + 4 * wpl <= bufs2 \/ bufs2 + 4 * wpl <= bufs1)%Z.
Section BC.
Variable rom : word -> option byte.
Variables (lined bufs1 bufs2 w1 lc uc wpl : Z).
Hypothesis HYP : bc_hyps lined bufs1 bufs2 w1 lc uc wpl.
Ltac dl_facts := pose proof HYP as (Hl & Hb1 & Hb2 & Hw1 & Hlc & Huc & ALl & ALb1 & ALb2 & Hwpl & DJ12); pose proof (dl_div_bounds w1 32 ltac:(lia) ltac:(lia)) as DW; destruct (al4_ex _ ALb1) as [cb1 Ecb1]; destruct (al4_ex _ ALb2) as [cb2 Ecb2].
(* [comment removed for export] *)
Lemma bc_1a82c : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + w1))) 1 = Some bs0 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a928) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a938) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 12 = Z_to_bv 64 (rdv true 1 bs0)
    /\ regs_agree (fun r => In r [11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 H10 H12 H13 H14 H15 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc; rdv true 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc; rdv true 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bc_1a83cf : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LT (getr regs 12) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (w1 / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (w1 / 32)))) 4 = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a938) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a95c) m' rom)
    /\ mframe [((lined + (4 * (w1 / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (lined + (4 * (w1 / 32)))
    /\ regs_agree (fun r => In r [10; 12; 15]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H10 H13 H14 H15 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc; rdv true 4 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bc_1a83ct : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 12) (Z_to_bv 64 0) = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a938) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a994) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H13 H14 H15 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bc_1a860f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 11) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = Some bs0 ->
  getr regs 10 = Z_to_bv 64 (lined + (4 * (w1 / 32))) ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a95c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a980) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 (bytea (bufs2 + w1))
    /\ getr regs' 12 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 H10 H13 H14 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bc_1a860t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 11) = true ->
  getr regs 10 = Z_to_bv 64 (lined + (4 * (w1 / 32))) ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a95c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a9c4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H13 H14 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bc_1a884f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 11) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = true ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w1)) ->
  getr regs 12 = Z_to_bv 64 255 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a980) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a9c4) m' rom)
    /\ mframe [((bytea (bufs2 + w1))%Z, 1%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 255
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [11]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H10 H12 H14 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bc_1a884t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 11) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = true ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w1)) ->
  getr regs 12 = Z_to_bv 64 255 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a980) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a9c4) m' rom)
    /\ mframe [((bytea (bufs2 + w1))%Z, 1%Z)] m m'
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = Some (word_to_le_bytes 1 (getr regs 11))
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H10 H12 H14 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bc_1a898f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 10) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w1))) 1 = true ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a994) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a9c4) m' rom)
    /\ mframe [((bytea (bufs2 + w1))%Z, 1%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 (bytea (bufs2 + w1))
    /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H13 H14 H15 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bc_1a898t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 10) = true ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a994) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a9c4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H13 H14 H15 H17.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [108996%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation bc_1a82c_cells := (bc_1a82c_cells_def lined bufs1 bufs2 w1 lc uc wpl).
Lemma bc_1a82c_path : forall (fx : FPState) regs m,
  cells_ok SEGS m bc_1a82c_cells ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a928) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a9c4) m' rom)
    /\ mframe bc_1a82c_cells m m'
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 15]%list) regs regs'.
Proof using All.
  intros fx regs m CK H10 H12 H13 H14 H15 H17.
  pose proof (mframe_refl bc_1a82c_cells m) as FK0.
  destruct (cells_ok_read SEGS m m bc_1a82c_cells (bytea (bufs1 + w1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (bc_1a82c fx regs m bs1_0 Rd1_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_12 & AG1).
  assert (FK1 : mframe bc_1a82c_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold bc_1a82c_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 12) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (bc_1a83ct fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe bc_1a82c_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bc_1a82c_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 uc) (getr r2 10)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (bc_1a898t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe bc_1a82c_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold bc_1a82c_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 bc_1a82c_cells (bytea (bufs2 + w1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (bc_1a898f fx r2 m2 bs3_0 B2 Rd3_0 (cells_ok_sok SEGS m m2 bc_1a82c_cells (bytea (bufs2 + w1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_11 & AG3).
      assert (FK3 : mframe bc_1a82c_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold bc_1a82c_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 bc_1a82c_cells (lined + (4 * (w1 / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (bc_1a83cf fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 bc_1a82c_cells (lined + (4 * (w1 / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_10 & AG2).
    assert (FK2 : mframe bc_1a82c_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold bc_1a82c_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 lc) (getr r2 11)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (bc_1a860t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe bc_1a82c_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold bc_1a82c_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 bc_1a82c_cells (bytea (bufs2 + w1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (bc_1a860f fx r2 m2 bs3_0 B2 Rd3_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_12 & AG3).
      assert (FK3 : mframe bc_1a82c_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold bc_1a82c_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (getr r3 11) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (bc_1a884t fx r3 m3  B3 (cells_ok_sok SEGS m m3 bc_1a82c_cells (bytea (bufs2 + w1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & SV4_0 & AG4).
        assert (FK4 : mframe bc_1a82c_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold bc_1a82c_cells_def; dl_incl).
        exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
        repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (bc_1a884f fx r3 m3  B3 (cells_ok_sok SEGS m m3 bc_1a82c_cells (bytea (bufs2 + w1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_11 & SV4_0 & AG4).
        assert (FK4 : mframe bc_1a82c_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold bc_1a82c_cells_def; dl_incl).
        exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
        repeat split; [dl_get .. | ra_chain].
Qed.

End BC.

(* [comment removed for export] *)
Definition bp_hyps (s lined bufs1 bufs2 w1 lc uc : Z) : Prop :=
  (4096 <= s < 2 ^ 47)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= lined < 2 ^ 47)%Z /\ (4096 <= bufs1 < 2 ^ 47)%Z /\ (4096 <= bufs2 < 2 ^ 47)%Z /\ (0 <= w1 <= 19999)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (lined mod 4 = 0)%Z /\ (bufs1 mod 4 = 0)%Z /\ (bufs2 mod 4 = 0)%Z.
Section BP.
Variable rom : word -> option byte.
Variables (s lined bufs1 bufs2 w1 lc uc : Z).
Hypothesis HYP : bp_hyps s lined bufs1 bufs2 w1 lc uc.
Ltac dl_facts := pose proof HYP as (Hs & ALs & Hl & Hb1 & Hb2 & Hw1 & Hlc & Huc & ALl & ALb1 & ALb2); idtac.
(* [comment removed for export] *)
Lemma bp_1a5a4 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 0 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a6a0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a790) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 32)
    /\ getr regs' 16 = Z_to_bv 64 2
    /\ getr regs' 17 = Z_to_bv 64 w1
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ regs_agree (fun r => In r [2; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 H2 H10 H11 H12 H13 H14 H15 H16.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108492%Z; 108840%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp_1a694f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 (w1 + 1)) (Z_to_bv 64 2) = false ->
  getr regs 2 = Z_to_bv 64 (s - 32) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 2 ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a790) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a7cc) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 5 = Z_to_bv 64 (bufs2 + 1)
    /\ getr regs' 6 = Z_to_bv 64 (bufs1 + 1)
    /\ getr regs' 7 = Z_to_bv 64 134217727
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 28 = Z_to_bv 64 w1
    /\ getr regs' 29 = Z_to_bv 64 18446744071562067968
    /\ regs_agree (fun r => In r [5; 6; 7; 11; 16; 28; 29]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H2 H10 H11 H12 H13 H14 H15 H16 H17.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108492%Z; 108840%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma bp_1a694t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 (w1 + 1)) (Z_to_bv 64 2) = true ->
  getr regs 2 = Z_to_bv 64 (s - 32) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 2 ->
  getr regs 17 = Z_to_bv 64 w1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a790) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a928) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 17 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [17]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H2 H10 H11 H12 H13 H14 H15 H16 H17.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [108492%Z; 108840%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End BP.

(* [comment removed for export] *)
Definition be_hyps (s : Z) : Prop :=
  (4096 <= s < 2 ^ 47)%Z /\ (s mod 16 = 0)%Z.
Section BE.
Variable rom : word -> option byte.
Variables (s : Z).
Hypothesis HYP : be_hyps s.
Ltac dl_facts := pose proof HYP as (Hs & ALs); idtac.
(* [comment removed for export] *)
Lemma be_1a8c8 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte),
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some bs2 ->
  getr regs 2 = Z_to_bv 64 (s - 32) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a9c4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a9d4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 8 = Z_to_bv 64 (rdv false 8 bs0)
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 8 bs1)
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 8 bs2)
    /\ regs_agree (fun r => In r [2; 8; 9; 18]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 R0 R1 R2 H2.
  dl_facts.
  ex_entry regs [s; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16]) by (ex_know regs).
  dl_run 400%nat (@nil Z) (SCR [] [EVar 33; EVar 34; EVar 35] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End BE.
