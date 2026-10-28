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

(* [comment removed for export] *)
Definition vp_hyps (s lined bufs1 bufs2 w1 lc uc : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (1 <= w1 <= 19999)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z.
Section VP.
Variable rom : word -> option byte.
Variables (s lined bufs1 bufs2 w1 lc uc : Z).
Hypothesis HYP : vp_hyps s lined bufs1 bufs2 w1 lc uc.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_w1 & R_lc & R_uc); idtac.
(* [comment removed for export] *)
Lemma vp_1ba84_f0 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 0 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bb88) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bdc4) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 48)
    /\ getr regs' 5 = Z_to_bv 64 1
    /\ getr regs' 6 = Z_to_bv 64 3
    /\ getr regs' 7 = Z_to_bv 64 2
    /\ getr regs' 11 = Z_to_bv 64 w1
    /\ getr regs' 17 = Z_to_bv 64 0
    /\ getr regs' 28 = Z_to_bv 64 1
    /\ getr regs' 29 = Z_to_bv 64 1
    /\ getr regs' 30 = Z_to_bv 64 134217727
    /\ getr regs' 31 = Z_to_bv 64 18446744071562067968
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 11; 17; 28; 29; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 H2 H10 H11 H12 H13 H14 H15 H16.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [113700%Z; 113896%Z; 114116%Z; 114536%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vp_1ba84_f1 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bb88) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc24) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 48)
    /\ getr regs' 5 = Z_to_bv 64 3
    /\ getr regs' 6 = Z_to_bv 64 2
    /\ getr regs' 7 = Z_to_bv 64 1
    /\ getr regs' 11 = Z_to_bv 64 w1
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 1
    /\ getr regs' 28 = Z_to_bv 64 134217727
    /\ getr regs' 29 = Z_to_bv 64 18446744071562067968
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 11; 13; 16; 17; 28; 29]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 H2 H10 H11 H12 H13 H14 H15 H16.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 19999; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255]) by (ex_know regs).
  dl_run 400%nat [113700%Z; 113896%Z; 114116%Z; 114536%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End VP.

(* [comment removed for export] *)
Definition vq_hyps (s lined bufs1 bufs2 lc uc : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z.
Section VQ.
Variable rom : word -> option byte.
Variables (s lined bufs1 bufs2 lc uc : Z).
Hypothesis HYP : vq_hyps s lined bufs1 bufs2 lc uc.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_lc & R_uc); idtac.
(* [comment removed for export] *)
Lemma vq_1ba84_f0 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 0 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bb88) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bf68) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 48)
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ regs_agree (fun r => In r [2; 11; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 H2 H10 H11 H12 H13 H14 H15 H16.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113700%Z; 113896%Z; 114116%Z; 114536%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vq_1ba84_f1 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bb88) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bce8) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 48)
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ regs_agree (fun r => In r [2; 11; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 H2 H10 H11 H12 H13 H14 H15 H16.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113700%Z; 113896%Z; 114116%Z; 114536%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End VQ.

Definition v1_1bb20_cells_def (lined bufs1 j w1 lc uc wpl : Z) : list (Z * Z) := [((bytea (bufs1 + j))%Z, 1%Z); ((bytea (bufs1 + j + 1))%Z, 1%Z); ((lined + (4 * (j / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition v1_hyps (lined bufs1 j w1 lc uc wpl : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (0 <= j <= 19999)%Z /\ (1 <= w1 <= 19999)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (0 <= j < w1)%Z /\ (w1 + 1 <= 4 * wpl)%Z.
Section V1.
Variable rom : word -> option byte.
Variables (lined bufs1 j w1 lc uc wpl : Z).
Hypothesis HYP : v1_hyps lined bufs1 j w1 lc uc wpl.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_j & R_w1 & R_lc & R_uc & Hj & Hwpl); pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1].
(* [comment removed for export] *)
Lemma v1_1bb1cf : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = false ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 (j + 1) ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 (j + 1) ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc20) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc24) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bb1ct : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 (j + 1) ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 (j + 1) ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc20) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bce8) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bb20 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j))) 1 = Some bs0 ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc24) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 8 = Z_to_bv 64 (rdv true 1 bs0)
    /\ getr regs' 30 = Z_to_bv 64 (bufs1 + j)
    /\ regs_agree (fun r => In r [8; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc; rdv true 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc; rdv true 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bb44f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LT (getr regs 8) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 32)))) 4 = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 30 = Z_to_bv 64 (bufs1 + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc48) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc88) m' rom)
    /\ mframe [((lined + (4 * (j / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 (lined + (4 * (j / 32)))
    /\ regs_agree (fun r => In r [8; 9; 18]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc; rdv true 4 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [false; false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bb44t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 8) (Z_to_bv 64 0) = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 30 = Z_to_bv 64 (bufs1 + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc48) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bccc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bb84f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 31) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs0 ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 (lined + (4 * (j / 32))) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 30 = Z_to_bv 64 (bufs1 + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc88) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bcbc) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 8 = Z_to_bv 64 255
    /\ getr regs' 30 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ regs_agree (fun r => In r [8; 9; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [false; false; false; false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bb84t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 lc) (getr regs 31) = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 (lined + (4 * (j / 32))) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 30 = Z_to_bv 64 (bufs1 + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc88) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc20) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [13; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bbb8f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 31) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 255 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 30 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bcbc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc20) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 31 = Z_to_bv 64 255
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [13; 16; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bbb8t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 31) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 255 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 30 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bcbc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc20) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some (word_to_le_bytes 1 (getr regs 31))
    /\ regs_agree (fun r => In r [13; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bbc8f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 31) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 30 = Z_to_bv 64 (bufs1 + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bccc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc20) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 30 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ regs_agree (fun r => In r [8; 9; 13; 16; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [false; false; false; true] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1bbc8t : forall (fx : FPState) regs m ,
  branch_taken BC_GE (Z_to_bv 64 uc) (getr regs 31) = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  getr regs 30 = Z_to_bv 64 (bufs1 + j) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bccc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc20) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [13; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30.
  dl_facts.
  ex_entry regs [lined; bufs1; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 1 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [113696%Z; 113700%Z; 113896%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation v1_1bb20_cells := (v1_1bb20_cells_def lined bufs1 j w1 lc uc wpl).
Lemma v1_1bb20_path : forall (fx : FPState) regs m,
  cells_ok SEGS m v1_1bb20_cells ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 2 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 lc ->
  getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 1 ->
  getr regs 28 = Z_to_bv 64 134217727 ->
  getr regs 29 = Z_to_bv 64 18446744071562067968 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bc24) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bc20) m' rom)
    /\ mframe v1_1bb20_cells m m'
    /\ getr regs' 13 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [8; 9; 13; 16; 18; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m CK H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29.
  pose proof (mframe_refl v1_1bb20_cells m) as FK0.
  destruct (cells_ok_read SEGS m m v1_1bb20_cells (bytea (bufs1 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (v1_1bb20 fx regs m bs1_0 Rd1_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_8 & E1_30 & AG1).
  assert (FK1 : mframe v1_1bb20_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold v1_1bb20_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 8) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (v1_1bb44t fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe v1_1bb20_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold v1_1bb20_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 uc) (getr r2 31)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (v1_1bbc8t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_13 & E3_16 & AG3).
      assert (FK3 : mframe v1_1bb20_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v1_1bb20_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 v1_1bb20_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (v1_1bbc8f fx r2 m2 bs3_0 B2 Rd3_0 (cells_ok_sok SEGS m m2 v1_1bb20_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_13 & E3_16 & E3_30 & AG3).
      assert (FK3 : mframe v1_1bb20_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v1_1bb20_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 v1_1bb20_cells (lined + (4 * (j / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (v1_1bb44f fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 v1_1bb20_cells (lined + (4 * (j / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_8 & AG2).
    assert (FK2 : mframe v1_1bb20_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold v1_1bb20_cells_def; dl_incl).
    destruct (branch_taken BC_GE (Z_to_bv 64 lc) (getr r2 31)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (v1_1bb84t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_13 & E3_16 & AG3).
      assert (FK3 : mframe v1_1bb20_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v1_1bb20_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 v1_1bb20_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (v1_1bb84f fx r2 m2 bs3_0 B2 Rd3_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_8 & E3_30 & AG3).
      assert (FK3 : mframe v1_1bb20_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v1_1bb20_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (getr r3 31) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (v1_1bbb8t fx r3 m3  B3 (cells_ok_sok SEGS m m3 v1_1bb20_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_13 & E4_16 & SV4_0 & AG4).
        assert (FK4 : mframe v1_1bb20_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold v1_1bb20_cells_def; dl_incl).
        exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
        repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (v1_1bbb8f fx r3 m3  B3 (cells_ok_sok SEGS m m3 v1_1bb20_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_13 & E4_16 & E4_31 & SV4_0 & AG4).
        assert (FK4 : mframe v1_1bb20_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold v1_1bb20_cells_def; dl_incl).
        exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
        repeat split; [dl_get .. | ra_chain].
Qed.

End V1.

Definition vt1_1bbe4_cells_def (lined bufs1 w1 wpl : Z) : list (Z * Z) := [((bytea (bufs1 + w1))%Z, 1%Z); ((lined + (4 * (w1 / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition vt1_hyps (lined bufs1 w1 wpl : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (0 <= w1 <= 19999)%Z /\ (w1 + 1 <= 4 * wpl)%Z.
Section VT1.
Variable rom : word -> option byte.
Variables (lined bufs1 w1 wpl : Z).
Hypothesis HYP : vt1_hyps lined bufs1 w1 wpl.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_w1 & Hwpl); pose proof (dl_div_bounds w1 32 ltac:(lia) ltac:(lia)) as DW; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1].
(* [comment removed for export] *)
Lemma vt1_1bbe4 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + w1))) 1 = Some bs0 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bce8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bd10) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 12 = Z_to_bv 64 (rdv true 1 bs0)
    /\ getr regs' 13 = Z_to_bv 64 (bufs1 + w1)
    /\ regs_agree (fun r => In r [12; 13; 14]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 H10 H11 H12.
  dl_facts.
  ex_entry regs [lined; bufs1; w1; rdv true 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; w1; rdv true 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [false; false] [EVar 35] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt1_1bc0cf : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LT (getr regs 12) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (w1 / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (w1 / 32)))) 4 = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 13 = Z_to_bv 64 (bufs1 + w1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bd10) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe [((lined + (4 * (w1 / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 12 = Z_to_bv 64 (lined + (4 * (w1 / 32)))
    /\ getr regs' 13 = Z_to_bv 64 18446744071562067968
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H10 H11 H13.
  dl_facts.
  ex_entry regs [lined; bufs1; w1; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; w1; rdv true 4 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [false; false; false] [EVar 35] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt1_1bc0ct : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 12) (Z_to_bv 64 0) = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 13 = Z_to_bv 64 (bufs1 + w1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bd10) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H10 H11 H13.
  dl_facts.
  ex_entry regs [lined; bufs1; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999]) by (ex_know regs).
  dl_run 400%nat [114808%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation vt1_1bbe4_cells := (vt1_1bbe4_cells_def lined bufs1 w1 wpl).
Lemma vt1_1bbe4_path : forall (fx : FPState) regs m,
  cells_ok SEGS m vt1_1bbe4_cells ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bce8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c078) m' rom)
    /\ mframe vt1_1bbe4_cells m m'
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]%list) regs regs'.
Proof using All.
  intros fx regs m CK H10 H11 H12.
  pose proof (mframe_refl vt1_1bbe4_cells m) as FK0.
  destruct (cells_ok_read SEGS m m vt1_1bbe4_cells (bytea (bufs1 + w1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (vt1_1bbe4 fx regs m bs1_0 Rd1_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_12 & E1_13 & AG1).
  assert (FK1 : mframe vt1_1bbe4_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold vt1_1bbe4_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 12) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (vt1_1bc0ct fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe vt1_1bbe4_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold vt1_1bbe4_cells_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 vt1_1bbe4_cells (lined + (4 * (w1 / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (vt1_1bc0cf fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 vt1_1bbe4_cells (lined + (4 * (w1 / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_12 & E2_13 & AG2).
    assert (FK2 : mframe vt1_1bbe4_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold vt1_1bbe4_cells_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
    repeat split; [dl_get .. | ra_chain].
Qed.

End VT1.

(* [comment removed for export] *)
Definition ve_hyps (s : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z.
Section VE.
Variable rom : word -> option byte.
Variables (s : Z).
Hypothesis HYP : ve_hyps s.
Ltac dl_facts := pose proof HYP as (R_s & A_s); idtac.
(* [comment removed for export] *)
Lemma ve_1bf74 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte) (bs5 : list byte),
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some bs4 ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some bs5 ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c078) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c094) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 8 = Z_to_bv 64 (rdv false 8 bs0)
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 8 bs1)
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 8 bs2)
    /\ getr regs' 19 = Z_to_bv 64 (rdv false 8 bs3)
    /\ getr regs' 20 = Z_to_bv 64 (rdv false 8 bs4)
    /\ getr regs' 21 = Z_to_bv 64 (rdv false 8 bs5)
    /\ regs_agree (fun r => In r [2; 8; 9; 18; 19; 20; 21]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 bs5 R0 R1 R2 R3 R4 R5 H2.
  dl_facts.
  ex_entry regs [s; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16]) by (ex_know regs).
  dl_run 400%nat (@nil Z) (SCR [] [EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End VE.
