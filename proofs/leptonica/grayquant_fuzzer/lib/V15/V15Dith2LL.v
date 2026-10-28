(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab.
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
Definition vp_hyps (s lined bufs1 bufs2 tabval tab38 tab14 w1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z /\ (1 <= w1 <= 19999)%Z.
Section VP.
Variable rom : word -> option byte.
Variables (s lined bufs1 bufs2 tabval tab38 tab14 w1 : Z).
Hypothesis HYP : vp_hyps s lined bufs1 bufs2 tabval tab38 tab14 w1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14 & R_w1); idtac.
(* [comment removed for export] *)
Lemma vp_1eb00_f0 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 80)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 17 = Z_to_bv 64 0 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ec04) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eee0) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z); ((s - 56)%Z, 8%Z); ((s - 64)%Z, 8%Z); ((s - 72)%Z, 8%Z); ((s - 80)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 80)
    /\ getr regs' 5 = Z_to_bv 64 0
    /\ getr regs' 6 = Z_to_bv 64 3
    /\ getr regs' 7 = Z_to_bv 64 1
    /\ getr regs' 8 = Z_to_bv 64 1
    /\ getr regs' 11 = Z_to_bv 64 w1
    /\ getr regs' 28 = Z_to_bv 64 1
    /\ getr regs' 29 = Z_to_bv 64 18446744072635809792
    /\ getr regs' 30 = Z_to_bv 64 30
    /\ getr regs' 31 = Z_to_bv 64 268435455
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 22))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 23))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 24))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 25))
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 8; 11; 28; 29; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 H2 H10 H11 H12 H13 H14 H15 H16 H17.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; tabval; tab38; tab14; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; tabval; tab38; tab14; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126140%Z; 126368%Z; 126688%Z; 127048%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vp_1eb00_f1 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 80)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 17 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ec04) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ecbc) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z); ((s - 56)%Z, 8%Z); ((s - 64)%Z, 8%Z); ((s - 72)%Z, 8%Z); ((s - 80)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 80)
    /\ getr regs' 5 = Z_to_bv 64 3
    /\ getr regs' 6 = Z_to_bv 64 1
    /\ getr regs' 7 = Z_to_bv 64 1
    /\ getr regs' 8 = Z_to_bv 64 1
    /\ getr regs' 9 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 w1
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 (bufs1 + 1)
    /\ getr regs' 18 = Z_to_bv 64 w1
    /\ getr regs' 28 = Z_to_bv 64 18446744072635809792
    /\ getr regs' 29 = Z_to_bv 64 30
    /\ getr regs' 30 = Z_to_bv 64 2
    /\ getr regs' 31 = Z_to_bv 64 268435455
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 22))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 23))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 24))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 25))
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 8; 9; 11; 13; 16; 17; 18; 28; 29; 30; 31]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 H2 H10 H11 H12 H13 H14 H15 H16 H17.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; tabval; tab38; tab14; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; tabval; tab38; tab14; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126140%Z; 126368%Z; 126688%Z; 127048%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End VP.

(* [comment removed for export] *)
Definition vq_hyps (s lined bufs1 bufs2 tabval tab38 tab14 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z.
Section VQ.
Variable rom : word -> option byte.
Variables (s lined bufs1 bufs2 tabval tab38 tab14 : Z).
Hypothesis HYP : vq_hyps s lined bufs1 bufs2 tabval tab38 tab14.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14); idtac.
(* [comment removed for export] *)
Lemma vq_1eb00_f0 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 80)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 17 = Z_to_bv 64 0 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ec04) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f048) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z); ((s - 56)%Z, 8%Z); ((s - 64)%Z, 8%Z); ((s - 72)%Z, 8%Z); ((s - 80)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 80)
    /\ getr regs' 5 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 22))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 23))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 24))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 25))
    /\ regs_agree (fun r => In r [2; 5; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 H2 H10 H11 H12 H13 H14 H15 H16 H17.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; tabval; tab38; tab14] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; tabval; tab38; tab14]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4]) by (ex_know regs).
  dl_run 400%nat [126140%Z; 126368%Z; 126688%Z; 127048%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vq_1eb00_f1 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 80)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 17 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ec04) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eda0) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z); ((s - 56)%Z, 8%Z); ((s - 64)%Z, 8%Z); ((s - 72)%Z, 8%Z); ((s - 80)%Z, 8%Z)] m m'
    /\ getr regs' 2 = Z_to_bv 64 (s - 80)
    /\ getr regs' 5 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 22))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 23))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 24))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 25))
    /\ regs_agree (fun r => In r [2; 5; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 H2 H10 H11 H12 H13 H14 H15 H16 H17.
  dl_facts.
  ex_entry regs [s; lined; bufs1; bufs2; tabval; tab38; tab14] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; bufs1; bufs2; tabval; tab38; tab14]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4]) by (ex_know regs).
  dl_run 400%nat [126140%Z; 126368%Z; 126688%Z; 127048%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End VQ.

Definition v1_1ebb8_cells_def (lined bufs1 tabval tab38 j w1 c wpl wpld : Z) : list (Z * Z) := [((bytea (bufs1 + j))%Z, 1%Z); ((lined + (4 * (j / 16)))%Z, 4%Z); ((bytea (bufs1 + j + 1))%Z, 1%Z)].
(* [comment removed for export] *)
Definition v1_hyps (lined bufs1 tabval tab38 j w1 c wpl wpld : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (0 <= j <= 19999)%Z /\ (1 <= w1 <= 19999)%Z /\ (1 <= c <= 19999)%Z /\ (0 <= j < w1)%Z /\ (w1 + 1 <= 4 * wpl)%Z /\ (w1 + 1 <= 16 * wpld)%Z /\ dapart lined (4 * wpld) bufs1 (4 * wpl) /\ dapart lined (4 * wpld) tab38 1024.
Section V1.
Variable rom : word -> option byte.
Variables (lined bufs1 tabval tab38 j w1 c wpl wpld : Z).
Hypothesis HYP : v1_hyps lined bufs1 tabval tab38 j w1 c wpl wpld.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_j & R_w1 & R_c & Hj & Hwpl & Hwpld & AP_l1 & AP_l38); pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1].
(* [comment removed for export] *)
Lemma v1_1ebb4f : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (c - 1)) (Z_to_bv 64 0) = false ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 1 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 (j + 1) ->
  getr regs 17 = Z_to_bv 64 (bufs1 + j + 2) ->
  getr regs 18 = Z_to_bv 64 (c - 1) ->
  getr regs 30 = Z_to_bv 64 2 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ecb8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ecbc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 1 19999; KRange (EVar 39) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [126136%Z; 126140%Z; 126368%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1ebb4t : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 (c - 1)) (Z_to_bv 64 0) = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 1 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 (j + 1) ->
  getr regs 17 = Z_to_bv 64 (bufs1 + j + 2) ->
  getr regs 18 = Z_to_bv 64 (c - 1) ->
  getr regs 30 = Z_to_bv 64 2 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ecb8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eda0) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 1 19999; KRange (EVar 39) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [126136%Z; 126140%Z; 126368%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1ebb8 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 16)))) 4 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (tabval + (4 * (rdv false 1 bs0)))) 4 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (tab38 + (4 * (rdv false 1 bs0)))) 4 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs4 ->
  tv_ok (rdv true 4 bs3) ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 16)))) 4 = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 1 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 18 = Z_to_bv 64 c ->
  getr regs 30 = Z_to_bv 64 2 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ecbc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ed7c) m' rom)
    /\ mframe [((lined + (4 * (j / 16)))%Z, 4%Z)] m m'
    /\ getr regs' 19 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 20 = Z_to_bv 64 (rdv true 4 bs3)
    /\ getr regs' 21 = Z_to_bv 64 (rdv false 1 bs4)
    /\ regs_agree (fun r => In r [19; 20; 21; 22; 23; 24]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 R0 R1 R2 R3 R4 TV3 S0 H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H30 H31.
  dl_facts.
  pose proof (tv_range _ TV3) as RGT3.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  pose proof (rdv_u8 SEGS _ _ _ R4) as U4.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv true 4 bs3; rdv false 1 bs4] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv true 4 bs3; rdv false 1 bs4]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 1 19999; KRange (EVar 39) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [126136%Z; 126140%Z; 126368%Z] (SCR [false; false; false; false; false] [EVar 40; EVar 41; EVar 42; EVar 43; EVar 44] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1ec78f : forall (fx : FPState) regs m  (d20 d21 : Z),
  branch_taken BC_LT (Z_to_bv 64 d20) (Z_to_bv 64 0) = false ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 1 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 18 = Z_to_bv 64 c ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 20 = Z_to_bv 64 d20 ->
  getr regs 21 = Z_to_bv 64 d21 ->
  getr regs 30 = Z_to_bv 64 2 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  tv_ok d20 ->
  (0 <= d21 <= 255)%Z ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ed7c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ed94) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 21 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [20; 21; 22]%list) regs regs'.
Proof using All.
  intros fx regs m d20 d21 BT H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H19 H20 H21 H30 H31 DC20 DC21.
  dl_facts.
  pose proof (tv_range _ DC20) as RG20.
  pose proof (tv_nn30 _ DC20 BT) as NN20.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d20; d21] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d20; d21]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 1 19999; KRange (EVar 39) 4096 140737488375327; KRange (EVar 57) 0 255]) by (ex_know regs).
  dl_run 400%nat [126136%Z; 126140%Z; 126368%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1ec78t : forall (fx : FPState) regs m  (d20 d21 : Z),
  branch_taken BC_LT (Z_to_bv 64 d20) (Z_to_bv 64 0) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 1 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 18 = Z_to_bv 64 c ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 20 = Z_to_bv 64 d20 ->
  getr regs 21 = Z_to_bv 64 d21 ->
  getr regs 30 = Z_to_bv 64 2 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  tv_ok d20 ->
  (0 <= d21 <= 255)%Z ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ed7c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ecb8) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bufs1 + j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (bufs1 + j + 2)
    /\ getr regs' 18 = Z_to_bv 64 (c - 1)
    /\ regs_agree (fun r => In r [9; 13; 16; 17; 18; 20; 21]%list) regs regs'.
Proof using All.
  intros fx regs m d20 d21 BT S0 H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H19 H20 H21 H30 H31 DC20 DC21.
  dl_facts.
  pose proof (tv_range _ DC20) as RG20.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d20; d21] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d20; d21]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 1 19999; KRange (EVar 39) 4096 140737488375327; KRange (EVar 57) 0 255]) by (ex_know regs).
  dl_run 400%nat [126136%Z; 126140%Z; 126368%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1ec90f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 20) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 1 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 18 = Z_to_bv 64 c ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 21 = Z_to_bv 64 255 ->
  getr regs 30 = Z_to_bv 64 2 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ed94) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ecb8) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bufs1 + j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (bufs1 + j + 2)
    /\ getr regs' 18 = Z_to_bv 64 (c - 1)
    /\ getr regs' 20 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [9; 13; 16; 17; 18; 20]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H19 H21 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 1 19999; KRange (EVar 39) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [126136%Z; 126140%Z; 126368%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v1_1ec90t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 20) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 1 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 18 = Z_to_bv 64 c ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 21 = Z_to_bv 64 255 ->
  getr regs 30 = Z_to_bv 64 2 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ed94) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ecb8) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bufs1 + j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (bufs1 + j + 2)
    /\ getr regs' 18 = Z_to_bv 64 (c - 1)
    /\ regs_agree (fun r => In r [9; 13; 16; 17; 18]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H19 H21 H30 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; tab38; j; w1; c; (bufs1 + j)%Z]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 0 19999; KRange (EVar 37) 1 19999; KRange (EVar 38) 1 19999; KRange (EVar 39) 4096 140737488375327]) by (ex_know regs).
  dl_run 400%nat [126136%Z; 126140%Z; 126368%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation v1_1ebb8_cells := (v1_1ebb8_cells_def lined bufs1 tabval tab38 j w1 c wpl wpld).
Lemma v1_1ebb8_path : forall (fx : FPState) regs m,
  cells_ok SEGS m v1_1ebb8_cells ->
  tab_rd SEGS false (fun _ => True) v1_1ebb8_cells m tabval ->
  tab_rd SEGS true tv_ok v1_1ebb8_cells m tab38 ->
  getr regs 5 = Z_to_bv 64 3 ->
  getr regs 6 = Z_to_bv 64 1 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bufs1 + j) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 j ->
  getr regs 17 = Z_to_bv 64 (bufs1 + j + 1) ->
  getr regs 18 = Z_to_bv 64 c ->
  getr regs 30 = Z_to_bv 64 2 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ecbc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ecb8) m' rom)
    /\ mframe v1_1ebb8_cells m m'
    /\ getr regs' 9 = Z_to_bv 64 (bufs1 + j + 1)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1)
    /\ getr regs' 17 = Z_to_bv 64 (bufs1 + j + 2)
    /\ getr regs' 18 = Z_to_bv 64 (c - 1)
    /\ getr regs' 19 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ regs_agree (fun r => In r [9; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_tabval_false TR_tab38_true H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H30 H31.
  pose proof (mframe_refl v1_1ebb8_cells m) as FK0.
  destruct (cells_ok_read SEGS m m v1_1ebb8_cells (bytea (bufs1 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (cells_ok_read SEGS m m v1_1ebb8_cells (lined + (4 * (j / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_1 Rd1_1].
  destruct (TR_tabval_false m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_2 & Rd1_2 & TV1_2).
  destruct (TR_tab38_true m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_3 & Rd1_3 & TV1_3).
  destruct (cells_ok_read SEGS m m v1_1ebb8_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_4 Rd1_4].
  destruct (v1_1ebb8 fx regs m bs1_0 bs1_1 bs1_2 bs1_3 bs1_4 Rd1_0 Rd1_1 Rd1_2 Rd1_3 Rd1_4 TV1_3 (cells_ok_sok SEGS m m v1_1ebb8_cells (lined + (4 * (j / 16)))%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_19 & E1_20 & E1_21 & AG1).
  assert (FK1 : mframe v1_1ebb8_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold v1_1ebb8_cells_def; dl_incl).
  assert (DX : exists d, getr r1 20 = Z_to_bv 64 d /\ tv_ok d) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_20 & DE2_20 & DC2_20).
  assert (DX : exists d, getr r1 21 = Z_to_bv 64 d /\ (0 <= d <= 255)%Z) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_21 & DE2_21 & DC2_21).
  destruct (branch_taken BC_LT (Z_to_bv 64 d2_20) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (v1_1ec78t fx r1 m1 d2_20 d2_21 B1 (cells_ok_sok SEGS m m1 v1_1ebb8_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) DC2_20 DC2_21) as (r2 & m2 & RUN2 & FR2 & E2_9 & E2_16 & E2_17 & E2_18 & AG2).
    assert (FK2 : mframe v1_1ebb8_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold v1_1ebb8_cells_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (v1_1ec78f fx r1 m1 d2_20 d2_21 B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) DC2_20 DC2_21) as (r2 & m2 & RUN2 & FR2 & E2_21 & AG2).
    assert (FK2 : mframe v1_1ebb8_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold v1_1ebb8_cells_def; dl_incl).
    destruct (branch_taken BC_LT (getr r2 20) (Z_to_bv 64 255)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (v1_1ec90t fx r2 m2  B2 (cells_ok_sok SEGS m m2 v1_1ebb8_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_9 & E3_16 & E3_17 & E3_18 & AG3).
      assert (FK3 : mframe v1_1ebb8_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v1_1ebb8_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (v1_1ec90f fx r2 m2  B2 (cells_ok_sok SEGS m m2 v1_1ebb8_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_9 & E3_16 & E3_17 & E3_18 & E3_20 & AG3).
      assert (FK3 : mframe v1_1ebb8_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v1_1ebb8_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
Qed.

End V1.

Definition vt1_1ec9c_cells_def (lined bufs1 tabval w0 wpl wpld : Z) : list (Z * Z) := [((bytea (bufs1 + w0))%Z, 1%Z); ((lined + (4 * (w0 / 16)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition vt1_hyps (lined bufs1 tabval w0 wpl wpld : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (0 <= w0 <= 19999)%Z /\ (w0 + 1 <= 4 * wpl)%Z /\ (w0 + 1 <= 16 * wpld)%Z.
Section VT1.
Variable rom : word -> option byte.
Variables (lined bufs1 tabval w0 wpl wpld : Z).
Hypothesis HYP : vt1_hyps lined bufs1 tabval w0 wpl wpld.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_tabval & A_tabval & R_w0 & Hwpl & Hwpld); pose proof (dl_div_bounds w0 16 ltac:(lia) ltac:(lia)) as DW; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1].
(* [comment removed for export] *)
Lemma vt1_1ec9c : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + w0))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (w0 / 16)))) 4 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (tabval + (4 * (rdv false 1 bs0)))) 4 = Some bs2 ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (w0 / 16)))) 4 = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w0 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eda0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f16c) m' rom)
    /\ mframe [((lined + (4 * (w0 / 16)))%Z, 4%Z)] m m'
    /\ getr regs' 12 = Z_to_bv 64 (lined + (4 * (w0 / 16)))
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 R0 R1 R2 S0 H10 H11 H12 H14.
  dl_facts.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  ex_entry regs [lined; bufs1; tabval; w0; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; tabval; w0; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999]) by (ex_know regs).
  dl_run 400%nat [127340%Z] (SCR [false; false; false; false; false] [EVar 36; EVar 37; EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation vt1_1ec9c_cells := (vt1_1ec9c_cells_def lined bufs1 tabval w0 wpl wpld).
Lemma vt1_1ec9c_path : forall (fx : FPState) regs m,
  cells_ok SEGS m vt1_1ec9c_cells ->
  tab_rd SEGS false (fun _ => True) vt1_1ec9c_cells m tabval ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w0 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eda0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f16c) m' rom)
    /\ mframe vt1_1ec9c_cells m m'
    /\ getr regs' 12 = Z_to_bv 64 (lined + (4 * (w0 / 16)))
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_tabval_false H10 H11 H12 H14.
  pose proof (mframe_refl vt1_1ec9c_cells m) as FK0.
  destruct (cells_ok_read SEGS m m vt1_1ec9c_cells (bytea (bufs1 + w0))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (cells_ok_read SEGS m m vt1_1ec9c_cells (lined + (4 * (w0 / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_1 Rd1_1].
  destruct (TR_tabval_false m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_2 & Rd1_2 & TV1_2).
  destruct (vt1_1ec9c fx regs m bs1_0 bs1_1 bs1_2 Rd1_0 Rd1_1 Rd1_2 (cells_ok_sok SEGS m m vt1_1ec9c_cells (lined + (4 * (w0 / 16)))%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_12 & AG1).
  assert (FK1 : mframe vt1_1ec9c_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold vt1_1ec9c_cells_def; dl_incl).
  exists r1, m1. split; [exact RUN1|]. split; [exact FK1|].
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
Lemma ve_1f068 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte) (bs5 : list byte) (bs6 : list byte) (bs7 : list byte) (bs8 : list byte) (bs9 : list byte),
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some bs4 ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some bs5 ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some bs6 ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some bs7 ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some bs8 ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some bs9 ->
  getr regs 2 = Z_to_bv 64 (s - 80) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f16c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f198) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 8 = Z_to_bv 64 (rdv false 8 bs0)
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 8 bs1)
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 8 bs2)
    /\ getr regs' 19 = Z_to_bv 64 (rdv false 8 bs3)
    /\ getr regs' 20 = Z_to_bv 64 (rdv false 8 bs4)
    /\ getr regs' 21 = Z_to_bv 64 (rdv false 8 bs5)
    /\ getr regs' 22 = Z_to_bv 64 (rdv false 8 bs6)
    /\ getr regs' 23 = Z_to_bv 64 (rdv false 8 bs7)
    /\ getr regs' 24 = Z_to_bv 64 (rdv false 8 bs8)
    /\ getr regs' 25 = Z_to_bv 64 (rdv false 8 bs9)
    /\ regs_agree (fun r => In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 bs5 bs6 bs7 bs8 bs9 R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 H2.
  dl_facts.
  ex_entry regs [s; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5; rdv false 8 bs6; rdv false 8 bs7; rdv false 8 bs8; rdv false 8 bs9] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5; rdv false 8 bs6; rdv false 8 bs7; rdv false 8 bs8; rdv false 8 bs9]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16]) by (ex_know regs).
  dl_run 400%nat (@nil Z) (SCR [] [EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End VE.
