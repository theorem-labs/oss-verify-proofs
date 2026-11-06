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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab DitherTabW.
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
Definition ca_hyps (s : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z.
Section CA.
Variable rom : word -> option byte.
Variables (s : Z).
Hypothesis HYP : ca_hyps s.
Ltac dl_facts := pose proof HYP as (R_s & A_s); idtac.
(* [comment removed for export] *)
Lemma ca_17bac : forall (fx : FPState) regs m ,
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
  store_ok SEGS m (Z_to_bv 64 (s - 88)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 2 ->
  getr regs 11 = Z_to_bv 64 4 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x17ca8) m rom) (@mkst fx regs' (Z_to_bv 64 0x20ea0) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z); ((s - 56)%Z, 8%Z); ((s - 64)%Z, 8%Z); ((s - 72)%Z, 8%Z); ((s - 80)%Z, 8%Z); ((s - 88)%Z, 8%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 97584
    /\ getr regs' 2 = Z_to_bv 64 (s - 96)
    /\ getr regs' 8 = Z_to_bv 64 4
    /\ getr regs' 10 = Z_to_bv 64 1
    /\ getr regs' 11 = Z_to_bv 64 24
    /\ getr regs' 18 = Z_to_bv 64 4
    /\ getr regs' 19 = Z_to_bv 64 2
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25))
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 18; 19]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 H2 H10 H11.
  dl_facts.
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16]) by (ex_know regs).
  dl_run 400%nat [134816%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End CA.

(* [comment removed for export] *)
Definition cb_hyps (f cm : Z) : Prop :=
  (4096 <= f <= 140737488355328)%Z /\ (f mod 16 = 0)%Z /\ (4096 <= cm <= 140737488355328)%Z /\ (cm mod 16 = 0)%Z.
Section CB.
Variable rom : word -> option byte.
Variables (f cm : Z).
Hypothesis HYP : cb_hyps f cm.
Ltac dl_facts := pose proof HYP as (R_f & A_f & R_cm & A_cm); idtac.
(* [comment removed for export] *)
Lemma cb_17c34 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (cm + 8)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (cm + 12)) 4 = true ->
  getr regs 2 = Z_to_bv 64 f ->
  getr regs 8 = Z_to_bv 64 4 ->
  getr regs 10 = Z_to_bv 64 cm ->
  getr regs 18 = Z_to_bv 64 4 ->
  getr regs 19 = Z_to_bv 64 2 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x17d30) m rom) (@mkst fx regs' (Z_to_bv 64 0x20ea0) m' rom)
    /\ mframe [((cm + 8)%Z, 4%Z); ((cm + 12)%Z, 4%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 97608
    /\ getr regs' 9 = Z_to_bv 64 cm
    /\ getr regs' 10 = Z_to_bv 64 4
    /\ getr regs' 11 = Z_to_bv 64 4
    /\ rdn SEGS m' (Z_to_bv 64 (cm + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))
    /\ rdn SEGS m' (Z_to_bv 64 (cm + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4))
    /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 H2 H8 H10 H18 H19.
  dl_facts.
  ex_entry regs [f; cm] HR.
  assert (HK : know_ok SEGS (ex_env regs [f; cm]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 16]) by (ex_know regs).
  dl_run 400%nat [134816%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End CB.

(* [comment removed for export] *)
Definition cc_hyps (f cm arr : Z) : Prop :=
  (4096 <= f <= 140737488355328)%Z /\ (f mod 16 = 0)%Z /\ (4096 <= cm <= 140737488355328)%Z /\ (cm mod 16 = 0)%Z /\ (4096 <= arr <= 140737488355328)%Z /\ (arr mod 16 = 0)%Z /\ dapart cm 24 arr 16 /\ dapart cm 24 f 96 /\ dapart arr 16 f 96 /\ dapart cm 24 182144 8 /\ dapart arr 16 182144 8.
Section CC.
Variable rom : word -> option byte.
Variables (f cm arr : Z).
Hypothesis HYP : cc_hyps f cm arr.
Ltac dl_facts := pose proof HYP as (R_f & A_f & R_cm & A_cm & R_arr & A_arr & AP_ca & AP_cf & AP_af & AP_cg & AP_ag); idtac.
(* [comment removed for export] *)
Lemma cc_17c4c : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte) (bs5 : list byte) (bs6 : list byte) (bs7 : list byte) (bs8 : list byte) (bs9 : list byte) (bs10 : list byte) (bs11 : list byte),
  rdn SEGS m (Z_to_bv 64 182144) 8 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (f + 88)) 8 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (f + 80)) 8 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (f + 72)) 8 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (f + 64)) 8 = Some bs4 ->
  rdn SEGS m (Z_to_bv 64 (f + 56)) 8 = Some bs5 ->
  rdn SEGS m (Z_to_bv 64 (f + 48)) 8 = Some bs6 ->
  rdn SEGS m (Z_to_bv 64 (f + 40)) 8 = Some bs7 ->
  rdn SEGS m (Z_to_bv 64 (f + 32)) 8 = Some bs8 ->
  rdn SEGS m (Z_to_bv 64 (f + 24)) 8 = Some bs9 ->
  rdn SEGS m (Z_to_bv 64 (f + 16)) 8 = Some bs10 ->
  rdn SEGS m (Z_to_bv 64 (f + 8)) 8 = Some bs11 ->
  store_ok SEGS m (Z_to_bv 64 cm) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (cm + 16)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 arr) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 1)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 2)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 3)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 4)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 5)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 6)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 7)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 8)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 9)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 10)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 11)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 12)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 13)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 14)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 15)) 1 = true ->
  rdn SEGS m (Z_to_bv 64 (cm + 12)) 4 = Some (Z_to_le_bytes 4 4) ->
  getr regs 2 = Z_to_bv 64 f ->
  getr regs 8 = Z_to_bv 64 4 ->
  getr regs 9 = Z_to_bv 64 cm ->
  getr regs 10 = Z_to_bv 64 arr ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x17d48) m rom) (@mkst fx regs' (Z_to_bv 64 0x17eac) m' rom)
    /\ mframe [((cm)%Z, 8%Z); ((cm + 16)%Z, 4%Z); ((arr)%Z, 1%Z); ((arr + 1)%Z, 1%Z); ((arr + 2)%Z, 1%Z); ((arr + 3)%Z, 1%Z); ((arr + 4)%Z, 1%Z); ((arr + 5)%Z, 1%Z); ((arr + 6)%Z, 1%Z); ((arr + 7)%Z, 1%Z); ((arr + 8)%Z, 1%Z); ((arr + 9)%Z, 1%Z); ((arr + 10)%Z, 1%Z); ((arr + 11)%Z, 1%Z); ((arr + 12)%Z, 1%Z); ((arr + 13)%Z, 1%Z); ((arr + 14)%Z, 1%Z); ((arr + 15)%Z, 1%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 (rdv false 8 bs1)
    /\ getr regs' 2 = Z_to_bv 64 (f + 96)
    /\ getr regs' 8 = Z_to_bv 64 (rdv false 8 bs2)
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 8 bs3)
    /\ getr regs' 10 = Z_to_bv 64 cm
    /\ getr regs' 11 = Z_to_bv 64 (arr + 12)
    /\ getr regs' 12 = Z_to_bv 64 255
    /\ getr regs' 13 = Z_to_bv 64 12
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 8 bs4)
    /\ getr regs' 19 = Z_to_bv 64 (rdv false 8 bs5)
    /\ getr regs' 20 = Z_to_bv 64 (rdv false 8 bs6)
    /\ getr regs' 21 = Z_to_bv 64 (rdv false 8 bs7)
    /\ getr regs' 22 = Z_to_bv 64 (rdv false 8 bs8)
    /\ getr regs' 23 = Z_to_bv 64 (rdv false 8 bs9)
    /\ getr regs' 24 = Z_to_bv 64 (rdv false 8 bs10)
    /\ getr regs' 25 = Z_to_bv 64 (rdv false 8 bs11)
    /\ rdn SEGS m' (Z_to_bv 64 cm) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr))
    /\ rdn SEGS m' (Z_to_bv 64 arr) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 2)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 3)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 4)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 85))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 5)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 85))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 6)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 85))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 7)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 8)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 170))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 9)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 170))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 170))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 12)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 13)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 14)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 15)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615))
    /\ rdn SEGS m' (Z_to_bv 64 (cm + 16)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4))
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 bs5 bs6 bs7 bs8 bs9 bs10 bs11 R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17 KC0 H2 H8 H9 H10.
  dl_facts.
  ex_entry regs [f; cm; arr; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5; rdv false 8 bs6; rdv false 8 bs7; rdv false 8 bs8; rdv false 8 bs9; rdv false 8 bs10; rdv false 8 bs11] HR.
  assert (HK : know_ok SEGS (ex_env regs [f; cm; arr; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5; rdv false 8 bs6; rdv false 8 bs7; rdv false 8 bs8; rdv false 8 bs9; rdv false 8 bs10; rdv false 8 bs11]) m [KWord (SA (EVar 33) (12)) 4 (ELit 4); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 16; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 16; KDisj (SA (EVar 33) (0)) 24 (SA (EVar 34) (0)) 16; KDisj (SA (EVar 33) (0)) 24 (SA (EVar 32) (0)) 96; KDisj (SA (EVar 34) (0)) 16 (SA (EVar 32) (0)) 96; KDisj (SA (EVar 33) (0)) 24 (SA (ELit 182144) (0)) 8; KDisj (SA (EVar 34) (0)) 16 (SA (ELit 182144) (0)) 8]) by (unfold dapart in *; ex_know regs).
  dl_run 400%nat (@nil Z) (SCR [] [EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45; EVar 46] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End CC.
