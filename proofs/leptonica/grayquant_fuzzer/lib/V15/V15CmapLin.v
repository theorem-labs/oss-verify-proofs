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
Definition ca_hyps (s : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z.
Section CA.
Variable rom : word -> option byte.
Variables (s : Z).
Hypothesis HYP : ca_hyps s.
Ltac dl_facts := pose proof HYP as (R_s & A_s); idtac.
(* [comment removed for export] *)
Lemma ca_1849c : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 8)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 24)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 2 ->
  getr regs 11 = Z_to_bv 64 4 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x185a0) m rom) (@mkst fx regs' (Z_to_bv 64 0x2891c) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 99860
    /\ getr regs' 2 = Z_to_bv 64 (s - 48)
    /\ getr regs' 9 = Z_to_bv 64 4
    /\ getr regs' 10 = Z_to_bv 64 1
    /\ getr regs' 11 = Z_to_bv 64 24
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 18 = Z_to_bv 64 4
    /\ getr regs' 19 = Z_to_bv 64 2
    /\ rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ regs_agree (fun r => In r [1; 2; 9; 10; 11; 12; 18; 19]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 H2 H10 H11.
  dl_facts.
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16]) by (ex_know regs).
  dl_run 400%nat [166172%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
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
Lemma cb_18510 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (cm + 8)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (cm + 12)) 4 = true ->
  getr regs 2 = Z_to_bv 64 f ->
  getr regs 9 = Z_to_bv 64 4 ->
  getr regs 10 = Z_to_bv 64 cm ->
  getr regs 18 = Z_to_bv 64 4 ->
  getr regs 19 = Z_to_bv 64 2 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18614) m rom) (@mkst fx regs' (Z_to_bv 64 0x2891c) m' rom)
    /\ mframe [((cm + 8)%Z, 4%Z); ((cm + 12)%Z, 4%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 99896
    /\ getr regs' 8 = Z_to_bv 64 cm
    /\ getr regs' 10 = Z_to_bv 64 4
    /\ getr regs' 11 = Z_to_bv 64 4
    /\ rdn SEGS m' (Z_to_bv 64 (cm + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))
    /\ rdn SEGS m' (Z_to_bv 64 (cm + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4))
    /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 H2 H9 H10 H18 H19.
  dl_facts.
  ex_entry regs [f; cm] HR.
  assert (HK : know_ok SEGS (ex_env regs [f; cm]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 16]) by (ex_know regs).
  dl_run 400%nat [166172%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End CB.

(* [comment removed for export] *)
Definition cc_hyps (f cm arr : Z) : Prop :=
  (4096 <= f <= 140737488355328)%Z /\ (f mod 16 = 0)%Z /\ (4096 <= cm <= 140737488355328)%Z /\ (cm mod 16 = 0)%Z /\ (4096 <= arr <= 140737488355328)%Z /\ (arr mod 16 = 0)%Z /\ dapart cm 24 arr 16 /\ dapart cm 24 f 48 /\ dapart arr 16 f 48.
Section CC.
Variable rom : word -> option byte.
Variables (f cm arr : Z).
Hypothesis HYP : cc_hyps f cm arr.
Ltac dl_facts := pose proof HYP as (R_f & A_f & R_cm & A_cm & R_arr & A_arr & AP_ca & AP_cf & AP_af); idtac.
(* [comment removed for export] *)
Lemma cc_18534 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte) (bs5 : list byte),
  rdn SEGS m (Z_to_bv 64 (f + 40)) 8 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (f + 32)) 8 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (f + 24)) 8 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (f + 16)) 8 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (f + 8)) 8 = Some bs4 ->
  rdn SEGS m (Z_to_bv 64 f) 8 = Some bs5 ->
  store_ok SEGS m (Z_to_bv 64 cm) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (cm + 16)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 2)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 arr) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 1)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 3)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 6)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 4)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 5)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 7)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 10)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 8)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 9)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 11)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 14)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 12)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 13)) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (arr + 15)) 1 = true ->
  rdn SEGS m (Z_to_bv 64 (cm + 12)) 4 = Some (Z_to_le_bytes 4 4) ->
  getr regs 2 = Z_to_bv 64 f ->
  getr regs 8 = Z_to_bv 64 cm ->
  getr regs 10 = Z_to_bv 64 arr ->
  getr regs 18 = Z_to_bv 64 4 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18638) m rom) (@mkst fx regs' (Z_to_bv 64 0x18720) m' rom)
    /\ mframe [((cm)%Z, 8%Z); ((cm + 16)%Z, 4%Z); ((arr + 2)%Z, 1%Z); ((arr)%Z, 1%Z); ((arr + 1)%Z, 1%Z); ((arr + 3)%Z, 1%Z); ((arr + 6)%Z, 1%Z); ((arr + 4)%Z, 1%Z); ((arr + 5)%Z, 1%Z); ((arr + 7)%Z, 1%Z); ((arr + 10)%Z, 1%Z); ((arr + 8)%Z, 1%Z); ((arr + 9)%Z, 1%Z); ((arr + 11)%Z, 1%Z); ((arr + 14)%Z, 1%Z); ((arr + 12)%Z, 1%Z); ((arr + 13)%Z, 1%Z); ((arr + 15)%Z, 1%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 (rdv false 8 bs0)
    /\ getr regs' 2 = Z_to_bv 64 (f + 48)
    /\ getr regs' 5 = Z_to_bv 64 0
    /\ getr regs' 8 = Z_to_bv 64 (rdv false 8 bs1)
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 8 bs2)
    /\ getr regs' 10 = Z_to_bv 64 cm
    /\ getr regs' 11 = Z_to_bv 64 255
    /\ getr regs' 12 = Z_to_bv 64 255
    /\ getr regs' 13 = Z_to_bv 64 255
    /\ getr regs' 14 = Z_to_bv 64 4
    /\ getr regs' 15 = Z_to_bv 64 (arr + 12)
    /\ getr regs' 16 = Z_to_bv 64 18446744073709551615
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 8 bs3)
    /\ getr regs' 19 = Z_to_bv 64 (rdv false 8 bs4)
    /\ getr regs' 20 = Z_to_bv 64 (rdv false 8 bs5)
    /\ rdn SEGS m' (Z_to_bv 64 cm) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 2)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 arr) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 3)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 6)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 85))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 4)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 85))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 5)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 85))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 7)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 170))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 8)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 170))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 9)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 170))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 14)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 12)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 13)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ rdn SEGS m' (Z_to_bv 64 (arr + 15)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615))
    /\ rdn SEGS m' (Z_to_bv 64 (cm + 16)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4))
    /\ regs_agree (fun r => In r [1; 2; 5; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 bs5 R0 R1 R2 R3 R4 R5 S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17 KC0 H2 H8 H10 H18.
  dl_facts.
  ex_entry regs [f; cm; arr; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5] HR.
  assert (HK : know_ok SEGS (ex_env regs [f; cm; arr; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5]) m [KWord (SA (EVar 33) (12)) 4 (ELit 4); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 16; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 16; KDisj (SA (EVar 33) (0)) 24 (SA (EVar 34) (0)) 16; KDisj (SA (EVar 33) (0)) 24 (SA (EVar 32) (0)) 48; KDisj (SA (EVar 34) (0)) 16 (SA (EVar 32) (0)) 48]) by (unfold dapart in *; ex_know regs).
  dl_run 400%nat (@nil Z) (SCR [false; false; false; false] [EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End CC.
