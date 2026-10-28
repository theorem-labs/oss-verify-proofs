(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2.
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
Definition xp_hyps (s datad w h wpld datas wpls bufs1 bufs2 lc uc : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wpld <= 625)%Z /\ (4096 <= datas <= 140737488355328)%Z /\ (datas mod 4 = 0)%Z /\ (1 <= wpls <= 5000)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z.
Section XP.
Variable rom : word -> option byte.
Variables (s datad w h wpld datas wpls bufs1 bufs2 lc uc : Z).
Hypothesis HYP : xp_hyps s datad w h wpld datas wpls bufs1 bufs2 lc uc.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_w & R_h & R_wpld & R_datas & A_datas & R_wpls & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_lc & R_uc); idtac.
(* [comment removed for export] *)
Lemma xp_1b858 : forall (fx : FPState) regs m ,
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
  store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 104)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 120)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 136)) 8 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 datad ->
  getr regs 11 = Z_to_bv 64 w ->
  getr regs 12 = Z_to_bv 64 h ->
  getr regs 13 = Z_to_bv 64 wpld ->
  getr regs 14 = Z_to_bv 64 datas ->
  getr regs 15 = Z_to_bv 64 wpls ->
  getr regs 16 = Z_to_bv 64 bufs1 ->
  getr regs 17 = Z_to_bv 64 bufs2 ->
  getr regs 28 = Z_to_bv 64 lc ->
  getr regs 29 = Z_to_bv 64 uc ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b95c) m rom) (@mkst fx regs' (Z_to_bv 64 0x326c4) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z); ((s - 56)%Z, 8%Z); ((s - 64)%Z, 8%Z); ((s - 72)%Z, 8%Z); ((s - 80)%Z, 8%Z); ((s - 88)%Z, 8%Z); ((s - 96)%Z, 8%Z); ((s - 104)%Z, 8%Z); ((s - 120)%Z, 8%Z); ((s - 128)%Z, 8%Z); ((s - 136)%Z, 8%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 113132
    /\ getr regs' 2 = Z_to_bv 64 (s - 144)
    /\ getr regs' 10 = Z_to_bv 64 bufs2
    /\ getr regs' 11 = Z_to_bv 64 datas
    /\ getr regs' 12 = Z_to_bv 64 (wpls * 4)
    /\ getr regs' 18 = Z_to_bv 64 bufs2
    /\ getr regs' 19 = Z_to_bv 64 bufs1
    /\ getr regs' 21 = Z_to_bv 64 datad
    /\ getr regs' 22 = Z_to_bv 64 wpld
    /\ getr regs' 23 = Z_to_bv 64 wpls
    /\ getr regs' 24 = Z_to_bv 64 datas
    /\ getr regs' 25 = Z_to_bv 64 (wpls * 4)
    /\ getr regs' 26 = Z_to_bv 64 h
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
    /\ rdn SEGS m' (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 uc))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 lc))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w))
    /\ regs_agree (fun r => In r [1; 2; 10; 11; 12; 18; 19; 21; 22; 23; 24; 25; 26]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 H2 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29.
  dl_facts.
  ex_entry regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 625; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 1 5000; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 4; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255]) by (ex_know regs).
  dl_run 400%nat [206532%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End XP.

(* [comment removed for export] *)
Definition xa_hyps (s datad wpld datas wpls bufs1 bufs2 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= wpld <= 625)%Z /\ (4096 <= datas <= 140737488355328)%Z /\ (datas mod 4 = 0)%Z /\ (1 <= wpls <= 5000)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z.
Section XA.
Variable rom : word -> option byte.
Variables (s datad wpld datas wpls bufs1 bufs2 : Z).
Hypothesis HYP : xa_hyps s datad wpld datas wpls bufs1 bufs2.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_wpld & R_datas & A_datas & R_wpls & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2); idtac.
(* [comment removed for export] *)
Lemma xa_1b8e8 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 144)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  getr regs 26 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b9ec) m rom) (@mkst fx regs' (Z_to_bv 64 0x1badc) m' rom)
    /\ mframe [((s - 112)%Z, 8%Z); ((s - 144)%Z, 8%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ rdn SEGS m' (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 H2 H18 H19 H21 H22 H23 H24 H25 H26.
  dl_facts.
  ex_entry regs [s; datad; wpld; datas; wpls; bufs1; bufs2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; wpld; datas; wpls; bufs1; bufs2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 625; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 5000; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4]) by (ex_know regs).
  dl_run 400%nat [113372%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End XA.

(* [comment removed for export] *)
Definition xb_hyps (s datad wpld datas wpls bufs1 bufs2 h2 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= wpld <= 625)%Z /\ (4096 <= datas <= 140737488355328)%Z /\ (datas mod 4 = 0)%Z /\ (1 <= wpls <= 5000)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (2 <= h2 <= 20000)%Z.
Section XB.
Variable rom : word -> option byte.
Variables (s datad wpld datas wpls bufs1 bufs2 h2 : Z).
Hypothesis HYP : xb_hyps s datad wpld datas wpls bufs1 bufs2 h2.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_wpld & R_datas & A_datas & R_wpls & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_h2); idtac.
(* [comment removed for export] *)
Lemma xb_1b8e8 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 144)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  getr regs 26 = Z_to_bv 64 h2 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b9ec) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ba20) m' rom)
    /\ mframe [((s - 112)%Z, 8%Z); ((s - 144)%Z, 8%Z)] m m'
    /\ getr regs' 8 = Z_to_bv 64 (h2 - 1)
    /\ getr regs' 9 = Z_to_bv 64 1
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 26 = Z_to_bv 64 0
    /\ getr regs' 27 = Z_to_bv 64 1
    /\ rdn SEGS m' (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (h2 - 1)))
    /\ regs_agree (fun r => In r [8; 9; 10; 11; 26; 27]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 H2 H18 H19 H21 H22 H23 H24 H25 H26.
  dl_facts.
  ex_entry regs [s; datad; wpld; datas; wpls; bufs1; bufs2; h2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; wpld; datas; wpls; bufs1; bufs2; h2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 625; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 1 5000; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 2 20000]) by (ex_know regs).
  dl_run 400%nat [113184%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End XB.

(* [comment removed for export] *)
Definition xr_hyps (s datad w wpld datas wpls bufs1 bufs2 lc uc i h1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= wpld <= 625)%Z /\ (4096 <= datas <= 140737488355328)%Z /\ (datas mod 4 = 0)%Z /\ (1 <= wpls <= 5000)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (0 <= i <= 19998)%Z /\ (0 <= h1 <= 19999)%Z /\ (0 <= i < h1)%Z /\ (0 <= (i + 1) * wpls < 2 ^ 24)%Z /\ (0 <= i * wpld < 2 ^ 24)%Z.
Section XR.
Variable rom : word -> option byte.
Variables (s datad w wpld datas wpls bufs1 bufs2 lc uc i h1 : Z).
Hypothesis HYP : xr_hyps s datad w wpld datas wpls bufs1 bufs2 lc uc i h1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_w & R_wpld & R_datas & A_datas & R_wpls & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_lc & R_uc & R_i & R_h1 & Hi & Hps & Hpd); idtac.
(* [comment removed for export] *)
Lemma xr_1b91c : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 8 = Z_to_bv 64 h1 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  getr regs 26 = Z_to_bv 64 i ->
  getr regs 27 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ba20) m rom) (@mkst fx regs' (Z_to_bv 64 0x326c4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 113208
    /\ getr regs' 10 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 bufs2
    /\ getr regs' 12 = Z_to_bv 64 (wpls * 4)
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1]) m [KWord (SA (EVar 32) (-112)) 8 (ELit 0); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KWord (SA (EVar 32) (-128)) 8 (EVar 40); KWord (SA (EVar 32) (-136)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 625; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 5000; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 19998; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [113184%Z; 113372%Z; 113544%Z; 206532%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma xr_1b934 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 8 = Z_to_bv 64 h1 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  getr regs 26 = Z_to_bv 64 i ->
  getr regs 27 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ba38) m rom) (@mkst fx regs' (Z_to_bv 64 0x326c4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 113284
    /\ getr regs' 10 = Z_to_bv 64 bufs2
    /\ getr regs' 11 = Z_to_bv 64 (datas + (4 * ((i + 1) * wpls)))
    /\ getr regs' 12 = Z_to_bv 64 (wpls * 4)
    /\ getr regs' 20 = Z_to_bv 64 (i + 1)
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 20]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1]) m [KWord (SA (EVar 32) (-112)) 8 (ELit 0); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KWord (SA (EVar 32) (-128)) 8 (EVar 40); KWord (SA (EVar 32) (-136)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 625; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 5000; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 19998; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [113184%Z; 113372%Z; 113544%Z; 206532%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma xr_1b980 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 8 = Z_to_bv 64 h1 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 20 = Z_to_bv 64 (i + 1) ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  getr regs 26 = Z_to_bv 64 i ->
  getr regs 27 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ba84) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bb88) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 113364
    /\ getr regs' 10 = Z_to_bv 64 (datad + (4 * (i * wpld)))
    /\ getr regs' 11 = Z_to_bv 64 w
    /\ getr regs' 12 = Z_to_bv 64 bufs1
    /\ getr regs' 13 = Z_to_bv 64 bufs2
    /\ getr regs' 14 = Z_to_bv 64 lc
    /\ getr regs' 15 = Z_to_bv 64 uc
    /\ getr regs' 16 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1]) m [KWord (SA (EVar 32) (-112)) 8 (ELit 0); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KWord (SA (EVar 32) (-128)) 8 (EVar 40); KWord (SA (EVar 32) (-136)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 625; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 5000; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 19998; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [113184%Z; 113372%Z; 113544%Z; 206532%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma xr_1b9d0 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 8 = Z_to_bv 64 h1 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 20 = Z_to_bv 64 (i + 1) ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  getr regs 27 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bad4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bad8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 26 = Z_to_bv 64 (i + 1)
    /\ regs_agree (fun r => In r [26]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H27.
  dl_facts.
  ex_entry regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1]) m [KWord (SA (EVar 32) (-112)) 8 (ELit 0); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KWord (SA (EVar 32) (-128)) 8 (EVar 40); KWord (SA (EVar 32) (-136)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 625; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 5000; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 19998; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [113184%Z; 113372%Z; 113544%Z; 206532%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma xr_1b9d4f : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 h1) (Z_to_bv 64 (i + 1)) = false ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 8 = Z_to_bv 64 h1 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 20 = Z_to_bv 64 (i + 1) ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  getr regs 26 = Z_to_bv 64 (i + 1) ->
  getr regs 27 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bad8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1badc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1]) m [KWord (SA (EVar 32) (-112)) 8 (ELit 0); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KWord (SA (EVar 32) (-128)) 8 (EVar 40); KWord (SA (EVar 32) (-136)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 625; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 5000; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 19998; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [113184%Z; 113372%Z; 113544%Z; 206532%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma xr_1b9d4t : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 h1) (Z_to_bv 64 (i + 1)) = true ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 8 = Z_to_bv 64 h1 ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 20 = Z_to_bv 64 (i + 1) ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  getr regs 26 = Z_to_bv 64 (i + 1) ->
  getr regs 27 = Z_to_bv 64 1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1bad8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ba20) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; wpld; datas; wpls; bufs1; bufs2; lc; uc; i; h1]) m [KWord (SA (EVar 32) (-112)) 8 (ELit 0); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KWord (SA (EVar 32) (-128)) 8 (EVar 40); KWord (SA (EVar 32) (-136)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 625; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 5000; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 19998; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [113184%Z; 113372%Z; 113544%Z; 206532%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End XR.

(* [comment removed for export] *)
Definition xl_hyps (s datad w wpld wpls bufs1 bufs2 lc uc h1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= wpld <= 625)%Z /\ (1 <= wpls <= 5000)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (0 <= h1 <= 19999)%Z /\ (0 <= h1 * wpld < 2 ^ 24)%Z.
Section XL.
Variable rom : word -> option byte.
Variables (s datad w wpld wpls bufs1 bufs2 lc uc h1 : Z).
Hypothesis HYP : xl_hyps s datad w wpld wpls bufs1 bufs2 lc uc h1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_w & R_wpld & R_wpls & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_lc & R_uc & R_h1 & Hpd); idtac.
(* [comment removed for export] *)
Lemma xl_1b9d8 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1badc) m rom) (@mkst fx regs' (Z_to_bv 64 0x326c4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 113396
    /\ getr regs' 10 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 bufs2
    /\ getr regs' 12 = Z_to_bv 64 (wpls * 4)
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 KC4 H2 H18 H19 H21 H22 H23 H25.
  dl_facts.
  ex_entry regs [s; datad; w; wpld; wpls; bufs1; bufs2; lc; uc; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; wpld; wpls; bufs1; bufs2; lc; uc; h1]) m [KWord (SA (EVar 32) (-112)) 8 (ELit 0); KWord (SA (EVar 32) (-120)) 8 (EVar 40); KWord (SA (EVar 32) (-128)) 8 (EVar 39); KWord (SA (EVar 32) (-136)) 8 (EVar 34); KWord (SA (EVar 32) (-144)) 8 (EVar 41); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 625; KRange (EVar 36) 1 5000; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 0 255; KRange (EVar 40) 0 255; KRange (EVar 41) 0 19999]) by (ex_know regs).
  dl_run 400%nat [113544%Z; 206532%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma xl_1b9f0 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte) (bs5 : list byte) (bs6 : list byte) (bs7 : list byte) (bs8 : list byte) (bs9 : list byte) (bs10 : list byte) (bs11 : list byte) (bs12 : list byte),
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
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some bs10 ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some bs11 ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some bs12 ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 144) ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 bufs1 ->
  getr regs 21 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 wpld ->
  getr regs 23 = Z_to_bv 64 wpls ->
  getr regs 25 = Z_to_bv 64 (wpls * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1baf4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1bb88) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 (rdv false 8 bs0)
    /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 8 = Z_to_bv 64 (rdv false 8 bs1)
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 8 bs2)
    /\ getr regs' 10 = Z_to_bv 64 (datad + (4 * (h1 * wpld)))
    /\ getr regs' 11 = Z_to_bv 64 w
    /\ getr regs' 12 = Z_to_bv 64 bufs1
    /\ getr regs' 13 = Z_to_bv 64 bufs2
    /\ getr regs' 14 = Z_to_bv 64 lc
    /\ getr regs' 15 = Z_to_bv 64 uc
    /\ getr regs' 16 = Z_to_bv 64 1
    /\ getr regs' 18 = Z_to_bv 64 (rdv false 8 bs3)
    /\ getr regs' 19 = Z_to_bv 64 (rdv false 8 bs4)
    /\ getr regs' 20 = Z_to_bv 64 (rdv false 8 bs5)
    /\ getr regs' 21 = Z_to_bv 64 (rdv false 8 bs6)
    /\ getr regs' 22 = Z_to_bv 64 (rdv false 8 bs7)
    /\ getr regs' 23 = Z_to_bv 64 (rdv false 8 bs8)
    /\ getr regs' 24 = Z_to_bv 64 (rdv false 8 bs9)
    /\ getr regs' 25 = Z_to_bv 64 (rdv false 8 bs10)
    /\ getr regs' 26 = Z_to_bv 64 (rdv false 8 bs11)
    /\ getr regs' 27 = Z_to_bv 64 (rdv false 8 bs12)
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 bs5 bs6 bs7 bs8 bs9 bs10 bs11 bs12 R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 KC0 KC1 KC2 KC3 KC4 H2 H18 H19 H21 H22 H23 H25.
  dl_facts.
  ex_entry regs [s; datad; w; wpld; wpls; bufs1; bufs2; lc; uc; h1; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5; rdv false 8 bs6; rdv false 8 bs7; rdv false 8 bs8; rdv false 8 bs9; rdv false 8 bs10; rdv false 8 bs11; rdv false 8 bs12] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; wpld; wpls; bufs1; bufs2; lc; uc; h1; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5; rdv false 8 bs6; rdv false 8 bs7; rdv false 8 bs8; rdv false 8 bs9; rdv false 8 bs10; rdv false 8 bs11; rdv false 8 bs12]) m [KWord (SA (EVar 32) (-112)) 8 (ELit 0); KWord (SA (EVar 32) (-120)) 8 (EVar 40); KWord (SA (EVar 32) (-128)) 8 (EVar 39); KWord (SA (EVar 32) (-136)) 8 (EVar 34); KWord (SA (EVar 32) (-144)) 8 (EVar 41); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 625; KRange (EVar 36) 1 5000; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 0 255; KRange (EVar 40) 0 255; KRange (EVar 41) 0 19999]) by (ex_know regs).
  dl_run 400%nat [113544%Z; 206532%Z] (SCR [false; false] [EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48; EVar 49; EVar 50; EVar 51; EVar 52; EVar 53; EVar 54] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End XL.
