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

(* [comment removed for export] *)
Definition wp_hyps (s datad w h wpld datas wpls bufs1 bufs2 lc uc : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wpld <= 625)%Z /\ (4096 <= datas <= 140737488355328)%Z /\ (datas mod 4 = 0)%Z /\ (1 <= wpls <= 5000)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z.
Section WP.
Variable rom : word -> option byte.
Variables (s datad w h wpld datas wpls bufs1 bufs2 lc uc : Z).
Hypothesis HYP : wp_hyps s datad w h wpld datas wpls bufs1 bufs2 lc uc.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_w & R_h & R_wpld & R_datas & A_datas & R_wpls & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_lc & R_uc); idtac.
(* [comment removed for export] *)
Lemma wp_1a358 : forall (fx : FPState) regs m ,
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
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 120)) 8 = true ->
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
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a454) m rom) (@mkst fx regs' (Z_to_bv 64 0x2ac48) m' rom)
    /\ mframe [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z); ((s - 56)%Z, 8%Z); ((s - 64)%Z, 8%Z); ((s - 72)%Z, 8%Z); ((s - 80)%Z, 8%Z); ((s - 88)%Z, 8%Z); ((s - 96)%Z, 8%Z); ((s - 104)%Z, 8%Z); ((s - 112)%Z, 8%Z); ((s - 120)%Z, 8%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 107720
    /\ getr regs' 2 = Z_to_bv 64 (s - 128)
    /\ getr regs' 8 = Z_to_bv 64 bufs1
    /\ getr regs' 9 = Z_to_bv 64 uc
    /\ getr regs' 10 = Z_to_bv 64 bufs2
    /\ getr regs' 11 = Z_to_bv 64 datas
    /\ getr regs' 12 = Z_to_bv 64 (wpls * 4)
    /\ getr regs' 18 = Z_to_bv 64 lc
    /\ getr regs' 19 = Z_to_bv 64 w
    /\ getr regs' 21 = Z_to_bv 64 bufs2
    /\ getr regs' 23 = Z_to_bv 64 (wpls * 4)
    /\ getr regs' 24 = Z_to_bv 64 datas
    /\ getr regs' 25 = Z_to_bv 64 wpls
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
    /\ rdn SEGS m' (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wpld))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad))
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 21; 23; 24; 25; 26]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 H2 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29.
  dl_facts.
  ex_entry regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 625; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 1 5000; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 4; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255]) by (ex_know regs).
  dl_run 400%nat [175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End WP.

(* [comment removed for export] *)
Definition wa_hyps (s datad w h wpld datas wpls bufs1 bufs2 lc uc : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wpld <= 625)%Z /\ (4096 <= datas <= 140737488355328)%Z /\ (datas mod 4 = 0)%Z /\ (1 <= wpls <= 5000)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z.
Section WA.
Variable rom : word -> option byte.
Variables (s datad w h wpld datas wpls bufs1 bufs2 lc uc : Z).
Hypothesis HYP : wa_hyps s datad w h wpld datas wpls bufs1 bufs2 lc uc.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_w & R_h & R_wpld & R_datas & A_datas & R_wpls & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_lc & R_uc); idtac.
(* [comment removed for export] *)
Lemma wa_1a3cc : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datad) ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 wpls ->
  getr regs 26 = Z_to_bv 64 h ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a4c8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a4d0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 2
    /\ getr regs' 27 = Z_to_bv 64 (h - 1)
    /\ regs_agree (fun r => In r [10; 27]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H8 H9 H18 H19 H21 H24 H25 H26.
  dl_facts.
  ex_entry regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc]) m [KWord (SA (EVar 32) (-112)) 8 (EVar 36); KWord (SA (EVar 32) (-120)) 8 (EVar 33); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 625; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 1 5000; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 4; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wa_1a3d4f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 h) (Z_to_bv 64 2) = false ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datad) ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 2 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 wpls ->
  getr regs 26 = Z_to_bv 64 h ->
  getr regs 27 = Z_to_bv 64 (h - 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a4d0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a4f0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 ((4294967296 * h) - 4294967296)
    /\ getr regs' 20 = Z_to_bv 64 (4 * wpls)
    /\ getr regs' 22 = Z_to_bv 64 (h - 1)
    /\ getr regs' 24 = Z_to_bv 64 (datas + (4 * wpls))
    /\ getr regs' 25 = Z_to_bv 64 datad
    /\ getr regs' 26 = Z_to_bv 64 (4 * wpld)
    /\ regs_agree (fun r => In r [10; 20; 22; 24; 25; 26]%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H8 H9 H10 H18 H19 H21 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc]) m [KWord (SA (EVar 32) (-112)) 8 (EVar 36); KWord (SA (EVar 32) (-120)) 8 (EVar 33); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 625; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 1 5000; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 4; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wa_1a3d4t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 h) (Z_to_bv 64 2) = true ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datad) ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 2 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 24 = Z_to_bv 64 datas ->
  getr regs 25 = Z_to_bv 64 wpls ->
  getr regs 26 = Z_to_bv 64 h ->
  getr regs 27 = Z_to_bv 64 (h - 1) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a4d0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a540) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H8 H9 H10 H18 H19 H21 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; h; wpld; datas; wpls; bufs1; bufs2; lc; uc]) m [KWord (SA (EVar 32) (-112)) 8 (EVar 36); KWord (SA (EVar 32) (-120)) 8 (EVar 33); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000; KRange (EVar 36) 1 625; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 1 5000; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 4; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End WA.

(* [comment removed for export] *)
Definition wr_hyps (s bufs1 bufs2 srow drow w lc uc n4 d4 cnt h1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= srow <= 140737488355328)%Z /\ (srow mod 4 = 0)%Z /\ (4096 <= drow <= 140737488355328)%Z /\ (drow mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (4 <= n4 <= 20000)%Z /\ (4 <= d4 <= 2500)%Z /\ (1 <= cnt <= 19999)%Z /\ (0 <= h1 <= 19999)%Z.
Section WR.
Variable rom : word -> option byte.
Variables (s bufs1 bufs2 srow drow w lc uc n4 d4 cnt h1 : Z).
Hypothesis HYP : wr_hyps s bufs1 bufs2 srow drow w lc uc n4 d4 cnt h1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_srow & A_srow & R_drow & A_drow & R_w & R_lc & R_uc & R_n4 & R_d4 & R_cnt & R_h1); idtac.
(* [comment removed for export] *)
Lemma wr_1a3f4 : forall (fx : FPState) regs m ,
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 22 = Z_to_bv 64 cnt ->
  getr regs 23 = Z_to_bv 64 n4 ->
  getr regs 24 = Z_to_bv 64 srow ->
  getr regs 25 = Z_to_bv 64 drow ->
  getr regs 26 = Z_to_bv 64 d4 ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a4f0) m rom) (@mkst fx regs' (Z_to_bv 64 0x2ac48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 107776
    /\ getr regs' 10 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 bufs2
    /\ getr regs' 12 = Z_to_bv 64 n4
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 255; KRange (EVar 39) 0 255; KRange (EVar 40) 4 20000; KRange (EVar 41) 4 2500; KRange (EVar 42) 1 19999; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z; 108192%Z; 175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wr_1a404 : forall (fx : FPState) regs m ,
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 22 = Z_to_bv 64 cnt ->
  getr regs 23 = Z_to_bv 64 n4 ->
  getr regs 24 = Z_to_bv 64 srow ->
  getr regs 25 = Z_to_bv 64 drow ->
  getr regs 26 = Z_to_bv 64 d4 ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a500) m rom) (@mkst fx regs' (Z_to_bv 64 0x2ac48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 107792
    /\ getr regs' 10 = Z_to_bv 64 bufs2
    /\ getr regs' 11 = Z_to_bv 64 srow
    /\ getr regs' 12 = Z_to_bv 64 n4
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 255; KRange (EVar 39) 0 255; KRange (EVar 40) 4 20000; KRange (EVar 41) 4 2500; KRange (EVar 42) 1 19999; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z; 108192%Z; 175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wr_1a414 : forall (fx : FPState) regs m ,
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 22 = Z_to_bv 64 cnt ->
  getr regs 23 = Z_to_bv 64 n4 ->
  getr regs 24 = Z_to_bv 64 srow ->
  getr regs 25 = Z_to_bv 64 drow ->
  getr regs 26 = Z_to_bv 64 d4 ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a510) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a6a0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 107824
    /\ getr regs' 10 = Z_to_bv 64 drow
    /\ getr regs' 11 = Z_to_bv 64 w
    /\ getr regs' 12 = Z_to_bv 64 bufs1
    /\ getr regs' 13 = Z_to_bv 64 bufs2
    /\ getr regs' 14 = Z_to_bv 64 lc
    /\ getr regs' 15 = Z_to_bv 64 uc
    /\ getr regs' 16 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 255; KRange (EVar 39) 0 255; KRange (EVar 40) 4 20000; KRange (EVar 41) 4 2500; KRange (EVar 42) 1 19999; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z; 108192%Z; 175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wr_1a434 : forall (fx : FPState) regs m ,
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 22 = Z_to_bv 64 cnt ->
  getr regs 23 = Z_to_bv 64 n4 ->
  getr regs 24 = Z_to_bv 64 srow ->
  getr regs 25 = Z_to_bv 64 drow ->
  getr regs 26 = Z_to_bv 64 d4 ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a530) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a53c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 22 = Z_to_bv 64 (cnt - 1)
    /\ getr regs' 24 = Z_to_bv 64 (srow + n4)
    /\ getr regs' 25 = Z_to_bv 64 (drow + d4)
    /\ regs_agree (fun r => In r [22; 24; 25]%list) regs regs'.
Proof using All.
  intros fx regs m  H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 255; KRange (EVar 39) 0 255; KRange (EVar 40) 4 20000; KRange (EVar 41) 4 2500; KRange (EVar 42) 1 19999; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z; 108192%Z; 175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wr_1a440f : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 0) = false ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 22 = Z_to_bv 64 (cnt - 1) ->
  getr regs 23 = Z_to_bv 64 n4 ->
  getr regs 24 = Z_to_bv 64 (srow + n4) ->
  getr regs 25 = Z_to_bv 64 (drow + d4) ->
  getr regs 26 = Z_to_bv 64 d4 ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a53c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a540) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 255; KRange (EVar 39) 0 255; KRange (EVar 40) 4 20000; KRange (EVar 41) 4 2500; KRange (EVar 42) 1 19999; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z; 108192%Z; 175176%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wr_1a440t : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 0) = true ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 22 = Z_to_bv 64 (cnt - 1) ->
  getr regs 23 = Z_to_bv 64 n4 ->
  getr regs 24 = Z_to_bv 64 (srow + n4) ->
  getr regs 25 = Z_to_bv 64 (drow + d4) ->
  getr regs 26 = Z_to_bv 64 d4 ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a53c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a4f0) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; srow; drow; w; lc; uc; n4; d4; cnt; h1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 255; KRange (EVar 39) 0 255; KRange (EVar 40) 4 20000; KRange (EVar 41) 4 2500; KRange (EVar 42) 1 19999; KRange (EVar 43) 0 19999]) by (ex_know regs).
  dl_run 400%nat [107760%Z; 107840%Z; 108192%Z; 175176%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End WR.

(* [comment removed for export] *)
Definition wl_hyps (s bufs1 bufs2 w lc uc n4 h1 wpld datad : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (4 <= n4 <= 20000)%Z /\ (0 <= h1 <= 19999)%Z /\ (1 <= wpld <= 625)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (0 <= h1 * wpld < 2 ^ 29)%Z.
Section WL.
Variable rom : word -> option byte.
Variables (s bufs1 bufs2 w lc uc n4 h1 wpld datad : Z).
Hypothesis HYP : wl_hyps s bufs1 bufs2 w lc uc n4 h1 wpld datad.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_w & R_lc & R_uc & R_n4 & R_h1 & R_wpld & R_datad & A_datad & Hrow); idtac.
(* [comment removed for export] *)
Lemma wl_1a444 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datad) ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 21 = Z_to_bv 64 bufs2 ->
  getr regs 23 = Z_to_bv 64 n4 ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a540) m rom) (@mkst fx regs' (Z_to_bv 64 0x2ac48) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 107856
    /\ getr regs' 10 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 bufs2
    /\ getr regs' 12 = Z_to_bv 64 n4
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H8 H9 H18 H19 H21 H23 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; w; lc; uc; n4; h1; wpld; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; w; lc; uc; n4; h1; wpld; datad]) m [KWord (SA (EVar 32) (-112)) 8 (EVar 40); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KRange (EVar 38) 4 20000; KRange (EVar 39) 0 19999; KRange (EVar 40) 1 625; KRange (EVar 41) 4096 140737488355328; KAlign (EVar 41) 4]) by (ex_know regs).
  dl_run 400%nat [107932%Z; 108084%Z; 175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wl_1a454 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datad) ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a550) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a568) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 2
    /\ getr regs' 22 = Z_to_bv 64 (datad + (4 * (h1 * wpld)))
    /\ regs_agree (fun r => In r [10; 22]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 H2 H8 H9 H18 H19 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; w; lc; uc; n4; h1; wpld; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; w; lc; uc; n4; h1; wpld; datad]) m [KWord (SA (EVar 32) (-112)) 8 (EVar 40); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KRange (EVar 38) 4 20000; KRange (EVar 39) 0 19999; KRange (EVar 40) 1 625; KRange (EVar 41) 4096 140737488355328; KAlign (EVar 41) 4]) by (ex_know regs).
  dl_run 400%nat [107932%Z; 108084%Z; 175176%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wl_1a46cf : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 w) (Z_to_bv 64 2) = false ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datad) ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 2 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 22 = Z_to_bv 64 (datad + (4 * (h1 * wpld))) ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a568) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a59c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 (bufs1 + 1)
    /\ getr regs' 13 = Z_to_bv 64 (w - 1)
    /\ getr regs' 14 = Z_to_bv 64 18446744071562067968
    /\ getr regs' 19 = Z_to_bv 64 (w - 1)
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 19]%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H8 H9 H10 H18 H19 H22 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; w; lc; uc; n4; h1; wpld; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; w; lc; uc; n4; h1; wpld; datad]) m [KWord (SA (EVar 32) (-112)) 8 (EVar 40); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KRange (EVar 38) 4 20000; KRange (EVar 39) 0 19999; KRange (EVar 40) 1 625; KRange (EVar 41) 4096 140737488355328; KAlign (EVar 41) 4]) by (ex_know regs).
  dl_run 400%nat [107932%Z; 108084%Z; 175176%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wl_1a46ct : forall (fx : FPState) regs m ,
  branch_taken BC_LT (Z_to_bv 64 w) (Z_to_bv 64 2) = true ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datad) ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 2 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 19 = Z_to_bv 64 w ->
  getr regs 22 = Z_to_bv 64 (datad + (4 * (h1 * wpld))) ->
  getr regs 27 = Z_to_bv 64 h1 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a568) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a634) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 19 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [19]%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 H2 H8 H9 H10 H18 H19 H22 H27.
  dl_facts.
  ex_entry regs [s; bufs1; bufs2; w; lc; uc; n4; h1; wpld; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; bufs2; w; lc; uc; n4; h1; wpld; datad]) m [KWord (SA (EVar 32) (-112)) 8 (EVar 40); KWord (SA (EVar 32) (-120)) 8 (EVar 41); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 1 20000; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KRange (EVar 38) 4 20000; KRange (EVar 39) 0 19999; KRange (EVar 40) 1 625; KRange (EVar 41) 4096 140737488355328; KAlign (EVar 41) 4]) by (ex_know regs).
  dl_run 400%nat [107932%Z; 108084%Z; 175176%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End WL.

Definition wf_1a4a0_cells_def (bufs1 lrow j w1 lc uc wpl : Z) : list (Z * Z) := [((bytea (bufs1 + j))%Z, 1%Z); ((bytea (bufs1 + j + 1))%Z, 1%Z); ((lrow + (4 * (j / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition wf_hyps (bufs1 lrow j w1 lc uc wpl : Z) : Prop :=
  (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= lrow <= 140737488355328)%Z /\ (lrow mod 4 = 0)%Z /\ (0 <= j <= 19999)%Z /\ (0 <= w1 <= 19999)%Z /\ (0 <= lc <= 255)%Z /\ (0 <= uc <= 255)%Z /\ (0 <= j < w1)%Z /\ (w1 + 1 <= 4 * wpl)%Z.
Section WF.
Variable rom : word -> option byte.
Variables (bufs1 lrow j w1 lc uc wpl : Z).
Hypothesis HYP : wf_hyps bufs1 lrow j w1 lc uc wpl.
Ltac dl_facts := pose proof HYP as (R_bufs1 & A_bufs1 & R_lrow & A_lrow & R_j & R_w1 & R_lc & R_uc & Hj & Hwpl); pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1].
(* [comment removed for export] *)
Lemma wf_1a49cf : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = false ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 (j + 1) ->
  getr regs 11 = Z_to_bv 64 (j + 1) ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a598) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a59c) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H9 H10 H11 H12 H13 H14 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a49ct : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = true ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 (j + 1) ->
  getr regs 11 = Z_to_bv 64 (j + 1) ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a598) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a634) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H9 H10 H11 H12 H13 H14 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a4a0 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j))) 1 = Some bs0 ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a59c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a5ac) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 15 = Z_to_bv 64 (rdv true 1 bs0)
    /\ regs_agree (fun r => In r [15; 16]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 H8 H9 H10 H11 H12 H13 H14 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc; rdv true 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc; rdv true 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a4b0f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LT (getr regs 15) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lrow + (4 * (j / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lrow + (4 * (j / 32)))) 4 = true ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a5ac) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a5cc) m' rom)
    /\ mframe [((lrow + (4 * (j / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 15 = Z_to_bv 64 (lrow + (4 * (j / 32)))
    /\ regs_agree (fun r => In r [5; 15; 17]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H8 H9 H10 H11 H12 H13 H14 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc; rdv true 4 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a4b0t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 15) (Z_to_bv 64 0) = true ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a5ac) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a600) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [16]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H9 H10 H11 H12 H13 H14 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a4d0f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GEU (Z_to_bv 64 lc) (getr regs 16) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs0 ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 15 = Z_to_bv 64 (lrow + (4 * (j / 32))) ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a5cc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a5f0) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 15 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 17 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [5; 15; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 H8 H9 H10 H11 H12 H13 H14 H15 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a4d0t : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (Z_to_bv 64 lc) (getr regs 16) = true ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 15 = Z_to_bv 64 (lrow + (4 * (j / 32))) ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a5cc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a598) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 (j + 1)
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H9 H10 H11 H12 H13 H14 H15 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a4f4f : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 16) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 255 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a5f0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a598) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (j + 1)
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 16 = Z_to_bv 64 255
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 255))
    /\ regs_agree (fun r => In r [10; 11; 16]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H8 H9 H10 H11 H12 H13 H14 H15 H17 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a4f4t : forall (fx : FPState) regs m ,
  branch_taken BC_LTU (getr regs 16) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 15 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 17 = Z_to_bv 64 255 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a5f0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a598) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (j + 1)
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ rdn SEGS m' (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some (word_to_le_bytes 1 (getr regs 16))
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H8 H9 H10 H11 H12 H13 H14 H15 H17 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a504f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_GEU (Z_to_bv 64 uc) (getr regs 16) = false ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a600) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a598) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (j + 1)
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ getr regs' 15 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ regs_agree (fun r => In r [5; 10; 11; 15; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H8 H9 H10 H11 H12 H13 H14 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc; rdv false 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc; rdv false 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [false] [EVar 38] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma wf_1a504t : forall (fx : FPState) regs m ,
  branch_taken BC_GEU (Z_to_bv 64 uc) (getr regs 16) = true ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a600) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a598) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 10 = Z_to_bv 64 (j + 1)
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H8 H9 H10 H11 H12 H13 H14 H18 H22.
  dl_facts.
  ex_entry regs [bufs1; lrow; j; w1; lc; uc] HR.
  assert (HK : know_ok SEGS (ex_env regs [bufs1; lrow; j; w1; lc; uc]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 0 19999; KRange (EVar 35) 0 19999; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255]) by (ex_know regs).
  dl_run 400%nat [107928%Z; 107932%Z; 108084%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation wf_1a4a0_cells := (wf_1a4a0_cells_def bufs1 lrow j w1 lc uc wpl).
Lemma wf_1a4a0_path : forall (fx : FPState) regs m,
  cells_ok SEGS m wf_1a4a0_cells ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 9 = Z_to_bv 64 uc ->
  getr regs 10 = Z_to_bv 64 j ->
  getr regs 11 = Z_to_bv 64 j ->
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) ->
  getr regs 13 = Z_to_bv 64 w1 ->
  getr regs 14 = Z_to_bv 64 18446744071562067968 ->
  getr regs 18 = Z_to_bv 64 lc ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a59c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a598) m' rom)
    /\ mframe wf_1a4a0_cells m m'
    /\ getr regs' 10 = Z_to_bv 64 (j + 1)
    /\ getr regs' 11 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [5; 10; 11; 15; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m CK H8 H9 H10 H11 H12 H13 H14 H18 H22.
  pose proof (mframe_refl wf_1a4a0_cells m) as FK0.
  destruct (cells_ok_read SEGS m m wf_1a4a0_cells (bytea (bufs1 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (wf_1a4a0 fx regs m bs1_0 Rd1_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_15 & AG1).
  assert (FK1 : mframe wf_1a4a0_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold wf_1a4a0_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 15) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (wf_1a4b0t fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe wf_1a4a0_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold wf_1a4a0_cells_def; dl_incl).
    destruct (branch_taken BC_GEU (Z_to_bv 64 uc) (getr r2 16)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (wf_1a504t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_11 & AG3).
      assert (FK3 : mframe wf_1a4a0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold wf_1a4a0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 wf_1a4a0_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (wf_1a504f fx r2 m2 bs3_0 B2 Rd3_0 (cells_ok_sok SEGS m m2 wf_1a4a0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_11 & E3_15 & AG3).
      assert (FK3 : mframe wf_1a4a0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold wf_1a4a0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 wf_1a4a0_cells (lrow + (4 * (j / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (wf_1a4b0f fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 wf_1a4a0_cells (lrow + (4 * (j / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_15 & AG2).
    assert (FK2 : mframe wf_1a4a0_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold wf_1a4a0_cells_def; dl_incl).
    destruct (branch_taken BC_GEU (Z_to_bv 64 lc) (getr r2 16)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (wf_1a4d0t fx r2 m2  B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_11 & AG3).
      assert (FK3 : mframe wf_1a4a0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold wf_1a4a0_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (cells_ok_read SEGS m m2 wf_1a4a0_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK2) ltac:(dl_in0)) as [bs3_0 Rd3_0].
      destruct (wf_1a4d0f fx r2 m2 bs3_0 B2 Rd3_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_15 & E3_17 & AG3).
      assert (FK3 : mframe wf_1a4a0_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold wf_1a4a0_cells_def; dl_incl).
      destruct (branch_taken BC_LTU (getr r3 16) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (wf_1a4f4t fx r3 m3  B3 (cells_ok_sok SEGS m m3 wf_1a4a0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_10 & E4_11 & SV4_0 & AG4).
        assert (FK4 : mframe wf_1a4a0_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold wf_1a4a0_cells_def; dl_incl).
        exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
        repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (wf_1a4f4f fx r3 m3  B3 (cells_ok_sok SEGS m m3 wf_1a4a0_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK3) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_10 & E4_11 & E4_16 & SV4_0 & AG4).
        assert (FK4 : mframe wf_1a4a0_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold wf_1a4a0_cells_def; dl_incl).
        exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact FK4|].
        repeat split; [dl_get .. | ra_chain].
Qed.

End WF.

Definition we_1a538_cells_def (s bufs1 lrow w1 : Z) : list (Z * Z) := [((bytea (bufs1 + w1))%Z, 1%Z); ((lrow + (4 * (w1 / 32)))%Z, 4%Z)].
(* [comment removed for export] *)
Definition we_hyps (s bufs1 lrow w1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= lrow <= 140737488355328)%Z /\ (lrow mod 4 = 0)%Z /\ (0 <= w1 <= 19999)%Z.
Section WE.
Variable rom : word -> option byte.
Variables (s bufs1 lrow w1 : Z).
Hypothesis HYP : we_hyps s bufs1 lrow w1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_bufs1 & A_bufs1 & R_lrow & A_lrow & R_w1); pose proof (dl_div_bounds w1 32 ltac:(lia) ltac:(lia)) as DW.
(* [comment removed for export] *)
Lemma we_1a538 : forall (fx : FPState) regs m (bs0 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + w1))) 1 = Some bs0 ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 19 = Z_to_bv 64 w1 ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a634) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a640) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 8 = Z_to_bv 64 (bufs1 + w1)
    /\ getr regs' 10 = Z_to_bv 64 (rdv true 1 bs0)
    /\ regs_agree (fun r => In r [8; 10]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 R0 H2 H8 H19 H22.
  dl_facts.
  ex_entry regs [s; bufs1; lrow; w1; rdv true 1 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; lrow; w1; rdv true 1 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999]) by (ex_know regs).
  dl_run 400%nat [108132%Z] (SCR [] [EVar 36] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma we_1a544f : forall (fx : FPState) regs m (bs0 : list byte),
  branch_taken BC_LT (getr regs 10) (Z_to_bv 64 0) = false ->
  rdn SEGS m (Z_to_bv 64 (lrow + (4 * (w1 / 32)))) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (lrow + (4 * (w1 / 32)))) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 (bufs1 + w1) ->
  getr regs 19 = Z_to_bv 64 w1 ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a640) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a664) m' rom)
    /\ mframe [((lrow + (4 * (w1 / 32)))%Z, 4%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 (lrow + (4 * (w1 / 32)))
    /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 BT R0 S0 H2 H8 H19 H22.
  dl_facts.
  ex_entry regs [s; bufs1; lrow; w1; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; lrow; w1; rdv true 4 bs0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999]) by (ex_know regs).
  dl_run 400%nat [108132%Z] (SCR [false] [EVar 36] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma we_1a544t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 10) (Z_to_bv 64 0) = true ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 (bufs1 + w1) ->
  getr regs 19 = Z_to_bv 64 w1 ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a640) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a664) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H2 H8 H19 H22.
  dl_facts.
  ex_entry regs [s; bufs1; lrow; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; lrow; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999]) by (ex_know regs).
  dl_run 400%nat [108132%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma we_1a568_e : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte) (bs5 : list byte) (bs6 : list byte) (bs7 : list byte) (bs8 : list byte) (bs9 : list byte) (bs10 : list byte) (bs11 : list byte) (bs12 : list byte),
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
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a664) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a69c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 (rdv false 8 bs0)
    /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 8 = Z_to_bv 64 (rdv false 8 bs1)
    /\ getr regs' 9 = Z_to_bv 64 (rdv false 8 bs2)
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
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 bs5 bs6 bs7 bs8 bs9 bs10 bs11 bs12 R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H2.
  dl_facts.
  ex_entry regs [s; bufs1; lrow; w1; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5; rdv false 8 bs6; rdv false 8 bs7; rdv false 8 bs8; rdv false 8 bs9; rdv false 8 bs10; rdv false 8 bs11; rdv false 8 bs12] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bufs1; lrow; w1; rdv false 8 bs0; rdv false 8 bs1; rdv false 8 bs2; rdv false 8 bs3; rdv false 8 bs4; rdv false 8 bs5; rdv false 8 bs6; rdv false 8 bs7; rdv false 8 bs8; rdv false 8 bs9; rdv false 8 bs10; rdv false 8 bs11; rdv false 8 bs12]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 0 19999]) by (ex_know regs).
  dl_run 400%nat [108132%Z] (SCR [] [EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation we_1a538_cells := (we_1a538_cells_def s bufs1 lrow w1).
Lemma we_1a538_path : forall (fx : FPState) regs m,
  cells_ok SEGS m we_1a538_cells ->
  getr regs 2 = Z_to_bv 64 (s - 128) ->
  getr regs 8 = Z_to_bv 64 bufs1 ->
  getr regs 19 = Z_to_bv 64 w1 ->
  getr regs 22 = Z_to_bv 64 lrow ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a634) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a664) m' rom)
    /\ mframe we_1a538_cells m m'
    /\ getr regs' 8 = Z_to_bv 64 (bufs1 + w1)
    /\ regs_agree (fun r => In r [8; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m CK H2 H8 H19 H22.
  pose proof (mframe_refl we_1a538_cells m) as FK0.
  destruct (cells_ok_read SEGS m m we_1a538_cells (bytea (bufs1 + w1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (we_1a538 fx regs m bs1_0 Rd1_0 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_8 & E1_10 & AG1).
  assert (FK1 : mframe we_1a538_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold we_1a538_cells_def; dl_incl).
  destruct (branch_taken BC_LT (getr r1 10) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (we_1a544t fx r1 m1  B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe we_1a538_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold we_1a538_cells_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (cells_ok_read SEGS m m1 we_1a538_cells (lrow + (4 * (w1 / 32)))%Z 4%Z wr_readable_img CK (proj1 FK1) ltac:(dl_in0)) as [bs2_0 Rd2_0].
    destruct (we_1a544f fx r1 m1 bs2_0 B1 Rd2_0 (cells_ok_sok SEGS m m1 we_1a538_cells (lrow + (4 * (w1 / 32)))%Z 4%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & E2_10 & AG2).
    assert (FK2 : mframe we_1a538_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold we_1a538_cells_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
    repeat split; [dl_get .. | ra_chain].
Qed.

End WE.
