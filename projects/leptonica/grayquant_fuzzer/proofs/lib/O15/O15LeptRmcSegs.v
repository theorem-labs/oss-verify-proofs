(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec LeptExecX DitherLib LeptRmcLib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Section Segs.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Definition RMCF (m : word -> option byte) (s : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 (getr regs 1)))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).

(* [comment removed for export] *)
Definition RMC0 (m : word -> option byte) (s w h : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (RMCF m s regs)
    (Z_to_bv 64 (s - 120)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 124)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 128)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 120)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 124)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
    (Z_to_bv 64 (s - 128)) (word_to_le_bytes 4 (Z_to_bv 64 8)).

(* [comment removed for export] *)
Lemma rmc_S0 : forall (fx : FPState) regs m (s pixs cm w h n : Z),
  (256 <= s < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (1 <= cm)%Z -> (cm + 24 < 2 ^ 63)%Z ->
  (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (1 <= n <= 256)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 256 = true ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 cm) -> rdn SEGS m (Z_to_bv 64 (pixs + 0)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (cm + 16)) 4 = Some (Z_to_le_bytes 4 n) ->
  (pixs + 64 <= s - 256 \/ s <= pixs)%Z -> (cm + 24 <= s - 256 \/ s <= cm)%Z ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19278) m rom) (@mkst fx regs' (Z_to_bv 64 0x189f0) (RMC0 m s w h regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 256) /\ getr regs' 1 = Z_to_bv 64 0x19428 /\ getr regs' 10 = Z_to_bv 64 cm
    /\ getr regs' 11 = Z_to_bv 64 (s - 152) /\ getr regs' 12 = Z_to_bv 64 (s - 160) /\ getr regs' 13 = Z_to_bv 64 (s - 168) /\ getr regs' 14 = Z_to_bv 64 (s - 176)
    /\ getr regs' 19 = Z_to_bv 64 pixs /\ getr regs' 20 = Z_to_bv 64 n /\ getr regs' 21 = Z_to_bv 64 1 /\ getr regs' 22 = Z_to_bv 64 256 /\ getr regs' 23 = Z_to_bv 64 cm
    /\ regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 19; 20; 21; 22; 23]%list) regs regs'.
Proof.
  intros fx regs m s pixs cm w h n Hs Hpixs Hpixs63 Hcm Hcm63 Hw Hh Hn SOK Ccm Cw Ch Cd Cn APp APc H2 H10 H11.
  ex_entry regs [s; pixs; cm; w; h; n] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; cm; w; h; n]) m
                 [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63); KRange (EVar 34) 1 (2 ^ 63); KRange (EVar 35) 0 (2 ^ 31 - 1);
                  KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 1 256; KWr (SA (EVar 32) (-256)) 256;
                  KWord (SA (EVar 33) 48) 8 (EVar 34); KWord (SA (EVar 33) 0) 4 (EVar 35); KWord (SA (EVar 33) 4) 4 (EVar 36); KWord (SA (EVar 33) 8) 4 (ELit 8);
                  KWord (SA (EVar 34) 16) 4 (EVar 37);
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-256)) 256; KDisj (SA (EVar 34) 0) 24 (SA (EVar 32) (-256)) 256]).
  { ex_know regs. }
  ex_run 300%nat [0x189f0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold RMC0, RMCF; ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_S0z : forall (fx : FPState) regs m (s pixs : Z),
  (256 <= s < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 256 = true ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  (pixs + 64 <= s - 256 \/ s <= pixs)%Z ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pixs ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19278) m rom) (@mkst fx regs' (Z_to_bv 64 0x1728c) (RMCF m s regs) rom)
    /\ getr regs' 11 = Z_to_bv 64 (pixs + 20) /\ getr regs' 12 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [11; 12]%list) regs regs'.
Proof.
  intros fx regs m s pixs Hs Hpixs Hpixs63 SOK Ccm APp H2 H10.
  ex_entry regs [s; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs]) m
                 [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63); KWr (SA (EVar 32) (-256)) 256;
                  KWord (SA (EVar 33) 48) 8 (ELit 0); KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-256)) 256]).
  { ex_know regs. }
  ex_run 300%nat [0x1728c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold RMCF; ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Definition RMC1 (m : word -> option byte) (s datas wpls : Z) : word -> option byte :=
  wbytes (wbytes m (Z_to_bv 64 (s - 232)) (word_to_le_bytes 8 (Z_to_bv 64 datas))) (Z_to_bv 64 (s - 240)) (word_to_le_bytes 8 (Z_to_bv 64 wpls)).

Lemma rmc_S1 : forall (fx : FPState) regs m (s pixs w h datas wpls : Z),
  (256 <= s < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  (0 <= datas < 2 ^ 63)%Z -> (0 <= wpls < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 256 = true ->
  rdn SEGS m (Z_to_bv 64 (pixs + 56)) 8 = Some (Z_to_le_bytes 8 datas) -> rdn SEGS m (Z_to_bv 64 (pixs + 16)) 4 = Some (Z_to_le_bytes 4 wpls) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h) ->
  (pixs + 64 <= s - 256 \/ s <= pixs)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 10 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 pixs -> getr regs 21 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19428) m rom) (@mkst fx regs' (Z_to_bv 64 0x166a0) (RMC1 m s datas wpls) rom)
    /\ getr regs' 1 = Z_to_bv 64 0x198cc /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 8
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m s pixs w h datas wpls Hs Hpixs Hpixs63 Hw Hh Hdatas Hwpls SOK Cdata Cwpl Cw Ch APp H2 H10 H19 H21.
  ex_entry regs [s; pixs; w; h; datas; wpls] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; datas; wpls]) m
                 [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63); KRange (EVar 34) 0 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1);
                  KRange (EVar 37) 0 (2 ^ 31 - 1); KWr (SA (EVar 32) (-256)) 256;
                  KWord (SA (EVar 33) 56) 8 (EVar 36); KWord (SA (EVar 33) 16) 4 (EVar 37);
                  KWord (SA (EVar 32) (-120)) 4 (EVar 34); KWord (SA (EVar 32) (-124)) 4 (EVar 35);
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-256)) 256]).
  { ex_know regs. }
  ex_run 300%nat [0x166a0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold RMC1; ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Definition RMC2 (m : word -> option byte) (s pixd datad : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 datad))) (Z_to_bv 64 (s - 248)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)).

Lemma rmc_S2 : forall (fx : FPState) regs m (s pixs pixd datad wpld : Z),
  (256 <= s < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (1 <= pixd)%Z -> (pixd + 64 < 2 ^ 63)%Z ->
  (0 <= datad < 2 ^ 63)%Z -> (0 <= wpld < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 256 = true -> store_ok SEGS m (Z_to_bv 64 pixd) 64 = true ->
  rdn SEGS m (Z_to_bv 64 (pixs + 24)) 8 = Some (Z_to_le_bytes 8 0) -> rdn SEGS m (Z_to_bv 64 (pixs + 32)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS m (Z_to_bv 64 (pixd + 56)) 8 = Some (Z_to_le_bytes 8 datad) -> rdn SEGS m (Z_to_bv 64 (pixd + 16)) 4 = Some (Z_to_le_bytes 4 wpld) ->
  (pixs + 64 <= s - 256 \/ s <= pixs)%Z -> (pixd + 64 <= s - 256 \/ s <= pixd)%Z -> (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 19 = Z_to_bv 64 pixs -> getr regs 22 = Z_to_bv 64 256 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x198cc) m rom) (@mkst fx regs' (Z_to_bv 64 0x20ea0) (RMC2 m s pixd datad) rom)
    /\ getr regs' 1 = Z_to_bv 64 0x19910 /\ getr regs' 10 = Z_to_bv 64 256 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 21 = Z_to_bv 64 wpld
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 21]%list) regs regs'.
Proof.
  intros fx regs m s pixs pixd datad wpld Hs Hpixs Hpixs63 Hpixd Hpixd63 Hdatad Hwpld SOK SOKd Cres Cfmt Cdata Cwpl APp APd APpd H2 H10 H19 H22.
  ex_entry regs [s; pixs; pixd; datad; wpld] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; pixd; datad; wpld]) m
                 [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63); KRange (EVar 34) 1 (2 ^ 63); KRange (EVar 36) 0 (2 ^ 31 - 1);
                  KWr (SA (EVar 32) (-256)) 256; KWr (SA (EVar 34) 0) 64;
                  KWord (SA (EVar 33) 24) 8 (ELit 0); KWord (SA (EVar 33) 32) 4 (ELit 0);
                  KWord (SA (EVar 34) 56) 8 (EVar 35); KWord (SA (EVar 34) 16) 4 (EVar 36);
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-256)) 256; KDisj (SA (EVar 34) 0) 64 (SA (EVar 32) (-256)) 256;
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 34) 0) 64]).
  { ex_know regs. }
  ex_run 300%nat [0x20ea0%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold RMC2; ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_S4 : forall (fx : FPState) regs m (s h datas wpls datad wpld : Z),
  (256 <= s < 2 ^ 63)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= datas < 2 ^ 63)%Z -> (0 <= wpls < 2 ^ 31)%Z -> (0 <= datad < 2 ^ 63)%Z -> (0 <= wpld < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (s - 240)) 8 = Some (Z_to_le_bytes 8 wpls) -> rdn SEGS m (Z_to_bv 64 (s - 232)) 8 = Some (Z_to_le_bytes 8 datas) ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 21 = Z_to_bv 64 wpld ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19994) m rom) (@mkst fx regs' (Z_to_bv 64 0x19a14) m rom)
    /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 (4 * wpls) /\ getr regs' 15 = Z_to_bv 64 3 /\ getr regs' 5 = Z_to_bv 64 1
    /\ getr regs' 7 = Z_to_bv 64 4 /\ getr regs' 31 = Z_to_bv 64 8 /\ getr regs' 21 = Z_to_bv 64 (4 * wpld)
    /\ getr regs' 23 = Z_to_bv 64 datas /\ getr regs' 20 = Z_to_bv 64 datas /\ getr regs' 22 = Z_to_bv 64 datad /\ getr regs' 24 = Z_to_bv 64 datad
    /\ regs_agree (fun r => In r [5; 7; 11; 13; 14; 15; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros fx regs m s h datas wpls datad wpld Hs Hh Hdatas Hwpls Hdatad Hwpld Ch Cdd Cws Cds H2 H21.
  ex_entry regs [s; h; datas; wpls; datad; wpld] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h; datas; wpls; datad; wpld]) m
                 [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 31 - 1);
                  KWord (SA (EVar 32) (-124)) 4 (EVar 33); KWord (SA (EVar 32) (-184)) 8 (EVar 36); KWord (SA (EVar 32) (-240)) 8 (EVar 35);
                  KWord (SA (EVar 32) (-232)) 8 (EVar 34)]).
  { ex_know regs. }
  ex_run 100%nat [0x19a14%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_RH : forall (big : bool) (fx : FPState) regs m (s w wpls datas srow drow : Z),
  (256 <= s < 2 ^ 63)%Z -> (1 <= w <= 20000)%Z -> (0 <= wpls < 2 ^ 31)%Z -> (0 <= datas < 2 ^ 63)%Z -> (0 <= srow < 2 ^ 63)%Z -> (0 <= drow < 2 ^ 63)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 8) -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 240)) 8 = Some (Z_to_le_bytes 8 wpls) -> rdn SEGS m (Z_to_bv 64 (s - 232)) 8 = Some (Z_to_le_bytes 8 datas) ->
  (if big then 4 <= w else w < 4)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 15 = Z_to_bv 64 3 -> getr regs 7 = Z_to_bv 64 4 -> getr regs 31 = Z_to_bv 64 8 ->
  getr regs 23 = Z_to_bv 64 srow -> getr regs 22 = Z_to_bv 64 drow ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19a14) m rom) (@mkst fx regs' (Z_to_bv 64 (if big then 0x19bfc else 0x19fbc)) m rom)
    /\ getr regs' 25 = Z_to_bv 64 w
    /\ (if big then getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 srow /\ getr regs' 8 = Z_to_bv 64 drow else getr regs' 18 = Z_to_bv 64 0)
    /\ regs_agree (fun r => In r [8; 9; 12; 16; 18; 25]%list) regs regs'.
Proof.
  intros big fx regs m s w wpls datas srow drow Hs Hw Hwpls Hdatas Hsrow Hdrow Cd Cw Cws Cds Hbig H2 H15 H7 H31 H23 H22.
  ex_entry regs [s; w; wpls; datas; srow; drow] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; wpls; datas; srow; drow]) m
                 [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 1 20000;
                  KWord (SA (EVar 32) (-128)) 4 (ELit 8); KWord (SA (EVar 32) (-120)) 4 (EVar 33); KWord (SA (EVar 32) (-240)) 8 (EVar 34);
                  KWord (SA (EVar 32) (-232)) 8 (EVar 35)]).
  { ex_know regs. }
  destruct big.
  - ex_run 100%nat [0x19bfc%Z; 0x19fbc%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 100%nat [0x19bfc%Z; 0x19fbc%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_B4 : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s g src dst j w sw : Z) (bs3 bs2 bs1 bs0 : list byte),
  (4096 <= s - 256)%Z -> (s <= 2 ^ 47)%Z -> (4096 <= g < 2 ^ 47)%Z -> (4096 <= src < 2 ^ 47)%Z -> (4096 <= dst < 2 ^ 47)%Z ->
  (0 <= j)%Z -> (j + 4 <= w <= 20000)%Z -> (0 <= sw < 2 ^ 32)%Z ->
  rdn SEGS m (Z_to_bv 64 src) 4 = Some (Z_to_le_bytes 4 sw) -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (g + lut_o3 sw)) 4 = Some bs3 -> rdn SEGS m (Z_to_bv 64 (g + lut_o2 sw)) 4 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (g + lut_o1 sw)) 4 = Some bs1 -> rdn SEGS m (Z_to_bv 64 (g + lut_o0 sw)) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 dst) 4 = true -> (dst + 4 <= s - 256 \/ s <= dst)%Z ->
  (if more then j + 7 < w else w <= j + 7)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 10 = Z_to_bv 64 g -> getr regs 12 = Z_to_bv 64 src -> getr regs 8 = Z_to_bv 64 dst -> getr regs 9 = Z_to_bv 64 j ->
  exists regs' (v : word),
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19bfc) m rom)
                (@mkst fx regs' (Z_to_bv 64 (if more then 0x19bfc else 0x19fbc)) (wbytes m (Z_to_bv 64 dst) (word_to_le_bytes 4 v)) rom)
    /\ getr regs' 9 = Z_to_bv 64 (j + 4) /\ getr regs' 18 = Z_to_bv 64 (j + 4) /\ getr regs' 12 = Z_to_bv 64 (src + 4) /\ getr regs' 8 = Z_to_bv 64 (dst + 4)
    /\ getr regs' 25 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [8; 9; 12; 18; 25; 26; 27]%list) regs regs'.
Proof.
  intros more fx regs m s g src dst j w sw bs3 bs2 bs1 bs0 Hs Hs47 Hg Hsrc Hdst Hj Hw Hsw Csw Cw C3 C2 C1 C0 SOKd APd Hmore H2 H10 H12 H8 H9.
  ex_entry regs [s; g; src; dst; j; w; sw; rdv true 4 bs3; rdv true 4 bs2; rdv true 4 bs1; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; g; src; dst; j; w; sw; rdv true 4 bs3; rdv true 4 bs2; rdv true 4 bs1; rdv true 4 bs0]) m
                 [KRange (EVar 32) 4352 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 35) 4096 (2 ^ 47);
                  KRange (EVar 36) 0 19996; KRange (EVar 37) 4 20000; KRange (EVar 38) 0 (2 ^ 32 - 1);
                  KWord (SA (EVar 34) 0) 4 (EVar 38); KWord (SA (EVar 32) (-120)) 4 (EVar 37); KWr (SA (EVar 35) 0) 4;
                  KDisj (SA (EVar 35) 0) 4 (SA (EVar 32) (-256)) 256]).
  { ex_know regs. }
  assert (BR : forall t : bool, (if t then j + 7 < w else w <= j + 7)%Z ->
               branch_taken BC_LT (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 7)))) (ext_val true 0 4 (Z_to_bv 64 w)) = t).
  { intros t Ht. rewrite w_addw, zbv_addw_small by lia. destruct t; ex_br. }
  destruct more.
  - ex_runN 39%nat 80%nat [0x19bfc%Z; 0x19fbc%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    + exact (BR true Hmore).
    + exx_named (g + lut_o0 sw)%Z C0 ltac:(rewrite lut_a0 by lia; rewrite zbv_addi; f_equal; lia).
    + exx_named (g + lut_o1 sw)%Z C1 ltac:(rewrite lut_a12 by lia; rewrite zbv_addi; f_equal; unfold lut_o1; lia).
    + exx_named (g + lut_o2 sw)%Z C2 ltac:(rewrite lut_a12 by lia; rewrite zbv_addi; f_equal; unfold lut_o2; lia).
    + exx_named (g + lut_o3 sw)%Z C3 ltac:(rewrite lut_a3 by lia; rewrite zbv_addi; f_equal; lia).
    + exists R'. eexists. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_runN 39%nat 80%nat [0x19bfc%Z; 0x19fbc%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    + exact (BR false Hmore).
    + exx_named (g + lut_o0 sw)%Z C0 ltac:(rewrite lut_a0 by lia; rewrite zbv_addi; f_equal; lia).
    + exx_named (g + lut_o1 sw)%Z C1 ltac:(rewrite lut_a12 by lia; rewrite zbv_addi; f_equal; unfold lut_o1; lia).
    + exx_named (g + lut_o2 sw)%Z C2 ltac:(rewrite lut_a12 by lia; rewrite zbv_addi; f_equal; unfold lut_o2; lia).
    + exx_named (g + lut_o3 sw)%Z C3 ltac:(rewrite lut_a3 by lia; rewrite zbv_addi; f_equal; lia).
    + exists R'. eexists. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_TH : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (j w : Z),
  (0 <= j <= 20000)%Z -> (1 <= w <= 20000)%Z -> (if more then j < w else w <= j)%Z ->
  getr regs 18 = Z_to_bv 64 j -> getr regs 25 = Z_to_bv 64 w ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19fbc) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x19fc0 else 0x199f0)) m rom)
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof.
  intros more fx regs m j w Hj Hw Hmore H18 H25.
  ex_entry regs [j; w] HR.
  assert (HK : know_ok SEGS (ex_env regs [j; w]) m [KRange (EVar 32) 0 20000; KRange (EVar 33) 1 20000]) by (ex_know regs).
  destruct more.
  - ex_run 10%nat [0x19fc0%Z; 0x199f0%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms | ex_agree HR HR'].
  - ex_run 10%nat [0x19fc0%Z; 0x199f0%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms | ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Definition RMCT (m : word -> option byte) (s drow j : Z) (v : word) : word -> option byte :=
  wbytes (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 v)) (Z_to_bv 64 (bytea (drow + j))) (word_to_le_bytes 1 v).

Lemma rmc_TB : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s g srow drow j w : Z) (bsb bsl : list byte),
  (4096 <= s - 256)%Z -> (s <= 2 ^ 47)%Z -> (4096 <= g < 2 ^ 47)%Z -> (4096 <= srow < 2 ^ 47)%Z -> (4096 <= drow < 2 ^ 47)%Z ->
  (0 <= j < w)%Z -> (w <= 20000)%Z ->
  rdn SEGS m (Z_to_bv 64 (bytea (srow + j))) 1 = Some bsb -> rdn SEGS m (Z_to_bv 64 (g + 4 * rdv false 1 bsb)) 4 = Some bsl ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 4 = true -> store_ok SEGS m (Z_to_bv 64 (bytea (drow + j))) 1 = true ->
  (bytea (drow + j) + 1 <= s - 256 \/ s <= bytea (drow + j))%Z ->
  (if more then j + 1 < w else w <= j + 1)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 10 = Z_to_bv 64 g -> getr regs 20 = Z_to_bv 64 srow -> getr regs 24 = Z_to_bv 64 drow -> getr regs 18 = Z_to_bv 64 j ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19fc0) m rom)
                (@mkst fx regs' (Z_to_bv 64 (if more then 0x19fc0 else 0x199f0)) (RMCT m s drow j (Z_to_bv 64 (rdv true 4 bsl))) rom)
    /\ getr regs' 18 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [8; 12; 18]%list) regs regs'.
Proof.
  intros more fx regs m s g srow drow j w bsb bsl Hs Hs47 Hg Hsrow Hdrow Hj Hw Cb Cl Cw SOKs SOKd APd Hmore H2 H10 H20 H24 H18.
  ex_entry regs [s; g; srow; drow; j; w; rdv false 1 bsb; rdv true 4 bsl] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; g; srow; drow; j; w; rdv false 1 bsb; rdv true 4 bsl]) m
                 [KRange (EVar 32) 4352 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 35) 4096 (2 ^ 47);
                  KRange (EVar 36) 0 19999; KRange (EVar 37) 1 20000;
                  KWord (SA (EVar 32) (-120)) 4 (EVar 37); KWr (SA (EVar 32) (-112)) 4]).
  { ex_know regs. }
  pose proof (rdv_byte_range bsb (rdn_length _ _ _ _ _ Cb)) as Rb. pose proof (bytea_near (drow + j)) as Nd. pose proof (bytea_near (srow + j)) as Ns.
  assert (XD : alu64 ALU_XOR (Z_to_bv 64 (drow + j)) (Z_to_bv 64 3) = Z_to_bv 64 (bytea (drow + j))) by (apply dl_xor3; lia).
  assert (XS : alu64 ALU_XOR (Z_to_bv 64 (srow + j)) (Z_to_bv 64 3) = Z_to_bv 64 (bytea (srow + j))) by (apply dl_xor3; lia).
  assert (XL : alu64 ALU_ADD (Z_to_bv 64 g) (mul_div M_MUL (Z_to_bv 64 4) (Z_to_bv 64 (rdv false 1 bsb))) = Z_to_bv 64 (g + 4 * rdv false 1 bsb))
    by (rewrite m_mul, zbv_mul, alu_add, zbv_add; reflexivity).
  assert (MEM : forall (fx0 : FPState) ms R pc E log,
            msteps SEGS ms (@mkst fx0 R pc (mem_denot E m log) rom) ->
            mem_denot E m log = RMCT m s drow j (Z_to_bv 64 (rdv true 4 bsl)) ->
            msteps SEGS ms (@mkst fx0 R pc (RMCT m s drow j (Z_to_bv 64 (rdv true 4 bsl))) rom)) by (intros fx0 ms R pc E log X <-; exact X).
  destruct more.
  - ex_runN 38%nat 80%nat [0x19fc0%Z; 0x199f0%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    + rewrite XD. rewrite !u_Z2bv by lia. clear - Hs Hs47 Nd APd Hdrow Hj Hw. lia.
    + rewrite XD, zbv_addi, Z.add_0_r. exact SOKd.
    + exx_named (g + 4 * rdv false 1 bsb)%Z Cl ltac:(rewrite XL, zbv_addi; f_equal; lia).
    + rewrite XL. rewrite !u_Z2bv by lia. lia.
    + exx_named (bytea (srow + j)) Cb ltac:(rewrite XS, zbv_addi; f_equal; lia).
    + exists R'. split.
      * apply MEM with (1 := Hms). unfold RMCT. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity] | | reflexivity].
        ex_unfoldE. unfold adenot. cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite ?H24, ?H18, ?ex_ptr_val, XD, zbv_addi. f_equal. lia.
      * repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_runN 38%nat 80%nat [0x19fc0%Z; 0x199f0%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    + rewrite XD. rewrite !u_Z2bv by lia. clear - Hs Hs47 Nd APd Hdrow Hj Hw. lia.
    + rewrite XD, zbv_addi, Z.add_0_r. exact SOKd.
    + exx_named (g + 4 * rdv false 1 bsb)%Z Cl ltac:(rewrite XL, zbv_addi; f_equal; lia).
    + rewrite XL. rewrite !u_Z2bv by lia. lia.
    + exx_named (bytea (srow + j)) Cb ltac:(rewrite XS, zbv_addi; f_equal; lia).
    + exists R'. split.
      * apply MEM with (1 := Hms). unfold RMCT. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity] | | reflexivity].
        ex_unfoldE. unfold adenot. cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite ?H24, ?H18, ?ex_ptr_val, XD, zbv_addi. f_equal. lia.
      * repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_RL : forall (last : bool) (fx : FPState) regs (m : word -> option byte) (s i h srow drow sstep dstep : Z),
  (256 <= s < 2 ^ 63)%Z -> (0 <= i < h)%Z -> (h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h) ->
  (if last then h <= i + 1 else i + 1 < h)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 11 = Z_to_bv 64 i -> getr regs 21 = Z_to_bv 64 dstep -> getr regs 13 = Z_to_bv 64 sstep ->
  getr regs 23 = Z_to_bv 64 srow -> getr regs 20 = Z_to_bv 64 srow -> getr regs 22 = Z_to_bv 64 drow -> getr regs 24 = Z_to_bv 64 drow ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x199f0) m rom) (@mkst fx regs' (Z_to_bv 64 (if last then 0x1a038 else 0x19a14)) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 23 = Z_to_bv 64 (srow + sstep) /\ getr regs' 20 = Z_to_bv 64 (srow + sstep)
    /\ getr regs' 22 = Z_to_bv 64 (drow + dstep) /\ getr regs' 24 = Z_to_bv 64 (drow + dstep)
    /\ regs_agree (fun r => In r [11; 12; 14; 19; 20; 22; 23; 24]%list) regs regs'.
Proof.
  intros last fx regs m s i h srow drow sstep dstep Hs Hi Hh Ch Hlast H2 H11 H21 H13 H23 H20 H22 H24.
  ex_entry regs [s; i; h; srow; drow; sstep; dstep] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; h; srow; drow; sstep; dstep]) m
                 [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 0 (2 ^ 31 - 2); KRange (EVar 34) 1 (2 ^ 31 - 1); KWord (SA (EVar 32) (-124)) 4 (EVar 34)]) by (ex_know regs).
  destruct last.
  - ex_run 20%nat [0x19a14%Z; 0x1a038%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 20%nat [0x19a14%Z; 0x1a038%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_S5 : forall (fx : FPState) regs (m : word -> option byte) (g : Z),
  (1 <= g < 2 ^ 63)%Z -> getr regs 10 = Z_to_bv 64 g ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a038) m rom) (@mkst fx regs' (Z_to_bv 64 0x20fd8) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x197b4 /\ getr regs' 10 = Z_to_bv 64 g
    /\ regs_agree (fun r => In r [1]%list) regs regs'.
Proof.
  intros fx regs m g Hg H10.
  ex_entry regs [g] HR.
  assert (HK : know_ok SEGS (ex_env regs [g]) m [KRange (EVar 32) 1 (2 ^ 63)]) by (ex_know regs).
  ex_run 10%nat [0x20fd8%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)

Lemma rmc_S6 : forall (fx : FPState) regs (m : word -> option byte) (s p : Z),
  (256 <= s < 2 ^ 63)%Z -> (0 <= p < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 p) -> getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x197b4) m rom) (@mkst fx regs' (Z_to_bv 64 0x20fd8) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1a09c /\ getr regs' 10 = Z_to_bv 64 p
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s p Hs Hp Cp H2.
  ex_entry regs [s; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p]) m [KRange (EVar 32) 256 (2 ^ 63); KWord (SA (EVar 32) (-152)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 10%nat [0x20fd8%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma rmc_S7 : forall (fx : FPState) regs (m : word -> option byte) (s p : Z),
  (256 <= s < 2 ^ 63)%Z -> (0 <= p < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 p) -> getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a09c) m rom) (@mkst fx regs' (Z_to_bv 64 0x20fd8) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1a0a4 /\ getr regs' 10 = Z_to_bv 64 p
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s p Hs Hp Cp H2.
  ex_entry regs [s; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p]) m [KRange (EVar 32) 256 (2 ^ 63); KWord (SA (EVar 32) (-160)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 10%nat [0x20fd8%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma rmc_S8 : forall (fx : FPState) regs (m : word -> option byte) (s p : Z),
  (256 <= s < 2 ^ 63)%Z -> (0 <= p < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 p) -> getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a0a4) m rom) (@mkst fx regs' (Z_to_bv 64 0x20fd8) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1a0ac /\ getr regs' 10 = Z_to_bv 64 p
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s p Hs Hp Cp H2.
  ex_entry regs [s; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p]) m [KRange (EVar 32) 256 (2 ^ 63); KWord (SA (EVar 32) (-168)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 10%nat [0x20fd8%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma rmc_S9 : forall (fx : FPState) regs (m : word -> option byte) (s p : Z),
  (256 <= s < 2 ^ 63)%Z -> (0 <= p < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 p) -> getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a0ac) m rom) (@mkst fx regs' (Z_to_bv 64 0x20fd8) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1a0b4 /\ getr regs' 10 = Z_to_bv 64 p
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s p Hs Hp Cp H2.
  ex_entry regs [s; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p]) m [KRange (EVar 32) 256 (2 ^ 63); KWord (SA (EVar 32) (-176)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 10%nat [0x20fd8%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_SE : forall (fx : FPState) regs (m : word -> option byte) (s pixd z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 : Z),
  (256 <= s < 2 ^ 63)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
  (0 <= z1 < 2 ^ 64)%Z -> (0 <= z8 < 2 ^ 64)%Z -> (0 <= z9 < 2 ^ 64)%Z -> (0 <= z18 < 2 ^ 64)%Z -> (0 <= z19 < 2 ^ 64)%Z -> (0 <= z20 < 2 ^ 64)%Z ->
  (0 <= z21 < 2 ^ 64)%Z -> (0 <= z22 < 2 ^ 64)%Z -> (0 <= z23 < 2 ^ 64)%Z -> (0 <= z24 < 2 ^ 64)%Z -> (0 <= z25 < 2 ^ 64)%Z -> (0 <= z26 < 2 ^ 64)%Z ->
  (0 <= z27 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 pixd) ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (Z_to_le_bytes 8 z1) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (Z_to_le_bytes 8 z8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (Z_to_le_bytes 8 z9) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 z18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 z19) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 z20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 z21) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 z22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 z23) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 z24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 z25) -> rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (Z_to_le_bytes 8 z26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 z27) ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a0b4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a034) m rom)
    /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = Z_to_bv 64 z1 /\ getr regs' 8 = Z_to_bv 64 z8
    /\ getr regs' 9 = Z_to_bv 64 z9 /\ getr regs' 18 = Z_to_bv 64 z18 /\ getr regs' 19 = Z_to_bv 64 z19 /\ getr regs' 20 = Z_to_bv 64 z20
    /\ getr regs' 21 = Z_to_bv 64 z21 /\ getr regs' 22 = Z_to_bv 64 z22 /\ getr regs' 23 = Z_to_bv 64 z23 /\ getr regs' 24 = Z_to_bv 64 z24
    /\ getr regs' 25 = Z_to_bv 64 z25 /\ getr regs' 26 = Z_to_bv 64 z26 /\ getr regs' 27 = Z_to_bv 64 z27
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros fx regs m s pixd z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 Hs Hpixd R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
         Cp C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 H2.
  ex_entry regs [s; pixd; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27]) m
                 [KRange (EVar 32) 256 (2 ^ 63); KWord (SA (EVar 32) (-248)) 8 (EVar 33);
                  KWord (SA (EVar 32) (-8)) 8 (EVar 34); KWord (SA (EVar 32) (-16)) 8 (EVar 35); KWord (SA (EVar 32) (-24)) 8 (EVar 36);
                  KWord (SA (EVar 32) (-32)) 8 (EVar 37); KWord (SA (EVar 32) (-40)) 8 (EVar 38); KWord (SA (EVar 32) (-48)) 8 (EVar 39);
                  KWord (SA (EVar 32) (-56)) 8 (EVar 40); KWord (SA (EVar 32) (-64)) 8 (EVar 41); KWord (SA (EVar 32) (-72)) 8 (EVar 42);
                  KWord (SA (EVar 32) (-80)) 8 (EVar 43); KWord (SA (EVar 32) (-88)) 8 (EVar 44); KWord (SA (EVar 32) (-96)) 8 (EVar 45);
                  KWord (SA (EVar 32) (-104)) 8 (EVar 46)]) by (ex_know regs).
  ex_run 50%nat [0x1a034%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

End Segs.
