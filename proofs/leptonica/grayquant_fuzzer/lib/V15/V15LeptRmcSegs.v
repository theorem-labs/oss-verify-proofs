(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec LeptExecX DitherLib LeptRmcLib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Definition RMC0n (m : word -> option byte) (s w h n : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (RMC0 m s w h regs) (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (Z_to_bv 64 n)).

Lemma rmc_S0 : forall (fx : FPState) regs m (s pixs cm w h n : Z),
  (272 <= s < 2 ^ 63)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z -> (1 <= cm)%Z -> (cm + 24 < 2 ^ 63)%Z -> (cm mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (1 <= n <= 256)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 272)) 272 = true ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 cm) -> rdn SEGS m (Z_to_bv 64 (pixs + 0)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (cm + 16)) 4 = Some (Z_to_le_bytes 4 n) ->
  (pixs + 64 <= s - 272 \/ s <= pixs)%Z -> (cm + 24 <= s - 272 \/ s <= cm)%Z ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19f1c) m rom) (@mkst fx regs' (Z_to_bv 64 0x193f8) (RMC0n m s w h n regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 272) /\ getr regs' 1 = Z_to_bv 64 0x1a0dc /\ getr regs' 10 = Z_to_bv 64 cm
    /\ getr regs' 11 = Z_to_bv 64 (s - 152) /\ getr regs' 12 = Z_to_bv 64 (s - 160) /\ getr regs' 13 = Z_to_bv 64 (s - 168) /\ getr regs' 14 = Z_to_bv 64 (s - 176)
    /\ getr regs' 19 = Z_to_bv 64 pixs /\ getr regs' 20 = Z_to_bv 64 cm /\ getr regs' 22 = Z_to_bv 64 256 /\ getr regs' 23 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 22; 23]%list) regs regs'.
Proof.
  intros fx regs m s pixs cm w h n Hs Hs16 Hpixs Hpixs63 ALp Hcm Hcm63 ALc Hw Hh Hn SOK Ccm Cw Ch Cd Cn APp APc H2 H10 H11.
  ex_entry regs [s; pixs; cm; w; h; n] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; cm; w; h; n]) m
                 [KRange (EVar 32) 272 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 33) 1 (2 ^ 63); KAlign (EVar 33) 8; KRange (EVar 34) 1 (2 ^ 63); KAlign (EVar 34) 8;
                  KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 1 256; KWr (SA (EVar 32) (-272)) 272;
                  KWord (SA (EVar 33) 48) 8 (EVar 34); KWord (SA (EVar 33) 0) 4 (EVar 35); KWord (SA (EVar 33) 4) 4 (EVar 36); KWord (SA (EVar 33) 8) 4 (ELit 8);
                  KWord (SA (EVar 34) 16) 4 (EVar 37);
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-272)) 272; KDisj (SA (EVar 34) 0) 24 (SA (EVar 32) (-272)) 272]).
  { ex_know regs. }
  ex_run 300%nat [0x193f8%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold RMC0n, RMC0, RMCF; ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_S0z : forall (fx : FPState) regs m (s pixs : Z),
  (272 <= s < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 272)) 272 = true ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  (pixs + 64 <= s - 272 \/ s <= pixs)%Z ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pixs ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19f1c) m rom) (@mkst fx regs' (Z_to_bv 64 0x179d0) (RMCF m s regs) rom)
    /\ getr regs' 11 = Z_to_bv 64 (pixs + 20) /\ getr regs' 12 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [11; 12]%list) regs regs'.
Proof.
  intros fx regs m s pixs Hs Hpixs Hpixs63 ALp SOK Ccm APp H2 H10.
  ex_entry regs [s; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs]) m
                 [KRange (EVar 32) 272 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63); KAlign (EVar 33) 8; KWr (SA (EVar 32) (-272)) 272;
                  KWord (SA (EVar 33) 48) 8 (ELit 0); KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-272)) 272]).
  { ex_know regs. }
  ex_run 300%nat [0x179d0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold RMCF; ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Definition RMC1 (m : word -> option byte) (s datas : Z) : word -> option byte :=
  wbytes m (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 datas)).

Lemma rmc_S1 : forall (fx : FPState) regs m (s pixs w h datas wpls : Z),
  (272 <= s < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  (0 <= datas < 2 ^ 63)%Z -> (0 <= wpls < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 272)) 272 = true ->
  rdn SEGS m (Z_to_bv 64 (pixs + 56)) 8 = Some (Z_to_le_bytes 8 datas) -> rdn SEGS m (Z_to_bv 64 (pixs + 16)) 4 = Some (Z_to_le_bytes 4 wpls) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h) ->
  (pixs + 64 <= s - 272 \/ s <= pixs)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 272) -> getr regs 10 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 pixs -> getr regs 23 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a0dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x16b48) (RMC1 m s datas) rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1a84c /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 8
    /\ getr regs' 18 = Z_to_bv 64 wpls
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
Proof.
  intros fx regs m s pixs w h datas wpls Hs Hpixs Hpixs63 ALp Hw Hh Hdatas Hwpls SOK Cdata Cwpl Cw Ch APp H2 H10 H19 H23.
  ex_entry regs [s; pixs; w; h; datas; wpls] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; datas; wpls]) m
                 [KRange (EVar 32) 272 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63); KAlign (EVar 33) 8; KRange (EVar 34) 0 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1);
                  KRange (EVar 37) 0 (2 ^ 31 - 1); KWr (SA (EVar 32) (-272)) 272;
                  KWord (SA (EVar 33) 56) 8 (EVar 36); KWord (SA (EVar 33) 16) 4 (EVar 37);
                  KWord (SA (EVar 32) (-120)) 4 (EVar 34); KWord (SA (EVar 32) (-124)) 4 (EVar 35);
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-272)) 272]).
  { ex_know regs. }
  ex_run 300%nat [0x16b48%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold RMC1; ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Definition RMC2 (m : word -> option byte) (s wpls pixd datad wpld : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 256)) (word_to_le_bytes 8 (Z_to_bv 64 wpls)))
    (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (Z_to_bv 64 datad))) (Z_to_bv 64 (s - 264)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
    (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 wpld)).

Lemma rmc_S2 : forall (fx : FPState) regs m (s pixs pixd datad wpls wpld : Z),
  (272 <= s < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z -> (1 <= pixd)%Z -> (pixd + 64 < 2 ^ 63)%Z -> (pixd mod 8 = 0)%Z ->
  (0 <= datad < 2 ^ 63)%Z -> (0 <= wpls < 2 ^ 31)%Z -> (0 <= wpld < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 272)) 272 = true -> store_ok SEGS m (Z_to_bv 64 pixd) 64 = true ->
  rdn SEGS m (Z_to_bv 64 (pixs + 24)) 8 = Some (Z_to_le_bytes 8 0) -> rdn SEGS m (Z_to_bv 64 (pixs + 32)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS m (Z_to_bv 64 (pixd + 56)) 8 = Some (Z_to_le_bytes 8 datad) -> rdn SEGS m (Z_to_bv 64 (pixd + 16)) 4 = Some (Z_to_le_bytes 4 wpld) ->
  (pixs + 64 <= s - 272 \/ s <= pixs)%Z -> (pixd + 64 <= s - 272 \/ s <= pixd)%Z -> (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 272) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 19 = Z_to_bv 64 pixs -> getr regs 22 = Z_to_bv 64 256 ->
  getr regs 18 = Z_to_bv 64 wpls ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a84c) m rom) (@mkst fx regs' (Z_to_bv 64 0x2891c) (RMC2 m s wpls pixd datad wpld) rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1a894 /\ getr regs' 10 = Z_to_bv 64 256 /\ getr regs' 11 = Z_to_bv 64 4
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 20]%list) regs regs'.
Proof.
  intros fx regs m s pixs pixd datad wpls wpld Hs Hpixs Hpixs63 ALp Hpixd Hpixd63 ALd Hdatad Hwpls Hwpld SOK SOKd Cres Cfmt Cdata Cwpl APp APd APpd H2 H10 H19 H22 H18.
  ex_entry regs [s; pixs; pixd; datad; wpls; wpld] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; pixd; datad; wpls; wpld]) m
                 [KRange (EVar 32) 272 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63); KAlign (EVar 33) 8; KRange (EVar 34) 1 (2 ^ 63); KAlign (EVar 34) 8;
                  KRange (EVar 37) 0 (2 ^ 31 - 1);
                  KWr (SA (EVar 32) (-272)) 272; KWr (SA (EVar 34) 0) 64;
                  KWord (SA (EVar 33) 24) 8 (ELit 0); KWord (SA (EVar 33) 32) 4 (ELit 0);
                  KWord (SA (EVar 34) 56) 8 (EVar 35); KWord (SA (EVar 34) 16) 4 (EVar 37);
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-272)) 272; KDisj (SA (EVar 34) 0) 64 (SA (EVar 32) (-272)) 272;
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 34) 0) 64]).
  { ex_know regs. }
  ex_run 300%nat [0x2891c%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold RMC2; ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_S4 : forall (fx : FPState) regs m (s g h datas wpls datad : Z),
  (272 <= s < 2 ^ 63)%Z -> (1 <= g < 2 ^ 63)%Z -> (1 <= h < 2 ^ 31)%Z -> (1 <= datas < 2 ^ 63)%Z -> (datas mod 4 = 0)%Z -> (0 <= wpls < 2 ^ 31)%Z ->
  (1 <= datad < 2 ^ 63)%Z -> (datad mod 4 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 192)) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 wpls) -> rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 datas) ->
  getr regs 2 = Z_to_bv 64 (s - 272) -> getr regs 10 = Z_to_bv 64 g ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a9cc) m rom)
                (@mkst fx regs' (Z_to_bv 64 0x1aa44) (wbytes m (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (Z_to_bv 64 0x3ffffff))) rom)
    /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 29 = Z_to_bv 64 wpls
    /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 1 /\ getr regs' 16 = Z_to_bv 64 (2 ^ 64 - 1 - g) /\ getr regs' 17 = Z_to_bv 64 3
    /\ getr regs' 31 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 28; 29; 31]%list) regs regs'.
Proof.
  intros fx regs m s g h datas wpls datad Hs Hg Hh Hdatas ALs Hwpls Hdatad ALd SOK Ch Cdd Cws Cds H2 H10.
  ex_entry regs [s; g; h; datas; wpls; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; g; h; datas; wpls; datad]) m
                 [KRange (EVar 32) 272 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 1 (2 ^ 63); KAlign (EVar 35) 4;
                  KRange (EVar 37) 1 (2 ^ 63); KAlign (EVar 37) 4; KWr (SA (EVar 32) (-192)) 8;
                  KWord (SA (EVar 32) (-124)) 4 (EVar 34); KWord (SA (EVar 32) (-200)) 8 (EVar 37); KWord (SA (EVar 32) (-256)) 8 (EVar 36);
                  KWord (SA (EVar 32) (-184)) 8 (EVar 35)]).
  { ex_know regs. }
  ex_run 100%nat [0x1aa44%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  all: rewrite ?zbv_snez, ?zbv_not by lia; try reflexivity; try (apply bv_eq; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma rmc_RH : forall (big : bool) (fx : FPState) regs m (s w i wpls wpld datas datad : Z),
  (272 <= s < 2 ^ 63)%Z -> (1 <= w <= 20000)%Z -> (0 <= i <= 20000)%Z -> (0 <= wpls <= 5000)%Z -> (0 <= wpld <= 5000)%Z ->
  (0 <= wpls * i <= 20000000)%Z -> (0 <= wpld * i <= 20000000)%Z ->
  (4096 <= datas)%Z -> (datas + 4 * (wpls * i) < 2 ^ 47)%Z -> (4096 <= datad)%Z -> (datad + 4 * (wpld * i) < 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 8) -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 wpld) -> rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 datas) ->
  rdn SEGS m (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 datad) ->
  (if big then 4 <= w else w < 4)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 272) -> getr regs 13 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (wpls * i) -> getr regs 12 = Z_to_bv 64 (wpld * i) ->
  getr regs 29 = Z_to_bv 64 wpls -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 3 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1aa44) m rom) (@mkst fx regs' (Z_to_bv 64 (if big then 0x1adac else 0x1b45c)) m rom)
    /\ getr regs' 5 = Z_to_bv 64 w /\ getr regs' 7 = Z_to_bv 64 0 /\ getr regs' 28 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 (2 ^ 31)
    /\ getr regs' 27 = Z_to_bv 64 (datas + 4 * (wpls * i)) /\ getr regs' 23 = Z_to_bv 64 (datas + 4 * (wpls * i))
    /\ getr regs' 25 = Z_to_bv 64 (datad + 4 * (wpld * i)) /\ getr regs' 24 = Z_to_bv 64 (datad + 4 * (wpld * i))
    /\ regs_agree (fun r => In r [1; 5; 7; 23; 24; 25; 26; 27; 28]%list) regs regs'.
Proof.
  intros big fx regs m s w i wpls wpld datas datad Hs Hw Hi Hwpls Hwpld Psi Pdi Hdatas Hsrow Hdatad Hdrow Cd Cw Cwd Cds Cdd Hbig H2 H13 H11 H12 H29 H14 H15 H17.
  set (psi := (wpls * i)%Z) in *. set (pdi := (wpld * i)%Z) in *.
  ex_entry regs [s; w; i; wpls; wpld; datas; datad; psi; pdi] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; i; wpls; wpld; datas; datad; psi; pdi]) m
                 [KRange (EVar 32) 272 (2 ^ 63); KRange (EVar 33) 1 20000; KRange (EVar 34) 0 20000; KRange (EVar 35) 0 5000; KRange (EVar 36) 0 5000;
                  KRange (EVar 37) 4096 (2 ^ 47); KRange (EVar 38) 4096 (2 ^ 47); KRange (EVar 39) 0 20000000; KRange (EVar 40) 0 20000000;
                  KWord (SA (EVar 32) (-128)) 4 (ELit 8); KWord (SA (EVar 32) (-120)) 4 (EVar 33); KWord (SA (EVar 32) (-208)) 8 (EVar 36);
                  KWord (SA (EVar 32) (-184)) 8 (EVar 37); KWord (SA (EVar 32) (-200)) 8 (EVar 38)]).
  { ex_know regs. }
  assert (Es : (i * wpls = psi)%Z) by (unfold psi; ring). assert (Ed : (i * wpld = pdi)%Z) by (unfold pdi; ring).
  (* [comment removed for export] *)
  assert (G1 : forall a b p, (a * b = p)%Z -> (0 <= a < 2 ^ 31)%Z -> (0 <= b < 2 ^ 31)%Z -> (0 <= p < 2 ^ 31)%Z ->
               branch_taken BC_NE (sext 64 (mul_div M_MUL (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b)))) (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b)) = false).
  { intros a b p E Ha Hb Hp. rewrite w_mulw, m_mul. rewrite zbv_mul. rewrite zbv_mulw_small by lia. rewrite E. cbn [branch_taken]. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. }
  assert (G2 : forall a b p base, (a * b = p)%Z -> (0 <= p < 2 ^ 31)%Z -> (0 <= base)%Z -> (base + 4 * p < 2 ^ 63)%Z ->
               branch_taken BC_EQ
                 (alu64 ALU_XOR (alu64 ALU_XOR
                    (alu64 ALU_SLTU (alu64 ALU_ADD (Z_to_bv 64 base) (mul_div M_MUL (Z_to_bv 64 4)
                        (sext 64 (alu32 ALU_ADD (low32 (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b))) (low32 (Z_to_bv 64 0)))))) (Z_to_bv 64 base))
                    (alu64 ALU_SLT (sext 64 (alu32 ALU_ADD (low32 (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b))) (low32 (Z_to_bv 64 0)))) (Z_to_bv 64 0)))
                    (Z_to_bv 64 1)) (Z_to_bv 64 0) = false).
  { intros a b p base E Hp Hb Hbp. rewrite !m_mul. rewrite !zbv_mul. rewrite E. rewrite !w_addw. rewrite !zbv_addw_small by lia. rewrite zbv_mul, alu_add, zbv_add.
    rewrite alu_sltu. rewrite zbv_sltu_ge by lia. rewrite alu_slt. rewrite v_slt_Z by lia. replace (p + 0 <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  destruct big.
  - ex_run 200%nat [0x1adac%Z; 0x1b45c%Z] (SCR [false; false; false; false; false] [] []) HR HK R' HR' Hms.
    + exact (G2 i wpld pdi datad Ed ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (G1 i wpld pdi Ed ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (G2 i wpls psi datas Es ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (G1 i wpls psi Es ltac:(lia) ltac:(lia) ltac:(lia)).
    + exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?zbv_mul, ?zbv_add; f_equal; lia.
  - ex_run 200%nat [0x1adac%Z; 0x1b45c%Z] (SCR [false; false; false; false; true] [] []) HR HK R' HR' Hms.
    + exact (G2 i wpld pdi datad Ed ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (G1 i wpld pdi Ed ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (G2 i wpls psi datas Es ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (G1 i wpls psi Es ltac:(lia) ltac:(lia) ltac:(lia)).
    + exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?zbv_mul, ?zbv_add; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma rmc_B4 : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s g ng srow drow j w sw : Z) (bs3 bs2 bs1 bs0 : list byte),
  ng = (2 ^ 64 - 1 - g)%Z ->
  (4096 <= s - 272)%Z -> (s <= 2 ^ 47)%Z -> (4096 <= g)%Z -> (g + 1024 <= 2 ^ 47)%Z -> (g mod 4 = 0)%Z -> (4096 <= srow)%Z -> (srow + 20000 < 2 ^ 47)%Z -> (srow mod 4 = 0)%Z ->
  (4096 <= drow)%Z -> (drow + 20000 < 2 ^ 47)%Z -> (drow mod 4 = 0)%Z -> (0 <= j)%Z -> (j mod 4 = 0)%Z -> (j + 4 <= w <= 20000)%Z -> (0 <= sw < 2 ^ 32)%Z ->
  rdn SEGS m (Z_to_bv 64 (srow + j + 0)) 4 = Some (Z_to_le_bytes 4 sw) -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (g + lut_o3 sw)) 4 = Some bs3 -> rdn SEGS m (Z_to_bv 64 (g + lut_u 40 sw)) 4 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (g + lut_u 48 sw)) 4 = Some bs1 -> rdn SEGS m (Z_to_bv 64 (g + lut_o0 sw)) 4 = Some bs0 ->
  store_ok SEGS m (Z_to_bv 64 (drow + j)) 4 = true -> (drow + j + 4 <= s - 272 \/ s <= drow + j)%Z ->
  (if more then j + 7 < w else w <= j + 7)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 272) -> getr regs 10 = Z_to_bv 64 g -> getr regs 16 = Z_to_bv 64 ng ->
  getr regs 27 = Z_to_bv 64 srow -> getr regs 23 = Z_to_bv 64 srow -> getr regs 25 = Z_to_bv 64 drow -> getr regs 24 = Z_to_bv 64 drow ->
  getr regs 7 = Z_to_bv 64 j -> getr regs 28 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 31 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 1 -> getr regs 1 = Z_to_bv 64 (2 ^ 31) ->
  exists regs' (v : word),
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1adac) m rom)
                (@mkst fx regs' (Z_to_bv 64 (if more then 0x1adac else 0x1b45c)) (wbytes m (Z_to_bv 64 (drow + j)) (word_to_le_bytes 4 v)) rom)
    /\ getr regs' 7 = Z_to_bv 64 (j + 4) /\ getr regs' 28 = Z_to_bv 64 (j + 4) /\ getr regs' 5 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [5; 7; 8; 9; 18; 28; 29; 30]%list) regs regs'.
Proof.
  intros more fx regs m s g ng srow drow j w sw bs3 bs2 bs1 bs0 Eng Hs Hs47 Hg Hg47 ALg Hsrow Hsrow47 ALs Hdrow Hdrow47 ALd Hj ALj Hw Hsw Csw Cw C3 C2 C1 C0 SOKd APd Hmore
         H2 H10 H16 H27 H23 H25 H24 H7 H28 H14 H15 H31 H21 H1.
  destruct (lut_o_range sw Hsw) as (O0 & _ & _ & O3). pose proof (lut_u_range 40 sw) as U2. pose proof (lut_u_range 48 sw) as U1.
  assert (Hng : (2 ^ 64 - 1 - 2 ^ 47 <= ng <= 2 ^ 64 - 1 - 4096)%Z) by lia.
  ex_entry regs [s; g; ng; srow; drow; j; w; sw; rdv true 4 bs3; rdv true 4 bs2; rdv true 4 bs1; rdv true 4 bs0] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; g; ng; srow; drow; j; w; sw; rdv true 4 bs3; rdv true 4 bs2; rdv true 4 bs1; rdv true 4 bs0]) m
                 [KRange (EVar 32) 4368 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 4; KRange (EVar 34) (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1 - 4096);
                  KRange (EVar 35) 4096 (2 ^ 47); KRange (EVar 36) 4096 (2 ^ 47); KAlign (EVar 35) 4; KAlign (EVar 36) 4;
                  KRange (EVar 37) 0 19996; KAlign (EVar 37) 4; KRange (EVar 38) 4 20000; KRange (EVar 39) 0 (2 ^ 32 - 1);
                  KWord (SA (EAlu ALU_ADD (EVar 35) (EVar 37)) 0) 4 (EVar 39); KWord (SA (EVar 32) (-120)) 4 (EVar 38)]).
  { ex_know regs. apply (exx_kword_sum SEGS _ m _ _ _ srow j 0 sw 4); [reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | cbn; lia | lia | exact Csw]. }
  assert (A3 : alu64 ALU_ADD (Z_to_bv 64 g) (mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (ext_val false 0 4 (Z_to_bv 64 sw))) (low32 (Z_to_bv 64 24)))))
               = Z_to_bv 64 (g + lut_o3 sw)) by (apply lut_a3; lia).
  assert (X2 : mul_div M_MUL (Z_to_bv 64 4) (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 1099511627776) (ext_val false 0 4 (Z_to_bv 64 sw))) (Z_to_bv 64 56)) = Z_to_bv 64 (lut_u 40 sw))
    by (exact (lut_au_off sw 40 Hsw ltac:(lia))).
  assert (X1 : mul_div M_MUL (Z_to_bv 64 4) (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 281474976710656) (ext_val false 0 4 (Z_to_bv 64 sw))) (Z_to_bv 64 56)) = Z_to_bv 64 (lut_u 48 sw))
    by (exact (lut_au_off sw 48 Hsw ltac:(lia))).
  assert (BR : forall t : bool, (if t then j + 7 < w else w <= j + 7)%Z ->
               branch_taken BC_LT (sext 64 (alu32 ALU_ADD (low32 (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 4))))) (low32 (Z_to_bv 64 3))))
                 (ext_val true 0 4 (Z_to_bv 64 w)) = t).
  { intros t Ht. rewrite !w_addw. rewrite zbv_addw_small by lia. rewrite zbv_addw_small by lia. destruct t; ex_br. }
  destruct more.
  - ex_runN 40%nat 200%nat [0x1adac%Z; 0x1b45c%Z] (SCR [false; false; false; false; false; false; true] [] []) HR HK R' HR' Hms.
    + exact (BR true Hmore).
    + rewrite Z.add_0_r. exact SOKd.
    + exx_named (g + lut_o0 sw)%Z C0 ltac:(rewrite lut_a0 by lia; rewrite zbv_addi; f_equal; lia).
    + exx_named (g + lut_u 48 sw)%Z C1 ltac:(rewrite X1, alu_add, zbv_add, zbv_addi; f_equal; lia).
    + rewrite X1, alu_add, zbv_add. rewrite !u_Z2bv by lia. lia.
    + exx_named (g + lut_u 40 sw)%Z C2 ltac:(rewrite X2, alu_add, zbv_add, zbv_addi; f_equal; lia).
    + rewrite X2, alu_add, zbv_add. rewrite !u_Z2bv by lia. lia.
    + exx_named (g + lut_o3 sw)%Z C3 ltac:(rewrite A3; rewrite zbv_addi; f_equal; lia).
    + rewrite X1. ex_br.
    + rewrite X2. ex_br.
    + rewrite A3. rewrite (alu_sltu (Z_to_bv 64 0) (Z_to_bv 64 g)), (alu_sltu (Z_to_bv 64 (g + lut_o3 sw)) (Z_to_bv 64 1)). rewrite zbv_snez by lia. rewrite (zbv_sltu_ge (g + lut_o3 sw) 1) by lia. reflexivity.
    + rewrite A3. ex_br.
    + exists R'. eexists. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_runN 40%nat 200%nat [0x1adac%Z; 0x1b45c%Z] (SCR [false; false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    + exact (BR false Hmore).
    + rewrite Z.add_0_r. exact SOKd.
    + exx_named (g + lut_o0 sw)%Z C0 ltac:(rewrite lut_a0 by lia; rewrite zbv_addi; f_equal; lia).
    + exx_named (g + lut_u 48 sw)%Z C1 ltac:(rewrite X1, alu_add, zbv_add, zbv_addi; f_equal; lia).
    + rewrite X1, alu_add, zbv_add. rewrite !u_Z2bv by lia. lia.
    + exx_named (g + lut_u 40 sw)%Z C2 ltac:(rewrite X2, alu_add, zbv_add, zbv_addi; f_equal; lia).
    + rewrite X2, alu_add, zbv_add. rewrite !u_Z2bv by lia. lia.
    + exx_named (g + lut_o3 sw)%Z C3 ltac:(rewrite A3; rewrite zbv_addi; f_equal; lia).
    + rewrite X1. ex_br.
    + rewrite X2. ex_br.
    + rewrite A3. rewrite (alu_sltu (Z_to_bv 64 0) (Z_to_bv 64 g)), (alu_sltu (Z_to_bv 64 (g + lut_o3 sw)) (Z_to_bv 64 1)). rewrite zbv_snez by lia. rewrite (zbv_sltu_ge (g + lut_o3 sw) 1) by lia. reflexivity.
    + rewrite A3. ex_br.
    + exists R'. eexists. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_TH : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (j w : Z),
  (0 <= j <= 20000)%Z -> (1 <= w <= 20000)%Z -> (if more then j < w else w <= j)%Z ->
  getr regs 28 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 w ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b45c) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x1b460 else 0x1aa28)) m rom)
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof.
  intros more fx regs m j w Hj Hw Hmore H28 H5.
  ex_entry regs [j; w] HR.
  assert (HK : know_ok SEGS (ex_env regs [j; w]) m [KRange (EVar 32) 0 20000; KRange (EVar 33) 1 20000]) by (ex_know regs).
  destruct more.
  - ex_run 10%nat [0x1b460%Z; 0x1aa28%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms | ex_agree HR HR'].
  - ex_run 10%nat [0x1b460%Z; 0x1aa28%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms | ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Definition RMCT (m : word -> option byte) (s drow j : Z) (v : word) : word -> option byte :=
  wbytes (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 v)) (Z_to_bv 64 (bytea (drow + j))) (word_to_le_bytes 1 v).

Lemma rmc_TB : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s g srow drow j w : Z) (bsb bsl : list byte),
  (4096 <= s - 272)%Z -> (s <= 2 ^ 47)%Z -> (4096 <= g)%Z -> (g + 1024 <= 2 ^ 47)%Z -> (g mod 4 = 0)%Z -> (4096 <= srow)%Z -> (srow + 20000 < 2 ^ 47)%Z ->
  (4096 <= drow)%Z -> (drow + 20000 < 2 ^ 47)%Z -> (0 <= j < w)%Z -> (w <= 20000)%Z ->
  rdn SEGS m (Z_to_bv 64 (bytea (srow + j))) 1 = Some bsb -> rdn SEGS m (Z_to_bv 64 (g + 4 * rdv false 1 bsb)) 4 = Some bsl ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 4 = true -> store_ok SEGS m (Z_to_bv 64 (bytea (drow + j))) 1 = true ->
  (bytea (drow + j) + 1 <= s - 272 \/ s <= bytea (drow + j))%Z ->
  (if more then j + 1 < w else w <= j + 1)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 272) -> getr regs 10 = Z_to_bv 64 g -> getr regs 27 = Z_to_bv 64 srow -> getr regs 23 = Z_to_bv 64 srow ->
  getr regs 25 = Z_to_bv 64 drow -> getr regs 24 = Z_to_bv 64 drow -> getr regs 7 = Z_to_bv 64 j ->
  getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 3 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b460) m rom)
                (@mkst fx regs' (Z_to_bv 64 (if more then 0x1b460 else 0x1aa28)) (RMCT m s drow j (Z_to_bv 64 (rdv true 4 bsl))) rom)
    /\ getr regs' 7 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [5; 7; 28; 29]%list) regs regs'.
Proof.
  intros more fx regs m s g srow drow j w bsb bsl Hs Hs47 Hg Hg47 ALg Hsrow Hsrow47 Hdrow Hdrow47 Hj Hw Cb Cl Cw SOKs SOKd APd Hmore H2 H10 H27 H23 H25 H24 H7 H14 H15 H17.
  pose proof (rdv_byte_range bsb (rdn_length _ _ _ _ _ Cb)) as Rb. pose proof (bytea_near (drow + j)) as Nd. pose proof (bytea_near (srow + j)) as Ns.
  ex_entry regs [s; g; srow; drow; j; w; rdv false 1 bsb; rdv true 4 bsl] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; g; srow; drow; j; w; rdv false 1 bsb; rdv true 4 bsl]) m
                 [KRange (EVar 32) 4368 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 4; KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 35) 4096 (2 ^ 47);
                  KRange (EVar 36) 0 19999; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 255;
                  KWord (SA (EVar 32) (-120)) 4 (EVar 37); KWr (SA (EVar 32) (-112)) 4]).
  { ex_know regs. }
  assert (XD : alu64 ALU_XOR (Z_to_bv 64 (drow + j)) (Z_to_bv 64 3) = Z_to_bv 64 (bytea (drow + j))) by (apply dl_xor3; lia).
  assert (XS : alu64 ALU_XOR (Z_to_bv 64 (srow + j)) (Z_to_bv 64 3) = Z_to_bv 64 (bytea (srow + j))) by (apply dl_xor3; lia).
  assert (XL : alu64 ALU_ADD (Z_to_bv 64 g) (mul_div M_MUL (Z_to_bv 64 4) (Z_to_bv 64 (rdv false 1 bsb))) = Z_to_bv 64 (g + 4 * rdv false 1 bsb))
    by (rewrite m_mul, zbv_mul, alu_add, zbv_add; reflexivity).
  assert (MEM : forall (fx0 : FPState) ms R pc E log,
            msteps SEGS ms (@mkst fx0 R pc (mem_denot E m log) rom) ->
            mem_denot E m log = RMCT m s drow j (Z_to_bv 64 (rdv true 4 bsl)) ->
            msteps SEGS ms (@mkst fx0 R pc (RMCT m s drow j (Z_to_bv 64 (rdv true 4 bsl))) rom)) by (intros fx0 ms R pc E log X <-; exact X).
  destruct more.
  - ex_runN 38%nat 80%nat [0x1b460%Z; 0x1aa28%Z] (SCR [true; true; true; true; true] [] []) HR HK R' HR' Hms.
    + rewrite XD. rewrite !u_Z2bv by lia. clear - Hs Hs47 Nd APd Hdrow Hdrow47 Hj Hw. lia.
    + rewrite XD, zbv_addi, Z.add_0_r. exact SOKd.
    + exx_named (g + 4 * rdv false 1 bsb)%Z Cl ltac:(rewrite XL, zbv_addi; f_equal; lia).
    + rewrite XL. rewrite (alu_sltu (Z_to_bv 64 0) (Z_to_bv 64 g)), (alu_sltu (Z_to_bv 64 (g + 4 * rdv false 1 bsb)) (Z_to_bv 64 1)).
      rewrite zbv_snez by lia. rewrite (zbv_sltu_ge (g + 4 * rdv false 1 bsb) 1) by lia. reflexivity.
    + rewrite XL. ex_br.
    + exx_named (bytea (srow + j)) Cb ltac:(rewrite XS, zbv_addi; f_equal; lia).
    + exists R'. split.
      * apply MEM with (1 := Hms). unfold RMCT. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity] | | reflexivity].
        ex_unfoldE. unfold adenot. cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite ?ex_ptr_val, XD, zbv_addi. f_equal. lia.
      * repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_runN 38%nat 80%nat [0x1b460%Z; 0x1aa28%Z] (SCR [true; true; true; true; false] [] []) HR HK R' HR' Hms.
    + rewrite XD. rewrite !u_Z2bv by lia. clear - Hs Hs47 Nd APd Hdrow Hdrow47 Hj Hw. lia.
    + rewrite XD, zbv_addi, Z.add_0_r. exact SOKd.
    + exx_named (g + 4 * rdv false 1 bsb)%Z Cl ltac:(rewrite XL, zbv_addi; f_equal; lia).
    + rewrite XL. rewrite (alu_sltu (Z_to_bv 64 0) (Z_to_bv 64 g)), (alu_sltu (Z_to_bv 64 (g + 4 * rdv false 1 bsb)) (Z_to_bv 64 1)).
      rewrite zbv_snez by lia. rewrite (zbv_sltu_ge (g + 4 * rdv false 1 bsb) 1) by lia. reflexivity.
    + rewrite XL. ex_br.
    + exx_named (bytea (srow + j)) Cb ltac:(rewrite XS, zbv_addi; f_equal; lia).
    + exists R'. split.
      * apply MEM with (1 := Hms). unfold RMCT. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity] | | reflexivity].
        ex_unfoldE. unfold adenot. cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite ?ex_ptr_val, XD, zbv_addi. f_equal. lia.
      * repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_RL : forall (last : bool) (fx : FPState) regs (m : word -> option byte) (s i h wpls wpld psi pdi : Z),
  (272 <= s < 2 ^ 63)%Z -> (0 <= i < h)%Z -> (h <= 20000)%Z -> (0 <= wpls <= 5000)%Z -> (0 <= wpld <= 5000)%Z -> (0 <= psi <= 20000000)%Z -> (0 <= pdi <= 20000000)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 wpls) ->
  (if last then h <= i + 1 else i + 1 < h)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 272) -> getr regs 13 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 psi -> getr regs 12 = Z_to_bv 64 pdi ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1aa28) m rom) (@mkst fx regs' (Z_to_bv 64 (if last then 0x1b540 else 0x1aa44)) m rom)
    /\ getr regs' 13 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 (psi + wpls) /\ getr regs' 12 = Z_to_bv 64 (pdi + wpld) /\ getr regs' 29 = Z_to_bv 64 wpls
    /\ regs_agree (fun r => In r [5; 7; 11; 12; 13; 29]%list) regs regs'.
Proof.
  intros last fx regs m s i h wpls wpld psi pdi Hs Hi Hh Hwpls Hwpld Hpsi Hpdi Ch Cwd Cws Hlast H2 H13 H11 H12.
  ex_entry regs [s; i; h; wpls; wpld; psi; pdi] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; h; wpls; wpld; psi; pdi]) m
                 [KRange (EVar 32) 272 (2 ^ 63); KRange (EVar 33) 0 19999; KRange (EVar 34) 1 20000; KRange (EVar 35) 0 5000; KRange (EVar 36) 0 5000;
                  KRange (EVar 37) 0 20000000; KRange (EVar 38) 0 20000000;
                  KWord (SA (EVar 32) (-124)) 4 (EVar 34); KWord (SA (EVar 32) (-208)) 8 (EVar 36); KWord (SA (EVar 32) (-256)) 8 (EVar 35)]) by (ex_know regs).
  destruct last.
  - ex_run 20%nat [0x1aa44%Z; 0x1b540%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    + rewrite w_addw, zbv_addw_small by lia. ex_br.
    + exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 20%nat [0x1aa44%Z; 0x1b540%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    + rewrite w_addw, zbv_addw_small by lia. ex_br.
    + exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_S5 : forall (fx : FPState) regs (m : word -> option byte) (g : Z),
  (1 <= g < 2 ^ 63)%Z -> getr regs 10 = Z_to_bv 64 g ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b540) m rom) (@mkst fx regs' (Z_to_bv 64 0x28a54) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1a704 /\ getr regs' 10 = Z_to_bv 64 g
    /\ regs_agree (fun r => In r [1]%list) regs regs'.
Proof.
  intros fx regs m g Hg H10.
  ex_entry regs [g] HR.
  assert (HK : know_ok SEGS (ex_env regs [g]) m [KRange (EVar 32) 1 (2 ^ 63)]) by (ex_know regs).
  ex_run 10%nat [0x28a54%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)

Lemma rmc_S6 : forall (fx : FPState) regs (m : word -> option byte) (s p : Z),
  (272 <= s < 2 ^ 63)%Z -> (0 <= p < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 p) -> getr regs 2 = Z_to_bv 64 (s - 272) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a704) m rom) (@mkst fx regs' (Z_to_bv 64 0x28a54) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1b5a4 /\ getr regs' 10 = Z_to_bv 64 p
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s p Hs Hp Cp H2.
  ex_entry regs [s; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p]) m [KRange (EVar 32) 272 (2 ^ 63); KWord (SA (EVar 32) (-152)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 10%nat [0x28a54%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma rmc_S7 : forall (fx : FPState) regs (m : word -> option byte) (s p : Z),
  (272 <= s < 2 ^ 63)%Z -> (0 <= p < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 p) -> getr regs 2 = Z_to_bv 64 (s - 272) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5a4) m rom) (@mkst fx regs' (Z_to_bv 64 0x28a54) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1b5ac /\ getr regs' 10 = Z_to_bv 64 p
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s p Hs Hp Cp H2.
  ex_entry regs [s; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p]) m [KRange (EVar 32) 272 (2 ^ 63); KWord (SA (EVar 32) (-160)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 10%nat [0x28a54%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma rmc_S8 : forall (fx : FPState) regs (m : word -> option byte) (s p : Z),
  (272 <= s < 2 ^ 63)%Z -> (0 <= p < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 p) -> getr regs 2 = Z_to_bv 64 (s - 272) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5ac) m rom) (@mkst fx regs' (Z_to_bv 64 0x28a54) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1b5b4 /\ getr regs' 10 = Z_to_bv 64 p
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s p Hs Hp Cp H2.
  ex_entry regs [s; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p]) m [KRange (EVar 32) 272 (2 ^ 63); KWord (SA (EVar 32) (-168)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 10%nat [0x28a54%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma rmc_S9 : forall (fx : FPState) regs (m : word -> option byte) (s p : Z),
  (272 <= s < 2 ^ 63)%Z -> (0 <= p < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 p) -> getr regs 2 = Z_to_bv 64 (s - 272) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5b4) m rom) (@mkst fx regs' (Z_to_bv 64 0x28a54) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1b5bc /\ getr regs' 10 = Z_to_bv 64 p
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s p Hs Hp Cp H2.
  ex_entry regs [s; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p]) m [KRange (EVar 32) 272 (2 ^ 63); KWord (SA (EVar 32) (-176)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 10%nat [0x28a54%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_SE : forall (fx : FPState) regs (m : word -> option byte) (s pixd z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 : Z),
  (272 <= s < 2 ^ 63)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
  (0 <= z1 < 2 ^ 64)%Z -> (0 <= z8 < 2 ^ 64)%Z -> (0 <= z9 < 2 ^ 64)%Z -> (0 <= z18 < 2 ^ 64)%Z -> (0 <= z19 < 2 ^ 64)%Z -> (0 <= z20 < 2 ^ 64)%Z ->
  (0 <= z21 < 2 ^ 64)%Z -> (0 <= z22 < 2 ^ 64)%Z -> (0 <= z23 < 2 ^ 64)%Z -> (0 <= z24 < 2 ^ 64)%Z -> (0 <= z25 < 2 ^ 64)%Z -> (0 <= z26 < 2 ^ 64)%Z ->
  (0 <= z27 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 264)) 8 = Some (Z_to_le_bytes 8 pixd) ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (Z_to_le_bytes 8 z1) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (Z_to_le_bytes 8 z8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (Z_to_le_bytes 8 z9) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 z18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 z19) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 z20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 z21) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 z22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 z23) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 z24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 z25) -> rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (Z_to_le_bytes 8 z26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 z27) ->
  getr regs 2 = Z_to_bv 64 (s - 272) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5bc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b53c) m rom)
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
                 [KRange (EVar 32) 272 (2 ^ 63); KWord (SA (EVar 32) (-264)) 8 (EVar 33);
                  KWord (SA (EVar 32) (-8)) 8 (EVar 34); KWord (SA (EVar 32) (-16)) 8 (EVar 35); KWord (SA (EVar 32) (-24)) 8 (EVar 36);
                  KWord (SA (EVar 32) (-32)) 8 (EVar 37); KWord (SA (EVar 32) (-40)) 8 (EVar 38); KWord (SA (EVar 32) (-48)) 8 (EVar 39);
                  KWord (SA (EVar 32) (-56)) 8 (EVar 40); KWord (SA (EVar 32) (-64)) 8 (EVar 41); KWord (SA (EVar 32) (-72)) 8 (EVar 42);
                  KWord (SA (EVar 32) (-80)) 8 (EVar 43); KWord (SA (EVar 32) (-88)) 8 (EVar 44); KWord (SA (EVar 32) (-96)) 8 (EVar 45);
                  KWord (SA (EVar 32) (-104)) 8 (EVar 46)]) by (ex_know regs).
  ex_run 50%nat [0x1b53c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_S3a : forall (fx : FPState) regs m (s n g rm gm bm : Z),
  (272 <= s < 2 ^ 63)%Z -> (1 <= n <= 256)%Z -> (1 <= g < 2 ^ 63)%Z -> (g mod 4 = 0)%Z -> (0 <= rm < 2 ^ 64)%Z -> (0 <= gm < 2 ^ 64)%Z -> (0 <= bm < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 n) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 rm) -> rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 gm) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 bm) ->
  getr regs 2 = Z_to_bv 64 (s - 272) -> getr regs 10 = Z_to_bv 64 g ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a894) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a8d0) m rom)
    /\ getr regs' 30 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 rm /\ getr regs' 13 = Z_to_bv 64 gm /\ getr regs' 14 = Z_to_bv 64 bm
    /\ getr regs' 15 = Z_to_bv 64 1 /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 17 = Z_to_bv 64 0x3f000000
    /\ getr regs' 5 = Z_to_bv 64 0x118b8 /\ getr regs' 6 = Z_to_bv 64 0x118bc /\ getr regs' 7 = Z_to_bv 64 0x118c0 /\ getr regs' 28 = Z_to_bv 64 0x118c4
    /\ getr regs' 29 = Z_to_bv 64 0x118c8
    /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs'.
Proof.
  intros fx regs m s n g rm gm bm Hs Hn Hg ALg Hrm Hgm Hbm Cn Crm Cgm Cbm H2 H10.
  ex_entry regs [s; n; g; rm; gm; bm] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; n; g; rm; gm; bm]) m
                 [KRange (EVar 32) 272 (2 ^ 63); KRange (EVar 33) 1 256; KRange (EVar 34) 1 (2 ^ 63); KAlign (EVar 34) 4;
                  KWord (SA (EVar 32) (-192)) 8 (EVar 33); KWord (SA (EVar 32) (-152)) 8 (EVar 35); KWord (SA (EVar 32) (-160)) 8 (EVar 36);
                  KWord (SA (EVar 32) (-168)) 8 (EVar 37)]).
  { ex_know regs. }
  ex_run 100%nat [0x1a8d0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  all: rewrite ?zbv_snez by lia; try reflexivity; try (apply bv_eq; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma rmc_S3b : forall (fx : FPState) regs m (n rm gm bm : Z),
  (1 <= n <= 256)%Z -> (1 <= rm < 2 ^ 63)%Z -> (rm mod 4 = 0)%Z -> (1 <= gm < 2 ^ 63)%Z -> (gm mod 4 = 0)%Z -> (1 <= bm < 2 ^ 63)%Z -> (bm mod 4 = 0)%Z ->
  getr regs 15 = Z_to_bv 64 1 -> getr regs 16 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 rm -> getr regs 13 = Z_to_bv 64 gm -> getr regs 14 = Z_to_bv 64 bm ->
  getr regs 30 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a8e8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a920) m rom)
    /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 17 = Z_to_bv 64 1 /\ getr regs' 5 = Z_to_bv 64 1 /\ getr regs' 6 = Z_to_bv 64 1
    /\ getr regs' 7 = Z_to_bv 64 1 /\ getr regs' 28 = Z_to_bv 64 1 /\ getr regs' 29 = Z_to_bv 64 1 /\ getr regs' 30 = Z_to_bv 64 (4 * n)
    /\ regs_agree (fun r => In r [5; 6; 7; 16; 17; 28; 29; 30]%list) regs regs'.
Proof.
  intros fx regs m n rm gm bm Hn Hrm ALr Hgm ALg Hbm ALb H15 H16 H12 H13 H14 H30.
  ex_entry regs [n; rm; gm; bm] HR.
  assert (HK : know_ok SEGS (ex_env regs [n; rm; gm; bm]) m
                 [KRange (EVar 32) 1 256; KRange (EVar 33) 1 (2 ^ 63); KAlign (EVar 33) 4; KRange (EVar 34) 1 (2 ^ 63); KAlign (EVar 34) 4;
                  KRange (EVar 35) 1 (2 ^ 63); KAlign (EVar 35) 4]).
  { ex_know regs. }
  ex_run 100%nat [0x1a920%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  all: rewrite ?zbv_snez by lia; try reflexivity; try (apply bv_eq; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma rmc_L1a : forall (fx : FPState) regs m (rm gm bm off r g b : Z),
  (1 <= rm)%Z -> (rm + 1024 < 2 ^ 63)%Z -> (1 <= gm)%Z -> (gm + 1024 < 2 ^ 63)%Z -> (1 <= bm)%Z -> (bm + 1024 < 2 ^ 63)%Z -> (0 <= off <= 1020)%Z ->
  (0 <= r <= 255)%Z -> (0 <= g <= 255)%Z -> (0 <= b <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (rm + off + 0)) 4 = Some (Z_to_le_bytes 4 r) -> rdn SEGS m (Z_to_bv 64 (gm + off + 0)) 4 = Some (Z_to_le_bytes 4 g) ->
  rdn SEGS m (Z_to_bv 64 (bm + off + 0)) 4 = Some (Z_to_le_bytes 4 b) ->
  getr regs 11 = Z_to_bv 64 off -> getr regs 12 = Z_to_bv 64 rm -> getr regs 13 = Z_to_bv 64 gm -> getr regs 14 = Z_to_bv 64 bm ->
  getr regs 17 = Z_to_bv 64 1 -> getr regs 5 = Z_to_bv 64 1 -> getr regs 6 = Z_to_bv 64 1 -> getr regs 7 = Z_to_bv 64 1 -> getr regs 28 = Z_to_bv 64 1 -> getr regs 29 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a920) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a974) m rom)
    /\ getr regs' 31 = Z_to_bv 64 r /\ getr regs' 8 = Z_to_bv 64 g /\ getr regs' 9 = Z_to_bv 64 b
    /\ regs_agree (fun x => In x [8; 9; 18; 31]%list) regs regs'.
Proof.
  intros fx regs m rm gm bm off r g b Hrm Hrm63 Hgm Hgm63 Hbm Hbm63 Hoff Hr Hg Hb Cr Cg Cb H11 H12 H13 H14 H17 H5 H6 H7 H28 H29.
  ex_entry regs [rm; gm; bm; off; r; g; b] HR.
  assert (HK : know_ok SEGS (ex_env regs [rm; gm; bm; off; r; g; b]) m
                 [KRange (EVar 32) 1 (2 ^ 63 - 1024); KRange (EVar 33) 1 (2 ^ 63 - 1024); KRange (EVar 34) 1 (2 ^ 63 - 1024); KRange (EVar 35) 0 1020;
                  KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255;
                  KWord (SA (EAlu ALU_ADD (EVar 32) (EVar 35)) 0) 4 (EVar 36); KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 35)) 0) 4 (EVar 37);
                  KWord (SA (EAlu ALU_ADD (EVar 34) (EVar 35)) 0) 4 (EVar 38)]).
  { ex_know regs.
    - apply (exx_kword_sum SEGS _ m _ _ _ rm off 0 r 4); [reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | cbn; lia | lia | exact Cr].
    - apply (exx_kword_sum SEGS _ m _ _ _ gm off 0 g 4); [reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | cbn; lia | lia | exact Cg].
    - apply (exx_kword_sum SEGS _ m _ _ _ bm off 0 b 4); [reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | cbn; lia | lia | exact Cb]. }
  ex_run 100%nat [0x1a974%Z] (SCR [false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma rmc_L1c : forall (fx : FPState) regs m (g off : Z),
  (1 <= g)%Z -> (g + 1024 < 2 ^ 63)%Z -> (0 <= off <= 1020)%Z ->
  getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 off -> getr regs 15 = Z_to_bv 64 1 -> getr regs 16 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a9a4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1a9bc) m rom)
    /\ getr regs' 31 = Z_to_bv 64 (g + off)
    /\ regs_agree (fun x => In x [8; 31]%list) regs regs'.
Proof.
  intros fx regs m g off Hg Hg63 Hoff H10 H11 H15 H16.
  ex_entry regs [g; off] HR.
  assert (HK : know_ok SEGS (ex_env regs [g; off]) m [KRange (EVar 32) 1 (2 ^ 63 - 1024); KRange (EVar 33) 0 1020]) by (ex_know regs).
  ex_run 100%nat [0x1a9bc%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

End Segs.
