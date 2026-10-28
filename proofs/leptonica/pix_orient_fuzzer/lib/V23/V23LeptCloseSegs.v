(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCloseSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.

Lemma cs_agree_comp : forall (L1 L2 L : list reg) regs R1 R2,
  regs_agree (fun r => In r L1) regs R1 -> regs_agree (fun r => In r L2) R1 R2 ->
  (forall r, In r L1 \/ In r L2 -> In r L) -> regs_agree (fun r => In r L) regs R2.
Proof.
  unfold regs_agree. intros L1 L2 L regs R1 R2 H1 H2 HL r Hr.
  rewrite H2 by (intro; apply Hr, HL; tauto). apply H1. intro; apply Hr, HL; tauto.
Qed.

Lemma cs_cw8_rd : forall m (p a v z : Z),
  (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> (0 <= p)%Z -> (p + 8 <= 2 ^ 64)%Z -> (a + 8 <= p \/ p + 8 <= a)%Z ->
  rdn SEGS (O23LeptCloseSegs.CW8 m p v) (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z) ->
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z).
Proof.
  intros m p a v z Ha Ha8 Hp Hp8 Hd H. unfold O23LeptCloseSegs.CW8 in H.
  rewrite rdn_wbytes_out_Z in H; [exact H|]. zlen. lia.
Qed.

Lemma cs_A1 : forall regs m (s pix1 hs vs : Z) (ret : word),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix1)%Z -> (pix1 + 64 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 ->
  getr regs 12 = Z_to_bv 64 hs -> getr regs 13 = Z_to_bv 64 vs ->
  exists regs',
    msteps SEGS (mkst regs (0xa4878 : word) m rom) (mkst regs' (0xa48bc : word) (O23LeptCloseSegs.FRC m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pix1 /\ getr regs' 10 = Z_to_bv 64 pix1
    /\ getr regs' 18 = Z_to_bv 64 hs /\ getr regs' 19 = Z_to_bv 64 vs /\ getr regs' 20 = Z_to_bv 64 pix1
    /\ regs_agree (fun r => In r [2; 8; 18; 19; 20]%list) regs regs'.
Proof.
  intros regs m s pix1 hs vs ret Hs Hs64 Hp1 Hp64 SOK H2 H1 H10 H11 H12 H13.
  replace (0xa4878 : word) with (Z_to_bv 64 0xa4878) by (apply bv_eq; reflexivity).
  replace (0xa48bc : word) with (Z_to_bv 64 0xa48bc) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pix1; hs; vs] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pix1; hs; vs]) m
                 [KWr (SA (EVar 32) (-112)) 112; KRange (EVar 33) 1 (2 ^ 64 - 65)]%Z) by (ex_know regs).
  ex_run 100%nat [0xa48bc%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCloseSegs.FRC. subst ret. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

Lemma cs_A2_h : forall regs M (s pix1 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix1)%Z -> (pix1 + 64 < 2 ^ 64)%Z -> (pix1 mod 8 = 0)%Z ->
  rdn SEGS M (Z_to_bv 64 (pix1 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS M (Z_to_bv 64 0x127ca0) 4 = Some (Z_to_le_bytes 4 1) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 8 = Z_to_bv 64 pix1 -> getr regs 10 = Z_to_bv 64 pix1 ->
  getr regs 18 = Z_to_bv 64 30 -> getr regs 19 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 pix1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa48bc : word) M rom) (mkst regs' (0xa3574 : word) M rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa49c4 /\ getr regs' 9 = Z_to_bv 64 2
    /\ getr regs' 10 = Z_to_bv 64 30 /\ getr regs' 11 = Z_to_bv 64 1
    /\ getr regs' 12 = Z_to_bv 64 (s - 80) /\ getr regs' 13 = Z_to_bv 64 (s - 88)
    /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13]%list) regs regs'.
Proof.
  intros regs M s pix1 Hs Hs64 Hp1 Hp64 AL8 RD RB H2 H8 H10 H18 H19 H20.
  replace (0xa48bc : word) with (Z_to_bv 64 0xa48bc) by (apply bv_eq; reflexivity).
  replace (0xa3574 : word) with (Z_to_bv 64 0xa3574) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pix1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pix1]) M
                 [KRange (EVar 33) 1 (2 ^ 64 - 65); KAlign (EVar 33) 8;
                  KWord (SA (EVar 33) 8) 4 (ELit 1); KWord (SA (ELit 0) 0x127ca0) 4 (ELit 1)]%Z) by (ex_know regs).
  ex_run 200%nat [0xa3574%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

Lemma cs_A2_v : forall regs M (s pix1 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix1)%Z -> (pix1 + 64 < 2 ^ 64)%Z -> (pix1 mod 8 = 0)%Z ->
  rdn SEGS M (Z_to_bv 64 (pix1 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS M (Z_to_bv 64 0x127ca0) 4 = Some (Z_to_le_bytes 4 1) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 8 = Z_to_bv 64 pix1 -> getr regs 10 = Z_to_bv 64 pix1 ->
  getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 8 -> getr regs 20 = Z_to_bv 64 pix1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa48bc : word) M rom) (mkst regs' (0xa3574 : word) M rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4a18 /\ getr regs' 9 = Z_to_bv 64 2
    /\ getr regs' 10 = Z_to_bv 64 8 /\ getr regs' 11 = Z_to_bv 64 2
    /\ getr regs' 12 = Z_to_bv 64 (s - 96) /\ getr regs' 13 = Z_to_bv 64 (s - 104)
    /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13]%list) regs regs'.
Proof.
  intros regs M s pix1 Hs Hs64 Hp1 Hp64 AL8 RD RB H2 H8 H10 H18 H19 H20.
  replace (0xa48bc : word) with (Z_to_bv 64 0xa48bc) by (apply bv_eq; reflexivity).
  replace (0xa3574 : word) with (Z_to_bv 64 0xa3574) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pix1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pix1]) M
                 [KRange (EVar 33) 1 (2 ^ 64 - 65); KAlign (EVar 33) 8;
                  KWord (SA (EVar 33) 8) 4 (ELit 1); KWord (SA (ELit 0) 0x127ca0) 4 (ELit 1)]%Z) by (ex_know regs).
  ex_run 200%nat [0xa3574%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_A_h : forall regs m (s pix1 : Z) (ret : word),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix1)%Z -> (pix1 + 64 < 2 ^ 64)%Z -> (pix1 mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  rdn SEGS (O23LeptCloseSegs.FRC m s ret regs) (Z_to_bv 64 (pix1 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS (O23LeptCloseSegs.FRC m s ret regs) (Z_to_bv 64 0x127ca0) 4 = Some (Z_to_le_bytes 4 1) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 ->
  getr regs 12 = Z_to_bv 64 30 -> getr regs 13 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4878 : word) m rom) (mkst regs' (0xa3574 : word) (O23LeptCloseSegs.FRC m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 112)
    /\ getr regs' 1 = Z_to_bv 64 0xa49c4
    /\ getr regs' 8 = Z_to_bv 64 pix1
    /\ getr regs' 9 = Z_to_bv 64 2
    /\ getr regs' 18 = Z_to_bv 64 30
    /\ getr regs' 19 = Z_to_bv 64 1
    /\ getr regs' 20 = Z_to_bv 64 pix1
    /\ getr regs' 10 = Z_to_bv 64 30
    /\ getr regs' 11 = Z_to_bv 64 1
    /\ getr regs' 12 = Z_to_bv 64 (s - 80)
    /\ getr regs' 13 = Z_to_bv 64 (s - 88)
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20]%list) regs regs'.
Proof.
  intros regs m s pix1 ret Hs Hs64 Hp1 Hp64 AL8 SOK RD RB H2 H1 H10 H11 H12 H13.
  destruct (cs_A1 regs m s pix1 30 1 ret Hs Hs64 Hp1 Hp64 SOK H2 H1 H10 H11 H12 H13)
    as (R1 & MS1 & A2 & A8 & A10 & A18 & A19 & A20 & AG1).
  destruct (cs_A2_h R1 _ s pix1 Hs Hs64 Hp1 Hp64 AL8 RD RB A2 A8 A10 A18 A19 A20)
    as (R2 & MS2 & B1 & B9 & B10 & B11 & B12 & B13 & AG2).
  exists R2. split; [eapply msteps_trans; [exact MS1 | exact MS2] |].
  repeat split; try assumption;
    try (rewrite AG2 by (cbn [In]; intuition discriminate); assumption).
  eapply cs_agree_comp; [exact AG1 | exact AG2 |]. cbn [In]; intros r Hr; tauto.
Qed.

(* [comment removed for export] *)
Lemma cs_C_h : forall regs m (pix1 : Z),
  getr regs 10 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 2 -> getr regs 18 = Z_to_bv 64 30 -> getr regs 19 = Z_to_bv 64 1 ->
  getr regs 20 = Z_to_bv 64 pix1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa49c4 : word) m rom) (mkst regs' (0x70e84 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4ad0
    /\ getr regs' 9 = Z_to_bv 64 32
    /\ getr regs' 10 = Z_to_bv 64 pix1
    /\ getr regs' 11 = Z_to_bv 64 32
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 9; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m pix1 H10 H9 H18 H19 H20.
  replace (0xa49c4 : word) with (Z_to_bv 64 0xa49c4) by (apply bv_eq; reflexivity).
  replace (0x70e84 : word) with (Z_to_bv 64 0x70e84) by (apply bv_eq; reflexivity).
  ex_entry regs [pix1] HR.
  assert (HK : know_ok SEGS (ex_env regs [pix1]) m []) by (ex_know regs).
  ex_run 100%nat [0x70e84%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_D_h : forall regs m (s pixsb sel1 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel1 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
  rdn SEGS (O23LeptCloseSegs.CW8 m (s - 56) pixsb) (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 sel1) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixsb -> getr regs 18 = Z_to_bv 64 30 -> getr regs 19 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4ad0 : word) m rom) (mkst regs' (0xa1968 : word) (O23LeptCloseSegs.CW8 m (s - 56) pixsb) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4aec
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 pixsb
    /\ getr regs' 12 = Z_to_bv 64 sel1
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s pixsb sel1 Hs Hs64 Hsel SOK RD H2 H10 H18 H19.
  apply cs_cw8_rd in RD; [| lia | lia | lia | lia | lia].
  replace (0xa4ad0 : word) with (Z_to_bv 64 0xa4ad0) by (apply bv_eq; reflexivity).
  replace (0xa1968 : word) with (Z_to_bv 64 0xa1968) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixsb; sel1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixsb; sel1]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWr (SA (EVar 32) (-56)) 8; KWord (SA (EVar 32) (-80)) 8 (EVar 34)]%Z)
    by (ex_know regs).
  ex_run 100%nat [0xa1968%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCloseSegs.CW8. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_E_h : forall regs m (s pixt sel2 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel2 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 sel2) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (0xa4aec : word) m rom) (mkst regs' (0xa1968 : word) (O23LeptCloseSegs.CW8 m (s - 64) pixt) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4b04
    /\ getr regs' 19 = Z_to_bv 64 pixt
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 pixt
    /\ getr regs' 12 = Z_to_bv 64 sel2
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 19]%list) regs regs'.
Proof.
  intros regs m s pixt sel2 Hs Hs64 Hsel SOK RD H2 H10.
  replace (0xa4aec : word) with (Z_to_bv 64 0xa4aec) by (apply bv_eq; reflexivity).
  replace (0xa1968 : word) with (Z_to_bv 64 0xa1968) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixt; sel2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixt; sel2]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWr (SA (EVar 32) (-64)) 8; KWord (SA (EVar 32) (-88)) 8 (EVar 34)]%Z)
    by (ex_know regs).
  ex_run 100%nat [0xa1968%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCloseSegs.CW8. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_F_h : forall regs m (s pixt pixdb sel1 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel1 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 sel1) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixdb -> getr regs 19 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (0xa4b04 : word) m rom) (mkst regs' (0xa1d7c : word) (O23LeptCloseSegs.CW8 m (s - 72) pixdb) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4b1c
    /\ getr regs' 18 = Z_to_bv 64 pixdb
    /\ getr regs' 10 = Z_to_bv 64 pixt
    /\ getr regs' 11 = Z_to_bv 64 pixdb
    /\ getr regs' 12 = Z_to_bv 64 sel1
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
Proof.
  intros regs m s pixt pixdb sel1 Hs Hs64 Hsel SOK RD H2 H10 H19.
  replace (0xa4b04 : word) with (Z_to_bv 64 0xa4b04) by (apply bv_eq; reflexivity).
  replace (0xa1d7c : word) with (Z_to_bv 64 0xa1d7c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixt; pixdb; sel1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixt; pixdb; sel1]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWr (SA (EVar 32) (-72)) 8; KWord (SA (EVar 32) (-80)) 8 (EVar 35)]%Z)
    by (ex_know regs).
  ex_run 100%nat [0xa1d7c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCloseSegs.CW8. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_G_h : forall regs m (s pixt pixdb sel2 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel2 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 sel2) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 18 = Z_to_bv 64 pixdb -> getr regs 19 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (0xa4b1c : word) m rom) (mkst regs' (0xa1d7c : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4be8
    /\ getr regs' 10 = Z_to_bv 64 pixdb
    /\ getr regs' 11 = Z_to_bv 64 pixt
    /\ getr regs' 12 = Z_to_bv 64 sel2
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s pixt pixdb sel2 Hs Hs64 Hsel RD H2 H18 H19.
  replace (0xa4b1c : word) with (Z_to_bv 64 0xa4b1c) by (apply bv_eq; reflexivity).
  replace (0xa1d7c : word) with (Z_to_bv 64 0xa1d7c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixt; pixdb; sel2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixt; pixdb; sel2]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWord (SA (EVar 32) (-88)) 8 (EVar 35)]%Z)
    by (ex_know regs).
  ex_run 100%nat [0xa1d7c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_A_v : forall regs m (s pix1 : Z) (ret : word),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix1)%Z -> (pix1 + 64 < 2 ^ 64)%Z -> (pix1 mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  rdn SEGS (O23LeptCloseSegs.FRC m s ret regs) (Z_to_bv 64 (pix1 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS (O23LeptCloseSegs.FRC m s ret regs) (Z_to_bv 64 0x127ca0) 4 = Some (Z_to_le_bytes 4 1) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 ->
  getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 8 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4878 : word) m rom) (mkst regs' (0xa3574 : word) (O23LeptCloseSegs.FRC m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 112)
    /\ getr regs' 1 = Z_to_bv 64 0xa4a18
    /\ getr regs' 8 = Z_to_bv 64 pix1
    /\ getr regs' 9 = Z_to_bv 64 2
    /\ getr regs' 18 = Z_to_bv 64 1
    /\ getr regs' 19 = Z_to_bv 64 8
    /\ getr regs' 20 = Z_to_bv 64 pix1
    /\ getr regs' 10 = Z_to_bv 64 8
    /\ getr regs' 11 = Z_to_bv 64 2
    /\ getr regs' 12 = Z_to_bv 64 (s - 96)
    /\ getr regs' 13 = Z_to_bv 64 (s - 104)
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20]%list) regs regs'.
Proof.
  intros regs m s pix1 ret Hs Hs64 Hp1 Hp64 AL8 SOK RD RB H2 H1 H10 H11 H12 H13.
  destruct (cs_A1 regs m s pix1 1 8 ret Hs Hs64 Hp1 Hp64 SOK H2 H1 H10 H11 H12 H13)
    as (R1 & MS1 & A2 & A8 & A10 & A18 & A19 & A20 & AG1).
  destruct (cs_A2_v R1 _ s pix1 Hs Hs64 Hp1 Hp64 AL8 RD RB A2 A8 A10 A18 A19 A20)
    as (R2 & MS2 & B1 & B9 & B10 & B11 & B12 & B13 & AG2).
  exists R2. split; [eapply msteps_trans; [exact MS1 | exact MS2] |].
  repeat split; try assumption;
    try (rewrite AG2 by (cbn [In]; intuition discriminate); assumption).
  eapply cs_agree_comp; [exact AG1 | exact AG2 |]. cbn [In]; intros r Hr; tauto.
Qed.

(* [comment removed for export] *)
Lemma cs_C_v : forall regs m (pix1 : Z),
  getr regs 10 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 2 -> getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 8 ->
  getr regs 20 = Z_to_bv 64 pix1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4a18 : word) m rom) (mkst regs' (0x70e84 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4ad0
    /\ getr regs' 9 = Z_to_bv 64 32
    /\ getr regs' 10 = Z_to_bv 64 pix1
    /\ getr regs' 11 = Z_to_bv 64 32
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 9; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m pix1 H10 H9 H18 H19 H20.
  replace (0xa4a18 : word) with (Z_to_bv 64 0xa4a18) by (apply bv_eq; reflexivity).
  replace (0x70e84 : word) with (Z_to_bv 64 0x70e84) by (apply bv_eq; reflexivity).
  ex_entry regs [pix1] HR.
  assert (HK : know_ok SEGS (ex_env regs [pix1]) m []) by (ex_know regs).
  ex_run 100%nat [0x70e84%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_D_v : forall regs m (s pixsb sel1 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel1 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
  rdn SEGS (O23LeptCloseSegs.CW8 m (s - 56) pixsb) (Z_to_bv 64 (s - 96)) 8 = Some (Z_to_le_bytes 8 sel1) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixsb -> getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 8 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4ad0 : word) m rom) (mkst regs' (0xa1968 : word) (O23LeptCloseSegs.CW8 m (s - 56) pixsb) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4b34
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 pixsb
    /\ getr regs' 12 = Z_to_bv 64 sel1
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s pixsb sel1 Hs Hs64 Hsel SOK RD H2 H10 H18 H19.
  apply cs_cw8_rd in RD; [| lia | lia | lia | lia | lia].
  replace (0xa4ad0 : word) with (Z_to_bv 64 0xa4ad0) by (apply bv_eq; reflexivity).
  replace (0xa1968 : word) with (Z_to_bv 64 0xa1968) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixsb; sel1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixsb; sel1]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWr (SA (EVar 32) (-56)) 8; KWord (SA (EVar 32) (-96)) 8 (EVar 34)]%Z)
    by (ex_know regs).
  ex_run 100%nat [0xa1968%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCloseSegs.CW8. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_E_v : forall regs m (s pixt sel2 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel2 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 sel2) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (0xa4b34 : word) m rom) (mkst regs' (0xa1968 : word) (O23LeptCloseSegs.CW8 m (s - 64) pixt) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4b4c
    /\ getr regs' 19 = Z_to_bv 64 pixt
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 pixt
    /\ getr regs' 12 = Z_to_bv 64 sel2
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 19]%list) regs regs'.
Proof.
  intros regs m s pixt sel2 Hs Hs64 Hsel SOK RD H2 H10.
  replace (0xa4b34 : word) with (Z_to_bv 64 0xa4b34) by (apply bv_eq; reflexivity).
  replace (0xa1968 : word) with (Z_to_bv 64 0xa1968) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixt; sel2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixt; sel2]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWr (SA (EVar 32) (-64)) 8; KWord (SA (EVar 32) (-104)) 8 (EVar 34)]%Z)
    by (ex_know regs).
  ex_run 100%nat [0xa1968%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCloseSegs.CW8. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_F_v : forall regs m (s pixt pixdb sel1 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel1 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (Z_to_le_bytes 8 sel1) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixdb -> getr regs 19 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (0xa4b4c : word) m rom) (mkst regs' (0xa1d7c : word) (O23LeptCloseSegs.CW8 m (s - 72) pixdb) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4bd8
    /\ getr regs' 18 = Z_to_bv 64 pixdb
    /\ getr regs' 10 = Z_to_bv 64 pixt
    /\ getr regs' 11 = Z_to_bv 64 pixdb
    /\ getr regs' 12 = Z_to_bv 64 sel1
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
Proof.
  intros regs m s pixt pixdb sel1 Hs Hs64 Hsel SOK RD H2 H10 H19.
  replace (0xa4b4c : word) with (Z_to_bv 64 0xa4b4c) by (apply bv_eq; reflexivity).
  replace (0xa1d7c : word) with (Z_to_bv 64 0xa1d7c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixt; pixdb; sel1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixt; pixdb; sel1]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWr (SA (EVar 32) (-72)) 8; KWord (SA (EVar 32) (-96)) 8 (EVar 35)]%Z)
    by (ex_know regs).
  ex_run 100%nat [0xa1d7c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCloseSegs.CW8. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_G_v : forall regs m (s pixt pixdb sel2 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel2 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 sel2) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 18 = Z_to_bv 64 pixdb -> getr regs 19 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (0xa4bd8 : word) m rom) (mkst regs' (0xa1d7c : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4be8
    /\ getr regs' 10 = Z_to_bv 64 pixdb
    /\ getr regs' 11 = Z_to_bv 64 pixt
    /\ getr regs' 12 = Z_to_bv 64 sel2
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s pixt pixdb sel2 Hs Hs64 Hsel RD H2 H18 H19.
  replace (0xa4bd8 : word) with (Z_to_bv 64 0xa4bd8) by (apply bv_eq; reflexivity).
  replace (0xa1d7c : word) with (Z_to_bv 64 0xa1d7c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixt; pixdb; sel2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixt; pixdb; sel2]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWord (SA (EVar 32) (-104)) 8 (EVar 35)]%Z)
    by (ex_know regs).
  ex_run 100%nat [0xa1d7c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_H : forall regs m (s : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4be8 : word) m rom) (mkst regs' (0x6df98 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4bf0
    /\ getr regs' 10 = Z_to_bv 64 (s - 64)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa4be8 : word) with (Z_to_bv 64 0xa4be8) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs).
  ex_run 100%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_I : forall regs m (pixdb : Z),
  getr regs 18 = Z_to_bv 64 pixdb -> getr regs 9 = Z_to_bv 64 32 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4bf0 : word) m rom) (mkst regs' (0x711d4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4bfc
    /\ getr regs' 10 = Z_to_bv 64 pixdb
    /\ getr regs' 11 = Z_to_bv 64 32
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros regs m pixdb H18 H9.
  replace (0xa4bf0 : word) with (Z_to_bv 64 0xa4bf0) by (apply bv_eq; reflexivity).
  replace (0x711d4 : word) with (Z_to_bv 64 0x711d4) by (apply bv_eq; reflexivity).
  ex_entry regs [pixdb] HR.
  assert (HK : know_ok SEGS (ex_env regs [pixdb]) m []) by (ex_know regs).
  ex_run 100%nat [0x711d4%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_J : forall regs m (s pixt2 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixt2 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4bfc : word) m rom) (mkst regs' (0x6df98 : word) (O23LeptCloseSegs.CW8 m (s - 64) pixt2) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4c08
    /\ getr regs' 10 = Z_to_bv 64 (s - 56)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s pixt2 Hs Hs64 SOK H2 H10.
  replace (0xa4bfc : word) with (Z_to_bv 64 0xa4bfc) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixt2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixt2]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KWr (SA (EVar 32) (-64)) 8]%Z) by (ex_know regs).
  ex_run 100%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCloseSegs.CW8. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_K : forall regs m (s : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4c08 : word) m rom) (mkst regs' (0x6df98 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4c10
    /\ getr regs' 10 = Z_to_bv 64 (s - 72)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa4c08 : word) with (Z_to_bv 64 0xa4c08) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs).
  ex_run 100%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_L : forall regs m (s pix1 pixt2 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix1 < 2 ^ 64)%Z -> (0 <= pixt2 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixt2) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 8 = Z_to_bv 64 pix1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4c10 : word) m rom) (mkst regs' (0x6eb5c : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4c20
    /\ getr regs' 10 = Z_to_bv 64 pix1
    /\ getr regs' 11 = Z_to_bv 64 pixt2
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros regs m s pix1 pixt2 Hs Hs64 Hp1 Hpt RD H2 H8.
  replace (0xa4c10 : word) with (Z_to_bv 64 0xa4c10) by (apply bv_eq; reflexivity).
  replace (0x6eb5c : word) with (Z_to_bv 64 0x6eb5c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pix1; pixt2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pix1; pixt2]) m
                 [KRange (EVar 32) 112 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1);
                  KWord (SA (EVar 32) (-64)) 8 (EVar 34)]%Z) by (ex_know regs).
  ex_run 100%nat [0x6eb5c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_M : forall regs m (s : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4c20 : word) m rom) (mkst regs' (0x6df98 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4c28
    /\ getr regs' 10 = Z_to_bv 64 (s - 64)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa4c20 : word) with (Z_to_bv 64 0xa4c20) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs).
  ex_run 100%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_N : forall regs m (s : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4c28 : word) m rom) (mkst regs' (0xa4c74 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4c38
    /\ getr regs' 10 = Z_to_bv 64 (s - 80)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa4c28 : word) with (Z_to_bv 64 0xa4c28) by (apply bv_eq; reflexivity).
  replace (0xa4c74 : word) with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs).
  ex_run 100%nat [0xa4c74%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_O : forall regs m (s : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4c38 : word) m rom) (mkst regs' (0xa4c74 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4c40
    /\ getr regs' 10 = Z_to_bv 64 (s - 88)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa4c38 : word) with (Z_to_bv 64 0xa4c38) by (apply bv_eq; reflexivity).
  replace (0xa4c74 : word) with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs).
  ex_run 100%nat [0xa4c74%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_P : forall regs m (s : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4c40 : word) m rom) (mkst regs' (0xa4c74 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4c48
    /\ getr regs' 10 = Z_to_bv 64 (s - 96)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa4c40 : word) with (Z_to_bv 64 0xa4c40) by (apply bv_eq; reflexivity).
  replace (0xa4c74 : word) with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs).
  ex_run 100%nat [0xa4c74%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_Q : forall regs m (s : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4c48 : word) m rom) (mkst regs' (0xa4c74 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4c50
    /\ getr regs' 10 = Z_to_bv 64 (s - 104)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa4c48 : word) with (Z_to_bv 64 0xa4c48) by (apply bv_eq; reflexivity).
  replace (0xa4c74 : word) with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs).
  ex_run 100%nat [0xa4c74%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - exact Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma cs_Z : forall regs m (s pix1 : Z) (ret v0 v1 v2 v3 v4 : word),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 8 = Z_to_bv 64 pix1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa4c50 : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 pix1
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
Proof.
  intros regs m s pix1 ret v0 v1 v2 v3 v4 Hs Hs64 Hret R0 R1 R2 R3 R4 R5 H2 H8.
  replace (0xa4c50 : word) with (Z_to_bv 64 0xa4c50) by (apply bv_eq; reflexivity).
  ex_entryL [ret; v0; v1; v2; v3; v4] regs [s; pix1] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4] regs [s; pix1]) m
                 [KRange (EVar 38) 112 (2 ^ 64 - 1);
                  KWord (SA (EVar 38) (-8)) 8 (EVar 0); KWord (SA (EVar 38) (-16)) 8 (EVar 1);
                  KWord (SA (EVar 38) (-24)) 8 (EVar 2); KWord (SA (EVar 38) (-32)) 8 (EVar 3);
                  KWord (SA (EVar 38) (-40)) 8 (EVar 4); KWord (SA (EVar 38) (-48)) 8 (EVar 5)]%Z) by (ex_know regs).
  ex_run 100%nat [0xa4c70%Z] (SCR [] [] []) HR HK R' HR' Hms.
  assert (G1 : getr R' 1 = ret) by (ex_reg regs HR').
  assert (G2 : getr R' 2 = Z_to_bv 64 s) by (ex_reg regs HR').
  assert (G10 : getr R' 10 = Z_to_bv 64 pix1) by (ex_reg regs HR').
  assert (G8 : getr R' 8 = v0) by (ex_reg regs HR').
  assert (G9 : getr R' 9 = v1) by (ex_reg regs HR').
  assert (G18 : getr R' 18 = v2) by (ex_reg regs HR').
  assert (G19 : getr R' 19 = v3) by (ex_reg regs HR').
  assert (G20 : getr R' 20 = v4) by (ex_reg regs HR').
  assert (AG : regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs R') by (ex_agree HR HR').
  cbn [mem_denot] in Hms.
  exists R'. split.
  - eapply msteps_trans; [exact Hms|].
    ex_fetch SEGS 0xa4c70%Z F D.
    lazymatch type of D with decode_any ?w = _ =>
      assert (Dj : decode_any w = Some (Jalr 0 1 0, 4%Z)) by (rewrite D; f_equal; f_equal; f_equal; apply bv_eq; reflexivity) end.
    eapply mst_step; [reflexivity | eapply step_jalr_x0; [exact F | reflexivity | exact Dj | exact G1] |].
    match goal with |- msteps _ (mkst _ ?t _ _) _ => replace t with ret by (symmetry; exact (Hret : v_jalr ret 0 = ret)) end.
    apply mst_refl.
  - repeat split; assumption.
Qed.

End Segs.
