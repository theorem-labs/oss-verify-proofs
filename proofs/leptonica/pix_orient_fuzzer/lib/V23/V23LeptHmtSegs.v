(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRop GrayLib LeptRecs LeptSel LeptExec LeptExecW LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23ExecUb V23LeptBase V23LeptDilSegs.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition FRH (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (FRD m s ret regs) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).
(* [comment removed for export] *)
Definition PGDH (m : word -> option byte) (s w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 w))) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 h)).
(* [comment removed for export] *)
Definition SARH (m : word -> option byte) (s : Z) : word -> option byte :=
  wbytes m (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

#[local] Ltac exB_sc_hook ::= v23_sc_hook.

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma hm_A : forall regs m (s pixd pixs sel : Z) (ret : word),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
  getr regs 12 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (0xa2088 : word) m rom) (mkst regs' (0xa1b7c : word) (FRH m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0xa20d0 /\ getr regs' 9 = Z_to_bv 64 sel
    /\ getr regs' 18 = Z_to_bv 64 pixs /\ getr regs' 13 = Z_to_bv 64 (s - 152)
    /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 12 = Z_to_bv 64 sel
    /\ regs_agree (fun r => In r [1; 2; 9; 13; 18]%list) regs regs'.
Proof.
  intros regs m s pixd pixs sel ret Hs Hs64 SOK H2 H1 H10 H11 H12.
  replace (0xa2088 : word) with (Z_to_bv 64 0xa2088) by (apply bv_eq; reflexivity).
  replace (0xa1b7c : word) with (Z_to_bv 64 0xa1b7c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixd; pixs; sel] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd; pixs; sel]) m [KWr (SA (EVar 32) (-160)) 160]) by (ex_know regs).
  ex_run 400%nat [0xa1b7c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold FRH, FRD. subst ret. ex_mem regs Hms.
  - repeat split; try (v23_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma hm_N : forall regs m (s : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (0xa20d0 : word) m rom) (mkst regs' (0x63740 : word) m rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0xa2408 /\ getr regs' 10 = Z_to_bv 64 0x16ae9
    /\ getr regs' 11 = Z_to_bv 64 0x16348 /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RG RV H2 H10.
  replace (0xa20d0 : word) with (Z_to_bv 64 0xa20d0) by (apply bv_eq; reflexivity).
  replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3)]%Z) by (ex_know regs).
  ex_run 400%nat [0x63740%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR'].
Qed.

Lemma hm_Nz : forall regs m (s v : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z -> ret_ok ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) -> rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v11) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 v ->
  exists regs',
    msteps SEGS (mkst regs (0xa2408 : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 v
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5
    /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10 /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s v ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 Hv Hret R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H2 H10.
  replace (0xa2408 : word) with (Z_to_bv 64 0xa2408) by (apply bv_eq; reflexivity).
  ex_entryL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] regs [s; v] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] regs [s; v]) m
    [KWord (SA (EVar 45) (-8)) 8 (EVar 0); KWord (SA (EVar 45) (-16)) 8 (EVar 1); KWord (SA (EVar 45) (-24)) 8 (EVar 2);
     KWord (SA (EVar 45) (-32)) 8 (EVar 3); KWord (SA (EVar 45) (-40)) 8 (EVar 4); KWord (SA (EVar 45) (-48)) 8 (EVar 5);
     KWord (SA (EVar 45) (-56)) 8 (EVar 6); KWord (SA (EVar 45) (-64)) 8 (EVar 7); KWord (SA (EVar 45) (-72)) 8 (EVar 8);
     KWord (SA (EVar 45) (-80)) 8 (EVar 9); KWord (SA (EVar 45) (-88)) 8 (EVar 10); KWord (SA (EVar 45) (-96)) 8 (EVar 11);
     KWord (SA (EVar 45) (-104)) 8 (EVar 12);
     KRange (EVar 45) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa2450%Z] (SCR [] [] []) HR HK R' HR' Hms.
  assert (E1 : getr R' 1 = ret) by (ex_reg regs HR').
  exists R'. split.
  - cbn [s_pc] in Hms.
    assert (F : fetch_word SEGS (Z_to_bv 64 0xa2450) = Some (0x00008067 : bv 32)) by v23_vm_refl.
    assert (D : decode_any (0x00008067 : bv 32) = Some (Jalr 0 1 0, 4%Z)) by v23_vm_refl.
    eapply ex_msteps_snoc; [ex_mem regs Hms | reflexivity |].
    rewrite (step_jalr_x0 _ _ _ _ _ _ _ _ _ F eq_refl D E1).
    change (v_jalr ret (bv_signed (0 : bv 12))) with (v_jalr ret 0). rewrite (Hret : v_jalr ret 0 = ret). reflexivity.
  - repeat split; try (v23_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma hm_B : forall regs m (s pixd pixs sel w h : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs + 8 <= 2 ^ 64)%Z -> (pixs mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (pixs + 8 <= s - 112 \/ s - 104 <= pixs)%Z ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs -> getr regs 9 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (0xa20d0 : word) m rom) (mkst regs' (0xa4fd0 : word) (PGDH m s w h) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0xa2104 /\ getr regs' 8 = Z_to_bv 64 pixd
    /\ getr regs' 10 = Z_to_bv 64 sel /\ getr regs' 11 = Z_to_bv 64 (s - 120) /\ getr regs' 12 = Z_to_bv 64 (s - 116)
    /\ getr regs' 13 = Z_to_bv 64 (s - 128) /\ getr regs' 14 = Z_to_bv 64 (s - 124)
    /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd pixs sel w h Hs Hs64 Hs16 Hpd Hp1 Hp2 ALp Hw Hh DJ RW RH SOK H2 H10 H18 H9.
  replace (0xa20d0 : word) with (Z_to_bv 64 0xa20d0) by (apply bv_eq; reflexivity).
  replace (0xa4fd0 : word) with (Z_to_bv 64 0xa4fd0) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixd; pixs; sel; w; h] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd; pixs; sel; w; h]) m
    [KWord (SA (EVar 34) 0) 4 (EVar 36); KWord (SA (EVar 34) 4) 4 (EVar 37); KWr (SA (EVar 32) (-112)) 8;
     KDisj (SA (EVar 34) 0) 8 (SA (EVar 32) (-112)) 8;
     KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 64 - 8);
     KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa4fd0%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [unfold PGDH; v23_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
  all: try (rewrite ?Z.add_0_r; exact SOK).
Qed.

(* [comment removed for export] *)
Lemma hm_E : forall regs m (s sel sy sx : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z -> (1 <= sel < 2 ^ 64)%Z -> (sel mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 sx) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (0xa2104 : word) m rom) (mkst regs' (0xa21a8 : word) m rom)
    /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 20 = Z_to_bv 64 2 /\ getr regs' 21 = Z_to_bv 64 0x7fffffff
    /\ getr regs' 22 = Z_to_bv 64 0 /\ getr regs' 23 = Z_to_bv 64 (4 * 0) /\ getr regs' 24 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 0
    /\ getr regs' 26 = Z_to_bv 64 (8 * 0) /\ getr regs' 27 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 sx
    /\ regs_agree (fun r => In r [10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s sel sy sx Hs Hs64 Hsy Hsx Hsel ALs RY RX H2 H9.
  replace (0xa2104 : word) with (Z_to_bv 64 0xa2104) by (apply bv_eq; reflexivity).
  replace (0xa21a8 : word) with (Z_to_bv 64 0xa21a8) by (apply bv_eq; reflexivity).
  ex_entry regs [s; sel; sy; sx] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; sel; sy; sx]) m
    [KWord (SA (EVar 32) (-120)) 4 (EVar 34); KWord (SA (EVar 32) (-116)) 4 (EVar 35);
     KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 1 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa21a8%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
Qed.

(* [comment removed for export] *)
Lemma hm_F : forall regs m (s : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs',
    msteps SEGS (mkst regs (0xa23d0 : word) m rom) (mkst regs' (0x6df98 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa23d8 /\ getr regs' 10 = Z_to_bv 64 (s - 152)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa23d0 : word) with (Z_to_bv 64 0xa23d0) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs).
  ex_run 20%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma hm_Z : forall regs m (s pixd : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> ret_ok ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) -> rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v11) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs',
    msteps SEGS (mkst regs (0xa23d8 : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5
    /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10 /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s pixd ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 Hpd Hret R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H2 H8.
  replace (0xa23d8 : word) with (Z_to_bv 64 0xa23d8) by (apply bv_eq; reflexivity).
  ex_entryL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] regs [s; pixd] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] regs [s; pixd]) m
    [KWord (SA (EVar 45) (-8)) 8 (EVar 0); KWord (SA (EVar 45) (-16)) 8 (EVar 1); KWord (SA (EVar 45) (-24)) 8 (EVar 2);
     KWord (SA (EVar 45) (-32)) 8 (EVar 3); KWord (SA (EVar 45) (-40)) 8 (EVar 4); KWord (SA (EVar 45) (-48)) 8 (EVar 5);
     KWord (SA (EVar 45) (-56)) 8 (EVar 6); KWord (SA (EVar 45) (-64)) 8 (EVar 7); KWord (SA (EVar 45) (-72)) 8 (EVar 8);
     KWord (SA (EVar 45) (-80)) 8 (EVar 9); KWord (SA (EVar 45) (-88)) 8 (EVar 10); KWord (SA (EVar 45) (-96)) 8 (EVar 11);
     KWord (SA (EVar 45) (-104)) 8 (EVar 12);
     KRange (EVar 45) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa2450%Z] (SCR [] [] []) HR HK R' HR' Hms.
  assert (E1 : getr R' 1 = ret) by (ex_reg regs HR').
  exists R'. split.
  - cbn [s_pc] in Hms.
    assert (F : fetch_word SEGS (Z_to_bv 64 0xa2450) = Some (0x00008067 : bv 32)) by v23_vm_refl.
    assert (D : decode_any (0x00008067 : bv 32) = Some (Jalr 0 1 0, 4%Z)) by v23_vm_refl.
    eapply ex_msteps_snoc; [ex_mem regs Hms | reflexivity |].
    rewrite (step_jalr_x0 _ _ _ _ _ _ _ _ _ F eq_refl D E1).
    change (v_jalr ret (bv_signed (0 : bv 12))) with (v_jalr ret 0). rewrite (Hret : v_jalr ret 0 = ret). reflexivity.
  - repeat split; try (v23_reg regs HR'); ex_agree HR HR'.
Qed.

End Segs.

Section SegsB.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma hm_X1s : forall regs m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 0) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs', msteps SEGS (mkst regs (0xa2300 : word) m rom) (mkst regs' (0xa232c : word) m rom) /\ regs_agree (fun r => In r [13]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RX H2.
  replace (0xa2300 : word) with (Z_to_bv 64 0xa2300) by (apply bv_eq; reflexivity).
  replace (0xa232c : word) with (Z_to_bv 64 0xa232c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (EVar 32) (-132)) 4 (ELit 0); KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa232c%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ v23_mem regs Hms | ex_agree HR HR' ] ].
Qed.
Lemma hm_X1c : forall regs m (s pixd xp h : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= xp < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 xp) -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs', msteps SEGS (mkst regs (0xa2300 : word) m rom) (mkst regs' (0x7f13c : word) (SARH m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa232c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 xp /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd xp h Hs Hs64 Hx Hh RX RH SOK H2 H8.
  replace (0xa2300 : word) with (Z_to_bv 64 0xa2300) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; pixd; xp; h] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; xp; h]) m
      [KWord (SA (EVar 32) (-132)) 4 (EVar 34); KWord (SA (EVar 32) (-112)) 4 (EVar 35); KWr (SA (EVar 32) (-160)) 8;
       KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0x7f13c%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARH; v23_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma hm_X2s : forall regs m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 140)) 4 = Some (Z_to_le_bytes 4 0) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs', msteps SEGS (mkst regs (0xa232c : word) m rom) (mkst regs' (0xa2368 : word) m rom) /\ regs_agree (fun r => In r [13]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RX H2.
  replace (0xa232c : word) with (Z_to_bv 64 0xa232c) by (apply bv_eq; reflexivity).
  replace (0xa2368 : word) with (Z_to_bv 64 0xa2368) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (EVar 32) (-140)) 4 (ELit 0); KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa2368%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ v23_mem regs Hms | ex_agree HR HR' ] ].
Qed.
Lemma hm_X2c : forall regs m (s pixd xn w h : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= xn < 2 ^ 30)%Z -> (0 <= w < 2 ^ 30)%Z -> (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 140)) 4 = Some (Z_to_le_bytes 4 xn) -> rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs', msteps SEGS (mkst regs (0xa232c : word) m rom) (mkst regs' (0x7f13c : word) (SARH m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa2368 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 (w - xn) /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 xn /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd xn w h Hs Hs64 Hx Hw Hh RX RW RH SOK H2 H8.
  replace (0xa232c : word) with (Z_to_bv 64 0xa232c) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; pixd; xn; w; h] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; xn; w; h]) m
      [KWord (SA (EVar 32) (-140)) 4 (EVar 34); KWord (SA (EVar 32) (-108)) 4 (EVar 35); KWord (SA (EVar 32) (-112)) 4 (EVar 36);
       KWr (SA (EVar 32) (-160)) 8; KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 30 - 1);
       KRange (EVar 35) 0 (2 ^ 30 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0x7f13c%Z] (SCR [false] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARH; v23_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma hm_X3s : forall regs m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 0) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs', msteps SEGS (mkst regs (0xa2368 : word) m rom) (mkst regs' (0xa2394 : word) m rom) /\ regs_agree (fun r => In r [14]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RX H2.
  replace (0xa2368 : word) with (Z_to_bv 64 0xa2368) by (apply bv_eq; reflexivity).
  replace (0xa2394 : word) with (Z_to_bv 64 0xa2394) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (EVar 32) (-136)) 4 (ELit 0); KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa2394%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ v23_mem regs Hms | ex_agree HR HR' ] ].
Qed.
Lemma hm_X3c : forall regs m (s pixd yp w : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= yp < 2 ^ 31)%Z -> (0 <= w < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 yp) -> rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs', msteps SEGS (mkst regs (0xa2368 : word) m rom) (mkst regs' (0x7f13c : word) (SARH m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa2394 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 yp /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd yp w Hs Hs64 Hy Hw RY RW SOK H2 H8.
  replace (0xa2368 : word) with (Z_to_bv 64 0xa2368) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; pixd; yp; w] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; yp; w]) m
      [KWord (SA (EVar 32) (-136)) 4 (EVar 34); KWord (SA (EVar 32) (-108)) 4 (EVar 35); KWr (SA (EVar 32) (-160)) 8;
       KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0x7f13c%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARH; v23_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma hm_X4s : forall regs m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 4 = Some (Z_to_le_bytes 4 0) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs', msteps SEGS (mkst regs (0xa2394 : word) m rom) (mkst regs' (0xa23d0 : word) m rom) /\ regs_agree (fun r => In r [14]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RX H2.
  replace (0xa2394 : word) with (Z_to_bv 64 0xa2394) by (apply bv_eq; reflexivity).
  replace (0xa23d0 : word) with (Z_to_bv 64 0xa23d0) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (EVar 32) (-144)) 4 (ELit 0); KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa23d0%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ v23_mem regs Hms | ex_agree HR HR' ] ].
Qed.
Lemma hm_X4c : forall regs m (s pixd yn w h : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= yn < 2 ^ 30)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 30)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 4 = Some (Z_to_le_bytes 4 yn) -> rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs', msteps SEGS (mkst regs (0xa2394 : word) m rom) (mkst regs' (0x7f13c : word) (SARH m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa23d0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (h - yn)
    /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 yn /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd yn w h Hs Hs64 Hy Hw Hh RY RW RH SOK H2 H8.
  replace (0xa2394 : word) with (Z_to_bv 64 0xa2394) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; pixd; yn; w; h] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; yn; w; h]) m
      [KWord (SA (EVar 32) (-144)) 4 (EVar 34); KWord (SA (EVar 32) (-108)) 4 (EVar 35); KWord (SA (EVar 32) (-112)) 4 (EVar 36);
       KWr (SA (EVar 32) (-160)) 8; KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 30 - 1);
       KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 30 - 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0x7f13c%Z] (SCR [false] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARH; v23_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR' ] ].
Qed.

Lemma hm_L : forall regs m (s sy sx i j : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z -> (0 <= i < sy)%Z -> (0 <= j < sx)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 sx) ->
  getr regs 2 = Z_to_bv 64 (s - 160) ->
  getr regs 18 = Z_to_bv 64 i -> getr regs 21 = Z_to_bv 64 0x7fffffff -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 (4 * j) ->
  getr regs 24 = Z_to_bv 64 j -> getr regs 25 = Z_to_bv 64 j -> getr regs 26 = Z_to_bv 64 (8 * i) -> getr regs 27 = Z_to_bv 64 i ->
  exists regs' (pc : word),
    msteps SEGS (mkst regs (0xa2194 : word) m rom) (mkst regs' pc m rom)
    /\ ( ((j + 1 < sx)%Z /\ pc = (0xa21a8 : word) /\ getr regs' 18 = Z_to_bv 64 i /\ getr regs' 23 = Z_to_bv 64 (4 * (j + 1))
          /\ getr regs' 24 = Z_to_bv 64 (j + 1) /\ getr regs' 25 = Z_to_bv 64 (j + 1) /\ getr regs' 26 = Z_to_bv 64 (8 * i)
          /\ getr regs' 27 = Z_to_bv 64 i)
       \/ ((j + 1 = sx)%Z /\ (i + 1 < sy)%Z /\ pc = (0xa21a8 : word) /\ getr regs' 18 = Z_to_bv 64 (i + 1) /\ getr regs' 23 = Z_to_bv 64 (4 * 0)
          /\ getr regs' 24 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 0 /\ getr regs' 26 = Z_to_bv 64 (8 * (i + 1))
          /\ getr regs' 27 = Z_to_bv 64 (i + 1))
       \/ ((j + 1 = sx)%Z /\ (i + 1 = sy)%Z /\ pc = (0xa22e8 : word)) )
    /\ regs_agree (fun r => In r [11; 18; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s sy sx i j Hs Hs64 Hsy Hsx Hi Hj RY RX H2 H18 H21 H22 H23 H24 H25 H26 H27.
  replace (0xa2194 : word) with (Z_to_bv 64 0xa2194) by (apply bv_eq; reflexivity).
  ex_entry regs [s; sy; sx; i; j; (4 * j)%Z; (8 * i)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; sy; sx; i; j; (4 * j)%Z; (8 * i)%Z]) m
    [KWord (SA (EVar 32) (-120)) 4 (EVar 33); KWord (SA (EVar 32) (-116)) 4 (EVar 34);
     KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1);
     KRange (EVar 35) 0 (2 ^ 31 - 2); KRange (EVar 36) 0 (2 ^ 31 - 2); KRange (EVar 37) 0 (2 ^ 33); KRange (EVar 38) 0 (2 ^ 34)]%Z) by (ex_know regs).
  destruct (Z.lt_ge_cases (j + 1) sx) as [C1|C1].
  - ex_run 400%nat [0xa21a8%Z; 0xa22e8%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R', (Z_to_bv 64 0xa21a8). split; [ex_mem regs Hms|]. split; [left; repeat split; first [lia | (apply bv_eq; reflexivity) | v23_reg regs HR'] | ex_agree HR HR']. }
  - destruct (Z.lt_ge_cases (i + 1) sy) as [C2|C2].
    + ex_run 400%nat [0xa21a8%Z; 0xa22e8%Z] (SCR [true; false] [] []) HR HK R' HR' Hms.
      all: cycle -1.
      { exists R', (Z_to_bv 64 0xa21a8). split; [ex_mem regs Hms|].
        split; [right; left; repeat split; first [lia | (apply bv_eq; reflexivity) | v23_reg regs HR'] | ex_agree HR HR']. }
    + ex_run 400%nat [0xa21a8%Z; 0xa22e8%Z] (SCR [true; true] [] []) HR HK R' HR' Hms.
      all: cycle -1.
      { exists R', (Z_to_bv 64 0xa22e8). split; [ex_mem regs Hms|].
        split; [right; right; repeat split; first [lia | (apply bv_eq; reflexivity)] | ex_agree HR HR']. }
Qed.

Lemma hm_M : forall regs m (sel data row i j c : Z),
  (0 <= sel)%Z -> (sel + 24 <= 2 ^ 64)%Z -> (1 <= data)%Z -> (data + 8 * i + 8 <= 2 ^ 64)%Z -> (1 <= row)%Z -> (row + 4 * j + 4 <= 2 ^ 64)%Z ->
  (data mod 8 = 0)%Z -> (row mod 4 = 0)%Z ->
  (0 <= i < 2 ^ 31)%Z -> (0 <= j < 2 ^ 31)%Z -> (0 <= c < 2 ^ 31)%Z -> c <> 1%Z -> c <> 2%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
  rdn SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = Some (Z_to_le_bytes 4 c) ->
  getr regs 9 = Z_to_bv 64 sel -> getr regs 19 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 2 -> getr regs 23 = Z_to_bv 64 (4 * j) ->
  getr regs 26 = Z_to_bv 64 (8 * i) ->
  exists regs',
    msteps SEGS (mkst regs (0xa21a8 : word) m rom) (mkst regs' (0xa2194 : word) m rom)
    /\ regs_agree (fun r => In r [11; 12; 13; 14]%list) regs regs'.
Proof.
  intros regs m sel data row i j c Hs1 Hs2 Hd1 Hd2 Hr1 Hr2 ALd ALr Hi Hj Hc Hc1 Hc2 RD RR RC H9 H19 H20 H23 H26.
  replace (0xa21a8 : word) with (Z_to_bv 64 0xa21a8) by (apply bv_eq; reflexivity).
  replace (0xa2194 : word) with (Z_to_bv 64 0xa2194) by (apply bv_eq; reflexivity).
  ex_entry regs [sel; data; row; i; j; c; (8 * i)%Z; (4 * j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sel; data; row; i; j; c; (8 * i)%Z; (4 * j)%Z]) m
    [KWord (SA (EVar 32) 16) 8 (EVar 33); KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 0) 8 (EVar 34);
     KWord (SA (EAlu ALU_ADD (EVar 34) (EVar 39)) 0) 4 (EVar 37);
     KRange (EVar 32) 0 (2 ^ 64 - 24); KRange (EVar 33) 1 (2 ^ 64 - 8); KRange (EVar 34) 1 (2 ^ 64 - 4);
     KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 34); KRange (EVar 39) 0 (2 ^ 33)]%Z).
  { unfold know_ok.
    apply Forall_cons; [eapply ex_kword_Z; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | exact RD] |].
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (data + 8 * i)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RR]. }
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (row + 4 * j)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RC]. }
    repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]). apply Forall_nil. }
  ex_run 400%nat [0xa2194%Z] (SCR [false; false; false; false; false; false; false; true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | ex_agree HR HR']. }
Qed.

Lemma hm_H1f : forall regs m (sel data row i j pixd : Z),
  (0 <= sel)%Z -> (sel + 24 <= 2 ^ 64)%Z -> (1 <= data)%Z -> (data + 8 * i + 8 <= 2 ^ 64)%Z -> (1 <= row)%Z -> (row + 4 * j + 4 <= 2 ^ 64)%Z ->
  (data mod 8 = 0)%Z -> (row mod 4 = 0)%Z ->
  (0 <= i < 2 ^ 31)%Z -> (0 <= j < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
  rdn SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = Some (Z_to_le_bytes 4 1) ->
  getr regs 9 = Z_to_bv 64 sel -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 19 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 2 ->
  getr regs 23 = Z_to_bv 64 (4 * j) -> getr regs 26 = Z_to_bv 64 (8 * i) -> getr regs 10 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa21a8 : word) m rom) (mkst regs' (0x6ff30 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa2210 /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros regs m sel data row i j pixd Hs1 Hs2 Hd1 Hd2 Hr1 Hr2 ALd ALr Hi Hj RD RR RC H9 H8 H19 H20 H23 H26 H10.
  replace (0xa21a8 : word) with (Z_to_bv 64 0xa21a8) by (apply bv_eq; reflexivity).
  replace (0x6ff30 : word) with (Z_to_bv 64 0x6ff30) by (apply bv_eq; reflexivity).
  ex_entry regs [sel; data; row; i; j; pixd; (8 * i)%Z; (4 * j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sel; data; row; i; j; pixd; (8 * i)%Z; (4 * j)%Z]) m
    [KWord (SA (EVar 32) 16) 8 (EVar 33); KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 0) 8 (EVar 34);
     KWord (SA (EAlu ALU_ADD (EVar 34) (EVar 39)) 0) 4 (ELit 1);
     KRange (EVar 32) 0 (2 ^ 64 - 24); KRange (EVar 33) 1 (2 ^ 64 - 8); KRange (EVar 34) 1 (2 ^ 64 - 4);
     KRange (EVar 38) 0 (2 ^ 34); KRange (EVar 39) 0 (2 ^ 33)]%Z).
  { unfold know_ok.
    apply Forall_cons; [eapply ex_kword_Z; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | exact RD] |].
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (data + 8 * i)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RR]. }
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (row + 4 * j)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RC]. }
    repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]). apply Forall_nil. }
  ex_run 400%nat [0x6ff30%Z] (SCR [false; false; false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
Qed.

Lemma hm_H2f : forall regs m (sel data row i j pixd : Z),
  (0 <= sel)%Z -> (sel + 24 <= 2 ^ 64)%Z -> (1 <= data)%Z -> (data + 8 * i + 8 <= 2 ^ 64)%Z -> (1 <= row)%Z -> (row + 4 * j + 4 <= 2 ^ 64)%Z ->
  (data mod 8 = 0)%Z -> (row mod 4 = 0)%Z ->
  (0 <= i < 2 ^ 31)%Z -> (0 <= j < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
  rdn SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = Some (Z_to_le_bytes 4 2) ->
  getr regs 9 = Z_to_bv 64 sel -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 19 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 2 ->
  getr regs 23 = Z_to_bv 64 (4 * j) -> getr regs 26 = Z_to_bv 64 (8 * i) -> getr regs 10 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (mkst regs (0xa21a8 : word) m rom) (mkst regs' (0x6ffb4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa2240 /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros regs m sel data row i j pixd Hs1 Hs2 Hd1 Hd2 Hr1 Hr2 ALd ALr Hi Hj RD RR RC H9 H8 H19 H20 H23 H26 H10.
  replace (0xa21a8 : word) with (Z_to_bv 64 0xa21a8) by (apply bv_eq; reflexivity).
  replace (0x6ffb4 : word) with (Z_to_bv 64 0x6ffb4) by (apply bv_eq; reflexivity).
  ex_entry regs [sel; data; row; i; j; pixd; (8 * i)%Z; (4 * j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [sel; data; row; i; j; pixd; (8 * i)%Z; (4 * j)%Z]) m
    [KWord (SA (EVar 32) 16) 8 (EVar 33); KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 0) 8 (EVar 34);
     KWord (SA (EAlu ALU_ADD (EVar 34) (EVar 39)) 0) 4 (ELit 2);
     KRange (EVar 32) 0 (2 ^ 64 - 24); KRange (EVar 33) 1 (2 ^ 64 - 8); KRange (EVar 34) 1 (2 ^ 64 - 4);
     KRange (EVar 38) 0 (2 ^ 34); KRange (EVar 39) 0 (2 ^ 33)]%Z).
  { unfold know_ok.
    apply Forall_cons; [eapply ex_kword_Z; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | exact RD] |].
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (data + 8 * i)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RR]. }
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (row + 4 * j)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RC]. }
    repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]). apply Forall_nil. }
  ex_run 400%nat [0x6ffb4%Z] (SCR [false; false; false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
Qed.

Lemma hm_H1n : forall regs m (s sel data row i j cx cy w h pixt : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= sel)%Z -> (sel + 24 <= 2 ^ 64)%Z -> (1 <= data)%Z -> (data + 8 * i + 8 <= 2 ^ 64)%Z -> (1 <= row)%Z -> (row + 4 * j + 4 <= 2 ^ 64)%Z ->
  (data mod 8 = 0)%Z -> (row mod 4 = 0)%Z ->
  (0 <= i < 2 ^ 30)%Z -> (0 <= j < 2 ^ 30)%Z -> (0 <= cx < 2 ^ 30)%Z -> (0 <= cy < 2 ^ 30)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  (0 <= pixt < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
  rdn SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 cx) -> rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 cy) ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixt) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 sel -> getr regs 19 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 2 ->
  getr regs 23 = Z_to_bv 64 (4 * j) -> getr regs 24 = Z_to_bv 64 j -> getr regs 26 = Z_to_bv 64 (8 * i) -> getr regs 27 = Z_to_bv 64 i ->
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (0xa21a8 : word) m rom) (mkst regs' (0xa2180 : word) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (cx - j) /\ getr regs' 12 = Z_to_bv 64 (cy - i) /\ getr regs' 13 = Z_to_bv 64 w
    /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 8 /\ getr regs' 16 = Z_to_bv 64 pixt
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof.
  intros regs m s sel data row i j cx cy w h pixt Hs Hs64 Hs1 Hs2 Hd1 Hd2 Hr1 Hr2 ALd ALr Hi Hj Hcx Hcy Hw Hh Hpt
    RD RR RC RCX RCY RW RH RT H2 H9 H19 H20 H23 H24 H26 H27 H10.
  replace (0xa21a8 : word) with (Z_to_bv 64 0xa21a8) by (apply bv_eq; reflexivity).
  replace (0xa2180 : word) with (Z_to_bv 64 0xa2180) by (apply bv_eq; reflexivity).
  ex_entry regs [s; sel; data; row; i; j; cx; cy; w; h; pixt; (8 * i)%Z; (4 * j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; sel; data; row; i; j; cx; cy; w; h; pixt; (8 * i)%Z; (4 * j)%Z]) m
    [KWord (SA (EVar 33) 16) 8 (EVar 34); KWord (SA (EAlu ALU_ADD (EVar 34) (EVar 43)) 0) 8 (EVar 35);
     KWord (SA (EAlu ALU_ADD (EVar 35) (EVar 44)) 0) 4 (ELit 1);
     KWord (SA (EVar 32) (-124)) 4 (EVar 38); KWord (SA (EVar 32) (-128)) 4 (EVar 39);
     KWord (SA (EVar 32) (-108)) 4 (EVar 40); KWord (SA (EVar 32) (-112)) 4 (EVar 41);
     KWord (SA (EVar 32) (-152)) 8 (EVar 42);
     KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 24); KRange (EVar 34) 1 (2 ^ 64 - 8); KRange (EVar 35) 1 (2 ^ 64 - 4);
     KRange (EVar 36) 0 (2 ^ 30 - 1); KRange (EVar 37) 0 (2 ^ 30 - 1); KRange (EVar 38) 0 (2 ^ 30 - 1); KRange (EVar 39) 0 (2 ^ 30 - 1);
     KRange (EVar 40) 0 (2 ^ 31 - 1); KRange (EVar 41) 0 (2 ^ 31 - 1); KRange (EVar 43) 0 (2 ^ 33); KRange (EVar 44) 0 (2 ^ 32)]%Z).
  { unfold know_ok.
    apply Forall_cons; [eapply ex_kword_Z; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | exact RD] |].
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (data + 8 * i)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RR]. }
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (row + 4 * j)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RC]. }
    ex_know regs. }
  ex_run 400%nat [0xa2180%Z] (SCR [false; false; false; false; false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
Qed.

Lemma hm_H2n : forall regs m (s sel data row i j cx cy w h pixt : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= sel)%Z -> (sel + 24 <= 2 ^ 64)%Z -> (1 <= data)%Z -> (data + 8 * i + 8 <= 2 ^ 64)%Z -> (1 <= row)%Z -> (row + 4 * j + 4 <= 2 ^ 64)%Z ->
  (data mod 8 = 0)%Z -> (row mod 4 = 0)%Z ->
  (0 <= i < 2 ^ 30)%Z -> (0 <= j < 2 ^ 30)%Z -> (0 <= cx < 2 ^ 30)%Z -> (0 <= cy < 2 ^ 30)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  (0 <= pixt < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
  rdn SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = Some (Z_to_le_bytes 4 2) ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 cx) -> rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 cy) ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixt) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 sel -> getr regs 19 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 2 ->
  getr regs 23 = Z_to_bv 64 (4 * j) -> getr regs 24 = Z_to_bv 64 j -> getr regs 26 = Z_to_bv 64 (8 * i) -> getr regs 27 = Z_to_bv 64 i ->
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (0xa21a8 : word) m rom) (mkst regs' (0xa2180 : word) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (cx - j) /\ getr regs' 12 = Z_to_bv 64 (cy - i) /\ getr regs' 13 = Z_to_bv 64 w
    /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 2 /\ getr regs' 16 = Z_to_bv 64 pixt
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof.
  intros regs m s sel data row i j cx cy w h pixt Hs Hs64 Hs1 Hs2 Hd1 Hd2 Hr1 Hr2 ALd ALr Hi Hj Hcx Hcy Hw Hh Hpt
    RD RR RC RCX RCY RW RH RT H2 H9 H19 H20 H23 H24 H26 H27 H10.
  replace (0xa21a8 : word) with (Z_to_bv 64 0xa21a8) by (apply bv_eq; reflexivity).
  replace (0xa2180 : word) with (Z_to_bv 64 0xa2180) by (apply bv_eq; reflexivity).
  ex_entry regs [s; sel; data; row; i; j; cx; cy; w; h; pixt; (8 * i)%Z; (4 * j)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; sel; data; row; i; j; cx; cy; w; h; pixt; (8 * i)%Z; (4 * j)%Z]) m
    [KWord (SA (EVar 33) 16) 8 (EVar 34); KWord (SA (EAlu ALU_ADD (EVar 34) (EVar 43)) 0) 8 (EVar 35);
     KWord (SA (EAlu ALU_ADD (EVar 35) (EVar 44)) 0) 4 (ELit 2);
     KWord (SA (EVar 32) (-124)) 4 (EVar 38); KWord (SA (EVar 32) (-128)) 4 (EVar 39);
     KWord (SA (EVar 32) (-108)) 4 (EVar 40); KWord (SA (EVar 32) (-112)) 4 (EVar 41);
     KWord (SA (EVar 32) (-152)) 8 (EVar 42);
     KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 24); KRange (EVar 34) 1 (2 ^ 64 - 8); KRange (EVar 35) 1 (2 ^ 64 - 4);
     KRange (EVar 36) 0 (2 ^ 30 - 1); KRange (EVar 37) 0 (2 ^ 30 - 1); KRange (EVar 38) 0 (2 ^ 30 - 1); KRange (EVar 39) 0 (2 ^ 30 - 1);
     KRange (EVar 40) 0 (2 ^ 31 - 1); KRange (EVar 41) 0 (2 ^ 31 - 1); KRange (EVar 43) 0 (2 ^ 33); KRange (EVar 44) 0 (2 ^ 32)]%Z).
  { unfold know_ok.
    apply Forall_cons; [eapply ex_kword_Z; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | exact RD] |].
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (data + 8 * i)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RR]. }
    apply Forall_cons.
    { eapply ex_kword_Z with (b := (row + 4 * j)%Z);
        [ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
        | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RC]. }
    ex_know regs. }
  ex_run 400%nat [0xa2180%Z] (SCR [false; false; false; false; false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
Qed.

Lemma hm_C12 : forall regs m (s i j cx cy w h pixt : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= i < 2 ^ 30)%Z -> (0 <= j < 2 ^ 30)%Z -> (0 <= cx < 2 ^ 30)%Z -> (0 <= cy < 2 ^ 30)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  (0 <= pixt < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 cx) -> rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 cy) ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixt) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 24 = Z_to_bv 64 j -> getr regs 27 = Z_to_bv 64 i ->
  exists regs',
    msteps SEGS (mkst regs (0xa2210 : word) m rom) (mkst regs' (0xa2180 : word) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (cx - j) /\ getr regs' 12 = Z_to_bv 64 (cy - i) /\ getr regs' 13 = Z_to_bv 64 w
    /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixt
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof.
  intros regs m s i j cx cy w h pixt Hs Hs64 Hi Hj Hcx Hcy Hw Hh Hpt RCX RCY RW RH RT H2 H24 H27.
  replace (0xa2210 : word) with (Z_to_bv 64 0xa2210) by (apply bv_eq; reflexivity).
  replace (0xa2180 : word) with (Z_to_bv 64 0xa2180) by (apply bv_eq; reflexivity).
  ex_entry regs [s; i; j; cx; cy; w; h; pixt] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; j; cx; cy; w; h; pixt]) m
    [KWord (SA (EVar 32) (-124)) 4 (EVar 35); KWord (SA (EVar 32) (-128)) 4 (EVar 36);
     KWord (SA (EVar 32) (-108)) 4 (EVar 37); KWord (SA (EVar 32) (-112)) 4 (EVar 38);
     KWord (SA (EVar 32) (-152)) 8 (EVar 39);
     KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 30 - 1); KRange (EVar 34) 0 (2 ^ 30 - 1);
     KRange (EVar 35) 0 (2 ^ 30 - 1); KRange (EVar 36) 0 (2 ^ 30 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1)]%Z)
    by (ex_know regs).
  ex_run 400%nat [0xa2180%Z] (SCR [false; true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
Qed.

Lemma hm_C3 : forall regs m (s i j cx cy w h pixt : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= i < 2 ^ 30)%Z -> (0 <= j < 2 ^ 30)%Z -> (0 <= cx < 2 ^ 30)%Z -> (0 <= cy < 2 ^ 30)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  (0 <= pixt < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 cx) -> rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 cy) ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixt) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 24 = Z_to_bv 64 j -> getr regs 27 = Z_to_bv 64 i ->
  exists regs',
    msteps SEGS (mkst regs (0xa2240 : word) m rom) (mkst regs' (0xa2180 : word) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (cx - j) /\ getr regs' 12 = Z_to_bv 64 (cy - i) /\ getr regs' 13 = Z_to_bv 64 w
    /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 3 /\ getr regs' 16 = Z_to_bv 64 pixt
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof.
  intros regs m s i j cx cy w h pixt Hs Hs64 Hi Hj Hcx Hcy Hw Hh Hpt RCX RCY RW RH RT H2 H24 H27.
  replace (0xa2240 : word) with (Z_to_bv 64 0xa2240) by (apply bv_eq; reflexivity).
  replace (0xa2180 : word) with (Z_to_bv 64 0xa2180) by (apply bv_eq; reflexivity).
  ex_entry regs [s; i; j; cx; cy; w; h; pixt] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; j; cx; cy; w; h; pixt]) m
    [KWord (SA (EVar 32) (-124)) 4 (EVar 35); KWord (SA (EVar 32) (-128)) 4 (EVar 36);
     KWord (SA (EVar 32) (-108)) 4 (EVar 37); KWord (SA (EVar 32) (-112)) 4 (EVar 38);
     KWord (SA (EVar 32) (-152)) 8 (EVar 39);
     KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 30 - 1); KRange (EVar 34) 0 (2 ^ 30 - 1);
     KRange (EVar 35) 0 (2 ^ 30 - 1); KRange (EVar 36) 0 (2 ^ 30 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1)]%Z)
    by (ex_know regs).
  ex_run 400%nat [0xa2180%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
Qed.

Lemma hm_S : forall regs m (s pixd : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs',
    msteps SEGS (mkst regs (0xa2180 : word) m rom) (mkst regs' (0x7f13c : word) (SARH m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa2190 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 17 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 10; 17]%list) regs regs'.
Proof.
  intros regs m s pixd Hs Hs64 SOK H2 H8.
  replace (0xa2180 : word) with (Z_to_bv 64 0xa2180) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd]) m [KWr (SA (EVar 32) (-160)) 8; KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs).
  ex_run 20%nat [0x7f13c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [unfold SARH; v23_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
  all: try (rewrite ?Z.add_0_r; exact SOK).
Qed.

Lemma hm_R : forall regs m, exists regs',
    msteps SEGS (mkst regs (0xa2190 : word) m rom) (mkst regs' (0xa2194 : word) m rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof.
  intros regs m.
  replace (0xa2190 : word) with (Z_to_bv 64 0xa2190) by (apply bv_eq; reflexivity).
  replace (0xa2194 : word) with (Z_to_bv 64 0xa2194) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []) by (apply Forall_nil).
  ex_run 20%nat [0xa2194%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms | split; [v23_reg regs HR' | ex_agree HR HR']]. }
Qed.

(* [comment removed for export] *)
Lemma hm_T : forall regs m (s sel : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (0xa22e8 : word) m rom) (mkst regs' (0xa5590 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa2300 /\ getr regs' 10 = Z_to_bv 64 sel /\ getr regs' 11 = Z_to_bv 64 (s - 132)
    /\ getr regs' 12 = Z_to_bv 64 (s - 136) /\ getr regs' 13 = Z_to_bv 64 (s - 140) /\ getr regs' 14 = Z_to_bv 64 (s - 144)
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros regs m s sel Hs Hs64 H2 H9.
  replace (0xa22e8 : word) with (Z_to_bv 64 0xa22e8) by (apply bv_eq; reflexivity).
  replace (0xa5590 : word) with (Z_to_bv 64 0xa5590) by (apply bv_eq; reflexivity).
  ex_entry regs [s; sel] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; sel]) m [KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs).
  ex_run 100%nat [0xa5590%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR'].
Qed.

End SegsB.
