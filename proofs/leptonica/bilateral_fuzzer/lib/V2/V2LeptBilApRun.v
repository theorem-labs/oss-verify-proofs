(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2_code_pixCreateTemplate V2_code_bilateralApply.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Ltac post1 :=
  lazymatch goal with
  | |- regs_agree _ _ _ => solve_regs_agree
  | |- getr _ _ = _ => gres; pin; first [ reflexivity | apply bv_eq; rewrite ?u_Z2bv by lia; lia ]
  | |- _ = _ => first [ reflexivity | assumption ]
  end.
Ltac post := repeat (lazymatch goal with |- _ /\ _ => split end); post1.

Ltac cellw regs HK Hlf off a x :=
  let C := fresh "C" in
  exB_cellw HK Hlf (EVar 32) off a x C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacW); exact C.
Ltac cellz regs HK Hlf off n a z :=
  let C := fresh "C" in
  exB_cell HK Hlf (EVar 32) off n a z C ltac:(exB_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact C.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Existing Instance exf_fxd | 100.

Lemma ap_A : forall (fx : FPState) regs (m : word -> option byte) (s bil pixs kx kf pa ls : Z),
  (4096 + 160 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 160)%Z ->
  (bil mod 8 = 0)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= s - 160)%Z ->
  (pa mod 8 = 0)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  (0 <= kx < 2 ^ 64)%Z ->
  (0 <= kf < 2 ^ 64)%Z ->
  (0 <= ls < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 bil) 8 = Some (Z_to_le_bytes 8 pixs) ->
  rdn SEGS m (Z_to_bv 64 (bil + 16)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (bil + 56)) 4 = Some (Z_to_le_bytes 4 10) ->
  rdn SEGS m (Z_to_bv 64 (bil + 72)) 8 = Some (Z_to_le_bytes 8 kx) ->
  rdn SEGS m (Z_to_bv 64 (bil + 80)) 8 = Some (Z_to_le_bytes 8 kf) ->
  rdn SEGS m (Z_to_bv 64 (bil + 88)) 8 = Some (Z_to_le_bytes 8 pa) ->
  rdn SEGS m (Z_to_bv 64 (bil + 96)) 8 = Some (Z_to_le_bytes 8 ls) ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 238988) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104716) M' rom /\
      rinv [((s - 160)%Z, 160%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) /\
      getr regs' 1 = Z_to_bv 64 239100 /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 21 = Z_to_bv 64 pixs /\
      getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 kx /\ getr regs' 24 = Z_to_bv 64 kf /\ getr regs' 25 = Z_to_bv 64 ls /\
      regs_agree (fun r => In r [1; 2; 8; 10; 11; 21; 22; 23; 24; 25]%list) regs regs').
Proof.
  intros fx regs m s bil pixs kx kf pa ls Hs Hb Hbs Ab Hp Hps Ap Hpx Hkx Hkf Hls R0 R16 R56 R72 R80 R88 R96 Rpa SOK H2 H10.
  ex_entry regs [s; bil; pixs; kx; kf; pa; ls] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bil; pixs; kx; kf; pa; ls]) m
    [KWr (SA (EVar 32) (-160)) 160; KAlign (EVar 33) 8; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 37) 8; KRange (EVar 37) 4096 (2 ^ 47);
     KDisj (SA (EVar 32) (-160)) 160 (SA (EVar 33) 0) 104; KDisj (SA (EVar 32) (-160)) 160 (SA (EVar 37) 0) 4;
     KWord (SA (EVar 33) 0) 8 (EVar 34); KWord (SA (EVar 33) 16) 4 (ELit 1); KWord (SA (EVar 33) 56) 4 (ELit 10);
     KWord (SA (EVar 33) 72) 8 (EVar 35); KWord (SA (EVar 33) 80) 8 (EVar 36); KWord (SA (EVar 33) 88) 8 (EVar 37);
     KWord (SA (EVar 33) 96) 8 (EVar 38); KWord (SA (EVar 37) 0) 4 (ELit 10)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 200%nat [104716%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 160)%Z, 160%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (ex_reg regs HR); try (ex_agree HRo HR).
  all: lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?s - ?k)) 8 = Some (word_to_le_bytes 8 ?x) =>
    let k' := eval cbv in (- k)%Z in cellw regs HK Hlf k' (s - k)%Z x end.
Qed.

Lemma ap_B : forall (fx : FPState) regs (m : word -> option byte) (s pixs pixd datas wpls datad wpld w h : Z),
  (4096 + 160 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 160)%Z ->
  (pixs mod 8 = 0)%Z ->
  (4096 <= pixd)%Z ->
  (pixd + 64 <= s - 160)%Z ->
  (pixd mod 8 = 0)%Z ->
  (0 <= datas < 2 ^ 64)%Z ->
  (0 <= wpls < 2 ^ 31)%Z ->
  (0 <= datad < 2 ^ 64)%Z ->
  (0 <= wpld < 2 ^ 31)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (1 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 56)) 8 = Some (Z_to_le_bytes 8 datas) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 16)) 4 = Some (Z_to_le_bytes 4 wpls) ->
  rdn SEGS m (Z_to_bv 64 (pixd + 56)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (pixd + 16)) 4 = Some (Z_to_le_bytes 4 wpld) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
  getr regs 2 = Z_to_bv 64 (s - 160) ->
  getr regs 10 = Z_to_bv 64 pixd ->
  getr regs 21 = Z_to_bv 64 pixs ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 239100) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 239184) M' rom /\
      rinv [((s - 144)%Z, 8%Z); ((s - 112)%Z, 8%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) /\
      rdn SEGS M' (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpld) /\
      getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 datas /\ getr regs' 18 = Z_to_bv 64 wpls /\
      getr regs' 19 = Z_to_bv 64 datad /\ getr regs' 10 = Z_to_bv 64 h /\
      regs_agree (fun r => In r [1; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s pixs pixd datas wpls datad wpld w h Hs As Hps Hpss Aps Hpd Hpds Apd Hds Hws Hdd Hwd Hw Hh R56 R16 D56 D16 R0 R4 SOK H2 H10 H21.
  assert (As' : ((s - 160) mod 16 = 0)%Z) by (rewrite Zminus_mod, As; reflexivity).
  ex_entry regs [(s - 160)%Z; pixs; pixd; datas; wpls; datad; wpld; w; h] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 160)%Z; pixs; pixd; datas; wpls; datad; wpld; w; h]) m
    [KWr (SA (EVar 32) 0) 160; KAlign (EVar 32) 16; KRange (EVar 32) 4096 (2 ^ 47);
     KAlign (EVar 33) 8; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 34) 8; KRange (EVar 34) 4096 (2 ^ 47);
     KDisj (SA (EVar 32) 0) 160 (SA (EVar 33) 0) 64; KDisj (SA (EVar 32) 0) 160 (SA (EVar 34) 0) 64;
     KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1); KRange (EVar 39) 0 (2 ^ 31 - 1); KRange (EVar 40) 1 (2 ^ 31 - 1);
     KWord (SA (EVar 33) 56) 8 (EVar 35); KWord (SA (EVar 33) 16) 4 (EVar 36); KWord (SA (EVar 34) 56) 8 (EVar 37);
     KWord (SA (EVar 34) 16) 4 (EVar 38); KWord (SA (EVar 33) 0) 4 (EVar 39); KWord (SA (EVar 33) 4) 4 (EVar 40)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 300%nat [239184%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 144)%Z, 8%Z); ((s - 112)%Z, 8%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (ex_reg regs HR); try (ex_agree HRo HR).
  all: try (rewrite ?ex_sx32 by lia; reflexivity).
  - cellz regs HK Hlf 52%Z 4%nat (s - 108)%Z w.
  - cellz regs HK Hlf 48%Z 4%nat (s - 112)%Z h.
  - cellz regs HK Hlf 16%Z 8%nat (s - 144)%Z wpld.
Qed.

Lemma ap_Bn : forall (fx : FPState) regs (m : word -> option byte) (s : Z) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  (4096 + 160 <= s <= 2 ^ 47)%Z ->
  (487424 <= s - 160)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v27) ->
  getr regs 2 = Z_to_bv 64 (s - 160) ->
  getr regs 10 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 239100) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 97988) M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 67429 /\ getr regs' 11 = Z_to_bv 64 70815 /\ getr regs' 12 = Z_to_bv 64 0 /\
      getr regs' 1 = v1 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs').
Proof.
  intros fx regs m s v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hs Himg HG HV R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 H2 H10.
  rewrite <- (zbv_self v1) in R1; rewrite <- (zbv_self v8) in R8; rewrite <- (zbv_self v9) in R9; rewrite <- (zbv_self v18) in R18; rewrite <- (zbv_self v19) in R19; rewrite <- (zbv_self v20) in R20; rewrite <- (zbv_self v21) in R21; rewrite <- (zbv_self v22) in R22; rewrite <- (zbv_self v23) in R23; rewrite <- (zbv_self v24) in R24; rewrite <- (zbv_self v25) in R25; rewrite <- (zbv_self v26) in R26; rewrite <- (zbv_self v27) in R27.
  ex_entry regs [(s - 160)%Z; u v1; u v8; u v9; u v18; u v19; u v20; u v21; u v22; u v23; u v24; u v25; u v26; u v27] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 160)%Z; u v1; u v8; u v9; u v18; u v19; u v20; u v21; u v22; u v23; u v24; u v25; u v26; u v27]) m
    [KImg 282176 282336; KImg 286472 286480;
     KWord (SA (EVar 32) 152) 8 (EVar 33); KWord (SA (EVar 32) 144) 8 (EVar 34); KWord (SA (EVar 32) 136) 8 (EVar 35);
     KWord (SA (EVar 32) 128) 8 (EVar 36); KWord (SA (EVar 32) 120) 8 (EVar 37); KWord (SA (EVar 32) 112) 8 (EVar 38);
     KWord (SA (EVar 32) 104) 8 (EVar 39); KWord (SA (EVar 32) 96) 8 (EVar 40); KWord (SA (EVar 32) 88) 8 (EVar 41);
     KWord (SA (EVar 32) 80) 8 (EVar 42); KWord (SA (EVar 32) 72) 8 (EVar 43); KWord (SA (EVar 32) 64) 8 (EVar 44);
     KWord (SA (EVar 32) 56) 8 (EVar 45)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 300%nat [97988%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (ex_reg regs HR); try (ex_agree HRo HR).
  all: first [ reflexivity | apply zbv_self ].
Qed.

Lemma ap_C : forall (fx : FPState) regs (m : word -> option byte) (s : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  (4096 + 160 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v27) ->
  getr regs 2 = Z_to_bv 64 (s - 160) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240152) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = getr regs 8 /\
      getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs').
Proof.
  intros fx regs m s ret v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hs Hret E1 R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 H2. subst v1.
  unfold reach. eexists. split.
  - norm_pc.
    sn F_3aa18 D_3aa18.
    stepLD8 F_3aa1c D_3aa1c ret.
    stepLD8 F_3aa20 D_3aa20 v8.
    stepLD8 F_3aa24 D_3aa24 v9.
    stepLD8 F_3aa28 D_3aa28 v18.
    stepLD8 F_3aa2c D_3aa2c v19.
    stepLD8 F_3aa30 D_3aa30 v20.
    stepLD8 F_3aa34 D_3aa34 v21.
    stepLD8 F_3aa38 D_3aa38 v22.
    stepLD8 F_3aa3c D_3aa3c v23.
    stepLD8 F_3aa40 D_3aa40 v24.
    stepLD8 F_3aa44 D_3aa44 v25.
    stepLD8 F_3aa48 D_3aa48 v26.
    stepLD8 F_3aa4c D_3aa4c v27.
    zv F_3aa50 D_3aa50 (Z_to_bv 64 s).
    stepret F_3aa54 D_3aa54 ret ltac:(bveq).
    apply mst_refl.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

End Segs.
