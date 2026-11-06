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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec LeptExecX DitherLib LeptRmcLib LeptMask32Lib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Section Segs.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma b32_P : forall (fx : FPState) regs (m : word -> option byte) (s w h wpld wpls pixd : Z),
  (144 <= s < 2 ^ 63)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= wpld < 2 ^ 31)%Z -> (0 <= wpls < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 18 = Z_to_bv 64 wpls -> getr regs 26 = Z_to_bv 64 pixd ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c530) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c564) m rom)
    /\ getr regs' 11 = Z_to_bv 64 wpld /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 w /\ getr regs' 18 = Z_to_bv 64 (4 * wpls)
    /\ getr regs' 13 = Z_to_bv 64 18446744071562067968 /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 18]%list) regs regs'.
Proof.
  intros fx regs m s w h wpld wpls pixd Hs Hh Hw Hwd Hws Ch Cw H2 H10 H18 H26.
  ex_entry regs [s; w; h; wpld; wpls; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; h; wpld; wpls; pixd]) m
                 [KRange (EVar 32) 144 (2 ^ 63); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1);
                  KWord (SA (EVar 32) (-128)) 4 (EVar 34); KWord (SA (EVar 32) (-124)) 4 (EVar 33)]) by (ex_know regs).
  ex_run 20%nat [0x1c564%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma b32_RH : forall (fx : FPState) regs (m : word -> option byte) (w i wpld datad lines : Z),
  (1 <= w < 2 ^ 31)%Z -> (0 <= i <= 20000)%Z -> (0 <= wpld <= 20000)%Z -> (0 <= datad)%Z -> (datad + 4 * (i * wpld) < 2 ^ 63)%Z -> (0 <= lines < 2 ^ 63)%Z ->
  getr regs 14 = Z_to_bv 64 w -> getr regs 12 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 wpld -> getr regs 9 = Z_to_bv 64 datad -> getr regs 8 = Z_to_bv 64 lines ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c564) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c594) m rom)
    /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0 /\ getr regs' 17 = Z_to_bv 64 (datad + 4 * (i * wpld)) /\ getr regs' 5 = Z_to_bv 64 lines
    /\ regs_agree (fun r => In r [5; 15; 16; 17]%list) regs regs'.
Proof.
  intros fx regs m w i wpld datad lines Hw Hi Hwd Hd Hd2 Hl H14 H12 H11 H9 H8.
  ex_entry regs [w; i; wpld; datad; lines] HR.
  assert (HK : know_ok SEGS (ex_env regs [w; i; wpld; datad; lines]) m
                 [KRange (EVar 32) 1 (2 ^ 31 - 1); KRange (EVar 33) 0 20000; KRange (EVar 34) 0 20000]) by (ex_know regs).
  ex_run 20%nat [0x1c594%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma b32_PL : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (w j p : Z),
  (1 <= w < 2 ^ 31)%Z -> (0 <= j < w)%Z -> (0 <= p)%Z -> (p + 4 < 2 ^ 63)%Z -> (if more then j + 1 < w else w <= j + 1)%Z ->
  getr regs 14 = Z_to_bv 64 w -> getr regs 16 = Z_to_bv 64 j -> getr regs 15 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 p ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c584) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x1c594 else 0x1c554)) m rom)
    /\ getr regs' 16 = Z_to_bv 64 (j + 1) /\ getr regs' 15 = Z_to_bv 64 (j + 1) /\ getr regs' 5 = Z_to_bv 64 (p + 4)
    /\ regs_agree (fun r => In r [5; 15; 16]%list) regs regs'.
Proof.
  intros more fx regs m w j p Hw Hj Hp Hp2 Hmore H14 H16 H15 H5.
  ex_entry regs [w; j; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [w; j; p]) m [KRange (EVar 32) 1 (2 ^ 31 - 1); KRange (EVar 33) 0 (2 ^ 31 - 2)]) by (ex_know regs).
  destruct more.
  - ex_run 20%nat [0x1c594%Z; 0x1c554%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 20%nat [0x1c594%Z; 0x1c554%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma b32_RL : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s h i lines step : Z),
  (144 <= s < 2 ^ 63)%Z -> (0 <= i < h)%Z -> (h < 2 ^ 31)%Z -> (0 <= lines)%Z -> (0 <= step)%Z -> (lines + step < 2 ^ 63)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 h) -> (if more then i + 1 < h else h <= i + 1)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 12 = Z_to_bv 64 i -> getr regs 8 = Z_to_bv 64 lines -> getr regs 18 = Z_to_bv 64 step ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c554) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x1c564 else 0x1c414)) m rom)
    /\ getr regs' 12 = Z_to_bv 64 (i + 1) /\ getr regs' 8 = Z_to_bv 64 (lines + step)
    /\ regs_agree (fun r => In r [8; 12; 15]%list) regs regs'.
Proof.
  intros more fx regs m s h i lines step Hs Hi Hh Hl Hst Hl2 Ch Hmore H2 H12 H8 H18.
  ex_entry regs [s; h; i; lines; step] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h; i; lines; step]) m
                 [KRange (EVar 32) 144 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 2); KWord (SA (EVar 32) (-128)) 4 (EVar 33)]) by (ex_know regs).
  destruct more.
  - ex_run 20%nat [0x1c564%Z; 0x1c414%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 20%nat [0x1c564%Z; 0x1c414%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Ltac px_sc Hpw R1 R2 R3 :=
  rewrite ?ext_val_zx_id by (rewrite u_Z2bv by lia; cbn; lia);
  first [ rewrite px_r_eq by lia
        | (change 281474976710656%Z with (2 ^ 48)%Z; rewrite px_m_eq by lia)
        | (change 1099511627776%Z with (2 ^ 40)%Z; rewrite px_m_eq by lia) ];
  lazymatch goal with
  | |- branch_taken BC_LT _ (Z_to_bv 64 18446744073709551615) = false => apply blt_m1_false; lia
  | |- branch_taken BC_LT (Z_to_bv 64 1) _ = true => apply (blt_1 _ true); [lia | cbn; lia]
  | |- branch_taken BC_LT (Z_to_bv 64 1) _ = false => apply (blt_1 _ false); [lia | cbn; lia]
  end.

Lemma b32_PX : forall (fx : FPState) regs (m : word -> option byte) (s w j p lined pw : Z) (bsd : list byte),
  (144 <= s <= 2 ^ 47)%Z -> (1 <= w < 2 ^ 31)%Z -> (0 <= j < w)%Z -> (4096 <= p)%Z -> (p + 4 < 2 ^ 47)%Z -> (4096 <= lined)%Z -> (lined + 4 * (j / 32) + 4 < 2 ^ 47)%Z ->
  (0 <= pw < 2 ^ 32)%Z ->
  rdn SEGS m (Z_to_bv 64 p) 4 = Some (Z_to_le_bytes 4 pw) -> rdn SEGS m (Z_to_bv 64 (lined + 4 * (j / 32))) 4 = Some bsd ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 w) ->
  store_ok SEGS m (Z_to_bv 64 (lined + 4 * (j / 32))) 4 = true ->
  (lined + 4 * (j / 32) + 4 <= s - 144 \/ s <= lined + 4 * (j / 32))%Z ->
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 14 = Z_to_bv 64 w -> getr regs 16 = Z_to_bv 64 j -> getr regs 15 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 p ->
  getr regs 17 = Z_to_bv 64 lined -> getr regs 13 = Z_to_bv 64 18446744071562067968 ->
  getr regs 20 = Z_to_bv 64 18446744073709551615 -> getr regs 21 = Z_to_bv 64 18446744073709551615 -> getr regs 22 = Z_to_bv 64 18446744073709551615 ->
  getr regs 23 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 1 -> getr regs 25 = Z_to_bv 64 1 ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c594) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c584) M' rom)
    /\ (M' = m \/ exists v : word, M' = wbytes m (Z_to_bv 64 (lined + 4 * (j / 32))) (word_to_le_bytes 4 v))
    /\ getr regs' 14 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [6; 7; 14]%list) regs regs'.
Proof.
  intros fx regs m s w j p lined pw bsd Hs Hw Hj Hp Hp2 Hl Hl2 Hpw Cp Cd Cw SOK AP H2 H14 H16 H15 H5 H17 H13 H20 H21 H22 H23 H24 H25.
  pose proof (px_r_range pw Hpw) as Rr. pose proof (px_m_range 40 pw) as Rg. pose proof (px_m_range 48 pw) as Rb.
  ex_entry regs [s; w; j; p; lined; pw; rdv true 4 bsd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; j; p; lined; pw; rdv true 4 bsd]) m
                 [KRange (EVar 32) 144 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 2); KRange (EVar 35) 4096 (2 ^ 47);
                  KRange (EVar 36) 4096 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 32 - 1); KWord (SA (EVar 32) (-124)) 4 (EVar 33); KWord (SA (EVar 35) 0) 4 (EVar 37)]).
  { ex_know regs. }
  assert (XD : alu64 ALU_ADD (Z_to_bv 64 lined) (mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 5)))))
               = Z_to_bv 64 (lined + 4 * (j / 32))) by (apply dl_bitword_w; lia).
  pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as (D1 & D2).
  destruct (Z_lt_ge_dec 1 (px_r pw)) as [R1|R1].
  { ex_runN 38%nat 80%nat [0x1c584%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    - px_sc Hpw R1 R1 R1.
    - exists R', m. split; [ex_mem2 regs Hms|]. split; [left; reflexivity|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext. }
  destruct (Z_lt_ge_dec 1 (px_m 40 pw)) as [R2|R2].
  { ex_runN 38%nat 80%nat [0x1c584%Z] (SCR [false; false; true] [] []) HR HK R' HR' Hms.
    - px_sc Hpw R1 R2 R2.
    - px_sc Hpw R1 R2 R2.
    - px_sc Hpw R1 R2 R2.
    - exists R', m. split; [ex_mem2 regs Hms|]. split; [left; reflexivity|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext. }
  destruct (Z_lt_ge_dec 1 (px_m 48 pw)) as [R3|R3].
  { ex_runN 38%nat 80%nat [0x1c584%Z] (SCR [false; false; false; false; true] [] []) HR HK R' HR' Hms.
    - px_sc Hpw R1 R2 R3.
    - px_sc Hpw R1 R2 R3.
    - px_sc Hpw R1 R2 R3.
    - px_sc Hpw R1 R2 R3.
    - px_sc Hpw R1 R2 R3.
    - exists R', m. split; [ex_mem2 regs Hms|]. split; [left; reflexivity|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext. }
  ex_runN 38%nat 80%nat [0x1c584%Z] (SCR [false; false; false; false; false] [] []) HR HK R' HR' Hms.
  - rewrite XD. rewrite !u_Z2bv by lia. clear - Hs AP Hl Hl2 D1. lia.
  - rewrite XD, zbv_addi, Z.add_0_r. exact SOK.
  - exx_named (lined + 4 * (j / 32))%Z Cd ltac:(rewrite XD, zbv_addi; f_equal; lia).
  - px_sc Hpw R1 R2 R3.
  - px_sc Hpw R1 R2 R3.
  - px_sc Hpw R1 R2 R3.
  - px_sc Hpw R1 R2 R3.
  - px_sc Hpw R1 R2 R3.
  - lazymatch type of Hms with msteps _ _ (mkst _ _ ?MM _) => exists R', MM end. split; [exact Hms|]. split.
    + right. eexists. cbn [mem_denot s_log e_addr e_width e_val]. apply ex_wbytes_eq; [reflexivity | | reflexivity].
      ex_unfoldE. unfold adenot. cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite ?H17, ?H16, XD, zbv_addi. f_equal. lia.
    + repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d32_P : forall (fx : FPState) regs (m : word -> option byte) (s w h wpld wpls pixd : Z),
  (160 <= s <= 2 ^ 47)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= wpld < 2 ^ 31)%Z -> (0 <= wpls < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 18 = Z_to_bv 64 wpls -> getr regs 23 = Z_to_bv 64 pixd ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c7e4) m rom)
                (@mkst fx regs' (Z_to_bv 64 0x1c818) (wbytes m (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
    /\ getr regs' 20 = Z_to_bv 64 wpld /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 (4 * wpls)
    /\ getr regs' 24 = Z_to_bv 64 18446744071562067968
    /\ regs_agree (fun r => In r [9; 10; 11; 20; 23; 24]%list) regs regs'.
Proof.
  intros fx regs m s w h wpld wpls pixd Hs Hh Hw Hwd Hws Ch Cw SOK H2 H10 H18 H23.
  ex_entry regs [s; w; h; wpld; wpls; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; h; wpld; wpls; pixd]) m
                 [KRange (EVar 32) 160 (2 ^ 47); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1);
                  KWord (SA (EVar 32) (-112)) 4 (EVar 34); KWord (SA (EVar 32) (-108)) 4 (EVar 33); KWr (SA (EVar 32) (-160)) 8]) by (ex_know regs).
  ex_run 20%nat [0x1c818%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma d32_RH : forall (fx : FPState) regs (m : word -> option byte) (w i wpld datad lines : Z),
  (1 <= w < 2 ^ 31)%Z -> (0 <= i <= 20000)%Z -> (0 <= wpld <= 20000)%Z -> (0 <= datad)%Z -> (datad + 4 * (i * wpld) < 2 ^ 63)%Z -> (0 <= lines < 2 ^ 63)%Z ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 23 = Z_to_bv 64 i -> getr regs 20 = Z_to_bv 64 wpld -> getr regs 19 = Z_to_bv 64 datad -> getr regs 21 = Z_to_bv 64 lines ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c818) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c84c) m rom)
    /\ getr regs' 25 = Z_to_bv 64 0 /\ getr regs' 26 = Z_to_bv 64 0 /\ getr regs' 27 = Z_to_bv 64 (datad + 4 * (i * wpld)) /\ getr regs' 18 = Z_to_bv 64 lines
    /\ regs_agree (fun r => In r [10; 18; 25; 26; 27]%list) regs regs'.
Proof.
  intros fx regs m w i wpld datad lines Hw Hi Hwd Hd Hd2 Hl H10 H23 H20 H19 H21.
  ex_entry regs [w; i; wpld; datad; lines] HR.
  assert (HK : know_ok SEGS (ex_env regs [w; i; wpld; datad; lines]) m
                 [KRange (EVar 32) 1 (2 ^ 31 - 1); KRange (EVar 33) 0 20000; KRange (EVar 34) 0 20000]) by (ex_know regs).
  ex_run 20%nat [0x1c84c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma d32_PL : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s w j p : Z),
  (160 <= s <= 2 ^ 47)%Z -> (1 <= w < 2 ^ 31)%Z -> (0 <= j < w)%Z -> (0 <= p)%Z -> (p + 4 < 2 ^ 63)%Z -> (if more then j + 1 < w else w <= j + 1)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 26 = Z_to_bv 64 j -> getr regs 25 = Z_to_bv 64 j -> getr regs 18 = Z_to_bv 64 p ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c838) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x1c84c else 0x1c808)) m rom)
    /\ getr regs' 26 = Z_to_bv 64 (j + 1) /\ getr regs' 25 = Z_to_bv 64 (j + 1) /\ getr regs' 18 = Z_to_bv 64 (p + 4) /\ getr regs' 10 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [10; 18; 25; 26]%list) regs regs'.
Proof.
  intros more fx regs m s w j p Hs Hw Hj Hp Hp2 Hmore Cw H2 H26 H25 H18.
  ex_entry regs [s; w; j; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; j; p]) m [KRange (EVar 32) 160 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 2);
                                                          KWord (SA (EVar 32) (-108)) 4 (EVar 33)]) by (ex_know regs).
  destruct more.
  - ex_run 20%nat [0x1c84c%Z; 0x1c808%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 20%nat [0x1c84c%Z; 0x1c808%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma d32_RL : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s h i lines step : Z),
  (160 <= s <= 2 ^ 47)%Z -> (0 <= i < h)%Z -> (h < 2 ^ 31)%Z -> (0 <= lines)%Z -> (0 <= step)%Z -> (lines + step < 2 ^ 63)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) -> (if more then i + 1 < h else h <= i + 1)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 23 = Z_to_bv 64 i -> getr regs 21 = Z_to_bv 64 lines -> getr regs 9 = Z_to_bv 64 step ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c808) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x1c818 else 0x1c938)) m rom)
    /\ getr regs' 23 = Z_to_bv 64 (i + 1) /\ getr regs' 21 = Z_to_bv 64 (lines + step)
    /\ regs_agree (fun r => In r [11; 21; 23]%list) regs regs'.
Proof.
  intros more fx regs m s h i lines step Hs Hi Hh Hl Hst Hl2 Ch Hmore H2 H23 H21 H9.
  ex_entry regs [s; h; i; lines; step] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h; i; lines; step]) m
                 [KRange (EVar 32) 160 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 2); KWord (SA (EVar 32) (-112)) 4 (EVar 33)]) by (ex_know regs).
  destruct more.
  - ex_run 20%nat [0x1c818%Z; 0x1c938%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 20%nat [0x1c818%Z; 0x1c938%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma d32_EX : forall (fx : FPState) regs (m : word -> option byte) (s pixd : Z),
  (160 <= s <= 2 ^ 47)%Z -> (0 <= pixd < 2 ^ 64)%Z -> rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixd) ->
  getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c938) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c724) m rom)
    /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof.
  intros fx regs m s pixd Hs Hp Cp H2.
  ex_entry regs [s; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd]) m [KRange (EVar 32) 160 (2 ^ 47); KWord (SA (EVar 32) (-160)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 20%nat [0x1c724%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma d32_PX : forall (fx : FPState) regs (m : word -> option byte) (s p pw : Z),
  (160 <= s <= 2 ^ 47)%Z -> (4096 <= p)%Z -> (p + 4 < 2 ^ 47)%Z -> (0 <= pw < 2 ^ 32)%Z ->
  rdn SEGS m (Z_to_bv 64 p) 4 = Some (Z_to_le_bytes 4 pw) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 0) -> rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 0) -> rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 0) -> rdn SEGS m (Z_to_bv 64 (s - 140)) 4 = Some (Z_to_le_bytes 4 0) ->
  store_ok SEGS m (Z_to_bv 64 (s - 152)) 12 = true ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 18 = Z_to_bv 64 p -> getr regs 8 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 1 ->
  exists regs' (v1 v2 v3 : word),
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c84c) m rom)
                (@mkst fx regs' (Z_to_bv 64 0x1c838)
                   (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 144)) (word_to_le_bytes 4 v1)) (Z_to_bv 64 (s - 148)) (word_to_le_bytes 4 v2))
                           (Z_to_bv 64 (s - 152)) (word_to_le_bytes 4 v3)) rom)
    /\ regs_agree (fun r => In r [1; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros fx regs m s p pw Hs Hp Hp2 Hpw Cp C1 C2 C3 C4 C5 C6 SOK H2 H18 H8 H22.
  ex_entry regs [s; p; pw] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; p; pw]) m
                 [KRange (EVar 32) 160 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 0 (2 ^ 32 - 1); KWord (SA (EVar 33) 0) 4 (EVar 34);
                  KWord (SA (EVar 32) (-120)) 4 (ELit 0); KWord (SA (EVar 32) (-124)) 4 (ELit 0); KWord (SA (EVar 32) (-128)) 4 (ELit 0);
                  KWord (SA (EVar 32) (-132)) 4 (ELit 0); KWord (SA (EVar 32) (-136)) 4 (ELit 0); KWord (SA (EVar 32) (-140)) 4 (ELit 0);
                  KWr (SA (EVar 32) (-152)) 12]).
  { ex_know regs. }
  ex_run 120%nat [0x1c838%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. eexists. eexists. split; [|ex_agree HR HR'].
  eapply ex_msteps_mem; [exact Hms|]. cbn [mem_denot s_log e_addr e_width e_val].
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | reflexivity ]). reflexivity.
Qed.
End Segs.
