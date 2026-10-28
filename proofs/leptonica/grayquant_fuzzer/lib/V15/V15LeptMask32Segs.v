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
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec LeptExecFP LeptExecX LeptExecA DitherLib LeptRmcLib LeptMask32Lib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Section Segs.
Variable rom : word -> option byte.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma b32_P : forall (fx : FPState) regs (m : word -> option byte) (s h wpld pixd datas datad : Z),
  (144 <= s <= 2 ^ 47)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= wpld < 2 ^ 31)%Z ->
  (4096 <= datas < 2 ^ 47)%Z -> (datas mod 4 = 0)%Z -> (4096 <= datad < 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 h) ->
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 8 = Z_to_bv 64 datas -> getr regs 18 = Z_to_bv 64 datad -> getr regs 20 = Z_to_bv 64 pixd ->
  getr regs 22 = Z_to_bv 64 18446744073709551615 -> getr regs 24 = Z_to_bv 64 18446744073709551615 -> getr regs 25 = Z_to_bv 64 18446744073709551615 ->
  getr regs 21 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 1 -> getr regs 26 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e54c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e5a8) m rom)
    /\ getr regs' 11 = Z_to_bv 64 wpld /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 1 /\ getr regs' 16 = Z_to_bv 64 1
    /\ getr regs' 6 = Z_to_bv 64 18446744073709551615 /\ getr regs' 7 = Z_to_bv 64 18446744073709551615 /\ getr regs' 28 = Z_to_bv 64 18446744073709551615
    /\ getr regs' 17 = Z_to_bv 64 1 /\ getr regs' 5 = Z_to_bv 64 1 /\ getr regs' 29 = Z_to_bv 64 1
    /\ getr regs' 30 = Z_to_bv 64 18446744071562067968 /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs'.
Proof.
  intros fx regs m s h wpld pixd datas datad Hs Hh Hwd Hds ALds Hdd Ch H2 H10 H8 H18 H20 H22 H24 H25 H21 H23 H26.
  ex_entry regs [s; h; wpld; pixd; datas; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h; wpld; pixd; datas; datad]) m
                 [KRange (EVar 32) 144 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 36) 4096 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 4096 (2 ^ 47);
                  KWord (SA (EVar 32) (-128)) 4 (EVar 33)]) by (ex_know regs).
  ex_runA 38%nat 40%nat 100%nat [0x1e5a8%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  assert (SN : forall x, (0 < x < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1) by (intros x Hx; rewrite alu_sltu; apply zbv_snez; lia).
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?SN by lia; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma b32_RH : forall (fx : FPState) regs (m : word -> option byte) (s w i wpls wpld datas datad : Z),
  (144 <= s <= 2 ^ 47)%Z -> (1 <= w <= 20000)%Z -> (0 <= i <= 20000)%Z -> (0 <= wpls <= 20000)%Z -> (0 <= wpld <= 20000)%Z ->
  (0 <= wpls * i <= 20000000)%Z -> (0 <= wpld * i <= 20000000)%Z ->
  (4096 <= datas)%Z -> (datas + 4 * (wpls * i) < 2 ^ 47)%Z -> (datas mod 4 = 0)%Z -> (4096 <= datad)%Z -> (datad + 4 * (wpld * i) < 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 13 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 (wpls * i) -> getr regs 9 = Z_to_bv 64 wpls -> getr regs 11 = Z_to_bv 64 wpld ->
  getr regs 8 = Z_to_bv 64 datas -> getr regs 18 = Z_to_bv 64 datad -> getr regs 17 = Z_to_bv 64 1 -> getr regs 5 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e5a8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e644) m rom)
    /\ getr regs' 31 = Z_to_bv 64 (datas + 4 * (wpls * i)) /\ getr regs' 19 = Z_to_bv 64 (datad + 4 * (wpld * i)) /\ getr regs' 24 = Z_to_bv 64 w
    /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 (datas + 4 * (wpls * i)) /\ getr regs' 23 = Z_to_bv 64 (datas + 4 * (wpls * i))
    /\ regs_agree (fun r => In r [19; 20; 21; 22; 23; 24; 31]%list) regs regs'.
Proof.
  intros fx regs m s w i wpls wpld datas datad Hs Hw Hi Hwpls Hwpld Psi Pdi Hds Hsrow ALds Hdd Hdrow Cw H2 H13 H12 H9 H11 H8 H18 H17 H5.
  set (psi := (wpls * i)%Z) in *. set (pdi := (wpld * i)%Z) in *.
  ex_entry regs [s; w; i; wpls; wpld; datas; datad; psi; pdi] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; i; wpls; wpld; datas; datad; psi; pdi]) m
                 [KRange (EVar 32) 144 (2 ^ 47); KRange (EVar 33) 1 20000; KRange (EVar 34) 0 20000; KRange (EVar 35) 0 20000; KRange (EVar 36) 0 20000;
                  KRange (EVar 37) 4096 (2 ^ 47); KAlign (EVar 37) 4; KRange (EVar 38) 4096 (2 ^ 47); KRange (EVar 39) 0 20000000; KRange (EVar 40) 0 20000000;
                  KWord (SA (EVar 32) (-124)) 4 (EVar 33)]).
  { ex_know regs. }
  assert (Es : (i * wpls = psi)%Z) by (unfold psi; ring). assert (Ed : (i * wpld = pdi)%Z) by (unfold pdi; ring).
  ex_runA 41%nat 40%nat 100%nat [0x1e644%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  - exact (ub_ptr_guard i wpld pdi datad Ed ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ub_mul_guard i wpld pdi Ed ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ub_ptr_guard i wpls psi datas Es ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ub_mul_guard i wpls psi Es ltac:(lia) ltac:(lia) ltac:(lia)).
  - exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?m_mul, ?zbv_mul, ?w_addw, ?Es, ?Ed, ?zbv_addw_small, ?zbv_mul, ?alu_add, ?zbv_add by lia; try reflexivity; try (f_equal; lia).
Qed.

(* [comment removed for export] *)
Lemma b32_PL : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (w j p : Z),
  (1 <= w < 2 ^ 31)%Z -> (0 <= j < w)%Z -> (0 <= p)%Z -> (p + 4 < 2 ^ 63)%Z -> (if more then j + 1 < w else w <= j + 1)%Z ->
  getr regs 24 = Z_to_bv 64 w -> getr regs 21 = Z_to_bv 64 j -> getr regs 20 = Z_to_bv 64 j -> getr regs 22 = Z_to_bv 64 p -> getr regs 23 = Z_to_bv 64 p ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e630) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x1e644 else 0x1e598)) m rom)
    /\ getr regs' 21 = Z_to_bv 64 (j + 1) /\ getr regs' 20 = Z_to_bv 64 (j + 1) /\ getr regs' 22 = Z_to_bv 64 (p + 4) /\ getr regs' 23 = Z_to_bv 64 (p + 4)
    /\ regs_agree (fun r => In r [20; 21; 22; 23]%list) regs regs'.
Proof.
  intros more fx regs m w j p Hw Hj Hp Hp2 Hmore H24 H21 H20 H22 H23.
  ex_entry regs [w; j; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [w; j; p]) m [KRange (EVar 32) 1 (2 ^ 31 - 1); KRange (EVar 33) 0 (2 ^ 31 - 2)]) by (ex_know regs).
  destruct more.
  - ex_run 20%nat [0x1e644%Z; 0x1e598%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 20%nat [0x1e644%Z; 0x1e598%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma b32_RL : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s h i acc wpls : Z),
  (144 <= s <= 2 ^ 47)%Z -> (0 <= i < h)%Z -> (h < 2 ^ 31)%Z -> (0 <= acc)%Z -> (0 <= wpls)%Z -> (acc + wpls < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 h) -> (if more then i + 1 < h else h <= i + 1)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 13 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 acc -> getr regs 9 = Z_to_bv 64 wpls ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e598) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x1e5a8 else 0x1e368)) m rom)
    /\ getr regs' 13 = Z_to_bv 64 (i + 1) /\ getr regs' 12 = Z_to_bv 64 (acc + wpls)
    /\ regs_agree (fun r => In r [12; 13; 31]%list) regs regs'.
Proof.
  intros more fx regs m s h i acc wpls Hs Hi Hh Ha Hws Haw Ch Hmore H2 H13 H12 H9.
  ex_entry regs [s; h; i; acc; wpls] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h; i; acc; wpls]) m
                 [KRange (EVar 32) 144 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 2); KWord (SA (EVar 32) (-128)) 4 (EVar 33)]) by (ex_know regs).
  destruct more.
  - ex_run 20%nat [0x1e5a8%Z; 0x1e368%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    { rewrite ?w_addw, ?zbv_addw_small by lia. ex_br. }
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?w_addw, ?zbv_addw_small by lia; try reflexivity; try (f_equal; lia).
  - ex_run 20%nat [0x1e5a8%Z; 0x1e368%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    { rewrite ?w_addw, ?zbv_addw_small by lia. ex_br. }
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?w_addw, ?zbv_addw_small by lia; try reflexivity; try (f_equal; lia).
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

Lemma b32_PX : forall (fx : FPState) regs (m : word -> option byte) (s w j srow p drow datad pw : Z) (bsd : list byte),
  (144 <= s <= 2 ^ 47)%Z -> (1 <= w < 2 ^ 31)%Z -> (0 <= j < w)%Z -> (4096 <= srow)%Z -> (srow <= p)%Z -> (p + 4 < 2 ^ 47)%Z -> (p mod 4 = 0)%Z ->
  (4096 <= datad < 2 ^ 47)%Z -> (4096 <= drow)%Z -> (drow + 4 * (j / 32) + 4 < 2 ^ 47)%Z -> (drow mod 4 = 0)%Z ->
  (0 <= pw < 2 ^ 32)%Z ->
  rdn SEGS m (Z_to_bv 64 p) 4 = Some (Z_to_le_bytes 4 pw) -> rdn SEGS m (Z_to_bv 64 (drow + 4 * (j / 32))) 4 = Some bsd ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 w) ->
  store_ok SEGS m (Z_to_bv 64 (drow + 4 * (j / 32))) 4 = true ->
  (drow + 4 * (j / 32) + 4 <= s - 144 \/ s <= drow + 4 * (j / 32))%Z ->
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 24 = Z_to_bv 64 w -> getr regs 21 = Z_to_bv 64 j -> getr regs 20 = Z_to_bv 64 j ->
  getr regs 22 = Z_to_bv 64 p -> getr regs 23 = Z_to_bv 64 p -> getr regs 31 = Z_to_bv 64 srow -> getr regs 19 = Z_to_bv 64 drow -> getr regs 18 = Z_to_bv 64 datad ->
  getr regs 30 = Z_to_bv 64 18446744071562067968 -> getr regs 17 = Z_to_bv 64 1 -> getr regs 5 = Z_to_bv 64 1 -> getr regs 29 = Z_to_bv 64 1 ->
  getr regs 6 = Z_to_bv 64 18446744073709551615 -> getr regs 7 = Z_to_bv 64 18446744073709551615 -> getr regs 28 = Z_to_bv 64 18446744073709551615 ->
  getr regs 16 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e644) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e630) M' rom)
    /\ (M' = m \/ exists v : word, M' = wbytes m (Z_to_bv 64 (drow + 4 * (j / 32))) (word_to_le_bytes 4 v))
    /\ getr regs' 24 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [24; 25; 26]%list) regs regs'.
Proof.
  intros fx regs m s w j srow p drow datad pw bsd Hs Hw Hj Hsr Hsp Hp2 ALp Hdd Hdr Hdr2 ALdr Hpw Cp Cd Cw SOK AP
         H2 H24 H21 H20 H22 H23 H31 H19 H18 H30 H17 H5 H29 H6 H7 H28 H16 H15 H14.
  pose proof (px_r_range pw Hpw) as Rr. pose proof (px_m_range 40 pw) as Rg. pose proof (px_m_range 48 pw) as Rb.
  ex_entry regs [s; w; j; srow; p; drow; datad; pw; rdv true 4 bsd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; j; srow; p; drow; datad; pw; rdv true 4 bsd]) m
                 [KRange (EVar 32) 144 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 2); KRange (EVar 35) 4096 (2 ^ 47);
                  KRange (EVar 36) 4096 (2 ^ 47); KAlign (EVar 36) 4; KRange (EVar 37) 4096 (2 ^ 47); KAlign (EVar 37) 4; KRange (EVar 38) 4096 (2 ^ 47);
                  KRange (EVar 39) 0 (2 ^ 32 - 1); KWord (SA (EVar 32) (-124)) 4 (EVar 33); KWord (SA (EVar 36) 0) 4 (EVar 39)]).
  { ex_know regs. }
  assert (XD : alu64 ALU_ADD (Z_to_bv 64 drow) (mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 5)))))
               = Z_to_bv 64 (drow + 4 * (j / 32))) by (apply dl_bitword_w; lia).
  pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as (D1 & D2).
  destruct (Z_lt_ge_dec 1 (px_r pw)) as [R1|R1].
  { ex_runA 40%nat 60%nat 100%nat [0x1e630%Z] (SCR [false; true] [] []) HR HK R' HR' Hms.
    - px_sc Hpw R1 R1 R1.
    - exists R', m. split; [ex_mem2 regs Hms|]. split; [left; reflexivity|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext. }
  destruct (Z_lt_ge_dec 1 (px_m 40 pw)) as [R2|R2].
  { ex_runA 40%nat 60%nat 100%nat [0x1e630%Z] (SCR [false; false; false; true] [] []) HR HK R' HR' Hms.
    - px_sc Hpw R1 R2 R2.
    - px_sc Hpw R1 R2 R2.
    - px_sc Hpw R1 R2 R2.
    - exists R', m. split; [ex_mem2 regs Hms|]. split; [left; reflexivity|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext. }
  destruct (Z_lt_ge_dec 1 (px_m 48 pw)) as [R3|R3].
  { ex_runA 40%nat 60%nat 100%nat [0x1e630%Z] (SCR [false; false; false; false; false; true] [] []) HR HK R' HR' Hms.
    - px_sc Hpw R1 R2 R3.
    - px_sc Hpw R1 R2 R3.
    - px_sc Hpw R1 R2 R3.
    - px_sc Hpw R1 R2 R3.
    - px_sc Hpw R1 R2 R3.
    - exists R', m. split; [ex_mem2 regs Hms|]. split; [left; reflexivity|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext. }
  ex_runA 40%nat 60%nat 100%nat [0x1e630%Z] (SCR [false; false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
  - rewrite XD. rewrite !u_Z2bv by lia. clear - Hs AP Hdr Hdr2 D1. lia.
  - rewrite XD, zbv_addi, Z.add_0_r. exact SOK.
  - exx_named (drow + 4 * (j / 32))%Z Cd ltac:(rewrite XD, zbv_addi; f_equal; lia).
  - rewrite XD. ex_br.
  - px_sc Hpw R1 R2 R3.
  - px_sc Hpw R1 R2 R3.
  - px_sc Hpw R1 R2 R3.
  - px_sc Hpw R1 R2 R3.
  - px_sc Hpw R1 R2 R3.
  - lazymatch type of Hms with msteps _ _ (mkst _ _ ?MM _) => exists R', MM end. split; [exact Hms|]. split.
    + right. eexists. cbn [mem_denot s_log e_addr e_width e_val]. apply ex_wbytes_eq; [reflexivity | | reflexivity].
      ex_unfoldE. unfold adenot. cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite ?H19, ?H21, XD, zbv_addi. f_equal. lia.
    + repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition D32P (m : word -> option byte) (s wpld pixd datas wpls : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 wpld)))
    (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
    (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 168)) (word_to_le_bytes 8 (Z_to_bv 64 datas)))
    (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (Z_to_bv 64 wpls)).

(* [comment removed for export] *)
Lemma d32_P : forall (fx : FPState) regs (m : word -> option byte) (s h wpld wpls pixd datas datad : Z),
  (208 <= s <= 2 ^ 47)%Z -> (1 <= h < 2 ^ 31)%Z -> (4096 <= datas < 2 ^ 47)%Z -> (datas mod 4 = 0)%Z -> (4096 <= datad < 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 200)) 60 = true ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 20 = Z_to_bv 64 datas -> getr regs 19 = Z_to_bv 64 wpls -> getr regs 21 = Z_to_bv 64 datad ->
  getr regs 18 = Z_to_bv 64 pixd ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e8c4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e920) (D32P m s wpld pixd datas wpls) rom)
    /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 1 /\ getr regs' 26 = Z_to_bv 64 1 /\ getr regs' 27 = Z_to_bv 64 1
    /\ getr regs' 9 = Z_to_bv 64 18446744071562067968
    /\ regs_agree (fun r => In r [9; 10; 11; 12; 25; 26; 27]%list) regs regs'.
Proof.
  intros fx regs m s h wpld wpls pixd datas datad Hs Hh Hds ALds Hdd Ch SOK H2 H10 H20 H19 H21 H18.
  ex_entry regs [s; h; wpld; wpls; pixd; datas; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h; wpld; wpls; pixd; datas; datad]) m
                 [KRange (EVar 32) 208 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 37) 4096 (2 ^ 47); KAlign (EVar 37) 4; KRange (EVar 38) 4096 (2 ^ 47);
                  KWord (SA (EVar 32) (-112)) 4 (EVar 33); KWr (SA (EVar 32) (-200)) 60]) by (ex_know regs).
  ex_runA 39%nat 40%nat 100%nat [0x1e920%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold D32P; ex_mem2 regs Hms|].
  assert (SN : forall x, (0 < x < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1) by (intros x Hx; rewrite alu_sltu; apply zbv_snez; lia).
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?SN by lia; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma d32_RH : forall (fx : FPState) regs (m : word -> option byte) (s w i wpls wpld datas datad : Z),
  (208 <= s <= 2 ^ 47)%Z -> (1 <= w <= 20000)%Z -> (0 <= i <= 20000)%Z -> (0 <= wpls <= 20000)%Z -> (0 <= wpld <= 20000)%Z ->
  (0 <= wpls * i <= 20000000)%Z -> (0 <= wpld * i <= 20000000)%Z ->
  (4096 <= datas)%Z -> (datas + 4 * (wpls * i) < 2 ^ 47)%Z -> (datas mod 4 = 0)%Z -> (4096 <= datad)%Z -> (datad + 4 * (wpld * i) < 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 datas) ->
  rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 wpld) -> rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 (wpls * i)) ->
  store_ok SEGS m (Z_to_bv 64 (s - 200)) 60 = true ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 12 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 wpls -> getr regs 21 = Z_to_bv 64 datad ->
  getr regs 25 = Z_to_bv 64 1 -> getr regs 26 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e920) m rom)
                (@mkst fx regs' (Z_to_bv 64 0x1e9dc) (wbytes m (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 i))) rom)
    /\ getr regs' 18 = Z_to_bv 64 (datas + 4 * (wpls * i)) /\ getr regs' 20 = Z_to_bv 64 (datad + 4 * (wpld * i))
    /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 23 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 (datas + 4 * (wpls * i)) /\ getr regs' 24 = Z_to_bv 64 (datas + 4 * (wpls * i))
    /\ regs_agree (fun r => In r [10; 11; 12; 18; 19; 20; 22; 23; 24]%list) regs regs'.
Proof.
  intros fx regs m s w i wpls wpld datas datad Hs Hw Hi Hwpls Hwpld Psi Pdi Hds Hsrow ALds Hdd Hdrow Cw Cds Cwd Cacc SOK H2 H12 H19 H21 H25 H26.
  set (psi := (wpls * i)%Z) in *. set (pdi := (wpld * i)%Z) in *.
  ex_entry regs [s; w; i; wpls; wpld; datas; datad; psi; pdi] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; i; wpls; wpld; datas; datad; psi; pdi]) m
                 [KRange (EVar 32) 208 (2 ^ 47); KRange (EVar 33) 1 20000; KRange (EVar 34) 0 20000; KRange (EVar 35) 0 20000; KRange (EVar 36) 0 20000;
                  KRange (EVar 37) 4096 (2 ^ 47); KAlign (EVar 37) 4; KRange (EVar 38) 4096 (2 ^ 47); KRange (EVar 39) 0 20000000; KRange (EVar 40) 0 20000000;
                  KWord (SA (EVar 32) (-108)) 4 (EVar 33); KWord (SA (EVar 32) (-168)) 8 (EVar 37); KWord (SA (EVar 32) (-184)) 8 (EVar 36);
                  KWord (SA (EVar 32) (-176)) 8 (EVar 39); KWr (SA (EVar 32) (-200)) 60]).
  { ex_know regs. }
  assert (Es : (i * wpls = psi)%Z) by (unfold psi; ring). assert (Ed : (i * wpld = pdi)%Z) by (unfold pdi; ring).
  ex_runA 41%nat 40%nat 100%nat [0x1e9dc%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
  - exact (ub_ptr_guard i wpld pdi datad Ed ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ub_mul_guard i wpld pdi Ed ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ub_ptr_guard i wpls psi datas Es ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ub_mul_guard i wpls psi Es ltac:(lia) ltac:(lia) ltac:(lia)).
  - exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?m_mul, ?zbv_mul, ?w_addw, ?Es, ?Ed, ?zbv_addw_small, ?zbv_mul, ?alu_add, ?zbv_add by lia; try reflexivity; try (f_equal; lia).
Qed.

(* [comment removed for export] *)
Lemma d32_PL : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s w j p : Z),
  (208 <= s <= 2 ^ 47)%Z -> (1 <= w < 2 ^ 31)%Z -> (0 <= j < w)%Z -> (0 <= p)%Z -> (p + 4 < 2 ^ 63)%Z -> (if more then j + 1 < w else w <= j + 1)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 23 = Z_to_bv 64 j -> getr regs 19 = Z_to_bv 64 j -> getr regs 22 = Z_to_bv 64 p -> getr regs 24 = Z_to_bv 64 p ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e9c4) m rom) (@mkst fx regs' (Z_to_bv 64 (if more then 0x1e9dc else 0x1e900)) m rom)
    /\ getr regs' 23 = Z_to_bv 64 (j + 1) /\ getr regs' 19 = Z_to_bv 64 (j + 1) /\ getr regs' 22 = Z_to_bv 64 (p + 4) /\ getr regs' 24 = Z_to_bv 64 (p + 4)
    /\ regs_agree (fun r => In r [10; 19; 22; 23; 24]%list) regs regs'.
Proof.
  intros more fx regs m s w j p Hs Hw Hj Hp Hp2 Hmore Cw H2 H23 H19 H22 H24.
  ex_entry regs [s; w; j; p] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; j; p]) m [KRange (EVar 32) 208 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 2);
                                                          KWord (SA (EVar 32) (-108)) 4 (EVar 33)]) by (ex_know regs).
  destruct more.
  - ex_run 20%nat [0x1e9dc%Z; 0x1e900%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 20%nat [0x1e9dc%Z; 0x1e900%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma d32_RL : forall (more : bool) (fx : FPState) regs (m : word -> option byte) (s h i acc wpls : Z),
  (208 <= s <= 2 ^ 47)%Z -> (0 <= i < h)%Z -> (h < 2 ^ 31)%Z -> (0 <= acc)%Z -> (0 <= wpls)%Z -> (acc + wpls < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 i) ->
  rdn SEGS m (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 wpls) -> rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 acc) ->
  store_ok SEGS m (Z_to_bv 64 (s - 200)) 60 = true ->
  (if more then i + 1 < h else h <= i + 1)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e900) m rom)
                (@mkst fx regs' (Z_to_bv 64 (if more then 0x1e920 else 0x1ebf0)) (wbytes m (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 (acc + wpls)))) rom)
    /\ getr regs' 12 = Z_to_bv 64 (i + 1) /\ getr regs' 19 = Z_to_bv 64 wpls
    /\ regs_agree (fun r => In r [10; 11; 12; 19]%list) regs regs'.
Proof.
  intros more fx regs m s h i acc wpls Hs Hi Hh Ha Hws Haw Ch Ci Cws Cacc SOK Hmore H2.
  ex_entry regs [s; h; i; acc; wpls] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h; i; acc; wpls]) m
                 [KRange (EVar 32) 208 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 2); KWord (SA (EVar 32) (-112)) 4 (EVar 33);
                  KWord (SA (EVar 32) (-160)) 8 (EVar 34); KWord (SA (EVar 32) (-192)) 8 (EVar 36); KWord (SA (EVar 32) (-176)) 8 (EVar 35);
                  KWr (SA (EVar 32) (-200)) 60]) by (ex_know regs).
  destruct more.
  - ex_run 20%nat [0x1e920%Z; 0x1ebf0%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    { rewrite ?w_addw, ?zbv_addw_small by lia. ex_br. }
    exists R'. split.
    { eapply ex_msteps_mem; [exact Hms|]. cbn [mem_denot s_log e_addr e_width e_val]. apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | ].
      ex_unfoldE. cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite w_addw, zbv_addw_small by lia. reflexivity. }
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?w_addw, ?zbv_addw_small by lia; try reflexivity; try (f_equal; lia).
  - ex_run 20%nat [0x1e920%Z; 0x1ebf0%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    { rewrite ?w_addw, ?zbv_addw_small by lia. ex_br. }
    exists R'. split.
    { eapply ex_msteps_mem; [exact Hms|]. cbn [mem_denot s_log e_addr e_width e_val]. apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | ].
      ex_unfoldE. cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite w_addw, zbv_addw_small by lia. reflexivity. }
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?w_addw, ?zbv_addw_small by lia; try reflexivity; try (f_equal; lia).
Qed.

(* [comment removed for export] *)
Lemma d32_EX : forall (fx : FPState) regs (m : word -> option byte) (s pixd : Z),
  (208 <= s <= 2 ^ 47)%Z -> (0 <= pixd < 2 ^ 64)%Z -> rdn SEGS m (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 pixd) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ebf0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e808) m rom)
    /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof.
  intros fx regs m s pixd Hs Hp Cp H2.
  ex_entry regs [s; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd]) m [KRange (EVar 32) 208 (2 ^ 47); KWord (SA (EVar 32) (-200)) 8 (EVar 33)]) by (ex_know regs).
  ex_run 20%nat [0x1e808%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Definition D32C (m : word -> option byte) (s vr vg vb : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 144)) (Z_to_le_bytes 4 vr)) (Z_to_bv 64 (s - 148)) (Z_to_le_bytes 4 vg)) (Z_to_bv 64 (s - 152)) (Z_to_le_bytes 4 vb).

Lemma d32_PXa : forall (fx : FPState) regs (m : word -> option byte) (s srow p pw : Z),
  (208 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z -> (4096 <= srow)%Z -> (srow <= p)%Z -> (p + 4 < 2 ^ 47)%Z -> (p mod 4 = 0)%Z -> (0 <= pw < 2 ^ 32)%Z ->
  rdn SEGS m (Z_to_bv 64 p) 4 = Some (Z_to_le_bytes 4 pw) ->
  store_ok SEGS m (Z_to_bv 64 (s - 200)) 60 = true ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 22 = Z_to_bv 64 p -> getr regs 24 = Z_to_bv 64 p -> getr regs 18 = Z_to_bv 64 srow ->
  getr regs 25 = Z_to_bv 64 1 -> getr regs 27 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e9dc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ea04) (D32C m s (px_r pw) (px_m 40 pw) (px_m 48 pw)) rom)
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros fx regs m s srow p pw Hs Hs16 Hsr Hsp Hp2 ALp Hpw Cp SOK H2 H22 H24 H18 H25 H27.
  pose proof (px_r_range pw Hpw) as Rr. pose proof (px_m_range 40 pw) as Rg. pose proof (px_m_range 48 pw) as Rb.
  destruct (sx32_val pw Hpw) as (spw & Esx & Rspw & Mspw).
  ex_entry regs [s; srow; p; pw] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; srow; p; pw]) m
                 [KRange (EVar 32) 208 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47); KAlign (EVar 34) 4;
                  KRange (EVar 35) 0 (2 ^ 32 - 1); KWord (SA (EVar 34) 0) 4 (EVar 35); KWr (SA (EVar 32) (-200)) 60]).
  { ex_know regs. }
  ex_runA 36%nat 40%nat 100%nat [0x1ea04%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. split; [|ex_agree HR HR'].
  eapply ex_msteps_mem; [exact Hms|]. unfold D32C. cbn [mem_denot s_log e_addr e_width e_val].
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | ]); [reflexivity | | | ];
    ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; rewrite Esx.
  - rewrite srlw24_sx by lia. rewrite Mspw. symmetry. apply w2b_Z. lia.
  - change 1099511627776%Z with (2 ^ 40)%Z. rewrite px_m_eq by lia. rewrite (px_m_sx 40 spw) by lia. rewrite Mspw. symmetry. apply w2b_Z. lia.
  - change 281474976710656%Z with (2 ^ 48)%Z. rewrite px_m_eq by lia. rewrite (px_m_sx 48 spw) by lia. rewrite Mspw. symmetry. apply w2b_Z. lia.
Qed.

(* [comment removed for export] *)
Ltac d32_sc :=
  rewrite ?ex_sx32 by lia; rewrite ?m_mul, ?zbv_mul;
  repeat match goal with |- context [(-1 * ?v)%Z] => replace (-1 * v)%Z with (- v)%Z by lia end;
  rewrite ?sextw_neg, ?subw0_Z by lia;
  lazymatch goal with
  | |- branch_taken BC_GE _ (Z_to_bv 64 0) = false => rewrite bgez_neg by lia; apply Z.eqb_neq; lia
  | |- branch_taken BC_NE ?x ?x = false => cbn [branch_taken]; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity
  | |- branch_taken BC_EQ (Z_to_bv 64 (- ?v)) _ = false =>
      cbn [branch_taken]; unfold bv_eqb; rewrite u_neg by lia; destruct (Z.eqb_spec v 0); [lia|]; rewrite u_Z2bv by lia; apply Z.eqb_neq; lia
  end.

(* [comment removed for export] *)
Lemma d32_PXr : forall (fx : FPState) regs (m : word -> option byte) (s v : Z),
  (208 <= s <= 2 ^ 47)%Z -> (0 <= v <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 0) -> rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 4 = Some (Z_to_le_bytes 4 v) ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 18446744071562067968 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 125444) m rom) (@mkst fx regs' (Z_to_bv 64 125524) m rom)
    /\ getr regs' 10 = Z_to_bv 64 v /\ getr regs' 11 = Z_to_bv 64 v
    /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
Proof.
  intros fx regs m s v Hs Hv C1 C2 Cv H2 H8 H9.
  destruct (Z.eq_dec v 0) as [->|NZ].
  - ex_entry regs [s] HR.
    assert (HK : know_ok SEGS (ex_env regs [s]) m
                   [KRange (EVar 32) 208 (2 ^ 47); KWord (SA (EVar 32) (-120)) 4 (ELit 0); KWord (SA (EVar 32) (-132)) 4 (ELit 0); KWord (SA (EVar 32) (-144)) 4 (ELit 0)]).
    { ex_know regs. }
    ex_runA 33%nat 40%nat 100%nat [125524%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_entry regs [s; v] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; v]) m
                   [KRange (EVar 32) 208 (2 ^ 47); KRange (EVar 33) 1 255; KWord (SA (EVar 32) (-120)) 4 (ELit 0); KWord (SA (EVar 32) (-132)) 4 (ELit 0);
                    KWord (SA (EVar 32) (-144)) 4 (EVar 33)]).
    { ex_know regs. }
    ex_runA 34%nat 40%nat 100%nat [125524%Z] (SCR [false; false; false; false; false] [] []) HR HK R' HR' Hms.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; rewrite ?ex_sx32 by lia; rewrite ?m_mul, ?zbv_mul;
        repeat match goal with |- context [(-1 * ?x)%Z] => replace (-1 * x)%Z with (- x)%Z by lia end;
        rewrite <- ?w_subw, <- ?w_addw; rewrite ?sextw_neg, ?subw0_Z by lia; rewrite ?negw_neg by lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma d32_PXg : forall (fx : FPState) regs (m : word -> option byte) (s v : Z),
  (208 <= s <= 2 ^ 47)%Z -> (0 <= v <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 0) -> rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 v) ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 18446744071562067968 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 125524) m rom) (@mkst fx regs' (Z_to_bv 64 125584) m rom)
    /\ getr regs' 12 = Z_to_bv 64 v /\ getr regs' 13 = Z_to_bv 64 v
    /\ regs_agree (fun r => In r [12; 13; 14; 15]%list) regs regs'.
Proof.
  intros fx regs m s v Hs Hv C1 C2 Cv H2 H8 H9.
  destruct (Z.eq_dec v 0) as [->|NZ].
  - ex_entry regs [s] HR.
    assert (HK : know_ok SEGS (ex_env regs [s]) m
                   [KRange (EVar 32) 208 (2 ^ 47); KWord (SA (EVar 32) (-124)) 4 (ELit 0); KWord (SA (EVar 32) (-136)) 4 (ELit 0); KWord (SA (EVar 32) (-148)) 4 (ELit 0)]).
    { ex_know regs. }
    ex_runA 33%nat 40%nat 100%nat [125584%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_entry regs [s; v] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; v]) m
                   [KRange (EVar 32) 208 (2 ^ 47); KRange (EVar 33) 1 255; KWord (SA (EVar 32) (-124)) 4 (ELit 0); KWord (SA (EVar 32) (-136)) 4 (ELit 0);
                    KWord (SA (EVar 32) (-148)) 4 (EVar 33)]).
    { ex_know regs. }
    ex_runA 34%nat 40%nat 100%nat [125584%Z] (SCR [false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; rewrite ?ex_sx32 by lia; rewrite ?m_mul, ?zbv_mul;
        repeat match goal with |- context [(-1 * ?x)%Z] => replace (-1 * x)%Z with (- x)%Z by lia end;
        rewrite <- ?w_subw, <- ?w_addw; rewrite ?sextw_neg, ?subw0_Z by lia; rewrite ?negw_neg by lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma d32_PXb : forall (fx : FPState) regs (m : word -> option byte) (s v : Z),
  (208 <= s <= 2 ^ 47)%Z -> (0 <= v <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 0) -> rdn SEGS m (Z_to_bv 64 (s - 140)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 v) ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 18446744071562067968 ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 125584) m rom) (@mkst fx regs' (Z_to_bv 64 125644) m rom)
    /\ getr regs' 14 = Z_to_bv 64 v /\ getr regs' 16 = Z_to_bv 64 v
    /\ regs_agree (fun r => In r [14; 15; 16; 17]%list) regs regs'.
Proof.
  intros fx regs m s v Hs Hv C1 C2 Cv H2 H8 H9.
  destruct (Z.eq_dec v 0) as [->|NZ].
  - ex_entry regs [s] HR.
    assert (HK : know_ok SEGS (ex_env regs [s]) m
                   [KRange (EVar 32) 208 (2 ^ 47); KWord (SA (EVar 32) (-128)) 4 (ELit 0); KWord (SA (EVar 32) (-140)) 4 (ELit 0); KWord (SA (EVar 32) (-152)) 4 (ELit 0)]).
    { ex_know regs. }
    ex_runA 33%nat 40%nat 100%nat [125644%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_entry regs [s; v] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; v]) m
                   [KRange (EVar 32) 208 (2 ^ 47); KRange (EVar 33) 1 255; KWord (SA (EVar 32) (-128)) 4 (ELit 0); KWord (SA (EVar 32) (-140)) 4 (ELit 0);
                    KWord (SA (EVar 32) (-152)) 4 (EVar 33)]).
    { ex_know regs. }
    ex_runA 34%nat 40%nat 100%nat [125644%Z] (SCR [false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + d32_sc.
    + exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; rewrite ?ex_sx32 by lia; rewrite ?m_mul, ?zbv_mul;
        repeat match goal with |- context [(-1 * ?x)%Z] => replace (-1 * x)%Z with (- x)%Z by lia end;
        rewrite <- ?w_subw, <- ?w_addw; rewrite ?sextw_neg, ?subw0_Z by lia; rewrite ?negw_neg by lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma d32_PXf : forall (fx : FPState) regs (m : word -> option byte) (vr vg vb : Z),
  (0 <= vr <= 255)%Z -> (0 <= vg <= 255)%Z -> (0 <= vb <= 255)%Z ->
  getr regs 10 = Z_to_bv 64 vr -> getr regs 11 = Z_to_bv 64 vr -> getr regs 12 = Z_to_bv 64 vg -> getr regs 13 = Z_to_bv 64 vg ->
  getr regs 14 = Z_to_bv 64 vb -> getr regs 16 = Z_to_bv 64 vb ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eacc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1e9c4) m rom)
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof.
  intros fx regs m vr vg vb Hr Hg Hb H10 H11 H12 H13 H14 H16.
  ex_entry regs [vr; vg; vb] HR.
  assert (HK : know_ok SEGS (ex_env regs [vr; vg; vb]) m [KRange (EVar 32) 0 255; KRange (EVar 33) 0 255; KRange (EVar 34) 0 255]) by (ex_know regs).
  ex_runA 35%nat 40%nat 100%nat [0x1e9c4%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem2 regs Hms | ex_agree HR HR'].
Qed.
End Segs.
