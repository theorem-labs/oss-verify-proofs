(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecW LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23ExecUb V23LeptBase V23LeptRop.
Import SX2. Import SX2S.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition RLC_P : word := 0x7fc9c.
Definition RLC_A1 : word := 0x7fd10.
Definition RLC_X2 : word := 0x7fdec.
Definition RLC_X3 : word := 0x7fe30.
Definition RLC_A2 : word := 0x7fe74.
Definition RLC_Y2 : word := 0x7fee8.
Definition RLC_Y3 : word := 0x7ff28.
Definition RLC_W : word := 0x7ff68.
Definition RLC_H : word := 0x7ff74.
Definition RLC_D : word := 0x7ff84.
Definition RLC_E : word := 0x875b8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sx32_Z : forall z : Z, (- 2 ^ 31 <= z < 2 ^ 31)%Z -> ext_val true 0 4 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold ext_val, ext_Z. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_nat N.of_nat Z.of_N Pos.of_succ_nat Pos.succ Z.mul N.mul].
  rewrite Z.pow_0_r, Z.div_1_r. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma br_eq_Z : forall e1 e2 : Z, e1 = e2 -> Sem.branch_taken BC_EQ (Z_to_bv 64 e1) (Z_to_bv 64 e2) = true.
Proof. intros e1 e2 E. subst e2. cbn [Sem.branch_taken]. unfold bv_eqb. apply Z.eqb_eq. reflexivity. Qed.

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma rl_A0g : forall regs m (s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy : Z) (ret : word),
  (240 <= s)%Z -> (s + 64 < 2 ^ 64)%Z ->
  (- 2 ^ 31 <= dpixw < 2 ^ 31)%Z -> (- 2 ^ 31 <= dpixh < 2 ^ 31)%Z -> (- 2 ^ 31 <= dx < 2 ^ 31)%Z -> (- 2 ^ 31 <= dy < 2 ^ 31)%Z ->
  (- 2 ^ 31 <= dw < 2 ^ 31)%Z -> (- 2 ^ 31 <= dh < 2 ^ 31)%Z -> (- 2 ^ 31 <= op < 2 ^ 31)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  (- 2 ^ 31 <= spixw < 2 ^ 31)%Z -> (- 2 ^ 31 <= spixh < 2 ^ 31)%Z -> (- 2 ^ 31 <= swpl < 2 ^ 31)%Z ->
  (- 2 ^ 31 <= sx < 2 ^ 31)%Z -> (- 2 ^ 31 <= sy < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw ->
  getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  exists regs',
    msteps SEGS (mkst regs RLC_P m rom) (mkst regs' RLC_A1 (RLF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 5 = Z_to_bv 64 dpixw /\ getr regs' 6 = Z_to_bv 64 swpl
    /\ getr regs' 8 = Z_to_bv 64 dw /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 19 = Z_to_bv 64 datas /\ getr regs' 20 = Z_to_bv 64 sx /\ getr regs' 21 = Z_to_bv 64 dpixw
    /\ getr regs' 22 = Z_to_bv 64 dh /\ getr regs' 23 = Z_to_bv 64 dpixh /\ getr regs' 26 = Z_to_bv 64 sy
    /\ getr regs' 28 = Z_to_bv 64 spixh /\ getr regs' 29 = Z_to_bv 64 spixw /\ getr regs' 30 = Z_to_bv 64 dx
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 8; 11; 12; 19; 20; 21; 22; 23; 26; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret Hs Hs64
    R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 SOK A0 A1 A2 A3 A4 A5 A6 A7 H2 H1 H10 H11 H12 H13 H14 H15 H16 H17.
  unfold RLC_P, RLC_A1.
  replace (0x7fc9c : word) with (Z_to_bv 64 0x7fc9c) by (apply bv_eq; reflexivity).
  replace (0x7fd10 : word) with (Z_to_bv 64 0x7fd10) by (apply bv_eq; reflexivity).
  ex_entry regs [s; dh; op; datas; spixw; spixh; swpl; sx; sy] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; dh; op; datas; spixw; spixh; swpl; sx; sy]) m
                 [KWr (SA (EVar 32) (-112)) 112; KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34);
                  KWord (SA (EVar 32) 16) 8 (EVar 35); KWord (SA (EVar 32) 24) 8 (EVar 36); KWord (SA (EVar 32) 32) 8 (EVar 37);
                  KWord (SA (EVar 32) 40) 8 (EVar 38); KWord (SA (EVar 32) 48) 8 (EVar 39); KWord (SA (EVar 32) 56) 8 (EVar 40)]%Z)
    by (ex_know regs).
  ex_run 200%nat [0x7fd10%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold RLF. subst ret. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (ex_agree HR HR'); try (apply sx32_Z; lia).
Qed.

Ltac rlc_norm := repeat first [ rewrite w_addw | rewrite w_subw | rewrite addw_fit by lia | rewrite subw_fit by lia
  | rewrite ex_ptr_val | rewrite alu_add | rewrite alu_sub | rewrite zbv_add | rewrite zbv_sub | rewrite m_mul | rewrite zbv_mul ].
Ltac rlc_sc := rlc_norm; first [ apply br_eq_Z; lia | ex_br ].
Ltac rlc_val := first [ reflexivity | (rlc_norm; f_equal; lia) ].
Ltac rlc_bytes regs :=
  first [ reflexivity | (f_equal; ex_val regs; rlc_val) | (rewrite <- w2b_Z by lia; f_equal; ex_val regs; rlc_val) ].
Ltac rlc_mem regs Hms :=
  eapply ex_msteps_mem; [exact Hms | cbn [mem_denot s_log e_addr e_width e_val];
    repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | rlc_bytes regs ]); reflexivity].
Ltac rlc_tail regs HR HR' Hms :=
  lazymatch type of HR' with regs_ok _ _ ?R => exists R end;
  split; [rlc_mem regs Hms | unfold clip_w2, clip_d, clip_s; repeat split; try (ex_reg regs HR'); try (ex_agree HR HR');
                           try solve [rlc_val]].
Ltac rlc_fin regs HR HR' Hms := rlc_tail regs HR HR' Hms.

Lemma rl_X1 : forall regs m (dx sx dw dpw : Z),
  (- 2 ^ 24 <= dx <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sx <= 2 ^ 24)%Z -> (0 <= dw <= 2 ^ 24)%Z ->
  getr regs 5 = Z_to_bv 64 dpw -> getr regs 8 = Z_to_bv 64 dw -> getr regs 15 = Z_to_bv 64 dx -> getr regs 17 = Z_to_bv 64 dw ->
  getr regs 20 = Z_to_bv 64 sx -> getr regs 30 = Z_to_bv 64 dx ->
  exists regs',
    msteps SEGS (mkst regs RLC_A1 m rom) (mkst regs' RLC_X2 m rom)
    /\ getr regs' 8 = Z_to_bv 64 (clip_w2 dx sx dw) /\ getr regs' 25 = Z_to_bv 64 (clip_d dx sx)
    /\ getr regs' 27 = Z_to_bv 64 (clip_s dx sx)
    /\ regs_agree (fun r => In r [8; 12; 13; 15; 17; 25; 27; 31]%list) regs regs'.
Proof.
  intros regs m dx sx dw dpw Hdx Hsx Hdw H5 H8 H15 H17 H20 H30.
  unfold RLC_A1, RLC_X2.
  replace (0x7fd10 : word) with (Z_to_bv 64 0x7fd10) by (apply bv_eq; reflexivity).
  replace (0x7fdec : word) with (Z_to_bv 64 0x7fdec) by (apply bv_eq; reflexivity).
  ex_entry regs [dx; sx; dw] HR.
  assert (HK : know_ok SEGS (ex_env regs [dx; sx; dw]) m []) by (ex_know regs).
  destruct (Z_lt_le_dec dx 0) as [Cx|Cx];
    [destruct (Z_lt_le_dec (sx - dx) 0) as [Cs|Cs] | destruct (Z_lt_le_dec sx 0) as [Cs|Cs]].
  - ex_run 200%nat [0x7fdec%Z] (SCR [true; true; true; false; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7fdec%Z] (SCR [true; true; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7fdec%Z] (SCR [false; false; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7fdec%Z] (SCR [false; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

Lemma rl_X2 : forall regs m (DX W2 DPW : Z),
  (0 <= DX <= 2 ^ 26)%Z -> (- 2 ^ 26 <= W2 <= 2 ^ 26)%Z -> (0 <= DPW <= 2 ^ 24)%Z ->
  getr regs 5 = Z_to_bv 64 DPW -> getr regs 21 = Z_to_bv 64 DPW -> getr regs 8 = Z_to_bv 64 W2 -> getr regs 25 = Z_to_bv 64 DX ->
  exists regs',
    msteps SEGS (mkst regs RLC_X2 m rom) (mkst regs' RLC_X3 m rom)
    /\ getr regs' 8 = Z_to_bv 64 (W2 - Z.max 0 (W2 - DPW + DX)) /\ getr regs' 12 = Z_to_bv 64 (W2 - Z.max 0 (W2 - DPW + DX))
    /\ getr regs' 13 = Z_to_bv 64 DX /\ getr regs' 31 = Z_to_bv 64 (DX + W2 - DPW)
    /\ regs_agree (fun r => In r [8; 12; 13; 15; 17; 31]%list) regs regs'.
Proof.
  intros regs m DX W2 DPW HDX HW2 HDPW H5 H21 H8 H25.
  unfold RLC_X2, RLC_X3.
  replace (0x7fdec : word) with (Z_to_bv 64 0x7fdec) by (apply bv_eq; reflexivity).
  replace (0x7fe30 : word) with (Z_to_bv 64 0x7fe30) by (apply bv_eq; reflexivity).
  ex_entry regs [DX; W2; DPW] HR.
  assert (HK : know_ok SEGS (ex_env regs [DX; W2; DPW]) m []) by (ex_know regs).
  destruct (Z_lt_le_dec 0 (DX + W2 - DPW)) as [C|C].
  - ex_run 200%nat [0x7fe30%Z] (SCR [true; true; false; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7fe30%Z] (SCR [true; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

Lemma rl_X3 : forall regs m (SX W3 SPW : Z),
  (0 <= SX <= 2 ^ 26)%Z -> (- 2 ^ 26 <= W3 <= 2 ^ 26)%Z -> (0 <= SPW <= 2 ^ 24)%Z ->
  getr regs 29 = Z_to_bv 64 SPW -> getr regs 8 = Z_to_bv 64 W3 -> getr regs 12 = Z_to_bv 64 W3 -> getr regs 27 = Z_to_bv 64 SX ->
  exists regs',
    msteps SEGS (mkst regs RLC_X3 m rom) (mkst regs' RLC_A2 m rom)
    /\ getr regs' 8 = Z_to_bv 64 (W3 - Z.max 0 (SX - SPW + W3)) /\ getr regs' 12 = Z_to_bv 64 (W3 - Z.max 0 (SX - SPW + W3))
    /\ getr regs' 24 = Z_to_bv 64 SX
    /\ regs_agree (fun r => In r [5; 8; 12; 15; 17; 24]%list) regs regs'.
Proof.
  intros regs m SX W3 SPW HSX HW3 HSPW H29 H8 H12 H27.
  unfold RLC_X3, RLC_A2.
  replace (0x7fe30 : word) with (Z_to_bv 64 0x7fe30) by (apply bv_eq; reflexivity).
  replace (0x7fe74 : word) with (Z_to_bv 64 0x7fe74) by (apply bv_eq; reflexivity).
  ex_entry regs [SX; W3; SPW] HR.
  assert (HK : know_ok SEGS (ex_env regs [SX; W3; SPW]) m []) by (ex_know regs).
  destruct (Z_lt_le_dec 0 (SX + W3 - SPW)) as [C|C].
  - ex_run 200%nat [0x7fe74%Z] (SCR [true; true; false; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7fe74%Z] (SCR [true; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

(* [comment removed for export] *)
Lemma rl_A1g_run : forall regs m (dx sx dw dpw spw : Z),
  (- 2 ^ 24 <= dx <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sx <= 2 ^ 24)%Z -> (0 <= dw <= 2 ^ 24)%Z -> (0 <= dpw <= 2 ^ 24)%Z -> (0 <= spw <= 2 ^ 24)%Z ->
  getr regs 5 = Z_to_bv 64 dpw -> getr regs 8 = Z_to_bv 64 dw -> getr regs 15 = Z_to_bv 64 dx -> getr regs 17 = Z_to_bv 64 dw ->
  getr regs 20 = Z_to_bv 64 sx -> getr regs 21 = Z_to_bv 64 dpw -> getr regs 29 = Z_to_bv 64 spw -> getr regs 30 = Z_to_bv 64 dx ->
  exists regs',
    msteps SEGS (mkst regs RLC_A1 m rom) (mkst regs' RLC_A2 m rom)
    /\ getr regs' 8 = Z_to_bv 64 (clip_w dx sx dw dpw spw) /\ getr regs' 12 = Z_to_bv 64 (clip_w dx sx dw dpw spw)
    /\ getr regs' 13 = Z_to_bv 64 (clip_d dx sx) /\ getr regs' 24 = Z_to_bv 64 (clip_s dx sx)
    /\ getr regs' 25 = Z_to_bv 64 (clip_d dx sx) /\ getr regs' 27 = Z_to_bv 64 (clip_s dx sx)
    /\ getr regs' 31 = Z_to_bv 64 (clip_d dx sx + clip_w2 dx sx dw - dpw)
    /\ regs_agree (fun r => In r [5; 8; 12; 13; 15; 17; 24; 25; 27; 31]%list) regs regs'.
Proof.
  intros regs m dx sx dw dpw spw Hdx Hsx Hdw Hdpw Hspw H5 H8 H15 H17 H20 H21 H29 H30.
  destruct (rl_X1 regs m dx sx dw dpw Hdx Hsx Hdw H5 H8 H15 H17 H20 H30) as (r1 & S1 & B8 & B25 & B27 & AG1).
  carry AG1 H5 (5 : reg) B5. carry AG1 H21 (21 : reg) B21. carry AG1 H29 (29 : reg) B29.
  destruct (rl_X2 r1 m (clip_d dx sx) (clip_w2 dx sx dw) dpw ltac:(unfold clip_d; lia) ltac:(unfold clip_w2; lia) Hdpw
              B5 B21 B8 B25) as (r2 & S2 & C8 & C12 & C13 & C31 & AG2).
  carry AG2 B29 (29 : reg) C29. carry AG2 B27 (27 : reg) C27. carry AG2 B25 (25 : reg) C25.
  destruct (rl_X3 r2 m (clip_s dx sx) (clip_w3 dx sx dw dpw) spw ltac:(unfold clip_s; lia)
              ltac:(unfold clip_w3, clip_w2, clip_d; lia) Hspw C29 C8 C12 C27) as (r3 & S3 & D8 & D12 & D24 & AG3).
  carry AG3 C13 (13 : reg) D13. carry AG3 C25 (25 : reg) D25. carry AG3 C27 (27 : reg) D27. carry AG3 C31 (31 : reg) D31.
  exists r3. split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | exact S3]] |].
  split; [exact D8 |]. split; [exact D12 |]. split; [exact D13 |]. split; [exact D24 |]. split; [exact D25 |].
  split; [exact D27 |]. split; [exact D31 |].
  eapply regs_agree_trans; [eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2] | regs_agree_weaken AG3].
Qed.

Lemma rl_Y1 : forall regs m (dy sy dh : Z),
  (- 2 ^ 24 <= dy <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sy <= 2 ^ 24)%Z -> (0 <= dh <= 2 ^ 24)%Z ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 22 = Z_to_bv 64 dh -> getr regs 26 = Z_to_bv 64 sy ->
  exists regs',
    msteps SEGS (mkst regs RLC_A2 m rom) (mkst regs' RLC_Y2 m rom)
    /\ getr regs' 1 = Z_to_bv 64 (clip_s dy sy) /\ getr regs' 7 = Z_to_bv 64 (clip_d dy sy)
    /\ getr regs' 22 = Z_to_bv 64 (clip_w2 dy sy dh)
    /\ regs_agree (fun r => In r [1; 5; 7; 12; 15; 17; 22]%list) regs regs'.
Proof.
  intros regs m dy sy dh Hdy Hsy Hdh H16 H22 H26.
  unfold RLC_A2, RLC_Y2.
  replace (0x7fe74 : word) with (Z_to_bv 64 0x7fe74) by (apply bv_eq; reflexivity).
  replace (0x7fee8 : word) with (Z_to_bv 64 0x7fee8) by (apply bv_eq; reflexivity).
  ex_entry regs [dy; sy; dh] HR.
  assert (HK : know_ok SEGS (ex_env regs [dy; sy; dh]) m []) by (ex_know regs).
  destruct (Z_lt_le_dec dy 0) as [Cy|Cy];
    [destruct (Z_lt_le_dec (sy - dy) 0) as [Cs|Cs] | destruct (Z_lt_le_dec sy 0) as [Cs|Cs]].
  - ex_run 200%nat [0x7fee8%Z] (SCR [true; true; true; false; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7fee8%Z] (SCR [true; true; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7fee8%Z] (SCR [false; true; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7fee8%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

Lemma rl_Y2 : forall regs m (DY H2 DPH : Z),
  (0 <= DY <= 2 ^ 26)%Z -> (- 2 ^ 26 <= H2 <= 2 ^ 26)%Z -> (0 <= DPH <= 2 ^ 24)%Z ->
  getr regs 23 = Z_to_bv 64 DPH -> getr regs 22 = Z_to_bv 64 H2 -> getr regs 7 = Z_to_bv 64 DY ->
  exists regs',
    msteps SEGS (mkst regs RLC_Y2 m rom) (mkst regs' RLC_Y3 m rom)
    /\ getr regs' 22 = Z_to_bv 64 (H2 - Z.max 0 (H2 - DPH + DY)) /\ getr regs' 12 = Z_to_bv 64 (H2 - Z.max 0 (H2 - DPH + DY))
    /\ getr regs' 18 = Z_to_bv 64 (DY + H2 - DPH) /\ getr regs' 7 = Z_to_bv 64 DY
    /\ regs_agree (fun r => In r [5; 7; 12; 15; 17; 18; 22]%list) regs regs'.
Proof.
  intros regs m DY H2 DPH HDY HH2 HDPH H23 H22 H7.
  unfold RLC_Y2, RLC_Y3.
  replace (0x7fee8 : word) with (Z_to_bv 64 0x7fee8) by (apply bv_eq; reflexivity).
  replace (0x7ff28 : word) with (Z_to_bv 64 0x7ff28) by (apply bv_eq; reflexivity).
  ex_entry regs [DY; H2; DPH] HR.
  assert (HK : know_ok SEGS (ex_env regs [DY; H2; DPH]) m []) by (ex_know regs).
  destruct (Z_lt_le_dec 0 (DY + H2 - DPH)) as [C|C].
  - ex_run 200%nat [0x7ff28%Z] (SCR [true; true; false; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7ff28%Z] (SCR [true; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

Lemma rl_Y3 : forall regs m (SY H3 SPH : Z),
  (0 <= SY <= 2 ^ 26)%Z -> (- 2 ^ 26 <= H3 <= 2 ^ 26)%Z -> (0 <= SPH <= 2 ^ 24)%Z ->
  getr regs 28 = Z_to_bv 64 SPH -> getr regs 22 = Z_to_bv 64 H3 -> getr regs 12 = Z_to_bv 64 H3 -> getr regs 1 = Z_to_bv 64 SY ->
  exists regs',
    msteps SEGS (mkst regs RLC_Y3 m rom) (mkst regs' RLC_W m rom)
    /\ getr regs' 22 = Z_to_bv 64 (H3 - Z.max 0 (SY - SPH + H3)) /\ getr regs' 12 = Z_to_bv 64 (H3 - Z.max 0 (SY - SPH + H3))
    /\ getr regs' 5 = Z_to_bv 64 SY
    /\ regs_agree (fun r => In r [5; 12; 15; 17; 22]%list) regs regs'.
Proof.
  intros regs m SY H3 SPH HSY HH3 HSPH H28 H22 H12 H1.
  unfold RLC_Y3, RLC_W.
  replace (0x7ff28 : word) with (Z_to_bv 64 0x7ff28) by (apply bv_eq; reflexivity).
  replace (0x7ff68 : word) with (Z_to_bv 64 0x7ff68) by (apply bv_eq; reflexivity).
  ex_entry regs [SY; H3; SPH] HR.
  assert (HK : know_ok SEGS (ex_env regs [SY; H3; SPH]) m []) by (ex_know regs).
  destruct (Z_lt_le_dec 0 (SY + H3 - SPH)) as [C|C].
  - ex_run 200%nat [0x7ff68%Z] (SCR [true; true; false; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7ff68%Z] (SCR [true; true; true] [] []) HR HK R' HR' Hms.
    all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

(* [comment removed for export] *)
Lemma rl_A2g_run : forall regs m (dy sy dh dpixh spixh : Z),
  (- 2 ^ 24 <= dy <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sy <= 2 ^ 24)%Z -> (0 <= dh <= 2 ^ 24)%Z -> (0 <= dpixh <= 2 ^ 24)%Z -> (0 <= spixh <= 2 ^ 24)%Z ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 22 = Z_to_bv 64 dh -> getr regs 23 = Z_to_bv 64 dpixh ->
  getr regs 26 = Z_to_bv 64 sy -> getr regs 28 = Z_to_bv 64 spixh ->
  exists regs',
    msteps SEGS (mkst regs RLC_A2 m rom) (mkst regs' RLC_W m rom)
    /\ getr regs' 1 = Z_to_bv 64 (clip_s dy sy) /\ getr regs' 5 = Z_to_bv 64 (clip_s dy sy)
    /\ getr regs' 7 = Z_to_bv 64 (clip_d dy sy)
    /\ getr regs' 12 = Z_to_bv 64 (clip_w dy sy dh dpixh spixh) /\ getr regs' 22 = Z_to_bv 64 (clip_w dy sy dh dpixh spixh)
    /\ getr regs' 18 = Z_to_bv 64 (clip_d dy sy + clip_w2 dy sy dh - dpixh)
    /\ regs_agree (fun r => In r [1; 5; 7; 12; 15; 17; 18; 22]%list) regs regs'.
Proof.
  intros regs m dy sy dh dpixh spixh Hdy Hsy Hdh Hdph Hsph H16 H22 H23 H26 H28.
  destruct (rl_Y1 regs m dy sy dh Hdy Hsy Hdh H16 H22 H26) as (r1 & S1 & B1 & B7 & B22 & AG1).
  carry AG1 H23 (23 : reg) B23. carry AG1 H28 (28 : reg) B28.
  destruct (rl_Y2 r1 m (clip_d dy sy) (clip_w2 dy sy dh) dpixh ltac:(unfold clip_d; lia) ltac:(unfold clip_w2; lia) Hdph
              B23 B22 B7) as (r2 & S2 & C22 & C12 & C18 & C7 & AG2).
  carry AG2 B28 (28 : reg) C28. carry AG2 B1 (1 : reg) C1.
  destruct (rl_Y3 r2 m (clip_s dy sy) (clip_w3 dy sy dh dpixh) spixh ltac:(unfold clip_s; lia)
              ltac:(unfold clip_w3, clip_w2, clip_d; lia) Hsph C28 C22 C12 C1) as (r3 & S3 & D22 & D12 & D5 & AG3).
  carry AG3 C1 (1 : reg) D1. carry AG3 C7 (7 : reg) D7. carry AG3 C18 (18 : reg) D18.
  exists r3. split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | exact S3]] |].
  split; [exact D1 |]. split; [exact D5 |]. split; [exact D7 |]. split; [exact D12 |]. split; [exact D22 |].
  split; [exact D18 |].
  eapply regs_agree_trans; [eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2] | regs_agree_weaken AG3].
Qed.

(* [comment removed for export] *)
Lemma rl_A1c : forall regs m (Wd : Z), (1 <= Wd < 2 ^ 31)%Z -> getr regs 8 = Z_to_bv 64 Wd ->
  exists regs',
    msteps SEGS (mkst regs RLC_W m rom) (mkst regs' RLC_H m rom)
    /\ getr regs' 9 = Z_to_bv 64 Wd /\ regs_agree (fun r => In r [9]%list) regs regs'.
Proof.
  intros regs m Wd HWd H8.
  unfold RLC_W, RLC_H.
  replace (0x7ff68 : word) with (Z_to_bv 64 0x7ff68) by (apply bv_eq; reflexivity).
  replace (0x7ff74 : word) with (Z_to_bv 64 0x7ff74) by (apply bv_eq; reflexivity).
  ex_entry regs [Wd] HR.
  assert (HK : know_ok SEGS (ex_env regs [Wd]) m []) by (ex_know regs).
  ex_run 50%nat [0x7ff74%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

Lemma rl_A1e : forall regs m (Wd : Z), (- 2 ^ 31 <= Wd <= 0)%Z -> getr regs 8 = Z_to_bv 64 Wd ->
  exists regs',
    msteps SEGS (mkst regs RLC_W m rom) (mkst regs' RLC_E m rom)
    /\ regs_agree (fun r => In r [9]%list) regs regs'.
Proof.
  intros regs m Wd HWd H8.
  unfold RLC_W, RLC_E.
  replace (0x7ff68 : word) with (Z_to_bv 64 0x7ff68) by (apply bv_eq; reflexivity).
  replace (0x875b8 : word) with (Z_to_bv 64 0x875b8) by (apply bv_eq; reflexivity).
  ex_entry regs [Wd] HR.
  assert (HK : know_ok SEGS (ex_env regs [Wd]) m []) by (ex_know regs).
  ex_run 50%nat [0x875b8%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

Lemma rl_A2c : forall regs m (s Hd : Z), (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= Hd < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 12 = Z_to_bv 64 Hd -> getr regs 22 = Z_to_bv 64 Hd ->
  exists regs',
    msteps SEGS (mkst regs RLC_H m rom) (mkst regs' RLC_D (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 Hd))) rom)
    /\ getr regs' 22 = Z_to_bv 64 Hd /\ regs_agree (fun r => In r [22]%list) regs regs'.
Proof.
  intros regs m s Hd Hs Hs64 HHd SOK H2 H12 H22.
  unfold RLC_H, RLC_D.
  replace (0x7ff74 : word) with (Z_to_bv 64 0x7ff74) by (apply bv_eq; reflexivity).
  replace (0x7ff84 : word) with (Z_to_bv 64 0x7ff84) by (apply bv_eq; reflexivity).
  ex_entry regs [s; Hd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; Hd]) m [KRange (EVar 32) 240 (2 ^ 64 - 1); KWr (SA (EVar 32) (-112)) 8]%Z)
    by (ex_know regs).
  ex_run 50%nat [0x7ff84%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

Lemma rl_A2e : forall regs m (s Hd : Z), (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (- 2 ^ 31 <= Hd <= 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 12 = Z_to_bv 64 Hd -> getr regs 22 = Z_to_bv 64 Hd ->
  exists regs',
    msteps SEGS (mkst regs RLC_H m rom) (mkst regs' RLC_E (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 Hd))) rom)
    /\ getr regs' 22 = Z_to_bv 64 Hd /\ regs_agree (fun r => In r [22]%list) regs regs'.
Proof.
  intros regs m s Hd Hs Hs64 HHd SOK H2 H12 H22.
  unfold RLC_H, RLC_E.
  replace (0x7ff74 : word) with (Z_to_bv 64 0x7ff74) by (apply bv_eq; reflexivity).
  replace (0x875b8 : word) with (Z_to_bv 64 0x875b8) by (apply bv_eq; reflexivity).
  ex_entry regs [s; Hd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; Hd]) m [KRange (EVar 32) 240 (2 ^ 64 - 1); KWr (SA (EVar 32) (-112)) 8]%Z)
    by (ex_know regs).
  ex_run 50%nat [0x875b8%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  all: try solve [rlc_sc]. all: rlc_fin regs HR HR' Hms.
Qed.

Lemma rl_Eg : forall regs M (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 (s - 240) ->
  rlcells M s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ->
  exists regs',
    msteps SEGS (mkst regs RLC_E M rom) (mkst regs' ret M rom)
    /\ getr regs' 1 = ret /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = v0 /\ getr regs' 9 = v1
    /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5 /\ getr regs' 22 = v6
    /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10 /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs M s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 Hret H2 RC.
  destruct RC as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
  unfold RLC_E.
  replace (0x875b8 : word) with (Z_to_bv 64 0x875b8) by (apply bv_eq; reflexivity).
  ex_entryL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] regs [s]) M
                 [KRange (EVar 45) 240 (2 ^ 64 - 1);
                  KWord (SA (EVar 45) (-8)) 8 (EVar 0); KWord (SA (EVar 45) (-16)) 8 (EVar 1);
                  KWord (SA (EVar 45) (-24)) 8 (EVar 2); KWord (SA (EVar 45) (-32)) 8 (EVar 3);
                  KWord (SA (EVar 45) (-40)) 8 (EVar 4); KWord (SA (EVar 45) (-48)) 8 (EVar 5);
                  KWord (SA (EVar 45) (-56)) 8 (EVar 6); KWord (SA (EVar 45) (-64)) 8 (EVar 7);
                  KWord (SA (EVar 45) (-72)) 8 (EVar 8); KWord (SA (EVar 45) (-80)) 8 (EVar 9);
                  KWord (SA (EVar 45) (-88)) 8 (EVar 10); KWord (SA (EVar 45) (-96)) 8 (EVar 11);
                  KWord (SA (EVar 45) (-104)) 8 (EVar 12)]%Z) by (ex_know regs).
  ex_run 100%nat [0x875f0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  assert (G1 : getr R' 1 = ret) by (ex_reg regs HR').
  assert (G2 : getr R' 2 = Z_to_bv 64 s) by (ex_reg regs HR').
  assert (G8 : getr R' 8 = v0) by (ex_reg regs HR').
  assert (G9 : getr R' 9 = v1) by (ex_reg regs HR').
  assert (G18 : getr R' 18 = v2) by (ex_reg regs HR').
  assert (G19 : getr R' 19 = v3) by (ex_reg regs HR').
  assert (G20 : getr R' 20 = v4) by (ex_reg regs HR').
  assert (G21 : getr R' 21 = v5) by (ex_reg regs HR').
  assert (G22 : getr R' 22 = v6) by (ex_reg regs HR').
  assert (G23 : getr R' 23 = v7) by (ex_reg regs HR').
  assert (G24 : getr R' 24 = v8) by (ex_reg regs HR').
  assert (G25 : getr R' 25 = v9) by (ex_reg regs HR').
  assert (G26 : getr R' 26 = v10) by (ex_reg regs HR').
  assert (G27 : getr R' 27 = v11) by (ex_reg regs HR').
  assert (AG : regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs R') by (ex_agree HR HR').
  cbn [mem_denot] in Hms.
  exists R'. split.
  - eapply msteps_trans; [exact Hms|].
    ex_fetch SEGS 0x875f0%Z F D.
    lazymatch type of D with decode_any ?w = _ =>
      assert (Dj : decode_any w = Some (Jalr 0 1 0, 4%Z)) by (rewrite D; f_equal; f_equal; f_equal; apply bv_eq; reflexivity) end.
    eapply mst_step; [reflexivity | eapply step_jalr_x0; [exact F | reflexivity | exact Dj | exact G1] |].
    match goal with |- msteps _ (mkst _ ?t _ _) _ => replace t with ret by (symmetry; exact (Hret : v_jalr ret 0 = ret)) end.
    apply mst_refl.
  - repeat split; assumption.
Qed.

Lemma rl_clip_pre : forall regs m (s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy : Z) (ret : word),
  (240 <= s)%Z -> (s + 64 < 2 ^ 64)%Z ->
  (0 <= dpixw <= 2 ^ 24)%Z -> (0 <= dpixh <= 2 ^ 24)%Z -> (0 <= spixw <= 2 ^ 24)%Z -> (0 <= spixh <= 2 ^ 24)%Z ->
  (- 2 ^ 24 <= dx <= 2 ^ 24)%Z -> (- 2 ^ 24 <= dy <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sx <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sy <= 2 ^ 24)%Z ->
  (0 <= dw <= 2 ^ 24)%Z -> (0 <= dh <= 2 ^ 24)%Z ->
  (- 2 ^ 31 <= op < 2 ^ 31)%Z -> (0 <= datas < 2 ^ 64)%Z -> (- 2 ^ 31 <= swpl < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw ->
  getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  exists regs',
    msteps SEGS (mkst regs RLC_P m rom) (mkst regs' RLC_W (RLF m s ret regs) rom)
    /\ getr regs' 1 = Z_to_bv 64 (clip_s dy sy) /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 5 = Z_to_bv 64 (clip_s dy sy)
    /\ getr regs' 6 = Z_to_bv 64 swpl /\ getr regs' 7 = Z_to_bv 64 (clip_d dy sy)
    /\ getr regs' 8 = Z_to_bv 64 (clip_w dx sx dw dpixw spixw)
    /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 12 = Z_to_bv 64 (clip_w dy sy dh dpixh spixh) /\ getr regs' 13 = Z_to_bv 64 (clip_d dx sx)
    /\ getr regs' 18 = Z_to_bv 64 (clip_d dy sy + clip_w2 dy sy dh - dpixh) /\ getr regs' 19 = Z_to_bv 64 datas
    /\ getr regs' 20 = Z_to_bv 64 sx /\ getr regs' 21 = Z_to_bv 64 dpixw /\ getr regs' 22 = Z_to_bv 64 (clip_w dy sy dh dpixh spixh)
    /\ getr regs' 23 = Z_to_bv 64 dpixh /\ getr regs' 24 = Z_to_bv 64 (clip_s dx sx) /\ getr regs' 25 = Z_to_bv 64 (clip_d dx sx)
    /\ getr regs' 26 = Z_to_bv 64 sy /\ getr regs' 27 = Z_to_bv 64 (clip_s dx sx) /\ getr regs' 28 = Z_to_bv 64 spixh
    /\ getr regs' 29 = Z_to_bv 64 spixw /\ getr regs' 30 = Z_to_bv 64 dx /\ getr regs' 31 = Z_to_bv 64 (clip_d dx sx + clip_w2 dx sx dw - dpixw)
    /\ regs_agree (fun r => In r [1; 2; 5; 6; 7; 8; 11; 12; 13; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret Hs Hs64
    Hdpw Hdph Hspw Hsph Hdx Hdy Hsx Hsy Hdw Hdh Hop Hdatas Hswpl SOK A0 A1 A2 A3 A4 A5 A6 A7 H2 H1 H10 H11 H12 H13 H14 H15 H16 H17.
  destruct (rl_A0g regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret Hs Hs64
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hop Hdatas ltac:(lia) ltac:(lia) Hswpl ltac:(lia) ltac:(lia)
              SOK A0 A1 A2 A3 A4 A5 A6 A7 H2 H1 H10 H11 H12 H13 H14 H15 H16 H17)
    as (r1 & S1 & B2 & B5 & B6 & B8 & B11 & B12 & B19 & B20 & B21 & B22 & B23 & B26 & B28 & B29 & B30 & AG1).
  carry AG1 H15 (15 : reg) B15. carry AG1 H17 (17 : reg) B17. carry AG1 H16 (16 : reg) B16.
  destruct (rl_A1g_run r1 (RLF m s ret regs) dx sx dw dpixw spixw Hdx Hsx Hdw Hdpw Hspw B5 B8 B15 B17 B20 B21 B29 B30)
    as (r2 & S2 & C8 & C12 & C13 & C24 & C25 & C27 & C31 & AG2).
  carry AG2 B16 (16 : reg) C16. carry AG2 B22 (22 : reg) C22. carry AG2 B23 (23 : reg) C23. carry AG2 B26 (26 : reg) C26.
  carry AG2 B28 (28 : reg) C28.
  destruct (rl_A2g_run r2 (RLF m s ret regs) dy sy dh dpixh spixh Hdy Hsy Hdh Hdph Hsph C16 C22 C23 C26 C28)
    as (r3 & S3 & D1 & D5 & D7 & D12 & D22 & D18 & AG3).
  assert (AG23 : regs_agree (fun r => In r [1; 5; 7; 8; 12; 13; 15; 17; 18; 22; 24; 25; 27; 31]%list) r1 r3)
    by (eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]).
  carry AG23 B2 (2 : reg) D2. carry AG23 B6 (6 : reg) D6. carry AG23 B11 (11 : reg) D11. carry AG23 B19 (19 : reg) D19.
  carry AG23 B20 (20 : reg) D20. carry AG23 B21 (21 : reg) D21. carry AG23 B23 (23 : reg) D23. carry AG23 B26 (26 : reg) D26.
  carry AG23 B28 (28 : reg) D28. carry AG23 B29 (29 : reg) D29. carry AG23 B30 (30 : reg) D30.
  carry AG3 C8 (8 : reg) D8. carry AG3 C13 (13 : reg) D13. carry AG3 C24 (24 : reg) D24. carry AG3 C25 (25 : reg) D25.
  carry AG3 C27 (27 : reg) D27. carry AG3 C31 (31 : reg) D31.
  exists r3. split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | exact S3]] |].
  do 23 (split; [assumption |]).
  eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG23].
Qed.

Lemma rl_clip_run : forall regs m (s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy : Z) (ret : word),
  (240 <= s)%Z -> (s + 64 < 2 ^ 64)%Z ->
  (0 <= dpixw <= 2 ^ 24)%Z -> (0 <= dpixh <= 2 ^ 24)%Z -> (0 <= spixw <= 2 ^ 24)%Z -> (0 <= spixh <= 2 ^ 24)%Z ->
  (- 2 ^ 24 <= dx <= 2 ^ 24)%Z -> (- 2 ^ 24 <= dy <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sx <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sy <= 2 ^ 24)%Z ->
  (0 <= dw <= 2 ^ 24)%Z -> (0 <= dh <= 2 ^ 24)%Z ->
  (- 2 ^ 31 <= op < 2 ^ 31)%Z -> (0 <= datas < 2 ^ 64)%Z -> (- 2 ^ 31 <= swpl < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw ->
  getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  (1 <= clip_w dx sx dw dpixw spixw)%Z -> (1 <= clip_w dy sy dh dpixh spixh)%Z ->
  exists regs',
    msteps SEGS (mkst regs RLC_P m rom)
      (mkst regs' RLC_D (wbytes (RLF m s ret regs) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 (clip_w dy sy dh dpixh spixh)))) rom)
    /\ getr regs' 1 = Z_to_bv 64 (clip_s dy sy) /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 5 = Z_to_bv 64 (clip_s dy sy)
    /\ getr regs' 6 = Z_to_bv 64 swpl /\ getr regs' 7 = Z_to_bv 64 (clip_d dy sy)
    /\ getr regs' 8 = Z_to_bv 64 (clip_w dx sx dw dpixw spixw) /\ getr regs' 9 = Z_to_bv 64 (clip_w dx sx dw dpixw spixw)
    /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 12 = Z_to_bv 64 (clip_w dy sy dh dpixh spixh) /\ getr regs' 13 = Z_to_bv 64 (clip_d dx sx)
    /\ getr regs' 18 = Z_to_bv 64 (clip_d dy sy + clip_w2 dy sy dh - dpixh) /\ getr regs' 19 = Z_to_bv 64 datas
    /\ getr regs' 20 = Z_to_bv 64 sx /\ getr regs' 21 = Z_to_bv 64 dpixw /\ getr regs' 22 = Z_to_bv 64 (clip_w dy sy dh dpixh spixh)
    /\ getr regs' 23 = Z_to_bv 64 dpixh /\ getr regs' 24 = Z_to_bv 64 (clip_s dx sx) /\ getr regs' 25 = Z_to_bv 64 (clip_d dx sx)
    /\ getr regs' 26 = Z_to_bv 64 sy /\ getr regs' 27 = Z_to_bv 64 (clip_s dx sx) /\ getr regs' 28 = Z_to_bv 64 spixh
    /\ getr regs' 29 = Z_to_bv 64 spixw /\ getr regs' 30 = Z_to_bv 64 dx /\ getr regs' 31 = Z_to_bv 64 (clip_d dx sx + clip_w2 dx sx dw - dpixw)
    /\ regs_agree (fun r => In r [1; 2; 5; 6; 7; 8; 9; 11; 12; 13; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret Hs Hs64
    Hdpw Hdph Hspw Hsph Hdx Hdy Hsx Hsy Hdw Hdh Hop Hdatas Hswpl SOK A0 A1 A2 A3 A4 A5 A6 A7 H2 H1 H10 H11 H12 H13 H14 H15 H16 H17
    HW HHt.
  destruct (rl_clip_pre regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret Hs Hs64
              Hdpw Hdph Hspw Hsph Hdx Hdy Hsx Hsy Hdw Hdh Hop Hdatas Hswpl SOK A0 A1 A2 A3 A4 A5 A6 A7 H2 H1 H10 H11 H12 H13 H14 H15 H16 H17)
    as (r3 & S3 & D1 & D2 & D5 & D6 & D7 & D8 & D11 & D12 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27
        & D28 & D29 & D30 & D31 & AG3).
  pose proof (clip_facts dx sx dw dpixw spixw ltac:(lia) ltac:(lia) HW) as (_ & _ & _ & _ & CW).
  pose proof (clip_facts dy sy dh dpixh spixh ltac:(lia) ltac:(lia) HHt) as (_ & _ & _ & _ & CH).
  destruct (rl_A1c r3 (RLF m s ret regs) (clip_w dx sx dw dpixw spixw) ltac:(lia) D8) as (r4 & S4 & E9 & AG4).
  carry AG4 D2 (2 : reg) E2. carry AG4 D12 (12 : reg) E12. carry AG4 D22 (22 : reg) E22.
  assert (SOK8 : store_ok SEGS (RLF m s ret regs) (Z_to_bv 64 (s - 112)) 8 = true) by (unfold RLF; sok_in SOK).
  destruct (rl_A2c r4 (RLF m s ret regs) s (clip_w dy sy dh dpixh spixh) Hs ltac:(lia) ltac:(lia) SOK8 E2 E12 E22)
    as (r5 & S5 & F22 & AG5).
  assert (AG45 : regs_agree (fun r => In r [9; 22]%list) r3 r5)
    by (eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5]).
  carry AG5 E9 (9 : reg) F9.
  carry AG45 D1 (1 : reg) F1. carry AG45 D2 (2 : reg) F2. carry AG45 D5 (5 : reg) F5. carry AG45 D6 (6 : reg) F6.
  carry AG45 D7 (7 : reg) F7. carry AG45 D8 (8 : reg) F8. carry AG45 D11 (11 : reg) F11. carry AG45 D12 (12 : reg) F12.
  carry AG45 D13 (13 : reg) F13. carry AG45 D18 (18 : reg) F18. carry AG45 D19 (19 : reg) F19. carry AG45 D20 (20 : reg) F20.
  carry AG45 D21 (21 : reg) F21. carry AG45 D23 (23 : reg) F23. carry AG45 D24 (24 : reg) F24. carry AG45 D25 (25 : reg) F25.
  carry AG45 D26 (26 : reg) F26. carry AG45 D27 (27 : reg) F27. carry AG45 D28 (28 : reg) F28. carry AG45 D29 (29 : reg) F29.
  carry AG45 D30 (30 : reg) F30. carry AG45 D31 (31 : reg) F31.
  exists r5. split; [eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact S4 | exact S5]] |].
  do 24 (split; [assumption |]).
  eapply regs_agree_trans; [regs_agree_weaken AG3 | regs_agree_weaken AG45].
Qed.

Lemma rl_clip_empty : forall regs m (s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy : Z) (ret : word),
  (240 <= s)%Z -> (s + 64 < 2 ^ 64)%Z ->
  (0 <= dpixw <= 2 ^ 24)%Z -> (0 <= dpixh <= 2 ^ 24)%Z -> (0 <= spixw <= 2 ^ 24)%Z -> (0 <= spixh <= 2 ^ 24)%Z ->
  (- 2 ^ 24 <= dx <= 2 ^ 24)%Z -> (- 2 ^ 24 <= dy <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sx <= 2 ^ 24)%Z -> (- 2 ^ 24 <= sy <= 2 ^ 24)%Z ->
  (0 <= dw <= 2 ^ 24)%Z -> (0 <= dh <= 2 ^ 24)%Z ->
  (- 2 ^ 31 <= op < 2 ^ 31)%Z -> (0 <= datas < 2 ^ 64)%Z -> (- 2 ^ 31 <= swpl < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw ->
  getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  (clip_w dx sx dw dpixw spixw <= 0 \/ clip_w dy sy dh dpixh spixh <= 0)%Z ->
  exists regs1 M1,
    msteps SEGS (mkst regs RLC_P m rom) (mkst regs1 ret M1 rom)
    /\ (forall a : word, ~ (s - 240 <= u a < s)%Z -> M1 a = m a) /\ mem_grows m M1 /\ cs_kept regs regs1.
Proof.
  intros regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret Hs Hs64
    Hdpw Hdph Hspw Hsph Hdx Hdy Hsx Hsy Hdw Hdh Hop Hdatas Hswpl SOK A0 A1 A2 A3 A4 A5 A6 A7 H2 H1 Hret H10 H11 H12 H13 H14 H15 H16 H17
    HE.
  destruct (rl_clip_pre regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret Hs Hs64
              Hdpw Hdph Hspw Hsph Hdx Hdy Hsx Hsy Hdw Hdh Hop Hdatas Hswpl SOK A0 A1 A2 A3 A4 A5 A6 A7 H2 H1 H10 H11 H12 H13 H14 H15 H16 H17)
    as (r3 & S3 & D1 & D2 & D5 & D6 & D7 & D8 & D11 & D12 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27
        & D28 & D29 & D30 & D31 & AG3).
  assert (RC : rlcells (RLF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                 (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27))
    by (apply rlcells_RLF; lia).
  assert (GR1 : mem_grows m (RLF m s ret regs))
    by (unfold RLF; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  destruct (Z_le_gt_dec (clip_w dx sx dw dpixw spixw) 0) as [CW|CW].
  - destruct (rl_A1e r3 (RLF m s ret regs) (clip_w dx sx dw dpixw spixw)
                ltac:(unfold clip_w, clip_w3, clip_w2, clip_d, clip_s in *; lia) D8) as (r4 & S4 & AG4).
    carry AG4 D2 (2 : reg) E2.
    destruct (rl_Eg r4 (RLF m s ret regs) s ret _ _ _ _ _ _ _ _ _ _ _ _ Hs ltac:(lia) Hret E2 RC)
      as (r5 & S5 & G1 & G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & AG5).
    assert (AG35 : regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) r3 r5)
      by (eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5]).
    exists r5, (RLF m s ret regs). split; [eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact S4 | exact S5]] |].
    split; [intros a Ha; apply RLF_outside; lia |]. split; [exact GR1 |].
    apply cs_kept_intro; try assumption.
    + rewrite G2, H2. reflexivity.
    + rewrite (AG35 (3 : reg) ltac:(notin_list)), (AG3 (3 : reg) ltac:(notin_list)). reflexivity.
    + rewrite (AG35 (4 : reg) ltac:(notin_list)), (AG3 (4 : reg) ltac:(notin_list)). reflexivity.
  - pose proof (clip_facts dx sx dw dpixw spixw ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & _ & CWb).
    assert (CH : (clip_w dy sy dh dpixh spixh <= 0)%Z) by lia.
    destruct (rl_A1c r3 (RLF m s ret regs) (clip_w dx sx dw dpixw spixw) ltac:(lia) D8) as (r4 & S4 & E9 & AG4).
    carry AG4 D2 (2 : reg) E2. carry AG4 D12 (12 : reg) E12. carry AG4 D22 (22 : reg) E22.
    assert (SOK8 : store_ok SEGS (RLF m s ret regs) (Z_to_bv 64 (s - 112)) 8 = true) by (unfold RLF; sok_in SOK).
    destruct (rl_A2e r4 (RLF m s ret regs) s (clip_w dy sy dh dpixh spixh) Hs ltac:(lia)
                ltac:(unfold clip_w, clip_w3, clip_w2, clip_d, clip_s in *; lia) SOK8 E2 E12 E22) as (r5 & S5 & F22 & AG5).
    carry AG5 E2 (2 : reg) F2.
    assert (RC2 : rlcells (wbytes (RLF m s ret regs) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 (clip_w dy sy dh dpixh spixh))))
                    s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                    (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
    { apply (rlcells_frame (RLF m s ret regs)); [lia | lia | exact RC |].
      intros x Hx. apply wbytes_outside; zlen; rewrite ?u_Z2bv by lia; lia. }
    destruct (rl_Eg r5 _ s ret _ _ _ _ _ _ _ _ _ _ _ _ Hs ltac:(lia) Hret F2 RC2)
      as (r6 & S6 & G1 & G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & AG6).
    assert (AG36 : regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) r3 r6)
      by (eapply regs_agree_trans; [eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5] | regs_agree_weaken AG6]).
    exists r6. eexists. split.
    { eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact S4 | eapply msteps_trans; [exact S5 | exact S6]]]. }
    split; [intros a Ha; rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia); apply RLF_outside; lia |].
    split; [eapply mem_grows_trans; [exact GR1 | apply wbytes_grows] |].
    apply cs_kept_intro; try assumption.
    + rewrite G2, H2. reflexivity.
    + rewrite (AG36 (3 : reg) ltac:(notin_list)), (AG3 (3 : reg) ltac:(notin_list)). reflexivity.
    + rewrite (AG36 (4 : reg) ltac:(notin_list)), (AG3 (4 : reg) ltac:(notin_list)). reflexivity.
Qed.

End Segs.
