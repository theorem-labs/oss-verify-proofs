(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MemsetFill_iface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptMulw.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecW LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptStderr O23LeptRopLow O23LeptRopUni O23LeptRopClip O23LeptRopUniC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23ExecUb V23LeptBase V23LeptRop_iface V23LeptRopUni V23_code_rasteropUniLow.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition RUC_P : word := 0x7f3d8.
Definition RUC_X : word := 0x7f458.
Definition RUC_Y : word := 0x7f490.
Definition RUC_W : word := 0x7f4d8.
Definition RUC_H : word := 0x7f4e0.
Definition RUC_A : word := 0x7f4e8.
Definition RUC_G : word := 0x7f4f0.
Definition RUC_M : word := 0x7f5a8.
Definition RUC_E : word := 0x7fb08.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ruc_sx32 : forall z : Z, (- 2 ^ 31 <= z < 2 ^ 31)%Z -> SX2.ext_val true 0 4 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold SX2.ext_val, SX2.ext_Z. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_nat N.of_nat Z.of_N Pos.of_succ_nat Pos.succ Z.mul N.mul].
  rewrite Z.pow_0_r, Z.div_1_r. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma ruc_br_eq : forall e1 e2 : Z, e1 = e2 -> Sem.branch_taken BC_EQ (Z_to_bv 64 e1) (Z_to_bv 64 e2) = true.
Proof. intros e1 e2 E. subst e2. cbn [Sem.branch_taken]. unfold bv_eqb. apply Z.eqb_eq. reflexivity. Qed.
Lemma ruc_br_ne : forall e1 e2 : Z, e1 = e2 -> Sem.branch_taken BC_NE (Z_to_bv 64 e1) (Z_to_bv 64 e2) = false.
Proof. intros e1 e2 E. subst e2. cbn [Sem.branch_taken]. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma ruc_br_eqf : forall e1 e2 : Z, (0 <= e1 < 2 ^ 64)%Z -> (0 <= e2 < 2 ^ 64)%Z -> e1 <> e2 ->
  Sem.branch_taken BC_EQ (Z_to_bv 64 e1) (Z_to_bv 64 e2) = false.
Proof. intros e1 e2 H1 H2 NE. cbn [Sem.branch_taken]. unfold bv_eqb. rewrite !u_Z2bv by lia. apply Z.eqb_neq. exact NE. Qed.
Lemma ruc_and31 : forall x : Z, (0 <= x < 2 ^ 64)%Z -> v_and (Z_to_bv 64 x) (Z_to_bv 64 31) = Z_to_bv 64 (x mod 32).
Proof.
  intros x Hx. unfold v_and. rewrite !u_Z2bv by lia.
  change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.
Ltac ruc_modb := repeat match goal with |- context [(?x mod ?k)%Z] =>
  lazymatch goal with H : (0 <= x mod k < k)%Z |- _ => fail | _ => pose proof (Z.mod_pos_bound x k ltac:(lia)) end end.
Ltac ruc_norm := repeat first [ rewrite w_addw | rewrite w_subw | rewrite addw_fit by lia | rewrite subw_fit by lia
  | rewrite ex_ptr_val | rewrite alu_and | rewrite ruc_and31 by lia | rewrite alu_add | rewrite alu_sub | rewrite zbv_add
  | rewrite zbv_sub | rewrite m_mul | rewrite zbv_mul ].
Ltac ruc_sc := ruc_norm; first [ apply ruc_br_eq; lia | apply ruc_br_ne; lia | (apply ruc_br_eqf; ruc_modb; lia) | ex_br ].
Ltac ruc_val := first [ reflexivity | (ruc_norm; f_equal; lia) | (apply ruc_sx32; lia) ].
Ltac ruc_tail regs HR HR' Hms :=
  lazymatch type of HR' with SX2S.regs_ok _ _ ?R => exists R end;
  split; [try unfold UF; ex_mem regs Hms | unfold uclip_w; repeat split; try (ex_reg regs HR'); try (ex_agree HR HR'); try solve [ruc_val]].
Ltac ruc_fin regs HR HR' Hms := try solve [ruc_sc]; ruc_tail regs HR HR' Hms.
Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma ru_A0g : forall regs m (s dpixw dx dw dh op : Z),
  (32 <= s)%Z -> (s + 16 < 2 ^ 64)%Z -> (- 2 ^ 24 <= dx <= 2 ^ 24)%Z -> (0 <= dw <= 2 ^ 24)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 dpixw ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 dx -> getr regs 17 = Z_to_bv 64 dw ->
  exists regs',
    msteps SEGS (mkst regs RUC_P m rom) (mkst regs' RUC_X (UF m s regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 6 = Z_to_bv 64 dh
    /\ getr regs' 28 = Z_to_bv 64 dpixw /\ getr regs' 7 = Z_to_bv 64 (Z.max 0 dx) /\ getr regs' 17 = Z_to_bv 64 (dw + Z.min 0 dx)
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 11; 13; 15; 17; 28]%list) regs regs'.
Proof.
  intros regs m s dpixw dx dw dh op Hs Hs64 Hdx Hdw SOK A0 A1 H2 H11 H13 H15 H17.
  unfold RUC_P, RUC_X.
  replace (0x7f3d8 : word) with (Z_to_bv 64 0x7f3d8) by (apply bv_eq; reflexivity).
  replace (0x7f458 : word) with (Z_to_bv 64 0x7f458) by (apply bv_eq; reflexivity).
  ex_entry regs [s; dh; op] HR.
  assert (HK : SX2S.know_ok SEGS (ex_env regs [s; dh; op]) m
                 [SX2.KWr (SX2.SA (SX2.EVar 32) (-32)) 32; SX2.KWord (SX2.SA (SX2.EVar 32) 0) 8 (SX2.EVar 33);
                  SX2.KWord (SX2.SA (SX2.EVar 32) 8) 8 (SX2.EVar 34)]%Z)
    by (ex_know regs).
  destruct (Z_lt_le_dec dx 0) as [C|C].
  - ex_run 200%nat [0x7f458%Z] (SX2.SCR [false; false; false] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7f458%Z] (SX2.SCR [true] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
Qed.

(* [comment removed for export] *)
Lemma ru_A1g_run : forall regs m (dx dw dpixw : Z),
  (- 2 ^ 24 <= dx <= 2 ^ 24)%Z -> (0 <= dw <= 2 ^ 24)%Z -> (0 <= dpixw <= 2 ^ 24)%Z ->
  getr regs 7 = Z_to_bv 64 (Z.max 0 dx) -> getr regs 17 = Z_to_bv 64 (dw + Z.min 0 dx) -> getr regs 28 = Z_to_bv 64 dpixw ->
  exists regs',
    msteps SEGS (mkst regs RUC_X m rom) (mkst regs' RUC_Y m rom)
    /\ getr regs' 17 = Z_to_bv 64 (uclip_w dx dw dpixw) /\ getr regs' 28 = Z_to_bv 64 dpixw /\ getr regs' 29 = Z_to_bv 64 (Z.max 0 dx)
    /\ regs_agree (fun r => In r [5; 13; 15; 17; 28; 29]%list) regs regs'.
Proof.
  intros regs m dx dw dpixw Hdx Hdw Hdpw H7 H17 H28.
  unfold RUC_X, RUC_Y.
  replace (0x7f458 : word) with (Z_to_bv 64 0x7f458) by (apply bv_eq; reflexivity).
  replace (0x7f490 : word) with (Z_to_bv 64 0x7f490) by (apply bv_eq; reflexivity).
  ex_entry regs [dx; dw; dpixw] HR.
  assert (HK : SX2S.know_ok SEGS (ex_env regs [dx; dw; dpixw]) m []) by (ex_know regs).
  destruct (Z_le_gt_dec (Z.max 0 dx - dpixw + (dw + Z.min 0 dx)) 0) as [C|C].
  - ex_run 200%nat [0x7f490%Z] (SX2.SCR [false; false; true] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7f490%Z] (SX2.SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
Qed.

Lemma ru_A1c : forall regs m (Wd : Z), (1 <= Wd < 2 ^ 31)%Z -> getr regs 17 = Z_to_bv 64 Wd ->
  exists regs',
    msteps SEGS (mkst regs RUC_W m rom) (mkst regs' RUC_H m rom)
    /\ getr regs' 13 = Z_to_bv 64 Wd /\ regs_agree (fun r => In r [13]%list) regs regs'.
Proof.
  intros regs m Wd HW H17.
  unfold RUC_W, RUC_H.
  replace (0x7f4d8 : word) with (Z_to_bv 64 0x7f4d8) by (apply bv_eq; reflexivity).
  replace (0x7f4e0 : word) with (Z_to_bv 64 0x7f4e0) by (apply bv_eq; reflexivity).
  ex_entry regs [Wd] HR.
  assert (HK : SX2S.know_ok SEGS (ex_env regs [Wd]) m []) by (ex_know regs).
  ex_run 50%nat [0x7f4e0%Z] (SX2.SCR [false] [] []) HR HK R' HR' Hms.
  all: ruc_fin regs HR HR' Hms.
Qed.

Lemma ru_A1e : forall regs m (Wd : Z), (- 2 ^ 31 <= Wd <= 0)%Z -> getr regs 17 = Z_to_bv 64 Wd ->
  exists regs',
    msteps SEGS (mkst regs RUC_W m rom) (mkst regs' RUC_E m rom)
    /\ regs_agree (fun r => In r [13]%list) regs regs'.
Proof.
  intros regs m Wd HW H17.
  unfold RUC_W, RUC_E.
  replace (0x7f4d8 : word) with (Z_to_bv 64 0x7f4d8) by (apply bv_eq; reflexivity).
  replace (0x7fb08 : word) with (Z_to_bv 64 0x7fb08) by (apply bv_eq; reflexivity).
  ex_entry regs [Wd] HR.
  assert (HK : SX2S.know_ok SEGS (ex_env regs [Wd]) m []) by (ex_know regs).
  ex_run 50%nat [0x7fb08%Z] (SX2.SCR [true] [] []) HR HK R' HR' Hms.
  all: ruc_fin regs HR HR' Hms.
Qed.

(* [comment removed for export] *)
Lemma ru_A2g_run : forall regs m (dy dh dpixh : Z),
  (- 2 ^ 24 <= dy <= 2 ^ 24)%Z -> (0 <= dh <= 2 ^ 24)%Z -> (0 <= dpixh <= 2 ^ 24)%Z ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 6 = Z_to_bv 64 dh -> getr regs 12 = Z_to_bv 64 dpixh ->
  exists regs',
    msteps SEGS (mkst regs RUC_Y m rom) (mkst regs' RUC_W m rom)
    /\ getr regs' 16 = Z_to_bv 64 (Z.max 0 dy) /\ getr regs' 6 = Z_to_bv 64 (uclip_w dy dh dpixh)
    /\ regs_agree (fun r => In r [5; 6; 12; 13; 15; 16]%list) regs regs'.
Proof.
  intros regs m dy dh dpixh Hdy Hdh Hdph H16 H6 H12.
  unfold RUC_Y, RUC_W.
  replace (0x7f490 : word) with (Z_to_bv 64 0x7f490) by (apply bv_eq; reflexivity).
  replace (0x7f4d8 : word) with (Z_to_bv 64 0x7f4d8) by (apply bv_eq; reflexivity).
  ex_entry regs [dy; dh; dpixh] HR.
  assert (HK : SX2S.know_ok SEGS (ex_env regs [dy; dh; dpixh]) m []) by (ex_know regs).
  destruct (Z_lt_le_dec dy 0) as [Cy|Cy]; destruct (Z_le_gt_dec (Z.max 0 dy - dpixh + (dh + Z.min 0 dy)) 0) as [C|C].
  - ex_run 200%nat [0x7f4d8%Z] (SX2.SCR [false; false; false; false; true] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7f4d8%Z] (SX2.SCR [false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7f4d8%Z] (SX2.SCR [true; false; false; true] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
  - ex_run 200%nat [0x7f4d8%Z] (SX2.SCR [true; false; false; false; false] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
Qed.

Lemma ru_A2c : forall regs m (Hd : Z), (1 <= Hd < 2 ^ 31)%Z -> getr regs 6 = Z_to_bv 64 Hd ->
  exists regs',
    msteps SEGS (mkst regs RUC_H m rom) (mkst regs' RUC_A m rom)
    /\ getr regs' 12 = Z_to_bv 64 Hd /\ regs_agree (fun r => In r [12]%list) regs regs'.
Proof.
  intros regs m Hd HH H6.
  unfold RUC_H, RUC_A.
  replace (0x7f4e0 : word) with (Z_to_bv 64 0x7f4e0) by (apply bv_eq; reflexivity).
  replace (0x7f4e8 : word) with (Z_to_bv 64 0x7f4e8) by (apply bv_eq; reflexivity).
  ex_entry regs [Hd] HR.
  assert (HK : SX2S.know_ok SEGS (ex_env regs [Hd]) m []) by (ex_know regs).
  ex_run 50%nat [0x7f4e8%Z] (SX2.SCR [false] [] []) HR HK R' HR' Hms.
  all: ruc_fin regs HR HR' Hms.
Qed.

Lemma ru_A2e : forall regs m (Hd : Z), (- 2 ^ 31 <= Hd <= 0)%Z -> getr regs 6 = Z_to_bv 64 Hd ->
  exists regs',
    msteps SEGS (mkst regs RUC_H m rom) (mkst regs' RUC_E m rom)
    /\ regs_agree (fun r => In r [12]%list) regs regs'.
Proof.
  intros regs m Hd HH H6.
  unfold RUC_H, RUC_E.
  replace (0x7f4e0 : word) with (Z_to_bv 64 0x7f4e0) by (apply bv_eq; reflexivity).
  replace (0x7fb08 : word) with (Z_to_bv 64 0x7fb08) by (apply bv_eq; reflexivity).
  ex_entry regs [Hd] HR.
  assert (HK : SX2S.know_ok SEGS (ex_env regs [Hd]) m []) by (ex_know regs).
  ex_run 50%nat [0x7fb08%Z] (SX2.SCR [true] [] []) HR HK R' HR' Hms.
  all: ruc_fin regs HR HR' Hms.
Qed.

Lemma ru_A3 : forall regs m (DX a6 : Z), (0 <= DX < 2 ^ 31)%Z -> a6 = (DX mod 32)%Z -> getr regs 7 = Z_to_bv 64 DX ->
  exists regs',
    msteps SEGS (mkst regs RUC_A m rom) (mkst regs' (if Z.eq_dec a6 0 then RUC_M else RUC_G) m rom)
    /\ getr regs' 15 = Z_to_bv 64 a6 /\ regs_agree (fun r => In r [15]%list) regs regs'.
Proof.
  intros regs m DX a6 HDX Ha6 H7. subst a6.
  destruct (Z.eq_dec (DX mod 32) 0) as [E|E]; cbv beta iota; unfold RUC_A, RUC_M, RUC_G.
  - replace (0x7f4e8 : word) with (Z_to_bv 64 0x7f4e8) by (apply bv_eq; reflexivity).
    replace (0x7f5a8 : word) with (Z_to_bv 64 0x7f5a8) by (apply bv_eq; reflexivity).
    ex_entry regs [DX] HR.
    assert (HK : SX2S.know_ok SEGS (ex_env regs [DX]) m []) by (ex_know regs).
    ex_run 50%nat [0x7f5a8%Z] (SX2.SCR [true] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
  - replace (0x7f4e8 : word) with (Z_to_bv 64 0x7f4e8) by (apply bv_eq; reflexivity).
    replace (0x7f4f0 : word) with (Z_to_bv 64 0x7f4f0) by (apply bv_eq; reflexivity).
    ex_entry regs [DX] HR.
    assert (HK : SX2S.know_ok SEGS (ex_env regs [DX]) m []) by (ex_know regs).
    ex_run 50%nat [0x7f4f0%Z] (SX2.SCR [false] [] []) HR HK R' HR' Hms.
    all: ruc_fin regs HR HR' Hms.
Qed.
End Segs.

Section RopUniC.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition rasteropUniLow_clip_contract : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh op : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPUNI_STACK <= s)%Z -> (s + 16 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  (0 <= datad < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh 1 dwpl ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  (op = 0 \/ op = 15)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropUniLow) m al_rom) md) S.

Theorem rasteropUniLow_clip_W : rasteropUniLow_clip_contract.
Proof.
  unfold rasteropUniLow_clip_contract.
  intros C Ar A m md regs s datad dpixw dpixh dwpl dx dy0 dw dh0 op ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Hdd SHd Hdx Hdy Hdw Hdh Hop Ld Ld0 Ld00 HK.
  unfold PC_rasteropUniLow. replace (Z_to_bv 64 0x7f3d8) with RUC_P by (unfold RUC_P; apply bv_eq; reflexivity).
  destruct SHd as (Hd & Hdpw & Hdph & Ewd & Hszd).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 128 <= s)%Z) by (unfold ROPUNI_STACK in Hlo; exact Hlo).
  assert (Hhi' : (s <= c_top C)%Z) by lia.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (DV : dval 1) by (unfold dval; lia).
  pose proof (wpl_of_range dpixw 1 ltac:(lia) DV) as Hwd. rewrite <- Ewd in Hwd.
  pose proof (wpl_bits dpixw 1 ltac:(lia) ltac:(lia)) as WBd. rewrite <- Ewd in WBd.
  assert (Hph : (dwpl * dpixh <= 2 ^ 24)%Z) by lia.
  set (nd := (4 * (dwpl * dpixh))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; nia).
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (ru_A0g al_rom regs m s dpixw dx dw dh0 op ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rdh Rop H2 H11 H13 H15 H17)
    as (q0 & RN0 & UA2 & UA11 & UA6 & UA28 & UA7 & UA17 & AGa).
  rzs HW RN0.
  set (M1 := UF m s regs).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1) by (subst M1; unfold UF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (ucells_UF m s regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (UM1 : UMI C Ar A md s m datad nd (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) M1).
  { split; [exact HW1|]. split; [exact PM1|]. split; [exact CE1|].
    intros a Ha1 Ha2. subst M1. apply UF_outside; [lia | lia |]. intros X. apply Ha1. unfold scratch. lia. }
  assert (TBL : forall base, (base = 0x1f4c4 \/ base = 0x1f440)%Z -> forall j, (1 <= j <= 31)%Z ->
            exists (bs : list byte) (v : word), rdn SEGS M1 (Z_to_bv 64 (base + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v).
  { intros base Hb j Hj. destruct (tbl_rd base Hb j Hj) as (bs & Rb & Lb). destruct (le4_word bs Lb) as (v & Ev). exists bs, v. split; [|exact Ev].
    rewrite <- p16_segs. rewrite (W_rdn_ro C A M1 md (base + 4 * j) 4 HW1) by (destruct Hb as [-> | ->]; cbn; lia). rewrite p16_segs. exact Rb. }
  assert (KF : UKF C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) regs).
  { intros m' r' HW' PM' FT' Z2 Y0 Y1 Y2 Y3 (J1 & J3 & J4 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27).
    apply (HK m' r' HW'); [| exact PM' | exact FT'].
    apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | assumption ]. }
  assert (EMP : forall r, getr r 2 = Z_to_bv 64 (s - 32) -> keep11 regs r -> realizes SEGS (mkCfg (mkst r RUC_E M1 al_rom) md) S).
  { intros r R2 KPr. unfold RUC_E.
    destruct (vu_E al_rom r M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) Hret CE1 R2
                ltac:(destruct KPr as (K1 & _); rewrite K1; exact H1)) as (r9 & RN9 & Z2 & Z8 & Z9 & Z18 & Z19 & AG9).
    rzs HW1 RN9.
    destruct UM1 as (_ & _ & _ & FT1).
    apply (KF M1 r9 HW1 PM1 FT1 Z2 Z8 Z9 Z18 Z19).
    destruct KPr as (K1 & K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    unfold keep11. repeat split; csr; first [reflexivity | assumption]. }
  destruct (ru_A1g_run al_rom q0 M1 dx dw dpixw ltac:(lia) ltac:(lia) ltac:(lia) UA7 UA17 UA28) as (q1 & RN1 & UB17 & UB28 & UB29 & AGb).
  rzs HW1 RN1.
  destruct (ru_A2g_run al_rom q1 M1 dy0 dh0 dpixh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (q2 & RN2 & UC16 & UC6 & AGc).
  rzs HW1 RN2.
  destruct (Z_le_gt_dec (uclip_w dx dw dpixw) 0) as [WE | WC].
  { destruct (ru_A1e al_rom q2 M1 (uclip_w dx dw dpixw) ltac:(clear - WE Hdx Hdw Hdpw; unfold uclip_w in *; lia) ltac:(csr; reflexivity)) as (q3 & RN3 & AGd).
    rzs HW1 RN3. apply EMP; [csr; reflexivity | unfold keep11; repeat split; csr; reflexivity]. }
  destruct (ru_A1c al_rom q2 M1 (uclip_w dx dw dpixw) ltac:(clear - WC Hdx Hdw Hdpw; unfold uclip_w in *; lia) ltac:(csr; reflexivity)) as (q3 & RN3 & UD13 & AGd).
  rzs HW1 RN3.
  destruct (Z_le_gt_dec (uclip_w dy0 dh0 dpixh) 0) as [HE | HC].
  { destruct (ru_A2e al_rom q3 M1 (uclip_w dy0 dh0 dpixh) ltac:(clear - HE Hdy Hdh Hdph; unfold uclip_w in *; lia) ltac:(csr; reflexivity)) as (q4 & RN4 & AGe).
    rzs HW1 RN4. apply EMP; [csr; reflexivity | unfold keep11; repeat split; csr; reflexivity]. }
  destruct (ru_A2c al_rom q3 M1 (uclip_w dy0 dh0 dpixh) ltac:(clear - HC Hdy Hdh Hdph; unfold uclip_w in *; lia) ltac:(csr; reflexivity)) as (q4 & RN4 & UE12 & AGe).
  rzs HW1 RN4.
  pose proof (uclip_facts dx dw dpixw ltac:(lia) ltac:(lia)) as (HDX0 & HDXW & HDWw).
  pose proof (uclip_facts dy0 dh0 dpixh ltac:(lia) ltac:(lia)) as (Hdy0 & Hdyh & Hdhh).
  set (DX := Z.max 0 dx) in *. set (DW := uclip_w dx dw dpixw) in *.
  set (dy := Z.max 0 dy0) in *. set (dh := uclip_w dy0 dh0 dpixh) in *.
  clearbody DX DW dy dh.
  assert (Hdh1 : (1 <= dh)%Z) by lia.
  assert (HDX : (0 <= DX <= 160000)%Z) by lia. assert (HDW : (1 <= DW <= 160000)%Z) by lia.
  assert (Mdy : (0 <= dy * dwpl < 2 ^ 24)%Z) by (clear - Hph Hdyh Hdh1 Hdy0 Hwd; nia).
  assert (Mdh : (dh * dwpl <= 2 ^ 24)%Z) by (clear - Hph Hdyh Hdh1 Hdy0 Hwd; nia).
  set (a6 := (DX mod 32)%Z). set (cdx := (DX / 32)%Z).
  pose proof (Z.div_mod DX 32 ltac:(lia)) as EDX. fold cdx a6 in EDX. pose proof (Z.mod_pos_bound DX 32 ltac:(lia)) as Ha6. fold a6 in Ha6.
  assert (Hcdx : (0 <= cdx < 2 ^ 26)%Z) by lia.
  assert (SET : exists set : bool, op = (if set then 15 else 0)%Z) by (destruct Hop as [-> | ->]; [exists false | exists true]; reflexivity).
  destruct SET as [set Eop].
  destruct (ru_A3 al_rom q4 M1 DX a6 ltac:(lia) eq_refl ltac:(csr; reflexivity)) as (r1 & RN5 & Q15 & AGf).
  rzs HW1 RN5.
  assert (KP1 : keep11 regs r1) by (unfold keep11; repeat split; csr; reflexivity).
  assert (Q13 : getr r1 13 = Z_to_bv 64 DW) by (csr; reflexivity).
  assert (Q12 : getr r1 12 = Z_to_bv 64 dh) by (csr; reflexivity).
  assert (Q29 : getr r1 29 = Z_to_bv 64 DX) by (csr; reflexivity).
  assert (E2 : getr r1 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E17 : getr r1 17 = Z_to_bv 64 DW) by (csr; reflexivity).
  assert (E7 : getr r1 7 = Z_to_bv 64 DX) by (csr; reflexivity).
  assert (E11 : getr r1 11 = Z_to_bv 64 op) by (csr; reflexivity).
  assert (E10 : getr r1 10 = Z_to_bv 64 datad) by (csr; reflexivity).
  assert (E16 : getr r1 16 = Z_to_bv 64 dy) by (csr; reflexivity).
  assert (E14 : getr r1 14 = Z_to_bv 64 dwpl) by (csr; reflexivity).
  assert (E6 : getr r1 6 = Z_to_bv 64 dh) by (csr; reflexivity).
  clear AGa AGb AGc AGd AGe AGf RN0 RN1 RN2 RN3 RN4 RN5.
  unfold RUC_M, RUC_G.
  destruct (Z.eq_dec a6 0) as [AL0 | NAL].
  -
    set (nfw := (DW / 32)%Z). set (k := (DW mod 32)%Z).
    pose proof (Z.div_mod DW 32 ltac:(lia)) as EDW. fold nfw k in EDW. pose proof (Z.mod_pos_bound DW 32 ltac:(lia)) as Hk. fold k in Hk.
    assert (Hnfw : (0 <= nfw < 2 ^ 26)%Z) by lia.
    pose proof (col_bound DX DW dwpl cdx nfw k ltac:(lia) EDW Hk ltac:(lia)) as CBd.
    destruct (vu_M al_rom r1 M1 DW k ltac:(lia) eq_refl Hk (TBL 0x1f4c4%Z ltac:(left; reflexivity)) E17) as (r2 & RUN2 & W15 & AG2).
    rzs HW1 RUN2.
    destruct (vu_S al_rom set r2 M1 DW DX nfw cdx op datad dy dwpl ltac:(lia) ltac:(lia) eq_refl eq_refl Eop ltac:(lia) ltac:(lia) Mdy Hcdx ltac:(lia) ltac:(lia)
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r3 & RUN3 & X5 & X16 & X17 & X29 & X30 & AG3).
    rzs HW1 RUN3.
    pose proof (UMI_geom C Ar A md s m datad nd (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) CK Hlo Ld Hdd Hnd M1 UM1) as (_ & _ & _ & _ & AL16).
    destruct (vu_S2 al_rom set r3 M1 datad (4 * cdx) (4 * (dy * dwpl)) ltac:(lia) ltac:(apply mod16_mod4; exact AL16) ltac:(csr; reflexivity) X29 X30
                ltac:(csr; rewrite Eop; reflexivity)) as (r4 & RUN4 & Y7 & Y11 & Y28 & Y10 & Ypf & Y5 & AG4).
    rzs HW1 RUN4.
    set (pf := (datad + 4 * (dy * dwpl) + 4 * cdx)%Z) in *.
    apply (U_arows C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) regs CK Hlo Hhi' SUB Ld Ld0 Ld00 Hdd Hnd
             set pf nfw k DW dh dwpl r4 M1 Hret H1 ltac:(lia) EDW Hk Hnfw ltac:(lia) ltac:(lia) Mdh).
    + exists (dy * dwpl + cdx)%Z. subst pf. lia.
    + intros i' Hi'. subst pf nd.
      pose proof (rop_rows_in datad dwpl dpixh dy dh cdx (nfw + (if Z.eq_dec k 0 then 0 else 1))%Z i' ltac:(lia) ltac:(lia) ltac:(destruct (Z.eq_dec k 0); lia) CBd Hdyh Hi') as [X1 X2].
      split; lia.
    + exact UM1.
    + unfold keep11. destruct KP1 as (J1 & J3 & J4 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27). repeat split; csr; reflexivity.
    + csr. reflexivity.
    + exact Y7.
    + exact Y11.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + exact Y10.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + exact Y28.
    + rewrite Ypf. subst pf. f_equal. lia.
    + exact Y5.
    + exact KF.
  -
    destruct (vu_G0 al_rom r1 M1 a6 DW DX cdx datad dy dwpl ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Mdy Hcdx ltac:(lia) ltac:(lia)
                (TBL 0x1f440%Z ltac:(right; reflexivity)) Q15 E17 Q13 E7 E10 E16 E14) as (r2 & RUN2 & W30 & W5 & W16 & W10 & AG2).
    rzs HW1 RUN2.
    set (pfp := (datad + 4 * (dy * dwpl) + 4 * cdx)%Z) in *.
    set (lw2 := ((DX + DW) mod 32)%Z).
    pose proof (Z.mod_pos_bound (DX + DW) 32 ltac:(lia)) as Hlw. fold lw2 in Hlw.
    assert (EXp : exists X, pfp = (datad + 4 * X)%Z) by (exists (dy * dwpl + cdx)%Z; subst pfp; lia).
    destruct (Z.ltb_spec DW (32 - a6)) as [DBL | BIG].
    +
      destruct (vu_G1d al_rom r2 M1 a6 DW ltac:(lia) ltac:(lia) DBL (TBL 0x1f4c4%Z ltac:(left; reflexivity)) W10) as (r3 & RUN3 & X15 & X16 & X28 & AG3).
      rzs HW1 RUN3.
      destruct (vu_G2a al_rom r3 M1 DX DW (32 - a6) lw2 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl Hlw ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (r4 & RUN4 & Y17 & Y10 & AG4).
      rzs HW1 RUN4.
      replace (DW <? 32 - a6)%Z with true in Y17 by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in Y17.
      destruct (vu_G2b al_rom set true r4 M1 lw2 pfp 0 op I ltac:(subst pfp; lia) ltac:(lia) ltac:(subst pfp; lia) Eop (TBL 0x1f4c4%Z ltac:(left; reflexivity)) Y17 Y10
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r5 & RUN5 & _ & AG5).
      rzs HW1 RUN5.
      apply (U_general C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) regs CK Hlo Hhi' SUB Ld Ld0 Ld00 Hdd Hnd
               set false true pfp dh dwpl 0 r5 M1 Hret H1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros X; discriminate X) ltac:(intros _; reflexivity) EXp).
      * intros i' Hi'. subst pfp nd.
        pose proof (rop_rows_in datad dwpl dpixh dy dh cdx 1 i' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdyh Hi') as [X1 X2]. split; lia.
      * exact UM1.
      * unfold keep11. destruct KP1 as (J1 & J3 & J4 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27). repeat split; csr; reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * intros X; discriminate X.
      * intros X; discriminate X.
      * exact KF.
    +
      set (R := (DW - (32 - a6))%Z) in *. set (dnf := (R / 32)%Z).
      pose proof (Z.div_mod R 32 ltac:(lia)) as ER. fold dnf in ER. pose proof (Z.mod_pos_bound R 32 ltac:(lia)) as HRm.
      assert (Elw : lw2 = (R mod 32)%Z) by (subst lw2; replace (DX + DW)%Z with (R + (cdx + 1) * 32)%Z by lia; apply Z_mod_plus_full).
      assert (Hdnf : (0 <= dnf < 2 ^ 26)%Z) by lia.
      destruct (vu_G1a al_rom r2 M1 R dnf pfp ltac:(lia) eq_refl ltac:(subst pfp; lia) ltac:(subst pfp; lia) W10 W5) as (r3 & RUN3 & X15 & X28 & X16 & AG3).
      rzs HW1 RUN3.
      destruct (vu_G2a al_rom r3 M1 DX DW (32 - a6) lw2 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl Hlw ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (r4 & RUN4 & Y17 & Y10 & AG4).
      rzs HW1 RUN4.
      replace (DW <? 32 - a6)%Z with false in Y17 by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in Y17.
      assert (CB : (cdx + (1 + dnf + (if (lw2 =? 0)%Z then 0 else 1)) <= dwpl)%Z) by (destruct (Z.eqb_spec lw2 0); lia).
      destruct (vu_G2b al_rom set (lw2 =? 0)%Z r4 M1 lw2 pfp dnf op ltac:(destruct (Z.eqb_spec lw2 0); [exact I | lia]) ltac:(subst pfp; lia) Hdnf
                  ltac:(subst pfp; lia) Eop (TBL 0x1f4c4%Z ltac:(left; reflexivity)) Y17 Y10
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r5 & RUN5 & Z10 & AG5).
      rzs HW1 RUN5.
      apply (U_general C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) regs CK Hlo Hhi' SUB Ld Ld0 Ld00 Hdd Hnd
               set (negb (dnf =? 0)%Z) (lw2 =? 0)%Z pfp dh dwpl dnf r5 M1 Hret H1 ltac:(lia) ltac:(lia) Hdnf).
      * intros X. destruct (Z.eqb_spec dnf 0) as [Y|Y]; [discriminate X | lia].
      * intros X. destruct (Z.eqb_spec dnf 0) as [Y|Y]; [exact Y | discriminate X].
      * exact EXp.
      * intros i' Hi'. subst pfp nd.
        pose proof (rop_rows_in datad dwpl dpixh dy dh cdx (1 + dnf + (if (lw2 =? 0)%Z then 0 else 1))%Z i' ltac:(lia) ltac:(lia) ltac:(destruct (lw2 =? 0)%Z; lia) CB Hdyh Hi') as [X1 X2].
        split; [lia|]. destruct (lw2 =? 0)%Z; lia.
      * exact UM1.
      * unfold keep11. destruct KP1 as (J1 & J3 & J4 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27). repeat split; csr; reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * rewrite (AG5 28) by (cbv; intuition discriminate). rewrite (AG4 28) by (cbv; intuition discriminate). rewrite X28. destruct (dnf =? 0)%Z; reflexivity.
      * csr. reflexivity.
      * intros X. destruct (Z.eqb_spec dnf 0) as [Y|Y]; [discriminate X|]. csr. exact (X16 Y).
      * exact Z10.
      * exact KF.
Qed.

End RopUniC.
