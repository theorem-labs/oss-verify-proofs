(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptArith2 LibAtomic LeptRecs LeptSlots.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8LeptStderr O8LeptBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8CL7a.
Import O8CL7a.O8LeptErr. Import O8CL7a.O8LeptPixMisc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8CL8a.
Import O8CL8a.O8LeptBox.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8LeptBoxa O8LeptPtra O8LeptPixa.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8CL11a.
Import O8CL11a.O8LeptCf.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8_code_13660_14000 O8_code_14000_15000 O8_code_15000_16000 O8_code_16000_17000 O8_code_17000_18000.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomCF.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Local Ltac forall_cells := repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

(* [comment removed for export] *)
Lemma v_divw_1 : forall a, (0 <= a < 2 ^ 31)%Z -> v_divw (Z_to_bv 64 a) (Z_to_bv 64 1) = Z_to_bv 64 a.
Proof.
  intros a Ha. unfold v_divw. rewrite !u_Z2bv by lia. change (bv_wrap 32 1) with 1%Z. cbn [Z.eqb].
  assert (E1 : bv_swrap 32 1 = 1%Z) by reflexivity. rewrite E1.
  assert (Ea : bv_swrap 32 a = a) by (apply bv_swrap_small; change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
  rewrite Ea, Z.quot_1_r, Ea. reflexivity.
Qed.

Section CfCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL8} {PN8 : O8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Definition ccF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
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
      (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)).
  Definition cc_cells (m : word -> option byte) (s : Z) (ret : word) (R : bvmap 5 word) : Prop :=
    cellsZ m [(s - 8, ret); (s - 16, getr R 8); (s - 24, getr R 9); (s - 32, getr R 18); (s - 40, getr R 19);
              (s - 48, getr R 20); (s - 56, getr R 21); (s - 64, getr R 22); (s - 72, getr R 23);
              (s - 80, getr R 24); (s - 88, getr R 25); (s - 96, getr R 26)]%Z.
  Lemma ccF_cells : forall m s ret regs, (112 <= s)%Z -> (s < 2 ^ 64)%Z -> cc_cells (ccF m s ret regs) s ret regs.
  Proof. intros m s ret regs Hs Hs64. unfold cc_cells, ccF. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  (* [comment removed for export] *)
  Lemma cc_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix + 64 <= s - 112)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> PIXat m pix v ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x16604 : word) m rom) (mkst regs' (0x16650 : word) (ccF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 1 /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 pix
      /\ getr regs' 10 = Z_to_bv 64 (p_d v) /\ getr regs' 11 = Z_to_bv 64 32
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 Hpix Hpixs SOK PX H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    assert (PX' : PIXat (ccF m s ret regs) pix v).
    { unfold ccF. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    eexists. split.
    - zv F_16500 D_16500 (Z_to_bv 64 (s - 112)).
      stepST F_16504 D_16504 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16508 D_16508 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1650c D_1650c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_16510 D_16510 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_16514 D_16514 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_16518 D_16518 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_1651c D_1651c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_16520 D_16520 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_16524 D_16524 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_16528 D_16528 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_1652c D_1652c (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_16530 D_16530 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepb_ft F_16534 D_16534 ltac:(condZ).
      sn F_16538 D_16538. sn F_1653c D_1653c. sn F_16540 D_16540. sn F_16544 D_16544.
      change (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) with (ccF m s ret regs).
      (* [comment removed for export] *)
      stepb_ft F_15468 D_15468 ltac:(condZ).
      stepLD F_1546c D_1546c (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; exact (PIX_rd_d SEGS _ _ _ PX')) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia.
      stepret F_15470 D_15470 (Z_to_bv 64 0x1664c) ltac:(bveq).
      sn F_16548 D_16548.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_D : forall regs m (s d : Z) (ret : word) (R : bvmap 5 word),
    (0x52000 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 31)%Z -> d <> 32%Z ->
    rdn SEGS m (Z_to_bv 64 0x1ffa0) 8 = Some (Z_to_le_bytes 8 0x21010) ->
    rdn SEGS m (Z_to_bv 64 0x21010) 4 = Some (Z_to_le_bytes 4 3) ->
    cc_cells m s ret R ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 32 ->
    exists regs',
      msteps SEGS (mkst regs (0x16650 : word) m rom) (mkst regs' (0x13e20 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10570 /\ getr regs' 11 = Z_to_bv 64 0x10492 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = getr R 8 /\ getr regs' 9 = getr R 9 /\ getr regs' 18 = getr R 18 /\ getr regs' 19 = getr R 19
      /\ getr regs' 20 = getr R 20 /\ getr regs' 21 = getr R 21 /\ getr regs' 22 = getr R 22 /\ getr regs' 23 = getr R 23
      /\ getr regs' 24 = getr R 24 /\ getr regs' 25 = getr R 25 /\ getr regs' 26 = getr R 26
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s d ret R Hs Hs64 Hd Hd32 Rg Rs CE H2 H10 H11.
    destruct CE as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & _).
    eexists. split.
    - stepb_tk F_1654c D_1654c ltac:(condZ).
      sn F_16614 D_16614.
      stepLD F_16618 D_16618 (Z_to_le_bytes 8 0x21010) (Z_to_bv 64 0x21010) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1661c D_1661c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16620 D_16620.
      stepb_ft F_16624 D_16624 ltac:(condZ).
      sn F_16628 D_16628. sn F_1662c D_1662c. sn F_16630 D_16630. sn F_16634 D_16634. sn F_16638 D_16638.
      stepLD8 F_1663c D_1663c ret. stepLD8 F_16640 D_16640 (getr R 8). stepLD8 F_16644 D_16644 (getr R 9).
      stepLD8 F_16648 D_16648 (getr R 18). stepLD8 F_1664c D_1664c (getr R 19). stepLD8 F_16650 D_16650 (getr R 20).
      stepLD8 F_16654 D_16654 (getr R 21). stepLD8 F_16658 D_16658 (getr R 22). stepLD8 F_1665c D_1665c (getr R 23).
      stepLD8 F_16660 D_16660 (getr R 24). stepLD8 F_16664 D_16664 (getr R 25). stepLD8 F_16668 D_16668 (getr R 26).
      zv F_1666c D_1666c (Z_to_bv 64 s).
      sn F_16670 D_16670.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma cc_B : forall regs m (s pix : Z) (v : pixv),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix + 64 <= s - 112)%Z -> p_d v = 32%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> PIXat m pix v ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 9 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 pix ->
    getr regs 10 = Z_to_bv 64 (p_d v) -> getr regs 11 = Z_to_bv 64 32 ->
    exists regs',
      msteps SEGS (mkst regs (0x16650 : word) m rom)
                  (mkst regs' (0x16674 : word)
                     (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                        (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                        (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))))
                        (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 (p_h v)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 19 = Z_to_bv 64 (p_w v) /\ getr regs' 10 = Z_to_bv 64 10
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 19]%list) regs regs'.
  Proof.
    intros regs m s pix v Hs Hs64 Hpix Hpixs Hd SOK PX H2 H9 H18 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    eexists. split.
    - stepb_ft F_1654c D_1654c ltac:(condZ).
      zv F_16550 D_16550 (Z_to_bv 64 (s - 100)).
      zv F_16554 D_16554 (Z_to_bv 64 (s - 104)).
      sn F_16558 D_16558. sn F_1655c D_1655c. sn F_16560 D_16560.
      (* [comment removed for export] *)
      stepb_ft F_1527c D_1527c ltac:(condZ).
      stepST F_15280 D_15280 (Z_to_bv 64 (s - 100)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15284 D_15284 ltac:(condZ).
      stepST F_15288 D_15288 (Z_to_bv 64 (s - 104)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_1528c D_1528c ltac:(condZ).
      stepb_ft F_15294 D_15294 ltac:(condZ).
      stepb_ft F_15298 D_15298 ltac:(condZ).
      stepLD F_1529c D_1529c (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_152a0 D_152a0 (Z_to_bv 64 (s - 100)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_152a4 D_152a4 ltac:(condZ).
      stepLD F_152a8 D_152a8 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_152ac D_152ac (Z_to_bv 64 (s - 104)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      sn F_152b0 D_152b0.
      stepb_tk F_152b4 D_152b4 ltac:(condZ).
      sn F_152c0 D_152c0.
      stepret F_152c4 D_152c4 (Z_to_bv 64 0x16668) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_16564 D_16564 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; rewrite <- (w2b_Z 4 (p_w v)) by lia; rdn_chain) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      sn F_16568 D_16568. fixv (Z_to_bv 64 (p_w v)) ltac:(rewrite v_divw_1 by lia; reflexivity).
      sn F_1656c D_1656c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma cc_C : forall regs m (s w h : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (10 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 8 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 w -> getr regs 10 = Z_to_bv 64 10 ->
    exists regs',
      msteps SEGS (mkst regs (0x16674 : word) m rom) (mkst regs' (0x16684 : word) m rom)
      /\ getr regs' 21 = Z_to_bv 64 h /\ getr regs' 10 = Z_to_bv 64 9
      /\ regs_agree (fun r => In r [10; 21]%list) regs regs'.
  Proof.
    intros regs m s w h Hs Hs64 Hw Hh Rh H2 H8 H19 H10.
    eexists. split.
    - stepb_ft F_16570 D_16570 ltac:(condZ).
      stepLD F_16574 D_16574 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply lez4; lia).
      rewrite (v_lw_small h) by lia.
      sn F_16578 D_16578. fixv (Z_to_bv 64 h) ltac:(rewrite v_divw_1 by lia; reflexivity).
      sn F_1657c D_1657c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_E1 : forall regs m (w : Z),
    (0 <= w < 10)%Z -> getr regs 19 = Z_to_bv 64 w -> getr regs 10 = Z_to_bv 64 10 ->
    msteps SEGS (mkst regs (0x16674 : word) m rom) (mkst regs (0x16778 : word) m rom).
  Proof. intros regs m w Hw H19 H10. stepb_tk F_16570 D_16570 ltac:(condZ). apply mst_refl. Qed.
  Lemma cc_E2 : forall regs m (h : Z),
    (0 <= h < 10)%Z -> getr regs 21 = Z_to_bv 64 h -> getr regs 10 = Z_to_bv 64 9 ->
    msteps SEGS (mkst regs (0x16684 : word) m rom) (mkst regs (0x16778 : word) m rom).
  Proof. intros regs m h Hh H21 H10. stepb_tk F_16580 D_16580 ltac:(condZ). apply mst_refl. Qed.

  (* [comment removed for export] *)
  Lemma cc_err : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x1ffa0) 8 = Some (Z_to_le_bytes 8 0x21010) ->
    rdn SEGS m (Z_to_bv 64 0x21010) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16778 : word) m rom) (mkst regs' (0x13e20 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x167a4 /\ getr regs' 10 = Z_to_bv 64 0x103f4 /\ getr regs' 11 = Z_to_bv 64 0x10492 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs. eexists. split.
    - sn F_16674 D_16674.
      stepLD F_16678 D_16678 (Z_to_le_bytes 8 0x21010) (Z_to_bv 64 0x21010) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1667c D_1667c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16680 D_16680.
      stepb_ft F_16684 D_16684 ltac:(condZ).
      sn F_16688 D_16688. sn F_1668c D_1668c. sn F_16690 D_16690. sn F_16694 D_16694.
      sn F_16698 D_16698. sn F_1669c D_1669c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_P : forall regs m (s : Z) (ret : word) (R : bvmap 5 word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cc_cells m s ret R ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs',
      msteps SEGS (mkst regs (0x167a4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 10
      /\ getr regs' 8 = getr R 8 /\ getr regs' 9 = getr R 9 /\ getr regs' 18 = getr R 18 /\ getr regs' 19 = getr R 19
      /\ getr regs' 20 = getr R 20 /\ getr regs' 21 = getr R 21 /\ getr regs' 22 = getr R 22 /\ getr regs' 23 = getr R 23
      /\ getr regs' 24 = getr R 24 /\ getr regs' 25 = getr R 25 /\ getr regs' 26 = getr R 26
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s ret R Hs Hs64 Hret CE H2.
    destruct CE as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & _).
    eexists. split.
    - sn F_166a0 D_166a0.
      stepLD8 F_16708 D_16708 ret. stepLD8 F_1670c D_1670c (getr R 8). stepLD8 F_16710 D_16710 (getr R 9).
      stepLD8 F_16714 D_16714 (getr R 18). stepLD8 F_16718 D_16718 (getr R 19). stepLD8 F_1671c D_1671c (getr R 20).
      stepLD8 F_16720 D_16720 (getr R 21). stepLD8 F_16724 D_16724 (getr R 22). stepLD8 F_16728 D_16728 (getr R 23).
      stepLD8 F_1672c D_1672c (getr R 24). stepLD8 F_16730 D_16730 (getr R 25). stepLD8 F_16734 D_16734 (getr R 26).
      zv F_16738 D_16738 (Z_to_bv 64 s).
      stepret F_1673c D_1673c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_F : forall regs m (h : Z),
    (10 <= h < 2 ^ 31)%Z -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 h -> getr regs 10 = Z_to_bv 64 9 ->
    exists regs',
      msteps SEGS (mkst regs (0x16684 : word) m rom) (mkst regs' (0x14804 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x16694 /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 20 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 20]%list) regs regs'.
  Proof.
    intros regs m h Hh H8 H9 H21 H10. eexists. split.
    - stepb_ft F_16580 D_16580 ltac:(condZ).
      sn F_16584 D_16584. fixv (Z_to_bv 64 1) ltac:(rewrite zbv_mulw_small by lia; reflexivity).
      sn F_16588 D_16588. sn F_1658c D_1658c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_G : forall regs m (s ba w h : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= ba < 2 ^ 64)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 ba -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 1 ->
    getr regs 19 = Z_to_bv 64 w -> getr regs 21 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x16694 : word) m rom) (mkst regs' (0x14684 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x166d0
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 w /\ getr regs' 13 = Z_to_bv 64 h
      /\ getr regs' 22 = Z_to_bv 64 ba /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 0 /\ getr regs' 26 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s ba w h Hs Hs64 Hba Hw Hh SOK H2 H10 H8 H9 H19 H21. eexists. split.
    - sn F_16590 D_16590.
      stepb_ft F_16594 D_16594 ltac:(condZ).
      sn F_16598 D_16598. sn F_1659c D_1659c.
      stepb_ft F_165a8 D_165a8 ltac:(condZ).
      sn F_165ac D_165ac.
      sn F_165b0 D_165b0. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_mulw_small by lia; reflexivity).
      sn F_165b4 D_165b4. sn F_165b8 D_165b8. sn F_165bc D_165bc. sn F_165c0 D_165c0. sn F_165c4 D_165c4. sn F_165c8 D_165c8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_H : forall regs m (ba : Z) (bx : word),
    getr regs 10 = bx -> getr regs 22 = Z_to_bv 64 ba ->
    exists regs',
      msteps SEGS (mkst regs (0x166d0 : word) m rom) (mkst regs' (0x14a60 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x166e0 /\ getr regs' 10 = Z_to_bv 64 ba /\ getr regs' 11 = bx /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m ba bx H10 H22. eexists. split.
    - sn F_165cc D_165cc. sn F_165d0 D_165d0. sn F_165d4 D_165d4. sn F_165d8 D_165d8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_I : forall regs m (w : Z),
    (0 <= w < 2 ^ 31)%Z ->
    getr regs 8 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 w -> getr regs 23 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x166e0 : word) m rom) (mkst regs' (0x1731c : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x167bc /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 88
      /\ regs_agree (fun r => In r [1; 10; 11; 23; 25; 26]%list) regs regs'.
  Proof.
    intros regs m w Hw H8 H19 H23 H25 H26. eexists. split.
    - sn F_165dc D_165dc.
      sn F_165e0 D_165e0. fixv (Z_to_bv 64 w) ltac:(rewrite v_addw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_165e4 D_165e4 ltac:(condZ).
      sn F_165e8 D_165e8.
      sn F_165a0 D_165a0. fixv (Z_to_bv 64 1) ltac:(rewrite zbv_addiw_small by lia; reflexivity).
      stepb_tk F_165a4 D_165a4 ltac:(condZ).
      sn F_166ac D_166ac. sn F_166b0 D_166b0. sn F_166b4 D_166b4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_J : forall regs m (s cf pix w h ba : Z) (v : pixv),
    (1 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix mod 16 = 0)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (0 <= ba < 2 ^ 64)%Z ->
    PIXat m pix v -> p_rc v = 1%Z -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true -> store_ok SEGS m (Z_to_bv 64 cf) 88 = true ->
    (cf + 88 <= pix \/ pix + 64 <= cf)%Z ->
    getr regs 10 = Z_to_bv 64 cf -> getr regs 18 = Z_to_bv 64 pix -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 1 ->
    getr regs 19 = Z_to_bv 64 w -> getr regs 21 = Z_to_bv 64 h -> getr regs 22 = Z_to_bv 64 ba -> getr regs 20 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x167bc : word) m rom)
                  (mkst regs' (0x1420c : word)
                     (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 2)))
                        (Z_to_bv 64 cf) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
                        (Z_to_bv 64 (cf + 16)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
                        (Z_to_bv 64 (cf + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
                        (Z_to_bv 64 (cf + 24)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
                        (Z_to_bv 64 (cf + 28)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
                        (Z_to_bv 64 (cf + 40)) (word_to_le_bytes 8 (Z_to_bv 64 ba))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x167e8 /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 cf
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 23]%list) regs regs'.
  Proof.
    intros regs m s cf pix w h ba v Hcf Hcf64 Hpix Hal Hw Hh Hba PX RC SOKx SOKc DJ H10 H18 H8 H9 H19 H21 H22 H20.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - sn F_166b8 D_166b8. sn F_166bc D_166bc. sn F_166c0 D_166c0.
      (* [comment removed for export] *)
      stepb_ft F_153e0 D_153e0 ltac:(condZ).
      zv F_153e4 D_153e4 (Z_to_bv 64 (pix + 20)).
      sn F_153e8 D_153e8.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_153ec eq_refl D_153ec);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; rewrite <- RC; exact (PIX_rd_rc SEGS _ _ _ PX)
          | apply lez4; lia
          | gres; sok_in SOKx ]
        | step_simpl ].
      gres. rewrite zbv_add. change (1 + 1)%Z with 2%Z.
      stepret F_153f0 D_153f0 (Z_to_bv 64 0x167c8) ltac:(bveq).
      (* [comment removed for export] *)
      stepST F_166c4 D_166c4 (Z_to_bv 64 cf) (Z_to_bv 64 pix) ltac:(sok_in SOKc).
      stepST F_166c8 D_166c8 (Z_to_bv 64 (cf + 16)) (Z_to_bv 64 1) ltac:(sok_in SOKc).
      stepST F_166cc D_166cc (Z_to_bv 64 (cf + 20)) (Z_to_bv 64 1) ltac:(sok_in SOKc).
      stepST F_166d0 D_166d0 (Z_to_bv 64 (cf + 24)) (Z_to_bv 64 w) ltac:(sok_in SOKc).
      stepST F_166d4 D_166d4 (Z_to_bv 64 (cf + 28)) (Z_to_bv 64 h) ltac:(sok_in SOKc).
      stepST F_166d8 D_166d8 (Z_to_bv 64 (cf + 40)) (Z_to_bv 64 ba) ltac:(sok_in SOKc).
      sn F_166dc D_166dc. sn F_166e0 D_166e0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_K : forall regs m (cf naa : Z),
    (1 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> (0 <= naa < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 cf) 88 = true ->
    getr regs 10 = Z_to_bv 64 naa -> getr regs 23 = Z_to_bv 64 cf -> getr regs 20 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x167e8 : word) m rom) (mkst regs' (0x13fc0 : word) (wbytes m (Z_to_bv 64 (cf + 64)) (word_to_le_bytes 8 (Z_to_bv 64 naa))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x167f4 /\ getr regs' 10 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf naa Hcf Hcf64 Hnaa SOKc H10 H23 H20. eexists. split.
    - stepST F_166e4 D_166e4 (Z_to_bv 64 (cf + 64)) (Z_to_bv 64 naa) ltac:(sok_in SOKc).
      sn F_166e8 D_166e8. sn F_166ec D_166ec. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_L : forall regs m (cf dnaa : Z),
    (1 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> (0 <= dnaa < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 cf) 88 = true ->
    getr regs 10 = Z_to_bv 64 dnaa -> getr regs 23 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x167f4 : word) m rom) (mkst regs' (0x14458 : word) (wbytes m (Z_to_bv 64 (cf + 72)) (word_to_le_bytes 8 (Z_to_bv 64 dnaa))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x16800 /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf dnaa Hcf Hcf64 Hd SOKc H10 H23. eexists. split.
    - stepST F_166f0 D_166f0 (Z_to_bv 64 (cf + 72)) (Z_to_bv 64 dnaa) ltac:(sok_in SOKc).
      sn F_166f4 D_166f4. sn F_166f8 D_166f8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_M : forall regs m (s cf px : Z) (ret : word) (R : bvmap 5 word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cf)%Z -> (cf + 88 <= s - 112)%Z -> (0 <= px < 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 cf) 88 = true -> cc_cells m s ret R ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 px -> getr regs 23 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x16800 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (cf + 80)) (word_to_le_bytes 8 (Z_to_bv 64 px))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 cf
      /\ getr regs' 8 = getr R 8 /\ getr regs' 9 = getr R 9 /\ getr regs' 18 = getr R 18 /\ getr regs' 19 = getr R 19
      /\ getr regs' 20 = getr R 20 /\ getr regs' 21 = getr R 21 /\ getr regs' 22 = getr R 22 /\ getr regs' 23 = getr R 23
      /\ getr regs' 24 = getr R 24 /\ getr regs' 25 = getr R 25 /\ getr regs' 26 = getr R 26
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s cf px ret R Hs Hs64 Hcf Hcfs Hpx Hret SOKc CE H2 H10 H23.
    destruct CE as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & _).
    eexists. split.
    - sn F_166fc D_166fc. sn F_16700 D_16700.
      stepST F_16704 D_16704 (Z_to_bv 64 (cf + 80)) (Z_to_bv 64 px) ltac:(sok_in SOKc).
      stepLD8 F_16708 D_16708 ret. stepLD8 F_1670c D_1670c (getr R 8). stepLD8 F_16710 D_16710 (getr R 9).
      stepLD8 F_16714 D_16714 (getr R 18). stepLD8 F_16718 D_16718 (getr R 19). stepLD8 F_1671c D_1671c (getr R 20).
      stepLD8 F_16720 D_16720 (getr R 21). stepLD8 F_16724 D_16724 (getr R 22). stepLD8 F_16728 D_16728 (getr R 23).
      stepLD8 F_1672c D_1672c (getr R 24). stepLD8 F_16730 D_16730 (getr R 25). stepLD8 F_16734 D_16734 (getr R 26).
      zv F_16738 D_16738 (Z_to_bv 64 s).
      stepret F_1673c D_1673c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ccF_out : forall m s ret regs (x : word), (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 112 \/ s <= u x)%Z -> ccF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold ccF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.

Lemma str_not32 : str16 0x10570 15. Proof. str16_tac. Qed.
Lemma str_cfCreate : str16 0x10492 17. Proof. str16_tac. Qed.
Lemma str_tile : str16 0x103f4 19. Proof. str16_tac. Qed.

Section CWalk.
  Variables (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s pix : Z) (v : pixv) (ret : word) (S : TSet).
  Hypothesis CK : Cok C.
  Hypothesis HW : W C A m md.
  Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
  Hypothesis Hs16 : (s mod 16 = 0)%Z.
  Hypothesis Hlo : (c_top C - LSTK + 208 + LSF <= s)%Z.
  Hypothesis Hhi : (s <= c_top C)%Z.
  Hypothesis H1 : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis H4 : getr regs 4 = Z_to_bv 64 0x31370.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 pix.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 1.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 1.
  Hypothesis PX : PIXat m pix v.
  Hypothesis RC1 : p_rc v = 1%Z.
  Hypothesis Lpix : live A (Z_to_bv 64 pix) = Some 64%Z.
  Hypothesis L0pix : live (c_A0 C) (Z_to_bv 64 pix) = None.
  Hypothesis Halp : (pix mod 16 = 0)%Z.
  Hypothesis Z0A : live A (Z_to_bv 64 0) = None.
  Hypothesis Z0 : live (c_A0 C) (Z_to_bv 64 0) = None.
  Variables (kR bR : Z).
  Hypothesis Hrm : aroom A (m_vmmaps md) kR bR.
  Hypothesis Hrk : (RK_cf <= kR)%Z.
  Hypothesis Hrb : (RB_cf <= bR)%Z.
  Hypothesis HK : forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C (c_A0 C) s m m' ->
    live A' (Z_to_bv 64 0) = None ->
    ( (getr regs' 10 = Z_to_bv 64 0 /\ (forall (q : Z) k, live A (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A A' m m' q))
      \/ (exists o, getr regs' 10 = Z_to_bv 64 (o_cf o) /\ o_pix o = pix /\ o_tw o = p_w v /\ o_th o = p_h v /\ cf_ok C A A' m' (set_rc v 2) o /\
            (forall (q : Z) k, live A (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> q <> pix -> keeps A A' m m' q)) ) ->
    aroom A' vm' (kR - RK_cf) (bR - RB_cf) ->
    realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

  #[local] Notation w := (p_w v) (only parsing).
  #[local] Notation h := (p_h v) (only parsing).

  Definition KEEP (Ak : AS) (mk : word -> option byte) : Prop :=
    forall (q : Z) k, live A (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> q <> pix -> keeps A Ak m mk q.
  Definition BASE (Ak : AS) (mk : word -> option byte) (vmk : VmMaps) (rk : bvmap 5 word) : Prop :=
    W C Ak mk (with_vmmaps vmk md) /\ getr rk 2 = Z_to_bv 64 (s - 112) /\ getr rk 4 = Z_to_bv 64 0x31370 /\
    getr rk 3 = getr regs 3 /\ getr rk 27 = getr regs 27 /\
    cc_cells mk s ret regs /\ live Ak (Z_to_bv 64 pix) = Some 64%Z /\ sub_live A Ak /\ live Ak (Z_to_bv 64 0) = None /\
    KEEP Ak mk /\ POSTM C (c_A0 C) s m mk.

  (* [comment removed for export] *)
  #[local] Ltac rlia := pose proof (alloc_margin_le (1 * 88)); room_consts; lia.
  #[local] Ltac rmono H := (eapply aroom_mono; [exact H | rlia | rlia]).
  #[local] Ltac rvm H := (rewrite with_vmmaps_vmmaps; exact H).
  #[local] Ltac prep :=
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LL8] in *; unfold LSF in *.

  (* [comment removed for export] *)
  Lemma LP : forall Ak mk vmk rk, BASE Ak mk vmk rk -> getr rk 10 = Z_to_bv 64 0 -> keeps A Ak m mk pix ->
    aroom Ak vmk (kR - RK_cf) (bR - RB_cf) ->
    realizes SEGS (mkCfg (mkst rk (0x167a4 : word) mk al_rom) (with_vmmaps vmk md)) S.
  Proof.
    intros Ak mk vmk rk (HWk & R2 & R4 & R3 & R27 & CEk & Lpk & SUBk & Z0k & KP & PMk) R10 Kpix RMk. prep.
    destruct (cc_P al_rom rk mk s ret regs ltac:(lia) ltac:(lia) Hret CEk R2) as (r9 & RUN9 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & AG9).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN9 |].
    apply (HK Ak mk vmk r9 HWk).
    - apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?H2; try reflexivity.
      all: rewrite (AG9 _) by notin_lit; first [exact R3 | exact R27 | rewrite R4, H4; reflexivity].
    - exact PMk.
    - exact Z0k.
    - left. split; [rewrite V10; exact R10|]. intros q k L Hq. destruct (Z.eq_dec q pix) as [->|NE]; [exact Kpix | exact (KP q k L Hq NE)].
    - exact RMk.
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_store : forall Ak mk mdk (c a : word) kc bs (q : Z), W C Ak mk mdk -> W C Ak (wbytes mk a bs) mdk ->
    live Ak c = Some kc -> (u c <= u a)%Z -> (u a + Z.of_nat (length bs) <= u c + kc)%Z ->
    (0 <= q < 2 ^ 64)%Z -> Z_to_bv 64 q <> c -> keeps Ak Ak mk (wbytes mk a bs) q.
  Proof.
    intros Ak mk mdk c a kc bs q HWk HW' Lc Ha1 Ha2 Hq NE. apply (keeps_agree C Ak Ak mk _ mdk q HW' eq_refl Hq).
    intros k x L Hx.
    pose proof (ai_live_disjoint Ak mk (m_vmmaps mdk) _ _ _ _ (w_inv _ _ _ _ HWk) L Lc NE) as D.
    pose proof (ai_live_hull Ak mk (m_vmmaps mdk) _ _ (w_inv _ _ _ _ HWk) L) as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0).
    pose proof (ai_live_hull Ak mk (m_vmmaps mdk) _ _ (w_inv _ _ _ _ HWk) Lc) as (Hc0 & _ & TOPc & _). pose proof (round16_ge kc Hc0).
    pose proof (alloc_top_lt (m_vmmaps mdk)) as T. unfold two_pow_64 in T.
    rewrite u_Z2bv in D, TOPq by lia. apply wbytes_outside; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_frame : forall Ak mk mk' mdk (q : Z), W C Ak mk mdk -> W C Ak mk' mdk ->
    (forall x : word, (u x < s - 112 - 48 - LSF)%Z -> mk' x = mk x) -> (0 <= q < 2 ^ 64)%Z -> keeps Ak Ak mk mk' q.
  Proof.
    intros Ak mk mk' mdk q HWk HW' OUT Hq. prep. apply (keeps_agree C Ak Ak mk mk' mdk q HW' eq_refl Hq).
    intros k x L Hx. apply OUT.
    destruct (blk_range C Ak mk mdk (Z_to_bv 64 q) k CK HWk L ltac:(destruct (Z_lt_le_dec 0 k); [exact l | exfalso; clear -Hx l; lia])) as [_ TOP]. rewrite u_Z2bv in TOP by lia.
    clear -Hx TOP T1 Hlo PIN7. lia.
  Qed.

  (* [comment removed for export] *)
  Definition FBA (A1 : AS) (ba barr : Z) : Prop :=
    ba <> 0%Z -> live A (Z_to_bv 64 ba) = None /\ live A (Z_to_bv 64 barr) = None /\ live A1 (Z_to_bv 64 ba) = Some 24%Z /\ live A1 (Z_to_bv 64 barr) = Some 8%Z /\
                 barr <> 0%Z /\ (0 <= ba < 2 ^ 64)%Z /\ (0 <= barr < 2 ^ 64)%Z.
  Definition FBX (A1 A2 : AS) (bx : Z) : Prop :=
    bx <> 0%Z -> live A1 (Z_to_bv 64 bx) = None /\ live A2 (Z_to_bv 64 bx) = Some 20%Z /\ (0 <= bx < 2 ^ 64)%Z.
  Definition FNA (A3 A4 : AS) (naa narr : Z) : Prop :=
    naa <> 0%Z -> live A3 (Z_to_bv 64 naa) = None /\ live A3 (Z_to_bv 64 narr) = None /\ live A4 (Z_to_bv 64 naa) = Some 16%Z /\ live A4 (Z_to_bv 64 narr) = Some 8%Z /\
                  narr <> 0%Z /\ (0 <= naa < 2 ^ 64)%Z /\ (0 <= narr < 2 ^ 64)%Z.

  (* [comment removed for export] *)
  Definition ST_M (A1 A2 A3 A4 A5 : AS) (cf ba barr bx nb naa narr dnaa darr : Z)
             (A6 : AS) (m6 : word -> option byte) (vm6 : VmMaps) (r6 : bvmap 5 word) (px parr pba pbarr : Z) : Prop :=
    BASE A6 m6 vm6 r6 /\ getr r6 23 = Z_to_bv 64 cf /\ getr r6 10 = Z_to_bv 64 px /\
    sub_live A A1 /\ sub_live A1 A2 /\ sub_live A2 A3 /\ sub_live A3 A4 /\ sub_live A4 A5 /\ sub_live A5 A6 /\
    (10 <= w)%Z /\ (10 <= h)%Z /\
    PIXat m6 pix (set_rc v 2) /\
    RECat m6 cf (cf_flds pix w h ba naa dnaa 0) /\ live A2 (Z_to_bv 64 cf) = None /\ live A3 (Z_to_bv 64 cf) = Some 88%Z /\ live A6 (Z_to_bv 64 cf) = Some 88%Z /\
    live (c_A0 C) (Z_to_bv 64 cf) = None /\ (1 <= cf)%Z /\ (cf + 88 < 2 ^ 64)%Z /\
    FBA A1 ba barr /\ FBX A1 A2 bx /\ (ba <> 0%Z -> boxa_at C A6 m6 ba nb 1 barr bx /\ ((bx = 0%Z /\ nb = 0%Z) \/ (bx <> 0%Z /\ nb = 1%Z))) /\
    FNA A3 A4 naa narr /\ (naa <> 0%Z -> ptra_at C A6 m6 naa 1 narr) /\
    FNA A4 A5 dnaa darr /\ (dnaa <> 0%Z -> ptra_at C A6 m6 dnaa 1 darr) /\
    ((px = 0%Z /\ forall q, live A6 q = live A5 q) \/ pixa_new C A5 A6 m6 px parr pba pbarr) /\
    aroom A6 vm6 (kR - RK_boxa - RK_box - 1 - RK_naa - RK_naa - RK_pixa) (bR - RB_boxa 1 - RB_box - alloc_margin (1 * 88) - RB_naa 1 - RB_naa 1 - RB_pixa 20).

  Lemma LM : forall A1 A2 A3 A4 A5 cf ba barr bx nb naa narr dnaa darr A6 m6 vm6 r6 px parr pba pbarr,
    ST_M A1 A2 A3 A4 A5 cf ba barr bx nb naa narr dnaa darr A6 m6 vm6 r6 px parr pba pbarr ->
    realizes SEGS (mkCfg (mkst r6 (0x16800 : word) m6 al_rom) (with_vmmaps vm6 md)) S.
  Proof.
    intros A1 A2 A3 A4 A5 cf ba barr bx nb naa narr dnaa darr A6 m6 vm6 r6 px parr pba pbarr
      ((HW6 & R2 & R4 & R3 & R27 & CE6 & Lp6 & SUB6 & Z06 & KP & PM6) & R23 & R10 & S01 & S12 & S23 & S34 & S45 & S56 & Hw & Hh & PX6 & RC6 & Lcf2 & Lcf3 & Lcf6 & L0cf & Hcf1 & Hcf88 &
       Fba & Fbx & OBA & Fna & ONA & Fdn & ODN & OPX & RM). prep.
    destruct (blk_range C A6 m6 _ (Z_to_bv 64 cf) 88 CK HW6 Lcf6 ltac:(lia)) as [Gcf TOPcf]. rewrite u_Z2bv in Gcf, TOPcf by lia.
    assert (Hpx : (0 <= px < 2 ^ 64)%Z).
    { destruct OPX as [[-> _] | PN]; [lia|]. pose proof PN as ((RP & _) & _). pose proof (RECat_range m6 _ _ RP) as [X0 X1]. cbn in X1. lia. }
    assert (SOKc : store_ok SEGS m6 (Z_to_bv 64 cf) 88 = true).
    { rewrite <- p8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m6 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m6 cf _ x RC6 ltac:(cbn; clear -Hx; lia) E). }
    destruct (cc_M al_rom r6 m6 s cf px ret regs ltac:(lia) ltac:(lia) Hcf1 ltac:(lia) Hpx Hret SOKc CE6 R2 R10 R23)
      as (r7 & RUN7 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
    set (M7 := wbytes m6 (Z_to_bv 64 (cf + 80)) (word_to_le_bytes 8 (Z_to_bv 64 px))).
    assert (HW7 : W C A6 M7 (with_vmmaps vm6 md)).
    { subst M7. apply (W_store_blk C A6 m6 _ (Z_to_bv 64 cf) _ 88 _ CK HW6 Lcf6 L0cf); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    assert (K7 : forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> cf -> keeps A6 A6 m6 M7 q).
    { intros q Hq NE. subst M7. apply (keeps_store A6 m6 _ (Z_to_bv 64 cf) _ 88 _ q HW6 HW7 Lcf6); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [lia | cbn; lia | exact Hq | exact (zneq_w q cf Hq ltac:(lia) NE)]. }
    apply (HK A6 M7 vm6 r7 HW7).
    - apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?H2; try reflexivity.
      all: rewrite (AG7 _) by notin_lit; first [exact R3 | exact R27 | rewrite R4, H4; reflexivity].
    - eapply POSTM_trans; [exact PM6|]. subst M7.
      apply (POSTM_blk C (c_A0 C) A6 m6 _ (Z_to_bv 64 cf) _ 88 _ s CK HW6 Lcf6 L0cf (w_keep _ _ _ _ HW6)); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia].
    - exact Z06.
    - right.
      exists (CFO cf pix (p_w v) (p_h v) ba nb barr bx naa narr dnaa darr px parr pba pbarr A1 A2 A3 A4 A5).
      split; [exact V10|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      assert (NEcp : cf <> pix).
      { intros ->. pose proof (sub_live_trans _ _ _ S01 S12 _ _ Lpix). congruence. }
      split.
      + (* [comment removed for export] *)
        unfold cf_ok; cbn [o_cf o_pix o_tw o_th o_ba o_nb o_barr o_b0 o_naa o_narr o_dnaa o_darr o_px o_parr o_pba o_pbarr o_B1 o_B2 o_B3 o_B4 o_B5].
        split; [subst M7; eapply (REC_wr' _ _ (cf_flds pix (p_w v) (p_h v) ba naa dnaa 0) _ 13 8); [exact RC6 | clear; cbn; lia | exact Hpx | reflexivity | reflexivity | reflexivity]|].
        split; [exact Lcf6|]. split; [exact L0cf|].
        split; [subst M7; apply PIXat_out; [exact PX6 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn]|].
        { pose proof PX as (Wp0 & _). pose proof (ai_live_disjoint A6 m6 _ _ _ _ _ (w_inv _ _ _ _ HW6) Lcf6 Lp6 (zneq_w cf pix ltac:(lia) ltac:(pose proof PX as (? & ? & _); lia) NEcp)) as D.
          pose proof PX as (_ & Wp64 & _). rewrite !u_Z2bv in D by lia. change (round16 88) with 96%Z in D. change (round16 64) with 64%Z in D. clear -D. lia. }
        split; [destruct v; reflexivity|]. split; [exact Halp|]. split; [exact Lp6|]. split; [exact L0pix|].
        split.
        { destruct (Z.eq_dec ba 0) as [Hb0|Hb0]; [left; exact Hb0 | right]. destruct (OBA Hb0) as [BXA NB]. destruct (Fba Hb0) as (_ & _ & _ & _ & Hbarr & Hba' & Hbarr').
          split; [| split; [exact Hbarr | clear -NB; lia]].
          apply (boxa_at_transport C A6 A6 m6 M7 ba nb 1 barr bx BXA); [apply K7; [exact Hba' |] | apply K7; [exact Hbarr' |] |].
          - intros ->. pose proof BXA as (_ & _ & Lb & _). pose proof (S56 _ _ (S45 _ _ (S34 _ _ (S23 _ _ ltac:(destruct (Fba Hb0) as (_ & _ & X & _); exact (S12 _ _ X)))))). congruence.
          - intros ->. destruct (Fba Hb0) as (_ & _ & _ & X & _). pose proof (S23 _ _ (S12 _ _ X)). congruence.
          - intros Hnb. destruct NB as [[_ Hn0] | [Hbx _]]; [lia|]. destruct (Fbx Hbx) as (_ & Lbx2 & Hbx').
            apply K7; [exact Hbx' |]. intros ->. pose proof (S23 _ _ Lbx2). congruence. }
        split.
        { destruct (Z.eq_dec naa 0) as [Hn0|Hn0]; [left; exact Hn0 | right]. destruct (Fna Hn0) as (Ln3 & Lr3 & Ln4 & Lr4 & Hnarr & Hnaa' & Hnarr').
          split; [| exact Hnarr]. apply (ptra_at_transport C A6 A6 m6 M7 naa 1 narr (ONA Hn0)); apply K7; [exact Hnaa' | intros ->; congruence | exact Hnarr' | intros ->; congruence]. }
        split.
        { destruct (Z.eq_dec dnaa 0) as [Hn0|Hn0]; [left; exact Hn0 | right]. destruct (Fdn Hn0) as (Ln3 & Lr3 & Ln4 & Lr4 & Hnarr & Hnaa' & Hnarr').
          split; [| exact Hnarr]. apply (ptra_at_transport C A6 A6 m6 M7 dnaa 1 darr (ODN Hn0)); apply K7; [exact Hnaa' | intros ->; pose proof (S34 _ _ Lcf3); congruence | exact Hnarr' | intros ->; pose proof (S34 _ _ Lcf3); congruence]. }
        split.
        { destruct OPX as [[Hp0 _] | PN]; [left; exact Hp0 | right]. pose proof PN as (PXA & Hpbarr & F1 & F2 & F3 & F4 & Lr6 & _).
          pose proof PXA as (RP & _ & Lpx6 & _ & Lparr6 & _ & _ & _ & (RB & _ & Lpba6 & _) & _).
          pose proof (PIXA_wf m6 _ 0 20 1 _ _ RP) as (_ & _ & Wparr & Wpba & _). pose proof (BOXA_wf m6 _ 0 20 1 _ RB) as (_ & _ & Wpbarr & Wpba0 & Wpba24).
          pose proof (S34 _ _ Lcf3) as Lcf4. pose proof (S45 _ _ Lcf4) as Lcf5.
          apply (pixa_at_transport C A6 A6 m6 M7 _ 20 _ _ 20 _ PXA); apply K7; try lia; intros ->; congruence. }
        split; [exact S01|]. split; [exact S12|]. split; [exact S23|]. split; [exact S34|]. split; [exact S45|]. split; [exact S56|].
        split; [exact Lpix|].
        split; [intros NZ; destruct (Fba NZ) as (X1 & X2 & X3 & X4 & _); repeat split; assumption|].
        split.
        { intros NZ Hnb. destruct (OBA NZ) as [_ NB]. destruct NB as [[_ Hn0] | [Hbx _]]; [lia|]. destruct (Fbx Hbx) as (X1 & X2 & _). split; assumption. }
        split; [exact Lcf2|]. split; [exact Lcf3|].
        split; [intros NZ; destruct (Fna NZ) as (X1 & X2 & X3 & X4 & _); repeat split; assumption|].
        split; [intros NZ; destruct (Fdn NZ) as (X1 & X2 & X3 & X4 & _); repeat split; assumption|].
        intros NZ. destruct OPX as [[Hp0 _] | PN]; [lia|]. pose proof PN as (_ & _ & F1 & F2 & F3 & F4 & _). repeat split; assumption.
      + intros q k L Hq NEp. apply (keeps_trans A A6 A6 m m6 M7 q (KP q k L Hq NEp)). apply K7; [exact Hq|].
        intros ->. pose proof (S12 _ _ (S01 _ _ L)). congruence.
    - rmono RM.
  Qed.

  (* [comment removed for export] *)
  Definition ST_L (A1 A2 A3 A4 : AS) (cf ba barr bx nb naa narr : Z)
             (A5 : AS) (m5 : word -> option byte) (vm5 : VmMaps) (r5 : bvmap 5 word) (dnaa darr : Z) : Prop :=
    BASE A5 m5 vm5 r5 /\ getr r5 23 = Z_to_bv 64 cf /\ getr r5 10 = Z_to_bv 64 dnaa /\
    sub_live A A1 /\ sub_live A1 A2 /\ sub_live A2 A3 /\ sub_live A3 A4 /\ sub_live A4 A5 /\
    (10 <= w)%Z /\ (10 <= h)%Z /\
    PIXat m5 pix (set_rc v 2) /\
    RECat m5 cf (cf_flds pix w h ba naa 0 0) /\ live A2 (Z_to_bv 64 cf) = None /\ live A3 (Z_to_bv 64 cf) = Some 88%Z /\ live A5 (Z_to_bv 64 cf) = Some 88%Z /\
    live (c_A0 C) (Z_to_bv 64 cf) = None /\ (1 <= cf)%Z /\ (cf + 88 < 2 ^ 64)%Z /\
    FBA A1 ba barr /\ FBX A1 A2 bx /\ (ba <> 0%Z -> boxa_at C A5 m5 ba nb 1 barr bx /\ ((bx = 0%Z /\ nb = 0%Z) \/ (bx <> 0%Z /\ nb = 1%Z))) /\
    FNA A3 A4 naa narr /\ (naa <> 0%Z -> ptra_at C A5 m5 naa 1 narr) /\
    ((dnaa = 0%Z /\ forall q, live A5 q = live A4 q) \/ ptra_new C A4 A5 m5 dnaa 1 darr) /\
    aroom A5 vm5 (kR - RK_boxa - RK_box - 1 - RK_naa - RK_naa) (bR - RB_boxa 1 - RB_box - alloc_margin (1 * 88) - RB_naa 1 - RB_naa 1).

  Lemma LL : forall A1 A2 A3 A4 cf ba barr bx nb naa narr A5 m5 vm5 r5 dnaa darr,
    ST_L A1 A2 A3 A4 cf ba barr bx nb naa narr A5 m5 vm5 r5 dnaa darr ->
    realizes SEGS (mkCfg (mkst r5 (0x167f4 : word) m5 al_rom) (with_vmmaps vm5 md)) S.
  Proof.
    intros A1 A2 A3 A4 cf ba barr bx nb naa narr A5 m5 vm5 r5 dnaa darr
      ((HW5 & R2 & R4 & R3 & R27 & CE5 & Lp5 & SUB5 & Z05 & KP & PM5) & R23 & R10 & S01 & S12 & S23 & S34 & S45 & Hw & Hh & PX5 & RC5 & Lcf2 & Lcf3 & Lcf5 & L0cf & Hcf1 & Hcf88 &
       Fba & Fbx & OBA & Fna & ONA & ODN & RM). prep.
    destruct (blk_range C A5 m5 _ (Z_to_bv 64 cf) 88 CK HW5 Lcf5 ltac:(lia)) as [Gcf TOPcf]. rewrite u_Z2bv in Gcf, TOPcf by lia.
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    assert (Hdn : (0 <= dnaa < 2 ^ 64)%Z).
    { destruct ODN as [[-> _] | PN]; [lia|]. pose proof PN as (RP & _). pose proof (RECat_range m5 _ _ RP) as [X0 X1]. cbn in X1. lia. }
    assert (SOKc : store_ok SEGS m5 (Z_to_bv 64 cf) 88 = true).
    { rewrite <- p8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m5 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m5 cf _ x RC5 ltac:(cbn; clear -Hx; lia) E). }
    destruct (cc_L al_rom r5 m5 cf dnaa Hcf1 Hcf88 Hdn SOKc R10 R23) as (r6 & RUN6 & V2 & V1 & V10 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |].
    set (M := wbytes m5 (Z_to_bv 64 (cf + 72)) (word_to_le_bytes 8 (Z_to_bv 64 dnaa))).
    assert (HWM : W C A5 M (with_vmmaps vm5 md)).
    { subst M. apply (W_store_blk C A5 m5 _ (Z_to_bv 64 cf) _ 88 _ CK HW5 Lcf5 L0cf); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    assert (KM : forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> cf -> keeps A5 A5 m5 M q).
    { intros q Hq NE. subst M. apply (keeps_store A5 m5 _ (Z_to_bv 64 cf) _ 88 _ q HW5 HWM Lcf5); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [lia | cbn; lia | exact Hq | exact (zneq_w q cf Hq ltac:(lia) NE)]. }
    assert (RCM : RECat M cf (cf_flds pix (p_w v) (p_h v) ba naa dnaa 0)).
    { subst M. eapply (REC_wr' _ _ (cf_flds pix (p_w v) (p_h v) ba naa 0 0) _ 12 8); [exact RC5 | clear; cbn; lia | exact Hdn | reflexivity | reflexivity | reflexivity]. }
    assert (CEM : cc_cells M s ret regs).
    { unfold cc_cells. apply (cellsZ_out m5 M cf (cf + 88)); [| clear -HsR TOPcf T1 Hlo PIN7; forall_cells | exact CE5].
      intros x Hx. subst M. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PMM : POSTM C (c_A0 C) s m M).
    { eapply POSTM_trans; [exact PM5|]. subst M.
      apply (POSTM_blk C (c_A0 C) A5 m5 _ (Z_to_bv 64 cf) _ 88 _ s CK HW5 Lcf5 L0cf (w_keep _ _ _ _ HW5)); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    assert (V2' : getr r6 2 = Z_to_bv 64 (s - 112)) by (rewrite V2; exact R2).
    assert (V4 : getr r6 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    apply (pixaCreate_W C A5 M _ r6 (s - 112) (Z_to_bv 64 0x16800) S CK HWM V2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V4 V10 Z05 Z0
             (kR - RK_boxa - RK_box - 1 - RK_naa - RK_naa) (bR - RB_boxa 1 - RB_box - alloc_margin (1 * 88) - RB_naa 1 - RB_naa 1) ltac:(rvm RM) ltac:(rlia) ltac:(rlia)).
    intros A6 m6 vm6 r7 HW6 CS6 PM6 OUT6 RM6. rewrite with_vmmaps_twice in HW6. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x16800) with (0x16800 : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (OUTn : exists px parr pba pbarr : Z, getr r7 10 = Z_to_bv 64 px /\
              (forall q : word, live A5 q <> None -> live A6 q = live A5 q) /\ live A6 (Z_to_bv 64 0) = None /\
              ((px = 0%Z /\ forall q, live A6 q = live A5 q) \/ pixa_new C A5 A6 m6 px parr pba pbarr)).
    { destruct OUT6 as [[A10 LIVEQ] | (px & parr & pba & pbarr & A10 & PN)].
      - exists 0%Z, 0%Z, 0%Z, 0%Z. split; [exact A10|]. split; [intros q _; apply LIVEQ|]. split; [rewrite LIVEQ; exact Z05|]. left. split; [reflexivity | exact LIVEQ].
      - exists px, parr, pba, pbarr. split; [exact A10|].
        pose proof PN as ((RP & _ & Lpx6 & _ & Lparr6 & _ & _ & _ & (RB & _ & Lpba6 & _) & _) & Hpbarr & F1 & F2 & F3 & F4 & Lr6 & _ & LEQ6).
        pose proof (RECat_range m6 _ _ RP) as [X0 X1]. cbn in X1. pose proof (RECat_range m6 _ _ RB) as [Y0 Y1]. cbn in Y1.
        pose proof (PIXA_wf m6 _ 0 20 1 _ _ RP) as (_ & _ & Wparr & _). pose proof (BOXA_wf m6 _ 0 20 1 _ RB) as (_ & _ & Wpbarr & _).
        assert (E : forall q : word, live A5 q <> None -> live A6 q = live A5 q).
        { intros q Hq. apply LEQ6; intros ->; congruence. }
        split; [exact E|]. split; [| right; exact PN].
        destruct (blk_range C A6 m6 _ (Z_to_bv 64 px) 32 CK HW6 Lpx6 ltac:(lia)) as [G1 _]. destruct (blk_range C A6 m6 _ (Z_to_bv 64 parr) 160 CK HW6 Lparr6 ltac:(lia)) as [G2 _].
        destruct (blk_range C A6 m6 _ (Z_to_bv 64 pba) 24 CK HW6 Lpba6 ltac:(lia)) as [G3 _]. destruct (blk_range C A6 m6 _ (Z_to_bv 64 pbarr) 160 CK HW6 Lr6 ltac:(lia)) as [G4 _].
        rewrite !u_Z2bv in G1, G2, G3, G4 by lia.
        rewrite (LEQ6 _ (zneq_w 0 px ltac:(lia) ltac:(lia) ltac:(lia)) (zneq_w 0 parr ltac:(lia) ltac:(lia) ltac:(lia)) (zneq_w 0 pba ltac:(lia) ltac:(lia) ltac:(lia)) (zneq_w 0 pbarr ltac:(lia) ltac:(lia) ltac:(lia))). exact Z05. }
    clear OUT6. destruct OUTn as (px & parr & pba & pbarr & A10 & E56 & Z06 & OPX).
    assert (K56 : forall (q : Z) k, live A5 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A5 A6 M m6 q).
    { intros q k L Hq. assert (E : live A6 (Z_to_bv 64 q) = live A5 (Z_to_bv 64 q)) by (apply E56; congruence).
      exact (keeps_postm C A5 A6 A5 (s - 112) M m6 _ q HW6 PM6 eq_refl E Hq). }
    assert (K5M6 : forall (q : Z) k, live A5 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> q <> cf -> keeps A5 A6 m5 m6 q).
    { intros q k L Hq NE. exact (keeps_trans A5 A5 A6 m5 M m6 q (KM q Hq NE) (K56 q k L Hq)). }
    assert (Lcf6 : live A6 (Z_to_bv 64 cf) = Some 88%Z) by (rewrite (E56 _ ltac:(rewrite Lcf5; discriminate)); exact Lcf5).
    apply (LM A1 A2 A3 A4 A5 cf ba barr bx nb naa narr dnaa darr A6 m6 vm6 r7 px parr pba pbarr).
    split.
    { split; [exact HW6|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [unfold cc_cells; apply (cellsZ_frm C (s - 112) M m6); [exact CK | exact (proj1 PM6) | lia | clear -HsR; forall_cells | exact CEM]|].
      split; [rewrite (E56 _ ltac:(rewrite Lp5; discriminate)); exact Lp5|].
      split; [intros q k L; rewrite (E56 q ltac:(rewrite (SUB5 q k L); discriminate)); exact (SUB5 q k L)|].
      split; [exact Z06|].
      split.
      { intros q k L Hq NEp. apply (keeps_trans A A5 A6 m m5 m6 q (KP q k L Hq NEp)). apply (K5M6 q k (SUB5 _ _ L) Hq).
        intros ->. pose proof (S12 _ _ (S01 _ _ L)). congruence. }
      eapply POSTM_trans; [exact PMM|]. apply (POSTM_sub C (c_A0 C) A5 _ _ _ (W_sub0 _ _ _ _ HW5)). eapply POSTM_mono; [|exact PM6]. lia. }
    split; [csr; reflexivity|]. split; [exact A10|].
    split; [exact S01|]. split; [exact S12|]. split; [exact S23|]. split; [exact S34|]. split; [exact S45|].
    split; [intros q k L; rewrite (E56 q ltac:(rewrite L; discriminate)); exact L|].
    split; [exact Hw|]. split; [exact Hh|].
    split.
    { assert (NEcp : pix <> cf) by (intros E; pose proof (S12 _ _ (S01 _ _ Lpix)) as L'; rewrite E in L'; congruence).
      pose proof PX as (Wp0 & Wp64 & _).
      destruct (K5M6 pix 64%Z Lp5 ltac:(lia) NEcp 64%Z Lp5) as (_ & _ & Mp). exact (PIXat_frame m5 m6 pix _ PX5 Mp). }
    split; [apply (RECat_POSTM C A5 (s - 112) M m6 (Z_to_bv 64 cf) 88 _ _ RCM PM6 Lcf5); rewrite u_Z2bv by lia; [lia | cbn; lia]|].
    split; [exact Lcf2|]. split; [exact Lcf3|]. split; [exact Lcf6|]. split; [exact L0cf|]. split; [exact Hcf1|]. split; [exact Hcf88|].
    split; [exact Fba|]. split; [exact Fbx|].
    split.
    { intros NZ. destruct (OBA NZ) as [BXA NB]. split; [| exact NB]. destruct (Fba NZ) as (_ & _ & Lba1 & Lbarr1 & Hbarr & Hba' & Hbarr').
      pose proof (S45 _ _ (S34 _ _ (S23 _ _ (S12 _ _ Lba1)))) as Lba5. pose proof (S45 _ _ (S34 _ _ (S23 _ _ (S12 _ _ Lbarr1)))) as Lbarr5.
      apply (boxa_at_transport C A5 A6 m5 m6 ba nb 1 barr bx BXA).
      - apply (K5M6 _ _ Lba5 Hba'). intros ->. pose proof (S12 _ _ Lba1). congruence.
      - apply (K5M6 _ _ Lbarr5 Hbarr'). intros ->. pose proof (S12 _ _ Lbarr1). congruence.
      - intros Hnb. destruct NB as [[_ Hn0] | [Hbx _]]; [lia|]. destruct (Fbx Hbx) as (_ & Lbx2 & Hbx').
        apply (K5M6 _ _ (S45 _ _ (S34 _ _ (S23 _ _ Lbx2))) Hbx'). intros ->. congruence. }
    split; [exact Fna|].
    split.
    { intros NZ. destruct (Fna NZ) as (Ln3 & Lr3 & Ln4 & Lr4 & Hnarr & Hnaa' & Hnarr').
      apply (ptra_at_transport C A5 A6 m5 m6 naa 1 narr (ONA NZ)).
      - apply (K5M6 _ _ (S45 _ _ Ln4) Hnaa'). intros ->. congruence.
      - apply (K5M6 _ _ (S45 _ _ Lr4) Hnarr'). intros ->. congruence. }
    split.
    { unfold FNA. intros NZ. destruct ODN as [[Hd0 _] | PN]; [lia|].
      pose proof PN as (RP & Harr1 & NEra & Ld4 & Lr4 & _ & _ & Ld5 & Lr5 & _).
      pose proof (RECat_range m5 _ _ RP) as [X0 X1]. cbn in X1. pose proof (PTRA_wf m5 _ 1 0 _ RP) as (_ & _ & Wdarr & _).
      repeat split; try assumption; lia. }
    split.
    { intros NZ. destruct ODN as [[Hd0 _] | PN]; [lia|].
      pose proof PN as (RP & Harr1 & NEra & Ld4 & Lr4 & _ & _ & Ld5 & Lr5 & _).
      pose proof (RECat_range m5 _ _ RP) as [X0 X1]. cbn in X1. pose proof (PTRA_wf m5 _ 1 0 _ RP) as (_ & _ & Wdarr & _).
      pose proof (S34 _ _ Lcf3) as Lcf4.
      apply (ptra_at_transport C A5 A6 m5 m6 dnaa 1 darr (ptra_new_at C A4 A5 m5 dnaa 1 darr ltac:(lia) PN)).
      - apply (K5M6 _ _ Ld5 ltac:(lia)). intros ->. congruence.
      - apply (K5M6 _ _ Lr5 ltac:(lia)). intros ->. congruence. }
    split; [exact OPX | exact RM6].
  Qed.

  (* [comment removed for export] *)
  Definition ST_K (A1 A2 A3 : AS) (cf ba barr bx nb : Z)
             (A4 : AS) (m4 : word -> option byte) (vm4 : VmMaps) (r4 : bvmap 5 word) (naa narr : Z) : Prop :=
    BASE A4 m4 vm4 r4 /\ getr r4 23 = Z_to_bv 64 cf /\ getr r4 10 = Z_to_bv 64 naa /\ getr r4 20 = Z_to_bv 64 1 /\
    sub_live A A1 /\ sub_live A1 A2 /\ sub_live A2 A3 /\ sub_live A3 A4 /\
    (10 <= w)%Z /\ (10 <= h)%Z /\
    PIXat m4 pix (set_rc v 2) /\
    RECat m4 cf (cf_flds pix w h ba 0 0 0) /\ live A2 (Z_to_bv 64 cf) = None /\ live A3 (Z_to_bv 64 cf) = Some 88%Z /\ live A4 (Z_to_bv 64 cf) = Some 88%Z /\
    live (c_A0 C) (Z_to_bv 64 cf) = None /\ (1 <= cf)%Z /\ (cf + 88 < 2 ^ 64)%Z /\
    FBA A1 ba barr /\ FBX A1 A2 bx /\ (ba <> 0%Z -> boxa_at C A4 m4 ba nb 1 barr bx /\ ((bx = 0%Z /\ nb = 0%Z) \/ (bx <> 0%Z /\ nb = 1%Z))) /\
    ((naa = 0%Z /\ forall q, live A4 q = live A3 q) \/ ptra_new C A3 A4 m4 naa 1 narr) /\
    aroom A4 vm4 (kR - RK_boxa - RK_box - 1 - RK_naa) (bR - RB_boxa 1 - RB_box - alloc_margin (1 * 88) - RB_naa 1).

  Lemma LK : forall A1 A2 A3 cf ba barr bx nb A4 m4 vm4 r4 naa narr,
    ST_K A1 A2 A3 cf ba barr bx nb A4 m4 vm4 r4 naa narr ->
    realizes SEGS (mkCfg (mkst r4 (0x167e8 : word) m4 al_rom) (with_vmmaps vm4 md)) S.
  Proof.
    intros A1 A2 A3 cf ba barr bx nb A4 m4 vm4 r4 naa narr
      ((HW4 & R2 & R4 & R3 & R27 & CE4 & Lp4 & SUB4 & Z04 & KP & PM4) & R23 & R10 & R20 & S01 & S12 & S23 & S34 & Hw & Hh & PX4 & RC4 & Lcf2 & Lcf3 & Lcf4 & L0cf & Hcf1 & Hcf88 &
       Fba & Fbx & OBA & ONA & RM). prep.
    destruct (blk_range C A4 m4 _ (Z_to_bv 64 cf) 88 CK HW4 Lcf4 ltac:(lia)) as [Gcf TOPcf]. rewrite u_Z2bv in Gcf, TOPcf by lia.
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    assert (Hna : (0 <= naa < 2 ^ 64)%Z).
    { destruct ONA as [[-> _] | PN]; [lia|]. pose proof PN as (RP & _). pose proof (RECat_range m4 _ _ RP) as [X0 X1]. cbn in X1. lia. }
    assert (SOKc : store_ok SEGS m4 (Z_to_bv 64 cf) 88 = true).
    { rewrite <- p8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m4 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m4 cf _ x RC4 ltac:(cbn; clear -Hx; lia) E). }
    destruct (cc_K al_rom r4 m4 cf naa Hcf1 Hcf88 Hna SOKc R10 R23 R20) as (r6 & RUN6 & V2 & V1 & V10 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
    set (M := wbytes m4 (Z_to_bv 64 (cf + 64)) (word_to_le_bytes 8 (Z_to_bv 64 naa))).
    assert (HWM : W C A4 M (with_vmmaps vm4 md)).
    { subst M. apply (W_store_blk C A4 m4 _ (Z_to_bv 64 cf) _ 88 _ CK HW4 Lcf4 L0cf); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    assert (KM : forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> cf -> keeps A4 A4 m4 M q).
    { intros q Hq NE. subst M. apply (keeps_store A4 m4 _ (Z_to_bv 64 cf) _ 88 _ q HW4 HWM Lcf4); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [lia | cbn; lia | exact Hq | exact (zneq_w q cf Hq ltac:(lia) NE)]. }
    assert (RCM : RECat M cf (cf_flds pix (p_w v) (p_h v) ba naa 0 0)).
    { subst M. eapply (REC_wr' _ _ (cf_flds pix (p_w v) (p_h v) ba 0 0 0) _ 11 8); [exact RC4 | clear; cbn; lia | exact Hna | reflexivity | reflexivity | reflexivity]. }
    assert (CEM : cc_cells M s ret regs).
    { unfold cc_cells. apply (cellsZ_out m4 M cf (cf + 88)); [| clear -HsR TOPcf T1 Hlo PIN7; forall_cells | exact CE4].
      intros x Hx. subst M. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PMM : POSTM C (c_A0 C) s m M).
    { eapply POSTM_trans; [exact PM4|]. subst M.
      apply (POSTM_blk C (c_A0 C) A4 m4 _ (Z_to_bv 64 cf) _ 88 _ s CK HW4 Lcf4 L0cf (w_keep _ _ _ _ HW4)); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    assert (V2' : getr r6 2 = Z_to_bv 64 (s - 112)) by (rewrite V2; exact R2).
    assert (V4 : getr r6 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    apply (l_dnaaCreate_W C A4 M _ r6 (s - 112) 1 (Z_to_bv 64 0x167f4) S CK HWM V2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V4 V10 ltac:(lia) Z04 Z0
             (kR - RK_boxa - RK_box - 1 - RK_naa) (bR - RB_boxa 1 - RB_box - alloc_margin (1 * 88) - RB_naa 1) ltac:(rvm RM) ltac:(rlia) ltac:(rlia)).
    intros A5 m5 vm5 r7 HW5 CS5 PM5 OUT5 RM5. rewrite with_vmmaps_twice in HW5. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x167f4) with (0x167f4 : word) by (apply bv_eq; reflexivity).
    assert (OUTn : exists dnaa darr : Z, getr r7 10 = Z_to_bv 64 dnaa /\
              (forall q : word, live A4 q <> None -> live A5 q = live A4 q) /\ live A5 (Z_to_bv 64 0) = None /\
              ((dnaa = 0%Z /\ forall q, live A5 q = live A4 q) \/ ptra_new C A4 A5 m5 dnaa 1 darr)).
    { destruct OUT5 as [[A10 LIVEQ] | (dnaa & darr & A10 & PN)].
      - exists 0%Z, 0%Z. split; [exact A10|]. split; [intros q _; apply LIVEQ|]. split; [rewrite LIVEQ; exact Z04|]. left. split; [reflexivity | exact LIVEQ].
      - exists dnaa, darr. split; [exact A10|].
        pose proof PN as (RP & Harr1 & NEra & Ld4 & Lr4 & _ & _ & Ld5 & Lr5 & LEQ5).
        pose proof (RECat_range m5 _ _ RP) as [X0 X1]. cbn in X1. pose proof (PTRA_wf m5 _ 1 0 _ RP) as (_ & _ & Wdarr & _).
        assert (E : forall q : word, live A4 q <> None -> live A5 q = live A4 q) by (intros q Hq; apply LEQ5; intros ->; congruence).
        split; [exact E|]. split; [| right; exact PN].
        destruct (blk_range C A5 m5 _ (Z_to_bv 64 dnaa) 16 CK HW5 Ld5 ltac:(lia)) as [G1 _]. destruct (blk_range C A5 m5 _ (Z_to_bv 64 darr) 8 CK HW5 Lr5 ltac:(lia)) as [G2 _].
        rewrite !u_Z2bv in G1, G2 by lia.
        rewrite (LEQ5 _ (zneq_w 0 dnaa ltac:(lia) ltac:(lia) ltac:(lia)) (zneq_w 0 darr ltac:(lia) ltac:(lia) ltac:(lia))). exact Z04. }
    clear OUT5. destruct OUTn as (dnaa & darr & A10 & E45 & Z05 & ODN).
    assert (K45 : forall (q : Z) k, live A4 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A4 A5 M m5 q).
    { intros q k L Hq. assert (E : live A5 (Z_to_bv 64 q) = live A4 (Z_to_bv 64 q)) by (apply E45; congruence).
      exact (keeps_postm C A4 A5 A4 (s - 112) M m5 _ q HW5 PM5 eq_refl E Hq). }
    assert (K4M5 : forall (q : Z) k, live A4 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> q <> cf -> keeps A4 A5 m4 m5 q).
    { intros q k L Hq NE. exact (keeps_trans A4 A4 A5 m4 M m5 q (KM q Hq NE) (K45 q k L Hq)). }
    assert (Lcf5 : live A5 (Z_to_bv 64 cf) = Some 88%Z) by (rewrite (E45 _ ltac:(rewrite Lcf4; discriminate)); exact Lcf4).
    apply (LL A1 A2 A3 A4 cf ba barr bx nb naa narr A5 m5 vm5 r7 dnaa darr).
    split.
    { split; [exact HW5|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [unfold cc_cells; apply (cellsZ_frm C (s - 112) M m5); [exact CK | exact (proj1 PM5) | lia | clear -HsR; forall_cells | exact CEM]|].
      split; [rewrite (E45 _ ltac:(rewrite Lp4; discriminate)); exact Lp4|].
      split; [intros q k L; rewrite (E45 q ltac:(rewrite (SUB4 q k L); discriminate)); exact (SUB4 q k L)|].
      split; [exact Z05|].
      split.
      { intros q k L Hq NEp. apply (keeps_trans A A4 A5 m m4 m5 q (KP q k L Hq NEp)). apply (K4M5 q k (SUB4 _ _ L) Hq).
        intros ->. pose proof (S12 _ _ (S01 _ _ L)). congruence. }
      eapply POSTM_trans; [exact PMM|]. apply (POSTM_sub C (c_A0 C) A4 _ _ _ (W_sub0 _ _ _ _ HW4)). eapply POSTM_mono; [|exact PM5]. lia. }
    split; [csr; reflexivity|]. split; [exact A10|].
    split; [exact S01|]. split; [exact S12|]. split; [exact S23|]. split; [exact S34|].
    split; [intros q k L; rewrite (E45 q ltac:(rewrite L; discriminate)); exact L|].
    split; [exact Hw|]. split; [exact Hh|].
    split.
    { assert (NEcp : pix <> cf) by (intros E; pose proof (S12 _ _ (S01 _ _ Lpix)) as L'; rewrite E in L'; congruence).
      pose proof PX as (Wp0 & Wp64 & _).
      destruct (K4M5 pix 64%Z Lp4 ltac:(lia) NEcp 64%Z Lp4) as (_ & _ & Mp). exact (PIXat_frame m4 m5 pix _ PX4 Mp). }
    split; [apply (RECat_POSTM C A4 (s - 112) M m5 (Z_to_bv 64 cf) 88 _ _ RCM PM5 Lcf4); rewrite u_Z2bv by lia; [lia | cbn; lia]|].
    split; [exact Lcf2|]. split; [exact Lcf3|]. split; [exact Lcf5|]. split; [exact L0cf|]. split; [exact Hcf1|]. split; [exact Hcf88|].
    split; [exact Fba|]. split; [exact Fbx|].
    split.
    { intros NZ. destruct (OBA NZ) as [BXA NB]. split; [| exact NB]. destruct (Fba NZ) as (_ & _ & Lba1 & Lbarr1 & Hbarr & Hba' & Hbarr').
      pose proof (S34 _ _ (S23 _ _ (S12 _ _ Lba1))) as Lba4. pose proof (S34 _ _ (S23 _ _ (S12 _ _ Lbarr1))) as Lbarr4.
      apply (boxa_at_transport C A4 A5 m4 m5 ba nb 1 barr bx BXA).
      - apply (K4M5 _ _ Lba4 Hba'). intros ->. pose proof (S12 _ _ Lba1). congruence.
      - apply (K4M5 _ _ Lbarr4 Hbarr'). intros ->. pose proof (S12 _ _ Lbarr1). congruence.
      - intros Hnb. destruct NB as [[_ Hn0] | [Hbx _]]; [lia|]. destruct (Fbx Hbx) as (_ & Lbx2 & Hbx').
        apply (K4M5 _ _ (S34 _ _ (S23 _ _ Lbx2)) Hbx'). intros ->. congruence. }
    split.
    { unfold FNA. intros NZ. destruct ONA as [[Hd0 _] | PN]; [lia|].
      pose proof PN as (RP & Harr1 & NEra & Ld4 & Lr4 & _ & _ & Ld5 & Lr5 & _).
      pose proof (RECat_range m4 _ _ RP) as [X0 X1]. cbn in X1. pose proof (PTRA_wf m4 _ 1 0 _ RP) as (_ & _ & Wdarr & _).
      repeat split; try assumption; lia. }
    split.
    { intros NZ. destruct ONA as [[Hd0 _] | PN]; [lia|].
      pose proof PN as (RP & Harr1 & NEra & Ld4 & Lr4 & _ & _ & Ld5 & Lr5 & _).
      pose proof (RECat_range m4 _ _ RP) as [X0 X1]. cbn in X1. pose proof (PTRA_wf m4 _ 1 0 _ RP) as (_ & _ & Wdarr & _).
      apply (ptra_at_transport C A4 A5 m4 m5 naa 1 narr (ptra_new_at C A3 A4 m4 naa 1 narr ltac:(lia) PN)).
      - apply (K4M5 _ _ Ld5 ltac:(lia)). intros ->. congruence.
      - apply (K4M5 _ _ Lr5 ltac:(lia)). intros ->. congruence. }
    split; [exact ODN | exact RM5].
  Qed.

  (* [comment removed for export] *)
  Definition ST_I (A1 : AS) (ba barr bx nb : Z) (A2 : AS) (mI : word -> option byte) (vmI : VmMaps) (rI : bvmap 5 word) : Prop :=
    BASE A2 mI vmI rI /\
    getr rI 8 = Z_to_bv 64 1 /\ getr rI 9 = Z_to_bv 64 1 /\ getr rI 18 = Z_to_bv 64 pix /\ getr rI 19 = Z_to_bv 64 w /\ getr rI 21 = Z_to_bv 64 h /\
    getr rI 20 = Z_to_bv 64 1 /\ getr rI 22 = Z_to_bv 64 ba /\ getr rI 23 = Z_to_bv 64 0 /\ getr rI 25 = Z_to_bv 64 0 /\ getr rI 26 = Z_to_bv 64 1 /\
    sub_live A A1 /\ sub_live A1 A2 /\ (10 <= w)%Z /\ (10 <= h)%Z /\
    PIXat mI pix v /\ keeps A A2 m mI pix /\ (0 <= ba < 2 ^ 64)%Z /\
    FBA A1 ba barr /\ FBX A1 A2 bx /\ (ba <> 0%Z -> boxa_at C A2 mI ba nb 1 barr bx /\ ((bx = 0%Z /\ nb = 0%Z) \/ (bx <> 0%Z /\ nb = 1%Z))) /\
    aroom A2 vmI (kR - RK_boxa - RK_box) (bR - RB_boxa 1 - RB_box).

  (* [comment removed for export] *)
  Lemma LJ : forall A1 ba barr bx nb A2 mI vmI rI A3 m3 vm3 r3 (cf : Z),
    ST_I A1 ba barr bx nb A2 mI vmI rI ->
    W C A3 m3 (with_vmmaps vm3 md) -> getr r3 10 = Z_to_bv 64 cf ->
    getr r3 2 = Z_to_bv 64 (s - 112) /\ getr r3 4 = Z_to_bv 64 0x31370 /\ getr r3 3 = getr regs 3 /\ getr r3 27 = getr regs 27 /\
    getr r3 8 = Z_to_bv 64 1 /\ getr r3 9 = Z_to_bv 64 1 /\ getr r3 18 = Z_to_bv 64 pix /\ getr r3 19 = Z_to_bv 64 w /\ getr r3 21 = Z_to_bv 64 h /\
    getr r3 20 = Z_to_bv 64 1 /\ getr r3 22 = Z_to_bv 64 ba ->
    (1 <= cf)%Z -> live A2 (Z_to_bv 64 cf) = None -> live A3 (Z_to_bv 64 cf) = Some 88%Z -> live (c_A0 C) (Z_to_bv 64 cf) = None ->
    (forall q, q <> Z_to_bv 64 cf -> live A3 q = live A2 q) ->
    (forall i, (0 <= i < 88)%Z -> m3 (at_ (Z_to_bv 64 cf) i) = Some (Z_to_bv 8 0)) -> (cf mod 16 = 0)%Z -> (cf + 96 <= alloc_top (c_vm C))%Z ->
    POSTM C A2 (s - 112) mI m3 ->
    aroom A3 vm3 (kR - RK_boxa - RK_box - 1) (bR - RB_boxa 1 - RB_box - alloc_margin (1 * 88)) ->
    realizes SEGS (mkCfg (mkst r3 (0x167bc : word) m3 al_rom) (with_vmmaps vm3 md)) S.
  Proof.
    intros A1 ba barr bx nb A2 mI vmI rI A3 m3 vm3 r3 cf
      ((HWI & R2 & R4 & R3 & R27 & CEI & LpI & SUBI & Z0I & KP & PMI) & R8 & R9 & R18 & R19 & R21 & R20 & R22 & R23z & R25 & R26 & S01 & S12 & Hw & Hh & PXI & KpixI & Hba & Fba & Fbx & OBA & RM)
      HW3 Q10 (Q2 & Q4 & Q3 & Q27 & Q8 & Q9 & Q18 & Q19 & Q21 & Q20 & Q22) Hcf1 Lcf2 Lcf3 L0cf LEQ3 ZERO Halc TOPc PM3 RM3. prep.
    pose proof PX as (Wp0 & Wp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia.
    assert (E23 : forall q : word, live A2 q <> None -> live A3 q = live A2 q) by (intros q Hq; apply LEQ3; intros ->; congruence).
    assert (S23 : sub_live A2 A3) by (intros q k L; rewrite (E23 q ltac:(rewrite L; discriminate)); exact L).
    assert (Lp3 : live A3 (Z_to_bv 64 pix) = Some 64%Z) by (exact (S23 _ _ LpI)).
    assert (NEcp : cf <> pix) by (intros ->; congruence).
    destruct (blk_range C A3 m3 _ (Z_to_bv 64 pix) 64 CK HW3 Lp3 ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
    pose proof (ai_live_disjoint A3 m3 _ _ _ _ _ (w_inv _ _ _ _ HW3) Lcf3 Lp3 (zneq_w cf pix Hcf ltac:(lia) NEcp)) as Dcp.
    rewrite !u_Z2bv in Dcp by lia. change (round16 88) with 96%Z in Dcp. change (round16 64) with 64%Z in Dcp.
    (* [comment removed for export] *)
    assert (K23 : forall (q : Z) k, live A2 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A2 A3 mI m3 q).
    { intros q k L Hq. exact (keeps_postm C A2 A3 A2 (s - 112) mI m3 _ q HW3 PM3 eq_refl (E23 _ ltac:(rewrite L; discriminate)) Hq). }
    destruct (K23 pix 64%Z LpI ltac:(lia) 64%Z LpI) as (_ & _ & Mp23).
    pose proof (PIXat_frame mI m3 pix v PXI Mp23) as PX3.
    assert (REC0 : RECat m3 cf (zflds [8; 8; 4; 4; 4; 4; 4; 4; 8; 8; 8; 8; 8; 8]%nat)).
    { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
      unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. clear -Hi. lia. }
    assert (SOKx : store_ok SEGS m3 (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m3 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m3 pix v x PX3 ltac:(clear -Hx; lia) E). }
    assert (SOKc : store_ok SEGS m3 (Z_to_bv 64 cf) 88 = true).
    { rewrite <- p8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m3 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m3 cf _ x REC0 ltac:(cbn; clear -Hx; lia) E). }
    destruct (cc_J al_rom r3 m3 s cf pix (p_w v) (p_h v) ba v Hcf1 ltac:(lia) ltac:(lia) Halp ltac:(lia) ltac:(lia) Hba PX3 RC1 SOKx SOKc ltac:(clear -Dcp; lia)
                Q10 Q18 Q8 Q9 Q19 Q21 Q22 Q20) as (r4 & RUN4 & V2 & V1 & V10 & V23 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
    set (M1 := wbytes m3 (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 2))).
    set (M := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M1 _ _) _ _) _ _) _ _) _ _) _ _).
    assert (HWM1 : W C A3 M1 (with_vmmaps vm3 md)).
    { subst M1. apply (W_store_blk C A3 m3 _ (Z_to_bv 64 pix) _ 64 _ CK HW3 Lp3 L0pix); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    assert (HWM : W C A3 M (with_vmmaps vm3 md)).
    { subst M. do 6 (apply (W_store_blk C A3 _ _ (Z_to_bv 64 cf) _ 88 _ CK); [| exact Lcf3 | exact L0cf | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]). exact HWM1. }
    assert (K3M : forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> pix -> q <> cf -> keeps A3 A3 m3 M q).
    { intros q Hq N1 N2. apply (keeps_agree C A3 A3 m3 M _ q HWM eq_refl Hq). intros k x L Hx.
      pose proof (ai_live_disjoint A3 m3 _ _ _ _ _ (w_inv _ _ _ _ HW3) L Lp3 (zneq_w q pix Hq ltac:(clear -Wp0 Wp64; lia) N1)) as D1.
      pose proof (ai_live_disjoint A3 m3 _ _ _ _ _ (w_inv _ _ _ _ HW3) L Lcf3 (zneq_w q cf Hq Hcf N2)) as D2.
      pose proof (ai_live_hull A3 m3 _ _ _ (w_inv _ _ _ _ HW3) L) as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0) as RG.
      rewrite (u_Z2bv q) in D1, D2, TOPq by (clear -Hq; lia). rewrite (u_Z2bv pix) in D1 by (clear -Wp0 Wp64; lia). rewrite (u_Z2bv cf) in D2 by (clear -Hcf; lia).
      change (round16 88) with 96%Z in D2. change (round16 64) with 64%Z in D1.
      pose proof (alloc_top_lt (m_vmmaps (with_vmmaps vm3 md))) as AT3. unfold two_pow_64 in AT3.
      subst M M1. clear -Hx D1 D2 RG Hcf Gp AT3 ATL TOPc TOPp TOPq Hq Wp0 Wp64.
      rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXM : PIXat M pix (set_rc v 2)).
    { subst M. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; clear -Dcp; lia]).
      subst M1. apply PIX_wr_rc; [exact PX3 | lia]. }
    assert (RCM : RECat M cf (cf_flds pix (p_w v) (p_h v) ba 0 0 0)).
    { subst M. unfold cf_flds.
      Local Ltac cfwr FS i k := eapply (REC_wr' _ _ FS _ i k);
        [ | clear; cbn; lia | | reflexivity | cbn [fld_off Z.of_nat Pos.of_succ_nat Pos.succ Nat.add]; first [reflexivity | f_equal; clear; lia] | reflexivity ].
      cfwr [(8%nat, pix); (8%nat, 0%Z); (4%nat, 1%Z); (4%nat, 1%Z); (4%nat, p_w v); (4%nat, p_h v); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] 8%nat 8%nat; [| exact Hba].
      cfwr [(8%nat, pix); (8%nat, 0%Z); (4%nat, 1%Z); (4%nat, 1%Z); (4%nat, p_w v); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] 5%nat 4%nat; [| cbn; lia].
      cfwr [(8%nat, pix); (8%nat, 0%Z); (4%nat, 1%Z); (4%nat, 1%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] 4%nat 4%nat; [| cbn; lia].
      cfwr [(8%nat, pix); (8%nat, 0%Z); (4%nat, 1%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] 3%nat 4%nat; [| cbn; lia].
      cfwr [(8%nat, pix); (8%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] 2%nat 4%nat; [| cbn; lia].
      cfwr [(8%nat, 0%Z); (8%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] 0%nat 8%nat; [| cbn; lia].
      subst M1. apply RECat_out; [exact REC0 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; clear -Dcp; lia]. }
    assert (CEM : cc_cells M s ret regs).
    { unfold cc_cells. apply (cellsZ_keep m3 M).
      - subst M M1. clear -HsR TOPc TOPp T1 Hlo PIN7 Hcf Gp.
        repeat (apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [lia|]; intros x Hx;
          rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia; reflexivity |]). apply Forall_nil.
      - apply (cellsZ_frm C (s - 112) mI m3); [exact CK | exact (proj1 PM3) | lia | clear -HsR; forall_cells | exact CEI]. }
    assert (PMM : POSTM C (c_A0 C) s m M).
    { eapply POSTM_trans; [exact PMI|]. apply (POSTM_trans C (c_A0 C) s mI m3 M).
      - apply (POSTM_sub C (c_A0 C) A2 _ _ _ (W_sub0 _ _ _ _ HWI)). eapply POSTM_mono; [|exact PM3]. lia.
      - apply (POSTM_local C (c_A0 C) A3 m3 _ M s CK HW3 (W_sub0 _ _ _ _ HW3)). intros a Ha. right.
        destruct (Sumbool.sumbool_and _ _ _ _ (Z_le_dec cf (u a)) (Z_lt_dec (u a) (cf + 88))) as [[C1 C2] | Cn].
        + exists (Z_to_bv 64 cf), 88%Z. split; [exact Lcf3|]. split; [exact L0cf|]. rewrite u_Z2bv by lia. lia.
        + exists (Z_to_bv 64 pix), 64%Z. split; [exact Lp3|]. split; [exact L0pix|]. rewrite u_Z2bv by lia.
          destruct (Sumbool.sumbool_and _ _ _ _ (Z_le_dec (pix + 20) (u a)) (Z_lt_dec (u a) (pix + 24))) as [[P1 P2] | Pn]; [lia|].
          exfalso. apply Ha. subst M M1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (V2' : getr r4 2 = Z_to_bv 64 (s - 112)) by (rewrite V2; exact Q2).
    assert (V4 : getr r4 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    assert (Z03 : live A3 (Z_to_bv 64 0) = None) by (rewrite (LEQ3 _ (zneq_w 0 cf ltac:(lia) Hcf ltac:(lia))); exact Z0I).
    apply (numaaCreate_W C A3 M _ r4 (s - 112) 1 (Z_to_bv 64 0x167e8) S CK HWM V2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V4 V10 ltac:(lia) Z03 Z0
             (kR - RK_boxa - RK_box - 1) (bR - RB_boxa 1 - RB_box - alloc_margin (1 * 88)) ltac:(rvm RM3) ltac:(rlia) ltac:(rlia)).
    intros A4 m4 vm4 r5 HW4 CS4 PM4 OUT4 RM4. rewrite with_vmmaps_twice in HW4. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x167e8) with (0x167e8 : word) by (apply bv_eq; reflexivity).
    assert (OUTn : exists naa narr : Z, getr r5 10 = Z_to_bv 64 naa /\
              (forall q : word, live A3 q <> None -> live A4 q = live A3 q) /\ live A4 (Z_to_bv 64 0) = None /\
              ((naa = 0%Z /\ forall q, live A4 q = live A3 q) \/ ptra_new C A3 A4 m4 naa 1 narr)).
    { destruct OUT4 as [[A10 LIVEQ] | (naa & narr & A10 & PN)].
      - exists 0%Z, 0%Z. split; [exact A10|]. split; [intros q _; apply LIVEQ|]. split; [rewrite LIVEQ; exact Z03|]. left. split; [reflexivity | exact LIVEQ].
      - exists naa, narr. split; [exact A10|].
        pose proof PN as (RP & Harr1 & NEra & Ld4 & Lr4 & _ & _ & Ld5 & Lr5 & LEQ5).
        pose proof (RECat_range m4 _ _ RP) as [X0 X1]. cbn in X1. pose proof (PTRA_wf m4 _ 1 0 _ RP) as (_ & _ & Wdarr & _).
        assert (E : forall q : word, live A3 q <> None -> live A4 q = live A3 q) by (intros q Hq; apply LEQ5; intros ->; congruence).
        split; [exact E|]. split; [| right; exact PN].
        destruct (blk_range C A4 m4 _ (Z_to_bv 64 naa) 16 CK HW4 Ld5 ltac:(lia)) as [G1 _]. destruct (blk_range C A4 m4 _ (Z_to_bv 64 narr) 8 CK HW4 Lr5 ltac:(lia)) as [G2 _].
        rewrite !u_Z2bv in G1, G2 by lia.
        rewrite (LEQ5 _ (zneq_w 0 naa ltac:(lia) ltac:(lia) ltac:(lia)) (zneq_w 0 narr ltac:(lia) ltac:(lia) ltac:(lia))). exact Z03. }
    clear OUT4. destruct OUTn as (naa & narr & A10 & E34 & Z04 & ONA).
    assert (K34 : forall (q : Z) k, live A3 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A3 A4 M m4 q).
    { intros q k L Hq. assert (E : live A4 (Z_to_bv 64 q) = live A3 (Z_to_bv 64 q)) by (apply E34; congruence).
      exact (keeps_postm C A3 A4 A3 (s - 112) M m4 _ q HW4 PM4 eq_refl E Hq). }
    assert (K24 : forall (q : Z) k, live A2 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> q <> pix -> keeps A2 A4 mI m4 q).
    { intros q k L Hq NEp. assert (NEc : q <> cf) by (intros ->; congruence).
      apply (keeps_trans A2 A3 A4 mI m3 m4 q (K23 q k L Hq)). apply (keeps_trans A3 A3 A4 m3 M m4 q (K3M q Hq NEp NEc)). exact (K34 q k (S23 _ _ L) Hq). }
    assert (Lcf4 : live A4 (Z_to_bv 64 cf) = Some 88%Z) by (rewrite (E34 _ ltac:(rewrite Lcf3; discriminate)); exact Lcf3).
    apply (LK A1 A2 A3 cf ba barr bx nb A4 m4 vm4 r5 naa narr).
    split.
    { split; [exact HW4|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [unfold cc_cells; apply (cellsZ_frm C (s - 112) M m4); [exact CK | exact (proj1 PM4) | lia | clear -HsR; forall_cells | exact CEM]|].
      split; [rewrite (E34 _ ltac:(rewrite Lp3; discriminate)); exact Lp3|].
      split; [intros q k L; pose proof (S23 _ _ (SUBI _ _ L)) as L3; rewrite (E34 q ltac:(rewrite L3; discriminate)); exact L3|].
      split; [exact Z04|].
      split.
      { intros q k L Hq NEp. apply (keeps_trans A A2 A4 m mI m4 q (KP q k L Hq NEp)). exact (K24 q k (SUBI _ _ L) Hq NEp). }
      eapply POSTM_trans; [exact PMM|]. apply (POSTM_sub C (c_A0 C) A3 _ _ _ (W_sub0 _ _ _ _ HW3)). eapply POSTM_mono; [|exact PM4]. lia. }
    split; [csr; reflexivity|]. split; [exact A10|]. split; [csr; reflexivity|].
    split; [exact S01|]. split; [exact S12|]. split; [exact S23|].
    split; [intros q k L; rewrite (E34 q ltac:(rewrite L; discriminate)); exact L|].
    split; [exact Hw|]. split; [exact Hh|].
    split.
    { destruct (K34 pix 64%Z Lp3 ltac:(lia) 64%Z Lp3) as (_ & _ & Mp). exact (PIXat_frame M m4 pix _ PXM Mp). }
    split; [apply (RECat_POSTM C A3 (s - 112) M m4 (Z_to_bv 64 cf) 88 _ _ RCM PM4 Lcf3); rewrite u_Z2bv by lia; [lia | cbn; lia]|].
    split; [exact Lcf2|]. split; [exact Lcf3|]. split; [exact Lcf4|]. split; [exact L0cf|]. split; [exact Hcf1|]. split; [lia|].
    split; [exact Fba|]. split; [exact Fbx|].
    split.
    { intros NZ. destruct (OBA NZ) as [BXA NB]. split; [| exact NB]. destruct (Fba NZ) as (_ & _ & Lba1 & Lbarr1 & Hbarr & Hba' & Hbarr').
      pose proof (S12 _ _ Lba1) as Lba2. pose proof (S12 _ _ Lbarr1) as Lbarr2.
      assert (NPa : ba <> pix) by (intros ->; destruct (Fba NZ) as (X & _); congruence).
      assert (NPr : barr <> pix) by (intros ->; destruct (Fba NZ) as (_ & X & _); congruence).
      apply (boxa_at_transport C A2 A4 mI m4 ba nb 1 barr bx BXA); [exact (K24 _ _ Lba2 Hba' NPa) | exact (K24 _ _ Lbarr2 Hbarr' NPr) |].
      intros Hnb. destruct NB as [[_ Hn0] | [Hbx _]]; [lia|]. destruct (Fbx Hbx) as (Lbx1 & Lbx2 & Hbx').
      apply (K24 _ _ Lbx2 Hbx'). intros ->. pose proof (S01 _ _ Lpix). congruence. }
    split; [exact ONA | exact RM4].
  Qed.

  (* [comment removed for export] *)
  Lemma LI : forall A1 ba barr bx nb A2 mI vmI rI, ST_I A1 ba barr bx nb A2 mI vmI rI ->
    realizes SEGS (mkCfg (mkst rI (0x166e0 : word) mI al_rom) (with_vmmaps vmI md)) S.
  Proof.
    intros A1 ba barr bx nb A2 mI vmI rI STI.
    pose proof STI as ((HWI & R2 & R4 & R3 & R27 & CEI & LpI & SUBI & Z0I & KP & PMI) & R8 & R9 & R18 & R19 & R21 & R20 & R22 & R23z & R25 & R26 & S01 & S12 & Hw & Hh & PXI & KpixI & Hba & Fba & Fbx & OBA & RM). prep.
    pose proof PX as (Wp0 & Wp64 & WF & _). pose proof (wf_w _ WF) as Rw.
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    destruct (cc_I al_rom rI mI (p_w v) Rw R8 R19 R23z R25 R26) as (r1 & RUN1 & V2 & V1 & V10 & V11 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWI)) | exact (mp_lazy _ (w_pure _ _ _ _ HWI)) | exact RUN1 |].
    assert (V2' : getr r1 2 = Z_to_bv 64 (s - 112)) by (rewrite V2; exact R2).
    assert (V4 : getr r1 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    replace (0x1731c : word) with (Z_to_bv 64 0x1731c) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A2 mI _ r1 1 88 (kR - RK_boxa - RK_box) (bR - RB_boxa 1 - RB_box) (Z_to_bv 64 0x167bc) (s - 112) S CK HWI V10 V11 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rvm RM) ltac:(rlia) ltac:(rlia) ltac:(unfold ROOM_NMAX; lia) V1
             ltac:(red; apply bv_eq; reflexivity) V4 V2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A3 m3 vm3 r3 res HW3 Hres CS3 Hnz L0 L1 L00 LEQ ZERO AL16 TOP PM3 RM3. rewrite with_vmmaps_twice in HW3. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x167bc) with (0x167bc : word) by (apply bv_eq; reflexivity).
    assert (RR : getr r3 2 = Z_to_bv 64 (s - 112) /\ getr r3 4 = Z_to_bv 64 0x31370 /\ getr r3 3 = getr regs 3 /\ getr r3 27 = getr regs 27).
    { repeat split; csr; try reflexivity. }
    assert (Hcf : (1 <= u res)%Z /\ (u res + 96 <= alloc_top (c_vm C))%Z).
      { pose proof (u64_range res). unfold round16 in TOP. change ((1 * 88 + 15) / 16)%Z with 6%Z in TOP. lia. }
      assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
      set (cf := u res) in *. clearbody cf. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
      apply (LJ A1 ba barr bx nb A2 mI vmI rI A3 m3 vm3 r3 cf STI HW3 Hres); [| lia | exact L0 | exact L1 | exact L00 | exact LEQ | | exact AL16 | lia | exact PM3 | exact RM3].
      + destruct RR as (X2 & X4 & X3 & X27). repeat split; try assumption; csr; reflexivity.
      + intros i Hi. apply ZERO. lia.
  Qed.

  (* [comment removed for export] *)
  Definition ST_H (A1 : AS) (ba barr : Z) (A2 : AS) (mH : word -> option byte) (vmH : VmMaps) (rH : bvmap 5 word) (bx : Z) : Prop :=
    BASE A2 mH vmH rH /\
    getr rH 8 = Z_to_bv 64 1 /\ getr rH 9 = Z_to_bv 64 1 /\ getr rH 18 = Z_to_bv 64 pix /\ getr rH 19 = Z_to_bv 64 w /\ getr rH 21 = Z_to_bv 64 h /\
    getr rH 20 = Z_to_bv 64 1 /\ getr rH 22 = Z_to_bv 64 ba /\ getr rH 23 = Z_to_bv 64 0 /\ getr rH 25 = Z_to_bv 64 0 /\ getr rH 26 = Z_to_bv 64 1 /\
    getr rH 10 = Z_to_bv 64 bx /\
    sub_live A A1 /\ sub_live A1 A2 /\ (10 <= w)%Z /\ (10 <= h)%Z /\
    PIXat mH pix v /\ keeps A A2 m mH pix /\ (0 <= ba < 2 ^ 64)%Z /\
    FBA A1 ba barr /\ (ba <> 0%Z -> boxa_at C A2 mH ba 0 1 barr 0) /\
    ((bx = 0%Z /\ forall q, live A2 q = live A1 q) \/ box_new C A1 A2 mH bx w h) /\
    aroom A2 vmH (kR - RK_boxa - RK_box) (bR - RB_boxa 1 - RB_box).

  Lemma LH : forall A1 ba barr A2 mH vmH rH bx, ST_H A1 ba barr A2 mH vmH rH bx ->
    realizes SEGS (mkCfg (mkst rH (0x166d0 : word) mH al_rom) (with_vmmaps vmH md)) S.
  Proof.
    intros A1 ba barr A2 mH vmH rH bx
      ((HWH & R2 & R4 & R3 & R27 & CEH & LpH & SUBH & Z0H & KP & PMH) & R8 & R9 & R18 & R19 & R21 & R20 & R22 & R23z & R25 & R26 & R10 & S01 & S12 & Hw & Hh & PXH & KpixH & Hba & Fba & OBA & BX & RM). prep.
    pose proof PX as (Wp0 & Wp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    assert (Hbx : (0 <= bx < 2 ^ 64)%Z).
    { destruct BX as [[-> _] | BN]; [lia|]. pose proof BN as (B1 & B2 & _). pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT. lia. }
    assert (FBX2 : FBX A1 A2 bx).
    { intros NZ. destruct BX as [[Hb0 _] | BN]; [lia|]. pose proof BN as (_ & _ & _ & Lb1 & _ & Lb2 & _). repeat split; [exact Lb1 | exact Lb2 | lia | lia]. }
    destruct (cc_H al_rom rH mH ba (Z_to_bv 64 bx) R10 R22) as (r1 & RUN1 & V2 & V1 & V10 & V11 & V12 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWH)) | exact (mp_lazy _ (w_pure _ _ _ _ HWH)) | exact RUN1 |].
    assert (V2' : getr r1 2 = Z_to_bv 64 (s - 112)) by (rewrite V2; exact R2).
    (* [comment removed for export] *)
    assert (JOIN : forall m' r' nb, W C A2 m' (with_vmmaps vmH md) -> cs_kept r1 r' ->
              (forall (q : Z) k, live A2 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> (ba <> 0%Z -> q <> ba /\ q <> barr) -> keeps A2 A2 mH m' q) ->
              FRM C (s - 112) mH m' ->
              (ba <> 0%Z -> boxa_at C A2 m' ba nb 1 barr bx /\ ((bx = 0%Z /\ nb = 0%Z) \/ (bx <> 0%Z /\ nb = 1%Z))) ->
              POSTM C (c_A0 C) s m m' ->
              realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0x166e0) m' al_rom) (with_vmmaps vmH md)) S).
    { intros m' r' nb HW' CS' K' FR' OBA' PM'. replace (Z_to_bv 64 0x166e0) with (0x166e0 : word) by (apply bv_eq; reflexivity).
      assert (Kq : forall (q : Z) k, live A (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A2 A2 mH m' q).
      { intros q k L Hq. apply (K' q k (SUBH _ _ L) Hq). intros NZ. destruct (Fba NZ) as (X1 & X2 & _). split; intros ->; congruence. }
      apply (LI A1 ba barr bx nb A2 m' vmH r').
      split.
      { split; [exact HW'|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
        split; [unfold cc_cells; apply (cellsZ_frm C (s - 112) mH m'); [exact CK | exact FR' | lia | clear -HsR; forall_cells | exact CEH]|].
        split; [exact LpH|]. split; [exact SUBH|]. split; [exact Z0H|].
        split; [intros q k L Hq NEp; exact (keeps_trans A A2 A2 m mH m' q (KP q k L Hq NEp) (Kq q k L Hq))|]. exact PM'. }
      split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [exact S01|]. split; [exact S12|]. split; [exact Hw|]. split; [exact Hh|].
      split; [destruct (Kq pix 64%Z Lpix ltac:(lia) 64%Z LpH) as (_ & _ & Mp); exact (PIXat_frame mH m' pix v PXH Mp)|].
      split; [exact (keeps_trans A A2 A2 m mH m' pix KpixH (Kq pix 64%Z Lpix ltac:(lia)))|].
      split; [exact Hba|]. split; [exact Fba|]. split; [exact FBX2|]. split; [exact OBA' | exact RM]. }
    destruct (Z.eq_dec ba 0) as [Hb0 | Hb0].
    - (* [comment removed for export] *)
      apply (boxaAddBox_err_W C A2 mH _ r1 (s - 112) ba (Z_to_bv 64 bx) (Z_to_bv 64 0x166e0) S CK HWH V2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V10 V11 (or_introl Hb0)).
      intros m' r' HW' CS' PM' _. apply (JOIN m' r' 0%Z HW' CS').
      + intros q k L Hq _. exact (keeps_postm C A2 A2 A2 (s - 112) mH m' _ q HW' PM' eq_refl eq_refl Hq).
      + exact (proj1 PM').
      + intros NZ. exfalso. exact (NZ Hb0).
      + eapply POSTM_trans; [exact PMH|]. apply (POSTM_sub C (c_A0 C) A2 _ _ _ (W_sub0 _ _ _ _ HWH)). eapply POSTM_mono; [|exact PM']. lia.
    - pose proof (OBA Hb0) as BXA. pose proof BXA as (RB & Halb & Lba2 & L0ba & ARR). destruct (Fba Hb0) as (FA1 & FA2 & Lba1 & Lbarr1 & Hbarr & Hba' & Hbarr').
      destruct ARR as [[Harr0 _] | (Lbarr2 & L0barr & _ & NEab & _)]; [exfalso; exact (Hbarr Harr0)|].
      destruct BX as [[Hbx0 LIVEQ] | BN].
      + (* [comment removed for export] *)
        rewrite Hbx0 in V11.
        apply (boxaAddBox_err_W C A2 mH _ r1 (s - 112) ba (Z_to_bv 64 0) (Z_to_bv 64 0x166e0) S CK HWH V2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
                 ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V10 V11 (or_intror (conj (ltac:(clear -Hba' Hb0; lia) : (1 <= ba < 2 ^ 64)%Z) eq_refl))).
        intros m' r' HW' CS' PM' _. apply (JOIN m' r' 0%Z HW' CS').
        * intros q k L Hq _. exact (keeps_postm C A2 A2 A2 (s - 112) mH m' _ q HW' PM' eq_refl eq_refl Hq).
        * exact (proj1 PM').
        * intros _. rewrite Hbx0. split; [| left; split; reflexivity].
          apply (boxa_at_transport C A2 A2 mH m' ba 0 1 barr 0 BXA);
            [ exact (keeps_postm C A2 A2 A2 (s - 112) mH m' _ ba HW' PM' eq_refl eq_refl Hba')
            | exact (keeps_postm C A2 A2 A2 (s - 112) mH m' _ barr HW' PM' eq_refl eq_refl Hbarr')
            | intros X; discriminate X ].
        * eapply POSTM_trans; [exact PMH|]. apply (POSTM_sub C (c_A0 C) A2 _ _ _ (W_sub0 _ _ _ _ HWH)). eapply POSTM_mono; [|exact PM']. lia.
      + (* [comment removed for export] *)
        pose proof BN as (Hbx1 & TOPbx & Halbx & Lbx1 & L0bx & Lbx2 & LEQ2 & RX).
        assert (NExa : bx <> ba) by (intros ->; congruence). assert (NExr : bx <> barr) by (intros ->; congruence).
        apply (boxaAddBox_W C A2 mH _ r1 (s - 112) ba bx 0 1 1 barr (Z_to_bv 64 0x166e0) S CK HWH V2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
                 ltac:(lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V10 V11 V12 ltac:(lia) RB ltac:(lia) ltac:(lia) NEab Lba2 L0ba
                 ltac:(exact Lbarr2) L0barr).
        intros m' r' HW' CS' _ RB' RDa PAR AGR. apply (JOIN m' r' 1%Z HW' CS').
        * intros q k L Hq NZ'. destruct (NZ' Hb0) as [N1 N2].
          apply (keeps_agree C A2 A2 mH m' _ q HW' eq_refl Hq). intros k' x L' Hx.
          exact (AGR (Z_to_bv 64 q) k' x L' (zneq_w q ba Hq Hba' N1) (zneq_w q barr Hq Hbarr' N2) ltac:(rewrite u_Z2bv by lia; exact Hx)).
        * exact (proj1 (PAR A SUBH FA1 FA2)).
        * intros _. split; [| right; split; [lia | reflexivity]].
          split; [exact RB'|]. split; [exact Halb|]. split; [exact Lba2|]. split; [exact L0ba|].
          right. split; [exact Lbarr2|]. split; [exact L0barr|]. split; [lia|]. split; [exact NEab|].
          right. split; [reflexivity|]. split; [rewrite Z.mul_0_r, Z.add_0_r in RDa; exact RDa|].
          split; [| split; [exact NExa | exact NExr]].
          split; [| split; [exact Halbx | split; [exact Lbx2 | exact L0bx]]].
          exists 0%Z, 0%Z, (p_w v), (p_h v). apply (RECat_frame mH m' bx _ RX). intros x Hx. cbn in Hx.
          exact (AGR (Z_to_bv 64 bx) 20%Z x Lbx2 (zneq_w bx ba ltac:(lia) Hba' NExa) (zneq_w bx barr ltac:(lia) Hbarr' NExr) ltac:(rewrite u_Z2bv by lia; lia)).
        * eapply POSTM_trans; [exact PMH|]. eapply POSTM_mono; [| exact (PAR (c_A0 C) (W_sub0 _ _ _ _ HWH) L0ba L0barr)]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition ST_G (A1 : AS) (m1 : word -> option byte) (vm1 : VmMaps) (r1 : bvmap 5 word) (ba barr : Z) : Prop :=
    BASE A1 m1 vm1 r1 /\
    getr r1 8 = Z_to_bv 64 1 /\ getr r1 9 = Z_to_bv 64 1 /\ getr r1 18 = Z_to_bv 64 pix /\ getr r1 19 = Z_to_bv 64 w /\ getr r1 21 = Z_to_bv 64 h /\
    getr r1 20 = Z_to_bv 64 1 /\ getr r1 10 = Z_to_bv 64 ba /\
    (10 <= w)%Z /\ (10 <= h)%Z /\
    PIXat m1 pix v /\ keeps A A1 m m1 pix /\ (0 <= ba < 2 ^ 64)%Z /\
    FBA A1 ba barr /\ (ba <> 0%Z -> boxa_at C A1 m1 ba 0 1 barr 0) /\
    aroom A1 vm1 (kR - RK_boxa) (bR - RB_boxa 1).

  Lemma LG : forall A1 m1 vm1 r1 ba barr, ST_G A1 m1 vm1 r1 ba barr ->
    realizes SEGS (mkCfg (mkst r1 (0x16694 : word) m1 al_rom) (with_vmmaps vm1 md)) S.
  Proof.
    intros A1 m1 vm1 r1 ba barr
      ((HWG & R2 & R4 & R3 & R27 & CEG & LpG & SUBG & Z0G & KP & PMG) & R8 & R9 & R18 & R19 & R21 & R20 & R10 & Hw & Hh & PXG & KpixG & Hba & Fba & OBA & RM). prep.
    pose proof PX as (Wp0 & Wp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    destruct (cc_G al_rom r1 m1 s ba (p_w v) (p_h v) ltac:(lia) ltac:(lia) Hba ltac:(lia) ltac:(lia)
                (W_sok_win C A1 m1 _ (s - 112) 8 CK HWG ltac:(lia) ltac:(cbn; lia)) R2 R10 R8 R9 R19 R21)
      as (r2 & RUN2 & V2 & V1 & V10 & V11 & V12 & V13 & V22 & V23 & V24 & V25 & V26 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWG)) | exact (mp_lazy _ (w_pure _ _ _ _ HWG)) | exact RUN2 |].
    set (M := m1).      (* [comment removed for export] *)
    assert (WPM : W C A1 M (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) s m M).
    { subst M. split; [exact HWG | exact PMG]. }
    destruct WPM as [HWM PMM].
    assert (KM : forall q : Z, (0 <= q < 2 ^ 64)%Z -> keeps A1 A1 m1 M q).
    { intros q Hq. apply (keeps_frame A1 m1 M _ q HWG HWM); [| exact Hq]. intros x Hx. reflexivity. }
    assert (V4 : getr r2 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    apply (boxCreate_W C A1 M _ r2 (s - 112) (p_w v) (p_h v) (Z_to_bv 64 0x166d0) S CK HWM V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V4 V10 V11 V12 V13 ltac:(lia) ltac:(lia)
             (kR - RK_boxa) (bR - RB_boxa 1) ltac:(rvm RM) ltac:(rlia) ltac:(rlia)).
    intros A2 m2 vm2 r3 HW2 CS2 PM2 OUT2 RM2. rewrite with_vmmaps_twice in HW2. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x166d0) with (0x166d0 : word) by (apply bv_eq; reflexivity).
    assert (OUTn : exists bx : Z, getr r3 10 = Z_to_bv 64 bx /\ (forall q : word, live A1 q <> None -> live A2 q = live A1 q) /\ live A2 (Z_to_bv 64 0) = None /\
              ((bx = 0%Z /\ forall q, live A2 q = live A1 q) \/ box_new C A1 A2 m2 bx (p_w v) (p_h v))).
    { destruct OUT2 as [[A10 LIVEQ] | (bx & A10 & BN)].
      - exists 0%Z. split; [exact A10|]. split; [intros q _; apply LIVEQ|]. split; [rewrite LIVEQ; exact Z0G|]. left. split; [reflexivity | exact LIVEQ].
      - exists bx. split; [exact A10|]. pose proof BN as (Hbx1 & TOPbx & _ & Lbx1 & _ & Lbx2 & LEQ2 & _).
        pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
        split; [intros q Hq; apply LEQ2; intros ->; congruence|].
        split; [rewrite (LEQ2 _ (zneq_w 0 bx ltac:(lia) ltac:(lia) ltac:(lia))); exact Z0G | right; exact BN]. }
    clear OUT2. destruct OUTn as (bx & A10 & E12 & Z02 & BX).
    assert (K12 : forall (q : Z) k, live A1 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A1 A2 m1 m2 q).
    { intros q k L Hq. apply (keeps_trans A1 A1 A2 m1 M m2 q (KM q Hq)).
      exact (keeps_postm C A1 A2 A1 (s - 112) M m2 _ q HW2 PM2 eq_refl (E12 _ ltac:(rewrite L; discriminate)) Hq). }
    apply (LH A1 ba barr A2 m2 vm2 r3 bx).
    split.
    { split; [exact HW2|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split.
      { unfold cc_cells. apply (cellsZ_frm C (s - 112) M m2); [exact CK | exact (proj1 PM2) | lia | clear -HsR; forall_cells |].
        exact CEG. }
      split; [rewrite (E12 _ ltac:(rewrite LpG; discriminate)); exact LpG|].
      split; [intros q k L; rewrite (E12 q ltac:(rewrite (SUBG q k L); discriminate)); exact (SUBG q k L)|].
      split; [exact Z02|].
      split; [intros q k L Hq NEp; exact (keeps_trans A A1 A2 m m1 m2 q (KP q k L Hq NEp) (K12 q k (SUBG _ _ L) Hq))|].
      eapply POSTM_trans; [exact PMM|]. apply (POSTM_sub C (c_A0 C) A1 _ _ _ (W_sub0 _ _ _ _ HWG)). eapply POSTM_mono; [|exact PM2]. lia. }
    split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
    split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
    split; [exact A10|].
    split; [exact SUBG|]. split; [intros q k L; rewrite (E12 q ltac:(rewrite L; discriminate)); exact L|]. split; [exact Hw|]. split; [exact Hh|].
    split; [destruct (K12 pix 64%Z LpG ltac:(lia) 64%Z LpG) as (_ & _ & Mp); exact (PIXat_frame m1 m2 pix v PXG Mp)|].
    split; [exact (keeps_trans A A1 A2 m m1 m2 pix KpixG (K12 pix 64%Z LpG ltac:(lia)))|].
    split; [exact Hba|]. split; [exact Fba|].
    split.
    { intros NZ. destruct (Fba NZ) as (_ & _ & Lba1 & Lbarr1 & Hbarr & Hba' & Hbarr').
      apply (boxa_at_transport C A1 A2 m1 m2 ba 0 1 barr 0 (OBA NZ) (K12 _ _ Lba1 Hba') (K12 _ _ Lbarr1 Hbarr')). intros X; discriminate X. }
    split; [exact BX | exact RM2].
  Qed.

  (* [comment removed for export] *)
  Lemma l_colorfillCreate_main : realizes SEGS (mkCfg (mkst regs (0x16604 : word) m al_rom) md) S.
  Proof.
    prep. pose proof PX as (Wp0 & Wp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh. pose proof (wf_d _ WF) as Rd.
    assert (HsR : (0x52000 + 8192 <= s < 2 ^ 63)%Z) by lia.
    destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lpix ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
    destruct (cc_A al_rom regs m s pix v ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) PX H2 H1 H10 H11 H12)
      as (r0 & RUN0 & Q2 & Q8 & Q9 & Q18 & Q10 & Q11 & AG0).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN0 |].
    assert (WP0 : W C A (ccF m s ret regs) md /\ POSTM C (c_A0 C) s m (ccF m s ret regs)).
    { unfold ccF. do 12 (apply (WP_win C A (c_A0 C) m _ _ _ _ s CK); [| exact (W_sub0 _ _ _ _ HW) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]).
      split; [exact HW | apply POSTM_refl]. }
    destruct WP0 as [HW0 PM0].
    assert (K0 : forall q : Z, (0 <= q < 2 ^ 64)%Z -> keeps A A m (ccF m s ret regs) q).
    { intros q Hq. apply (keeps_frame A m _ md q HW HW0); [| exact Hq]. intros x Hx. unfold LSF in Hx. apply ccF_out; clear -Hx HsR; lia. }
    pose proof (ccF_cells m s ret regs ltac:(lia) ltac:(lia)) as CE0.
    assert (Q4 : getr r0 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    destruct (Z.eq_dec (p_d v) 32) as [Hd | Hd].
    2: { (* [comment removed for export] *)
      destruct (cc_D al_rom r0 (ccF m s ret regs) s (p_d v) ret regs ltac:(lia) ltac:(lia) Rd Hd (W_sev_got C A _ md HW0) (W_sev C A _ md HW0) CE0 Q2 Q10 Q11)
        as (r1 & RUN1 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & AG1).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN1 |].
      apply (returnErrorPtr_W C A _ md r1 s 0x10570 0x10492 15 17 ret (Z_to_bv 64 0) S CK HW0 V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret V10 V11 V12 str_not32 str_cfCreate).
      intros m' r' HW' OUT' GR' CS' A10. unfold LSF in OUT'.
      rewrite <- (with_vmmaps_same md). apply (HK A m' (m_vmmaps md) r').
      - rewrite with_vmmaps_same. exact HW'.
      - apply cs_kept_intro; csr; rewrite ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26; try reflexivity.
      - eapply POSTM_trans; [exact PM0|]. apply (POSTM_sub C (c_A0 C) A _ _ _ (W_sub0 _ _ _ _ HW)).
        eapply (POSTM_range C A _ md m'); [exact CK | exact HW0 | exact OUT' | lia | lia | lia].
      - exact Z0A.
      - left. split; [exact A10|]. intros q k L Hq. apply (keeps_trans A A A m _ m' q (K0 q Hq)).
        apply (keeps_frame A _ m' md q HW0); [exact HW' | | exact Hq]. intros x Hx. unfold LSF in Hx. apply OUT'. clear -Hx. lia.
      - rmono Hrm. }
    (* [comment removed for export] *)
    destruct (cc_B al_rom r0 (ccF m s ret regs) s pix v ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd
                (W_sok_win C A _ md (s - 112) 112 CK HW0 ltac:(lia) ltac:(cbn; lia)) ltac:(apply (PIXat_frame m _ pix v PX); intros x Hx; apply ccF_out; lia) Q2 Q9 Q18 Q10 Q11)
      as (r1 & RUN1 & V2 & V19 & V10 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN1 |].
    set (M1 := wbytes (wbytes (wbytes (wbytes (ccF m s ret regs) _ _) _ _) _ _) _ _).
    assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) s m M1).
    { subst M1. do 4 (apply (WP_win C A (c_A0 C) m _ _ _ _ s CK); [| exact (W_sub0 _ _ _ _ HW) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]).
      split; [exact HW0 | exact PM0]. }
    destruct WP1 as [HW1 PM1].
    assert (K1 : forall q : Z, (0 <= q < 2 ^ 64)%Z -> keeps A A m M1 q).
    { intros q Hq. apply (keeps_trans A A A m _ M1 q (K0 q Hq)). apply (keeps_frame A _ M1 md q HW0 HW1); [| exact Hq].
      intros x Hx. unfold LSF in Hx. subst M1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try (clear -Hx HsR; lia). reflexivity. }
    assert (CE1 : cc_cells M1 s ret regs).
    { unfold cc_cells. subst M1. apply (cellsZ_out (ccF m s ret regs) _ (s - 104) (s - 96)); [| clear -HsR; forall_cells | exact CE0].
      intros x Hx. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try (clear -Hx HsR; lia). reflexivity. }
    (* [comment removed for export] *)
    assert (ERR : forall rE, getr rE 2 = Z_to_bv 64 (s - 112) -> getr rE 4 = Z_to_bv 64 0x31370 -> getr rE 3 = getr regs 3 -> getr rE 27 = getr regs 27 ->
              realizes SEGS (mkCfg (mkst rE (0x16778 : word) M1 al_rom) md) S).
    { intros rE E2 E4 E3 E27.
      destruct (cc_err al_rom rE M1 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r2 & RUN2 & U2 & U1 & U10 & U11 & U12 & AG2).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
      assert (U2' : getr r2 2 = Z_to_bv 64 (s - 112)) by (rewrite U2; exact E2).
      apply (returnErrorPtr_W C A M1 md r2 (s - 112) 0x103f4 0x10492 19 17 (Z_to_bv 64 0x167a4) (Z_to_bv 64 0) S CK HW1 U2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 U11 U12 str_tile str_cfCreate).
      intros m' r' HW' OUT' GR' CS' A10. unfold LSF in OUT'. replace (Z_to_bv 64 0x167a4) with (0x167a4 : word) by (apply bv_eq; reflexivity).
      assert (K' : forall q : Z, (0 <= q < 2 ^ 64)%Z -> keeps A A m m' q).
      { intros q Hq. apply (keeps_trans A A A m M1 m' q (K1 q Hq)). apply (keeps_frame A M1 m' md q HW1 HW'); [| exact Hq]. intros x Hx. unfold LSF in Hx. apply OUT'. clear -Hx. lia. }
      rewrite <- (with_vmmaps_same md). apply (LP A m' (m_vmmaps md) r').
      - split; [rewrite with_vmmaps_same; exact HW'|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
        split; [unfold cc_cells; apply (cellsZ_out M1 m' (s - 112 - 3392) (s - 112)); [exact OUT' | clear -HsR; forall_cells | exact CE1]|].
        split; [exact Lpix|]. split; [apply sub_live_refl|]. split; [exact Z0A|].
        split; [intros q k L Hq _; exact (K' q Hq)|].
        eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C (c_A0 C) A _ _ _ (W_sub0 _ _ _ _ HW)).
        eapply (POSTM_range C A M1 md m'); [exact CK | exact HW1 | exact OUT' | lia | lia | lia].
      - exact A10.
      - exact (K' pix ltac:(lia)).
      - rmono Hrm. }
    assert (V4' : getr r1 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    assert (V3 : getr r1 3 = getr regs 3) by (csr; reflexivity).
    assert (V27 : getr r1 27 = getr regs 27) by (csr; reflexivity).
    destruct (Z_lt_le_dec (p_w v) 10) as [Hw | Hw].
    { eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (cc_E1 al_rom r1 M1 (p_w v) ltac:(lia) V19 V10) |].
      exact (ERR r1 V2 V4' V3 V27). }
    destruct (cc_C al_rom r1 M1 s (p_w v) (p_h v) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(subst M1; rewrite <- (w2b_Z 4 (p_h v)) by lia; rdn_chain) V2 ltac:(csr; reflexivity) V19 V10)
      as (r2 & RUN2 & U21 & U10 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    destruct (Z_lt_le_dec (p_h v) 10) as [Hh | Hh].
    { eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (cc_E2 al_rom r2 M1 (p_h v) ltac:(lia) U21 U10) |].
      apply (ERR r2); csr; try reflexivity. }
    (* [comment removed for export] *)
    destruct (cc_F al_rom r2 M1 (p_h v) ltac:(lia) ltac:(csr; reflexivity) ltac:(csr; reflexivity) U21 U10) as (r3 & RUN3 & X2 & X1 & X10 & X20 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    assert (X2' : getr r3 2 = Z_to_bv 64 (s - 112)) by (rewrite X2; csr; reflexivity).
    assert (X4 : getr r3 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    apply (boxaCreate_W C A M1 md r3 (s - 112) 1 (Z_to_bv 64 0x16694) S CK HW1 X2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 ltac:(lia) Z0A Z0
             kR bR Hrm ltac:(rlia) ltac:(rlia)).
    intros A1 m1 vm1 r4 HWa CSa PMa OUTa RMa. replace (Z_to_bv 64 0x16694) with (0x16694 : word) by (apply bv_eq; reflexivity).
    assert (OUTn : exists ba barr : Z, getr r4 10 = Z_to_bv 64 ba /\ (forall q : word, live A q <> None -> live A1 q = live A q) /\ live A1 (Z_to_bv 64 0) = None /\
              (0 <= ba < 2 ^ 64)%Z /\ FBA A1 ba barr /\ (ba <> 0%Z -> boxa_at C A1 m1 ba 0 1 barr 0)).
    { destruct OUTa as [[A10 LIVEQ] | (ba & barr & A10 & BN)].
      - exists 0%Z, 0%Z. split; [exact A10|]. split; [intros q _; apply LIVEQ|]. split; [rewrite LIVEQ; exact Z0A|]. split; [lia|].
        split; [intros X; exfalso; exact (X eq_refl) | intros X; exfalso; exact (X eq_refl)].
      - exists ba, barr. split; [exact A10|].
        pose proof BN as (RB & Halb & Harr1 & Halr & NEab & La & Lr & L0a & L0r & La1 & Lr1 & LEQ1 & TOPa & TOPr).
        pose proof (RECat_range m1 _ _ RB) as [B0 B1]. cbn in B1. pose proof (BOXA_wf m1 _ 0 1 1 _ RB) as (_ & _ & Wbarr & _).
        pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
        destruct (blk_range C A1 m1 _ (Z_to_bv 64 ba) 24 CK HWa La1 ltac:(lia)) as [Gba _]. rewrite u_Z2bv in Gba by lia.
        split; [intros q Hq; apply LEQ1; intros ->; congruence|].
        split; [rewrite (LEQ1 _ (zneq_w 0 ba ltac:(lia) ltac:(lia) ltac:(lia)) (zneq_w 0 barr ltac:(lia) ltac:(lia) ltac:(lia))); exact Z0A|].
        split; [lia|]. split; [intros _; repeat split; try assumption; lia|].
        intros _. exact (boxa_new_at C A A1 m1 ba 1 barr ltac:(lia) BN). }
    clear OUTa. destruct OUTn as (ba & barr & A10 & E01 & Z01 & Hba & Fba & OBA).
    assert (K01 : forall (q : Z) k, live A (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A A1 m m1 q).
    { intros q k L Hq. apply (keeps_trans A A A1 m M1 m1 q (K1 q Hq)).
      exact (keeps_postm C A A1 A (s - 112) M1 m1 _ q HWa PMa eq_refl (E01 _ ltac:(rewrite L; discriminate)) Hq). }
    apply (LG A1 m1 vm1 r4 ba barr).
    split.
    { split; [exact HWa|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [unfold cc_cells; apply (cellsZ_frm C (s - 112) M1 m1); [exact CK | exact (proj1 PMa) | lia | clear -HsR; forall_cells | exact CE1]|].
      split; [rewrite (E01 _ ltac:(rewrite Lpix; discriminate)); exact Lpix|].
      split; [intros q k L; rewrite (E01 q ltac:(rewrite L; discriminate)); exact L|].
      split; [exact Z01|].
      split; [intros q k L Hq _; exact (K01 q k L Hq)|].
      eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C (c_A0 C) A _ _ _ (W_sub0 _ _ _ _ HW)). eapply POSTM_mono; [|exact PMa]. lia. }
    split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
    split; [csr; reflexivity|]. split; [exact A10|]. split; [lia|]. split; [lia|].
    split; [destruct (K01 pix 64%Z Lpix ltac:(lia) 64%Z Lpix) as (_ & _ & Mp); apply (PIXat_frame m m1 pix v PX Mp)|].
    split; [exact (K01 pix 64%Z Lpix ltac:(lia))|].
    split; [exact Hba|]. split; [exact Fba|]. split; [exact OBA | exact RMa].
  Qed.
End CWalk.
End CfCreate.
