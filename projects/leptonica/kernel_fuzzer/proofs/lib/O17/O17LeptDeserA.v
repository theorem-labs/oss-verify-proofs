(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptStderr O17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17CL7a.
Import O17CL7a.O17LeptErr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17_code_132e8_14000 O17_code_14000_15000 O17_code_15000_16000 O17_code_1d000_1db90.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section DeserA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Definition FR12 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
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
       (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)).

  (* [comment removed for export] *)
  Lemma pd_A0 : forall regs m (s dp nb : Z) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= dp < 2 ^ 64)%Z -> (0 <= nb < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs',
      msteps SEGS (mkst regs (0x150dc : word) m rom) (mkst regs' (0x1511c : word) (FR12 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 nb
      /\ getr regs' 12 = Z_to_bv 64 18446744071562067995 /\ getr regs' 13 = Z_to_bv 64 (nb + 18446744071562067968)
      /\ regs_agree (fun r => In r [2; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s dp nb ret Hs Hs64 Hdp Hnb SOK H2 H1 H10 H11.
    unfold FR12. eexists. split.
    - zv F_14fe0 D_14fe0 (Z_to_bv 64 (s - 112)).
      stepST F_14fe4 D_14fe4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14fe8 D_14fe8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14fec D_14fec (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_14ff0 D_14ff0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_14ff4 D_14ff4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_14ff8 D_14ff8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_14ffc D_14ffc (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_15000 D_15000 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_15004 D_15004 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_15008 D_15008 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_1500c D_1500c (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepb_ft F_15010 D_15010 ltac:(condZ).
      sn F_15014 D_15014.
      zv F_15018 D_15018 (Z_to_bv 64 (nb + 18446744071562067968)).
      sn F_1501c D_1501c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A1 : forall regs m (nb : Z),
    (28 <= nb < 2 ^ 31)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    exists regs', msteps SEGS (mkst regs (0x1511c : word) m rom) (mkst regs' (0x1517c : word) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof.
    intros regs m nb Hnb H12 H13. eexists. split.
    - stepb_tk F_15020 D_15020 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A2 : forall regs m (nb : Z),
    (0 <= nb < 28)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    getr regs 11 = Z_to_bv 64 nb ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) -> rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x1511c : word) m rom) (mkst regs' (0x13a04 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x107be /\ getr regs' 11 = Z_to_bv 64 0x1068f /\ getr regs' 12 = Z_to_bv 64 nb /\ getr regs' 1 = Z_to_bv 64 0x15150
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m nb Hnb H12 H13 H11 Rg Rs. eexists. split.
    - stepb_ft F_15020 D_15020 ltac:(condZ).
      sn F_15024 D_15024.
      stepLD F_15028 D_15028 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1502c D_1502c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15030 D_15030. stepb_ft F_15034 D_15034 ltac:(condZ).
      sn F_15038 D_15038. sn F_1503c D_1503c. sn F_15040 D_15040. sn F_15044 D_15044. sn F_15048 D_15048. sn F_1504c D_1504c.
      sn F_15050 D_15050. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_B : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    u b0 = 115%Z -> u b1 = 112%Z -> u b2 = 105%Z -> u b3 = 120%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x1517c : word) m rom) (mkst regs' (0x151ac : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof.
    intros regs m dp b0 b1 b2 b3 Hdp Hdp4 R0 R1 R2 R3 E0 E1 E2 E3 H10. eexists. split.
    - stepLBU F_15080 D_15080 b0 ltac:(addr_norm; exact R0). rewrite E0.
      sn F_15084 D_15084. stepb_ft F_15088 D_15088 ltac:(condZ).
      stepLBU F_1508c D_1508c b1 ltac:(addr_norm; exact R1). rewrite E1.
      sn F_15090 D_15090. stepb_ft F_15094 D_15094 ltac:(condZ).
      stepLBU F_15098 D_15098 b2 ltac:(addr_norm; exact R2). rewrite E2.
      sn F_1509c D_1509c. stepb_ft F_150a0 D_150a0 ltac:(condZ).
      stepLBU F_150a4 D_150a4 b3 ltac:(addr_norm; exact R3). rewrite E3.
      sn F_150a8 D_150a8. stepb_ft F_150ac D_150ac ltac:(condZ).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Bbad : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    ~ (u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x1517c : word) m rom) (mkst regs' (0x151e8 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof.
    intros regs m dp b0 b1 b2 b3 Hdp Hdp4 R0 R1 R2 R3 NE H10.
    pose proof (u8_range b0). pose proof (u8_range b1). pose proof (u8_range b2). pose proof (u8_range b3).
    destruct (Z.eq_dec (u b0) 115) as [E0|E0].
    2: { clear NE. eexists. split.
         { stepLBU F_15080 D_15080 b0 ltac:(addr_norm; exact R0). sn F_15084 D_15084. stepb_tk F_15088 D_15088 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    destruct (Z.eq_dec (u b1) 112) as [E1|E1].
    2: { clear NE. eexists. split.
         { stepLBU F_15080 D_15080 b0 ltac:(addr_norm; exact R0). sn F_15084 D_15084. stepb_ft F_15088 D_15088 ltac:(condZ).
           stepLBU F_1508c D_1508c b1 ltac:(addr_norm; exact R1). sn F_15090 D_15090. stepb_tk F_15094 D_15094 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    destruct (Z.eq_dec (u b2) 105) as [E2|E2].
    2: { clear NE. eexists. split.
         { stepLBU F_15080 D_15080 b0 ltac:(addr_norm; exact R0). sn F_15084 D_15084. stepb_ft F_15088 D_15088 ltac:(condZ).
           stepLBU F_1508c D_1508c b1 ltac:(addr_norm; exact R1). sn F_15090 D_15090. stepb_ft F_15094 D_15094 ltac:(condZ).
           stepLBU F_15098 D_15098 b2 ltac:(addr_norm; exact R2). sn F_1509c D_1509c. stepb_tk F_150a0 D_150a0 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    assert (E3 : u b3 <> 120%Z) by (intros E3; apply NE; lia). clear NE.
    eexists. split.
    { stepLBU F_15080 D_15080 b0 ltac:(addr_norm; exact R0). sn F_15084 D_15084. stepb_ft F_15088 D_15088 ltac:(condZ).
      stepLBU F_1508c D_1508c b1 ltac:(addr_norm; exact R1). sn F_15090 D_15090. stepb_ft F_15094 D_15094 ltac:(condZ).
      stepLBU F_15098 D_15098 b2 ltac:(addr_norm; exact R2). sn F_1509c D_1509c. stepb_ft F_150a0 D_150a0 ltac:(condZ).
      stepLBU F_150a4 D_150a4 b3 ltac:(addr_norm; exact R3). sn F_150a8 D_150a8. stepb_tk F_150ac D_150ac ltac:(condZ).
      apply mst_refl. }
    solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pd_C : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x151ac : word) m rom) (mkst regs' (0x15244 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 wr /\ getr regs' 12 = Z_to_bv 64 18446744073708551615
      /\ regs_agree (fun r => In r [9; 12; 13]%list) regs regs'.
  Proof.
    intros regs m dp wr bs4 Hdp Hdphi R4 W4 Hwr H10. eexists. split.
    - stepLD F_150b0 D_150b0 bs4 (Z_to_bv 64 wr) ltac:(addr_norm; exact R4) ltac:(rewrite u_Z2bv by lia; exact W4).
      rewrite (v_lw_small wr) by lia.
      sn F_150b4 D_150b4. sn F_150b8 D_150b8.
      sn F_150bc D_150bc. fixv (Z_to_bv 64 (sw32 (sw32 wr + 18446744073708551615))) ltac:(rewrite v_addw_Z, (sw32_small wr) by lia; reflexivity).
      stepb_tk F_150c0 D_150c0 ltac:(pin; rewrite c_ltu_zx; apply wchk_ok; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Cbad : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (0 <= wr < 2 ^ 32)%Z -> ~ (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x151ac : word) m rom) (mkst regs' (0x151c0 : word) m rom)
      /\ regs_agree (fun r => In r [9; 12; 13]%list) regs regs'.
  Proof.
    intros regs m dp wr bs4 Hdp Hdphi R4 W4 Hwr NW H10. eexists. split.
    - stepLD F_150b0 D_150b0 bs4 (Z_to_bv 64 wr) ltac:(addr_norm; exact R4) ltac:(rewrite u_Z2bv by lia; exact W4).
      rewrite (v_lw_Z wr).
      sn F_150b4 D_150b4. sn F_150b8 D_150b8.
      sn F_150bc D_150bc. fixv (Z_to_bv 64 (sw32 (sw32 wr + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      stepb_ft F_150c0 D_150c0 ltac:(pin; rewrite c_ltu_zx; apply wchk_bad; lia).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_D : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 12 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x15244 : word) m rom) (mkst regs' (0x15278 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 hr /\ regs_agree (fun r => In r [18; 13]%list) regs regs'.
  Proof.
    intros regs m dp hr bs8 Hdp Hdphi R8 W8 Hhr H10 H12. eexists. split.
    - stepLD F_15148 D_15148 bs8 (Z_to_bv 64 hr) ltac:(addr_norm; exact R8) ltac:(rewrite u_Z2bv by lia; exact W8).
      rewrite (v_lw_small hr) by lia.
      sn F_1514c D_1514c. fixv (Z_to_bv 64 (sw32 (sw32 hr + 18446744073708551615))) ltac:(rewrite v_addw_Z, (sw32_small hr) by lia; reflexivity).
      stepb_tk F_15150 D_15150 ltac:(pin; rewrite c_ltu_zx; apply wchk_ok; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Dbad : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (0 <= hr < 2 ^ 32)%Z -> ~ (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 12 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x15244 : word) m rom) (mkst regs' (0x15250 : word) m rom)
      /\ regs_agree (fun r => In r [18; 13]%list) regs regs'.
  Proof.
    intros regs m dp hr bs8 Hdp Hdphi R8 W8 Hhr NH H10 H12. eexists. split.
    - stepLD F_15148 D_15148 bs8 (Z_to_bv 64 hr) ltac:(addr_norm; exact R8) ltac:(rewrite u_Z2bv by lia; exact W8).
      rewrite (v_lw_Z hr).
      sn F_1514c D_1514c. fixv (Z_to_bv 64 (sw32 (sw32 hr + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      stepb_ft F_15150 D_15150 ltac:(pin; rewrite c_ltu_zx; apply wchk_bad; lia).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_E : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x15278 : word) m rom) (mkst regs' (0x152b0 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof.
    intros regs m wr hr Hw Hh Hwh H9 H18. eexists. split.
    - zv F_1517c D_1517c (Z_to_bv 64 (hr * wr)). sn F_15180 D_15180. sn F_15184 D_15184.
      stepb_tk F_15188 D_15188 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  Lemma pd_Ebad : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (400000000 < wr * hr)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x15278 : word) m rom) (mkst regs' (0x15288 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof.
    intros regs m wr hr Hw Hh Hwh H9 H18. assert (hr * wr < 2 ^ 63)%Z by nia. eexists. split.
    - zv F_1517c D_1517c (Z_to_bv 64 (hr * wr)). sn F_15180 D_15180. sn F_15184 D_15184.
      stepb_ft F_15188 D_15188 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_F : forall regs m (dp nb ncr q dr wr hr : Z) bs20 bs12,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr <= 256)%Z -> (ncr + 7 < q)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 12)) 4 = Some bs12 -> bytes_le_to_Z bs12 = dr -> (0 <= dr < 2 ^ 32)%Z ->
    (0 <= wr < 2 ^ 64)%Z -> (0 <= hr < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x152b0 : word) m rom) (mkst regs' (0x13ccc : word) m rom)
      /\ getr regs' 23 = Z_to_bv 64 ncr /\ getr regs' 8 = Z_to_bv 64 nb /\ getr regs' 25 = Z_to_bv 64 dp
      /\ getr regs' 20 = Z_to_bv 64 (zx (sw32 dr))
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 (zx (sw32 dr)) /\ getr regs' 1 = Z_to_bv 64 0x152e4
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 20; 23; 25]%list) regs regs'.
  Proof.
    intros regs m dp nb ncr q dr wr hr bs20 bs12 Hdp Hdphi Hnb Hq R20 W20 Hncr Hq7 R12 W12 Hdr Hwr Hhr H10 H11 H9 H18.
    assert (Hq4 : (0 <= q < 2 ^ 29)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    eexists. split.
    - stepLD F_151b4 D_151b4 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
      sn F_151b8 D_151b8. stepb_ft F_151bc D_151bc ltac:(condZ).
      zv F_151c0 D_151c0 (Z_to_bv 64 (ncr + 7)).
      stepiv F_151c4 D_151c4 (Z_to_bv 64 q) ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; subst q; reflexivity).
      stepb_ft F_151c8 D_151c8 ltac:(condZ).
      sn F_151cc D_151cc. sn F_151d0 D_151d0.
      stepLD F_151d4 D_151d4 bs12 (Z_to_bv 64 dr) ltac:(addr_norm; exact R12) ltac:(rewrite u_Z2bv by lia; exact W12).
      rewrite (v_lw_Z dr), <- (zbv_zx (sw32 dr)).
      sn F_151d8 D_151d8. sn F_151dc D_151dc. sn F_151e0 D_151e0. sn F_151e4 D_151e4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Fbad : forall regs m (dp nb ncr q : Z) bs20,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr < 2 ^ 32)%Z -> ~ (ncr <= 256 /\ ncr + 7 < q)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs', msteps SEGS (mkst regs (0x152b0 : word) m rom) (mkst regs' (0x15398 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13; 23]%list) regs regs'.
  Proof.
    intros regs m dp nb ncr q bs20 Hdp Hdphi Hnb Hq R20 W20 Hncr NC H10 H11.
    assert (Hq4 : (0 <= q < 2 ^ 29)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct (Z_lt_ge_dec 256 ncr) as [BIG|OK].
    - clear NC. eexists. split.
      { stepLD F_151b4 D_151b4 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
        sn F_151b8 D_151b8. stepb_tk F_151bc D_151bc ltac:(condZ). apply mst_refl. }
      solve_regs_agree.
    - assert (NQ : (q <= ncr + 7)%Z) by lia. clear NC. eexists. split.
      { stepLD F_151b4 D_151b4 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
        sn F_151b8 D_151b8. stepb_ft F_151bc D_151bc ltac:(condZ).
        zv F_151c0 D_151c0 (Z_to_bv 64 (ncr + 7)).
        stepiv F_151c4 D_151c4 (Z_to_bv 64 q) ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; subst q; reflexivity).
        stepb_tk F_151c8 D_151c8 ltac:(condZ). apply mst_refl. }
      solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Definition et_leaves : list (Z * Z) :=
    [(0x151e8, 0x107e1); (0x151c0, 0x10a2e); (0x15250, 0x10371); (0x15288, 0x10327); (0x15398, 0x10866); (0x153c0, 0x10505)]%Z.
  Lemma pd_ET : forall pc msg regs m,
    In (pc, msg) et_leaves ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) -> rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x1520c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x1068f
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros pc msg regs m Hin Rg Rs. unfold et_leaves in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E; intros <- <-.
    - replace (Z_to_bv 64 0x151e8) with (0x151e8 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_150ec D_150ec.
        stepLD F_150f0 D_150f0 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_150f4 D_150f4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_150f8 D_150f8. stepb_ft F_150fc D_150fc ltac:(condZ).
        sn F_15100 D_15100. sn F_15104 D_15104. sn F_15108 D_15108. sn F_1510c D_1510c.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x151c0) with (0x151c0 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_150c4 D_150c4.
        stepLD F_150c8 D_150c8 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_150cc D_150cc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_150d0 D_150d0. stepb_ft F_150d4 D_150d4 ltac:(condZ).
        sn F_150d8 D_150d8. sn F_150dc D_150dc. sn F_150e0 D_150e0. sn F_150e4 D_150e4.
        sn F_150e8 D_150e8.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15250) with (0x15250 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_15154 D_15154.
        stepLD F_15158 D_15158 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_1515c D_1515c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15160 D_15160. stepb_ft F_15164 D_15164 ltac:(condZ).
        sn F_15168 D_15168. sn F_1516c D_1516c. sn F_15170 D_15170. sn F_15174 D_15174.
        sn F_15178 D_15178.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15288) with (0x15288 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_1518c D_1518c.
        stepLD F_15190 D_15190 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15194 D_15194 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15198 D_15198. stepb_ft F_1519c D_1519c ltac:(condZ).
        sn F_151a0 D_151a0. sn F_151a4 D_151a4. sn F_151a8 D_151a8. sn F_151ac D_151ac.
        sn F_151b0 D_151b0.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15398) with (0x15398 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_1529c D_1529c.
        stepLD F_152a0 D_152a0 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_152a4 D_152a4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_152a8 D_152a8. stepb_ft F_152ac D_152ac ltac:(condZ).
        sn F_152b0 D_152b0. sn F_152b4 D_152b4. sn F_152b8 D_152b8. sn F_152bc D_152bc.
        sn F_152c0 D_152c0.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x153c0) with (0x153c0 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_152c4 D_152c4.
        stepLD F_152c8 D_152c8 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_152cc D_152cc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_152d0 D_152d0. stepb_ft F_152d4 D_152d4 ltac:(condZ).
        sn F_152d8 D_152d8. sn F_152dc D_152dc. sn F_152e0 D_152e0. sn F_152e4 D_152e4.
        sn F_152e8 D_152e8.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition ej_leaves : list (Z * Z) := [(0x15420, 0x108da); (0x15458, 0x10b77); (0x154c0, 0x10424)]%Z.
  Lemma pd_EJ : forall pc msg regs m,
    In (pc, msg) ej_leaves ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) -> rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x13aa0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x1068f /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x154ec
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros pc msg regs m Hin Rg Rs. unfold ej_leaves in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
    - replace (Z_to_bv 64 0x15420) with (0x15420 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_15324 D_15324.
        stepLD F_15328 D_15328 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_1532c D_1532c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15330 D_15330. stepb_ft F_15334 D_15334 ltac:(condZ).
        sn F_15338 D_15338. sn F_1533c D_1533c. sn F_15340 D_15340. sn F_15344 D_15344.
        sn F_15348 D_15348.
        sn F_153e8 D_153e8. sn F_153ec D_153ec.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15458) with (0x15458 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_1535c D_1535c.
        stepLD F_15360 D_15360 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15364 D_15364 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15368 D_15368. stepb_ft F_1536c D_1536c ltac:(condZ).
        sn F_15370 D_15370. sn F_15374 D_15374. sn F_15378 D_15378. sn F_1537c D_1537c.
        sn F_15380 D_15380.
        sn F_153e8 D_153e8. sn F_153ec D_153ec.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x154c0) with (0x154c0 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_153c4 D_153c4.
        stepLD F_153c8 D_153c8 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_153cc D_153cc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_153d0 D_153d0. stepb_ft F_153d4 D_153d4 ltac:(condZ).
        sn F_153d8 D_153d8. sn F_153dc D_153dc. sn F_153e0 D_153e0. sn F_153e4 D_153e4.
        sn F_153e8 D_153e8. sn F_153ec D_153ec.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition pd_cells (m : word -> option byte) (s : Z) (ret : word) (sv : nat -> word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (sv 8%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (sv 9%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (sv 18%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (sv 19%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (sv 20%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (sv 21%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (sv 22%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (sv 23%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (sv 24%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (sv 25%nat)).

  (* [comment removed for export] *)
  Lemma pd_X50 : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x1520c : word) m rom) (mkst regs' (0x13aa0 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs m s ret sv Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) H2. eexists. split.
    - sn F_15110 D_15110.
      stepLD8 F_15114 D_15114 ret. stepLD8 F_15118 D_15118 (sv 8%nat). stepLD8 F_1511c D_1511c (sv 9%nat).
      stepLD8 F_15120 D_15120 (sv 18%nat). stepLD8 F_15124 D_15124 (sv 19%nat). stepLD8 F_15128 D_15128 (sv 20%nat).
      stepLD8 F_1512c D_1512c (sv 21%nat). stepLD8 F_15130 D_15130 (sv 22%nat). stepLD8 F_15134 D_15134 (sv 23%nat).
      stepLD8 F_15138 D_15138 (sv 24%nat). stepLD8 F_1513c D_1513c (sv 25%nat).
      zv F_15140 D_15140 (Z_to_bv 64 s). sn F_15144 D_15144. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x154f4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs m s ret sv Hs Hs64 Hret (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) H2. eexists. split.
    - stepLD8 F_153f8 D_153f8 ret. stepLD8 F_153fc D_153fc (sv 8%nat). stepLD8 F_15400 D_15400 (sv 9%nat).
      stepLD8 F_15404 D_15404 (sv 18%nat). stepLD8 F_15408 D_15408 (sv 19%nat). stepLD8 F_1540c D_1540c (sv 20%nat).
      stepLD8 F_15410 D_15410 (sv 21%nat). stepLD8 F_15414 D_15414 (sv 22%nat). stepLD8 F_15418 D_15418 (sv 23%nat).
      stepLD8 F_1541c D_1541c (sv 24%nat). stepLD8 F_15420 D_15420 (sv 25%nat).
      zv F_15424 D_15424 (Z_to_bv 64 s). stepret F_15428 D_15428 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_R0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x154f0 : word) m rom) (mkst regs' (0x154f4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_153f4 D_153f4; apply mst_refl|]. split; [gres; reflexivity | solve_regs_agree]. Qed.

  Lemma pd_J94 : forall regs m, exists regs', msteps SEGS (mkst regs (0x15150 : word) m rom) (mkst regs' (0x154f0 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_15054 D_15054; apply mst_refl | solve_regs_agree]. Qed.
  Lemma pd_J60 : forall regs m, exists regs', msteps SEGS (mkst regs (0x1541c : word) m rom) (mkst regs' (0x154f0 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_15320 D_15320; apply mst_refl | solve_regs_agree]. Qed.
  Lemma pd_J30 : forall regs m, exists regs', msteps SEGS (mkst regs (0x154ec : word) m rom) (mkst regs' (0x154f4 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_153f0 D_153f0; apply mst_refl | solve_regs_agree]. Qed.
  Ltac rdn_out R := rewrite rdn_wbytes_out_Z; [exact R | rewrite ?length_N_to_le_bytes; lia].

  (* [comment removed for export] *)
  Lemma pd_G0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x152e4 : word) m rom)
                              (mkst regs' (0x153c0 : word) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_151e8 D_151e8 (Z_to_bv 64 (s - 104)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_151ec D_151ec ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_G : forall regs m (s dp nb nc pix1 wpl hr ir : Z) (v1 : pixv) bsi,
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    PIXat m pix1 v1 -> (4096 <= pix1)%Z -> (pix1 + 64 <= s - 112)%Z -> p_wpl v1 = wpl -> (1 <= hr <= 1000000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * hr) <= 67108864)%Z ->
    (0 <= nc <= 256)%Z -> (28 <= nb < 2 ^ 31)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= dp)%Z -> (dp + nb <= s - 112)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4 * nc + 24)) 4 = Some bsi -> bytes_le_to_Z bsi = ir -> (0 <= ir < 2 ^ 32)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 23 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 nb ->
    getr regs 25 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x152e4 : word) m rom)
                              (mkst regs' (0x14008 : word) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 (s - 104) /\ getr regs' 1 = Z_to_bv 64 0x1531c
      /\ getr regs' 19 = Z_to_bv 64 nc /\ getr regs' 24 = Z_to_bv 64 (dp + 4 * nc) /\ getr regs' 21 = Z_to_bv 64 (zx (sw32 ir))
      /\ getr regs' 8 = Z_to_bv 64 (4 * (wpl * hr)) /\ getr regs' 22 = Z_to_bv 64 (nb - 4 * nc - 28)
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 19; 21; 22; 24]%list) regs regs'.
  Proof.
    intros regs m s dp nb nc pix1 wpl hr ir v1 bsi Hs Hs64 SOK PX Gp Hp1 Hwpl Hhr Hw0 Hsz Hnc Hnb Hnc4 Hdp Hdpnb Ri Wi Hir H2 H10 H23 H8 H25 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rw. rewrite Hwpl in Rw.
    pose proof (zx_range (sw32 ir)) as Hzi.
    assert (PX1 : PIXat (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) pix1 v1).
    { apply PIXat_out; [exact PX | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    eexists. split.
    - stepST F_151e8 D_151e8 (Z_to_bv 64 (s - 104)) (Z_to_bv 64 pix1) ltac:(sok_in SOK).
      stepb_ft F_151ec D_151ec ltac:(condZ).
      sn F_151f0 D_151f0. fixv (Z_to_bv 64 nc) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      sn F_151f4 D_151f4.
      stepb_ft F_13ecc D_13ecc ltac:(condZ).
      stepLD F_13ed0 D_13ed0 (Z_to_le_bytes 4 wpl) (Z_to_bv 64 wpl) ltac:(addr_norm; rewrite <- Hwpl; exact (PIX_rd_wpl SEGS _ _ _ PX1)) ltac:(apply lez4; lia).
      rewrite (v_lw_small wpl) by lia.
      stepret F_13ed4 D_13ed4 (0x152f4 : word) ltac:(bveq).
      stepiv F_151f8 D_151f8 (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      stepiv F_151fc D_151fc (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_15200 D_15200. fixv (Z_to_bv 64 (nb - 4 * nc)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      zv F_15204 D_15204 (Z_to_bv 64 (dp + 4 * nc)).
      stepLD F_15208 D_15208 bsi (Z_to_bv 64 ir) ltac:(rewrite zbv_addi; rdn_out Ri) ltac:(rewrite u_Z2bv by lia; exact Wi).
      rewrite (v_lw_Z ir), <- (zbv_zx (sw32 ir)).
      zv F_1520c D_1520c (Z_to_bv 64 (hr * wpl)).
      sn F_15210 D_15210. fixv (Z_to_bv 64 (4 * (wpl * hr))) ltac:(rewrite v_slliw_2, sw32_small by lia; f_equal; lia).
      sn F_15214 D_15214. fixv (Z_to_bv 64 (nb - 4 * nc - 28)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      zv F_15218 D_15218 (Z_to_bv 64 (s - 104)).
      sn F_1521c D_1521c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_H : forall regs m (sz wr hr d : Z),
    (0 <= sz < 2 ^ 32)%Z ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 sz ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr -> getr regs 20 = Z_to_bv 64 d ->
    exists regs', msteps SEGS (mkst regs (0x1531c : word) m rom) (mkst regs' (0x13b04 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 1 = Z_to_bv 64 0x15334
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m sz wr hr d Hsz H8 H22 H21 H9 H18 H20. eexists. split.
    - stepb_ft F_15220 D_15220 ltac:(condZ). stepb_ft F_15224 D_15224 ltac:(condZ).
      sn F_15228 D_15228. sn F_1522c D_1522c. sn F_15230 D_15230. sn F_15234 D_15234. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Hbad : forall regs m (sz msz isz : Z),
    (0 <= sz < 2 ^ 32)%Z -> (0 <= msz < 2 ^ 32)%Z -> (0 <= isz < 2 ^ 64)%Z -> (sz <> msz \/ sz <> isz) ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) -> rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 msz -> getr regs 21 = Z_to_bv 64 isz ->
    exists regs', msteps SEGS (mkst regs (0x1531c : word) m rom) (mkst regs' (0x13a04 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10593 /\ getr regs' 11 = Z_to_bv 64 0x1068f /\ getr regs' 1 = Z_to_bv 64 0x1541c
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m sz msz isz Hsz Hmsz Hisz NE Rg Rs H8 H22 H21.
    destruct (Z.eq_dec sz msz) as [E1|N1].
    - assert (N2 : sz <> isz) by lia. clear NE. eexists. split.
      { stepb_ft F_15220 D_15220 ltac:(condZ). stepb_tk F_15224 D_15224 ltac:(condZ).
        sn F_152ec D_152ec.
        stepLD F_152f0 D_152f0 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_152f4 D_152f4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_152f8 D_152f8. stepb_ft F_152fc D_152fc ltac:(condZ).
        sn F_15300 D_15300. sn F_15304 D_15304. sn F_15308 D_15308. sn F_1530c D_1530c.
        sn F_15310 D_15310. sn F_15314 D_15314. sn F_15318 D_15318. sn F_1531c D_1531c. apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - clear NE. eexists. split.
      { stepb_tk F_15220 D_15220 ltac:(condZ).
        sn F_152ec D_152ec.
        stepLD F_152f0 D_152f0 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_152f4 D_152f4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_152f8 D_152f8. stepb_ft F_152fc D_152fc ltac:(condZ).
        sn F_15300 D_15300. sn F_15304 D_15304. sn F_15308 D_15308. sn F_1530c D_1530c.
        sn F_15310 D_15310. sn F_15314 D_15314. sn F_15318 D_15318. sn F_1531c D_1531c. apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pd_I0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15334 : word) m rom)
                              (mkst regs' (0x15420 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_15238 D_15238 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_1523c D_1523c ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I1 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> (1 <= pixd < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15334 : word) m rom)
                              (mkst regs' (0x15484 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [9]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 SOK Hp H2 H10 H23. eexists. split.
    - stepST F_15238 D_15238 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepb_ft F_1523c D_1523c ltac:(condZ). stepb_tk F_15240 D_15240 ltac:(condZ).
      sn F_1534c D_1534c. sn F_15350 D_15350. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I2 : forall regs m (s pixd dp nc : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z -> (0 <= dp < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 nc -> getr regs 25 = Z_to_bv 64 dp -> getr regs 19 = Z_to_bv 64 nc ->
    exists regs', msteps SEGS (mkst regs (0x15334 : word) m rom)
                              (mkst regs' (0x14a4c : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (dp + 24) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 nc /\ getr regs' 1 = Z_to_bv 64 0x15350
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixd dp nc Hs Hs64 SOK Hp Hnc Hdp H2 H10 H23 H25 H19. eexists. split.
    - stepST F_15238 D_15238 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepb_ft F_1523c D_1523c ltac:(condZ). stepb_ft F_15240 D_15240 ltac:(condZ).
      zv F_15244 D_15244 (Z_to_bv 64 (dp + 24)). sn F_15248 D_15248. sn F_1524c D_1524c. sn F_15250 D_15250. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_J0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15350 : word) m rom) (mkst regs' (0x14008 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x15458 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2 H10. eexists. split.
    - stepb_tk F_15254 D_15254 ltac:(condZ). zv F_15354 D_15354 (Z_to_bv 64 (s - 112)). sn F_15358 D_15358. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_J1 : forall regs m (s cm pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x15350 : word) m rom) (mkst regs' (0x14154 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 1 = Z_to_bv 64 0x15364
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s cm pixd Hs Hs64 Hcm Hp Rp H2 H10. eexists. split.
    - stepb_ft F_15254 D_15254 ltac:(condZ). sn F_15258 D_15258.
      stepLD8 F_1525c D_1525c (Z_to_bv 64 pixd). sn F_15260 D_15260. sn F_15264 D_15264. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_K : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15364 : word) m rom) (mkst regs' (0x15484 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rp H2 H10. eexists. split.
    - stepb_tk F_15268 D_15268 ltac:(condZ). stepLD8 F_15384 D_15384 (Z_to_bv 64 pixd). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_GD : forall regs m (pixd e8 sz : Z) (v : pixv),
    PIXat m pixd v -> (4096 <= pixd)%Z -> (0 <= e8)%Z -> (e8 + 28 < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 24 = Z_to_bv 64 e8 -> getr regs 8 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x15484 : word) m rom) (mkst regs' (0x1d738 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (e8 + 28) /\ getr regs' 12 = Z_to_bv 64 sz /\ getr regs' 1 = Z_to_bv 64 0x15494
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixd e8 sz v PX Gp He8 He8' H10 H24 H8. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF).
    eexists. split.
    - sn F_15388 D_15388. stepb_ft F_141bc D_141bc ltac:(condZ).
      stepLD F_141c0 D_141c0 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_141c4 D_141c4 (0x15488 : word) ltac:(bveq).
      zv F_1538c D_1538c (Z_to_bv 64 (e8 + 28)). sn F_15390 D_15390. sn F_15394 D_15394. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_L0 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15494 : word) m rom) (mkst regs' (0x154f4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rp H2 H23. eexists. split.
    - stepb_tk F_15398 D_15398 ltac:(condZ). stepLD8 F_153b4 D_153b4 (Z_to_bv 64 pixd). sn F_153b8 D_153b8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_L1 : forall regs m (s pixd nc cm : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 23 = Z_to_bv 64 nc -> getr regs 9 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x15494 : word) m rom) (mkst regs' (0x146cc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 (s - 92) /\ getr regs' 1 = Z_to_bv 64 0x154a8
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixd nc cm Hs Hs64 Hp Hnc Rp H2 H23 H9. eexists. split.
    - stepb_ft F_15398 D_15398 ltac:(condZ). stepLD8 F_1539c D_1539c (Z_to_bv 64 pixd).
      zv F_153a0 D_153a0 (Z_to_bv 64 (s - 92)). sn F_153a4 D_153a4. sn F_153a8 D_153a8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_M1 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x154a8 : word) m rom) (mkst regs' (0x154f4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rv Rp H2. eexists. split.
    - stepLD F_153ac D_153ac (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_ft F_153b0 D_153b0 ltac:(condZ). stepLD8 F_153b4 D_153b4 (Z_to_bv 64 pixd). sn F_153b8 D_153b8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_M0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 0) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (0x154a8 : word) m rom) (mkst regs' (0x14008 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x154c0 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 Rv H2. eexists. split.
    - stepLD F_153ac D_153ac (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_tk F_153b0 D_153b0 ltac:(condZ). zv F_153bc D_153bc (Z_to_bv 64 (s - 112)). sn F_153c0 D_153c0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End DeserA.
