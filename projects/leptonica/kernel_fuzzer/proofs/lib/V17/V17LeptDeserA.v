(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17LeptStderr V17LeptBase V17LeptErr V17_code_133ec_14000 V17_code_15000_16000.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section DeserA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LLU17} {P16 : V17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Definition FR9 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
       (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
       (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
       (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
       (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)).

  (* [comment removed for export] *)
  Lemma pd_A0 : forall regs m (s dp nb : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= dp < 2 ^ 64)%Z -> (0 <= nb < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs',
      msteps SEGS (mkst regs (0x157b4 : word) m rom) (mkst regs' (0x157ec : word) (FR9 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 nb
      /\ getr regs' 12 = Z_to_bv 64 18446744071562067995 /\ getr regs' 13 = Z_to_bv 64 (nb + 18446744071562067968)
      /\ regs_agree (fun r => In r [2; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s dp nb ret Hs Hs64 Hdp Hnb SOK H2 H1 H10 H11.
    unfold FR9. eexists. split.
    - zv F_156b8 D_156b8 (Z_to_bv 64 (s - 96)).
      stepST F_156bc D_156bc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_156c0 D_156c0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_156c4 D_156c4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_156c8 D_156c8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_156cc D_156cc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_156d0 D_156d0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_156d4 D_156d4 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_156d8 D_156d8 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_156dc D_156dc (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepb_ft F_156e0 D_156e0 ltac:(condZ).
      sn F_156e4 D_156e4.
      zv F_156e8 D_156e8 (Z_to_bv 64 (nb + 18446744071562067968)).
      sn F_156ec D_156ec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A1 : forall regs m (nb : Z),
    (28 <= nb < 2 ^ 31)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    exists regs', msteps SEGS (mkst regs (0x157ec : word) m rom) (mkst regs' (0x1584c : word) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof.
    intros regs m nb Hnb H12 H13. eexists. split.
    - stepb_tk F_156f0 D_156f0 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A2 : forall regs m (nb : Z),
    (0 <= nb < 28)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    getr regs 11 = Z_to_bv 64 nb ->
    rdn SEGS m (Z_to_bv 64 0x1f9d0) 8 = Some (Z_to_le_bytes 8 0x20a40) -> rdn SEGS m (Z_to_bv 64 0x20a40) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x157ec : word) m rom) (mkst regs' (0x13b08 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x107ea /\ getr regs' 11 = Z_to_bv 64 0x106ae /\ getr regs' 12 = Z_to_bv 64 nb /\ getr regs' 1 = Z_to_bv 64 0x15820
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m nb Hnb H12 H13 H11 Rg Rs. eexists. split.
    - stepb_ft F_156f0 D_156f0 ltac:(condZ).
      sn F_156f4 D_156f4.
      stepLD F_156f8 D_156f8 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_156fc D_156fc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15700 D_15700. stepb_ft F_15704 D_15704 ltac:(condZ).
      sn F_15708 D_15708. sn F_1570c D_1570c. sn F_15710 D_15710. sn F_15714 D_15714. sn F_15718 D_15718. sn F_1571c D_1571c.
      sn F_15720 D_15720. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mod4_plus : forall p k, (p mod 4 = 0)%Z -> (k mod 4 = 0)%Z -> ((p + k) mod 4 = 0)%Z.
  Proof.
    intros p k Hp Hk.
    apply Z.mod_divide in Hp; [|lia]. apply Z.mod_divide in Hk; [|lia]. destruct Hp as [a Ha]. destruct Hk as [b Hb].
    subst. replace (a * 4 + b * 4)%Z with ((a + b) * 4)%Z by lia. apply Z_mod_mult.
  Qed.
  Ltac guard4 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).

  (* [comment removed for export] *)
  Lemma pd_B : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (dp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    u b0 = 115%Z -> u b1 = 112%Z -> u b2 = 105%Z -> u b3 = 120%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x1584c : word) m rom) (mkst regs' (0x158e4 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (dp + 20) /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof.
    intros regs m dp b0 b1 b2 b3 Hdp Hdp4 AL4 R0 R1 R2 R3 E0 E1 E2 E3 H10.
    assert (EQ4 : ((dp + 4) mod 4 = 0)%Z) by (apply mod4_plus; [exact AL4 | reflexivity]).
    assert (EQ8 : ((dp + 8) mod 4 = 0)%Z) by (apply mod4_plus; [exact AL4 | reflexivity]).
    assert (EQ12 : ((dp + 12) mod 4 = 0)%Z) by (apply mod4_plus; [exact AL4 | reflexivity]).
    assert (EQ20 : ((dp + 20) mod 4 = 0)%Z) by (apply mod4_plus; [exact AL4 | reflexivity]).
    eexists. split.
    - stepLBU F_15750 D_15750 b0 ltac:(addr_norm; exact R0). rewrite E0.
      sn F_15754 D_15754. stepb_ft F_15758 D_15758 ltac:(condZ).
      sn F_1575c D_1575c. stepb_ft F_15760 D_15760 ltac:(condZ).
      stepLBU F_15764 D_15764 b1 ltac:(addr_norm; exact R1). rewrite E1.
      sn F_15768 D_15768. stepb_ft F_1576c D_1576c ltac:(condZ).
      sn F_15770 D_15770. stepb_ft F_15774 D_15774 ltac:(condZ).
      stepLBU F_15778 D_15778 b2 ltac:(addr_norm; exact R2). rewrite E2.
      sn F_1577c D_1577c. stepb_ft F_15780 D_15780 ltac:(condZ).
      sn F_15784 D_15784. stepb_ft F_15788 D_15788 ltac:(condZ).
      stepLBU F_1578c D_1578c b3 ltac:(addr_norm; exact R3). rewrite E3.
      sn F_15790 D_15790. stepb_ft F_15794 D_15794 ltac:(condZ).
      sn F_15798 D_15798. stepb_ft F_1579c D_1579c ltac:(condZ).
      zv F_157a0 D_157a0 (Z_to_bv 64 (dp + 4)). guard4 F_157a4 D_157a4 EQ4. stepb_ft F_157a8 D_157a8 ltac:(condZ).
      sn F_157ac D_157ac. stepb_ft F_157b0 D_157b0 ltac:(condZ).
      zv F_157b4 D_157b4 (Z_to_bv 64 (dp + 8)). guard4 F_157b8 D_157b8 EQ8. stepb_ft F_157bc D_157bc ltac:(condZ).
      sn F_157c0 D_157c0. stepb_ft F_157c4 D_157c4 ltac:(condZ).
      zv F_157c8 D_157c8 (Z_to_bv 64 (dp + 12)). guard4 F_157cc D_157cc EQ12. stepb_ft F_157d0 D_157d0 ltac:(condZ).
      sn F_157d4 D_157d4. stepb_ft F_157d8 D_157d8 ltac:(condZ).
      zv F_157dc D_157dc (Z_to_bv 64 (dp + 20)). guard4 F_157e0 D_157e0 EQ20. stepb_ft F_157e4 D_157e4 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Bbad : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    ~ (u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x1584c : word) m rom) (mkst regs' (0x15920 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof.
    intros regs m dp b0 b1 b2 b3 Hdp Hdp4 R0 R1 R2 R3 NE H10.
    pose proof (u8_range b0). pose proof (u8_range b1). pose proof (u8_range b2). pose proof (u8_range b3).
    destruct (Z.eq_dec (u b0) 115) as [E0|E0].
    2: { clear NE. eexists. split.
         { stepLBU F_15750 D_15750 b0 ltac:(addr_norm; exact R0). sn F_15754 D_15754. stepb_tk F_15758 D_15758 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    destruct (Z.eq_dec (u b1) 112) as [E1|E1].
    2: { clear NE. eexists. split.
         { stepLBU F_15750 D_15750 b0 ltac:(addr_norm; exact R0). sn F_15754 D_15754. stepb_ft F_15758 D_15758 ltac:(condZ).
           sn F_1575c D_1575c. stepb_ft F_15760 D_15760 ltac:(condZ).
           stepLBU F_15764 D_15764 b1 ltac:(addr_norm; exact R1). sn F_15768 D_15768. stepb_tk F_1576c D_1576c ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    destruct (Z.eq_dec (u b2) 105) as [E2|E2].
    2: { clear NE. eexists. split.
         { stepLBU F_15750 D_15750 b0 ltac:(addr_norm; exact R0). sn F_15754 D_15754. stepb_ft F_15758 D_15758 ltac:(condZ).
           sn F_1575c D_1575c. stepb_ft F_15760 D_15760 ltac:(condZ).
           stepLBU F_15764 D_15764 b1 ltac:(addr_norm; exact R1). sn F_15768 D_15768. stepb_ft F_1576c D_1576c ltac:(condZ).
           sn F_15770 D_15770. stepb_ft F_15774 D_15774 ltac:(condZ).
           stepLBU F_15778 D_15778 b2 ltac:(addr_norm; exact R2). sn F_1577c D_1577c. stepb_tk F_15780 D_15780 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    assert (E3 : u b3 <> 120%Z) by (intros E3; apply NE; lia). clear NE.
    eexists. split.
    { stepLBU F_15750 D_15750 b0 ltac:(addr_norm; exact R0). sn F_15754 D_15754. stepb_ft F_15758 D_15758 ltac:(condZ).
      sn F_1575c D_1575c. stepb_ft F_15760 D_15760 ltac:(condZ).
      stepLBU F_15764 D_15764 b1 ltac:(addr_norm; exact R1). sn F_15768 D_15768. stepb_ft F_1576c D_1576c ltac:(condZ).
      sn F_15770 D_15770. stepb_ft F_15774 D_15774 ltac:(condZ).
      stepLBU F_15778 D_15778 b2 ltac:(addr_norm; exact R2). sn F_1577c D_1577c. stepb_ft F_15780 D_15780 ltac:(condZ).
      sn F_15784 D_15784. stepb_ft F_15788 D_15788 ltac:(condZ).
      stepLBU F_1578c D_1578c b3 ltac:(addr_norm; exact R3). sn F_15790 D_15790. stepb_tk F_15794 D_15794 ltac:(condZ).
      apply mst_refl. }
    solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pd_C : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x158e4 : word) m rom) (mkst regs' (0x15974 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 wr /\ getr regs' 13 = Z_to_bv 64 18446744073708551615
      /\ regs_agree (fun r => In r [9; 13; 14]%list) regs regs'.
  Proof.
    intros regs m dp wr bs4 Hdp Hdphi R4 W4 Hwr H10. eexists. split.
    - stepLD F_157e8 D_157e8 bs4 (Z_to_bv 64 wr) ltac:(addr_norm; exact R4) ltac:(rewrite u_Z2bv by lia; exact W4).
      rewrite (v_lw_small wr) by lia.
      sn F_157ec D_157ec. sn F_157f0 D_157f0.
      sn F_157f4 D_157f4. fixv (Z_to_bv 64 (sw32 (sw32 wr + 18446744073708551615))) ltac:(rewrite v_addw_Z, (sw32_small wr) by lia; reflexivity).
      stepb_tk F_157f8 D_157f8 ltac:(pin; rewrite c_ltu_zx; apply wchk_ok; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Cbad : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (0 <= wr < 2 ^ 32)%Z -> ~ (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x158e4 : word) m rom) (mkst regs' (0x158f8 : word) m rom)
      /\ regs_agree (fun r => In r [9; 13; 14]%list) regs regs'.
  Proof.
    intros regs m dp wr bs4 Hdp Hdphi R4 W4 Hwr NW H10. eexists. split.
    - stepLD F_157e8 D_157e8 bs4 (Z_to_bv 64 wr) ltac:(addr_norm; exact R4) ltac:(rewrite u_Z2bv by lia; exact W4).
      rewrite (v_lw_Z wr).
      sn F_157ec D_157ec. sn F_157f0 D_157f0.
      sn F_157f4 D_157f4. fixv (Z_to_bv 64 (sw32 (sw32 wr + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      stepb_ft F_157f8 D_157f8 ltac:(pin; rewrite c_ltu_zx; apply wchk_bad; lia).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_D : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 13 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x15974 : word) m rom) (mkst regs' (0x159a8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 hr /\ regs_agree (fun r => In r [18; 14]%list) regs regs'.
  Proof.
    intros regs m dp hr bs8 Hdp Hdphi R8 W8 Hhr H10 H13. eexists. split.
    - stepLD F_15878 D_15878 bs8 (Z_to_bv 64 hr) ltac:(addr_norm; exact R8) ltac:(rewrite u_Z2bv by lia; exact W8).
      rewrite (v_lw_small hr) by lia.
      sn F_1587c D_1587c. fixv (Z_to_bv 64 (sw32 (sw32 hr + 18446744073708551615))) ltac:(rewrite v_addw_Z, (sw32_small hr) by lia; reflexivity).
      stepb_tk F_15880 D_15880 ltac:(pin; rewrite c_ltu_zx; apply wchk_ok; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Dbad : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (0 <= hr < 2 ^ 32)%Z -> ~ (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 13 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x15974 : word) m rom) (mkst regs' (0x15980 : word) m rom)
      /\ regs_agree (fun r => In r [18; 14]%list) regs regs'.
  Proof.
    intros regs m dp hr bs8 Hdp Hdphi R8 W8 Hhr NH H10 H13. eexists. split.
    - stepLD F_15878 D_15878 bs8 (Z_to_bv 64 hr) ltac:(addr_norm; exact R8) ltac:(rewrite u_Z2bv by lia; exact W8).
      rewrite (v_lw_Z hr).
      sn F_1587c D_1587c. fixv (Z_to_bv 64 (sw32 (sw32 hr + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      stepb_ft F_15880 D_15880 ltac:(pin; rewrite c_ltu_zx; apply wchk_bad; lia).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_E : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x159a8 : word) m rom) (mkst regs' (0x159e0 : word) m rom)
      /\ regs_agree (fun r => In r [13; 14]%list) regs regs'.
  Proof.
    intros regs m wr hr Hw Hh Hwh H9 H18. eexists. split.
    - zv F_158ac D_158ac (Z_to_bv 64 (hr * wr)). sn F_158b0 D_158b0. sn F_158b4 D_158b4.
      stepb_tk F_158b8 D_158b8 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  Lemma pd_Ebad : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (400000000 < wr * hr)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x159a8 : word) m rom) (mkst regs' (0x159b8 : word) m rom)
      /\ regs_agree (fun r => In r [13; 14]%list) regs regs'.
  Proof.
    intros regs m wr hr Hw Hh Hwh H9 H18. assert (hr * wr < 2 ^ 63)%Z by nia. eexists. split.
    - zv F_158ac D_158ac (Z_to_bv 64 (hr * wr)). sn F_158b0 D_158b0. sn F_158b4 D_158b4.
      stepb_ft F_158b8 D_158b8 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition et_leaves : list (Z * Z) :=
    [(0x15920, 0x1080d); (0x158f8, 0x10a78); (0x15980, 0x1037d); (0x159b8, 0x10333); (0x15af0, 0x108a1); (0x15b18, 0x10511)]%Z.
  Lemma pd_ET : forall pc msg regs m,
    In (pc, msg) et_leaves ->
    rdn SEGS m (Z_to_bv 64 0x1f9d0) 8 = Some (Z_to_le_bytes 8 0x20a40) -> rdn SEGS m (Z_to_bv 64 0x20a40) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x15944 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x106ae
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros pc msg regs m Hin Rg Rs. unfold et_leaves in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E; intros <- <-.
    - replace (Z_to_bv 64 0x15920) with (0x15920 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_15824 D_15824.
        stepLD F_15828 D_15828 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_1582c D_1582c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15830 D_15830. stepb_ft F_15834 D_15834 ltac:(condZ).
        sn F_15838 D_15838. sn F_1583c D_1583c. sn F_15840 D_15840. sn F_15844 D_15844.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x158f8) with (0x158f8 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_157fc D_157fc.
        stepLD F_15800 D_15800 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15804 D_15804 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15808 D_15808. stepb_ft F_1580c D_1580c ltac:(condZ).
        sn F_15810 D_15810. sn F_15814 D_15814. sn F_15818 D_15818. sn F_1581c D_1581c.
        sn F_15820 D_15820.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15980) with (0x15980 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_15884 D_15884.
        stepLD F_15888 D_15888 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_1588c D_1588c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15890 D_15890. stepb_ft F_15894 D_15894 ltac:(condZ).
        sn F_15898 D_15898. sn F_1589c D_1589c. sn F_158a0 D_158a0. sn F_158a4 D_158a4.
        sn F_158a8 D_158a8.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x159b8) with (0x159b8 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_158bc D_158bc.
        stepLD F_158c0 D_158c0 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_158c4 D_158c4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_158c8 D_158c8. stepb_ft F_158cc D_158cc ltac:(condZ).
        sn F_158d0 D_158d0. sn F_158d4 D_158d4. sn F_158d8 D_158d8. sn F_158dc D_158dc.
        sn F_158e0 D_158e0.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15af0) with (0x15af0 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_159f4 D_159f4.
        stepLD F_159f8 D_159f8 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_159fc D_159fc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15a00 D_15a00. stepb_ft F_15a04 D_15a04 ltac:(condZ).
        sn F_15a08 D_15a08. sn F_15a0c D_15a0c. sn F_15a10 D_15a10. sn F_15a14 D_15a14.
        sn F_15a18 D_15a18.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15b18) with (0x15b18 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_15a1c D_15a1c.
        stepLD F_15a20 D_15a20 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15a24 D_15a24 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15a28 D_15a28. stepb_ft F_15a2c D_15a2c ltac:(condZ).
        sn F_15a30 D_15a30. sn F_15a34 D_15a34. sn F_15a38 D_15a38. sn F_15a3c D_15a3c.
        sn F_15a40 D_15a40.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition ej_leaves : list (Z * Z) := [(0x15b78, 0x10915); (0x15bb0, 0x10bcd); (0x15c3c, 0x10430)]%Z.
  Lemma pd_EJ : forall pc msg regs m,
    In (pc, msg) ej_leaves ->
    rdn SEGS m (Z_to_bv 64 0x1f9d0) 8 = Some (Z_to_le_bytes 8 0x20a40) -> rdn SEGS m (Z_to_bv 64 0x20a40) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x13ba4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x106ae /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x15c68
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros pc msg regs m Hin Rg Rs. unfold ej_leaves in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
    - replace (Z_to_bv 64 0x15b78) with (0x15b78 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_15a7c D_15a7c.
        stepLD F_15a80 D_15a80 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15a84 D_15a84 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15a88 D_15a88. stepb_ft F_15a8c D_15a8c ltac:(condZ).
        sn F_15a90 D_15a90. sn F_15a94 D_15a94. sn F_15a98 D_15a98. sn F_15a9c D_15a9c.
        sn F_15aa0 D_15aa0.
        sn F_15b64 D_15b64. sn F_15b68 D_15b68.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15bb0) with (0x15bb0 : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_15ab4 D_15ab4.
        stepLD F_15ab8 D_15ab8 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15abc D_15abc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15ac0 D_15ac0. stepb_ft F_15ac4 D_15ac4 ltac:(condZ).
        sn F_15ac8 D_15ac8. sn F_15acc D_15acc. sn F_15ad0 D_15ad0. sn F_15ad4 D_15ad4.
        sn F_15ad8 D_15ad8.
        sn F_15b64 D_15b64. sn F_15b68 D_15b68.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x15c3c) with (0x15c3c : word) by (apply bv_eq; reflexivity). eexists. split.
      { sn F_15b40 D_15b40.
        stepLD F_15b44 D_15b44 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15b48 D_15b48 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15b4c D_15b4c. stepb_ft F_15b50 D_15b50 ltac:(condZ).
        sn F_15b54 D_15b54. sn F_15b58 D_15b58. sn F_15b5c D_15b5c. sn F_15b60 D_15b60.
        sn F_15b64 D_15b64. sn F_15b68 D_15b68.
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
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (sv 23%nat)).

  (* [comment removed for export] *)
  Lemma pd_X50 : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x15944 : word) m rom) (mkst regs' (0x13ba4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros regs m s ret sv Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) H2. eexists. split.
    - sn F_15848 D_15848.
      stepLD8 F_1584c D_1584c ret. stepLD8 F_15850 D_15850 (sv 8%nat). stepLD8 F_15854 D_15854 (sv 9%nat).
      stepLD8 F_15858 D_15858 (sv 18%nat). stepLD8 F_1585c D_1585c (sv 19%nat). stepLD8 F_15860 D_15860 (sv 20%nat).
      stepLD8 F_15864 D_15864 (sv 21%nat). stepLD8 F_15868 D_15868 (sv 22%nat). stepLD8 F_1586c D_1586c (sv 23%nat).
      zv F_15870 D_15870 (Z_to_bv 64 s). sn F_15874 D_15874. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x15c70 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros regs m s ret sv Hs Hs64 Hret (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) H2. eexists. split.
    - stepLD8 F_15b74 D_15b74 ret. stepLD8 F_15b78 D_15b78 (sv 8%nat). stepLD8 F_15b7c D_15b7c (sv 9%nat).
      stepLD8 F_15b80 D_15b80 (sv 18%nat). stepLD8 F_15b84 D_15b84 (sv 19%nat). stepLD8 F_15b88 D_15b88 (sv 20%nat).
      stepLD8 F_15b8c D_15b8c (sv 21%nat). stepLD8 F_15b90 D_15b90 (sv 22%nat). stepLD8 F_15b94 D_15b94 (sv 23%nat).
      zv F_15b98 D_15b98 (Z_to_bv 64 s). stepret F_15b9c D_15b9c ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_R0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x15c6c : word) m rom) (mkst regs' (0x15c70 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_15b70 D_15b70; apply mst_refl|]. split; [gres; reflexivity | solve_regs_agree]. Qed.

  Lemma pd_J34 : forall regs m, exists regs', msteps SEGS (mkst regs (0x15820 : word) m rom) (mkst regs' (0x15c6c : word) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_15724 D_15724; apply mst_refl | solve_regs_agree]. Qed.
  Lemma pd_J88 : forall regs m, exists regs', msteps SEGS (mkst regs (0x15b74 : word) m rom) (mkst regs' (0x15c6c : word) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_15a78 D_15a78; apply mst_refl | solve_regs_agree]. Qed.
  Lemma pd_J7c : forall regs m, exists regs', msteps SEGS (mkst regs (0x15c68 : word) m rom) (mkst regs' (0x15c70 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_15b6c D_15b6c; apply mst_refl | solve_regs_agree]. Qed.
  Ltac rdn_out R := rewrite rdn_wbytes_out_Z; [exact R | rewrite ?length_N_to_le_bytes; lia].
End Segs.
End DeserA.
