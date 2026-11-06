(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocKitOL RelocTacOL CanonImgOL RCodeOL_23720_24000 RCodeOL_24000_24fe0.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.OL Require Import LeptStderr LeptBase LeptErr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zval ::= rl_zval.      (* [comment removed for export] *)
#[local] Ltac condZ ::= rl_condZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section DeserA.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeOL RLOC} {RSITESF : RelocSitesOL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgOL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvOL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {PG : PinsG}.
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
      msteps SEGS (mkst regs (rl dOL_24b94 0x24b94) m rom) (mkst regs' (rl dOL_24b94 0x24bd4) (FR12 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 nb
      /\ getr regs' 12 = Z_to_bv 64 18446744071562067995 /\ getr regs' 13 = Z_to_bv 64 (nb + 18446744071562067968)
      /\ regs_agree (fun r => In r [2; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s dp nb ret Hs Hs64 Hdp Hnb SOK H2 H1 H10 H11.
    unfold FR12. eexists. split.
    - zv F_24b94 D_24b94 (Z_to_bv 64 (s - 112)).
      stepST F_24b98 D_24b98 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_24b9c D_24b9c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_24ba0 D_24ba0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_24ba4 D_24ba4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_24ba8 D_24ba8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_24bac D_24bac (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_24bb0 D_24bb0 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_24bb4 D_24bb4 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_24bb8 D_24bb8 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_24bbc D_24bbc (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_24bc0 D_24bc0 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepb_ft F_24bc4 D_24bc4 ltac:(condZ).
      sn F_24bc8 D_24bc8.
      zv F_24bcc D_24bcc (Z_to_bv 64 (nb + 18446744071562067968)).
      sn F_24bd0 D_24bd0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A1 : forall regs m (nb : Z),
    (28 <= nb < 2 ^ 31)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24bd4) m rom) (mkst regs' (rl dOL_24b94 0x24c34) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m nb Hnb H12 H13. eexists. split.
    - stepb_tk F_24bd4 D_24bd4 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A2 : forall regs m (nb : Z),
    (0 <= nb < 28)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    getr regs 11 = Z_to_bv 64 nb ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_24b94 0x24bd4) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dOLS_106fa 0x106fa /\ getr regs' 11 = rl dOLS_105cb 0x105cb /\ getr regs' 12 = Z_to_bv 64 nb /\ getr regs' 1 = rl dOL_24b94 0x24c08
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dOL_24b94 :: nil).
    intros regs m nb Hnb H12 H13 H11 Rg Rs. eexists. split.
    - stepb_ft F_24bd4 D_24bd4 ltac:(condZ).
      sn F_24bd8 D_24bd8.
      stepLD F_24bdc D_24bdc (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_24be0 D_24be0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_24be4 D_24be4. stepb_ft F_24be8 D_24be8 ltac:(condZ).
      sn F_24bec D_24bec. sn F_24bf0 D_24bf0. sn F_24bf4 D_24bf4. sn F_24bf8 D_24bf8. sn F_24bfc D_24bfc. sn F_24c00 D_24c00.
      sn F_24c04 D_24c04. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_B : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    u b0 = 115%Z -> u b1 = 112%Z -> u b2 = 105%Z -> u b3 = 120%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24c34) m rom) (mkst regs' (rl dOL_24b94 0x24c64) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m dp b0 b1 b2 b3 Hdp Hdp4 R0 R1 R2 R3 E0 E1 E2 E3 H10. eexists. split.
    - stepLBU F_24c34 D_24c34 b0 ltac:(addr_norm; exact R0). rewrite E0.
      sn F_24c38 D_24c38. stepb_ft F_24c3c D_24c3c ltac:(condZ).
      stepLBU F_24c40 D_24c40 b1 ltac:(addr_norm; exact R1). rewrite E1.
      sn F_24c44 D_24c44. stepb_ft F_24c48 D_24c48 ltac:(condZ).
      stepLBU F_24c4c D_24c4c b2 ltac:(addr_norm; exact R2). rewrite E2.
      sn F_24c50 D_24c50. stepb_ft F_24c54 D_24c54 ltac:(condZ).
      stepLBU F_24c58 D_24c58 b3 ltac:(addr_norm; exact R3). rewrite E3.
      sn F_24c5c D_24c5c. stepb_ft F_24c60 D_24c60 ltac:(condZ).
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
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24c34) m rom) (mkst regs' (rl dOL_24b94 0x24ca0) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m dp b0 b1 b2 b3 Hdp Hdp4 R0 R1 R2 R3 NE H10.
    pose proof (u8_range b0). pose proof (u8_range b1). pose proof (u8_range b2). pose proof (u8_range b3).
    destruct (Z.eq_dec (u b0) 115) as [E0|E0].
    2: { clear NE. eexists. split.
         { stepLBU F_24c34 D_24c34 b0 ltac:(addr_norm; exact R0). sn F_24c38 D_24c38. stepb_tk F_24c3c D_24c3c ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    destruct (Z.eq_dec (u b1) 112) as [E1|E1].
    2: { clear NE. eexists. split.
         { stepLBU F_24c34 D_24c34 b0 ltac:(addr_norm; exact R0). sn F_24c38 D_24c38. stepb_ft F_24c3c D_24c3c ltac:(condZ).
           stepLBU F_24c40 D_24c40 b1 ltac:(addr_norm; exact R1). sn F_24c44 D_24c44. stepb_tk F_24c48 D_24c48 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    destruct (Z.eq_dec (u b2) 105) as [E2|E2].
    2: { clear NE. eexists. split.
         { stepLBU F_24c34 D_24c34 b0 ltac:(addr_norm; exact R0). sn F_24c38 D_24c38. stepb_ft F_24c3c D_24c3c ltac:(condZ).
           stepLBU F_24c40 D_24c40 b1 ltac:(addr_norm; exact R1). sn F_24c44 D_24c44. stepb_ft F_24c48 D_24c48 ltac:(condZ).
           stepLBU F_24c4c D_24c4c b2 ltac:(addr_norm; exact R2). sn F_24c50 D_24c50. stepb_tk F_24c54 D_24c54 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    assert (E3 : u b3 <> 120%Z) by (intros E3; apply NE; lia). clear NE.
    eexists. split.
    { stepLBU F_24c34 D_24c34 b0 ltac:(addr_norm; exact R0). sn F_24c38 D_24c38. stepb_ft F_24c3c D_24c3c ltac:(condZ).
      stepLBU F_24c40 D_24c40 b1 ltac:(addr_norm; exact R1). sn F_24c44 D_24c44. stepb_ft F_24c48 D_24c48 ltac:(condZ).
      stepLBU F_24c4c D_24c4c b2 ltac:(addr_norm; exact R2). sn F_24c50 D_24c50. stepb_ft F_24c54 D_24c54 ltac:(condZ).
      stepLBU F_24c58 D_24c58 b3 ltac:(addr_norm; exact R3). sn F_24c5c D_24c5c. stepb_tk F_24c60 D_24c60 ltac:(condZ).
      apply mst_refl. }
    solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pd_C : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24c64) m rom) (mkst regs' (rl dOL_24b94 0x24cfc) m rom)
      /\ getr regs' 9 = Z_to_bv 64 wr /\ getr regs' 12 = Z_to_bv 64 18446744073708551615
      /\ regs_agree (fun r => In r [9; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m dp wr bs4 Hdp Hdphi R4 W4 Hwr H10. eexists. split.
    - stepLD F_24c64 D_24c64 bs4 (Z_to_bv 64 wr) ltac:(addr_norm; exact R4) ltac:(rewrite u_Z2bv by lia; exact W4).
      rewrite (v_lw_small wr) by lia.
      sn F_24c68 D_24c68. sn F_24c6c D_24c6c.
      sn F_24c70 D_24c70. fixv (Z_to_bv 64 (sw32 (sw32 wr + 18446744073708551615))) ltac:(rewrite v_addw_Z, (sw32_small wr) by lia; reflexivity).
      stepb_tk F_24c74 D_24c74 ltac:(pin; rewrite c_ltu_zx; apply wchk_ok; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Cbad : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (0 <= wr < 2 ^ 32)%Z -> ~ (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24c64) m rom) (mkst regs' (rl dOL_24b94 0x24c78) m rom)
      /\ regs_agree (fun r => In r [9; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m dp wr bs4 Hdp Hdphi R4 W4 Hwr NW H10. eexists. split.
    - stepLD F_24c64 D_24c64 bs4 (Z_to_bv 64 wr) ltac:(addr_norm; exact R4) ltac:(rewrite u_Z2bv by lia; exact W4).
      rewrite (v_lw_Z wr).
      sn F_24c68 D_24c68. sn F_24c6c D_24c6c.
      sn F_24c70 D_24c70. fixv (Z_to_bv 64 (sw32 (sw32 wr + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      stepb_ft F_24c74 D_24c74 ltac:(pin; rewrite c_ltu_zx; apply wchk_bad; lia).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_D : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 12 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24cfc) m rom) (mkst regs' (rl dOL_24b94 0x24d30) m rom)
      /\ getr regs' 18 = Z_to_bv 64 hr /\ regs_agree (fun r => In r [18; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m dp hr bs8 Hdp Hdphi R8 W8 Hhr H10 H12. eexists. split.
    - stepLD F_24cfc D_24cfc bs8 (Z_to_bv 64 hr) ltac:(addr_norm; exact R8) ltac:(rewrite u_Z2bv by lia; exact W8).
      rewrite (v_lw_small hr) by lia.
      sn F_24d00 D_24d00. fixv (Z_to_bv 64 (sw32 (sw32 hr + 18446744073708551615))) ltac:(rewrite v_addw_Z, (sw32_small hr) by lia; reflexivity).
      stepb_tk F_24d04 D_24d04 ltac:(pin; rewrite c_ltu_zx; apply wchk_ok; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Dbad : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (0 <= hr < 2 ^ 32)%Z -> ~ (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 12 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24cfc) m rom) (mkst regs' (rl dOL_24b94 0x24d08) m rom)
      /\ regs_agree (fun r => In r [18; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m dp hr bs8 Hdp Hdphi R8 W8 Hhr NH H10 H12. eexists. split.
    - stepLD F_24cfc D_24cfc bs8 (Z_to_bv 64 hr) ltac:(addr_norm; exact R8) ltac:(rewrite u_Z2bv by lia; exact W8).
      rewrite (v_lw_Z hr).
      sn F_24d00 D_24d00. fixv (Z_to_bv 64 (sw32 (sw32 hr + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      stepb_ft F_24d04 D_24d04 ltac:(pin; rewrite c_ltu_zx; apply wchk_bad; lia).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_E : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24d30) m rom) (mkst regs' (rl dOL_24b94 0x24d68) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m wr hr Hw Hh Hwh H9 H18. eexists. split.
    - zv F_24d30 D_24d30 (Z_to_bv 64 (hr * wr)). sn F_24d34 D_24d34. sn F_24d38 D_24d38.
      stepb_tk F_24d3c D_24d3c ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  Lemma pd_Ebad : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (400000000 < wr * hr)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24d30) m rom) (mkst regs' (rl dOL_24b94 0x24d40) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m wr hr Hw Hh Hwh H9 H18. assert (hr * wr < 2 ^ 63)%Z by nia. eexists. split.
    - zv F_24d30 D_24d30 (Z_to_bv 64 (hr * wr)). sn F_24d34 D_24d34. sn F_24d38 D_24d38.
      stepb_ft F_24d3c D_24d3c ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_F : forall regs m (dp nb ncr q dr wr hr : Z) bs20 bs12,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr <= 256)%Z -> (ncr + 7 < q)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 12)) 4 = Some bs12 -> bytes_le_to_Z bs12 = dr -> (0 <= dr < 2 ^ 32)%Z ->
    (0 <= wr < 2 ^ 64)%Z -> (0 <= hr < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24d68) m rom) (mkst regs' (rl dOL_238e8 0x238e8) m rom)
      /\ getr regs' 23 = Z_to_bv 64 ncr /\ getr regs' 8 = Z_to_bv 64 nb /\ getr regs' 25 = Z_to_bv 64 dp
      /\ getr regs' 20 = Z_to_bv 64 (zx (sw32 dr))
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 (zx (sw32 dr)) /\ getr regs' 1 = rl dOL_24b94 0x24d9c
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 20; 23; 25]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m dp nb ncr q dr wr hr bs20 bs12 Hdp Hdphi Hnb Hq R20 W20 Hncr Hq7 R12 W12 Hdr Hwr Hhr H10 H11 H9 H18.
    assert (Hq4 : (0 <= q < 2 ^ 29)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    eexists. split.
    - stepLD F_24d68 D_24d68 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
      sn F_24d6c D_24d6c. stepb_ft F_24d70 D_24d70 ltac:(condZ).
      zv F_24d74 D_24d74 (Z_to_bv 64 (ncr + 7)).
      stepiv F_24d78 D_24d78 (Z_to_bv 64 q) ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; subst q; reflexivity).
      stepb_ft F_24d7c D_24d7c ltac:(condZ).
      sn F_24d80 D_24d80. sn F_24d84 D_24d84.
      stepLD F_24d88 D_24d88 bs12 (Z_to_bv 64 dr) ltac:(addr_norm; exact R12) ltac:(rewrite u_Z2bv by lia; exact W12).
      rewrite (v_lw_Z dr), <- (zbv_zx (sw32 dr)).
      sn F_24d8c D_24d8c. sn F_24d90 D_24d90. sn F_24d94 D_24d94. sn F_24d98 D_24d98.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Fbad : forall regs m (dp nb ncr q : Z) bs20,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr < 2 ^ 32)%Z -> ~ (ncr <= 256 /\ ncr + 7 < q)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24d68) m rom) (mkst regs' (rl dOL_24b94 0x24e50) m rom)
      /\ regs_agree (fun r => In r [12; 13; 23]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m dp nb ncr q bs20 Hdp Hdphi Hnb Hq R20 W20 Hncr NC H10 H11.
    assert (Hq4 : (0 <= q < 2 ^ 29)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct (Z_lt_ge_dec 256 ncr) as [BIG|OK].
    - clear NC. eexists. split.
      { stepLD F_24d68 D_24d68 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
        sn F_24d6c D_24d6c. stepb_tk F_24d70 D_24d70 ltac:(condZ). apply mst_refl. }
      solve_regs_agree.
    - assert (NQ : (q <= ncr + 7)%Z) by lia. clear NC. eexists. split.
      { stepLD F_24d68 D_24d68 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
        sn F_24d6c D_24d6c. stepb_ft F_24d70 D_24d70 ltac:(condZ).
        zv F_24d74 D_24d74 (Z_to_bv 64 (ncr + 7)).
        stepiv F_24d78 D_24d78 (Z_to_bv 64 q) ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; subst q; reflexivity).
        stepb_tk F_24d7c D_24d7c ltac:(condZ). apply mst_refl. }
      solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Definition et_leaves : list (Z * Z) :=
    [((0x24ca0 + dOL_24b94), (0x1071d + dOLS_1071d)); ((0x24c78 + dOL_24b94), (0x10935 + dOLS_10935)); ((0x24d08 + dOL_24b94), (0x10340 + dOLS_10340)); ((0x24d40 + dOL_24b94), (0x10316 + dOLS_10316)); ((0x24e50 + dOL_24b94), (0x10764 + dOLS_10764)); ((0x24e78 + dOL_24b94), (0x1047c + dOLS_1047c))]%Z.
  Lemma pd_ET : forall pc msg regs m,
    In (pc, msg) et_leaves ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (rl dOL_24b94 0x24cc4) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = rl dOLS_105cb 0x105cb
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dOL_24b94 :: nil).
    intros pc msg regs m Hin Rg Rs. unfold et_leaves in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E; intros <- <-.
    - eexists. split.
      { sn F_24ca0 D_24ca0.
        stepLD F_24ca4 D_24ca4 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24ca8 D_24ca8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24cac D_24cac. stepb_ft F_24cb0 D_24cb0 ltac:(condZ).
        sn F_24cb4 D_24cb4. sn F_24cb8 D_24cb8. sn F_24cbc D_24cbc. sn F_24cc0 D_24cc0.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_24c78 D_24c78.
        stepLD F_24c7c D_24c7c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24c80 D_24c80 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24c84 D_24c84. stepb_ft F_24c88 D_24c88 ltac:(condZ).
        sn F_24c8c D_24c8c. sn F_24c90 D_24c90. sn F_24c94 D_24c94. sn F_24c98 D_24c98.
        sn F_24c9c D_24c9c.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_24d08 D_24d08.
        stepLD F_24d0c D_24d0c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24d10 D_24d10 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24d14 D_24d14. stepb_ft F_24d18 D_24d18 ltac:(condZ).
        sn F_24d1c D_24d1c. sn F_24d20 D_24d20. sn F_24d24 D_24d24. sn F_24d28 D_24d28.
        sn F_24d2c D_24d2c.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_24d40 D_24d40.
        stepLD F_24d44 D_24d44 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24d48 D_24d48 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24d4c D_24d4c. stepb_ft F_24d50 D_24d50 ltac:(condZ).
        sn F_24d54 D_24d54. sn F_24d58 D_24d58. sn F_24d5c D_24d5c. sn F_24d60 D_24d60.
        sn F_24d64 D_24d64.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_24e50 D_24e50.
        stepLD F_24e54 D_24e54 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24e58 D_24e58 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24e5c D_24e5c. stepb_ft F_24e60 D_24e60 ltac:(condZ).
        sn F_24e64 D_24e64. sn F_24e68 D_24e68. sn F_24e6c D_24e6c. sn F_24e70 D_24e70.
        sn F_24e74 D_24e74.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_24e78 D_24e78.
        stepLD F_24e7c D_24e7c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24e80 D_24e80 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24e84 D_24e84. stepb_ft F_24e88 D_24e88 ltac:(condZ).
        sn F_24e8c D_24e8c. sn F_24e90 D_24e90. sn F_24e94 D_24e94. sn F_24e98 D_24e98.
        sn F_24e9c D_24e9c.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition ej_leaves : list (Z * Z) := [((0x24ed8 + dOL_24b94), (0x107cc + dOLS_107cc)); ((0x24f10 + dOL_24b94), (0x10a26 + dOLS_10a26)); ((0x24f78 + dOL_24b94), (0x103e3 + dOLS_103e3))]%Z.
  Lemma pd_EJ : forall pc msg regs m,
    In (pc, msg) ej_leaves ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (rl dF_13730 0x13730) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = rl dOLS_105cb 0x105cb /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = rl dOL_24b94 0x24fa4
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dOL_24b94 :: nil).
    intros pc msg regs m Hin Rg Rs. unfold ej_leaves in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
    - eexists. split.
      { sn F_24ed8 D_24ed8.
        stepLD F_24edc D_24edc (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24ee0 D_24ee0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24ee4 D_24ee4. stepb_ft F_24ee8 D_24ee8 ltac:(condZ).
        sn F_24eec D_24eec. sn F_24ef0 D_24ef0. sn F_24ef4 D_24ef4. sn F_24ef8 D_24ef8.
        sn F_24efc D_24efc.
        sn F_24f9c D_24f9c. sn F_24fa0 D_24fa0.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_24f10 D_24f10.
        stepLD F_24f14 D_24f14 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24f18 D_24f18 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24f1c D_24f1c. stepb_ft F_24f20 D_24f20 ltac:(condZ).
        sn F_24f24 D_24f24. sn F_24f28 D_24f28. sn F_24f2c D_24f2c. sn F_24f30 D_24f30.
        sn F_24f34 D_24f34.
        sn F_24f9c D_24f9c. sn F_24fa0 D_24fa0.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_24f78 D_24f78.
        stepLD F_24f7c D_24f7c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24f80 D_24f80 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24f84 D_24f84. stepb_ft F_24f88 D_24f88 ltac:(condZ).
        sn F_24f8c D_24f8c. sn F_24f90 D_24f90. sn F_24f94 D_24f94. sn F_24f98 D_24f98.
        sn F_24f9c D_24f9c. sn F_24fa0 D_24fa0.
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
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24cc4) m rom) (mkst regs' (rl dF_13730 0x13730) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s ret sv Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) H2. eexists. split.
    - sn F_24cc4 D_24cc4.
      stepLD8 F_24cc8 D_24cc8 ret. stepLD8 F_24ccc D_24ccc (sv 8%nat). stepLD8 F_24cd0 D_24cd0 (sv 9%nat).
      stepLD8 F_24cd4 D_24cd4 (sv 18%nat). stepLD8 F_24cd8 D_24cd8 (sv 19%nat). stepLD8 F_24cdc D_24cdc (sv 20%nat).
      stepLD8 F_24ce0 D_24ce0 (sv 21%nat). stepLD8 F_24ce4 D_24ce4 (sv 22%nat). stepLD8 F_24ce8 D_24ce8 (sv 23%nat).
      stepLD8 F_24cec D_24cec (sv 24%nat). stepLD8 F_24cf0 D_24cf0 (sv 25%nat).
      zv F_24cf4 D_24cf4 (Z_to_bv 64 s). sn F_24cf8 D_24cf8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24fac) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s ret sv Hs Hs64 Hret (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) H2. eexists. split.
    - stepLD8 F_24fac D_24fac ret. stepLD8 F_24fb0 D_24fb0 (sv 8%nat). stepLD8 F_24fb4 D_24fb4 (sv 9%nat).
      stepLD8 F_24fb8 D_24fb8 (sv 18%nat). stepLD8 F_24fbc D_24fbc (sv 19%nat). stepLD8 F_24fc0 D_24fc0 (sv 20%nat).
      stepLD8 F_24fc4 D_24fc4 (sv 21%nat). stepLD8 F_24fc8 D_24fc8 (sv 22%nat). stepLD8 F_24fcc D_24fcc (sv 23%nat).
      stepLD8 F_24fd0 D_24fd0 (sv 24%nat). stepLD8 F_24fd4 D_24fd4 (sv 25%nat).
      zv F_24fd8 D_24fd8 (Z_to_bv 64 s). stepret F_24fdc D_24fdc ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_R0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24fa8) m rom) (mkst regs' (rl dOL_24b94 0x24fac) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil). intros regs m. eexists. split; [sn F_24fa8 D_24fa8; apply mst_refl|]. split; [gres; reflexivity | solve_regs_agree]. Qed.

  Lemma pd_J94 : forall regs m, exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24c08) m rom) (mkst regs' (rl dOL_24b94 0x24fa8) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil). intros regs m. eexists. split; [sn F_24c08 D_24c08; apply mst_refl | solve_regs_agree]. Qed.
  Lemma pd_J60 : forall regs m, exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24ed4) m rom) (mkst regs' (rl dOL_24b94 0x24fa8) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil). intros regs m. eexists. split; [sn F_24ed4 D_24ed4; apply mst_refl | solve_regs_agree]. Qed.
  Lemma pd_J30 : forall regs m, exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24fa4) m rom) (mkst regs' (rl dOL_24b94 0x24fac) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil). intros regs m. eexists. split; [sn F_24fa4 D_24fa4; apply mst_refl | solve_regs_agree]. Qed.
  Ltac rdn_out R := rewrite rdn_wbytes_out_Z; [exact R | rewrite ?length_N_to_le_bytes; lia].

  (* [comment removed for export] *)
  Lemma pd_G0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24d9c) m rom)
                              (mkst regs' (rl dOL_24b94 0x24e78) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_24d9c D_24d9c (Z_to_bv 64 (s - 104)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_24da0 D_24da0 ltac:(condZ). apply mst_refl.
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
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24d9c) m rom)
                              (mkst regs' (rl dOL_23c24 0x23c24) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 (s - 104) /\ getr regs' 1 = rl dOL_24b94 0x24dd4
      /\ getr regs' 19 = Z_to_bv 64 nc /\ getr regs' 24 = Z_to_bv 64 (dp + 4 * nc) /\ getr regs' 21 = Z_to_bv 64 (zx (sw32 ir))
      /\ getr regs' 8 = Z_to_bv 64 (4 * (wpl * hr)) /\ getr regs' 22 = Z_to_bv 64 (nb - 4 * nc - 28)
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 19; 21; 22; 24]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s dp nb nc pix1 wpl hr ir v1 bsi Hs Hs64 SOK PX Gp Hp1 Hwpl Hhr Hw0 Hsz Hnc Hnb Hnc4 Hdp Hdpnb Ri Wi Hir H2 H10 H23 H8 H25 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rw. rewrite Hwpl in Rw.
    pose proof (zx_range (sw32 ir)) as Hzi.
    assert (PX1 : PIXat (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) pix1 v1).
    { apply PIXat_out; [exact PX | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    eexists. split.
    - stepST F_24d9c D_24d9c (Z_to_bv 64 (s - 104)) (Z_to_bv 64 pix1) ltac:(sok_in SOK).
      stepb_ft F_24da0 D_24da0 ltac:(condZ).
      sn F_24da4 D_24da4. fixv (Z_to_bv 64 nc) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      sn F_24da8 D_24da8.
      stepb_ft F_23be4 D_23be4 ltac:(condZ).
      stepLD F_23be8 D_23be8 (Z_to_le_bytes 4 wpl) (Z_to_bv 64 wpl) ltac:(addr_norm; rewrite <- Hwpl; exact (PIX_rd_wpl SEGS _ _ _ PX1)) ltac:(apply lez4; lia).
      rewrite (v_lw_small wpl) by lia.
      stepretF F_23bec D_23bec F_24dac.
      stepiv F_24dac D_24dac (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      stepiv F_24db0 D_24db0 (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_24db4 D_24db4. fixv (Z_to_bv 64 (nb - 4 * nc)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      zv F_24db8 D_24db8 (Z_to_bv 64 (dp + 4 * nc)).
      stepLD F_24dbc D_24dbc bsi (Z_to_bv 64 ir) ltac:(rewrite zbv_addi; rdn_out Ri) ltac:(rewrite u_Z2bv by lia; exact Wi).
      rewrite (v_lw_Z ir), <- (zbv_zx (sw32 ir)).
      zv F_24dc0 D_24dc0 (Z_to_bv 64 (hr * wpl)).
      sn F_24dc4 D_24dc4. fixv (Z_to_bv 64 (4 * (wpl * hr))) ltac:(rewrite v_slliw_2, sw32_small by lia; f_equal; lia).
      sn F_24dc8 D_24dc8. fixv (Z_to_bv 64 (nb - 4 * nc - 28)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      zv F_24dcc D_24dcc (Z_to_bv 64 (s - 104)).
      sn F_24dd0 D_24dd0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_H : forall regs m (sz wr hr d : Z),
    (0 <= sz < 2 ^ 32)%Z ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 sz ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr -> getr regs 20 = Z_to_bv 64 d ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24dd4) m rom) (mkst regs' (rl dOL_23720 0x23720) m rom)
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 1 = rl dOL_24b94 0x24dec
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m sz wr hr d Hsz H8 H22 H21 H9 H18 H20. eexists. split.
    - stepb_ft F_24dd4 D_24dd4 ltac:(condZ). stepb_ft F_24dd8 D_24dd8 ltac:(condZ).
      sn F_24ddc D_24ddc. sn F_24de0 D_24de0. sn F_24de4 D_24de4. sn F_24de8 D_24de8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Hbad : forall regs m (sz msz isz : Z),
    (0 <= sz < 2 ^ 32)%Z -> (0 <= msz < 2 ^ 32)%Z -> (0 <= isz < 2 ^ 64)%Z -> (sz <> msz \/ sz <> isz) ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 msz -> getr regs 21 = Z_to_bv 64 isz ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24dd4) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dOLS_104e0 0x104e0 /\ getr regs' 11 = rl dOLS_105cb 0x105cb /\ getr regs' 1 = rl dOL_24b94 0x24ed4
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dOL_24b94 :: nil).
    intros regs m sz msz isz Hsz Hmsz Hisz NE Rg Rs H8 H22 H21.
    destruct (Z.eq_dec sz msz) as [E1|N1].
    - assert (N2 : sz <> isz) by lia. clear NE. eexists. split.
      { stepb_ft F_24dd4 D_24dd4 ltac:(condZ). stepb_tk F_24dd8 D_24dd8 ltac:(condZ).
        sn F_24ea0 D_24ea0.
        stepLD F_24ea4 D_24ea4 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24ea8 D_24ea8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24eac D_24eac. stepb_ft F_24eb0 D_24eb0 ltac:(condZ).
        sn F_24eb4 D_24eb4. sn F_24eb8 D_24eb8. sn F_24ebc D_24ebc. sn F_24ec0 D_24ec0.
        sn F_24ec4 D_24ec4. sn F_24ec8 D_24ec8. sn F_24ecc D_24ecc. sn F_24ed0 D_24ed0. apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - clear NE. eexists. split.
      { stepb_tk F_24dd4 D_24dd4 ltac:(condZ).
        sn F_24ea0 D_24ea0.
        stepLD F_24ea4 D_24ea4 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_24ea8 D_24ea8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_24eac D_24eac. stepb_ft F_24eb0 D_24eb0 ltac:(condZ).
        sn F_24eb4 D_24eb4. sn F_24eb8 D_24eb8. sn F_24ebc D_24ebc. sn F_24ec0 D_24ec0.
        sn F_24ec4 D_24ec4. sn F_24ec8 D_24ec8. sn F_24ecc D_24ecc. sn F_24ed0 D_24ed0. apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pd_I0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24dec) m rom)
                              (mkst regs' (rl dOL_24b94 0x24ed8) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_24dec D_24dec (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_24df0 D_24df0 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I1 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> (1 <= pixd < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24dec) m rom)
                              (mkst regs' (rl dOL_24b94 0x24f3c) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [9]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s pixd Hs Hs64 SOK Hp H2 H10 H23. eexists. split.
    - stepST F_24dec D_24dec (Z_to_bv 64 (s - 112)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepb_ft F_24df0 D_24df0 ltac:(condZ). stepb_tk F_24df4 D_24df4 ltac:(condZ).
      sn F_24f00 D_24f00. sn F_24f04 D_24f04. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I2 : forall regs m (s pixd dp nc : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z -> (0 <= dp < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 nc -> getr regs 25 = Z_to_bv 64 dp -> getr regs 19 = Z_to_bv 64 nc ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24dec) m rom)
                              (mkst regs' (rl dOL_24498 0x24498) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (dp + 24) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 nc /\ getr regs' 1 = rl dOL_24b94 0x24e08
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s pixd dp nc Hs Hs64 SOK Hp Hnc Hdp H2 H10 H23 H25 H19. eexists. split.
    - stepST F_24dec D_24dec (Z_to_bv 64 (s - 112)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepb_ft F_24df0 D_24df0 ltac:(condZ). stepb_ft F_24df4 D_24df4 ltac:(condZ).
      zv F_24df8 D_24df8 (Z_to_bv 64 (dp + 24)). sn F_24dfc D_24dfc. sn F_24e00 D_24e00. sn F_24e04 D_24e04. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_J0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24e08) m rom) (mkst regs' (rl dOL_23c24 0x23c24) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = rl dOL_24b94 0x24f10 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s Hs Hs64 H2 H10. eexists. split.
    - stepb_tk F_24e08 D_24e08 ltac:(condZ). zv F_24f08 D_24f08 (Z_to_bv 64 (s - 112)). sn F_24f0c D_24f0c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_J1 : forall regs m (s cm pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24e08) m rom) (mkst regs' (rl dOL_23d70 0x23d70) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 1 = rl dOL_24b94 0x24e1c
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s cm pixd Hs Hs64 Hcm Hp Rp H2 H10. eexists. split.
    - stepb_ft F_24e08 D_24e08 ltac:(condZ). sn F_24e0c D_24e0c.
      stepLD8 F_24e10 D_24e10 (Z_to_bv 64 pixd). sn F_24e14 D_24e14. sn F_24e18 D_24e18. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_K : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24e1c) m rom) (mkst regs' (rl dOL_24b94 0x24f3c) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s pixd Hs Hs64 Hp Rp H2 H10. eexists. split.
    - stepb_tk F_24e1c D_24e1c ltac:(condZ). stepLD8 F_24f38 D_24f38 (Z_to_bv 64 pixd). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_GD : forall regs m (pixd e8 sz : Z) (v : pixv),
    PIXat m pixd v -> (4096 <= pixd)%Z -> (0 <= e8)%Z -> (e8 + 28 < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 24 = Z_to_bv 64 e8 -> getr regs 8 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24f3c) m rom) (mkst regs' (rl dF_1c9b4 0x1c9b4) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (e8 + 28) /\ getr regs' 12 = Z_to_bv 64 sz /\ getr regs' 1 = rl dOL_24b94 0x24f4c
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m pixd e8 sz v PX Gp He8 He8' H10 H24 H8. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF).
    eexists. split.
    - sn F_24f3c D_24f3c. stepb_ft F_23ed4 D_23ed4 ltac:(condZ).
      stepLD F_23ed8 D_23ed8 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepretF F_23edc D_23edc F_24f40.
      zv F_24f40 D_24f40 (Z_to_bv 64 (e8 + 28)). sn F_24f44 D_24f44. sn F_24f48 D_24f48. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_L0 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24f4c) m rom) (mkst regs' (rl dOL_24b94 0x24fac) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s pixd Hs Hs64 Hp Rp H2 H23. eexists. split.
    - stepb_tk F_24f4c D_24f4c ltac:(condZ). stepLD8 F_24f68 D_24f68 (Z_to_bv 64 pixd). sn F_24f6c D_24f6c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_L1 : forall regs m (s pixd nc cm : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 23 = Z_to_bv 64 nc -> getr regs 9 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24f4c) m rom) (mkst regs' (rl dOL_24118 0x24118) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 (s - 92) /\ getr regs' 1 = rl dOL_24b94 0x24f60
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s pixd nc cm Hs Hs64 Hp Hnc Rp H2 H23 H9. eexists. split.
    - stepb_ft F_24f4c D_24f4c ltac:(condZ). stepLD8 F_24f50 D_24f50 (Z_to_bv 64 pixd).
      zv F_24f54 D_24f54 (Z_to_bv 64 (s - 92)). sn F_24f58 D_24f58. sn F_24f5c D_24f5c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_M1 : forall regs m (s pixd : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24f60) m rom) (mkst regs' (rl dOL_24b94 0x24fac) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s pixd Hs Hs64 Hp Rv Rp H2. eexists. split.
    - stepLD F_24f60 D_24f60 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_ft F_24f64 D_24f64 ltac:(condZ). stepLD8 F_24f68 D_24f68 (Z_to_bv 64 pixd). sn F_24f6c D_24f6c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_M0 : forall regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 0) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs', msteps SEGS (mkst regs (rl dOL_24b94 0x24f60) m rom) (mkst regs' (rl dOL_23c24 0x23c24) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = rl dOL_24b94 0x24f78 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof. rl_dbounds (dOL_24b94 :: nil).
    intros regs m s Hs Hs64 Rv H2. eexists. split.
    - stepLD F_24f60 D_24f60 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_tk F_24f64 D_24f64 ltac:(condZ). zv F_24f70 D_24f70 (Z_to_bv 64 (s - 112)). sn F_24f74 D_24f74. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End DeserA.
