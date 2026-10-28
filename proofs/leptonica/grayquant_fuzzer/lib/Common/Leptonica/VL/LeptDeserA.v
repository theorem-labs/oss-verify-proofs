(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_25000_25620.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr LeptBase LeptErr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
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
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvVL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {P16 : PinsG}.
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
      msteps SEGS (mkst regs (rl dVL_25134 0x25134) m rom) (mkst regs' (rl dVL_25134 0x2516c) (FR9 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 nb
      /\ getr regs' 12 = Z_to_bv 64 18446744071562067995 /\ getr regs' 13 = Z_to_bv 64 (nb + 18446744071562067968)
      /\ regs_agree (fun r => In r [2; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m s dp nb ret Hs Hs64 Hdp Hnb SOK H2 H1 H10 H11.
    unfold FR9. eexists. split.
    - zv F_25134 D_25134 (Z_to_bv 64 (s - 96)).
      stepST F_25138 D_25138 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_2513c D_2513c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_25140 D_25140 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_25144 D_25144 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_25148 D_25148 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_2514c D_2514c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_25150 D_25150 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_25154 D_25154 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_25158 D_25158 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepb_ft F_2515c D_2515c ltac:(condZ).
      sn F_25160 D_25160.
      zv F_25164 D_25164 (Z_to_bv 64 (nb + 18446744071562067968)).
      sn F_25168 D_25168.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A1 : forall regs m (nb : Z),
    (28 <= nb < 2 ^ 31)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x2516c) m rom) (mkst regs' (rl dVL_25134 0x251cc) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m nb Hnb H12 H13. eexists. split.
    - stepb_tk F_2516c D_2516c ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A2 : forall regs m (nb : Z),
    (0 <= nb < 28)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    getr regs 11 = Z_to_bv 64 nb ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_25134 0x2516c) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_10726 0x10726 /\ getr regs' 11 = rl dVLS_105ea 0x105ea /\ getr regs' 12 = Z_to_bv 64 nb /\ getr regs' 1 = rl dVL_25134 0x251a0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVL_25134 :: nil).
    intros regs m nb Hnb H12 H13 H11 Rg Rs. eexists. split.
    - stepb_ft F_2516c D_2516c ltac:(condZ).
      sn F_25170 D_25170.
      stepLD F_25174 D_25174 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_25178 D_25178 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_2517c D_2517c. stepb_ft F_25180 D_25180 ltac:(condZ).
      sn F_25184 D_25184. sn F_25188 D_25188. sn F_2518c D_2518c. sn F_25190 D_25190. sn F_25194 D_25194. sn F_25198 D_25198.
      sn F_2519c D_2519c. apply mst_refl.
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
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x251cc) m rom) (mkst regs' (rl dVL_25134 0x25264) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (dp + 20) /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m dp b0 b1 b2 b3 Hdp Hdp4 AL4 R0 R1 R2 R3 E0 E1 E2 E3 H10.
    assert (EQ4 : ((dp + 4) mod 4 = 0)%Z) by (apply mod4_plus; [exact AL4 | reflexivity]).
    assert (EQ8 : ((dp + 8) mod 4 = 0)%Z) by (apply mod4_plus; [exact AL4 | reflexivity]).
    assert (EQ12 : ((dp + 12) mod 4 = 0)%Z) by (apply mod4_plus; [exact AL4 | reflexivity]).
    assert (EQ20 : ((dp + 20) mod 4 = 0)%Z) by (apply mod4_plus; [exact AL4 | reflexivity]).
    eexists. split.
    - stepLBU F_251cc D_251cc b0 ltac:(addr_norm; exact R0). rewrite E0.
      sn F_251d0 D_251d0. stepb_ft F_251d4 D_251d4 ltac:(condZ).
      sn F_251d8 D_251d8. stepb_ft F_251dc D_251dc ltac:(condZ).
      stepLBU F_251e0 D_251e0 b1 ltac:(addr_norm; exact R1). rewrite E1.
      sn F_251e4 D_251e4. stepb_ft F_251e8 D_251e8 ltac:(condZ).
      sn F_251ec D_251ec. stepb_ft F_251f0 D_251f0 ltac:(condZ).
      stepLBU F_251f4 D_251f4 b2 ltac:(addr_norm; exact R2). rewrite E2.
      sn F_251f8 D_251f8. stepb_ft F_251fc D_251fc ltac:(condZ).
      sn F_25200 D_25200. stepb_ft F_25204 D_25204 ltac:(condZ).
      stepLBU F_25208 D_25208 b3 ltac:(addr_norm; exact R3). rewrite E3.
      sn F_2520c D_2520c. stepb_ft F_25210 D_25210 ltac:(condZ).
      sn F_25214 D_25214. stepb_ft F_25218 D_25218 ltac:(condZ).
      zv F_2521c D_2521c (Z_to_bv 64 (dp + 4)). guard4 F_25220 D_25220 EQ4. stepb_ft F_25224 D_25224 ltac:(condZ).
      sn F_25228 D_25228. stepb_ft F_2522c D_2522c ltac:(condZ).
      zv F_25230 D_25230 (Z_to_bv 64 (dp + 8)). guard4 F_25234 D_25234 EQ8. stepb_ft F_25238 D_25238 ltac:(condZ).
      sn F_2523c D_2523c. stepb_ft F_25240 D_25240 ltac:(condZ).
      zv F_25244 D_25244 (Z_to_bv 64 (dp + 12)). guard4 F_25248 D_25248 EQ12. stepb_ft F_2524c D_2524c ltac:(condZ).
      sn F_25250 D_25250. stepb_ft F_25254 D_25254 ltac:(condZ).
      zv F_25258 D_25258 (Z_to_bv 64 (dp + 20)). guard4 F_2525c D_2525c EQ20. stepb_ft F_25260 D_25260 ltac:(condZ).
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
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x251cc) m rom) (mkst regs' (rl dVL_25134 0x252a0) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m dp b0 b1 b2 b3 Hdp Hdp4 R0 R1 R2 R3 NE H10.
    pose proof (u8_range b0). pose proof (u8_range b1). pose proof (u8_range b2). pose proof (u8_range b3).
    destruct (Z.eq_dec (u b0) 115) as [E0|E0].
    2: { clear NE. eexists. split.
         { stepLBU F_251cc D_251cc b0 ltac:(addr_norm; exact R0). sn F_251d0 D_251d0. stepb_tk F_251d4 D_251d4 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    destruct (Z.eq_dec (u b1) 112) as [E1|E1].
    2: { clear NE. eexists. split.
         { stepLBU F_251cc D_251cc b0 ltac:(addr_norm; exact R0). sn F_251d0 D_251d0. stepb_ft F_251d4 D_251d4 ltac:(condZ).
           sn F_251d8 D_251d8. stepb_ft F_251dc D_251dc ltac:(condZ).
           stepLBU F_251e0 D_251e0 b1 ltac:(addr_norm; exact R1). sn F_251e4 D_251e4. stepb_tk F_251e8 D_251e8 ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    destruct (Z.eq_dec (u b2) 105) as [E2|E2].
    2: { clear NE. eexists. split.
         { stepLBU F_251cc D_251cc b0 ltac:(addr_norm; exact R0). sn F_251d0 D_251d0. stepb_ft F_251d4 D_251d4 ltac:(condZ).
           sn F_251d8 D_251d8. stepb_ft F_251dc D_251dc ltac:(condZ).
           stepLBU F_251e0 D_251e0 b1 ltac:(addr_norm; exact R1). sn F_251e4 D_251e4. stepb_ft F_251e8 D_251e8 ltac:(condZ).
           sn F_251ec D_251ec. stepb_ft F_251f0 D_251f0 ltac:(condZ).
           stepLBU F_251f4 D_251f4 b2 ltac:(addr_norm; exact R2). sn F_251f8 D_251f8. stepb_tk F_251fc D_251fc ltac:(condZ).
           apply mst_refl. }
         solve_regs_agree. }
    assert (E3 : u b3 <> 120%Z) by (intros E3; apply NE; lia). clear NE.
    eexists. split.
    { stepLBU F_251cc D_251cc b0 ltac:(addr_norm; exact R0). sn F_251d0 D_251d0. stepb_ft F_251d4 D_251d4 ltac:(condZ).
      sn F_251d8 D_251d8. stepb_ft F_251dc D_251dc ltac:(condZ).
      stepLBU F_251e0 D_251e0 b1 ltac:(addr_norm; exact R1). sn F_251e4 D_251e4. stepb_ft F_251e8 D_251e8 ltac:(condZ).
      sn F_251ec D_251ec. stepb_ft F_251f0 D_251f0 ltac:(condZ).
      stepLBU F_251f4 D_251f4 b2 ltac:(addr_norm; exact R2). sn F_251f8 D_251f8. stepb_ft F_251fc D_251fc ltac:(condZ).
      sn F_25200 D_25200. stepb_ft F_25204 D_25204 ltac:(condZ).
      stepLBU F_25208 D_25208 b3 ltac:(addr_norm; exact R3). sn F_2520c D_2520c. stepb_tk F_25210 D_25210 ltac:(condZ).
      apply mst_refl. }
    solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pd_C : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25264) m rom) (mkst regs' (rl dVL_25134 0x252f4) m rom)
      /\ getr regs' 9 = Z_to_bv 64 wr /\ getr regs' 13 = Z_to_bv 64 18446744073708551615
      /\ regs_agree (fun r => In r [9; 13; 14]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m dp wr bs4 Hdp Hdphi R4 W4 Hwr H10. eexists. split.
    - stepLD F_25264 D_25264 bs4 (Z_to_bv 64 wr) ltac:(addr_norm; exact R4) ltac:(rewrite u_Z2bv by lia; exact W4).
      rewrite (v_lw_small wr) by lia.
      sn F_25268 D_25268. sn F_2526c D_2526c.
      sn F_25270 D_25270. fixv (Z_to_bv 64 (sw32 (sw32 wr + 18446744073708551615))) ltac:(rewrite v_addw_Z, (sw32_small wr) by lia; reflexivity).
      stepb_tk F_25274 D_25274 ltac:(pin; rewrite c_ltu_zx; apply wchk_ok; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Cbad : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (0 <= wr < 2 ^ 32)%Z -> ~ (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25264) m rom) (mkst regs' (rl dVL_25134 0x25278) m rom)
      /\ regs_agree (fun r => In r [9; 13; 14]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m dp wr bs4 Hdp Hdphi R4 W4 Hwr NW H10. eexists. split.
    - stepLD F_25264 D_25264 bs4 (Z_to_bv 64 wr) ltac:(addr_norm; exact R4) ltac:(rewrite u_Z2bv by lia; exact W4).
      rewrite (v_lw_Z wr).
      sn F_25268 D_25268. sn F_2526c D_2526c.
      sn F_25270 D_25270. fixv (Z_to_bv 64 (sw32 (sw32 wr + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      stepb_ft F_25274 D_25274 ltac:(pin; rewrite c_ltu_zx; apply wchk_bad; lia).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_D : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 13 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x252f4) m rom) (mkst regs' (rl dVL_25134 0x25328) m rom)
      /\ getr regs' 18 = Z_to_bv 64 hr /\ regs_agree (fun r => In r [18; 14]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m dp hr bs8 Hdp Hdphi R8 W8 Hhr H10 H13. eexists. split.
    - stepLD F_252f4 D_252f4 bs8 (Z_to_bv 64 hr) ltac:(addr_norm; exact R8) ltac:(rewrite u_Z2bv by lia; exact W8).
      rewrite (v_lw_small hr) by lia.
      sn F_252f8 D_252f8. fixv (Z_to_bv 64 (sw32 (sw32 hr + 18446744073708551615))) ltac:(rewrite v_addw_Z, (sw32_small hr) by lia; reflexivity).
      stepb_tk F_252fc D_252fc ltac:(pin; rewrite c_ltu_zx; apply wchk_ok; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Dbad : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (0 <= hr < 2 ^ 32)%Z -> ~ (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 13 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x252f4) m rom) (mkst regs' (rl dVL_25134 0x25300) m rom)
      /\ regs_agree (fun r => In r [18; 14]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m dp hr bs8 Hdp Hdphi R8 W8 Hhr NH H10 H13. eexists. split.
    - stepLD F_252f4 D_252f4 bs8 (Z_to_bv 64 hr) ltac:(addr_norm; exact R8) ltac:(rewrite u_Z2bv by lia; exact W8).
      rewrite (v_lw_Z hr).
      sn F_252f8 D_252f8. fixv (Z_to_bv 64 (sw32 (sw32 hr + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      stepb_ft F_252fc D_252fc ltac:(pin; rewrite c_ltu_zx; apply wchk_bad; lia).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_E : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25328) m rom) (mkst regs' (rl dVL_25134 0x25360) m rom)
      /\ regs_agree (fun r => In r [13; 14]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m wr hr Hw Hh Hwh H9 H18. eexists. split.
    - zv F_25328 D_25328 (Z_to_bv 64 (hr * wr)). sn F_2532c D_2532c. sn F_25330 D_25330.
      stepb_tk F_25334 D_25334 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  Lemma pd_Ebad : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (400000000 < wr * hr)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25328) m rom) (mkst regs' (rl dVL_25134 0x25338) m rom)
      /\ regs_agree (fun r => In r [13; 14]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m wr hr Hw Hh Hwh H9 H18. assert (hr * wr < 2 ^ 63)%Z by nia. eexists. split.
    - zv F_25328 D_25328 (Z_to_bv 64 (hr * wr)). sn F_2532c D_2532c. sn F_25330 D_25330.
      stepb_ft F_25334 D_25334 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition et_leaves : list (Z * Z) :=
    [((0x252a0 + dVL_25134), (0x10749 + dVLS_10749)); ((0x25278 + dVL_25134), (0x1097f + dVLS_1097f)); ((0x25300 + dVL_25134), (0x1034c + dVLS_1034c)); ((0x25338 + dVL_25134), (0x10322 + dVLS_10322)); ((0x25470 + dVL_25134), (0x1079f + dVLS_1079f)); ((0x25498 + dVL_25134), (0x10488 + dVLS_10488))]%Z.
  Lemma pd_ET : forall pc msg regs m,
    In (pc, msg) et_leaves ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (rl dVL_25134 0x252c4) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = rl dVLS_105ea 0x105ea
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVL_25134 :: nil).
    intros pc msg regs m Hin Rg Rs. unfold et_leaves in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E; intros <- <-.
    - eexists. split.
      { sn F_252a0 D_252a0.
        stepLD F_252a4 D_252a4 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_252a8 D_252a8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_252ac D_252ac. stepb_ft F_252b0 D_252b0 ltac:(condZ).
        sn F_252b4 D_252b4. sn F_252b8 D_252b8. sn F_252bc D_252bc. sn F_252c0 D_252c0.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_25278 D_25278.
        stepLD F_2527c D_2527c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_25280 D_25280 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_25284 D_25284. stepb_ft F_25288 D_25288 ltac:(condZ).
        sn F_2528c D_2528c. sn F_25290 D_25290. sn F_25294 D_25294. sn F_25298 D_25298.
        sn F_2529c D_2529c.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_25300 D_25300.
        stepLD F_25304 D_25304 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_25308 D_25308 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_2530c D_2530c. stepb_ft F_25310 D_25310 ltac:(condZ).
        sn F_25314 D_25314. sn F_25318 D_25318. sn F_2531c D_2531c. sn F_25320 D_25320.
        sn F_25324 D_25324.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_25338 D_25338.
        stepLD F_2533c D_2533c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_25340 D_25340 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_25344 D_25344. stepb_ft F_25348 D_25348 ltac:(condZ).
        sn F_2534c D_2534c. sn F_25350 D_25350. sn F_25354 D_25354. sn F_25358 D_25358.
        sn F_2535c D_2535c.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_25470 D_25470.
        stepLD F_25474 D_25474 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_25478 D_25478 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_2547c D_2547c. stepb_ft F_25480 D_25480 ltac:(condZ).
        sn F_25484 D_25484. sn F_25488 D_25488. sn F_2548c D_2548c. sn F_25490 D_25490.
        sn F_25494 D_25494.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_25498 D_25498.
        stepLD F_2549c D_2549c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_254a0 D_254a0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_254a4 D_254a4. stepb_ft F_254a8 D_254a8 ltac:(condZ).
        sn F_254ac D_254ac. sn F_254b0 D_254b0. sn F_254b4 D_254b4. sn F_254b8 D_254b8.
        sn F_254bc D_254bc.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition ej_leaves : list (Z * Z) := [((0x254f8 + dVL_25134), (0x10807 + dVLS_10807)); ((0x25530 + dVL_25134), (0x10a7c + dVLS_10a7c)); ((0x255bc + dVL_25134), (0x103ef + dVLS_103ef))]%Z.
  Lemma pd_EJ : forall pc msg regs m,
    In (pc, msg) ej_leaves ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (rl dF_13730 0x13730) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = rl dVLS_105ea 0x105ea /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = rl dVL_25134 0x255e8
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVL_25134 :: nil).
    intros pc msg regs m Hin Rg Rs. unfold ej_leaves in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
    - eexists. split.
      { sn F_254f8 D_254f8.
        stepLD F_254fc D_254fc (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_25500 D_25500 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_25504 D_25504. stepb_ft F_25508 D_25508 ltac:(condZ).
        sn F_2550c D_2550c. sn F_25510 D_25510. sn F_25514 D_25514. sn F_25518 D_25518.
        sn F_2551c D_2551c.
        sn F_255e0 D_255e0. sn F_255e4 D_255e4.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_25530 D_25530.
        stepLD F_25534 D_25534 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_25538 D_25538 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_2553c D_2553c. stepb_ft F_25540 D_25540 ltac:(condZ).
        sn F_25544 D_25544. sn F_25548 D_25548. sn F_2554c D_2554c. sn F_25550 D_25550.
        sn F_25554 D_25554.
        sn F_255e0 D_255e0. sn F_255e4 D_255e4.
        apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      { sn F_255bc D_255bc.
        stepLD F_255c0 D_255c0 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_255c4 D_255c4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_255c8 D_255c8. stepb_ft F_255cc D_255cc ltac:(condZ).
        sn F_255d0 D_255d0. sn F_255d4 D_255d4. sn F_255d8 D_255d8. sn F_255dc D_255dc.
        sn F_255e0 D_255e0. sn F_255e4 D_255e4.
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
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x252c4) m rom) (mkst regs' (rl dF_13730 0x13730) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m s ret sv Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) H2. eexists. split.
    - sn F_252c4 D_252c4.
      stepLD8 F_252c8 D_252c8 ret. stepLD8 F_252cc D_252cc (sv 8%nat). stepLD8 F_252d0 D_252d0 (sv 9%nat).
      stepLD8 F_252d4 D_252d4 (sv 18%nat). stepLD8 F_252d8 D_252d8 (sv 19%nat). stepLD8 F_252dc D_252dc (sv 20%nat).
      stepLD8 F_252e0 D_252e0 (sv 21%nat). stepLD8 F_252e4 D_252e4 (sv 22%nat). stepLD8 F_252e8 D_252e8 (sv 23%nat).
      zv F_252ec D_252ec (Z_to_bv 64 s). sn F_252f0 D_252f0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x255f0) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil).
    intros regs m s ret sv Hs Hs64 Hret (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) H2. eexists. split.
    - stepLD8 F_255f0 D_255f0 ret. stepLD8 F_255f4 D_255f4 (sv 8%nat). stepLD8 F_255f8 D_255f8 (sv 9%nat).
      stepLD8 F_255fc D_255fc (sv 18%nat). stepLD8 F_25600 D_25600 (sv 19%nat). stepLD8 F_25604 D_25604 (sv 20%nat).
      stepLD8 F_25608 D_25608 (sv 21%nat). stepLD8 F_2560c D_2560c (sv 22%nat). stepLD8 F_25610 D_25610 (sv 23%nat).
      zv F_25614 D_25614 (Z_to_bv 64 s). stepret F_25618 D_25618 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_R0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x255ec) m rom) (mkst regs' (rl dVL_25134 0x255f0) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil). intros regs m. eexists. split; [sn F_255ec D_255ec; apply mst_refl|]. split; [gres; reflexivity | solve_regs_agree]. Qed.

  Lemma pd_J34 : forall regs m, exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x251a0) m rom) (mkst regs' (rl dVL_25134 0x255ec) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil). intros regs m. eexists. split; [sn F_251a0 D_251a0; apply mst_refl | solve_regs_agree]. Qed.
  Lemma pd_J88 : forall regs m, exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x254f4) m rom) (mkst regs' (rl dVL_25134 0x255ec) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil). intros regs m. eexists. split; [sn F_254f4 D_254f4; apply mst_refl | solve_regs_agree]. Qed.
  Lemma pd_J7c : forall regs m, exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x255e8) m rom) (mkst regs' (rl dVL_25134 0x255f0) m rom) /\ regs_agree (fun r => False) regs regs'.
  Proof. rl_dbounds (dVL_25134 :: nil). intros regs m. eexists. split; [sn F_255e8 D_255e8; apply mst_refl | solve_regs_agree]. Qed.
  Ltac rdn_out R := rewrite rdn_wbytes_out_Z; [exact R | rewrite ?length_N_to_le_bytes; lia].
End Segs.
End DeserA.
