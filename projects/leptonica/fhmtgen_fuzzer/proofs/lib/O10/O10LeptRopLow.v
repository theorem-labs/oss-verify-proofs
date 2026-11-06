(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10LeptStderr O10LeptBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10CL7a.
Import O10CL7a.O10LeptRop_iface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10_code_fhB.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition RLF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
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
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).

Lemma rdn_RLF_above : forall m s ret regs (a : Z) (n : nat), (112 <= s)%Z -> (s <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z ->
  rdn SEGS (RLF m s ret regs) (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros m s ret regs a n Hs Ha Hn. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. unfold RLF.
  rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.

Lemma RLF_outside : forall m s ret regs (a : word), (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 112 <= u a < s)%Z -> RLF m s ret regs a = m a.
Proof.
  intros m s ret regs a Hs Hs64 Ha. unfold RLF. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rl_A0 : forall regs m (s datad dpixw d dx dw spixw sx : Z) (ret : word),
  (112 <= s)%Z -> (s + 64 < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z ->
  (0 <= dpixw <= 20000)%Z -> (0 <= dx <= 20000)%Z -> (0 <= dw <= 20000)%Z -> (0 <= spixw <= 20000)%Z -> (0 <= sx <= 20000)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw ->
  getr regs 13 = Z_to_bv 64 d -> getr regs 15 = Z_to_bv 64 dx -> getr regs 17 = Z_to_bv 64 dw ->
  exists regs',
    msteps SEGS (mkst regs (0x1cda8 : word) m rom) (mkst regs' (0x1ce08 : word) (RLF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 5 = Z_to_bv 64 datad /\ getr regs' 11 = Z_to_bv 64 (dpixw * d)
    /\ getr regs' 15 = Z_to_bv 64 (dx * d) /\ getr regs' 17 = Z_to_bv 64 (dw * d) /\ getr regs' 6 = Z_to_bv 64 (spixw * d)
    /\ getr regs' 7 = Z_to_bv 64 (sx * d)
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 11; 15; 17; 28]%list) regs regs'.
Proof.
  intros regs m s datad dpixw d dx dw spixw sx ret Hs Hs64 Hd Hdpw Hdx Hdw Hspw Hsx SOK Rspw Rsx H2 H1 H10 H11 H13 H15 H17.
  assert (Hdd : (d = 1 \/ d = 8)%Z) by exact Hd.
  destruct Hd as [-> | ->]; eexists; (split; [
      zv F_1ccac D_1ccac (Z_to_bv 64 (s - 112));
      stepST F_1ccb0 D_1ccb0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
      stepST F_1ccb4 D_1ccb4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
      stepST F_1ccb8 D_1ccb8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
      stepST F_1ccbc D_1ccbc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
      stepST F_1ccc0 D_1ccc0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
      stepST F_1ccc4 D_1ccc4 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
      stepST F_1ccc8 D_1ccc8 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
      stepST F_1cccc D_1cccc (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK);
      stepST F_1ccd0 D_1ccd0 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK);
      stepST F_1ccd4 D_1ccd4 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK);
      stepST F_1ccd8 D_1ccd8 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK);
      stepST F_1ccdc D_1ccdc (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK);
      stepST F_1cce0 D_1cce0 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK);
      stepLD F_1cce4 D_1cce4 (word_to_le_bytes 8 (Z_to_bv 64 sx)) (Z_to_bv 64 sx) ltac:(addr_norm; repeat rdn_peel1; exact Rsx) ltac:(apply bytes_le_to_Z_8);
      stepLD F_1cce8 D_1cce8 (word_to_le_bytes 8 (Z_to_bv 64 spixw)) (Z_to_bv 64 spixw) ltac:(addr_norm; repeat rdn_peel1; exact Rspw) ltac:(apply bytes_le_to_Z_8);
      sn F_1ccec D_1ccec; sn F_1ccf0 D_1ccf0 |]).
  - (* [comment removed for export] *)
    stepb_tk F_1ccf4 D_1ccf4 ltac:(condZ). unfold RLF. apply mst_refl.
  - rewrite !Z.mul_1_r. repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - (* [comment removed for export] *)
    stepb_ft F_1ccf4 D_1ccf4 ltac:(condZ).
    sn F_1ccf8 D_1ccf8. fixv (Z_to_bv 64 (dpixw * 8)) ltac:(rewrite zbv_mul; f_equal; lia).
    sn F_1ccfc D_1ccfc. fixv (Z_to_bv 64 (dx * 8)) ltac:(rewrite zbv_mulw_small by lia; reflexivity).
    sn F_1cd00 D_1cd00. fixv (Z_to_bv 64 (dw * 8)) ltac:(rewrite zbv_mul; reflexivity).
    sn F_1cd04 D_1cd04. fixv (Z_to_bv 64 (spixw * 8)) ltac:(rewrite zbv_mul; reflexivity).
    sn F_1cd08 D_1cd08. fixv (Z_to_bv 64 (sx * 8)) ltac:(rewrite zbv_mul; reflexivity).
    unfold RLF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac fz := fixv' (Z_to_bv 64 0) ltac:(first [ apply srai63_nn; lia | apply and_0_l | apply slt0_nonpos; lia | rewrite v_subw_Z; reflexivity | rewrite zbv_sub; reflexivity ]).
Ltac fbit x := fixv' (Z_to_bv 64 (if (0 <? x)%Z then 1 else 0)%Z) ltac:(apply slt0_Z; lia).
Ltac fmskw x := fixv' (Z_to_bv 64 (msk0 x)) ltac:(apply negw_bit).
Ltac fmsk x := fixv' (Z_to_bv 64 (msk0 x)) ltac:(apply neg_bit).
Ltac fmax x := fixv' (Z_to_bv 64 x) ltac:(apply and_msk0_nn; lia).
Ltac fsubw v := fixv' (Z_to_bv 64 v) ltac:(rewrite subw_fit by lia; f_equal; lia).
Ltac faddw v := fixv' (Z_to_bv 64 v) ltac:(rewrite addw_fit by lia; f_equal; lia).
Ltac fadd v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_add; f_equal; lia).

(* [comment removed for export] *)
Lemma rl_A1 : forall regs m (DX SX DW DPW SPW : Z),
  (0 <= DX)%Z -> (0 <= SX)%Z -> (1 <= DW)%Z -> (DX + DW <= DPW)%Z -> (SX + DW <= SPW)%Z -> (DPW <= 160000)%Z -> (SPW <= 160000)%Z ->
  getr regs 15 = Z_to_bv 64 DX -> getr regs 7 = Z_to_bv 64 SX -> getr regs 17 = Z_to_bv 64 DW -> getr regs 11 = Z_to_bv 64 DPW -> getr regs 6 = Z_to_bv 64 SPW ->
  exists regs',
    msteps SEGS (mkst regs (0x1ce08 : word) m rom) (mkst regs' (0x1ce78 : word) m rom)
    /\ getr regs' 19 = Z_to_bv 64 DX /\ getr regs' 26 = Z_to_bv 64 SX /\ getr regs' 6 = Z_to_bv 64 DW
    /\ regs_agree (fun r => In r [6; 7; 10; 11; 13; 15; 17; 19; 26]%list) regs regs'.
Proof.
  intros regs m DX SX DW DPW SPW H0 H0s H1 Hov1 Hov2 Hc1 Hc2 H15 H7 H17 H11 H6. eexists. split.
  - sn F_1cd0c D_1cd0c. fz. sn F_1cd10 D_1cd10. fbit DX. sn F_1cd14 D_1cd14. fz. sn F_1cd18 D_1cd18. fmskw DX.
    sn F_1cd1c D_1cd1c. fsubw SX. sn F_1cd20 D_1cd20. sn F_1cd24 D_1cd24. fmax DX.
    sn F_1cd28 D_1cd28. fbit SX. sn F_1cd2c D_1cd2c. fz. sn F_1cd30 D_1cd30. fmsk SX. sn F_1cd34 D_1cd34. fz.
    sn F_1cd38 D_1cd38. fmax SX. sn F_1cd3c D_1cd3c. sn F_1cd40 D_1cd40. fsubw DX.
    sn F_1cd44 D_1cd44. fsubw (DW - DPW)%Z. sn F_1cd48 D_1cd48. faddw (DW - DPW + DX)%Z.
    sn F_1cd4c D_1cd4c. fz. sn F_1cd50 D_1cd50. fz. sn F_1cd54 D_1cd54. fz. sn F_1cd58 D_1cd58. fsubw DW.
    sn F_1cd5c D_1cd5c. fsubw (SX - SPW)%Z. sn F_1cd60 D_1cd60. faddw (SX - SPW + DW)%Z.
    sn F_1cd64 D_1cd64. fz. sn F_1cd68 D_1cd68. fz. sn F_1cd6c D_1cd6c. fz. sn F_1cd70 D_1cd70. fsubw DW.
    stepb_tk F_1cd74 D_1cd74 ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_A2 : forall regs m (s dy sy dh dpixh spixh : Z),
  (112 <= s)%Z -> (s + 64 < 2 ^ 64)%Z ->
  (0 <= dy)%Z -> (0 <= sy)%Z -> (1 <= dh)%Z -> (dy + dh <= dpixh)%Z -> (sy + dh <= spixh)%Z -> (dpixh <= 20000)%Z -> (spixh <= 20000)%Z ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 16 = Z_to_bv 64 dy -> getr regs 12 = Z_to_bv 64 dpixh ->
  exists regs',
    msteps SEGS (mkst regs (0x1ce78 : word) m rom) (mkst regs' (0x1cef4 : word) m rom)
    /\ getr regs' 27 = Z_to_bv 64 dy /\ getr regs' 23 = Z_to_bv 64 sy /\ getr regs' 12 = Z_to_bv 64 dh
    /\ regs_agree (fun r => In r [10; 11; 12; 13; 15; 16; 17; 18; 23; 24; 25; 27]%list) regs regs'.
Proof.
  intros regs m s dy sy dh dpixh spixh Hs Hs64 H0 H0s H1 Hov1 Hov2 Hc1 Hc2 Rdh Rsph Rsy H2 H16 H12. eexists. split.
  - stepLD F_1cd7c D_1cd7c (word_to_le_bytes 8 (Z_to_bv 64 sy)) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply bytes_le_to_Z_8).
    stepLD F_1cd80 D_1cd80 (word_to_le_bytes 8 (Z_to_bv 64 spixh)) (Z_to_bv 64 spixh) ltac:(addr_norm; exact Rsph) ltac:(apply bytes_le_to_Z_8).
    stepLD F_1cd84 D_1cd84 (word_to_le_bytes 8 (Z_to_bv 64 dh)) (Z_to_bv 64 dh) ltac:(addr_norm; rewrite ?Z.sub_0_r; exact Rdh) ltac:(apply bytes_le_to_Z_8).
    sn F_1cd88 D_1cd88. fz. sn F_1cd8c D_1cd8c. fbit dy. sn F_1cd90 D_1cd90. fz. sn F_1cd94 D_1cd94. fmskw dy.
    sn F_1cd98 D_1cd98. fmax dy. sn F_1cd9c D_1cd9c. sn F_1cda0 D_1cda0. fsubw sy.
    sn F_1cda4 D_1cda4. fz. sn F_1cda8 D_1cda8. fbit sy. sn F_1cdac D_1cdac. fz. sn F_1cdb0 D_1cdb0. fmskw sy.
    sn F_1cdb4 D_1cdb4. sn F_1cdb8 D_1cdb8. fmax sy. sn F_1cdbc D_1cdbc. fsubw dy.
    sn F_1cdc0 D_1cdc0. fsubw (dh - dpixh)%Z. sn F_1cdc4 D_1cdc4. faddw (dh - dpixh + dy)%Z.
    sn F_1cdc8 D_1cdc8. fz. sn F_1cdcc D_1cdcc. fz. sn F_1cdd0 D_1cdd0. fz. sn F_1cdd4 D_1cdd4. fsubw dh.
    sn F_1cdd8 D_1cdd8. fsubw (sy - spixh)%Z. sn F_1cddc D_1cddc. faddw (sy - spixh + dh)%Z.
    sn F_1cde0 D_1cde0. fz. sn F_1cde4 D_1cde4. fz. sn F_1cde8 D_1cde8. fz. sn F_1cdec D_1cdec. fsubw dh.
    stepb_tk F_1cdf0 D_1cdf0 ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_A3a : forall regs m (s DX SX swpl datas : Z),
  (112 <= s)%Z -> (s + 64 < 2 ^ 64)%Z -> (0 <= DX < 2 ^ 31)%Z -> (0 <= SX < 2 ^ 31)%Z -> (DX mod 32 = 0)%Z -> (SX mod 32 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 12)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 19 = Z_to_bv 64 DX -> getr regs 26 = Z_to_bv 64 SX ->
  exists regs',
    msteps SEGS (mkst regs (0x1cef4 : word) m rom) (mkst regs' (0x1cfb4 : word) m rom)
    /\ getr regs' 13 = Z_to_bv 64 swpl /\ getr regs' 22 = Z_to_bv 64 datas /\ getr regs' 21 = Z_to_bv 64 11
    /\ regs_agree (fun r => In r [11; 13; 15; 21; 22]%list) regs regs'.
Proof.
  intros regs m s DX SX swpl datas Hs Hs64 HDX HSX EDX ESX Rop Rdatas Rswpl H2 H19 H26. eexists. split.
  - stepLD F_1cdf8 D_1cdf8 (word_to_le_bytes 8 (Z_to_bv 64 swpl)) (Z_to_bv 64 swpl) ltac:(addr_norm; exact Rswpl) ltac:(apply bytes_le_to_Z_8).
    stepLD F_1cdfc D_1cdfc (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(addr_norm; exact Rop) ltac:(apply bytes_le_to_Z_8).
    stepLD F_1ce00 D_1ce00 (word_to_le_bytes 8 (Z_to_bv 64 datas)) (Z_to_bv 64 datas) ltac:(addr_norm; exact Rdatas) ltac:(apply bytes_le_to_Z_8).
    sn F_1ce04 D_1ce04. sn F_1ce08 D_1ce08. fixv' (Z_to_bv 64 0) ltac:(apply or_andi31_0; lia).
    sn F_1ce0c D_1ce0c.
    stepb_tk F_1ce10 D_1ce10 ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_A3b : forall regs m (DW k : Z),
  (1 <= DW < 2 ^ 31)%Z -> k = (DW mod 32)%Z -> (0 <= k < 32)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x1193c + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 6 = Z_to_bv 64 DW ->
  exists regs',
    msteps SEGS (mkst regs (0x1cfb4 : word) m rom) (mkst regs' (0x1d0bc : word) m rom)
    /\ getr regs' 15 = Z_to_bv 64 k
    /\ regs_agree (fun r => In r [7; 10; 15; 16]%list) regs regs'.
Proof.
  intros regs m DW k HDW Ek Hk TBL H6.
  destruct (Z.eq_dec k 0) as [E0 | NE0].
  - eexists. split.
    + sn F_1ceb8 D_1ceb8. fixv' (Z_to_bv 64 k) ltac:(rewrite andi_31_Z by lia; rewrite <- Ek; reflexivity).
      stepb_tk F_1cebc D_1cebc ltac:(condZ).
      apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - destruct (TBL k ltac:(lia)) as (bs & v & Rv & Ev).
    eexists. split.
    + sn F_1ceb8 D_1ceb8. fixv' (Z_to_bv 64 k) ltac:(rewrite andi_31_Z by lia; rewrite <- Ek; reflexivity).
      stepb_ft F_1cebc D_1cebc ltac:(condZ).
      sn F_1cec0 D_1cec0. fixv' (Z_to_bv 64 (4 * k)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
      sn F_1cec4 D_1cec4. sn F_1cec8 D_1cec8. sn F_1cecc D_1cecc.
      fixv' (Z_to_bv 64 (0x1193c + 4 * k)) ltac:(vclose).
      stepLD F_1ced0 D_1ced0 bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev).
      sn F_1ced4 D_1ced4.
      apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_A3c : forall regs m (DW DX SX sy dy swpl dwpl datas datad nfw cdx csx : Z) (mk : word),
  (1 <= DW < 2 ^ 31)%Z -> (0 <= DX < 2 ^ 31)%Z -> (0 <= SX < 2 ^ 31)%Z ->
  nfw = (DW / 32)%Z -> cdx = (DX / 32)%Z -> csx = (SX / 32)%Z -> (0 <= nfw < 2 ^ 26)%Z -> (0 <= cdx < 2 ^ 26)%Z -> (0 <= csx < 2 ^ 26)%Z ->
  (0 <= sy < 2 ^ 24)%Z -> (0 <= swpl)%Z -> (sy * swpl < 2 ^ 24)%Z -> (0 <= dy < 2 ^ 24)%Z -> (0 <= dwpl)%Z -> (dy * dwpl < 2 ^ 24)%Z ->
  (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  rdn SEGS m (Z_to_bv 64 0x118ac) 4 = Some (Z_to_le_bytes 4 50004) ->
  getr regs 6 = Z_to_bv 64 DW -> getr regs 23 = Z_to_bv 64 sy -> getr regs 13 = Z_to_bv 64 swpl -> getr regs 26 = Z_to_bv 64 SX ->
  getr regs 27 = Z_to_bv 64 dy -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 21 = Z_to_bv 64 11 -> getr regs 22 = Z_to_bv 64 datas ->
  getr regs 5 = Z_to_bv 64 datad -> getr regs 19 = Z_to_bv 64 DX -> getr regs 7 = mk ->
  exists regs',
    msteps SEGS (mkst regs (0x1d0bc : word) m rom) (mkst regs' (0x1dc50 : word) m rom)
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 5 = Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * cdx) /\ getr regs' 17 = Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * cdx)
    /\ getr regs' 8 = Z_to_bv 64 (datas + 4 * (sy * swpl) + 4 * csx) /\ getr regs' 16 = Z_to_bv 64 (datas + 4 * (sy * swpl) + 4 * csx)
    /\ getr regs' 29 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 30 = Z_to_bv 64 (4 * swpl) /\ getr regs' 31 = Z_to_bv 64 32
    /\ (1 <= nfw -> getr regs' 28 = Z_to_bv 64 (4 * nfw))%Z
    /\ regs_agree (fun r => In r [5; 8; 10; 11; 16; 17; 21; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs m DW DX SX sy dy swpl dwpl datas datad nfw cdx csx mk HDW HDX HSX Enf Ecd Ecs Hnf Hcd Hcs Hsy Hswpl Hsyw Hdy Hdwpl Hdyw Hsw Hdw JT
    H6 H23 H13 H26 H27 H14 H21 H22 H5 H19 H7.
  assert (M1 : (0 <= sy * swpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (M2 : (0 <= dy * dwpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  eexists. split.
  - sn F_1cfc0 D_1cfc0. sn F_1cfc4 D_1cfc4. sn F_1cfc8 D_1cfc8.
    stepb_ft F_1cfcc D_1cfcc ltac:(condZ).
    sn F_1cfd0 D_1cfd0. fixv' (Z_to_bv 64 nfw) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Enf; reflexivity).
    sn F_1cfd4 D_1cfd4. fixv' (Z_to_bv 64 (sy * swpl)) ltac:(rewrite zbv_mulw_small by lia; reflexivity).
    sn F_1cfd8 D_1cfd8. fixv' (Z_to_bv 64 csx) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Ecs; reflexivity).
    sn F_1cfdc D_1cfdc. fixv' (Z_to_bv 64 (dy * dwpl)) ltac:(rewrite zbv_mulw_small by lia; reflexivity).
    sn F_1cfe0 D_1cfe0. fixv' (Z_to_bv 64 44) ltac:(rewrite zbv_slli by lia; reflexivity).
    sn F_1cfe4 D_1cfe4. fixv' (Z_to_bv 64 (4 * (sy * swpl))) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cfe8 D_1cfe8. fixv' (Z_to_bv 64 (datas + 4 * (sy * swpl))) ltac:(rewrite zbv_add; reflexivity).
    sn F_1cfec D_1cfec.
    sn F_1cff0 D_1cff0. fixv' (Z_to_bv 64 (4 * csx)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cff4 D_1cff4. fixv' (Z_to_bv 64 (4 * (dy * dwpl))) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cff8 D_1cff8. fixv' (Z_to_bv 64 0x11880) ltac:(vclose).
    sn F_1cffc D_1cffc. fixv' (Z_to_bv 64 0x118ac) ltac:(rewrite zbv_add; reflexivity).
    sn F_1d000 D_1d000. fixv' (Z_to_bv 64 (datas + 4 * (sy * swpl) + 4 * csx)) ltac:(rewrite zbv_add; reflexivity).
    stepLD F_1d004 D_1d004 (Z_to_le_bytes 4 50004) (Z_to_bv 64 50004) ltac:(addr_norm; rewrite ?Z.add_0_r; exact JT) ltac:(apply lez4; lia).
    change (v_lw (Z_to_bv 64 50004)) with (Z_to_bv 64 50004).
    sn F_1d008 D_1d008. fixv' (Z_to_bv 64 (datad + 4 * (dy * dwpl))) ltac:(rewrite zbv_add; reflexivity).
    sn F_1d00c D_1d00c. fixv' (Z_to_bv 64 cdx) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Ecd; reflexivity).
    sn F_1d010 D_1d010. fixv' (Z_to_bv 64 (4 * cdx)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1d014 D_1d014. fixv' (Z_to_bv 64 0x1dbd4) ltac:(rewrite zbv_add; reflexivity).
    sn F_1d018 D_1d018. fixv' (Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * cdx)) ltac:(rewrite zbv_add; reflexivity).
    stepret F_1d01c D_1d01c (0x1dbd4 : word) ltac:(bveq).
    sn F_1dad8 D_1dad8. sn F_1dadc D_1dadc.
    sn F_1dae0 D_1dae0. fixv' (Z_to_bv 64 (4 * cdx + 4 * (dy * dwpl))) ltac:(rewrite zbv_add; reflexivity).
    sn F_1dae4 D_1dae4. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1dae8 D_1dae8. fixv' (Z_to_bv 64 (4 * swpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1daec D_1daec. fixv' (Z_to_bv 64 (nfw - 1)) ltac:(rewrite zbv_addi; f_equal; lia).
    sn F_1daf0 D_1daf0. fixv' (Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * cdx)) ltac:(rewrite zbv_add; f_equal; lia).
    sn F_1daf4 D_1daf4. sn F_1daf8 D_1daf8. sn F_1dafc D_1dafc.
    sn F_1db00 D_1db00. sn F_1db04 D_1db04. sn F_1db08 D_1db08.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; [intros Hn1; apply zext_len4; lia | solve_regs_agree].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma le4_word : forall bs : list byte, length bs = 4%nat -> exists v : word, bytes_le_to_Z bs = bv_unsigned v.
Proof.
  intros bs L. exists (Z_to_bv 64 (bytes_le_to_Z bs)). pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in B. rewrite u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rl_Hf : forall regs m (DW : Z), (32 <= DW < 2 ^ 31)%Z ->
  getr regs 6 = Z_to_bv 64 DW -> getr regs 31 = Z_to_bv 64 32 ->
  exists regs', msteps SEGS (mkst regs (0x1dc50 : word) m rom) (mkst regs' (0x1dc58 : word) m rom)
    /\ getr regs' 18 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [18]%list) regs regs'.
Proof.
  intros regs m DW HDW H6 H31. eexists. split.
  - stepb_ft F_1db54 D_1db54 ltac:(condZ). sn F_1db58 D_1db58. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_I : forall (last : bool) regs m (srow drow off n4 : Z) (bs : list byte) (v : word),
  (0 <= srow)%Z -> (0 <= drow)%Z -> (0 <= off)%Z -> (off + 4 <= n4)%Z -> (n4 < 2 ^ 32)%Z -> (srow + n4 < 2 ^ 64)%Z -> (drow + n4 < 2 ^ 64)%Z ->
  (if last then off + 4 = n4 else off + 4 < n4)%Z ->
  rdn SEGS m (Z_to_bv 64 (srow + off)) 4 = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  store_ok SEGS m (Z_to_bv 64 (drow + off)) 4 = true ->
  getr regs 8 = Z_to_bv 64 srow -> getr regs 5 = Z_to_bv 64 drow -> getr regs 18 = Z_to_bv 64 off -> getr regs 28 = Z_to_bv 64 n4 ->
  exists regs',
    msteps SEGS (mkst regs (0x1dc58 : word) m rom)
                (mkst regs' (if last then (0x1dc70 : word) else (0x1dc58 : word)) (wbytes m (Z_to_bv 64 (drow + off)) (word_to_le_bytes 4 (v_lw v))) rom)
    /\ getr regs' 18 = Z_to_bv 64 (off + 4)
    /\ regs_agree (fun r => In r [9; 18; 19]%list) regs regs'.
Proof.
  intros last regs m srow drow off n4 bs v H1 H2 H3 H4 H5 H6 H7 HL Rd Ev SOK R8 R5 R18 R28.
  destruct last; eexists; (split; [
    sn F_1db5c D_1db5c; fixv' (Z_to_bv 64 (srow + off)) ltac:(rewrite zbv_add; reflexivity);
    stepLD F_1db60 D_1db60 bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Ev);
    sn F_1db64 D_1db64; fixv' (Z_to_bv 64 (drow + off)) ltac:(rewrite zbv_add; reflexivity);
    sn F_1db68 D_1db68; fixv' (Z_to_bv 64 (off + 4)) ltac:(rewrite zbv_addi; reflexivity);
    stepST F_1db6c D_1db6c (Z_to_bv 64 (drow + off)) (v_lw v) ltac:(store_ok_peel; exact SOK) |]).
  - stepb_ft F_1db70 D_1db70 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_tk F_1db70 D_1db70 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_T : forall regs m (srow drow n4 k : Z),
  (0 <= k < 32)%Z ->
  getr regs 8 = Z_to_bv 64 srow -> getr regs 5 = Z_to_bv 64 drow -> getr regs 18 = Z_to_bv 64 n4 -> getr regs 15 = Z_to_bv 64 k ->
  exists regs',
    msteps SEGS (mkst regs (0x1dc70 : word) m rom) (mkst regs' (if Z.eq_dec k 0 then (0x1dc3c : word) else (0x1dc24 : word)) m rom)
    /\ getr regs' 9 = Z_to_bv 64 (drow + n4) /\ getr regs' 18 = Z_to_bv 64 (srow + n4)
    /\ regs_agree (fun r => In r [9; 18]%list) regs regs'.
Proof.
  intros regs m srow drow n4 k Hk R8 R5 R18 R15.
  destruct (Z.eq_dec k 0) as [E|NE]; eexists; (split; [
    sn F_1db74 D_1db74; fixv' (Z_to_bv 64 (drow + n4)) ltac:(rewrite zbv_add; reflexivity);
    sn F_1db78 D_1db78; fixv' (Z_to_bv 64 (srow + n4)) ltac:(rewrite zbv_add; reflexivity) |]).
  - stepb_ft F_1db7c D_1db7c ltac:(condZ). sn F_1db80 D_1db80. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_tk F_1db7c D_1db7c ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_S : forall regs m (DW i swpl dwpl psf pdf k : Z),
  (1 <= DW < 32)%Z -> (1 <= k < 32)%Z -> (0 <= i < 2 ^ 24)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  getr regs 6 = Z_to_bv 64 DW -> getr regs 31 = Z_to_bv 64 32 -> getr regs 10 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 swpl ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 16 = Z_to_bv 64 psf -> getr regs 17 = Z_to_bv 64 pdf -> getr regs 15 = Z_to_bv 64 k ->
  exists regs',
    msteps SEGS (mkst regs (0x1dc50 : word) m rom) (mkst regs' (0x1dc24 : word) m rom)
    /\ getr regs' 9 = Z_to_bv 64 (pdf + 4 * (i * dwpl)) /\ getr regs' 18 = Z_to_bv 64 (psf + 4 * (i * swpl))
    /\ regs_agree (fun r => In r [9; 18; 19]%list) regs regs'.
Proof.
  intros regs m DW i swpl dwpl psf pdf k HDW Hk Hi Hsw Hdw R6 R31 R10 R13 R14 R16 R17 R15. eexists. split.
  - stepb_tk F_1db54 D_1db54 ltac:(condZ).
    sn F_1db0c D_1db0c. fixv' (Z_to_bv 64 (i * swpl)) ltac:(rewrite zbv_mul; reflexivity).
    sn F_1db10 D_1db10. fixv' (Z_to_bv 64 (i * dwpl)) ltac:(rewrite zbv_mul; reflexivity).
    sn F_1db14 D_1db14. fixv' (Z_to_bv 64 (4 * (i * swpl))) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1db18 D_1db18. fixv' (Z_to_bv 64 (4 * (i * dwpl))) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1db1c D_1db1c. fixv' (Z_to_bv 64 (psf + 4 * (i * swpl))) ltac:(rewrite zbv_add; reflexivity).
    sn F_1db20 D_1db20. fixv' (Z_to_bv 64 (pdf + 4 * (i * dwpl))) ltac:(rewrite zbv_add; reflexivity).
    stepb_ft F_1db24 D_1db24 ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_P : forall regs m (pd ps : Z) (bd bsr : list byte) (vd vs : word),
  (0 <= pd < 2 ^ 64)%Z -> (0 <= ps < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> bytes_le_to_Z bd = bv_unsigned vd ->
  rdn SEGS m (Z_to_bv 64 ps) 4 = Some bsr -> bytes_le_to_Z bsr = bv_unsigned vs ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  getr regs 9 = Z_to_bv 64 pd -> getr regs 18 = Z_to_bv 64 ps ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (0x1dc24 : word) m rom) (mkst regs' (0x1dc3c : word) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ regs_agree (fun r => In r [18; 19]%list) regs regs'.
Proof.
  intros regs m pd ps bd bsr vd vs Hpd Hps Rd Evd Rs Evs SOK R9 R18. eexists. eexists. split.
  - stepLD F_1db28 D_1db28 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    stepLD F_1db2c D_1db2c bsr vs ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(exact Evs).
    sn F_1db30 D_1db30. sn F_1db34 D_1db34. sn F_1db38 D_1db38.
    stepST F_1db3c D_1db3c (Z_to_bv 64 pd) (v_or (v_and (v_lw vs) (getr regs 7)) (v_and (v_lw vd) (getr regs 11))) ltac:(store_ok_peel; exact SOK).
    apply mst_refl.
  - gres. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition rlcells (M : word -> option byte) (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) /\
  rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) /\
  rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) /\
  rdn SEGS M (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) /\
  rdn SEGS M (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) /\
  rdn SEGS M (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) /\
  rdn SEGS M (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) /\
  rdn SEGS M (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) /\
  rdn SEGS M (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) /\
  rdn SEGS M (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) /\
  rdn SEGS M (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v11).

Lemma rlcells_RLF : forall m s ret regs, (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rlcells (RLF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27).
Proof. intros m s ret regs Hs Hs64. unfold rlcells, RLF. repeat split; rdn_chain. Qed.

Lemma rlcells_frame : forall M M' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11, (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rlcells M s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 -> (forall x : word, (s - 104 <= u x < s)%Z -> M' x = M x) -> rlcells M' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11.
Proof.
  intros M M' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 (C & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) E.
  unfold rlcells. repeat split;
    [rewrite <- C | rewrite <- C0 | rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6 | rewrite <- C7 | rewrite <- C8 | rewrite <- C9 | rewrite <- C10 | rewrite <- C11];
    (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
Qed.

(* [comment removed for export] *)
Lemma rl_N1 : forall regs m (i dh srow drow s4 d4 : Z),
  (0 <= i)%Z -> (i + 1 < dh)%Z -> (dh < 2 ^ 31)%Z ->
  getr regs 10 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 dh -> getr regs 5 = Z_to_bv 64 drow -> getr regs 8 = Z_to_bv 64 srow ->
  getr regs 29 = Z_to_bv 64 d4 -> getr regs 30 = Z_to_bv 64 s4 ->
  exists regs',
    msteps SEGS (mkst regs (0x1dc3c : word) m rom) (mkst regs' (0x1dc50 : word) m rom)
    /\ getr regs' 10 = Z_to_bv 64 (i + 1) /\ getr regs' 5 = Z_to_bv 64 (drow + d4) /\ getr regs' 8 = Z_to_bv 64 (srow + s4)
    /\ regs_agree (fun r => In r [5; 8; 10]%list) regs regs'.
Proof.
  intros regs m i dh srow drow s4 d4 Hi Hi1 Hdh R10 R12 R5 R8 R29 R30. eexists. split.
  - sn F_1db40 D_1db40. fixv' (Z_to_bv 64 (i + 1)) ltac:(rewrite zbv_addi; reflexivity).
    sn F_1db44 D_1db44. fixv' (Z_to_bv 64 (drow + d4)) ltac:(rewrite zbv_add; reflexivity).
    sn F_1db48 D_1db48. fixv' (Z_to_bv 64 (srow + s4)) ltac:(rewrite zbv_add; reflexivity).
    stepb_tk F_1db4c D_1db4c ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rl_N2 : forall regs m (s i dh : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = dh)%Z -> (dh < 2 ^ 31)%Z -> ret_ok ret ->
  rlcells m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 dh ->
  exists regs',
    msteps SEGS (mkst regs (0x1dc3c : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5 /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10 /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 5; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s i dh ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 Hi Hi1 Hdh Hret (C & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) R2 R10 R12.
  eexists. split.
  - sn F_1db40 D_1db40. fixv' (Z_to_bv 64 (i + 1)) ltac:(rewrite zbv_addi; reflexivity).
    sn F_1db44 D_1db44. sn F_1db48 D_1db48.
    stepb_ft F_1db4c D_1db4c ltac:(condZ).
    sn F_1db50 D_1db50.
    stepLD8 F_1ec44 D_1ec44 ret. stepLD8 F_1ec48 D_1ec48 v0. stepLD8 F_1ec4c D_1ec4c v1. stepLD8 F_1ec50 D_1ec50 v2.
    stepLD8 F_1ec54 D_1ec54 v3. stepLD8 F_1ec58 D_1ec58 v4. stepLD8 F_1ec5c D_1ec5c v5. stepLD8 F_1ec60 D_1ec60 v6.
    stepLD8 F_1ec64 D_1ec64 v7. stepLD8 F_1ec68 D_1ec68 v8. stepLD8 F_1ec6c D_1ec6c v9. stepLD8 F_1ec70 D_1ec70 v10.
    stepLD8 F_1ec74 D_1ec74 v11.
    zv F_1ec78 D_1ec78 (Z_to_bv 64 s).
    stepret F_1ec7c D_1ec7c ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.
End Segs.

(* [comment removed for export] *)
Section RopLowW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma W_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

(* [comment removed for export] *)
Lemma W_rd4_blk : forall C A m md (p : word) (k a : Z), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + 4 <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z ->
  exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = u v.
Proof.
  intros C A m md p k a CK HW L Hlo Hhi Hk. pose proof (u64_range p).
  destruct (rdn_defined SEGS m a 4 ltac:(lia) ltac:(cbn; lia)) as (bs & R & Lb).
  { intros i Hi. cbn in Hi. destruct (blk_byte C A m md p k (Z_to_bv 64 (a + i)) CK HW L ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact D. }
  destruct (le4_word bs Lb) as (v & Ev). exists bs, v. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma rl_inner_W : forall (n : nat) C Ar A m0 md (s : Z) (S : TSet) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word)
    (datad nd datas ns srow drow nfw : Z) (r0 : bvmap 5 word) m r (j : Z),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s <= c_top C)%Z ->
  sub_live Ar A -> live A (Z_to_bv 64 datad) = Some nd -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some ns -> (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z -> (0 < nd)%Z -> (0 < ns)%Z ->
  (1 <= nfw < 2 ^ 26)%Z -> (datad <= drow)%Z -> (drow + 4 * nfw <= datad + nd)%Z -> (datas <= srow)%Z -> (srow + 4 * nfw <= datas + ns)%Z ->
  (Z.of_nat n = nfw - 1 - j)%Z -> (0 <= j < nfw)%Z ->
  W C A m md -> POSTM C Ar s m0 m -> rlcells m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m a = m0 a) ->
  regs_agree (fun x => In x [9; 18; 19]%list) r0 r ->
  getr r0 8 = Z_to_bv 64 srow -> getr r0 5 = Z_to_bv 64 drow -> getr r0 28 = Z_to_bv 64 (4 * nfw) -> getr r 18 = Z_to_bv 64 (4 * j) ->
  (forall m' r', W C A m' md -> POSTM C Ar s m0 m' -> rlcells m' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m' a = m0 a) ->
     regs_agree (fun x => In x [9; 18; 19]%list) r0 r' -> getr r' 18 = Z_to_bv 64 (4 * nfw) ->
     realizes SEGS (mkCfg (mkst r' (0x1dc70 : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x1dc58 : word) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ar A m0 md s S ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 datad nd datas ns srow drow nfw r0 m r j
    CK Hs16 Hlo Hhi SUB Ld Ld0 Ld00 Ls Hdd Hds Hnd Hns Hnfw Hd1 Hd2 Hs1 Hs2 Hn Hj HW PM CE FT AG0 R8 R5 R28 R18 KT;
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LL16] in *; unfold ROPLOW_STACK in Hlo;
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [Gd TOPd]; rewrite u_Z2bv in Gd, TOPd by lia;
    destruct (blk_range C A m md (Z_to_bv 64 datas) ns CK HW Ls Hns) as [Gs TOPs]; rewrite u_Z2bv in Gs, TOPs by lia;
    destruct (W_rd4_blk C A m md (Z_to_bv 64 datas) ns (srow + 4 * j) CK HW Ls ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia))
      as (bs & v & Rd & Ev);
    pose proof (W_sok_blk C A m md (Z_to_bv 64 datad) nd (drow + 4 * j) 4 CK HW Ld ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia)) as SOK;
    assert (E8 : getr r 8 = Z_to_bv 64 srow) by (rewrite (AG0 8) by (cbv; intuition discriminate); exact R8);
    assert (E5 : getr r 5 = Z_to_bv 64 drow) by (rewrite (AG0 5) by (cbv; intuition discriminate); exact R5);
    assert (E28 : getr r 28 = Z_to_bv 64 (4 * nfw)) by (rewrite (AG0 28) by (cbv; intuition discriminate); exact R28).
  - (* [comment removed for export] *)
    destruct (rl_I al_rom true r m srow drow (4 * j) (4 * nfw) bs v ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                Rd Ev SOK E8 E5 R18 E28) as (r1 & RUN & Q18 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    set (m1 := wbytes m _ _).
    assert (WP : W C A m1 md /\ POSTM C Ar s m0 m1)
      by (subst m1; apply (WP_blk C Ar A m0 m _ (Z_to_bv 64 datad) _ nd _ s CK (conj HW PM) Ld Ld0 Ld00 SUB); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
    apply (KT m1 r1 (proj1 WP) (proj2 WP)).
    + apply (rlcells_frame m m1 s); [lia | lia | exact CE |]. intros x Hx. subst m1. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    + intros a Ha1 Ha2. subst m1. rewrite wbytes_outside by (rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia). exact (FT a Ha1 Ha2).
    + intros x Hx. rewrite (AG1 x Hx). exact (AG0 x Hx).
    + rewrite Q18. f_equal. lia.
  - (* [comment removed for export] *)
    destruct (rl_I al_rom false r m srow drow (4 * j) (4 * nfw) bs v ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                Rd Ev SOK E8 E5 R18 E28) as (r1 & RUN & Q18 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    set (m1 := wbytes m _ _).
    assert (WP : W C A m1 md /\ POSTM C Ar s m0 m1)
      by (subst m1; apply (WP_blk C Ar A m0 m _ (Z_to_bv 64 datad) _ nd _ s CK (conj HW PM) Ld Ld0 Ld00 SUB); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
    apply (IH C Ar A m0 md s S ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 datad nd datas ns srow drow nfw r0 m1 r1 (j + 1)%Z CK Hs16 ltac:(unfold ROPLOW_STACK; lia) Hhi SUB Ld Ld0 Ld00 Ls
             Hdd Hds Hnd Hns Hnfw Hd1 Hd2 Hs1 Hs2 ltac:(lia) ltac:(lia) (proj1 WP) (proj2 WP)).
    + apply (rlcells_frame m m1 s); [lia | lia | exact CE |]. intros x Hx. subst m1. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    + intros a Ha1 Ha2. subst m1. rewrite wbytes_outside by (rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia). exact (FT a Ha1 Ha2).
    + intros x Hx. rewrite (AG1 x Hx). exact (AG0 x Hx).
    + exact R8. + exact R5. + exact R28.
    + rewrite Q18. f_equal. lia.
    + exact KT.
Qed.

(* [comment removed for export] *)
Lemma rl_row_W : forall (n : nat) C Ar A m0 md (s : Z) (S : TSet) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word)
    (datad nd datas ns psf pdf nfw k DW dh swpl dwpl : Z) m r (i : Z),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  sub_live Ar A -> live A (Z_to_bv 64 datad) = Some nd -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some ns -> (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z -> (0 < nd)%Z -> (0 < ns)%Z ->
  (1 <= DW < 2 ^ 31)%Z -> (DW = 32 * nfw + k)%Z -> (0 <= k < 32)%Z -> (0 <= nfw < 2 ^ 26)%Z -> (1 <= dh < 2 ^ 24)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= pdf + 4 * dwpl * i')%Z /\ (pdf + 4 * dwpl * i' + 4 * (nfw + (if Z.eq_dec k 0 then 0 else 1)) <= datad + nd)%Z) ->
  (forall i', (0 <= i' < dh)%Z -> (datas <= psf + 4 * swpl * i')%Z /\ (psf + 4 * swpl * i' + 4 * (nfw + (if Z.eq_dec k 0 then 0 else 1)) <= datas + ns)%Z) ->
  (Z.of_nat n = dh - 1 - i)%Z -> (0 <= i < dh)%Z ->
  W C A m md -> POSTM C Ar s m0 m -> rlcells m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m a = m0 a) ->
  getr r 2 = Z_to_bv 64 (s - 112) -> getr r 10 = Z_to_bv 64 i -> getr r 5 = Z_to_bv 64 (pdf + 4 * dwpl * i) -> getr r 8 = Z_to_bv 64 (psf + 4 * swpl * i) ->
  getr r 6 = Z_to_bv 64 DW -> getr r 31 = Z_to_bv 64 32 -> getr r 12 = Z_to_bv 64 dh -> getr r 13 = Z_to_bv 64 swpl -> getr r 14 = Z_to_bv 64 dwpl ->
  getr r 15 = Z_to_bv 64 k -> getr r 16 = Z_to_bv 64 psf -> getr r 17 = Z_to_bv 64 pdf -> getr r 29 = Z_to_bv 64 (4 * dwpl) -> getr r 30 = Z_to_bv 64 (4 * swpl) ->
  (1 <= nfw -> getr r 28 = Z_to_bv 64 (4 * nfw))%Z ->
  (forall m' r', W C A m' md -> POSTM C Ar s m0 m' -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m' a = m0 a) -> getr r' 2 = Z_to_bv 64 s -> getr r' 1 = ret ->
     getr r' 8 = v0 -> getr r' 9 = v1 -> getr r' 18 = v2 -> getr r' 19 = v3 -> getr r' 20 = v4 -> getr r' 21 = v5 -> getr r' 22 = v6 -> getr r' 23 = v7 -> getr r' 24 = v8 -> getr r' 25 = v9 -> getr r' 26 = v10 -> getr r' 27 = v11 -> getr r' 3 = getr r 3 -> getr r' 4 = getr r 4 ->
     realizes SEGS (mkCfg (mkst r' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x1dc50 : word) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ar A m0 md s S ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 datad nd datas ns psf pdf nfw k DW dh swpl dwpl m r i
    CK Hs16 Hlo Hhi Hret SUB Ld Ld0 Ld00 Ls Hdd Hds Hnd Hns HDW EDW Hk Hnfw Hdh Hsw Hdw GD GS Hn Hi HW PM CE FT
    R2 R10 R5 R8 R6 R31 R12 R13 R14 R15 R16 R17 R29 R30 R28 KF;
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LL16] in *;
    assert (Hlo' : (c_top C - LSTK + 240 <= s)%Z) by (unfold ROPLOW_STACK in Hlo; exact Hlo);
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    destruct (GD i Hi) as [GD1 GD2]; destruct (GS i Hi) as [GS1 GS2];
    set (drow := (pdf + 4 * dwpl * i)%Z) in *; set (srow := (psf + 4 * swpl * i)%Z) in *;
    (* [comment removed for export] *)
    assert (TAIL : forall m' r', W C A m' md -> POSTM C Ar s m0 m' -> rlcells m' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m' a = m0 a) ->
               regs_agree (fun x => In x [9; 18; 19]%list) r r' ->
               realizes SEGS (mkCfg (mkst r' (0x1dc3c : word) m' al_rom) md) S).
  all: lazymatch goal with |- forall _ : word -> option byte, _ => idtac | _ => shelve end.
  all: intros m' r' HW' PM' CE' FT' AG';
       assert (E2 : getr r' 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity);
       assert (E10 : getr r' 10 = Z_to_bv 64 i) by (csr; reflexivity);
       assert (E12 : getr r' 12 = Z_to_bv 64 dh) by (csr; reflexivity);
       assert (E5 : getr r' 5 = Z_to_bv 64 drow) by (csr; reflexivity);
       assert (E8 : getr r' 8 = Z_to_bv 64 srow) by (csr; reflexivity);
       assert (E29 : getr r' 29 = Z_to_bv 64 (4 * dwpl)) by (csr; reflexivity);
       assert (E30 : getr r' 30 = Z_to_bv 64 (4 * swpl)) by (csr; reflexivity).
  1: { (* [comment removed for export] *)
    destruct (rl_N2 al_rom r' m' s i dh ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret CE' E2 E10 E12)
      as (r2 & RUN2 & Q2 & Q1 & QV0 & QV1 & QV2 & QV3 & QV4 & QV5 & QV6 & QV7 & QV8 & QV9 & QV10 & QV11 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |].
    apply (KF m' r2 HW' PM' FT' Q2 Q1); try assumption; csr; reflexivity. }
  1: { (* [comment removed for export] *)
    destruct (rl_N1 al_rom r' m' i dh srow drow (4 * swpl) (4 * dwpl) ltac:(lia) ltac:(lia) ltac:(lia) E10 E12 E5 E8 E29 E30)
      as (r2 & RUN2 & Q10 & Q5 & Q8 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |].
    apply (IH C Ar A m0 md s S ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 datad nd datas ns psf pdf nfw k DW dh swpl dwpl m' r2 (i + 1)%Z
             CK Hs16 Hlo Hhi Hret SUB Ld Ld0 Ld00 Ls Hdd Hds Hnd Hns HDW EDW Hk Hnfw Hdh Hsw Hdw GD GS ltac:(lia) ltac:(lia) HW' PM' CE' FT');
      try (csr; reflexivity).
    + rewrite Q5. subst drow. f_equal. lia.
    + rewrite Q8. subst srow. f_equal. lia.
    + intros Hn1. csr. exact (R28 Hn1).
    + intros m'' r'' HW'' PM'' FT'' Z2 Z1 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 Z3 Z4. apply (KF m'' r'' HW'' PM'' FT'' Z2 Z1 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11); [rewrite Z3 | rewrite Z4]; csr; reflexivity. }
  Unshelve.
  all: (* [comment removed for export] *)
    assert (PART : forall m' r' (pd ps : Z), W C A m' md -> POSTM C Ar s m0 m' -> rlcells m' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m' a = m0 a) ->
               regs_agree (fun x => In x [9; 18; 19]%list) r r' ->
               (datad <= pd)%Z -> (pd + 4 <= datad + nd)%Z -> (datas <= ps)%Z -> (ps + 4 <= datas + ns)%Z ->
               getr r' 9 = Z_to_bv 64 pd -> getr r' 18 = Z_to_bv 64 ps ->
               realizes SEGS (mkCfg (mkst r' (0x1dc24 : word) m' al_rom) md) S);
    [ intros m' r' pd ps HW' PM' CE' FT' AG' P1 P2 P3 P4 E9 E18;
      destruct (blk_range C A m' md (Z_to_bv 64 datad) nd CK HW' Ld Hnd) as [Gd TOPd]; rewrite u_Z2bv in Gd, TOPd by lia;
      destruct (blk_range C A m' md (Z_to_bv 64 datas) ns CK HW' Ls Hns) as [Gs TOPs]; rewrite u_Z2bv in Gs, TOPs by lia;
      destruct (W_rd4_blk C A m' md (Z_to_bv 64 datad) nd pd CK HW' Ld ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)) as (bd & vd & Rd & Evd);
      destruct (W_rd4_blk C A m' md (Z_to_bv 64 datas) ns ps CK HW' Ls ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)) as (bsr & vs & Rs & Evs);
      pose proof (W_sok_blk C A m' md (Z_to_bv 64 datad) nd pd 4 CK HW' Ld ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia)) as SOK;
      destruct (rl_P al_rom r' m' pd ps bd bsr vd vs ltac:(lia) ltac:(lia) Rd Evd Rs Evs SOK E9 E18) as (r2 & w & RUN2 & AG2);
      (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]);
      set (m2 := wbytes m' _ _);
      assert (WP : W C A m2 md /\ POSTM C Ar s m0 m2)
        by (subst m2; apply (WP_blk C Ar A m0 m' _ (Z_to_bv 64 datad) _ nd _ s CK (conj HW' PM') Ld Ld0 Ld00 SUB); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia);
      apply (TAIL m2 r2 (proj1 WP) (proj2 WP));
      [ apply (rlcells_frame m' m2 s); [lia | lia | exact CE' |]; intros x Hx; subst m2; apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
      | intros a Ha1 Ha2; subst m2; rewrite wbytes_outside by (rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia); exact (FT' a Ha1 Ha2)
      | intros x Hx; rewrite (AG2 x ltac:(intros X; apply Hx; cbv in X |- *; intuition)); exact (AG' x Hx) ]
    |].
  all: destruct (Z_lt_ge_dec DW 32) as [SMALL | BIG].
  1,3: (* [comment removed for export] *)
    assert (Ek : k = DW) by lia; assert (En0 : nfw = 0%Z) by lia;
    destruct (Z.eq_dec k 0) as [K0|K0]; [lia|];
    destruct (rl_S al_rom r m DW i swpl dwpl psf pdf k ltac:(lia) ltac:(lia) ltac:(lia) Hsw Hdw R6 R31 R10 R13 R14 R16 R17 R15)
      as (r1 & RUN1 & Q9 & Q18 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]);
    apply (PART m r1 (pdf + 4 * (i * dwpl))%Z (psf + 4 * (i * swpl))%Z HW PM CE FT AG1); subst drow srow; try lia; assumption.
  all: (* [comment removed for export] *)
    assert (Hn1 : (1 <= nfw)%Z) by lia;
    destruct (rl_Hf al_rom r m DW ltac:(lia) R6 R31) as (r1 & RUN1 & Q18 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]);
    apply (rl_inner_W (Z.to_nat (nfw - 1)) C Ar A m0 md s S ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 datad nd datas ns srow drow nfw r1 m r1 0
             CK Hs16 Hlo Hhi SUB Ld Ld0 Ld00 Ls Hdd Hds Hnd Hns ltac:(lia)
             ltac:(subst drow; lia) ltac:(subst drow; destruct (Z.eq_dec k 0); lia) ltac:(subst srow; lia) ltac:(subst srow; destruct (Z.eq_dec k 0); lia)
             ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) HW PM CE FT ltac:(intros x Hx; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; exact (R28 Hn1)) ltac:(rewrite Q18; reflexivity));
    intros m' r' HW' PM' CE' FT' AG' E18;
    assert (AGr : regs_agree (fun x => In x [9; 18; 19]%list) r r')
      by (intros x Hx; rewrite (AG' x Hx); apply AG1; intros X; apply Hx; cbv in X |- *; intuition);
    destruct (rl_T al_rom r' m' srow drow (4 * nfw) k Hk ltac:(csr; reflexivity) ltac:(csr; reflexivity) E18 ltac:(csr; reflexivity))
      as (r2 & RUN2 & Q9 & Q18' & AG2);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]);
    assert (AGr2 : regs_agree (fun x => In x [9; 18; 19]%list) r r2)
      by (intros x Hx; rewrite (AG2 x ltac:(intros X; apply Hx; cbv in X |- *; intuition)); exact (AGr x Hx));
    destruct (Z.eq_dec k 0) as [K0|K0];
    [ exact (TAIL m' r2 HW' PM' CE' FT' AGr2)
    | apply (PART m' r2 (drow + 4 * nfw)%Z (srow + 4 * nfw)%Z HW' PM' CE' FT' AGr2); subst drow srow; try lia; assumption ].
Qed.

(* [comment removed for export] *)
Lemma lmask_rd : forall j, (1 <= j <= 31)%Z ->
  exists bs, rdn SEGS (fun _ => None) (Z_to_bv 64 (0x1193c + 4 * j)) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros j Hj.
  assert (E : (j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/
              j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31)%Z) by lia.
  clear Hj.
  repeat (destruct E as [-> | E]; [ lazymatch goal with |- exists bs, ?l = Some bs /\ _ =>
      let v := eval vm_compute in l in lazymatch v with Some ?bs => exists bs; split; [vm_compute; reflexivity | reflexivity] end end |]).
  subst j. lazymatch goal with |- exists bs, ?l = Some bs /\ _ =>
      let v := eval vm_compute in l in lazymatch v with Some ?bs => exists bs; split; [vm_compute; reflexivity | reflexivity] end end.
Qed.
Lemma jt_src_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 0x118ac) 4 = Some (Z_to_le_bytes 4 50004).
Proof. vm_refl_bv. Qed.

Theorem rasteropLow_W : rasteropLow_contract.
Proof.
  unfold rasteropLow_contract.
  intros C Ar A m md regs s datad dpixw dpixh d dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs RCd RCs ALd ALs Ld Ld0 Ld00 Ls NEsd HK.
  unfold PC_rasteropLow. replace (Z_to_bv 64 0x1cda8) with (0x1cda8 : word) by (apply bv_eq; reflexivity).
  destruct SHd as (Hd & Hdpw & Hdph & Ewd & Hszd). destruct SHs as (_ & Hspw & Hsph & Ews & Hszs).
  destruct RCd as (Hdx0 & Hdy0 & Hdw1 & Hdh1 & Hdxw & Hdyh). destruct RCs as (Hsx0 & Hsy0 & _ & _ & Hsxw & Hsyh).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LL16] in *. unfold ROPLOW_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (DV : dval d) by (unfold dval; lia).
  pose proof (wpl_of_range dpixw d ltac:(lia) DV) as Hwd. rewrite <- Ewd in Hwd.
  pose proof (wpl_of_range spixw d ltac:(lia) DV) as Hws. rewrite <- Ews in Hws.
  pose proof (wpl_bits dpixw d ltac:(lia) ltac:(lia)) as WBd. rewrite <- Ewd in WBd.
  pose proof (wpl_bits spixw d ltac:(lia) ltac:(lia)) as WBs. rewrite <- Ews in WBs.
  assert (Msy : (0 <= sy * swpl < 2 ^ 24)%Z) by (clear - Hszs Hsyh Hdh1 Hsy0 Hws; nia).
  assert (Mdy : (0 <= dy * dwpl < 2 ^ 24)%Z) by (clear - Hszd Hdyh Hdh1 Hdy0 Hwd; nia).
  set (nd := (4 * (dwpl * dpixh))%Z) in *. set (ns := (4 * (swpl * spixh))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; nia). assert (Hns : (0 < ns)%Z) by (subst ns; nia).
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [Gd TOPd].
  destruct (blk_range C A m md (Z_to_bv 64 datas) ns CK HW Ls Hns) as [Gs TOPs].
  pose proof (u64_range (Z_to_bv 64 datad)) as Udd. pose proof (u64_range (Z_to_bv 64 datas)) as Uds.
  (* [comment removed for export] *)
  set (DX := (dx * d)%Z). set (SX := (sx * d)%Z). set (DW := (dw * d)%Z).
  assert (HDX : (0 <= DX <= 160000)%Z) by (subst DX; nia). assert (HSX : (0 <= SX <= 160000)%Z) by (subst SX; nia).
  assert (HDW : (1 <= DW <= 160000)%Z) by (subst DW; nia).
  assert (HDXW : (DX + DW <= dpixw * d)%Z) by (subst DX DW; nia). assert (HSXW : (SX + DW <= spixw * d)%Z) by (subst SX DW; nia).
  assert (HDPW : (dpixw * d <= 160000)%Z) by nia. assert (HSPW : (spixw * d <= 160000)%Z) by nia.
  fold DX in ALd. fold SX in ALs.
  set (nfw := (DW / 32)%Z). set (k := (DW mod 32)%Z). set (cdx := (DX / 32)%Z). set (csx := (SX / 32)%Z).
  pose proof (Z.div_mod DW 32 ltac:(lia)) as EDW. fold nfw k in EDW. pose proof (Z.mod_pos_bound DW 32 ltac:(lia)) as Hk. fold k in Hk.
  pose proof (Z.div_mod DX 32 ltac:(lia)) as EDX. fold cdx in EDX. rewrite ALd in EDX.
  pose proof (Z.div_mod SX 32 ltac:(lia)) as ESX. fold csx in ESX. rewrite ALs in ESX.
  assert (Hnfw : (0 <= nfw < 2 ^ 26)%Z) by lia. assert (Hcdx : (0 <= cdx < 2 ^ 26)%Z) by lia. assert (Hcsx : (0 <= csx < 2 ^ 26)%Z) by lia.
  pose proof (col_bound DX DW dwpl cdx nfw k ltac:(lia) EDW Hk ltac:(lia)) as CBd.
  pose proof (col_bound SX DW swpl csx nfw k ltac:(lia) EDW Hk ltac:(lia)) as CBs.
  (* [comment removed for export] *)
  destruct (rl_A0 al_rom regs m s datad dpixw d dx dw spixw sx ret ltac:(lia) ltac:(lia) Hd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) Rspw Rsx H2 H1 H10 H11 H13 H15 H17)
    as (r0 & RUN0 & P2 & P5 & P11 & P15 & P17 & P6 & P7 & AG0).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN0 |].
  set (M1 := RLF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1) by (subst M1; unfold RLF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (rlcells_RLF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Rdh1 : rdn SEGS M1 (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh))) by (subst M1; rewrite rdn_RLF_above by (cbn; lia); exact Rdh).
  assert (Rop1 : rdn SEGS M1 (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 12))) by (subst M1; rewrite rdn_RLF_above by (cbn; lia); exact Rop).
  assert (Rdatas1 : rdn SEGS M1 (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas))) by (subst M1; rewrite rdn_RLF_above by (cbn; lia); exact Rdatas).
  assert (Rsph1 : rdn SEGS M1 (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh))) by (subst M1; rewrite rdn_RLF_above by (cbn; lia); exact Rsph).
  assert (Rswpl1 : rdn SEGS M1 (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))) by (subst M1; rewrite rdn_RLF_above by (cbn; lia); exact Rswpl).
  assert (Rsy1 : rdn SEGS M1 (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy))) by (subst M1; rewrite rdn_RLF_above by (cbn; lia); exact Rsy).
  (* [comment removed for export] *)
  fold DX in P15. fold SX in P7. fold DW in P17.
  destruct (rl_A1 al_rom r0 M1 DX SX DW (dpixw * d)%Z (spixw * d)%Z ltac:(lia) ltac:(lia) ltac:(lia) HDXW HSXW HDPW HSPW P15 P7 P17 P11 P6)
    as (r1 & RUN1 & Q19 & Q26 & Q6 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN1 |].
  destruct (rl_A2 al_rom r1 M1 s dy sy dh dpixh spixh ltac:(lia) ltac:(lia) Hdy0 Hsy0 Hdh1 Hdyh Hsyh ltac:(lia) ltac:(lia) Rdh1 Rsph1 Rsy1
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r2 & RUN2 & Q27 & Q23 & Q12 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  (* [comment removed for export] *)
  destruct (rl_A3a al_rom r2 M1 s DX SX swpl datas ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALd ALs Rop1 Rdatas1 Rswpl1
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r3 & RUN3 & Q13 & Q22 & Q21 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
  assert (TBL : forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS M1 (Z_to_bv 64 (0x1193c + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v).
  { intros j Hj. destruct (lmask_rd j Hj) as (bs & Rb & Lb). destruct (le4_word bs Lb) as (v & Ev). exists bs, v. split; [|exact Ev].
    rewrite <- p16_segs. rewrite (W_rdn_ro C A M1 md (0x1193c + 4 * j) 4 HW1) by (cbn; lia). rewrite p16_segs. exact Rb. }
  assert (X6 : getr r3 6 = Z_to_bv 64 DW) by (csr; reflexivity).
  pose proof (rl_A3b al_rom r3 M1 DW k ltac:(lia) eq_refl Hk TBL X6) as XA3b. destruct XA3b as (r4 & RUN4 & Q15 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
  assert (JT : rdn SEGS M1 (Z_to_bv 64 0x118ac) 4 = Some (Z_to_le_bytes 4 50004)).
  { rewrite <- p16_segs. rewrite (W_rdn_ro C A M1 md 0x118ac 4 HW1) by (cbn; lia). rewrite p16_segs. exact jt_src_rd. }
  pose proof (rl_A3c al_rom r4 M1 DW DX SX sy dy swpl dwpl datas datad nfw cdx csx (getr r4 7) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl eq_refl eq_refl Hnfw Hcdx Hcsx
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) JT
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) eq_refl)
    as XA3c. destruct XA3c as (r5 & RUN5 & V10 & V5 & V17 & V8 & V16 & V29 & V30 & V31 & V28 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN5 |].
  (* [comment removed for export] *)
  set (pdf := (datad + 4 * (dy * dwpl) + 4 * cdx)%Z) in *. set (psf := (datas + 4 * (sy * swpl) + 4 * csx)%Z) in *.
  rewrite u_Z2bv in Gd, TOPd, Gs, TOPs by lia.
  apply (rl_row_W (Z.to_nat (dh - 1)) C Ar A m md s S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) datad nd datas ns psf pdf nfw k DW dh swpl dwpl M1 r5 0
           CK Hs16 ltac:(unfold ROPLOW_STACK; lia) ltac:(lia) Hret SUB Ld Ld0 Ld00 Ls ltac:(lia) ltac:(lia) Hnd Hns ltac:(lia) EDW Hk Hnfw ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros i' Hi'. subst pdf nd. apply (rop_rows_in datad dwpl dpixh dy dh cdx (nfw + (if Z.eq_dec k 0 then 0 else 1))%Z i'); try lia. destruct (Z.eq_dec k 0); lia.
  - intros i' Hi'. subst psf ns. apply (rop_rows_in datas swpl spixh sy dh csx (nfw + (if Z.eq_dec k 0 then 0 else 1))%Z i'); try lia. destruct (Z.eq_dec k 0); lia.
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - exact HW1.
  - exact PM1.
  - exact CE1.
  - intros a Ha1 Ha2. subst M1. apply RLF_outside; [lia | lia |]. intros X. apply Ha1. unfold scratch. lia.
  - csr. reflexivity.
  - exact V10.
  - rewrite V5. f_equal. lia.
  - rewrite V8. f_equal. lia.
  - csr. reflexivity.
  - exact V31.
  - csr. reflexivity.
  - csr. reflexivity.
  - csr. reflexivity.
  - csr. reflexivity.
  - exact V16.
  - exact V17.
  - exact V29.
  - exact V30.
  - exact V28.
  - intros m' r' HW' PM' FT' Z2 Z1 Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 Z3 Z4.
    apply (HK m' r' HW'); [| exact PM' | exact FT'].
    apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | rewrite Z3; csr; reflexivity | rewrite Z4; csr; reflexivity | assumption ].
Qed.

End RopLowW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
