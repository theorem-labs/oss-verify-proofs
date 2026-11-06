(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MemsetFill_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptStderr O14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL7a.
Import O14CL7a.O14LeptRop_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14_code_gmB O14LeptRopLow.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
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

Ltac condS := pin; rewrite c_eq_Z0s by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma ru_A0 : forall regs m (s dpixw d dwpl dx dw : Z) (ret : word),
  (112 <= s)%Z -> (s + 16 < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z ->
  (0 <= dpixw <= 20000)%Z -> (0 <= dx <= 20000)%Z -> (0 <= dw <= 20000)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 11 = Z_to_bv 64 dpixw ->
  getr regs 13 = Z_to_bv 64 d -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 17 = Z_to_bv 64 dw ->
  exists regs',
    msteps SEGS (mkst regs (0x1c8c0 : word) m rom) (mkst regs' (0x1c908 : word) (RLF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 dwpl /\ getr regs' 11 = Z_to_bv 64 (dpixw * d)
    /\ getr regs' 14 = Z_to_bv 64 (dx * d) /\ getr regs' 13 = Z_to_bv 64 (dw * d)
    /\ regs_agree (fun r => In r [2; 8; 11; 13; 14]%list) regs regs'.
Proof.
  intros regs m s dpixw d dwpl dx dw ret Hs Hs64 Hd Hdpw Hdx Hdw SOK H2 H1 H11 H13 H14 H15 H17.
  eexists. split.
  - zv F_1c7c4 D_1c7c4 (Z_to_bv 64 (s - 112)).
    stepST F_1c7c8 D_1c7c8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_1c7cc D_1c7cc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_1c7d0 D_1c7d0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_1c7d4 D_1c7d4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_1c7d8 D_1c7d8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_1c7dc D_1c7dc (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_1c7e0 D_1c7e0 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_1c7e4 D_1c7e4 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_1c7e8 D_1c7e8 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_1c7ec D_1c7ec (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_1c7f0 D_1c7f0 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    stepST F_1c7f4 D_1c7f4 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
    stepST F_1c7f8 D_1c7f8 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
    sn F_1c7fc D_1c7fc.
    sn F_1c800 D_1c800. fixv' (Z_to_bv 64 (dpixw * d)) ltac:(rewrite zbv_mul; f_equal; lia).
    sn F_1c804 D_1c804. fixv' (Z_to_bv 64 (dx * d)) ltac:(rewrite zbv_mulw_small by nia; reflexivity).
    sn F_1c808 D_1c808. fixv' (Z_to_bv 64 (dw * d)) ltac:(rewrite zbv_mul; f_equal; lia).
    unfold RLF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_A1 : forall regs m (DX DW DPW : Z),
  (0 <= DX)%Z -> (1 <= DW)%Z -> (DX + DW <= DPW)%Z -> (DPW <= 160000)%Z ->
  getr regs 14 = Z_to_bv 64 DX -> getr regs 13 = Z_to_bv 64 DW -> getr regs 11 = Z_to_bv 64 DPW ->
  exists regs',
    msteps SEGS (mkst regs (0x1c908 : word) m rom) (mkst regs' (0x1c93c : word) m rom)
    /\ getr regs' 13 = Z_to_bv 64 DX /\ getr regs' 18 = Z_to_bv 64 DW
    /\ regs_agree (fun r => In r [11; 13; 14; 15; 18]%list) regs regs'.
Proof.
  intros regs m DX DW DPW H0 H1 Hov Hc H14 H13 H11. eexists. split.
  - sn F_1c80c D_1c80c. fz. sn F_1c810 D_1c810. fz. sn F_1c814 D_1c814. fadd DW.
    sn F_1c818 D_1c818. fbit DX. sn F_1c81c D_1c81c. fmsk DX. sn F_1c820 D_1c820. fmax DX.
    sn F_1c824 D_1c824. fsubw (DX - DPW)%Z. sn F_1c828 D_1c828. faddw (DX - DPW + DW)%Z.
    sn F_1c82c D_1c82c. fz. sn F_1c830 D_1c830. fz. sn F_1c834 D_1c834. fz. sn F_1c838 D_1c838. fsubw DW.
    stepb_ft F_1c83c D_1c83c ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_A2 : forall regs m (s dy dh dpixh : Z),
  (112 <= s)%Z -> (s + 16 < 2 ^ 64)%Z ->
  (0 <= dy)%Z -> (1 <= dh)%Z -> (dy + dh <= dpixh)%Z -> (dpixh <= 20000)%Z ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 16 = Z_to_bv 64 dy -> getr regs 12 = Z_to_bv 64 dpixh ->
  exists regs',
    msteps SEGS (mkst regs (0x1c93c : word) m rom) (mkst regs' (0x1c974 : word) m rom)
    /\ getr regs' 14 = Z_to_bv 64 dy /\ getr regs' 19 = Z_to_bv 64 dh
    /\ regs_agree (fun r => In r [11; 12; 14; 15; 17; 19]%list) regs regs'.
Proof.
  intros regs m s dy dh dpixh Hs Hs64 H0 H1 Hov Hc Rdh H2 H16 H12. eexists. split.
  - stepLD F_1c840 D_1c840 (word_to_le_bytes 8 (Z_to_bv 64 dh)) (Z_to_bv 64 dh) ltac:(addr_norm; rewrite ?Z.sub_0_r; exact Rdh) ltac:(apply bytes_le_to_Z_8).
    sn F_1c844 D_1c844. fz. sn F_1c848 D_1c848. fbit dy. sn F_1c84c D_1c84c. fz.
    sn F_1c850 D_1c850. fmsk dy. sn F_1c854 D_1c854. fmax dy. sn F_1c858 D_1c858. fadd dh.
    sn F_1c85c D_1c85c. fsubw (dy - dpixh)%Z. sn F_1c860 D_1c860. faddw (dy - dpixh + dh)%Z.
    sn F_1c864 D_1c864. fz. sn F_1c868 D_1c868. fz. sn F_1c86c D_1c86c. fz. sn F_1c870 D_1c870. fsubw dh.
    stepb_ft F_1c874 D_1c874 ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_A3 : forall regs m (s op DX dy dwpl a6 cdx : Z),
  (112 <= s)%Z -> (s + 16 < 2 ^ 64)%Z -> (0 <= DX < 2 ^ 31)%Z -> a6 = (DX mod 32)%Z -> cdx = (DX / 32)%Z ->
  (0 <= dy < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z -> (0 <= dy * dwpl < 2 ^ 24)%Z ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 13 = Z_to_bv 64 DX -> getr regs 14 = Z_to_bv 64 dy -> getr regs 8 = Z_to_bv 64 dwpl ->
  exists regs',
    msteps SEGS (mkst regs (0x1c974 : word) m rom) (mkst regs' (if Z.eq_dec a6 0 then (0x1ca4c : word) else (0x1c988 : word)) m rom)
    /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 16 = Z_to_bv 64 a6 /\ getr regs' 15 = Z_to_bv 64 (dy * dwpl) /\ getr regs' 14 = Z_to_bv 64 cdx
    /\ regs_agree (fun r => In r [11; 14; 15; 16]%list) regs regs'.
Proof.
  intros regs m s op DX dy dwpl a6 cdx Hs Hs64 HDX Ea6 Ecdx Hdy Hdwpl Hm Rop H2 H13 H14 H8.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)) as Ha6. rewrite <- Ea6 in Ha6.
  destruct (Z.eq_dec a6 0) as [E|NE]; eexists; (split; [
    stepLD F_1c878 D_1c878 (word_to_le_bytes 8 (Z_to_bv 64 op)) (Z_to_bv 64 op) ltac:(addr_norm; exact Rop) ltac:(apply bytes_le_to_Z_8);
    sn F_1c87c D_1c87c; fixv' (Z_to_bv 64 a6) ltac:(rewrite andi_31_Z by lia; rewrite <- Ea6; reflexivity);
    sn F_1c880 D_1c880; fixv' (Z_to_bv 64 (dy * dwpl)) ltac:(rewrite zbv_mulw_small by lia; reflexivity);
    sn F_1c884 D_1c884; fixv' (Z_to_bv 64 cdx) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Ecdx; reflexivity) |]).
  - stepb_tk F_1c888 D_1c888 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_ft F_1c888 D_1c888 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ru_M : forall regs m (DW k : Z),
  (1 <= DW < 2 ^ 31)%Z -> k = (DW mod 32)%Z -> (0 <= k < 32)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x1170c + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 18 = Z_to_bv 64 DW ->
  exists regs',
    msteps SEGS (mkst regs (0x1ca4c : word) m rom) (mkst regs' (0x1cb80 : word) m rom)
    /\ getr regs' 20 = Z_to_bv 64 k
    /\ regs_agree (fun r => In r [12; 13; 20; 22]%list) regs regs'.
Proof.
  intros regs m DW k HDW Ek Hk TBL H18.
  destruct (Z.eq_dec k 0) as [E0 | NE0].
  - eexists. split.
    + sn F_1c950 D_1c950. fixv' (Z_to_bv 64 k) ltac:(rewrite andi_31_Z by lia; rewrite <- Ek; reflexivity).
      stepb_tk F_1c954 D_1c954 ltac:(condZ).
      apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - destruct (TBL k ltac:(lia)) as (bs & v & Rv & Ev).
    eexists. split.
    + sn F_1c950 D_1c950. fixv' (Z_to_bv 64 k) ltac:(rewrite andi_31_Z by lia; rewrite <- Ek; reflexivity).
      stepb_ft F_1c954 D_1c954 ltac:(condZ).
      sn F_1c958 D_1c958. fixv' (Z_to_bv 64 (4 * k)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
      sn F_1c95c D_1c95c. sn F_1c960 D_1c960. sn F_1c964 D_1c964.
      fixv' (Z_to_bv 64 (0x1170c + 4 * k)) ltac:(vclose).
      stepLD F_1c968 D_1c968 bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev).
      sn F_1c96c D_1c96c.
      apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_S : forall (set : bool) regs m (DW nfw op datad dyw cdx : Z),
  (1 <= DW < 2 ^ 31)%Z -> nfw = (DW / 32)%Z -> op = (if set then 15 else 0)%Z -> (0 <= dyw < 2 ^ 24)%Z -> (0 <= cdx < 2 ^ 26)%Z ->
  getr regs 18 = Z_to_bv 64 DW -> getr regs 11 = Z_to_bv 64 op -> getr regs 10 = Z_to_bv 64 datad -> getr regs 15 = Z_to_bv 64 dyw -> getr regs 14 = Z_to_bv 64 cdx ->
  exists regs',
    msteps SEGS (mkst regs (0x1cb80 : word) m rom) (mkst regs' (if set then (0x1cc58 : word) else (0x1cce4 : word)) m rom)
    /\ getr regs' 12 = Z_to_bv 64 nfw /\ getr regs' 21 = Z_to_bv 64 (datad + 4 * dyw + 4 * cdx)
    /\ regs_agree (fun r => In r [12; 13; 21]%list) regs regs'.
Proof.
  intros set regs m DW nfw op datad dyw cdx HDW Enf Eop Hdyw Hcdx H18 H11 H10 H15 H14.
  destruct set; subst op; eexists; (split; [
    sn F_1ca84 D_1ca84; fixv' (Z_to_bv 64 nfw) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Enf; reflexivity);
    sn F_1ca88 D_1ca88; fixv' (Z_to_bv 64 (4 * dyw)) ltac:(rewrite zbv_slli by lia; f_equal; lia);
    sn F_1ca8c D_1ca8c; fixv' (Z_to_bv 64 (datad + 4 * dyw)) ltac:(rewrite zbv_add; reflexivity);
    sn F_1ca90 D_1ca90; fixv' (Z_to_bv 64 (4 * cdx)) ltac:(rewrite zbv_slli by lia; f_equal; lia);
    sn F_1ca94 D_1ca94; fixv' (Z_to_bv 64 (datad + 4 * dyw + 4 * cdx)) ltac:(rewrite zbv_add; reflexivity) |]).
  - stepb_ft F_1ca98 D_1ca98 ltac:(condZ). sn F_1ca9c D_1ca9c. stepb_tk F_1caa0 D_1caa0 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_tk F_1ca98 D_1ca98 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition pcA_head (set : bool) : word := if set then 0x1ccac else 0x1cd38.
Definition pcA_part (set : bool) : word := if set then 0x1ccd0 else 0x1cd58.
Definition pcA_next (set : bool) : word := if set then 0x1cc9c else 0x1cd28.

(* [comment removed for export] *)
Lemma ru_S2 : forall (set : bool) regs m (s datad dyw cdx nfw dh dwpl : Z),
  (112 <= s < 2 ^ 64)%Z -> (0 <= dh < 2 ^ 31)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 datad -> getr regs 15 = Z_to_bv 64 dyw -> getr regs 14 = Z_to_bv 64 cdx ->
  getr regs 12 = Z_to_bv 64 nfw -> getr regs 19 = Z_to_bv 64 dh -> getr regs 8 = Z_to_bv 64 dwpl ->
  exists regs' (cw : word),
    msteps SEGS (mkst regs (if set then (0x1cc58 : word) else (0x1cce4 : word)) m rom)
                (mkst regs' (pcA_head set) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 cw)) rom)
    /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 25 = Z_to_bv 64 (0 - dh) /\ getr regs' 27 = Z_to_bv 64 32
    /\ getr regs' 9 = len4 nfw
    /\ getr regs' (if set then 24 else 22) = Z_to_bv 64 (datad + 4 * (cdx + dyw))
    /\ (if set then cw else getr regs' 24) = v_add (len4 nfw) (Z_to_bv 64 (datad + 4 * (cdx + dyw)))
    /\ regs_agree (fun r => In r [9; 10; 11; 12; 14; 19; 22; 23; 24; 25; 27]%list) regs regs'.
Proof.
  intros set regs m s datad dyw cdx nfw dh dwpl Hs Hdh Hdwpl SOK H2 H10 H15 H14 H12 H19 H8.
  destruct set; eexists; eexists; (split; [| ]).
  - sn F_1cb5c D_1cb5c.
    sn F_1cb60 D_1cb60. fixv' (Z_to_bv 64 (cdx + dyw)) ltac:(rewrite zbv_add; reflexivity).
    sn F_1cb64 D_1cb64. fixv' (Z_to_bv 64 (nfw - 1)) ltac:(rewrite zbv_addi; f_equal; lia).
    sn F_1cb68 D_1cb68.
    sn F_1cb6c D_1cb6c. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cb70 D_1cb70. fixv' (Z_to_bv 64 (4 * (cdx + dyw))) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cb74 D_1cb74.
    sn F_1cb78 D_1cb78. fixv' (Z_to_bv 64 dh) ltac:(apply zext32_id; lia).
    sn F_1cb7c D_1cb7c. fixv' (Z_to_bv 64 (datad + 4 * (cdx + dyw))) ltac:(rewrite zbv_add; reflexivity).
    sn F_1cb80 D_1cb80.
    sn F_1cb84 D_1cb84. fixv' (Z_to_bv 64 (0 - dh)) ltac:(rewrite zbv_sub; reflexivity).
    sn F_1cb88 D_1cb88. fold (len4 nfw).
    sn F_1cb8c D_1cb8c.
    sn F_1cb90 D_1cb90.
    stepST F_1cb94 D_1cb94 (Z_to_bv 64 (s - 112)) (v_add (len4 nfw) (Z_to_bv 64 (datad + 4 * (cdx + dyw)))) ltac:(sok_in SOK).
    sn F_1cb98 D_1cb98.
    sn F_1cb9c D_1cb9c.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1cbe8 D_1cbe8.
    sn F_1cbec D_1cbec.
    stepST F_1cbf0 D_1cbf0 (Z_to_bv 64 (s - 112)) (v_xori (getr regs 22) (-1)) ltac:(sok_in SOK).
    sn F_1cbf4 D_1cbf4. fixv' (Z_to_bv 64 (cdx + dyw)) ltac:(rewrite zbv_add; reflexivity).
    sn F_1cbf8 D_1cbf8. fixv' (Z_to_bv 64 (nfw - 1)) ltac:(rewrite zbv_addi; f_equal; lia).
    sn F_1cbfc D_1cbfc.
    sn F_1cc00 D_1cc00. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cc04 D_1cc04. fixv' (Z_to_bv 64 (4 * (cdx + dyw))) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cc08 D_1cc08.
    sn F_1cc0c D_1cc0c. fixv' (Z_to_bv 64 dh) ltac:(apply zext32_id; lia).
    sn F_1cc10 D_1cc10. fixv' (Z_to_bv 64 (datad + 4 * (cdx + dyw))) ltac:(rewrite zbv_add; reflexivity).
    sn F_1cc14 D_1cc14.
    sn F_1cc18 D_1cc18. fixv' (Z_to_bv 64 (0 - dh)) ltac:(rewrite zbv_sub; reflexivity).
    sn F_1cc1c D_1cc1c. fold (len4 nfw).
    sn F_1cc20 D_1cc20.
    sn F_1cc24 D_1cc24.
    sn F_1cc28 D_1cc28.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ru_Hs : forall (set : bool) regs m (DW : Z) (rowp : word), (1 <= DW < 32)%Z ->
  getr regs 18 = Z_to_bv 64 DW -> getr regs 27 = Z_to_bv 64 32 -> getr regs 21 = rowp ->
  exists regs', msteps SEGS (mkst regs (pcA_head set) m rom) (mkst regs' (pcA_part set) m rom)
    /\ getr regs' 26 = rowp /\ regs_agree (fun r => In r [26]%list) regs regs'.
Proof.
  intros set regs m DW rowp HDW H18 H27 H21. unfold pcA_head, pcA_part. destruct set; eexists; (split; [|]).
  - sn F_1cbb0 D_1cbb0. stepb_tk F_1cbb4 D_1cbb4 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1cc3c D_1cc3c. stepb_tk F_1cc40 D_1cc40 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_Hb : forall (set : bool) regs m (s DW iw pf pf4 : Z) (n4 : word),
  (112 <= s < 2 ^ 64)%Z -> (32 <= DW < 2 ^ 31)%Z -> (0 <= iw < 2 ^ 24)%Z ->
  (if set then rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pf4)) else getr regs 24 = Z_to_bv 64 pf4) ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 18 = Z_to_bv 64 DW -> getr regs 27 = Z_to_bv 64 32 -> getr regs 23 = Z_to_bv 64 iw -> getr regs (if set then 24 else 22) = Z_to_bv 64 pf -> getr regs 9 = n4 ->
  exists regs', msteps SEGS (mkst regs (pcA_head set) m rom) (mkst regs' (0x2942c : word) m rom)
    /\ getr regs' 1 = pcA_part set /\ getr regs' 10 = Z_to_bv 64 (pf + 4 * iw) /\ getr regs' 11 = Z_to_bv 64 (if set then 255 else 0) /\ getr regs' 12 = n4
    /\ getr regs' 26 = Z_to_bv 64 (pf4 + 4 * iw)
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 26]%list) regs regs'.
Proof.
  intros set regs m s DW iw pf pf4 n4 Hs HDW Hiw Hpf4 H2 H18 H27 H23 Hpf H9. unfold pcA_head, pcA_part. destruct set; eexists; (split; [|]).
  - sn F_1cbb0 D_1cbb0. stepb_ft F_1cbb4 D_1cbb4 ltac:(condZ).
    sn F_1cbb8 D_1cbb8. fixv' (Z_to_bv 64 (4 * iw)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cbbc D_1cbbc. fixv' (Z_to_bv 64 (pf + 4 * iw)) ltac:(rewrite zbv_add; reflexivity).
    stepLD F_1cbc0 D_1cbc0 (word_to_le_bytes 8 (Z_to_bv 64 pf4)) (Z_to_bv 64 pf4) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Hpf4) ltac:(apply bytes_le_to_Z_8).
    sn F_1cbc4 D_1cbc4. fixv' (Z_to_bv 64 (pf4 + 4 * iw)) ltac:(rewrite zbv_add; reflexivity).
    sn F_1cbc8 D_1cbc8. sn F_1cbcc D_1cbcc.
    sn F_1cbd0 D_1cbd0.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  - sn F_1cc3c D_1cc3c. stepb_ft F_1cc40 D_1cc40 ltac:(condZ).
    sn F_1cc44 D_1cc44. fixv' (Z_to_bv 64 (4 * iw)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1cc48 D_1cc48. fixv' (Z_to_bv 64 (pf + 4 * iw)) ltac:(rewrite zbv_add; reflexivity).
    sn F_1cc4c D_1cc4c. fixv' (Z_to_bv 64 (pf4 + 4 * iw)) ltac:(rewrite zbv_add; reflexivity).
    sn F_1cc50 D_1cc50. sn F_1cc54 D_1cc54.
    sn F_1cc58 D_1cc58.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_P : forall (set : bool) regs m (s pd k : Z) (bd : list byte) (vd cw : word),
  (112 <= s < 2 ^ 64)%Z -> (0 <= pd < 2 ^ 64)%Z -> (1 <= k < 32)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> bytes_le_to_Z bd = bv_unsigned vd ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 cw) ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 26 = Z_to_bv 64 pd -> getr regs 20 = Z_to_bv 64 k ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (pcA_part set) m rom) (mkst regs' (pcA_next set) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof.
  intros set regs m s pd k bd vd cw Hs Hpd Hk Rd Evd Rc SOK H2 H26 H20. unfold pcA_part, pcA_next. destruct set; eexists; eexists; (split; [|]).
  - stepb_ft F_1cbd4 D_1cbd4 ltac:(condZ).
    stepLD F_1cbd8 D_1cbd8 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1cbdc D_1cbdc.
    stepST F_1cbe0 D_1cbe0 (Z_to_bv 64 pd) (v_or (v_lw vd) (getr regs 22)) ltac:(store_ok_peel; exact SOK).
    sn F_1cbe4 D_1cbe4.
    apply mst_refl.
  - gres. solve_regs_agree.
  - stepb_ft F_1cc5c D_1cc5c ltac:(condZ).
    stepLD F_1cc60 D_1cc60 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    stepLD F_1cc64 D_1cc64 (word_to_le_bytes 8 cw) cw ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rc) ltac:(apply bytes_le_to_Z_8).
    sn F_1cc68 D_1cc68.
    stepST F_1cc6c D_1cc6c (Z_to_bv 64 pd) (v_and (v_lw vd) cw) ltac:(store_ok_peel; exact SOK).
    sn F_1cc70 D_1cc70.
    apply mst_refl.
  - gres. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_P0 : forall (set : bool) regs m, getr regs 20 = Z_to_bv 64 0 ->
  exists regs', msteps SEGS (mkst regs (pcA_part set) m rom) (mkst regs' (pcA_next set) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof.
  intros set regs m H20. unfold pcA_part, pcA_next. destruct set; eexists; (split; [|]).
  - stepb_tk F_1cbd4 D_1cbd4 ltac:(condZ). apply mst_refl.
  - solve_regs_agree.
  - stepb_tk F_1cc5c D_1cc5c ltac:(condZ). apply mst_refl.
  - solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_N : forall (set last : bool) regs m (i dh iw dwpl rowp d4 : Z),
  (0 <= i)%Z -> (if last then i + 1 = dh else i + 1 < dh)%Z -> (dh < 2 ^ 31)%Z -> (0 <= iw)%Z -> (0 <= dwpl)%Z -> (iw + dwpl < 2 ^ 31)%Z ->
  getr regs 23 = Z_to_bv 64 iw -> getr regs 8 = Z_to_bv 64 dwpl -> getr regs 25 = Z_to_bv 64 (i - dh) -> getr regs 21 = Z_to_bv 64 rowp -> getr regs 19 = Z_to_bv 64 d4 ->
  exists regs', msteps SEGS (mkst regs (pcA_next set) m rom) (mkst regs' (if last then (0x1cb44 : word) else pcA_head set) m rom)
    /\ getr regs' 23 = Z_to_bv 64 (iw + dwpl) /\ getr regs' 25 = Z_to_bv 64 (i + 1 - dh) /\ getr regs' 21 = Z_to_bv 64 (rowp + d4)
    /\ regs_agree (fun r => In r [21; 23; 25]%list) regs regs'.
Proof.
  intros set last regs m i dh iw dwpl rowp d4 Hi HL Hdh Hiw Hdwpl Hsum H23 H8 H25 H21 H19. unfold pcA_next, pcA_head.
  destruct set; destruct last; eexists; (split; [|]).
  - sn F_1cba0 D_1cba0. faddw (iw + dwpl)%Z. sn F_1cba4 D_1cba4. fixv' (Z_to_bv 64 (i + 1 - dh)) ltac:(rewrite zbv_addi; f_equal; lia).
    sn F_1cba8 D_1cba8. fadd (rowp + d4)%Z. stepb_tk F_1cbac D_1cbac ltac:(condS). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1cba0 D_1cba0. faddw (iw + dwpl)%Z. sn F_1cba4 D_1cba4. fixv' (Z_to_bv 64 (i + 1 - dh)) ltac:(rewrite zbv_addi; f_equal; lia).
    sn F_1cba8 D_1cba8. fadd (rowp + d4)%Z. stepb_ft F_1cbac D_1cbac ltac:(condS). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1cc2c D_1cc2c. faddw (iw + dwpl)%Z. sn F_1cc30 D_1cc30. fixv' (Z_to_bv 64 (i + 1 - dh)) ltac:(rewrite zbv_addi; f_equal; lia).
    sn F_1cc34 D_1cc34. fadd (rowp + d4)%Z. stepb_tk F_1cc38 D_1cc38 ltac:(condS). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1cc2c D_1cc2c. faddw (iw + dwpl)%Z. sn F_1cc30 D_1cc30. fixv' (Z_to_bv 64 (i + 1 - dh)) ltac:(rewrite zbv_addi; f_equal; lia).
    sn F_1cc34 D_1cc34. fadd (rowp + d4)%Z. stepb_ft F_1cc38 D_1cc38 ltac:(condS). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_E : forall regs m (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
  rlcells m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  exists regs',
    msteps SEGS (mkst regs (0x1cb44 : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5 /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10 /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 Hret (C & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) R2.
  eexists. split.
  - stepLD8 F_1ca48 D_1ca48 ret. stepLD8 F_1ca4c D_1ca4c v0. stepLD8 F_1ca50 D_1ca50 v1. stepLD8 F_1ca54 D_1ca54 v2.
    stepLD8 F_1ca58 D_1ca58 v3. stepLD8 F_1ca5c D_1ca5c v4. stepLD8 F_1ca60 D_1ca60 v5. stepLD8 F_1ca64 D_1ca64 v6.
    stepLD8 F_1ca68 D_1ca68 v7. stepLD8 F_1ca6c D_1ca6c v8. stepLD8 F_1ca70 D_1ca70 v9. stepLD8 F_1ca74 D_1ca74 v10.
    stepLD8 F_1ca78 D_1ca78 v11.
    zv F_1ca7c D_1ca7c (Z_to_bv 64 s).
    stepret F_1ca80 D_1ca80 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ru_G0 : forall regs m (a6 DW datad dyw cdx : Z),
  (1 <= a6 < 32)%Z -> (1 <= DW < 2 ^ 31)%Z -> (0 <= dyw < 2 ^ 24)%Z -> (0 <= cdx < 2 ^ 26)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x11688 + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 16 = Z_to_bv 64 a6 -> getr regs 18 = Z_to_bv 64 DW -> getr regs 10 = Z_to_bv 64 datad -> getr regs 15 = Z_to_bv 64 dyw -> getr regs 14 = Z_to_bv 64 cdx ->
  exists regs',
    msteps SEGS (mkst regs (0x1c988 : word) m rom) (mkst regs' (if (DW <? 32 - a6)%Z then (0x1c9b8 : word) else (0x1ca6c : word)) m rom)
    /\ getr regs' 17 = Z_to_bv 64 (32 - a6) /\ getr regs' 10 = Z_to_bv 64 (datad + 4 * dyw + 4 * cdx)
    /\ regs_agree (fun r => In r [5; 10; 12; 14; 15; 17]%list) regs regs'.
Proof.
  intros regs m a6 DW datad dyw cdx Ha6 HDW Hdyw Hcdx TBL H16 H18 H10 H15 H14.
  destruct (TBL (32 - a6)%Z ltac:(lia)) as (bs & v & Rv & Ev).
  destruct (Z.ltb_spec DW (32 - a6)) as [LT|GE]; eexists; (split; [
    sn F_1c88c D_1c88c; sn F_1c890 D_1c890;
    sn F_1c894 D_1c894; fixv' (Z_to_bv 64 (32 - a6)) ltac:(rewrite zbv_sub; reflexivity);
    sn F_1c898 D_1c898;
    sn F_1c89c D_1c89c; fixv' (Z_to_bv 64 (4 * (32 - a6))) ltac:(rewrite zbv_slli by lia; f_equal; lia);
    sn F_1c8a0 D_1c8a0; fixv' (Z_to_bv 64 (0x11688 + 4 * (32 - a6))) ltac:(vclose);
    stepLD F_1c8a4 D_1c8a4 bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev);
    sn F_1c8a8 D_1c8a8; fixv' (Z_to_bv 64 (4 * dyw)) ltac:(rewrite zbv_slli by lia; f_equal; lia);
    sn F_1c8ac D_1c8ac; fixv' (Z_to_bv 64 (datad + 4 * dyw)) ltac:(rewrite zbv_add; reflexivity);
    sn F_1c8b0 D_1c8b0; fixv' (Z_to_bv 64 (4 * cdx)) ltac:(rewrite zbv_slli by lia; f_equal; lia);
    sn F_1c8b4 D_1c8b4; fixv' (Z_to_bv 64 (datad + 4 * dyw + 4 * cdx)) ltac:(rewrite zbv_add; reflexivity) |]).
  - stepb_ft F_1c8b8 D_1c8b8 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_tk F_1c8b8 D_1c8b8 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition pcG_l1s (set : bool) : word := if set then 0x1cab8 else 0x1c9fc.   (* [comment removed for export] *)
Definition pcG_l1 (set : bool) : word := if set then 0x1cac0 else 0x1ca08.    (* [comment removed for export] *)
Definition pcG_l1x (set : bool) : word := if set then 0x1cad8 else 0x1ca20.   (* [comment removed for export] *)
Definition pcG_l2 (set : bool) : word := if set then 0x1cddc else 0x1ce10.    (* [comment removed for export] *)
Definition pcG_l2r (set : bool) : word := if set then 0x1cdf0 else 0x1ce24.   (* [comment removed for export] *)
Definition pcG_l3t (set : bool) : word := if set then 0x1cae0 else 0x1ca24.   (* [comment removed for export] *)
Definition pcG_l3 (set : bool) : word := if set then 0x1cae4 else 0x1ca30.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ru_G1d : forall (set : bool) regs m (a6 DW op : Z),
  (1 <= a6 < 32)%Z -> (1 <= DW)%Z -> (DW < 32 - a6)%Z -> op = (if set then 15 else 0)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x1170c + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 16 = Z_to_bv 64 a6 -> getr regs 18 = Z_to_bv 64 DW -> getr regs 11 = Z_to_bv 64 op ->
  exists regs',
    msteps SEGS (mkst regs (0x1c9b8 : word) m rom) (mkst regs' (pcG_l1s set) m rom)
    /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 1 /\ getr regs' 22 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [9; 12; 13; 14; 20; 22; 23]%list) regs regs'.
Proof.
  intros set regs m a6 DW op Ha6 HDW HLT Eop TBL H16 H18 H11.
  destruct (TBL (DW + a6)%Z ltac:(lia)) as (bs & v & Rv & Ev). unfold pcG_l1s.
  destruct set; subst op; eexists; (split; [
    sn F_1c8bc D_1c8bc; sn F_1c8c0 D_1c8c0; sn F_1c8c4 D_1c8c4;
    sn F_1c8c8 D_1c8c8; faddw (DW + a6)%Z;
    sn F_1c8cc D_1c8cc;
    sn F_1c8d0 D_1c8d0; fixv' (Z_to_bv 64 (4 * (DW + a6))) ltac:(rewrite zbv_slli by lia; f_equal; lia);
    sn F_1c8d4 D_1c8d4;
    sn F_1c8d8 D_1c8d8; fixv' (Z_to_bv 64 (0x1170c + 4 * (DW + a6))) ltac:(vclose);
    stepLD F_1c8dc D_1c8dc bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev);
    sn F_1c8e0 D_1c8e0; sn F_1c8e4 D_1c8e4; sn F_1c8e8 D_1c8e8; sn F_1c8ec D_1c8ec |]).
  - stepb_tk F_1c8f0 D_1c8f0 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_ft F_1c8f0 D_1c8f0 ltac:(condZ). sn F_1c8f4 D_1c8f4. stepb_ft F_1c8f8 D_1c8f8 ltac:(condZ). stepb_ft F_1c8fc D_1c8fc ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_G1a : forall regs m (DW DX dfw pfp R lw2 : Z),
  (1 <= dfw < 32)%Z -> (dfw <= DW)%Z -> (DW <= 160000)%Z -> (0 <= DX <= 160000)%Z -> R = (DW - dfw)%Z -> lw2 = ((DW + DX) mod 32)%Z ->
  getr regs 18 = Z_to_bv 64 DW -> getr regs 17 = Z_to_bv 64 dfw -> getr regs 10 = Z_to_bv 64 pfp -> getr regs 13 = Z_to_bv 64 DX ->
  exists regs',
    msteps SEGS (mkst regs (0x1ca6c : word) m rom) (mkst regs' (0x1ca8c : word) m rom)
    /\ getr regs' 13 = Z_to_bv 64 (if (R <? 32)%Z then 1 else 0) /\ getr regs' 22 = Z_to_bv 64 (R / 32) /\ getr regs' 14 = Z_to_bv 64 lw2
    /\ getr regs' 20 = Z_to_bv 64 (pfp + 4) /\ getr regs' 9 = Z_to_bv 64 (if (R <? 32)%Z then 0 else pfp + 4)
    /\ regs_agree (fun r => In r [9; 13; 14; 15; 18; 20; 22]%list) regs regs'.
Proof.
  intros regs m DW DX dfw pfp R lw2 Hdfw Hge HDW HDX ER Elw H18 H17 H10 H13.
  destruct (Z.ltb_spec R 32) as [LT|GE]; eexists; (split; [
    sn F_1c970 D_1c970; fsubw R;
    sn F_1c974 D_1c974; fixv' (Z_to_bv 64 (pfp + 4)) ltac:(rewrite zbv_addi; reflexivity);
    sn F_1c978 D_1c978; fadd (DW + DX)%Z;
    sn F_1c97c D_1c97c; fixv' (Z_to_bv 64 (if (R <? 32)%Z then 1 else 0)) ltac:(rewrite v_sltiu_Z by lia; reflexivity);
    sn F_1c980 D_1c980; fixv' (Z_to_bv 64 (R / 32)) ltac:(rewrite zbv_srliw_small by lia; reflexivity) |]).
  - destruct (Z.ltb_spec R 32) as [_|X]; [|lia].
    sn F_1c984 D_1c984. fixv' (Z_to_bv 64 0) ltac:(rewrite zbv_addi; reflexivity).
    sn F_1c988 D_1c988. fixv' (Z_to_bv 64 lw2) ltac:(rewrite andi_31_Z by lia; rewrite <- Elw; reflexivity).
    sn F_1c98c D_1c98c. fz.
    apply mst_refl.
  - destruct (Z.ltb_spec R 32) as [_|X]; [|lia]. repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - destruct (Z.ltb_spec R 32) as [X|_]; [lia|].
    sn F_1c984 D_1c984.
    sn F_1c988 D_1c988. fixv' (Z_to_bv 64 lw2) ltac:(rewrite andi_31_Z by lia; rewrite <- Elw; reflexivity).
    sn F_1c98c D_1c98c. fixv' (Z_to_bv 64 (pfp + 4)) ltac:(apply and_m1u_l).
    apply mst_refl.
  - destruct (Z.ltb_spec R 32) as [X|_]; [lia|]. repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_G1b : forall (set : bool) regs m (lw2 op p4 dnf : Z),
  (0 <= lw2 < 32)%Z -> op = (if set then 15 else 0)%Z -> (0 <= dnf < 2 ^ 26)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x1170c + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 14 = Z_to_bv 64 lw2 -> getr regs 11 = Z_to_bv 64 op -> getr regs 20 = Z_to_bv 64 p4 -> getr regs 22 = Z_to_bv 64 dnf ->
  exists regs',
    msteps SEGS (mkst regs (0x1ca8c : word) m rom) (mkst regs' (pcG_l1s set) m rom)
    /\ getr regs' 23 = Z_to_bv 64 (if (lw2 =? 0)%Z then 1 else 0) /\ (lw2 <> 0%Z -> getr regs' 20 = Z_to_bv 64 (p4 + 4 * dnf))
    /\ regs_agree (fun r => In r [14; 15; 20; 21; 23]%list) regs regs'.
Proof.
  intros set regs m lw2 op p4 dnf Hlw Eop Hdnf TBL H14 H11 H20 H22. unfold pcG_l1s.
  destruct (Z.eqb_spec lw2 0) as [E0|NE0].
  - destruct set; subst op; eexists; (split; [
      stepb_tk F_1c990 D_1c990 ltac:(condZ); sn F_1cb48 D_1cb48; sn F_1cb4c D_1cb4c; sn F_1cb50 D_1cb50 |]).
    + stepb_ft F_1cb54 D_1cb54 ltac:(condZ). sn F_1cb58 D_1cb58. apply mst_refl.
    + repeat split; gres; pin; try reflexivity; try (intros X; contradiction). solve_regs_agree.
    + stepb_tk F_1cb54 D_1cb54 ltac:(condZ). sn F_1c8f4 D_1c8f4. stepb_ft F_1c8f8 D_1c8f8 ltac:(condZ). stepb_ft F_1c8fc D_1c8fc ltac:(condZ). apply mst_refl.
    + repeat split; gres; pin; try reflexivity; try (intros X; contradiction). solve_regs_agree.
  - destruct (TBL lw2 ltac:(lia)) as (bs & v & Rv & Ev).
    destruct set; subst op; eexists; (split; [
      stepb_ft F_1c990 D_1c990 ltac:(condZ); sn F_1c994 D_1c994;
      sn F_1c998 D_1c998; fixv' (Z_to_bv 64 (4 * lw2)) ltac:(rewrite zbv_slli by lia; f_equal; lia);
      sn F_1c99c D_1c99c; sn F_1c9a0 D_1c9a0;
      sn F_1c9a4 D_1c9a4; fixv' (Z_to_bv 64 (0x1170c + 4 * lw2)) ltac:(vclose);
      stepLD F_1c9a8 D_1c9a8 bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev);
      sn F_1c9ac D_1c9ac; fixv' (Z_to_bv 64 (4 * dnf)) ltac:(rewrite zbv_slli by lia; f_equal; lia);
      sn F_1c9b0 D_1c9b0; fadd (p4 + 4 * dnf)%Z;
      sn F_1c9b4 D_1c9b4 |]).
    + stepb_ft F_1c9b8 D_1c9b8 ltac:(condZ). apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    + stepb_tk F_1c9b8 D_1c9b8 ltac:(condZ). sn F_1c8f4 D_1c8f4. stepb_ft F_1c8f8 D_1c8f8 ltac:(condZ). stepb_ft F_1c8fc D_1c8fc ltac:(condZ). apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_L1s : forall (set : bool) regs m (dwpl dh : Z), (0 <= dwpl < 2 ^ 24)%Z ->
  getr regs 8 = Z_to_bv 64 dwpl -> getr regs 19 = Z_to_bv 64 dh ->
  exists regs', msteps SEGS (mkst regs (pcG_l1s set) m rom) (mkst regs' (pcG_l1 set) m rom)
    /\ getr regs' 14 = Z_to_bv 64 dh /\ getr regs' (if set then 11 else 12) = Z_to_bv 64 (4 * dwpl)
    /\ regs_agree (fun r => In r [11; 12; 14]%list) regs regs'.
Proof.
  intros set regs m dwpl dh Hdwpl H8 H19. unfold pcG_l1s, pcG_l1. destruct set; eexists; (split; [|]).
  - sn F_1c9bc D_1c9bc. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia). sn F_1c9c0 D_1c9c0. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1c900 D_1c900. sn F_1c904 D_1c904. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia). sn F_1c908 D_1c908. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_L1 : forall (set last : bool) regs m (p c stp : Z) (bd : list byte) (vd : word),
  (0 <= p < 2 ^ 64)%Z -> (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
  rdn SEGS m (Z_to_bv 64 p) 4 = Some bd -> bytes_le_to_Z bd = bv_unsigned vd -> store_ok SEGS m (Z_to_bv 64 p) 4 = true ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 c -> getr regs (if set then 11 else 12) = Z_to_bv 64 stp ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (pcG_l1 set) m rom) (mkst regs' (if last then pcG_l1x set else pcG_l1 set) (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (p + stp) /\ getr regs' 14 = Z_to_bv 64 (c - 1)
    /\ regs_agree (fun r => In r [10; 14; 15]%list) regs regs'.
Proof.
  intros set last regs m p c stp bd vd Hp Hc HL Rd Evd SOK H10 H14 Hstp. unfold pcG_l1, pcG_l1x.
  destruct set; destruct last; eexists; eexists; (split; [|]).
  - stepLD F_1c9c4 D_1c9c4 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1c9c8 D_1c9c8. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia). sn F_1c9cc D_1c9cc.
    stepST F_1c9d0 D_1c9d0 (Z_to_bv 64 p) (v_or (v_lw vd) (getr regs 12)) ltac:(store_ok_peel; exact SOK).
    sn F_1c9d4 D_1c9d4. fadd (p + stp)%Z. stepb_ft F_1c9d8 D_1c9d8 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepLD F_1c9c4 D_1c9c4 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1c9c8 D_1c9c8. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia). sn F_1c9cc D_1c9cc.
    stepST F_1c9d0 D_1c9d0 (Z_to_bv 64 p) (v_or (v_lw vd) (getr regs 12)) ltac:(store_ok_peel; exact SOK).
    sn F_1c9d4 D_1c9d4. fadd (p + stp)%Z. stepb_tk F_1c9d8 D_1c9d8 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepLD F_1c90c D_1c90c bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1c910 D_1c910. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia). sn F_1c914 D_1c914.
    stepST F_1c918 D_1c918 (Z_to_bv 64 p) (v_and (v_lw vd) (getr regs 11)) ltac:(store_ok_peel; exact SOK).
    sn F_1c91c D_1c91c. fadd (p + stp)%Z. stepb_ft F_1c920 D_1c920 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepLD F_1c90c D_1c90c bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1c910 D_1c910. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia). sn F_1c914 D_1c914.
    stepST F_1c918 D_1c918 (Z_to_bv 64 p) (v_and (v_lw vd) (getr regs 11)) ltac:(store_ok_peel; exact SOK).
    sn F_1c91c D_1c91c. fadd (p + stp)%Z. stepb_tk F_1c920 D_1c920 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_L1x : forall (set full : bool) regs m (dwpl dnf dh : Z), (0 <= dwpl < 2 ^ 24)%Z -> (0 <= dnf < 2 ^ 26)%Z ->
  getr regs 8 = Z_to_bv 64 dwpl -> getr regs 22 = Z_to_bv 64 dnf -> getr regs 19 = Z_to_bv 64 dh -> getr regs 13 = Z_to_bv 64 (if full then 0 else 1) ->
  exists regs', msteps SEGS (mkst regs (pcG_l1x set) m rom) (mkst regs' (if full then pcG_l2 set else pcG_l3t set) m rom)
    /\ (set = true -> getr regs' 18 = Z_to_bv 64 (4 * dwpl))
    /\ (full = true -> getr regs' (if set then 8 else 18) = Z_to_bv 64 (4 * dnf) /\ getr regs' (if set then 24 else 25) = Z_to_bv 64 dh /\ (set = false -> getr regs' 24 = Z_to_bv 64 (4 * dwpl)))
    /\ regs_agree (fun r => In r (if full then (if set then [8; 18; 24] else [18; 24; 25]) else (if set then [18] else []))%list) regs regs'.
Proof.
  intros set full regs m dwpl dnf dh Hdwpl Hdnf H8 H22 H19 H13. unfold pcG_l1x, pcG_l2, pcG_l3t.
  destruct set; destruct full; eexists; (split; [|]).
  - sn F_1c9dc D_1c9dc. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia). stepb_tk F_1c9e0 D_1c9e0 ltac:(condZ).
    sn F_1ccc8 D_1ccc8. fixv' (Z_to_bv 64 (4 * dnf)) ltac:(rewrite zbv_slli by lia; f_equal; lia). sn F_1cccc D_1cccc. sn F_1ccd0 D_1ccd0. apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity); try (intros; discriminate). all: try solve_regs_agree.
  - sn F_1c9dc D_1c9dc. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia). stepb_ft F_1c9e0 D_1c9e0 ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity); try (intros; discriminate). all: try solve_regs_agree.
  - stepb_tk F_1c924 D_1c924 ltac:(condZ).
    sn F_1ccf8 D_1ccf8. fixv' (Z_to_bv 64 (4 * dnf)) ltac:(rewrite zbv_slli by lia; f_equal; lia).
    sn F_1ccfc D_1ccfc. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia). sn F_1cd00 D_1cd00. sn F_1cd04 D_1cd04. apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity); try (intros; discriminate). all: try solve_regs_agree.
  - stepb_ft F_1c924 D_1c924 ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity); try (intros; discriminate). all: try solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_L2a : forall (set : bool) regs m (dnf : Z) (p n4 : word), (1 <= dnf < 2 ^ 26)%Z ->
  getr regs 22 = Z_to_bv 64 dnf -> getr regs 9 = p -> getr regs (if set then 8 else 18) = n4 ->
  exists regs', msteps SEGS (mkst regs (pcG_l2 set) m rom) (mkst regs' (0x2942c : word) m rom)
    /\ getr regs' 1 = pcG_l2r set /\ getr regs' 10 = p /\ getr regs' 11 = Z_to_bv 64 (if set then 255 else 0) /\ getr regs' 12 = n4
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros set regs m dnf p n4 Hdnf H22 H9 Hn4. unfold pcG_l2, pcG_l2r. destruct set; eexists; (split; [|]).
  - stepb_ft F_1cce0 D_1cce0 ltac:(condZ). sn F_1cce4 D_1cce4. sn F_1cce8 D_1cce8. sn F_1ccec D_1ccec. sn F_1ccf0 D_1ccf0. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  - stepb_ft F_1cd14 D_1cd14 ltac:(condZ). sn F_1cd18 D_1cd18. sn F_1cd1c D_1cd1c. sn F_1cd20 D_1cd20. sn F_1cd24 D_1cd24. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_L2b : forall (set last : bool) regs m (p c stp : Z), (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
  getr regs 9 = Z_to_bv 64 p -> getr regs (if set then 24 else 25) = Z_to_bv 64 c -> getr regs (if set then 18 else 24) = Z_to_bv 64 stp ->
  exists regs', msteps SEGS (mkst regs (pcG_l2r set) m rom) (mkst regs' (if last then pcG_l3t set else pcG_l2 set) m rom)
    /\ getr regs' 9 = Z_to_bv 64 (p + stp) /\ getr regs' (if set then 24 else 25) = Z_to_bv 64 (c - 1) /\ getr regs' (if set then 18 else 24) = Z_to_bv 64 stp
    /\ regs_agree (fun r => In r [9; 24; 25]%list) regs regs'.
Proof.
  intros set last regs m p c stp Hc HL H9 Hcn Hstp. unfold pcG_l2r, pcG_l3t, pcG_l2. destruct set; destruct last; eexists; (split; [|]).
  - sn F_1ccf4 D_1ccf4. sn F_1ccd4 D_1ccd4. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
    sn F_1ccd8 D_1ccd8. fadd (p + stp)%Z. stepb_tk F_1ccdc D_1ccdc ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1ccf4 D_1ccf4. sn F_1ccd4 D_1ccd4. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
    sn F_1ccd8 D_1ccd8. fadd (p + stp)%Z. stepb_ft F_1ccdc D_1ccdc ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1cd28 D_1cd28. sn F_1cd08 D_1cd08. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
    sn F_1cd0c D_1cd0c. fadd (p + stp)%Z. stepb_tk F_1cd10 D_1cd10 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_1cd28 D_1cd28. sn F_1cd08 D_1cd08. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
    sn F_1cd0c D_1cd0c. fadd (p + stp)%Z. stepb_ft F_1cd10 D_1cd10 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_L3t : forall (set nolast : bool) regs m (dwpl : Z), (0 <= dwpl < 2 ^ 24)%Z ->
  getr regs 23 = Z_to_bv 64 (if nolast then 1 else 0) -> (set = false -> getr regs 8 = Z_to_bv 64 dwpl) ->
  exists regs', msteps SEGS (mkst regs (pcG_l3t set) m rom) (mkst regs' (if nolast then (0x1cb44 : word) else pcG_l3 set) m rom)
    /\ (nolast = false -> set = false -> getr regs' 8 = Z_to_bv 64 (4 * dwpl))
    /\ regs_agree (fun r => In r (if set then [] else [8; 10])%list) regs regs'.
Proof.
  intros set nolast regs m dwpl Hdwpl H23 H8. unfold pcG_l3t, pcG_l3. destruct set; destruct nolast; eexists; (split; [|]).
  - stepb_tk F_1c9e4 D_1c9e4 ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; discriminate). all: try solve_regs_agree.
  - stepb_ft F_1c9e4 D_1c9e4 ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; discriminate). all: try solve_regs_agree.
  - stepb_tk F_1c928 D_1c928 ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; discriminate). all: try solve_regs_agree.
  - specialize (H8 eq_refl). stepb_ft F_1c928 D_1c928 ltac:(condZ). sn F_1c92c D_1c92c.
    sn F_1c930 D_1c930. fixv' (Z_to_bv 64 (4 * dwpl)) ltac:(rewrite zbv_slli by lia; f_equal; lia). apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity). all: try solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ru_L3 : forall (set last : bool) regs m (p c stp : Z) (bd : list byte) (vd : word),
  (0 <= p < 2 ^ 64)%Z -> (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
  rdn SEGS m (Z_to_bv 64 p) 4 = Some bd -> bytes_le_to_Z bd = bv_unsigned vd -> store_ok SEGS m (Z_to_bv 64 p) 4 = true ->
  getr regs 20 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 c -> getr regs (if set then 18 else 8) = Z_to_bv 64 stp ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (pcG_l3 set) m rom) (mkst regs' (if last then (0x1cb44 : word) else pcG_l3 set) (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 20 = Z_to_bv 64 (p + stp) /\ getr regs' 19 = Z_to_bv 64 (c - 1)
    /\ regs_agree (fun r => In r [10; 11; 19; 20]%list) regs regs'.
Proof.
  intros set last regs m p c stp bd vd Hp Hc HL Rd Evd SOK H20 H19 Hstp. unfold pcG_l3.
  destruct set; destruct last; eexists; eexists; (split; [|]).
  - stepLD F_1c9e8 D_1c9e8 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1c9ec D_1c9ec. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia). sn F_1c9f0 D_1c9f0.
    stepST F_1c9f4 D_1c9f4 (Z_to_bv 64 p) (v_or (v_lw vd) (getr regs 21)) ltac:(store_ok_peel; exact SOK).
    sn F_1c9f8 D_1c9f8. fadd (p + stp)%Z. stepb_ft F_1c9fc D_1c9fc ltac:(condZ). sn F_1ca00 D_1ca00. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepLD F_1c9e8 D_1c9e8 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1c9ec D_1c9ec. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia). sn F_1c9f0 D_1c9f0.
    stepST F_1c9f4 D_1c9f4 (Z_to_bv 64 p) (v_or (v_lw vd) (getr regs 21)) ltac:(store_ok_peel; exact SOK).
    sn F_1c9f8 D_1c9f8. fadd (p + stp)%Z. stepb_tk F_1c9fc D_1c9fc ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepLD F_1c934 D_1c934 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1c938 D_1c938. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia). sn F_1c93c D_1c93c.
    stepST F_1c940 D_1c940 (Z_to_bv 64 p) (v_and (v_lw vd) (getr regs 10)) ltac:(store_ok_peel; exact SOK).
    sn F_1c944 D_1c944. fadd (p + stp)%Z. stepb_ft F_1c948 D_1c948 ltac:(condZ). sn F_1c94c D_1c94c. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepLD F_1c934 D_1c934 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_1c938 D_1c938. fixv' (Z_to_bv 64 (c - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia). sn F_1c93c D_1c93c.
    stepST F_1c940 D_1c940 (Z_to_bv 64 p) (v_and (v_lw vd) (getr regs 10)) ltac:(store_ok_peel; exact SOK).
    sn F_1c944 D_1c944. fadd (p + stp)%Z. stepb_tk F_1c948 D_1c948 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.
End Segs.

(* [comment removed for export] *)
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

Section RopUniW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Hypothesis MEMSET : memset_fill_stmt SEGS (0x2942c : word).

Section Inv.
Variables (C : lctx) (Ar A : AS) (md : Model) (s : Z) (m0 : word -> option byte) (datad nd : Z) (S : TSet).
Variables (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word).
Hypotheses (CK : Cok C) (Hlo : (c_top C - LSTK + ROPUNI_STACK <= s)%Z) (Hhi : (s <= c_top C)%Z) (SUB : sub_live Ar A).
Hypotheses (Ld : live A (Z_to_bv 64 datad) = Some nd) (Ld0 : live Ar (Z_to_bv 64 datad) = None) (Ld00 : live (c_A0 C) (Z_to_bv 64 datad) = None).
Hypotheses (Hdd : (0 <= datad < 2 ^ 64)%Z) (Hnd : (0 < nd)%Z).

(* [comment removed for export] *)
Definition UMI (cw : option word) (m : word -> option byte) : Prop :=
  W C A m md /\ POSTM C Ar s m0 m /\ rlcells m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 /\
  (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m a = m0 a) /\
  match cw with Some c => rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 c) | None => True end.

Lemma UMI_geom : forall cw m, UMI cw m -> (4096 <= datad)%Z /\ (datad + nd + 8192 + LSTK <= c_top C)%Z /\ (c_top C < 2 ^ 64)%Z /\ (c_top C - LSTK + 128 <= s)%Z.
Proof.
  intros cw m (HW & _). pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [G TOP]. rewrite u_Z2bv in G, TOP by lia.
  pose proof (u64_range (c_sp0 C)). unfold ROPUNI_STACK in Hlo. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma UMI_fill : forall cw m m' (d n : Z), UMI cw m -> (datad <= d)%Z -> (0 <= n)%Z -> (d + n <= datad + nd)%Z ->
  (forall x : word, (u x < d \/ d + n <= u x)%Z -> m' x = m x) -> mem_grows m m' -> UMI cw m'.
Proof.
  intros cw m m' d n UM Hd Hn Hdn OUT GR. destruct (UMI_geom cw m UM) as (G1 & G2 & G3 & G4).
  destruct UM as (HW & PM & CE & FT & CW). pose proof LSTK_val as LV.
  assert (CH : forall a, m' a <> m a -> scratch C s a \/ (exists p k, live A p = Some k /\ live Ar p = None /\ (u p <= u a < u p + k)%Z)).
  { intros a NE. right. exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0|]].
    destruct (Z_lt_ge_dec (u a) d); [exfalso; apply NE; apply OUT; lia|].
    destruct (Z_lt_ge_dec (u a) (d + n)); [lia | exfalso; apply NE; apply OUT; lia]. }
  assert (HW' : W C A m' md).
  { apply (W_local C A m md m' s CK HW Hhi); [| exact GR].
    intros a NE. right. exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00|]].
    destruct (Z_lt_ge_dec (u a) d); [exfalso; apply NE; apply OUT; lia|].
    destruct (Z_lt_ge_dec (u a) (d + n)); [lia | exfalso; apply NE; apply OUT; lia]. }
  split; [exact HW'|]. split; [eapply POSTM_trans; [exact PM | exact (POSTM_local C Ar A m md m' s CK HW SUB CH)]|].
  split; [apply (rlcells_frame m m' s); [lia | lia | exact CE |]; intros x Hx; apply OUT; lia|].
  split; [intros a Ha1 Ha2; rewrite OUT by lia; exact (FT a Ha1 Ha2)|].
  destruct cw as [c|]; [|exact I]. rewrite <- CW. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT. lia.
Qed.

(* [comment removed for export] *)
Lemma UMI_word : forall cw m (pd : Z) (w : word), UMI cw m -> (datad <= pd)%Z -> (pd + 4 <= datad + nd)%Z ->
  UMI cw (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)).
Proof.
  intros cw m pd w UM H1 H2. destruct (UMI_geom cw m UM) as (G1 & G2 & G3 & G4). pose proof LSTK_val as LV.
  apply (UMI_fill cw m _ pd 4 UM H1 ltac:(lia) H2).
  - intros x Hx. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
  - apply wbytes_grows.
Qed.

Lemma UMI_rd4 : forall cw m (pd : Z), UMI cw m -> (datad <= pd)%Z -> (pd + 4 <= datad + nd)%Z ->
  exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 pd) 4 = Some bs /\ bytes_le_to_Z bs = u v.
Proof.
  intros cw m pd UM H1 H2. destruct (UMI_geom cw m UM) as (G1 & G2 & G3 & G4). pose proof LSTK_val as LV. destruct UM as (HW & _).
  apply (W_rd4_blk C A m md (Z_to_bv 64 datad) nd pd CK HW Ld); rewrite u_Z2bv by lia; lia.
Qed.

Lemma UMI_sok : forall cw m (a : Z) (n : nat), UMI cw m -> (datad <= a)%Z -> (a + Z.of_nat n <= datad + nd)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros cw m a n UM H1 H2. destruct (UMI_geom cw m UM) as (G1 & G2 & G3 & G4). pose proof LSTK_val as LV. destruct UM as (HW & _).
  apply (W_sok_blk C A m md (Z_to_bv 64 datad) nd a n CK HW Ld); rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma U_memset : forall cw m r (d n c : Z) (retpc : word),
  UMI cw m -> (datad <= d)%Z -> (1 <= n)%Z -> (d + n <= datad + nd)%Z -> (0 <= c < 256)%Z -> ret_ok retpc ->
  getr r 1 = retpc -> getr r 10 = Z_to_bv 64 d -> getr r 11 = Z_to_bv 64 c -> getr r 12 = Z_to_bv 64 n ->
  (forall r' m', UMI cw m' -> regs_agree (fun x => In x [11; 12; 13; 14; 15; 16]%list) r r' -> realizes SEGS (mkCfg (mkst r' retpc m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x2942c : word) m al_rom) md) S.
Proof.
  intros cw m r d n c retpc UM H1 Hn H2 Hc Hret R1 R10 R11 R12 K.
  destruct (UMI_geom cw m UM) as (G1 & G2 & G3 & G4). pose proof LSTK_val as LV.
  pose proof (UMI_sok cw m d (Z.to_nat n) UM H1 ltac:(rewrite Z2Nat.id by lia; lia)) as SOK.
  destruct (MEMSET r m al_rom d n c retpc ltac:(lia) ltac:(lia) ltac:(lia) Hc SOK Hret R1 R10 R11 R12) as (r' & m' & RUN & _ & AG & OUT & GR & _).
  pose proof UM as (HW & _). rzs HW RUN.
  apply K; [exact (UMI_fill cw m m' d n UM H1 ltac:(lia) H2 OUT GR) | exact AG].
Qed.

(* [comment removed for export] *)
Lemma U_rows : forall (P : Z -> bvmap 5 word -> (word -> option byte) -> Prop) (HEAD EXIT : word) (dh : Z),
  (forall i r m, (0 <= i < dh)%Z -> P i r m ->
     (forall r' m', P (i + 1)%Z r' m' -> realizes SEGS (mkCfg (mkst r' (if Z.eq_dec (i + 1) dh then EXIT else HEAD) m' al_rom) md) S) ->
     realizes SEGS (mkCfg (mkst r HEAD m al_rom) md) S) ->
  forall (n : nat) i r m, (Z.of_nat n = dh - 1 - i)%Z -> (0 <= i < dh)%Z -> P i r m ->
  (forall r' m', P dh r' m' -> realizes SEGS (mkCfg (mkst r' EXIT m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r HEAD m al_rom) md) S.
Proof.
  intros P HEAD EXIT dh BODY. induction n as [|n IH]; intros i r m Hn Hi HP K; apply (BODY i r m Hi HP); intros r' m' HP';
    destruct (Z.eq_dec (i + 1) dh) as [E|NE]; try lia.
  - rewrite E in HP'. exact (K r' m' HP').
  - apply (IH (i + 1)%Z r' m' ltac:(lia) ltac:(lia) HP' K).
Qed.

(* [comment removed for export] *)
Lemma U_exit : forall cw m r (g3 g4 : word),
  ret_ok ret -> UMI cw m -> getr r 2 = Z_to_bv 64 (s - 112) -> getr r 3 = g3 -> getr r 4 = g4 ->
  (forall m' r', W C A m' md -> POSTM C Ar s m0 m' -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m' a = m0 a) ->
     getr r' 2 = Z_to_bv 64 s -> getr r' 1 = ret -> getr r' 3 = g3 -> getr r' 4 = g4 ->
     getr r' 8 = v0 -> getr r' 9 = v1 -> getr r' 18 = v2 -> getr r' 19 = v3 -> getr r' 20 = v4 -> getr r' 21 = v5 -> getr r' 22 = v6 -> getr r' 23 = v7 -> getr r' 24 = v8 -> getr r' 25 = v9 -> getr r' 26 = v10 -> getr r' 27 = v11 ->
     realizes SEGS (mkCfg (mkst r' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x1cb44 : word) m al_rom) md) S.
Proof.
  intros cw m r g3 g4 Hret UM R2 R3 R4 KF. destruct (UMI_geom cw m UM) as (G1 & G2 & G3 & G4). destruct UM as (HW & PM & CE & FT & _).
  destruct (ru_E al_rom r m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ltac:(lia) ltac:(lia) Hret CE R2)
    as (r2 & RUN2 & Q2 & Q1 & QV0 & QV1 & QV2 & QV3 & QV4 & QV5 & QV6 & QV7 & QV8 & QV9 & QV10 & QV11 & AG2).
  rzs HW RUN2.
  apply (KF m r2 HW PM FT Q2 Q1); try assumption; csr; reflexivity.
Qed.

Ltac ag_sub Hx := let X := fresh "X" in intros X; apply Hx; cbv in X |- *; intuition.

(* [comment removed for export] *)
Definition UKF (g3 g4 : word) : Prop :=
  forall m' r', W C A m' md -> POSTM C Ar s m0 m' -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m' a = m0 a) ->
     getr r' 2 = Z_to_bv 64 s -> getr r' 1 = ret -> getr r' 3 = g3 -> getr r' 4 = g4 ->
     getr r' 8 = v0 -> getr r' 9 = v1 -> getr r' 18 = v2 -> getr r' 19 = v3 -> getr r' 20 = v4 -> getr r' 21 = v5 -> getr r' 22 = v6 -> getr r' 23 = v7 -> getr r' 24 = v8 -> getr r' 25 = v9 -> getr r' 26 = v10 -> getr r' 27 = v11 ->
     realizes SEGS (mkCfg (mkst r' ret m' al_rom) md) S.


(* [comment removed for export] *)
Lemma U_arows : forall (set : bool) (cw : word) (pf nfw k DW dh dwpl : Z) (g3 g4 : word) r0 m,
  ret_ok ret -> (1 <= DW < 2 ^ 31)%Z -> (DW = 32 * nfw + k)%Z -> (0 <= k < 32)%Z -> (0 <= nfw < 2 ^ 26)%Z -> (1 <= dh <= 20000)%Z -> (1 <= dwpl < 2 ^ 24)%Z -> (dh * dwpl <= 2 ^ 24)%Z ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= pf + 4 * dwpl * i')%Z /\ (pf + 4 * dwpl * i' + 4 * (nfw + (if Z.eq_dec k 0 then 0 else 1)) <= datad + nd)%Z) ->
  UMI (Some cw) m ->
  getr r0 2 = Z_to_bv 64 (s - 112) -> getr r0 3 = g3 -> getr r0 4 = g4 ->
  getr r0 21 = Z_to_bv 64 pf -> getr r0 23 = Z_to_bv 64 0 -> getr r0 25 = Z_to_bv 64 (0 - dh) ->
  getr r0 18 = Z_to_bv 64 DW -> getr r0 27 = Z_to_bv 64 32 -> getr r0 20 = Z_to_bv 64 k -> getr r0 8 = Z_to_bv 64 dwpl -> getr r0 19 = Z_to_bv 64 (4 * dwpl) ->
  getr r0 (if set then 24 else 22) = Z_to_bv 64 pf ->
  ((1 <= nfw)%Z -> getr r0 9 = Z_to_bv 64 (4 * nfw)) ->
  ((1 <= nfw)%Z -> (if set then cw else getr r0 24) = Z_to_bv 64 (pf + 4 * nfw)) ->
  UKF g3 g4 ->
  realizes SEGS (mkCfg (mkst r0 (pcA_head set) m al_rom) md) S.
Proof.
  intros set cw pf nfw k DW dh dwpl g3 g4 r0 m Hret HDW EDW Hk Hnfw Hdh Hdwpl Hsz GD UM0 H2 H3 H4 H21 H23 H25 H18 H27 H20 H8 H19 Hpf H9 Hpf4 KF.
  apply (U_rows (fun i r m => UMI (Some cw) m /\ regs_agree (fun x => In x [1; 10; 11; 12; 13; 14; 15; 16; 21; 23; 25; 26]%list) r0 r
                              /\ getr r 21 = Z_to_bv 64 (pf + 4 * dwpl * i) /\ getr r 23 = Z_to_bv 64 (i * dwpl) /\ getr r 25 = Z_to_bv 64 (i - dh))
                (pcA_head set) (0x1cb44 : word) dh) with (n := Z.to_nat (dh - 1)) (i := 0%Z).
  - (* [comment removed for export] *)
    intros i r m1 Hi (UM & AG & R21 & R23 & R25) K.
    destruct (UMI_geom _ _ UM) as (G1 & G2 & G3 & G4). pose proof LSTK_val as LV.
    destruct (GD i Hi) as [GD1 GD2].
    assert (Hiw : (0 <= i * dwpl /\ i * dwpl + dwpl <= 2 ^ 24)%Z) by (clear - Hi Hdwpl Hsz; nia).
    assert (TAIL : forall r' m', UMI (Some cw) m' -> regs_agree (fun x => In x [1; 10; 11; 12; 13; 14; 15; 16; 26]%list) r r' ->
                     realizes SEGS (mkCfg (mkst r' (pcA_next set) m' al_rom) md) S).
    { intros r' m' UM' AG'. pose proof UM' as (HW' & _).
      assert (AG2 : regs_agree (fun x => In x [1; 10; 11; 12; 13; 14; 15; 16; 21; 23; 25; 26]%list) r0 r')
        by (intros x Hx; rewrite (AG' x ltac:(ag_sub Hx)); exact (AG x Hx)).
      destruct (Z.eq_dec (i + 1) dh) as [E|NE].
      - destruct (ru_N al_rom set true r' m' i dh (i * dwpl) dwpl (pf + 4 * dwpl * i) (4 * dwpl) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
          as (r2 & RUN2 & Q23 & Q25 & Q21 & AGN).
        rzs HW' RUN2. apply K. split; [exact UM'|]. split; [intros x Hx; rewrite (AGN x ltac:(ag_sub Hx)); exact (AG2 x Hx)|].
        split; [rewrite Q21; f_equal; lia|]. split; [rewrite Q23; f_equal; lia | rewrite Q25; f_equal; lia].
      - destruct (ru_N al_rom set false r' m' i dh (i * dwpl) dwpl (pf + 4 * dwpl * i) (4 * dwpl) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
          as (r2 & RUN2 & Q23 & Q25 & Q21 & AGN).
        rzs HW' RUN2. apply K. split; [exact UM'|]. split; [intros x Hx; rewrite (AGN x ltac:(ag_sub Hx)); exact (AG2 x Hx)|].
        split; [rewrite Q21; f_equal; lia|]. split; [rewrite Q23; f_equal; lia | rewrite Q25; f_equal; lia]. }
    (* [comment removed for export] *)
    assert (PART : forall r' m' (pd : Z), UMI (Some cw) m' -> regs_agree (fun x => In x [1; 10; 11; 12; 13; 14; 15; 16; 26]%list) r r' ->
                     k <> 0%Z -> (datad <= pd)%Z -> (pd + 4 <= datad + nd)%Z -> getr r' 26 = Z_to_bv 64 pd ->
                     realizes SEGS (mkCfg (mkst r' (pcA_part set) m' al_rom) md) S).
    { intros r' m' pd UM' AG' K0 P1 P2 E26. pose proof UM' as (HW' & _ & _ & _ & CW').
      destruct (UMI_rd4 _ _ pd UM' P1 P2) as (bd & vd & Rd & Evd).
      pose proof (UMI_sok _ _ pd 4 UM' P1 ltac:(cbn; lia)) as SOK.
      destruct (ru_P al_rom set r' m' s pd k bd vd cw ltac:(lia) ltac:(lia) ltac:(lia) Rd Evd CW' SOK ltac:(csr; reflexivity) E26 ltac:(csr; reflexivity))
        as (r2 & w & RUN2 & AGP).
      rzs HW' RUN2. apply TAIL; [exact (UMI_word _ _ pd w UM' P1 P2)|].
      intros x Hx. rewrite (AGP x ltac:(ag_sub Hx)). exact (AG' x Hx). }
    pose proof UM as (HW & _).
    destruct (Z_lt_ge_dec DW 32) as [SMALL | BIG].
    + (* [comment removed for export] *)
      assert (Ek : k = DW) by lia. assert (K0 : k <> 0%Z) by lia. destruct (Z.eq_dec k 0) as [X|_]; [lia|].
      destruct (ru_Hs al_rom set r m1 DW (Z_to_bv 64 (pf + 4 * dwpl * i)) ltac:(lia) ltac:(csr; reflexivity) ltac:(csr; reflexivity) R21) as (r1 & RUN1 & Q26 & AG1).
      rzs HW RUN1. apply (PART r1 m1 (pf + 4 * dwpl * i)%Z UM); [| exact K0 | lia | lia | exact Q26].
      intros x Hx. apply AG1. ag_sub Hx.
    + (* [comment removed for export] *)
      assert (Hn1 : (1 <= nfw)%Z) by lia. specialize (H9 Hn1). specialize (Hpf4 Hn1).
      destruct (ru_Hb al_rom set r m1 s DW (i * dwpl) pf (pf + 4 * nfw) (Z_to_bv 64 (4 * nfw)) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(destruct set; [destruct UM as (_ & _ & _ & _ & CW); rewrite <- Hpf4; exact CW | csr; reflexivity])
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) R23 ltac:(destruct set; csr; reflexivity) ltac:(csr; reflexivity))
        as (r1 & RUN1 & Q1 & Q10 & Q11 & Q12 & Q26 & AG1).
      rzs HW RUN1.
      apply (U_memset (Some cw) m1 r1 (pf + 4 * (i * dwpl)) (4 * nfw) (if set then 255 else 0) (pcA_part set) UM ltac:(lia) ltac:(lia) ltac:(destruct (Z.eq_dec k 0); lia)
               ltac:(destruct set; lia) ltac:(destruct set; red; apply bv_eq; reflexivity) Q1 Q10 Q11 Q12).
      intros r2 m2 UM2 AGM.
      assert (AG12 : regs_agree (fun x => In x [1; 10; 11; 12; 13; 14; 15; 16; 26]%list) r r2)
        by (intros x Hx; rewrite (AGM x ltac:(ag_sub Hx)); apply AG1; ag_sub Hx).
      destruct (Z.eq_dec k 0) as [K0|K0].
      * pose proof UM2 as (HW2 & _).
        destruct (ru_P0 al_rom set r2 m2 ltac:(csr; rewrite K0; reflexivity)) as (r3 & RUN3 & AG3).
        rzs HW2 RUN3. apply TAIL; [exact UM2|]. intros x Hx. rewrite (AG3 x ltac:(intros X; exact X)). exact (AG12 x Hx).
      * apply (PART r2 m2 (pf + 4 * nfw + 4 * (i * dwpl))%Z UM2 AG12 K0); [lia | lia |].
        rewrite (AGM 26) by (cbv; intuition discriminate). exact Q26.
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [exact UM0|]. split; [intros x Hx; reflexivity|]. split; [rewrite H21; f_equal; lia|]. split; [rewrite H23; f_equal; lia | rewrite H25; f_equal; lia].
  - intros r' m' (UM' & AG' & _). apply (U_exit (Some cw) m' r' g3 g4 Hret UM'); [csr; reflexivity | csr; reflexivity | csr; reflexivity | exact KF].
Qed.

(* [comment removed for export] *)
Lemma U_wloop : forall (HEAD EXIT : word) (RP RC : reg) (CLB : list reg) (P0 dwpl dh : Z) r0 r1 m,
  (forall (last : bool) regs mm (p c : Z) (bd : list byte) (vd : word),
     (0 <= p < 2 ^ 64)%Z -> (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
     rdn SEGS mm (Z_to_bv 64 p) 4 = Some bd -> bytes_le_to_Z bd = u vd -> store_ok SEGS mm (Z_to_bv 64 p) 4 = true ->
     getr regs RP = Z_to_bv 64 p -> getr regs RC = Z_to_bv 64 c -> regs_agree (fun x => In x CLB) r0 regs ->
     exists regs' (w : word),
       msteps SEGS (mkst regs HEAD mm al_rom) (mkst regs' (if last then EXIT else HEAD) (wbytes mm (Z_to_bv 64 p) (word_to_le_bytes 4 w)) al_rom)
       /\ getr regs' RP = Z_to_bv 64 (p + 4 * dwpl) /\ getr regs' RC = Z_to_bv 64 (c - 1) /\ regs_agree (fun x => In x CLB) regs regs') ->
  (1 <= dh <= 20000)%Z ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= P0 + 4 * dwpl * i')%Z /\ (P0 + 4 * dwpl * i' + 4 <= datad + nd)%Z) ->
  UMI None m -> regs_agree (fun x => In x CLB) r0 r1 -> getr r1 RP = Z_to_bv 64 P0 -> getr r1 RC = Z_to_bv 64 dh ->
  (forall r' m', UMI None m' -> regs_agree (fun x => In x CLB) r0 r' -> realizes SEGS (mkCfg (mkst r' EXIT m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r1 HEAD m al_rom) md) S.
Proof.
  intros HEAD EXIT RP RC CLB P0 dwpl dh r0 r1 m ITER Hdh GD UM0 AG0 HP HC K.
  apply (U_rows (fun i r m => UMI None m /\ regs_agree (fun x => In x CLB) r0 r /\ getr r RP = Z_to_bv 64 (P0 + 4 * dwpl * i) /\ getr r RC = Z_to_bv 64 (dh - i))
                HEAD EXIT dh) with (n := Z.to_nat (dh - 1)) (i := 0%Z).
  - intros i r m1 Hi (UM & AG & RP1 & RC1) KK.
    destruct (UMI_geom _ _ UM) as (G1 & G2 & G3 & G4). pose proof LSTK_val as LV. destruct (GD i Hi) as [GD1 GD2].
    destruct (UMI_rd4 _ _ (P0 + 4 * dwpl * i) UM GD1 GD2) as (bd & vd & Rd & Evd).
    pose proof (UMI_sok _ _ (P0 + 4 * dwpl * i) 4 UM GD1 ltac:(cbn; lia)) as SOK. pose proof UM as (HW & _).
    destruct (Z.eq_dec (i + 1) dh) as [E|NE].
    + destruct (ITER true r m1 (P0 + 4 * dwpl * i)%Z (dh - i)%Z bd vd ltac:(lia) ltac:(lia) ltac:(cbn; lia) Rd Evd SOK RP1 RC1 AG) as (r2 & w & RUN & QP & QC & AG2).
      rzs HW RUN. apply KK. split; [exact (UMI_word _ _ _ w UM GD1 GD2)|]. split; [intros x Hx; rewrite (AG2 x Hx); exact (AG x Hx)|].
      split; [rewrite QP; f_equal; lia | rewrite QC; f_equal; lia].
    + destruct (ITER false r m1 (P0 + 4 * dwpl * i)%Z (dh - i)%Z bd vd ltac:(lia) ltac:(lia) ltac:(cbn; lia) Rd Evd SOK RP1 RC1 AG) as (r2 & w & RUN & QP & QC & AG2).
      rzs HW RUN. apply KK. split; [exact (UMI_word _ _ _ w UM GD1 GD2)|]. split; [intros x Hx; rewrite (AG2 x Hx); exact (AG x Hx)|].
      split; [rewrite QP; f_equal; lia | rewrite QC; f_equal; lia].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [exact UM0|]. split; [exact AG0|]. split; [rewrite HP; f_equal; lia | rewrite HC; f_equal; lia].
  - intros r' m' (UM' & AG' & _). exact (K r' m' UM' AG').
Qed.

(* [comment removed for export] *)
Lemma U_mloop : forall (set : bool) (P0 dwpl dnf dh : Z) r0 m,
  (1 <= dh <= 20000)%Z -> (1 <= dnf < 2 ^ 26)%Z ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= P0 + 4 * dwpl * i')%Z /\ (P0 + 4 * dwpl * i' + 4 * dnf <= datad + nd)%Z) ->
  UMI None m -> getr r0 9 = Z_to_bv 64 P0 -> getr r0 (if set then 24 else 25) = Z_to_bv 64 dh -> getr r0 (if set then 18 else 24) = Z_to_bv 64 (4 * dwpl) ->
  getr r0 22 = Z_to_bv 64 dnf -> getr r0 (if set then 8 else 18) = Z_to_bv 64 (4 * dnf) ->
  (forall r' m', UMI None m' -> regs_agree (fun x => In x [1; 9; 10; 11; 12; 13; 14; 15; 16; 24; 25]%list) r0 r' -> getr r' (if set then 18 else 24) = Z_to_bv 64 (4 * dwpl) ->
     realizes SEGS (mkCfg (mkst r' (pcG_l3t set) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r0 (pcG_l2 set) m al_rom) md) S.
Proof.
  intros set P0 dwpl dnf dh r0 m Hdh Hdnf GD UM0 H9 Hc Hstp H22 Hn4 K.
  apply (U_rows (fun i r m => UMI None m /\ regs_agree (fun x => In x [1; 9; 10; 11; 12; 13; 14; 15; 16; 24; 25]%list) r0 r
                              /\ getr r 9 = Z_to_bv 64 (P0 + 4 * dwpl * i) /\ getr r (if set then 24 else 25) = Z_to_bv 64 (dh - i)
                              /\ getr r (if set then 18 else 24) = Z_to_bv 64 (4 * dwpl))
                (pcG_l2 set) (pcG_l3t set) dh) with (n := Z.to_nat (dh - 1)) (i := 0%Z).
  - intros i r m1 Hi (UM & AG & R9 & RC & RS) KK.
    destruct (UMI_geom _ _ UM) as (G1 & G2 & G3 & G4). pose proof LSTK_val as LV. destruct (GD i Hi) as [GD1 GD2]. pose proof UM as (HW & _).
    destruct (ru_L2a al_rom set r m1 dnf (Z_to_bv 64 (P0 + 4 * dwpl * i)) (Z_to_bv 64 (4 * dnf)) Hdnf ltac:(csr; reflexivity) R9 ltac:(destruct set; csr; reflexivity))
      as (r1 & RUN1 & Q1 & Q10 & Q11 & Q12 & AG1).
    rzs HW RUN1.
    apply (U_memset None m1 r1 (P0 + 4 * dwpl * i) (4 * dnf) (if set then 255 else 0) (pcG_l2r set) UM ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(destruct set; lia) ltac:(destruct set; red; apply bv_eq; reflexivity) Q1 Q10 Q11 Q12).
    intros r2 m2 UM2 AGM. pose proof UM2 as (HW2 & _).
    assert (E9 : getr r2 9 = Z_to_bv 64 (P0 + 4 * dwpl * i)) by (csr; reflexivity).
    assert (EC : getr r2 (if set then 24 else 25) = Z_to_bv 64 (dh - i)) by (destruct set; csr; reflexivity).
    assert (ES : getr r2 (if set then 18 else 24) = Z_to_bv 64 (4 * dwpl)) by (destruct set; csr; reflexivity).
    assert (AG02 : regs_agree (fun x => In x [1; 9; 10; 11; 12; 13; 14; 15; 16; 24; 25]%list) r0 r2)
      by (intros x Hx; rewrite (AGM x ltac:(ag_sub Hx)); rewrite (AG1 x ltac:(ag_sub Hx)); exact (AG x Hx)).
    destruct (Z.eq_dec (i + 1) dh) as [E|NE].
    + destruct (ru_L2b al_rom set true r2 m2 (P0 + 4 * dwpl * i) (dh - i) (4 * dwpl) ltac:(lia) ltac:(cbn; lia) E9 EC ES) as (r3 & RUN3 & Q9 & QC & QS & AG3).
      rzs HW2 RUN3. apply KK. split; [exact UM2|]. split; [intros x Hx; rewrite (AG3 x ltac:(ag_sub Hx)); exact (AG02 x Hx)|].
      split; [rewrite Q9; f_equal; lia|]. split; [rewrite QC; f_equal; lia | exact QS].
    + destruct (ru_L2b al_rom set false r2 m2 (P0 + 4 * dwpl * i) (dh - i) (4 * dwpl) ltac:(lia) ltac:(cbn; lia) E9 EC ES) as (r3 & RUN3 & Q9 & QC & QS & AG3).
      rzs HW2 RUN3. apply KK. split; [exact UM2|]. split; [intros x Hx; rewrite (AG3 x ltac:(ag_sub Hx)); exact (AG02 x Hx)|].
      split; [rewrite Q9; f_equal; lia|]. split; [rewrite QC; f_equal; lia | exact QS].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [exact UM0|]. split; [intros x Hx; reflexivity|]. split; [rewrite H9; f_equal; lia|]. split; [rewrite Hc; f_equal; lia | exact Hstp].
  - intros r' m' (UM' & AG' & _ & _ & RS'). exact (K r' m' UM' AG' RS').
Qed.

(* [comment removed for export] *)
Lemma U_general : forall (set full nolast : bool) (pfp dh dwpl dnf : Z) (g3 g4 : word) r0 m,
  ret_ok ret -> (1 <= dh <= 20000)%Z -> (1 <= dwpl < 2 ^ 24)%Z -> (0 <= dnf < 2 ^ 26)%Z -> (full = true -> (1 <= dnf)%Z) ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= pfp + 4 * dwpl * i')%Z /\
        (pfp + 4 * dwpl * i' + 4 + (if full then 4 * dnf else 0) + (if nolast then 0 else 4) <= datad + nd)%Z) ->
  UMI None m ->
  getr r0 2 = Z_to_bv 64 (s - 112) -> getr r0 3 = g3 -> getr r0 4 = g4 ->
  getr r0 10 = Z_to_bv 64 pfp -> getr r0 8 = Z_to_bv 64 dwpl -> getr r0 19 = Z_to_bv 64 dh -> getr r0 22 = Z_to_bv 64 dnf ->
  getr r0 13 = Z_to_bv 64 (if full then 0 else 1) -> getr r0 23 = Z_to_bv 64 (if nolast then 1 else 0) ->
  (full = true -> getr r0 9 = Z_to_bv 64 (pfp + 4)) -> (nolast = false -> getr r0 20 = Z_to_bv 64 (pfp + 4 + (if full then 4 * dnf else 0))) ->
  UKF g3 g4 ->
  realizes SEGS (mkCfg (mkst r0 (pcG_l1s set) m al_rom) md) S.
Proof.
  intros set full nolast pfp dh dwpl dnf g3 g4 r0 m Hret Hdh Hdwpl Hdnf Hfull GD UM0 H2 H3 H4 H10 H8 H19 H22 H13 H23 H9 H20 KF.
  pose proof UM0 as (HW0 & _).
  (* [comment removed for export] *)
  assert (K3 : forall r m', UMI None m' -> getr r 2 = Z_to_bv 64 (s - 112) -> getr r 3 = g3 -> getr r 4 = g4 ->
                 getr r 23 = Z_to_bv 64 (if nolast then 1 else 0) -> getr r 19 = Z_to_bv 64 dh ->
                 (nolast = false -> getr r 20 = Z_to_bv 64 (pfp + 4 + (if full then 4 * dnf else 0))) ->
                 (set = false -> getr r 8 = Z_to_bv 64 dwpl) -> (set = true -> getr r 18 = Z_to_bv 64 (4 * dwpl)) ->
                 realizes SEGS (mkCfg (mkst r (pcG_l3t set) m' al_rom) md) S).
  { intros r m' UM E2 E3 E4 E23 E19 E20 E8 E18. pose proof UM as (HW & _).
    destruct (ru_L3t al_rom set nolast r m' dwpl ltac:(lia) E23 E8) as (r1 & RUN1 & Q8 & AG1).
    rzs HW RUN1. destruct nolast.
    - apply (U_exit None m' r1 g3 g4 Hret UM); [destruct set; csr; reflexivity | destruct set; csr; reflexivity | destruct set; csr; reflexivity | exact KF].
    - specialize (E20 eq_refl). specialize (Q8 eq_refl).
      apply (U_wloop (pcG_l3 set) (0x1cb44 : word) 20 19 [10; 11; 19; 20]%list (pfp + 4 + (if full then 4 * dnf else 0)) dwpl dh r1 r1 m').
      + intros last regs mm p c bd vd Hp Hc HL Rd Evd SOK RP RC AG.
        destruct (ru_L3 al_rom set last regs mm p c (4 * dwpl) bd vd Hp Hc HL Rd Evd SOK RP RC
                    ltac:(destruct set; [rewrite (AG 18) by (cbv; intuition discriminate); rewrite (AG1 18) by (cbv; intuition discriminate); exact (E18 eq_refl)
                                        | rewrite (AG 8) by (cbv; intuition discriminate); exact (Q8 eq_refl)]))
          as (regs' & w & RUN & QP & QC & AG').
        exists regs', w. split; [exact RUN|]. split; [exact QP|]. split; [exact QC | exact AG'].
      + exact Hdh.
      + intros i' Hi'. destruct (GD i' Hi') as [X1 X2]. destruct full; lia.
      + exact UM.
      + intros x Hx. reflexivity.
      + destruct set; csr; reflexivity.
      + destruct set; csr; reflexivity.
      + intros r' m'' UM' AG'. apply (U_exit None m'' r' g3 g4 Hret UM'); [destruct set; csr; reflexivity | destruct set; csr; reflexivity | destruct set; csr; reflexivity | exact KF]. }
  (* [comment removed for export] *)
  destruct (ru_L1s al_rom set r0 m dwpl dh ltac:(lia) H8 H19) as (r1 & RUN1 & Q14 & Qstp & AG1).
  rzs HW0 RUN1.
  apply (U_wloop (pcG_l1 set) (pcG_l1x set) 10 14 [10; 14; 15]%list pfp dwpl dh r1 r1 m).
  - intros last regs mm p c bd vd Hp Hc HL Rd Evd SOK RP RC AG.
    destruct (ru_L1 al_rom set last regs mm p c (4 * dwpl) bd vd Hp Hc HL Rd Evd SOK RP RC
                ltac:(destruct set; [rewrite (AG 11) by (cbv; intuition discriminate) | rewrite (AG 12) by (cbv; intuition discriminate)]; exact Qstp))
      as (regs' & w & RUN & QP & QC & AG').
    exists regs', w. split; [exact RUN|]. split; [exact QP|]. split; [exact QC | exact AG'].
  - exact Hdh.
  - intros i' Hi'. destruct (GD i' Hi') as [X1 X2]. destruct full; destruct nolast; lia.
  - exact UM0.
  - intros x Hx. reflexivity.
  - csr. reflexivity.
  - exact Q14.
  - intros r2 m2 UM2 AG2. pose proof UM2 as (HW2 & _).
    destruct (ru_L1x al_rom set full r2 m2 dwpl dnf dh ltac:(lia) Hdnf ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r3 & RUN3 & Q18 & QF & AG3).
    rzs HW2 RUN3. destruct full.
    + destruct (QF eq_refl) as (Qn4 & Qc & Qs). specialize (Hfull eq_refl). specialize (H9 eq_refl).
      apply (U_mloop set (pfp + 4) dwpl dnf dh r3 m2 Hdh ltac:(lia)).
      * intros i' Hi'. destruct (GD i' Hi') as [X1 X2]. destruct nolast; lia.
      * exact UM2.
      * destruct set; csr; reflexivity.
      * exact Qc.
      * destruct set; [exact (Q18 eq_refl) | exact (Qs eq_refl)].
      * destruct set; csr; reflexivity.
      * exact Qn4.
      * intros r4 m4 UM4 AG4 ES4.
        apply (K3 r4 m4 UM4).
        -- destruct set; csr; reflexivity.
        -- destruct set; csr; reflexivity.
        -- destruct set; csr; reflexivity.
        -- destruct set; csr; reflexivity.
        -- destruct set; csr; reflexivity.
        -- intros NL. specialize (H20 NL). destruct set; csr; reflexivity.
        -- intros ->. csr. reflexivity.
        -- intros ->. exact ES4.
    + apply (K3 r3 m2 UM2).
      * destruct set; csr; reflexivity.
      * destruct set; csr; reflexivity.
      * destruct set; csr; reflexivity.
      * destruct set; csr; reflexivity.
      * destruct set; csr; reflexivity.
      * intros NL. specialize (H20 NL). destruct set; csr; reflexivity.
      * intros ->. csr. reflexivity.
      * intros ->. exact (Q18 eq_refl).
Qed.

(* [comment removed for export] *)
Lemma UMI_cell : forall m (cw : word), UMI None m -> UMI (Some cw) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 cw)).
Proof.
  intros m cw UM. destruct (UMI_geom _ _ UM) as (G1 & G2 & G3 & G4). pose proof LSTK_val as LV. destruct UM as (HW & PM & CE & FT & _).
  assert (WP : W C A (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 cw)) md /\ POSTM C Ar s m0 (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 cw)))
    by (apply (WP_win C A Ar m0 m md _ _ s CK (conj HW PM) SUB); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  destruct WP as [HW' PM']. split; [exact HW'|]. split; [exact PM'|].
  split; [apply (rlcells_frame m _ s); [lia | lia | exact CE |]; intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia|].
  split; [intros a Ha1 Ha2; rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; unfold scratch in Ha1; lia); exact (FT a Ha1 Ha2)|].
  apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
Qed.

End Inv.

(* [comment removed for export] *)
Lemma rmask_rd : forall j, (1 <= j <= 31)%Z ->
  exists bs, rdn SEGS (fun _ => None) (Z_to_bv 64 (0x11688 + 4 * j)) 4 = Some bs /\ length bs = 4%nat.
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

Theorem rasteropUniLow_W : rasteropUniLow_contract.
Proof.
  unfold rasteropUniLow_contract.
  intros C Ar A m md regs s datad dpixw dpixh d dwpl dx dy dw dh op ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Hdd SHd RCd Hop Ld Ld0 Ld00 HK.
  unfold PC_rasteropUniLow. replace (Z_to_bv 64 0x1c8c0) with (0x1c8c0 : word) by (apply bv_eq; reflexivity).
  destruct SHd as (Hd & Hdpw & Hdph & Ewd & Hszd). destruct RCd as (Hdx0 & Hdy0 & Hdw1 & Hdh1 & Hdxw & Hdyh).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LL16] in *.
  assert (Hlo' : (c_top C - LSTK + 128 <= s)%Z) by (unfold ROPUNI_STACK in Hlo; exact Hlo).
  assert (Hhi' : (s <= c_top C)%Z) by lia.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (DV : dval d) by (unfold dval; lia).
  pose proof (wpl_of_range dpixw d ltac:(lia) DV) as Hwd. rewrite <- Ewd in Hwd.
  pose proof (wpl_bits dpixw d ltac:(lia) ltac:(lia)) as WBd. rewrite <- Ewd in WBd.
  assert (Mdy : (0 <= dy * dwpl < 2 ^ 24)%Z) by (clear - Hszd Hdyh Hdh1 Hdy0 Hwd; nia).
  assert (Mdh : (dh * dwpl <= 2 ^ 24)%Z) by (clear - Hszd Hdyh Hdh1 Hdy0 Hwd; nia).
  set (nd := (4 * (dwpl * dpixh))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; nia).
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  set (DX := (dx * d)%Z). set (DW := (dw * d)%Z).
  assert (HDX : (0 <= DX <= 160000)%Z) by (subst DX; nia). assert (HDW : (1 <= DW <= 160000)%Z) by (subst DW; nia).
  assert (HDXW : (DX + DW <= dpixw * d)%Z) by (subst DX DW; nia). assert (HDPW : (dpixw * d <= 160000)%Z) by nia.
  set (a6 := (DX mod 32)%Z). set (cdx := (DX / 32)%Z).
  pose proof (Z.div_mod DX 32 ltac:(lia)) as EDX. fold cdx a6 in EDX. pose proof (Z.mod_pos_bound DX 32 ltac:(lia)) as Ha6. fold a6 in Ha6.
  assert (Hcdx : (0 <= cdx < 2 ^ 26)%Z) by lia.
  assert (SET : exists set : bool, op = (if set then 15 else 0)%Z) by (destruct Hop as [-> | ->]; [exists false | exists true]; reflexivity).
  destruct SET as [set Eop].
  (* [comment removed for export] *)
  destruct (ru_A0 al_rom regs m s dpixw d dwpl dx dw ret ltac:(lia) ltac:(lia) Hd ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H11 H13 H14 H15 H17)
    as (r0 & RUN0 & P2 & P8 & P11 & P14 & P13 & AG0).
  rzs HW RUN0.
  set (M1 := RLF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1) by (subst M1; unfold RLF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (rlcells_RLF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Rdh1 : rdn SEGS M1 (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh))) by (subst M1; rewrite rdn_RLF_above by (cbn; lia); exact Rdh).
  assert (Rop1 : rdn SEGS M1 (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op))) by (subst M1; rewrite rdn_RLF_above by (cbn; lia); exact Rop).
  assert (UM1 : UMI C Ar A md s m datad nd ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
                    (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) None M1).
  { split; [exact HW1|]. split; [exact PM1|]. split; [exact CE1|]. split; [|exact I].
    intros a Ha1 Ha2. subst M1. apply RLF_outside; [lia | lia |]. intros X. apply Ha1. unfold scratch. lia. }
  (* [comment removed for export] *)
  fold DX in P14. fold DW in P13.
  destruct (ru_A1 al_rom r0 M1 DX DW (dpixw * d)%Z ltac:(lia) ltac:(lia) HDXW HDPW P14 P13 P11) as (r1 & RUN1 & Q13 & Q18 & AG1).
  rzs HW1 RUN1.
  destruct (ru_A2 al_rom r1 M1 s dy dh dpixh ltac:(lia) ltac:(lia) Hdy0 Hdh1 Hdyh ltac:(lia) Rdh1 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r2 & RUN2 & Q14 & Q19 & AG2).
  rzs HW1 RUN2.
  destruct (ru_A3 al_rom r2 M1 s op DX dy dwpl a6 cdx ltac:(lia) ltac:(lia) ltac:(lia) eq_refl eq_refl ltac:(lia) ltac:(lia) Mdy Rop1
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) Q14 ltac:(csr; reflexivity))
    as (r3 & RUN3 & V11 & V16 & V15 & V14 & AG3).
  rzs HW1 RUN3.
  assert (TBL : forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS M1 (Z_to_bv 64 (0x1170c + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v).
  { intros j Hj. destruct (lmask_rd j Hj) as (bs & Rb & Lb). destruct (le4_word bs Lb) as (v & Ev). exists bs, v. split; [|exact Ev].
    rewrite <- p16_segs. rewrite (W_rdn_ro C A M1 md (0x1170c + 4 * j) 4 HW1) by (cbn; lia). rewrite p16_segs. exact Rb. }
  assert (KF : UKF C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
                   (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 3) (getr regs 4)).
  { intros m' r' HW' PM' FT' Z2 Z1 Z3 Z4 Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11.
    apply (HK m' r' HW'); [| exact PM' | exact FT'].
    apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | assumption ]. }
  assert (E2 : getr r3 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (E3 : getr r3 3 = getr regs 3) by (csr; reflexivity).
  assert (E4 : getr r3 4 = getr regs 4) by (csr; reflexivity).
  assert (E18 : getr r3 18 = Z_to_bv 64 DW) by (csr; reflexivity).
  assert (E10 : getr r3 10 = Z_to_bv 64 datad) by (csr; reflexivity).
  assert (E8 : getr r3 8 = Z_to_bv 64 dwpl) by (csr; reflexivity).
  assert (E19 : getr r3 19 = Z_to_bv 64 dh) by (csr; reflexivity).
  assert (E13 : getr r3 13 = Z_to_bv 64 DX) by (csr; reflexivity).
  clear AG0 AG1 AG2 AG3 RUN0 RUN1 RUN2 RUN3.
  destruct (Z.eq_dec a6 0) as [AL0 | NAL].
  - (* [comment removed for export] *)
    set (nfw := (DW / 32)%Z). set (k := (DW mod 32)%Z).
    pose proof (Z.div_mod DW 32 ltac:(lia)) as EDW. fold nfw k in EDW. pose proof (Z.mod_pos_bound DW 32 ltac:(lia)) as Hk. fold k in Hk.
    assert (Hnfw : (0 <= nfw < 2 ^ 26)%Z) by lia.
    pose proof (col_bound DX DW dwpl cdx nfw k ltac:(lia) EDW Hk ltac:(lia)) as CBd.
    destruct (ru_M al_rom r3 M1 DW k ltac:(lia) eq_refl Hk TBL E18) as (r4 & RUN4 & W20 & AG4).
    rzs HW1 RUN4.
    destruct (ru_S al_rom set r4 M1 DW nfw op datad (dy * dwpl) cdx ltac:(lia) eq_refl Eop Mdy Hcdx ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
                ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r5 & RUN5 & W12 & W21 & AG5).
    rzs HW1 RUN5.
    destruct (ru_S2 al_rom set r5 M1 s datad (dy * dwpl) cdx nfw dh dwpl ltac:(lia) ltac:(lia) ltac:(lia)
                (W_sok_win C A M1 md (s - 112) 8 CK HW1 ltac:(lia) ltac:(cbn; lia))
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) W12 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r6 & cw & RUN6 & X23 & X19 & X25 & X27 & X9 & Xpf & Xpf4 & AG6).
    rzs HW1 RUN6.
    pose proof (UMI_cell C Ar A md s m datad nd ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) CK Hlo Hhi' SUB Ld Hdd Hnd M1 cw UM1) as UM2.
    set (pf := (datad + 4 * (cdx + dy * dwpl))%Z) in *.
    apply (U_arows C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) CK Hlo Hhi' SUB Ld Ld0 Ld00 Hdd Hnd set cw pf nfw k DW dh dwpl (getr regs 3) (getr regs 4) r6 _
             Hret ltac:(lia) EDW Hk Hnfw ltac:(lia) ltac:(lia) Mdh).
    + intros i' Hi'. subst pf nd.
      pose proof (rop_rows_in datad dwpl dpixh dy dh cdx (nfw + (if Z.eq_dec k 0 then 0 else 1))%Z i' ltac:(lia) ltac:(lia) ltac:(destruct (Z.eq_dec k 0); lia) CBd Hdyh Hi') as [X1 X2].
      split; lia.
    + exact UM2.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + rewrite (AG6 21) by (cbv; intuition discriminate). rewrite W21. subst pf. f_equal. lia.
    + exact X23.
    + exact X25.
    + csr. reflexivity.
    + exact X27.
    + csr. reflexivity.
    + csr. reflexivity.
    + exact X19.
    + exact Xpf.
    + intros Hn1. rewrite X9. unfold len4. apply zext_len4. lia.
    + intros Hn1. rewrite Xpf4. unfold len4. rewrite zext_len4 by lia. rewrite zbv_add. f_equal. lia.
    + exact KF.
  - (* [comment removed for export] *)
    assert (TBR : forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS M1 (Z_to_bv 64 (0x11688 + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v).
    { intros j Hj. destruct (rmask_rd j Hj) as (bs & Rb & Lb). destruct (le4_word bs Lb) as (v & Ev). exists bs, v. split; [|exact Ev].
      rewrite <- p16_segs. rewrite (W_rdn_ro C A M1 md (0x11688 + 4 * j) 4 HW1) by (cbn; lia). rewrite p16_segs. exact Rb. }
    destruct (ru_G0 al_rom r3 M1 a6 DW datad (dy * dwpl) cdx ltac:(lia) ltac:(lia) Mdy Hcdx TBR V16 E18 E10 V15 V14) as (r4 & RUN4 & W17 & W10 & AG4).
    rzs HW1 RUN4.
    set (pfp := (datad + 4 * (dy * dwpl) + 4 * cdx)%Z) in *.
    destruct (Z.ltb_spec DW (32 - a6)) as [DBL | BIG].
    + (* [comment removed for export] *)
      destruct (ru_G1d al_rom set r4 M1 a6 DW op ltac:(lia) ltac:(lia) DBL Eop TBL ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (r5 & RUN5 & W13 & W23 & W22 & AG5).
      rzs HW1 RUN5.
      apply (U_general C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) CK Hlo Hhi' SUB Ld Ld0 Ld00 Hdd Hnd set false true pfp dh dwpl 0 (getr regs 3) (getr regs 4) r5 M1
               Hret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros X; discriminate X)).
      * intros i' Hi'. subst pfp nd.
        pose proof (rop_rows_in datad dwpl dpixh dy dh cdx 1 i' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdyh Hi') as [X1 X2]. split; lia.
      * exact UM1.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * exact W22.
      * exact W13.
      * exact W23.
      * intros X; discriminate X.
      * intros X; discriminate X.
      * exact KF.
    + (* [comment removed for export] *)
      set (R := (DW - (32 - a6))%Z). set (lw2 := ((DW + DX) mod 32)%Z). set (dnf := (R / 32)%Z).
      pose proof (Z.mod_pos_bound (DW + DX) 32 ltac:(lia)) as Hlw. fold lw2 in Hlw.
      pose proof (Z.div_mod R 32 ltac:(lia)) as ER. fold dnf in ER. pose proof (Z.mod_pos_bound R 32 ltac:(lia)) as HRm.
      assert (Elw : lw2 = (R mod 32)%Z) by (subst lw2; replace (DW + DX)%Z with (R + (cdx + 1) * 32)%Z by lia; apply Z_mod_plus_full).
      assert (Hdnf : (0 <= dnf < 2 ^ 26)%Z) by lia.
      destruct (ru_G1a al_rom r4 M1 DW DX (32 - a6) pfp R lw2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl eq_refl ltac:(csr; reflexivity) W17 W10 ltac:(csr; reflexivity))
        as (r5 & RUN5 & X13 & X22 & X14 & X20 & X9 & AG5).
      rzs HW1 RUN5.
      destruct (ru_G1b al_rom set r5 M1 lw2 op (pfp + 4) dnf Hlw Eop Hdnf TBL X14 ltac:(csr; reflexivity) X20 X22) as (r6 & RUN6 & Y23 & Y20 & AG6).
      rzs HW1 RUN6.
      assert (CB : (cdx + (1 + dnf + (if (lw2 =? 0)%Z then 0 else 1)) <= dwpl)%Z) by (destruct (Z.eqb_spec lw2 0); lia).
      assert (FD : (R <? 32)%Z = true -> dnf = 0%Z) by (intros X; apply Z.ltb_lt in X; subst dnf; apply Z.div_small; lia).
      apply (U_general C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) CK Hlo Hhi' SUB Ld Ld0 Ld00 Hdd Hnd set (negb (R <? 32)%Z) (lw2 =? 0)%Z pfp dh dwpl dnf (getr regs 3) (getr regs 4) r6 M1
               Hret ltac:(lia) ltac:(lia) Hdnf).
      * intros X. destruct (Z.ltb_spec R 32) as [Y|Y]; [discriminate X | lia].
      * intros i' Hi'. subst pfp nd.
        pose proof (rop_rows_in datad dwpl dpixh dy dh cdx (1 + dnf + (if (lw2 =? 0)%Z then 0 else 1))%Z i' ltac:(lia) ltac:(lia) ltac:(destruct (lw2 =? 0)%Z; lia) CB Hdyh Hi') as [X1 X2].
        split; [lia|]. destruct (R <? 32)%Z eqn:ER32; cbn [negb]; [rewrite (FD eq_refl) in X2 |]; destruct (lw2 =? 0)%Z; lia.
      * exact UM1.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * rewrite (AG6 13) by (cbv; intuition discriminate). rewrite X13. destruct (R <? 32)%Z; reflexivity.
      * exact Y23.
      * intros X. rewrite (AG6 9) by (cbv; intuition discriminate). rewrite X9. destruct (R <? 32)%Z; [discriminate X | reflexivity].
      * intros X. apply Z.eqb_neq in X. rewrite (Y20 X). destruct (R <? 32)%Z eqn:ER32; cbn [negb]; [rewrite (FD eq_refl)|]; f_equal; lia.
      * exact KF.
Qed.

End RopUniW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
