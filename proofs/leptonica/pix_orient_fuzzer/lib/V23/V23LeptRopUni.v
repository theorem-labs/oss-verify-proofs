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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRop_iface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropUniLow.
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
Ltac fadd v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_add; f_equal; lia).
Ltac faddi v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_addi; f_equal; lia).
Ltac fsub v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_sub; f_equal; lia).
Ltac fsubw v := fixv' (Z_to_bv 64 v) ltac:(rewrite subw_fit by lia; f_equal; lia).
Ltac faddw v := fixv' (Z_to_bv 64 v) ltac:(rewrite addw_fit by lia; f_equal; lia).
Ltac fsext v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
Ltac faddiw v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
Ltac fmul v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_mul; f_equal; lia).
Ltac fmulw v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
Ltac fslli v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_slli by lia; f_equal; lia).
Ltac fsnez := fixv' (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
Ltac fseqz0 := fixv' (Z_to_bv 64 0) ltac:(apply zbv_seqz_nz; lia).
Ltac fsltu0 := fixv' (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
Ltac fslti0 := fixv' (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
(* [comment removed for export] *)
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac condG := first [ condR | condZ ].

(* [comment removed for export] *)
Ltac condSg := pin; rewrite c_lts_Zs by lia; first [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
Ltac fnot v := fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_not by lia; f_equal; lia).
Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition UF (m : word -> option byte) (s : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 19)).

Lemma rdn_UF_above : forall m s regs (a : Z) (n : nat), (32 <= s)%Z -> (s <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z ->
  rdn SEGS (UF m s regs) (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros m s regs a n Hs Ha Hn. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. unfold UF.
  rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.

Lemma UF_outside : forall m s regs (a : word), (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 32 <= u a < s)%Z -> UF m s regs a = m a.
Proof.
  intros m s regs a Hs Hs64 Ha. unfold UF. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vu_A0 : forall regs m (s dpixw d dx dw dh op : Z),
  (32 <= s)%Z -> (s + 16 < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z ->
  (0 <= dpixw <= 20000)%Z -> (0 <= dx <= 20000)%Z -> (0 <= dw <= 20000)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 dpixw ->
  getr regs 13 = Z_to_bv 64 d -> getr regs 15 = Z_to_bv 64 dx -> getr regs 17 = Z_to_bv 64 dw ->
  exists regs',
    msteps SEGS (mkst regs (0x7f3d8 : word) m rom) (mkst regs' (0x7f458 : word) (UF m s regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 6 = Z_to_bv 64 dh
    /\ getr regs' 28 = Z_to_bv 64 (dpixw * d) /\ getr regs' 7 = Z_to_bv 64 (dx * d) /\ getr regs' 17 = Z_to_bv 64 (dw * d)
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 11; 13; 15; 17; 28]%list) regs regs'.
Proof.
  intros regs m s dpixw d dx dw dh op Hs Hs64 Hd Hdpw Hdx Hdw SOK Rdh Rop H2 H11 H13 H15 H17.
  destruct Hd as [-> | ->]; eexists; (split; [
      zv F_7f3d8 D_7f3d8 (Z_to_bv 64 (s - 32));
      stepST F_7f3dc D_7f3dc (Z_to_bv 64 (s - 8)) (getr regs 8) ltac:(sok_in SOK);
      stepST F_7f3e0 D_7f3e0 (Z_to_bv 64 (s - 16)) (getr regs 9) ltac:(sok_in SOK);
      stepST F_7f3e4 D_7f3e4 (Z_to_bv 64 (s - 24)) (getr regs 18) ltac:(sok_in SOK);
      stepST F_7f3e8 D_7f3e8 (Z_to_bv 64 (s - 32)) (getr regs 19) ltac:(sok_in SOK);
      sn F_7f3ec D_7f3ec;
      stepLD F_7f3f0 D_7f3f0 (word_to_le_bytes 8 (Z_to_bv 64 op)) (Z_to_bv 64 op) ltac:(addr_norm; repeat rdn_peel1; exact Rop) ltac:(apply bytes_le_to_Z_8);
      stepLD F_7f3f4 D_7f3f4 (word_to_le_bytes 8 (Z_to_bv 64 dh)) (Z_to_bv 64 dh) ltac:(addr_norm; repeat rdn_peel1; rewrite ?Z.sub_0_r; exact Rdh) ltac:(apply bytes_le_to_Z_8);
      sn F_7f3f8 D_7f3f8 |]).
  - (* [comment removed for export] *)
    stepb_ft F_7f3fc D_7f3fc ltac:(condG).
    sn F_7f400 D_7f400. sn F_7f404 D_7f404. sn F_7f408 D_7f408. fsext dx.
    stepb_tk F_7f40c D_7f40c ltac:(condZ).
    unfold UF. apply mst_refl.
  - rewrite !Z.mul_1_r. repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - (* [comment removed for export] *)
    stepb_tk F_7f3fc D_7f3fc ltac:(condG).
    sn F_7f414 D_7f414. fmul (dpixw * 8)%Z. sn F_7f418 D_7f418. fmulw (dpixw * 8)%Z. stepb_ft F_7f41c D_7f41c ltac:(condG).
    sn F_7f420 D_7f420. fmul (dx * 8)%Z. sn F_7f424 D_7f424. fmulw (dx * 8)%Z. stepb_ft F_7f428 D_7f428 ltac:(condG).
    sn F_7f42c D_7f42c. fmul (dw * 8)%Z. sn F_7f430 D_7f430. fmulw (dw * 8)%Z. stepb_ft F_7f434 D_7f434 ltac:(condG).
    sn F_7f438 D_7f438. sn F_7f43c D_7f43c. fsext (dx * 8)%Z.
    stepb_tk F_7f440 D_7f440 ltac:(condZ).
    unfold UF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_A1 : forall regs m (DX DW DPW dy dh dpixh a6 : Z),
  (0 <= DX)%Z -> (1 <= DW)%Z -> (DX + DW <= DPW)%Z -> (DPW <= 160000)%Z -> (0 <= dy)%Z -> (1 <= dh)%Z -> (dy + dh <= dpixh)%Z -> (dpixh <= 20000)%Z ->
  a6 = (DX mod 32)%Z ->
  getr regs 7 = Z_to_bv 64 DX -> getr regs 17 = Z_to_bv 64 DW -> getr regs 28 = Z_to_bv 64 DPW ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 6 = Z_to_bv 64 dh -> getr regs 12 = Z_to_bv 64 dpixh ->
  exists regs',
    msteps SEGS (mkst regs (0x7f458 : word) m rom) (mkst regs' (if Z.eq_dec a6 0 then (0x7f5a8 : word) else (0x7f4f0 : word)) m rom)
    /\ getr regs' 12 = Z_to_bv 64 dh /\ getr regs' 13 = Z_to_bv 64 DW /\ getr regs' 15 = Z_to_bv 64 a6 /\ getr regs' 29 = Z_to_bv 64 DX
    /\ regs_agree (fun r => In r [5; 12; 13; 15; 28; 29]%list) regs regs'.
Proof.
  intros regs m DX DW DPW dy dh dpixh a6 H0 H1 Hov Hc Hy0 Hh1 Hyh Hch Ea6 R7 R17 R28 R16 R6 R12.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)) as Ha6. rewrite <- Ea6 in Ha6.
  destruct (Z.eq_dec a6 0) as [E|NE]; eexists; (split; [
    sn F_7f458 D_7f458; fsext DW; sn F_7f45c D_7f45c; fsext DX;
    sn F_7f460 D_7f460; fadd (DX + DW)%Z; sn F_7f464 D_7f464; faddw (DX + DW)%Z; stepb_ft F_7f468 D_7f468 ltac:(condG);
    sn F_7f46c D_7f46c; fsext (DX + DW)%Z; sn F_7f470 D_7f470; fsext DPW;
    sn F_7f474 D_7f474; fsubw (DX + DW - DPW)%Z; sn F_7f478 D_7f478; fsub (DX + DW - DPW)%Z; stepb_ft F_7f47c D_7f47c ltac:(condG);
    stepb_tk F_7f480 D_7f480 ltac:(condSg);
    stepb_tk F_7f490 D_7f490 ltac:(condZ);
    sn F_7f4a8 D_7f4a8; fsext dh;
    sn F_7f4ac D_7f4ac; fadd (dy + dh)%Z; sn F_7f4b0 D_7f4b0; faddw (dy + dh)%Z; stepb_ft F_7f4b4 D_7f4b4 ltac:(condG);
    sn F_7f4b8 D_7f4b8; fsext (dy + dh)%Z;
    sn F_7f4bc D_7f4bc; fsubw (dy + dh - dpixh)%Z; sn F_7f4c0 D_7f4c0; fsub (dy + dh - dpixh)%Z; stepb_ft F_7f4c4 D_7f4c4 ltac:(condG);
    stepb_tk F_7f4c8 D_7f4c8 ltac:(condSg);
    sn F_7f4d8 D_7f4d8; fsext DW; stepb_ft F_7f4dc D_7f4dc ltac:(condZ);
    sn F_7f4e0 D_7f4e0; fsext dh; stepb_ft F_7f4e4 D_7f4e4 ltac:(condZ);
    sn F_7f4e8 D_7f4e8; fixv' (Z_to_bv 64 a6) ltac:(rewrite andi_31_Z by lia; rewrite <- Ea6; reflexivity) |]).
  - stepb_tk F_7f4ec D_7f4ec ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_ft F_7f4ec D_7f4ec ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vu_M : forall regs m (DW k : Z),
  (1 <= DW < 2 ^ 31)%Z -> k = (DW mod 32)%Z -> (0 <= k < 32)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x1f4c4 + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 17 = Z_to_bv 64 DW ->
  exists regs',
    msteps SEGS (mkst regs (0x7f5a8 : word) m rom) (mkst regs' (0x7f5ec : word) m rom)
    /\ getr regs' 15 = Z_to_bv 64 k
    /\ regs_agree (fun r => In r [5; 6; 15; 28]%list) regs regs'.
Proof.
  intros regs m DW k HDW Ek Hk TBL H17.
  destruct (Z.eq_dec k 0) as [E0 | NE0].
  - eexists. split.
    + sn F_7f5a8 D_7f5a8. fixv' (Z_to_bv 64 k) ltac:(rewrite andi_31_Z by lia; rewrite <- Ek; reflexivity).
      stepb_tk F_7f5ac D_7f5ac ltac:(condZ).
      apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - destruct (TBL k ltac:(lia)) as (bs & v & Rv & Ev).
    eexists. split.
    + sn F_7f5a8 D_7f5a8. fixv' (Z_to_bv 64 k) ltac:(rewrite andi_31_Z by lia; rewrite <- Ek; reflexivity).
      stepb_ft F_7f5ac D_7f5ac ltac:(condZ).
      sn F_7f5b0 D_7f5b0. fslli (4 * k)%Z.
      sn F_7f5b4 D_7f5b4. sn F_7f5b8 D_7f5b8. sn F_7f5bc D_7f5bc.
      stepb_ft F_7f5c0 D_7f5c0 ltac:(condZ).
      sn F_7f5c4 D_7f5c4. fixv' (Z_to_bv 64 (0x1f4c4 + 4 * k)) ltac:(vclose).
      stepLD F_7f5c8 D_7f5c8 bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev).
      sn F_7f5cc D_7f5cc.
      apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_S : forall (set : bool) regs m (DW DX nfw cdx op datad dy dwpl : Z),
  (1 <= DW < 2 ^ 31)%Z -> (0 <= DX < 2 ^ 31)%Z -> nfw = (DW / 32)%Z -> cdx = (DX / 32)%Z -> op = (if set then 15 else 0)%Z ->
  (0 <= dy < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z -> (0 <= dy * dwpl < 2 ^ 24)%Z -> (0 <= cdx < 2 ^ 26)%Z -> (1 <= datad)%Z -> (datad + 4 * (dy * dwpl) + 4 * cdx < 2 ^ 64)%Z ->
  getr regs 17 = Z_to_bv 64 DW -> getr regs 7 = Z_to_bv 64 DX -> getr regs 11 = Z_to_bv 64 op -> getr regs 10 = Z_to_bv 64 datad ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 14 = Z_to_bv 64 dwpl ->
  exists regs',
    msteps SEGS (mkst regs (0x7f5ec : word) m rom) (mkst regs' (if set then (0x7fb20 : word) else (0x7fbe0 : word)) m rom)
    /\ getr regs' 5 = Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * cdx) /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 17 = Z_to_bv 64 nfw
    /\ getr regs' 29 = Z_to_bv 64 (4 * cdx) /\ getr regs' 30 = Z_to_bv 64 (4 * (dy * dwpl))
    /\ regs_agree (fun r => In r [5; 7; 16; 17; 28; 29; 30]%list) regs regs'.
Proof.
  intros set regs m DW DX nfw cdx op datad dy dwpl HDW HDX Enf Ecd Eop Hdy Hdwpl Hm Hcdx Hdat Hsum H17 H7 H11 H10 H16 H14.
  destruct set; subst op; eexists; (split; [
    sn F_7f5ec D_7f5ec; fmul (dy * dwpl)%Z; sn F_7f5f0 D_7f5f0; fmulw (dy * dwpl)%Z; stepb_ft F_7f5f4 D_7f5f4 ltac:(condG);
    sn F_7f5f8 D_7f5f8; fsext (dy * dwpl)%Z;
    sn F_7f5fc D_7f5fc; fslli (4 * (dy * dwpl))%Z;
    sn F_7f600 D_7f600; fadd (datad + 4 * (dy * dwpl))%Z;
    sn F_7f604 D_7f604; fsnez; sn F_7f608 D_7f608; fseqz0; stepb_ft F_7f60c D_7f60c ltac:(condG);
    sn F_7f610 D_7f610; fsltu0; sn F_7f614 D_7f614; fslti0; sn F_7f618 D_7f618; sn F_7f61c D_7f61c; stepb_ft F_7f620 D_7f620 ltac:(condG);
    sn F_7f624 D_7f624; fixv' (Z_to_bv 64 cdx) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Ecd; reflexivity);
    sn F_7f628 D_7f628; fslli (4 * cdx)%Z;
    sn F_7f62c D_7f62c; fadd (datad + 4 * (dy * dwpl) + 4 * cdx)%Z; stepb_ft F_7f630 D_7f630 ltac:(condZ);
    sn F_7f634 D_7f634; fseqz0; sn F_7f638 D_7f638; stepb_ft F_7f63c D_7f63c ltac:(condG);
    sn F_7f640 D_7f640; fixv' (Z_to_bv 64 nfw) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Enf; reflexivity) |]).
  - stepb_ft F_7f644 D_7f644 ltac:(condZ). sn F_7f648 D_7f648. stepb_tk F_7f64c D_7f64c ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_tk F_7f644 D_7f644 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition pcA_head (set : bool) : word := if set then 0x7fb50 else 0x7fc18.
Definition pcA_inner (set : bool) : word := if set then 0x7fb9c else 0x7fc64.
Definition pcA_part (set : bool) : word := if set then 0x7fbc0 else 0x7fc88.
Definition pcA_next (set : bool) : word := if set then 0x7fb44 else 0x7fc0c.

(* [comment removed for export] *)
Lemma vu_S2 : forall (set : bool) regs m (datad c4 dyw4 : Z),
  (0 <= datad < 2 ^ 64)%Z -> (datad mod 4 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 29 = Z_to_bv 64 c4 -> getr regs 30 = Z_to_bv 64 dyw4 -> getr regs 11 = Z_to_bv 64 (if set then 15 else 0) ->
  exists regs',
    msteps SEGS (mkst regs (if set then (0x7fb20 : word) else (0x7fbe0 : word)) m rom) (mkst regs' (pcA_head set) m rom)
    /\ getr regs' 7 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 28 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 32
    /\ getr regs' (if set then 30 else 29) = Z_to_bv 64 (datad + c4 + dyw4) /\ getr regs' (if set then 29 else 30) = Z_to_bv 64 5
    /\ regs_agree (fun r => In r [6; 7; 10; 11; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros set regs m datad c4 dyw4 Hdat AL H10 H29 H30 H11. unfold pcA_head. destruct set; eexists; (split; [|]).
  - sn F_7fb20 D_7fb20. sn F_7fb24 D_7fb24. sn F_7fb28 D_7fb28. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia).
    sn F_7fb2c D_7fb2c. fadd (datad + c4)%Z. sn F_7fb30 D_7fb30. sn F_7fb34 D_7fb34.
    sn F_7fb38 D_7fb38. fadd (datad + c4 + dyw4)%Z. sn F_7fb3c D_7fb3c. sn F_7fb40 D_7fb40. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_7fbe0 D_7fbe0. sn F_7fbe4 D_7fbe4. sn F_7fbe8 D_7fbe8. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia).
    sn F_7fbec D_7fbec. fadd (datad + c4)%Z. sn F_7fbf0 D_7fbf0.
    sn F_7fbf4 D_7fbf4. fadd (datad + c4 + dyw4)%Z. sn F_7fbf8 D_7fbf8. sn F_7fbfc D_7fbfc. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_H : forall (set big : bool) regs m (i dwpl pf pf' iw DW nfw : Z),
  (0 <= i < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z -> (0 <= i * dwpl < 2 ^ 24)%Z -> (0 <= iw < 2 ^ 24)%Z -> (1 <= pf)%Z -> (pf + 4 * (i * dwpl) < 2 ^ 64)%Z ->
  (if big then 32 <= DW < 2 ^ 31 else 1 <= DW < 32)%Z ->
  getr regs 7 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 5 = Z_to_bv 64 pf -> getr regs 16 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 DW -> getr regs 10 = Z_to_bv 64 32 -> getr regs 11 = Z_to_bv 64 iw ->
  getr regs (if set then 30 else 29) = Z_to_bv 64 pf' -> getr regs 17 = Z_to_bv 64 nfw ->
  exists regs',
    msteps SEGS (mkst regs (pcA_head set) m rom) (mkst regs' (if big then pcA_inner set else pcA_part set) m rom)
    /\ (if big then getr regs' (if set then 8 else 31) = Z_to_bv 64 (pf + 4 * (i * dwpl)) /\ getr regs' (if set then 9 else 8) = Z_to_bv 64 (pf' + 4 * iw)
                    /\ getr regs' (if set then 18 else 9) = Z_to_bv 64 nfw
        else getr regs' (if set then 19 else 18) = Z_to_bv 64 (pf + 4 * (i * dwpl)))
    /\ regs_agree (fun r => In r [8; 9; 18; 19; 31]%list) regs regs'.
Proof.
  intros set big regs m i dwpl pf pf' iw DW nfw Hi Hdwpl Hm Hiw Hpf Hsum HDW R7 R14 R5 R16 R13 R10 R11 Rpf' R17.
  unfold pcA_head, pcA_inner, pcA_part. destruct set.
  - destruct big; eexists; (split; [
      sn F_7fb50 D_7fb50; fmul (i * dwpl)%Z; sn F_7fb54 D_7fb54; fmulw (i * dwpl)%Z; stepb_ft F_7fb58 D_7fb58 ltac:(condG);
      sn F_7fb5c D_7fb5c; fsext (i * dwpl)%Z; sn F_7fb60 D_7fb60; fslli (4 * (i * dwpl))%Z;
      sn F_7fb64 D_7fb64; fadd (pf + 4 * (i * dwpl))%Z;
      sn F_7fb68 D_7fb68; fseqz0; stepb_ft F_7fb6c D_7fb6c ltac:(condG);
      sn F_7fb70 D_7fb70; fsltu0; sn F_7fb74 D_7fb74; fslti0; sn F_7fb78 D_7fb78; sn F_7fb7c D_7fb7c; stepb_ft F_7fb80 D_7fb80 ltac:(condG) |]).
    + stepb_tk F_7fb84 D_7fb84 ltac:(condZ).
      sn F_7fb90 D_7fb90. fslli (4 * iw)%Z. sn F_7fb94 D_7fb94. fadd (pf' + 4 * iw)%Z. sn F_7fb98 D_7fb98. apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    + stepb_ft F_7fb84 D_7fb84 ltac:(condZ). sn F_7fb88 D_7fb88. sn F_7fb8c D_7fb8c. apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - destruct big; eexists; (split; [
      sn F_7fc18 D_7fc18; fmul (i * dwpl)%Z; sn F_7fc1c D_7fc1c; fmulw (i * dwpl)%Z; stepb_ft F_7fc20 D_7fc20 ltac:(condG);
      sn F_7fc24 D_7fc24; fsext (i * dwpl)%Z; sn F_7fc28 D_7fc28; fslli (4 * (i * dwpl))%Z;
      sn F_7fc2c D_7fc2c; fadd (pf + 4 * (i * dwpl))%Z;
      sn F_7fc30 D_7fc30; fseqz0; stepb_ft F_7fc34 D_7fc34 ltac:(condG);
      sn F_7fc38 D_7fc38; fsltu0; sn F_7fc3c D_7fc3c; fslti0; sn F_7fc40 D_7fc40; sn F_7fc44 D_7fc44; stepb_ft F_7fc48 D_7fc48 ltac:(condG) |]).
    + stepb_tk F_7fc4c D_7fc4c ltac:(condZ).
      sn F_7fc58 D_7fc58. fslli (4 * iw)%Z. sn F_7fc5c D_7fc5c. fadd (pf' + 4 * iw)%Z. sn F_7fc60 D_7fc60. apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    + stepb_ft F_7fc4c D_7fc4c ltac:(condZ). sn F_7fc50 D_7fc50. sn F_7fc54 D_7fc54. apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_I : forall (set last : bool) regs m (p acc c : Z),
  (1 <= p)%Z -> (p + 4 < 2 ^ 64)%Z -> (1 <= acc)%Z -> (acc + 4 < 2 ^ 64)%Z -> (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
  store_ok SEGS m (Z_to_bv 64 p) 4 = true ->
  getr regs (if set then 8 else 31) = Z_to_bv 64 p -> getr regs (if set then 9 else 8) = Z_to_bv 64 acc -> getr regs (if set then 18 else 9) = Z_to_bv 64 c ->
  getr regs 28 = Z_to_bv 64 0 -> getr regs (if set then 29 else 30) = Z_to_bv 64 5 ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (pcA_inner set) m rom) (mkst regs' (if last then pcA_part set else pcA_inner set) (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' (if set then 8 else 31) = Z_to_bv 64 (p + 4) /\ getr regs' (if set then 9 else 8) = Z_to_bv 64 (acc + 4)
    /\ getr regs' (if set then 18 else 9) = Z_to_bv 64 (c - 1) /\ getr regs' (if set then 19 else 18) = Z_to_bv 64 (p + 4)
    /\ regs_agree (fun r => In r [8; 9; 18; 19; 31]%list) regs regs'.
Proof.
  intros set last regs m p acc c Hp Hp4 Hacc Hacc4 Hc HL SOK Rp Racc Rc R28 R5.
  unfold pcA_inner, pcA_part. destruct set.
  - eexists; eexists; split; [
      sn F_7fb9c D_7fb9c; faddi (acc + 4)%Z; stepb_ft F_7fba0 D_7fba0 ltac:(condZ); stepb_ft F_7fba4 D_7fba4 ltac:(condZ); stepb_ft F_7fba8 D_7fba8 ltac:(condG);
      sn F_7fbac D_7fbac; faddi (p + 4)%Z; sn F_7fbb0 D_7fbb0; faddiw (c - 1)%Z;
      stepST F_7fbb4 D_7fbb4 (Z_to_bv 64 p) (getr regs 31) ltac:(store_ok_peel; exact SOK);
      sn F_7fbb8 D_7fbb8;
      (destruct last; [ stepb_ft F_7fbbc D_7fbbc ltac:(condZ); apply mst_refl | stepb_tk F_7fbbc D_7fbbc ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
  - eexists; eexists; split; [
      sn F_7fc64 D_7fc64; faddi (acc + 4)%Z; stepb_ft F_7fc68 D_7fc68 ltac:(condZ); stepb_ft F_7fc6c D_7fc6c ltac:(condZ); stepb_ft F_7fc70 D_7fc70 ltac:(condG);
      sn F_7fc74 D_7fc74; faddi (p + 4)%Z; sn F_7fc78 D_7fc78; faddiw (c - 1)%Z;
      stepST F_7fc7c D_7fc7c (Z_to_bv 64 p) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK);
      sn F_7fc80 D_7fc80;
      (destruct last; [ stepb_ft F_7fc84 D_7fc84 ltac:(condZ); apply mst_refl | stepb_tk F_7fc84 D_7fc84 ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
Qed.

(* [comment removed for export] *)
Lemma vu_P : forall (set : bool) regs m (pd k : Z) (bd : list byte) (vd : word),
  (1 <= pd < 2 ^ 64)%Z -> (pd mod 4 = 0)%Z -> (1 <= k < 32)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> bytes_le_to_Z bd = bv_unsigned vd -> store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  getr regs (if set then 19 else 18) = Z_to_bv 64 pd -> getr regs 15 = Z_to_bv 64 k ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (pcA_part set) m rom) (mkst regs' (pcA_next set) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ regs_agree (fun r => In r [8; 31]%list) regs regs'.
Proof.
  intros set regs m pd k bd vd Hpd AL Hk Rd Evd SOK Rp R15. unfold pcA_part, pcA_next. destruct set; eexists; eexists; (split; [|]).
  - stepb_ft F_7fbc0 D_7fbc0 ltac:(condZ). stepb_ft F_7fbc4 D_7fbc4 ltac:(condZ).
    sn F_7fbc8 D_7fbc8. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia). stepb_ft F_7fbcc D_7fbcc ltac:(condG).
    stepLD F_7fbd0 D_7fbd0 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_7fbd4 D_7fbd4.
    stepST F_7fbd8 D_7fbd8 (Z_to_bv 64 pd) (v_or (v_lw vd) (getr regs 6)) ltac:(store_ok_peel; exact SOK).
    sn F_7fbdc D_7fbdc. apply mst_refl.
  - gres. solve_regs_agree.
  - stepb_ft F_7fc88 D_7fc88 ltac:(condZ). stepb_ft F_7fc8c D_7fc8c ltac:(condZ).
    sn F_7fc90 D_7fc90. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia). stepb_tk F_7fc94 D_7fc94 ltac:(condG).
    stepLD F_7fc00 D_7fc00 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd).
    sn F_7fc04 D_7fc04.
    stepST F_7fc08 D_7fc08 (Z_to_bv 64 pd) (v_and (v_lw vd) (getr regs 6)) ltac:(store_ok_peel; exact SOK).
    apply mst_refl.
  - gres. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_P0 : forall (set : bool) regs m, getr regs 15 = Z_to_bv 64 0 ->
  exists regs', msteps SEGS (mkst regs (pcA_part set) m rom) (mkst regs' (pcA_next set) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof.
  intros set regs m H15. unfold pcA_part, pcA_next. destruct set; eexists; (split; [|]).
  - stepb_tk F_7fbc0 D_7fbc0 ltac:(condZ). apply mst_refl.
  - solve_regs_agree.
  - stepb_tk F_7fc88 D_7fc88 ltac:(condZ). apply mst_refl.
  - solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_N : forall (set last : bool) regs m (i dh iw dwpl : Z),
  (0 <= i)%Z -> (if last then i + 1 = dh else i + 1 < dh)%Z -> (dh < 2 ^ 31)%Z -> (0 <= iw)%Z -> (0 <= dwpl)%Z -> (iw + dwpl < 2 ^ 31)%Z ->
  getr regs 7 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 iw -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 12 = Z_to_bv 64 dh ->
  exists regs', msteps SEGS (mkst regs (pcA_next set) m rom) (mkst regs' (if last then (0x7fb08 : word) else pcA_head set) m rom)
    /\ getr regs' 7 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 (iw + dwpl)
    /\ regs_agree (fun r => In r [7; 11]%list) regs regs'.
Proof.
  intros set last regs m i dh iw dwpl Hi HL Hdh Hiw Hdwpl Hsum R7 R11 R14 R12. unfold pcA_next, pcA_head.
  destruct set; destruct last; eexists; (split; [|]).
  - sn F_7fb44 D_7fb44. faddiw (i + 1)%Z. sn F_7fb48 D_7fb48. faddw (iw + dwpl)%Z. stepb_tk F_7fb4c D_7fb4c ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_7fb44 D_7fb44. faddiw (i + 1)%Z. sn F_7fb48 D_7fb48. faddw (iw + dwpl)%Z. stepb_ft F_7fb4c D_7fb4c ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_7fc0c D_7fc0c. faddiw (i + 1)%Z. sn F_7fc10 D_7fc10. faddw (iw + dwpl)%Z. stepb_tk F_7fc14 D_7fc14 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_7fc0c D_7fc0c. faddiw (i + 1)%Z. sn F_7fc10 D_7fc10. faddw (iw + dwpl)%Z. stepb_ft F_7fc14 D_7fc14 ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition ucells (M : word -> option byte) (s : Z) (v0 v1 v2 v3 : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v0) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v1) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v2) /\
  rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v3).

Lemma ucells_UF : forall m s regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ucells (UF m s regs) s (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19).
Proof. intros m s regs Hs Hs64. unfold ucells, UF. repeat split; rdn_chain. Qed.

Lemma ucells_frame : forall M M' s v0 v1 v2 v3, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  ucells M s v0 v1 v2 v3 -> (forall x : word, (s - 32 <= u x < s)%Z -> M' x = M x) -> ucells M' s v0 v1 v2 v3.
Proof.
  intros M M' s v0 v1 v2 v3 Hs Hs64 (C0 & C1 & C2 & C3) E.
  unfold ucells. repeat split; [rewrite <- C0 | rewrite <- C1 | rewrite <- C2 | rewrite <- C3];
    (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
Qed.

(* [comment removed for export] *)
Lemma vu_E : forall regs m (s : Z) (ret v0 v1 v2 v3 : word),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> ucells m s v0 v1 v2 v3 ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 1 = ret ->
  exists regs',
    msteps SEGS (mkst regs (0x7fb08 : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3
    /\ regs_agree (fun r => In r [2; 8; 9; 18; 19]%list) regs regs'.
Proof.
  intros regs m s ret v0 v1 v2 v3 Hs Hs64 Hret (C0 & C1 & C2 & C3) R2 R1.
  eexists. split.
  - stepLD8 F_7fb08 D_7fb08 v0. stepLD8 F_7fb0c D_7fb0c v1. stepLD8 F_7fb10 D_7fb10 v2. stepLD8 F_7fb14 D_7fb14 v3.
    zv F_7fb18 D_7fb18 (Z_to_bv 64 s).
    stepret F_7fb1c D_7fb1c ret ltac:(first [exact R1 | pin; reflexivity]).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vu_G0 : forall regs m (a6 DW DX cdx datad dy dwpl : Z),
  (1 <= a6 < 32)%Z -> (1 <= DW < 2 ^ 31)%Z -> (0 <= DX < 2 ^ 31)%Z -> cdx = (DX / 32)%Z ->
  (0 <= dy < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z -> (0 <= dy * dwpl < 2 ^ 24)%Z -> (0 <= cdx < 2 ^ 26)%Z -> (1 <= datad)%Z -> (datad + 4 * (dy * dwpl) + 4 * cdx < 2 ^ 64)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x1f440 + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 15 = Z_to_bv 64 a6 -> getr regs 17 = Z_to_bv 64 DW -> getr regs 13 = Z_to_bv 64 DW -> getr regs 7 = Z_to_bv 64 DX -> getr regs 10 = Z_to_bv 64 datad ->
  getr regs 16 = Z_to_bv 64 dy -> getr regs 14 = Z_to_bv 64 dwpl ->
  exists regs',
    msteps SEGS (mkst regs (0x7f4f0 : word) m rom) (mkst regs' (if (DW <? 32 - a6)%Z then (0x7f570 : word) else (0x7f5d0 : word)) m rom)
    /\ getr regs' 30 = Z_to_bv 64 (32 - a6) /\ getr regs' 5 = Z_to_bv 64 (datad + 4 * (dy * dwpl) + 4 * cdx) /\ getr regs' 16 = Z_to_bv 64 1
    /\ getr regs' 10 = Z_to_bv 64 (DW - (32 - a6))
    /\ regs_agree (fun r => In r [5; 7; 8; 10; 15; 16; 28; 30; 31]%list) regs regs'.
Proof.
  intros regs m a6 DW DX cdx datad dy dwpl Ha6 HDW HDX Ecd Hdy Hdwpl Hm Hcdx Hdat Hsum TBL H15 H17 H13 H7 H10 H16 H14.
  destruct (TBL (32 - a6)%Z ltac:(lia)) as (bs & v & Rv & Ev).
  destruct (Z.ltb_spec DW (32 - a6)) as [LT|GE]; eexists; (split; [
    sn F_7f4f0 D_7f4f0; sn F_7f4f4 D_7f4f4;
    sn F_7f4f8 D_7f4f8; fsub (32 - a6)%Z;
    sn F_7f4fc D_7f4fc;
    sn F_7f500 D_7f500; fslli (4 * (32 - a6))%Z;
    sn F_7f504 D_7f504; stepb_ft F_7f508 D_7f508 ltac:(condZ);
    sn F_7f50c D_7f50c; fmul (dy * dwpl)%Z; sn F_7f510 D_7f510; fmulw (dy * dwpl)%Z; stepb_ft F_7f514 D_7f514 ltac:(condG);
    sn F_7f518 D_7f518; fsext (dy * dwpl)%Z;
    sn F_7f51c D_7f51c; fslli (4 * (dy * dwpl))%Z;
    sn F_7f520 D_7f520; fadd (datad + 4 * (dy * dwpl))%Z;
    sn F_7f524 D_7f524; fsnez; sn F_7f528 D_7f528; fseqz0; stepb_ft F_7f52c D_7f52c ltac:(condG);
    sn F_7f530 D_7f530; fsltu0; sn F_7f534 D_7f534; fslti0; sn F_7f538 D_7f538; sn F_7f53c D_7f53c; stepb_ft F_7f540 D_7f540 ltac:(condG);
    sn F_7f544 D_7f544; fixv' (Z_to_bv 64 cdx) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Ecd; reflexivity);
    sn F_7f548 D_7f548; fslli (4 * cdx)%Z;
    sn F_7f54c D_7f54c; fadd (datad + 4 * (dy * dwpl) + 4 * cdx)%Z; stepb_ft F_7f550 D_7f550 ltac:(condZ);
    sn F_7f554 D_7f554; fseqz0; sn F_7f558 D_7f558; stepb_ft F_7f55c D_7f55c ltac:(condG);
    sn F_7f560 D_7f560; fixv' (Z_to_bv 64 (0x1f440 + 4 * (32 - a6))) ltac:(vclose);
    stepLD F_7f564 D_7f564 bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev);
    sn F_7f568 D_7f568; fsubw (DW - (32 - a6))%Z |]).
  - stepb_ft F_7f56c D_7f56c ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - stepb_tk F_7f56c D_7f56c ltac:(condZ). apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_G1d : forall regs m (a6 DW : Z),
  (1 <= a6 < 32)%Z -> (1 <= DW)%Z -> (DW < 32 - a6)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x1f4c4 + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 10 = Z_to_bv 64 (DW - (32 - a6)) ->
  exists regs',
    msteps SEGS (mkst regs (0x7f570 : word) m rom) (mkst regs' (0x7f6fc : word) m rom)
    /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0 /\ getr regs' 28 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [7; 10; 15; 16; 17; 28]%list) regs regs'.
Proof.
  intros regs m a6 DW Ha6 HDW HLT TBL H10.
  destruct (TBL (DW + a6)%Z ltac:(lia)) as (bs & v & Rv & Ev).
  eexists. split.
  - sn F_7f570 D_7f570. fixv' (Z_to_bv 64 (DW + a6)) ltac:(rewrite addiw_fit by lia; f_equal; lia).
    sn F_7f574 D_7f574. stepb_ft F_7f578 D_7f578 ltac:(condZ).
    sn F_7f57c D_7f57c. fslli (4 * (DW + a6))%Z.
    sn F_7f580 D_7f580. sn F_7f584 D_7f584. sn F_7f588 D_7f588. stepb_ft F_7f58c D_7f58c ltac:(condZ).
    sn F_7f590 D_7f590. sn F_7f594 D_7f594.
    sn F_7f598 D_7f598. fixv' (Z_to_bv 64 (0x1f4c4 + 4 * (DW + a6))) ltac:(vclose).
    stepLD F_7f59c D_7f59c bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev).
    sn F_7f5a0 D_7f5a0. sn F_7f5a4 D_7f5a4. sn F_7f6f8 D_7f6f8.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_G1a : forall regs m (R dnf pfp : Z),
  (0 <= R < 2 ^ 31)%Z -> dnf = (R / 32)%Z -> (1 <= pfp)%Z -> (pfp + 4 < 2 ^ 64)%Z ->
  getr regs 10 = Z_to_bv 64 R -> getr regs 5 = Z_to_bv 64 pfp ->
  exists regs',
    msteps SEGS (mkst regs (0x7f5d0 : word) m rom) (mkst regs' (0x7f6fc : word) m rom)
    /\ getr regs' 15 = Z_to_bv 64 dnf /\ getr regs' 28 = Z_to_bv 64 (if (dnf =? 0)%Z then 1 else 0)
    /\ (dnf <> 0%Z -> getr regs' 16 = Z_to_bv 64 (pfp + 4))
    /\ regs_agree (fun r => In r [10; 15; 16; 28]%list) regs regs'.
Proof.
  intros regs m R dnf pfp HR Ednf Hp Hp4 H10 H5.
  assert (Hdnf : (0 <= dnf)%Z) by (subst dnf; apply Z.div_pos; lia).
  destruct (Z.eqb_spec dnf 0) as [E0|NE0]; eexists; (split; [
    sn F_7f5d0 D_7f5d0; fixv' (Z_to_bv 64 dnf) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite <- Ednf; reflexivity) |]).
  - stepb_tk F_7f5d4 D_7f5d4 ltac:(condZ). sn F_7f6f4 D_7f6f4. sn F_7f6f8 D_7f6f8. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (intros X; contradiction). solve_regs_agree.
  - assert (Hd2 : (dnf < 2 ^ 31)%Z) by (subst dnf; apply Z.div_lt_upper_bound; lia).
    stepb_ft F_7f5d4 D_7f5d4 ltac:(condZ).
    sn F_7f5d8 D_7f5d8. faddi (pfp + 4)%Z. sn F_7f5dc D_7f5dc. stepb_ft F_7f5e0 D_7f5e0 ltac:(condZ).
    sn F_7f5e4 D_7f5e4. sn F_7f5e8 D_7f5e8. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_G2a : forall regs m (DX DW dfw lw2 : Z),
  (0 <= DX <= 160000)%Z -> (1 <= DW <= 160000)%Z -> (1 <= dfw < 32)%Z -> lw2 = ((DX + DW) mod 32)%Z -> (0 <= lw2 < 32)%Z ->
  getr regs 29 = Z_to_bv 64 DX -> getr regs 13 = Z_to_bv 64 DW -> getr regs 30 = Z_to_bv 64 dfw ->
  exists regs',
    msteps SEGS (mkst regs (0x7f6fc : word) m rom) (mkst regs' (0x7f718 : word) m rom)
    /\ getr regs' 17 = Z_to_bv 64 (if ((DW <? dfw) || (lw2 =? 0))%Z then 1 else 0) /\ getr regs' 10 = Z_to_bv 64 lw2
    /\ regs_agree (fun r => In r [10; 13; 17]%list) regs regs'.
Proof.
  intros regs m DX DW dfw lw2 HDX HDW Hdfw Elw Hlw R29 R13 R30.
  assert (V1 : v_sltu (Z_to_bv 64 DW) (Z_to_bv 64 dfw) = Z_to_bv 64 (if (DW <? dfw)%Z then 1 else 0)) by (rewrite v_sltu_Z by lia; reflexivity).
  assert (V2 : v_sltiu (Z_to_bv 64 lw2) 1 = Z_to_bv 64 (if (lw2 =? 0)%Z then 1 else 0)) by (apply zbv_seqz; lia).
  eexists. split.
  - sn F_7f6fc D_7f6fc. fadd (DX + DW)%Z. sn F_7f700 D_7f700. faddw (DX + DW)%Z. stepb_ft F_7f704 D_7f704 ltac:(condG).
    sn F_7f708 D_7f708. rewrite V1.
    sn F_7f70c D_7f70c. fixv' (Z_to_bv 64 lw2) ltac:(rewrite andi_31_Z by lia; rewrite <- Elw; reflexivity).
    sn F_7f710 D_7f710. rewrite V2.
    sn F_7f714 D_7f714. fixv' (Z_to_bv 64 (if ((DW <? dfw) || (lw2 =? 0))%Z then 1 else 0)) ltac:(destruct (DW <? dfw)%Z; destruct (lw2 =? 0)%Z; apply bv_eq; reflexivity).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition pcG_l1s (set : bool) : word := if set then 0x7f8a0 else 0x7f734.
Lemma vu_G2b : forall (set nolast : bool) regs m (lw2 pfp dnf op : Z),
  (if nolast then True else 1 <= lw2 < 32)%Z -> (1 <= pfp)%Z -> (0 <= dnf < 2 ^ 26)%Z -> (pfp + 4 + 4 * dnf < 2 ^ 64)%Z -> op = (if set then 15 else 0)%Z ->
  (forall j, (1 <= j <= 31)%Z -> exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (0x1f4c4 + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v) ->
  getr regs 17 = Z_to_bv 64 (if nolast then 1 else 0) -> getr regs 10 = Z_to_bv 64 lw2 -> getr regs 5 = Z_to_bv 64 pfp ->
  getr regs 15 = Z_to_bv 64 dnf -> getr regs 11 = Z_to_bv 64 op ->
  exists regs',
    msteps SEGS (mkst regs (0x7f718 : word) m rom) (mkst regs' (pcG_l1s set) m rom)
    /\ (nolast = false -> getr regs' 10 = Z_to_bv 64 (pfp + 4 + 4 * dnf))
    /\ regs_agree (fun r => In r [10; 13; 29; 30; 31]%list) regs regs'.
Proof.
  intros set nolast regs m lw2 pfp dnf op Hlw Hp Hdnf Hsum Eop TBL R17 R10 R5 R15 R11. unfold pcG_l1s.
  destruct nolast.
  - destruct set; subst op; eexists; (split; [ stepb_ft F_7f718 D_7f718 ltac:(condZ); sn F_7f71c D_7f71c; sn F_7f720 D_7f720 |]).
    + stepb_tk F_7f724 D_7f724 ltac:(condZ). apply mst_refl.
    + repeat split; try (intros X; discriminate X). solve_regs_agree.
    + stepb_ft F_7f724 D_7f724 ltac:(condZ). sn F_7f728 D_7f728. stepb_ft F_7f72c D_7f72c ltac:(condZ). stepb_ft F_7f730 D_7f730 ltac:(condZ). apply mst_refl.
    + repeat split; try (intros X; discriminate X). solve_regs_agree.
  - destruct (TBL lw2 ltac:(lia)) as (bs & v & Rv & Ev).
    destruct set; subst op; eexists; (split; [
      stepb_tk F_7f718 D_7f718 ltac:(condZ);
      sn F_7f85c D_7f85c; fslli (4 * lw2)%Z; sn F_7f860 D_7f860; sn F_7f864 D_7f864; sn F_7f868 D_7f868; stepb_ft F_7f86c D_7f86c ltac:(condZ);
      sn F_7f870 D_7f870; faddi (pfp + 4)%Z; sn F_7f874 D_7f874; stepb_ft F_7f878 D_7f878 ltac:(condZ);
      sn F_7f87c D_7f87c; fslli (4 * dnf)%Z; sn F_7f880 D_7f880; fnot (2 ^ 64 - 1 - (pfp + 4))%Z; stepb_ft F_7f884 D_7f884 ltac:(condZ);
      sn F_7f888 D_7f888; fixv' (Z_to_bv 64 (0x1f4c4 + 4 * lw2)) ltac:(vclose);
      stepLD F_7f88c D_7f88c bs v ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rv) ltac:(exact Ev);
      sn F_7f890 D_7f890; fslli (4 * dnf)%Z; sn F_7f894 D_7f894; fadd (pfp + 4 + 4 * dnf)%Z; sn F_7f898 D_7f898 |]).
    + stepb_ft F_7f89c D_7f89c ltac:(condZ). apply mst_refl.
    + repeat split; try (intros _; gres; pin; reflexivity). solve_regs_agree.
    + stepb_tk F_7f89c D_7f89c ltac:(condZ). sn F_7f728 D_7f728. stepb_ft F_7f72c D_7f72c ltac:(condZ). stepb_ft F_7f730 D_7f730 ltac:(condZ). apply mst_refl.
    + repeat split; try (intros _; gres; pin; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition pcG_l1 (set : bool) : word := if set then 0x7f8b8 else 0x7f750.    (* [comment removed for export] *)
Definition pcG_l1x (set : bool) : word := if set then 0x7f8f0 else 0x7f788.   (* [comment removed for export] *)
Definition pcG_l2 (set : bool) : word := if set then 0x7f908 else 0x7f79c.    (* [comment removed for export] *)
Definition pcG_l2i (set : bool) : word := if set then 0x7f920 else 0x7f7b4.   (* [comment removed for export] *)
Definition pcG_l2n (set : bool) : word := if set then 0x7f948 else 0x7f7dc.   (* [comment removed for export] *)
Definition pcG_l3t (set : bool) : word := if set then 0x7f978 else 0x7f80c.   (* [comment removed for export] *)
Definition pcG_l3 (set : bool) : word := if set then 0x7f988 else 0x7f820.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vu_L1s : forall (set : bool) regs m (pfp dwpl dh : Z), (0 <= pfp < 2 ^ 64)%Z -> (pfp mod 4 = 0)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  getr regs 5 = Z_to_bv 64 pfp -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 6 = Z_to_bv 64 dh ->
  exists regs', msteps SEGS (mkst regs (pcG_l1s set) m rom) (mkst regs' (pcG_l1 set) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 30 = Z_to_bv 64 pfp /\ getr regs' 29 = Z_to_bv 64 dh
    /\ regs_agree (fun r => In r [7; 11; 14; 29; 30]%list) regs regs'.
Proof.
  intros set regs m pfp dwpl dh Hp AL Hdwpl R5 R14 R6. unfold pcG_l1s, pcG_l1. destruct set; eexists; (split; [|]).
  - sn F_7f8a0 D_7f8a0. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia). stepb_ft F_7f8a4 D_7f8a4 ltac:(condG).
    sn F_7f8a8 D_7f8a8. fslli (4 * dwpl)%Z. sn F_7f8ac D_7f8ac. fslti0. sn F_7f8b0 D_7f8b0. sn F_7f8b4 D_7f8b4. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - sn F_7f734 D_7f734. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia). stepb_ft F_7f738 D_7f738 ltac:(condG).
    sn F_7f73c D_7f73c.
    sn F_7f740 D_7f740. fslli (4 * dwpl)%Z. sn F_7f744 D_7f744. fslti0. sn F_7f748 D_7f748. sn F_7f74c D_7f74c. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_L1 : forall (set last : bool) regs m (p c stp : Z) (bd : list byte) (vd : word),
  (1 <= p)%Z -> (0 <= stp)%Z -> (p + stp < 2 ^ 64)%Z -> (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
  rdn SEGS m (Z_to_bv 64 p) 4 = Some bd -> bytes_le_to_Z bd = bv_unsigned vd -> store_ok SEGS m (Z_to_bv 64 p) 4 = true ->
  getr regs 5 = Z_to_bv 64 p -> getr regs 30 = Z_to_bv 64 p -> getr regs 29 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 stp -> getr regs 14 = Z_to_bv 64 0 ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (pcG_l1 set) m rom) (mkst regs' (if last then pcG_l1x set else pcG_l1 set) (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 5 = Z_to_bv 64 (p + stp) /\ getr regs' 30 = Z_to_bv 64 (p + stp) /\ getr regs' 29 = Z_to_bv 64 (c - 1)
    /\ regs_agree (fun r => In r [5; 8; 29; 30; 31]%list) regs regs'.
Proof.
  intros set last regs m p c stp bd vd Hp Hstp Hsum Hc HL Rd Evd SOK R5 R30 R29 R11 R14. unfold pcG_l1, pcG_l1x.
  destruct set.
  - eexists; eexists; split; [
      stepb_ft F_7f8b8 D_7f8b8 ltac:(condZ);
      stepLD F_7f8bc D_7f8bc bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd);
      sn F_7f8c0 D_7f8c0; sn F_7f8c4 D_7f8c4; fadd (p + stp)%Z;
      stepST F_7f8c8 D_7f8c8 (Z_to_bv 64 p) (v_or (v_lw vd) (getr regs 7)) ltac:(store_ok_peel; exact SOK);
      stepb_ft F_7f8cc D_7f8cc ltac:(condZ);
      sn F_7f8d0 D_7f8d0; fsltu0; sn F_7f8d4 D_7f8d4; sn F_7f8d8 D_7f8d8; stepb_ft F_7f8dc D_7f8dc ltac:(condG);
      sn F_7f8e0 D_7f8e0; faddiw (c - 1)%Z; sn F_7f8e4 D_7f8e4; fadd (p + stp)%Z; sn F_7f8e8 D_7f8e8;
      (destruct last; [ stepb_ft F_7f8ec D_7f8ec ltac:(condZ); apply mst_refl | stepb_tk F_7f8ec D_7f8ec ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
  - eexists; eexists; split; [
      stepb_ft F_7f750 D_7f750 ltac:(condZ);
      stepLD F_7f754 D_7f754 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd);
      sn F_7f758 D_7f758; sn F_7f75c D_7f75c; fadd (p + stp)%Z;
      stepST F_7f760 D_7f760 (Z_to_bv 64 p) (v_and (v_lw vd) (getr regs 7)) ltac:(store_ok_peel; exact SOK);
      stepb_ft F_7f764 D_7f764 ltac:(condZ);
      sn F_7f768 D_7f768; fsltu0; sn F_7f76c D_7f76c; sn F_7f770 D_7f770; stepb_ft F_7f774 D_7f774 ltac:(condG);
      sn F_7f778 D_7f778; faddiw (c - 1)%Z; sn F_7f77c D_7f77c; fadd (p + stp)%Z; sn F_7f780 D_7f780;
      (destruct last; [ stepb_ft F_7f784 D_7f784 ltac:(condZ); apply mst_refl | stepb_tk F_7f784 D_7f784 ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
Qed.

(* [comment removed for export] *)
Lemma vu_L1x : forall (set full : bool) regs m (P2 : Z), (0 <= P2 < 2 ^ 64)%Z -> (P2 mod 4 = 0)%Z ->
  getr regs 28 = Z_to_bv 64 (if full then 0 else 1) -> (full = true -> getr regs 16 = Z_to_bv 64 P2) ->
  exists regs', msteps SEGS (mkst regs (pcG_l1x set) m rom) (mkst regs' (if full then pcG_l2 set else pcG_l3t set) m rom)
    /\ (full = true -> getr regs' 5 = Z_to_bv 64 0 /\ getr regs' 7 = Z_to_bv 64 1 /\ getr regs' (if set then 29 else 28) = Z_to_bv 64 P2)
    /\ regs_agree (fun r => In r (if full then [5; 7; 28; 29] else [])%list) regs regs'.
Proof.
  intros set full regs m P2 HP2 AL R28 R16. unfold pcG_l1x, pcG_l2, pcG_l3t. destruct set; destruct full; eexists; (split; [|]).
  - specialize (R16 eq_refl). stepb_ft F_7f8f0 D_7f8f0 ltac:(condZ). sn F_7f8f4 D_7f8f4.
    sn F_7f8f8 D_7f8f8. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia). sn F_7f8fc D_7f8fc. sn F_7f900 D_7f900. sn F_7f904 D_7f904. apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity). all: try solve_regs_agree.
  - stepb_tk F_7f8f0 D_7f8f0 ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; discriminate). all: try solve_regs_agree.
  - specialize (R16 eq_refl). stepb_ft F_7f788 D_7f788 ltac:(condZ). sn F_7f78c D_7f78c.
    sn F_7f790 D_7f790. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia). sn F_7f794 D_7f794. sn F_7f798 D_7f798. apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity). all: try solve_regs_agree.
  - stepb_tk F_7f788 D_7f788 ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; discriminate). all: try solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_L2h : forall (set : bool) regs m (dnf rp chk : Z), (1 <= dnf < 2 ^ 26)%Z -> (1 <= rp < 2 ^ 64)%Z ->
  getr regs 15 = Z_to_bv 64 dnf -> getr regs 16 = Z_to_bv 64 rp -> getr regs 7 = Z_to_bv 64 1 -> getr regs (if set then 29 else 28) = Z_to_bv 64 chk ->
  exists regs', msteps SEGS (mkst regs (pcG_l2 set) m rom) (mkst regs' (pcG_l2i set) m rom)
    /\ getr regs' (if set then 8 else 31) = Z_to_bv 64 rp /\ getr regs' (if set then 9 else 8) = Z_to_bv 64 chk /\ getr regs' (if set then 18 else 9) = Z_to_bv 64 dnf
    /\ getr regs' (if set then 30 else 29) = Z_to_bv 64 1 /\ getr regs' (if set then 31 else 30) = Z_to_bv 64 1
    /\ getr regs' (if set then 29 else 28) = Z_to_bv 64 chk
    /\ regs_agree (fun r => In r [8; 9; 18; 29; 30; 31]%list) regs regs'.
Proof.
  intros set regs m dnf rp chk Hdnf Hrp R15 R16 R7 Rchk. unfold pcG_l2, pcG_l2i. destruct set; eexists; (split; [|]).
  - stepb_ft F_7f908 D_7f908 ltac:(condZ). sn F_7f90c D_7f90c. fsnez. sn F_7f910 D_7f910.
    sn F_7f914 D_7f914. sn F_7f918 D_7f918. sn F_7f91c D_7f91c. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  - stepb_ft F_7f79c D_7f79c ltac:(condZ). sn F_7f7a0 D_7f7a0. fsnez. sn F_7f7a4 D_7f7a4.
    sn F_7f7a8 D_7f7a8. sn F_7f7ac D_7f7ac. sn F_7f7b0 D_7f7b0. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_L2i : forall (set last : bool) regs m (p q rp c : Z),
  (1 <= rp)%Z -> (rp <= q)%Z -> (q + 4 < 2 ^ 64)%Z -> (0 <= p)%Z -> (p + 4 < 2 ^ 64)%Z -> (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
  store_ok SEGS m (Z_to_bv 64 p) 4 = true ->
  getr regs (if set then 8 else 31) = Z_to_bv 64 p -> getr regs (if set then 9 else 8) = Z_to_bv 64 q -> getr regs (if set then 18 else 9) = Z_to_bv 64 c ->
  getr regs 16 = Z_to_bv 64 rp -> getr regs (if set then 30 else 29) = Z_to_bv 64 1 -> getr regs (if set then 31 else 30) = Z_to_bv 64 1 ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (pcG_l2i set) m rom) (mkst regs' (if last then pcG_l2n set else pcG_l2i set) (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' (if set then 8 else 31) = Z_to_bv 64 (p + 4) /\ getr regs' (if set then 9 else 8) = Z_to_bv 64 (q + 4)
    /\ getr regs' (if set then 18 else 9) = Z_to_bv 64 (c - 1) /\ getr regs' (if set then 31 else 30) = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [8; 9; 18; 19; 31]%list) regs regs'.
Proof.
  intros set last regs m p q rp c Hrp Hq Hq4 Hp Hp4 Hc HL SOK Rp Rq Rc R16 Rf1 Rf2. unfold pcG_l2i, pcG_l2n. destruct set.
  - eexists; eexists; split; [
      stepb_ft F_7f920 D_7f920 ltac:(condZ);
      sn F_7f924 D_7f924; fseqz0; sn F_7f928 D_7f928; stepb_ft F_7f92c D_7f92c ltac:(condG); stepb_ft F_7f930 D_7f930 ltac:(condG);
      stepST F_7f934 D_7f934 (Z_to_bv 64 p) (getr regs 28) ltac:(store_ok_peel; exact SOK);
      sn F_7f938 D_7f938; faddi (c - 1)%Z; sn F_7f93c D_7f93c; faddi (q + 4)%Z; sn F_7f940 D_7f940; faddi (p + 4)%Z;
      (destruct last; [ stepb_ft F_7f944 D_7f944 ltac:(condZ); apply mst_refl | stepb_tk F_7f944 D_7f944 ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
  - eexists; eexists; split; [
      stepb_ft F_7f7b4 D_7f7b4 ltac:(condZ);
      sn F_7f7b8 D_7f7b8; fseqz0; sn F_7f7bc D_7f7bc; stepb_ft F_7f7c0 D_7f7c0 ltac:(condG); stepb_ft F_7f7c4 D_7f7c4 ltac:(condG);
      stepST F_7f7c8 D_7f7c8 (Z_to_bv 64 p) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK);
      sn F_7f7cc D_7f7cc; faddi (c - 1)%Z; sn F_7f7d0 D_7f7d0; faddi (q + 4)%Z; sn F_7f7d4 D_7f7d4; faddi (p + 4)%Z;
      (destruct last; [ stepb_ft F_7f7d8 D_7f7d8 ltac:(condZ); apply mst_refl | stepb_tk F_7f7d8 D_7f7d8 ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
Qed.

(* [comment removed for export] *)
Lemma vu_L2n : forall (set last : bool) regs m (rp chk stp i dh : Z),
  (1 <= rp)%Z -> (0 <= stp)%Z -> (rp + stp < 2 ^ 64)%Z -> (0 <= i)%Z -> (if last then i + 1 = dh else i + 1 < dh)%Z -> (dh < 2 ^ 31)%Z ->
  getr regs 16 = Z_to_bv 64 rp -> getr regs 11 = Z_to_bv 64 stp -> getr regs 14 = Z_to_bv 64 0 -> getr regs 5 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 dh ->
  getr regs (if set then 29 else 28) = Z_to_bv 64 chk ->
  exists regs', msteps SEGS (mkst regs (pcG_l2n set) m rom) (mkst regs' (if last then pcG_l3t set else pcG_l2 set) m rom)
    /\ getr regs' 16 = Z_to_bv 64 (rp + stp) /\ getr regs' (if set then 29 else 28) = Z_to_bv 64 (chk + stp) /\ getr regs' 5 = Z_to_bv 64 (i + 1)
    /\ regs_agree (fun r => In r [5; 8; 16; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros set last regs m rp chk stp i dh Hrp Hstp Hsum Hi HL Hdh R16 R11 R14 R5 R12 Rchk. unfold pcG_l2n, pcG_l3t, pcG_l2.
  assert (Hi1 : (i + 1 <= dh)%Z) by (destruct last; lia). destruct set.
  - eexists; split; [
      sn F_7f948 D_7f948; fadd (rp + stp)%Z; sn F_7f94c D_7f94c; fsnez; sn F_7f950 D_7f950; fseqz0; stepb_ft F_7f954 D_7f954 ltac:(condG);
      sn F_7f958 D_7f958; fsltu0; sn F_7f95c D_7f95c; sn F_7f960 D_7f960; stepb_ft F_7f964 D_7f964 ltac:(condG);
      sn F_7f968 D_7f968; faddiw (i + 1)%Z; sn F_7f96c D_7f96c; fadd (chk + stp)%Z; sn F_7f970 D_7f970;
      (destruct last; [ stepb_ft F_7f974 D_7f974 ltac:(condZ); apply mst_refl | stepb_tk F_7f974 D_7f974 ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
  - eexists; split; [
      sn F_7f7dc D_7f7dc; fadd (rp + stp)%Z; sn F_7f7e0 D_7f7e0; fsnez; sn F_7f7e4 D_7f7e4; fseqz0; stepb_ft F_7f7e8 D_7f7e8 ltac:(condG);
      sn F_7f7ec D_7f7ec; fsltu0; sn F_7f7f0 D_7f7f0; sn F_7f7f4 D_7f7f4; stepb_ft F_7f7f8 D_7f7f8 ltac:(condG);
      sn F_7f7fc D_7f7fc; faddiw (i + 1)%Z; sn F_7f800 D_7f800; fadd (chk + stp)%Z; sn F_7f804 D_7f804;
      (destruct last; [ stepb_ft F_7f808 D_7f808 ltac:(condZ); apply mst_refl | stepb_tk F_7f808 D_7f808 ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
Qed.

(* [comment removed for export] *)
Lemma vu_L3t : forall (set nolast : bool) regs m (plw : Z), (0 <= plw < 2 ^ 64)%Z -> (plw mod 4 = 0)%Z ->
  getr regs 17 = Z_to_bv 64 (if nolast then 1 else 0) -> (nolast = false -> getr regs 10 = Z_to_bv 64 plw) ->
  exists regs', msteps SEGS (mkst regs (pcG_l3t set) m rom) (mkst regs' (if nolast then (0x7fb08 : word) else pcG_l3 set) m rom)
    /\ (nolast = false -> getr regs' (if set then 12 else 13) = Z_to_bv 64 plw)
    /\ regs_agree (fun r => In r (if nolast then [] else [12; 13])%list) regs regs'.
Proof.
  intros set nolast regs m plw Hplw AL R17 R10. unfold pcG_l3t, pcG_l3. destruct set; destruct nolast; eexists; (split; [|]).
  - stepb_tk F_7f978 D_7f978 ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; discriminate). all: try solve_regs_agree.
  - specialize (R10 eq_refl). stepb_ft F_7f978 D_7f978 ltac:(condZ).
    sn F_7f97c D_7f97c. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia). stepb_ft F_7f980 D_7f980 ltac:(condG). sn F_7f984 D_7f984. apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity). all: try solve_regs_agree.
  - stepb_tk F_7f80c D_7f80c ltac:(condZ). apply mst_refl.
  - repeat split; try (intros; discriminate). all: try solve_regs_agree.
  - specialize (R10 eq_refl). stepb_ft F_7f80c D_7f80c ltac:(condZ).
    sn F_7f810 D_7f810. fixv' (Z_to_bv 64 0) ltac:(apply andi3_Z0; lia). stepb_ft F_7f814 D_7f814 ltac:(condG). sn F_7f818 D_7f818. sn F_7f81c D_7f81c. apply mst_refl.
  - repeat split; try (intros; gres; pin; reflexivity). all: try solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma vu_L3 : forall (set last : bool) regs m (p c stp : Z) (bd : list byte) (vd : word),
  (1 <= p)%Z -> (0 <= stp)%Z -> (p + stp < 2 ^ 64)%Z -> (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
  rdn SEGS m (Z_to_bv 64 p) 4 = Some bd -> bytes_le_to_Z bd = bv_unsigned vd -> store_ok SEGS m (Z_to_bv 64 p) 4 = true ->
  getr regs 10 = Z_to_bv 64 p -> getr regs (if set then 12 else 13) = Z_to_bv 64 p -> getr regs 6 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 stp -> getr regs 14 = Z_to_bv 64 0 ->
  exists regs' (w : word),
    msteps SEGS (mkst regs (pcG_l3 set) m rom) (mkst regs' (if last then (0x7fb08 : word) else pcG_l3 set) (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (p + stp) /\ getr regs' (if set then 12 else 13) = Z_to_bv 64 (p + stp) /\ getr regs' 6 = Z_to_bv 64 (c - 1)
    /\ regs_agree (fun r => In r [6; 10; 12; 13; 15; 16]%list) regs regs'.
Proof.
  intros set last regs m p c stp bd vd Hp Hstp Hsum Hc HL Rd Evd SOK R10 Rprev R6 R11 R14. unfold pcG_l3.
  destruct set.
  - eexists; eexists; split; [
      stepb_ft F_7f988 D_7f988 ltac:(condZ);
      stepLD F_7f98c D_7f98c bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd);
      sn F_7f990 D_7f990; sn F_7f994 D_7f994; fadd (p + stp)%Z;
      stepST F_7f998 D_7f998 (Z_to_bv 64 p) (v_or (v_lw vd) (getr regs 13)) ltac:(store_ok_peel; exact SOK);
      stepb_ft F_7f99c D_7f99c ltac:(condZ);
      sn F_7f9a0 D_7f9a0; fsltu0; sn F_7f9a4 D_7f9a4; sn F_7f9a8 D_7f9a8; stepb_ft F_7f9ac D_7f9ac ltac:(condG);
      sn F_7f9b0 D_7f9b0; faddiw (c - 1)%Z; sn F_7f9b4 D_7f9b4; fadd (p + stp)%Z; sn F_7f9b8 D_7f9b8;
      (destruct last; [ stepb_ft F_7f9bc D_7f9bc ltac:(condZ); sn F_7f9c0 D_7f9c0; apply mst_refl | stepb_tk F_7f9bc D_7f9bc ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
  - eexists; eexists; split; [
      stepb_ft F_7f820 D_7f820 ltac:(condZ);
      stepLD F_7f824 D_7f824 bd vd ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rd) ltac:(exact Evd);
      sn F_7f828 D_7f828; sn F_7f82c D_7f82c; fadd (p + stp)%Z;
      stepST F_7f830 D_7f830 (Z_to_bv 64 p) (v_and (v_lw vd) (getr regs 12)) ltac:(store_ok_peel; exact SOK);
      stepb_ft F_7f834 D_7f834 ltac:(condZ);
      sn F_7f838 D_7f838; fsltu0; sn F_7f83c D_7f83c; sn F_7f840 D_7f840; stepb_ft F_7f844 D_7f844 ltac:(condG);
      sn F_7f848 D_7f848; faddiw (c - 1)%Z; sn F_7f84c D_7f84c; fadd (p + stp)%Z; sn F_7f850 D_7f850;
      (destruct last; [ stepb_ft F_7f854 D_7f854 ltac:(condZ); sn F_7f858 D_7f858; apply mst_refl | stepb_tk F_7f854 D_7f854 ltac:(condZ); apply mst_refl ])
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ].
Qed.
End Segs.

(* [comment removed for export] *)
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac ag_sub Hx := let X := fresh "X" in intros X; apply Hx; cbv in X |- *; intuition.

Section RopUniW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma W_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.
Lemma le4_word : forall bs : list byte, length bs = 4%nat -> exists v : word, bytes_le_to_Z bs = bv_unsigned v.
Proof.
  intros bs L. exists (Z_to_bv 64 (bytes_le_to_Z bs)). pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in B. rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma W_rd4_blk : forall C A m md (p : word) (k a : Z), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + 4 <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z ->
  exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = u v.
Proof.
  intros C A m md p k a CK HW L Hlo Hhi Hk. pose proof (u64_range p).
  destruct (rdn_defined SEGS m a 4 ltac:(lia) ltac:(cbn; lia)) as (bs & R & Lb).
  { intros i Hi. cbn in Hi. destruct (blk_byte C A m md p k (Z_to_bv 64 (a + i)) CK HW L ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact D. }
  destruct (le4_word bs Lb) as (v & Ev). exists bs, v. split; assumption.
Qed.

Section Inv.
Variables (C : lctx) (Ar A : AS) (md : Model) (s : Z) (m0 : word -> option byte) (datad nd : Z) (S : TSet).
Variables (ret v0 v1 v2 v3 : word) (rE : bvmap 5 word).
Hypotheses (CK : Cok C) (Hlo : (c_top C - LSTK + ROPUNI_STACK <= s)%Z) (Hhi : (s <= c_top C)%Z) (SUB : sub_live Ar A).
Hypotheses (Ld : live A (Z_to_bv 64 datad) = Some nd) (Ld0 : live Ar (Z_to_bv 64 datad) = None) (Ld00 : live (c_A0 C) (Z_to_bv 64 datad) = None).
Hypotheses (Hdd : (0 <= datad < 2 ^ 64)%Z) (Hnd : (0 < nd)%Z).

(* [comment removed for export] *)
Definition UMI (m : word -> option byte) : Prop :=
  W C A m md /\ POSTM C Ar s m0 m /\ ucells m s v0 v1 v2 v3 /\
  (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m a = m0 a).

Lemma UMI_geom : forall m, UMI m -> (4096 <= datad)%Z /\ (datad + nd + 8192 + LSTK <= c_top C)%Z /\ (c_top C <= 2 ^ 47)%Z /\ (c_top C - LSTK + 128 <= s)%Z /\ (datad mod 16 = 0)%Z.
Proof.
  intros m (HW & _). pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [G TOP]. rewrite u_Z2bv in G, TOP by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) (Z_to_bv 64 datad) nd (w_inv _ _ _ _ HW) Ld) as (_ & AL16 & _). rewrite u_Z2bv in AL16 by lia.
  unfold ROPUNI_STACK in Hlo. change 0x800000000000%Z with (2 ^ 47)%Z in T3. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma UMI_fill : forall m m' (d n : Z), UMI m -> (datad <= d)%Z -> (0 <= n)%Z -> (d + n <= datad + nd)%Z ->
  (forall x : word, (u x < d \/ d + n <= u x)%Z -> m' x = m x) -> mem_grows m m' -> UMI m'.
Proof.
  intros m m' d n UM Hd Hn Hdn OUT GR. destruct (UMI_geom m UM) as (G1 & G2 & G3 & G4 & _).
  destruct UM as (HW & PM & CE & FT). pose proof LSTK_val as LV.
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
  split; [apply (ucells_frame m m' s); [lia | lia | exact CE |]; intros x Hx; apply OUT; lia|].
  intros a Ha1 Ha2. rewrite OUT by lia. exact (FT a Ha1 Ha2).
Qed.

(* [comment removed for export] *)
Lemma UMI_word : forall m (pd : Z) (w : word), UMI m -> (datad <= pd)%Z -> (pd + 4 <= datad + nd)%Z ->
  UMI (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)).
Proof.
  intros m pd w UM H1 H2. destruct (UMI_geom m UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV.
  apply (UMI_fill m _ pd 4 UM H1 ltac:(lia) H2).
  - intros x Hx. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
  - apply wbytes_grows.
Qed.

Lemma UMI_rd4 : forall m (pd : Z), UMI m -> (datad <= pd)%Z -> (pd + 4 <= datad + nd)%Z ->
  exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 pd) 4 = Some bs /\ bytes_le_to_Z bs = u v.
Proof.
  intros m pd UM H1 H2. destruct (UMI_geom m UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV. destruct UM as (HW & _).
  apply (W_rd4_blk C A m md (Z_to_bv 64 datad) nd pd CK HW Ld); rewrite u_Z2bv by lia; lia.
Qed.

Lemma UMI_sok : forall m (a : Z) (n : nat), UMI m -> (datad <= a)%Z -> (a + Z.of_nat n <= datad + nd)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros m a n UM H1 H2. destruct (UMI_geom m UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV. destruct UM as (HW & _).
  apply (W_sok_blk C A m md (Z_to_bv 64 datad) nd a n CK HW Ld); rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma UMI_al4 : forall m (x : Z), UMI m -> ((datad + 4 * x) mod 4 = 0)%Z.
Proof.
  intros m x UM. destruct (UMI_geom m UM) as (_ & _ & _ & _ & AL16). apply mod16_plus_mod4; [exact AL16|]. rewrite Z.mul_comm. apply Z_mod_mult.
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
Definition keep11 (r : bvmap 5 word) : Prop :=
  getr r 1 = getr rE 1 /\ getr r 3 = getr rE 3 /\ getr r 4 = getr rE 4 /\ getr r 20 = getr rE 20 /\ getr r 21 = getr rE 21 /\ getr r 22 = getr rE 22 /\
  getr r 23 = getr rE 23 /\ getr r 24 = getr rE 24 /\ getr r 25 = getr rE 25 /\ getr r 26 = getr rE 26 /\ getr r 27 = getr rE 27.

(* [comment removed for export] *)
Definition UKF : Prop :=
  forall m' r', W C A m' md -> POSTM C Ar s m0 m' -> (forall a : word, ~ scratch C s a -> ~ (datad <= u a < datad + nd)%Z -> m' a = m0 a) ->
     getr r' 2 = Z_to_bv 64 s -> getr r' 8 = v0 -> getr r' 9 = v1 -> getr r' 18 = v2 -> getr r' 19 = v3 -> keep11 r' ->
     realizes SEGS (mkCfg (mkst r' ret m' al_rom) md) S.

(* [comment removed for export] *)
Lemma U_exit : forall m r, ret_ok ret -> getr rE 1 = ret -> UMI m -> getr r 2 = Z_to_bv 64 (s - 32) -> keep11 r -> UKF ->
  realizes SEGS (mkCfg (mkst r (0x7fb08 : word) m al_rom) md) S.
Proof.
  intros m r Hret E1 UM R2 KP KF. destruct (UMI_geom m UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV. destruct UM as (HW & PM & CE & FT).
  destruct KP as (K1 & K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  destruct (vu_E al_rom r m s ret v0 v1 v2 v3 ltac:(lia) ltac:(lia) Hret CE R2 ltac:(rewrite K1; exact E1)) as (r2 & RUN2 & Q2 & Q8 & Q9 & Q18 & Q19 & AG2).
  rzs HW RUN2.
  apply (KF m r2 HW PM FT Q2 Q8 Q9 Q18 Q19). unfold keep11. repeat split; csr; first [reflexivity | assumption].
Qed.

(* [comment removed for export] *)
Lemma U_inner : forall (set : bool) (rowp acc0 nfw : Z) r0 m,
  (1 <= nfw < 2 ^ 26)%Z -> (datad <= rowp)%Z -> (rowp + 4 * nfw <= datad + nd)%Z -> (1 <= acc0)%Z -> (acc0 + 4 * nfw < 2 ^ 64)%Z ->
  UMI m -> getr r0 (if set then 8 else 31) = Z_to_bv 64 rowp -> getr r0 (if set then 9 else 8) = Z_to_bv 64 acc0 -> getr r0 (if set then 18 else 9) = Z_to_bv 64 nfw ->
  getr r0 28 = Z_to_bv 64 0 -> getr r0 (if set then 29 else 30) = Z_to_bv 64 5 ->
  (forall r' m', UMI m' -> regs_agree (fun x => In x [8; 9; 18; 19; 31]%list) r0 r' -> getr r' (if set then 19 else 18) = Z_to_bv 64 (rowp + 4 * nfw) ->
     realizes SEGS (mkCfg (mkst r' (pcA_part set) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r0 (pcA_inner set) m al_rom) md) S.
Proof.
  intros set rowp acc0 nfw r0 m Hnfw Hr1 Hr2 Hacc Hacc2 UM0 Rp Racc Rc R28 R5 K.
  apply (U_rows (fun j r m => UMI m /\ regs_agree (fun x => In x [8; 9; 18; 19; 31]%list) r0 r
                              /\ getr r (if set then 8 else 31) = Z_to_bv 64 (rowp + 4 * j) /\ getr r (if set then 9 else 8) = Z_to_bv 64 (acc0 + 4 * j)
                              /\ getr r (if set then 18 else 9) = Z_to_bv 64 (nfw - j)
                              /\ ((1 <= j)%Z -> getr r (if set then 19 else 18) = Z_to_bv 64 (rowp + 4 * j)))
                (pcA_inner set) (pcA_part set) nfw) with (n := Z.to_nat (nfw - 1)) (i := 0%Z).
  - intros j r m1 Hj (UM & AG & Qp & Qa & Qc & _) KK.
    destruct (UMI_geom _ UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV. pose proof UM as (HW & _).
    pose proof (UMI_sok _ (rowp + 4 * j) 4 UM ltac:(lia) ltac:(cbn; lia)) as SOK.
    assert (E28 : getr r 28 = Z_to_bv 64 0) by (csr; reflexivity).
    assert (E5 : getr r (if set then 29 else 30) = Z_to_bv 64 5) by (destruct set; csr; reflexivity).
    destruct (Z.eq_dec (j + 1) nfw) as [E|NE].
    + destruct (vu_I al_rom set true r m1 (rowp + 4 * j) (acc0 + 4 * j) (nfw - j) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) SOK Qp Qa Qc E28 E5)
        as (r2 & w & RUN & Q1 & Q2 & Q3 & Q4 & AG2).
      rzs HW RUN. apply KK. split; [exact (UMI_word _ (rowp + 4 * j)%Z w UM ltac:(lia) ltac:(lia))|]. split; [intros x Hx; rewrite (AG2 x Hx); exact (AG x Hx)|].
      split; [rewrite Q1; f_equal; lia|]. split; [rewrite Q2; f_equal; lia|]. split; [rewrite Q3; f_equal; lia | intros _; rewrite Q4; f_equal; lia].
    + destruct (vu_I al_rom set false r m1 (rowp + 4 * j) (acc0 + 4 * j) (nfw - j) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) SOK Qp Qa Qc E28 E5)
        as (r2 & w & RUN & Q1 & Q2 & Q3 & Q4 & AG2).
      rzs HW RUN. apply KK. split; [exact (UMI_word _ (rowp + 4 * j)%Z w UM ltac:(lia) ltac:(lia))|]. split; [intros x Hx; rewrite (AG2 x Hx); exact (AG x Hx)|].
      split; [rewrite Q1; f_equal; lia|]. split; [rewrite Q2; f_equal; lia|]. split; [rewrite Q3; f_equal; lia | intros _; rewrite Q4; f_equal; lia].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [exact UM0|]. split; [intros x Hx; reflexivity|]. split; [rewrite Rp; f_equal; lia|]. split; [rewrite Racc; f_equal; lia|].
    split; [rewrite Rc; f_equal; lia | intros X; lia].
  - intros r' m' (UM' & AG' & _ & _ & _ & Q19). exact (K r' m' UM' AG' (Q19 ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma U_arows : forall (set : bool) (pf nfw k DW dh dwpl : Z) r0 m,
  ret_ok ret -> getr rE 1 = ret -> (1 <= DW < 2 ^ 31)%Z -> (DW = 32 * nfw + k)%Z -> (0 <= k < 32)%Z -> (0 <= nfw < 2 ^ 26)%Z -> (1 <= dh <= 20000)%Z -> (1 <= dwpl < 2 ^ 24)%Z -> (dh * dwpl <= 2 ^ 24)%Z ->
  (exists X, pf = datad + 4 * X)%Z ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= pf + 4 * dwpl * i')%Z /\ (pf + 4 * dwpl * i' + 4 * (nfw + (if Z.eq_dec k 0 then 0 else 1)) <= datad + nd)%Z) ->
  UMI m -> keep11 r0 ->
  getr r0 2 = Z_to_bv 64 (s - 32) -> getr r0 7 = Z_to_bv 64 0 -> getr r0 11 = Z_to_bv 64 0 -> getr r0 14 = Z_to_bv 64 dwpl -> getr r0 5 = Z_to_bv 64 pf ->
  getr r0 16 = Z_to_bv 64 1 -> getr r0 13 = Z_to_bv 64 DW -> getr r0 10 = Z_to_bv 64 32 -> getr r0 17 = Z_to_bv 64 nfw -> getr r0 15 = Z_to_bv 64 k ->
  getr r0 12 = Z_to_bv 64 dh -> getr r0 28 = Z_to_bv 64 0 ->
  getr r0 (if set then 30 else 29) = Z_to_bv 64 pf -> getr r0 (if set then 29 else 30) = Z_to_bv 64 5 ->
  UKF ->
  realizes SEGS (mkCfg (mkst r0 (pcA_head set) m al_rom) md) S.
Proof.
  intros set pf nfw k DW dh dwpl r0 m Hret E1 HDW EDW Hk Hnfw Hdh Hdwpl Hsz [X EX] GD UM0 KP0 H2 H7 H11 H14 H5 H16 H13 H10 H17 H15 H12 H28 Hpf' H5' KF.
  destruct KP0 as (K1 & K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  apply (U_rows (fun i r m => UMI m /\ regs_agree (fun x => In x [7; 8; 9; 11; 18; 19; 31]%list) r0 r
                              /\ getr r 7 = Z_to_bv 64 i /\ getr r 11 = Z_to_bv 64 (i * dwpl))
                (pcA_head set) (0x7fb08 : word) dh) with (n := Z.to_nat (dh - 1)) (i := 0%Z).
  - (* [comment removed for export] *)
    intros i r m1 Hi (UM & AG & R7 & R11) K.
    destruct (UMI_geom _ UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV.
    destruct (GD i Hi) as [GD1 GD2]. destruct (GD 0%Z ltac:(lia)) as [GD01 _].
    assert (GD3 : (pf + 4 * dwpl * i + 4 * nfw <= datad + nd)%Z) by (destruct (Z.eq_dec k 0); lia).
    assert (Hiw : (0 <= i * dwpl /\ i * dwpl + dwpl <= 2 ^ 24)%Z) by (clear - Hi Hdwpl Hsz; nia).
    assert (TAIL : forall r' m', UMI m' -> regs_agree (fun x => In x [8; 9; 18; 19; 31]%list) r r' ->
                     realizes SEGS (mkCfg (mkst r' (pcA_next set) m' al_rom) md) S).
    { intros r' m' UM' AG'. pose proof UM' as (HW' & _).
      assert (AG2 : regs_agree (fun x => In x [7; 8; 9; 11; 18; 19; 31]%list) r0 r')
        by (intros x Hx; rewrite (AG' x ltac:(ag_sub Hx)); exact (AG x Hx)).
      destruct (Z.eq_dec (i + 1) dh) as [E|NE].
      - destruct (vu_N al_rom set true r' m' i dh (i * dwpl) dwpl ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r2 & RUN2 & Q7 & Q11 & AGN).
        rzs HW' RUN2. apply K. split; [exact UM'|]. split; [intros x Hx; rewrite (AGN x ltac:(ag_sub Hx)); exact (AG2 x Hx)|].
        split; [rewrite Q7; f_equal; lia | rewrite Q11; f_equal; lia].
      - destruct (vu_N al_rom set false r' m' i dh (i * dwpl) dwpl ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r2 & RUN2 & Q7 & Q11 & AGN).
        rzs HW' RUN2. apply K. split; [exact UM'|]. split; [intros x Hx; rewrite (AGN x ltac:(ag_sub Hx)); exact (AG2 x Hx)|].
        split; [rewrite Q7; f_equal; lia | rewrite Q11; f_equal; lia]. }
    (* [comment removed for export] *)
    assert (PART : forall r' m' (pd : Z), UMI m' -> regs_agree (fun x => In x [8; 9; 18; 19; 31]%list) r r' ->
                     k <> 0%Z -> (datad <= pd)%Z -> (pd + 4 <= datad + nd)%Z -> (exists Y, pd = datad + 4 * Y)%Z -> getr r' (if set then 19 else 18) = Z_to_bv 64 pd ->
                     realizes SEGS (mkCfg (mkst r' (pcA_part set) m' al_rom) md) S).
    { intros r' m' pd UM' AG' K0 P1 P2 [Y EY] Ep. pose proof UM' as (HW' & _).
      destruct (UMI_rd4 _ pd UM' P1 P2) as (bd & vd & Rd & Evd).
      pose proof (UMI_sok _ pd 4 UM' P1 ltac:(cbn; lia)) as SOK.
      destruct (vu_P al_rom set r' m' pd k bd vd ltac:(lia) ltac:(rewrite EY; exact (UMI_al4 _ Y UM')) ltac:(lia) Rd Evd SOK Ep ltac:(csr; reflexivity))
        as (r2 & w & RUN2 & AGP).
      rzs HW' RUN2. apply TAIL; [exact (UMI_word _ pd w UM' P1 P2)|].
      intros x Hx. rewrite (AGP x ltac:(ag_sub Hx)). exact (AG' x Hx). }
    pose proof UM as (HW & _).
    destruct (Z_lt_ge_dec DW 32) as [SMALL | BIG].
    + (* [comment removed for export] *)
      assert (Ek : k = DW) by lia. assert (K0 : k <> 0%Z) by lia. destruct (Z.eq_dec k 0) as [X0|_]; [lia|].
      destruct (vu_H al_rom set false r m1 i dwpl pf pf (i * dwpl) DW nfw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                  R7 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) R11
                  ltac:(destruct set; csr; reflexivity) ltac:(csr; reflexivity)) as (r1 & RUN1 & Q & AG1).
      rzs HW RUN1. apply (PART r1 m1 (pf + 4 * (i * dwpl))%Z UM AG1 K0); [lia | lia | exists (X + i * dwpl)%Z; lia | exact Q].
    + (* [comment removed for export] *)
      assert (Hn1 : (1 <= nfw)%Z) by lia.
      destruct (vu_H al_rom set true r m1 i dwpl pf pf (i * dwpl) DW nfw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                  R7 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) R11
                  ltac:(destruct set; csr; reflexivity) ltac:(csr; reflexivity)) as (r1 & RUN1 & (Qp & Qa & Qc) & AG1).
      rzs HW RUN1.
      apply (U_inner set (pf + 4 * (i * dwpl)) (pf + 4 * (i * dwpl)) nfw r1 m1 ltac:(lia) ltac:(lia) ltac:(destruct (Z.eq_dec k 0); lia) ltac:(lia) ltac:(lia) UM Qp Qa Qc
               ltac:(csr; reflexivity) ltac:(destruct set; csr; reflexivity)).
      intros r2 m2 UM2 AG2 Q19.
      assert (AG12 : regs_agree (fun x => In x [8; 9; 18; 19; 31]%list) r r2) by (intros x Hx; rewrite (AG2 x Hx); exact (AG1 x Hx)).
      destruct (Z.eq_dec k 0) as [K0|K0].
      * pose proof UM2 as (HW2 & _).
        destruct (vu_P0 al_rom set r2 m2 ltac:(csr; rewrite K0; reflexivity)) as (r3 & RUN3 & AG3).
        rzs HW2 RUN3. apply TAIL; [exact UM2|]. intros x Hx. rewrite (AG3 x ltac:(intros X0; exact X0)). exact (AG12 x Hx).
      * apply (PART r2 m2 (pf + 4 * (i * dwpl) + 4 * nfw)%Z UM2 AG12 K0); [lia | lia | exists (X + i * dwpl + nfw)%Z; lia | exact Q19].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [exact UM0|]. split; [intros x Hx; reflexivity|]. split; [exact H7 | rewrite H11; f_equal; lia].
  - intros r' m' (UM' & AG' & _). apply (U_exit m' r' Hret E1 UM'); [csr; reflexivity | unfold keep11; repeat split; csr; reflexivity | exact KF].
Qed.

(* [comment removed for export] *)
Lemma U_wloop : forall (HEAD EXIT : word) (RP1 RP2 RC : reg) (CLB : list reg) (P0 dwpl dh : Z) r0 r1 m,
  (forall (last : bool) regs mm (p c : Z) (bd : list byte) (vd : word),
     (1 <= p)%Z -> (p + 4 * dwpl < 2 ^ 64)%Z -> (1 <= c < 2 ^ 31)%Z -> (if last then c = 1 else 1 < c)%Z ->
     rdn SEGS mm (Z_to_bv 64 p) 4 = Some bd -> bytes_le_to_Z bd = u vd -> store_ok SEGS mm (Z_to_bv 64 p) 4 = true ->
     getr regs RP1 = Z_to_bv 64 p -> getr regs RP2 = Z_to_bv 64 p -> getr regs RC = Z_to_bv 64 c -> regs_agree (fun x => In x CLB) r0 regs ->
     exists regs' (w : word),
       msteps SEGS (mkst regs HEAD mm al_rom) (mkst regs' (if last then EXIT else HEAD) (wbytes mm (Z_to_bv 64 p) (word_to_le_bytes 4 w)) al_rom)
       /\ getr regs' RP1 = Z_to_bv 64 (p + 4 * dwpl) /\ getr regs' RP2 = Z_to_bv 64 (p + 4 * dwpl) /\ getr regs' RC = Z_to_bv 64 (c - 1)
       /\ regs_agree (fun x => In x CLB) regs regs') ->
  (1 <= dh <= 20000)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= P0 + 4 * dwpl * i')%Z /\ (P0 + 4 * dwpl * i' + 4 <= datad + nd)%Z) ->
  UMI m -> regs_agree (fun x => In x CLB) r0 r1 -> getr r1 RP1 = Z_to_bv 64 P0 -> getr r1 RP2 = Z_to_bv 64 P0 -> getr r1 RC = Z_to_bv 64 dh ->
  (forall r' m', UMI m' -> regs_agree (fun x => In x CLB) r0 r' -> realizes SEGS (mkCfg (mkst r' EXIT m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r1 HEAD m al_rom) md) S.
Proof.
  intros HEAD EXIT RP1 RP2 RC CLB P0 dwpl dh r0 r1 m ITER Hdh Hdwpl GD UM0 AG0 HP1 HP2 HC K.
  apply (U_rows (fun i r m => UMI m /\ regs_agree (fun x => In x CLB) r0 r /\ getr r RP1 = Z_to_bv 64 (P0 + 4 * dwpl * i)
                              /\ getr r RP2 = Z_to_bv 64 (P0 + 4 * dwpl * i) /\ getr r RC = Z_to_bv 64 (dh - i))
                HEAD EXIT dh) with (n := Z.to_nat (dh - 1)) (i := 0%Z).
  - intros i r m1 Hi (UM & AG & RP1' & RP2' & RC1) KK.
    destruct (UMI_geom _ UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV. destruct (GD i Hi) as [GD1 GD2].
    destruct (UMI_rd4 _ (P0 + 4 * dwpl * i) UM GD1 GD2) as (bd & vd & Rd & Evd).
    pose proof (UMI_sok _ (P0 + 4 * dwpl * i) 4 UM GD1 ltac:(cbn; lia)) as SOK. pose proof UM as (HW & _).
    destruct (Z.eq_dec (i + 1) dh) as [E|NE].
    + destruct (ITER true r m1 (P0 + 4 * dwpl * i)%Z (dh - i)%Z bd vd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Rd Evd SOK RP1' RP2' RC1 AG) as (r2 & w & RUN & QP1 & QP2 & QC & AG2).
      rzs HW RUN. apply KK. split; [exact (UMI_word _ _ w UM GD1 GD2)|]. split; [intros x Hx; rewrite (AG2 x Hx); exact (AG x Hx)|].
      split; [rewrite QP1; f_equal; lia|]. split; [rewrite QP2; f_equal; lia | rewrite QC; f_equal; lia].
    + destruct (ITER false r m1 (P0 + 4 * dwpl * i)%Z (dh - i)%Z bd vd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Rd Evd SOK RP1' RP2' RC1 AG) as (r2 & w & RUN & QP1 & QP2 & QC & AG2).
      rzs HW RUN. apply KK. split; [exact (UMI_word _ _ w UM GD1 GD2)|]. split; [intros x Hx; rewrite (AG2 x Hx); exact (AG x Hx)|].
      split; [rewrite QP1; f_equal; lia|]. split; [rewrite QP2; f_equal; lia | rewrite QC; f_equal; lia].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [exact UM0|]. split; [exact AG0|]. split; [rewrite HP1; f_equal; lia|]. split; [rewrite HP2; f_equal; lia | rewrite HC; f_equal; lia].
  - intros r' m' (UM' & AG' & _). exact (K r' m' UM' AG').
Qed.

(* [comment removed for export] *)
Lemma U_inner2 : forall (set : bool) (rp dnf : Z) r0 m,
  (1 <= dnf < 2 ^ 26)%Z -> (datad <= rp)%Z -> (rp + 4 * dnf <= datad + nd)%Z ->
  UMI m -> getr r0 (if set then 8 else 31) = Z_to_bv 64 rp -> getr r0 (if set then 9 else 8) = Z_to_bv 64 rp -> getr r0 (if set then 18 else 9) = Z_to_bv 64 dnf ->
  getr r0 16 = Z_to_bv 64 rp -> getr r0 (if set then 30 else 29) = Z_to_bv 64 1 -> getr r0 (if set then 31 else 30) = Z_to_bv 64 1 ->
  (forall r' m', UMI m' -> regs_agree (fun x => In x [8; 9; 18; 19; 31]%list) r0 r' -> realizes SEGS (mkCfg (mkst r' (pcG_l2n set) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r0 (pcG_l2i set) m al_rom) md) S.
Proof.
  intros set rp dnf r0 m Hdnf Hr1 Hr2 UM0 Rp Rq Rc R16 Rf1 Rf2 K.
  apply (U_rows (fun j r m => UMI m /\ regs_agree (fun x => In x [8; 9; 18; 19; 31]%list) r0 r
                              /\ getr r (if set then 8 else 31) = Z_to_bv 64 (rp + 4 * j) /\ getr r (if set then 9 else 8) = Z_to_bv 64 (rp + 4 * j)
                              /\ getr r (if set then 18 else 9) = Z_to_bv 64 (dnf - j) /\ getr r (if set then 31 else 30) = Z_to_bv 64 1)
                (pcG_l2i set) (pcG_l2n set) dnf) with (n := Z.to_nat (dnf - 1)) (i := 0%Z).
  - intros j r m1 Hj (UM & AG & Qp & Qq & Qc & Qf2) KK.
    destruct (UMI_geom _ UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV. pose proof UM as (HW & _).
    pose proof (UMI_sok _ (rp + 4 * j) 4 UM ltac:(lia) ltac:(cbn; lia)) as SOK.
    assert (E16 : getr r 16 = Z_to_bv 64 rp) by (csr; reflexivity).
    assert (Ef1 : getr r (if set then 30 else 29) = Z_to_bv 64 1) by (destruct set; csr; reflexivity).
    destruct (Z.eq_dec (j + 1) dnf) as [E|NE].
    + destruct (vu_L2i al_rom set true r m1 (rp + 4 * j) (rp + 4 * j) rp (dnf - j) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) SOK Qp Qq Qc E16 Ef1 Qf2)
        as (r2 & w & RUN & Q1 & Q2 & Q3 & Q4 & AG2).
      rzs HW RUN. apply KK. split; [exact (UMI_word _ (rp + 4 * j)%Z w UM ltac:(lia) ltac:(lia))|]. split; [intros x Hx; rewrite (AG2 x Hx); exact (AG x Hx)|].
      split; [rewrite Q1; f_equal; lia|]. split; [rewrite Q2; f_equal; lia|]. split; [rewrite Q3; f_equal; lia | exact Q4].
    + destruct (vu_L2i al_rom set false r m1 (rp + 4 * j) (rp + 4 * j) rp (dnf - j) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) SOK Qp Qq Qc E16 Ef1 Qf2)
        as (r2 & w & RUN & Q1 & Q2 & Q3 & Q4 & AG2).
      rzs HW RUN. apply KK. split; [exact (UMI_word _ (rp + 4 * j)%Z w UM ltac:(lia) ltac:(lia))|]. split; [intros x Hx; rewrite (AG2 x Hx); exact (AG x Hx)|].
      split; [rewrite Q1; f_equal; lia|]. split; [rewrite Q2; f_equal; lia|]. split; [rewrite Q3; f_equal; lia | exact Q4].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [exact UM0|]. split; [intros x Hx; reflexivity|]. split; [rewrite Rp; f_equal; lia|]. split; [rewrite Rq; f_equal; lia|]. split; [rewrite Rc; f_equal; lia | exact Rf2].
  - intros r' m' (UM' & AG' & _). exact (K r' m' UM' AG').
Qed.

(* [comment removed for export] *)
Lemma U_mloop : forall (set : bool) (P2 dwpl dnf dh : Z) r0 m,
  (1 <= dh <= 20000)%Z -> (1 <= dnf < 2 ^ 26)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= P2 + 4 * dwpl * i')%Z /\ (P2 + 4 * dwpl * i' + 4 * dnf <= datad + nd)%Z) ->
  UMI m -> getr r0 16 = Z_to_bv 64 P2 -> getr r0 (if set then 29 else 28) = Z_to_bv 64 P2 -> getr r0 5 = Z_to_bv 64 0 ->
  getr r0 15 = Z_to_bv 64 dnf -> getr r0 7 = Z_to_bv 64 1 -> getr r0 11 = Z_to_bv 64 (4 * dwpl) -> getr r0 14 = Z_to_bv 64 0 -> getr r0 12 = Z_to_bv 64 dh ->
  (forall r' m', UMI m' -> regs_agree (fun x => In x [5; 8; 9; 16; 18; 19; 28; 29; 30; 31]%list) r0 r' -> realizes SEGS (mkCfg (mkst r' (pcG_l3t set) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r0 (pcG_l2 set) m al_rom) md) S.
Proof.
  intros set P2 dwpl dnf dh r0 m Hdh Hdnf Hdwpl GD UM0 H16 Hchk H5 H15 H7 H11 H14 H12 K.
  apply (U_rows (fun i r m => UMI m /\ regs_agree (fun x => In x [5; 8; 9; 16; 18; 19; 28; 29; 30; 31]%list) r0 r
                              /\ getr r 16 = Z_to_bv 64 (P2 + 4 * dwpl * i) /\ getr r (if set then 29 else 28) = Z_to_bv 64 (P2 + 4 * dwpl * i) /\ getr r 5 = Z_to_bv 64 i)
                (pcG_l2 set) (pcG_l3t set) dh) with (n := Z.to_nat (dh - 1)) (i := 0%Z).
  - intros i r m1 Hi (UM & AG & R16 & Rchk & R5) KK.
    destruct (UMI_geom _ UM) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV. destruct (GD i Hi) as [GD1 GD2]. pose proof UM as (HW & _).
    destruct (vu_L2h al_rom set r m1 dnf (P2 + 4 * dwpl * i) (P2 + 4 * dwpl * i) Hdnf ltac:(lia) ltac:(csr; reflexivity) R16 ltac:(csr; reflexivity) Rchk)
      as (r1 & RUN1 & Qp & Qq & Qc & Qf1 & Qf2 & Qchk & AG1).
    rzs HW RUN1.
    apply (U_inner2 set (P2 + 4 * dwpl * i) dnf r1 m1 Hdnf GD1 GD2 UM Qp Qq Qc ltac:(csr; reflexivity) Qf1 Qf2).
    intros r2 m2 UM2 AG2. pose proof UM2 as (HW2 & _).
    assert (AG02 : regs_agree (fun x => In x [5; 8; 9; 16; 18; 19; 28; 29; 30; 31]%list) r0 r2)
      by (intros x Hx; rewrite (AG2 x ltac:(ag_sub Hx)); rewrite (AG1 x ltac:(ag_sub Hx)); exact (AG x Hx)).
    assert (E16 : getr r2 16 = Z_to_bv 64 (P2 + 4 * dwpl * i)) by (csr; reflexivity).
    assert (Echk : getr r2 (if set then 29 else 28) = Z_to_bv 64 (P2 + 4 * dwpl * i)) by (destruct set; csr; reflexivity).
    destruct (Z.eq_dec (i + 1) dh) as [E|NE].
    + destruct (vu_L2n al_rom set true r2 m2 (P2 + 4 * dwpl * i) (P2 + 4 * dwpl * i) (4 * dwpl) i dh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)
                  E16 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) Echk) as (r3 & RUN3 & Q16 & Qck & Q5 & AG3).
      rzs HW2 RUN3. apply KK. split; [exact UM2|]. split; [intros x Hx; rewrite (AG3 x ltac:(ag_sub Hx)); exact (AG02 x Hx)|].
      split; [rewrite Q16; f_equal; lia|]. split; [rewrite Qck; f_equal; lia | exact Q5].
    + destruct (vu_L2n al_rom set false r2 m2 (P2 + 4 * dwpl * i) (P2 + 4 * dwpl * i) (4 * dwpl) i dh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)
                  E16 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) Echk) as (r3 & RUN3 & Q16 & Qck & Q5 & AG3).
      rzs HW2 RUN3. apply KK. split; [exact UM2|]. split; [intros x Hx; rewrite (AG3 x ltac:(ag_sub Hx)); exact (AG02 x Hx)|].
      split; [rewrite Q16; f_equal; lia|]. split; [rewrite Qck; f_equal; lia | exact Q5].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [exact UM0|]. split; [intros x Hx; reflexivity|]. split; [rewrite H16; f_equal; lia|]. split; [rewrite Hchk; f_equal; lia | exact H5].
  - intros r' m' (UM' & AG' & _). exact (K r' m' UM' AG').
Qed.

(* [comment removed for export] *)
Lemma U_general : forall (set full nolast : bool) (pfp dh dwpl dnf : Z) r0 m,
  ret_ok ret -> getr rE 1 = ret -> (1 <= dh <= 20000)%Z -> (1 <= dwpl < 2 ^ 24)%Z -> (0 <= dnf < 2 ^ 26)%Z -> (full = true -> (1 <= dnf)%Z) -> (full = false -> dnf = 0%Z) ->
  (exists X, pfp = datad + 4 * X)%Z ->
  (forall i', (0 <= i' < dh)%Z -> (datad <= pfp + 4 * dwpl * i')%Z /\
        (pfp + 4 * dwpl * i' + 4 + 4 * dnf + (if nolast then 0 else 4) <= datad + nd)%Z) ->
  UMI m -> keep11 r0 ->
  getr r0 2 = Z_to_bv 64 (s - 32) -> getr r0 5 = Z_to_bv 64 pfp -> getr r0 14 = Z_to_bv 64 dwpl -> getr r0 6 = Z_to_bv 64 dh -> getr r0 12 = Z_to_bv 64 dh ->
  getr r0 15 = Z_to_bv 64 dnf -> getr r0 28 = Z_to_bv 64 (if full then 0 else 1) -> getr r0 17 = Z_to_bv 64 (if nolast then 1 else 0) ->
  (full = true -> getr r0 16 = Z_to_bv 64 (pfp + 4)) -> (nolast = false -> getr r0 10 = Z_to_bv 64 (pfp + 4 + 4 * dnf)) ->
  UKF ->
  realizes SEGS (mkCfg (mkst r0 (pcG_l1s set) m al_rom) md) S.
Proof.
  intros set full nolast pfp dh dwpl dnf r0 m Hret E1 Hdh Hdwpl Hdnf Hfull Hnfull [X EX] GD UM0 KP0 H2 H5 H14 H6 H12 H15 H28 H17 H16 H10 KF.
  destruct KP0 as (K1 & K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof UM0 as (HW0 & _). destruct (UMI_geom _ UM0) as (G1 & G2 & G3 & G4 & _). pose proof LSTK_val as LV.
  destruct (GD 0%Z ltac:(lia)) as [GD01 GD02].
  assert (GD03 : (pfp + 4 + 4 * dnf + 4 <= datad + nd + 4)%Z) by (destruct nolast; lia).
  (* [comment removed for export] *)
  assert (K3' : forall r m', UMI m' -> getr r 2 = Z_to_bv 64 (s - 32) -> keep11 r ->
                 getr r 17 = Z_to_bv 64 (if nolast then 1 else 0) -> getr r 6 = Z_to_bv 64 dh -> getr r 11 = Z_to_bv 64 (4 * dwpl) -> getr r 14 = Z_to_bv 64 0 ->
                 (nolast = false -> getr r 10 = Z_to_bv 64 (pfp + 4 + 4 * dnf)) ->
                 realizes SEGS (mkCfg (mkst r (pcG_l3t set) m' al_rom) md) S).
  { intros r m' UM E2 KP E17 E6 E11 E14 E10. pose proof UM as (HW & _).
    destruct KP as (J1 & J3 & J4 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27).
    destruct (vu_L3t al_rom set nolast r m' (pfp + 4 + 4 * dnf) ltac:(destruct nolast; lia)
                ltac:(rewrite EX; replace (datad + 4 * X + 4 + 4 * dnf)%Z with (datad + 4 * (X + 1 + dnf))%Z by lia; exact (UMI_al4 _ _ UM)) E17 E10) as (r1 & RUN1 & Qprev & AG1).
    rzs HW RUN1. destruct nolast.
    - apply (U_exit m' r1 Hret E1 UM); [csr; reflexivity | unfold keep11; repeat split; csr; reflexivity | exact KF].
    - specialize (E10 eq_refl). specialize (Qprev eq_refl).
      apply (U_wloop (pcG_l3 set) (0x7fb08 : word) 10 (if set then 12 else 13) 6 [6; 10; 12; 13; 15; 16]%list (pfp + 4 + 4 * dnf) dwpl dh r1 r1 m').
      + intros last regs mm p c bd vd Hp Hp2 Hc HL Rd Evd SOK RP1 RP2 RC AG.
        destruct (vu_L3 al_rom set last regs mm p c (4 * dwpl) bd vd Hp ltac:(lia) Hp2 Hc HL Rd Evd SOK RP1 RP2 RC
                    ltac:(rewrite (AG 11) by (cbv; intuition discriminate); csr; reflexivity) ltac:(rewrite (AG 14) by (cbv; intuition discriminate); csr; reflexivity))
          as (regs' & w & RUN & QP1 & QP2 & QC & AG').
        exists regs', w. split; [exact RUN|]. split; [exact QP1|]. split; [exact QP2|]. split; [exact QC | exact AG'].
      + exact Hdh.
      + lia.
      + intros i' Hi'. destruct (GD i' Hi') as [X1 X2]. lia.
      + exact UM.
      + intros x Hx. reflexivity.
      + csr. reflexivity.
      + exact Qprev.
      + csr. reflexivity.
      + intros r' m'' UM' AG'. apply (U_exit m'' r' Hret E1 UM'); [csr; reflexivity | unfold keep11; repeat split; csr; reflexivity | exact KF]. }
  (* [comment removed for export] *)
  destruct (vu_L1s al_rom set r0 m pfp dwpl dh ltac:(lia) ltac:(rewrite EX; exact (UMI_al4 _ _ UM0)) ltac:(lia) H5 H14 H6) as (r1 & RUN1 & Q11 & Q14 & Q30 & Q29 & AG1).
  rzs HW0 RUN1.
  apply (U_wloop (pcG_l1 set) (pcG_l1x set) 5 30 29 [5; 8; 29; 30; 31]%list pfp dwpl dh r1 r1 m).
  - intros last regs mm p c bd vd Hp Hp2 Hc HL Rd Evd SOK RP1 RP2 RC AG.
    destruct (vu_L1 al_rom set last regs mm p c (4 * dwpl) bd vd Hp ltac:(lia) Hp2 Hc HL Rd Evd SOK RP1 RP2 RC
                ltac:(rewrite (AG 11) by (cbv; intuition discriminate); exact Q11) ltac:(rewrite (AG 14) by (cbv; intuition discriminate); exact Q14))
      as (regs' & w & RUN & QP1 & QP2 & QC & AG').
    exists regs', w. split; [exact RUN|]. split; [exact QP1|]. split; [exact QP2|]. split; [exact QC | exact AG'].
  - exact Hdh.
  - lia.
  - intros i' Hi'. destruct (GD i' Hi') as [X1 X2]. destruct nolast; lia.
  - exact UM0.
  - intros x Hx. reflexivity.
  - csr. reflexivity.
  - exact Q30.
  - exact Q29.
  - intros r2 m2 UM2 AG2. pose proof UM2 as (HW2 & _).
    destruct (vu_L1x al_rom set full r2 m2 (pfp + 4) ltac:(lia) ltac:(rewrite EX; replace (datad + 4 * X + 4)%Z with (datad + 4 * (X + 1))%Z by lia; exact (UMI_al4 _ _ UM2))
                ltac:(csr; reflexivity) ltac:(intros F; csr; exact (H16 F))) as (r3 & RUN3 & QF & AG3).
    rzs HW2 RUN3. destruct full.
    + destruct (QF eq_refl) as (Q5 & Q7 & Qchk). specialize (Hfull eq_refl). specialize (H16 eq_refl).
      apply (U_mloop set (pfp + 4) dwpl dnf dh r3 m2 Hdh ltac:(lia) ltac:(lia)).
      * intros i' Hi'. destruct (GD i' Hi') as [X1 X2]. destruct nolast; lia.
      * exact UM2.
      * csr. reflexivity.
      * exact Qchk.
      * exact Q5.
      * csr. reflexivity.
      * exact Q7.
      * csr. reflexivity.
      * csr. reflexivity.
      * csr. reflexivity.
      * intros r4 m4 UM4 AG4.
        apply (K3' r4 m4 UM4); [csr; reflexivity | unfold keep11; repeat split; csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity |].
        intros NL. specialize (H10 NL). csr. reflexivity.
    + apply (K3' r3 m2 UM2); [csr; reflexivity | unfold keep11; repeat split; csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity |].
      intros NL. specialize (H10 NL). csr. reflexivity.
Qed.

End Inv.

(* [comment removed for export] *)
Lemma tbl_rd : forall base, (base = 0x1f4c4 \/ base = 0x1f440)%Z -> forall j, (1 <= j <= 31)%Z ->
  exists bs, rdn SEGS (fun _ => None) (Z_to_bv 64 (base + 4 * j)) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros base Hb j Hj.
  assert (E : (j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/
              j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31)%Z) by lia.
  clear Hj.
  destruct Hb as [-> | ->];
  (repeat (destruct E as [-> | E]; [ lazymatch goal with |- exists bs, ?l = Some bs /\ _ =>
      let v := eval vm_compute in l in lazymatch v with Some ?bs => exists bs; split; [vm_compute; reflexivity | reflexivity] end end |]);
   subst j; lazymatch goal with |- exists bs, ?l = Some bs /\ _ =>
      let v := eval vm_compute in l in lazymatch v with Some ?bs => exists bs; split; [vm_compute; reflexivity | reflexivity] end end).
Qed.

Theorem rasteropUniLow_W : rasteropUniLow_contract.
Proof.
  unfold rasteropUniLow_contract.
  intros C Ar A m md regs s datad dpixw dpixh d dwpl dx dy dw dh op ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Hdd SHd RCd Hop Ld Ld0 Ld00 HK.
  unfold PC_rasteropUniLow. replace (Z_to_bv 64 0x7f3d8) with (0x7f3d8 : word) by (apply bv_eq; reflexivity).
  destruct SHd as (Hd & Hdpw & Hdph & Ewd & Hszd). destruct RCd as (Hdx0 & Hdy0 & Hdw1 & Hdh1 & Hdxw & Hdyh).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
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
  destruct (vu_A0 al_rom regs m s dpixw d dx dw dh op ltac:(lia) ltac:(lia) Hd ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rdh Rop H2 H11 H13 H15 H17)
    as (r0 & RUN0 & P2 & P11 & P6 & P28 & P7 & P17 & AG0).
  rzs HW RUN0.
  set (M1 := UF m s regs).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1) by (subst M1; unfold UF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (ucells_UF m s regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (UM1 : UMI C Ar A md s m datad nd (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) M1).
  { split; [exact HW1|]. split; [exact PM1|]. split; [exact CE1|].
    intros a Ha1 Ha2. subst M1. apply UF_outside; [lia | lia |]. intros X. apply Ha1. unfold scratch. lia. }
  (* [comment removed for export] *)
  fold DX in P7. fold DW in P17.
  destruct (vu_A1 al_rom r0 M1 DX DW (dpixw * d)%Z dy dh dpixh a6 ltac:(lia) ltac:(lia) HDXW HDPW Hdy0 Hdh1 Hdyh ltac:(lia) eq_refl P7 P17 P28
              ltac:(csr; reflexivity) P6 ltac:(csr; reflexivity)) as (r1 & RUN1 & Q12 & Q13 & Q15 & Q29 & AG1).
  rzs HW1 RUN1.
  assert (TBL : forall base, (base = 0x1f4c4 \/ base = 0x1f440)%Z -> forall j, (1 <= j <= 31)%Z ->
            exists (bs : list byte) (v : word), rdn SEGS M1 (Z_to_bv 64 (base + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v).
  { intros base Hb j Hj. destruct (tbl_rd base Hb j Hj) as (bs & Rb & Lb). destruct (le4_word bs Lb) as (v & Ev). exists bs, v. split; [|exact Ev].
    rewrite <- p16_segs. rewrite (W_rdn_ro C A M1 md (base + 4 * j) 4 HW1) by (destruct Hb as [-> | ->]; cbn; lia). rewrite p16_segs. exact Rb. }
  assert (KF : UKF C Ar A md s m datad nd S ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) regs).
  { intros m' r' HW' PM' FT' Z2 Y0 Y1 Y2 Y3 (J1 & J3 & J4 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27).
    apply (HK m' r' HW'); [| exact PM' | exact FT'].
    apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | assumption ]. }
  assert (KP1 : keep11 regs r1) by (unfold keep11; repeat split; csr; reflexivity).
  assert (E2 : getr r1 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E17 : getr r1 17 = Z_to_bv 64 DW) by (csr; reflexivity).
  assert (E7 : getr r1 7 = Z_to_bv 64 DX) by (csr; reflexivity).
  assert (E11 : getr r1 11 = Z_to_bv 64 op) by (csr; reflexivity).
  assert (E10 : getr r1 10 = Z_to_bv 64 datad) by (csr; reflexivity).
  assert (E16 : getr r1 16 = Z_to_bv 64 dy) by (csr; reflexivity).
  assert (E14 : getr r1 14 = Z_to_bv 64 dwpl) by (csr; reflexivity).
  assert (E6 : getr r1 6 = Z_to_bv 64 dh) by (csr; reflexivity).
  clear AG0 AG1 RUN0 RUN1.
  destruct (Z.eq_dec a6 0) as [AL0 | NAL].
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    destruct (vu_G0 al_rom r1 M1 a6 DW DX cdx datad dy dwpl ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Mdy Hcdx ltac:(lia) ltac:(lia)
                (TBL 0x1f440%Z ltac:(right; reflexivity)) Q15 E17 Q13 E7 E10 E16 E14) as (r2 & RUN2 & W30 & W5 & W16 & W10 & AG2).
    rzs HW1 RUN2.
    set (pfp := (datad + 4 * (dy * dwpl) + 4 * cdx)%Z) in *.
    set (lw2 := ((DX + DW) mod 32)%Z).
    pose proof (Z.mod_pos_bound (DX + DW) 32 ltac:(lia)) as Hlw. fold lw2 in Hlw.
    assert (EXp : exists X, pfp = (datad + 4 * X)%Z) by (exists (dy * dwpl + cdx)%Z; subst pfp; lia).
    destruct (Z.ltb_spec DW (32 - a6)) as [DBL | BIG].
    + (* [comment removed for export] *)
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
    + (* [comment removed for export] *)
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

End RopUniW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
