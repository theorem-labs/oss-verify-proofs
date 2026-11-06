(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15_code_gqR_rmc.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac fpn := cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by reg_neq_tac
               | rewrite fpv_get_same | rewrite fpv_get_other by reg_neq_tac ].
Ltac fz Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma rmc_S3 : forall (fx : FPState) regs m (s n g rm gm bm : Z) (c03 c02 c05 : list byte),
  (256 <= s < 2 ^ 63)%Z -> (1 <= n <= 256)%Z -> (0 <= g < 2 ^ 63)%Z -> (0 <= rm < 2 ^ 64)%Z -> (0 <= gm < 2 ^ 64)%Z -> (0 <= bm < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 rm) -> rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 gm) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 bm) ->
  rdn SEGS m (Z_to_bv 64 0x116fc) 4 = Some c03 -> rdn SEGS m (Z_to_bv 64 0x116f4) 4 = Some c02 -> rdn SEGS m (Z_to_bv 64 0x11620) 8 = Some c05 ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 10 = Z_to_bv 64 g -> getr regs 20 = Z_to_bv 64 n ->
  exists fr' regs',
    msteps SEGS (@mkst fx regs (0x19910 : word) m rom) (@mkst (mkFP fr' (@fp_csr fx)) regs' (0x1994c : word) m rom)
    /\ getr regs' 11 = Z_to_bv 64 rm /\ getr regs' 12 = Z_to_bv 64 gm /\ getr regs' 13 = Z_to_bv 64 bm
    /\ getr regs' 14 = Z_to_bv 64 (g + 4 * n) /\ getr regs' 15 = Z_to_bv 64 g
    /\ regs_agree (fun r => In r [11; 12; 13; 14; 15]%list) regs regs'.
Proof.
  intros fx regs m s n g rm gm bm c03 c02 c05 Hs Hn Hg Hrm Hgm Hbm Crm Cgm Cbm K03 K02 K05 H2 H10 H20.
  eexists _, _. split.
  - stepb_ft F_198b8 D_198b8 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_198bc D_198bc (Z_to_le_bytes 8 rm) (Z_to_bv 64 rm) ltac:(addr_norm; repeat rdn_peel1; exact Crm) ltac:(apply lez8; lia).   (* [comment removed for export] *)
    stepLD F_198c0 D_198c0 (Z_to_le_bytes 8 gm) (Z_to_bv 64 gm) ltac:(addr_norm; repeat rdn_peel1; exact Cgm) ltac:(apply lez8; lia).   (* [comment removed for export] *)
    stepLD F_198c4 D_198c4 (Z_to_le_bytes 8 bm) (Z_to_bv 64 bm) ltac:(addr_norm; repeat rdn_peel1; exact Cbm) ltac:(apply lez8; lia).   (* [comment removed for export] *)
    stepiv F_198c8 D_198c8 (Z_to_bv 64 (4 * n)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).   (* [comment removed for export] *)
    sn F_198cc D_198cc.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 0x116fc) (bs := c03); [exact F_198d0 | reflexivity | exact D_198d0 | gres; imm_norm; addr_tac | repeat rdn_peel1; exact K03] | step_simpl ]; fpn.   (* [comment removed for export] *)
    sn F_198d4 D_198d4.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 0x116f4) (bs := c02); [exact F_198d8 | reflexivity | exact D_198d8 | gres; imm_norm; addr_tac | repeat rdn_peel1; exact K02] | step_simpl ]; fpn.   (* [comment removed for export] *)
    sn F_198dc D_198dc.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 0x11620) (bs := c05); [exact F_198e0 | reflexivity | exact D_198e0 | gres; imm_norm; addr_tac | repeat rdn_peel1; exact K05] | step_simpl ]; fpn.   (* [comment removed for export] *)
    zv F_198e4 D_198e4 (Z_to_bv 64 (g + 4 * n)).   (* [comment removed for export] *)
    sn F_198e8 D_198e8.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fp_step_fmv_w_x; [exact F_198ec | reflexivity | exact D_198ec] | step_simpl ]; fpn.   (* [comment removed for export] *)
    sn F_198f0 D_198f0.   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rmc_L1 : forall (last : bool) (fx : FPState) regs m (rp gp bp dp gend : Z) (bsr bsg bsb : list byte),
  frm_zero (@fp_csr fx) ->
  (0 <= rp)%Z -> (rp + 4 < 2 ^ 63)%Z -> (0 <= gp)%Z -> (gp + 4 < 2 ^ 63)%Z -> (0 <= bp)%Z -> (bp + 4 < 2 ^ 63)%Z -> (0 <= dp)%Z -> (dp + 4 < 2 ^ 63)%Z ->
  (0 <= gend < 2 ^ 63)%Z ->
  rdn SEGS m (Z_to_bv 64 rp) 4 = Some bsr -> length bsr = 4%nat -> rdn SEGS m (Z_to_bv 64 gp) 4 = Some bsg -> length bsg = 4%nat ->
  rdn SEGS m (Z_to_bv 64 bp) 4 = Some bsb -> length bsb = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 dp) 4 = true ->
  (if last then dp + 4 = gend else dp + 4 <> gend)%Z ->
  getr regs 11 = Z_to_bv 64 rp -> getr regs 12 = Z_to_bv 64 gp -> getr regs 13 = Z_to_bv 64 bp -> getr regs 15 = Z_to_bv 64 dp -> getr regs 14 = Z_to_bv 64 gend ->
  exists fr' cs' regs' (bs : list byte),
    msteps SEGS (@mkst fx regs (0x1994c : word) m rom)
                (@mkst (mkFP fr' cs') regs' (if last then (0x19994 : word) else (0x1994c : word)) (wbytes m (Z_to_bv 64 dp) bs) rom)
    /\ frm_zero cs' /\ length bs = 4%nat
    /\ getr regs' 11 = Z_to_bv 64 (rp + 4) /\ getr regs' 12 = Z_to_bv 64 (gp + 4) /\ getr regs' 13 = Z_to_bv 64 (bp + 4) /\ getr regs' 15 = Z_to_bv 64 (dp + 4)
    /\ regs_agree (fun r => In r [11; 12; 13; 15; 16; 17]%list) regs regs'.
Proof.
  intros last fx regs m rp gp bp dp gend bsr bsg bsb Hz Hrp Hrp63 Hgp Hgp63 Hbp Hbp63 Hdp Hdp63 Hgend Cr Lr Cg Lg Cb Lb SOK Hlast H11 H12 H13 H15 H14.
  destruct last.
  - eexists _, _, _, _. split.
    + stepLD F_198f4 D_198f4 bsr (Z_to_bv 64 (lez bsr)) ltac:(addr_norm; exact Cr) ltac:(symmetry; apply u_lez4; exact Lr).   (* [comment removed for export] *)
      stepLD F_198f8 D_198f8 bsg (Z_to_bv 64 (lez bsg)) ltac:(addr_norm; exact Cg) ltac:(symmetry; apply u_lez4; exact Lg).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_198fc | reflexivity | exact D_198fc | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_19900 | reflexivity | exact D_19900 | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepLD F_19904 D_19904 bsb (Z_to_bv 64 (lez bsb)) ltac:(addr_norm; exact Cb) ltac:(symmetry; apply u_lez4; exact Lb).   (* [comment removed for export] *)
      zv F_19908 D_19908 (Z_to_bv 64 (bp + 4)).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_1990c | reflexivity | exact D_1990c | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fma; [exact F_19910 | reflexivity | exact D_19910 | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_19914 | reflexivity | exact D_19914 | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fma; [exact F_19918 | reflexivity | exact D_19918 | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f; [exact F_1991c | reflexivity | exact D_1991c | right; split; reflexivity | left; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_19920 | reflexivity | exact D_19920 | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_x_of_f; [exact F_19924 | reflexivity | exact D_19924 | right; left; repeat split; reflexivity | right; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      match goal with |- context [regupd _ 16 ?v] => stepST F_19928 D_19928 (Z_to_bv 64 dp) v ltac:(store_ok_peel; exact SOK) end.   (* [comment removed for export] *)
      zv F_1992c D_1992c (Z_to_bv 64 (dp + 4)).   (* [comment removed for export] *)
      zv F_19930 D_19930 (Z_to_bv 64 (gp + 4)).   (* [comment removed for export] *)
      zv F_19934 D_19934 (Z_to_bv 64 (rp + 4)).   (* [comment removed for export] *)
      stepb_ft F_19938 D_19938 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    + split; [fz Hz|]. split; [apply length_N_to_le_bytes|]. repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  - eexists _, _, _, _. split.
    + stepLD F_198f4 D_198f4 bsr (Z_to_bv 64 (lez bsr)) ltac:(addr_norm; exact Cr) ltac:(symmetry; apply u_lez4; exact Lr).
      stepLD F_198f8 D_198f8 bsg (Z_to_bv 64 (lez bsg)) ltac:(addr_norm; exact Cg) ltac:(symmetry; apply u_lez4; exact Lg).
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_198fc | reflexivity | exact D_198fc | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_19900 | reflexivity | exact D_19900 | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
      stepLD F_19904 D_19904 bsb (Z_to_bv 64 (lez bsb)) ltac:(addr_norm; exact Cb) ltac:(symmetry; apply u_lez4; exact Lb).
      zv F_19908 D_19908 (Z_to_bv 64 (bp + 4)).
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_1990c | reflexivity | exact D_1990c | fz Hz | reflexivity] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fma; [exact F_19910 | reflexivity | exact D_19910 | fz Hz | reflexivity] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_19914 | reflexivity | exact D_19914 | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fma; [exact F_19918 | reflexivity | exact D_19918 | fz Hz | reflexivity] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f; [exact F_1991c | reflexivity | exact D_1991c | right; split; reflexivity | left; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_19920 | reflexivity | exact D_19920 | fz Hz | reflexivity] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fcvt_x_of_f; [exact F_19924 | reflexivity | exact D_19924 | right; left; repeat split; reflexivity | right; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
      match goal with |- context [regupd _ 16 ?v] => stepST F_19928 D_19928 (Z_to_bv 64 dp) v ltac:(store_ok_peel; exact SOK) end.
      zv F_1992c D_1992c (Z_to_bv 64 (dp + 4)).
      zv F_19930 D_19930 (Z_to_bv 64 (gp + 4)).
      zv F_19934 D_19934 (Z_to_bv 64 (rp + 4)).
      stepb_tk F_19938 D_19938 ltac:(condZ).
      apply mst_refl.
    + split; [fz Hz|]. split; [apply length_N_to_le_bytes|]. repeat split; gres; pin; try reflexivity; try solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rmc_clone_tail : forall (fx : FPState) regs m (pixs : Z) (ret : word),
  (0 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 4 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) -> store_ok SEGS m (Z_to_bv 64 (pixs + 20)) 4 = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 11 = Z_to_bv 64 (pixs + 20) -> getr regs 12 = Z_to_bv 64 1 ->
  msteps SEGS (@mkst fx regs (0x1728c : word) m rom) (@mkst fx regs ret (wbytes m (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) rom).
Proof.
  intros fx regs m pixs ret Hp Hp63 Hal Crc SOK Hret H1 H11 H12.
  chain_step; [ reflexivity
              | eapply step_amoadd_w with (bs := Z_to_le_bytes 4 1) (v := Z_to_bv 64 1);
                [ exact F_17234 | reflexivity | exact D_17234
                | rewrite H11, u_Z2bv by lia; rewrite <- Z.add_mod_idemp_l, Hal by lia; reflexivity
                | rewrite H11; exact Crc | reflexivity | rewrite H11; exact SOK ]
              | step_simpl ].
  rewrite H11, H12. replace (word_to_le_bytes 4 (v_add (Z_to_bv 64 1) (Z_to_bv 64 1))) with (Z_to_le_bytes 4 2) by reflexivity.
  stepret F_17238 D_17238 ret ltac:(exact H1). apply mst_refl.
Qed.

(* [comment removed for export] *)
Lemma rmc_ret : forall (fx : FPState) regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a034) m rom) (@mkst fx regs ret m rom).
Proof.
  intros fx regs m ret Hret H1. replace (Z_to_bv 64 0x1a034) with (0x1a034 : word) by (apply bv_eq; reflexivity).
  stepret F_19fdc D_19fdc ret ltac:(exact H1). apply mst_refl.
Qed.

End Segs.
