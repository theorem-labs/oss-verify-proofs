(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptRecs LeptArith LeptArith2 GrayACELib LeptNuma LeptEdgeFP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9_code_edC.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Ltac fpn := cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by reg_neq_tac
               | rewrite fpv_get_same | rewrite fpv_get_other by reg_neq_tac ].

Ltac fz Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.
Ltac fin_fp Hz := split; [fz Hz|]; repeat split; gres; pin; try reflexivity; try solve_regs_agree;
  try (rewrite fpv_get_same; unfold fpv_box, f32i; cbn [fp_format]; rewrite u_Z2bv by lia; reflexivity).

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Lemma ngf_run : forall (fx : FPState) regs m (na nalloc n rc arr i pv : Z) (bs : list byte) (ret : word),
    RECat m na (numa_flds nalloc n rc arr) -> (0 <= i < n)%Z -> (n < 2 ^ 31)%Z -> (1 <= na)%Z -> (1 <= pv)%Z -> (pv + 4 < 2 ^ 64)%Z ->
    (0 <= arr)%Z -> (arr + 4 * n < 2 ^ 64)%Z ->
    (pv + 4 <= na \/ na + 32 <= pv)%Z -> (pv + 4 <= arr + 4 * i \/ arr + 4 * i + 4 <= pv)%Z ->
    rdn SEGS m (Z_to_bv 64 (arr + 4 * i)) 4 = Some bs ->
    store_ok SEGS m (Z_to_bv 64 pv) 4 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na -> getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 pv ->
    exists fr' regs',
      msteps SEGS (@mkst fx regs (0x60db4 : word) m rom)
                  (@mkst (mkFP fr' (@fp_csr fx)) regs' ret (wbytes (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 pv) bs) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 13]%list) regs regs'.
  Proof.
    intros fx regs m na nalloc n rc arr i pv bs ret R Hi Hn Hna Hpv Hpv64 Harr Harr64 D1 D2 RC SOK Hret H1 H10 H11 H12.
    pose proof (NUMA_wf m na nalloc n rc arr R) as (Wna & Wn & Wrc & Warr & Wna0 & Wna64).
    pose proof (NUMA_rd_n SEGS m na nalloc n rc arr R) as Cn. pose proof (NUMA_rd_arr SEGS m na nalloc n rc arr R) as Carr.
    eexists _, _. split.
    - stepb_ft F_60d5c D_60d5c ltac:(condZ).
      stepST F_60d60 D_60d60 (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
      stepb_ft F_60d64 D_60d64 ltac:(condZ).
      stepb_ft F_60d68 D_60d68 ltac:(condZ).
      stepLD F_60d6c D_60d6c (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepb_ft F_60d70 D_60d70 ltac:(condZ).
      sn F_60d74 D_60d74. sn F_60d78 D_60d78.
      stepLD F_60d7c D_60d7c (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; repeat rdn_peel1; exact Carr) ltac:(apply lez8; lia).
      stepiv F_60d80 D_60d80 (Z_to_bv 64 (4 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_60d84 D_60d84 (Z_to_bv 64 (arr + 4 * i)).
      (* [comment removed for export] *)
      chain_step; [ reflexivity
                  | eapply fp_step_flw with (a := Z_to_bv 64 (arr + 4 * i)) (bs := bs); [exact F_60d88 | reflexivity | exact D_60d88 | gres; imm_norm; addr_tac | repeat rdn_peel1; exact RC]
                  | step_simpl ].
      (* [comment removed for export] *)
      chain_step; [ reflexivity
                  | eapply fp_step_fsw with (a := Z_to_bv 64 pv); [exact F_60d8c | reflexivity | exact D_60d8c | gres; imm_norm; addr_tac | store_ok_peel; exact SOK]
                  | step_simpl ].
      stepret F_60d90 D_60d90 ret ltac:(exact H1).
      cbn [fp_regs]. rewrite fpv_get_same, fpv_flw_bytes by (exact (rdn_length _ _ _ _ _ RC)).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ngi_run : forall (fx : FPState) regs m (na nalloc n rc arr i pv : Z) (bs : list byte) (ret : word),
    frm_zero (@fp_csr fx) ->
    RECat m na (numa_flds nalloc n rc arr) -> (0 <= i < n)%Z -> (n < 2 ^ 31)%Z -> (1 <= na)%Z -> (0x100000 <= pv)%Z -> (pv + 4 < 2 ^ 64)%Z ->
    (0 <= arr)%Z -> (arr + 4 * n < 2 ^ 64)%Z ->
    (pv + 4 <= na \/ na + 32 <= pv)%Z -> (pv + 4 <= arr + 4 * i \/ arr + 4 * i + 4 <= pv)%Z ->
    rdn SEGS m (Z_to_bv 64 (arr + 4 * i)) 4 = Some bs ->
    rdn SEGS m (Z_to_bv 64 0x1c1b8) 8 = Some (Z_to_le_bytes 8 0x3ff0000000000000) ->
    rdn SEGS m (Z_to_bv 64 0x1c1c0) 8 = Some (Z_to_le_bytes 8 0xbff0000000000000) ->
    rdn SEGS m (Z_to_bv 64 0x1c3f8) 8 = Some (Z_to_le_bytes 8 0x3fe0000000000000) ->
    store_ok SEGS m (Z_to_bv 64 pv) 4 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na -> getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 pv ->
    exists fr' cs' regs' (iv : word),
      msteps SEGS (@mkst fx regs (0x60e78 : word) m rom)
                  (@mkst (mkFP fr' cs') regs' ret (wbytes (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 pv) (word_to_le_bytes 4 iv)) rom)
      /\ frm_zero cs'
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 13]%list) regs regs'.
  Proof.
    intros fx regs m na nalloc n rc arr i pv bs ret Hz R Hi Hn Hna Hpv Hpv64 Harr Harr64 D1 D2 RC RT0 RT1 RH SOK Hret H1 H10 H11 H12.
    pose proof (NUMA_wf m na nalloc n rc arr R) as (Wna & Wn & Wrc & Warr & Wna0 & Wna64).
    pose proof (NUMA_rd_n SEGS m na nalloc n rc arr R) as Cn. pose proof (NUMA_rd_arr SEGS m na nalloc n rc arr R) as Carr.
    eexists _, _, _, _. split.
    - stepb_ft F_60e20 D_60e20 ltac:(condZ).
      stepST F_60e24 D_60e24 (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
      stepb_ft F_60e28 D_60e28 ltac:(condZ).
      stepb_ft F_60e2c D_60e2c ltac:(condZ).
      stepLD F_60e30 D_60e30 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepb_ft F_60e34 D_60e34 ltac:(condZ).
      sn F_60e38 D_60e38. sn F_60e3c D_60e3c.
      stepLD F_60e40 D_60e40 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; repeat rdn_peel1; exact Carr) ltac:(apply lez8; lia).
      stepiv F_60e44 D_60e44 (Z_to_bv 64 (4 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_60e48 D_60e48 (Z_to_bv 64 (arr + 4 * i)).
      chain_step; [ reflexivity
                  | eapply fp_step_flw with (a := Z_to_bv 64 (arr + 4 * i)) (bs := bs); [exact F_60e4c | reflexivity | exact D_60e4c | gres; imm_norm; addr_tac | repeat rdn_peel1; exact RC]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fp_step_fmv_w_x; [exact F_60e50 | reflexivity | exact D_60e50] | step_simpl ]; fpn.
      sn F_60e54 D_60e54. sn F_60e58 D_60e58.
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_60e5c | reflexivity | exact D_60e5c] | step_simpl ]; fpn.
      match goal with |- context [regupd _ 13 (if ?b then Z_to_bv 64 1 else Z_to_bv 64 0)] =>
        stepiv F_60e60 D_60e60 (if b then Z_to_bv 64 8 else Z_to_bv 64 0) ltac:(gres; pin; imm_norm; destruct b; apply bv_eq; reflexivity) end.
      match goal with |- context [regupd _ 13 (if ?b then Z_to_bv 64 8 else Z_to_bv 64 0)] =>
        stepat F_60e64 D_60e64 (if b then Z_to_bv 64 0x1c1c0 else Z_to_bv 64 0x1c1b8) ltac:(gres; pin; destruct b; apply bv_eq; reflexivity);
        (chain_step; [ reflexivity
                  | eapply fp_step_fld with (a := if b then Z_to_bv 64 0x1c1c0 else Z_to_bv 64 0x1c1b8)
                                            (bs := if b then Z_to_le_bytes 8 0xbff0000000000000 else Z_to_le_bytes 8 0x3ff0000000000000);
                    [exact F_60e68 | reflexivity | exact D_60e68 | gres; imm_norm; destruct b; addr_tac | destruct b; repeat rdn_peel1; assumption]
                  | step_simpl ]; fpn) end.
      sn F_60e6c D_60e6c.
      chain_step; [ reflexivity
                  | eapply fp_step_fld with (a := Z_to_bv 64 0x1c3f8) (bs := Z_to_le_bytes 8 0x3fe0000000000000);
                    [exact F_60e70 | reflexivity | exact D_60e70 | gres; imm_norm; addr_tac | repeat rdn_peel1; assumption]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity
                  | eapply fpv_step_fcvt_f_of_f; [exact F_60e74 | reflexivity | exact D_60e74 | right; split; reflexivity | left; split; reflexivity
                                                 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity
                  | eapply fpv_step_fma; [exact F_60e78 | reflexivity | exact D_60e78 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity
                  | eapply fpv_step_fcvt_x_of_f; [exact F_60e7c | reflexivity | exact D_60e7c | left; repeat split; reflexivity | right; split; reflexivity
                                                 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity]
                  | step_simpl ]; fpn.
      match goal with |- context [regupd _ 11 (fpv_x_of_f ?a ?b ?c ?d ?e)] =>
        stepST F_60e80 D_60e80 (Z_to_bv 64 pv) (fpv_x_of_f a b c d e) ltac:(store_ok_peel; exact SOK) end.
      stepret F_60e84 D_60e84 ret ltac:(exact H1).
      apply mst_refl.
    - split; [cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz|]. repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition NFEF (m : word -> option byte) (s : Z) (ret : word) (regs fr : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
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
      (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (reg_get fr 8)))
      (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (reg_get fr 9)))
      (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (reg_get fr 18)).

  (* [comment removed for export] *)
  Lemma delta_cmp : fst (fpv_cmp F_LT FMT_S 1065353216 0) = false.
  Proof. vm_compute. reflexivity. Qed.
  Lemma low32_0 : bv_unsigned (low32 (Z_to_bv 64 0)) = 0%Z.
  Proof. vm_compute. reflexivity. Qed.
  Lemma sgnj_one : bv_unsigned (sgnj_val F_SGNJ (Z_to_bv 32 0x3f800000) (Z_to_bv 32 0x3f800000)) = 0x3f800000%Z.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma nfe_A : forall (fx : FPState) regs m (s nas n : Z) (ret : word),
    frm_zero (@fp_csr fx) -> reg_get (@fp_regs fx) 10 = nan_box (Z_to_bv 32 0x3f800000) ->
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= nas)%Z -> (nas + 32 <= s - 128)%Z -> (0 <= n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (nas + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
    store_ok SEGS m (Z_to_bv 64 (s - 128)) 128 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 nas -> getr regs 11 = Z_to_bv 64 0 ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x60738 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x609ec : word) (NFEF m s ret regs (@fp_regs fx)) rom)
      /\ frm_zero cs'
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 1 = Z_to_bv 64 0x6083c /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = Z_to_bv 64 nas /\ getr regs' 18 = Z_to_bv 64 n /\ getr regs' 20 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 18; 20]%list) regs regs'.
  Proof.
    intros fx regs m s nas n ret Hz Hfa0 Hs Hs64 Hnas Hnas2 Hn Cn SOK H2 H1 H10 H11. unfold NFEF.
    eexists _, _, _. split.
    - zv F_606e0 D_606e0 (Z_to_bv 64 (s - 128)).   (* [comment removed for export] *)
      stepST F_606e4 D_606e4 (Z_to_bv 64 (s - 8)) (ret) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_606e8 D_606e8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_606ec D_606ec (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_606f0 D_606f0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_606f4 D_606f4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_606f8 D_606f8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_606fc D_606fc (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_60700 D_60700 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_60704 D_60704 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_60708 D_60708 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_6070c D_6070c (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 96)); [exact F_60710 | reflexivity | exact D_60710 | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 104)); [exact F_60714 | reflexivity | exact D_60714 | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 112)); [exact F_60718 | reflexivity | exact D_60718 | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_6071c D_6071c.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_60720 | reflexivity | exact D_60720] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_60724 D_60724.   (* [comment removed for export] *)
      stepb_tk F_60728 D_60728 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_60730 D_60730 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fmv_w_x; [exact F_60734 | reflexivity | exact D_60734] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_60738 | reflexivity | exact D_60738] | step_simpl ]; fpn.   (* [comment removed for export] *)
      rewrite Hfa0, fpv_unbox_box, sgnj_one, getr_zero, low32_0, delta_cmp.
      stepb_tk F_6073c D_6073c ltac:(condZ).   (* [comment removed for export] *)
      sn F_607d0 D_607d0.   (* [comment removed for export] *)
      sn F_607d4 D_607d4.   (* [comment removed for export] *)
      stepb_ft F_60c24 D_60c24 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_60c28 D_60c28 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.   (* [comment removed for export] *)
      stepret F_60c2c D_60c2c (Z_to_bv 64 0x60830) ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_607d8 D_607d8.   (* [comment removed for export] *)
      sn F_607dc D_607dc.   (* [comment removed for export] *)
      sn F_607e0 D_607e0.   (* [comment removed for export] *)
      apply mst_refl.
    - split; [cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz|]. repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition nfe_R1 (regs : bvmap 5 word) (s nas nad n i : Z) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 128) /\ getr regs 8 = Z_to_bv 64 nas /\ getr regs 9 = Z_to_bv 64 nad /\ getr regs 18 = Z_to_bv 64 n /\
    getr regs 19 = Z_to_bv 64 0 /\ getr regs 21 = Z_to_bv 64 i.
  Definition MONE : Z := 18446744073709551615.   (* [comment removed for export] *)
  Definition nfe_R2 (regs : bvmap 5 word) (s nas nad n i loc : Z) (d : bool) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 128) /\ getr regs 8 = Z_to_bv 64 nas /\ getr regs 9 = Z_to_bv 64 nad /\ getr regs 18 = Z_to_bv 64 n /\
    getr regs 19 = Z_to_bv 64 0 /\ getr regs 20 = Z_to_bv 64 i /\ getr regs 21 = Z_to_bv 64 loc /\
    getr regs 22 = Z_to_bv 64 1 /\ getr regs 23 = Z_to_bv 64 MONE /\ getr regs 25 = (if d then Z_to_bv 64 1 else Z_to_bv 64 MONE).

  (* [comment removed for export] *)
  Lemma nfe_B1 : forall (fx : FPState) regs m (s nas nad n : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 10 = Z_to_bv 64 nad -> getr regs 8 = Z_to_bv 64 nas -> getr regs 18 = Z_to_bv 64 n ->
    getr regs 20 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x6083c : word) m rom) (@mkst fx regs' (0x60db4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 8 = Z_to_bv 64 nas /\ getr regs' 9 = Z_to_bv 64 nad /\ getr regs' 18 = Z_to_bv 64 n
      /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x6086c
      /\ getr regs' 10 = Z_to_bv 64 nas /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 116)
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 19]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n Hs Hs64 H2 H10 H8 H18 H20.
    eexists. split.
    - sn F_607e4 D_607e4.   (* [comment removed for export] *)
      stepb_tk F_607e8 D_607e8 ltac:(condZ).   (* [comment removed for export] *)
      sn F_60800 D_60800.   (* [comment removed for export] *)
      zv F_60804 D_60804 (Z_to_bv 64 (s - 116)).   (* [comment removed for export] *)
      sn F_60808 D_60808.   (* [comment removed for export] *)
      sn F_6080c D_6080c.   (* [comment removed for export] *)
      sn F_60810 D_60810.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_B2 : forall (fx : FPState) regs m (s nas nad n : Z),
    (2 <= n < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 nas -> getr regs 9 = Z_to_bv 64 nad -> getr regs 18 = Z_to_bv 64 n ->
    getr regs 19 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x6086c : word) m rom) (@mkst fx regs' (0x60878 : word) m rom)
      /\ nfe_R1 regs' s nas nad n 1
      /\ regs_agree (fun r => In r [10; 21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n Hn H2 H8 H9 H18 H19. unfold nfe_R1.
    eexists. split.
    - sn F_60814 D_60814.   (* [comment removed for export] *)
      stepb_ft F_60818 D_60818 ltac:(condZ).   (* [comment removed for export] *)
      sn F_6081c D_6081c.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L1h : forall (fx : FPState) regs m (s nas nad n i : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> nfe_R1 regs s nas nad n i ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x60878 : word) m rom) (@mkst fx regs' (0x60db4 : word) m rom)
      /\ nfe_R1 regs' s nas nad n i /\ getr regs' 1 = Z_to_bv 64 0x60888
      /\ getr regs' 10 = Z_to_bv 64 nas /\ getr regs' 11 = Z_to_bv 64 i /\ getr regs' 12 = Z_to_bv 64 (s - 120)
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hs Hs64 (H2 & H8 & H9 & H18 & H19 & H21). unfold nfe_R1.
    eexists. split.
    - zv F_60820 D_60820 (Z_to_bv 64 (s - 120)).   (* [comment removed for export] *)
      sn F_60824 D_60824.   (* [comment removed for export] *)
      sn F_60828 D_60828.   (* [comment removed for export] *)
      sn F_6082c D_6082c.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  Lemma nfe_L1a : forall (fx : FPState) regs m (s : Z) (b8 b12 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 -> rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some b12 ->
    getr regs 2 = Z_to_bv 64 (s - 128) ->
    exists fr' cs' regs' (b : bool),
      msteps SEGS (@mkst fx regs (0x60888 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x60898 : word) m rom)
      /\ frm_zero cs' /\ getr regs' 10 = (if b then Z_to_bv 64 1 else Z_to_bv 64 0)
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros fx regs m s b8 b12 Hz Hs Hs64 R8 R12 H2.
    eexists _, _, _, _. split.
    - chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_60830 | reflexivity | exact D_60830 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 116)) (bs := b12); [exact F_60834 | reflexivity | exact D_60834 | gres; imm_norm; addr_tac | exact R12] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_60838 | reflexivity | exact D_60838 | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_6083c | reflexivity | exact D_6083c] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L1b : forall (fx : FPState) regs m (b : bool),
    frm_zero (@fp_csr fx) -> getr regs 10 = (if b then Z_to_bv 64 1 else Z_to_bv 64 0) ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x60898 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x608a4 : word) m rom)
      /\ frm_zero cs' /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0)
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros fx regs m b Hz H10. destruct b.
    - eexists _, _, _, _. split.
      + stepb_ft F_60840 D_60840 ltac:(condZ).   (* [comment removed for export] *)
        chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_60844 | reflexivity | exact D_60844] | step_simpl ]; fpn.   (* [comment removed for export] *)
        chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_60848 | reflexivity | exact D_60848] | step_simpl ]; fpn.   (* [comment removed for export] *)
        apply mst_refl.
      + fin_fp Hz.
    - eexists _, _, _, _. split.
      + stepb_tk F_60840 D_60840 ltac:(condZ).   (* [comment removed for export] *)
        chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_60848 | reflexivity | exact D_60848] | step_simpl ]; fpn.   (* [comment removed for export] *)
        apply mst_refl.
      + fin_fp Hz.
  Qed.

  Lemma nfe_R1_agree : forall regs regs' s nas nad n i,
    nfe_R1 regs s nas nad n i -> regs_agree (fun r => In r [10]%list) regs regs' -> nfe_R1 regs' s nas nad n i.
  Proof.
    intros regs regs' s nas nad n i (H2 & H8 & H9 & H18 & H19 & H21) AG. unfold nfe_R1.
    repeat split; csr; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L1cF : forall (fx : FPState) regs m (s nas nad n i : Z),
    frm_zero (@fp_csr fx) -> (1 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R1 regs s nas nad n i -> getr regs 10 = Z_to_bv 64 1 ->
    exists fr' cs' regs' (b : bool),
      msteps SEGS (@mkst fx regs (0x608a4 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x608f0 : word) m rom)
      /\ frm_zero cs' /\ nfe_R2 regs' s nas nad n (i + 1) i b
      /\ regs_agree (fun r => In r [10; 20; 22; 23; 25]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hz Hi Hin Hn (H2 & H8 & H9 & H18 & H19 & H21) H10. unfold nfe_R2, MONE.
    eexists _, _, _, _. split.
    - stepb_tk F_6084c D_6084c ltac:(condZ).   (* [comment removed for export] *)
      stepat F_6085c D_6085c (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_60860 D_60860 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_60864 | reflexivity | exact D_60864] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_60868 D_60868.   (* [comment removed for export] *)
      match goal with |- context [regupd _ 10 (if ?b then Z_to_bv 64 1 else Z_to_bv 64 0)] =>
        stepiv F_6086c D_6086c (if b then Z_to_bv 64 0 else Z_to_bv 64 18446744073709551615) ltac:(gres; pin; imm_norm; destruct b; apply bv_eq; reflexivity);   (* [comment removed for export] *)
        stepiv F_60870 D_60870 (if b then Z_to_bv 64 1 else Z_to_bv 64 18446744073709551615) ltac:(gres; pin; imm_norm; destruct b; apply bv_eq; reflexivity) end.   (* [comment removed for export] *)
      sn F_60874 D_60874.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_60878 | reflexivity | exact D_60878] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_6087c D_6087c.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  Lemma nfe_R2_agree : forall regs regs' s nas nad n i loc d,
    nfe_R2 regs s nas nad n i loc d -> regs_agree (fun r => In r [10]%list) regs regs' -> nfe_R2 regs' s nas nad n i loc d.
  Proof.
    intros regs regs' s nas nad n i loc d (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) AG. unfold nfe_R2.
    repeat split; csr; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L1cX : forall (fx : FPState) regs m (s nas nad n i : Z),
    (1 <= i)%Z -> (n <= i + 1)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R1 regs s nas nad n i -> getr regs 10 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x608a4 : word) m rom) (@mkst fx regs' (0x609a8 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 9 = Z_to_bv 64 nad
      /\ regs_agree (fun r => In r [20]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hi Hin Hi2 Hn (H2 & H8 & H9 & H18 & H19 & H21) H10.
    eexists. split.
    - stepb_tk F_6084c D_6084c ltac:(condZ).
      stepat F_6085c D_6085c (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_tk F_60860 D_60860 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L1cN : forall (fx : FPState) regs m (s nas nad n i : Z),
    (1 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R1 regs s nas nad n i -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x608a4 : word) m rom) (@mkst fx regs' (0x60878 : word) m rom)
      /\ nfe_R1 regs' s nas nad n (i + 1)
      /\ regs_agree (fun r => In r [21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hi Hin Hn (H2 & H8 & H9 & H18 & H19 & H21) H10. unfold nfe_R1.
    eexists. split.
    - stepb_ft F_6084c D_6084c ltac:(condZ).
      stepat F_60850 D_60850 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_tk F_60854 D_60854 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma nfe_L1cE : forall (fx : FPState) regs m (s nas nad n i : Z),
    (1 <= i)%Z -> (i + 1 = n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R1 regs s nas nad n i -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x608a4 : word) m rom) (@mkst fx regs' (0x609a8 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 9 = Z_to_bv 64 nad
      /\ regs_agree (fun r => In r [21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hi Hin Hn (H2 & H8 & H9 & H18 & H19 & H21) H10.
    eexists. split.
    - stepb_ft F_6084c D_6084c ltac:(condZ).
      stepat F_60850 D_60850 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_ft F_60854 D_60854 ltac:(condZ).
      sn F_60858 D_60858.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma nfe_L2h : forall (fx : FPState) regs m (s nas nad n i loc : Z) (d : bool),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> nfe_R2 regs s nas nad n i loc d ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x608f0 : word) m rom) (@mkst fx regs' (0x60db4 : word) m rom)
      /\ nfe_R2 regs' s nas nad n i loc d /\ getr regs' 1 = Z_to_bv 64 0x60900
      /\ getr regs' 10 = Z_to_bv 64 nas /\ getr regs' 11 = Z_to_bv 64 i /\ getr regs' 12 = Z_to_bv 64 (s - 120)
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc d Hs Hs64 (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold nfe_R2.
    eexists. split.
    - zv F_60898 D_60898 (Z_to_bv 64 (s - 120)).   (* [comment removed for export] *)
      sn F_6089c D_6089c.   (* [comment removed for export] *)
      sn F_608a0 D_608a0.   (* [comment removed for export] *)
      sn F_608a4 D_608a4.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a : forall (fx : FPState) regs m (s nas nad n i loc : Z) (b8 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 ->
    nfe_R2 regs s nas nad n i loc true ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x60900 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x6090c : word) m rom)
      /\ frm_zero cs' /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0)
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc b8 Hz Hs Hs64 Hi0 Hin Hn R8  (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold nfe_R2, MONE in *.
    eexists _, _, _, _. split.
    - chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_608a8 | reflexivity | exact D_608a8 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepb_ft F_608ac D_608ac ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_608b0 | reflexivity | exact D_608b0] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b : forall (fx : FPState) regs m (s nas nad n i loc : Z) (b8 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 ->
    nfe_R2 regs s nas nad n i loc false ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x60900 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x6091c : word) m rom)
      /\ frm_zero cs' /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0) /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [10; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc b8 Hz Hs Hs64 Hi0 Hin Hn R8  (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold nfe_R2, MONE in *.
    eexists _, _, _, _. split.
    - chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_608a8 | reflexivity | exact D_608a8 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepb_tk F_608ac D_608ac ltac:(condZ).   (* [comment removed for export] *)
      sn F_608b8 D_608b8.   (* [comment removed for export] *)
      stepb_ft F_608bc D_608bc ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_608c0 | reflexivity | exact D_608c0] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a1 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc true -> getr regs 10 = Z_to_bv 64 1 ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x6090c : word) m rom) (@mkst (mkFP fr' cs') regs' (0x608e4 : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i i true /\ getr regs' 24 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [21; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_tk F_608b4 D_608b4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_60880 D_60880.   (* [comment removed for export] *)
      sn F_60884 D_60884.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_60888 | reflexivity | exact D_60888] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a0 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc true -> getr regs 10 = Z_to_bv 64 0 ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x6090c : word) m rom) (@mkst (mkFP fr' cs') regs' (0x60938 : word) m rom)
      /\ frm_zero cs'
      /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0) /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [10; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10. unfold nfe_R2, MONE in *.
    eexists _, _, _, _. split.
    - stepb_ft F_608b4 D_608b4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_608b8 D_608b8.   (* [comment removed for export] *)
      stepb_tk F_608bc D_608bc ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_608d4 D_608d4 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_608d8 | reflexivity | exact D_608d8 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_608dc | reflexivity | exact D_608dc] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a00 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc true -> getr regs 10 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x60938 : word) m rom) (@mkst fx regs' (0x608e4 : word) m rom)
      /\ nfe_R2 regs' s nas nad n i loc true /\ getr regs' 24 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists. split.
    - stepb_tk F_608e0 D_608e0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_60948 D_60948.   (* [comment removed for export] *)
      sn F_6094c D_6094c.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a01 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc true -> getr regs 10 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x60938 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x60b90 : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i loc true /\ getr regs' 24 = Z_to_bv 64 MONE /\ getr regs' 1 = Z_to_bv 64 0x60948 /\ getr regs' 10 = Z_to_bv 64 nad /\ reg_get fr' 10 = nan_box (Z_to_bv 32 (f32i loc))
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_ft F_608e0 D_608e0 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_608e4 | reflexivity | exact D_608e4 | left; split; reflexivity | left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_608e8 D_608e8.   (* [comment removed for export] *)
      sn F_608ec D_608ec.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2aR : forall (fx : FPState) regs m (s nas nad n i loc : Z) (b8 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 -> nfe_R2 regs s nas nad n i loc true -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x60948 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x608e4 : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i i true /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc b8 Hz Hs Hs64 Hi0 Hin Hn Hloc R8 (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H24. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_tk F_608f0 D_608f0 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_60900 | reflexivity | exact D_60900 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_60904 D_60904.   (* [comment removed for export] *)
      sn F_60908 D_60908.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b1 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc false -> getr regs 10 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x6091c : word) m rom) (@mkst (mkFP fr' cs') regs' (0x608e4 : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i i false /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_ft F_608c4 D_608c4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_608c8 D_608c8.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_608cc | reflexivity | exact D_608cc] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_608d0 D_608d0.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b0 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc false -> getr regs 10 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x6091c : word) m rom) (@mkst (mkFP fr' cs') regs' (0x60978 : word) m rom)
      /\ frm_zero cs'
      /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0) /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists _, _, _, _. split.
    - stepb_tk F_608c4 D_608c4 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_608d4 D_608d4 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_6090c D_6090c ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_60918 | reflexivity | exact D_60918 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_6091c | reflexivity | exact D_6091c] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b00 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc false -> getr regs 10 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x60978 : word) m rom) (@mkst fx regs' (0x608e4 : word) m rom)
      /\ nfe_R2 regs' s nas nad n i loc false /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists. split.
    - stepb_tk F_60920 D_60920 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b01 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc false -> getr regs 10 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x60978 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x60b90 : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i loc false /\ getr regs' 1 = Z_to_bv 64 0x60988 /\ getr regs' 10 = Z_to_bv 64 nad /\ reg_get fr' 10 = nan_box (Z_to_bv 32 (f32i loc))
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_ft F_60920 D_60920 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_60924 | reflexivity | exact D_60924 | left; split; reflexivity | left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_60928 D_60928.   (* [comment removed for export] *)
      sn F_6092c D_6092c.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2bR : forall (fx : FPState) regs m (s nas nad n i loc : Z) (b8 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 -> nfe_R2 regs s nas nad n i loc false -> 
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x60988 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x608e4 : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i i false /\ getr regs' 24 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [21; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc b8 Hz Hs Hs64 Hi0 Hin Hn Hloc R8 (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_tk F_60930 D_60930 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_60940 | reflexivity | exact D_60940 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_60944 D_60944.   (* [comment removed for export] *)
      sn F_60948 D_60948.   (* [comment removed for export] *)
      sn F_6094c D_6094c.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_LATn : forall (fx : FPState) regs m (s nas nad n i loc : Z) (d d' : bool),
    (0 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc d -> getr regs 24 = (if d' then Z_to_bv 64 1 else Z_to_bv 64 MONE) ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x608e4 : word) m rom) (@mkst fx regs' (0x608f0 : word) m rom)
      /\ nfe_R2 regs' s nas nad n (i + 1) loc d'
      /\ regs_agree (fun r => In r [20; 25]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc d d' Hi0 Hin Hn (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H24. unfold nfe_R2, MONE in *.
    eexists. split.
    - stepat F_6088c D_6088c (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      sn F_60890 D_60890.   (* [comment removed for export] *)
      stepb_ft F_60894 D_60894 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  Lemma nfe_LATx : forall (fx : FPState) regs m (s nas nad n i loc : Z) (d : bool),
    (0 <= i)%Z -> (i + 1 = n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc d ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x608e4 : word) m rom) (@mkst fx regs' (0x609a8 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 9 = Z_to_bv 64 nad
      /\ regs_agree (fun r => In r [20; 25]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc d Hi0 Hin Hn (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold MONE in *.
    eexists. split.
    - stepat F_6088c D_6088c (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      sn F_60890 D_60890.   (* [comment removed for export] *)
      stepb_tk F_60894 D_60894 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_exit : forall (fx : FPState) regs m (s nad : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : word) (f8 f9 f18 : list byte),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) -> rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) -> rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) -> rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) -> rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) -> rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some f8 -> rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some f9 -> rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some f18 ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 9 = Z_to_bv 64 nad ->
    exists fr' regs',
      msteps SEGS (@mkst fx regs (0x609a8 : word) m rom) (@mkst (mkFP fr' (@fp_csr fx)) regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 nad
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21
      /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros fx regs m s nad ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 f8 f9 f18 Hs Hs64 Hret C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 CF8 CF9 CF18 H2 H9.
    eexists _, _. split.
    - sn F_60950 D_60950.   (* [comment removed for export] *)
      stepLD8 F_60954 D_60954 ret. stepLD8 F_60958 D_60958 v8. stepLD8 F_6095c D_6095c v9. stepLD8 F_60960 D_60960 v18.
      stepLD8 F_60964 D_60964 v19. stepLD8 F_60968 D_60968 v20. stepLD8 F_6096c D_6096c v21. stepLD8 F_60970 D_60970 v22.
      stepLD8 F_60974 D_60974 v23. stepLD8 F_60978 D_60978 v24. stepLD8 F_6097c D_6097c v25.
      chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 96)) (bs := f8); [exact F_60980 | reflexivity | exact D_60980 | gres; imm_norm; addr_tac | exact CF8] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 104)) (bs := f9); [exact F_60984 | reflexivity | exact D_60984 | gres; imm_norm; addr_tac | exact CF9] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 112)) (bs := f18); [exact F_60988 | reflexivity | exact D_60988 | gres; imm_norm; addr_tac | exact CF18] | step_simpl ]; fpn.
      zv F_6098c D_6098c (Z_to_bv 64 s).   (* [comment removed for export] *)
      stepret F_60990 D_60990 ret ltac:(reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.


End Segs.
