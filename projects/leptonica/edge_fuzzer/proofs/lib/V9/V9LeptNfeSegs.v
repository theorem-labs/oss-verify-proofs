(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptRecs LeptArith LeptArith2 GrayACELib LeptNuma LeptEdgeFP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9_code_edA.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

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

(* [comment removed for export] *)
Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac snez1 F D := sn F D; fixv' (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Lemma ngf_run : forall (fx : FPState) regs m (na nalloc n rc arr i pv : Z) (bs : list byte) (ret : word),
    RECat m na (numa_flds nalloc n rc arr) -> (0 <= i < n)%Z -> (n < 2 ^ 31)%Z -> (1 <= na)%Z -> (1 <= pv)%Z -> (pv + 4 < 2 ^ 64)%Z ->
    (1 <= arr)%Z -> (arr + 4 * n < 2 ^ 64)%Z ->
    (pv + 4 <= na \/ na + 32 <= pv)%Z -> (pv + 4 <= arr + 4 * i \/ arr + 4 * i + 4 <= pv)%Z ->
    (pv mod 4 = 0)%Z -> (na mod 8 = 0)%Z -> (arr mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (arr + 4 * i)) 4 = Some bs ->
    store_ok SEGS m (Z_to_bv 64 pv) 4 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na -> getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 pv ->
    exists fr' regs',
      msteps SEGS (@mkst fx regs (0x61ad0 : word) m rom)
                  (@mkst (mkFP fr' (@fp_csr fx)) regs' ret (wbytes (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 pv) bs) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 13; 14]%list) regs regs'.
  Proof.
    intros fx regs m na nalloc n rc arr i pv bs ret R Hi Hn Hna Hpv Hpv64 Harr Harr64 D1 D2 ALpv ALna ALarr RC SOK Hret H1 H10 H11 H12.
    pose proof (NUMA_wf m na nalloc n rc arr R) as (Wna & Wn & Wrc & Warr & Wna0 & Wna64).
    pose proof (NUMA_rd_n SEGS m na nalloc n rc arr R) as Cn. pose proof (NUMA_rd_arr SEGS m na nalloc n rc arr R) as Carr.
    assert (ALc : ((arr + 4 * i) mod 4 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALarr).
    eexists _, _. split.
    - stepb_ft F_61a78 D_61a78 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_61a7c D_61a7c andi_3 ALpv. stepb_ft F_61a80 D_61a80 ltac:(condZ).          (* [comment removed for export] *)
      stepST F_61a84 D_61a84 (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
      stepb_ft F_61a88 D_61a88 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_61a8c D_61a8c ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_61a90 D_61a90 andi_7 ALna. stepb_ft F_61a94 D_61a94 ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_61a98 D_61a98 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepb_ft F_61a9c D_61a9c ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_61aa0 D_61aa0 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; repeat rdn_peel1; exact Carr) ltac:(apply lez8; lia).
      stepiv F_61aa4 D_61aa4 (Z_to_bv 64 (4 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_61aa8 D_61aa8 (Z_to_bv 64 (arr + 4 * i)).
      stepb_ft F_61aac D_61aac ltac:(condZ).                                          (* [comment removed for export] *)
      snez1 F_61ab0 D_61ab0.                                                          (* [comment removed for export] *)
      seqz0 F_61ab4 D_61ab4.                                                          (* [comment removed for export] *)
      sn F_61ab8 D_61ab8.                                                             (* [comment removed for export] *)
      stepb_ft F_61abc D_61abc ltac:(condR).                                          (* [comment removed for export] *)
      stepb_ft F_61ac0 D_61ac0 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_61ac4 D_61ac4 andi_3 ALc. stepb_ft F_61ac8 D_61ac8 ltac:(condZ).          (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [ reflexivity
                  | eapply fp_step_flw with (a := Z_to_bv 64 (arr + 4 * i)) (bs := bs); [exact F_61acc | reflexivity | exact D_61acc | gres; imm_norm; addr_tac | repeat rdn_peel1; exact RC]
                  | step_simpl ].
      (* [comment removed for export] *)
      chain_step; [ reflexivity
                  | eapply fp_step_fsw with (a := Z_to_bv 64 pv); [exact F_61ad0 | reflexivity | exact D_61ad0 | gres; imm_norm; addr_tac | store_ok_peel; exact SOK]
                  | step_simpl ].
      stepret F_61ad4 D_61ad4 ret ltac:(exact H1).
      cbn [fp_regs]. rewrite fpv_get_same, fpv_flw_bytes by (exact (rdn_length _ _ _ _ _ RC)).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
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
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= nas)%Z -> (nas + 32 <= s - 128)%Z -> (0 <= n < 2 ^ 31)%Z -> (nas mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (nas + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
    store_ok SEGS m (Z_to_bv 64 (s - 128)) 128 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 nas -> getr regs 11 = Z_to_bv 64 0 ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x613c0 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x61688 : word) (NFEF m s ret regs (@fp_regs fx)) rom)
      /\ frm_zero cs'
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 1 = Z_to_bv 64 0x614cc /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = Z_to_bv 64 nas /\ getr regs' 18 = Z_to_bv 64 n /\ getr regs' 20 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 18; 20]%list) regs regs'.
  Proof.
    intros fx regs m s nas n ret Hz Hfa0 Hs Hs64 Hnas Hnas2 Hn ALnas Cn SOK H2 H1 H10 H11. unfold NFEF.
    eexists _, _, _. split.
    - zv F_61368 D_61368 (Z_to_bv 64 (s - 128)).   (* [comment removed for export] *)
      stepST F_6136c D_6136c (Z_to_bv 64 (s - 8)) (ret) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_61370 D_61370 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_61374 D_61374 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_61378 D_61378 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_6137c D_6137c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_61380 D_61380 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_61384 D_61384 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_61388 D_61388 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_6138c D_6138c (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_61390 D_61390 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_61394 D_61394 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 96)); [exact F_61398 | reflexivity | exact D_61398 | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 104)); [exact F_6139c | reflexivity | exact D_6139c | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 112)); [exact F_613a0 | reflexivity | exact D_613a0 | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_613a4 D_613a4.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_613a8 | reflexivity | exact D_613a8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_613ac D_613ac.   (* [comment removed for export] *)
      stepb_tk F_613b0 D_613b0 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_613c0 D_613c0 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fmv_w_x; [exact F_613c4 | reflexivity | exact D_613c4] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_613c8 | reflexivity | exact D_613c8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      rewrite Hfa0, fpv_unbox_box, sgnj_one, getr_zero, low32_0, delta_cmp.
      stepb_tk F_613cc D_613cc ltac:(condZ).   (* [comment removed for export] *)
      sn F_61460 D_61460.   (* [comment removed for export] *)
      sn F_61464 D_61464.   (* [comment removed for export] *)
      stepb_ft F_61918 D_61918 ltac:(condZ).   (* [comment removed for export] *)
      zand F_6191c D_6191c andi_7 ALnas. stepb_ft F_61920 D_61920 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_61924 D_61924 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.   (* [comment removed for export] *)
      stepret F_61928 D_61928 (Z_to_bv 64 0x614c0) ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_61468 D_61468.   (* [comment removed for export] *)
      sn F_6146c D_6146c.   (* [comment removed for export] *)
      sn F_61470 D_61470.   (* [comment removed for export] *)
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
      msteps SEGS (@mkst fx regs (0x614cc : word) m rom) (@mkst fx regs' (0x61ad0 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 8 = Z_to_bv 64 nas /\ getr regs' 9 = Z_to_bv 64 nad /\ getr regs' 18 = Z_to_bv 64 n
      /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x61504
      /\ getr regs' 10 = Z_to_bv 64 nas /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 116)
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 19]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n Hs Hs64 H2 H10 H8 H18 H20.
    eexists. split.
    - sn F_61474 D_61474.   (* [comment removed for export] *)
      stepb_tk F_61478 D_61478 ltac:(condZ).   (* [comment removed for export] *)
      sn F_61498 D_61498.   (* [comment removed for export] *)
      zv F_6149c D_6149c (Z_to_bv 64 (s - 116)).   (* [comment removed for export] *)
      sn F_614a0 D_614a0.   (* [comment removed for export] *)
      sn F_614a4 D_614a4.   (* [comment removed for export] *)
      sn F_614a8 D_614a8.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_B2 : forall (fx : FPState) regs m (s nas nad n : Z),
    (2 <= n < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 nas -> getr regs 9 = Z_to_bv 64 nad -> getr regs 18 = Z_to_bv 64 n ->
    getr regs 19 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x61504 : word) m rom) (@mkst fx regs' (0x61510 : word) m rom)
      /\ nfe_R1 regs' s nas nad n 1
      /\ regs_agree (fun r => In r [10; 21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n Hn H2 H8 H9 H18 H19. unfold nfe_R1.
    eexists. split.
    - sn F_614ac D_614ac.   (* [comment removed for export] *)
      stepb_ft F_614b0 D_614b0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_614b4 D_614b4.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L1h : forall (fx : FPState) regs m (s nas nad n i : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> nfe_R1 regs s nas nad n i ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x61510 : word) m rom) (@mkst fx regs' (0x61ad0 : word) m rom)
      /\ nfe_R1 regs' s nas nad n i /\ getr regs' 1 = Z_to_bv 64 0x61520
      /\ getr regs' 10 = Z_to_bv 64 nas /\ getr regs' 11 = Z_to_bv 64 i /\ getr regs' 12 = Z_to_bv 64 (s - 120)
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hs Hs64 (H2 & H8 & H9 & H18 & H19 & H21). unfold nfe_R1.
    eexists. split.
    - zv F_614b8 D_614b8 (Z_to_bv 64 (s - 120)).   (* [comment removed for export] *)
      sn F_614bc D_614bc.   (* [comment removed for export] *)
      sn F_614c0 D_614c0.   (* [comment removed for export] *)
      sn F_614c4 D_614c4.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  Lemma nfe_L1a : forall (fx : FPState) regs m (s : Z) (b8 b12 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 -> rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some b12 ->
    getr regs 2 = Z_to_bv 64 (s - 128) ->
    exists fr' cs' regs' (b : bool),
      msteps SEGS (@mkst fx regs (0x61520 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x61530 : word) m rom)
      /\ frm_zero cs' /\ getr regs' 10 = (if b then Z_to_bv 64 1 else Z_to_bv 64 0)
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros fx regs m s b8 b12 Hz Hs Hs64 R8 R12 H2.
    eexists _, _, _, _. split.
    - chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_614c8 | reflexivity | exact D_614c8 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 116)) (bs := b12); [exact F_614cc | reflexivity | exact D_614cc | gres; imm_norm; addr_tac | exact R12] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_614d0 | reflexivity | exact D_614d0 | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_614d4 | reflexivity | exact D_614d4] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L1b : forall (fx : FPState) regs m (b : bool),
    frm_zero (@fp_csr fx) -> getr regs 10 = (if b then Z_to_bv 64 1 else Z_to_bv 64 0) ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x61530 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x6153c : word) m rom)
      /\ frm_zero cs' /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0)
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros fx regs m b Hz H10. destruct b.
    - eexists _, _, _, _. split.
      + stepb_ft F_614d8 D_614d8 ltac:(condZ).   (* [comment removed for export] *)
        chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_614dc | reflexivity | exact D_614dc] | step_simpl ]; fpn.   (* [comment removed for export] *)
        chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_614e0 | reflexivity | exact D_614e0] | step_simpl ]; fpn.   (* [comment removed for export] *)
        apply mst_refl.
      + fin_fp Hz.
    - eexists _, _, _, _. split.
      + stepb_tk F_614d8 D_614d8 ltac:(condZ).   (* [comment removed for export] *)
        chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_614e0 | reflexivity | exact D_614e0] | step_simpl ]; fpn.   (* [comment removed for export] *)
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
      msteps SEGS (@mkst fx regs (0x6153c : word) m rom) (@mkst (mkFP fr' cs') regs' (0x61588 : word) m rom)
      /\ frm_zero cs' /\ nfe_R2 regs' s nas nad n (i + 1) i b
      /\ regs_agree (fun r => In r [10; 20; 22; 23; 25]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hz Hi Hin Hn (H2 & H8 & H9 & H18 & H19 & H21) H10. unfold nfe_R2, MONE.
    eexists _, _, _, _. split.
    - stepb_tk F_614e4 D_614e4 ltac:(condZ).   (* [comment removed for export] *)
      stepat F_614f4 D_614f4 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_614f8 D_614f8 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_614fc | reflexivity | exact D_614fc] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_61500 D_61500.   (* [comment removed for export] *)
      match goal with |- context [regupd _ 10 (if ?b then Z_to_bv 64 1 else Z_to_bv 64 0)] =>
        stepiv F_61504 D_61504 (if b then Z_to_bv 64 0 else Z_to_bv 64 18446744073709551615) ltac:(gres; pin; imm_norm; destruct b; apply bv_eq; reflexivity);   (* [comment removed for export] *)
        stepiv F_61508 D_61508 (if b then Z_to_bv 64 1 else Z_to_bv 64 18446744073709551615) ltac:(gres; pin; imm_norm; destruct b; apply bv_eq; reflexivity) end.   (* [comment removed for export] *)
      sn F_6150c D_6150c.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_61510 | reflexivity | exact D_61510] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_61514 D_61514.   (* [comment removed for export] *)
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
      msteps SEGS (@mkst fx regs (0x6153c : word) m rom) (@mkst fx regs' (0x61640 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 9 = Z_to_bv 64 nad
      /\ regs_agree (fun r => In r [20]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hi Hin Hi2 Hn (H2 & H8 & H9 & H18 & H19 & H21) H10.
    eexists. split.
    - stepb_tk F_614e4 D_614e4 ltac:(condZ).
      stepat F_614f4 D_614f4 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_tk F_614f8 D_614f8 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L1cN : forall (fx : FPState) regs m (s nas nad n i : Z),
    (1 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R1 regs s nas nad n i -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x6153c : word) m rom) (@mkst fx regs' (0x61510 : word) m rom)
      /\ nfe_R1 regs' s nas nad n (i + 1)
      /\ regs_agree (fun r => In r [21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hi Hin Hn (H2 & H8 & H9 & H18 & H19 & H21) H10. unfold nfe_R1.
    eexists. split.
    - stepb_ft F_614e4 D_614e4 ltac:(condZ).
      stepat F_614e8 D_614e8 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_tk F_614ec D_614ec ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma nfe_L1cE : forall (fx : FPState) regs m (s nas nad n i : Z),
    (1 <= i)%Z -> (i + 1 = n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R1 regs s nas nad n i -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x6153c : word) m rom) (@mkst fx regs' (0x61640 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 9 = Z_to_bv 64 nad
      /\ regs_agree (fun r => In r [21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i Hi Hin Hn (H2 & H8 & H9 & H18 & H19 & H21) H10.
    eexists. split.
    - stepb_ft F_614e4 D_614e4 ltac:(condZ).
      stepat F_614e8 D_614e8 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
      stepb_ft F_614ec D_614ec ltac:(condZ).
      sn F_614f0 D_614f0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma nfe_L2h : forall (fx : FPState) regs m (s nas nad n i loc : Z) (d : bool),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> nfe_R2 regs s nas nad n i loc d ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x61588 : word) m rom) (@mkst fx regs' (0x61ad0 : word) m rom)
      /\ nfe_R2 regs' s nas nad n i loc d /\ getr regs' 1 = Z_to_bv 64 0x61598
      /\ getr regs' 10 = Z_to_bv 64 nas /\ getr regs' 11 = Z_to_bv 64 i /\ getr regs' 12 = Z_to_bv 64 (s - 120)
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc d Hs Hs64 (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold nfe_R2.
    eexists. split.
    - zv F_61530 D_61530 (Z_to_bv 64 (s - 120)).   (* [comment removed for export] *)
      sn F_61534 D_61534.   (* [comment removed for export] *)
      sn F_61538 D_61538.   (* [comment removed for export] *)
      sn F_6153c D_6153c.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a : forall (fx : FPState) regs m (s nas nad n i loc : Z) (b8 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 ->
    nfe_R2 regs s nas nad n i loc true ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x61598 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x615a4 : word) m rom)
      /\ frm_zero cs' /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0)
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc b8 Hz Hs Hs64 Hi0 Hin Hn R8  (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold nfe_R2, MONE in *.
    eexists _, _, _, _. split.
    - chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_61540 | reflexivity | exact D_61540 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepb_ft F_61544 D_61544 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_61548 | reflexivity | exact D_61548] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b : forall (fx : FPState) regs m (s nas nad n i loc : Z) (b8 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 ->
    nfe_R2 regs s nas nad n i loc false ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x61598 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x615b4 : word) m rom)
      /\ frm_zero cs' /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0) /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [10; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc b8 Hz Hs Hs64 Hi0 Hin Hn R8  (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold nfe_R2, MONE in *.
    eexists _, _, _, _. split.
    - chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_61540 | reflexivity | exact D_61540 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepb_tk F_61544 D_61544 ltac:(condZ).   (* [comment removed for export] *)
      sn F_61550 D_61550.   (* [comment removed for export] *)
      stepb_ft F_61554 D_61554 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_61558 | reflexivity | exact D_61558] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a1 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc true -> getr regs 10 = Z_to_bv 64 1 ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x615a4 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x6157c : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i i true /\ getr regs' 24 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [21; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_tk F_6154c D_6154c ltac:(condZ).   (* [comment removed for export] *)
      sn F_61518 D_61518.   (* [comment removed for export] *)
      sn F_6151c D_6151c.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_61520 | reflexivity | exact D_61520] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a0 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc true -> getr regs 10 = Z_to_bv 64 0 ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x615a4 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x615d0 : word) m rom)
      /\ frm_zero cs'
      /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0) /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [10; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10. unfold nfe_R2, MONE in *.
    eexists _, _, _, _. split.
    - stepb_ft F_6154c D_6154c ltac:(condZ).   (* [comment removed for export] *)
      sn F_61550 D_61550.   (* [comment removed for export] *)
      stepb_tk F_61554 D_61554 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_6156c D_6156c ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_61570 | reflexivity | exact D_61570 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_61574 | reflexivity | exact D_61574] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a00 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc true -> getr regs 10 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x615d0 : word) m rom) (@mkst fx regs' (0x6157c : word) m rom)
      /\ nfe_R2 regs' s nas nad n i loc true /\ getr regs' 24 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists. split.
    - stepb_tk F_61578 D_61578 ltac:(condZ).   (* [comment removed for export] *)
      sn F_615e0 D_615e0.   (* [comment removed for export] *)
      sn F_615e4 D_615e4.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2a01 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc true -> getr regs 10 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x615d0 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x61848 : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i loc true /\ getr regs' 24 = Z_to_bv 64 MONE /\ getr regs' 1 = Z_to_bv 64 0x615e0 /\ getr regs' 10 = Z_to_bv 64 nad /\ reg_get fr' 10 = nan_box (Z_to_bv 32 (f32i loc))
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_ft F_61578 D_61578 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_6157c | reflexivity | exact D_6157c | left; split; reflexivity | left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_61580 D_61580.   (* [comment removed for export] *)
      sn F_61584 D_61584.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2aR : forall (fx : FPState) regs m (s nas nad n i loc : Z) (b8 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 -> nfe_R2 regs s nas nad n i loc true -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x615e0 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x6157c : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i i true /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc b8 Hz Hs Hs64 Hi0 Hin Hn Hloc R8 (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H24. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_tk F_61588 D_61588 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_61598 | reflexivity | exact D_61598 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_6159c D_6159c.   (* [comment removed for export] *)
      sn F_615a0 D_615a0.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b1 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc false -> getr regs 10 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x615b4 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x6157c : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i i false /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [21]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_ft F_6155c D_6155c ltac:(condZ).   (* [comment removed for export] *)
      sn F_61560 D_61560.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F_61564 | reflexivity | exact D_61564] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_61568 D_61568.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b0 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc false -> getr regs 10 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs' (b' : bool),
      msteps SEGS (@mkst fx regs (0x615b4 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x61610 : word) m rom)
      /\ frm_zero cs'
      /\ getr regs' 10 = (if b' then Z_to_bv 64 1 else Z_to_bv 64 0) /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists _, _, _, _. split.
    - stepb_tk F_6155c D_6155c ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_6156c D_6156c ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_615a4 D_615a4 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_615b0 | reflexivity | exact D_615b0 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_615b4 | reflexivity | exact D_615b4] | step_simpl ]; fpn.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b00 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc false -> getr regs 10 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x61610 : word) m rom) (@mkst fx regs' (0x6157c : word) m rom)
      /\ nfe_R2 regs' s nas nad n i loc false /\ getr regs' 24 = Z_to_bv 64 MONE
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists. split.
    - stepb_tk F_615b8 D_615b8 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2b01 : forall (fx : FPState) regs m (s nas nad n i loc : Z),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc false -> getr regs 10 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 MONE ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x61610 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x61848 : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i loc false /\ getr regs' 1 = Z_to_bv 64 0x61620 /\ getr regs' 10 = Z_to_bv 64 nad /\ reg_get fr' 10 = nan_box (Z_to_bv 32 (f32i loc))
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc Hz Hs Hs64 Hi0 Hin Hn Hloc (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H10 H24. unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_ft F_615b8 D_615b8 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_615bc | reflexivity | exact D_615bc | left; split; reflexivity | left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_615c0 D_615c0.   (* [comment removed for export] *)
      sn F_615c4 D_615c4.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_L2bR : forall (fx : FPState) regs m (s nas nad n i loc : Z) (b8 : list byte),
    frm_zero (@fp_csr fx) -> (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= loc < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some b8 -> nfe_R2 regs s nas nad n i loc false -> 
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x61620 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x6157c : word) m rom)
      /\ frm_zero cs'
      /\ nfe_R2 regs' s nas nad n i i false /\ getr regs' 24 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [21; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc b8 Hz Hs Hs64 Hi0 Hin Hn Hloc R8 (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold nfe_R2, MONE in *.
    eexists _, _, _. split.
    - stepb_tk F_615c8 D_615c8 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 120)) (bs := b8); [exact F_615d8 | reflexivity | exact D_615d8 | gres; imm_norm; addr_tac | exact R8] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_615dc D_615dc.   (* [comment removed for export] *)
      sn F_615e0 D_615e0.   (* [comment removed for export] *)
      sn F_615e4 D_615e4.   (* [comment removed for export] *)
      apply mst_refl.
    - fin_fp Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma nfe_LATn : forall (fx : FPState) regs m (s nas nad n i loc : Z) (d d' : bool),
    (0 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc d -> getr regs 24 = (if d' then Z_to_bv 64 1 else Z_to_bv 64 MONE) ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x6157c : word) m rom) (@mkst fx regs' (0x61588 : word) m rom)
      /\ nfe_R2 regs' s nas nad n (i + 1) loc d'
      /\ regs_agree (fun r => In r [20; 25]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc d d' Hi0 Hin Hn (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25) H24. unfold nfe_R2, MONE in *.
    eexists. split.
    - stepat F_61524 D_61524 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      sn F_61528 D_61528.   (* [comment removed for export] *)
      stepb_ft F_6152c D_6152c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  Lemma nfe_LATx : forall (fx : FPState) regs m (s nas nad n i loc : Z) (d : bool),
    (0 <= i)%Z -> (i + 1 = n)%Z -> (n < 2 ^ 31)%Z ->
    nfe_R2 regs s nas nad n i loc d ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x6157c : word) m rom) (@mkst fx regs' (0x61640 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 9 = Z_to_bv 64 nad
      /\ regs_agree (fun r => In r [20; 25]%list) regs regs'.
  Proof.
    intros fx regs m s nas nad n i loc d Hi0 Hin Hn (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25). unfold MONE in *.
    eexists. split.
    - stepat F_61524 D_61524 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      sn F_61528 D_61528.   (* [comment removed for export] *)
      stepb_tk F_6152c D_6152c ltac:(condZ).   (* [comment removed for export] *)
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
      msteps SEGS (@mkst fx regs (0x61640 : word) m rom) (@mkst (mkFP fr' (@fp_csr fx)) regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 nad
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21
      /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros fx regs m s nad ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 f8 f9 f18 Hs Hs64 Hret C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 CF8 CF9 CF18 H2 H9.
    eexists _, _. split.
    - sn F_615e8 D_615e8.   (* [comment removed for export] *)
      stepLD8 F_615ec D_615ec ret. stepLD8 F_615f0 D_615f0 v8. stepLD8 F_615f4 D_615f4 v9. stepLD8 F_615f8 D_615f8 v18.
      stepLD8 F_615fc D_615fc v19. stepLD8 F_61600 D_61600 v20. stepLD8 F_61604 D_61604 v21. stepLD8 F_61608 D_61608 v22.
      stepLD8 F_6160c D_6160c v23. stepLD8 F_61610 D_61610 v24. stepLD8 F_61614 D_61614 v25.
      chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 96)) (bs := f8); [exact F_61618 | reflexivity | exact D_61618 | gres; imm_norm; addr_tac | exact CF8] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 104)) (bs := f9); [exact F_6161c | reflexivity | exact D_6161c | gres; imm_norm; addr_tac | exact CF9] | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 112)) (bs := f18); [exact F_61620 | reflexivity | exact D_61620 | gres; imm_norm; addr_tac | exact CF18] | step_simpl ]; fpn.
      zv F_61624 D_61624 (Z_to_bv 64 s).   (* [comment removed for export] *)
      stepret F_61628 D_61628 ret ltac:(reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.


End Segs.
