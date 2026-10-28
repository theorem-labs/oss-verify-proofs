(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require FpReal ExpfModelB ExpfTablesB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require SeqExec.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptArithB GrayACELib LeptRop
  DitherLib DitherLoop LeptExecB LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptExpf V2LeptExpfV V2KernUb V2_code_kernelSetElement V2_code_krng.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require V2MallocLayout.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRop2Arith LeptRgbLib.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac condS :=
  idtac; pin; rewrite ?c_lts_Zs by lia;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | reflexivity ]; lia.
Ltac ldhyp F D a z R :=
  stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(rdn_addr a; exact R) ltac:(apply bytes_le_to_Z_4; unorm; lia);
  rewrite ?(v_lw_small z) by lia.
Ltac ldhyp8 F D a z R :=
  stepLD F D (word_to_le_bytes 8 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(rdn_addr a; exact R) ltac:(apply bytes_le_to_Z_8).

Ltac fpn := cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by reg_neq_tac
               | rewrite fpv_get_same | rewrite fpv_get_other by reg_neq_tac ].
Ltac fz Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.
(* [comment removed for export] *)
Ltac fsgnj F D := chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F | reflexivity | exact D] | step_simpl ]; fpn.
Ltac fcmp F D := chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F | reflexivity | exact D] | step_simpl ]; fpn.
Ltac fari F D Hz := chain_step; [ reflexivity | eapply fpv_step_fari; [exact F | reflexivity | exact D | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvt_ds F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f; [exact F | reflexivity | exact D | right; split; reflexivity | left; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvt_sd F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f; [exact F | reflexivity | exact D | left; split; reflexivity | right; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvt_swu F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F | reflexivity | exact D | left; split; reflexivity | right; left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fmvwx F D := chain_step; [ reflexivity | eapply fp_step_fmv_w_x; [exact F | reflexivity | exact D] | step_simpl ]; fpn.

Lemma w2b4_Z : forall z, (0 <= z < 2 ^ 64)%Z -> word_to_le_bytes 4 (Z_to_bv 64 z) = Z_to_le_bytes 4 z.
Proof. intros z Hz. unfold word_to_le_bytes. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fle_one_zero : fst (fpv_cmp F_LE FMT_S (bv_unsigned (unbox_s (Z_to_bv 64 18446744070479937536))) (bv_unsigned (low32 (Z_to_bv 64 0)))) = false.
Proof. vm_compute. reflexivity. Qed.

Section KseOk.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Variable rom : word -> option byte.
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).

  Lemma kse_ok : forall regs m (kel sy sx arr rp row col : Z) (ret : word),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (1 <= rp)%Z -> (rp + 4 * sx < 2 ^ 64)%Z ->
    (0 <= row < sy)%Z -> (0 <= col < sx)%Z -> (sy < 2 ^ 31)%Z -> (sx < 2 ^ 31)%Z ->
    (kel mod 8 = 0)%Z -> (arr mod 8 = 0)%Z -> (rp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (kel + 4)) 4 = Some (Z_to_le_bytes 4 sx) ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (Z_to_le_bytes 8 arr) -> rdn SEGS m (Z_to_bv 64 (arr + 8 * row)) 8 = Some (Z_to_le_bytes 8 rp) ->
    store_ok SEGS m (Z_to_bv 64 (rp + 4 * col)) 4 = true ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 kel -> getr regs 11 = Z_to_bv 64 row -> getr regs 12 = Z_to_bv 64 col ->
    exists regs',
      msteps SEGS (mkst regs (0x38940 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (rp + 4 * col)) (Z_to_le_bytes 4 (u (low32 (reg_get (@fp_regs fx) 10))))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m kel sy sx arr rp row col ret Hk Hk64 Ha Ha64 Hr Hr64 Hrow Hcol Hsy Hsx ALk ALa ALr Rsy Rsx Rarr Rrp SOK H1 Hret H10 H11 H12.
    assert (AL8r : ((arr + 8 * row) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALa).
    assert (AL4c : ((rp + 4 * col) mod 4 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALr).
    eexists. split.
    - stepb_ft F_38940 D_38940 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_38944 D_38944 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_38948 D_38948 andi_7 ALk.
      stepb_ft F_3894c D_3894c ltac:(condZ).
      stepLD F_38950 D_38950 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply lez4; lia).
      rewrite (v_lw_small sy) by lia.
      stepb_ft F_38954 D_38954 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_38958 D_38958 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_3895c D_3895c (Z_to_le_bytes 4 sx) (Z_to_bv 64 sx) ltac:(addr_norm; exact Rsx) ltac:(apply lez4; lia).
      rewrite (v_lw_small sx) by lia.
      stepb_ft F_38960 D_38960 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_38964 D_38964 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply lez8; lia).
      stepiv F_38968 D_38968 (Z_to_bv 64 (8 * row)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 3)%Z with 8%Z; lia).
      zv F_3896c D_3896c (Z_to_bv 64 (arr + 8 * row)).
      stepb_ft F_38970 D_38970 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_38974 D_38974. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      stepiv F_38978 D_38978 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_3897c D_3897c (Z_to_bv 64 1).                                            
      stepb_ft F_38980 D_38980 ltac:(condZ).                                          
      stepb_ft F_38984 D_38984 ltac:(condZ).                                          
      zand F_38988 D_38988 andi_7 AL8r.
      stepb_ft F_3898c D_3898c ltac:(condZ).
      stepLD F_38990 D_38990 (Z_to_le_bytes 8 rp) (Z_to_bv 64 rp) ltac:(addr_norm; exact Rrp) ltac:(apply lez8; lia).
      stepiv F_38994 D_38994 (Z_to_bv 64 (4 * col)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_38998 D_38998 (Z_to_bv 64 (rp + 4 * col)).
      stepb_ft F_3899c D_3899c ltac:(condZ).                                          
      sn F_389a0 D_389a0. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             
      stepiv F_389a4 D_389a4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   
      zlit F_389a8 D_389a8 (Z_to_bv 64 1).                                            
      stepb_ft F_389ac D_389ac ltac:(condZ).                                          
      stepb_ft F_389b0 D_389b0 ltac:(condZ).                                          
      zand F_389b4 D_389b4 andi_3 AL4c.
      stepb_ft F_389b8 D_389b8 ltac:(condZ).
      chain_step; [ reflexivity
                  | eapply fp_step_fsw with (a := Z_to_bv 64 (rp + 4 * col)); [exact F_389bc | reflexivity | exact D_389bc | gres; imm_norm; addr_tac | exact SOK]
                  | step_simpl ].
      stepret F_389c0 D_389c0 ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End KseOk.

Lemma krv_rdn_hit : forall (m : word -> option byte) (a z : Z), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) (Z_to_le_bytes 4 z)) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 z).
Proof.
  intros m a z Ha Ha4. pose proof (SeqExec.rdn_wbytes_hit SEGS (Z_to_le_bytes 4 z) m (Z_to_bv 64 a)) as H.
  rewrite length_Z_to_le_bytes in H. apply H. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
Lemma krv_den_u : bv_unsigned (Z_to_bv 32 ExpfTablesB.DEN_RANGE1) = ExpfTablesB.DEN_RANGE1.
Proof. vm_compute. reflexivity. Qed.
Lemma krv_arg : forall x : Z,
  fst (fpv_ari F_DIV FMT_S RNE
    (bv_unsigned (sgnj_val F_SGNJN (unbox_s (nan_box (Z_to_bv 32 (fst (fp_of_int (fp_format FMT_S) RNE false 32 (bv_unsigned (Z_to_bv 64 (x * x))))))))
                                   (unbox_s (nan_box (Z_to_bv 32 (fst (fp_of_int (fp_format FMT_S) RNE false 32 (bv_unsigned (Z_to_bv 64 (x * x))))))))))
    (bv_unsigned (unbox_s (nan_box (Z_to_bv 32 ExpfTablesB.DEN_RANGE1)))))
  = ExpfModelB.bil_arg ExpfTablesB.DEN_RANGE1 x.
Proof.
  intros x. rewrite !fpv_unbox_box, krv_den_u.
  unfold ExpfModelB.bil_arg, ExpfModelB.fneg32, ExpfModelB.u64, ExpfModelB.ES. reflexivity.
Qed.
Lemma krv_cellv : forall x : Z,
  bv_unsigned (low32 (nan_box (Z_to_bv 32 (ExpfModelB.expf_model (Z_to_bv 32 (ExpfModelB.bil_arg ExpfTablesB.DEN_RANGE1 x))))))
  = ExpfModelB.bil_cell ExpfTablesB.DEN_RANGE1 x.
Proof. intros x. rewrite fpv_low32_box. unfold ExpfModelB.bil_cell. reflexivity. Qed.

Section KrngSegs.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Notation w4 x := (word_to_le_bytes 4 x) (only parsing).

Definition FRR (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (fr : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (reg_get fr 8)).
Definition framer (s : Z) (ret : word) (r0 : bvmap 5 word) (fr : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, reg_get fr 8)].
Lemma FRR_out : forall m s ret regs fr (x : word), (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 40 <= u x < s)%Z -> FRR m s ret regs fr x = m x.
Proof.
  intros m s ret regs fr x Hs Hs64 Hx. pose proof (u64_range x). unfold FRR.
  rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.
Lemma framer_bounds : forall s ret r0 fr, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av => s - 40 <= fst av /\ fst av + 8 <= s)%Z (framer s ret r0 fr).
Proof. intros s ret r0 fr Hs Hs64. unfold framer. repeat constructor; cbn; lia. Qed.
Lemma framer_init : forall m s ret regs fr, (48 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRR m s ret regs fr) (framer s ret regs fr).
Proof. intros m s ret regs fr Hs Hs64. unfold cellsZ, framer, FRR. repeat split; rdn_solve. Qed.


Section Segs.
Variable rom : word -> option byte.

  Lemma kr_A : forall fr cs regs m (s : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> reg_get fr 10 = Z_to_bv 64 18446744070479937536 ->
    exists fr' cs' regs',
      msteps SEGS (@mkst (mkFP fr cs) regs (0x3b5c4 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x382d0 : word) (FRR m s ret regs fr) rom)
      /\ (frm_zero cs -> frm_zero cs') /\ (forall r : reg, r <> 8%bv -> r <> 15%bv -> reg_get fr' r = reg_get fr r)
      /\ reg_get fr' 8 = nan_box (Z_to_bv 32 FpReal.p_one_s)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x3b5fc /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 256
      /\ getr regs' 18 = Z_to_bv 64 256
      /\ regs_agree (fun x => In x [1; 2; 10; 11; 18]%list) regs regs'.
  Proof.
    intros fr cs regs m s ret Hs Hs64 SOK H2 H1 Hf10.
    assert (R10 : fpv_read fr FMT_S 10 = bv_unsigned (unbox_s (reg_get fr 10))) by reflexivity.
    do 3 eexists. split.
    - zv F_3b5c4 D_3b5c4 (Z_to_bv 64 (s - 48)).
      stepST F_3b5c8 D_3b5c8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_3b5cc D_3b5cc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_3b5d0 D_3b5d0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_3b5d4 D_3b5d4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 40)); [exact F_3b5d8 | reflexivity | exact D_3b5d8 | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.
      fmvwx F_3b5dc D_3b5dc.
      fcmp F_3b5e0 D_3b5e0. rewrite R10, Hf10, ?getr_zero, fle_one_zero.
      stepb_ft F_3b5e4 D_3b5e4 ltac:(cond_compute).
      fsgnj F_3b5e8 D_3b5e8.
      sn F_3b5ec D_3b5ec.
      sn F_3b5f0 D_3b5f0.
      sn F_3b5f4 D_3b5f4.
      sn F_3b5f8 D_3b5f8.
      apply mst_refl.
    - split; [intros FZ; cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ|].
      split; [intros r N8 N15; rewrite !fpv_get_other by assumption; reflexivity|].
      split; [rewrite fpv_get_same, Hf10; apply bv_eq; vm_compute; reflexivity|].
      repeat split; try solve_regs_agree; gres; pin; try reflexivity; bveq.
  Qed.

  Lemma kr_B : forall fr cs regs m (kel : Z),
    (1 <= kel < 2 ^ 64)%Z -> frm_zero cs -> getr regs 10 = Z_to_bv 64 kel -> reg_get fr 8 = nan_box (Z_to_bv 32 FpReal.p_one_s) ->
    exists fr' cs' regs',
      msteps SEGS (@mkst (mkFP fr cs) regs (0x3b5fc : word) m rom) (@mkst (mkFP fr' cs') regs' (0x38a54 : word) m rom)
      /\ frm_zero cs' /\ (forall r : reg, r <> 8%bv -> r <> 14%bv -> r <> 15%bv -> reg_get fr' r = reg_get fr r)
      /\ reg_get fr' 8 = nan_box (Z_to_bv 32 ExpfTablesB.DEN_RANGE1)
      /\ getr regs' 8 = Z_to_bv 64 kel /\ getr regs' 10 = Z_to_bv 64 kel /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 1 = Z_to_bv 64 0x3b620
      /\ regs_agree (fun x => In x [1; 8; 11; 12]%list) regs regs'.
  Proof.
    intros fr cs regs m kel Hk FZ H10 Hf8.
    do 3 eexists. split.
    - stepb_ft F_3b5fc D_3b5fc ltac:(condZ).
      sn F_3b600 D_3b600.
      fcvt_ds F_3b604 D_3b604 FZ.
      fari F_3b608 D_3b608 FZ.
      fari F_3b60c D_3b60c FZ.
      fcvt_sd F_3b610 D_3b610 FZ.
      sn F_3b614 D_3b614.
      sn F_3b618 D_3b618.
      sn F_3b61c D_3b61c.
      apply mst_refl.
    - split; [cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ|].
      split; [intros r N8 N14 N15; rewrite !fpv_get_other by assumption; reflexivity|].
      split; [rewrite fpv_get_same; unfold fpv_read; rewrite Hf8; apply bv_eq; vm_compute; reflexivity|].
      repeat split; try solve_regs_agree; gres; pin; try reflexivity; bveq.
  Qed.
  Lemma kse_run : forall fr cs regs m (kel arr row x : Z) (ret : word),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 < 2 ^ 64)%Z -> (1 <= row)%Z -> (row + 1024 + 8 <= 2 ^ 64)%Z -> (0 <= x < 256)%Z ->
    (kel mod 8 = 0)%Z -> (arr mod 8 = 0)%Z -> (row mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (w4 (Z_to_bv 64 1)) -> rdn SEGS m (Z_to_bv 64 (kel + 4)) 4 = Some (w4 (Z_to_bv 64 256)) ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
    rdn SEGS m (Z_to_bv 64 arr) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 row)) ->
    store_ok SEGS m (Z_to_bv 64 (row + 4 * x)) 4 = true ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 kel -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 x ->
    exists regs',
      msteps SEGS (@mkst (mkFP fr cs) regs (0x38940 : word) m rom)
                  (@mkst (mkFP fr cs) regs' ret (wbytes m (Z_to_bv 64 (row + 4 * x)) (Z_to_le_bytes 4 (u (low32 (reg_get fr 10))))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros fr cs regs m kel arr row x ret Hk Hk24 Ha Ha8 Hr Hr1032 Hx ALk ALa ALr Ch Cw Ca Cr SOK H1 Hret H10 H11 H12.
    rewrite w2b4_Z in Ch, Cw by lia. rewrite (w2b_Z 8 arr) in Ca by lia. rewrite (w2b_Z 8 row) in Cr by lia.
    replace (Z_to_bv 64 arr) with (Z_to_bv 64 (arr + 8 * 0)) in Cr by (f_equal; lia).
    destruct (@kse_ok (mkFP fr cs) rom regs m kel 1 256 arr row 0 x ret Hk Hk24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hx ltac:(lia) ltac:(lia)
                ALk ALa ALr Ch Cw Ca Cr SOK H1 Hret H10 H11 H12) as (regs' & RUN & E2 & E10 & AG).
    exists regs'. split; [exact RUN | split; [exact E10 | exact AG]].
  Qed.

  Lemma kr_C : forall (fx : FPState) regs m,
    exists regs',
      msteps SEGS (@mkst fx regs (0x3b620 : word) m rom) (@mkst fx regs' (0x3b624 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ regs_agree (fun x => In x [9]%list) regs regs'.
  Proof.
    intros fx regs m. eexists. split.
    - sn F_3b620 D_3b620.
      apply mst_refl.
    - split; [gres; pin; try reflexivity; bveq | solve_regs_agree].
  Qed.

  Lemma kr_E : forall fr0 fr cs regs r0 m (s kel : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (framer s ret r0 fr0) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 kel ->
    exists regs',
      msteps SEGS (@mkst (mkFP fr cs) regs (0x3b6bc : word) m rom) (@mkst (mkFP (bvmap_set 8 (reg_get fr0 8) fr) cs) regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 kel
      /\ (forall x, In x [8; 9; 18]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 18]%list) regs regs'.
  Proof.
    intros fr0 fr cs regs r0 m s kel ret Hs Hs64 Hret CF H2 H8.
    unfold framer in CF; cbn [cellsZ] in CF; destruct CF as (C1 & C2 & C3 & C4 & C5 & _).
    eexists. split.
    - zv F_3b6bc D_3b6bc (Z_to_bv 64 kel).
      stepLD8 F_3b6c0 D_3b6c0 ret.
      stepLD8 F_3b6c4 D_3b6c4 (getr r0 8).
      stepLD8 F_3b6c8 D_3b6c8 (getr r0 9).
      stepLD8 F_3b6cc D_3b6cc (getr r0 18).
      chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 40)) (bs := word_to_le_bytes 8 (reg_get fr0 8)); [exact F_3b6d0 | reflexivity | exact D_3b6d0 | gres; imm_norm; addr_tac | exact C5] | step_simpl ].
      rewrite exf_extract64; unfold le_bytes_to_word; rewrite bytes_le_to_Z_8, zbv_self.
      zv F_3b6d4 D_3b6d4 (Z_to_bv 64 s).
      stepret F_3b6d8 D_3b6d8 ret ltac:(reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
      intros x Hx; cbn in Hx; repeat destruct Hx as [<- | Hx]; first [ contradiction | gres; pin; reflexivity ].
  Qed.

  Section KrL.
  Variables (s kel arr row : Z) (M0 : word -> option byte).
  Definition R_Kr : list (Z * Z) := [(row, 1024%Z); ((s - 64)%Z, 16%Z)].
  Hypothesis GEO : (4096 <= s - 64 /\ s <= 2 ^ 47 /\ 4096 <= kel /\ kel + 24 <= 2 ^ 47 /\ 4096 <= arr /\ arr + 8 <= 2 ^ 47 /\ 4096 <= row /\ row + 1024 <= 2 ^ 47 /\
                    (row + 1024 <= kel \/ kel + 24 <= row) /\ (row + 1024 <= arr \/ arr + 8 <= row) /\ kel + 24 <= s - 64 /\ arr + 8 <= s - 64 /\ row + 1024 <= s - 64)%Z.
  Hypothesis ALG : (kel mod 8 = 0 /\ arr mod 8 = 0 /\ row mod 4 = 0)%Z.
  Hypothesis SOKr : store_ok SEGS M0 (Z_to_bv 64 row) 1024 = true.
  Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 (s - 64)) 16 = true.
  Hypothesis Ch : rdn SEGS M0 (Z_to_bv 64 kel) 4 = Some (w4 (Z_to_bv 64 1)).
  Hypothesis Cw : rdn SEGS M0 (Z_to_bv 64 (kel + 4)) 4 = Some (w4 (Z_to_bv 64 256)).
  Hypothesis Ca : rdn SEGS M0 (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)).
  Hypothesis Cr : rdn SEGS M0 (Z_to_bv 64 arr) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 row)).
  Hypothesis RO1 : forall j, (0x133a0 <= j < 0x134e8)%Z -> M0 (Z_to_bv 64 j) = None.
  Hypothesis RO2 : forall j, (0x127b4 <= j < 0x127c0)%Z -> M0 (Z_to_bv 64 j) = None.
  Ltac geo := pose proof GEO as (Gs & Gs47 & Gk & Gk2 & Ga & Ga2 & Gr & Gr2 & APrk & APra & Gks & Gas & Grs).

  Definition CL_Kr : list reg := [1; 2; 9; 10; 11; 12; 13; 14]%bv.

  Lemma kr_cell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv R_Kr M0 M -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
    (row + 1024 <= a \/ a + Z.of_nat n <= row)%Z -> (s - 64 + 16 <= a \/ a + Z.of_nat n <= s - 64)%Z ->
    rdn SEGS M0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros M a n bs RI Ha Han D1 D2 R. rewrite (rinv_rdn SEGS R_Kr M0 M a n RI Ha Han); [exact R|].
    intros r Hr. unfold R_Kr in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
  Qed.

  Lemma krv_ro_out : forall (lo : Z) (n : nat) (y : Z), store_ok SEGS M0 (Z_to_bv 64 lo) n = true -> (0 <= lo)%Z -> (lo + Z.of_nat n <= 2 ^ 64)%Z ->
    (0 <= y < 2 ^ 64)%Z -> M0 (Z_to_bv 64 y) = None -> wview SEGS M0 (Z_to_bv 64 y) = M0 (Z_to_bv 64 y) -> ~ (lo <= y < lo + Z.of_nat n)%Z.
  Proof.
    intros lo n y SOK Hlo Hn Hy Hm Hv Hin.
    assert (Hw : wview SEGS M0 (Z_to_bv 64 y) <> None).
    { apply (store_ok_all SEGS M0 n (Z_to_bv 64 lo)); rewrite ?u_Z2bv by lia; [lia | exact SOK | lia]. }
    apply Hw. rewrite Hv. exact Hm.
  Qed.

  Lemma krv_ro : forall (M : word -> option byte) (P : Z -> Prop), rinv R_Kr M0 M ->
    (forall j, P j -> M0 (Z_to_bv 64 j) = None) ->
    (forall j, P j -> (0 <= j < 2 ^ 64)%Z /\ exists seg, find_segment SEGS j 1 = Some seg /\ seg_writable seg = false) ->
    forall j, P j -> M (Z_to_bv 64 j) = None.
  Proof.
    intros M P RI HN HS j Hj. geo. destruct (HS j Hj) as (Hj64 & seg & Hf & Hw).
    pose proof (HN j Hj) as Hm.
    assert (Hv : wview SEGS M0 (Z_to_bv 64 j) = M0 (Z_to_bv 64 j)).
    { apply (MallocLayout.wview_of_find_ro SEGS M0 (Z_to_bv 64 j) seg); [rewrite u_Z2bv by lia; exact Hf | exact Hw]. }
    destruct RI as [_ RI']. transitivity (M0 (Z_to_bv 64 j)); [| exact Hm].
    apply RI'. intros r Hr. unfold R_Kr in Hr. cbn [In] in Hr. unfold inreg. rewrite u_Z2bv by lia.
    destruct Hr as [<-|[<-|[]]]; cbn [fst snd].
    - pose proof (krv_ro_out row 1024 j SOKr ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hj64 Hm Hv) as H.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. lia.
    - pose proof (krv_ro_out (s - 64) 16 j SOKs ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hj64 Hm Hv) as H.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. lia.
  Qed.

  Ltac krv_seg :=
    let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; cbv beta in Hj; split; [lia|];
    lazymatch type of V2MallocLayout.u16_find_seg1 with
    | forall y, (?b1 <= y)%Z -> _ => destruct (Z.lt_ge_cases j b1)
    end;
    (eexists; split; [first [apply V2MallocLayout.u16_find_seg0; lia | apply V2MallocLayout.u16_find_seg1; lia] | reflexivity]).

  Lemma kr_loop : forall (j : nat) fr0 regs0 fr cs regs (M : word -> option byte) (x : Z),
    Z.of_nat j = (256 - x)%Z -> (0 <= x < 256)%Z -> frm_zero cs -> rinv R_Kr M0 M ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 9 = Z_to_bv 64 x -> getr regs 8 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 256 ->
    reg_get fr 8 = nan_box (Z_to_bv 32 ExpfTablesB.DEN_RANGE1) ->
    regs_agree (fun r => In r CL_Kr) regs0 regs -> (forall r : reg, In (u r) fs_list -> reg_get fr r = reg_get fr0 r) ->
    reach SEGS (@mkst (mkFP fr cs) regs (0x3b624 : word) M rom)
      (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x3b6bc : word) M' rom /\ frm_zero cs' /\ rinv R_Kr M0 M' /\
                  rinv [((row + 4 * x)%Z, (1024 - 4 * x)%Z); ((s - 64)%Z, 16%Z)] M M' /\
                  getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 kel /\ regs_agree (fun r => In r CL_Kr) regs0 regs' /\
                  (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr0 r) /\
                  (forall jj, (x <= jj < 256)%Z -> rdn SEGS M' (Z_to_bv 64 (row + 4 * jj)) 4 =
                     Some (Z_to_le_bytes 4 (ExpfModelB.bil_cell ExpfTablesB.DEN_RANGE1 jj)))).
  Proof using GEO ALG SOKr SOKs Ch Cw Ca Cr RO1 RO2.
    induction j as [|j IH]; intros fr0 regs0 fr cs regs M x Hj Hx FZ RI E2 E9 E8 E18 F8 AG FS; [lia|].
    geo. destruct ALG as (ALk & ALa & ALr).
    eapply reach_msteps.
    { zv F_3b624 D_3b624 (Z_to_bv 64 (x * x)).
      fcvt_swu F_3b628 D_3b628 FZ.
      fsgnj F_3b62c D_3b62c.
      fari F_3b630 D_3b630 FZ.
      stepj F_3b634 D_3b634.
      apply mst_refl. }
    eapply reach_bind.
    { apply (expf_runV rom _ _ _ (s - 48) (Z_to_bv 64 0x3b638) (Z_to_bv 32 (ExpfModelB.bil_arg ExpfTablesB.DEN_RANGE1 x))).
      - fz FZ.
      - red; apply bv_eq; reflexivity.
      - gres; reflexivity.
      - gres; pin; reflexivity.
      - cbn [fp_regs]. rewrite fpv_get_same. do 2 f_equal. gres; pin.
        change (fpv_read fr FMT_S 8) with (bv_unsigned (unbox_s (reg_get fr 8))). rewrite F8.
        apply krv_arg.
      - lia.
      - replace (s - 48 - 16)%Z with (s - 64)%Z by lia.
        apply (reg_sok SEGS M0 M (s - 64) 16 (s - 64) 16); [exact (proj1 RI) | exact SOKs | lia | lia | lia | lia].
      - first [apply (krv_ro M _ RI RO1) | apply (krv_ro M _ RI RO2)]. krv_seg.
      - first [apply (krv_ro M _ RI RO1) | apply (krv_ro M _ RI RO2)]. krv_seg. }
    intros fin (fr2 & cs2 & regs2 & M2 & -> & FZ2 & FS2 & XV & AG2 & E2' & RI2).
    assert (RIa : rinv R_Kr M0 M2).
    { eapply rinv_trans; [exact RI|]. eapply rinv_weaken; [exact RI2|].
      intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. exists ((s - 64)%Z, 16%Z). cbn [fst snd]. split; [unfold R_Kr; cbn; tauto | lia]. }
    assert (RIb : rinv [((row + 4 * x)%Z, (1024 - 4 * x)%Z); ((s - 64)%Z, 16%Z)] M M2).
    { eapply rinv_weaken; [exact RI2|].
      intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. exists ((s - 64)%Z, 16%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
    assert (Ch2 : rdn SEGS M2 (Z_to_bv 64 kel) 4 = Some (w4 (Z_to_bv 64 1))) by (apply (kr_cell M2 kel 4 _ RIa); [lia | cbn; lia | cbn; lia | cbn; lia | exact Ch]).
    assert (Cw2 : rdn SEGS M2 (Z_to_bv 64 (kel + 4)) 4 = Some (w4 (Z_to_bv 64 256))) by (apply (kr_cell M2 (kel + 4) 4 _ RIa); [lia | cbn; lia | cbn; lia | cbn; lia | exact Cw]).
    assert (Ca2 : rdn SEGS M2 (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr))) by (apply (kr_cell M2 (kel + 16) 8 _ RIa); [lia | cbn; lia | cbn; lia | cbn; lia | exact Ca]).
    assert (Cr2 : rdn SEGS M2 (Z_to_bv 64 arr) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 row))) by (apply (kr_cell M2 arr 8 _ RIa); [lia | cbn; lia | cbn; lia | cbn; lia | exact Cr]).
    assert (SOK2 : store_ok SEGS M2 (Z_to_bv 64 (row + 4 * x)) 4 = true)
      by (apply (reg_sok SEGS M0 M2 row 1024 (row + 4 * x) 4); [exact (proj1 RIa) | exact SOKr | lia | lia | lia | cbn; lia]).
    assert (G8 : getr regs2 8 = Z_to_bv 64 kel) by (rewrite (AG2 8) by notin_list; gres; pin; reflexivity).
    assert (G9 : getr regs2 9 = Z_to_bv 64 x) by (rewrite (AG2 9) by notin_list; gres; pin; reflexivity).
    assert (G18 : getr regs2 18 = Z_to_bv 64 256) by (rewrite (AG2 18) by notin_list; gres; pin; reflexivity).
    assert (F8' : reg_get fr2 8 = nan_box (Z_to_bv 32 ExpfTablesB.DEN_RANGE1)).
    { rewrite FS2 by (unfold fs_list; in_list). cbn [fp_regs]. rewrite !fpv_get_other by reg_neq_tac. exact F8. }
    replace (Z_to_bv 64 0x3b638) with (0x3b638 : word) by (apply bv_eq; reflexivity).
    eapply reach_msteps.
    { sn F_3b638 D_3b638. sn F_3b63c D_3b63c. sn F_3b640 D_3b640.
      stepj F_3b644 D_3b644.
      apply mst_refl. }
    match goal with |- reach _ (@mkst _ ?R _ _ _) _ => set (R3 := R) end.
    destruct (kse_run fr2 cs2 R3 M2 kel arr row x (0x3b648 : word) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hx ALk ALa ALr
                Ch2 Cw2 Ca2 Cr2 SOK2 ltac:(subst R3; gres; bveq) ltac:(red; apply bv_eq; reflexivity)
                ltac:(subst R3; gres; pin; reflexivity) ltac:(subst R3; gres; reflexivity) ltac:(subst R3; gres; pin; reflexivity))
      as (regs4 & RUN4 & E10' & AG4).
    eapply reach_msteps; [exact RUN4|].
    set (M4 := wbytes M2 _ _).
    assert (RI4 : rinv R_Kr M0 M4).
    { subst M4. apply (rinv_wbytes R_Kr M0 M2 (row + 4 * x) 4); [exact RIa | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |].
      exists (row, 1024%Z). cbn [fst snd]. split; [unfold R_Kr; cbn; tauto | lia]. }
    assert (RIb4 : rinv [((row + 4 * x)%Z, (1024 - 4 * x)%Z); ((s - 64)%Z, 16%Z)] M M4).
    { subst M4. apply (rinv_wbytes _ M M2 (row + 4 * x) 4); [exact RIb | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |].
      exists ((row + 4 * x)%Z, (1024 - 4 * x)%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
    assert (VAL4 : rdn SEGS M4 (Z_to_bv 64 (row + 4 * x)) 4 = Some (Z_to_le_bytes 4 (ExpfModelB.bil_cell ExpfTablesB.DEN_RANGE1 x))).
    { subst M4. rewrite krv_rdn_hit by lia. do 2 f_equal. rewrite XV. apply krv_cellv. }
    assert (K8 : getr regs4 8 = Z_to_bv 64 kel) by (rewrite (AG4 8) by notin_list; subst R3; gres; exact G8).
    assert (K9 : getr regs4 9 = Z_to_bv 64 x) by (rewrite (AG4 9) by notin_list; subst R3; gres; exact G9).
    assert (K18 : getr regs4 18 = Z_to_bv 64 256) by (rewrite (AG4 18) by notin_list; subst R3; gres; exact G18).
    assert (K2 : getr regs4 2 = Z_to_bv 64 (s - 48)) by (rewrite (AG4 2) by notin_list; subst R3; gres; rewrite E2'; f_equal; lia).
    assert (AGr : regs_agree (fun r => In r CL_Kr) regs0 regs4) by (unfold CL_Kr in AG |- *; subst R3; ra_chain).
    destruct j as [|j].
    - assert (Ex : x = 255%Z) by lia. subst x.
      eapply reach_msteps.
      { stepiwv F_3b648 D_3b648 (Z_to_bv 64 256) ltac:(gres; pin; apply bv_eq; vm_compute; reflexivity).
        stepb_ft F_3b64c D_3b64c ltac:(condZ).
        stepj F_3b650 D_3b650.
        apply mst_refl. }
      apply reach_done. do 4 eexists. split; [reflexivity|].
      split; [exact FZ2|]. split; [exact RI4|]. split; [exact RIb4|]. split; [gres; exact K2|]. split; [gres; exact K8|]. split; [|split].
      + unfold CL_Kr in AGr |- *. apply regs_agree_upd; [in_list | exact AGr].
      + intros r Hr. rewrite FS2 by exact Hr. cbn [fp_regs]. unfold reg_get at 1.
        rewrite !bvmap_get_set_other by (let EQ := fresh in intros EQ; subst r; vm_compute in Hr; intuition discriminate). exact (FS r Hr).
      + intros jj Hjj. assert (jj = 255%Z) as -> by lia. exact VAL4.
    - eapply reach_msteps.
      { stepiwv F_3b648 D_3b648 (Z_to_bv 64 (x + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_tk F_3b64c D_3b64c ltac:(condZ).
        apply mst_refl. }
      eapply reach_weaken; [| eapply (IH fr0 regs0 fr2 cs2 _ M4 (x + 1)%Z ltac:(lia) ltac:(lia) FZ2 RI4)].
      + intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI' & RIx & E2f & E8f & AGf & FSf & VALf).
        exists fr', cs', regs', M'. split; [reflexivity|]. split; [exact FZ'|]. split; [exact RI'|].
        split.
        { eapply rinv_trans; [exact RIb4|]. eapply rinv_weaken; [exact RIx|].
          intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]].
          - exists ((row + 4 * x)%Z, (1024 - 4 * x)%Z). cbn [fst snd]. split; [cbn; tauto | lia].
          - exists ((s - 64)%Z, 16%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
        split; [exact E2f|]. split; [exact E8f|]. split; [exact AGf|]. split; [exact FSf|].
        intros jj Hjj. destruct (Z.eq_dec jj x) as [->|Hne].
        * rewrite (rinv_rdn SEGS _ M4 M' (row + 4 * x) 4 RIx); [exact VAL4 | lia | cbn; lia |].
          intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
        * apply VALf. lia.
      + gres; exact K2.
      + gres; reflexivity.
      + gres; exact K8.
      + gres; exact K18.
      + exact F8'.
      + unfold CL_Kr in AGr |- *. apply regs_agree_upd; [in_list | exact AGr].
      + intros r Hr. rewrite FS2 by exact Hr. cbn [fp_regs]. unfold reg_get at 1.
        rewrite !bvmap_get_set_other by (let EQ := fresh in intros EQ; subst r; vm_compute in Hr; intuition discriminate). exact (FS r Hr).
  Qed.
  End KrL.

End Segs.
End KrngSegs.
