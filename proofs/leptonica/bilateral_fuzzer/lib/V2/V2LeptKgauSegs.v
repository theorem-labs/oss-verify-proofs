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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptExpfV V2LeptKrngSegs V2_code_makeGaussianKernel.
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

Ltac fpn := cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by reg_neq_tac
               | rewrite fpv_get_same | rewrite fpv_get_other by reg_neq_tac ].
Ltac fz Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.
(* [comment removed for export] *)
Ltac fsgnj F D := chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F | reflexivity | exact D] | step_simpl ]; fpn.
Ltac fari F D Hz := chain_step; [ reflexivity | eapply fpv_step_fari; [exact F | reflexivity | exact D | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvt_ds F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f; [exact F | reflexivity | exact D | right; split; reflexivity | left; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvt_sd F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f; [exact F | reflexivity | exact D | left; split; reflexivity | right; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvt_sw F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F | reflexivity | exact D | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac kglit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
Ltac kgand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
Ltac kgfix F D v := sn F D; fixv v ltac:(gres; pin; apply bv_eq; vm_compute; reflexivity).

Lemma kg_sgnj_mx : nan_box (sgnj_val F_SGNJ (unbox_s (Z_to_bv 64 18446744070479937536)) (unbox_s (Z_to_bv 64 18446744070479937536))) = nan_box (Z_to_bv 32 FpReal.p_one_s).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma kg_sgnj_sd : nan_box (sgnj_val F_SGNJ (unbox_s (Z_to_bv 64 18446744070507200512)) (unbox_s (Z_to_bv 64 18446744070507200512))) = Z_to_bv 64 18446744070507200512.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma kg_swrap_small : forall z : Z, (- 2 ^ 31 <= z < 2 ^ 31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31)%Z by reflexivity. replace (bv_modulus 32) with (2 ^ 32)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma kg_mod64_32 : forall x : Z, ((x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32)%Z.
Proof.
  intros x. rewrite (Z.mod_eq x (2 ^ 64)) by lia.
  replace (x - 2 ^ 64 * (x / 2 ^ 64))%Z with (x + (- (x / 2 ^ 64) * 2 ^ 32) * 2 ^ 32)%Z by ring.
  apply Z_mod_plus_full.
Qed.
Lemma kg_mulw_s : forall a b : Z, (- 2 ^ 31 <= a * b < 2 ^ 31)%Z -> v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b H. unfold v_mulw. rewrite !u_Z2bv_mod. f_equal.
  transitivity (bv_swrap 32 (a * b)); [apply bv_swrap_congr | apply kg_swrap_small; exact H].
  unfold bv_wrap. replace (bv_modulus 32) with (2 ^ 32)%Z by reflexivity.
  rewrite Z.mul_mod by lia. rewrite !kg_mod64_32. rewrite <- Z.mul_mod by lia. reflexivity.
Qed.
Lemma kg_subw_s : forall a b : Z, (- 2 ^ 31 <= a - b < 2 ^ 31)%Z -> v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H. unfold v_subw. rewrite !u_Z2bv_mod. f_equal.
  transitivity (bv_swrap 32 (a - b)); [apply bv_swrap_congr | apply kg_swrap_small; exact H].
  unfold bv_wrap. replace (bv_modulus 32) with (2 ^ 32)%Z by reflexivity.
  rewrite Zminus_mod. rewrite !kg_mod64_32. rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma kg_ofint_s : forall f md v, (0 <= v < 2 ^ 31)%Z -> fp_of_int f md true 32 v = fp_of_int f md false 32 v.
Proof.
  intros f md v Hv.
  assert (Hb : Z.testbit (int_wrap 32 v) (32 - 1) = false).
  { unfold int_wrap. rewrite Z.land_spec. replace (32 - 1)%Z with 31%Z by reflexivity.
    destruct (Z.eq_dec v 0) as [->|Hn]; [reflexivity|].
    rewrite Z.bits_above_log2; [reflexivity | lia |].
    apply (proj1 (Z.log2_lt_pow2 v 31 ltac:(lia))). lia. }
  unfold fp_of_int. cbn [andb]. rewrite Hb. reflexivity.
Qed.
Lemma kg_den_u : bv_unsigned (Z_to_bv 64 ExpfTablesB.DEN_GAUSS_D) = ExpfTablesB.DEN_GAUSS_D.
Proof. vm_compute. reflexivity. Qed.
Lemma kg_one_u : bv_unsigned (unbox_s (nan_box (Z_to_bv 32 FpReal.p_one_s))) = FpReal.p_one_s.
Proof. vm_compute. reflexivity. Qed.
Lemma kg_arg : forall q, (0 <= q < 2 ^ 31)%Z ->
  fst (fp_convert (fp_format FMT_D) (fp_format FMT_S) RNE
    (bv_unsigned (Z_to_bv 64 (fst (fpv_ari F_DIV FMT_D RNE
      (bv_unsigned (Z_to_bv 64 (fst (fp_convert (fp_format FMT_S) (fp_format FMT_D) RNE
        (bv_unsigned (sgnj_val F_SGNJN (unbox_s (nan_box (Z_to_bv 32 (fst (fp_of_int (fp_format FMT_S) RNE true 32 (bv_unsigned (Z_to_bv 64 q)))))))
                                       (unbox_s (nan_box (Z_to_bv 32 (fst (fp_of_int (fp_format FMT_S) RNE true 32 (bv_unsigned (Z_to_bv 64 q)))))))))))))
      (bv_unsigned (Z_to_bv 64 ExpfTablesB.DEN_GAUSS_D)))))))
  = ExpfModelB.gauss_arg ExpfTablesB.DEN_GAUSS_D q.
Proof.
  intros q Hq. rewrite !fpv_unbox_box, kg_den_u.
  rewrite (u_Z2bv q) by lia. rewrite kg_ofint_s by exact Hq.
  unfold ExpfModelB.gauss_arg, ExpfModelB.fneg32, ExpfModelB.u64, ExpfModelB.ES, ExpfModelB.ED.
  rewrite (u_Z2bv q) by lia. reflexivity.
Qed.
Lemma kg_cellv : forall q,
  bv_unsigned (low32 (nan_box (Z_to_bv 32 (fst (fpv_ari F_MUL FMT_S RNE (bv_unsigned (unbox_s (nan_box (Z_to_bv 32 FpReal.p_one_s))))
    (bv_unsigned (unbox_s (nan_box (Z_to_bv 32 (ExpfModelB.expf_model (Z_to_bv 32 (ExpfModelB.gauss_arg ExpfTablesB.DEN_GAUSS_D q))))))))))))
  = ExpfModelB.gauss_cell ExpfTablesB.DEN_GAUSS_D FpReal.p_one_s q.
Proof.
  intros q. rewrite fpv_low32_box, kg_one_u, fpv_unbox_box.
  unfold ExpfModelB.gauss_cell, ExpfModelB.u32, ExpfModelB.ES. reflexivity.
Qed.
Lemma kgi_addw_s : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b H. unfold v_addw. rewrite !u_Z2bv_mod. f_equal.
  transitivity (bv_swrap 32 (a + b)); [apply bv_swrap_congr | apply kg_swrap_small; exact H].
  unfold bv_wrap. replace (bv_modulus 32) with (2 ^ 32)%Z by reflexivity.
  rewrite Zplus_mod. rewrite !kg_mod64_32. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma kgi_addiw_s : forall a k : Z, (- 2 ^ 31 <= a + k < 2 ^ 31)%Z -> v_addiw (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof.
  intros a k H. unfold v_addiw. rewrite u_Z2bv_mod. f_equal.
  transitivity (bv_swrap 32 (a + k)); [apply bv_swrap_congr | apply kg_swrap_small; exact H].
  unfold bv_wrap. replace (bv_modulus 32) with (2 ^ 32)%Z by reflexivity.
  rewrite Zplus_mod. rewrite kg_mod64_32. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma kgi_wview_ro : forall (m : word -> option byte) (a : word),
  ((0x127b4 <= bv_unsigned a < 0x127c0) \/ (0x133a0 <= bv_unsigned a < 0x134e8))%Z -> wview SEGS m a = m a.
Proof.
  intros m a Ha.
  lazymatch type of V2MallocLayout.u16_find_seg1 with
  | forall y, (?b1 <= y)%Z -> _ => destruct (Z.lt_ge_cases (bv_unsigned a) b1) as [H1|H1]
  end.
  - eapply MallocLayout.wview_of_find_ro; [apply V2MallocLayout.u16_find_seg0; lia | reflexivity].
  - eapply MallocLayout.wview_of_find_ro; [apply V2MallocLayout.u16_find_seg1; lia | reflexivity].
Qed.
Lemma kgi_rdn_hit : forall (m : word -> option byte) (a z : Z), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) (Z_to_le_bytes 4 z)) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 z).
Proof.
  intros m a z Ha Ha4. pose proof (SeqExec.rdn_wbytes_hit SEGS (Z_to_le_bytes 4 z) m (Z_to_bv 64 a)) as H.
  rewrite length_Z_to_le_bytes in H. apply H. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Section KgauSegs.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Notation w4 x := (word_to_le_bytes 4 x) (only parsing).
#[local] Notation w8 x := (word_to_le_bytes 8 x) (only parsing).

(* [comment removed for export] *)
Definition FRG (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (fr : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (w8 ret))
    (Z_to_bv 64 (s - 16)) (w8 (getr regs 8))) (Z_to_bv 64 (s - 24)) (w8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (w8 (getr regs 18))) (Z_to_bv 64 (s - 40)) (w8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (w8 (getr regs 20))) (Z_to_bv 64 (s - 56)) (w8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (w8 (getr regs 22))) (Z_to_bv 64 (s - 72)) (w8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (w8 (getr regs 24))) (Z_to_bv 64 (s - 88)) (w8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (w8 (reg_get fr 8))) (Z_to_bv 64 (s - 104)) (w8 (reg_get fr 9)).
Definition frameg (s : Z) (ret : word) (r0 : bvmap 5 word) (fr : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
   ((s - 56)%Z, getr r0 21); ((s - 64)%Z, getr r0 22); ((s - 72)%Z, getr r0 23); ((s - 80)%Z, getr r0 24); ((s - 88)%Z, getr r0 25);
   ((s - 96)%Z, reg_get fr 8); ((s - 104)%Z, reg_get fr 9)].
Lemma FRG_out : forall m s ret regs fr (x : word), (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 104 <= u x < s)%Z -> FRG m s ret regs fr x = m x.
Proof.
  intros m s ret regs fr x Hs Hs64 Hx. pose proof (u64_range x). unfold FRG.
  rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.
Lemma frameg_bounds : forall s ret r0 fr, (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av => s - 104 <= fst av /\ fst av + 8 <= s)%Z (frameg s ret r0 fr).
Proof. intros s ret r0 fr Hs Hs64. unfold frameg. repeat constructor; cbn; lia. Qed.
Lemma frameg_init : forall m s ret regs fr, (112 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRG m s ret regs fr) (frameg s ret regs fr).
Proof. intros m s ret regs fr Hs Hs64. unfold cellsZ, frameg, FRG. repeat split; rdn_solve. Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma kg_A : forall fr cs regs m (s : Z) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 20 -> getr regs 11 = Z_to_bv 64 20 ->
    reg_get fr 10 = Z_to_bv 64 18446744070507200512 -> reg_get fr 11 = Z_to_bv 64 18446744070479937536 ->
    exists fr' regs',
      msteps SEGS (@mkst (mkFP fr cs) regs (0x390ac : word) m rom) (@mkst (mkFP fr' cs) regs' (0x382d0 : word) (FRG m s ret regs fr) rom)
      /\ (forall r : reg, r <> 8%bv -> r <> 9%bv -> reg_get fr' r = reg_get fr r)
      /\ reg_get fr' 8 = nan_box (Z_to_bv 32 FpReal.p_one_s) /\ reg_get fr' 9 = Z_to_bv 64 18446744070507200512
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x3911c /\ getr regs' 10 = Z_to_bv 64 41 /\ getr regs' 11 = Z_to_bv 64 41
      /\ getr regs' 8 = Z_to_bv 64 20 /\ getr regs' 9 = Z_to_bv 64 20 /\ getr regs' 21 = Z_to_bv 64 40 /\ getr regs' 22 = Z_to_bv 64 40
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 11; 12; 21; 22]%list) regs regs'.
Proof.
  intros fr cs regs m s ret Hs Hs64 SOK H2 H1 H10 H11 Hf10 Hf11.
  do 2 eexists. split.
  - zv F_390ac D_390ac (Z_to_bv 64 (s - 112)).
    stepST F_390b0 D_390b0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_390b4 D_390b4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_390b8 D_390b8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_390bc D_390bc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_390c0 D_390c0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_390c4 D_390c4 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_390c8 D_390c8 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_390cc D_390cc (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_390d0 D_390d0 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_390d4 D_390d4 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_390d8 D_390d8 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 96)); [exact F_390dc | reflexivity | exact D_390dc | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.
    chain_step; [ reflexivity | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 104)); [exact F_390e0 | reflexivity | exact D_390e0 | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.
    zv F_390e4 D_390e4 (Z_to_bv 64 20).
    kglit F_390e8 D_390e8 (Z_to_bv 64 1073741824).
    kgfix F_390ec D_390ec (Z_to_bv 64 1073741844).
    stepb_ft F_390f0 D_390f0 ltac:(condZ).
    zv F_390f4 D_390f4 (Z_to_bv 64 20).
    kgfix F_390f8 D_390f8 (Z_to_bv 64 1073741844).
    stepb_ft F_390fc D_390fc ltac:(condZ).
    fsgnj F_39100 D_39100. rewrite Hf11, kg_sgnj_mx.
    fsgnj F_39104 D_39104. rewrite Hf10, kg_sgnj_sd.
    kgfix F_39108 D_39108 (Z_to_bv 64 40).
    kgfix F_3910c D_3910c (Z_to_bv 64 40).
    kglit F_39110 D_39110 (Z_to_bv 64 41).
    kglit F_39114 D_39114 (Z_to_bv 64 41).
    sn F_39118 D_39118.
    apply mst_refl.
  - split; [intros r Hr8 Hr9; rewrite !fpv_get_other by assumption; reflexivity|].
    split; [rewrite fpv_get_other by reg_neq_tac; apply fpv_get_same|].
    split; [apply fpv_get_same|].
    repeat split; try solve_regs_agree; gres; pin; try reflexivity; bveq.
Qed.

  (* [comment removed for export] *)
  Lemma kg_B : forall fr cs regs m (kel : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (kel mod 8 = 0)%Z -> frm_zero cs ->
    store_ok SEGS m (Z_to_bv 64 (kel + 8)) 8 = true -> reg_get fr 9 = Z_to_bv 64 18446744070507200512 ->
    getr regs 10 = Z_to_bv 64 kel -> getr regs 8 = Z_to_bv 64 20 -> getr regs 9 = Z_to_bv 64 20 -> getr regs 22 = Z_to_bv 64 40 ->
    exists fr' cs' regs',
      msteps SEGS (@mkst (mkFP fr cs) regs (0x3911c : word) m rom)
                  (@mkst (mkFP fr' cs') regs' (0x39158 : word)
                     (wbytes (wbytes m (Z_to_bv 64 (kel + 8)) (w4 (Z_to_bv 64 20))) (Z_to_bv 64 (kel + 12)) (w4 (Z_to_bv 64 20))) rom)
      /\ frm_zero cs' /\ (forall r : reg, r <> 9%bv -> r <> 14%bv -> r <> 15%bv -> reg_get fr' r = reg_get fr r)
      /\ reg_get fr' 9 = Z_to_bv 64 ExpfTablesB.DEN_GAUSS_D
      /\ getr regs' 18 = Z_to_bv 64 kel /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 41 /\ getr regs' 23 = Z_to_bv 64 (-20)
      /\ regs_agree (fun x => In x [10; 18; 19; 22; 23]%list) regs regs'.
Proof.
  intros fr cs regs m kel Hk Hk24 ALk FZ SOK Hf9 H10 H8 H9 H22.
  do 3 eexists. split.
  - stepb_ft F_3911c D_3911c ltac:(condZ).
    zv F_39120 D_39120 (Z_to_bv 64 kel).
    kgand F_39124 D_39124 andi_7 ALk.
    stepb_ft F_39128 D_39128 ltac:(condZ).
    stepST F_3912c D_3912c (Z_to_bv 64 (kel + 8)) (Z_to_bv 64 20) ltac:(sok_in SOK).
    stepST F_39130 D_39130 (Z_to_bv 64 (kel + 12)) (Z_to_bv 64 20) ltac:(sok_in SOK).
    stepb_ft F_39134 D_39134 ltac:(condZ).
    fcvt_ds F_39138 D_39138 FZ.
    kglit F_3913c D_3913c (Z_to_bv 64 41).
    fari F_39140 D_39140 FZ.
    stepb_tk F_39144 D_39144 ltac:(condZ).
    kglit F_3914c D_3914c (Z_to_bv 64 0).
    fari F_39150 D_39150 FZ.
    kgfix F_39154 D_39154 (Z_to_bv 64 (-20)).
    apply mst_refl.
  - split; [cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ|].
    split; [intros r Hr9 Hr14 Hr15; rewrite !fpv_get_other by assumption; reflexivity|].
    split; [rewrite fpv_get_same; unfold fpv_read; rewrite Hf9; apply bv_eq; vm_compute; reflexivity|].
    repeat split; try solve_regs_agree; gres; pin; reflexivity.
Qed.

  (* [comment removed for export] *)
  Lemma kg_OH : forall (fx : FPState) regs m (i : Z),
    (0 <= i < 41)%Z ->
    getr regs 8 = Z_to_bv 64 20 -> getr regs 9 = Z_to_bv 64 20 -> getr regs 19 = Z_to_bv 64 i -> getr regs 23 = Z_to_bv 64 (-20) ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x39158 : word) m rom) (@mkst fx regs' (0x39188 : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 ((i - 20) * (i - 20)) /\ getr regs' 25 = Z_to_bv 64 (-20)
      /\ regs_agree (fun x => In x [10; 11; 20; 24; 25]%list) regs regs'.
Proof.
  intros fx regs m i Hi H8 H9 H19 H23.
  assert (Hq : (0 <= (i - 20) * (i - 20) <= 400)%Z) by (split; [apply Z.square_nonneg | nia]).
  eexists. split.
  - stepb_ft F_39158 D_39158 ltac:(condZ).
    zv F_3915c D_3915c (Z_to_bv 64 (i - 20)).
    sn F_39160 D_39160. fixv (Z_to_bv 64 (i - 20)) ltac:(gres; pin; apply kg_subw_s; lia).
    stepb_ft F_39164 D_39164 ltac:(apply c_eq_refl).
    zv F_39168 D_39168 (Z_to_bv 64 ((i - 20) * (i - 20))).
    stepat F_3916c D_3916c (Z_to_bv 64 ((i - 20) * (i - 20))) ltac:(gres; pin; apply kg_mulw_s; lia).
    stepat F_39170 D_39170 (Z_to_bv 64 0) ltac:(gres; pin; unfold v_xor; rewrite Z.lxor_nilpotent; reflexivity).
    stepat F_39174 D_39174 (Z_to_bv 64 0) ltac:(gres; pin; apply bv_eq; vm_compute; reflexivity).
    stepb_ft F_39178 D_39178 ltac:(condZ).
    kglit F_3917c D_3917c (Z_to_bv 64 0).
    stepiwv F_39180 D_39180 (Z_to_bv 64 ((i - 20) * (i - 20))) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
    zv F_39184 D_39184 (Z_to_bv 64 (-20)).
    apply mst_refl.
  - repeat split; try solve_regs_agree; gres; pin; reflexivity.
Qed.

  (* [comment removed for export] *)
  Lemma kg_ON : forall (fx : FPState) (last : bool) regs m (i : Z),
    (0 <= i < 41)%Z -> (if last then i + 1 = 41 else i + 1 < 41)%Z ->
    getr regs 19 = Z_to_bv 64 i -> getr regs 21 = Z_to_bv 64 40 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x391dc : word) m rom) (@mkst fx regs' (if last then (0x39258 : word) else (0x39158 : word)) m rom)
      /\ getr regs' 19 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun x => In x [10; 19]%list) regs regs'.
Proof.
  intros fx last regs m i Hi Hl H19 H21.
  destruct last; eexists; split.
  - stepiwv F_391dc D_391dc (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
    stepb_ft F_391e0 D_391e0 ltac:(condZ).
    zv F_391e4 D_391e4 (Z_to_bv 64 (i + 1)).
    stepb_ft F_391e8 D_391e8 ltac:(condZ).
    sn F_391ec D_391ec.
    apply mst_refl.
  - repeat split; try solve_regs_agree; gres; pin; reflexivity.
  - stepiwv F_391dc D_391dc (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
    stepb_ft F_391e0 D_391e0 ltac:(condZ).
    zv F_391e4 D_391e4 (Z_to_bv 64 (i + 1)).
    stepb_tk F_391e8 D_391e8 ltac:(condZ).
    apply mst_refl.
  - repeat split; try solve_regs_agree; gres; pin; reflexivity.
Qed.

  (* [comment removed for export] *)
  Lemma kg_E : forall fr0 fr cs regs r0 m (s kel : Z) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameg s ret r0 fr0) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 18 = Z_to_bv 64 kel ->
    exists regs',
      msteps SEGS (@mkst (mkFP fr cs) regs (0x39258 : word) m rom) (@mkst (mkFP (bvmap_set 9 (reg_get fr0 9) (bvmap_set 8 (reg_get fr0 8) fr)) cs) regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 kel
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof.
  intros fr0 fr cs regs r0 m s kel ret Hs Hs64 Hret CF H2 H18.
  unfold frameg in CF; cbn [cellsZ] in CF; destruct CF as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
  eexists. split.
  - zv F_39258 D_39258 (Z_to_bv 64 kel).
    stepLD8 F_3925c D_3925c ret.
    stepLD8 F_39260 D_39260 (getr r0 8).
    stepLD8 F_39264 D_39264 (getr r0 9).
    stepLD8 F_39268 D_39268 (getr r0 18).
    stepLD8 F_3926c D_3926c (getr r0 19).
    stepLD8 F_39270 D_39270 (getr r0 20).
    stepLD8 F_39274 D_39274 (getr r0 21).
    stepLD8 F_39278 D_39278 (getr r0 22).
    stepLD8 F_3927c D_3927c (getr r0 23).
    stepLD8 F_39280 D_39280 (getr r0 24).
    stepLD8 F_39284 D_39284 (getr r0 25).
    chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 96)) (bs := word_to_le_bytes 8 (reg_get fr0 8)); [exact F_39288 | reflexivity | exact D_39288 | gres; imm_norm; addr_tac | exact C12] | step_simpl ].
    rewrite exf_extract64; unfold le_bytes_to_word; rewrite bytes_le_to_Z_8, zbv_self.
    chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 (s - 104)) (bs := word_to_le_bytes 8 (reg_get fr0 9)); [exact F_3928c | reflexivity | exact D_3928c | gres; imm_norm; addr_tac | exact C13] | step_simpl ].
    rewrite exf_extract64; unfold le_bytes_to_word; rewrite bytes_le_to_Z_8, zbv_self.
    zv F_39290 D_39290 (Z_to_bv 64 s).
    stepret F_39294 D_39294 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
    intros x Hx; cbn in Hx; repeat destruct Hx as [<- | Hx]; first [ contradiction | gres; pin; reflexivity ].
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section KgL.
  Variables (s kel arr i ri : Z) (M0 : word -> option byte).
  Definition R_Kg : list (Z * Z) := [(ri, 164%Z); ((s - 128)%Z, 16%Z)].
  Hypothesis GEO : (4096 <= s - 128 /\ s <= 2 ^ 47 /\ 4096 <= kel /\ kel + 24 <= 2 ^ 47 /\ 4096 <= arr /\ arr + 328 <= 2 ^ 47 /\ 4096 <= ri /\ ri + 164 <= 2 ^ 47 /\
                    (ri + 164 <= kel \/ kel + 24 <= ri) /\ (ri + 164 <= arr \/ arr + 328 <= ri) /\ kel + 24 <= s - 128 /\ arr + 328 <= s - 128 /\ ri + 164 <= s - 128 /\
                    0 <= i < 41)%Z.
  Hypothesis ALG : (kel mod 8 = 0 /\ arr mod 8 = 0 /\ ri mod 4 = 0)%Z.
  Hypothesis SOKr : store_ok SEGS M0 (Z_to_bv 64 ri) 164 = true.
  Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 (s - 128)) 16 = true.
  Hypothesis Ch : rdn SEGS M0 (Z_to_bv 64 kel) 4 = Some (w4 (Z_to_bv 64 41)).
  Hypothesis Cw : rdn SEGS M0 (Z_to_bv 64 (kel + 4)) 4 = Some (w4 (Z_to_bv 64 41)).
  Hypothesis Ca : rdn SEGS M0 (Z_to_bv 64 (kel + 16)) 8 = Some (w8 (Z_to_bv 64 arr)).
  Hypothesis Cr : rdn SEGS M0 (Z_to_bv 64 (arr + 8 * i)) 8 = Some (w8 (Z_to_bv 64 ri)).
  Hypothesis RO1 : forall j, (0x133a0 <= j < 0x134e8)%Z -> M0 (Z_to_bv 64 j) = None.
  Hypothesis RO2 : forall j, (0x127b4 <= j < 0x127c0)%Z -> M0 (Z_to_bv 64 j) = None.
  Ltac geo := pose proof GEO as (Gs & Gs47 & Gk & Gk2 & Ga & Ga2 & Gr & Gr2 & APrk & APra & Gks & Gas & Grs & Gi).

  Definition CL_Kg : list reg := [1; 2; 10; 11; 12; 13; 14; 20; 25]%bv.

  Lemma kg_cell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv R_Kg M0 M -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
    (ri + 164 <= a \/ a + Z.of_nat n <= ri)%Z -> (s - 128 + 16 <= a \/ a + Z.of_nat n <= s - 128)%Z ->
    rdn SEGS M0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs RI Ha Han D1 D2 R. rewrite (rinv_rdn SEGS R_Kg M0 M a n RI Ha Han); [exact R|].
  intros r Hr. unfold R_Kg in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
Qed.

  Lemma kgi_ro_out : forall (lo : Z) (n : nat) (y : Z), store_ok SEGS M0 (Z_to_bv 64 lo) n = true -> (0 <= lo)%Z -> (lo + Z.of_nat n <= 2 ^ 64)%Z ->
    ((0x127b4 <= y < 0x127c0) \/ (0x133a0 <= y < 0x134e8))%Z -> ~ (lo <= y < lo + Z.of_nat n)%Z.
  Proof.
    intros lo n y SOK Hlo Hn Hy Hin.
    assert (Hm : M0 (Z_to_bv 64 y) = None) by (destruct Hy; [apply RO2 | apply RO1]; lia).
    assert (Hw : wview SEGS M0 (Z_to_bv 64 y) <> None).
    { apply (store_ok_all SEGS M0 n (Z_to_bv 64 lo)); rewrite ?u_Z2bv by lia; [lia | exact SOK | lia]. }
    apply Hw. rewrite kgi_wview_ro by (rewrite u_Z2bv by lia; lia). exact Hm.
  Qed.

  Lemma kgi_ro : forall M, rinv R_Kg M0 M ->
    (forall j, (0x133a0 <= j < 0x134e8)%Z -> M (Z_to_bv 64 j) = None) /\ (forall j, (0x127b4 <= j < 0x127c0)%Z -> M (Z_to_bv 64 j) = None).
  Proof.
    intros M RI. geo. destruct RI as [_ RI'].
    assert (OUT : forall j, ((0x127b4 <= j < 0x127c0) \/ (0x133a0 <= j < 0x134e8))%Z -> M (Z_to_bv 64 j) = M0 (Z_to_bv 64 j)).
    { intros j Hj. apply RI'. intros r Hr. unfold R_Kg in Hr. cbn [In] in Hr. unfold inreg. rewrite u_Z2bv by lia.
      destruct Hr as [<-|[<-|[]]]; cbn [fst snd].
      - pose proof (kgi_ro_out ri 164 j SOKr ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hj) as H.
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. lia.
      - pose proof (kgi_ro_out (s - 128) 16 j SOKs ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hj) as H.
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. lia. }
    split; intros j Hj; rewrite OUT by lia; [apply RO1 | apply RO2]; exact Hj.
  Qed.

  Lemma kg_inner : forall (j : nat) fr0 regs0 fr cs regs (M : word -> option byte) (x : Z),
    Z.of_nat j = (41 - x)%Z -> (0 <= x < 41)%Z -> frm_zero cs -> rinv R_Kg M0 M ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 x -> getr regs 25 = Z_to_bv 64 (x - 20) ->
    getr regs 24 = Z_to_bv 64 ((i - 20) * (i - 20)) -> getr regs 18 = Z_to_bv 64 kel -> getr regs 22 = Z_to_bv 64 41 -> getr regs 19 = Z_to_bv 64 i ->
    reg_get fr 8 = nan_box (Z_to_bv 32 FpReal.p_one_s) -> reg_get fr 9 = Z_to_bv 64 ExpfTablesB.DEN_GAUSS_D ->
    regs_agree (fun r => In r CL_Kg) regs0 regs -> (forall r : reg, In (u r) fs_list -> reg_get fr r = reg_get fr0 r) ->
    reach SEGS (@mkst (mkFP fr cs) regs (0x39188 : word) M rom)
      (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x391dc : word) M' rom /\ frm_zero cs' /\ rinv R_Kg M0 M' /\
                  rinv [((ri + 4 * x)%Z, (164 - 4 * x)%Z); ((s - 128)%Z, 16%Z)] M M' /\
                  getr regs' 2 = Z_to_bv 64 (s - 112) /\ regs_agree (fun r => In r CL_Kg) regs0 regs' /\
                  (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr0 r) /\
                  (forall jj, (x <= jj < 41)%Z -> rdn SEGS M' (Z_to_bv 64 (ri + 4 * jj)) 4 =
                     Some (Z_to_le_bytes 4 (ExpfModelB.gauss_cell ExpfTablesB.DEN_GAUSS_D FpReal.p_one_s ((i - 20) * (i - 20) + (jj - 20) * (jj - 20)))))).
  Proof using GEO ALG SOKr SOKs Ch Cw Ca Cr RO1 RO2.
    induction j as [|j IH]; intros fr0 regs0 fr cs regs M x Hj Hx FZ RI E2 E20 E25 E24 E18 E22 E19 F8 F9 AG FS; [lia|].
    geo. destruct ALG as (ALk & ALa & ALr).
    destruct (kgi_ro M RI) as (ROa & ROb).
    assert (Hii : (0 <= (i - 20) * (i - 20))%Z) by apply Z.square_nonneg.
    assert (Hxx : (0 <= (x - 20) * (x - 20))%Z) by apply Z.square_nonneg.
    assert (Hii2 : ((i - 20) * (i - 20) <= 400)%Z) by (assert (- 20 <= i - 20 <= 20)%Z by lia; nia).
    assert (Hxx2 : ((x - 20) * (x - 20) <= 400)%Z) by (assert (- 20 <= x - 20 <= 20)%Z by lia; nia).
    eapply reach_msteps.
    { zv F_39188 D_39188 (Z_to_bv 64 ((x - 20) * (x - 20))).
      stepat F_3918c D_3918c (Z_to_bv 64 ((x - 20) * (x - 20))) ltac:(gres; pin; apply kg_mulw_s; lia).
      stepb_ft F_39190 D_39190 ltac:(apply c_eq_refl).
      stepiwv F_39194 D_39194 (Z_to_bv 64 ((x - 20) * (x - 20))) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
      zv F_39198 D_39198 (Z_to_bv 64 ((i - 20) * (i - 20) + (x - 20) * (x - 20))).
      sn F_3919c D_3919c. fixv (Z_to_bv 64 ((i - 20) * (i - 20) + (x - 20) * (x - 20))) ltac:(gres; pin; apply kgi_addw_s; lia).
      stepb_ft F_391a0 D_391a0 ltac:(apply c_eq_refl).
      fcvt_sw F_391a4 D_391a4 FZ.
      fsgnj F_391a8 D_391a8.
      fcvt_ds F_391ac D_391ac FZ.
      fari F_391b0 D_391b0 FZ.
      fcvt_sd F_391b4 D_391b4 FZ.
      stepj F_391b8 D_391b8.
      apply mst_refl. }
    eapply reach_bind.
    { apply (expf_runV rom _ _ _ (s - 112) (Z_to_bv 64 0x391bc)
               (Z_to_bv 32 (ExpfModelB.gauss_arg ExpfTablesB.DEN_GAUSS_D ((i - 20) * (i - 20) + (x - 20) * (x - 20))))).
      - fz FZ.
      - red; apply bv_eq; reflexivity.
      - gres; reflexivity.
      - gres; pin; reflexivity.
      - cbn [fp_regs]. rewrite fpv_get_same. do 2 f_equal. gres; pin.
        change (fpv_read fr FMT_D 9) with (bv_unsigned (reg_get fr 9)). rewrite F9.
        apply kg_arg. lia.
      - lia.
      - replace (s - 112 - 16)%Z with (s - 128)%Z by lia.
        apply (reg_sok SEGS M0 M (s - 128) 16 (s - 128) 16); [exact (proj1 RI) | exact SOKs | lia | lia | lia | lia].
      - exact ROa.
      - exact ROb. }
    intros fin (fr2 & cs2 & regs2 & M2 & -> & FZ2 & FS2 & XV & AG2 & E2' & RI2).
    assert (RIa : rinv R_Kg M0 M2).
    { eapply rinv_trans; [exact RI|]. eapply rinv_weaken; [exact RI2|].
      intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. exists ((s - 128)%Z, 16%Z). cbn [fst snd]. split; [unfold R_Kg; cbn; tauto | lia]. }
    assert (RIb : rinv [((ri + 4 * x)%Z, (164 - 4 * x)%Z); ((s - 128)%Z, 16%Z)] M M2).
    { eapply rinv_weaken; [exact RI2|].
      intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. exists ((s - 128)%Z, 16%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
    assert (Ch2 : rdn SEGS M2 (Z_to_bv 64 kel) 4 = Some (w4 (Z_to_bv 64 41))) by (apply (kg_cell M2 kel 4 _ RIa); [lia | cbn; lia | cbn; lia | cbn; lia | exact Ch]).
    assert (Cw2 : rdn SEGS M2 (Z_to_bv 64 (kel + 4)) 4 = Some (w4 (Z_to_bv 64 41))) by (apply (kg_cell M2 (kel + 4) 4 _ RIa); [lia | cbn; lia | cbn; lia | cbn; lia | exact Cw]).
    assert (Ca2 : rdn SEGS M2 (Z_to_bv 64 (kel + 16)) 8 = Some (w8 (Z_to_bv 64 arr))) by (apply (kg_cell M2 (kel + 16) 8 _ RIa); [lia | cbn; lia | cbn; lia | cbn; lia | exact Ca]).
    assert (Cr2 : rdn SEGS M2 (Z_to_bv 64 (arr + 8 * i)) 8 = Some (w8 (Z_to_bv 64 ri))) by (apply (kg_cell M2 (arr + 8 * i) 8 _ RIa); [lia | cbn; lia | cbn; lia | cbn; lia | exact Cr]).
    rewrite w2b4_Z in Ch2, Cw2 by lia. rewrite (w2b_Z 8 arr) in Ca2 by lia. rewrite (w2b_Z 8 ri) in Cr2 by lia.
    assert (SOK2 : store_ok SEGS M2 (Z_to_bv 64 (ri + 4 * x)) 4 = true)
      by (apply (reg_sok SEGS M0 M2 ri 164 (ri + 4 * x) 4); [exact (proj1 RIa) | exact SOKr | lia | cbn; lia | lia | cbn; lia]).
    assert (G18 : getr regs2 18 = Z_to_bv 64 kel) by (rewrite (AG2 18) by notin_list; gres; pin; reflexivity).
    assert (G19 : getr regs2 19 = Z_to_bv 64 i) by (rewrite (AG2 19) by notin_list; gres; pin; reflexivity).
    assert (G20 : getr regs2 20 = Z_to_bv 64 x) by (rewrite (AG2 20) by notin_list; gres; pin; reflexivity).
    assert (G22 : getr regs2 22 = Z_to_bv 64 41) by (rewrite (AG2 22) by notin_list; gres; pin; reflexivity).
    assert (G24 : getr regs2 24 = Z_to_bv 64 ((i - 20) * (i - 20))) by (rewrite (AG2 24) by notin_list; gres; pin; reflexivity).
    assert (G25 : getr regs2 25 = Z_to_bv 64 (x - 20)) by (rewrite (AG2 25) by notin_list; gres; pin; reflexivity).
    assert (F8' : reg_get fr2 8 = nan_box (Z_to_bv 32 FpReal.p_one_s)).
    { rewrite FS2 by (unfold fs_list; in_list). cbn [fp_regs]. rewrite !fpv_get_other by reg_neq_tac. exact F8. }
    assert (F9' : reg_get fr2 9 = Z_to_bv 64 ExpfTablesB.DEN_GAUSS_D).
    { rewrite FS2 by (unfold fs_list; in_list). cbn [fp_regs]. rewrite !fpv_get_other by reg_neq_tac. exact F9. }
    replace (Z_to_bv 64 0x391bc) with (0x391bc : word) by (apply bv_eq; reflexivity).
    eapply reach_msteps.
    { fari F_391bc D_391bc FZ2.
      sn F_391c0 D_391c0. sn F_391c4 D_391c4. sn F_391c8 D_391c8.
      stepj F_391cc D_391cc.
      apply mst_refl. }
    match goal with |- reach _ (@mkst ?FX ?R _ _ _) _ =>
      set (R3 := R);
      destruct (@kse_ok FX rom R3 M2 kel 41 41 arr ri i x (0x391d0 : word) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALk ALa ALr Ch2 Cw2 Ca2 Cr2 SOK2
                  ltac:(subst R3; gres; bveq) ltac:(red; apply bv_eq; reflexivity)
                  ltac:(subst R3; gres; pin; reflexivity) ltac:(subst R3; gres; pin; reflexivity) ltac:(subst R3; gres; pin; reflexivity))
        as (regs4 & RUN4 & E2k & E10k & AG4)
    end.
    eapply reach_msteps; [exact RUN4|].
    set (M4 := wbytes M2 _ _).
    assert (RI4 : rinv R_Kg M0 M4).
    { subst M4. apply (rinv_wbytes R_Kg M0 M2 (ri + 4 * x) 4); [exact RIa | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |].
      exists (ri, 164%Z). cbn [fst snd]. split; [unfold R_Kg; cbn; tauto | lia]. }
    assert (RIb4 : rinv [((ri + 4 * x)%Z, (164 - 4 * x)%Z); ((s - 128)%Z, 16%Z)] M M4).
    { subst M4. apply (rinv_wbytes _ M M2 (ri + 4 * x) 4); [exact RIb | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |].
      exists ((ri + 4 * x)%Z, (164 - 4 * x)%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
    assert (VAL4 : rdn SEGS M4 (Z_to_bv 64 (ri + 4 * x)) 4 =
                   Some (Z_to_le_bytes 4 (ExpfModelB.gauss_cell ExpfTablesB.DEN_GAUSS_D FpReal.p_one_s ((i - 20) * (i - 20) + (x - 20) * (x - 20))))).
    { subst M4. rewrite kgi_rdn_hit by lia. do 2 f_equal. cbn [fp_regs]. rewrite fpv_get_same.
      change (fpv_read fr2 FMT_S 8) with (bv_unsigned (unbox_s (reg_get fr2 8))).
      change (fpv_read fr2 FMT_S 10) with (bv_unsigned (unbox_s (reg_get fr2 10))).
      rewrite F8', XV. apply kg_cellv. }
    assert (K2 : getr regs4 2 = Z_to_bv 64 (s - 112)) by (rewrite (AG4 2) by notin_list; subst R3; gres; exact E2').
    assert (K18 : getr regs4 18 = Z_to_bv 64 kel) by (rewrite (AG4 18) by notin_list; subst R3; gres; exact G18).
    assert (K19 : getr regs4 19 = Z_to_bv 64 i) by (rewrite (AG4 19) by notin_list; subst R3; gres; exact G19).
    assert (K20 : getr regs4 20 = Z_to_bv 64 x) by (rewrite (AG4 20) by notin_list; subst R3; gres; exact G20).
    assert (K22 : getr regs4 22 = Z_to_bv 64 41) by (rewrite (AG4 22) by notin_list; subst R3; gres; exact G22).
    assert (K24 : getr regs4 24 = Z_to_bv 64 ((i - 20) * (i - 20))) by (rewrite (AG4 24) by notin_list; subst R3; gres; exact G24).
    assert (K25 : getr regs4 25 = Z_to_bv 64 (x - 20)) by (rewrite (AG4 25) by notin_list; subst R3; gres; exact G25).
    assert (AGr : regs_agree (fun r => In r CL_Kg) regs0 regs4) by (unfold CL_Kg in AG |- *; subst R3; ra_chain).
    assert (FSr : forall v r, In (u r) fs_list -> reg_get (bvmap_set (10 : reg) v fr2) r = reg_get fr0 r).
    { intros v r Hr.
      assert (N10 : r <> (10 : reg)) by (let EQ := fresh in intros EQ; subst r; vm_compute in Hr; intuition discriminate).
      assert (N15 : r <> (15 : reg)) by (let EQ := fresh in intros EQ; subst r; vm_compute in Hr; intuition discriminate).
      rewrite fpv_get_other by exact N10. rewrite FS2 by exact Hr. cbn [fp_regs].
      rewrite !fpv_get_other by assumption. exact (FS r Hr). }
    destruct j as [|j].
    - assert (Ex : x = 40%Z) by lia.
      eapply reach_msteps.
      { stepiwv F_391d0 D_391d0 (Z_to_bv 64 (x + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepiwv F_391d4 D_391d4 (Z_to_bv 64 (x + 1 - 20)) ltac:(gres; pin; imm_norm; rewrite kgi_addiw_s by lia; f_equal; lia).
        stepb_ft F_391d8 D_391d8 ltac:(condZ).
        apply mst_refl. }
      apply reach_done. do 4 eexists. split; [reflexivity|].
      split; [repeat apply fpv_frm_acc; exact FZ2|]. split; [exact RI4|]. split; [exact RIb4|]. split; [gres; exact K2|].
      split; [unfold CL_Kg in AGr |- *; repeat (apply regs_agree_upd; [in_list|]); exact AGr|].
      split; [intros r Hr; apply FSr; exact Hr|].
      intros jj Hjj. assert (jj = x) as -> by lia. exact VAL4.
    - eapply reach_msteps.
      { stepiwv F_391d0 D_391d0 (Z_to_bv 64 (x + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
        stepiwv F_391d4 D_391d4 (Z_to_bv 64 (x + 1 - 20)) ltac:(gres; pin; imm_norm; rewrite kgi_addiw_s by lia; f_equal; lia).
        stepb_tk F_391d8 D_391d8 ltac:(condZ).
        apply mst_refl. }
      eapply reach_weaken; [| eapply (IH fr0 regs0 _ _ _ M4 (x + 1)%Z ltac:(lia) ltac:(lia))].
      + intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI' & RIx & E2f & AGf & FSf & VALf).
        exists fr', cs', regs', M'. split; [reflexivity|]. split; [exact FZ'|]. split; [exact RI'|].
        split.
        { eapply rinv_trans; [exact RIb4|]. eapply rinv_weaken; [exact RIx|].
          intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]].
          - exists ((ri + 4 * x)%Z, (164 - 4 * x)%Z). cbn [fst snd]. split; [cbn; tauto | lia].
          - exists ((s - 128)%Z, 16%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
        split; [exact E2f|]. split; [exact AGf|]. split; [exact FSf|].
        intros jj Hjj. destruct (Z.eq_dec jj x) as [->|Hne].
        * rewrite (rinv_rdn SEGS _ M4 M' (ri + 4 * x) 4 RIx); [exact VAL4 | lia | cbn; lia |].
          intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
        * apply VALf. lia.
      + repeat apply fpv_frm_acc; exact FZ2.
      + exact RI4.
      + gres; exact K2.
      + gres; reflexivity.
      + gres; reflexivity.
      + gres; exact K24.
      + gres; exact K18.
      + gres; exact K22.
      + gres; exact K19.
      + rewrite fpv_get_other by reg_neq_tac. exact F8'.
      + rewrite fpv_get_other by reg_neq_tac. exact F9'.
      + unfold CL_Kg in AGr |- *. repeat (apply regs_agree_upd; [in_list|]). exact AGr.
      + intros r Hr; apply FSr; exact Hr.
  Qed.
  End KgL.

End Segs.
End KgauSegs.
