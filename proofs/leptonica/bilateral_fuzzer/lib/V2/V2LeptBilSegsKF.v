(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV FPStepsB Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib DitherLoop LeptExec LeptExecX LeptExecFP LeptExecB LeptFPB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpReal FpSiteB FpSiteC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBilSegs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_bilateralCreate.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require SeqExec.
From stdpp.bitvector Require Import tactics.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.


Section BilSegsKF.
Variable rom : word -> option byte.

Definition kf_x (v : Z) : Z := fst (fp_of_int fmt_single RNE true 32 v).
Definition kf_d (a b : Z) : Z := fst (fp_sub fmt_single RNE (kf_x b) (kf_x a)).

Lemma kf_xr : forall v, (0 <= v <= 255)%Z -> bc_int (kf_x v) v /\ (0 <= kf_x v < 2 ^ 32)%Z.
Proof. intros v Hv. exact (bc_int_of RNE v Hv). Qed.

Lemma kf_cvt : forall v, (0 <= v < 2 ^ 64)%Z -> fst (fp_of_int (fp_format FMT_S) RNE true 32 (bv_unsigned (Z_to_bv 64 v))) = kf_x v.
Proof. intros v Hv. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma kf_rdx : forall (fr : bvmap 5 word) (r : reg) (v : Z), reg_get fr r = nan_box (Z_to_bv 32 v) -> (0 <= v < 2 ^ 32)%Z ->
  fpv_read fr FMT_S r = v.
Proof. intros fr r v H Hv. unfold fpv_read. rewrite H, fpv_unbox_box. apply fp_u_Z2bv32. exact Hv. Qed.

Lemma kf_lt : forall a b, (0 <= a <= 255)%Z -> (0 <= b <= 255)%Z -> fst (fpv_cmp F_LT FMT_S (kf_x a) (kf_x b)) = (a <? b)%Z.
Proof.
  intros a b Ha Hb. destruct (kf_xr a Ha) as (IA & _). destruct (kf_xr b Hb) as (IB & _).
  exact (bc_int_lt (kf_x a) (kf_x b) a b IA IB).
Qed.

Lemma kf_dr : forall a b, (0 <= a < b)%Z -> (b <= 255)%Z -> (0 <= kf_d a b < 2 ^ 32)%Z.
Proof.
  intros a b Hab Hb. destruct (kf_xr a ltac:(lia)) as (IA & _). destruct (kf_xr b ltac:(lia)) as (IB & _).
  destruct (bc_kfract_full (kf_x a) (kf_x a) (kf_x b) a a b IA IA IB ltac:(lia) Hb) as (_ & D & _). exact D.
Qed.

Lemma kf_cval : forall a b i, (0 <= a <= i)%Z -> (i < b <= 255)%Z ->
  kfr_le1 (fst (fpv_ari F_DIV FMT_S RNE (bv_unsigned (Z_to_bv 32 (fst (fpv_ari F_SUB FMT_S RNE (kf_x i) (kf_x a))))) (kf_d a b))) /\
  (0 <= fst (fpv_ari F_DIV FMT_S RNE (bv_unsigned (Z_to_bv 32 (fst (fpv_ari F_SUB FMT_S RNE (kf_x i) (kf_x a))))) (kf_d a b)) < 2 ^ 32)%Z.
Proof.
  intros a b i Ha Hb. destruct (kf_xr a ltac:(lia)) as (IA & _). destruct (kf_xr b ltac:(lia)) as (IB & _).
  destruct (kf_xr i ltac:(lia)) as (II & _).
  destruct (bc_kfract_full (kf_x i) (kf_x a) (kf_x b) i a b II IA IB ltac:(lia) ltac:(lia)) as (L & _ & E & C).
  unfold fpv_ari. cbn [fp_format]. rewrite fp_u_Z2bv32 by exact E. unfold kf_d. split; [exact L | exact C].
Qed.

Lemma kf_rdn_hit : forall (M : word -> option byte) (a z : Z), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z ->
  rdn SEGS (wbytes M (Z_to_bv 64 a) (Z_to_le_bytes 4 z)) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 z).
Proof.
  intros M a z Ha Ha4. pose proof (SeqExec.rdn_wbytes_hit SEGS (Z_to_le_bytes 4 z) M (Z_to_bv 64 a)) as H.
  rewrite length_Z_to_le_bytes in H. apply H. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Lemma kf_mod4 : forall z, (z mod 16 = 0)%Z -> (z mod 4 = 0)%Z.
Proof.
  intros z H. rewrite (Z.div_mod z 16) by lia. rewrite H, Z.add_0_r.
  replace (16 * (z / 16))%Z with ((4 * (z / 16)) * 4)%Z by ring. apply Z.mod_mul. lia.
Qed.

Ltac kf_rne := let H := fresh "H" in intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.
Ltac kf_fpn := cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_unbox_box | rewrite fpv_read_other by kf_rne
               | rewrite fpv_get_same | rewrite fpv_get_other by kf_rne ].
Ltac kf_fz Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.
Ltac kf_fcvt F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F | reflexivity | exact D | left; split; reflexivity
  | left; repeat split; reflexivity | kf_fz Hz | reflexivity] | step_simpl ]; kf_fpn.
Ltac kf_fari F D Hz := chain_step; [ reflexivity | eapply fpv_step_fari; [exact F | reflexivity | exact D | kf_fz Hz | reflexivity] | step_simpl ]; kf_fpn.
Ltac kf_fcmp F D := chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F | reflexivity | exact D] | step_simpl ]; kf_fpn.
Ltac kf_fsw F D adr SOK := chain_step; [ reflexivity | eapply fp_step_fsw with (a := adr); [exact F | reflexivity | exact D | gres; pin; imm_norm; rewrite ?zbv_addi; first [reflexivity | f_equal; lia] | exact SOK] | step_simpl ].
Ltac kf_pc p := lazymatch goal with |- reach _ (@mkst _ _ ?q _ _) _ => replace q with p by (apply bv_eq; reflexivity) end.
Ltac kf_zand F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).
Ltac kf_lit F D v := stepat F D v ltac:(gres; pin; imm_norm; first [reflexivity | (apply bv_eq; vm_compute; reflexivity)]).
Ltac kf_lw F D a z R := stepLD F D (Z_to_le_bytes 4 z) (Z_to_bv 64 z) ltac:(rdn_addr a; exact R) ltac:(apply lez4; lia); rewrite (v_lw_small z) by lia.
Ltac kf_ld F D a z R := stepLD F D (Z_to_le_bytes 8 z) (Z_to_bv 64 z) ltac:(rdn_addr a; exact R) ltac:(apply lez8; lia).

Ltac kf_cond := first [ condZ | reflexivity | (vm_compute; reflexivity) ].
Ltac kf_frv := cbn [fp_regs]; repeat first [ rewrite fpv_get_same | rewrite fpv_get_other by kf_rne ]; reflexivity.
Ltac kf_rg := gres; pin; first [ reflexivity | f_equal; lia ].

Lemma kf_fsnot : forall r : reg, ~ In (ridx r) [12; 13; 14; 15]%nat -> r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv.
Proof. intros r H. repeat split; intro E; subst r; apply H; vm_compute; repeat first [left; reflexivity | right]. Qed.

Definition KF_L : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%bv.

Section KfL.
Variables (s nc kf minv maxv : Z) (m0 : word -> option byte).
Hypothesis GEO : (4096 + 320 <= s <= 2 ^ 47 /\ 4096 <= nc /\ nc + 40 <= s - 320 /\ 4096 <= kf /\ kf + 1024 <= s - 320 /\
                  (kf + 1024 <= nc \/ nc + 40 <= kf))%Z.
Hypothesis MNV : (0 <= minv <= 255 /\ 0 <= maxv <= 255)%Z.
Hypothesis Rncn : rdn SEGS m0 (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)).
Hypothesis Rnc : rdn SEGS m0 (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc).
Hypothesis NCV : forall j, (0 <= j < 10)%Z -> rdn SEGS m0 (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j)).
Hypothesis SOK0 : store_ok SEGS m0 (Z_to_bv 64 kf) 1024 = true.

Lemma kf_keep : forall M (a : Z) (n : nat), rinv [(kf, 1024%Z)] m0 M -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (a + Z.of_nat n <= kf \/ kf + 1024 <= a)%Z -> rdn SEGS M (Z_to_bv 64 a) n = rdn SEGS m0 (Z_to_bv 64 a) n.
Proof.
  intros M a n RI Ha Han D. apply (rinv_rdn SEGS _ m0 M a n RI Ha Han).
  intros r Hr. cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd]. lia.
Qed.

Lemma kf_sok : forall M i, rinv [(kf, 1024%Z)] m0 M -> (0 <= i < 256)%Z -> store_ok SEGS M (Z_to_bv 64 (kf + 4 * i)) 4 = true.
Proof.
  intros M i RI Hi. pose proof GEO as (Gs & Gn & Gn2 & Gk & Gk2 & D).
  apply (reg_sok SEGS m0 M kf 1024 (kf + 4 * i) 4); [exact (proj1 RI) | exact SOK0 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                    | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.

Lemma kf_store : forall M (i x : Z), rinv [(kf, 1024%Z)] m0 M -> kfr_ok kf M -> (0 <= i < 256)%Z -> kfr_le1 x ->
  rinv [(kf, 1024%Z)] m0 (wbytes M (Z_to_bv 64 (kf + 4 * i)) (Z_to_le_bytes 4 x)) /\
  kfr_ok kf (wbytes M (Z_to_bv 64 (kf + 4 * i)) (Z_to_le_bytes 4 x)).
Proof.
  intros M i x RI OK Hi LE. pose proof GEO as (Gs & Gn & Gn2 & Gk & Gk2 & D).
  split.
  - apply (rinv_wbytes _ m0 M (kf + 4 * i) 4); [exact RI | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |].
    exists (kf, 1024%Z). cbn [fst snd]. split; [cbn; tauto | lia].
  - intros v Hv. destruct (Z.eq_dec v i) as [-> | N].
    + exists x. split; [apply kf_rdn_hit; lia | exact LE].
    + destruct (OK v Hv) as (y & Ry & Ly). exists y. split; [| exact Ly].
      rewrite rdn_wbytes_out_Z; [exact Ry |]. rewrite length_Z_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Lemma kf_inner : forall (n : nat) (fr : bvmap 5 word) cs regs (M : word -> option byte) (a b i : Z),
  Z.of_nat n = (b - i)%Z -> (0 <= a <= i)%Z -> (i < b <= 255)%Z -> frm_zero cs ->
  rinv [(kf, 1024%Z)] m0 M -> kfr_ok kf M ->
  getr regs 10 = Z_to_bv 64 kf -> getr regs 12 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 i -> getr regs 5 = Z_to_bv 64 i ->
  getr regs 16 = Z_to_bv 64 (kf + 4 * i) -> getr regs 17 = Z_to_bv 64 (kf + 4 * i) ->
  reg_get fr 12 = nan_box (Z_to_bv 32 (kf_d a b)) -> reg_get fr 13 = nan_box (Z_to_bv 32 (kf_x a)) ->
  reg_get fr 14 = nan_box (Z_to_bv 32 (kf_x i)) -> reg_get fr 15 = nan_box (Z_to_bv 32 (kf_x b)) ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x39d38 : word) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x39d8c : word) M' rom /\ frm_zero cs' /\
       rinv [(kf, 1024%Z)] m0 M' /\ kfr_ok kf M' /\ getr regs' 13 = Z_to_bv 64 b /\
       regs_agree (fun r => In r [5; 6; 7; 13; 16; 17]%list) regs regs' /\
       (forall r : reg, r <> 14%bv -> reg_get fr' r = reg_get fr r)).
Proof using All.
  intros n. induction n as [|n IH]; intros fr cs regs M a b i Hn Ha Hb FZ RI OK E10 E12 E14 E13 E5 E16 E17 F12 F13 F14 F15; [lia |].
  pose proof GEO as (Gs & Gn & Gn2 & Gk & Gk2 & DK).
  destruct (kf_xr i ltac:(lia)) as (_ & Xi). destruct (kf_xr a ltac:(lia)) as (_ & Xa).
  destruct (kf_xr b ltac:(lia)) as (_ & Xb). destruct (kf_xr (i + 1) ltac:(lia)) as (_ & Xi1).
  assert (R14 : fpv_read fr FMT_S 14 = kf_x i) by (apply kf_rdx; [exact F14 | exact Xi]).
  assert (R13 : fpv_read fr FMT_S 13 = kf_x a) by (apply kf_rdx; [exact F13 | exact Xa]).
  assert (R12 : fpv_read fr FMT_S 12 = kf_d a b) by (apply kf_rdx; [exact F12 | apply kf_dr; lia]).
  assert (R15 : fpv_read fr FMT_S 15 = kf_x b) by (apply kf_rdx; [exact F15 | exact Xb]).
  destruct (kf_cval a b i ltac:(lia) ltac:(lia)) as (CL & CR).
  pose proof (kf_sok M i RI ltac:(lia)) as SOK.
  eapply reach_msteps.
  { stepat F_39d38 D_39d38 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
    stepb_ft F_39d3c D_39d3c ltac:(condZ).
    stepat F_39d40 D_39d40 (Z_to_bv 64 0)
      ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite (proj2 (Z.ltb_ge (kf + 4 * i) kf)) by lia; reflexivity).
    stepat F_39d44 D_39d44 (Z_to_bv 64 0)
      ltac:(gres; pin; imm_norm; rewrite v_slti_Z by lia; rewrite (proj2 (Z.ltb_ge i 0)) by lia; reflexivity).
    kf_lit F_39d48 D_39d48 (Z_to_bv 64 0).
    kf_lit F_39d4c D_39d4c (Z_to_bv 64 1).
    stepb_ft F_39d50 D_39d50 ltac:(condZ).
    stepb_ft F_39d54 D_39d54 ltac:(condZ).
    kf_fari F_39d58 D_39d58 FZ. rewrite R14, R13.
    kf_fari F_39d5c D_39d5c FZ. rewrite R12.
    stepat F_39d60 D_39d60 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
    kf_fsw F_39d64 D_39d64 (Z_to_bv 64 (kf + 4 * i)) SOK.
    kf_fpn. rewrite fpv_low32_box, (fp_u_Z2bv32 _ CR).
    stepb_ft F_39d68 D_39d68 ltac:(condZ).
    kf_fcvt F_39d6c D_39d6c FZ. gres. rewrite (kf_cvt (i + 1)) by lia.
    zv F_39d70 D_39d70 (Z_to_bv 64 (i + 1)).
    kf_fcmp F_39d74 D_39d74. rewrite (fp_u_Z2bv32 _ Xi1), R15, (kf_lt (i + 1) b) by lia.
    zv F_39d78 D_39d78 (Z_to_bv 64 (kf + 4 * (i + 1))).
    zv F_39d7c D_39d7c (Z_to_bv 64 (kf + 4 * (i + 1))).
    zv F_39d80 D_39d80 (Z_to_bv 64 (i + 1)).
    apply mst_refl. }
  destruct (kf_store M i _ RI OK ltac:(lia) CL) as (RI' & OK').
  destruct (Z.ltb_spec (i + 1) b) as [LT | GE].
  - eapply reach_msteps.
    { stepb_tk F_39d84 D_39d84 ltac:(first [reflexivity | vm_compute; reflexivity]). apply mst_refl. }
    kf_pc (0x39d38 : word).
    eapply reach_weaken; [| eapply (IH _ _ _ _ a b (i + 1)%Z ltac:(lia) ltac:(lia) ltac:(lia))].
    + intros fin (fr2 & cs2 & regs2 & M2 & -> & FZ2 & RI2 & OK2 & G13 & AG2 & FS2).
      exists fr2, cs2, regs2, M2. split; [reflexivity |].
      split; [exact FZ2 |]. split; [exact RI2 |]. split; [exact OK2 |]. split; [exact G13 |].
      split.
      * eapply regs_agree_trans; [| exact AG2]. solve_regs_agree.
      * intros r Hr. rewrite (FS2 r Hr). rewrite !fpv_get_other by exact Hr. reflexivity.
    + kf_fz FZ.
    + exact RI'.
    + exact OK'.
    + gres; pin; first [reflexivity | f_equal; lia].
    + gres; pin; first [reflexivity | f_equal; lia].
    + gres; pin; first [reflexivity | f_equal; lia].
    + gres; pin; first [reflexivity | f_equal; lia].
    + gres; pin; first [reflexivity | f_equal; lia].
    + gres; pin; first [reflexivity | f_equal; lia].
    + gres; pin; first [reflexivity | f_equal; lia].
    + rewrite !fpv_get_other by kf_rne. exact F12.
    + rewrite !fpv_get_other by kf_rne. exact F13.
    + apply fpv_get_same.
    + rewrite !fpv_get_other by kf_rne. exact F15.
  - eapply reach_msteps.
    { stepb_ft F_39d84 D_39d84 ltac:(first [reflexivity | vm_compute; reflexivity]).
      zv F_39d88 D_39d88 (Z_to_bv 64 (i + 1)).
      apply mst_refl. }
    kf_pc (0x39d8c : word).
    apply reach_done. do 4 eexists. split; [reflexivity |].
    split; [kf_fz FZ |]. split; [exact RI' |]. split; [exact OK' |].
    split; [gres; f_equal; lia |].
    split; [solve_regs_agree |].
    intros r Hr. rewrite !fpv_get_other by exact Hr. reflexivity.
Qed.

Lemma kf_outer : forall (n : nat) (fr : bvmap 5 word) cs regs (M : word -> option byte) (k i : Z),
  Z.of_nat n = (9 - k)%Z -> (0 <= k <= 8)%Z -> (nc_val minv maxv k <= i <= maxv)%Z -> frm_zero cs ->
  rinv [(kf, 1024%Z)] m0 M -> kfr_ok kf M ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 9 -> getr regs 10 = Z_to_bv 64 kf ->
  getr regs 11 = Z_to_bv 64 maxv -> getr regs 12 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 ->
  getr regs 13 = Z_to_bv 64 i -> getr regs 16 = Z_to_bv 64 k -> getr regs 28 = Z_to_bv 64 11 ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x39ce8 : word) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39d98) M' rom /\ frm_zero cs' /\
       rinv [(kf, 1024%Z)] m0 M' /\ kfr_ok kf M' /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 kf /\ getr regs' 11 = Z_to_bv 64 maxv /\
       getr regs' 28 = Z_to_bv 64 11 /\ getr regs' 8 = Z_to_bv 64 9 /\
       regs_agree (fun r => In r KF_L) regs regs' /\
       (forall r : reg, ~ In (ridx r) [12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof using All.
  induction n as [|n IH]; intros fr cs regs M k i Hn Hk Hi FZ RI OK E2 E8 E10 E11 E12 E14 E13 E16 E28; [lia |].
  pose proof GEO as (Gs & Gn & Gn2 & Gk & Gk2 & Dkn). pose proof MNV as (Hmin & Hmax).
  pose proof (nc_val_rng minv maxv k Hmin Hmax ltac:(lia)) as NA.
  pose proof (nc_val_rng minv maxv (k + 1) Hmin Hmax ltac:(lia)) as NB.
  assert (Rncn' : rdn SEGS M (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)))
    by (rewrite (kf_keep M (s - 256) 8 RI) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rncn).
  assert (Rnc' : rdn SEGS M (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc))
    by (rewrite (kf_keep M (s - 248) 8 RI) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rnc).
  assert (RB : rdn SEGS M (Z_to_bv 64 (nc + 4 * (k + 1))) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv (k + 1))))
    by (rewrite (kf_keep M (nc + 4 * (k + 1)) 4 RI) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); apply NCV; lia).
  assert (RA : rdn SEGS M (Z_to_bv 64 (nc + 4 * k)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv k)))
    by (rewrite (kf_keep M (nc + 4 * k) 4 RI) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); apply NCV; lia).
  set (a := nc_val minv maxv k) in *. set (b := nc_val minv maxv (k + 1)) in *.
  destruct (kf_xr i ltac:(lia)) as (_ & Xi). destruct (kf_xr a ltac:(lia)) as (_ & Xa).
  destruct (kf_xr b ltac:(lia)) as (_ & Xb).
  match goal with |- reach _ _ ?P =>
    assert (LATCH : forall fr' cs' regs' M' i', frm_zero cs' -> rinv [(kf, 1024%Z)] m0 M' -> kfr_ok kf M' ->
       (b <= i' <= 255)%Z ->
       getr regs' 2 = Z_to_bv 64 (s - 320) -> getr regs' 8 = Z_to_bv 64 9 -> getr regs' 10 = Z_to_bv 64 kf ->
       getr regs' 11 = Z_to_bv 64 maxv -> getr regs' 12 = Z_to_bv 64 1 -> getr regs' 14 = Z_to_bv 64 1 ->
       getr regs' 13 = Z_to_bv 64 i' -> getr regs' 15 = Z_to_bv 64 (k + 1) -> getr regs' 28 = Z_to_bv 64 11 ->
       regs_agree (fun r => In r KF_L) regs regs' ->
       (forall r : reg, ~ In (ridx r) [12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r) ->
       reach SEGS (@mkst (mkFP fr' cs') regs' (0x39d8c : word) M' rom) P)
  end.
  { intros fr' cs' regs' M' i' FZ' RI' OK' Hi' G2 G8 G10 G11 G12 G14 G13 G15 G28 AG FS.
    destruct (Z_lt_ge_dec maxv i') as [EX | CO].
    - eapply reach_msteps. { stepb_tk F_39d8c D_39d8c ltac:(condZ). apply mst_refl. }
      kf_pc (Z_to_bv 64 0x39d98). apply reach_done. do 4 eexists. split; [reflexivity |].
      do 8 (split; [assumption |]). split; [exact AG | exact FS].
    - eapply reach_msteps.
      { stepb_ft F_39d8c D_39d8c ltac:(condZ). zv F_39d90 D_39d90 (Z_to_bv 64 (k + 1)). apply mst_refl. }
      destruct (Z.eq_dec k 8%Z) as [K8 | K8].
      + eapply reach_msteps. { stepb_ft F_39d94 D_39d94 ltac:(condZ). apply mst_refl. }
        kf_pc (Z_to_bv 64 0x39d98). apply reach_done. do 4 eexists. split; [reflexivity |].
        do 3 (split; [assumption |]). do 5 (split; [kf_rg |]).
        split; [unfold KF_L in AG |- *; ra_chain | exact FS].
      + eapply reach_msteps. { stepb_tk F_39d94 D_39d94 ltac:(condZ). apply mst_refl. }
        kf_pc (0x39ce8 : word).
        eapply reach_weaken; cycle 1.
        { apply (IH fr' cs' _ M' (k + 1)%Z i' ltac:(lia) ltac:(lia) ltac:(lia) FZ' RI' OK'); kf_rg. }
        intros fin (fr'' & cs'' & regs'' & M'' & -> & FZ'' & RI'' & OK'' & H2' & H10' & H11' & H28' & H8' & AG' & FS').
        do 4 eexists. split; [reflexivity |]. do 8 (split; [assumption |]).
        split; [unfold KF_L in AG, AG' |- *; ra_chain |].
        intros r Hr. rewrite (FS' r Hr). exact (FS r Hr). }
  eapply reach_msteps.
  { zv F_39ce8 D_39ce8 (Z_to_bv 64 (k + 1)).
    stepiv F_39cec D_39cec (Z_to_bv 64 (4 * (k + 1))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
    kf_ld F_39cf0 D_39cf0 (s - 256)%Z (2 ^ 64 - 1 - nc)%Z Rncn'.
    stepb_ft F_39cf4 D_39cf4 ltac:(condZ).
    kf_ld F_39cf8 D_39cf8 (s - 248)%Z nc Rnc'.
    zv F_39cfc D_39cfc (Z_to_bv 64 (nc + 4 * (k + 1))).
    kf_lw F_39d00 D_39d00 (nc + 4 * (k + 1))%Z b RB.
    kf_fcvt F_39d04 D_39d04 FZ. gres. rewrite (kf_cvt b) by lia.
    kf_fcvt F_39d08 D_39d08 FZ. gres. rewrite E13, (kf_cvt i) by lia.
    kf_fcmp F_39d0c D_39d0c. rewrite (fp_u_Z2bv32 _ Xi), (fp_u_Z2bv32 _ Xb), (kf_lt i b) by lia.
    apply mst_refl. }
  destruct (Z.ltb_spec i b) as [ILT | IGE].
  - eapply reach_msteps.
    { stepb_ft F_39d10 D_39d10 ltac:(kf_cond).
      stepiv F_39d14 D_39d14 (Z_to_bv 64 (4 * k)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_39d18 D_39d18 (Z_to_bv 64 (nc + 4 * k)).
      kf_lw F_39d1c D_39d1c (nc + 4 * k)%Z a RA.
      stepiv F_39d20 D_39d20 (Z_to_bv 64 (4 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      kf_fcvt F_39d24 D_39d24 FZ. gres. rewrite (kf_cvt a) by lia.
      zv F_39d28 D_39d28 (Z_to_bv 64 (kf + 4 * i)).
      kf_fari F_39d2c D_39d2c FZ. rewrite (fp_u_Z2bv32 _ Xb), (fp_u_Z2bv32 _ Xa).
      change (fst (fpv_ari F_SUB FMT_S RNE (kf_x b) (kf_x a))) with (kf_d a b).
      zv F_39d30 D_39d30 (Z_to_bv 64 (kf + 4 * i)).
      zv F_39d34 D_39d34 (Z_to_bv 64 i).
      apply mst_refl. }
    eapply reach_bind.
    { eapply (kf_inner (Z.to_nat (b - i)) _ _ _ M a b i ltac:(rewrite Z2Nat.id by lia; reflexivity) ltac:(lia) ltac:(lia)
               _ RI OK);
      lazymatch goal with |- reg_get _ _ = _ => kf_frv | |- getr _ _ = _ => kf_rg | |- frm_zero _ => kf_fz FZ end. }
    intros fin (fr2 & cs2 & regs2 & M2 & -> & FZ2 & RI2 & OK2 & G13 & AG2 & FS2).
    apply (LATCH fr2 cs2 regs2 M2 b FZ2 RI2 OK2 ltac:(lia)); try exact G13;
      try (rewrite (AG2 _) by notin_list; kf_rg).
    + unfold KF_L. ra_chain.
    + intros r Hr. destruct (kf_fsnot r Hr) as (N12 & N13 & N14 & N15).
      rewrite (FS2 r N14). cbn [fp_regs]. rewrite !fpv_get_other by assumption. reflexivity.
  - eapply reach_msteps. { stepb_tk F_39d10 D_39d10 ltac:(kf_cond). apply mst_refl. }
    eapply (LATCH _ _ _ M i _ RI OK ltac:(lia));
      try lazymatch goal with |- getr _ _ = _ => kf_rg | |- frm_zero _ => kf_fz FZ end.
    + unfold KF_L. solve_regs_agree.
    + intros r Hr. destruct (kf_fsnot r Hr) as (N12 & N13 & N14 & N15).
      cbn [fp_regs]. rewrite !fpv_get_other by assumption. reflexivity.
  Unshelve.
  all: kf_fz FZ.
Qed.

End KfL.

Lemma kfr_seg : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s nc kf minv maxv : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= nc)%Z -> (nc + 40 <= s - 320)%Z ->
  (4096 <= kf)%Z -> (kf + 1024 <= s - 320)%Z -> (kf mod 16 = 0)%Z ->
  (kf + 1024 <= nc \/ nc + 40 <= kf)%Z ->
  (0 <= minv <= 255)%Z -> (0 <= maxv <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  rdn SEGS m (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) ->
  rdn SEGS m (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)) ->
  rdn SEGS m (Z_to_bv 64 (s - 272)) 8 = Some (Z_to_le_bytes 8 11) ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS m (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) ->
  store_ok SEGS m (Z_to_bv 64 kf) 1024 = true ->
  kfr_ok kf m ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 10 = Z_to_bv 64 kf -> getr regs 8 = Z_to_bv 64 9 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39c28) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39d98) M' rom /\ frm_zero cs' /\
      rinv [(kf, 1024%Z)] m M' /\ kfr_ok kf M' /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 kf /\ getr regs' 11 = Z_to_bv 64 maxv /\
      getr regs' 28 = Z_to_bv 64 11 /\ getr regs' 8 = Z_to_bv 64 9 /\
      regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%list) regs regs' /\
      (forall r : reg, ~ In (ridx r) [12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s nc kf minv maxv FZ Hs Hn1 Hn2 Hk1 Hk2 Hk16 Dkn Hmin Hmax Rmin Rmax Rnc Rncn R11 NCV SOK KOK H2 H10 H8.
  replace (Z_to_bv 64 0x39c28) with (0x39c28 : word) by (apply bv_eq; reflexivity).
  destruct (Z_lt_ge_dec maxv minv) as [LT | GE].
  - eapply reach_msteps.
    { kf_lw F_39c28 D_39c28 (s - 148)%Z minv Rmin.
      kf_lw F_39c2c D_39c2c (s - 152)%Z maxv Rmax.
      stepb_ft F_39c30 D_39c30 ltac:(condZ).
      kf_ld F_39c34 D_39c34 (s - 272)%Z 11%Z R11.
      stepj F_39c38 D_39c38.
      apply mst_refl. }
    kf_pc (Z_to_bv 64 0x39d98).
    apply reach_done. do 4 eexists. split; [reflexivity |].
    split; [exact FZ |]. split; [apply rinv_refl |]. split; [exact KOK |].
    split; [gres; pin; reflexivity |]. split; [gres; pin; reflexivity |]. split; [gres; pin; reflexivity |].
    split; [gres; pin; reflexivity |]. split; [gres; pin; reflexivity |].
    split; [solve_regs_agree | intros r _; reflexivity].
  - eapply reach_msteps.
    { kf_lw F_39c28 D_39c28 (s - 148)%Z minv Rmin.
      kf_lw F_39c2c D_39c2c (s - 152)%Z maxv Rmax.
      stepb_tk F_39c30 D_39c30 ltac:(condZ).
      sn F_39cd0 D_39cd0.
      stepat F_39cd4 D_39cd4 (Z_to_bv 64 1) ltac:(gres; pin; apply zbv_snez; lia).
      kf_zand F_39cd8 D_39cd8 (kf_mod4 kf Hk16).
      kf_lit F_39cdc D_39cdc (Z_to_bv 64 1).
      kf_lit F_39ce0 D_39ce0 (Z_to_bv 64 1).
      kf_ld F_39ce4 D_39ce4 (s - 272)%Z 11%Z R11.
      apply mst_refl. }
    eapply reach_weaken; cycle 1.
    { apply (kf_outer s nc kf minv maxv m ltac:(repeat split; lia) ltac:(lia) Rncn Rnc NCV SOK 9%nat fr cs _ m 0%Z minv
               ltac:(reflexivity) ltac:(lia) ltac:(unfold nc_val; rewrite Z.mul_0_r, Z.quot_0_l by lia; lia) FZ (rinv_refl _ _) KOK);
        gres; pin; first [reflexivity | f_equal; lia]. }
    intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI' & OK' & G2 & G10 & G11 & G28 & G8 & AG & FS).
    do 4 eexists. split; [reflexivity |].
    do 8 (split; [assumption |]).
    split; [| exact FS].
    unfold KF_L in AG. ra_chain.
Qed.

End BilSegsKF.
