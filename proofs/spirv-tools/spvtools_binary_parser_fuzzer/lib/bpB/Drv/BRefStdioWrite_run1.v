(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStepTac BHoare BWalkTac BStoreOk BStreamSim BMmapSim BLibAtomic BExitSim BShapeAlg BNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRefStdioDefs B_code_16b2d8_16b5b8.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma v_sub_Z : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.

Lemma v_add_Z : forall a (l : word), (0 <= a < 2^64)%Z ->
  v_add (Z_to_bv 64 a) l = Z_to_bv 64 (a + bv_unsigned l).
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_wZ : forall (b : word) c, (0 <= c < 2^64)%Z ->
  v_add b (Z_to_bv 64 c) = Z_to_bv 64 (bv_unsigned b + c).
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_ZZ' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.

Lemma sltu0_xor_ne : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> a <> b ->
  v_sltu (Z_to_bv 64 0) (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) = Z_to_bv 64 1.
Proof.
  intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
  rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
  pose proof (Z_lxor_range a b Ha Hb) as Hr.
  rewrite u_Z2bv by lia.
  destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
  intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
  rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

Lemma sltu_ge : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

Lemma sltu_lt : forall a b, (0 <= a < b)%Z -> (b < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
  intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
  destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

Lemma v_and_m1_l : forall a, (0 <= a < 2^64)%Z ->
  v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof.
  intros a H. unfold v_and. u_norm.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  f_equal. apply Z.mod_small. lia.
Qed.

Lemma v_subw_small_lit : forall a b, (0 <= b <= a)%Z -> (a < 2^31)%Z ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H H2. unfold v_subw. u_norm.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  reflexivity.
Qed.

Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (can : word) (wb n : Z) (s l : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (su - 8))  (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (su - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 (su - 24)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (su - 32)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (su - 40)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 (su - 48)) (word_to_le_bytes 8 s4))
    (Z_to_bv 64 (su - 56)) (word_to_le_bytes 8 s5))
    (Z_to_bv 64 (su - 64)) (word_to_le_bytes 8 s6))
    (Z_to_bv 64 (su - 72)) (word_to_le_bytes 8 can))
    (Z_to_bv 64 (su - 104)) (word_to_le_bytes 8 (Z_to_bv 64 wb)))
    (Z_to_bv 64 (su - 96)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (Z_to_bv 64 (su - 88)) (word_to_le_bytes 8 s))
    (Z_to_bv 64 (su - 80)) (word_to_le_bytes 8 l).

Lemma sw_enter `{fx : DFP} : forall regs mem rom (su f wb wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x189920 <= f)%Z -> (f + 232 <= 0x189be8)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wb < wp)%Z -> (wp < 2^64)%Z -> (wp - wb + bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x16cdd0 : word) mem rom)
      (mkst regs' (0x16ce58 : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 104)
    /\ getr regs' 12 = Z_to_bv 64 2
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 (su - 104)
    /\ getr regs' 21 = Z_to_bv 64 0x6e5898
    /\ getr regs' 22 = Z_to_bv 64 (wp - wb + bv_unsigned l)
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f wb wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WBP WPhi SMALL.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_16b428 D_16b428. rewrite Hsp. sp_renorm.

    stepST F_16b42c D_16b42c (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_16b430 D_16b430 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_16b434 D_16b434 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_16b438 D_16b438 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_16b43c D_16b43c (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_16b440 D_16b440 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_16b444 D_16b444 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_16b448 D_16b448 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).

    stepn F_16b44c D_16b44c. rewrite Ha2.
    stepn F_16b450 D_16b450. rewrite Ha0.

    stepn F_16b454 D_16b454.
    stepLD8 F_16b458 D_16b458 (Z_to_bv 64 0x6e5898).
    stepLD8 F_16b45c D_16b45c can.
    stepST F_16b460 D_16b460 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).

    stepLD8 F_16b464 D_16b464 (Z_to_bv 64 wp).
    stepLD8 F_16b468 D_16b468 (Z_to_bv 64 wb).

    stepn F_16b46c D_16b46c. rewrite (v_sub_Z wp wb) by lia.
    stepn F_16b470 D_16b470.

    stepST F_16b474 D_16b474 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
    stepST F_16b478 D_16b478 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
    stepST F_16b47c D_16b47c (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_16b480 D_16b480 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).

    stepn F_16b484 D_16b484. rewrite (v_add_Z (wp - wb) l) by lia.
    stepn F_16b488 D_16b488. rewrite (sltu0_xor_ne wp wb) by lia.

    stepb_ft F_16b48c D_16b48c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_16b490 D_16b490.
    replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepn F_16b494 D_16b494.

    stepLD F_16b49c D_16b49c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_16b4a0 D_16b4a0.
    stepn F_16b4a4 D_16b4a4.
    stepn F_16b4a8 D_16b4a8.
    stepn F_16b4ac D_16b4ac.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Lemma sw_enter_eq `{fx : DFP} : forall regs mem rom (su f wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x189920 <= f)%Z -> (f + 232 <= 0x189be8)%Z ->
  sw_file mem f wp wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wp < 2^64)%Z -> (bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x16cdd0 : word) mem rom)
      (mkst regs' (0x16ce58 : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wp 0 s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 88)
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 (su - 88)
    /\ getr regs' 21 = Z_to_bv 64 0x6e5898
    /\ getr regs' 22 = l
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WPhi SMALL.
  pose proof (u64_range l) as Hl.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_16b428 D_16b428. rewrite Hsp. sp_renorm.
    stepST F_16b42c D_16b42c (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_16b430 D_16b430 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_16b434 D_16b434 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_16b438 D_16b438 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_16b43c D_16b43c (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_16b440 D_16b440 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_16b444 D_16b444 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_16b448 D_16b448 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    stepn F_16b44c D_16b44c. rewrite Ha2.
    stepn F_16b450 D_16b450. rewrite Ha0.
    stepn F_16b454 D_16b454.
    stepLD8 F_16b458 D_16b458 (Z_to_bv 64 0x6e5898).
    stepLD8 F_16b45c D_16b45c can.
    stepST F_16b460 D_16b460 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    stepLD8 F_16b464 D_16b464 (Z_to_bv 64 wp).
    stepLD8 F_16b468 D_16b468 (Z_to_bv 64 wp).
    stepn F_16b46c D_16b46c. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
    stepn F_16b470 D_16b470.
    stepST F_16b474 D_16b474 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
    stepST F_16b478 D_16b478 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
    stepST F_16b47c D_16b47c (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_16b480 D_16b480 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    stepn F_16b484 D_16b484.
    stepn F_16b488 D_16b488. rewrite sltu0_xor_eq.

    stepb_tk F_16b48c D_16b48c ltac:(apply c_eq_refl).
    stepn F_16b498 D_16b498.
    replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepLD F_16b49c D_16b49c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_16b4a0 D_16b4a0.
    stepn F_16b4a4 D_16b4a4.
    stepn F_16b4a8 D_16b4a8.
    stepn F_16b4ac D_16b4ac.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
