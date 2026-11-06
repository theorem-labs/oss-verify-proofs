(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "le"; "modulo"; "lt"; "mul"; "sub"; "to_nat"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "@Corelib.Init.Datatypes"; "length"; "nat"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "word_le8"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "in_argv"; "in_envp"; "in_hwcap"; "in_uid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes.ArgBytes"; "STRo"; "A1o"; "ARGC"; "LEN"; "RNDo"; "L2U"; "L3"; "argv0"; "ms0A"; "BSB"; "RND16"; "argv1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "@Corelib.Init.Nat"; "add"; "mul"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init"; "phA"; "pcA"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "rnd0"; "rnd1"; "Jinit"; "ms0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "tab"; "bsb"; "img_len"; "pad_len"; "rand_off"; "region"; "str_off"; "valid_entry48"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "entry_stack_fits"; "mkEntry"; "@Stdlib.Lists.List"; "flat_map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros A l1 l2. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros A l1 l2. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma nth_error_skipn' : forall {A} (l : list A) n j, nth_error (skipn n l) j = nth_error l (n + j).
Proof. intros A l n j. rewrite nth_error_skipn. reflexivity. Qed.

Lemma flat_map_le8_nth : ltac2:(tb__ "0|3|
S14SbQ40A1M0A1S13S13SbQ8A1M1G0S1aR4S12G0R5A2A2S1aR4U8M2A2S0G1SfG1S2fS30G2R6A2R5A2S45G0G1S1cR7A4R4A4SfG1R5S1cSfG0R6R7R3A4A1R4A4A3F_;F_;Fd';Fd;Fj;Fk;Fl;").
Proof.
  induction l as [|w l IH]; intros k j d d' Hk Hj; [cbn in Hk; lia|].
  cbn [flat_map nth]. destruct k as [|k].
  - rewrite app_nth1 by (rewrite length_word_le8; lia). replace (8 * 0 + j)%nat with j by lia. reflexivity.
  - rewrite app_nth2 by (rewrite length_word_le8; lia). rewrite length_word_le8.
    replace (8 * S k + j - 8)%nat with (8 * k + j)%nat by lia. apply IH; [cbn in Hk; lia | exact Hj].
Qed.

Section ArgBytes.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
S42S35S44Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.

Definition argv0 : list byte := nth 0 (in_argv inp) [].
Definition argv1 : list byte := nth 1 (in_argv inp) [].
Definition ARGC : Z := Z.of_nat (length (in_argv inp)).

Definition STRo : Z := ltac2:(tb__ "0|0|
S3S41S1dVinp;A1S1eVinp;A1A2A1").
Definition A1o : Z := ltac2:(tb__ "0|0|
S2S21S2S3S12SbQ8A1S28A2A1Z1A2A2").
Definition RNDo : Z := ltac2:(tb__ "0|0|
S3S3fS1dVinp;A1S1eVinp;A1A2A1").
Definition LEN : Z := ltac2:(tb__ "0|0|
S3S3dS1dVinp;A1S1eVinp;A1A2A1").
Definition BSB : list byte := ltac2:(tb__ "0|0|
S3cS33Vsp;S1dVinp;A1S1eVinp;A1S20Vinp;A1S1fVinp;A1Vdraw;A7").

Definition RND16 : list byte := ltac2:(tb__ "0|0|
S17SbQ8A1S1cS36Vdraw;A1A1S1cS37Vdraw;A1A1A3").

Definition L3 : list byte := skipn (Z.to_nat A1o) BSB.
Definition L2U : list byte := skipn (Z.to_nat STRo) BSB.
Definition ms0A : machine_state := ltac2:(tb__ "0|0|
S39S3aS34S33Vsp;Vdraw;Vinp;A6").

Lemma Hsp : valid_sp sp. Proof. destruct Hent as (H & _). exact H. Qed.
Lemma Hfit : ltac2:(tb__ "0|0|
S43Vsp;S1dVinp;A1S1eVinp;A1A3"). Proof. destruct Hent as (_ & _ & _ & H). exact H. Qed.

Lemma arg_nums : ltac2:(tb__ "0|d|
S1S4Z7fff80000000SdQ40Vsp;A2M0A2S1S4S2G0S24A2SaZ2Z2fA2A2S1S0SeS5G0Z10M1A2Z0M2A3S1S1S4Z1M3S23A2S4S23Z400A2A2S1S0SeS21S2S2Zb8S7Z8M4S23A2A2S7G4S3S12S14SbQ8A1M5A1S1eVinp;A1M6A2A1A2A2A3S1S0SeS5S21G4A2G2A3S1S0SeS22S2S2S21S3S12G5S28A2A1M7A2G3A2A3S1S4S22S2S21S3S3bS1dVinp;A1M8A1A1M9A2MaA2S1S0SeS25S2S2GaS3S3bG6A1A1MbA2S3S3eG8G6A2A1McA2A3S1S6GcG4A2S1S0SeS5S25G4A2G2A3S1S0SeS24S2S25G1A2A3S1S4S24Z2228cfA2S1S4G7Z1ffffA2S1S4G9Z200000A2S4GbZ20000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (nums sp inp Hsp Hinp) as N. cbv zeta in N.
  destruct N as (Nsp & N16 & Nargc & Nenvc & Nstr & Nlen0 & Nlen0b & Nrnd & Npad & Ntab1 & Ntab2 & Nlen & Nrm8 & Nsm8).
  pose proof (LEN_fit sp inp Hinp Hfit) as LF. rewrite sp_hi_val in LF.
  pose proof (Zle_0_nat (rand_off (in_argv inp) (in_envp inp))) as H0.
  unfold LEN, RNDo, A1o, STRo, ARGC, argv0. repeat split; lia.
Qed.

Lemma length_BSB : Z.of_nat (length BSB) = LEN.
Proof. unfold BSB, LEN. rewrite length_bsb. reflexivity. Qed.

Lemma BSB_byte : ltac2:(tb__ "0|4|
SeS1S4Z0M0R1A2S6R1S24A2A2S0S16SbQ8M1A1M2A1S32S29ScQ40M3S2SdG3Vsp;A2R2A2A2A2S15G2SfG2S9R2A1S2aScG1G0A2A4A2A3F_;Foff;").
Proof.
  intros off Hoff. unfold ms0A. rewrite (ms0_mem_img segsA pcA phA sp draw inp Hsp Hinp off Hoff). fold BSB.
  apply nth_error_nth'. pose proof length_BSB. lia.
Qed.

Lemma length_L3 : ltac2:(tb__ "0|0|
S0SeS3S12SbQ8A1S27A2A1S8S24S22A2A3").
Proof. unfold L3. rewrite length_skipn. pose proof length_BSB. pose proof arg_nums. pose proof (Zle_0_nat (tab (in_argv inp))). lia. Qed.
Lemma length_L2U : ltac2:(tb__ "0|0|
S0SeS3S12SbQ8A1S26A2A1S8S24S21A2A3").
Proof. unfold L2U. rewrite length_skipn. pose proof length_BSB. pose proof arg_nums. pose proof (Zle_0_nat (tab (in_argv inp))). lia. Qed.

Lemma L3_byte : ltac2:(tb__ "0|3|
S13S1aR1S12SbQ8M0A1M1S27A2A2S0S16G1A1S32S29ScQ40M2S2S2SdG2Vsp;A2S22A2S3R2A1A2A2A2S15G1SfG1R2S27ScG0Z0A2A4A2A3F_;Fj;").
Proof.
  intros j Hj. pose proof length_L3. pose proof arg_nums. pose proof (Zle_0_nat (tab (in_argv inp))).
  replace (bv_unsigned sp + A1o + Z.of_nat j) with (bv_unsigned sp + (A1o + Z.of_nat j)) by lia.
  rewrite BSB_byte by lia. f_equal. unfold L3. rewrite nth_skipn. f_equal. lia.
Qed.
Lemma L2U_byte : ltac2:(tb__ "0|3|
S13S1aR1S12SbQ8M0A1M1S26A2A2S0S16G1A1S32S29ScQ40M2S2S2SdG2Vsp;A2S21A2S3R2A1A2A2A2S15G1SfG1R2S26ScG0Z0A2A4A2A3F_;Fj;").
Proof.
  intros j Hj. pose proof length_L2U. pose proof arg_nums. pose proof (Zle_0_nat (tab (in_argv inp))).
  replace (bv_unsigned sp + STRo + Z.of_nat j) with (bv_unsigned sp + (STRo + Z.of_nat j)) by lia.
  rewrite BSB_byte by lia. f_equal. unfold L2U. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma region_skipn : ltac2:(tb__ "0|2|
S13S14SbQ8A1M0A1M1S40S33Vsp;S1dVinp;A1S1eVinp;A1S20Vinp;A1S1fVinp;A1Vdraw;R2R1A9S0G1S10G0S12G0R2A2S11G0R3S2aA3A3R2A3F_;Fseg;Fo;").
Proof.
  intros o seg (pre & post & E & L). unfold BSB. rewrite E, <- L, skipn_app_exact. apply firstn_app_exact.
Qed.

Lemma L2U_head : ltac2:(tb__ "0|2|
S0S14SbQ8M0A1M1A1S10G1S2fS12G1S28A2U1A2S26A3S17G1S28S18G1ScG0Z0A2S19G1A1A3A3A3").
Proof.
  pose proof arg_nums as AN.
  pose proof (region_argv_str phA sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw 0 ltac:(unfold InitLayout.argc; unfold ARGC in AN; lia)) as R.
  cbn [firstn tab] in R. rewrite Nat.add_0_r in R. fold argv0 in R.
  replace (length argv0 + 1)%nat with (length (argv0 ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn; lia).
  unfold L2U, STRo. rewrite Nat2Z.id. exact (region_skipn _ _ R).
Qed.

Lemma L3_head : ltac2:(tb__ "0|2|
S4Z2S23A2S0S14SbQ8M0A1M1A1S10G1S2fS12G1S2cA2U1A2S27A3S17G1S2cS18G1ScG0Z0A2S19G1A1A3A3A3F_;").
Proof.
  intros H2. pose proof arg_nums as AN.
  pose proof (region_argv_str phA sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw 1 ltac:(unfold InitLayout.argc; unfold ARGC in H2; lia)) as R.
  fold argv1 in R.
  assert (E : (str_off (in_argv inp) (in_envp inp) + tab (firstn 1 (in_argv inp)))%nat = Z.to_nat A1o).
  { unfold A1o, STRo, argv0. unfold ARGC in H2. destruct (in_argv inp) as [|a r]; [cbn in H2; lia|]. cbn [firstn tab nth]. rewrite Nat.add_0_r. lia. }
  rewrite E in R.
  replace (length argv1 + 1)%nat with (length (argv1 ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn; lia).
  unfold L3. exact (region_skipn _ _ R).
Qed.

Lemma length_RND16 : length RND16 = 16%nat.
Proof. unfold RND16. rewrite length_app, !length_word_le8. reflexivity. Qed.

Lemma BSB_rand : ltac2:(tb__ "0|3|
S13S1aR1U10A2S0SbQ8M0A1M1SfG1S2fS9S25A1R2A2S2aScG0Z0A2M2A4SfG1R2S2bG2A4A3F_;Fj;").
Proof.
  intros j Hj. destruct (region_rand phA sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw) as (pre & post & E & L).
  unfold BSB. rewrite E. unfold RNDo. rewrite Nat2Z.id, <- L.
  rewrite app_nth2 by lia. rewrite Nat.add_comm, Nat.add_sub.
  assert (ER : rand_bytes draw = RND16).
  { unfold rand_bytes, RND16, rnd0, rnd1. rewrite at_random_bytes_words. cbn [flat_map]. rewrite app_nil_r. reflexivity. }
  rewrite app_nth1 by (rewrite ER, length_RND16; lia). rewrite ER. reflexivity.
Qed.

Lemma RND16_cell0 : ltac2:(tb__ "0|3|
S13S1aR1U8A2S0SbQ8M0A1M1SfG1R2S2bScG0Z0A2M2A4SfG1R2S1cS36Vdraw;A1A1G2A4A3F_;Fj;").
Proof. intros j Hj. unfold RND16. rewrite app_nth1 by (rewrite length_word_le8; lia). reflexivity. Qed.
Lemma RND16_cell1 : ltac2:(tb__ "0|4|
S13S1S1bU8M0R1A2S1aR1U10A2A2S0SbQ8M1A1M2SfG2R2S2bScG1Z0A2M3A4SfG2S31R2G0A2S1cS37Vdraw;A1A1G3A4A3F_;Fj;").
Proof. intros j Hj. unfold RND16. rewrite app_nth2 by (rewrite length_word_le8; lia). rewrite length_word_le8. reflexivity. Qed.

Lemma a1p_word : ltac2:(tb__ "0|4|
S4Z2S23A2S13S1aR1U8A2S0S16SbQ8M0A1M1A1S32S29ScQ40M2S2S2SdG2Vsp;A2M3Z10A2S3R2A1A2A2A2S15G1SfG1R2S1cScG2S2G3S22A2A2A1ScG0Z0A2A4A2A3F_;Fj;F_;").
Proof.
  intros H2 j Hj. pose proof arg_nums as AN. unfold ARGC in H2.
  assert (T1 : Z.of_nat (tab (firstn 1 (in_argv inp))) = Z.of_nat (length argv0) + 1).
  { unfold argv0. destruct (in_argv inp) as [|a r]; [cbn in H2; lia|]. change (tab (firstn 1 (a :: r))) with (length a + 1 + 0)%nat. cbn [nth]. lia. }
  assert (LP : length (argv_ptrs sp (in_argv inp) (in_envp inp)) = length (in_argv inp)) by (unfold argv_ptrs; apply string_addrs_fst_length).
  assert (P1 : nth 1 (argv_ptrs sp (in_argv inp) (in_envp inp)) (Z_to_bv 64 0) = Z_to_bv 64 (bv_unsigned sp + A1o)).
  { unfold argv_ptrs. rewrite string_addrs_nth by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold str_base.
    rewrite bv_add_unsigned. unfold nat_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite T1. unfold A1o, STRo, LEN, RNDo in *. pose proof (Zle_0_nat (str_off (in_argv inp) (in_envp inp))). pose proof (Zle_0_nat (tab (in_argv inp))).
    rewrite (Z.mod_small (Z.of_nat (str_off (in_argv inp) (in_envp inp))) (2 ^ 64)) by lia.
    rewrite (Z.mod_small (bv_unsigned sp + Z.of_nat (str_off (in_argv inp) (in_envp inp))) (2 ^ 64)) by lia.
    f_equal. lia. }
  destruct (region_hdr phA sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw) as (pre & post & E & L).
  assert (Lpre : pre = []) by (destruct pre; [reflexivity | cbn in L; lia]). subst pre. cbn [app] in E.
  replace (bv_unsigned sp + 16 + Z.of_nat j) with (bv_unsigned sp + (16 + Z.of_nat j)) by lia.
  rewrite BSB_byte by (pose proof (Zle_0_nat (tab (in_argv inp))); pose proof (Zle_0_nat (tab (in_envp inp))); pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))); lia).
  f_equal. unfold BSB. rewrite E. rewrite app_nth1 by (rewrite length_hdr_bytes; unfold InitLayout.argc; lia).
  unfold hdr_bytes. rewrite app_nth2 by (rewrite length_word_le8; lia). rewrite length_word_le8.
  rewrite app_nth1 by (rewrite length_flat_map_le8, LP; lia).
  replace (Z.to_nat (16 + Z.of_nat j) - 8)%nat with (8 * 1 + j)%nat by lia.
  rewrite (flat_map_le8_nth _ 1 j (Z_to_bv 8 0) (Z_to_bv 64 0)) by (rewrite ?LP; lia). rewrite P1. reflexivity.
Qed.

Lemma A1o_eq : ltac2:(tb__ "0|3|
S2eS38S3aS34S33Vsp;Vdraw;Vinp;R1A7S1S0SeS2S2SdQ40M0S2dR2P4A2A2SdG0S2dR2P5A2A2A2Z1A2S2SdG0Vsp;A2M1S22A2A3S1S0SeSdG0S2dR2P6A2A2S2G1S25A2A3S1S0SeSdG0S2dR2P1A2A2G1A3S1S0SeSdG0S2dR2P2A2A2S23A3S1S0SbG0A1M2S2dR2P9A2S36Vdraw;A1A3S0G2S2dR2PaA2S37Vdraw;A1A3A2A2A2A2A2F_;Frho;").
Proof.
  intros rho HJ. pose proof arg_nums as AN.
  rewrite (ji_sp _ _ _ _ _ _ _ HJ), (ji_argv0 _ _ _ _ _ _ _ HJ), (ji_len0 _ _ _ _ _ _ _ HJ), (ji_rand _ _ _ _ _ _ _ HJ), (ji_argc _ _ _ _ _ _ _ HJ),
          (ji_rnd0 _ _ _ _ _ _ _ HJ), (ji_rnd1 _ _ _ _ _ _ _ HJ).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (Zle_0_nat (tab (in_argv inp))). pose proof (Zle_0_nat (tab (in_envp inp))). pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))).
  unfold A1o, STRo, RNDo, LEN, ARGC, argv0 in *.
  rewrite !Z.mod_small by lia. repeat split; try lia; reflexivity.
Qed.
End ArgBytes.
