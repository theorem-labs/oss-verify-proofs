(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes
  AsanAcct AsanAcctShape NoReserve DivergeSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanNodesLibE AsanExtNodes.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanExtNodesSound () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "orshr"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "LinuxProcessSemantics.Riscv.Instr.ALU_OR"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "LinuxProcessSemantics.Riscv.Prelude.zext"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "TB"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.AsanExtNodes.code_is"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "OSSVerify.KrLib.ABoot.AsanExtNodes.rom_bytes_ok"; "Corelib.Init.Peano.lt"; "OSSVerify.KrLib.ABoot.PropExec.seg_rom"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "asanreflect_fx"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.node1_stmt"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.always"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.acs"; "OSSVerify.KrLib.ABoot.AsanExtNodes.node_imgword"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.atable"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "OSSVerify.KrLib.ABoot.AxSymRun3.env_agree"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.ext_stmt"; "OSSVerify.KrLib.ABoot.AsanExtNodes.XN_asan"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition orshr (x k : Z) : Z := Z.lor x (Z.shiftr x k).

Lemma orshr_spec : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "Px,$0.Pk,$0.Pi,$0.P,(1.=R2.)P,(1.=R2.)(2.$3.(4.(5.R5.R4.)R3.)(6.(4.R5.R3.)(4.R5.(7.R3.R4.))))")
(* [comment removed for export] *).
Proof. intros x k i Hk Hi. unfold orshr. rewrite Z.lor_spec, Z.shiftr_spec by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition smeared (x : Z) (m : Z) (s : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "Pi,$0.P,(1.=R1.)(8.(2.$3.(4.O1.R2.)$9.)(:.$0.Lj,$0.(;.(;.(1.=R1.)(1.R1.O2.))(2.$3.(4.O3.(7.R3.R1.))$9.))))")
(* [comment removed for export] *).

Lemma smeared_0 : forall x, smeared x 0 x.
Proof.
  intros x i Hi. split.
  - intros H. exists 0. rewrite Z.add_0_r. split; [lia | exact H].
  - intros (j & Hj & H). replace j with 0 in H by lia. rewrite Z.add_0_r in H. exact H.
Qed.

Lemma smeared_step : forall x m s k, 0 <= m -> k = m + 1 -> smeared x m s -> smeared x (m + k) (orshr s k).
Proof.
  intros x m s k Hm Hk HS i Hi. rewrite orshr_spec by lia. split.
  - intros H. apply orb_prop in H as [H|H].
    + destruct (proj1 (HS i Hi) H) as (j & Hj & Hb). exists j. split; [lia | exact Hb].
    + destruct (proj1 (HS (i + k) ltac:(lia)) H) as (j & Hj & Hb). exists (k + j). split; [lia|]. rewrite Z.add_assoc. exact Hb.
  - intros (j & Hj & Hb). destruct (Z_lt_le_dec j k) as [Hjk|Hjk].
    + rewrite (proj2 (HS i Hi)); [reflexivity|]. exists j. split; [lia | exact Hb].
    + rewrite (proj2 (HS (i + k) ltac:(lia))); [apply orb_true_r|]. exists (j - k). split; [lia|].
      replace (i + k + (j - k)) with (i + j) by lia. exact Hb.
Qed.

Definition smearZ (x : Z) : Z :=
  orshr (orshr (orshr (orshr (orshr (orshr x 1) 2) 4) 8) 16) 32.

Lemma smearZ_smeared : forall x, smeared x 63 (smearZ x).
Proof.
  intros x. unfold smearZ.
  apply (smeared_step x 31 _ 32); [lia | lia |]. apply (smeared_step x 15 _ 16); [lia | lia |].
  apply (smeared_step x 7 _ 8); [lia | lia |]. apply (smeared_step x 3 _ 4); [lia | lia |].
  apply (smeared_step x 1 _ 2); [lia | lia |]. apply (smeared_step x 0 _ 1); [lia | lia |]. apply smeared_0.
Qed.

Lemma smearZ_47 : forall x, 2 ^ 46 <= x < 2 ^ 47 -> smearZ x = 2 ^ 47 - 1.
Proof.
  intros x Hx. pose proof (smearZ_smeared x) as SM.
  assert (B46 : Z.testbit x 46 = true).
  { apply Z.testbit_true; [lia|]. replace (x / 2 ^ 46) with 1; [reflexivity|].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (BHI : forall k, 47 <= k -> Z.testbit x k = false).
  { intros k Hk. apply (Z_testbit_high 47); lia. }
  replace (2 ^ 47 - 1) with (Z.ones 47) by (rewrite Z.ones_equiv; lia).
  apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec n 47).
  - apply (proj2 (SM n Hn)). exists (46 - n). split; [lia|]. replace (n + (46 - n)) with 46 by lia. exact B46.
  - destruct (Z.testbit (smearZ x) n) eqn:Hb; [|reflexivity]. exfalso.
    destruct (proj1 (SM n Hn) Hb) as (j & Hj & Hbj). rewrite BHI in Hbj by lia. discriminate.
Qed.

(* [comment removed for export] *)
Lemma u_orshr : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "Ps,(<.&40.)Pk,(<.&6.)(2.$0.(=.&40.(>.$?.R2.(>.$10.R2.(11.&6.&40.R1.))))(5.(=.&40.R2.)(=.&6.R1.)))")
(* [comment removed for export] *).
Proof.
  intros s k. rewrite alu_or, alu_srli. unfold v_or, v_srli, orshr.
  pose proof (u64_range s) as Rs. pose proof (bv_unsigned_in_range _ k) as Rk.
  pose proof (Z_shiftr_range (bv_unsigned s) (bv_unsigned k) Rs ltac:(lia)) as R1.
  rewrite (u64_lit (Z.shiftr _ _)) by exact R1.
  apply u64_lit. apply Z_lor_range; [exact Rs | exact R1].
Qed.

Lemma smear_word : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "Px,(<.&40.)P,(;.(1.(12.+2.+2>.)(=.&40.R1.))(13.(=.&40.R1.)(12.+2.+2?.)))Zs1,(<.&40.)(>.$?.R2.(>.$10.R2.(11.&6.&40.(14.&6.+1.$15.))))Zs2,(<.&40.)(>.$?.R1.(>.$10.R1.(11.&6.&40.(14.&6.+2.$15.))))Zs3,(<.&40.)(>.$?.R1.(>.$10.R1.(11.&6.&40.(14.&6.+4.$15.))))Zs4,(<.&40.)(>.$?.R1.(>.$10.R1.(11.&6.&40.(14.&6.+8.$15.))))Zs5,(<.&40.)(>.$?.R1.(>.$10.R1.(11.&6.&40.(14.&6.+10.$15.))))Zs6,(<.&40.)(>.$?.R1.(>.$10.R1.(11.&6.&40.(14.&6.+20.$15.))))(2.(<.&40.)R1.(16.&40.(17.(12.+2.+2?.)+1.)))")
(* [comment removed for export] *).
Proof.
  intros x Hx. cbv zeta. apply bv_eq. rewrite !u_orshr. cbn [bv_unsigned].
  rewrite u64_lit by lia. fold (smearZ (bv_unsigned x)). apply smearZ_47. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_ne : forall r r' : bv 5, bv_unsigned r <> bv_unsigned r' -> r <> r'.
Proof. intros r r' H E. apply H. rewrite E. reflexivity. Qed.

Lemma if_rd : forall (T : Type) (rd : bv 5) (a b : T), bv_unsigned rd <> 0 -> (if bv_eqb rd 0 then a else b) = b.
Proof.
  intros T rd a b H. rewrite (bv_eqb_neq rd 0); [reflexivity|]. apply reg_ne. cbv. cbv in H. exact H.
Qed.

Lemma w32_of_unsigned : forall (w : bv 32) z, bv_unsigned w = z -> w = Z_to_bv 32 z.
Proof.
  intros w z H. apply bv_eq. rewrite Z_to_bv_unsigned, <- H. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Section Words.
Local Open Scope bv_scope.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
#[using="Type"] Lemma MD0 : decode_any (Z_to_bv 32 1398163) = Some (ShiftImm ALU_SRL 11 10 1, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME0 : is_ecall (Z_to_bv 32 1398163) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD1 : decode_any (Z_to_bv 32 1431655991) = Some (Lui 12 349525, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME1 : is_ecall (Z_to_bv 32 1431655991) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD2 : decode_any (Z_to_bv 32 858994359) = Some (Lui 13 209715, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME2 : is_ecall (Z_to_bv 32 858994359) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD3 : decode_any (Z_to_bv 32 252647223) = Some (Lui 14 61681, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME3 : is_ecall (Z_to_bv 32 252647223) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD4 : decode_any (Z_to_bv 32 16844727) = Some (Lui 15 4112, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME4 : is_ecall (Z_to_bv 32 16844727) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD5 : decode_any (Z_to_bv 32 11887923) = Some (Op ALU_OR 10 10 11, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME5 : is_ecall (Z_to_bv 32 11887923) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD6 : decode_any (Z_to_bv 32 1431700891) = Some (OpImm32 11 12 1365, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME6 : is_ecall (Z_to_bv 32 1431700891) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD7 : decode_any (Z_to_bv 32 859211291) = Some (OpImm32 12 13 819, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME7 : is_ecall (Z_to_bv 32 859211291) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD8 : decode_any (Z_to_bv 32 4042720923) = Some (OpImm32 13 14 3855, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME8 : is_ecall (Z_to_bv 32 4042720923) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD9 : decode_any (Z_to_bv 32 269977371) = Some (OpImm32 14 15 257, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME9 : is_ecall (Z_to_bv 32 269977371) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD10 : decode_any (Z_to_bv 32 2447251) = Some (ShiftImm ALU_SRL 15 10 2, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME10 : is_ecall (Z_to_bv 32 2447251) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD11 : decode_any (Z_to_bv 32 16082227) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME11 : is_ecall (Z_to_bv 32 16082227) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD12 : decode_any (Z_to_bv 32 33920915) = Some (ShiftImm ALU_SLL 15 11 32, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME12 : is_ecall (Z_to_bv 32 33920915) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD13 : decode_any (Z_to_bv 32 16090547) = Some (Op ALU_ADD 11 11 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME13 : is_ecall (Z_to_bv 32 16090547) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD14 : decode_any (Z_to_bv 32 33953683) = Some (ShiftImm ALU_SLL 15 12 32, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME14 : is_ecall (Z_to_bv 32 33953683) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD15 : decode_any (Z_to_bv 32 16123443) = Some (Op ALU_ADD 12 12 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME15 : is_ecall (Z_to_bv 32 16123443) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD16 : decode_any (Z_to_bv 32 33986451) = Some (ShiftImm ALU_SLL 15 13 32, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME16 : is_ecall (Z_to_bv 32 33986451) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD17 : decode_any (Z_to_bv 32 16156339) = Some (Op ALU_ADD 13 13 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME17 : is_ecall (Z_to_bv 32 16156339) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD18 : decode_any (Z_to_bv 32 34019219) = Some (ShiftImm ALU_SLL 15 14 32, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME18 : is_ecall (Z_to_bv 32 34019219) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD19 : decode_any (Z_to_bv 32 16189235) = Some (Op ALU_ADD 14 14 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME19 : is_ecall (Z_to_bv 32 16189235) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD20 : decode_any (Z_to_bv 32 4544403) = Some (ShiftImm ALU_SRL 15 10 4, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME20 : is_ecall (Z_to_bv 32 4544403) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD21 : decode_any (Z_to_bv 32 16082227) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME21 : is_ecall (Z_to_bv 32 16082227) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD22 : decode_any (Z_to_bv 32 8738707) = Some (ShiftImm ALU_SRL 15 10 8, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME22 : is_ecall (Z_to_bv 32 8738707) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD23 : decode_any (Z_to_bv 32 16082227) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME23 : is_ecall (Z_to_bv 32 16082227) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD24 : decode_any (Z_to_bv 32 17127315) = Some (ShiftImm ALU_SRL 15 10 16, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME24 : is_ecall (Z_to_bv 32 17127315) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD25 : decode_any (Z_to_bv 32 16082227) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME25 : is_ecall (Z_to_bv 32 16082227) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD26 : decode_any (Z_to_bv 32 33904531) = Some (ShiftImm ALU_SRL 15 10 32, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME26 : is_ecall (Z_to_bv 32 33904531) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD27 : decode_any (Z_to_bv 32 16082227) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME27 : is_ecall (Z_to_bv 32 16082227) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD28 : decode_any (Z_to_bv 32 4294264083) = Some (OpImm ALU_XOR 10 10 4095, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME28 : is_ecall (Z_to_bv 32 4294264083) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD29 : decode_any (Z_to_bv 32 1398675) = Some (ShiftImm ALU_SRL 15 10 1, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME29 : is_ecall (Z_to_bv 32 1398675) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD30 : decode_any (Z_to_bv 32 12055987) = Some (Op ALU_AND 11 15 11, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME30 : is_ecall (Z_to_bv 32 12055987) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD31 : decode_any (Z_to_bv 32 1085605171) = Some (Op ALU_SUB 10 10 11, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME31 : is_ecall (Z_to_bv 32 1085605171) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD32 : decode_any (Z_to_bv 32 12940723) = Some (Op ALU_AND 11 10 12, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME32 : is_ecall (Z_to_bv 32 12940723) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD33 : decode_any (Z_to_bv 32 2446611) = Some (ShiftImm ALU_SRL 10 10 2, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME33 : is_ecall (Z_to_bv 32 2446611) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD34 : decode_any (Z_to_bv 32 12940595) = Some (Op ALU_AND 10 10 12, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME34 : is_ecall (Z_to_bv 32 12940595) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD35 : decode_any (Z_to_bv 32 10847539) = Some (Op ALU_ADD 10 11 10, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME35 : is_ecall (Z_to_bv 32 10847539) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD36 : decode_any (Z_to_bv 32 4543891) = Some (ShiftImm ALU_SRL 11 10 4, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME36 : is_ecall (Z_to_bv 32 4543891) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD37 : decode_any (Z_to_bv 32 11863347) = Some (Op ALU_ADD 10 10 11, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME37 : is_ecall (Z_to_bv 32 11863347) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD38 : decode_any (Z_to_bv 32 13989171) = Some (Op ALU_AND 10 10 13, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME38 : is_ecall (Z_to_bv 32 13989171) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD39 : decode_any (Z_to_bv 32 48563507) = Some (Mul M_MUL 10 10 14, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME39 : is_ecall (Z_to_bv 32 48563507) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD40 : decode_any (Z_to_bv 32 59069715) = Some (ShiftImm ALU_SRL 10 10 56, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME40 : is_ecall (Z_to_bv 32 59069715) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD41 : decode_any (Z_to_bv 32 1084228923) = Some (Op32 ALU_SUB 10 0 10, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME41 : is_ecall (Z_to_bv 32 1084228923) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD42 : decode_any (Z_to_bv 32 4293920147) = Some (OpImm ALU_ADD 11 0 4095, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME42 : is_ecall (Z_to_bv 32 4293920147) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD43 : decode_any (Z_to_bv 32 10851635) = Some (Op ALU_SLL 10 11 10, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME43 : is_ecall (Z_to_bv 32 10851635) = false. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma MD44 : decode_any (Z_to_bv 32 4294264083) = Some (OpImm ALU_XOR 10 10 4095, 4%Z). Proof. vm_refl. Qed.
#[using="Type"] Lemma ME44 : is_ecall (Z_to_bv 32 4294264083) = false. Proof. vm_compute. reflexivity. Qed.
End Words.

(* [comment removed for export] *)
Definition TB (Rk R : bvmap 5 word) (a0 a1 a2 a3 a4 a5 : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "(;.(2.(<.&40.)(18.O8.(14.&5.+:.$15.))O6.)(;.(2.(<.&40.)(18.O8.(14.&5.+;.$15.))O5.)(;.(2.(<.&40.)(18.O8.(14.&5.+<.$15.))O4.)(;.(2.(<.&40.)(18.O8.(14.&5.+=.$15.))O3.)(;.(2.(<.&40.)(18.O8.(14.&5.+>.$15.))O2.)(;.(2.(<.&40.)(18.O8.(14.&5.+?.$15.))O1.)Pr,(<.&5.)P,(19.(2.(<.&5.)R1.(14.&5.+:.$15.)))P,(19.(2.(<.&5.)R2.(14.&5.+;.$15.)))P,(19.(2.(<.&5.)R3.(14.&5.+<.$15.)))P,(19.(2.(<.&5.)R4.(14.&5.+=.$15.)))P,(19.(2.(<.&5.)R5.(14.&5.+>.$15.)))P,(19.(2.(<.&5.)R6.(14.&5.+?.$15.)))(2.(<.&40.)(18.O8.R7.)(18.O7.R7.))))))))")
(* [comment removed for export] *).
Lemma TB_init : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PR,(1:.&5.(<.&40.))(1;.R1.R1.(18.R1.(14.&5.+:.$15.))(18.R1.(14.&5.+;.$15.))(18.R1.(14.&5.+<.$15.))(18.R1.(14.&5.+=.$15.))(18.R1.(14.&5.+>.$15.))(18.R1.(14.&5.+?.$15.)))")
(* [comment removed for export] *).
Proof. intros R. repeat split; intros; reflexivity. Qed.
Lemma TB_frame : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PRk,(1:.&5.(<.&40.))PR,(1:.&5.(<.&40.))Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)P,(1;.R8.R7.R6.R5.R4.R3.R2.R1.)Pr,(<.&5.)P,(19.(2.(<.&5.)R1.(14.&5.+:.$15.)))P,(19.(2.(<.&5.)R2.(14.&5.+;.$15.)))P,(19.(2.(<.&5.)R3.(14.&5.+<.$15.)))P,(19.(2.(<.&5.)R4.(14.&5.+=.$15.)))P,(19.(2.(<.&5.)R5.(14.&5.+>.$15.)))P,(19.(2.(<.&5.)R6.(14.&5.+?.$15.)))(2.(<.&40.)(18.R10.R7.)(18.R?.R7.))")
(* [comment removed for export] *).
Proof. intros Rk R a0 a1 a2 a3 a4 a5 H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
Lemma TB_get10 : forall Rk R a0 a1 a2 a3 a4 a5, TB Rk R a0 a1 a2 a3 a4 a5 -> getr Rk 10%bv = a0.
Proof. intros Rk R a0 a1 a2 a3 a4 a5 H. unfold TB in H. tauto. Qed.
Lemma TB_upd10 : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PRk,(1:.&5.(<.&40.))PR,(1:.&5.(<.&40.))Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pv,(<.&40.)P,(1;.R9.R8.R7.R6.R5.R4.R3.R2.)(1;.(1<.R:.(14.&5.+:.$15.)R2.)R9.R2.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros Rk R a0 a1 a2 a3 a4 a5 v (G0 & G1 & G2 & G3 & G4 & G5 & FR). unfold TB.
  rewrite getr_same by (apply reg_ne; cbv; lia). rewrite !getr_other by (apply reg_ne; cbv; lia).
  repeat split; try assumption. intros r N0 N1 N2 N3 N4 N5. rewrite getr_other by assumption. exact (FR r N0 N1 N2 N3 N4 N5).
Qed.
Lemma TB_get11 : forall Rk R a0 a1 a2 a3 a4 a5, TB Rk R a0 a1 a2 a3 a4 a5 -> getr Rk 11%bv = a1.
Proof. intros Rk R a0 a1 a2 a3 a4 a5 H. unfold TB in H. tauto. Qed.
Lemma TB_upd11 : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PRk,(1:.&5.(<.&40.))PR,(1:.&5.(<.&40.))Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pv,(<.&40.)P,(1;.R9.R8.R7.R6.R5.R4.R3.R2.)(1;.(1<.R:.(14.&5.+;.$15.)R2.)R9.R8.R2.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros Rk R a0 a1 a2 a3 a4 a5 v (G0 & G1 & G2 & G3 & G4 & G5 & FR). unfold TB.
  rewrite getr_same by (apply reg_ne; cbv; lia). rewrite !getr_other by (apply reg_ne; cbv; lia).
  repeat split; try assumption. intros r N0 N1 N2 N3 N4 N5. rewrite getr_other by assumption. exact (FR r N0 N1 N2 N3 N4 N5).
Qed.
Lemma TB_get12 : forall Rk R a0 a1 a2 a3 a4 a5, TB Rk R a0 a1 a2 a3 a4 a5 -> getr Rk 12%bv = a2.
Proof. intros Rk R a0 a1 a2 a3 a4 a5 H. unfold TB in H. tauto. Qed.
Lemma TB_upd12 : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PRk,(1:.&5.(<.&40.))PR,(1:.&5.(<.&40.))Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pv,(<.&40.)P,(1;.R9.R8.R7.R6.R5.R4.R3.R2.)(1;.(1<.R:.(14.&5.+<.$15.)R2.)R9.R8.R7.R2.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros Rk R a0 a1 a2 a3 a4 a5 v (G0 & G1 & G2 & G3 & G4 & G5 & FR). unfold TB.
  rewrite getr_same by (apply reg_ne; cbv; lia). rewrite !getr_other by (apply reg_ne; cbv; lia).
  repeat split; try assumption. intros r N0 N1 N2 N3 N4 N5. rewrite getr_other by assumption. exact (FR r N0 N1 N2 N3 N4 N5).
Qed.
Lemma TB_get13 : forall Rk R a0 a1 a2 a3 a4 a5, TB Rk R a0 a1 a2 a3 a4 a5 -> getr Rk 13%bv = a3.
Proof. intros Rk R a0 a1 a2 a3 a4 a5 H. unfold TB in H. tauto. Qed.
Lemma TB_upd13 : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PRk,(1:.&5.(<.&40.))PR,(1:.&5.(<.&40.))Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pv,(<.&40.)P,(1;.R9.R8.R7.R6.R5.R4.R3.R2.)(1;.(1<.R:.(14.&5.+=.$15.)R2.)R9.R8.R7.R6.R2.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros Rk R a0 a1 a2 a3 a4 a5 v (G0 & G1 & G2 & G3 & G4 & G5 & FR). unfold TB.
  rewrite getr_same by (apply reg_ne; cbv; lia). rewrite !getr_other by (apply reg_ne; cbv; lia).
  repeat split; try assumption. intros r N0 N1 N2 N3 N4 N5. rewrite getr_other by assumption. exact (FR r N0 N1 N2 N3 N4 N5).
Qed.
Lemma TB_get14 : forall Rk R a0 a1 a2 a3 a4 a5, TB Rk R a0 a1 a2 a3 a4 a5 -> getr Rk 14%bv = a4.
Proof. intros Rk R a0 a1 a2 a3 a4 a5 H. unfold TB in H. tauto. Qed.
Lemma TB_upd14 : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PRk,(1:.&5.(<.&40.))PR,(1:.&5.(<.&40.))Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pv,(<.&40.)P,(1;.R9.R8.R7.R6.R5.R4.R3.R2.)(1;.(1<.R:.(14.&5.+>.$15.)R2.)R9.R8.R7.R6.R5.R2.R3.)")
(* [comment removed for export] *).
Proof.
  intros Rk R a0 a1 a2 a3 a4 a5 v (G0 & G1 & G2 & G3 & G4 & G5 & FR). unfold TB.
  rewrite getr_same by (apply reg_ne; cbv; lia). rewrite !getr_other by (apply reg_ne; cbv; lia).
  repeat split; try assumption. intros r N0 N1 N2 N3 N4 N5. rewrite getr_other by assumption. exact (FR r N0 N1 N2 N3 N4 N5).
Qed.
Lemma TB_get15 : forall Rk R a0 a1 a2 a3 a4 a5, TB Rk R a0 a1 a2 a3 a4 a5 -> getr Rk 15%bv = a5.
Proof. intros Rk R a0 a1 a2 a3 a4 a5 H. unfold TB in H. tauto. Qed.
Lemma TB_upd15 : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PRk,(1:.&5.(<.&40.))PR,(1:.&5.(<.&40.))Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pv,(<.&40.)P,(1;.R9.R8.R7.R6.R5.R4.R3.R2.)(1;.(1<.R:.(14.&5.+?.$15.)R2.)R9.R8.R7.R6.R5.R4.R2.)")
(* [comment removed for export] *).
Proof.
  intros Rk R a0 a1 a2 a3 a4 a5 v (G0 & G1 & G2 & G3 & G4 & G5 & FR). unfold TB.
  rewrite getr_same by (apply reg_ne; cbv; lia). rewrite !getr_other by (apply reg_ne; cbv; lia).
  repeat split; try assumption. intros r N0 N1 N2 N3 N4 N5. rewrite getr_other by assumption. exact (FR r N0 N1 N2 N3 N4 N5).
Qed.
Section Sound.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Variable SP0 : Z.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SP0 SINV argH FS0).
#[local] Notation MR := (APS.Mr A SP0 argH).
#[local] Notation cfg := (cfg_of SEGS).

Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SP0 SINV argH argH_agree SINV_agree FS0.
Let hid_agree' := APS.hid_agree A nx0 SP0 argH argH_agree.

(* [comment removed for export] *)

#[using="Type"] Lemma code_is_at : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "Pp,$0.Pws,(1=.$0.)Pi,$1>.Pw,$0.Pq,$0.P,(2.$3.(1?.VSEGS,R5.R4.)$9.)P,(2.(20.$0.)(21.$0.R5.R4.)(22.$0.R3.))P,(2.$0.(7.R7.(23.+4.(24.R5.)))R3.)(2.(20.(<.&20.))(25.VSEGS,(16.&40.R4.))(22.(<.&20.)(16.&20.R5.)))")
(* [comment removed for export] *).
Proof.
  intros p ws. revert p. induction ws as [|w0 ws IH]; intros p i w q Hc Hn Hq.
  - destruct i; discriminate Hn.
  - cbn [code_is] in Hc. destruct (fetch_word SEGS (Z_to_bv 64 p)) as [w'|] eqn:Hf; [|discriminate].
    apply andb_prop in Hc as [Hw Hc]. apply Z.eqb_eq in Hw.
    destruct i as [|i].
    + cbn in Hn. injection Hn as <-. subst q. rewrite Z.mul_0_r, Z.add_0_r.
      rewrite Hf. f_equal. apply w32_of_unsigned. exact Hw.
    + cbn in Hn. apply (IH (p + 4) i w q Hc Hn). lia.
Qed.

#[using="Type"] Lemma rom_bytes_ok_at : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "Pb,$0.Pn,$1>.Pj,$1>.P,(2.$3.(26.VSEGS,R3.R2.)$9.)P,(27.R2.R3.)(19.(2.(20.(<.&8.))(28.VSEGS,(16.&40.(7.R5.(24.R3.))))(29.(<.&8.))))")
(* [comment removed for export] *).
Proof.
  intros b n. revert b. induction n as [|n IH]; intros b j H Hj; [lia|].
  cbn [rom_bytes_ok] in H. destruct (seg_rom SEGS (Z_to_bv 64 b)) as [v|] eqn:Hb; [|discriminate].
  destruct j as [|j].
  - rewrite Z.add_0_r, Hb. discriminate.
  - replace (b + Z.of_nat (S j)) with (b + 1 + Z.of_nat j) by lia. apply IH; [exact H | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_nstep : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PR,(1:.&5.(<.&40.))Ppcw,(<.&40.)PFULL,P,(<.&40.)(20.(<.&8.))Prom,P,(<.&40.)(20.(<.&8.))Pmodel,$2:.Pms',$2;.PT,$2<.P,(2.(20.(<.&40.))(2=.R3.)(29.(<.&40.)))P,(2.(2>.(2?.$2;.))(30.VSEGS,(31.$32.R8.R7.R6.R5.))(33.(2?.$2;.)(34.$2;.R3.(35.$36.))))P,(37.VSEGS,(38.R4.R5.)R3.)(37.VSEGS,(38.(31.$32.R:.R9.R8.R7.)R6.)R4.)")
(* [comment removed for export] *).
Proof.
  intros R pcw FULL rom model ms' T Hh Hs HT.
  eapply srz_silent1; [apply (node_instr_noacc SEGS); [exact Hh | reflexivity | exact Hs] | exact HT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="argH_agree SINV_agree cs_ok_agree' hid_agree'"] Lemma node_imgword_sound : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "Pb,$0.Pn,$1>.(39.VSEGS,VA,Vnx0,VLIMIT,VSP0,VSINV,VargH,VFS0,$3:.Lcs,$3;.(3<.VSEGS,Vnx0,R1.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros b n cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_imgword in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hrom]. apply andb_prop in Hc as [Hc Hb8]. apply andb_prop in Hc as [Hc Hb0].
  apply andb_prop in Hc as [Hc Hn8]. apply andb_prop in Hc as [Hfresh Hn1].
  apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8. apply Z.leb_le in Hb0. apply Z.ltb_lt in Hb8. unfold two64 in Hb8.
  set (v := nxt cs) in *.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle). fold v in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle.
  (* [comment removed for export] *)
  destruct (rdn_defined SEGS (MR E cs model FULL) n (Z_to_bv 64 b)) as (bs & Hrd & Hlen).
  { rewrite u64_lit by lia. lia. }
  { intros j Hj. unfold rd1. rewrite u64_lit by lia.
    pose proof (rom_bytes_ok_at b n j Hrom Hj) as Hr.
    destruct (MR E cs model FULL (Z_to_bv 64 (b + Z.of_nat j))); [discriminate | exact Hr]. }
  set (V := Z_to_bv 64 (bytes_le_to_Z bs)). set (E' := ext1 E v V).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree' E E' cs R FULL model Hag Hfresh HC) as HC'.
  apply (Hk E' R FULL model); [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | | reflexivity].
  assert (HMr : MR E' cs model FULL = MR E cs model FULL).
  { unfold Mr. rewrite (hid_agree' v E E' cs model Hag Fle Fallow). reflexivity. }
  assert (HV : word_to_le_bytes n V = bs).
  { unfold word_to_le_bytes, V. pose proof (AX2S.bytes_le_to_Z_bound bs) as Bb. rewrite Hlen in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Hlen. apply Z_to_le_bytes_to_Z. }
  destruct HC'; constructor; cbn [with_ss mk_ss a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset]; try assumption.
  - reflexivity.
  - change (MR E' (with_ss cs (mk_ss (pc cs) (s_regs (a_ss cs)) (KWord (SA (ELit 0) b) n (EVar v) :: kn_cutout (kn cs) (ELit 0) b (ELit (Z.of_nat n))) (S v))) model FULL)
      with (MR E' cs model FULL).
    constructor.
    + cbn [kentry_ok]. split; [exact Hn8|]. split.
      * unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia.
      * replace (adenot E' (SA (ELit 0) b)) with (Z_to_bv 64 b).
        2: { apply bv_eq. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite !u64_lit by (rewrite ?u64_lit; lia). lia. }
        rewrite HMr, Hrd. f_equal. cbn [edenot]. unfold E'. rewrite ext1_at. symmetry. exact HV.
    + eapply know_ok_cutout; [exact co_know0 | intros; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma getr0 : forall R, getr R 0%bv = Z_to_bv 64 0.
Proof. intros. reflexivity. Qed.

Ltac mstep HT F E D SA UPD :=
  lazymatch goal with |- srealizes _ (mkCfg (mkst ?Rk (Z_to_bv 64 ?p) _ _) _) _ =>
    lazymatch type of F with fetch_word _ (Z_to_bv 64 ?q) = _ => replace p with q by lia end end;
  eapply srz_nstep; [eassumption | eapply SA; [exact F | exact E | exact D] | ];
  rewrite if_rd by (cbv; lia);
  rewrite v_addi_pc by (unfold two64; lia);
  rewrite ?getr0;
  rewrite ?(TB_get10 _ _ _ _ _ _ _ _ HT), ?(TB_get11 _ _ _ _ _ _ _ _ HT), ?(TB_get12 _ _ _ _ _ _ _ _ HT),
          ?(TB_get13 _ _ _ _ _ _ _ _ HT), ?(TB_get14 _ _ _ _ _ _ _ _ HT), ?(TB_get15 _ _ _ _ _ _ _ _ HT);
  lazymatch goal with |- srealizes _ (mkCfg (mkst (regupd ?Rk ?rd ?v) _ _ _) _) _ =>
    let HT' := fresh "HT" in
    pose proof (UPD _ _ _ _ _ _ _ _ v HT) as HT'; clear HT; rename HT' into HT;
    let Rn := fresh "RR" in
    set (Rn := regupd Rk rd v) in *; clearbody Rn; try clear Rk
  end.

#[using="Type"] Lemma node_msbmask_sound : node1_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 always (node_msbmask SEGS).
Proof.
  intros cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_msbmask in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply AsanNodesLibE.Some_inj in Hn. subst cs'.
  apply andb_prop in Hc as [Hc Hrng]. apply andb_prop in Hc as [Hc Hcode]. apply andb_prop in Hc as [Hp0 HpB].
  apply Z.leb_le in Hp0. apply Z.ltb_lt in HpB. unfold two64 in HpB.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (xlo (kn cs) (reg cs 10)) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in Hrng as [Hlo46 Hhi47]. apply Z.leb_le in Hlo46. apply Z.ltb_lt in Hhi47.
  pose proof (xlo_sound SEGS E _ (kn cs) (reg cs 10) lo HK Hlo) as Xlo.
  pose proof (xhi_sound SEGS E _ (kn cs) (reg cs 10) hi HK Hhi) as Xhi.
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HR. pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  assert (Hx : 2 ^ 46 <= bv_unsigned (getr R 10%bv) < 2 ^ 47).
  { rewrite (HR 10%bv). change (sr_get (s_regs (a_ss cs)) 10%bv) with (reg cs 10). lia. }
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 0 1398163 (pc cs + 0) Hcode eq_refl ltac:(lia)) as F0.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 1 1431655991 (pc cs + 4) Hcode eq_refl ltac:(lia)) as F1.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 2 858994359 (pc cs + 8) Hcode eq_refl ltac:(lia)) as F2.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 3 252647223 (pc cs + 12) Hcode eq_refl ltac:(lia)) as F3.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 4 16844727 (pc cs + 16) Hcode eq_refl ltac:(lia)) as F4.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 5 11887923 (pc cs + 20) Hcode eq_refl ltac:(lia)) as F5.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 6 1431700891 (pc cs + 24) Hcode eq_refl ltac:(lia)) as F6.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 7 859211291 (pc cs + 28) Hcode eq_refl ltac:(lia)) as F7.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 8 4042720923 (pc cs + 32) Hcode eq_refl ltac:(lia)) as F8.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 9 269977371 (pc cs + 36) Hcode eq_refl ltac:(lia)) as F9.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 10 2447251 (pc cs + 40) Hcode eq_refl ltac:(lia)) as F10.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 11 16082227 (pc cs + 44) Hcode eq_refl ltac:(lia)) as F11.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 12 33920915 (pc cs + 48) Hcode eq_refl ltac:(lia)) as F12.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 13 16090547 (pc cs + 52) Hcode eq_refl ltac:(lia)) as F13.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 14 33953683 (pc cs + 56) Hcode eq_refl ltac:(lia)) as F14.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 15 16123443 (pc cs + 60) Hcode eq_refl ltac:(lia)) as F15.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 16 33986451 (pc cs + 64) Hcode eq_refl ltac:(lia)) as F16.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 17 16156339 (pc cs + 68) Hcode eq_refl ltac:(lia)) as F17.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 18 34019219 (pc cs + 72) Hcode eq_refl ltac:(lia)) as F18.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 19 16189235 (pc cs + 76) Hcode eq_refl ltac:(lia)) as F19.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 20 4544403 (pc cs + 80) Hcode eq_refl ltac:(lia)) as F20.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 21 16082227 (pc cs + 84) Hcode eq_refl ltac:(lia)) as F21.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 22 8738707 (pc cs + 88) Hcode eq_refl ltac:(lia)) as F22.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 23 16082227 (pc cs + 92) Hcode eq_refl ltac:(lia)) as F23.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 24 17127315 (pc cs + 96) Hcode eq_refl ltac:(lia)) as F24.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 25 16082227 (pc cs + 100) Hcode eq_refl ltac:(lia)) as F25.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 26 33904531 (pc cs + 104) Hcode eq_refl ltac:(lia)) as F26.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 27 16082227 (pc cs + 108) Hcode eq_refl ltac:(lia)) as F27.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 28 4294264083 (pc cs + 112) Hcode eq_refl ltac:(lia)) as F28.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 29 1398675 (pc cs + 116) Hcode eq_refl ltac:(lia)) as F29.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 30 12055987 (pc cs + 120) Hcode eq_refl ltac:(lia)) as F30.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 31 1085605171 (pc cs + 124) Hcode eq_refl ltac:(lia)) as F31.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 32 12940723 (pc cs + 128) Hcode eq_refl ltac:(lia)) as F32.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 33 2446611 (pc cs + 132) Hcode eq_refl ltac:(lia)) as F33.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 34 12940595 (pc cs + 136) Hcode eq_refl ltac:(lia)) as F34.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 35 10847539 (pc cs + 140) Hcode eq_refl ltac:(lia)) as F35.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 36 4543891 (pc cs + 144) Hcode eq_refl ltac:(lia)) as F36.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 37 11863347 (pc cs + 148) Hcode eq_refl ltac:(lia)) as F37.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 38 13989171 (pc cs + 152) Hcode eq_refl ltac:(lia)) as F38.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 39 48563507 (pc cs + 156) Hcode eq_refl ltac:(lia)) as F39.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 40 59069715 (pc cs + 160) Hcode eq_refl ltac:(lia)) as F40.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 41 1084228923 (pc cs + 164) Hcode eq_refl ltac:(lia)) as F41.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 42 4293920147 (pc cs + 168) Hcode eq_refl ltac:(lia)) as F42.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 43 10851635 (pc cs + 172) Hcode eq_refl ltac:(lia)) as F43.
  pose proof (code_is_at (pc cs) MSBMASK_WORDS 44 4294264083 (pc cs + 176) Hcode eq_refl ltac:(lia)) as F44.
  unfold cfg_of.
  pose proof (TB_init R) as HT.
  mstep HT F0 ME0 MD0 stepacc_shiftimm_gen TB_upd11.   (* [comment removed for export] *)
  mstep HT F1 ME1 MD1 stepacc_lui TB_upd12.   (* [comment removed for export] *)
  mstep HT F2 ME2 MD2 stepacc_lui TB_upd13.   (* [comment removed for export] *)
  mstep HT F3 ME3 MD3 stepacc_lui TB_upd14.   (* [comment removed for export] *)
  mstep HT F4 ME4 MD4 stepacc_lui TB_upd15.   (* [comment removed for export] *)
  mstep HT F5 ME5 MD5 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F6 ME6 MD6 stepacc_opimm32_gen TB_upd11.   (* [comment removed for export] *)
  mstep HT F7 ME7 MD7 stepacc_opimm32_gen TB_upd12.   (* [comment removed for export] *)
  mstep HT F8 ME8 MD8 stepacc_opimm32_gen TB_upd13.   (* [comment removed for export] *)
  mstep HT F9 ME9 MD9 stepacc_opimm32_gen TB_upd14.   (* [comment removed for export] *)
  mstep HT F10 ME10 MD10 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F11 ME11 MD11 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F12 ME12 MD12 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F13 ME13 MD13 stepacc_op_gen TB_upd11.   (* [comment removed for export] *)
  mstep HT F14 ME14 MD14 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F15 ME15 MD15 stepacc_op_gen TB_upd12.   (* [comment removed for export] *)
  mstep HT F16 ME16 MD16 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F17 ME17 MD17 stepacc_op_gen TB_upd13.   (* [comment removed for export] *)
  mstep HT F18 ME18 MD18 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F19 ME19 MD19 stepacc_op_gen TB_upd14.   (* [comment removed for export] *)
  mstep HT F20 ME20 MD20 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F21 ME21 MD21 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F22 ME22 MD22 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F23 ME23 MD23 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F24 ME24 MD24 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F25 ME25 MD25 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F26 ME26 MD26 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F27 ME27 MD27 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (smear_word (getr R 10%bv) Hx) as SW. cbv zeta in SW. rewrite SW in HT. clear SW.
  mstep HT F28 ME28 MD28 stepacc_opimm_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F29 ME29 MD29 stepacc_shiftimm_gen TB_upd15.   (* [comment removed for export] *)
  mstep HT F30 ME30 MD30 stepacc_op_gen TB_upd11.   (* [comment removed for export] *)
  mstep HT F31 ME31 MD31 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F32 ME32 MD32 stepacc_op_gen TB_upd11.   (* [comment removed for export] *)
  mstep HT F33 ME33 MD33 stepacc_shiftimm_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F34 ME34 MD34 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F35 ME35 MD35 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F36 ME36 MD36 stepacc_shiftimm_gen TB_upd11.   (* [comment removed for export] *)
  mstep HT F37 ME37 MD37 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F38 ME38 MD38 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F39 ME39 MD39 stepacc_mul_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F40 ME40 MD40 stepacc_shiftimm_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F41 ME41 MD41 stepacc_op32_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F42 ME42 MD42 stepacc_opimm_gen TB_upd11.   (* [comment removed for export] *)
  mstep HT F43 ME43 MD43 stepacc_op_gen TB_upd10.   (* [comment removed for export] *)
  mstep HT F44 ME44 MD44 stepacc_opimm_gen TB_upd10.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (pc cs + 176 + 4) with (pc cs + 180) by lia.
  lazymatch goal with |- srealizes _ (mkCfg (mkst ?Rf _ _ _) _) _ =>
    apply (Hk E Rf FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))); [|reflexivity] end.
  destruct HC; constructor; cbn [with_ss mk_ss a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset s_next]; try assumption.
  2: reflexivity.
  intros r. unfold sr_get. destruct (bv_eqb r 0%bv) eqn:Hr0.
  { unfold getr. rewrite Hr0. reflexivity. }
  rewrite !nth_sr_upd.
  Ltac regcase r rr E HT GET :=
    apply Nat.eqb_eq in E;
    let Heq := fresh in
    assert (Heq : r = rr); [apply bv_eq; unfold ridx in E; let z := eval cbv in (bv_unsigned rr) in replace (bv_unsigned rr) with z by reflexivity; lia|]; subst r;
    rewrite (GET _ _ _ _ _ _ _ _ HT), edenot_lit; apply bv_eq; vm_compute; reflexivity.
  destruct (Nat.eqb (ridx r) 15) eqn:E15. { regcase r (15%bv : bv 5) E15 HT TB_get15. }
  destruct (Nat.eqb (ridx r) 14) eqn:E14. { regcase r (14%bv : bv 5) E14 HT TB_get14. }
  destruct (Nat.eqb (ridx r) 13) eqn:E13. { regcase r (13%bv : bv 5) E13 HT TB_get13. }
  destruct (Nat.eqb (ridx r) 12) eqn:E12. { regcase r (12%bv : bv 5) E12 HT TB_get12. }
  destruct (Nat.eqb (ridx r) 11) eqn:E11. { regcase r (11%bv : bv 5) E11 HT TB_get11. }
  destruct (Nat.eqb (ridx r) 10) eqn:E10. { regcase r (10%bv : bv 5) E10 HT TB_get10. }
  rewrite (TB_frame _ _ _ _ _ _ _ _ HT r); try (intros ->; cbv in E10, E11, E12, E13, E14, E15; congruence).
  pose proof (HR r) as X. unfold sr_get in X. rewrite Hr0 in X. exact X.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma XN_asan_other : forall id args cs, id <> 200%nat -> id <> 202%nat -> XN_asan SEGS nx0 id args cs = None.
Proof.
  intros id args cs H1 H2. unfold XN_asan.
  do 203 (destruct id as [|id]; [first [reflexivity | exfalso; congruence | destruct args; reflexivity] |]).
  reflexivity.
Qed.

#[using="argH_agree SINV_agree cs_ok_agree' hid_agree'"] Theorem node_ext_sound : ext_stmt SEGS A nx0 LIMIT (XN_asan SEGS nx0) SP0 SINV argH FS0.
Proof.
  intros id args cs cs' E R FULL model T HC Hpre Hn Hk.
  destruct (Nat.eq_dec id 200) as [->|N1].
  { cbv beta iota delta [XN_asan] in Hn.
    destruct args as [|[b| | | | | | |] args1]; cbv beta iota in Hn; try discriminate Hn.
    destruct args1 as [|[n| | | | | | |] args2]; cbv beta iota in Hn; try discriminate Hn.
    destruct args2; cbv beta iota in Hn; [|discriminate Hn].
    exact (node_imgword_sound b (Z.to_nat n) cs cs' E R FULL model T HC Hpre Hn Hk). }
  destruct (Nat.eq_dec id 202) as [->|N2].
  { cbv beta iota delta [XN_asan] in Hn.
    destruct args; cbv beta iota in Hn; [|discriminate Hn].
    exact (node_msbmask_sound cs cs' E R FULL model T HC Hpre Hn Hk). }
  rewrite (XN_asan_other id args cs N1 N2) in Hn. discriminate Hn.
Qed.
End Sound.

Theorem node_ext_sound_OBL : ltac2:(CDefT.buildp (gd_tbl_AsanExtNodesSound ()) "PSEGS,(1=.$3=.)PA,$3>.Pnx0,$1>.PLIMIT,$0.PSP0,$0.PSINV,Px,$3?.Px0,P,(<.&40.)(20.(<.&8.))SpPargH,Px,$3?.Px0,(<.&40.)$3.PFS0,$40.P,PE,$3?.PE',$3?.Pa,(<.&40.)P,(41.R9.R3.R2.)(2.$3.A2.R6.R4.R2.A2.R6.R3.R2.)P,PE,$3?.PE',$3?.PM,P,(<.&40.)(20.(<.&8.))P,(41.R:.R3.R2.)P,A2.R8.R4.R2.A2.R9.R4.R3.(42.R:.R9.R8.R7.(43.R:.R8.)R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros. eapply node_ext_sound; eauto. Qed.
