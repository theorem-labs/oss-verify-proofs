(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec StepTac SeqExec CatExec StoreOk CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSWord AsanSLibc AsanSMat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Definition MIZ_WORDS : list (Z * Z) :=
  [(0x0, 0xff010113); (0x4, 0x00113423); (0x8, 0x00058693); (0xc, 0x00100713); (0x10, 0x02871713);
   (0x14, 0x00170593); (0x18, 0x08b6f263); (0x1c, 0x00000593); (0x20, 0x00d50733); (0x24, 0x00750793);
   (0x28, 0xff87f793); (0x2c, 0xff877613); (0x30, 0x02f57463); (0x34, 0x02068263); (0x38, 0x00000593);
   (0x3c, 0x00150693); (0x40, 0x00068813); (0x44, 0xfff6c683); (0x48, 0x00d5e5b3); (0x4c, 0x00f87663);
   (0x50, 0x00180693); (0x54, 0xfee866e3); (0x58, 0x00c7fa63); (0x5c, 0x0007b683); (0x60, 0x00878793);
   (0x64, 0x00b6e5b3); (0x68, 0xfec7eae3); (0x6c, 0x02a66063); (0x70, 0x00e67e63); (0x74, 0x40c70733);
   (0x78, 0x00064503); (0x7c, 0xfff70713); (0x80, 0x00a5e5b3); (0x84, 0x00160613); (0x88, 0xfe0718e3);
   (0x8c, 0x0015b513); (0x90, 0x00813083); (0x94, 0x01010113); (0x98, 0x00008067)]%Z.

Lemma D_0 : decode_any (Z_to_bv 32 0xff010113) = Some (OpImm ALU_ADD 2 2 4080, 4%Z). Proof. wdec. Qed.
Lemma D_4 : decode_any (Z_to_bv 32 0x00113423) = Some (Store SZ8 2 1 8, 4%Z). Proof. wdec. Qed.
Lemma D_8 : decode_any (Z_to_bv 32 0x00058693) = Some (OpImm ALU_ADD 13 11 0, 4%Z). Proof. wdec. Qed.
Lemma D_c : decode_any (Z_to_bv 32 0x00100713) = Some (OpImm ALU_ADD 14 0 1, 4%Z). Proof. wdec. Qed.
Lemma D_10 : decode_any (Z_to_bv 32 0x02871713) = Some (ShiftImm ALU_SLL 14 14 40, 4%Z). Proof. wdec. Qed.
Lemma D_14 : decode_any (Z_to_bv 32 0x00170593) = Some (OpImm ALU_ADD 11 14 1, 4%Z). Proof. wdec. Qed.
Lemma D_18 : decode_any (Z_to_bv 32 0x08b6f263) = Some (Branch BC_GEU 13 11 132, 4%Z). Proof. wdec. Qed.
Lemma D_1c : decode_any (Z_to_bv 32 0x00000593) = Some (OpImm ALU_ADD 11 0 0, 4%Z). Proof. wdec. Qed.
Lemma D_20 : decode_any (Z_to_bv 32 0x00d50733) = Some (Op ALU_ADD 14 10 13, 4%Z). Proof. wdec. Qed.
Lemma D_24 : decode_any (Z_to_bv 32 0x00750793) = Some (OpImm ALU_ADD 15 10 7, 4%Z). Proof. wdec. Qed.
Lemma D_28 : decode_any (Z_to_bv 32 0xff87f793) = Some (OpImm ALU_AND 15 15 4088, 4%Z). Proof. wdec. Qed.
Lemma D_2c : decode_any (Z_to_bv 32 0xff877613) = Some (OpImm ALU_AND 12 14 4088, 4%Z). Proof. wdec. Qed.
Lemma D_30 : decode_any (Z_to_bv 32 0x02f57463) = Some (Branch BC_GEU 10 15 40, 4%Z). Proof. wdec. Qed.
Lemma D_34 : decode_any (Z_to_bv 32 0x02068263) = Some (Branch BC_EQ 13 0 36, 4%Z). Proof. wdec. Qed.
Lemma D_38 : decode_any (Z_to_bv 32 0x00000593) = Some (OpImm ALU_ADD 11 0 0, 4%Z). Proof. wdec. Qed.
Lemma D_3c : decode_any (Z_to_bv 32 0x00150693) = Some (OpImm ALU_ADD 13 10 1, 4%Z). Proof. wdec. Qed.
Lemma D_40 : decode_any (Z_to_bv 32 0x00068813) = Some (OpImm ALU_ADD 16 13 0, 4%Z). Proof. wdec. Qed.
Lemma D_44 : decode_any (Z_to_bv 32 0xfff6c683) = Some (Load SZ1 false 13 13 4095, 4%Z). Proof. wdec. Qed.
Lemma D_48 : decode_any (Z_to_bv 32 0x00d5e5b3) = Some (Op ALU_OR 11 11 13, 4%Z). Proof. wdec. Qed.
Lemma D_4c : decode_any (Z_to_bv 32 0x00f87663) = Some (Branch BC_GEU 16 15 12, 4%Z). Proof. wdec. Qed.
Lemma D_50 : decode_any (Z_to_bv 32 0x00180693) = Some (OpImm ALU_ADD 13 16 1, 4%Z). Proof. wdec. Qed.
Lemma D_54 : decode_any (Z_to_bv 32 0xfee866e3) = Some (Branch BC_LTU 16 14 8172, 4%Z). Proof. wdec. Qed.
Lemma D_58 : decode_any (Z_to_bv 32 0x00c7fa63) = Some (Branch BC_GEU 15 12 20, 4%Z). Proof. wdec. Qed.
Lemma D_5c : decode_any (Z_to_bv 32 0x0007b683) = Some (Load SZ8 true 13 15 0, 4%Z). Proof. wdec. Qed.
Lemma D_60 : decode_any (Z_to_bv 32 0x00878793) = Some (OpImm ALU_ADD 15 15 8, 4%Z). Proof. wdec. Qed.
Lemma D_64 : decode_any (Z_to_bv 32 0x00b6e5b3) = Some (Op ALU_OR 11 13 11, 4%Z). Proof. wdec. Qed.
Lemma D_68 : decode_any (Z_to_bv 32 0xfec7eae3) = Some (Branch BC_LTU 15 12 8180, 4%Z). Proof. wdec. Qed.
Lemma D_6c : decode_any (Z_to_bv 32 0x02a66063) = Some (Branch BC_LTU 12 10 32, 4%Z). Proof. wdec. Qed.
Lemma D_70 : decode_any (Z_to_bv 32 0x00e67e63) = Some (Branch BC_GEU 12 14 28, 4%Z). Proof. wdec. Qed.
Lemma D_74 : decode_any (Z_to_bv 32 0x40c70733) = Some (Op ALU_SUB 14 14 12, 4%Z). Proof. wdec. Qed.
Lemma D_78 : decode_any (Z_to_bv 32 0x00064503) = Some (Load SZ1 false 10 12 0, 4%Z). Proof. wdec. Qed.
Lemma D_7c : decode_any (Z_to_bv 32 0xfff70713) = Some (OpImm ALU_ADD 14 14 4095, 4%Z). Proof. wdec. Qed.
Lemma D_80 : decode_any (Z_to_bv 32 0x00a5e5b3) = Some (Op ALU_OR 11 11 10, 4%Z). Proof. wdec. Qed.
Lemma D_84 : decode_any (Z_to_bv 32 0x00160613) = Some (OpImm ALU_ADD 12 12 1, 4%Z). Proof. wdec. Qed.
Lemma D_88 : decode_any (Z_to_bv 32 0xfe0718e3) = Some (Branch BC_NE 14 0 8176, 4%Z). Proof. wdec. Qed.
Lemma D_8c : decode_any (Z_to_bv 32 0x0015b513) = Some (OpImm ALU_SLTU 10 11 1, 4%Z). Proof. wdec. Qed.
Lemma D_90 : decode_any (Z_to_bv 32 0x00813083) = Some (Load SZ8 true 1 2 8, 4%Z). Proof. wdec. Qed.
Lemma D_94 : decode_any (Z_to_bv 32 0x01010113) = Some (OpImm ALU_ADD 2 2 16, 4%Z). Proof. wdec. Qed.
Lemma D_98 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. wdec. Qed.

(* [comment removed for export] *)
Definition MF (S S' : machine_state) (rs : list reg) (m : word -> option byte) : Prop :=
  ms_svc_pending S' = None /\ ms_rom S' = ms_rom S /\ ms_fregs S' = ms_fregs S /\ ms_fcsr S' = ms_fcsr S /\
  (ms_resv S' = ms_resv S \/ ms_resv S' = None) /\ (forall r, ~ In r rs -> rg S' r = rg S r) /\ ms_mem S' = m.

Lemma MF_setxn : forall S S1 rs m rd v p r mem',
  MF S S1 rs m -> (rd = 0 \/ In rd rs) -> (r = ms_resv S1 \/ exists a, r = inval a (ms_resv S1)) -> mem' = ms_mem S1 ->
  MF S (setx S1 rd v p r mem') rs m.
Proof.
  intros S S1 rs m rd v p r mem' (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hrd Hr ->.
  split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split.
  - rewrite resv_setx. destruct Hr as [->|(a & ->)]; [exact H5|].
    destruct (inval_cases a (ms_resv S1)) as [E|E]; rewrite E; [exact H5 | right; reflexivity].
  - split; [|exact H7].
    intros r0 Hr0. rewrite <- (H6 r0 Hr0).
    destruct Hrd as [->|Hin]; [apply rg_setx_x0|].
    apply rg_setx_other. intros ->. exact (Hr0 Hin).
Qed.

Ltac mfs HF :=
  repeat first [ exact HF
               | apply MF_setxn; [ | first [ left; reflexivity | right; memb ]
                                   | first [ left; reflexivity | right; eexists; reflexivity ] | reflexivity ] ].

(* [comment removed for export] *)
Definition MZC : list reg := [2; 10; 11; 12; 13; 14; 15; 16].
Definition MZCLOB : list reg := [10; 11; 12; 13; 14; 15; 16].

Lemma andm8 : forall x : word, alu64 ALU_AND x (sext 64 (@BV 12 4088 I)) = Z_to_bv 64 (bv_unsigned x / 8 * 8).
Proof.
  intros x. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned. rewrite sext64_Z_to_bv.
  change (bv_signed (@BV 12 4088 I)) with (-8)%Z.
  pose proof (u64_range x) as R.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 (bv_unsigned x / 8 * 8)) by (change (bv_modulus 64) with (2 ^ 64)%Z;
    pose proof (Z.mul_div_le (bv_unsigned x) 8 ltac:(lia)); pose proof (Z.div_pos (bv_unsigned x) 8 ltac:(lia) ltac:(lia)); lia).
  assert (E : Z.land (bv_unsigned x) (bv_wrap 64 (-8)) = Z.land (bv_unsigned x) (Z.lnot (Z.ones 3))).
  { apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
    destruct (Z_lt_ge_dec n 64).
    - unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
    - rewrite (Z_testbit_high 64 (bv_unsigned x) n) by lia. reflexivity. }
  rewrite E, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma zero_or : forall x : word, alu64 ALU_OR w0 x = x.
Proof. intros x. apply bv_eq. cbn [alu64 alu]. rewrite bv_or_unsigned. unfold w0. rewrite bvu_z by lia. reflexivity. Qed.
Lemma or_zero : forall x : word, alu64 ALU_OR x w0 = x.
Proof. intros x. apply bv_eq. cbn [alu64 alu]. rewrite bv_or_unsigned. unfold w0. rewrite bvu_z by lia. apply Z.lor_0_r. Qed.

Lemma zbyte_w0 : Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)) = w0.
Proof. reflexivity. Qed.

Lemma ld_zero8 : forall l : list byte, length l = 8%nat -> (forall i, (i < 8)%nat -> nth i l (Z_to_bv 8 0) = Z_to_bv 8 0) ->
  load_word SZ8 true l = w0.
Proof.
  intros l Hl H. destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|]]]]]]]]]; try discriminate Hl.
  pose proof (H 0%nat ltac:(lia)) as E0. pose proof (H 1%nat ltac:(lia)) as E1.
  pose proof (H 2%nat ltac:(lia)) as E2. pose proof (H 3%nat ltac:(lia)) as E3.
  pose proof (H 4%nat ltac:(lia)) as E4. pose proof (H 5%nat ltac:(lia)) as E5.
  pose proof (H 6%nat ltac:(lia)) as E6. pose proof (H 7%nat ltac:(lia)) as E7.
  cbn [nth] in E0, E1, E2, E3, E4, E5, E6, E7. subst. reflexivity.
Qed.

Section Miz.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable b : Z.
Hypothesis HW : words_ok segs b MIZ_WORDS = true.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs b MIZ_WORDS); [exact HW | inw | lia].

Lemma F_0 : fetch_word segs (pcw b 0x0) = Some (Z_to_bv 32 0xff010113). Proof. fw. Qed.
Lemma F_4 : fetch_word segs (pcw b 0x4) = Some (Z_to_bv 32 0x00113423). Proof. fw. Qed.
Lemma F_8 : fetch_word segs (pcw b 0x8) = Some (Z_to_bv 32 0x00058693). Proof. fw. Qed.
Lemma F_c : fetch_word segs (pcw b 0xc) = Some (Z_to_bv 32 0x00100713). Proof. fw. Qed.
Lemma F_10 : fetch_word segs (pcw b 0x10) = Some (Z_to_bv 32 0x02871713). Proof. fw. Qed.
Lemma F_14 : fetch_word segs (pcw b 0x14) = Some (Z_to_bv 32 0x00170593). Proof. fw. Qed.
Lemma F_18 : fetch_word segs (pcw b 0x18) = Some (Z_to_bv 32 0x08b6f263). Proof. fw. Qed.
Lemma F_1c : fetch_word segs (pcw b 0x1c) = Some (Z_to_bv 32 0x00000593). Proof. fw. Qed.
Lemma F_20 : fetch_word segs (pcw b 0x20) = Some (Z_to_bv 32 0x00d50733). Proof. fw. Qed.
Lemma F_24 : fetch_word segs (pcw b 0x24) = Some (Z_to_bv 32 0x00750793). Proof. fw. Qed.
Lemma F_28 : fetch_word segs (pcw b 0x28) = Some (Z_to_bv 32 0xff87f793). Proof. fw. Qed.
Lemma F_2c : fetch_word segs (pcw b 0x2c) = Some (Z_to_bv 32 0xff877613). Proof. fw. Qed.
Lemma F_30 : fetch_word segs (pcw b 0x30) = Some (Z_to_bv 32 0x02f57463). Proof. fw. Qed.
Lemma F_34 : fetch_word segs (pcw b 0x34) = Some (Z_to_bv 32 0x02068263). Proof. fw. Qed.
Lemma F_38 : fetch_word segs (pcw b 0x38) = Some (Z_to_bv 32 0x00000593). Proof. fw. Qed.
Lemma F_3c : fetch_word segs (pcw b 0x3c) = Some (Z_to_bv 32 0x00150693). Proof. fw. Qed.
Lemma F_40 : fetch_word segs (pcw b 0x40) = Some (Z_to_bv 32 0x00068813). Proof. fw. Qed.
Lemma F_44 : fetch_word segs (pcw b 0x44) = Some (Z_to_bv 32 0xfff6c683). Proof. fw. Qed.
Lemma F_48 : fetch_word segs (pcw b 0x48) = Some (Z_to_bv 32 0x00d5e5b3). Proof. fw. Qed.
Lemma F_4c : fetch_word segs (pcw b 0x4c) = Some (Z_to_bv 32 0x00f87663). Proof. fw. Qed.
Lemma F_50 : fetch_word segs (pcw b 0x50) = Some (Z_to_bv 32 0x00180693). Proof. fw. Qed.
Lemma F_54 : fetch_word segs (pcw b 0x54) = Some (Z_to_bv 32 0xfee866e3). Proof. fw. Qed.
Lemma F_58 : fetch_word segs (pcw b 0x58) = Some (Z_to_bv 32 0x00c7fa63). Proof. fw. Qed.
Lemma F_5c : fetch_word segs (pcw b 0x5c) = Some (Z_to_bv 32 0x0007b683). Proof. fw. Qed.
Lemma F_60 : fetch_word segs (pcw b 0x60) = Some (Z_to_bv 32 0x00878793). Proof. fw. Qed.
Lemma F_64 : fetch_word segs (pcw b 0x64) = Some (Z_to_bv 32 0x00b6e5b3). Proof. fw. Qed.
Lemma F_68 : fetch_word segs (pcw b 0x68) = Some (Z_to_bv 32 0xfec7eae3). Proof. fw. Qed.
Lemma F_6c : fetch_word segs (pcw b 0x6c) = Some (Z_to_bv 32 0x02a66063). Proof. fw. Qed.
Lemma F_70 : fetch_word segs (pcw b 0x70) = Some (Z_to_bv 32 0x00e67e63). Proof. fw. Qed.
Lemma F_74 : fetch_word segs (pcw b 0x74) = Some (Z_to_bv 32 0x40c70733). Proof. fw. Qed.
Lemma F_78 : fetch_word segs (pcw b 0x78) = Some (Z_to_bv 32 0x00064503). Proof. fw. Qed.
Lemma F_7c : fetch_word segs (pcw b 0x7c) = Some (Z_to_bv 32 0xfff70713). Proof. fw. Qed.
Lemma F_80 : fetch_word segs (pcw b 0x80) = Some (Z_to_bv 32 0x00a5e5b3). Proof. fw. Qed.
Lemma F_84 : fetch_word segs (pcw b 0x84) = Some (Z_to_bv 32 0x00160613). Proof. fw. Qed.
Lemma F_88 : fetch_word segs (pcw b 0x88) = Some (Z_to_bv 32 0xfe0718e3). Proof. fw. Qed.
Lemma F_8c : fetch_word segs (pcw b 0x8c) = Some (Z_to_bv 32 0x0015b513). Proof. fw. Qed.
Lemma F_90 : fetch_word segs (pcw b 0x90) = Some (Z_to_bv 32 0x00813083). Proof. fw. Qed.
Lemma F_94 : fetch_word segs (pcw b 0x94) = Some (Z_to_bv 32 0x01010113). Proof. fw. Qed.
Lemma F_98 : fetch_word segs (pcw b 0x98) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.

Section Loop.
Variable model0 : Model.
Hypothesis Hh0 : m_halted model0 = None.
Variable ms0 : machine_state.
Variable T : TSet.
Variable beg : word.
Variable size : Z.
Local Notation B := (bv_unsigned beg).
Local Notation E := (bv_unsigned beg + size)%Z.
(* [comment removed for export] *)
Definition ab : Z := ((bv_unsigned beg + 7) / 8 * 8)%Z.
Definition ae : Z := ((bv_unsigned beg + size) / 8 * 8)%Z.
Local Notation AB := ab.
Local Notation AE := ae.
Variable sp0 : word.
Hypothesis Hsz : (0 <= size <= 2 ^ 40)%Z.
Hypothesis Hnw : (bv_unsigned beg + size + 8 <= 2 ^ 64)%Z.
Hypothesis Hz : forall i, (0 <= i < size)%Z -> bat segs (ms_mem ms0) (beg + Z_to_bv 64 i) = Some (Z_to_bv 8 0).
Hypothesis Hbud : (vm_backing_used model0 + 4096 * size <= vm_limit (m_vmmaps model0))%Z.
Hypothesis Hsp : (16 <= bv_unsigned sp0)%Z.
Hypothesis Hok : store_ok segs (ms_mem ms0) (Z_to_bv 64 (bv_unsigned sp0 - 8)) 8 = true.
Hypothesis Hnls : no_lazy model0 (bv_unsigned sp0 - 8) (bv_unsigned sp0).
Hypothesis Hdisj : (bv_unsigned sp0 <= bv_unsigned beg \/ bv_unsigned beg + size <= bv_unsigned sp0 - 8)%Z.
Hypothesis H2 : rg ms0 2 = sp0.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Local Notation M1 := (write_to_mem (ms_mem ms0) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (store_bytes SZ8 (rg ms0 1))).
Hypothesis HK : forall ms' model', MF ms0 ms' MZCLOB M1 -> ms_pc_val ms' = rg ms0 1 -> rg ms' 10 = Z_to_bv 64 1 ->
  mat_of model0 model' size -> realizes_cfg segs cfg (mkCfg ms' model') T.

Lemma br_ltu_zw : forall (a : word) x, (0 <= x < 2 ^ 64)%Z -> branch_taken BC_LTU (Z_to_bv 64 x) a = (x <? bv_unsigned a)%Z.
Proof. intros a x Hx. pose proof (u64_range a). rewrite <- (Z_to_bv_u a) at 1. apply branch_ltu_z; lia. Qed.

Lemma ld_st8 : forall v : word, load_word SZ8 true (store_bytes SZ8 v) = v.
Proof. intros v. exact (load8 true v). Qed.

(* [comment removed for export] *)
Definition BI (k : Z) (ms : machine_state) (model : Model) : Prop :=
  MF ms0 ms MZC M1 /\ rg ms 2 = Z_to_bv 64 (bv_unsigned sp0 - 16) /\ mat_of model0 model k /\ (0 <= k)%Z.

Lemma u_sp0 : (0 <= bv_unsigned sp0 < 2 ^ 64)%Z.
Proof. pose proof (bv_unsigned_in_range 64 sp0) as R. change (bv_modulus 64) with (2 ^ 64)%Z in R. exact R. Qed.
Lemma u_beg : (0 <= bv_unsigned beg < 2 ^ 64)%Z.
Proof. pose proof (bv_unsigned_in_range 64 beg) as R. change (bv_modulus 64) with (2 ^ 64)%Z in R. exact R. Qed.

(* [comment removed for export] *)
Lemma M1_range : forall i, (0 <= i < size)%Z -> bat segs M1 (beg + Z_to_bv 64 i) = Some (Z_to_bv 8 0).
Proof.
  intros i Hi. pose proof u_sp0. pose proof u_beg. unfold bat.
  rewrite w2m_outside.
  - exact (Hz i Hi).
  - rewrite store_bytes8_len. rewrite bvu_z by lia. lia.
  - rewrite store_bytes8_len. rewrite bvu_z by lia. rewrite u_add_small by lia. lia.
Qed.

Lemma rd1z : forall i, (0 <= i < size)%Z -> rdn segs M1 (beg + Z_to_bv 64 i) 1 = Some [Z_to_bv 8 0].
Proof. intros i Hi. apply rdn_1. apply M1_range. exact Hi. Qed.

Lemma rd8z : forall i, (0 <= i)%Z -> (i + 8 <= size)%Z ->
  exists l, rdn segs M1 (beg + Z_to_bv 64 i) 8 = Some l /\ load_word SZ8 true l = w0.
Proof.
  intros i Hi Hi8.
  destruct (rdn_of_bats segs M1 8 (beg + Z_to_bv 64 i)) as [l [Hl Hlen]].
  { intros j Hj. exists (Z_to_bv 8 0). rewrite w_add_assoc. apply M1_range. lia. }
  exists l. split; [exact Hl|]. apply ld_zero8; [exact Hlen|].
  intros j Hj. pose proof (bat_of_rdn segs M1 8 _ l j Hl Hj) as H1.
  rewrite w_add_assoc, M1_range in H1 by lia. injection H1 as <-. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma b_r : forall k ms model, BI k ms model -> (k <= size)%Z ->
  ms_pc_val ms = pcw b 0x8c -> rg ms 11 = w0 -> realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros k ms model (HF & Hsp16 & Hmat & Hk0) Hk Hpc H11.
  pose proof HF as (Hsvc & _ & _ & _ & _ & HR & Hmem). pose proof u_sp0.
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model k Hmat); exact Hh0).
  wsx wacc_OpImm F_8c D_8c. rgn. rewrite H11. cbn [alu64 alu].
  unfold bv_ltu. rewrite sext64_Z_to_bv. change (bv_signed (@BV 12 1 I)) with 1%Z. unfold w0. rewrite !bvu_z by lia.
  cbn [Z.ltb Z.compare].
  eapply rzc_acc; [ assumption | reflexivity
    | eapply wacc_Load; [ fetch_tac F_90 | reflexivity | exact D_90 | ] | | ].
  - rgn. rewrite Hsp16, zw_add_sext. lits. rewrite ?mem_setx, Hmem.
    replace (bv_unsigned sp0 - 16 + 8)%Z with (bv_unsigned sp0 - 8)%Z by lia.
    rewrite write_to_mem_wbytes. cbn [msz_n].
    exact (rdn_wbytes_hit segs (store_bytes SZ8 (rg ms0 1)) (ms_mem ms0) (Z_to_bv 64 (bv_unsigned sp0 - 8))
             ltac:(rewrite store_bytes8_len, bvu_z by lia; lia)).
  - apply acc_ok_one; rgn; rewrite Hsp16, zw_add_sext; lits; cbn [msz_n];
      replace (bv_unsigned sp0 - 16 + 8)%Z with (bv_unsigned sp0 - 8)%Z by lia; rewrite bvu_z by lia.
    + lia.
    + apply (no_lazy_mat model0 model k); [exact Hmat|]. replace (bv_unsigned sp0 - 8 + Z.of_nat 8)%Z with (bv_unsigned sp0) by lia. exact Hnls.
  - pcn; nrm. rewrite ld_st8.
    wsx wacc_OpImm F_94 D_94. rgn. rewrite Hsp16, alu_add, zw_add_sext. lits.
    replace (bv_unsigned sp0 - 16 + 16)%Z with (bv_unsigned sp0) by lia. rewrite Z_to_bv_u.
    eapply rzc_acc; [ assumption | reflexivity
      | eapply wacc_Jalr; [ fetch_tac F_98 | reflexivity | exact D_98 ] | apply acc_ok_nil | ].
    rgn. rewrite ?pc_setx, ret_even by exact Hra.
    apply HK.
    + split; [reflexivity|]. split; [exact (proj1 (proj2 HF))|]. split; [exact (proj1 (proj2 (proj2 HF)))|].
      split; [exact (proj1 (proj2 (proj2 (proj2 HF))))|]. split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 HF)))))|].
      split; [|exact Hmem].
      intros r Hr. rewrite rg_setx_x0.
      destruct (bv_eq_dec 5 r 2) as [->|N2]; [rewrite rg_setx_same by reflexivity; exact (eq_sym H2)|].
      rewrite rg_setx_other by exact N2.
      destruct (bv_eq_dec 5 r 1) as [->|N1]; [rewrite rg_setx_same by reflexivity; reflexivity|].
      rewrite rg_setx_other by exact N1.
      rewrite rg_setx_other by (intros ->; apply Hr; cbn; tauto).
      apply HR. intros Hin. cbn in Hin. destruct Hin as [X|Hin]; [exact (N2 (eq_sym X))|]. apply Hr. exact Hin.
    + reflexivity.
    + rgn. reflexivity.
    + apply (mat_of_mono model0 model k); [exact Hmat | exact Hk].
Qed.

Lemma wacc_Load_at : forall ms w isz sz sg rd rs1 (imm : bv 12) bs (a : word),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, isz) ->
  rg ms rs1 + sext 64 imm = a ->
  rdn segs (ms_mem ms) a (msz_n sz) = Some bs ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (load_word sz sg bs)
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) [(a, msz_n sz)]).
Proof. intros ms w isz sz sg rd rs1 imm bs a Hf He Hd Ha Hr. subst a. exact (wacc_Load segs ms w isz sz sg rd rs1 imm bs Hf He Hd Hr). Qed.

Lemma u_bq : forall q, (0 <= q <= size + 7)%Z -> bv_unsigned (beg + Z_to_bv 64 q) = (bv_unsigned beg + q)%Z.
Proof. intros q Hq. pose proof u_beg. apply u_add_small; lia. Qed.

Lemma pg1 : forall (a : word), (bv_unsigned a mod 4096 + Z.of_nat 1 <= 4096)%Z.
Proof. intros a. pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)). lia. Qed.

Lemma pg8 : forall (a : word), (bv_unsigned a mod 8 = 0)%Z -> (bv_unsigned a mod 4096 + Z.of_nat 8 <= 4096)%Z.
Proof.
  intros a H. assert (Ha8 : (bv_unsigned a = 8 * (bv_unsigned a / 8))%Z) by (pose proof (Z.div_mod (bv_unsigned a) 8 ltac:(lia)); lia).
  rewrite Ha8. change 4096%Z with (8 * 512)%Z. rewrite Z.mul_mod_distr_l by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned a / 8) 512 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Ltac wlz F D q Hmat Hm' Hmem :=
  eapply rzc_mat;
  [ assumption | first [ reflexivity | assumption ]
  | eapply (wacc_Load_at _ _ _ _ _ _ _ _ _ (beg + Z_to_bv 64 q));
    [ fetch_tac F | reflexivity | exact D | | rewrite ?mem_setx, ?Hmem; apply rd1z; lia ]
  | exact Hm'
  | ].

(* [comment removed for export] *)
Lemma tl_loop : forall d q k ms model, (q + Z.of_nat (S d) = size)%Z -> (0 <= q)%Z -> (k <= q)%Z ->
  BI k ms model -> ms_pc_val ms = pcw b 0x78 -> rg ms 11 = w0 -> rg ms 12 = beg + Z_to_bv 64 q ->
  rg ms 14 = Z_to_bv 64 (size - q) -> realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  induction d as [|d IH]; intros q k ms model Hqd Hq0 Hk HBI Hpc H11 H12 H14;
    pose proof HBI as (HF & Hsp16 & Hmat & Hk0); pose proof HF as (Hsvc & _ & _ & _ & _ & HR & Hmem);
    assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model k Hmat); exact Hh0);
    destruct (mat_step model0 model k (beg + Z_to_bv 64 q) 1 Hmat ltac:(lia) (pg1 _) ltac:(lia)) as (model' & Hm' & Hmat');
    pose proof (mat_of_halted model0 model' (k + 1) Hmat') as Hh'; rewrite Hh0 in Hh'.
  all: wlz F_78 D_78 q Hmat Hm' Hmem.
  all: try (rgn; rewrite H12, add_sext0; reflexivity).
  all: try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn; nrm; rewrite lbu_val, zbyte_w0.
  all: wsx wacc_OpImm F_7c D_7c. all: rgn. all: rewrite H14, alu_add, zw_add_sext. all: lits.
  all: wsx wacc_Op F_80 D_80. all: rgn. all: rewrite H11, zero_or.
  all: wsx wacc_OpImm F_84 D_84. all: rgn. all: rewrite H12, alu_add, w_add_sext_z. all: lits.
  all: wsx wacc_Branch F_88 D_88. all: rgn. all: rewrite (br_ne0 (size - q + -1)) by lia.
  - rewrite (proj2 (Z.eqb_eq _ 0%Z)) by lia. cbn [negb]. pcn.
    apply (b_r (k + 1) _ model'); [ | lia | reflexivity | rgn; reflexivity ].
    split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat' | lia]]].
  - rewrite (proj2 (Z.eqb_neq _ 0%Z)) by lia. cbn [negb]. pcn.
    apply (IH (q + 1)%Z (k + 1)%Z _ model'); [ lia | lia | lia | | reflexivity | rgn; reflexivity | rgn; reflexivity | rgn; f_equal; lia ].
    split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat' | lia]]].
Qed.

Lemma AB_facts : (B <= AB <= B + 7)%Z /\ (AB mod 8 = 0)%Z.
Proof.
  unfold ab. pose proof u_beg. pose proof (Z.div_mod (B + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)).
  split; [lia | apply Z.mod_mul; lia].
Qed.
Lemma AE_facts : (E - 7 <= AE <= E)%Z /\ (AE mod 8 = 0)%Z.
Proof.
  unfold ae. pose proof u_beg. pose proof (Z.div_mod E 8 ltac:(lia)). pose proof (Z.mod_pos_bound E 8 ltac:(lia)).
  split; [lia | apply Z.mod_mul; lia].
Qed.
(* [comment removed for export] *)
Lemma al_ge_AB : forall x, (x mod 8 = 0)%Z -> (B <= x)%Z -> (AB <= x)%Z.
Proof.
  intros x Hx HB. pose proof u_beg. unfold ab.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.div_mod (B + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)).
  set (m := (x / 8)%Z) in *. set (n := ((B + 7) / 8)%Z) in *. set (r := ((B + 7) mod 8)%Z) in *.
  assert (n <= m)%Z by lia. lia.
Qed.

Lemma wq : forall q, (0 <= q <= size + 7)%Z -> Z_to_bv 64 (B + q) = beg + Z_to_bv 64 q.
Proof. intros q Hq. apply bv_eq. rewrite u_bq by lia. pose proof u_beg. apply bvu_z. lia. Qed.

(* [comment removed for export] *)
Lemma t_block : forall k ms model, (0 <= k <= size)%Z -> ((B <= AE)%Z -> (k <= AE - B)%Z) ->
  BI k ms model -> ms_pc_val ms = pcw b 0x6c -> rg ms 10 = beg -> rg ms 11 = w0 ->
  rg ms 12 = Z_to_bv 64 AE -> rg ms 14 = Z_to_bv 64 E -> realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros k ms model Hk HkAE HBI Hpc H10 H11 H12 H14.
  pose proof HBI as (HF & Hsp16 & Hmat & Hk0); pose proof HF as (Hsvc & _ & _ & _ & _ & HR & Hmem).
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model k Hmat); exact Hh0).
  pose proof u_beg. pose proof AE_facts as (HAE1 & HAE2).
  wsx wacc_Branch F_6c D_6c. rgn. rewrite H12, H10, br_ltu_zw by lia.
  destruct (Z.ltb_spec AE B) as [Hlt|Hge]; pcn.
  - apply (b_r k _ model); [ | lia | reflexivity | rgn; exact H11 ]. split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat | lia]]].
  - wsx wacc_Branch F_70 D_70. rgn. rewrite H12, H14. rewrite branch_geu_z by lia.
    destruct (Z.ltb_spec AE E) as [Hlt2|Hge2]; cbn [negb]; pcn.
    + wsx wacc_Op F_74 D_74. rgn. rewrite H14, H12, alu_sub, zw_sub.
      apply (tl_loop (Z.to_nat (E - AE - 1)) (AE - B) k _ model); [ lia | lia | lia | | reflexivity | rgn; exact H11
        | rgn; rewrite H12; replace AE with (B + (AE - B))%Z at 1 by lia; apply wq; lia | rgn; f_equal; lia ].
      split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat | lia]]].
    + apply (b_r k _ model); [ | lia | reflexivity | rgn; exact H11 ]. split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat | lia]]].
Qed.

(* [comment removed for export] *)
Lemma wl_loop : forall d w k ms model, (AB + 8 * Z.of_nat w + 8 * Z.of_nat (S d) = AE)%Z -> (0 <= k <= AB - B + Z.of_nat w)%Z ->
  BI k ms model -> ms_pc_val ms = pcw b 0x5c -> rg ms 10 = beg -> rg ms 11 = w0 ->
  rg ms 12 = Z_to_bv 64 AE -> rg ms 14 = Z_to_bv 64 E -> rg ms 15 = Z_to_bv 64 (AB + 8 * Z.of_nat w) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  pose proof AB_facts as (HAB1 & HAB2). pose proof AE_facts as (HAE1 & HAE2). pose proof u_beg.
  induction d as [|d IH]; intros w k ms model Hd Hk HBI Hpc H10 H11 H12 H14 H15;
    pose proof HBI as (HF & Hsp16 & Hmat & Hk0); pose proof HF as (Hsvc & _ & _ & _ & _ & HR & Hmem);
    assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model k Hmat); exact Hh0);
    set (q := (AB - B + 8 * Z.of_nat w)%Z);
    assert (Hq : (0 <= q /\ q + 8 <= size)%Z) by (subst q; lia);
    destruct (rd8z q ltac:(lia) ltac:(lia)) as (l & Hl & Hlw);
    assert (Hal : (bv_unsigned (beg + Z_to_bv 64 q) mod 8 = 0)%Z)
      by (rewrite u_bq by lia; subst q; replace (B + (AB - B + 8 * Z.of_nat w))%Z with (AB + Z.of_nat w * 8)%Z by lia;
          rewrite Z_mod_plus_full; exact HAB2);
    destruct (mat_step model0 model k (beg + Z_to_bv 64 q) 8 Hmat ltac:(lia) (pg8 _ Hal) ltac:(lia)) as (model' & Hm' & Hmat');
    pose proof (mat_of_halted model0 model' (k + 1) Hmat') as Hh'; rewrite Hh0 in Hh'.
  all: eapply rzc_mat; [ assumption | assumption
       | eapply (wacc_Load_at _ _ _ _ _ _ _ _ _ (beg + Z_to_bv 64 q));
         [ fetch_tac F_5c | reflexivity | exact D_5c | rewrite H15, add_sext0; subst q; rewrite <- wq by lia; f_equal; lia
         | rewrite Hmem; exact Hl ]
       | exact Hm' | rewrite Hpc; pcn; nrm; rewrite Hlw ].
  all: wsx wacc_OpImm F_60 D_60. all: rgn. all: rewrite H15, alu_add, zw_add_sext. all: lits.
  all: wsx wacc_Op F_64 D_64. all: rgn. all: rewrite H11, zero_or.
  all: wsx wacc_Branch F_68 D_68. all: rgn. all: rewrite H12. all: rewrite branch_ltu_z by lia.
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia. pcn.
    apply (t_block (k + 1) _ model'); [ lia | lia | | reflexivity | rgn; exact H10 | rgn; reflexivity | rgn; exact H12 | rgn; exact H14 ].
    split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat' | lia]]].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. pcn.
    apply (IH (S w) (k + 1)%Z _ model'); [ lia | lia | | reflexivity | rgn; exact H10 | rgn; reflexivity | rgn; exact H12
      | rgn; exact H14 | rgn; f_equal; lia ].
    split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat' | lia]]].
Qed.

(* [comment removed for export] *)
Lemma w_block : forall k ms model, (0 <= k <= AB - B)%Z -> (k <= size)%Z ->
  BI k ms model -> ms_pc_val ms = pcw b 0x58 -> rg ms 10 = beg -> rg ms 11 = w0 ->
  rg ms 12 = Z_to_bv 64 AE -> rg ms 14 = Z_to_bv 64 E -> rg ms 15 = Z_to_bv 64 AB ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros k ms model Hk Hks HBI Hpc H10 H11 H12 H14 H15.
  pose proof HBI as (HF & Hsp16 & Hmat & Hk0); pose proof HF as (Hsvc & _ & _ & _ & _ & HR & Hmem).
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model k Hmat); exact Hh0).
  pose proof AB_facts as (HAB1 & HAB2). pose proof AE_facts as (HAE1 & HAE2). pose proof u_beg.
  wsx wacc_Branch F_58 D_58. rgn. rewrite H15, H12. rewrite branch_geu_z by lia.
  destruct (Z.ltb_spec AB AE) as [Hlt|Hge]; cbn [negb]; pcn.
  - assert (Hd : exists d, (AB + 8 * Z.of_nat 0 + 8 * Z.of_nat (S d) = AE)%Z).
    { exists (Z.to_nat ((AE - AB) / 8 - 1)).
      assert (Hm : ((AE - AB) mod 8 = 0)%Z) by (rewrite Zminus_mod, HAB2, HAE2; reflexivity).
      pose proof (Z.div_mod (AE - AB) 8 ltac:(lia)). assert (1 <= (AE - AB) / 8)%Z by (apply Z.div_le_lower_bound; lia). lia. }
    destruct Hd as (d & Hd).
    apply (wl_loop d 0 k _ model); [ exact Hd | lia | | reflexivity | rgn; exact H10 | rgn; exact H11 | rgn; exact H12
      | rgn; exact H14 | rgn; rewrite H15; f_equal; lia ].
    split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat | lia]]].
  - apply (t_block k _ model); [ lia | | | reflexivity | rgn; exact H10 | rgn; exact H11 | rgn; exact H12 | rgn; exact H14 ].
    + intros HBAE. pose proof (al_ge_AB AE HAE2 HBAE). lia.
    + split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat | lia]]].
Qed.

(* [comment removed for export] *)
Lemma h_loop : forall d j ms model, (B + j + Z.of_nat (S d) = AB)%Z -> (0 <= j < size)%Z ->
  BI j ms model -> ms_pc_val ms = pcw b 0x40 -> rg ms 10 = beg -> rg ms 11 = w0 ->
  rg ms 12 = Z_to_bv 64 AE -> rg ms 13 = beg + Z_to_bv 64 (j + 1) -> rg ms 14 = Z_to_bv 64 E ->
  rg ms 15 = Z_to_bv 64 AB -> realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  pose proof AB_facts as (HAB1 & HAB2). pose proof AE_facts as (HAE1 & HAE2). pose proof u_beg.
  induction d as [|d IH]; intros j ms model Hd Hj HBI Hpc H10 H11 H12 H13 H14 H15;
    pose proof HBI as (HF & Hsp16 & Hmat & Hk0); pose proof HF as (Hsvc & _ & _ & _ & _ & HR & Hmem);
    assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model j Hmat); exact Hh0);
    destruct (mat_step model0 model j (beg + Z_to_bv 64 j) 1 Hmat ltac:(lia) (pg1 _) ltac:(lia)) as (model' & Hm' & Hmat');
    pose proof (mat_of_halted model0 model' (j + 1) Hmat') as Hh'; rewrite Hh0 in Hh'.
  all: wsx wacc_OpImm F_40 D_40. all: rgn. all: rewrite H13, alu_add, add_sext0.
  all: eapply rzc_mat; [ assumption | reflexivity
       | eapply (wacc_Load_at _ _ _ _ _ _ _ _ _ (beg + Z_to_bv 64 j));
         [ fetch_tac F_44 | reflexivity | exact D_44 | rgn; rewrite H13, w_add_sext_z; lits; f_equal; f_equal; lia
         | rewrite ?mem_setx, Hmem; apply rd1z; lia ]
       | exact Hm' | pcn; nrm; rewrite lbu_val, zbyte_w0 ].
  all: wsx wacc_Op F_48 D_48. all: rgn. all: rewrite H11, zero_or.
  all: wsx wacc_Branch F_4c D_4c. all: rgn. all: rewrite H15. all: rewrite <- (wq (j + 1)) by lia.
  all: rewrite branch_geu_z by lia.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [negb]. pcn.
    apply (w_block (j + 1) _ model'); [ lia | lia | | reflexivity | rgn; exact H10 | rgn; reflexivity | rgn; exact H12
      | rgn; exact H14 | rgn; exact H15 ].
    split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat' | lia]]].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb]. pcn.
    wsx wacc_OpImm F_50 D_50. rgn. rewrite alu_add, zw_add_sext. lits.
    wsx wacc_Branch F_54 D_54. rgn. rewrite H14. rewrite branch_ltu_z by lia.
    destruct (Z.ltb_spec (B + (j + 1)) E) as [Hlt|Hge]; pcn.
    + apply (IH (j + 1)%Z _ model'); [ lia | lia | | reflexivity | rgn; exact H10 | rgn; reflexivity | rgn; exact H12
        | rgn; rewrite <- wq by lia; f_equal; lia | rgn; exact H14 | rgn; exact H15 ].
      split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat' | lia]]].
    + apply (w_block (j + 1) _ model'); [ lia | lia | | reflexivity | rgn; exact H10 | rgn; reflexivity | rgn; exact H12
        | rgn; exact H14 | rgn; exact H15 ].
      split; [mfs HF | split; [rgn; exact Hsp16 | split; [exact Hmat' | lia]]].
Qed.

Lemma br_geu_w : forall (a : word) x, (0 <= x < 2 ^ 64)%Z -> branch_taken BC_GEU a (Z_to_bv 64 x) = negb (bv_unsigned a <? x)%Z.
Proof. intros a x Hx. pose proof (u64_range a). rewrite <- (Z_to_bv_u a) at 1. apply branch_geu_z; lia. Qed.

Lemma sll40 : alu64 ALU_SLL (Z_to_bv 64 1) (zext 64 (@BV 6 40 I)) = Z_to_bv 64 (2 ^ 40).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma miz_entry : ms_svc_pending ms0 = None -> ms_pc_val ms0 = pcw b 0 ->
  rg ms0 10 = beg -> rg ms0 11 = Z_to_bv 64 size -> realizes_cfg segs cfg (mkCfg ms0 model0) T.
Proof.
  intros Hsvc Hpc H10 H11.
  pose proof AB_facts as (HAB1 & HAB2). pose proof AE_facts as (HAE1 & HAE2). pose proof u_beg. pose proof u_sp0.
  wsx wacc_OpImm F_0 D_0. rgn. rewrite H2, alu_add, w_add_sext. lits. rewrite <- (Z_to_bv_u sp0) at 1. rewrite zw_add.
  eapply rzc_acc; [ assumption | reflexivity
    | eapply wacc_Store; [ fetch_tac F_4 | reflexivity | exact D_4 | ] | | ].
  - rgn. rewrite zw_add_sext. lits. replace (bv_unsigned sp0 + -16 + 8)%Z with (bv_unsigned sp0 - 8)%Z by lia.
    cbn [msz_n]. exact Hok.
  - apply acc_ok_one; rgn; rewrite zw_add_sext; lits; replace (bv_unsigned sp0 + -16 + 8)%Z with (bv_unsigned sp0 - 8)%Z by lia;
      cbn [msz_n]; rewrite bvu_z by lia; [ lia | replace (bv_unsigned sp0 - 8 + Z.of_nat 8)%Z with (bv_unsigned sp0) by lia; exact Hnls ].
  - pcn; nrm. rgn. rewrite zw_add_sext. lits. replace (bv_unsigned sp0 + -16 + 8)%Z with (bv_unsigned sp0 - 8)%Z by lia.
    match goal with |- realizes_cfg _ _ (mkCfg ?S _) _ => assert (HF1 : MF ms0 S MZC M1) end.
    { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [cbn [ms_resv setx]; destruct (inval_cases (Z_to_bv 64 (bv_unsigned sp0 - 8)) (ms_resv ms0)) as [X|X]; rewrite X;
              [left; reflexivity | right; reflexivity]|].
      split; [|reflexivity].
      intros r Hr. rewrite rg_setx_x0. rewrite rg_setx_other; [reflexivity|]. intros ->. apply Hr. cbn. tauto. }
    wsx wacc_OpImm F_8 D_8. rgn. rewrite H11, alu_add, add_sext0.
    wsx wacc_OpImm F_c D_c. rgn. rewrite alu_add, w0_add_sext. lits.
    wsx wacc_ShiftImm F_10 D_10. rgn. rewrite sll40.
    wsx wacc_OpImm F_14 D_14. rgn. rewrite alu_add, zw_add_sext. lits.
    wsx wacc_Branch F_18 D_18. rgn. rewrite branch_geu_z by lia. rewrite (proj2 (Z.ltb_lt size _)) by lia. cbn [negb]. pcn.
    wsx wacc_OpImm F_1c D_1c. rgn. rewrite alu_add, w0_add_sext. lits.
    wsx wacc_Op F_20 D_20. rgn. rewrite H10, alu_add, <- (wq size) by lia.
    wsx wacc_OpImm F_24 D_24. rgn. rewrite H10, alu_add, w_add_sext. lits.
    wsx wacc_OpImm F_28 D_28. rgn. rewrite andm8, u_bq by lia. change ((B + 7) / 8 * 8)%Z with ab.
    wsx wacc_OpImm F_2c D_2c. rgn. rewrite andm8, bvu_z by lia. change (E / 8 * 8)%Z with ae.
    assert (HBI0 : forall S, MF ms0 S MZC M1 -> rg S 2 = Z_to_bv 64 (bv_unsigned sp0 - 16) -> BI 0 S model0).
    { intros S HS1 HS2. split; [exact HS1 | split; [exact HS2 | split; [apply mat_of_refl | lia]]]. }
    wsx wacc_Branch F_30 D_30. rgn. rewrite H10, br_geu_w by lia.
    destruct (Z.ltb_spec B AB) as [Hlt|Hge]; cbn [negb]; pcn.
    + wsx wacc_Branch F_34 D_34. rgn. rewrite (br_eq0 size) by lia.
      destruct (Z.eqb_spec size 0) as [Hs0|Hs0]; pcn.
      * apply (w_block 0 _ model0); [ lia | lia | | reflexivity | rgn; exact H10 | rgn; reflexivity | rgn; reflexivity
          | rgn; f_equal; lia | rgn; reflexivity ].
        apply HBI0; [ mfs HF1 | rgn; f_equal; lia ].
      * wsx wacc_OpImm F_38 D_38. rgn. rewrite alu_add, w0_add_sext. lits.
        wsx wacc_OpImm F_3c D_3c. rgn. rewrite H10, alu_add, w_add_sext. lits.
        apply (h_loop (Z.to_nat (AB - B - 1)) 0 _ model0); [ lia | lia | | reflexivity | rgn; exact H10 | rgn; reflexivity
          | rgn; reflexivity | rgn; reflexivity | rgn; f_equal; lia | rgn; reflexivity ].
        apply HBI0; [ mfs HF1 | rgn; f_equal; lia ].
    + apply (w_block 0 _ model0); [ lia | lia | | reflexivity | rgn; exact H10 | rgn; reflexivity | rgn; reflexivity
        | rgn; f_equal; lia | rgn; reflexivity ].
      apply HBI0; [ mfs HF1 | rgn; f_equal; lia ].
Qed.

End Loop.

(* [comment removed for export] *)
Theorem miz_sum : forall (ms : machine_state) (model : Model) (T : TSet) (beg : word) (size : Z),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 10 = beg -> rg ms 11 = Z_to_bv 64 size ->
  (0 <= size <= 2 ^ 40)%Z -> (bv_unsigned beg + size + 8 <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < size)%Z -> bat segs (ms_mem ms) (beg + Z_to_bv 64 i) = Some (Z_to_bv 8 0)) ->
  (vm_backing_used model + 4096 * size <= vm_limit (m_vmmaps model))%Z ->
  (16 <= bv_unsigned (rg ms 2))%Z ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (rg ms 2) - 8)) 8 = true ->
  no_lazy model (bv_unsigned (rg ms 2) - 8) (bv_unsigned (rg ms 2)) ->
  (bv_unsigned (rg ms 2) <= bv_unsigned beg \/ bv_unsigned beg + size <= bv_unsigned (rg ms 2) - 8)%Z ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms' model', MF ms ms' MZCLOB (write_to_mem (ms_mem ms) (Z_to_bv 64 (bv_unsigned (rg ms 2) - 8)) (store_bytes SZ8 (rg ms 1))) ->
     ms_pc_val ms' = rg ms 1 -> rg ms' 10 = Z_to_bv 64 1 -> mat_of model model' size ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model T beg size Hsvc Hpc Hh H10 H11 Hsz Hnw Hz Hbud Hsp Hok Hnls Hdisj Hra HK.
  exact (miz_entry model Hh ms T beg size (rg ms 2) Hsz Hnw Hz Hbud Hsp Hok Hnls Hdisj eq_refl Hra HK Hsvc Hpc H10 H11).
Qed.

End Miz.
