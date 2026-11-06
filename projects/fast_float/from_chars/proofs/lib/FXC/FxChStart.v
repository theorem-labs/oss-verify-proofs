(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.

Module FxChLoop.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma isteps_one : forall segs ms ms', ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms' -> isteps segs ms ms'.
Proof. intros segs ms ms' H1 H2. eapply ist_step; [exact H1 | exact H2 | apply ist_refl]. Qed.

Lemma bv_addZ : forall a k, 0 <= a -> 0 <= k -> a + k < two64 -> (Z_to_bv 64 a + Z_to_bv 64 k)%bv = Z_to_bv 64 (a + k).
Proof.
  intros a k Ha Hk Hak. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, two64 in *.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in *. rewrite (Z.mod_small a), (Z.mod_small k) by lia. reflexivity.
Qed.

Lemma Z_to_bv5_0 : Z_to_bv 5 0 = (0%bv : reg).
Proof. apply bv_eq. reflexivity. Qed.
Lemma getr_rupd_same : forall regs r v, r <> Z_to_bv 5 0 -> getr (rupd regs r v) r = v.
Proof. intros regs r v H. rewrite Z_to_bv5_0 in H. unfold rupd. rewrite (bv_eqb_neq r 0%bv H). apply getr_same. exact H. Qed.
Lemma getr_rupd_other : forall regs r v r', r' <> r -> getr (rupd regs r v) r' = getr regs r'.
Proof. intros regs r v r' H. unfold rupd. destruct (bv_eqb r 0); [reflexivity|]. apply getr_other. exact H. Qed.
Lemma getr_x0 : forall regs, getr regs (Z_to_bv 5 0) = Z_to_bv 64 0.
Proof. intros regs. unfold getr. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_eq_bv : forall (a : word) z, bv_unsigned a = z -> a = Z_to_bv 64 z.
Proof. intros a z H. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- H. symmetry. apply bv_wrap_bv_unsigned. Qed.

Section Tbl.
Variable segs : list Segment.
Variable t : tree xi.
Hypothesis Ht : tbl_ok segs t.
Variables (fr : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (rv : option word) (mem rom : word -> option byte).

#[using="Ht"] Lemma tbl_ent : forall pc x, tlookup t pc = x -> x <> XOther -> x <> XEcall ->
  exists w i, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z) /\ xlate pc i = x.
Proof. LiaFast.lf_pins (fun (Ht : LiaFast.U) => LiaFast.u0). intros pc x H1 H2 H3. exact (Ht pc x H1 H2 H3). Qed.

#[using="Ht"] Lemma tbl_step_ld : forall pc sz sg (rd rs : reg) imm bs, tlookup t pc = XLd sz sg (rkey rd) (rkey rs) imm ->
  ov_read_bytes segs mem (getr regs rs + Z_to_bv 64 imm) (nbytes sz) = Some bs ->
  RiscvSemantics.step segs (mks fr fc regs (Z_to_bv 64 pc) rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (ld_word sz sg bs)) (Z_to_bv 64 pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Ht : LiaFast.U) => LiaFast.u0).
  intros pc sz sg rd rs imm bs H Hr. destruct (tbl_ent pc _ H ltac:(discriminate) ltac:(discriminate)) as (w & i & Hf & He & Hd & Hx).
  destruct (xl_ld pc i sz sg _ _ _ Hx) as (rd' & rs' & im & -> & H1 & H2 & H3).
  apply bv_key_inj in H1. apply bv_key_inj in H2. subst rd' rs'. apply (g_load segs fr fc regs _ rv mem rom w Hf He sz sg rd rs im bs Hd).
  rewrite (u_eq_bv _ _ (eq_sym H3)). exact Hr.
Qed.

#[using="Ht"] Lemma tbl_step_st : forall pc sz (rs1 rs2 : reg) imm, tlookup t pc = XSt sz (rkey rs1) (rkey rs2) imm ->
  store_ok segs mem (getr regs rs1 + Z_to_bv 64 imm) (nbytes sz) = true ->
  RiscvSemantics.step segs (mks fr fc regs (Z_to_bv 64 pc) rv mem rom) =
  MachineOk (mks fr fc regs (Z_to_bv 64 pc + Z_to_bv 64 4) (ival (getr regs rs1 + Z_to_bv 64 imm) rv)
               (write_to_mem mem (getr regs rs1 + Z_to_bv 64 imm) (Z_to_le_bytes (nbytes sz) (st_word sz (getr regs rs2)))) rom).
Proof. LiaFast.lf_pins (fun (Ht : LiaFast.U) => LiaFast.u0).
  intros pc sz rs1 rs2 imm H Hok. destruct (tbl_ent pc _ H ltac:(discriminate) ltac:(discriminate)) as (w & i & Hf & He & Hd & Hx).
  destruct (xl_st pc i sz _ _ _ Hx) as (a & b & im & -> & H1 & H2 & H3).
  apply bv_key_inj in H1. apply bv_key_inj in H2. subst a b.
  rewrite <- (u_eq_bv _ _ (eq_sym H3)) in Hok |- *.
  exact (g_store segs fr fc regs _ rv mem rom w Hf He sz rs1 rs2 im Hd Hok).
Qed.

#[using="Ht"] Lemma tbl_step_addi : forall pc (rd rs : reg) imm, tlookup t pc = XAluI ALU_ADD (rkey rd) (rkey rs) imm ->
  RiscvSemantics.step segs (mks fr fc regs (Z_to_bv 64 pc) rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (alu64 ALU_ADD (getr regs rs) (Z_to_bv 64 imm))) (Z_to_bv 64 pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Ht : LiaFast.U) => LiaFast.u0).
  intros pc rd rs imm H. destruct (tbl_ent pc _ H ltac:(discriminate) ltac:(discriminate)) as (w & i & Hf & He & Hd & Hx).
  destruct (xl_aluI pc i ALU_ADD _ _ _ Hx) as [(rd' & rs' & im & -> & H1 & H2 & H3)|(rd' & rs' & sh & -> & H1 & H2 & H3)];
    apply bv_key_inj in H1; apply bv_key_inj in H2; subst rd' rs'.
  - rewrite (g_opimm segs fr fc regs _ rv mem rom w Hf He ALU_ADD rd rs im Hd). rewrite (u_eq_bv _ _ (eq_sym H3)). reflexivity.
  - rewrite (g_shiftimm segs fr fc regs _ rv mem rom w Hf He ALU_ADD rd rs sh Hd). rewrite (u_eq_bv _ _ (eq_sym H3)). reflexivity.
Qed.

#[using="Ht"] Lemma tbl_step_jal : forall pc (rd : reg) tgt link, tlookup t pc = XJal (rkey rd) tgt link ->
  RiscvSemantics.step segs (mks fr fc regs (Z_to_bv 64 pc) rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (Z_to_bv 64 pc + Z_to_bv 64 4)) (Z_to_bv 64 tgt) rv mem rom).
Proof. LiaFast.lf_pins (fun (Ht : LiaFast.U) => LiaFast.u0).
  intros pc rd tgt link H. destruct (tbl_ent pc _ H ltac:(discriminate) ltac:(discriminate)) as (w & i & Hf & He & Hd & Hx).
  destruct (xl_jal pc i _ _ _ Hx) as (rd' & im & -> & H1 & H2 & H3).
  apply bv_key_inj in H1. subst rd'. rewrite (g_jal segs fr fc regs _ rv mem rom w Hf He rd im Hd). rewrite (u_eq_bv _ _ (eq_sym H2)). reflexivity.
Qed.

#[using="Ht"] Lemma tbl_step_br : forall pc c (rs1 rs2 : reg) tgt, tlookup t pc = XBr c (rkey rs1) (rkey rs2) tgt ->
  RiscvSemantics.step segs (mks fr fc regs (Z_to_bv 64 pc) rv mem rom) =
  MachineOk (mks fr fc regs (if branch_taken c (getr regs rs1) (getr regs rs2) then Z_to_bv 64 tgt else Z_to_bv 64 pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Ht : LiaFast.U) => LiaFast.u0).
  intros pc c rs1 rs2 tgt H. destruct (tbl_ent pc _ H ltac:(discriminate) ltac:(discriminate)) as (w & i & Hf & He & Hd & Hx).
  destruct (xl_br pc i c _ _ _ Hx) as (a & b & im & -> & H1 & H2 & H3).
  apply bv_key_inj in H1. apply bv_key_inj in H2. subst a b. rewrite (g_branch segs fr fc regs _ rv mem rom w Hf He c rs1 rs2 im Hd).
  rewrite (u_eq_bv _ _ (eq_sym H3)). reflexivity.
Qed.
End Tbl.


(* [comment removed for export] *)
Definition rA0 : reg := Z_to_bv 5 10.
Definition rS1 : reg := Z_to_bv 5 9.
Definition rX0 : reg := Z_to_bv 5 0.

Lemma rA0_nz : rA0 <> Z_to_bv 5 0. Proof. intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate. Qed.
Lemma rS1_nz : rS1 <> Z_to_bv 5 0. Proof. intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate. Qed.
Lemma rS1_A0 : rS1 <> rA0. Proof. intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate. Qed.

Section Scan.
Variable segs : list Segment.
Variable t : tree xi.
Hypothesis Ht : tbl_ok segs t.
Variable pc0 : Z.
Hypothesis Hpc : 0 <= pc0 /\ pc0 + 12 < two64.
Hypothesis T1 : tlookup t pc0 = XLd SZ8 true (rkey rA0) (rkey rS1) 0.
Hypothesis T2 : tlookup t (pc0 + 4) = XAluI ALU_ADD (rkey rS1) (rkey rS1) 8.
Hypothesis T3 : tlookup t (pc0 + 8) = XBr BC_NE (rkey rA0) (rkey rX0) pc0.

#[using="t Ht Hpc T1 T2 T3"] Lemma scan_iter : forall fr fc rv mem rom regs (base : Z) bs, 0 <= base -> base + 8 < two64 ->
  getr regs rS1 = Z_to_bv 64 base ->
  ov_read_bytes segs mem (Z_to_bv 64 base) 8 = Some bs ->
  isteps segs (mks fr fc regs (Z_to_bv 64 pc0) rv mem rom)
    (mks fr fc (rupd (rupd regs rA0 (ld_word SZ8 true bs)) rS1 (Z_to_bv 64 (base + 8)))
       (if negb (bv_eqb (ld_word SZ8 true bs) (Z_to_bv 64 0)) then Z_to_bv 64 pc0 else Z_to_bv 64 (pc0 + 12)) rv mem rom).
Proof. LiaFast.lf_pins (fun (t Ht Hpc T1 T2 T3 : LiaFast.U) => LiaFast.u0).
  intros fr fc rv mem rom regs base bs Hb0 Hb8 Hs1 Hrd. destruct Hpc as [Hp0 Hp1].
  eapply isteps_trans.
  { apply isteps_one; [reflexivity|]. apply (tbl_step_ld segs t Ht fr fc regs rv mem rom pc0 SZ8 true rA0 rS1 0 bs T1).
    rewrite Hs1. rewrite bv_addZ by (unfold two64 in *; lia). rewrite Z.add_0_r. exact Hrd. }
  rewrite bv_addZ by (unfold two64 in *; lia). eapply isteps_trans.
  { apply isteps_one; [reflexivity|]. exact (tbl_step_addi segs t Ht fr fc _ rv mem rom (pc0 + 4) rS1 rS1 8 T2). }
  rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 4 + 4) with (pc0 + 8) by lia.
  apply isteps_one; [reflexivity|].
  rewrite (tbl_step_br segs t Ht fr fc _ rv mem rom (pc0 + 8) BC_NE rA0 rX0 pc0 T3).
  rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 8 + 4) with (pc0 + 12) by lia.
  assert (Hr : rupd (rupd regs rA0 (ld_word SZ8 true bs)) rS1 (alu64 ALU_ADD (getr (rupd regs rA0 (ld_word SZ8 true bs)) rS1) (Z_to_bv 64 8))
             = rupd (rupd regs rA0 (ld_word SZ8 true bs)) rS1 (Z_to_bv 64 (base + 8))).
  { f_equal. rewrite getr_rupd_other by exact rS1_A0. rewrite Hs1. unfold alu64, alu. apply bv_addZ; unfold two64 in *; lia. }
  rewrite Hr. unfold branch_taken. unfold rX0. rewrite getr_x0.
  rewrite getr_rupd_other by (intro H; apply rS1_A0; symmetry; exact H). rewrite getr_rupd_same by exact rA0_nz.
  reflexivity.
Qed.

#[using="t Ht Hpc T1 T2 T3"] Lemma scan_loop : forall K fr fc rv mem rom regs (base : Z),
  0 <= base -> base + 8 * Z.of_nat K + 8 < two64 ->
  getr regs rS1 = Z_to_bv 64 base ->
  (forall i, (i < K)%nat -> exists bs, ov_read_bytes segs mem (Z_to_bv 64 (base + 8 * Z.of_nat i)) 8 = Some bs /\ ld_word SZ8 true bs <> Z_to_bv 64 0) ->
  (exists bs, ov_read_bytes segs mem (Z_to_bv 64 (base + 8 * Z.of_nat K)) 8 = Some bs /\ ld_word SZ8 true bs = Z_to_bv 64 0) ->
  exists regs', isteps segs (mks fr fc regs (Z_to_bv 64 pc0) rv mem rom) (mks fr fc regs' (Z_to_bv 64 (pc0 + 12)) rv mem rom) /\
     getr regs' rA0 = Z_to_bv 64 0 /\ getr regs' rS1 = Z_to_bv 64 (base + 8 * Z.of_nat K + 8) /\
     (forall r, r <> rA0 -> r <> rS1 -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (t Ht Hpc T1 T2 T3 : LiaFast.U) => LiaFast.u0).
  induction K as [|K IH]; intros fr fc rv mem rom regs base Hb0 Hbk Hs1 Hnz Hz.
  - destruct Hz as (bs & Hrd & Hv). cbn [Z.of_nat] in Hrd, Hbk |- *. rewrite Z.mul_0_r, Z.add_0_r in Hrd |- *.
    pose proof (scan_iter fr fc rv mem rom regs base bs Hb0 ltac:(lia) Hs1 Hrd) as Hst.
    rewrite Hv in Hst. rewrite bv_eqb_refl in Hst. cbn [negb] in Hst.
    eexists. split; [exact Hst|]. split; [|split].
    + rewrite getr_rupd_other by (intro H; apply rS1_A0; symmetry; exact H). rewrite getr_rupd_same by exact rA0_nz. reflexivity.
    + rewrite getr_rupd_same by exact rS1_nz. reflexivity.
    + intros r H1 H2. rewrite getr_rupd_other by exact H2. rewrite getr_rupd_other by exact H1. reflexivity.
  - destruct (Hnz O ltac:(lia)) as (bs & Hrd & Hv). cbn [Z.of_nat] in Hrd. rewrite Z.mul_0_r, Z.add_0_r in Hrd.
    pose proof (scan_iter fr fc rv mem rom regs base bs Hb0 ltac:(lia) Hs1 Hrd) as Hst.
    assert (Hne : bv_eqb (ld_word SZ8 true bs) (Z_to_bv 64 0) = false) by (apply bv_eqb_neq; exact Hv).
    rewrite Hne in Hst. cbn [negb] in Hst.
    set (regs2 := rupd (rupd regs rA0 (ld_word SZ8 true bs)) rS1 (Z_to_bv 64 (base + 8))) in Hst.
    destruct (IH fr fc rv mem rom regs2 (base + 8) ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hbk; lia))
      as (regs' & Hst' & H10 & H9 & Hoth).
    + unfold regs2. rewrite getr_rupd_same by exact rS1_nz. reflexivity.
    + intros i Hi. destruct (Hnz (S i) ltac:(lia)) as (bs' & Hrd' & Hv'). exists bs'. split; [|exact Hv'].
      rewrite Nat2Z.inj_succ in Hrd'. replace (base + 8 + 8 * Z.of_nat i) with (base + 8 * Z.succ (Z.of_nat i)) by lia. exact Hrd'.
    + destruct Hz as (bs' & Hrd' & Hv'). exists bs'. split; [|exact Hv']. rewrite Nat2Z.inj_succ in Hrd'.
      replace (base + 8 + 8 * Z.of_nat K) with (base + 8 * Z.succ (Z.of_nat K)) by lia. exact Hrd'.
    + exists regs'. split; [eapply isteps_trans; [exact Hst | exact Hst']|]. split; [exact H10|]. split.
      * rewrite H9. rewrite Nat2Z.inj_succ. f_equal. lia.
      * intros r H1 H2. rewrite (Hoth r H1 H2). unfold regs2. rewrite getr_rupd_other by exact H2. rewrite getr_rupd_other by exact H1. reflexivity.
Qed.
End Scan.

(* [comment removed for export] *)
Lemma ov1_rd1 : forall segs m a, ov_read_bytes segs m a 1 = match rd1 segs m a with Some b => Some [b] | None => None end.
Proof. intros segs m a. rewrite ov_rdn. cbn [rdn]. unfold rd1. destruct (m a); reflexivity. Qed.

Lemma wtm_other : forall m (G : Z) bs (x : word), 0 <= G -> G + Z.of_nat (length bs) <= two64 ->
  bv_unsigned x < G \/ G + Z.of_nat (length bs) <= bv_unsigned x -> write_to_mem m (Z_to_bv 64 G) bs x = m x.
Proof.
  intros m G bs x H0 H1 H2. rewrite write_to_mem_spec by assumption.
  destruct (Z.leb G (bv_unsigned x) && Z.ltb (bv_unsigned x) (G + Z.of_nat (length bs)))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma wtm_in : forall m (G : Z) bs (x : word), 0 <= G -> G + Z.of_nat (length bs) <= two64 ->
  G <= bv_unsigned x < G + Z.of_nat (length bs) -> write_to_mem m (Z_to_bv 64 G) bs x <> None.
Proof.
  intros m G bs x H0 H1 H2. rewrite write_to_mem_spec by assumption.
  replace (Z.leb G (bv_unsigned x) && Z.ltb (bv_unsigned x) (G + Z.of_nat (length bs)))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  destruct (nth_error bs (Z.to_nat (bv_unsigned x - G))) eqn:E; [discriminate|].
  apply nth_error_None in E. lia.
Qed.

Lemma wtm_twice : forall m (G : Z) bs1 bs2, 0 <= G -> G + Z.of_nat (length bs1) <= two64 -> length bs1 = length bs2 ->
  write_to_mem (write_to_mem m (Z_to_bv 64 G) bs1) (Z_to_bv 64 G) bs2 = write_to_mem m (Z_to_bv 64 G) bs2.
Proof.
  intros m G bs1 bs2 H0 H1 Hl. apply functional_extensionality. intros x.
  rewrite (write_to_mem_spec bs2 (write_to_mem m (Z_to_bv 64 G) bs1)) by lia.
  rewrite (write_to_mem_spec bs2 m) by lia.
  destruct (Z.leb G (bv_unsigned x) && Z.ltb (bv_unsigned x) (G + Z.of_nat (length bs2)))%bool eqn:E; [reflexivity|].
  apply wtm_other; [lia | lia |]. apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; rewrite Hl; lia.
Qed.

Lemma store_ok_wtm : forall segs m (G : Z) bs, 0 <= G -> G + Z.of_nat (length bs) <= two64 ->
  store_ok segs (write_to_mem m (Z_to_bv 64 G) bs) (Z_to_bv 64 G) (length bs) = true.
Proof.
  intros segs m G bs H0 H1. apply store_ok_from; [lia | lia |]. intros i Hi.
  unfold wview. pose proof (wtm_in m G bs (Z_to_bv 64 (G + i)) H0 H1) as Hw. rewrite u_small64 in Hw by (unfold two64 in *; lia).
  destruct (write_to_mem m (Z_to_bv 64 G) bs (Z_to_bv 64 (G + i))); [discriminate | exfalso; apply Hw; [lia | reflexivity]].
Qed.

Lemma ival_idem : forall a rv, ival a (ival a rv) = ival a rv.
Proof.
  intros a [r|]; cbn [ival]; [|reflexivity].
  destruct (Z.eqb (bv_unsigned r) (bv_unsigned a)) eqn:E; cbn [ival]; [reflexivity|]. rewrite E. reflexivity.
Qed.

Lemma bv_add_m1 : forall a, 0 < a < two64 -> (Z_to_bv 64 a + Z_to_bv 64 18446744073709551615)%bv = Z_to_bv 64 (a - 1).
Proof.
  intros a Ha. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, two64 in *.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in *. rewrite (Z.mod_small a) by lia.
  rewrite (Z.mod_small 18446744073709551615) by lia.
  replace (a + 18446744073709551615) with ((a - 1) + 1 * 18446744073709551616) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rA1 : reg := Z_to_bv 5 11.
Definition rA2 : reg := Z_to_bv 5 12.
Definition rA3 : reg := Z_to_bv 5 13.
Definition rS0 : reg := Z_to_bv 5 8.
Ltac rneq := let H := fresh "H" in intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.
Lemma rA1_nz : rA1 <> Z_to_bv 5 0. Proof. rneq. Qed.
Lemma rA2_nz : rA2 <> Z_to_bv 5 0. Proof. rneq. Qed.
Lemma rA3_nz : rA3 <> Z_to_bv 5 0. Proof. rneq. Qed.
Lemma rA1_A0 : rA1 <> rA0. Proof. rneq. Qed.
Lemma rA2_A0 : rA2 <> rA0. Proof. rneq. Qed.
Lemma rA2_A1 : rA2 <> rA1. Proof. rneq. Qed.
Lemma rA3_A0 : rA3 <> rA0. Proof. rneq. Qed.
Lemma rA3_A1 : rA3 <> rA1. Proof. rneq. Qed.
Lemma rA3_A2 : rA3 <> rA2. Proof. rneq. Qed.
Lemma rS0_A0 : rS0 <> rA0. Proof. rneq. Qed.
Lemma rA1_A3' : rA1 <> rA3. Proof. rneq. Qed.
Lemma rA0_A3' : rA0 <> rA3. Proof. rneq. Qed.
Lemma rA2_A0' : rA0 <> rA2. Proof. rneq. Qed.
Lemma rA2_A1' : rA1 <> rA2. Proof. rneq. Qed.

Section Pn.
Variable segs : list Segment.
Variable t : tree xi.
Hypothesis Ht : tbl_ok segs t.
Variable pc0 : Z.
Hypothesis Hpc : 0 <= pc0 /\ pc0 + 32 < two64.
Hypothesis T0 : tlookup t pc0 = XSt SZ8 (rkey rA0) (rkey rS0) 0.
Hypothesis T1 : tlookup t (pc0 + 4) = XAluI ALU_ADD (rkey rA2) (rkey rX0) 47.
Hypothesis T2 : tlookup t (pc0 + 8) = XJal (rkey rX0) (pc0 + 20) (pc0 + 12).
Hypothesis T3 : tlookup t (pc0 + 12) = XSt SZ8 (rkey rA0) (rkey rA1) 0.
Hypothesis T4 : tlookup t (pc0 + 16) = XAluI ALU_ADD (rkey rA1) (rkey rA1) 1.
Hypothesis T5 : tlookup t (pc0 + 20) = XLd SZ1 false (rkey rA3) (rkey rA1) 18446744073709551615.
Hypothesis T6 : tlookup t (pc0 + 24) = XBr BC_EQ (rkey rA3) (rkey rA2) (pc0 + 12).
Hypothesis T7 : tlookup t (pc0 + 28) = XBr BC_NE (rkey rA3) (rkey rX0) (pc0 + 16).
Variables (fr : bvmap 5 word) (fc : bv 32) (rv : option word) (rom : word -> option byte) (mem : word -> option byte).
Variables (p0 n G : Z) (ch : Z -> byte).
Hypothesis Hp0 : 0 < p0 /\ p0 + n + 2 < two64 /\ 0 <= n.
Hypothesis HG : 0 <= G /\ G + 8 <= two64 /\ (G + 8 <= p0 \/ p0 + n + 1 <= G).
Hypothesis Hch : forall i, 0 <= i < n -> rd1 segs mem (Z_to_bv 64 (p0 + i)) = Some (ch i) /\ ch i <> Z_to_bv 8 0.
Hypothesis Hnul : rd1 segs mem (Z_to_bv 64 (p0 + n)) = Some (Z_to_bv 8 0).
Hypothesis Hsok : store_ok segs mem (Z_to_bv 64 G) 8 = true.

Let wG (u : Z) := write_to_mem mem (Z_to_bv 64 G) (Z_to_le_bytes 8 u).

#[using="Hp0 HG"] Lemma pn_rd : forall u i, 0 <= i <= n -> rd1 segs (wG u) (Z_to_bv 64 (p0 + i)) = rd1 segs mem (Z_to_bv 64 (p0 + i)).
Proof. LiaFast.lf_pins (fun (Hp0 HG : LiaFast.U) => LiaFast.u0).
  intros u i Hi. unfold rd1, wG. rewrite wtm_other; [reflexivity | lia | rewrite length_Z_to_le_bytes; lia |].
  rewrite length_Z_to_le_bytes. rewrite u_small64 by (unfold two64 in *; lia). lia.
Qed.

#[using="Type"] Lemma ld_byte_eq : forall b : byte, bv_unsigned (ld_word SZ1 false [b]) = bv_unsigned b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b. unfold ld_word. rewrite le_word_1. rewrite b_extract8_id. unfold zext. rewrite bv_zero_extend_unsigned.
  reflexivity. lia.
Qed.

#[using="t Ht Hpc T3 T4 T5 T6 T7 ch Hp0 HG Hch Hnul"] Lemma pn_body : forall (k : nat) i regs u, i = n - Z.of_nat k -> 0 <= i ->
  getr regs rA0 = Z_to_bv 64 G -> getr regs rA1 = Z_to_bv 64 (p0 + i + 1) -> getr regs rA2 = Z_to_bv 64 47 ->
  exists regs' v, isteps segs (mks fr fc regs (Z_to_bv 64 (pc0 + 20)) (ival (Z_to_bv 64 G) rv) (wG u) rom)
                          (mks fr fc regs' (Z_to_bv 64 (pc0 + 32)) (ival (Z_to_bv 64 G) rv) (wG v) rom) /\
     getr regs' rA1 = Z_to_bv 64 (p0 + n + 1) /\ getr regs' rA3 = Z_to_bv 64 0 /\
     (forall r, r <> rA1 -> r <> rA3 -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (t Ht Hpc T3 T4 T5 T6 T7 ch Hp0 HG Hch Hnul : LiaFast.U) => LiaFast.u0).
  destruct Hpc as [Hpc0 Hpc1]. destruct Hp0 as (Hp1 & Hp2 & Hp3). destruct HG as (HG1 & HG2 & HG3).
  induction k as [|k IH]; intros i regs u Hi Hi0 Ha0 Ha1 Ha2.
  - (* [comment removed for export] *)
    cbn [Z.of_nat] in Hi. rewrite Z.sub_0_r in Hi. subst i.
    set (b0 := ld_word SZ1 false [Z_to_bv 8 0]).
    assert (Hb0 : b0 = Z_to_bv 64 0) by (apply bv_eq; unfold b0; rewrite ld_byte_eq; reflexivity).
    exists (rupd regs rA3 b0), u. split; [|split; [|split]].
    + eapply isteps_trans.
      { apply isteps_one; [reflexivity|].
        apply (tbl_step_ld segs t Ht fr fc regs _ (wG u) rom (pc0 + 20) SZ1 false rA3 rA1 _ [Z_to_bv 8 0] T5).
        rewrite Ha1. rewrite bv_add_m1 by (unfold two64 in *; lia). replace (p0 + n + 1 - 1) with (p0 + n) by lia.
        rewrite ov1_rd1. rewrite pn_rd by lia. rewrite Hnul. reflexivity. }
      rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 20 + 4) with (pc0 + 24) by lia.
      eapply isteps_trans.
      { apply isteps_one; [reflexivity|]. exact (tbl_step_br segs t Ht fr fc _ _ (wG u) rom (pc0 + 24) BC_EQ rA3 rA2 (pc0 + 12) T6). }
      unfold branch_taken. rewrite getr_rupd_same by exact rA3_nz. rewrite getr_rupd_other by exact (not_eq_sym rA3_A2).
      rewrite Ha2, Hb0. replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 47)) with false by reflexivity.
      rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 24 + 4) with (pc0 + 28) by lia.
      apply isteps_one; [reflexivity|].
      rewrite (tbl_step_br segs t Ht fr fc _ _ (wG u) rom (pc0 + 28) BC_NE rA3 rX0 (pc0 + 16) T7).
      unfold branch_taken. rewrite getr_rupd_same by exact rA3_nz. unfold rX0. rewrite getr_x0. rewrite ?Hb0.
      rewrite bv_eqb_refl. cbn [negb]. rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 28 + 4) with (pc0 + 32) by lia.
      reflexivity.
    + rewrite getr_rupd_other by exact rA1_A3'. exact Ha1.
    + rewrite getr_rupd_same by exact rA3_nz. exact Hb0.
    + intros r H1 H3. rewrite getr_rupd_other by exact H3. reflexivity.
  - (* [comment removed for export] *)
    assert (Hin : 0 <= i < n) by lia.
    destruct (Hch i Hin) as [Hrd Hnz].
    set (b := ld_word SZ1 false [ch i]).
    assert (Hbu : bv_unsigned b = bv_unsigned (ch i)) by (unfold b; apply ld_byte_eq).
    set (regs1 := rupd regs rA3 b).
    assert (S1 : isteps segs (mks fr fc regs (Z_to_bv 64 (pc0 + 20)) (ival (Z_to_bv 64 G) rv) (wG u) rom)
                             (mks fr fc regs1 (Z_to_bv 64 (pc0 + 24)) (ival (Z_to_bv 64 G) rv) (wG u) rom)).
    { apply isteps_one; [reflexivity|].
      rewrite (tbl_step_ld segs t Ht fr fc regs _ (wG u) rom (pc0 + 20) SZ1 false rA3 rA1 _ [ch i] T5).
      - rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 20 + 4) with (pc0 + 24) by lia. reflexivity.
      - rewrite Ha1. rewrite bv_add_m1 by (unfold two64 in *; lia). replace (p0 + i + 1 - 1) with (p0 + i) by lia.
        rewrite ov1_rd1. rewrite pn_rd by lia. rewrite Hrd. reflexivity. }
    assert (R1a0 : getr regs1 rA0 = Z_to_bv 64 G) by (unfold regs1; rewrite getr_rupd_other by exact rA0_A3'; exact Ha0).
    assert (R1a1 : getr regs1 rA1 = Z_to_bv 64 (p0 + i + 1)) by (unfold regs1; rewrite getr_rupd_other by exact rA1_A3'; exact Ha1).
    assert (R1a2 : getr regs1 rA2 = Z_to_bv 64 47) by (unfold regs1; rewrite getr_rupd_other by exact (not_eq_sym rA3_A2); exact Ha2).
    assert (R1a3 : getr regs1 rA3 = b) by (unfold regs1; rewrite getr_rupd_same by exact rA3_nz; reflexivity).
    (* [comment removed for export] *)
    assert (Tail : forall u', isteps segs (mks fr fc regs1 (Z_to_bv 64 (pc0 + 16)) (ival (Z_to_bv 64 G) rv) (wG u') rom)
                                (mks fr fc (rupd regs1 rA1 (Z_to_bv 64 (p0 + i + 2))) (Z_to_bv 64 (pc0 + 20)) (ival (Z_to_bv 64 G) rv) (wG u') rom)).
    { intros u'. apply isteps_one; [reflexivity|].
      rewrite (tbl_step_addi segs t Ht fr fc regs1 _ (wG u') rom (pc0 + 16) rA1 rA1 1 T4).
      rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 16 + 4) with (pc0 + 20) by lia.
      rewrite R1a1. unfold alu64, alu. rewrite bv_addZ by (unfold two64 in *; lia). replace (p0 + i + 1 + 1) with (p0 + i + 2) by lia.
      reflexivity. }
    assert (Hrec : forall u', exists regs' v, isteps segs (mks fr fc (rupd regs1 rA1 (Z_to_bv 64 (p0 + i + 2))) (Z_to_bv 64 (pc0 + 20)) (ival (Z_to_bv 64 G) rv) (wG u') rom)
                          (mks fr fc regs' (Z_to_bv 64 (pc0 + 32)) (ival (Z_to_bv 64 G) rv) (wG v) rom) /\
        getr regs' rA1 = Z_to_bv 64 (p0 + n + 1) /\ getr regs' rA3 = Z_to_bv 64 0 /\
        (forall r, r <> rA1 -> r <> rA3 -> getr regs' r = getr (rupd regs1 rA1 (Z_to_bv 64 (p0 + i + 2))) r)).
    { intros u'. apply (IH (i + 1)); [rewrite Nat2Z.inj_succ in Hi; lia | lia | | |].
      - rewrite getr_rupd_other by exact (not_eq_sym rA1_A0). exact R1a0.
      - rewrite getr_rupd_same by exact rA1_nz. f_equal. lia.
      - rewrite getr_rupd_other by exact rA2_A1. exact R1a2. }
    assert (Hfin : forall regs', (forall r, r <> rA1 -> r <> rA3 -> getr regs' r = getr (rupd regs1 rA1 (Z_to_bv 64 (p0 + i + 2))) r) ->
                    forall r, r <> rA1 -> r <> rA3 -> getr regs' r = getr regs r).
    { intros regs' Ho r H1 H3. rewrite (Ho r H1 H3). rewrite getr_rupd_other by exact H1. unfold regs1. rewrite getr_rupd_other by exact H3. reflexivity. }
    destruct (Z.eqb (bv_unsigned (ch i)) 47) eqn:Hsl.
    + (* [comment removed for export] *)
      destruct (Hrec (p0 + i + 1)) as (regs' & v & Sr & Q1 & Q3 & Qo).
      exists regs', v. split; [|split; [exact Q1|split; [exact Q3 | exact (Hfin regs' Qo)]]].
      eapply isteps_trans; [exact S1|].
      eapply isteps_trans.
      { apply isteps_one; [reflexivity|]. exact (tbl_step_br segs t Ht fr fc regs1 _ (wG u) rom (pc0 + 24) BC_EQ rA3 rA2 (pc0 + 12) T6). }
      unfold branch_taken. rewrite R1a3, R1a2. unfold bv_eqb. rewrite Hbu. change (bv_unsigned (Z_to_bv 64 47)) with 47. rewrite Hsl.
      eapply isteps_trans.
      { apply isteps_one; [reflexivity|].
        assert (Hok : store_ok segs (wG u) (getr regs1 rA0 + Z_to_bv 64 0) (nbytes SZ8) = true).
        { rewrite R1a0, bv_add_0_r by reflexivity. unfold wG. exact (store_ok_wtm segs mem G (Z_to_le_bytes 8 u) HG1 ltac:(rewrite length_Z_to_le_bytes; lia)). }
        exact (tbl_step_st segs t Ht fr fc regs1 _ (wG u) rom (pc0 + 12) SZ8 rA0 rA1 0 T3 Hok). }
      rewrite R1a0, R1a1. rewrite (bv_add_0_r (Z_to_bv 64 G) (Z_to_bv 64 0)) by reflexivity. rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 12 + 4) with (pc0 + 16) by lia.
      rewrite ival_idem. cbn [nbytes st_word]. rewrite u_small64 by (unfold two64 in *; lia).
      unfold wG. rewrite wtm_twice by (rewrite ?length_Z_to_le_bytes; lia). fold (wG (p0 + i + 1)).
      eapply isteps_trans; [exact (Tail (p0 + i + 1)) | exact Sr].
    + (* [comment removed for export] *)
      destruct (Hrec u) as (regs' & v & Sr & Q1 & Q3 & Qo).
      exists regs', v. split; [|split; [exact Q1|split; [exact Q3 | exact (Hfin regs' Qo)]]].
      eapply isteps_trans; [exact S1|].
      eapply isteps_trans.
      { apply isteps_one; [reflexivity|]. exact (tbl_step_br segs t Ht fr fc regs1 _ (wG u) rom (pc0 + 24) BC_EQ rA3 rA2 (pc0 + 12) T6). }
      unfold branch_taken. rewrite R1a3, R1a2. unfold bv_eqb at 1. rewrite Hbu. change (bv_unsigned (Z_to_bv 64 47)) with 47. rewrite Hsl.
      rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 24 + 4) with (pc0 + 28) by lia.
      eapply isteps_trans.
      { apply isteps_one; [reflexivity|]. exact (tbl_step_br segs t Ht fr fc regs1 _ (wG u) rom (pc0 + 28) BC_NE rA3 rX0 (pc0 + 16) T7). }
      unfold branch_taken. rewrite R1a3. unfold rX0. rewrite getr_x0.
      assert (Hne : bv_eqb b (Z_to_bv 64 0) = false).
      { unfold bv_eqb. rewrite Hbu. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. intro H0. apply Hnz.
        apply bv_eq. rewrite H0. reflexivity. }
      rewrite Hne. cbn [negb].
      eapply isteps_trans; [exact (Tail u) | exact Sr].
Qed.

#[using="Type"] Lemma rupd_x0 : forall regs v, rupd regs rX0 v = regs.
Proof. LiaFast.lf_pins LiaFast.u0. intros regs v. unfold rupd, rX0. reflexivity. Qed.

#[using="t Ht Hpc T0 T1 T2 T3 T4 T5 T6 T7 ch Hp0 HG Hch Hnul Hsok"] Lemma pn_run : forall regs, getr regs rS0 = Z_to_bv 64 p0 -> getr regs rA0 = Z_to_bv 64 G -> getr regs rA1 = Z_to_bv 64 (p0 + 1) ->
  exists regs' v, isteps segs (mks fr fc regs (Z_to_bv 64 pc0) rv mem rom)
                          (mks fr fc regs' (Z_to_bv 64 (pc0 + 32)) (ival (Z_to_bv 64 G) rv) (wG v) rom) /\
     getr regs' rA1 = Z_to_bv 64 (p0 + n + 1) /\ getr regs' rA3 = Z_to_bv 64 0 /\ getr regs' rA2 = Z_to_bv 64 47 /\
     (forall r, r <> rA1 -> r <> rA2 -> r <> rA3 -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (t Ht Hpc T0 T1 T2 T3 T4 T5 T6 T7 ch Hp0 HG Hch Hnul Hsok : LiaFast.U) => LiaFast.u0).
  intros regs Hs0 Ha0 Ha1. destruct Hpc as [Hpc0 Hpc1]. destruct Hp0 as (Hp1 & Hp2 & Hp3). destruct HG as (HG1 & HG2 & HG3).
  set (regs2 := rupd regs rA2 (Z_to_bv 64 47)).
  assert (S1 : isteps segs (mks fr fc regs (Z_to_bv 64 pc0) rv mem rom) (mks fr fc regs2 (Z_to_bv 64 (pc0 + 20)) (ival (Z_to_bv 64 G) rv) (wG p0) rom)).
  { eapply isteps_trans.
    { apply isteps_one; [reflexivity|].
      assert (Hok : store_ok segs mem (getr regs rA0 + Z_to_bv 64 0) (nbytes SZ8) = true) by (rewrite Ha0, bv_add_0_r by reflexivity; exact Hsok).
      exact (tbl_step_st segs t Ht fr fc regs rv mem rom pc0 SZ8 rA0 rS0 0 T0 Hok). }
    rewrite Ha0, (bv_add_0_r (Z_to_bv 64 G) (Z_to_bv 64 0)) by reflexivity. rewrite bv_addZ by (unfold two64 in *; lia).
    cbn [nbytes st_word]. rewrite Hs0. rewrite u_small64 by (unfold two64 in *; lia). fold (wG p0).
    eapply isteps_trans.
    { apply isteps_one; [reflexivity|]. exact (tbl_step_addi segs t Ht fr fc regs _ (wG p0) rom (pc0 + 4) rA2 rX0 47 T1). }
    rewrite bv_addZ by (unfold two64 in *; lia). replace (pc0 + 4 + 4) with (pc0 + 8) by lia.
    unfold rX0 at 1. rewrite getr_x0. replace (alu64 ALU_ADD (Z_to_bv 64 0) (Z_to_bv 64 47)) with (Z_to_bv 64 47) by (apply bv_eq; reflexivity).
    fold regs2. apply isteps_one; [reflexivity|].
    rewrite (tbl_step_jal segs t Ht fr fc regs2 _ (wG p0) rom (pc0 + 8) rX0 (pc0 + 20) (pc0 + 12) T2). rewrite rupd_x0. reflexivity. }
  destruct (pn_body (Z.to_nat n) 0 regs2 p0 ltac:(lia) ltac:(lia)) as (regs' & v & S2 & Q1 & Q3 & Qo).
  - unfold regs2. rewrite getr_rupd_other by exact rA2_A0'. exact Ha0.
  - unfold regs2. rewrite getr_rupd_other by exact rA2_A1'. rewrite Ha1. f_equal. lia.
  - unfold regs2. rewrite getr_rupd_same by exact rA2_nz. reflexivity.
  - exists regs', v. split; [eapply isteps_trans; [exact S1 | exact S2]|]. split; [exact Q1|]. split; [exact Q3|]. split.
    + rewrite (Qo rA2 rA2_A1 (not_eq_sym rA3_A2)). unfold regs2. rewrite getr_rupd_same by exact rA2_nz. reflexivity.
    + intros r H1 H2 H3. rewrite (Qo r H1 H3). unfold regs2. rewrite getr_rupd_other by exact H2. reflexivity.
Qed.
End Pn.
End FxChLoop.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rdn_ext : forall segs m m' n (X : Z), 0 <= X -> X + Z.of_nat n <= two64 ->
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (X + i)) = m' (Z_to_bv 64 (X + i))) ->
  rdn segs m (Z_to_bv 64 X) n = rdn segs m' (Z_to_bv 64 X) n.
Proof.
  intros segs m m' n. induction n as [|n IH]; intros X H0 H1 Heq; [reflexivity|].
  cbn [rdn]. pose proof (Heq 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. rewrite E0.
  rewrite word_add1. rewrite (IH (X + 1)); [reflexivity | lia | lia |].
  intros i Hi. replace (X + 1 + i) with (X + (i + 1)) by lia. apply Heq. lia.
Qed.

Lemma rd1_ext : forall segs m m' a, m a = m' a -> rd1 segs m a = rd1 segs m' a.
Proof. intros segs m m' a H. unfold rd1. rewrite H. reflexivity. Qed.

Lemma regs_ok_set : forall E R regs' (r : reg) l,
  r <> Z_to_bv 5 0 -> getr regs' r = lden E l ->
  (forall r', r' <> r -> getr regs' r' = lden E (rget R (rkey r'))) ->
  regs_ok E (rset R (rkey r) l) regs'.
Proof.
  intros E R regs' r l Hnz Hr Ho r'.
  assert (Hk : rkey r <> xH) by (intros H; apply Hnz; apply rkey_1 in H; rewrite H; apply bv_eq; reflexivity).
  destruct (decide (r' = r)) as [->|Hne].
  - rewrite rget_rset_same by exact Hk. exact Hr.
  - rewrite rget_rset_other by (intros H; apply Hne; apply bv_key_inj; exact H). exact (Ho r' Hne).
Qed.

Lemma rget_set_other : forall R (r r' : reg) l, r' <> r -> rget (rset R (rkey r) l) (rkey r') = rget R (rkey r').
Proof. intros R r r' l H. apply rget_rset_other. intros Hk. apply H. apply bv_key_inj. exact Hk. Qed.
Lemma rget_set_same : forall R (r : reg) l, r <> Z_to_bv 5 0 -> rget (rset R (rkey r) l) (rkey r) = l.
Proof.
  intros R r l Hnz. apply rget_rset_same. intros H. apply Hnz. apply rkey_1 in H. rewrite H. apply bv_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le_byte_bits : forall bs j k, 0 <= k < 8 -> (j < length bs)%nat ->
  Z.testbit (bytes_le_to_Z bs) (8 * Z.of_nat j + k) = Z.testbit (bv_unsigned (nth j bs (Z_to_bv 8 0))) k.
Proof.
  induction bs as [|b bs IH]; intros j k Hk Hj; cbn [length] in Hj; [lia|]. cbn [bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
  rewrite Z.lor_spec. destruct j as [|j].
  - cbn [nth]. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r _ (k - 8)) by lia. apply orb_false_r.
  - cbn [nth]. rewrite Z.shiftl_spec by lia. replace (8 * Z.of_nat (Datatypes.S j) + k - 8) with (8 * Z.of_nat j + k) by lia.
    rewrite IH by lia. replace (Z.testbit (bv_unsigned b) (8 * Z.of_nat (Datatypes.S j) + k)) with false; [reflexivity|].
    symmetry. apply (Z.bits_above_log2 (bv_unsigned b)); [lia|].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [->|Hnz]; [cbn; lia|].
    pose proof (Z.log2_lt_pow2 (bv_unsigned b) 8 ltac:(lia)) as H8. lia.
Qed.

Lemma le_byte_nth : forall bs j, (j < length bs)%nat ->
  Z_to_bv 8 (Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j)) = nth j bs (Z_to_bv 8 0).
Proof.
  intros bs j Hj. transitivity (Z_to_bv 8 (bv_unsigned (nth j bs (Z_to_bv 8 0)))); [|apply Z_to_bv_bv_unsigned].
  apply Z_to_bv8_bits. intros k Hk. rewrite Z.shiftr_spec by lia. rewrite Z.add_comm. apply le_byte_bits; assumption.
Qed.

(* [comment removed for export] *)
Definition forget_rgs (fs : list fact) (rgs : list region) (a : lin) (x : positive) : option (list region) :=
  match find_rg fs rgs a 8 O with
  | Some (i, R0, o) =>
      match rg_kind R0 with
      | RO => None
      | k => Some (upd_nth rgs i (RG (rg_base R0) (rg_size R0) k (put_bytes (rg_cont R0) o (st_bytes (lvar x) None 0 8))))
      end
  | None => None
  end.
Definition forget_post (S : sst) (a : lin) : option sst :=
  match forget_rgs (s_facts S) (s_rgs S) a (s_next S) with
  | Some rgs' => Some (SST (s_pc S) (s_regs S) rgs' (s_facts S) (Pos.succ (s_next S)) (s_resv S))
  | None => None
  end.

Section Forget.
Variable segs : list Segment.

#[using="Type"] Lemma rg_ok_put_same : forall E m R o bvs, rg_ok segs E m R -> rg_kind R <> RO -> 0 <= o -> o + Z.of_nat (length bvs) <= rsz E R ->
  (forall j x, nth_error bvs j = Some x -> rd1 segs m (Z_to_bv 64 (uE E (rg_base R) + o + Z.of_nat j)) = Some (bden E x)) ->
  rg_ok segs E m (RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o bvs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o bvs (Hs & Hw & Hall & Hcont) Hk Ho Hon Hb. unfold rg_ok, rsz in *. cbn [rg_base rg_size rg_kind rg_cont] in *.
  split; [exact Hs|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hall i Hi). destruct (rg_kind R) eqn:Hkd; [exact Hall | exact Hall | | | exact Hall].
    + destruct Hall as [Hv Hz]. split; [exact Hv|]. intros Ht. apply Hz. rewrite put_bytes_spec in Ht by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length bvs)))%bool eqn:E1; [|exact Ht].
      exfalso. apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      apply nth_error_None in Ht. lia.
    + destruct Hall as [Hv Hz]. split; [exact Hv|]. intros Ht. apply Hz. rewrite put_bytes_spec in Ht by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length bvs)))%bool eqn:E1; [|exact Ht].
      exfalso. apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      apply nth_error_None in Ht. lia.
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length bvs)))%bool eqn:E1; [|exact (Hcont p v Hp)].
    apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    split; [lia|].
    replace (bv_unsigned (lden E (rg_base R)) + (Zpos p - 1)) with (uE E (rg_base R) + o + Z.of_nat (Z.to_nat (Zpos p - 1 - o)))
      by (unfold uE; rewrite Z2Nat.id by lia; lia).
    exact (Hb _ v Hp).
Qed.

#[using="Type"] Lemma sden_forget : forall E S ms a rgs', sden segs E S ms -> bases_wf (s_next S) (s_rgs S) = true ->
  forget_rgs (s_facts S) (s_rgs S) a (s_next S) = Some rgs' ->
  exists v, sden segs (upd E (s_next S) v) (SST (s_pc S) (s_regs S) rgs' (s_facts S) (Pos.succ (s_next S)) (s_resv S)) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S ms a rgs' Hsd Hbw Hf. unfold forget_rgs in Hf.
  destruct (find_rg (s_facts S) (s_rgs S) a 8 O) as [[[i R0] o]|] eqn:Hfr; [|discriminate].
  destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth & Ho). rewrite Nat.sub_0_r in Hnth.
  assert (Hk : rg_kind R0 <> RO) by (intro Hk; rewrite Hk in Hf; discriminate).
  assert (Hrgs' : rgs' = upd_nth (s_rgs S) i (RG (rg_base R0) (rg_size R0) (rg_kind R0) (put_bytes (rg_cont R0) o (st_bytes (lvar (s_next S)) None 0 8)))).
  { destruct (rg_kind R0); [|exfalso; exact (Hk eq_refl)| | |]; injection Hf as <-; reflexivity. }
  assert (HwR : lwf (s_next S) (rg_base R0) = true /\ lwf (s_next S) (rg_size R0) = true).
  { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. apply andb_prop. apply Hbw. eapply nth_error_In. exact Hnth. }
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & Hregs & Hrg & Hdisj & Hfs & Hfrm).
  pose proof (proj1 (Forall_nth' _ _) Hrg i R0 Hnth) as HR0.
  destruct (rg_off_sound E _ _ _ _ _ (size_lo_sound E _ R0 Hfs) Ho) as (Ho0 & Hon & Haddr).
  set (A := uE E (rg_base R0)).
  set (bj := fun j : nat => match rd1 segs (ms_mem ms) (Z_to_bv 64 (A + o + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end).
  set (bs := List.map bj (seq 0 8)).
  assert (Hlb : length bs = 8%nat) by (unfold bs; rewrite length_map, length_seq; reflexivity).
  assert (Hrd : forall j, (j < 8)%nat -> rd1 segs (ms_mem ms) (Z_to_bv 64 (A + o + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))).
  { intros j Hj. unfold bs. rewrite (nth_indep _ _ (bj O)) by (rewrite length_map, length_seq; lia).
    rewrite map_nth. rewrite seq_nth by lia. cbn [Nat.add]. unfold bj.
    destruct HR0 as (_ & _ & Hall & _). specialize (Hall (o + Z.of_nat j) ltac:(lia)).
    replace (A + o + Z.of_nat j) with (uE E (rg_base R0) + (o + Z.of_nat j)) by (unfold A; lia).
    unfold uE. destruct (rd1 segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R0)) + (o + Z.of_nat j)))) eqn:Hr; [reflexivity|].
    exfalso. destruct (rg_kind R0); [exact (proj1 Hall eq_refl) | exact (Hk eq_refl) | exact (proj1 (proj1 Hall) eq_refl) | exact (proj1 (proj1 Hall) eq_refl) | exact (Hall eq_refl)]. }
  assert (Hbnd : 0 <= bytes_le_to_Z bs < two64).
  { pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlb in Hb. unfold two64. change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616 in Hb. lia. }
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). intros E'' Ha.
  assert (HaE : agree (s_next S) E E'').
  { intros x Hx. rewrite <- (Ha x (Pos.lt_trans _ _ _ Hx (Pos.lt_succ_diag_r _))). unfold upd. destruct (Pos.eqb_spec x (s_next S)); [lia | reflexivity]. }
  destruct (Hsd E'' HaE) as (Hpc'' & Hsvc'' & Hrsv'' & Hregs'' & Hrg'' & Hdisj'' & Hfs'' & Hfrm'').
  assert (HA : uE E'' (rg_base R0) = A) by (unfold A, uE; rewrite (lden_agree_wf _ E E'' _ (proj1 HwR) HaE); reflexivity).
  assert (Hv : E'' (s_next S) = Z_to_bv 64 (bytes_le_to_Z bs)) by (rewrite <- (Ha (s_next S) (Pos.lt_succ_diag_r _)); unfold upd; rewrite Pos.eqb_refl; reflexivity).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. split; [exact Hpc''|]. split; [exact Hsvc''|]. split; [exact Hrsv''|].
  split; [exact Hregs''|]. split; [|split; [|split; [exact Hfs'' | exact Hfrm'']]].
  - rewrite Hrgs'. apply Forall_nth'. intros j R Hj. destruct (Nat.eq_dec i j) as [<-|Hne].
    + rewrite (nth_upd_same _ i _ R0 Hnth) in Hj. injection Hj as <-.
      pose proof (proj1 (Forall_nth' _ _) Hrg'' i R0 Hnth) as HR0''.
      destruct (rg_off_sound E'' _ _ _ _ _ (size_lo_sound E'' _ R0 Hfs'') Ho) as (_ & Hon'' & _).
      apply (rg_ok_put_same E'' (ms_mem ms) R0 o (st_bytes (lvar (s_next S)) None 0 8)); [exact HR0'' | exact Hk | exact Ho0 | rewrite length_st_bytes; exact Hon'' |].
      intros j x Hx. destruct (st_bytes_nth _ _ _ _ _ _ Hx) as (Hj8 & ->). rewrite HA. rewrite (Hrd j Hj8). f_equal.
      cbn [bden]. rewrite lden_lvar, Hv. rewrite u_small64 by exact Hbnd. rewrite Z.add_0_l. symmetry. apply le_byte_nth. lia.
    + rewrite nth_upd_other in Hj by exact Hne. exact (proj1 (Forall_nth' _ _) Hrg'' j R Hj).
  - rewrite Hrgs'. exact (rgs_disj_upd E'' _ i (RG (rg_base R0) (rg_size R0) (rg_kind R0) (put_bytes (rg_cont R0) o (st_bytes (lvar (s_next S)) None 0 8))) R0 Hnth eq_refl eq_refl Hdisj'').
Qed.
End Forget.

Section St.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable t : tree xi.
Hypothesis Ht : tbl_ok segs t.

(* [comment removed for export] *)
#[using="Type"] Lemma frz_hidden_false : forall E S M ms model w, DEN segs LIMIT model0 mem0 E S M ms model ->
  alloc_top (m_vmmaps model) <= w < 0x800000000000 -> Hof E M model (Z_to_bv 64 w) = false.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model w Hd Hw. unfold Hof, mkH.
  destruct (page_in_ranges (page_base (Z_to_bv 64 w)) (m_vm_lazy model)) eqn:E0; [|reflexivity].
  exfalso. unfold page_in_ranges in E0. apply existsb_exists in E0 as (r & Hr & Hc).
  apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
  pose proof (alloc_top_lo _ (proj1 (dn_spok segs LIMIT model0 mem0 E S M ms model Hd))) as Hat.
  pose proof (pb_bounds (Z_to_bv 64 w)) as (P1 & P2). rewrite fg64' in P1 by (unfold two64; lia).
  unfold page_size in C2.
  assert (Hcl : covered (m_vm_lazy model) w = true).
  { unfold covered. apply existsb_exists. exists r. split; [exact Hr|]. unfold in_iv, in_rng, FxBacking.B, FxBacking.S.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  pose proof (dn_lzm segs LIMIT model0 mem0 E S M ms model Hd w Hcl) as Hcm.
  pose proof (covered_below_top segs LIMIT model0 mem0 E S M ms model w Hd Hcm). lia.
Qed.

#[using="Type"] Lemma frz_restrict : forall E S M ms model w, DEN segs LIMIT model0 mem0 E S M ms model ->
  (exists p, In p (sm_frz M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p)) ->
  ms_mem (restrict (Hof E M model) ms) (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model w Hd (p & Hp & Hw).
  destruct (dn_frz segs LIMIT model0 mem0 E S M ms model Hd p Hp w Hw) as (Htop & _ & Hm).
  rewrite restrict_mem. unfold mrestrict. rewrite (frz_hidden_false E S M ms model w Hd Htop). exact Hm.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sden_regs : forall E S ms R' regs' pc',
  sden segs E S ms ->
  (forall E', agree (s_next S) E E' -> regs_ok E' (s_regs S) (ms_regs ms) -> regs_ok E' R' regs') ->
  sden segs E (SST pc' R' (s_rgs S) (s_facts S) (s_next S) (s_resv S))
       (mks (ms_fregs ms) (ms_fcsr ms) regs' (Z_to_bv 64 pc') (ms_resv ms) (ms_mem ms) (ms_rom ms)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S ms R' regs' pc' Hsd HR E' Ha.
  destruct (Hsd E' Ha) as (Hpc & Hsvc & Hrsv & Hregs & Hrg & Hdisj & Hf & Hfrm).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_next s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
  repeat split; try assumption. exact (HR E' Ha Hregs).
Qed.

(* [comment removed for export] *)
Definition envp_post (S : sst) (pc' : Z) (l' : lin) : sst :=
  SST pc' (rset (rset (s_regs S) (rkey rA0) lc0) (rkey rS1) l') (s_rgs S) (s_facts S) (s_next S) (s_resv S).

#[using="Hwx Ht"] Theorem den_envp : forall pc0 E S M ms model T lb l' (K : nat),
  0 <= pc0 -> pc0 + 12 < two64 ->
  tlookup t pc0 = XLd SZ8 true (rkey rA0) (rkey rS1) 0 ->
  tlookup t (pc0 + 4) = XAluI ALU_ADD (rkey rS1) (rkey rS1) 8 ->
  tlookup t (pc0 + 8) = XBr BC_NE (rkey rA0) (rkey rX0) pc0 ->
  DEN segs LIMIT model0 mem0 E S M ms model ->
  s_pc S = pc0 -> rget (s_regs S) (rkey rS1) = lb ->
  uE E lb + 8 * Z.of_nat K + 8 < two64 ->
  (forall w, uE E lb <= w < uE E lb + 8 * Z.of_nat K + 8 ->
     exists p, In p (sm_frz M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p)) ->
  (forall i, (i < K)%nat -> exists bs, ov_read_bytes segs mem0 (Z_to_bv 64 (uE E lb + 8 * Z.of_nat i)) 8 = Some bs /\
                                       ld_word SZ8 true bs <> Z_to_bv 64 0) ->
  (exists bs, ov_read_bytes segs mem0 (Z_to_bv 64 (uE E lb + 8 * Z.of_nat K)) 8 = Some bs /\ ld_word SZ8 true bs = Z_to_bv 64 0) ->
  lden E l' = Z_to_bv 64 (uE E lb + 8 * Z.of_nat K + 8) -> lwf (s_next S) l' = true ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' (envp_post S (pc0 + 12) l') M ms' model' -> agree (s_next S) E E' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Ht : LiaFast.U) => LiaFast.u0).
  intros pc0 E S M ms model T lb l' K Hp0 Hp1 T1 T2 T3 Hd Hpc Hlb Hbnd Hfz Hnz Hz Hl' Hwl Hk.
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpcv & Hsvc & Hrsv & Hregs & Hrg & Hdisj & Hfs & Hfrm).
  set (base := uE E lb) in *.
  assert (Hb0 : 0 <= base) by (unfold base, uE; apply bv_unsigned_in_range).
  assert (Hs1 : getr (ms_regs msr) rS1 = Z_to_bv 64 base).
  { rewrite (Hregs rS1). rewrite Hlb. unfold base, uE. symmetry. apply lden_Z_to_bv_u. }
  (* [comment removed for export] *)
  assert (Hov : forall i, (i <= K)%nat -> ov_read_bytes segs (ms_mem msr) (Z_to_bv 64 (base + 8 * Z.of_nat i)) 8 =
                                        ov_read_bytes segs mem0 (Z_to_bv 64 (base + 8 * Z.of_nat i)) 8).
  { intros i Hi. rewrite !ov_rdn. apply rdn_ext; [lia | lia |]. intros j Hj.
    apply (frz_restrict E S M ms model); [exact Hd|]. apply Hfz. lia. }
  destruct (scan_loop segs t Ht pc0 (conj Hp0 Hp1) T1 T2 T3 K (ms_fregs msr) (ms_fcsr msr) (ms_resv msr) (ms_mem msr) (ms_rom msr)
              (ms_regs msr) base Hb0 Hbnd Hs1) as (regs' & Hst & R0 & R1 & Ro).
  { intros i Hi. rewrite (Hov i ltac:(lia)). exact (Hnz i Hi). }
  { rewrite (Hov K ltac:(lia)). exact Hz. }
  assert (Hms : msr = mks (ms_fregs msr) (ms_fcsr msr) (ms_regs msr) (Z_to_bv 64 pc0) (ms_resv msr) (ms_mem msr) (ms_rom msr)).
  { rewrite (mks_eta msr Hsvc) at 1. rewrite Hpcv, Hpc. reflexivity. }
  rewrite <- Hms in Hst.
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E S M ms model T (envp_post S (pc0 + 12) l')
           (mks (ms_fregs msr) (ms_fcsr msr) regs' (Z_to_bv 64 (pc0 + 12)) (ms_resv msr) (ms_mem msr) (ms_rom msr)) E
           Hd Hst); [| apply agree_refl | apply Pos.le_refl | intros x _; reflexivity | reflexivity | exact Hk].
  apply sden_regs; [exact Hsd|]. intros E' Ha HR.
  assert (Hl'' : lden E' l' = lden E l') by exact (lden_agree_wf _ E E' l' Hwl Ha).
  intros r. destruct (decide (r = rS1)) as [->|H1]; [rewrite rget_set_same by exact rS1_nz; rewrite Hl'', Hl'; exact R1|].
  rewrite rget_set_other by exact H1. destruct (decide (r = rA0)) as [->|H0]; [rewrite rget_set_same by exact rA0_nz; exact R0|].
  rewrite rget_set_other by exact H0. rewrite (Ro r H0 H1). apply HR.
Qed.
(* [comment removed for export] *)
Definition pn_post (S : sst) (pc' : Z) (l1 : lin) (rgs' : list region) : sst :=
  SST pc' (rset (rset (rset (s_regs S) (rkey rA1) l1) (rkey rA2) (lconst 47)) (rkey rA3) lc0) rgs' (s_facts S) (Pos.succ (s_next S)) (s_resv S).

#[using="Hwx Ht"] Theorem den_pn : forall pc0 E S M ms model T (G : Z) lp l1 rgs' (n : Z) (ch : Z -> byte),
  0 <= pc0 -> pc0 + 32 < two64 ->
  tlookup t pc0 = XSt SZ8 (rkey rA0) (rkey rS0) 0 ->
  tlookup t (pc0 + 4) = XAluI ALU_ADD (rkey rA2) (rkey rX0) 47 ->
  tlookup t (pc0 + 8) = XJal (rkey rX0) (pc0 + 20) (pc0 + 12) ->
  tlookup t (pc0 + 12) = XSt SZ8 (rkey rA0) (rkey rA1) 0 ->
  tlookup t (pc0 + 16) = XAluI ALU_ADD (rkey rA1) (rkey rA1) 1 ->
  tlookup t (pc0 + 20) = XLd SZ1 false (rkey rA3) (rkey rA1) 18446744073709551615 ->
  tlookup t (pc0 + 24) = XBr BC_EQ (rkey rA3) (rkey rA2) (pc0 + 12) ->
  tlookup t (pc0 + 28) = XBr BC_NE (rkey rA3) (rkey rX0) (pc0 + 16) ->
  DEN segs LIMIT model0 mem0 E S M ms model ->
  s_pc S = pc0 -> s_resv S = RNone ->
  rget (s_regs S) (rkey rS0) = lp -> rget (s_regs S) (rkey rA0) = lconst G ->
  lden E (rget (s_regs S) (rkey rA1)) = Z_to_bv 64 (uE E lp + 1) ->
  store_at (s_facts S) (s_rgs S) (lconst G) 8 (st_bytes (lvar (s_next S)) None 0 8) = Some rgs' ->
  0 < uE E lp -> uE E lp + n + 2 < two64 -> 0 <= n ->
  0 <= G -> G + 8 <= two64 -> (G + 8 <= uE E lp \/ uE E lp + n + 1 <= G) ->
  (forall w, uE E lp <= w <= uE E lp + n -> exists p, In p (sm_frz M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p)) ->
  (forall i, 0 <= i < n -> rd1 segs mem0 (Z_to_bv 64 (uE E lp + i)) = Some (ch i) /\ ch i <> Z_to_bv 8 0) ->
  rd1 segs mem0 (Z_to_bv 64 (uE E lp + n)) = Some (Z_to_bv 8 0) ->
  lden E l1 = Z_to_bv 64 (uE E lp + n + 1) -> lwf (s_next S) l1 = true ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' (pn_post S (pc0 + 32) l1 rgs') M ms' model' -> agree (s_next S) E E' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Ht : LiaFast.U) => LiaFast.u0).
  intros pc0 E S M ms model T G lp l1 rgs' n ch Hp0 Hp1 T0 T1 T2 T3 T4 T5 T6 T7 Hd Hpc Hrs Hlp HlG Hla1 Hsa
         Hq1 Hq2 Hq3 HG1 HG2 HG3 Hfz Hch Hnul Hl1 Hwl Hk.
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpcv & Hsvc & Hrsv & Hregs & Hrg & Hdisj & Hfs & Hfrm).
  set (p0 := uE E lp) in *.
  assert (Hrv : ms_resv msr = None) by (rewrite Hrs in Hrsv; exact Hrsv).
  assert (Hs0 : getr (ms_regs msr) rS0 = Z_to_bv 64 p0) by (rewrite (Hregs rS0), Hlp; unfold p0, uE; symmetry; apply lden_Z_to_bv_u).
  assert (Ha0 : getr (ms_regs msr) rA0 = Z_to_bv 64 G) by (rewrite (Hregs rA0), HlG; apply lden_lconst).
  assert (Ha1 : getr (ms_regs msr) rA1 = Z_to_bv 64 (p0 + 1)) by (rewrite (Hregs rA1); exact Hla1).
  (* [comment removed for export] *)
  assert (Hsok : store_ok segs (ms_mem msr) (Z_to_bv 64 G) 8 = true).
  { set (E0 := upd E (s_next S) (Z_to_bv 64 0)).
    destruct (Hsd E0 (agree_upd _ _ _)) as (_ & _ & _ & _ & Hrg0 & Hdisj0 & Hfs0 & _).
    destruct (store_at_sound segs E0 _ _ _ _ _ _ (ms_mem msr) (Z_to_le_bytes 8 0) Hrg0 Hdisj0 Hfs0 Hsa eq_refl
                (length_st_bytes _ _ _ _)) as (Hok & _).
    - intros i x Hx. destruct (st_bytes_nth _ _ _ _ _ _ Hx) as (Hi & ->).
      rewrite nth_Z_to_le_bytes by exact Hi. f_equal. cbn [bden]. rewrite lden_lvar. unfold E0, upd. rewrite Pos.eqb_refl.
      rewrite Z.add_0_l. reflexivity.
    - rewrite lden_lconst in Hok. exact Hok. }
  assert (Hrd : forall i, 0 <= i <= n -> rd1 segs (ms_mem msr) (Z_to_bv 64 (p0 + i)) = rd1 segs mem0 (Z_to_bv 64 (p0 + i))).
  { intros i Hi. apply rd1_ext. apply (frz_restrict E S M ms model); [exact Hd|]. apply Hfz. lia. }
  assert (Hch' : forall i, 0 <= i < n -> rd1 segs (ms_mem msr) (Z_to_bv 64 (p0 + i)) = Some (ch i) /\ ch i <> Z_to_bv 8 0).
  { intros i Hi. rewrite (Hrd i ltac:(lia)). exact (Hch i Hi). }
  assert (Hnul' : rd1 segs (ms_mem msr) (Z_to_bv 64 (p0 + n)) = Some (Z_to_bv 8 0)) by (rewrite (Hrd n ltac:(lia)); exact Hnul).
  assert (Hpp : 0 < p0 /\ p0 + n + 2 < two64 /\ 0 <= n) by (split; [|split]; assumption).
  assert (HGG : 0 <= G /\ G + 8 <= two64 /\ (G + 8 <= p0 \/ p0 + n + 1 <= G)) by (split; [|split]; assumption).
  destruct (pn_run segs t Ht pc0 (conj Hp0 Hp1) T0 T1 T2 T3 T4 T5 T6 T7 (ms_fregs msr) (ms_fcsr msr) (ms_resv msr) (ms_rom msr)
              (ms_mem msr) p0 n G ch Hpp HGG Hch' Hnul' Hsok (ms_regs msr) Hs0 Ha0 Ha1) as (regs' & v & Hst & R1 & R3 & R2 & Ro).
  assert (Hms : msr = mks (ms_fregs msr) (ms_fcsr msr) (ms_regs msr) (Z_to_bv 64 pc0) (ms_resv msr) (ms_mem msr) (ms_rom msr)).
  { rewrite (mks_eta msr Hsvc) at 1. rewrite Hpcv, Hpc. reflexivity. }
  rewrite <- Hms in Hst. rewrite Hrv in Hst. cbn [ival] in Hst.
  set (E1 := upd E (s_next S) (Z_to_bv 64 v)).
  assert (Ha1E : agree (s_next S) E E1) by apply agree_upd.
  set (R' := rset (rset (rset (s_regs S) (rkey rA1) l1) (rkey rA2) (lconst 47)) (rkey rA3) lc0).
  destruct (mem_sound segs E E1 S msr (lconst G) 8 (st_bytes (lvar (s_next S)) None 0 8) rgs' (Z_to_le_bytes 8 v) R'
              (Pos.succ (s_next S)) RNone regs' None (pc0 + 32) Hsd Ha1E ltac:(lia) Hsa) as (_ & Hsd').
  - intros E'' _. reflexivity.
  - apply length_Z_to_le_bytes.
  - apply length_st_bytes.
  - intros E'' Ha i x Hx. destruct (st_bytes_nth _ _ _ _ _ _ Hx) as (Hi & ->).
    rewrite nth_Z_to_le_bytes by exact Hi. f_equal. cbn [bden]. rewrite lden_lvar.
    rewrite <- (Ha (s_next S) ltac:(lia)). unfold E1, upd. rewrite Pos.eqb_refl. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite Z.add_0_l. change (Z.of_N 64) with 64. symmetry. apply byte_of_mod; lia.
  - intros E'' Ha. assert (HaE : agree (s_next S) E E'') by (apply (agree_trans _ E E1 E'' Ha1E); intros x Hx; apply Ha; lia).
    destruct (Hsd E'' HaE) as (_ & _ & _ & HR & _).
    assert (Hl1' : lden E'' l1 = lden E l1) by exact (lden_agree_wf _ E E'' l1 Hwl HaE).
    intros r. unfold R'.
    destruct (decide (r = rA3)) as [->|H3]; [rewrite rget_set_same by exact rA3_nz; exact R3|].
    rewrite rget_set_other by exact H3. destruct (decide (r = rA2)) as [->|H2]; [rewrite rget_set_same by exact rA2_nz; rewrite lden_lconst; exact R2|].
    rewrite rget_set_other by exact H2. destruct (decide (r = rA1)) as [->|H1]; [rewrite rget_set_same by exact rA1_nz; rewrite Hl1', Hl1; exact R1|].
    rewrite rget_set_other by exact H1. rewrite (Ro r H1 H2 H3). apply HR.
  - intros E'' _. reflexivity.
  - rewrite lden_lconst in Hsd'.
    apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E S M ms model T (pn_post S (pc0 + 32) l1 rgs')
             (mks (ms_fregs msr) (ms_fcsr msr) regs' (Z_to_bv 64 (pc0 + 32)) None
                  (write_to_mem (ms_mem msr) (Z_to_bv 64 G) (Z_to_le_bytes 8 v)) (ms_rom msr)) E1
             Hd Hst); [| exact Ha1E | cbn [s_next pn_post]; lia | | | exact Hk].
    + unfold pn_post. rewrite Hrs. exact Hsd'.
    + intros x Hx. cbn [ms_mem mks]. rewrite <- (lden_lconst E G).
      exact (store_at_frame segs E _ _ _ _ _ _ (ms_mem msr) _ Hrg Hfs Hsa (length_Z_to_le_bytes 8 v) x Hx).
    + cbn [pn_post s_rgs]. exact (store_at_shape _ _ _ _ _ _ Hsa).
Qed.
(* [comment removed for export] *)
#[using="Hwx"] Theorem den_forget : forall E S M ms model T a S', DEN segs LIMIT model0 mem0 E S M ms model -> forget_post S a = Some S' ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' S' M ms' model' -> agree (s_next S) E E' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T a S' Hd Hf Hk. unfold forget_post in Hf.
  destruct (forget_rgs (s_facts S) (s_rgs S) a (s_next S)) as [rgs'|] eqn:Hfr; [|discriminate]. injection Hf as <-.
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd.
  pose proof (dn_bases segs LIMIT model0 mem0 E S M ms model Hd) as Hbw.
  destruct (sden_forget segs E S _ a rgs' Hsd Hbw Hfr) as (v & Hsd').
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E S M ms model T _ (restrict (Hof E M model) ms) (upd E (s_next S) v)
           Hd (ist_refl _ _) Hsd' (agree_upd _ _ _)); [cbn [s_next]; lia | intros x _; reflexivity | | exact Hk].
  cbn [s_rgs]. unfold forget_rgs in Hfr.
  destruct (find_rg (s_facts S) (s_rgs S) a 8 O) as [[[i R0] o]|] eqn:Hfd; [|discriminate].
  destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfd) as (_ & Hnth & _). rewrite Nat.sub_0_r in Hnth.
  destruct (rg_kind R0); try discriminate; injection Hfr as <-; exact (shape_upd _ i (RG (rg_base R0) (rg_size R0) _ _) R0 Hnth eq_refl eq_refl).
Qed.
End St.
