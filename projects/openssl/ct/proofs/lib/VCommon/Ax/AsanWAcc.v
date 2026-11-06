(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac wacc_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step_accesses, ms_pc;
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     RiscvSemantics.access_value RiscvSemantics.accessed_ranges
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.fget Sem.fset
     Sem.with_regs Sem.with_fregs Sem.with_pc Sem.with_resv
     Sem.inval_resv
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition latch (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := Some (rg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

Lemma wacc_Ecall : forall ms w,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state (latch ms) []).
Proof.
  intros ms w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. reflexivity.
Qed.

Lemma wacc_Lui : forall ms w isz rd (imm : bv 20),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_Jal : forall ms w isz rd (imm : bv 21),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (ms_pc_val ms + Z_to_bv 64 isz)
                  (ms_pc_val ms + sext 64 imm) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_Jalr : forall ms w isz rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (ms_pc_val ms + Z_to_bv 64 isz)
                  (bv_and (rg ms rs1 + sext 64 imm) (bv_not w1)) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz rd rs1 imm Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_Branch : forall ms w isz bc rs1 rs2 (imm : bv 13),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch bc rs1 rs2 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms 0 w0
                  (if branch_taken bc (rg ms rs1) (rg ms rs2)
                   then ms_pc_val ms + sext 64 imm
                   else ms_pc_val ms + Z_to_bv 64 isz)
                  (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz bc rs1 rs2 imm Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; rewrite is_x0_0; reflexivity.
Qed.

Lemma wacc_OpImm : forall ms w isz op rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs1 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (alu64 op (rg ms rs1) (sext 64 imm))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz op rd rs1 imm Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_ShiftImm : forall ms w isz op rd rs1 (shamt : bv 6),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs1 shamt, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (alu64 op (rg ms rs1) (zext 64 shamt))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz op rd rs1 shamt Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_Op : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (alu64 op (rg ms rs1) (rg ms rs2))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_OpImm32 : forall ms w isz rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs1 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (sext 64 (alu32 ALU_ADD (low32 (rg ms rs1)) (sext 32 imm)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz rd rs1 imm Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_Op32 : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (sext 64 (alu32 op (low32 (rg ms rs1)) (low32 (rg ms rs2))))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_Load : forall ms w isz sz sg rd rs1 (imm : bv 12) bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, isz) ->
  rdn segs (ms_mem ms) (rg ms rs1 + sext 64 imm) (msz_n sz) = Some bs ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (load_word sz sg bs)
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) [(rg ms rs1 + sext 64 imm, msz_n sz)]).
Proof.
  intros ms w isz sz sg rd rs1 imm bs Hfetch Hecall Hdecode Hread.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hread.
  destruct sz; destruct sg; cbv beta iota delta [msz_n load_word] in *;
    rewrite ov_rdn, Hread; cbv beta iota;
    unfold setx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_Store : forall ms w isz sz rs1 rs2 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, isz) ->
  store_ok segs (ms_mem ms) (rg ms rs1 + sext 64 imm) (msz_n sz) = true ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1 + sext 64 imm) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1 + sext 64 imm)
                                (store_bytes sz (rg ms rs2)))) [(rg ms rs1 + sext 64 imm, msz_n sz)]).
Proof.
  intros ms w isz sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hok.
  unfold setx, inval, rg; rewrite is_x0_0.
  destruct sz; cbv beta iota delta [msz_n store_bytes] in *;
    rewrite Hok; cbv beta iota;
    destruct (ms_resv ms) as [r|]; [|reflexivity| |reflexivity| |reflexivity| |reflexivity];
    destruct (Z.eqb (bv_unsigned r) _); reflexivity.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zw_add : forall a b : Z, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_l, bv_wrap_add_idemp_r.
  reflexivity.
Qed.

Lemma zw_sub : forall a b : Z, (Z_to_bv 64 a - Z_to_bv 64 b)%bv = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq.
  rewrite bv_sub_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma zw_add_sext : forall (a : Z) {n} (imm : bv n),
  (Z_to_bv 64 a + sext 64 imm)%bv = Z_to_bv 64 (a + bv_signed imm).
Proof. intros a n imm. rewrite sext64_Z_to_bv. apply zw_add. Qed.

Lemma zw_mod : forall a : Z, Z_to_bv 64 (a + 2 ^ 64) = Z_to_bv 64 a.
Proof.
  intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.add_mod by lia. rewrite Z_mod_same_full, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma bvu_z : forall z : Z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. lia. Qed.

Lemma Z_to_bv_u : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros w. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_bv_unsigned. Qed.

Lemma le_bytes_to_word_8 : forall v : word, le_bytes_to_word (word_to_le_bytes 8 v) = v.
Proof. intros v. apply le_word_v. apply bytes_le_to_Z_8. Qed.

Lemma load8 : forall sg (v : word), load_word SZ8 sg (word_to_le_bytes 8 v) = v.
Proof. intros sg v. rewrite load_word_SZ8. apply le_bytes_to_word_8. Qed.

Lemma alu_add : forall a b : word, alu64 ALU_ADD a b = (a + b)%bv.
Proof. reflexivity. Qed.
Lemma alu_sub : forall a b : word, alu64 ALU_SUB a b = (a - b)%bv.
Proof. reflexivity. Qed.

Lemma alu_sltu_z : forall x y : Z, (0 <= x < 2 ^ 64)%Z -> (0 <= y < 2 ^ 64)%Z ->
  alu64 ALU_SLTU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if (x <? y)%Z then 1 else 0).
Proof.
  intros x y Hx Hy. cbv [alu64 alu]. unfold bv_ltu. rewrite !bvu_z by assumption.
  destruct (x <? y)%Z; reflexivity.
Qed.

Lemma branch_eq_z : forall x y : Z, (0 <= x < 2 ^ 64)%Z -> (0 <= y < 2 ^ 64)%Z ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y)%Z.
Proof.
  intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !bvu_z by assumption. reflexivity.
Qed.

Lemma branch_ne_z : forall x y : Z, (0 <= x < 2 ^ 64)%Z -> (0 <= y < 2 ^ 64)%Z ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y)%Z.
Proof.
  intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !bvu_z by assumption. reflexivity.
Qed.

Lemma branch_ltu_z : forall x y : Z, (0 <= x < 2 ^ 64)%Z -> (0 <= y < 2 ^ 64)%Z ->
  branch_taken BC_LTU (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof.
  intros x y Hx Hy. cbn [branch_taken]. unfold bv_ltu. rewrite !bvu_z by assumption. reflexivity.
Qed.

Lemma branch_geu_z : forall x y : Z, (0 <= x < 2 ^ 64)%Z -> (0 <= y < 2 ^ 64)%Z ->
  branch_taken BC_GEU (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y)%Z.
Proof.
  intros x y Hx Hy. cbn [branch_taken]. unfold bv_ltu. rewrite !bvu_z by assumption. reflexivity.
Qed.

Lemma branch_lt0_pos : forall x : Z, (0 <= x < 2 ^ 63)%Z ->
  branch_taken BC_LT (Z_to_bv 64 x) w0 = false.
Proof.
  intros x Hx. cbn [branch_taken]. unfold bv_lts, w0.
  rewrite !PropExec.bv_signed_small by (rewrite bvu_z by lia; lia).
  rewrite !bvu_z by lia. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma bv_eqb_true_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof.
  intros n a b H. destruct (bv_eq_dec n a b) as [E|NE]; [exact E|].
  unfold bv_eqb in H. apply Z.eqb_eq in H. exfalso. apply NE. apply bv_eq. exact H.
Qed.

Lemma w2m_outside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hnw Hx; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (u64_range a).
  destruct bs as [|b' bs'].
  - cbn [write_to_mem]. destruct (bv_eqb x a) eqn:E; [|reflexivity].
    apply bv_eqb_true_eq in E. subst. cbn [length] in Hx. lia.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z) by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH; [|cbn [length] in *; lia|cbn [length] in *; lia].
    destruct (bv_eqb x a) eqn:E; [|reflexivity].
    apply bv_eqb_true_eq in E. subst. lia.
Qed.

Lemma w2m_keeps_some : forall bs m (a x : word),
  m x <> None -> write_to_mem m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH. destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma alu_sltu_w : forall x y : word,
  alu64 ALU_SLTU x y = Z_to_bv 64 (if (bv_unsigned x <? bv_unsigned y)%Z then 1 else 0).
Proof. intros x y. cbv [alu64 alu]. unfold bv_ltu. destruct (bv_unsigned x <? bv_unsigned y)%Z; reflexivity. Qed.

Lemma alu_and : forall x y : word, alu64 ALU_AND x y = bv_and x y.
Proof. reflexivity. Qed.

Lemma w_add_z : forall (w : word) (z : Z), (w + Z_to_bv 64 z)%bv = Z_to_bv 64 (bv_unsigned w + z).
Proof. intros w z. rewrite <- (Z_to_bv_u w) at 1. apply zw_add. Qed.

Lemma w_sub_z : forall (w : word) (z : Z), (w - Z_to_bv 64 z)%bv = Z_to_bv 64 (bv_unsigned w - z).
Proof. intros w z. rewrite <- (Z_to_bv_u w) at 1. apply zw_sub. Qed.

Lemma z_sub_w : forall (z : Z) (w : word), (Z_to_bv 64 z - w)%bv = Z_to_bv 64 (z - bv_unsigned w).
Proof. intros z w. rewrite <- (Z_to_bv_u w) at 1. apply zw_sub. Qed.

Lemma and0_l : forall x : word, bv_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. apply bv_eq. rewrite bv_and_unsigned. rewrite bvu_z by lia. rewrite Z.land_0_l. reflexivity. Qed.

Lemma andm1_l : forall x : word, bv_and (Z_to_bv 64 18446744073709551615) x = x.
Proof.
  intros x. apply bv_eq. rewrite bv_and_unsigned. rewrite bvu_z by lia.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  apply Z.mod_small. apply u64_range.
Qed.

Lemma load4_pos : forall sg (z : Z), (0 <= z < 2 ^ 31)%Z ->
  load_word SZ4 sg (word_to_le_bytes 4 (Z_to_bv 64 z)) = Z_to_bv 64 z.
Proof.
  intros sg z Hz. cbn [load_word].
  assert (Hb : le_bytes_to_word (word_to_le_bytes 4 (Z_to_bv 64 z)) = Z_to_bv 64 z).
  { apply le_word_v. rewrite bytes_le_N. rewrite bvu_z by lia.
    change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. apply Z.mod_small. lia. }
  rewrite Hb. destruct sg.
  - apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned.
    unfold bv_signed. rewrite bv_extract_unsigned, Z.shiftr_0_r, bvu_z by lia.
    rewrite (bv_wrap_small 32 z) by (change (bv_modulus 32) with (2 ^ 32)%Z; lia).
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
    apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z; lia.
  - apply bv_eq. unfold zext. rewrite bv_zero_extend_unsigned by lia. rewrite bv_extract_unsigned, Z.shiftr_0_r.
    rewrite bvu_z by lia. apply bv_wrap_small. change (bv_modulus 32) with (2 ^ 32)%Z. lia.
Qed.

Lemma subw_z : forall x y : Z, (0 <= y <= x)%Z -> (x < 2 ^ 31)%Z ->
  sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) = Z_to_bv 64 (x - y).
Proof.
  intros x y Hy Hx. apply bv_eq. change (alu32 ALU_SUB ?a ?b) with (bv_sub a b). unfold low32, sext.
  rewrite bv_sign_extend_unsigned. unfold bv_signed. rewrite bv_sub_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r, !bvu_z by lia.
  rewrite !(bv_wrap_small 32 x), (bv_wrap_small 32 y) by (change (bv_modulus 32) with (2 ^ 32)%Z; lia).
  rewrite (bv_wrap_small 32 (x - y)) by (change (bv_modulus 32) with (2 ^ 32)%Z; lia).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z; lia.
Qed.

Lemma rdn_w2m_outZ : forall segs bs m (a x : Z) n,
  (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z -> (0 <= x)%Z -> (x + Z.of_nat n <= 2 ^ 64)%Z ->
  (x + Z.of_nat n <= a \/ a + Z.of_nat (length bs) <= x)%Z ->
  rdn segs (write_to_mem m (Z_to_bv 64 a) bs) (Z_to_bv 64 x) n = rdn segs m (Z_to_bv 64 x) n.
Proof.
  intros segs bs m a x n Ha Han Hx Hxn Hd.
  destruct n as [|n']; [reflexivity|]. destruct bs as [|b0 bs']; [reflexivity|].
  cbn [length] in *.
  apply rdn_ext; [rewrite bvu_z by lia; lia|].
  intros y Hy. rewrite bvu_z in Hy by lia. apply w2m_outside; cbn [length]; rewrite bvu_z by lia; lia.
Qed.

Lemma store_ok_w2m : forall segs m p bs (a : word) n,
  store_ok segs m a n = true -> store_ok segs (write_to_mem m p bs) a n = true.
Proof.
  intros segs m p bs a n H. eapply StoreOk.store_ok_mono; [|exact H].
  intros x Hx. apply w2m_keeps_some. exact Hx.
Qed.

Lemma length_store8 : forall v, length (store_bytes SZ8 v) = 8%nat.
Proof. intros v. reflexivity. Qed.

Lemma andm1_l' : forall x : word, bv_and (Z_to_bv 64 (-1)) x = x.
Proof.
  intros x. apply bv_eq. rewrite bv_and_unsigned. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (-1)) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  apply Z.mod_small. apply u64_range.
Qed.

Lemma rdn_w2m_hit8 : forall segs m (a : Z) (v : word),
  (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  rdn segs (write_to_mem m (Z_to_bv 64 a) (word_to_le_bytes 8 v)) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v).
Proof.
  intros segs m a v Ha Hb. rewrite write_to_mem_wbytes. apply rdn_wbytes_hit8. rewrite bvu_z by lia. lia.
Qed.

Lemma rdn_w2m_outW : forall segs bs m (a : Z) (x : word) n,
  (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z -> (bv_unsigned x + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat n <= a \/ a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  rdn segs (write_to_mem m (Z_to_bv 64 a) bs) x n = rdn segs m x n.
Proof.
  intros segs bs m a x n Ha Han Hxn Hd. rewrite <- (Z_to_bv_u x). pose proof (u64_range x).
  apply rdn_w2m_outZ; lia.
Qed.

Lemma skipn_app_l : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma skipn_app_r : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.
