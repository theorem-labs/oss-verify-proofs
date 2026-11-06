(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac acc_pipeline Hfetch Hecall Hdecode :=
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

Lemma acc_Lui : forall ms w isz rd (imm : bv 20),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Auipc : forall ms w isz rd (imm : bv 20),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (ms_pc_val ms + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Jal : forall ms w isz rd (imm : bv 21),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (ms_pc_val ms + Z_to_bv 64 isz)
                  (ms_pc_val ms + sext 64 imm) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Jalr : forall ms w isz rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (ms_pc_val ms + Z_to_bv 64 isz)
                  (bv_and (rg ms rs1 + sext 64 imm) (bv_not w1)) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz rd rs1 imm Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Branch : forall ms w isz bc rs1 rs2 (imm : bv 13),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch bc rs1 rs2 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms 0 w0
                  (if branch_taken bc (rg ms rs1) (rg ms rs2)
                   then ms_pc_val ms + sext 64 imm
                   else ms_pc_val ms + Z_to_bv 64 isz)
                  (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz bc rs1 rs2 imm Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; rewrite is_x0_0; reflexivity.
Qed.

Lemma acc_OpImm : forall ms w isz op rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs1 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (alu64 op (rg ms rs1) (sext 64 imm))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz op rd rs1 imm Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_ShiftImm : forall ms w isz op rd rs1 (shamt : bv 6),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs1 shamt, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (alu64 op (rg ms rs1) (zext 64 shamt))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz op rd rs1 shamt Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Op : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (alu64 op (rg ms rs1) (rg ms rs2))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_OpImm32 : forall ms w isz rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs1 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (sext 64 (alu32 ALU_ADD (low32 (rg ms rs1)) (sext 32 imm)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz rd rs1 imm Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_ShiftImm32 : forall ms w isz op rd rs1 (shamt : bv 5),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs1 shamt, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (sext 64 (alu32 op (low32 (rg ms rs1)) (zext 32 shamt)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz op rd rs1 shamt Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Op32 : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (sext 64 (alu32 op (low32 (rg ms rs1)) (low32 (rg ms rs2))))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Mul : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (mul_div op (rg ms rs1) (rg ms rs2))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Mul32 : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (sext 64 (mul_div op (low32 (rg ms rs1)) (low32 (rg ms rs2))))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Fence : forall ms w isz fm pred succ rd rs1,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence fm pred succ rd rs1, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz fm pred succ rd rs1 Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx; rewrite is_x0_0; reflexivity.
Qed.

Lemma acc_FenceI : forall ms w isz rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI rd rs1 imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    []).
Proof.
  intros ms w isz rd rs1 imm Hfetch Hecall Hdecode.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold setx; rewrite is_x0_0; reflexivity.
Qed.

Lemma acc_Load : forall ms w isz sz sg rd rs1 (imm : bv 12) bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, isz) ->
  rdn segs (ms_mem ms) (rg ms rs1 + sext 64 imm) (msz_n sz) = Some bs ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (load_word sz sg bs)
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms))
    [(rg ms rs1 + sext 64 imm, msz_n sz)]).
Proof.
  intros ms w isz sz sg rd rs1 imm bs Hfetch Hecall Hdecode Hread.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hread.
  destruct sz; destruct sg; cbv beta iota delta [msz_n load_word] in *;
    rewrite ov_rdn, Hread; cbv beta iota;
    unfold setx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Store : forall ms w isz sz rs1 rs2 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, isz) ->
  store_ok segs (ms_mem ms) (rg ms rs1 + sext 64 imm) (msz_n sz) = true ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1 + sext 64 imm) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1 + sext 64 imm)
                                (store_bytes sz (rg ms rs2))))
    [(rg ms rs1 + sext 64 imm, msz_n sz)]).
Proof.
  intros ms w isz sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hok.
  unfold setx, inval, rg; rewrite is_x0_0.
  destruct sz; cbv beta iota delta [msz_n store_bytes] in *;
    rewrite Hok; cbv beta iota;
    destruct (ms_resv ms) as [r|]; [|reflexivity| |reflexivity| |reflexivity| |reflexivity];
    destruct (Z.eqb (bv_unsigned r) _); reflexivity.
Qed.

Lemma acc_Lr : forall ms w isz wd aq rl rd rs1 bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr wd aq rl rd rs1, isz) ->
  amo_aligned wd (rg ms rs1) = true ->
  rdn segs (ms_mem ms) (rg ms rs1) (amo_n wd) = Some bs ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (lr_word wd bs)
                  (ms_pc_val ms + Z_to_bv 64 isz) (Some (rg ms rs1)) (ms_mem ms))
    [(rg ms rs1, amo_n wd)]).
Proof.
  intros ms w isz wd aq rl rd rs1 bs Hfetch Hecall Hdecode Hal Hread.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hal, Hread. unfold setx, rg. rewrite Hal. cbv beta iota delta [negb].
  destruct wd; cbv beta iota delta [amo_n lr_word] in *;
    rewrite ov_rdn, Hread; cbv beta iota;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Sc_ok : forall ms w isz wd aq rl rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, isz) ->
  amo_aligned wd (rg ms rs1) = true ->
  sc_ok (ms_resv ms) (rg ms rs1) = true ->
  store_ok segs (ms_mem ms) (rg ms rs1) (amo_n wd) = true ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd w0 (ms_pc_val ms + Z_to_bv 64 isz) None
                  (write_to_mem (ms_mem ms) (rg ms rs1) (sc_bytes wd (rg ms rs2))))
    [(rg ms rs1, amo_n wd)]).
Proof.
  intros ms w isz wd aq rl rd rs1 rs2 Hfetch Hecall Hdecode Hal Hres Hok.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold rg, sc_ok in Hal, Hres, Hok. unfold setx, rg. rewrite Hal. cbv beta iota delta [negb].
  rewrite Hres.
  destruct wd; cbv beta iota delta [amo_n sc_bytes] in *;
    rewrite Hok; cbv beta iota;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Sc_fail : forall ms w isz wd aq rl rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, isz) ->
  amo_aligned wd (rg ms rs1) = true ->
  sc_ok (ms_resv ms) (rg ms rs1) = false ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd w1 (ms_pc_val ms + Z_to_bv 64 isz) None (ms_mem ms))
    []).
Proof.
  intros ms w isz wd aq rl rd rs1 rs2 Hfetch Hecall Hdecode Hal Hres.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold rg, sc_ok in Hal, Hres. unfold setx, rg. rewrite Hal. cbv beta iota delta [negb].
  rewrite Hres. cbv beta iota.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Amo_w : forall ms w isz op aq rl rd rs1 rs2 bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op AW aq rl rd rs1 rs2, isz) ->
  amo_aligned AW (rg ms rs1) = true ->
  rdn segs (ms_mem ms) (rg ms rs1) 4 = Some bs ->
  store_ok segs (ms_mem ms) (rg ms rs1) 4 = true ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))
                  (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1)
                     (Z_to_le_bytes 4 (bv_unsigned
                        (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 (rg ms rs2)))))))
    [(rg ms rs1, 4%nat); (rg ms rs1, 4%nat)]).
Proof.
  intros ms w isz op aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hal, Hread, Hok. unfold setx, inval, rg. rewrite Hal. cbv beta iota delta [negb].
  rewrite ov_rdn, Hread. cbv beta iota. rewrite Hok. cbv beta iota.
  destruct (ms_resv ms) as [r|];
    [destruct (Z.eqb (bv_unsigned r) _)|];
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma acc_Amo_d : forall ms w isz op aq rl rd rs1 rs2 bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op AD aq rl rd rs1 rs2, isz) ->
  amo_aligned AD (rg ms rs1) = true ->
  rdn segs (ms_mem ms) (rg ms rs1) 8 = Some bs ->
  store_ok segs (ms_mem ms) (rg ms rs1) 8 = true ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state
    (setx ms rd (bv_extract 0 64 (le_bytes_to_word bs))
                  (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1)
                     (Z_to_le_bytes 8 (bv_unsigned
                        (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) (rg ms rs2))))))
    [(rg ms rs1, 8%nat); (rg ms rs1, 8%nat)]).
Proof.
  intros ms w isz op aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  acc_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hal, Hread, Hok. unfold setx, inval, rg. rewrite Hal. cbv beta iota delta [negb].
  rewrite ov_rdn, Hread. cbv beta iota. rewrite Hok. cbv beta iota.
  destruct (ms_resv ms) as [r|];
    [destruct (Z.eqb (bv_unsigned r) _)|];
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

End WithSegs.
