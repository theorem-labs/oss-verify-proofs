(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rg (ms : machine_state) (r : reg) : word :=
  if is_x0 r then w0 else reg_get (ms_regs ms) r.

(* [comment removed for export] *)
Definition fg (ms : machine_state) (r : reg) : word := reg_get (ms_fregs ms) r.

(* [comment removed for export] *)
Definition setx (ms : machine_state) (rd : reg) (v : word) (pc' : word)
    (resv : option word) (mem : word -> option byte) : machine_state :=
  {| ms_regs := if is_x0 rd then ms_regs ms else bvmap_set rd v (ms_regs ms);
     ms_fregs := ms_fregs ms;
     ms_pc_val := pc';
     ms_svc_pending := None;
     ms_resv := resv;
     ms_fcsr := ms_fcsr ms;
     ms_mem := mem;
     ms_rom := ms_rom ms |}.

(* [comment removed for export] *)
Definition setf (ms : machine_state) (rd : reg) (v : word) (pc' : word)
    (resv : option word) (mem : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms;
     ms_fregs := bvmap_set rd v (ms_fregs ms);
     ms_pc_val := pc';
     ms_svc_pending := None;
     ms_resv := resv;
     ms_fcsr := ms_fcsr ms;
     ms_mem := mem;
     ms_rom := ms_rom ms |}.

(* [comment removed for export] *)
Definition inval (a : word) (resv : option word) : option word :=
  match resv with
  | Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else resv
  | None => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition store_bytes (sz : msize) (v : word) : list byte :=
  match sz with
  | SZ1 => Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 v))
  | SZ2 => Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 v))
  | SZ4 => Z_to_le_bytes 4 (bv_unsigned (low32 v))
  | SZ8 => Z_to_le_bytes 8 (bv_unsigned v)
  end.

(* [comment removed for export] *)
Definition amo_n (wd : awidth) : nat :=
  match wd with AW => 4%nat | AD => 8%nat end.

(* [comment removed for export] *)
Definition lr_word (wd : awidth) (bs : list byte) : word :=
  match wd with
  | AW => sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | AD => bv_extract 0 64 (le_bytes_to_word bs)
  end.

(* [comment removed for export] *)
Definition sc_bytes (wd : awidth) (v : word) : list byte :=
  match wd with
  | AW => Z_to_le_bytes 4 (bv_unsigned (low32 v))
  | AD => Z_to_le_bytes 8 (bv_unsigned v)
  end.

(* [comment removed for export] *)
Definition sc_ok (resv : option word) (a : word) : bool :=
  match resv with
  | Some r => Z.eqb (bv_unsigned r) (bv_unsigned a)
  | None => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac boot_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses, ms_pc;
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
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
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_Lui : forall ms w isz rd (imm : bv 20),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Auipc : forall ms w isz rd (imm : bv 20),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (ms_pc_val ms + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Jal : forall ms w isz rd (imm : bv 21),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (ms_pc_val ms + Z_to_bv 64 isz)
                  (ms_pc_val ms + sext 64 imm) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Jalr : forall ms w isz rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (ms_pc_val ms + Z_to_bv 64 isz)
                  (bv_and (rg ms rs1 + sext 64 imm) (bv_not w1)) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 imm Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Branch : forall ms w isz bc rs1 rs2 (imm : bv 13),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch bc rs1 rs2 imm, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms 0 w0
                  (if branch_taken bc (rg ms rs1) (rg ms rs2)
                   then ms_pc_val ms + sext 64 imm
                   else ms_pc_val ms + Z_to_bv 64 isz)
                  (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz bc rs1 rs2 imm Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; rewrite is_x0_0; reflexivity.
Qed.

Lemma step_OpImm : forall ms w isz op rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs1 imm, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (alu64 op (rg ms rs1) (sext 64 imm))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 imm Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_ShiftImm : forall ms w isz op rd rs1 (shamt : bv 6),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs1 shamt, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (alu64 op (rg ms rs1) (zext 64 shamt))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 shamt Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Op : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (alu64 op (rg ms rs1) (rg ms rs2))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_OpImm32 : forall ms w isz rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs1 imm, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (sext 64 (alu32 ALU_ADD (low32 (rg ms rs1)) (sext 32 imm)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 imm Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_ShiftImm32 : forall ms w isz op rd rs1 (shamt : bv 5),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs1 shamt, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (sext 64 (alu32 op (low32 (rg ms rs1)) (zext 32 shamt)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 shamt Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Op32 : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (sext 64 (alu32 op (low32 (rg ms rs1)) (low32 (rg ms rs2))))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Mul : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (mul_div op (rg ms rs1) (rg ms rs2))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Mul32 : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (sext 64 (mul_div op (low32 (rg ms rs1)) (low32 (rg ms rs2))))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Fence : forall ms w isz fm pred succ rd rs1,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence fm pred succ rd rs1, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz fm pred succ rd rs1 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx; rewrite is_x0_0; reflexivity.
Qed.

Lemma step_FenceI : forall ms w isz rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI rd rs1 imm, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 imm Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx; rewrite is_x0_0; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ms_reg_rg : forall ms r, ms_reg ms r = rg ms r.
Proof. reflexivity. Qed.

Lemma step_Ecall : forall ms w,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs ms =
  MachineOk {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
               ms_pc_val := ms_pc_val ms;
               ms_svc_pending := Some (rg ms 17);
               ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
               ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Proof.
  intros ms w Hfetch Hecall.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses, ms_pc.
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_Load : forall ms w isz sz sg rd rs1 (imm : bv 12) bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, isz) ->
  rdn segs (ms_mem ms) (rg ms rs1 + sext 64 imm) (msz_n sz) = Some bs ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (load_word sz sg bs)
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz sz sg rd rs1 imm bs Hfetch Hecall Hdecode Hread.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hread.
  destruct sz; destruct sg; cbv beta iota delta [msz_n load_word] in *;
    rewrite ov_rdn, Hread; cbv beta iota;
    unfold setx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Store : forall ms w isz sz rs1 rs2 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, isz) ->
  store_ok segs (ms_mem ms) (rg ms rs1 + sext 64 imm) (msz_n sz) = true ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1 + sext 64 imm) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1 + sext 64 imm)
                                (store_bytes sz (rg ms rs2)))).
Proof.
  intros ms w isz sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hok.
  unfold setx, inval, rg; rewrite is_x0_0.
  destruct sz; cbv beta iota delta [msz_n store_bytes] in *;
    rewrite Hok; cbv beta iota;
    destruct (ms_resv ms) as [r|]; [|reflexivity| |reflexivity| |reflexivity| |reflexivity];
    destruct (Z.eqb (bv_unsigned r) _); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_Load_fault : forall ms w isz sz sg rd rs1 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, isz) ->
  rdn segs (ms_mem ms) (rg ms rs1 + sext 64 imm) (msz_n sz) = None ->
  RiscvSemantics.step segs ms = MachineFault.
Proof.
  intros ms w isz sz sg rd rs1 imm Hfetch Hecall Hdecode Hread.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hread.
  destruct sz; destruct sg; cbv beta iota delta [msz_n] in *;
    rewrite ov_rdn, Hread; reflexivity.
Qed.

Lemma step_Store_fault : forall ms w isz sz rs1 rs2 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, isz) ->
  store_ok segs (ms_mem ms) (rg ms rs1 + sext 64 imm) (msz_n sz) = false ->
  RiscvSemantics.step segs ms = MachineFault.
Proof.
  intros ms w isz sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hok.
  destruct sz; cbv beta iota delta [msz_n] in *; rewrite Hok; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_Lr : forall ms w isz wd aq rl rd rs1 bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr wd aq rl rd rs1, isz) ->
  amo_aligned wd (rg ms rs1) = true ->
  rdn segs (ms_mem ms) (rg ms rs1) (amo_n wd) = Some bs ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (lr_word wd bs)
                  (ms_pc_val ms + Z_to_bv 64 isz) (Some (rg ms rs1)) (ms_mem ms)).
Proof.
  intros ms w isz wd aq rl rd rs1 bs Hfetch Hecall Hdecode Hal Hread.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hal, Hread. unfold setx, rg. rewrite Hal. cbv beta iota delta [negb].
  destruct wd; cbv beta iota delta [amo_n lr_word] in *;
    rewrite ov_rdn, Hread; cbv beta iota;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Sc_ok : forall ms w isz wd aq rl rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, isz) ->
  amo_aligned wd (rg ms rs1) = true ->
  sc_ok (ms_resv ms) (rg ms rs1) = true ->
  store_ok segs (ms_mem ms) (rg ms rs1) (amo_n wd) = true ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd w0 (ms_pc_val ms + Z_to_bv 64 isz) None
                  (write_to_mem (ms_mem ms) (rg ms rs1) (sc_bytes wd (rg ms rs2)))).
Proof.
  intros ms w isz wd aq rl rd rs1 rs2 Hfetch Hecall Hdecode Hal Hres Hok.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg, sc_ok in Hal, Hres, Hok. unfold setx, rg. rewrite Hal. cbv beta iota delta [negb].
  rewrite Hres.
  destruct wd; cbv beta iota delta [amo_n sc_bytes] in *;
    rewrite Hok; cbv beta iota;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Sc_fail : forall ms w isz wd aq rl rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, isz) ->
  amo_aligned wd (rg ms rs1) = true ->
  sc_ok (ms_resv ms) (rg ms rs1) = false ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd w1 (ms_pc_val ms + Z_to_bv 64 isz) None (ms_mem ms)).
Proof.
  intros ms w isz wd aq rl rd rs1 rs2 Hfetch Hecall Hdecode Hal Hres.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg, sc_ok in Hal, Hres. unfold setx, rg. rewrite Hal. cbv beta iota delta [negb].
  rewrite Hres. cbv beta iota.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_Amo_w : forall ms w isz op aq rl rd rs1 rs2 bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op AW aq rl rd rs1 rs2, isz) ->
  amo_aligned AW (rg ms rs1) = true ->
  rdn segs (ms_mem ms) (rg ms rs1) 4 = Some bs ->
  store_ok segs (ms_mem ms) (rg ms rs1) 4 = true ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))
                  (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1)
                     (Z_to_le_bytes 4 (bv_unsigned
                        (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 (rg ms rs2))))))).
Proof.
  intros ms w isz op aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hal, Hread, Hok. unfold setx, inval, rg. rewrite Hal. cbv beta iota delta [negb].
  rewrite ov_rdn, Hread. cbv beta iota. rewrite Hok. cbv beta iota.
  destruct (ms_resv ms) as [r|];
    [destruct (Z.eqb (bv_unsigned r) _)|];
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Amo_d : forall ms w isz op aq rl rd rs1 rs2 bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op AD aq rl rd rs1 rs2, isz) ->
  amo_aligned AD (rg ms rs1) = true ->
  rdn segs (ms_mem ms) (rg ms rs1) 8 = Some bs ->
  store_ok segs (ms_mem ms) (rg ms rs1) 8 = true ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (bv_extract 0 64 (le_bytes_to_word bs))
                  (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1)
                     (Z_to_le_bytes 8 (bv_unsigned
                        (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) (rg ms rs2)))))).
Proof.
  intros ms w isz op aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hal, Hread, Hok. unfold setx, inval, rg. rewrite Hal. cbv beta iota delta [negb].
  rewrite ov_rdn, Hread. cbv beta iota. rewrite Hok. cbv beta iota.
  destruct (ms_resv ms) as [r|];
    [destruct (Z.eqb (bv_unsigned r) _)|];
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_FLoad_d : forall ms w isz rd rs1 (imm : bv 12) bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (FLoad FMT_D rd rs1 imm, isz) ->
  rdn segs (ms_mem ms) (rg ms rs1 + sext 64 imm) 8 = Some bs ->
  RiscvSemantics.step segs ms =
  MachineOk (setf ms rd (bv_extract 0 64 (le_bytes_to_word bs))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 imm bs Hfetch Hecall Hdecode Hread.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hread. unfold setf, rg.
  rewrite ov_rdn, Hread; cbv beta iota; reflexivity.
Qed.

Lemma step_FLoad_s : forall ms w isz rd rs1 (imm : bv 12) bs,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (FLoad FMT_S rd rs1 imm, isz) ->
  rdn segs (ms_mem ms) (rg ms rs1 + sext 64 imm) 4 = Some bs ->
  RiscvSemantics.step segs ms =
  MachineOk (setf ms rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 imm bs Hfetch Hecall Hdecode Hread.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hread. unfold setf, rg.
  rewrite ov_rdn, Hread; cbv beta iota; reflexivity.
Qed.

Lemma step_FStore_d : forall ms w isz rs1 rs2 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (FStore FMT_D rs1 rs2 imm, isz) ->
  store_ok segs (ms_mem ms) (rg ms rs1 + sext 64 imm) 8 = true ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1 + sext 64 imm) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1 + sext 64 imm)
                                (Z_to_le_bytes 8 (bv_unsigned (fg ms rs2))))).
Proof.
  intros ms w isz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hok. unfold setx, inval, rg, fg; rewrite is_x0_0.
  rewrite Hok; cbv beta iota.
  destruct (ms_resv ms) as [r|]; [|reflexivity].
  destruct (Z.eqb (bv_unsigned r) _); reflexivity.
Qed.

Lemma step_FStore_s : forall ms w isz rs1 rs2 (imm : bv 12),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (FStore FMT_S rs1 rs2 imm, isz) ->
  store_ok segs (ms_mem ms) (rg ms rs1 + sext 64 imm) 4 = true ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms 0 w0 (ms_pc_val ms + Z_to_bv 64 isz)
                  (inval (rg ms rs1 + sext 64 imm) (ms_resv ms))
                  (write_to_mem (ms_mem ms) (rg ms rs1 + sext 64 imm)
                                (Z_to_le_bytes 4 (bv_unsigned (low32 (fg ms rs2)))))).
Proof.
  intros ms w isz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold rg in Hok. unfold setx, inval, rg, fg; rewrite is_x0_0.
  rewrite Hok; cbv beta iota.
  destruct (ms_resv ms) as [r|]; [|reflexivity].
  destruct (Z.eqb (bv_unsigned r) _); reflexivity.
Qed.

Lemma step_Fmv_xd : forall ms w isz rd rs1,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_X_F FMT_D rd rs1, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (fg ms rs1)
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, fg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Fmv_dx : forall ms w isz rd rs1,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_F_X FMT_D rd rs1, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setf ms rd (rg ms rs1)
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setf, rg; reflexivity.
Qed.

Lemma step_Fmv_xs : forall ms w isz rd rs1,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_X_F FMT_S rd rs1, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setx ms rd (sext 64 (low32 (fg ms rs1)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setx, fg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_Fmv_sx : forall ms w isz rd rs1,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_F_X FMT_S rd rs1, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setf ms rd (nan_box (low32 (rg ms rs1)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz rd rs1 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setf, rg; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_Fsgnj_d : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj op FMT_D rd rs1 rs2, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setf ms rd (sgnj_val op (fg ms rs1) (fg ms rs2))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setf, fg; reflexivity.
Qed.

Lemma step_Fsgnj_s : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj op FMT_S rd rs1 rs2, isz) ->
  RiscvSemantics.step segs ms =
  MachineOk (setf ms rd (nan_box (sgnj_val op (unbox_s (fg ms rs1)) (unbox_s (fg ms rs2))))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  boot_pipeline Hfetch Hecall Hdecode.
  unfold setf, fg; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_extract_64_id : forall v : word, bv_extract 0 64 v = v.
Proof.
  intro v. apply bv_eq.
  rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma low32_zext32 : forall v : bv 32, low32 (zext 64 v) = v.
Proof.
  intro v. apply bv_eq. unfold low32, zext.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, bv_zero_extend_unsigned by lia.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma load_word_SZ8 : forall sg bs, load_word SZ8 sg bs = le_bytes_to_word bs.
Proof. intros. cbn [load_word]. apply bv_extract_64_id. Qed.

Lemma lr_word_AW : forall bs, lr_word AW bs = load_word SZ4 true bs.
Proof. reflexivity. Qed.

Lemma lr_word_AD : forall bs, lr_word AD bs = load_word SZ8 false bs.
Proof. reflexivity. Qed.

Lemma sc_bytes_AW : forall v, sc_bytes AW v = store_bytes SZ4 v.
Proof. reflexivity. Qed.

Lemma sc_bytes_AD : forall v, sc_bytes AD v = store_bytes SZ8 v.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma amo_w_bytes : forall nw : bv 32,
  Z_to_le_bytes 4 (bv_unsigned nw) = store_bytes SZ4 (zext 64 nw).
Proof. intro nw. cbn [store_bytes]. rewrite low32_zext32. reflexivity. Qed.

Lemma amo_d_bytes : forall nw : word,
  Z_to_le_bytes 8 (bv_unsigned nw) = store_bytes SZ8 nw.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sext64_Z_to_bv : forall {n} (imm : bv n), sext 64 imm = Z_to_bv 64 (bv_signed imm).
Proof.
  intros n imm. apply bv_eq. unfold sext.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

Lemma ea_sext : forall (a : word) {n} (imm : bv n),
  a + sext 64 imm = a + Z_to_bv 64 (bv_signed imm).
Proof. intros. rewrite sext64_Z_to_bv. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rg_x0 : forall ms r, is_x0 r = true -> rg ms r = w0.
Proof. intros ms r H. unfold rg. rewrite H. reflexivity. Qed.

Lemma setx_x0_regs : forall ms v p s m, ms_regs (setx ms 0 v p s m) = ms_regs ms.
Proof. intros. unfold setx; cbn [ms_regs]. rewrite is_x0_0. reflexivity. Qed.

Lemma rg_setx_x0 : forall ms v p s m r, rg (setx ms 0 v p s m) r = rg ms r.
Proof. intros. unfold rg. rewrite setx_x0_regs. reflexivity. Qed.

Lemma rg_setx_same : forall ms rd v p s m,
  is_x0 rd = false -> rg (setx ms rd v p s m) rd = v.
Proof.
  intros ms rd v p s m H. unfold rg, setx; cbn [ms_regs]. rewrite H.
  unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

Lemma rg_setx_other : forall ms rd v p s m r,
  r <> rd -> rg (setx ms rd v p s m) r = rg ms r.
Proof.
  intros ms rd v p s m r H. unfold rg, setx; cbn [ms_regs].
  destruct (is_x0 r); [reflexivity|].
  destruct (is_x0 rd); [reflexivity|].
  unfold reg_get. rewrite bvmap_get_set_other by congruence. reflexivity.
Qed.

Lemma fg_setx : forall ms rd v p s m r, fg (setx ms rd v p s m) r = fg ms r.
Proof. reflexivity. Qed.

Lemma rg_setf : forall ms rd v p s m r, rg (setf ms rd v p s m) r = rg ms r.
Proof. reflexivity. Qed.

Lemma fg_setf_same : forall ms rd v p s m, fg (setf ms rd v p s m) rd = v.
Proof.
  intros. unfold fg, setf; cbn [ms_fregs].
  unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

Lemma fg_setf_other : forall ms rd v p s m r,
  r <> rd -> fg (setf ms rd v p s m) r = fg ms r.
Proof.
  intros ms rd v p s m r H. unfold fg, setf; cbn [ms_fregs].
  unfold reg_get. rewrite bvmap_get_set_other by congruence. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac dec_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Lemma word32_of_unsigned : forall (x : bv 32) (z : Z),
  (bv_unsigned x =? z)%Z = true -> x = Z_to_bv 32 z.
Proof.
  intros x z H. apply Z.eqb_eq in H. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- H. symmetry. apply bv_wrap_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma decode_0004b503 : decode_any (Z_to_bv 32 0x0004b503) = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. dec_refl. Qed.
Lemma decode_00848493 : decode_any (Z_to_bv 32 0x00848493) = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. dec_refl. Qed.
Lemma decode_fe051ce3 : decode_any (Z_to_bv 32 0xfe051ce3) = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. dec_refl. Qed.
(* [comment removed for export] *)
Lemma decode_00b53023 : decode_any (Z_to_bv 32 0x00b53023) = Some (Store SZ8 10 11 0, 4%Z).
Proof. dec_refl. Qed.
Lemma decode_00158593 : decode_any (Z_to_bv 32 0x00158593) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. dec_refl. Qed.
Lemma decode_fff5c683 : decode_any (Z_to_bv 32 0xfff5c683) = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. dec_refl. Qed.
Lemma decode_fec68ae3 : decode_any (Z_to_bv 32 0xfec68ae3) = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. dec_refl. Qed.
Lemma decode_fe069ae3 : decode_any (Z_to_bv 32 0xfe069ae3) = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. dec_refl. Qed.

Lemma not_ecall_0004b503 : is_ecall (Z_to_bv 32 0x0004b503) = false. Proof. reflexivity. Qed.
Lemma not_ecall_00848493 : is_ecall (Z_to_bv 32 0x00848493) = false. Proof. reflexivity. Qed.
Lemma not_ecall_fe051ce3 : is_ecall (Z_to_bv 32 0xfe051ce3) = false. Proof. reflexivity. Qed.
Lemma not_ecall_00b53023 : is_ecall (Z_to_bv 32 0x00b53023) = false. Proof. reflexivity. Qed.
Lemma not_ecall_00158593 : is_ecall (Z_to_bv 32 0x00158593) = false. Proof. reflexivity. Qed.
Lemma not_ecall_fff5c683 : is_ecall (Z_to_bv 32 0xfff5c683) = false. Proof. reflexivity. Qed.
Lemma not_ecall_fec68ae3 : is_ecall (Z_to_bv 32 0xfec68ae3) = false. Proof. reflexivity. Qed.
Lemma not_ecall_fe069ae3 : is_ecall (Z_to_bv 32 0xfe069ae3) = false. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_of_step : forall SC M ms ms',
  m_halted M = None -> m_vm_lazy M = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep_cfg segs SC (mkCfg ms M) [] (SNext (mkCfg ms' M)).
Proof.
  intros SC M ms ms' Hh Hl Hsvc Hstep.
  apply sstep_cfg_instr; [exact Hh|exact Hsvc|].
  rewrite (mi_account_step_no_lazy segs ms M Hl), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive mrun : machine_state -> machine_state -> Prop :=
| mrun_refl : forall ms, mrun ms ms
| mrun_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    mrun ms' ms'' -> mrun ms ms''.

Lemma mrun_one : forall ms ms',
  ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms' -> mrun ms ms'.
Proof. intros ms ms' Hs Hst. eapply mrun_step; [exact Hs|exact Hst|apply mrun_refl]. Qed.

Lemma mrun_trans : forall ms1 ms2 ms3, mrun ms1 ms2 -> mrun ms2 ms3 -> mrun ms1 ms3.
Proof.
  intros ms1 ms2 ms3 H12 H23. induction H12 as [ms|ms ms' ms'' Hs Hst H IH]; [exact H23|].
  eapply mrun_step; [exact Hs|exact Hst|exact (IH H23)].
Qed.

Lemma mrun_star : forall SC M ms ms',
  m_halted M = None -> m_vm_lazy M = [] ->
  mrun ms ms' -> star_cfg segs SC (mkCfg ms M) [] (mkCfg ms' M).
Proof.
  intros SC M ms ms' Hh Hl H. induction H as [ms|ms ms1 ms2 Hs Hst H IH]; [apply star_cfg_refl|].
  exact (star_cfg_step segs SC _ [] _ [] _ (sstep_of_step SC M ms ms1 Hh Hl Hs Hst) IH).
Qed.

End WithSegs.
