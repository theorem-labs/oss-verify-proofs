(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Definition rg (ms : machine_state) (r : reg) : word :=
  if is_x0 r then w0 else reg_get (ms_regs ms) r.

Definition fg (ms : machine_state) (r : reg) : word := reg_get (ms_fregs ms) r.

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

Definition inval (a : word) (resv : option word) : option word :=
  match resv with
  | Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else resv
  | None => None
  end.

Definition store_bytes (sz : msize) (v : word) : list byte :=
  match sz with
  | SZ1 => Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 v))
  | SZ2 => Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 v))
  | SZ4 => Z_to_le_bytes 4 (bv_unsigned (low32 v))
  | SZ8 => Z_to_le_bytes 8 (bv_unsigned v)
  end.

Definition amo_n (wd : awidth) : nat :=
  match wd with AW => 4%nat | AD => 8%nat end.

Definition lr_word (wd : awidth) (bs : list byte) : word :=
  match wd with
  | AW => sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | AD => bv_extract 0 64 (le_bytes_to_word bs)
  end.

Definition sc_bytes (wd : awidth) (v : word) : list byte :=
  match wd with
  | AW => Z_to_le_bytes 4 (bv_unsigned (low32 v))
  | AD => Z_to_le_bytes 8 (bv_unsigned v)
  end.

Definition sc_ok (resv : option word) (a : word) : bool :=
  match resv with
  | Some r => Z.eqb (bv_unsigned r) (bv_unsigned a)
  | None => false
  end.

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

Lemma bv_extract_64_id : forall v : word, bv_extract 0 64 v = v.
Proof.
  intro v. apply bv_eq.
  rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma load_word_SZ8 : forall sg bs, load_word SZ8 sg bs = le_bytes_to_word bs.
Proof. intros. cbn [load_word]. apply bv_extract_64_id. Qed.

Lemma sext64_Z_to_bv : forall {n} (imm : bv n), sext 64 imm = Z_to_bv 64 (bv_signed imm).
Proof.
  intros n imm. apply bv_eq. unfold sext.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

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

Ltac dec_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_compute; reflexivity
  end.

Inductive mrun : machine_state -> machine_state -> Prop :=
| mrun_refl : forall ms, mrun ms ms
| mrun_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    mrun ms' ms'' -> mrun ms ms''.

End WithSegs.
