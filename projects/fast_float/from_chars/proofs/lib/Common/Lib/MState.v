(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Definition W64 : Type := bv 64.
(* [comment removed for export] *)
Fixpoint tset64 (p : positive) (x : bv 64) (t : tree W64) : tree W64 :=
  match t with
  | TEmpty =>
      match p with
      | xH => @TNode W64 TEmpty (@Some (bv 64) x) TEmpty
      | xO p => @TNode W64 (tset64 p x TEmpty) None TEmpty
      | xI p => @TNode W64 TEmpty None (tset64 p x TEmpty)
      end
  | TNode l v r =>
      match p with
      | xH => @TNode W64 l (@Some (bv 64) x) r
      | xO p => @TNode W64 (tset64 p x l) v r
      | xI p => @TNode W64 l v (tset64 p x r)
      end
  end.

(* [comment removed for export] *)
Definition MS (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
           (m ro : word -> option byte) : machine_state :=
  {| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None;
     ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

Definition MSsvc (R F : bvmap 5 word) (pc : word) (x8 : word) (fc : bv 32) (rv : option word)
           (m ro : word -> option byte) : machine_state :=
  {| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := Some x8;
     ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

(* [comment removed for export] *)
Definition MS_of_core (c : core) (m ro : word -> option byte) : machine_state :=
  MS (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m ro.

Lemma MS_eta : forall ms, ms_svc_pending ms = None ->
  ms = MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H; cbn in *; subst; reflexivity. Qed.

(* [comment removed for export] *)

Definition lift_result (ro : word -> option byte) (r : machine_result (core * (word -> option byte)))
  : machine_result machine_state :=
  match r with
  | MachineOk (c, m') => MachineOk (MS_of_core c m' ro)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

(* [comment removed for export] *)
Section WithSegsIeff.
Variable segs : list Segment.

Fixpoint ieff (t : eff) (m : word -> option byte)
    : machine_result (core * (word -> option byte)) :=
  match t with
  | EDone c => MachineOk (c, m)
  | EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault
  | EIllegal _ | EEcall _ => MachineUnmodeled
  | ELoad n a k =>
      match ov_read_bytes segs m a (width_bytes n) with
      | Some bs => ieff (k (bv_extract 0 n (le_bytes_to_word bs))) m
      | None => MachineFault
      end
  | EStore n a v k =>
      if store_ok segs m a (width_bytes n)
      then ieff k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
      else MachineFault
  end.

#[using="Type"] Lemma interp_eff_accesses_ieff : forall t m,
  match interp_eff_accesses segs t m with
  | MachineOk r => MachineOk (@access_value _ r)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end = ieff t m.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction t; intros m; cbn [interp_eff_accesses ieff]; try reflexivity.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|reflexivity].
    rewrite <- H. destruct (interp_eff_accesses segs _ m) as [r| |]; reflexivity.
  - destruct (store_ok segs m a (width_bytes n)); [|reflexivity].
    rewrite <- IHt. destruct (interp_eff_accesses segs t _) as [r| |]; reflexivity.
Qed.

#[using="Type"] Lemma interp_eff_ieff : forall t m, interp_eff segs t m = ieff t m.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t m. unfold interp_eff, drop_access_report. rewrite <- interp_eff_accesses_ieff.
  destruct (interp_eff_accesses segs t m) as [[v acc]| |]; reflexivity.
Qed.

#[using="Type"] Lemma step_gen : forall R F pc fc rv m ro w i sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  RiscvSemantics.step segs (MS R F pc fc rv m ro) =
  lift_result ro (ieff (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R F pc fc rv m ro w i sz Hf He Hd.
  unfold RiscvSemantics.step, step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He, Hd.
  cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS].
  rewrite <- interp_eff_accesses_ieff. unfold drop_access_report.
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) m) as [[[c m'] acc]| |]; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_ecall_gen : forall R F pc fc rv m ro w,
  fetch_word segs pc = Some w ->
  is_ecall w = true ->
  RiscvSemantics.step segs (MS R F pc fc rv m ro) =
  MachineOk (MSsvc R F pc (if is_x0 17 then w0 else reg_get R 17) fc rv m ro).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R F pc fc rv m ro w Hf He.
  unfold RiscvSemantics.step, step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma decode_exec_old : forall st w,
  decode_exec segs st w =
  if is_ecall w then
    MachineOk
      {| ms_regs := ms_regs st; ms_fregs := ms_fregs st;
         ms_pc_val := ms_pc_val st;
         ms_svc_pending := Some (ms_reg st 17);
         ms_resv := ms_resv st; ms_fcsr := ms_fcsr st;
         ms_mem := st.(ms_mem);
         ms_rom := st.(ms_rom) |}
  else
    match decode_any w with
    | None => if is_defined_illegal w then MachineFault else MachineUnmodeled
    | Some (i, isz) =>
      match interp_eff segs (exec (Z_to_bv 64 isz) i
                           {| c_regs := st.(ms_regs);
                              c_fregs := st.(ms_fregs);
                              c_pc := st.(ms_pc_val);
                              c_fcsr := st.(ms_fcsr);
                              c_resv := st.(ms_resv) |})
                        st.(ms_mem) with
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
      | MachineOk (c, m') =>
        MachineOk
          {| ms_regs := c.(c_regs); ms_fregs := c.(c_fregs);
             ms_pc_val := c.(c_pc);
             ms_svc_pending := None;
             ms_resv := c.(c_resv); ms_fcsr := c.(c_fcsr);
             ms_mem := m';
             ms_rom := st.(ms_rom) |}
      end
    end.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros st w. unfold decode_exec, decode_exec_accesses, interp_eff, drop_access_report.
  destruct (is_ecall w); [reflexivity|].
  destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); reflexivity].
  destruct (interp_eff_accesses segs _ _) as [[[c m'] acc]| |]; reflexivity.
Qed.

#[using="Type"] Lemma step_old : forall st,
  RiscvSemantics.step segs st =
  match fetch_word segs (ms_pc st) with
  | Some w => decode_exec segs st w
  | None =>
    match fetch_word_ov segs st.(ms_mem) (ms_pc st) with
    | Some w => decode_exec segs st w
    | None =>
      match fetch_tail_any segs st.(ms_mem) (ms_pc st) with
      | Some w => decode_exec segs st w
      | None => fetch_failure segs st.(ms_mem) (ms_pc st)
      end
    end
  end.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros st. unfold RiscvSemantics.step, step_accesses, decode_exec.
  destruct (fetch_word segs (ms_pc st)); [reflexivity|].
  destruct (fetch_word_ov segs _ _); [reflexivity|].
  destruct (fetch_tail_any segs _ _); [reflexivity|].
  unfold drop_access_report. destruct (fetch_failure _ _ _); reflexivity.
Qed.

End WithSegsIeff.

(* [comment removed for export] *)

Lemma reg_get_set_same : forall (R : bvmap 5 word) (r : reg) v,
  reg_get (bvmap_set r v R) r = v.
Proof. intros. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.

Lemma reg_get_set_other : forall (R : bvmap 5 word) (r r' : reg) v,
  r <> r' -> reg_get (bvmap_set r v R) r' = reg_get R r'.
Proof. intros. unfold reg_get. rewrite bvmap_get_set_other by assumption. reflexivity. Qed.

(* [comment removed for export] *)

Lemma w0_lit : w0 = Z_to_bv 64 0. Proof. reflexivity. Qed.
Lemma w1_lit : w1 = Z_to_bv 64 1. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lit_add_lit : forall a b, (Z_to_bv 64 a + Z_to_bv 64 b : word) = Z_to_bv 64 (a + b).
Proof.
  intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma v_addi_lit : forall p i, v_addi (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof.
  intros p i. unfold v_addi. rewrite Z_to_bv_unsigned. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addi_assoc : forall (x : word) a b,
  v_addi (Z_to_bv 64 (bv_unsigned x + a)) b = Z_to_bv 64 (bv_unsigned x + (a + b)).
Proof.
  intros. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma v_addi_var : forall (x : word) b, v_addi x b = Z_to_bv 64 (bv_unsigned x + b).
Proof. reflexivity. Qed.

Lemma Z_to_bv_bv_unsigned : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv_plus0 : forall (x : word), Z_to_bv 64 (bv_unsigned x + 0) = x.
Proof. intros. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma unsigned_lit : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Lemma unsigned_lit_wrap : forall z, bv_unsigned (Z_to_bv 64 z) = (z mod 2^64)%Z.
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Definition ret_pc (ra : word) : word := bv_and ra (bv_not (Z_to_bv 64 1)).

Lemma ret_pc_fold : forall ra, bv_and ra (bv_not (Z_to_bv 64 1)) = ret_pc ra.
Proof. reflexivity. Qed.

Lemma ret_pc_even : forall z, (0 <= z < 2^64)%Z -> (z mod 2 = 0)%Z -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz He. unfold ret_pc. apply bv_eq. rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  rewrite !(bv_wrap_small 64 z) by (unfold bv_modulus; lia).
  change (bv_wrap 64 (Z.lnot (bv_wrap 64 1))) with (Z.ones 64 - 1)%Z.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0).
  - subst i. rewrite (Z.bit0_eqb z). replace (z mod 2)%Z with 0%Z by lia. cbn. reflexivity.
  - destruct (Z.ltb_spec0 i 64).
    + replace (Z.testbit (Z.ones 64 - 1) i) with true. { apply andb_true_r. }
      symmetry. change (Z.ones 64 - 1)%Z with (Z.shiftl (Z.ones 63) 1). rewrite Z.shiftl_spec by lia. apply Z.ones_spec_low. lia.
    + rewrite (Z.bits_above_log2 z i); [reflexivity| lia |].
      destruct (Z.eq_dec z 0). { subst. cbn. lia. }
      apply Z.lt_le_trans with 64%Z; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
