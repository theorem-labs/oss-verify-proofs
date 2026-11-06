(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec FP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition csr_frmw (csr : bv 12) : bool := (bv_unsigned csr =? 2) || (bv_unsigned csr =? 3).

Definition frm_safe (i : instr) : bool :=
  match i with
  | Csr op _ rs1 csr => negb ((match op with CSR_RW => true | _ => negb (is_x0 rs1) end) && csr_frmw csr)
  | CsrI op _ uimm csr =>
      negb ((match op with CSR_RW => true | _ => negb (Z.eqb (bv_unsigned uimm) 0) end) && csr_frmw csr)
  | _ => true
  end.

(* [comment removed for export] *)
Fixpoint eff_all (P : core -> Prop) (t : eff) : Prop :=
  match t with
  | EDone c => P c
  | ELoad n a k => forall v, eff_all P (k v)
  | EStore n a v k => eff_all P k
  | _ => True
  end.

Lemma interp_eff_all : forall (P : core -> Prop) segs t m r,
  interp_eff_accesses segs t m = MachineOk r -> eff_all P t -> P (fst (access_value _ r)).
Proof.
  intros P segs t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r H HA; cbn [interp_eff_accesses eff_all] in H, HA;
    try discriminate.
  - injection H as <-. exact HA.
  - destruct (ov_read_bytes _ _ _ _) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:E; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ m rep E (HA _)).
  - destruct (store_ok _ _ _ _); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [rep| |] eqn:E; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ rep E HA).
Qed.

Lemma csr_slice_fflags : forall csr lo len, csr_slice csr = Some (lo, len) -> csr_frmw csr = false -> lo = 0 /\ len = 5.
Proof.
  intros csr lo len H Hf. unfold csr_slice, csr_frmw in *. cbv zeta in H.
  destruct (bv_unsigned csr =? 1); [injection H as <- <-; split; reflexivity|].
  destruct (bv_unsigned csr =? 2); [discriminate|]. destruct (bv_unsigned csr =? 3); discriminate.
Qed.

Lemma fcsr_rset : forall r v c, c_fcsr (rset r v c) = c_fcsr c.
Proof. intros r v c. unfold rset. destruct (is_x0 r); reflexivity. Qed.

Lemma exec_csr_frm : forall op rd operand writes csr c,
  negb (writes && csr_frmw csr) = true -> frm0 (c_fcsr c) -> eff_all (fun c' => frm0 (c_fcsr c')) (exec_csr op rd operand writes csr c).
Proof.
  intros op rd operand writes csr c Hs H0. unfold exec_csr.
  destruct (csr_slice csr) as [[lo len]|] eqn:E; cbn [eff_all]; [|exact I]. rewrite fcsr_rset.
  destruct writes; [|exact H0]. cbn [andb negb] in Hs. apply negb_true_iff in Hs.
  destruct (csr_slice_fflags csr lo len E Hs) as [-> ->]. cbn [with_fcsr c_fcsr]. apply frm0_slice_set_fflags. exact H0.
Qed.

Lemma fcsr_fwrite : forall fmt r v c, c_fcsr (fwrite fmt r v c) = c_fcsr c.
Proof. intros fmt r v c. destruct fmt; reflexivity. Qed.
Lemma fcsr_inval_resv : forall a c, c_fcsr (inval_resv a c) = c_fcsr c.
Proof. intros a c. unfold inval_resv. destruct (c_resv c); [destruct (_ =? _)|]; reflexivity. Qed.
Lemma fcsr_accrue : forall fl c, c_fcsr (accrue fl c) = Z_to_bv 32 (Z.lor (bv_unsigned (c_fcsr c)) (fflags_bits fl)).
Proof. intros fl c. reflexivity. Qed.

Ltac frm_leaf H0 := first [ exact I | exact H0 | (apply frm0_accrue; exact H0) ].
Ltac frm_go H0 :=
  repeat (first [ frm_leaf H0
                | progress intros
                | progress (rewrite ?fcsr_rset, ?fcsr_fwrite, ?fcsr_inval_resv, ?fcsr_accrue)
                | progress (cbn [eff_all c_fcsr with_pc with_resv with_regs with_fregs with_fcsr fset load_val store_val])
                | match goal with
                  | |- context [load_val ?s _ _ _] => is_var s; destruct s
                  | |- context [store_val ?s _ _ _] => is_var s; destruct s
                  | |- context [match ?x with _ => _ end] => destruct x
                  end ]).

Lemma exec_frm : forall sz i c, frm_safe i = true -> frm0 (c_fcsr c) ->
  eff_all (fun c' => frm0 (c_fcsr c')) (exec sz i c).
Proof.
  intros sz i [R F pc fc rv] Hs H0. cbn [c_fcsr] in H0.
  destruct i; cbn [frm_safe] in Hs; cbn [exec]; cbv zeta.
  all: try (destruct (csr_write_illegal _ _); [exact I | apply exec_csr_frm; [exact Hs | exact H0]]).
  all: frm_go H0.
Qed.

