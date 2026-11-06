(* Helpers of batch b8c (segments C01-C03 of fuzz_ctrl LLVMFuzzerTestOneInput, plain): byte loads and compares,
   the C4 cell of a store as a CB cell, the kind's range and frame size, and the side-goal tactics. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_b8 Tac_b8m.
Import ListNotations.
Open Scope Z_scope.

Lemma b8c_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (b8_bz_range b) as H. exact H. Qed.

Lemma b8c_eqb_zxb : forall (b : byte) c, 0 <= c < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (b8c_byte_range b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma b8c_firstn1 : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|x bs IH]; intros k d H; cbn in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma b8c_cp_b : forall fr i v, cp_v fr i = v -> 0 <= v < 256 -> cp_b fr i = Z_to_bv 8 v.
Proof.
  intros fr i v E Hv. apply bv_eq. unfold cp_v in E. rewrite E. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small; lia.
Qed.

(* The C4 cell a 4-byte store leaves, as the CB cell a callee premise asks for. *)
Lemma b8c_c4_cb : forall m A v, rw_cells rsegs m A [C4 v] -> rw_cells rsegs m A [CB 4 (le4 v)].
Proof.
  intros m A v [[_ Hb] Hw]. split; [split; [split; [apply length_le4 | exact I] | exact Hb] | exact Hw].
Qed.

Lemma b8c_c8_wr : forall m A v, rw_cells rsegs m A [C8 v] -> wr_at rsegs m A 8.
Proof. intros m A v [_ Hw]. exact Hw. Qed.

(* The kind k = fst (ctrlparse len g): 0 .. 13, and k <> 0 only for a frame of 50 bytes or more. *)
Lemma b8c_k_range : forall inp j, 0 <= t_k inp j <= 13.
Proof.
  intros inp j. unfold t_k, ctrlparse. destruct (cp_hdr _ _); cbn [fst]; [|lia].
  pose proof (cp_kind_range (t_g inp j)). lia.
Qed.

Lemma b8c_k_big : forall inp j, t_k inp j <> 0 -> 50 <= t_len inp j.
Proof.
  intros inp j K. unfold t_k in K. destruct (cp_hdr (t_len inp j) (t_g inp j)) eqn:E.
  - apply cp_hdr_spec in E as (E1 & _). exact E1.
  - unfold ctrlparse in K. rewrite E in K. cbn in K. lia.
Qed.

Ltac b8c_out := cbn [outside]; repeat split; try exact I; lia.

Ltac b8c_sub :=
  unfold sub_fp; let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in *; repeat split; try exact I; lia.

(* A branch arm that the facts in context exclude. *)
Ltac b8c_bad HC :=
  exfalso;
  first [ congruence
        | discriminate HC
        | (rewrite ?b8c_eqb_zxb, ?b8_eqb_lit in HC by lia; cbn [negb] in HC;
           first [ (apply Bool.negb_true_iff in HC; apply Z.eqb_neq in HC; lia)
                 | (apply Bool.negb_false_iff in HC; apply Z.eqb_eq in HC; lia)
                 | (apply Z.eqb_eq in HC; lia)
                 | (apply Z.eqb_neq in HC; lia)
                 | discriminate HC ])
        | (zify_cond HC; rewrite ?unsigned_lit in HC by lia; lia)
        | (vm_compute in HC; discriminate HC) ].

(* A conditional branch that is not taken (b8c_nt) or taken (b8c_tk); no-op when step already chose the arm. *)
Ltac b8c_nt := first [ let H := fresh "HC" in if_cases H; [b8c_bad H | clear H] | idtac ].
Ltac b8c_tk := first [ let H := fresh "HC" in if_cases H; [clear H | b8c_bad H] | idtac ].
