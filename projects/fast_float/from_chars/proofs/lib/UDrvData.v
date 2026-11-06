(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation PSEGS := Ubsan.M.loaded_segments.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Definition RS_P : list (Z * nat) :=
  [ (0x228cc, 296%nat);     (* [comment removed for export] *)
    (0x52ac8, 51%nat);      (* [comment removed for export] *)
    (0x60b9c, 3%nat);       (* [comment removed for export] *)
    (0x52910, 3%nat);       (* [comment removed for export] *)
    (0x5265c, 1%nat);       (* [comment removed for export] *)
    (0x52c54, 57%nat);      (* [comment removed for export] *)
    (0x52d98, 16%nat);      (* [comment removed for export] *)
    (0x55574, 498%nat);     (* [comment removed for export] *)
    (0x560a0, 1146%nat);    (* [comment removed for export] *)
    (0x5ab00, 7%nat);       (* [comment removed for export] *)
    (0x55fa0, 40%nat);      (* [comment removed for export] *)
    (0x600a8, 257%nat);     (* [comment removed for export] *)
    (0x60c10, 10%nat);      (* [comment removed for export] *)
    (0x55dd8, 1%nat);       (* [comment removed for export] *)
    (0x60628, 62%nat);      (* [comment removed for export] *)
    (0x61708, 37%nat) ].    (* [comment removed for export] *)

Definition TBL_P : tree xi := Eval vm_compute in mk_tbl_ranges PSEGS RS_P.
Set Default Proof Mode "Ltac2".
Lemma TBL_P_eq : TBL_P = mk_tbl_ranges PSEGS RS_P.
Proof. cert_refl_vm constr:(TBL_P). Qed.
Set Default Proof Mode "Classic".
Lemma TBL_P_ok : tbl_ok PSEGS TBL_P.
Proof. rewrite TBL_P_eq. apply mk_tbl_ranges_ok. Qed.

(* [comment removed for export] *)
Fixpoint mk_imgs_acc (segs : list Segment) (rs : list (Z * nat)) (t : tree Z) : tree Z :=
  match rs with [] => t | (lo, n) :: r => mk_imgs_acc segs r (mk_img_acc segs n (Z.shiftr lo 3) t) end.

Lemma mk_imgs_acc_ok : forall segs rs t, Forall (fun r => 0 <= fst r) rs -> img_ok segs t -> img_ok segs (mk_imgs_acc segs rs t).
Proof.
  intros segs rs. induction rs as [|[lo n] rs IH]; intros t Hf Ht; cbn [mk_imgs_acc]; [exact Ht|].
  apply Forall_cons_iff in Hf as [Hx Hf']. cbn [fst] in Hx. apply IH; [exact Hf'|].
  apply mk_img_acc_ok; [apply Z.shiftr_nonneg; lia | exact Ht].
Qed.

Definition IMGR_P : list (Z * nat) :=
  [ (0x65a18, 43%nat);      (* [comment removed for export] *)
    (0x659a8, 4%nat);       (* [comment removed for export] *)
    (0x66bd8, 60%nat);      (* [comment removed for export] *)
    (0x778e8, 1%nat);       (* [comment removed for export] *)
    (0x97c00, 1%nat);       (* [comment removed for export] *)
    (0x76e20, 3%nat);       (* [comment removed for export] *)
    (0x979d8, 37%nat);      (* [comment removed for export] *)
    (0x98060, 130%nat);     (* [comment removed for export] *)
    (0x10481, 4%nat); (0x10bd5, 5%nat); (0x10f35, 8%nat); (0x11bc5, 6%nat); (0x1287e, 2%nat); (0x125ce, 9%nat);
    (0x12bd6, 6%nat); (0x12f2e, 2%nat); (0x13020, 2%nat); (0x18330, 66%nat) ].

Definition IMG_P : tree Z := Eval vm_compute in mk_imgs_acc PSEGS IMGR_P TEmpty.
Lemma IMG_P_ok : img_ok PSEGS IMG_P.
Proof.
  change (img_ok PSEGS (mk_imgs_acc PSEGS IMGR_P TEmpty)). apply mk_imgs_acc_ok.
  - repeat constructor; cbn; lia.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
