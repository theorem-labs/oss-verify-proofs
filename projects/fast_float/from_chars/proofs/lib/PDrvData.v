(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation PSEGS := Plain.M.loaded_segments.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Definition RS_P : list (Z * nat) :=
  [ (0x22638, 296%nat);     (* [comment removed for export] *)
    (0x50d10, 51%nat);      (* [comment removed for export] *)
    (0x5ede4, 3%nat);       (* [comment removed for export] *)
    (0x50b58, 3%nat);       (* [comment removed for export] *)
    (0x508a4, 1%nat);       (* [comment removed for export] *)
    (0x50e9c, 57%nat);      (* [comment removed for export] *)
    (0x50fe0, 16%nat);      (* [comment removed for export] *)
    (0x537bc, 498%nat);     (* [comment removed for export] *)
    (0x542e8, 1146%nat);    (* [comment removed for export] *)
    (0x58d48, 7%nat);       (* [comment removed for export] *)
    (0x541e8, 40%nat);      (* [comment removed for export] *)
    (0x5e2f0, 257%nat);     (* [comment removed for export] *)
    (0x5ee58, 10%nat);      (* [comment removed for export] *)
    (0x54020, 1%nat);       (* [comment removed for export] *)
    (0x5e870, 62%nat);      (* [comment removed for export] *)
    (0x5f950, 37%nat) ].    (* [comment removed for export] *)

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
  [ (0x63c60, 43%nat);      (* [comment removed for export] *)
    (0x63bf0, 4%nat);       (* [comment removed for export] *)
    (0x64e20, 60%nat);      (* [comment removed for export] *)
    (0x75b28, 1%nat);       (* [comment removed for export] *)
    (0x95e40, 1%nat);       (* [comment removed for export] *)
    (0x75060, 3%nat);       (* [comment removed for export] *)
    (0x95c18, 37%nat);      (* [comment removed for export] *)
    (0x962a0, 130%nat);     (* [comment removed for export] *)
    (0x10481, 4%nat); (0x10bd5, 5%nat); (0x10f35, 8%nat); (0x11bc5, 6%nat); (0x12875, 2%nat); (0x125c5, 9%nat);
    (0x12bcd, 6%nat); (0x12f25, 2%nat); (0x13018, 2%nat); (0x18330, 66%nat) ].

Definition IMG_P : tree Z := Eval vm_compute in mk_imgs_acc PSEGS IMGR_P TEmpty.
Lemma IMG_P_ok : img_ok PSEGS IMG_P.
Proof.
  change (img_ok PSEGS (mk_imgs_acc PSEGS IMGR_P TEmpty)). apply mk_imgs_acc_ok.
  - repeat constructor; cbn; lia.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
