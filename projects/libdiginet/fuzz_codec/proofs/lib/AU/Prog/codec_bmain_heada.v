(* The arithmetic of the op byte for the HEAD segment of the image-B walk of LLVMFuzzerTestOneInput
   (0x80c30-0x80dc8, lib/AU/Prog/codec_bmain_inv.v seg_head): op mod 15, op / 15 mod 3 and 4 (op / 15 mod 3)
   as the multiply-shift forms of 0x80cdc-0x80d20 compute them from the op byte in s6. It is the image-A
   arithmetic (lib/A/Prog/codec_amain_heada.v) with the byte in s6 (A: s7) and the shifted index of image B's
   UBSan check of DESK + 4 i (0x80d20 slli a1,s8,2). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the arithmetic of the op byte ================================
   0x80cdc-0x80d1c computes, from the byte op in s6: q = (op * 137) >> 11 = op / 15, the kind
   op + q - 16 q = op - 15 q = op mod 15 (stored as a byte), and, from t = (q * 86) >> 8 = q / 3,
   the index q - t - 2 t = q mod 3; 0x80d20 shifts the index left by 2. *)
Definition hd_q : sv := SAlu ALU_SRL (SMd M_MUL (SAlu ALU_AND (SOff 22 0) (SLit 255)) (SLit 137)) (SLit 11).
Definition hd_t : sv := SAlu ALU_SRL (SMd M_MUL hd_q (SLit 86)) (SLit 8).
Definition hd_kind_e : sv :=
SAlu ALU_AND (SAluw ALU_SUB (SAlu ALU_ADD (SOff 22 0) hd_q) (SAlu ALU_SLL hd_q (SLit 4))) (SLit 255).
Definition hd_i_e : sv :=
SAlu ALU_AND (SAlu ALU_SUB (SAlu ALU_SUB hd_q hd_t) (SAlu ALU_SLL hd_t (SLit 1))) (SLit 255).
Definition hd_a1_e : sv := SAlu ALU_SLL hd_i_e (SLit 2).
Definition hd_kindZ (x : Z) : Z := zev (fun _ => x) hd_kind_e.
Definition hd_iZ (x : Z) : Z := zev (fun _ => x) hd_i_e.
Definition hd_a1Z (x : Z) : Z := zev (fun _ => x) hd_a1_e.

Lemma hd_kindZ_ok : forall x, 0 <= x < 256 -> hd_kindZ x = x mod 15.
Proof.
intros x Hx.
assert (CHK : forallb (fun n => Z.eqb (hd_kindZ (Z.of_nat n)) (Z.of_nat n mod 15)) (seq 0 256) = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) CHK (Z.to_nat x) ltac:(apply in_seq; lia)) as H.
cbv beta in H. rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.
Lemma hd_iZ_ok : forall x, 0 <= x < 256 -> hd_iZ x = x / 15 mod 3.
Proof.
intros x Hx.
assert (CHK : forallb (fun n => Z.eqb (hd_iZ (Z.of_nat n)) (Z.of_nat n / 15 mod 3)) (seq 0 256) = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) CHK (Z.to_nat x) ltac:(apply in_seq; lia)) as H.
cbv beta in H. rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.
Lemma hd_a1Z_ok : forall x, 0 <= x < 256 -> hd_a1Z x = 4 * (x / 15 mod 3).
Proof.
intros x Hx.
assert (CHK : forallb (fun n => Z.eqb (hd_a1Z (Z.of_nat n)) (4 * (Z.of_nat n / 15 mod 3))) (seq 0 256) = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) CHK (Z.to_nat x) ltac:(apply in_seq; lia)) as H.
cbv beta in H. rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.

Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma hd_kind_val : forall E, 0 <= bv_unsigned (ew E 22) < 256 ->
U E hd_kind_e = bv_unsigned (ew E 22) mod 15.
Proof.
intros E Hx. rewrite (U_zev E hd_kind_e ltac:(vm_compute; reflexivity)).
change (zev (rho_of E) hd_kind_e) with (hd_kindZ (rho_of E 22)).
apply hd_kindZ_ok. unfold rho_of. exact Hx.
Qed.
Lemma hd_i_val : forall E, 0 <= bv_unsigned (ew E 22) < 256 ->
U E hd_i_e = bv_unsigned (ew E 22) / 15 mod 3.
Proof.
intros E Hx. rewrite (U_zev E hd_i_e ltac:(vm_compute; reflexivity)).
change (zev (rho_of E) hd_i_e) with (hd_iZ (rho_of E 22)).
apply hd_iZ_ok. unfold rho_of. exact Hx.
Qed.
Lemma hd_a1_val : forall E, 0 <= bv_unsigned (ew E 22) < 256 ->
U E hd_a1_e = 4 * (bv_unsigned (ew E 22) / 15 mod 3).
Proof.
intros E Hx. rewrite (U_zev E hd_a1_e ltac:(vm_compute; reflexivity)).
change (zev (rho_of E) hd_a1_e) with (hd_a1Z (rho_of E 22)).
apply hd_a1Z_ok. unfold rho_of. exact Hx.
Qed.
End u.
