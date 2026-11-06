(* The arithmetic of the op byte for the HEAD segment of the image-A walk of LLVMFuzzerTestOneInput shares (0x80abc-0x80c30,
   lib/A/Prog/codec_amain_inv.v seg_head): the cuts inside the segment, the arithmetic of the op byte
   (op mod 15 and op / 15 mod 3 as the multiply-shift forms of 0x80b60-0x80b9c compute them), the two calls of
   the runtime's checked memset (0x80b5c and 0x80c08) and the call of diginet_personality_of (0x80bc4) as steps
   from one cut to the next, and the small memory facts the record needs. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkImg CPgWalkIntr CPgWalkKept CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_encl codec_amain_head_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the arithmetic of the op byte ================================
   0x80b60-0x80b9c computes, from the byte op in s7: q = (op * 137) >> 11 = op / 15, the kind
   op + q - 16 q = op - 15 q = op mod 15 (stored as a byte), and, from t = (q * 86) >> 8 = q / 3,
   the index q - t - 2 t = q mod 3. *)
Definition hd_q : sv := SAlu ALU_SRL (SMd M_MUL (SAlu ALU_AND (SOff 23 0) (SLit 255)) (SLit 137)) (SLit 11).
Definition hd_t : sv := SAlu ALU_SRL (SMd M_MUL hd_q (SLit 86)) (SLit 8).
Definition hd_kind_e : sv :=
SAlu ALU_AND (SAluw ALU_SUB (SAlu ALU_ADD (SOff 23 0) hd_q) (SAlu ALU_SLL hd_q (SLit 4))) (SLit 255).
Definition hd_i_e : sv :=
SAlu ALU_AND (SAlu ALU_SUB (SAlu ALU_SUB hd_q hd_t) (SAlu ALU_SLL hd_t (SLit 1))) (SLit 255).
Definition hd_kindZ (x : Z) : Z := zev (fun _ => x) hd_kind_e.
Definition hd_iZ (x : Z) : Z := zev (fun _ => x) hd_i_e.

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

Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma hd_kind_val : forall E, 0 <= bv_unsigned (ew E 23) < 256 ->
U E hd_kind_e = bv_unsigned (ew E 23) mod 15.
Proof.
intros E Hx. rewrite (U_zev E hd_kind_e ltac:(vm_compute; reflexivity)).
change (zev (rho_of E) hd_kind_e) with (hd_kindZ (rho_of E 23)).
apply hd_kindZ_ok. unfold rho_of. exact Hx.
Qed.
Lemma hd_i_val : forall E, 0 <= bv_unsigned (ew E 23) < 256 ->
U E hd_i_e = bv_unsigned (ew E 23) / 15 mod 3.
Proof.
intros E Hx. rewrite (U_zev E hd_i_e ltac:(vm_compute; reflexivity)).
change (zev (rho_of E) hd_i_e) with (hd_iZ (rho_of E 23)).
apply hd_iZ_ok. unfold rho_of. exact Hx.
Qed.
End u.

