From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib Require Import Tac.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require Import RStep.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.H Require Import GldProof.
Import ListNotations.

(* The UBSan build, at its link-time addresses. *)
Definition U_img : RImg := {| img_segs := Ubsan.M.loaded_segments; sym := fun k => k |}.

Lemma U_code : @CodeAtT (@img_segs U_img) (@sym U_img 0x12a7c) gld_prog.
Proof. apply code_checkb_t_ok. vm_compute. reflexivity. Qed.

Lemma U_rel : RelCode (@sym U_img 0x12a7c) 264.
Proof. unfold RelCode, rel_code. cbn. lia. Qed.

(* asn1_get_length_der in the published UBSan binary: from its entry, with a
   readable input buffer and a writable, aligned, non-null *len, execution
   returns to the caller without reaching the UBSan trap, touching only *len. *)
Theorem asn1_get_length_der_ubsan : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (der : list byte) (bs : list byte),
  bytes_at Ubsan.M.loaded_segments m (bv_unsigned a0) der ->
  bv_unsigned a0 <> 0%Z ->
  a1 = Z_to_bv 64 (Z.of_nat (length der)) -> (length der <= 512)%nat ->
  rw_cells Ubsan.M.loaded_segments m (bv_unsigned a2) [CB 4 bs] ->
  bv_unsigned a2 <> 0%Z -> (bv_unsigned a2 mod 4 = 0)%Z ->
  (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length der) <= bv_unsigned a2)%Z ->
  evt Ubsan.M.loaded_segments
    (@gld_post U_img ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 der m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12a7c) fc None m (seg_rom Ubsan.M.loaded_segments)).
Proof. exact (@gld_spec U_img U_code). Qed.

Print Assumptions asn1_get_length_der_ubsan.

From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Plain.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.H Require Import GldPlainProof.

Definition P_img : RImg := {| img_segs := Plain.M.loaded_segments; sym := fun k => k |}.

Lemma P_code : @CodeAtT (@img_segs P_img) (@sym P_img 0x12a7c) gldp_prog.
Proof. apply code_checkb_t_ok. vm_compute. reflexivity. Qed.

(* The same function in the published plain binary. *)
Theorem asn1_get_length_der_plain : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (der : list byte) (bs : list byte),
  bytes_at Plain.M.loaded_segments m (bv_unsigned a0) der ->
  a1 = Z_to_bv 64 (Z.of_nat (length der)) -> (length der <= 512)%nat ->
  rw_cells Plain.M.loaded_segments m (bv_unsigned a2) [CB 4 bs] ->
  (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length der) <= bv_unsigned a2)%Z ->
  evt Plain.M.loaded_segments
    (@gld_post P_img ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 der m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12a7c) fc None m (seg_rom Plain.M.loaded_segments)).
Proof. exact (@gldp_spec P_img P_code). Qed.

Print Assumptions asn1_get_length_der_plain.

From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.H Require Import GldHarness.

Lemma U_hcode : @CodeAtT (@img_segs U_img) (@sym U_img 0x12a54) hrn_prog.
Proof. apply code_checkb_t_ok. vm_compute. reflexivity. Qed.
Lemma P_hcode : @CodeAtT (@img_segs P_img) (@sym P_img 0x12a54) hrn_prog.
Proof. apply code_checkb_t_ok. vm_compute. reflexivity. Qed.

Lemma U_hrel : RelCode (@sym U_img 0x12a54) 40.
Proof. unfold RelCode, rel_code. cbn. lia. Qed.
Lemma P_hrel : RelCode (@sym P_img 0x12a54) 40.
Proof. unfold RelCode, rel_code. cbn. lia. Qed.

Lemma U_gld : @gld_contract U_img.
Proof. unfold gld_contract. intros. eapply asn1_get_length_der_ubsan; eassumption. Qed.
Lemma P_gld : @gld_contract P_img.
Proof. unfold gld_contract. intros. eapply asn1_get_length_der_plain; eassumption. Qed.

(* LLVMFuzzerTestOneInput in each build: given its own 16 bytes of stack and an
   input buffer of any length, it returns 0 with sp restored, having changed
   nothing outside its frame.  In the UBSan build this includes that no check fires. *)
Theorem harness_ubsan : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (der : list byte) (lo : Z),
  stk Ubsan.M.loaded_segments m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bytes_at Ubsan.M.loaded_segments m (bv_unsigned a0) der -> bv_unsigned a0 <> 0%Z ->
  a1 = Z_to_bv 64 (Z.of_nat (length der)) ->
  (bv_unsigned a0 + Z.of_nat (length der) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt Ubsan.M.loaded_segments (@hrn_post U_img ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 der lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12a54) fc None m (seg_rom Ubsan.M.loaded_segments)).
Proof. exact (@hrn_spec U_img U_hcode U_hrel U_gld). Qed.

Theorem harness_plain : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (der : list byte) (lo : Z),
  stk Plain.M.loaded_segments m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bytes_at Plain.M.loaded_segments m (bv_unsigned a0) der -> bv_unsigned a0 <> 0%Z ->
  a1 = Z_to_bv 64 (Z.of_nat (length der)) ->
  (bv_unsigned a0 + Z.of_nat (length der) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt Plain.M.loaded_segments (@hrn_post P_img ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 der lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12a54) fc None m (seg_rom Plain.M.loaded_segments)).
Proof. exact (@hrn_spec P_img P_hcode P_hrel P_gld). Qed.

Print Assumptions harness_ubsan.
Print Assumptions harness_plain.
