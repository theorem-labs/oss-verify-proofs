(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module SfKitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma unsigned_b8 : forall a, 0 <= a < 256 -> bv_unsigned (Z_to_bv 8 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma magic_wordA : forall m0 m1 m2 m3, 0 <= m0 < 256 -> 0 <= m1 < 256 -> 0 <= m2 < 256 -> 0 <= m3 < 256 ->
  Z.lor (Z.lor (Z.shiftl (bv_unsigned (sxb (Z_to_bv 8 m3))) 24 mod 18446744073709551616)
               (Z.shiftl (bv_unsigned (Z_to_bv 8 m2)) 16 mod 18446744073709551616))
        (Z.lor (Z.shiftl (bv_unsigned (Z_to_bv 8 m1)) 8 mod 18446744073709551616) (bv_unsigned (Z_to_bv 8 m0)))
  = magic_sx m0 m1 m2 m3.
Proof.
  intros m0 m1 m2 m3 H0 H1 H2 H3. unfold magic_sx.
  rewrite sxb_lit by lia. rewrite !unsigned_b8 by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (m1 * 2^8)) by lia. rewrite (Z.mod_small (m2 * 2^16)) by lia.
  rewrite (lor_high_low m1 m0 8) by lia.
  assert (D : m3 / 128 = 0 \/ m3 / 128 = 1) by (Z.div_mod_to_equations; lia).
  destruct D as [D|D]; rewrite D.
  - replace (m3 - 256 * 0) with m3 by lia. rewrite (unsigned_lit m3) by lia. rewrite (Z.mod_small (m3 * 2^24)) by lia.
    rewrite (lor_high_low m3 (m2 * 2^16) 24) by lia.
    replace (m3 * 2 ^ 24 + m2 * 2 ^ 16) with ((m3 * 2^8 + m2) * 2^16) by lia.
    rewrite (lor_high_low (m3 * 2^8 + m2) (m1 * 2^8 + m0) 16) by lia. lia.
  - rewrite (Z_to_bv_unsigned 64 (m3 - 256 * 1)). unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
    replace ((m3 - 256 * 1) mod 2^64) with (2^64 - 256 + m3) by (Z.div_mod_to_equations; lia).
    replace (((2 ^ 64 - 256 + m3) * 2 ^ 24) mod 18446744073709551616) with ((2^40 - 256 + m3) * 2^24) by (Z.div_mod_to_equations; lia).
    rewrite (lor_high_low (2^40 - 256 + m3) (m2 * 2^16) 24) by lia.
    replace ((2 ^ 40 - 256 + m3) * 2 ^ 24 + m2 * 2 ^ 16) with (((2 ^ 40 - 256 + m3) * 2^8 + m2) * 2^16) by lia.
    rewrite (lor_high_low ((2 ^ 40 - 256 + m3) * 2^8 + m2) (m1 * 2^8 + m0) 16) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swap16_valA : forall (w : word) a b, 0 <= a < 256 -> 0 <= b < 256 -> bv_unsigned w = a + 256 * b ->
  bv_unsigned (Z_to_bv 64 (Z.lor (Z.shiftl (bv_unsigned w) 8 mod 18446744073709551616) (Z.shiftr (bv_unsigned w) 8)))
  = b + 256 * a + 65536 * b.
Proof.
  intros w a b Ha Hb E. rewrite E. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace ((a + 256 * b) / 2^8) with b by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small ((a + 256 * b) * 2^8)) by lia.
  rewrite lor_high_low by lia. rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swap32_valA : forall (w : word) a b c d hi, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> 0 <= hi < 2^32 ->
  bv_unsigned w = a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi ->
  bv_unsigned (Z_to_bv 64
    (Z.lor (Z.lor (Z.shiftl (bv_unsigned w) 24 mod 18446744073709551616)
                  (Z.shiftl (Z.land (bv_unsigned w) 65280) 8 mod 18446744073709551616))
           (Z.lor (Z.land (Z.shiftr (bv_unsigned w) 8) 65280)
                  (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24) mod 18446744073709551616))))
  = d + 256 * c + 65536 * b + 16777216 * a + 4294967296 * (b + 256 * c + 65536 * d + 16777216 * (hi mod 256)).
Proof.
  intros w a b c d hi Ha Hb Hc Hd Hhi E. rewrite E. clear E w.
  set (U := a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi).
  assert (HU : 0 <= U < 2^64) by (subst U; lia).
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  rewrite (land_ff00 U) by lia. replace (U / 256 mod 256) with b by (subst U; Z.div_mod_to_equations; lia).
  rewrite (land_ff00 (U / 2^8)) by (Z.div_mod_to_equations; lia).
  replace (U / 2^8 / 256 mod 256) with c by (subst U; Z.div_mod_to_equations; lia).
  rewrite bv_wrap32_eq. replace (U mod 2^32 / 2^24) with d by (subst U; Z.div_mod_to_equations; lia).
  rewrite bv_swrap32_small by lia. rewrite (Z.mod_small d) by lia.
  replace (c * 256) with (c * 2^8) by lia. rewrite (lor_high_low c d 8) by lia.
  replace ((U * 2^24) mod 18446744073709551616) with ((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2^24)
    by (subst U; Z.div_mod_to_equations; lia).
  replace (b * 256 * 2^8) with (65536 * b) by lia. rewrite (Z.mod_small (65536 * b)) by lia.
  rewrite (lor_high_low _ (65536 * b) 24) by (Z.div_mod_to_equations; lia).
  replace ((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2 ^ 24 + 65536 * b)
    with (((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2^8 + b) * 2^16) by lia.
  rewrite lor_high_low by (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_wordA : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z.land (sxv l0 l1 l2 l3 mod 18446744073709551616) 67043328 = (l2 + 256 * (l3 mod 4)) * 65536.
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3. rewrite <- (reserved_word l0 l1 l2 l3) by lia.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma unsigned_b8 : forall a, 0 <= a < 256 -> bv_unsigned (Z_to_bv 8 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma magic_wordA : forall m0 m1 m2 m3, 0 <= m0 < 256 -> 0 <= m1 < 256 -> 0 <= m2 < 256 -> 0 <= m3 < 256 ->
  Z.lor (Z.lor (Z.shiftl (bv_unsigned (sxb (Z_to_bv 8 m3))) 24 mod 18446744073709551616)
               (Z.shiftl (bv_unsigned (Z_to_bv 8 m2)) 16 mod 18446744073709551616))
        (Z.lor (Z.shiftl (bv_unsigned (Z_to_bv 8 m1)) 8 mod 18446744073709551616) (bv_unsigned (Z_to_bv 8 m0)))
  = magic_sx m0 m1 m2 m3.
Proof.
  intros m0 m1 m2 m3 H0 H1 H2 H3. unfold magic_sx.
  rewrite sxb_lit by lia. rewrite !unsigned_b8 by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (m1 * 2^8)) by lia. rewrite (Z.mod_small (m2 * 2^16)) by lia.
  rewrite (lor_high_low m1 m0 8) by lia.
  assert (D : m3 / 128 = 0 \/ m3 / 128 = 1) by (Z.div_mod_to_equations; lia).
  destruct D as [D|D]; rewrite D.
  - replace (m3 - 256 * 0) with m3 by lia. rewrite (unsigned_lit m3) by lia. rewrite (Z.mod_small (m3 * 2^24)) by lia.
    rewrite (lor_high_low m3 (m2 * 2^16) 24) by lia.
    replace (m3 * 2 ^ 24 + m2 * 2 ^ 16) with ((m3 * 2^8 + m2) * 2^16) by lia.
    rewrite (lor_high_low (m3 * 2^8 + m2) (m1 * 2^8 + m0) 16) by lia. lia.
  - rewrite (Z_to_bv_unsigned 64 (m3 - 256 * 1)). unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
    replace ((m3 - 256 * 1) mod 2^64) with (2^64 - 256 + m3) by (Z.div_mod_to_equations; lia).
    replace (((2 ^ 64 - 256 + m3) * 2 ^ 24) mod 18446744073709551616) with ((2^40 - 256 + m3) * 2^24) by (Z.div_mod_to_equations; lia).
    rewrite (lor_high_low (2^40 - 256 + m3) (m2 * 2^16) 24) by lia.
    replace ((2 ^ 40 - 256 + m3) * 2 ^ 24 + m2 * 2 ^ 16) with (((2 ^ 40 - 256 + m3) * 2^8 + m2) * 2^16) by lia.
    rewrite (lor_high_low ((2 ^ 40 - 256 + m3) * 2^8 + m2) (m1 * 2^8 + m0) 16) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swap16_valA : forall (w : word) a b, 0 <= a < 256 -> 0 <= b < 256 -> bv_unsigned w = a + 256 * b ->
  bv_unsigned (Z_to_bv 64 (Z.lor (Z.shiftl (bv_unsigned w) 8 mod 18446744073709551616) (Z.shiftr (bv_unsigned w) 8)))
  = b + 256 * a + 65536 * b.
Proof.
  intros w a b Ha Hb E. rewrite E. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace ((a + 256 * b) / 2^8) with b by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small ((a + 256 * b) * 2^8)) by lia.
  rewrite lor_high_low by lia. rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swap32_valA : forall (w : word) a b c d hi, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> 0 <= hi < 2^32 ->
  bv_unsigned w = a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi ->
  bv_unsigned (Z_to_bv 64
    (Z.lor (Z.lor (Z.shiftl (bv_unsigned w) 24 mod 18446744073709551616)
                  (Z.shiftl (Z.land (bv_unsigned w) 65280) 8 mod 18446744073709551616))
           (Z.lor (Z.land (Z.shiftr (bv_unsigned w) 8) 65280)
                  (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24) mod 18446744073709551616))))
  = d + 256 * c + 65536 * b + 16777216 * a + 4294967296 * (b + 256 * c + 65536 * d + 16777216 * (hi mod 256)).
Proof.
  intros w a b c d hi Ha Hb Hc Hd Hhi E. rewrite E. clear E w.
  set (U := a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi).
  assert (HU : 0 <= U < 2^64) by (subst U; lia).
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  rewrite (land_ff00 U) by lia. replace (U / 256 mod 256) with b by (subst U; Z.div_mod_to_equations; lia).
  rewrite (land_ff00 (U / 2^8)) by (Z.div_mod_to_equations; lia).
  replace (U / 2^8 / 256 mod 256) with c by (subst U; Z.div_mod_to_equations; lia).
  rewrite bv_wrap32_eq. replace (U mod 2^32 / 2^24) with d by (subst U; Z.div_mod_to_equations; lia).
  rewrite bv_swrap32_small by lia. rewrite (Z.mod_small d) by lia.
  replace (c * 256) with (c * 2^8) by lia. rewrite (lor_high_low c d 8) by lia.
  replace ((U * 2^24) mod 18446744073709551616) with ((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2^24)
    by (subst U; Z.div_mod_to_equations; lia).
  replace (b * 256 * 2^8) with (65536 * b) by lia. rewrite (Z.mod_small (65536 * b)) by lia.
  rewrite (lor_high_low _ (65536 * b) 24) by (Z.div_mod_to_equations; lia).
  replace ((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2 ^ 24 + 65536 * b)
    with (((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2^8 + b) * 2^16) by lia.
  rewrite lor_high_low by (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_wordA : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z.land (sxv l0 l1 l2 l3 mod 18446744073709551616) 67043328 = (l2 + 256 * (l3 mod 4)) * 65536.
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3. rewrite <- (reserved_word l0 l1 l2 l3) by lia.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.
End TwB.
End SfKitA.

(* [comment removed for export] *)
Module SfKitB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lt16_wordA : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  (sxv l0 l1 l2 l3 mod 18446744073709551616) mod 65536 = l0 + 256 * l1.
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3. unfold sxv, le4val.
  assert (D : l3 / 128 = 0 \/ l3 / 128 = 1) by (Z.div_mod_to_equations; lia).
  destruct D as [D|D]; rewrite D; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma ltext_wordA : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  l2 = 0 -> l3 mod 4 = 0 ->
  Z_to_bv 64 (Z.land (sxv l0 l1 l2 l3 mod 18446744073709551616) 18446744073642442752) = Z_to_bv 64 (s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)).
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3 Z2 Z3. rewrite <- (ltext_word l0 l1 l2 l3) by assumption.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le4_intmax : le4 (Z_to_bv 64 (-2147483649)) = le4 (Z_to_bv 64 2147483647).
Proof.
  rewrite (le4_of_val (Z_to_bv 64 (-2147483649)) 255 255 255 127 4294967295), (le4_of_val (Z_to_bv 64 2147483647) 255 255 255 127 0);
    try lia; [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lt16_wordA : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  (sxv l0 l1 l2 l3 mod 18446744073709551616) mod 65536 = l0 + 256 * l1.
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3. unfold sxv, le4val.
  assert (D : l3 / 128 = 0 \/ l3 / 128 = 1) by (Z.div_mod_to_equations; lia).
  destruct D as [D|D]; rewrite D; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma ltext_wordA : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  l2 = 0 -> l3 mod 4 = 0 ->
  Z_to_bv 64 (Z.land (sxv l0 l1 l2 l3 mod 18446744073709551616) 18446744073642442752) = Z_to_bv 64 (s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)).
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3 Z2 Z3. rewrite <- (ltext_word l0 l1 l2 l3) by assumption.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le4_intmax : le4 (Z_to_bv 64 (-2147483649)) = le4 (Z_to_bv 64 2147483647).
Proof.
  rewrite (le4_of_val (Z_to_bv 64 (-2147483649)) 255 255 255 127 4294967295), (le4_of_val (Z_to_bv 64 2147483647) 255 255 255 127 0);
    try lia; [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.
End TwB.
End SfKitB.
