(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Uaccess.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK0s YK15 YN06 YN02 YK0q YQ0k.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YQ0j YQ0c YQ0b YQ0i YQ09 YQ04 YQ05 YQ06.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YO04 YL05 YL01.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma file_read_length : forall data (off count : word),
Z.of_nat (length (file_read data off count)) = Z.min (bv_unsigned count) (Z.max 0 (Z.of_nat (length data) - bv_unsigned off)).
Proof.
intros data off count. rewrite file_read_unguarded. rewrite length_firstn, length_skipn.
unfold word_to_nat. pose proof (u64_range count). pose proof (u64_range off). lia.
Qed.

Lemma file_read_eof : forall data (off count : word),
Z.of_nat (length data) <= bv_unsigned off -> file_read data off count = [].
Proof.
intros data off count H. rewrite file_read_unguarded. rewrite skipn_all2 by (unfold word_to_nat; lia).
apply firstn_nil.
Qed.
Section e.
Variable segs : list Segment.

End e.
Lemma read_mem_wbytes : forall mem (a : word) bs,
match bs with [] => mem | _ :: _ => write_to_mem mem a bs end = wbytes mem a bs.
Proof. intros mem a [|b bs]; [reflexivity| apply write_to_mem_wbytes]. Qed.
Lemma wbytes_inside' : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; cbn [length] in *; [lia|].
cbn [wbytes].
destruct rest as [|b' rest'].
- cbn [wbytes length] in *.
replace (bv_eqb x a) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; lia).
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with 0%nat by lia. reflexivity.
- cbn [length] in *.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1).
{ rewrite bv_add_unsigned. change (bv_unsigned (1:word)) with 1. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply Z.mod_small. pose proof (u64_range a). lia. }
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
+ rewrite wbytes_below by (cbn [length]; rewrite ?Hu1; lia).
replace (bv_eqb x a) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; lia).
rewrite Heq, Z.sub_diag. reflexivity.
+ rewrite IH by (cbn [length]; rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.
Section f.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.

End f.
Section g.
Variable segs : list Segment.
Definition abs_dest_check (rs : smem) (a n : Z) : bool :=
existsb (fun r => obase_eqb (r_base r) None && (r_wlo r <=? a) && (a + n <=? r_whi r) &&
forallb (fun c => (c_off c + c_len c <=? a) || (a + n <=? c_off c)) (r_chunks r)) rs.


Lemma read_dest_ok_w : forall mem (buf : word) (bs : list byte),
(forall i, 0 <= i < Z.of_nat (length bs) -> wview segs mem (Z_to_bv 64 (bv_unsigned buf + i)) <> None) ->
exists w, read_bytes_map (wview segs mem) buf (len_word bs) = Some w.
Proof.
intros mem buf bs Hdef. rewrite read_bytes_map_eq.
apply read_bytes_aux_defined. intros i Hi.
assert (Hlen : Z.of_nat (word_to_nat (len_word bs)) <= Z.of_nat (length bs)).
{ unfold word_to_nat, len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (Z.mod_le (Z.of_nat (length bs)) (2 ^ 64) ltac:(lia) ltac:(lia)).
rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). lia. }
apply Hdef. lia.
Qed.

End g.
End d.
