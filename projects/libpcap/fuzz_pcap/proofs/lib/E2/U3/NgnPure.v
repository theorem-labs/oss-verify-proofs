(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition q8 (data : list Z) (off : Z) (i : Z) : Z := get_u8 data (off + i).

Lemma zslice4_q8 : forall data off, (0 <= off)%Z -> (off + 4 <= Z.of_nat (length data))%Z ->
  zslice off 4 data = [q8 data off 0; q8 data off 1; q8 data off 2; q8 data off 3].
Proof using Type. pin_using tt.
  intros data off H0 H1. destruct (zslice_4 off data H0 H1) as (x0 & x1 & x2 & x3 & E).
  destruct (get_u8_of_slice4 off data x0 x1 x2 x3 H0 H1 E) as (E0 & E1 & E2 & E3).
  unfold q8. rewrite Z.add_0_r, E0, E1, E2, E3. exact E.
Qed.

Lemma get_le32_q8 : forall data off, (0 <= off)%Z -> (off + 4 <= Z.of_nat (length data))%Z ->
  get_le32 data off = le4val (q8 data off 0) (q8 data off 1) (q8 data off 2) (q8 data off 3).
Proof using Type. pin_using tt. intros data off H0 H1. unfold le4val. rewrite (get_le32_of_slice off data _ _ _ _ (zslice4_q8 data off H0 H1)). lia. Qed.

Lemma q8_range : forall data off i, Forall (fun x => 0 <= x < 256)%Z data -> (0 <= off + i < Z.of_nat (length data))%Z -> (0 <= q8 data off i < 256)%Z.
Proof using Type. pin_using tt.
  intros data off i HF Hi. unfold q8, get_u8.
  apply (proj1 (List.Forall_forall _ _) HF). apply znth_range. unfold zlength. lia.
Qed.

(* [comment removed for export] *)
Lemma firstn4_q8 : forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 4 <= Z.of_nat (length data))%Z ->
  firstn 4 (skipn k bs) = [b8 (q8 data off 0); b8 (q8 data off 1); b8 (q8 data off 2); b8 (q8 data off 3)].
Proof using Type. pin_using tt.
  intros data bs k off PFX Hk H1. subst off.
  transitivity (map b8 (zslice (Z.of_nat k) 4 data)); [| rewrite zslice4_q8 by lia; reflexivity].
  unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sxv_mod32 : forall a b c d, (0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> (sxv a b c d) mod 2^32 = le4val a b c d)%Z.
Proof using Type. pin_using tt. intros. unfold sxv, le4val. Z.div_mod_to_equations. lia. Qed.
End WithCeil.


Local Close Scope bv_scope.
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma swap32s_word : forall (w : word) a b c d hi, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> 0 <= hi < 2^32 ->
  bv_unsigned w = a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi ->
  Z_to_bv 64
    (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned w) 24))))
                                            (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned w) 65280))) 8))))))
           (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 8))) 65280)))
                                            (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24))))))))
  = Z_to_bv 64 (sxu (le4val d c b a)).
Proof using Type. pin_using tt.
  intros w a b c d hi Ha Hb Hc Hd Hhi E. rewrite E. clear E w.
  set (U := a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi).
  assert (HU : 0 <= U < 2^64) by (subst U; lia).
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  (* [comment removed for export] *)
  rewrite (land_ff00 U) by lia. replace (U / 256 mod 256) with b by (subst U; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (b * 256)) by lia.
  rewrite (unsigned_lit (U / 2^8)) by (Z.div_mod_to_equations; lia).
  rewrite (land_ff00 (U / 2^8)) by (Z.div_mod_to_equations; lia).
  replace (U / 2^8 / 256 mod 256) with c by (subst U; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (c * 256)) by lia.
  (* [comment removed for export] *)
  rewrite bv_wrap32_eq. replace (U mod 2^32 / 2^24) with d by (subst U; Z.div_mod_to_equations; lia).
  rewrite (bv_swrap32_small d) by lia. rewrite (unsigned_lit d) by lia.
  replace (c * 256) with (c * 2^8) by lia. rewrite (lor_high_low c d 8) by lia. rewrite (unsigned_lit (c * 2^8 + d)) by lia.
  (* [comment removed for export] *)
  rewrite bv_swrap32_eq.
  replace ((U * 2 ^ 24 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) with (a * 2^24 - (a / 128) * 2^32) by (subst U; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit_wrap (a * 2^24 - a / 128 * 2^32)).
  replace ((a * 2 ^ 24 - a / 128 * 2 ^ 32) mod 2 ^ 64) with ((a + (a / 128) * (2^40 - 2^8)) * 2^24) by (Z.div_mod_to_equations; lia).
  replace (b * 256 * 2^8) with (65536 * b) by lia. rewrite (unsigned_lit (65536 * b)) by lia.
  rewrite (lor_high_low _ (65536 * b) 24) by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit ((a + a / 128 * (2 ^ 40 - 2 ^ 8)) * 2 ^ 24 + 65536 * b)) by (Z.div_mod_to_equations; lia).
  replace ((a + a / 128 * (2 ^ 40 - 2 ^ 8)) * 2 ^ 24 + 65536 * b) with (((a + a / 128 * (2 ^ 40 - 2 ^ 8)) * 2^8 + b) * 2^16) by lia.
  rewrite lor_high_low by (Z.div_mod_to_equations; lia).
  f_equal. unfold sxu, le4val. destruct (Z.ltb_spec (d + 256 * c + 65536 * b + 16777216 * a) (2^31)); Z.div_mod_to_equations; lia.
Qed.

Lemma sxv_sxu : forall a b c d, (0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> sxv a b c d = sxu (le4val a b c d))%Z.
Proof using Type. pin_using tt. intros. unfold sxv, sxu, le4val. destruct (Z.ltb_spec (a + 256 * b + 65536 * c + 16777216 * d) (2^31)); Z.div_mod_to_equations; lia. Qed.

Lemma le4_word_mod32 : forall (w : word) v, (bv_unsigned w mod 2^32 = v)%Z -> le4 w = le4 (Z_to_bv 64 v).
Proof using Type. pin_using tt.
  intros w v Hv. rewrite <- (Z_to_bv_bv_unsigned w) at 1. pose proof (bv_unsigned_in_range 64 w). change (bv_modulus 64) with (2^64) in *.
  rewrite (le4_mod32 (bv_unsigned w)) by lia. rewrite Hv. reflexivity.
Qed.

Lemma sxu_mod32 : forall v, (0 <= v < 2^32)%Z -> (sxu v mod 2^32 = v)%Z.
Proof using Type. pin_using tt. intros v Hv. unfold sxu. destruct (Z.ltb_spec v (2^31)); Z.div_mod_to_equations; lia. Qed.
Lemma sxu_range' : forall v, (0 <= v < 2^32)%Z -> (0 <= sxu v < 2^64)%Z.
Proof using Type. pin_using tt. intros v Hv. unfold sxu. destruct (Z.ltb_spec v (2^31)); lia. Qed.

(* [comment removed for export] *)
Lemma ts_swap_word : forall h0 h1 h2 h3 l0 l1 l2 l3,
  0 <= h0 < 256 -> 0 <= h1 < 256 -> 0 <= h2 < 256 -> 0 <= h3 < 256 -> 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z_to_bv 64
   (Z.lor
      (bv_unsigned
         (Z_to_bv 64
            (Z.lor
               (bv_unsigned
                  (Z_to_bv 64
                     (Z.lor
                        (bv_unsigned
                           (Z_to_bv 64
                              (bv_unsigned (Z_to_bv 64 (le4val h0 h1 h2 h3))
                               ≪ 56)))
                        (bv_unsigned
                           (Z_to_bv 64
                              (bv_unsigned
                                 (Z_to_bv 64
                                    (Z.land
                                       (bv_unsigned
                                          (Z_to_bv 64 (le4val h0 h1 h2 h3)))
                                       65280))
                               ≪ 40))))))
               (bv_unsigned
                  (Z_to_bv 64
                     (Z.lor
                        (bv_unsigned
                           (Z_to_bv 64
                              (Z.lor
                                 (bv_unsigned
                                    (Z_to_bv 64
                                       (bv_unsigned
                                          (Z_to_bv 64
                                             (bv_unsigned
                                                (Z_to_bv 64 (sxv l0 l1 l2 l3))
                                              ≪ 56))
                                        ≫ 32)))
                                 (bv_unsigned
                                    (Z_to_bv 64
                                       (Z.land
                                          (bv_unsigned
                                             (Z_to_bv 64
                                                (bv_unsigned
                                                 (Z_to_bv 64
                                                 (sxv l0 l1 l2 l3)) ≪ 8)))
                                          16711680))))))
                        (bv_unsigned
                           (Z_to_bv 64
                              (Z.lor
                                 (bv_unsigned
                                    (Z_to_bv 64
                                       (Z.land
                                          (bv_unsigned
                                             (Z_to_bv 64
                                                (bv_unsigned
                                                 (Z_to_bv 64
                                                 (sxv l0 l1 l2 l3)) ≫ 8)))
                                          65280)))
                                 (bv_unsigned
                                    (Z_to_bv 64
                                       (bv_swrap 32
                                          (bv_wrap 32
                                             (bv_unsigned
                                                (Z_to_bv 64 (sxv l0 l1 l2 l3)))
                                           ≫ 24)))))))))))))
      (bv_unsigned
         (Z_to_bv 64
            (Z.lor
               (bv_unsigned
                  (Z_to_bv 64
                     (bv_unsigned
                        (Z_to_bv 64
                           (Z.land
                              (bv_unsigned
                                 (Z_to_bv 64
                                    (Z.lor
                                       (bv_unsigned
                                          (Z_to_bv 64
                                             (bv_unsigned
                                                (Z_to_bv 64 (sxv l0 l1 l2 l3))
                                              ≪ 32)))
                                       (bv_unsigned
                                          (Z_to_bv 64 (le4val h0 h1 h2 h3))))))
                              16711680))
                      ≪ 24)))
               (bv_unsigned
                  (Z_to_bv 64
                     (bv_unsigned
                        (Z_to_bv 64
                           (bv_swrap 32
                              (bv_wrap 32
                                 (bv_unsigned
                                    (Z_to_bv 64
                                       (Z.lor
                                          (bv_unsigned
                                             (Z_to_bv 64
                                                (bv_unsigned
                                                 (Z_to_bv 64
                                                 (sxv l0 l1 l2 l3)) ≪ 32)))
                                          (bv_unsigned
                                             (Z_to_bv 64 (le4val h0 h1 h2 h3))))))
                               ≫ 24)))
                      ≪ 32)))))))
  = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2 ^ 32 + le4val l3 l2 l1 l0).
Proof using Type. pin_using tt.
  intros h0 h1 h2 h3 l0 l1 l2 l3 R0 R1 R2 R3 S0 S1 S2 S3.
  set (U := le4val h0 h1 h2 h3). set (V := sxv l0 l1 l2 l3).
  assert (HU : U = h0 + 256 * h1 + 65536 * h2 + 16777216 * h3) by reflexivity.
  assert (HV : V = l0 + 256 * l1 + 65536 * l2 + 16777216 * l3 + 4294967296 * (l3 / 128 * 4294967295)) by reflexivity.
  clearbody U V.
  assert (RU : 0 <= U < 2^32) by lia.
  assert (RV : 0 <= V < 2^64) by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit U), (unsigned_lit V) by lia.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  (* [comment removed for export] *)
  rewrite (unsigned_lit_wrap (U * 2^56)).
  replace ((U * 2 ^ 56) mod 2 ^ 64) with (h0 * 2^56) by (Z.div_mod_to_equations; lia).
  rewrite (land_65280 U) by lia. replace (U / 256 mod 256) with h1 by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (h1 * 256)) by lia. rewrite (unsigned_lit (h1 * 256 * 2^40)) by lia.
  replace (h1 * 256 * 2^40) with (h1 * 2^48) by lia.
  rewrite (lor_add (h0 * 2^56) (h1 * 2^48) 56) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (h0 * 2^56 + h1 * 2^48)) by lia.
  (* [comment removed for export] *)
  rewrite (unsigned_lit_wrap (V * 2^56)).
  replace ((V * 2 ^ 56) mod 2 ^ 64) with (l0 * 2^56) by (Z.div_mod_to_equations; lia).
  replace (l0 * 2^56 / 2^32) with (l0 * 2^24) by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (l0 * 2^24)) by lia.
  rewrite (unsigned_lit_wrap (V * 2^8)).
  rewrite (land_16711680 ((V * 2^8) mod 2^64)) by (Z.div_mod_to_equations; lia).
  replace ((V * 2 ^ 8) mod 2 ^ 64 / 65536 mod 256) with l1 by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (l1 * 65536)) by lia.
  rewrite (lor_add (l0 * 2^24) (l1 * 65536) 24) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (l0 * 2^24 + l1 * 65536)) by lia.
  rewrite (unsigned_lit (V / 2^8)) by (Z.div_mod_to_equations; lia).
  rewrite (land_65280 (V / 2^8)) by (Z.div_mod_to_equations; lia).
  replace (V / 2 ^ 8 / 256 mod 256) with l2 by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (l2 * 256)) by lia.
  rewrite bv_wrap32_eq. replace (V mod 2^32 / 2^24) with l3 by (Z.div_mod_to_equations; lia).
  rewrite (bv_swrap32_small l3) by lia. rewrite (unsigned_lit l3) by lia.
  rewrite (lor_add (l2 * 256) l3 8) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (l2 * 256 + l3)) by lia.
  rewrite (lor_add (l0 * 2^24 + l1 * 65536) (l2 * 256 + l3) 16) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (l0 * 2 ^ 24 + l1 * 65536 + (l2 * 256 + l3))) by lia.
  rewrite (lor_add (h0 * 2^56 + h1 * 2^48) (l0 * 2 ^ 24 + l1 * 65536 + (l2 * 256 + l3)) 48) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (h0 * 2 ^ 56 + h1 * 2 ^ 48 + (l0 * 2 ^ 24 + l1 * 65536 + (l2 * 256 + l3)))) by lia.
  (* [comment removed for export] *)
  rewrite (unsigned_lit_wrap (V * 2^32)).
  replace ((V * 2 ^ 32) mod 2 ^ 64) with ((l0 + 256 * l1 + 65536 * l2 + 16777216 * l3) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite (lor_add ((l0 + 256 * l1 + 65536 * l2 + 16777216 * l3) * 2^32) U 32) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit ((l0 + 256 * l1 + 65536 * l2 + 16777216 * l3) * 2 ^ 32 + U)) by lia.
  rewrite (land_16711680 ((l0 + 256 * l1 + 65536 * l2 + 16777216 * l3) * 2 ^ 32 + U)) by lia.
  replace (((l0 + 256 * l1 + 65536 * l2 + 16777216 * l3) * 2 ^ 32 + U) / 65536 mod 256) with h2 by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (h2 * 65536)) by lia. rewrite (unsigned_lit (h2 * 65536 * 2^24)) by lia.
  rewrite bv_wrap32_eq.
  replace (((l0 + 256 * l1 + 65536 * l2 + 16777216 * l3) * 2 ^ 32 + U) mod 2 ^ 32 / 2 ^ 24) with h3 by (Z.div_mod_to_equations; lia).
  rewrite (bv_swrap32_small h3) by lia. rewrite (unsigned_lit h3) by lia. rewrite (unsigned_lit (h3 * 2^32)) by lia.
  rewrite (lor_add (h2 * 65536 * 2^24) (h3 * 2^32) 40) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (h2 * 65536 * 2 ^ 24 + h3 * 2 ^ 32)) by lia.
  (* [comment removed for export] *)
  rewrite <- (lor_add (h0 * 2^56 + h1 * 2^48) (l0 * 2 ^ 24 + l1 * 65536 + (l2 * 256 + l3)) 48) by (try lia; Z.div_mod_to_equations; lia).
  rewrite <- Z.lor_assoc. rewrite (Z.lor_comm (l0 * 2 ^ 24 + l1 * 65536 + (l2 * 256 + l3))).
  rewrite (lor_add (h2 * 65536 * 2 ^ 24 + h3 * 2 ^ 32) (l0 * 2 ^ 24 + l1 * 65536 + (l2 * 256 + l3)) 32) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add (h0 * 2^56 + h1 * 2^48) _ 48) by (try lia; Z.div_mod_to_equations; lia).
  f_equal. unfold le4val. lia.
Qed.

(* [comment removed for export] *)
Lemma swap32_sxv_mod32 : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  bv_unsigned
   (Z_to_bv 64
      (Z.lor
         (bv_unsigned
            (Z_to_bv 64
               (Z.lor
                  (bv_unsigned
                     (Z_to_bv 64
                        (bv_unsigned (Z_to_bv 64 (sxv a b c d)) ≪ 24)))
                  (bv_unsigned
                     (Z_to_bv 64
                        (bv_unsigned
                           (Z_to_bv 64
                              (Z.land
                                 (bv_unsigned (Z_to_bv 64 (sxv a b c d)))
                                 65280))
                         ≪ 8))))))
         (bv_unsigned
            (Z_to_bv 64
               (Z.lor
                  (bv_unsigned
                     (Z_to_bv 64
                        (Z.land
                           (bv_unsigned
                              (Z_to_bv 64
                                 (bv_unsigned (Z_to_bv 64 (sxv a b c d))
                                  ≫ 8)))
                           65280)))
                  (bv_unsigned
                     (Z_to_bv 64
                        (bv_swrap 32
                           (bv_wrap 32
                              (bv_unsigned (Z_to_bv 64 (sxv a b c d)))
                            ≫ 24)))))))))
 mod 2 ^ 32 = le4val d c b a.
Proof using Type. pin_using tt.
  intros a b c d Ha Hb Hc Hd.
  rewrite (swap32_val (Z_to_bv 64 (sxv a b c d)) a b c d ((d / 128) * 4294967295));
    [ unfold le4val; Z.div_mod_to_equations; lia | lia | lia | lia | lia | Z.div_mod_to_equations; lia |].
  rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia). unfold sxv, le4val. lia.
Qed.

(* [comment removed for export] *)
Lemma ts_word : forall h0 h1 h2 h3 l0 l1 l2 l3,
  0 <= h0 < 256 -> 0 <= h1 < 256 -> 0 <= h2 < 256 -> 0 <= h3 < 256 -> 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (sxv h0 h1 h2 h3))) 32))) (bv_unsigned (Z_to_bv 64 (le4val l0 l1 l2 l3))))
  = Z_to_bv 64 (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3).
Proof using Type. pin_using tt.
  intros h0 h1 h2 h3 l0 l1 l2 l3 R0 R1 R2 R3 S0 S1 S2 S3.
  rewrite (unsigned_lit (sxv h0 h1 h2 h3)) by (unfold sxv, le4val; Z.div_mod_to_equations; lia).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap.
  replace ((sxv h0 h1 h2 h3 * 2 ^ 32) mod 2 ^ 64) with (le4val h0 h1 h2 h3 * 2^32) by (unfold sxv, le4val; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
  rewrite (lor_add (le4val h0 h1 h2 h3 * 2^32) (le4val l0 l1 l2 l3) 32) by (unfold le4val; try lia; Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swap16_word_mod32 : forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
  bv_unsigned
   (Z_to_bv 64
      (bv_unsigned
         (Z_to_bv 64
            (bv_unsigned
               (Z_to_bv 64
                  (Z.lor
                     (bv_unsigned
                        (Z_to_bv 64
                           (bv_unsigned (Z_to_bv 64 (a + 256 * b)) ≪ 8)))
                     (bv_unsigned
                        (Z_to_bv 64
                           (bv_unsigned (Z_to_bv 64 (a + 256 * b)) ≫ 8)))))
             ≪ 48))
       ≫ 48))
 mod 2 ^ 32 = (b + 256 * a)%Z.
Proof using Type. pin_using tt.
  intros a b Ha Hb. rewrite (unsigned_lit (a + 256 * b)) by lia.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  rewrite (unsigned_lit ((a + 256 * b) * 2^8)) by lia.
  replace ((a + 256 * b) / 2^8) with b by (Z.div_mod_to_equations; lia). rewrite (unsigned_lit b) by lia.
  rewrite (lor_add ((a + 256 * b) * 2^8) b 8) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit ((a + 256 * b) * 2 ^ 8 + b)) by lia.
  rewrite (unsigned_lit_wrap (((a + 256 * b) * 2 ^ 8 + b) * 2^48)).
  replace ((((a + 256 * b) * 2 ^ 8 + b) * 2 ^ 48) mod 2 ^ 64) with ((a * 256 + b) * 2^48) by (Z.div_mod_to_equations; lia).
  replace ((a * 256 + b) * 2 ^ 48 / 2 ^ 48) with (a * 256 + b) by (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by lia. Z.div_mod_to_equations; lia.
Qed.
End WithCeil.


Local Open Scope bv_scope.
(* [comment removed for export] *)

Local Close Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Lemma swap_field_eq : forall k off (d : list Z), 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) ->
  swap_field k off d = firstn (Z.to_nat off) d ++ rev (zslice off k d) ++ skipn (Z.to_nat (off + k)) d.
Proof using Type. pin_using tt.
  intros k off d Ho Hk Hl. unfold swap_field, buf_write_at, zfirstn, zskipn, zlength.
  rewrite length_rev, (zslice_length off k d) by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma zslice2_q8 : forall data off, 0 <= off -> off + 2 <= Z.of_nat (length data) ->
  zslice off 2 data = [q8 data off 0; q8 data off 1].
Proof using Type. pin_using tt.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  unfold q8. rewrite Z.add_0_r, E0, E1. exact E.
Qed.

(* [comment removed for export] *)
Lemma shb_swap_data : forall data, 14 <= Z.of_nat (length data) ->
  swap_field 2 12 (swap_field 4 8 data)
  = firstn 8 data ++ [q8 data 8 3; q8 data 8 2; q8 data 8 1; q8 data 8 0] ++ [q8 data 12 1; q8 data 12 0] ++ skipn 14 data.
Proof using Type. pin_using tt.
  intros data Hl.
  assert (L1 : length (swap_field 4 8 data) = length data) by (apply swap_field_length; lia).
  assert (L8 : length (firstn 8 data) = 8%nat) by (rewrite length_firstn; lia).
  pose proof (zslice2_q8 data 12 ltac:(lia) ltac:(lia)) as S2. unfold zslice, zfirstn, zskipn in S2.
  change (Z.to_nat 12) with 12%nat in S2. change (Z.to_nat 2) with 2%nat in S2.
  assert (E4 : swap_field 4 8 data = firstn 8 data ++ [q8 data 8 3; q8 data 8 2; q8 data 8 1; q8 data 8 0] ++ skipn 12 data).
  { rewrite (swap_field_eq 4 8) by lia. rewrite zslice4_q8 by lia. reflexivity. }
  rewrite (swap_field_eq 2 12) by (try lia; rewrite L1; lia). rewrite E4.
  unfold zslice, zfirstn, zskipn. change (Z.to_nat 12) with 12%nat. change (Z.to_nat 2) with 2%nat. change (Z.to_nat (12 + 2)) with 14%nat.
  rewrite !firstn_app, !skipn_app, L8. cbn [Nat.sub length].
  rewrite (firstn_all2 (firstn 8 data)) by lia. rewrite (skipn_all2 (firstn 8 data)) by lia.
  cbn [firstn skipn app Nat.sub]. change (skipn 0 (skipn 12 data)) with (skipn 12 data). rewrite S2. cbn [rev app].
  rewrite (skipn_all2 (firstn 8 data)) by lia. rewrite skipn_skipn. cbn [Nat.add app]. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma idb_swap_data : forall data, 16 <= Z.of_nat (length data) ->
  swap_field 4 12 (swap_field 2 8 data)
  = firstn 8 data ++ [q8 data 8 1; q8 data 8 0] ++ [q8 data 10 0; q8 data 10 1] ++ [q8 data 12 3; q8 data 12 2; q8 data 12 1; q8 data 12 0] ++ skipn 16 data.
Proof using Type. pin_using tt.
  intros data Hl.
  assert (L1 : length (swap_field 2 8 data) = length data) by (apply swap_field_length; lia).
  assert (L8 : length (firstn 8 data) = 8%nat) by (rewrite length_firstn; lia).
  pose proof (zslice4_q8 data 12 ltac:(lia) ltac:(lia)) as S4. unfold zslice, zfirstn, zskipn in S4.
  change (Z.to_nat 12) with 12%nat in S4. change (Z.to_nat 4) with 4%nat in S4.
  pose proof (zslice2_q8 data 10 ltac:(lia) ltac:(lia)) as S10. unfold zslice, zfirstn, zskipn in S10.
  change (Z.to_nat 10) with 10%nat in S10. change (Z.to_nat 2) with 2%nat in S10.
  assert (E2 : swap_field 2 8 data = firstn 8 data ++ [q8 data 8 1; q8 data 8 0] ++ skipn 10 data).
  { rewrite (swap_field_eq 2 8) by lia. rewrite zslice2_q8 by lia. reflexivity. }
  rewrite (swap_field_eq 4 12) by (try lia; rewrite L1; lia). rewrite E2.
  unfold zslice, zfirstn, zskipn. change (Z.to_nat 12) with 12%nat. change (Z.to_nat 4) with 4%nat. change (Z.to_nat (12 + 4)) with 16%nat.
  rewrite !firstn_app, !skipn_app, L8. cbn [Nat.sub length].
  rewrite (firstn_all2 (firstn 8 data)) by lia. rewrite (skipn_all2 (firstn 8 data)) by lia.
  cbn [firstn skipn app Nat.sub].
  rewrite !skipn_skipn. cbn [Nat.add]. rewrite S4.
  replace (firstn 2 (skipn 10 data)) with ([q8 data 10 0; q8 data 10 1]) by (symmetry; exact S10).
  cbn [rev app]. rewrite (skipn_all2 (firstn 8 data)) by lia. cbn [app]. rewrite <- !app_assoc.
  reflexivity.
Qed.
End WithCeil.


Local Open Scope bv_scope.
(* [comment removed for export] *)

Local Close Scope bv_scope.
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition str_bytes (s : string) : list byte :=
  map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string s) ++ [Z_to_bv 8 0].
Lemma str_bytes_length : forall s, length (str_bytes s) = S (String.length s).
Proof using Type. pin_using tt. intros s. unfold str_bytes. rewrite length_app, length_map, length_list_ascii. cbn [length]. lia. Qed.
Lemma str_at_intro : forall m A (s : string),
  mem_inv usegs m -> ro_bytes_b usegs A (str_bytes s) = true ->
  0x10000 <= A -> A + Z.of_nat (String.length s) + 1 <= 0x13000 -> bytes_at usegs m A (str_bytes s).
Proof using Type. pin_using tt.
  intros m A s MI RO LO HI.
  pose proof (ro_cells_image usegs m A _ MI RO ltac:(lia)) as X. rewrite str_bytes_length in X.
  pose proof (ro_cells_bytes_at _ _ _ _ (X ltac:(lia))) as Y. cbn [cells_bytes cbytes] in Y. rewrite app_nil_r in Y. exact Y.
Qed.

(* [comment removed for export] *)
Lemma sextw_word : forall (w : word) v, (bv_unsigned w mod 2^32 = v)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + 0)) = Z_to_bv 64 (sxu v).
Proof using Type. pin_using tt.
  intros w v Hv. apply bv_eq. rewrite unsigned_sextw, Hv.
  assert (R : 0 <= v < 2^32) by (rewrite <- Hv; apply Z.mod_pos_bound; lia).
  symmetry. apply unsigned_lit. apply sxu_range'. exact R.
Qed.

(* [comment removed for export] *)
Lemma splice_length : forall (data mid : list Z) k, (k + length mid <= length data)%nat ->
  length (firstn k data ++ mid ++ skipn (k + length mid) data) = length data.
Proof using Type. pin_using tt. intros data mid k Hk. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma splice_pfx : forall (data mid : list Z) (bs : list byte) (k : nat),
  firstn (length data) bs = map b8 data -> (k + length mid <= length data)%nat -> (length data <= length bs)%nat ->
  firstn (length (firstn k data ++ mid ++ skipn (k + length mid) data)) (firstn k bs ++ map b8 mid ++ skipn (k + length mid) bs)
  = map b8 (firstn k data ++ mid ++ skipn (k + length mid) data).
Proof using Type. pin_using tt.
  intros data mid bs k PFX Hk Hl. rewrite splice_length by lia.
  assert (L1 : length (firstn k bs) = k) by (rewrite length_firstn; lia).
  assert (L2 : length (map b8 mid) = length mid) by apply length_map.
  rewrite firstn_app, L1, firstn_all2 by (rewrite L1; lia).
  rewrite firstn_app, L2, (firstn_all2 (map b8 mid)) by (rewrite L2; lia).
  rewrite !map_app, <- firstn_map, <- skipn_map, <- PFX.
  rewrite firstn_firstn by lia. replace (Nat.min k (length data)) with k by lia.
  f_equal. f_equal. rewrite firstn_skipn_comm. f_equal. f_equal. lia.
Qed.

Lemma splice_Forall : forall (data mid : list Z) k (Q : Z -> Prop),
  Forall Q data -> Forall Q mid -> Forall Q (firstn k data ++ mid ++ skipn (k + length mid) data).
Proof using Type. pin_using tt.
  intros data mid k Q HD HM. apply Forall_app; split; [| apply Forall_app; split; [exact HM|]].
  - rewrite <- (firstn_skipn k data) in HD. apply Forall_app in HD. tauto.
  - rewrite <- (firstn_skipn (k + length mid) data) in HD. apply Forall_app in HD. tauto.
Qed.

(* [comment removed for export] *)
Lemma shb_splice_le32 : forall (data : list Z) g3 g2 g1 g0 j1 j0, (14 <= length data)%nat ->
  get_le32 (firstn 8 data ++ [g3; g2; g1; g0; j1; j0] ++ skipn 14 data) 8 = le4val g3 g2 g1 g0.
Proof using Type. pin_using tt.
  intros data g3 g2 g1 g0 j1 j0 Hl.
  assert (L8 : length (firstn 8 data) = 8%nat) by (rewrite length_firstn; lia).
  rewrite (get_le32_of_slice 8 _ g3 g2 g1 g0); [unfold le4val; lia|].
  unfold zslice, zfirstn, zskipn. change (Z.to_nat 8) with 8%nat. change (Z.to_nat 4) with 4%nat.
  rewrite skipn_app, L8, skipn_all2 by lia. cbn [Nat.sub skipn app firstn]. reflexivity.
Qed.
Lemma shb_splice_le16 : forall (data : list Z) g3 g2 g1 g0 j1 j0, (14 <= length data)%nat ->
  get_le16 (firstn 8 data ++ [g3; g2; g1; g0; j1; j0] ++ skipn 14 data) 12 = j1 + 256 * j0.
Proof using Type. pin_using tt.
  intros data g3 g2 g1 g0 j1 j0 Hl.
  assert (L8 : length (firstn 8 data) = 8%nat) by (rewrite length_firstn; lia).
  rewrite (get_le16_of_slice 12 _ j1 j0); [lia|].
  unfold zslice, zfirstn, zskipn. change (Z.to_nat 12) with 12%nat. change (Z.to_nat 2) with 2%nat.
  rewrite skipn_app, L8, skipn_all2 by lia. cbn [Nat.sub skipn app firstn]. reflexivity.
Qed.

Lemma shb_swap_data' : forall data, 14 <= Z.of_nat (length data) ->
  swap_field 2 12 (swap_field 4 8 data)
  = firstn 8 data ++ [q8 data 8 3; q8 data 8 2; q8 data 8 1; q8 data 8 0; q8 data 12 1; q8 data 12 0] ++ skipn 14 data.
Proof using Type. pin_using tt. intros data Hl. rewrite shb_swap_data by lia. reflexivity. Qed.
End WithCeil.

Local Open Scope bv_scope.
(* [comment removed for export] *)

Local Close Scope bv_scope.
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma zext16_shifts : forall (w : word),
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 48))) 48) = Z_to_bv 64 (bv_unsigned w mod 2^16).
Proof using Type. pin_using tt.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R.
  f_equal. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma sxv_s32_word : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  Z_to_bv 64 (sxv a b c d) = Z_to_bv 64 (s32 (le4val a b c d)).
Proof using Type. pin_using tt.
  intros a b c d Ha Hb Hc Hd. rewrite <- (sx32_lit a b c d) by lia. apply sx32_s32. unfold le4val. lia.
Qed.
(* [comment removed for export] *)
Lemma idb_splice_le16 : forall (data : list Z) l1 l0 r0 r1 n3 n2 n1 n0, (16 <= length data)%nat ->
  get_le16 (firstn 8 data ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data) 8 = l1 + 256 * l0.
Proof using Type. pin_using tt.
  intros data l1 l0 r0 r1 n3 n2 n1 n0 Hl.
  assert (L8 : length (firstn 8 data) = 8%nat) by (rewrite length_firstn; lia).
  rewrite (get_le16_of_slice 8 _ l1 l0); [lia|].
  unfold zslice, zfirstn, zskipn. change (Z.to_nat 8) with 8%nat. change (Z.to_nat 2) with 2%nat.
  rewrite skipn_app, L8, skipn_all2 by lia. cbn [Nat.sub skipn app firstn]. reflexivity.
Qed.
Lemma idb_splice_le32 : forall (data : list Z) l1 l0 r0 r1 n3 n2 n1 n0, (16 <= length data)%nat ->
  get_le32 (firstn 8 data ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data) 12 = le4val n3 n2 n1 n0.
Proof using Type. pin_using tt.
  intros data l1 l0 r0 r1 n3 n2 n1 n0 Hl.
  assert (L8 : length (firstn 8 data) = 8%nat) by (rewrite length_firstn; lia).
  rewrite (get_le32_of_slice 12 _ n3 n2 n1 n0); [unfold le4val; lia|].
  unfold zslice, zfirstn, zskipn. change (Z.to_nat 12) with 12%nat. change (Z.to_nat 4) with 4%nat.
  rewrite skipn_app, L8, skipn_all2 by lia. cbn [Nat.sub skipn app firstn]. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma idb_swap_data' : forall data, 16 <= Z.of_nat (length data) ->
  swap_field 4 12 (swap_field 2 8 data)
  = firstn 8 data ++ [q8 data 8 1; q8 data 8 0; q8 data 10 0; q8 data 10 1; q8 data 12 3; q8 data 12 2; q8 data 12 1; q8 data 12 0] ++ skipn 16 data.
Proof using Type. pin_using tt. intros data Hl. rewrite idb_swap_data by lia. reflexivity. Qed.
End WithCeil.

Local Open Scope bv_scope.
(* [comment removed for export] *)

Local Close Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Lemma signed_lit_s32 : forall x, bv_signed (Z_to_bv 64 (s32 x)) = s32 x.
Proof using Type. pin_using tt.
  intros x. pose proof (s32_range x) as R. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_lt_dec (s32 x) 0).
  - replace ((s32 x) mod 2^64) with (s32 x + 2^64) by (Z.div_mod_to_equations; lia).
    replace (s32 x + 2 ^ 64 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite Z.mod_small by lia. replace (s32 x <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma s32_cases : forall x, 0 <= x < 2^32 -> (x < 2^31 /\ s32 x = x) \/ (2^31 <= x /\ s32 x = x - 2^32).
Proof using Type. pin_using tt. intros x Hx. unfold s32. destruct (Z_lt_dec x (2^31)); [left | right]; split; try lia; Z.div_mod_to_equations; lia. Qed.
End WithCeil.

Local Open Scope bv_scope.