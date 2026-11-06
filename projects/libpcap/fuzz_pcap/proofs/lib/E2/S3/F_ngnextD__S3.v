(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require NgnPure.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_ngnextD.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (bv_swrap _ (Z.add (bv_unsigned _) (0)%Z)) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Definition swap32s_word__stmt : Prop := forall (w : word) a b c d hi, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> 0 <= hi < 2^32 ->
  bv_unsigned w = a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi ->
  Z_to_bv 64
    (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned w) 24))))
                                            (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned w) 65280))) 8))))))
           (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 8))) 65280)))
                                            (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24))))))))
  = Z_to_bv 64 (sxu (le4val d c b a)).
Section Sz6.
Variables w a b c d hi : ltac2:(SecDiet.SzSec.tyM 'swap32s_word__stmt "vvvvvv" @w).
Lemma swap32s_word__body : ltac2:(SecDiet.SzSec.bodyP 'swap32s_word__stmt "vvvvvv").
Proof using Type. pin_using tt.
  intros Ha Hb Hc Hd Hhi E.
 rewrite E. clear E w.
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
End Sz6.
Lemma swap32s_word : ltac:(let t := eval cbv delta [swap32s_word__stmt] in swap32s_word__stmt in exact t).
Proof using Type. intros w a b c d hi. ltac2:(SecDiet.SzSec.closeP 'swap32s_word__body "vvvvvv"). Qed.

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
Definition ts_swap_word__stmt : Prop := forall h0 h1 h2 h3 l0 l1 l2 l3,
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
Section Sz11.
Variables h0 h1 h2 h3 l0 l1 l2 l3 : ltac2:(SecDiet.SzSec.tyM 'ts_swap_word__stmt "vvvvvvvv" @h0).
Lemma ts_swap_word__body : ltac2:(SecDiet.SzSec.bodyP 'ts_swap_word__stmt "vvvvvvvv").
Proof using Type. pin_using tt.
  intros R0 R1 R2 R3 S0 S1 S2 S3.
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
End Sz11.
Lemma ts_swap_word : ltac:(let t := eval cbv delta [ts_swap_word__stmt] in ts_swap_word__stmt in exact t).
Proof using Type. intros h0 h1 h2 h3 l0 l1 l2 l3. ltac2:(SecDiet.SzSec.closeP 'ts_swap_word__body "vvvvvvvv"). Qed.

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
Definition ts_word__stmt : Prop := forall h0 h1 h2 h3 l0 l1 l2 l3,
  0 <= h0 < 256 -> 0 <= h1 < 256 -> 0 <= h2 < 256 -> 0 <= h3 < 256 -> 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (sxv h0 h1 h2 h3))) 32))) (bv_unsigned (Z_to_bv 64 (le4val l0 l1 l2 l3))))
  = Z_to_bv 64 (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3).
Section Sz13.
Variables h0 h1 h2 h3 l0 l1 l2 l3 : ltac2:(SecDiet.SzSec.tyM 'ts_word__stmt "vvvvvvvv" @h0).
Lemma ts_word__body : ltac2:(SecDiet.SzSec.bodyP 'ts_word__stmt "vvvvvvvv").
Proof using Type. pin_using tt.
  intros R0 R1 R2 R3 S0 S1 S2 S3.
  rewrite (unsigned_lit (sxv h0 h1 h2 h3)) by (unfold sxv, le4val; Z.div_mod_to_equations; lia).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap.
  replace ((sxv h0 h1 h2 h3 * 2 ^ 32) mod 2 ^ 64) with (le4val h0 h1 h2 h3 * 2^32) by (unfold sxv, le4val; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
  rewrite (lor_add (le4val h0 h1 h2 h3 * 2^32) (le4val l0 l1 l2 l3) 32) by (unfold le4val; try lia; Z.div_mod_to_equations; lia).
  reflexivity.
Qed.
End Sz13.
Lemma ts_word : ltac:(let t := eval cbv delta [ts_word__stmt] in ts_word__stmt in exact t).
Proof using Type. intros h0 h1 h2 h3 l0 l1 l2 l3. ltac2:(SecDiet.SzSec.closeP 'ts_word__body "vvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition swap16_word_mod32__stmt : Prop := forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
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
Section Sz14.
Variables a b : ltac2:(SecDiet.SzSec.tyM 'swap16_word_mod32__stmt "vv" @a).
Lemma swap16_word_mod32__body : ltac2:(SecDiet.SzSec.bodyP 'swap16_word_mod32__stmt "vv").
Proof using Type. pin_using tt.
  intros Ha Hb.
 rewrite (unsigned_lit (a + 256 * b)) by lia.
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
End Sz14.
Lemma swap16_word_mod32 : ltac:(let t := eval cbv delta [swap16_word_mod32__stmt] in swap16_word_mod32__stmt in exact t).
Proof using Type. intros a b. ltac2:(SecDiet.SzSec.closeP 'swap16_word_mod32__body "vv"). Qed.
End WithCeil.


Local Open Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.
  (* [comment removed for export] *)
  #[local] Abbreviation pv := (F_ngnextA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (F_ngnextA.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (F_ngnextA.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (F_ngnextA.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (F_ngnextA.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (F_ngnextA.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (F_ngnextA.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (F_ngnextA.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (F_ngnextA.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (F_ngnextA.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (F_ngnextA.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (F_ngnextA.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold F_ngnextA.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold F_ngnextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  (* [comment removed for export] *)
  Definition ccells (Bq rem bt : Z) (cpad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (Bq + 8)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad].

  (* [comment removed for export] *)
  Definition ngn_spb__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (4 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK
                     (let len := (if swapped then bswap32 (get_le32 data 8) else get_le32 data 8) in
                      mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor (8 + 4) (rem - 4) bt))
                     (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17814) fc None m5 (seg_rom ssegs)).
  Section Sz15.
  Variables ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_spb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_spb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_spb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    (* [comment removed for export] *)
    try change (8 + 4)%Z with 12%Z.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold F_ngnextA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnextA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    set (g0 := q8 data 8 0). set (g1 := q8 data 8 1). set (g2 := q8 data 8 2). set (g3 := q8 data 8 3).
    pose proof (q8_range data 8 0 DRNG ltac:(lia)) as R0. pose proof (q8_range data 8 1 DRNG ltac:(lia)) as R1'.
    pose proof (q8_range data 8 2 DRNG ltac:(lia)) as R2'. pose proof (q8_range data 8 3 DRNG ltac:(lia)) as R3'.
    fold g0 in R0. fold g1 in R1'. fold g2 in R2'. fold g3 in R3'.
    rewrite (get_le32_q8 data 8) by lia. fold g0 g1 g2 g3.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; Z.to_nat alloc - 12]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite (firstn4_q8 data bsx' 8 8 PFX eq_refl) in BUF by lia. fold g0 g1 g2 g3 in BUF.
    assert (BUF4 : rw_cells ssegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); CB (Z.to_nat alloc - 12) (firstn (Z.to_nat alloc - 12) (skipn 4 (skipn 8 bsx')))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4 LBS; lia). }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit g0 g1 g2 g3) by lia. reflexivity. }
    clear BUF.
    (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
    assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
    apply (rw_cells_split_CB ssegs m5 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. step. if_cases BR0; zify_cond BR0. { exfalso. rewrite ?unsigned_lit in BR0 by lia. clear -BR0 K1 K3 K4. lia. }
    step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. rewrite (sx32_lit g0 g1 g2 g3) by lia.
    step.
    (* [comment removed for export] *)
    assert (K18 : forall (a1v a4v a6v : word) (len : Z), (0 <= len < 2^32)%Z ->
      evt ssegs (fun ms' => impl ssegs (at_node ssegs) (npeek ssegs)
        (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK (mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor (8 + 4) (rem - 4) bt)) (pv bq alloc data eb sx ix) ps)
        (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) a1v (Z_to_bv 64 (sxu len)) (Z_to_bv 64 (s32 bt)) a4v (Z_to_bv 64 (Bq + 8)) a6v a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17854) fc None m5 (seg_rom ssegs))).
    { intros a1v a4v a6v len Hlen. try change (8 + 4)%Z with 12%Z. pose proof (sxu_range' len Hlen) as SR. pose proof (sxu_range len Hlen) as (_ & SX2 & SX3).
      step. step. rewrite (sx32_small snapshot) by lia. step.
      (* [comment removed for export] *)
      assert (KJ : forall (cap : Z) (cw : word) (m6 : mem), (bv_unsigned cw mod 2^32 = cap)%Z -> cap = (if snapshot <? len then snapshot else len) ->
        munch [(HA, HA + 24)]%Z m5 m6 -> wmono ssegs m5 m6 -> mem_inv ssegs m6 -> stk ssegs m6 lo (bv_unsigned sp + -160) ->
        rw_cells ssegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); CB 4 (firstn 4 (skipn 8 (skipn 8 hj))); C4 (Z_to_bv 64 (sxu len))] ->
        rw_cells ssegs m6 (bv_unsigned sp + -160) (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj (ccells Bq rem bt cpad)) ->
        rw_cells ssegs m6 DA [CB 8 dwj] ->
        evt ssegs (fun ms' => impl ssegs (at_node ssegs) (npeek ssegs)
          (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK (mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor (8 + 4) (rem - 4) bt)) (pv bq alloc data eb sx ix) ps)
          (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                   (Z_to_bv 64 rem) (Z_to_bv 64 snapshot) cw (Z_to_bv 64 (s32 bt)) a4v (Z_to_bv 64 (Bq + 8)) a6v a7'
                   x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x17868) fc None m6 (seg_rom ssegs))).
      { intros cap cw m6 Hcw Ecap MU6 WM6 MI6 ST6 HH6 FR6 HD6. try change (8 + 4)%Z with 12%Z.
        assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite Ecap; destruct (snapshot <? len); lia).
        assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        unhide FR5. unhide PRIV. unhide IFS. clear FR5.
        assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. lia. }
        assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
        { eapply PCAPR_agree; [exact AGP6 | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
        assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP6|]. intros a [_ [Hna _]]. cbn [outside]. (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj cw a Hna; lia). }
        clear MU WM. pose proof (munch_refl [(HA, HA + 24)]%Z m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
        pose proof FR6 as FRJ'. unfold F_ngnextA.ngn_frame, ccells in FRJ'. cbn [app] in FRJ'. clear FRJ.
        hide FR6. hide HD6. step. step. step. step. step. step. unhide FR6. unhide HD6.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold F_ngnextA.ngn_frame, ccells in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD6; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R2; lia].
        assert (G7 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. lia. }
        assert (PC7 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7).
        { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G6 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
        assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj cw a Hna; lia). }
        lazymatch goal with HHx : rw_cells ssegs m7 HA ?cs |- _ =>
          assert (HH7 : rw_cells ssegs m7 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
            by (eapply rw_cells_recell; [exact HHx | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj cw LHJ; lia)
                                         | cbn [cells_bytes cbytes app]; rewrite (le4_word_mod32 cw cap Hcw), (le4_word_mod32 (Z_to_bv 64 (sxu len)) len) by (rewrite unsigned_lit by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw len bsx' hj cw SR; lia); apply sxu_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw len bsx' hj cw Hlen; lia)); reflexivity]);
          clear HHx end.
        apply evt_done. rewrite <- Ecap.
        replace (Z_to_bv 64 (rem + -4)) with (Z_to_bv 64 (rem - 4)) by (f_equal; lia).
        replace (Z_to_bv 64 (Bq + 8 + 4)) with (Z_to_bv 64 (Bq + 12)) by (f_equal; lia).
        eapply (ngn_found _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) cw _ _ m7 ps bq Bq Ix alloc 12 (rem - 4) data eb sx ix 0 0 cap len bt);
          [assumption | exact FR6 | reflexivity | assumption | exact G7 | exact PC7 | exact AG7 | exact HH7 | exact HD6 | reflexivity
          | rewrite unsigned_lit by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj cw; lia); reflexivity | exact Hcw | (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj cw; lia) | exact DRNG | (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj cw; lia) | reflexivity | (keep_hyps CEILV sp R P HA DA Bq alloc rem data hcs dw bsx' hj cw REM; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj cw LEN; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj cw LEN L30; lia) | | exact Hbt | exact OF5].
        destruct (Z.ltb_spec snapshot len); lia. }
      step. if_cases BR; zify_cond BR.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in BR by lia.
        assert (LT : (len < snapshot)%Z) by (destruct (Z_lt_dec len (2^31)); [rewrite SX2 in BR by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw len bsx' hj l; lia); (keep_hyps CEILV sp R P HA DA snapshot Bq alloc data hcs dw len bsx' hj BR; lia)| specialize (SX3 ltac:((keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw len bsx' hj n; lia))); (keep_hyps CEILV sp R P HA DA snapshot Bq alloc data hcs dw len bsx' hj W1' SX3 BR; lia)]).
        eapply (KJ len); [rewrite unsigned_lit by lia; apply sxu_mod32; lia | replace (snapshot <? len) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
                         | exact MU | exact WM | assumption | assumption | assumption | assumption | exact HD'].
      - rewrite ?unsigned_lit in BR by lia.
        step.
        eapply (KJ snapshot); [rewrite unsigned_lit by lia; apply Z.mod_small; lia | | exact MU | exact WM | assumption | assumption | assumption | assumption | exact HD'].
        destruct (Z_lt_dec len (2^31)); [rewrite SX2 in BR by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw len bsx' hj l; lia)| specialize (SX3 ltac:((keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw len bsx' hj n; lia)))]; destruct (Z.ltb_spec snapshot len); (keep_hyps CEILV sp R P HA DA snapshot Bq alloc data hcs dw bsx' hj len BR H0 lo rem W1' n; lia). }
    destruct swapped.
    - (* [comment removed for export] *)
      if_false. do 11 step.
      rewrite (swap32s_word (Z_to_bv 64 (sxv g0 g1 g2 g3)) g0 g1 g2 g3 ((g3 / 128) * 4294967295)) by (unfold sxv, le4val; try (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj R0 R1' R2' R3' lo rem; lia); rewrite unsigned_lit by (Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 R0 R1' R2' R3' H0 H1; lia)); Z.div_mod_to_equations; (keep_hyps CEILV R alloc data hcs dw bsx' hj q; lia)).
      rewrite (bswap32_le4val g0 g1 g2 g3) by lia.
      apply (K18 _ _ _ (le4val g3 g2 g1 g0)). unfold le4val. lia.
    - if_true. rewrite (sxv_sxu g0 g1 g2 g3) by lia.
      apply (K18 _ _ _ (le4val g0 g1 g2 g3)). unfold le4val. lia.
  Qed.
  End Sz15.
  Lemma ngn_spb : ltac:(let t := eval cbv delta [ngn_spb__stmt] in ngn_spb__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_spb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Ltac name_field data off a b c d DRNG :=
    set (a := q8 data off 0%Z) in *; set (b := q8 data off 1%Z) in *; set (c := q8 data off 2%Z) in *; set (d := q8 data off 3%Z) in *;
    let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
    pose proof (q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
    pose proof (q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
    fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

  (* [comment removed for export] *)
  Definition ngn_epb_swap__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a0' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (mx : mem)
           (i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 : Z) (Bq : Z) (djw : list byte) (pre : list byte) (rest tfr : list cell) (hj1 hj2 hj3 hj4 : list byte),
      Forall (fun x => 0 <= x < 256)%Z [i0; i1; i2; i3; h0; h1; h2; h3; l0; l1; l2; l3; c0; c1; c2; c3; n0; n1; n2; n3] ->
      rw_cells ssegs mx Bq ([CB 8 pre; C4 (Z_to_bv 64 (le4val i0 i1 i2 i3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                             C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ++ rest) ->
      rw_cells ssegs mx (bv_unsigned sp + -160) ([CB 8 djw; C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 HA)] ++ tfr) ->
      rw_cells ssegs mx HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] -> mem_inv ssegs mx ->
      (HA + 24 <= Bq \/ Bq + 28 <= HA)%Z -> (bv_unsigned sp <= HA)%Z -> (HA + 24 <= 2^64)%Z ->
      evt ssegs (fun ms' => exists (a1v a2v a4v a7v lw y0 y1 y2 y3 y4 y5 y6 : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y0 y1 y2 x0 x1 a0' a1v a2v a3' a4v a5' y3 a7v
                       x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) y4 y5 y6) F (Z_to_bv 64 0x179b4) fc None m' (seg_rom ssegs)
          /\ munch [(HA, HA + 24)]%Z mx m' /\ wmono ssegs mx m' /\ mem_inv ssegs m'
          /\ rw_cells ssegs m' HA [CB 8 hj1; CB 8 hj2; C4 a2v; C4 lw]
          /\ (bv_unsigned a1v mod 2^32 = le4val i3 i2 i1 i0)%Z /\ (bv_unsigned a2v mod 2^32 = le4val c3 c2 c1 c0)%Z
          /\ (bv_unsigned lw mod 2^32 = le4val n3 n2 n1 n0)%Z /\ a7v = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' (Z_to_bv 64 (sxv i0 i1 i2 i3)) a2' a3' (Z_to_bv 64 (Bq + 8)) a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x1789c) fc None mx (seg_rom ssegs)).
  Section Sz16.
  Variables ra' t0' t1' t2' x0 x1 a0' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq djw pre rest tfr hj1 hj2 hj3 hj4 : ltac2:(SecDiet.SzSec.tyM 'ngn_epb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_epb_swap__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R2 SPW. pin_using (fun (BU LO P1 R2 SPW : unit) => tt).
    intros GR HB HF HH MI SEP HHA HA64.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(HA, HA + 24)]%Z mx) as MU. pose proof (wmono_refl ssegs mx) as WM.
    do 4 step. step. rewrite (zx32_lit (le4val h0 h1 h2 h3)) by (unfold le4val; lia).
    step. rewrite (sx32_lit l0 l1 l2 l3) by lia. step. rewrite (sx32_lit c0 c1 c2 c3) by lia. step. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    do 47 step. hide HB. hide HF. do 6 step.
    apply evt_done. cbv beta.
    lazymatch goal with HX : rw_cells ssegs _ HA [_; _; C4 _; C4 ?lwv] |- _ =>
      do 4 eexists; exists lwv; do 8 eexists; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply swap32_sxv_mod32; assumption|]. split; [apply swap32_sxv_mod32; assumption|].
    split; [apply swap32_sxv_mod32; assumption|]. apply ts_swap_word; assumption.
  Qed.
  End Sz16.
  Lemma ngn_epb_swap : ltac:(let t := eval cbv delta [ngn_epb_swap__stmt] in ngn_epb_swap__stmt in exact t).
  Proof using BU LO P1 R2 SPW. intros ra' t0' t1' t2' x0 x1 a0' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq djw pre rest tfr hj1 hj2 hj3 hj4. ltac2:(SecDiet.SzSec.closeP 'ngn_epb_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_epb__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (20 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK
                     (let sw32 (v : Z) := if swapped then bswap32 v else v in
                      mkFound (sw32 (get_le32 data 8)) (sw32 (get_le32 data 12) * 2^32 + sw32 (get_le32 data 16)) (sw32 (get_le32 data 20)) (sw32 (get_le32 data 24))
                              (mkCursor (8 + 20) (rem - 20) bt))
                     (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17880) fc None m5 (seg_rom ssegs)).
  Section Sz17.
  Variables ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_epb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_epb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold F_ngnextA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnextA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    name_field data 8%Z i0 i1 i2 i3 DRNG. name_field data 12%Z h0 h1 h2 h3 DRNG. name_field data 16%Z l0 l1 l2 l3 DRNG.
    name_field data 20%Z c0 c1 c2 c3 DRNG. name_field data 24%Z n0 n1 n2 n3 DRNG.
    cbv zeta.
    rewrite (get_le32_q8 data 8), (get_le32_q8 data 12), (get_le32_q8 data 16), (get_le32_q8 data 20), (get_le32_q8 data 24) by (keep_hyps CEILV sp R P HA DA Bq data hcs dw lo rem LEN REM; lia).
    fold i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3. fold c0 c1 c2 c3 n0 n1 n2 n3.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 4; 4; 4; 4; Z.to_nat alloc - 28]%nat) in BUF; [| cbn; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4; lia)]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (firstn4_q8 data bsx' 8 8%Z PFX eq_refl), (firstn4_q8 data bsx' 12 12%Z PFX eq_refl), (firstn4_q8 data bsx' 16 16%Z PFX eq_refl),
            (firstn4_q8 data bsx' 20 20%Z PFX eq_refl), (firstn4_q8 data bsx' 24 24%Z PFX eq_refl) in BUF by (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM; lia).
    fold i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 in BUF. fold c0 c1 c2 c3 n0 n1 n2 n3 in BUF.
    assert (BUF4 : rw_cells ssegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val i0 i1 i2 i3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                                       C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 28) (firstn (Z.to_nat alloc - 28) (skipn 28 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4 LBS; lia). }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit i0 i1 i2 i3), (le4_lit h0 h1 h2 h3), (le4_lit l0 l1 l2 l3), (le4_lit c0 c1 c2 c3), (le4_lit n0 n1 n2 n3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' Ri0 Ri1 Ri2 Ri3 Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3 Rc0 Rc1 Rc2 Rc3 Rn0 Rn1 Rn2 Rn3; lia). reflexivity. }
    clear BUF.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
    assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
    apply (rw_cells_split_CB ssegs m5 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. step. if_cases BR0; zify_cond BR0. { exfalso. rewrite ?unsigned_lit in BR0 by lia. clear -BR0 K1 K3 K4. lia. }
    step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. rewrite (sx32_lit i0 i1 i2 i3) by lia.
    step. step. step.
    (* [comment removed for export] *)
    assert (JOIN : forall (iw cw lw a4v a7v y0 y1 y2 y3 y4 y5 y6 : word) (m6 : mem) (idv capv lenv tv : Z),
      munch [(HA, HA + 24)]%Z m5 m6 -> wmono ssegs m5 m6 -> mem_inv ssegs m6 -> stk ssegs m6 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 cw; C4 lw] ->
      rw_cells ssegs m6 (bv_unsigned sp + -160) (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj (ccells Bq rem bt cpad)) ->
      rw_cells ssegs m6 DA [CB 8 dwj] ->
      (bv_unsigned iw mod 2^32 = idv)%Z -> (bv_unsigned cw mod 2^32 = capv)%Z -> (bv_unsigned lw mod 2^32 = lenv)%Z ->
      a7v = Z_to_bv 64 tv -> (0 <= tv < 2^64)%Z -> (0 <= idv < 2^32)%Z -> (0 <= capv < 2^32)%Z -> (0 <= lenv < 2^32)%Z ->
      idv = (if swapped then bswap32 (le4val i0 i1 i2 i3) else le4val i0 i1 i2 i3) ->
      tv = ((if swapped then bswap32 (le4val h0 h1 h2 h3) else le4val h0 h1 h2 h3) * 2^32 + (if swapped then bswap32 (le4val l0 l1 l2 l3) else le4val l0 l1 l2 l3))%Z ->
      capv = (if swapped then bswap32 (le4val c0 c1 c2 c3) else le4val c0 c1 c2 c3) ->
      lenv = (if swapped then bswap32 (le4val n0 n1 n2 n3) else le4val n0 n1 n2 n3) ->
      evt ssegs (fun ms' => impl ssegs (at_node ssegs) (npeek ssegs)
        (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK
           (mkFound (if swapped then bswap32 (le4val i0 i1 i2 i3) else le4val i0 i1 i2 i3)
                    ((if swapped then bswap32 (le4val h0 h1 h2 h3) else le4val h0 h1 h2 h3) * 2 ^ 32 + (if swapped then bswap32 (le4val l0 l1 l2 l3) else le4val l0 l1 l2 l3))
                    (if swapped then bswap32 (le4val c0 c1 c2 c3) else le4val c0 c1 c2 c3)
                    (if swapped then bswap32 (le4val n0 n1 n2 n3) else le4val n0 n1 n2 n3)
                    (mkCursor 28 (rem - 20) bt)) (pv bq alloc data eb sx ix) ps)
        (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y0 y1 y2 (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (rem + -20)) iw cw (Z_to_bv 64 (s32 bt)) a4v (Z_to_bv 64 (Bq + 28)) y3 a7v
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) y4 y5 y6) F (Z_to_bv 64 0x179b4) fc None m6 (seg_rom ssegs))).
    { intros iw cw lw a4v a7v y0 y1 y2 y3 y4 y5 y6 m6 idv capv lenv tv MU6 WM6 MI6 ST6 HH6 FR6 HD6 Hiw Hcw Hlw -> Htv Hid Hcap Hlen Eid Etv Ecap Elen.
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      unhide FR5. unhide PRIV. unhide IFS. clear FR5.
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LO BU R1 R2 R3; lia). }
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header ps bq Bq Ix alloc data eb sx ix hcs dw bsx' hj iw cw lw m6 a LO BU R1 G6 H0; lia). }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj iw cw lw a Hna; lia). }
      assert (HH7 : rw_cells ssegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 capv); C4 (Z_to_bv 64 lenv)]).
      { eapply rw_cells_recell; [exact HH6 | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LHJ; lia) |].
        cbn [cells_bytes cbytes app]. rewrite (le4_word_mod32 cw capv Hcw), (le4_word_mod32 lw lenv Hlw). reflexivity. }
      apply evt_done. rewrite <- Eid, <- Etv, <- Ecap, <- Elen.
      replace (Z_to_bv 64 (rem + -20)) with (Z_to_bv 64 (rem - 20)) by (f_equal; lia).
      eapply (ngn_found _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iw cw _ _ m6 ps bq Bq Ix alloc 28 (rem - 20) data eb sx ix idv tv capv lenv bt);
        [exact ST6 | exact FR6 | reflexivity | exact MI6 | exact G6 | exact PC6 | exact AG6 | exact HH7 | exact HD6 | reflexivity
        | exact Hiw | exact Hcw | exact Htv | exact DRNG | (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj iw cw lw; lia) | reflexivity | (keep_hyps CEILV sp R P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw REM; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LEN; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LEN L30; lia) | exact Hlen | exact Hbt | exact OF5]. }
    destruct swapped.
    - (* [comment removed for export] *)
      if_false.
      eapply evt_cut.
      { eapply (ngn_epb_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq dj);
          [repeat (apply Forall_cons; [(keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Ri0 Ri1 Ri2 Ri3 Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3 Rc0 Rc1 Rc2 Rc3 Rn0 Rn1 Rn2 Rn3; lia)|]); apply Forall_nil | exact BUF4 | exact FRJ | exact HHj | assumption | gio_ceil_fact; clear -CLO__ K1 K4 R1 LO BU SPM SPW W4 LEN REM; unfold rc_lo, rc_spmain in *; (keep_hyps CEILV sp R lo HA Bq alloc rem data LO BU R1 K4 W4 CLO__; lia) | exact R1 | clear -R1 R2 R3 SP47 SPM; unfold rc_spmain in *; (keep_hyps R HA DA R2 R3 SP47; lia)]. }
      cbv beta. intros ms' (a1v & a2v & a4v & a7v & lw & y0 & y1 & y2 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & HH6 & Hi & Hc & Hl & Ht).
      assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      pose proof (agrees_stk _ _ _ _ _ AGP6 ST5 ltac:(intros a Ha; cbn [outside]; (keep_hyps CEILV sp R lo P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw a R1 Ha; lia))) as ST6.
      unhide FR5. pose proof FR5 as FR6. hide FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGP6) in FR6; [| intros a Ha; unfold F_ngnextA.ngn_frame, ccells in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia].
      pose proof HD' as HD6. apply (agrees_rw_cells _ _ _ _ _ AGP6) in HD6; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R2; lia].
      eapply (JOIN a1v a2v lw a4v a7v y0 y1 y2 y3 y4 y5 y6 m6 (le4val i3 i2 i1 i0) (le4val c3 c2 c1 c0) (le4val n3 n2 n1 n0) (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z);
        [exact MU6 | exact WM6 | exact MI6 | exact ST6 | exact HH6 | exact FR6 | exact HD6 | exact Hi | exact Hc | exact Hl | exact Ht
        | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Ri0 Ri1 Ri2 Ri3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rc0 Rc1 Rc2 Rc3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rn0 Rn1 Rn2 Rn3; lia)
        | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Ri0 Ri1 Ri2 Ri3; lia); reflexivity | rewrite !bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia); reflexivity | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rc0 Rc1 Rc2 Rc3; lia); reflexivity | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rn0 Rn1 Rn2 Rn3; lia); reflexivity].
    - if_true. step. rewrite (sx32_lit c0 c1 c2 c3) by lia. step. rewrite (sx32_lit n0 n1 n2 n3) by lia.
      step. rewrite (sx32_lit h0 h1 h2 h3) by lia. step. rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rl0 Rl1 Rl2 Rl3; lia)).
      hide BUF4. step. hide FRJ. step. step. step. step.
      rewrite (ts_word h0 h1 h2 h3 l0 l1 l2 l3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]) end.
      unhide FR5. pose proof FR5 as FR6. hide FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGP6) in FR6; [| intros a Ha; unfold F_ngnextA.ngn_frame, ccells in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia].
      lazymatch goal with HX : rw_cells ssegs ?mm HA [_; _; C4 ?cwv; C4 ?lwv] |- _ =>
        eapply (JOIN _ cwv lwv _ _ _ _ _ _ _ _ _ mm (le4val i0 i1 i2 i3) (le4val c0 c1 c2 c3) (le4val n0 n1 n2 n3) (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3)%Z);
          [exact MU | exact WM | assumption | assumption | exact HX | exact FR6 | exact HD'
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Ri0 Ri1 Ri2 Ri3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Ri0 Ri1 Ri2 Ri3; lia)
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Rc0 Rc1 Rc2 Rc3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rc0 Rc1 Rc2 Rc3; lia)
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Rn0 Rn1 Rn2 Rn3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia)
          | reflexivity | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1 Ri2 Ri3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rc0 Rc1 Rc2 Rc3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia) | reflexivity | reflexivity | reflexivity | reflexivity] end.
  Qed.
  End Sz17.
  Lemma ngn_epb : ltac:(let t := eval cbv delta [ngn_epb__stmt] in ngn_epb__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_epb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_pb_swap__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a0' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (mx : mem)
           (i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 : Z) (Bq : Z) (djw : list byte) (pre : list byte) (rest tfr : list cell) (hj1 hj2 hj3 hj4 : list byte),
      Forall (fun x => 0 <= x < 256)%Z [i0; i1; d0; d1; h0; h1; h2; h3; l0; l1; l2; l3; c0; c1; c2; c3; n0; n1; n2; n3] ->
      rw_cells ssegs mx Bq ([CB 8 pre; C2 (Z_to_bv 64 (i0 + 256 * i1)); C2 (Z_to_bv 64 (d0 + 256 * d1)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                             C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ++ rest) ->
      rw_cells ssegs mx (bv_unsigned sp + -160) ([CB 8 djw; C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 HA)] ++ tfr) ->
      rw_cells ssegs mx HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] -> mem_inv ssegs mx ->
      (HA + 24 <= Bq \/ Bq + 28 <= HA)%Z -> (bv_unsigned sp <= HA)%Z -> (HA + 24 <= 2^64)%Z ->
      evt ssegs (fun ms' => exists (a1v a2v a4v a7v lw y0 y1 y2 y3 y4 y5 y6 : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y0 y1 y2 x0 x1 a0' a1v a2v a3' a4v a5' y3 a7v
                       x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) y4 y5 y6) F (Z_to_bv 64 0x179b4) fc None m' (seg_rom ssegs)
          /\ munch [(HA, HA + 24)]%Z mx m' /\ wmono ssegs mx m' /\ mem_inv ssegs m'
          /\ rw_cells ssegs m' HA [CB 8 hj1; CB 8 hj2; C4 a2v; C4 lw]
          /\ (bv_unsigned a1v mod 2^32 = i1 + 256 * i0)%Z /\ (bv_unsigned a2v mod 2^32 = le4val c3 c2 c1 c0)%Z
          /\ (bv_unsigned lw mod 2^32 = le4val n3 n2 n1 n0)%Z /\ a7v = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' (Z_to_bv 64 (i0 + 256 * i1)) a2' a3' (Z_to_bv 64 (Bq + 8)) a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17730) fc None mx (seg_rom ssegs)).
  Section Sz18.
  Variables ra' t0' t1' t2' x0 x1 a0' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq djw pre rest tfr hj1 hj2 hj3 hj4 : ltac2:(SecDiet.SzSec.tyM 'ngn_pb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_pb_swap__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R2 SPW. pin_using (fun (BU LO P1 R2 SPW : unit) => tt).
    intros GR HB HF HH MI SEP HHA HA64.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(HA, HA + 24)]%Z mx) as MU. pose proof (wmono_refl ssegs mx) as WM.
    step. step. step. step. rewrite (zx32_lit (le4val h0 h1 h2 h3)) by (unfold le4val; lia).
    step. rewrite (sx32_lit l0 l1 l2 l3) by lia. step. rewrite (sx32_lit c0 c1 c2 c3) by lia. step. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    do 44 step. hide HB. hide HF. do 6 step.
    apply evt_done. cbv beta.
    lazymatch goal with HX : rw_cells ssegs _ HA [_; _; C4 _; C4 ?lwv] |- _ =>
      do 4 eexists; exists lwv; do 8 eexists; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply swap16_word_mod32; assumption|]. split; [apply swap32_sxv_mod32; assumption|].
    split; [apply swap32_sxv_mod32; assumption|]. apply ts_swap_word; assumption.
  Qed.
  End Sz18.
  Lemma ngn_pb_swap : ltac:(let t := eval cbv delta [ngn_pb_swap__stmt] in ngn_pb_swap__stmt in exact t).
  Proof using BU LO P1 R2 SPW. intros ra' t0' t1' t2' x0 x1 a0' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq djw pre rest tfr hj1 hj2 hj3 hj4. ltac2:(SecDiet.SzSec.closeP 'ngn_pb_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
    get_le16 data off = (q8 data off 0 + 256 * q8 data off 1)%Z.
  Proof using Type. pin_using tt.
    intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
    destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
    rewrite (get_le16_of_slice off data x0 x1 E). unfold q8. rewrite Z.add_0_r, E0, E1. reflexivity.
  Qed.
  Definition firstn2_q8__stmt : Prop := forall data (bs : list byte) (k : nat) off,
    firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
    firstn 2 (skipn k bs) = [b8 (q8 data off 0); b8 (q8 data off 1)].
  Section Sz20.
  Variables data bs k off : ltac2:(SecDiet.SzSec.tyM 'firstn2_q8__stmt "vvvv" @data).
  Lemma firstn2_q8__body : ltac2:(SecDiet.SzSec.bodyP 'firstn2_q8__stmt "vvvv").
  Proof using BU LO P1 R1 R2 SPW. pin_using (fun (BU LO P1 R1 R2 SPW : unit) => tt).
    intros PFX Hk H1.
 subst off.
    destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
    destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
    transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
    - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
    - rewrite E. unfold q8. rewrite Z.add_0_r, E0, E1. reflexivity.
  Qed.
  End Sz20.
  Lemma firstn2_q8 : ltac:(let t := eval cbv delta [firstn2_q8__stmt] in firstn2_q8__stmt in exact t).
  Proof using BU LO P1 R1 R2 SPW. intros data bs k off. ltac2:(SecDiet.SzSec.closeP 'firstn2_q8__body "vvvv"). Qed.
  Lemma bswap16_2 : forall a b, (0 <= a < 256 -> 0 <= b < 256 -> bswap16 (a + 256 * b) = b + 256 * a)%Z.
  Proof using DA HA P sp. pin_using (fun (DA HA P sp : unit) => tt). intros. rewrite <- (le_of_bytes_2 a b), bswap16_bytes, le_of_bytes_2 by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngn_pb__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (20 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK
                     (let sw32 (v : Z) := if swapped then bswap32 v else v in
                      let sw16 (v : Z) := if swapped then bswap16 v else v in
                      mkFound (sw16 (get_le16 data 8)) (sw32 (get_le32 data 12) * 2^32 + sw32 (get_le32 data 16)) (sw32 (get_le32 data 20)) (sw32 (get_le32 data 24))
                              (mkCursor (8 + 20) (rem - 20) bt))
                     (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17714) fc None m5 (seg_rom ssegs)).
  Section Sz22.
  Variables ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_pb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_pb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold F_ngnextA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnextA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    set (i0 := q8 data 8 0) in *. set (i1 := q8 data 8 1) in *. set (d0 := q8 data 10 0) in *. set (d1 := q8 data 10 1) in *.
    pose proof (q8_range data 8 0 DRNG ltac:(lia)) as Ri0. pose proof (q8_range data 8 1 DRNG ltac:(lia)) as Ri1.
    pose proof (q8_range data 10 0 DRNG ltac:(lia)) as Rd0. pose proof (q8_range data 10 1 DRNG ltac:(lia)) as Rd1.
    fold i0 in Ri0. fold i1 in Ri1. fold d0 in Rd0. fold d1 in Rd1.
    name_field data 12%Z h0 h1 h2 h3 DRNG. name_field data 16%Z l0 l1 l2 l3 DRNG.
    name_field data 20%Z c0 c1 c2 c3 DRNG. name_field data 24%Z n0 n1 n2 n3 DRNG.
    cbv zeta.
    rewrite (get_le16_q8' data 8), (get_le32_q8 data 12), (get_le32_q8 data 16), (get_le32_q8 data 20), (get_le32_q8 data 24) by (keep_hyps CEILV sp R P HA DA Bq data hcs dw lo rem LEN REM; lia).
    fold i0 i1 h0 h1 h2 h3 l0 l1 l2 l3. fold c0 c1 c2 c3 n0 n1 n2 n3.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; 4; 4; 4; Z.to_nat alloc - 28]%nat) in BUF; [| cbn; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4; lia)]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (firstn2_q8 data bsx' 8 8%Z PFX eq_refl), (firstn2_q8 data bsx' 10 10%Z PFX eq_refl), (firstn4_q8 data bsx' 12 12%Z PFX eq_refl), (firstn4_q8 data bsx' 16 16%Z PFX eq_refl),
            (firstn4_q8 data bsx' 20 20%Z PFX eq_refl), (firstn4_q8 data bsx' 24 24%Z PFX eq_refl) in BUF by (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM; lia).
    fold i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 in BUF. fold c0 c1 c2 c3 n0 n1 n2 n3 in BUF.
    assert (BUF4 : rw_cells ssegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (i0 + 256 * i1)); C2 (Z_to_bv 64 (d0 + 256 * d1)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                                       C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 28) (firstn (Z.to_nat alloc - 28) (skipn 28 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4 LBS; lia). }
      cbn [cells_bytes cbytes app]. rewrite (le2_lit i0 i1), (le2_lit d0 d1), (le4_lit h0 h1 h2 h3), (le4_lit l0 l1 l2 l3), (le4_lit c0 c1 c2 c3), (le4_lit n0 n1 n2 n3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' Ri0 Ri1 Rd0 Rd1 Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3 Rc0 Rc1 Rc2 Rc3 Rn0 Rn1 Rn2 Rn3; lia). reflexivity. }
    clear BUF.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
    assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
    apply (rw_cells_split_CB ssegs m5 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. step. if_cases BR0; zify_cond BR0. { exfalso. rewrite ?unsigned_lit in BR0 by lia. clear -BR0 K1 K3 K4. lia. }
    step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. rewrite (zx16_lit (i0 + 256 * i1)) by lia.
    step. step. step.
    (* [comment removed for export] *)
    assert (JOIN : forall (iw cw lw a4v a7v y0 y1 y2 y3 y4 y5 y6 : word) (m6 : mem) (idv capv lenv tv : Z),
      munch [(HA, HA + 24)]%Z m5 m6 -> wmono ssegs m5 m6 -> mem_inv ssegs m6 -> stk ssegs m6 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 cw; C4 lw] ->
      rw_cells ssegs m6 (bv_unsigned sp + -160) (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj (ccells Bq rem bt cpad)) ->
      rw_cells ssegs m6 DA [CB 8 dwj] ->
      (bv_unsigned iw mod 2^32 = idv)%Z -> (bv_unsigned cw mod 2^32 = capv)%Z -> (bv_unsigned lw mod 2^32 = lenv)%Z ->
      a7v = Z_to_bv 64 tv -> (0 <= tv < 2^64)%Z -> (0 <= idv < 2^32)%Z -> (0 <= capv < 2^32)%Z -> (0 <= lenv < 2^32)%Z ->
      idv = (if swapped then bswap16 (i0 + 256 * i1) else i0 + 256 * i1)%Z ->
      tv = ((if swapped then bswap32 (le4val h0 h1 h2 h3) else le4val h0 h1 h2 h3) * 2^32 + (if swapped then bswap32 (le4val l0 l1 l2 l3) else le4val l0 l1 l2 l3))%Z ->
      capv = (if swapped then bswap32 (le4val c0 c1 c2 c3) else le4val c0 c1 c2 c3) ->
      lenv = (if swapped then bswap32 (le4val n0 n1 n2 n3) else le4val n0 n1 n2 n3) ->
      evt ssegs (fun ms' => impl ssegs (at_node ssegs) (npeek ssegs)
        (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK
           (mkFound (if swapped then bswap16 (i0 + 256 * i1) else i0 + 256 * i1)%Z
                    ((if swapped then bswap32 (le4val h0 h1 h2 h3) else le4val h0 h1 h2 h3) * 2 ^ 32 + (if swapped then bswap32 (le4val l0 l1 l2 l3) else le4val l0 l1 l2 l3))
                    (if swapped then bswap32 (le4val c0 c1 c2 c3) else le4val c0 c1 c2 c3)
                    (if swapped then bswap32 (le4val n0 n1 n2 n3) else le4val n0 n1 n2 n3)
                    (mkCursor 28 (rem - 20) bt)) (pv bq alloc data eb sx ix) ps)
        (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y0 y1 y2 (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (rem + -20)) iw cw (Z_to_bv 64 (s32 bt)) a4v (Z_to_bv 64 (Bq + 28)) y3 a7v
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) y4 y5 y6) F (Z_to_bv 64 0x179b4) fc None m6 (seg_rom ssegs))).
    { intros iw cw lw a4v a7v y0 y1 y2 y3 y4 y5 y6 m6 idv capv lenv tv MU6 WM6 MI6 ST6 HH6 FR6 HD6 Hiw Hcw Hlw -> Htv Hid Hcap Hlen Eid Etv Ecap Elen.
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      unhide FR5. unhide PRIV. unhide IFS. clear FR5.
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LO BU R1 R2 R3; lia). }
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header ps bq Bq Ix alloc data eb sx ix hcs dw bsx' hj iw cw lw m6 a LO BU R1 G6 H0; lia). }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj iw cw lw a Hna; lia). }
      assert (HH7 : rw_cells ssegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 capv); C4 (Z_to_bv 64 lenv)]).
      { eapply rw_cells_recell; [exact HH6 | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LHJ; lia) |].
        cbn [cells_bytes cbytes app]. rewrite (le4_word_mod32 cw capv Hcw), (le4_word_mod32 lw lenv Hlw). reflexivity. }
      apply evt_done. rewrite <- Eid, <- Etv, <- Ecap, <- Elen.
      replace (Z_to_bv 64 (rem + -20)) with (Z_to_bv 64 (rem - 20)) by (f_equal; lia).
      eapply (ngn_found _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iw cw _ _ m6 ps bq Bq Ix alloc 28 (rem - 20) data eb sx ix idv tv capv lenv bt);
        [exact ST6 | exact FR6 | reflexivity | exact MI6 | exact G6 | exact PC6 | exact AG6 | exact HH7 | exact HD6 | reflexivity
        | exact Hiw | exact Hcw | exact Htv | exact DRNG | (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj iw cw lw; lia) | reflexivity | (keep_hyps CEILV sp R P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw REM; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LEN; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LEN L30; lia) | exact Hlen | exact Hbt | exact OF5]. }
    destruct swapped.
    - (* [comment removed for export] *)
      if_false.
      eapply evt_cut.
      { eapply (ngn_pb_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq dj);
          [repeat (apply Forall_cons; [(keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Ri0 Ri1 Rd0 Rd1 Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3 Rc0 Rc1 Rc2 Rc3 Rn0 Rn1 Rn2 Rn3; lia)|]); apply Forall_nil | exact BUF4 | exact FRJ | exact HHj | assumption | gio_ceil_fact; clear -CLO__ K1 K4 R1 LO BU SPM SPW W4 LEN REM; unfold rc_lo, rc_spmain in *; (keep_hyps CEILV sp R lo HA Bq alloc rem data LO BU R1 K4 W4 CLO__; lia) | exact R1 | clear -R1 R2 R3 SP47 SPM; unfold rc_spmain in *; (keep_hyps R HA DA R2 R3 SP47; lia)]. }
      cbv beta. intros ms' (a1v & a2v & a4v & a7v & lw & y0 & y1 & y2 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & HH6 & Hi & Hc & Hl & Ht).
      assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      pose proof (agrees_stk _ _ _ _ _ AGP6 ST5 ltac:(intros a Ha; cbn [outside]; (keep_hyps CEILV sp R lo P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw a R1 Ha; lia))) as ST6.
      unhide FR5. pose proof FR5 as FR6. hide FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGP6) in FR6; [| intros a Ha; unfold F_ngnextA.ngn_frame, ccells in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia].
      pose proof HD' as HD6. apply (agrees_rw_cells _ _ _ _ _ AGP6) in HD6; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R2; lia].
      eapply (JOIN a1v a2v lw a4v a7v y0 y1 y2 y3 y4 y5 y6 m6 (i1 + 256 * i0)%Z (le4val c3 c2 c1 c0) (le4val n3 n2 n1 n0) (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z);
        [exact MU6 | exact WM6 | exact MI6 | exact ST6 | exact HH6 | exact FR6 | exact HD6 | exact Hi | exact Hc | exact Hl | exact Ht
        | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Hi; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rc0 Rc1 Rc2 Rc3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rn0 Rn1 Rn2 Rn3; lia)
        | rewrite bswap16_2 by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Ri0 Ri1; lia); reflexivity | rewrite !bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia); reflexivity | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rc0 Rc1 Rc2 Rc3; lia); reflexivity | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rn0 Rn1 Rn2 Rn3; lia); reflexivity].
    - if_true. step. rewrite (sx32_lit c0 c1 c2 c3) by lia. step. rewrite (sx32_lit n0 n1 n2 n3) by lia.
      step. rewrite (sx32_lit h0 h1 h2 h3) by lia. step. rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
      hide BUF4. step. hide FRJ. step. step. step. step.
      rewrite (ts_word h0 h1 h2 h3 l0 l1 l2 l3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]) end.
      unhide FR5. pose proof FR5 as FR6. hide FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGP6) in FR6; [| intros a Ha; unfold F_ngnextA.ngn_frame, ccells in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia].
      lazymatch goal with HX : rw_cells ssegs ?mm HA [_; _; C4 ?cwv; C4 ?lwv] |- _ =>
        eapply (JOIN _ cwv lwv _ _ _ _ _ _ _ _ _ mm (i0 + 256 * i1)%Z (le4val c0 c1 c2 c3) (le4val n0 n1 n2 n3) (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3)%Z);
          [exact MU | exact WM | assumption | assumption | exact HX | exact FR6 | exact HD'
          | rewrite unsigned_lit by (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1; lia); apply Z.mod_small; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1; lia)
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Rc0 Rc1 Rc2 Rc3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rc0 Rc1 Rc2 Rc3; lia)
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Rn0 Rn1 Rn2 Rn3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia)
          | reflexivity | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rc0 Rc1 Rc2 Rc3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia) | reflexivity | reflexivity | reflexivity | reflexivity] end.
  Qed.
  End Sz22.
  Lemma ngn_pb : ltac:(let t := eval cbv delta [ngn_pb__stmt] in ngn_pb__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_pb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End NgnCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require NgnPure.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.NgnPure.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
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
Section WithCeil.
Context {CEILV : CEIL}.
Lemma geu_lits_false : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
Proof using Type. pin_using tt. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
Lemma ltu_lits_false : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof using Type. pin_using tt. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
(* [comment removed for export] *)
Lemma geu_neg_false : forall x k, (0 < k < 2^64)%Z -> (0 <= x < 2^64 - k)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 (- k))) = false.
Proof using Type. pin_using tt.
  intros x k Hk Hx. rewrite (zbv64_eq (- k) (2^64 - k)) by (Z.div_mod_to_equations; lia).
  apply geu_lits_false; lia.
Qed.

Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.
  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_ngnextA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (S3.F_ngnextA.TwB.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (S3.F_ngnextA.TwB.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (S3.F_ngnextA.TwB.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (S3.F_ngnextA.TwB.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (S3.F_ngnextA.TwB.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (S3.F_ngnextA.TwB.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (S3.F_ngnextA.TwB.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (S3.F_ngnextA.TwB.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (S3.F_ngnextA.TwB.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (S3.F_ngnextA.TwB.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (S3.F_ngnextA.TwB.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold S3.F_ngnextA.TwB.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold S3.F_ngnextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_ts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB.ngn_ts K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  (* [comment removed for export] *)
  Definition ccells (Bq rem bt : Z) (cpad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (Bq + 8)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad].

  (* [comment removed for export] *)
  Definition ngn_spb__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (4 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK
                     (let len := (if swapped then bswap32 (get_le32 data 8) else get_le32 data 8) in
                      mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor (8 + 4) (rem - 4) bt))
                     (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17fb8) fc None m5 (seg_rom usegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_spb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_spb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_spb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
 (* [comment removed for export] *)
 try change (8 + 4)%Z with 12%Z.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold S3.F_ngnextA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, S3.F_ngnextA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    set (g0 := q8 data 8 0). set (g1 := q8 data 8 1). set (g2 := q8 data 8 2). set (g3 := q8 data 8 3).
    pose proof (q8_range data 8 0 DRNG ltac:(lia)) as R0. pose proof (q8_range data 8 1 DRNG ltac:(lia)) as R1'.
    pose proof (q8_range data 8 2 DRNG ltac:(lia)) as R2'. pose proof (q8_range data 8 3 DRNG ltac:(lia)) as R3'.
    fold g0 in R0. fold g1 in R1'. fold g2 in R2'. fold g3 in R3'.
    rewrite (get_le32_q8 data 8) by lia. fold g0 g1 g2 g3.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; Z.to_nat alloc - 12]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite (firstn4_q8 data bsx' 8 8 PFX eq_refl) in BUF by lia. fold g0 g1 g2 g3 in BUF.
    assert (BUF4 : rw_cells usegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); CB (Z.to_nat alloc - 12) (firstn (Z.to_nat alloc - 12) (skipn 4 (skipn 8 bsx')))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4 LBS; lia). }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit g0 g1 g2 g3) by lia. reflexivity. }
    clear BUF.
    (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
    assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
    apply (rw_cells_split_CB usegs m5 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, ccells in FRJ. cbn [app] in FRJ. clear FR5.
    hide PRIV. hide IFS.
    pose proof (munch_refl [(HA, HA + 24); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. step. step. if_false_by (geu_lits_false 4 (Bq + 12) ltac:(clear -K1; lia) ltac:(clear -K1 K4 W4 LEN REM; lia)).
    (* [comment removed for export] *)
    step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. pstep. step.
    step. rewrite (and3_aligned (Bq + 8)) by (clear -K1 K2 K3 K4; try lia; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    unhide PRIV. unhide IFS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(HA, HA + 24); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (G5' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB mm)
        by (eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - R1 R2 R3 LO BU SPM; lia|];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - LO BU SPM; lia| apply Forall_nil]);
      rename mm into m5' end.
    assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5').
    { eapply PCAPR_agree; [exact AGD| | exact PC5]. intros a Ha. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). gio_ceil_fact; clear -CLO__ H0 R1 LO BU SPW. lia. }
    assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [Hc [Hn _]]; cbn [outside]. split; [clear - Hn; lia|]. split; [| exact Logic.I].
      destruct Hc as [Hc|Hc]; [clear - Hc; lia|]. destruct (ngn_CLc_facts _ _ _ _ G5 Hc) as [Hx _]. gio_ceil_fact; clear -CLO__ Hx LO BU SPW. lia. }
    assert (MI5' : mem_inv usegs m5') by assumption. assert (ST5' : stk usegs m5' lo (bv_unsigned sp + -160)) by assumption.
    clear MU WM AGD G5 G5e AG5 PC5 MI5 ST5.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5') as MU. pose proof (wmono_refl usegs m5') as WM.
    
    clear PRIV IFS.
    (* [comment removed for export] *)
    assert (KX : forall (a1v a4v a6v lw : word) (len : Z), (0 <= len < 2^32)%Z -> (bv_unsigned lw mod 2^32 = len)%Z ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (npeek usegs)
        (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK (mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor (8 + 4) (rem - 4) bt)) (pv bq alloc data eb sx ix) ps)
        (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (rem + -4)) a1v lw (Z_to_bv 64 (s32 bt)) a4v (Z_to_bv 64 (Bq + 12)) a6v a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x180b4) fc None m5' (seg_rom usegs))).
    { intros a1v a4v a6v lw len Hlen Hlw. pose proof (sxu_range' len Hlen) as SR. pose proof (sxu_range len Hlen) as (_ & SX2 & SX3).
      hide BUF4.
      step. rewrite (sx32_small snapshot) by lia. step. step. step. step.
      assert (KJ : forall (cap : Z) (cw : word) (m6 : mem), (bv_unsigned cw mod 2^32 = cap)%Z -> cap = (if snapshot <? len then snapshot else len) ->
        munch [(HA, HA + 24)]%Z m5' m6 -> wmono usegs m5' m6 -> mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -160) ->
        rw_cells usegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 lw; C4 lw] ->
        rw_cells usegs m6 (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 12)); C8 (Z_to_bv 64 (rem + -4)); C4 (Z_to_bv 64 bt); CB 4 cpad]) ->
        rw_cells usegs m6 DA [CB 8 dwj] ->
        evt usegs (fun ms' => impl usegs (at_node usegs) (npeek usegs)
          (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK (mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor (8 + 4) (rem - 4) bt)) (pv bq alloc data eb sx ix) ps)
          (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                   (Z_to_bv 64 (rem + -4)) cw lw (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 snapshot) (Z_to_bv 64 (Bq + 12)) (Z_to_bv 64 HA) a7'
                   x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x180d0) fc None m6 (seg_rom usegs))).
      { intros cap cw m6 Hcw Ecap MU6 WM6 MI6 ST6 HH6 FR6 HD6. try change (8 + 4)%Z with 12%Z.
        assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite Ecap; destruct (snapshot <? len); lia).
        assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        unhide BUF4. clear HD'.
        assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G5' | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' lw hj cw LO BU R1 R2 R3; lia). }
        assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
        { eapply PCAPR_agree; [exact AGP6 | | exact PC5']. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5' Ha). cbn [outside]. unfold rc_lo in LO. lia. }
        assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGP6|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
        clear MU WM. pose proof (munch_refl [(HA, HA + 24)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
        pose proof FR6 as FRJ'. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ'. cbn [app] in FRJ'. clear FRJ.
        (* [comment removed for export] *)
        hide FR6. hide HD6. step. step. step. step. unhide FR6. unhide HD6.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD6; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R2; lia].
        assert (G7 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' lw hj cw LO BU R1 R2 R3; lia). }
        assert (PC7 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7).
        { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G6 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
        assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
        lazymatch goal with HHx : rw_cells usegs m7 HA ?cs |- _ =>
          assert (HH7 : rw_cells usegs m7 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
            by (eapply rw_cells_recell; [exact HHx | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' lw hj cw LHJ; lia)
                                         | cbn [cells_bytes cbytes app]; rewrite (le4_word_mod32 cw cap Hcw), (le4_word_mod32 lw len Hlw); reflexivity]);
          clear HHx end.
        lazymatch goal with FRx : rw_cells usegs m7 (bv_unsigned sp + -160) _ |- _ => rename FRx into FR7 end.
        apply evt_done. rewrite <- Ecap.
        replace (Z_to_bv 64 (rem + -4)) with (Z_to_bv 64 (rem - 4)) by (f_equal; lia).
        (* [comment removed for export] *)
        eapply (ngn_found _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) cw _ _ m7 ps bq Bq Ix alloc 12 (rem - 4) data eb sx ix 0 0 cap len bt _ dj);
          [assumption | exact FR7 | assumption | exact G7 | exact PC7 | exact AG7 | exact HH7 | exact HD6 | reflexivity
          | rewrite unsigned_lit by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' lw hj cw; lia); reflexivity | exact Hcw | (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' lw hj cw; lia) | exact DRNG | (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' lw hj cw; lia) | reflexivity | (keep_hyps CEILV sp R P HA DA Bq alloc rem data hcs dw bsx' lw hj cw REM; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' lw hj cw LEN; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' lw hj cw LEN L30; lia) | | exact Hbt | exact OF5].
        destruct (Z.ltb_spec snapshot len); lia. }
      step. if_cases BR; zify_cond BR; rewrite sextw_mod, Hlw, ?unsigned_lit in BR by lia.
      - (* [comment removed for export] *)
        assert (LT : (len < snapshot)%Z) by (destruct (Z_lt_dec len (2^31)); [rewrite SX2 in BR by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' lw hj len l; lia); (keep_hyps CEILV sp R P HA DA snapshot Bq alloc data hcs dw bsx' lw hj len BR; lia)| specialize (SX3 ltac:((keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' lw hj len n; lia))); (keep_hyps CEILV sp R P HA DA snapshot Bq alloc data hcs dw bsx' lw hj len W1' SX3 BR; lia)]).
        eapply (KJ len); [rewrite unsigned_sextw, Hlw; apply sxu_mod32; lia | replace (snapshot <? len) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
                         | exact MU | exact WM | assumption | assumption | assumption | assumption | exact HD'].
      - step.
        eapply (KJ snapshot); [rewrite unsigned_lit by lia; apply Z.mod_small; lia | | exact MU | exact WM | assumption | assumption | assumption | assumption | exact HD'].
        destruct (Z_lt_dec len (2^31)); [rewrite SX2 in BR by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' lw hj len l; lia)| specialize (SX3 ltac:((keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' lw hj len n; lia)))]; destruct (Z.ltb_spec snapshot len); (keep_hyps CEILV sp R P HA DA snapshot Bq alloc data hcs dw bsx' lw hj len BR H0 lo rem W1' n; lia). }
    
    step. destruct swapped.
    - (* [comment removed for export] *)
      if_false. step. if_false.
      step. step. if_false_by (eqz_false HA ltac:(gio_ceil_fact; clear -CLO__ R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia)).
      step. step. rewrite (and7_aligned HA) by (gio_ceil_fact; clear -CLO__ AH R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
      step. rewrite (sx32_lit g0 g1 g2 g3) by lia.
      do 12 step.
      rewrite (bswap32_le4val g0 g1 g2 g3) by lia.
      eapply (KX _ _ _ _ (le4val g3 g2 g1 g0)); [unfold le4val; lia | apply swap32_sxv_mod32; assumption].
    - if_true. step. if_false.
      step. step. if_false_by (eqz_false HA ltac:(gio_ceil_fact; clear -CLO__ R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia)).
      step. step. rewrite (and7_aligned HA) by (gio_ceil_fact; clear -CLO__ AH R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
      step. rewrite (sx32_lit g0 g1 g2 g3) by lia.
      eapply (KX _ _ _ _ (le4val g0 g1 g2 g3)); [unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj R0 R1' R2' R3'; lia) | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 R0 R1' R2' R3' H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj R0 R1' R2' R3'; lia)].
  Qed.
  End Sz4.
  Lemma ngn_spb : ltac:(let t := eval cbv delta [ngn_spb__stmt] in ngn_spb__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_spb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Ltac name_field data off a b c d DRNG :=
    set (a := q8 data off 0%Z) in *; set (b := q8 data off 1%Z) in *; set (c := q8 data off 2%Z) in *; set (d := q8 data off 3%Z) in *;
    let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
    pose proof (q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
    pose proof (q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
    fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

  (* [comment removed for export] *)
  Definition ngn_epb_swap__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (mx : mem)
           (i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 : Z) (Bq : Z) (pre : list byte) (rest tfr : list cell) (hj1 hj2 hj3 hj4 : list byte) (fw0 fw1 : word),
      Forall (fun x => 0 <= x < 256)%Z [i0; i1; i2; i3; h0; h1; h2; h3; l0; l1; l2; l3; c0; c1; c2; c3; n0; n1; n2; n3] ->
      rw_cells usegs mx Bq ([CB 8 pre; C4 (Z_to_bv 64 (le4val i0 i1 i2 i3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                             C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ++ rest) ->
      rw_cells usegs mx (bv_unsigned sp + -160) ([C8 fw0; C8 fw1; C8 (Z_to_bv 64 HA)] ++ tfr) ->
      rw_cells usegs mx HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] -> mem_inv usegs mx ->
      (HA + 24 <= Bq \/ Bq + 28 <= HA)%Z -> (bv_unsigned sp <= HA)%Z -> (HA + 24 <= 2^64)%Z ->
      evt usegs (fun ms' => exists (a1v a2v a4v a6v a7v lw y0 y1 y2 y3 y4 y5 y6 y7 : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y0 y1 y2 x0 x1 a0' a1v a2v a3' a4v a5' a6v a7v
                       y7 x3 x4 x5 x6 x7 x8 x9 x10 x11 y3 y4 y5 y6) F (Z_to_bv 64 0x180e0) fc None m' (seg_rom usegs)
          /\ munch [(HA, HA + 24)]%Z mx m' /\ wmono usegs mx m' /\ mem_inv usegs m'
          /\ rw_cells usegs m' HA [CB 8 hj1; CB 8 hj2; C4 a1v; C4 lw]
          /\ (bv_unsigned a2v mod 2^32 = le4val i3 i2 i1 i0)%Z /\ (bv_unsigned a1v mod 2^32 = le4val c3 c2 c1 c0)%Z
          /\ (bv_unsigned lw mod 2^32 = le4val n3 n2 n1 n0)%Z /\ a7v = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' (Z_to_bv 64 (Bq + 8)) a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17ec0) fc None mx (seg_rom usegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq pre rest tfr hj1 hj2 hj3 hj4 fw0 fw1 : ltac2:(SecDiet.SzSec.tyM 'ngn_epb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_epb_swap__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R2 SPW. pin_using (fun (BU LO P1 R2 SPW : unit) => tt).
 intros GR HB HF HH MI SEP HHA HA64.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(HA, HA + 24)]%Z mx) as MU. pose proof (wmono_refl usegs mx) as WM.
    step. rewrite (sx32_lit i0 i1 i2 i3) by lia. step. rewrite (zx32_lit (le4val h0 h1 h2 h3)) by (unfold le4val; lia).
    step. rewrite (sx32_lit l0 l1 l2 l3) by lia. step. rewrite (sx32_lit c0 c1 c2 c3) by lia. step. step. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    do 47 step. do 2 step. hide HB. do 7 step. unhide HB.
    apply evt_done. cbv beta.
    lazymatch goal with HX : rw_cells usegs _ HA [_; _; C4 _; C4 ?lwv] |- _ =>
      do 5 eexists; exists lwv; do 9 eexists; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply swap32_sxv_mod32; assumption|]. split; [apply swap32_sxv_mod32; assumption|].
    split; [apply swap32_sxv_mod32; assumption|]. apply ts_swap_word; assumption.
  Qed.
  End Sz5.
  Lemma ngn_epb_swap : ltac:(let t := eval cbv delta [ngn_epb_swap__stmt] in ngn_epb_swap__stmt in exact t).
  Proof using BU LO P1 R2 SPW. intros ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq pre rest tfr hj1 hj2 hj3 hj4 fw0 fw1. ltac2:(SecDiet.SzSec.closeP 'ngn_epb_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_epb__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (20 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK
                     (let sw32 (v : Z) := if swapped then bswap32 v else v in
                      mkFound (sw32 (get_le32 data 8)) (sw32 (get_le32 data 12) * 2^32 + sw32 (get_le32 data 16)) (sw32 (get_le32 data 20)) (sw32 (get_le32 data 24))
                              (mkCursor (8 + 20) (rem - 20) bt))
                     (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17e7c) fc None m5 (seg_rom usegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_epb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_epb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold S3.F_ngnextA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, S3.F_ngnextA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    name_field data 8%Z i0 i1 i2 i3 DRNG. name_field data 12%Z h0 h1 h2 h3 DRNG. name_field data 16%Z l0 l1 l2 l3 DRNG.
    name_field data 20%Z c0 c1 c2 c3 DRNG. name_field data 24%Z n0 n1 n2 n3 DRNG.
    cbv zeta.
    rewrite (get_le32_q8 data 8), (get_le32_q8 data 12), (get_le32_q8 data 16), (get_le32_q8 data 20), (get_le32_q8 data 24) by (keep_hyps CEILV sp R P HA DA Bq data hcs dw lo rem LEN REM; lia).
    fold i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3. fold c0 c1 c2 c3 n0 n1 n2 n3.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 4; 4; 4; 4; Z.to_nat alloc - 28]%nat) in BUF; [| cbn; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4; lia)]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (firstn4_q8 data bsx' 8 8%Z PFX eq_refl), (firstn4_q8 data bsx' 12 12%Z PFX eq_refl), (firstn4_q8 data bsx' 16 16%Z PFX eq_refl),
            (firstn4_q8 data bsx' 20 20%Z PFX eq_refl), (firstn4_q8 data bsx' 24 24%Z PFX eq_refl) in BUF by (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM; lia).
    fold i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 in BUF. fold c0 c1 c2 c3 n0 n1 n2 n3 in BUF.
    assert (BUF4 : rw_cells usegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val i0 i1 i2 i3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                                       C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 28) (firstn (Z.to_nat alloc - 28) (skipn 28 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4 LBS; lia). }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit i0 i1 i2 i3), (le4_lit h0 h1 h2 h3), (le4_lit l0 l1 l2 l3), (le4_lit c0 c1 c2 c3), (le4_lit n0 n1 n2 n3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' Ri0 Ri1 Ri2 Ri3 Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3 Rc0 Rc1 Rc2 Rc3 Rn0 Rn1 Rn2 Rn3; lia). reflexivity. }
    clear BUF.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
    assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
    apply (rw_cells_split_CB usegs m5 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, ccells in FRJ. cbn [app] in FRJ. clear FR5.
    hide PRIV. hide IFS.
    pose proof (munch_refl [(HA, HA + 24); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. if_false_by (eqz_false (Bq + 8) ltac:(clear -K1 K3 K4; lia)).
    step. step. if_false_by (geu_neg_false (Bq + 8) 20 ltac:(lia) ltac:(clear -K1 K3 K4 W4 LEN REM; lia)).
    (* [comment removed for export] *)
    step. step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. pstep. step.
    step. rewrite (and3_aligned (Bq + 8)) by (clear -K1 K2 K3 K4; try lia; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    unhide PRIV. unhide IFS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(HA, HA + 24); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (G5' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB mm)
        by (eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - R1 R2 R3 LO BU SPM; lia|];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - LO BU SPM; lia| apply Forall_nil]);
      rename mm into m5' end.
    assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5').
    { eapply PCAPR_agree; [exact AGD| | exact PC5]. intros a Ha. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). gio_ceil_fact; clear -CLO__ H0 R1 LO BU SPW. lia. }
    assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [Hc [Hn _]]; cbn [outside]. split; [clear - Hn; lia|]. split; [| exact Logic.I].
      destruct Hc as [Hc|Hc]; [clear - Hc; lia|]. destruct (ngn_CLc_facts _ _ _ _ G5 Hc) as [Hx _]. gio_ceil_fact; clear -CLO__ Hx LO BU SPW. lia. }
    assert (MI5' : mem_inv usegs m5') by assumption. assert (ST5' : stk usegs m5' lo (bv_unsigned sp + -160)) by assumption.
    clear MU WM AGD G5 G5e AG5 PC5 MI5 ST5 PRIV IFS.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5') as MU. pose proof (wmono_refl usegs m5') as WM.
    (* [comment removed for export] *)
    assert (JOIN : forall (iw cw lw a4v a6v a7v y0 y1 y2 y3 y4 y5 y6 y7 : word) (m6 : mem) (idv capv lenv tv : Z),
      munch [(HA, HA + 24)]%Z m5' m6 -> wmono usegs m5' m6 -> mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 cw; C4 lw] ->
      rw_cells usegs m6 (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad]) ->
      rw_cells usegs m6 DA [CB 8 dwj] ->
      (bv_unsigned iw mod 2^32 = idv)%Z -> (bv_unsigned cw mod 2^32 = capv)%Z -> (bv_unsigned lw mod 2^32 = lenv)%Z ->
      a7v = Z_to_bv 64 tv -> (0 <= tv < 2^64)%Z -> (0 <= idv < 2^32)%Z -> (0 <= capv < 2^32)%Z -> (0 <= lenv < 2^32)%Z ->
      idv = (if swapped then bswap32 (le4val i0 i1 i2 i3) else le4val i0 i1 i2 i3) ->
      tv = ((if swapped then bswap32 (le4val h0 h1 h2 h3) else le4val h0 h1 h2 h3) * 2^32 + (if swapped then bswap32 (le4val l0 l1 l2 l3) else le4val l0 l1 l2 l3))%Z ->
      capv = (if swapped then bswap32 (le4val c0 c1 c2 c3) else le4val c0 c1 c2 c3) ->
      lenv = (if swapped then bswap32 (le4val n0 n1 n2 n3) else le4val n0 n1 n2 n3) ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (npeek usegs)
        (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK
           (mkFound (if swapped then bswap32 (le4val i0 i1 i2 i3) else le4val i0 i1 i2 i3)
                    ((if swapped then bswap32 (le4val h0 h1 h2 h3) else le4val h0 h1 h2 h3) * 2 ^ 32 + (if swapped then bswap32 (le4val l0 l1 l2 l3) else le4val l0 l1 l2 l3))
                    (if swapped then bswap32 (le4val c0 c1 c2 c3) else le4val c0 c1 c2 c3)
                    (if swapped then bswap32 (le4val n0 n1 n2 n3) else le4val n0 n1 n2 n3)
                    (mkCursor 28 (rem - 20) bt)) (pv bq alloc data eb sx ix) ps)
        (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y0 y1 y2 (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (rem + -20)) cw iw (Z_to_bv 64 (s32 bt)) a4v (Z_to_bv 64 (Bq + 28)) a6v a7v
                 y7 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 y3 y4 y5 y6) F (Z_to_bv 64 0x180e0) fc None m6 (seg_rom usegs))).
    { intros iw cw lw a4v a6v a7v y0 y1 y2 y3 y4 y5 y6 y7 m6 idv capv lenv tv MU6 WM6 MI6 ST6 HH6 FR6 HD6 Hiw Hcw Hlw -> Htv Hid Hcap Hlen Eid Etv Ecap Elen.
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5' | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LO BU R1 R2 R3; lia). }
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGP | | exact PC5']. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5' Ha). cbn [outside]. unfold rc_lo in LO. (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header ps bq Bq Ix alloc data eb sx ix hcs dw bsx' hj iw cw lw m6 a LO BU R1 G6 H0; lia). }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj iw cw lw a Hna; lia). }
      assert (HH7 : rw_cells usegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 capv); C4 (Z_to_bv 64 lenv)]).
      { eapply rw_cells_recell; [exact HH6 | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LHJ; lia) |].
        cbn [cells_bytes cbytes app]. rewrite (le4_word_mod32 cw capv Hcw), (le4_word_mod32 lw lenv Hlw). reflexivity. }
      apply evt_done. rewrite <- Eid, <- Etv, <- Ecap, <- Elen.
      replace (Z_to_bv 64 (rem + -20)) with (Z_to_bv 64 (rem - 20)) by (f_equal; lia).
      eapply (ngn_found _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iw cw _ _ m6 ps bq Bq Ix alloc 28 (rem - 20) data eb sx ix idv tv capv lenv bt _ dj);
        [exact ST6 | exact FR6 | exact MI6 | exact G6 | exact PC6 | exact AG6 | exact HH7 | exact HD6 | reflexivity
        | exact Hiw | exact Hcw | exact Htv | exact DRNG | (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj iw cw lw; lia) | reflexivity | (keep_hyps CEILV sp R P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw REM; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LEN; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LEN L30; lia) | exact Hlen | exact Hbt | exact OF5]. }
    step. destruct swapped.
    - (* [comment removed for export] *)
      if_false. step. if_false.
      step. step. if_false_by (eqz_false HA ltac:(gio_ceil_fact; clear -CLO__ R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia)).
      step. step. rewrite (and7_aligned HA) by (gio_ceil_fact; clear -CLO__ AH R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
      eapply evt_cut.
      { eapply (ngn_epb_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq);
          [repeat (apply Forall_cons; [(keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Ri0 Ri1 Ri2 Ri3 Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3 Rc0 Rc1 Rc2 Rc3 Rn0 Rn1 Rn2 Rn3; lia)|]); apply Forall_nil | exact BUF4 | exact FRJ | exact HHj | assumption | gio_ceil_fact; clear -CLO__ K1 K4 R1 LO BU SPM SPW W4 LEN REM; unfold rc_lo, rc_spmain in *; (keep_hyps CEILV sp R lo HA Bq alloc rem data LO BU R1 K4 W4 CLO__; lia) | exact R1 | clear -R1 R2 R3 SP47 SPM; unfold rc_spmain in *; (keep_hyps R HA DA R2 R3 SP47; lia)]. }
      cbv beta. intros ms' (a1v & a2v & a4v & a6v & a7v & lw & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & m6 & -> & MU6 & WM6 & MI6 & HH6 & Hi & Hc & Hl & Ht).
      assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      pose proof (agrees_stk _ _ _ _ _ AGP6 ST5' ltac:(intros a Ha; cbn [outside]; (keep_hyps CEILV sp R lo P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw a R1 Ha; lia))) as ST6.
      assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad])).
      { unfold S3.F_ngnextA.TwB.ngn_frame. cbn [app]. apply (agrees_rw_cells _ _ _ _ _ AGP6) in FRJ; [exact FRJ| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia]. }
      pose proof HD' as HD6. apply (agrees_rw_cells _ _ _ _ _ AGP6) in HD6; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R2; lia].
      eapply (JOIN a2v a1v lw a4v a6v a7v y0 y1 y2 y3 y4 y5 y6 y7 m6 (le4val i3 i2 i1 i0) (le4val c3 c2 c1 c0) (le4val n3 n2 n1 n0) (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z);
        [exact MU6 | exact WM6 | exact MI6 | exact ST6 | exact HH6 | exact FR6 | exact HD6 | exact Hi | exact Hc | exact Hl | exact Ht
        | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Ri0 Ri1 Ri2 Ri3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rc0 Rc1 Rc2 Rc3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rn0 Rn1 Rn2 Rn3; lia)
        | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Ri0 Ri1 Ri2 Ri3; lia); reflexivity | rewrite !bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia); reflexivity | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rc0 Rc1 Rc2 Rc3; lia); reflexivity | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rn0 Rn1 Rn2 Rn3; lia); reflexivity].
    - (* [comment removed for export] *)
      if_true. step. if_false.
      step. step. if_false_by (eqz_false HA ltac:(gio_ceil_fact; clear -CLO__ R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia)).
      step. step. rewrite (and7_aligned HA) by (gio_ceil_fact; clear -CLO__ AH R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
      step. rewrite (sx32_lit c0 c1 c2 c3) by lia. step. rewrite (sx32_lit n0 n1 n2 n3) by lia. step. rewrite (sx32_lit i0 i1 i2 i3) by lia.
      step. rewrite (sx32_lit h0 h1 h2 h3) by lia. step. rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
      hide BUF4. step. hide FRJ. step. step. step. step.
      rewrite (ts_word h0 h1 h2 h3 l0 l1 l2 l3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia).
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]) end.
      unhide FRJ.
      assert (FR6' : forall mm, agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' mm ->
                rw_cells usegs mm (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad])).
      { intros mm AG. unfold S3.F_ngnextA.TwB.ngn_frame. cbn [app]. apply (agrees_rw_cells _ _ _ _ _ AG) in FRJ; [exact FRJ| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia]. }
      lazymatch goal with HX : rw_cells usegs ?mm HA [_; _; C4 ?cwv; C4 ?lwv] |- _ =>
        eapply (JOIN _ cwv lwv _ _ _ _ _ _ _ _ _ _ _ mm (le4val i0 i1 i2 i3) (le4val c0 c1 c2 c3) (le4val n0 n1 n2 n3) (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3)%Z);
          [exact MU | exact WM | assumption | assumption | exact HX | exact (FR6' mm AGP6) | exact HD'
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Ri0 Ri1 Ri2 Ri3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Ri0 Ri1 Ri2 Ri3; lia)
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Rc0 Rc1 Rc2 Rc3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rc0 Rc1 Rc2 Rc3; lia)
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Rn0 Rn1 Rn2 Rn3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia)
          | reflexivity | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1 Ri2 Ri3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rc0 Rc1 Rc2 Rc3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia) | reflexivity | reflexivity | reflexivity | reflexivity] end.
  Qed.
  End Sz6.
  Lemma ngn_epb : ltac:(let t := eval cbv delta [ngn_epb__stmt] in ngn_epb__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_epb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_pb_swap__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (mx : mem)
           (i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 : Z) (Bq : Z) (pre : list byte) (rest tfr : list cell) (hj1 hj2 hj3 hj4 : list byte) (fw0 fw1 : word),
      Forall (fun x => 0 <= x < 256)%Z [i0; i1; d0; d1; h0; h1; h2; h3; l0; l1; l2; l3; c0; c1; c2; c3; n0; n1; n2; n3] ->
      rw_cells usegs mx Bq ([CB 8 pre; C2 (Z_to_bv 64 (i0 + 256 * i1)); C2 (Z_to_bv 64 (d0 + 256 * d1)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                             C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ++ rest) ->
      rw_cells usegs mx (bv_unsigned sp + -160) ([C8 fw0; C8 fw1; C8 (Z_to_bv 64 HA)] ++ tfr) ->
      rw_cells usegs mx HA [CB 8 hj1; CB 8 hj2; CB 4 hj3; CB 4 hj4] -> mem_inv usegs mx ->
      (HA + 24 <= Bq \/ Bq + 28 <= HA)%Z -> (bv_unsigned sp <= HA)%Z -> (HA + 24 <= 2^64)%Z ->
      evt usegs (fun ms' => exists (a1v a2v a4v a6v a7v lw y0 y1 y2 y3 y4 y5 y6 y7 : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y0 y1 y2 x0 x1 a0' a1v a2v a3' a4v a5' a6v a7v
                       y7 x3 x4 x5 x6 x7 x8 x9 x10 x11 y3 y4 y5 y6) F (Z_to_bv 64 0x180e0) fc None m' (seg_rom usegs)
          /\ munch [(HA, HA + 24)]%Z mx m' /\ wmono usegs mx m' /\ mem_inv usegs m'
          /\ rw_cells usegs m' HA [CB 8 hj1; CB 8 hj2; C4 a1v; C4 lw]
          /\ (bv_unsigned a2v mod 2^32 = i1 + 256 * i0)%Z /\ (bv_unsigned a1v mod 2^32 = le4val c3 c2 c1 c0)%Z
          /\ (bv_unsigned lw mod 2^32 = le4val n3 n2 n1 n0)%Z /\ a7v = Z_to_bv 64 (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' (Z_to_bv 64 (Bq + 8)) a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17db4) fc None mx (seg_rom usegs)).
  Section Sz7.
  Variables ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq pre rest tfr hj1 hj2 hj3 hj4 fw0 fw1 : ltac2:(SecDiet.SzSec.tyM 'ngn_pb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_pb_swap__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R2 SPW. pin_using (fun (BU LO P1 R2 SPW : unit) => tt).
 intros GR HB HF HH MI SEP HHA HA64.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(HA, HA + 24)]%Z mx) as MU. pose proof (wmono_refl usegs mx) as WM.
    step. rewrite (zx16_lit (i0 + 256 * i1)) by lia. step. rewrite (zx32_lit (le4val h0 h1 h2 h3)) by (unfold le4val; lia).
    step. rewrite (sx32_lit l0 l1 l2 l3) by lia. step. rewrite (sx32_lit c0 c1 c2 c3) by lia. step. step. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    do 44 step. do 2 step. hide HB. do 7 step. unhide HB.
    apply evt_done. cbv beta.
    lazymatch goal with HX : rw_cells usegs _ HA [_; _; C4 _; C4 ?lwv] |- _ =>
      do 5 eexists; exists lwv; do 9 eexists; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply swap16_word_mod32; assumption|]. split; [apply swap32_sxv_mod32; assumption|].
    split; [apply swap32_sxv_mod32; assumption|]. apply ts_swap_word; assumption.
  Qed.
  End Sz7.
  Lemma ngn_pb_swap : ltac:(let t := eval cbv delta [ngn_pb_swap__stmt] in ngn_pb_swap__stmt in exact t).
  Proof using BU LO P1 R2 SPW. intros ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq pre rest tfr hj1 hj2 hj3 hj4 fw0 fw1. ltac2:(SecDiet.SzSec.closeP 'ngn_pb_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
    get_le16 data off = (q8 data off 0 + 256 * q8 data off 1)%Z.
  Proof using Type. pin_using tt.
    intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
    destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
    rewrite (get_le16_of_slice off data x0 x1 E). unfold q8. rewrite Z.add_0_r, E0, E1. reflexivity.
  Qed.
  Definition firstn2_q8__stmt : Prop := forall data (bs : list byte) (k : nat) off,
    firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
    firstn 2 (skipn k bs) = [b8 (q8 data off 0); b8 (q8 data off 1)].
  Section Sz9.
  Variables data bs k off : ltac2:(SecDiet.SzSec.tyM 'firstn2_q8__stmt "vvvv" @data).
  Lemma firstn2_q8__body : ltac2:(SecDiet.SzSec.bodyP 'firstn2_q8__stmt "vvvv").
  Proof using BU LO P1 R1 R2 SPW. pin_using (fun (BU LO P1 R1 R2 SPW : unit) => tt).
    intros PFX Hk H1.
 subst off.
    destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
    destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
    transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
    - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
    - rewrite E. unfold q8. rewrite Z.add_0_r, E0, E1. reflexivity.
  Qed.
  End Sz9.
  Lemma firstn2_q8 : ltac:(let t := eval cbv delta [firstn2_q8__stmt] in firstn2_q8__stmt in exact t).
  Proof using BU LO P1 R1 R2 SPW. intros data bs k off. ltac2:(SecDiet.SzSec.closeP 'firstn2_q8__body "vvvv"). Qed.
  Lemma bswap16_2 : forall a b, (0 <= a < 256 -> 0 <= b < 256 -> bswap16 (a + 256 * b) = b + 256 * a)%Z.
  Proof using DA HA P sp. pin_using (fun (DA HA P sp : unit) => tt). intros. rewrite <- (le_of_bytes_2 a b), bswap16_bytes, le_of_bytes_2 by lia. reflexivity. Qed.


  (* [comment removed for export] *)
  Definition ngn_pb__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (20 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK
                     (let sw32 (v : Z) := if swapped then bswap32 v else v in
                      let sw16 (v : Z) := if swapped then bswap16 v else v in
                      mkFound (sw16 (get_le16 data 8)) (sw32 (get_le32 data 12) * 2^32 + sw32 (get_le32 data 16)) (sw32 (get_le32 data 20)) (sw32 (get_le32 data 24))
                              (mkCursor (8 + 20) (rem - 20) bt))
                     (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17d70) fc None m5 (seg_rom usegs)).
  Section Sz11.
  Variables ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_pb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_pb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold S3.F_ngnextA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, S3.F_ngnextA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    set (i0 := q8 data 8 0) in *. set (i1 := q8 data 8 1) in *. set (d0 := q8 data 10 0) in *. set (d1 := q8 data 10 1) in *.
    pose proof (q8_range data 8 0 DRNG ltac:(lia)) as Ri0. pose proof (q8_range data 8 1 DRNG ltac:(lia)) as Ri1.
    pose proof (q8_range data 10 0 DRNG ltac:(lia)) as Rd0. pose proof (q8_range data 10 1 DRNG ltac:(lia)) as Rd1.
    fold i0 in Ri0. fold i1 in Ri1. fold d0 in Rd0. fold d1 in Rd1.
    name_field data 12%Z h0 h1 h2 h3 DRNG. name_field data 16%Z l0 l1 l2 l3 DRNG.
    name_field data 20%Z c0 c1 c2 c3 DRNG. name_field data 24%Z n0 n1 n2 n3 DRNG.
    cbv zeta.
    rewrite (get_le16_q8' data 8), (get_le32_q8 data 12), (get_le32_q8 data 16), (get_le32_q8 data 20), (get_le32_q8 data 24) by (keep_hyps CEILV sp R P HA DA Bq data hcs dw lo rem LEN REM; lia).
    fold i0 i1 h0 h1 h2 h3 l0 l1 l2 l3. fold c0 c1 c2 c3 n0 n1 n2 n3.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; 4; 4; 4; Z.to_nat alloc - 28]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (firstn2_q8 data bsx' 8 8%Z PFX eq_refl), (firstn2_q8 data bsx' 10 10%Z PFX eq_refl), (firstn4_q8 data bsx' 12 12%Z PFX eq_refl), (firstn4_q8 data bsx' 16 16%Z PFX eq_refl),
            (firstn4_q8 data bsx' 20 20%Z PFX eq_refl), (firstn4_q8 data bsx' 24 24%Z PFX eq_refl) in BUF by (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM; lia).
    fold i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 in BUF. fold c0 c1 c2 c3 n0 n1 n2 n3 in BUF.
    assert (BUF4 : rw_cells usegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (i0 + 256 * i1)); C2 (Z_to_bv 64 (d0 + 256 * d1)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                                       C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 28) (firstn (Z.to_nat alloc - 28) (skipn 28 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' LEN REM W4 LBS; lia). }
      cbn [cells_bytes cbytes app]. rewrite (le2_lit i0 i1), (le2_lit d0 d1), (le4_lit h0 h1 h2 h3), (le4_lit l0 l1 l2 l3), (le4_lit c0 c1 c2 c3), (le4_lit n0 n1 n2 n3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' Ri0 Ri1 Rd0 Rd1 Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3 Rc0 Rc1 Rc2 Rc3 Rn0 Rn1 Rn2 Rn3; lia). reflexivity. }
    clear BUF.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
    assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
    apply (rw_cells_split_CB usegs m5 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, ccells in FRJ. cbn [app] in FRJ. clear FR5.
    hide PRIV. hide IFS.
    pose proof (munch_refl [(HA, HA + 24); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. if_false_by (eqz_false (Bq + 8) ltac:(clear -K1 K3 K4; lia)).
    step. step. if_false_by (geu_neg_false (Bq + 8) 20 ltac:(lia) ltac:(clear -K1 K3 K4 W4 LEN REM; lia)).
    (* [comment removed for export] *)
    step. step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. pstep. step.
    step. rewrite (and3_aligned (Bq + 8)) by (clear -K1 K2 K3 K4; try lia; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    unhide PRIV. unhide IFS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(HA, HA + 24); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (G5' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB mm)
        by (eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - R1 R2 R3 LO BU SPM; lia|];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - LO BU SPM; lia| apply Forall_nil]);
      rename mm into m5' end.
    assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5').
    { eapply PCAPR_agree; [exact AGD| | exact PC5]. intros a Ha. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). gio_ceil_fact; clear -CLO__ H0 R1 LO BU SPW. lia. }
    assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [Hc [Hn _]]; cbn [outside]. split; [clear - Hn; lia|]. split; [| exact Logic.I].
      destruct Hc as [Hc|Hc]; [clear - Hc; lia|]. destruct (ngn_CLc_facts _ _ _ _ G5 Hc) as [Hx _]. gio_ceil_fact; clear -CLO__ Hx LO BU SPW. lia. }
    assert (MI5' : mem_inv usegs m5') by assumption. assert (ST5' : stk usegs m5' lo (bv_unsigned sp + -160)) by assumption.
    clear MU WM AGD G5 G5e AG5 PC5 MI5 ST5 PRIV IFS.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5') as MU. pose proof (wmono_refl usegs m5') as WM.
    (* [comment removed for export] *)
    assert (JOIN : forall (iw cw lw a4v a6v a7v y0 y1 y2 y3 y4 y5 y6 y7 : word) (m6 : mem) (idv capv lenv tv : Z),
      munch [(HA, HA + 24)]%Z m5' m6 -> wmono usegs m5' m6 -> mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 cw; C4 lw] ->
      rw_cells usegs m6 (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad]) ->
      rw_cells usegs m6 DA [CB 8 dwj] ->
      (bv_unsigned iw mod 2^32 = idv)%Z -> (bv_unsigned cw mod 2^32 = capv)%Z -> (bv_unsigned lw mod 2^32 = lenv)%Z ->
      a7v = Z_to_bv 64 tv -> (0 <= tv < 2^64)%Z -> (0 <= idv < 2^32)%Z -> (0 <= capv < 2^32)%Z -> (0 <= lenv < 2^32)%Z ->
      idv = (if swapped then bswap16 (i0 + 256 * i1) else i0 + 256 * i1)%Z ->
      tv = ((if swapped then bswap32 (le4val h0 h1 h2 h3) else le4val h0 h1 h2 h3) * 2^32 + (if swapped then bswap32 (le4val l0 l1 l2 l3) else le4val l0 l1 l2 l3))%Z ->
      capv = (if swapped then bswap32 (le4val c0 c1 c2 c3) else le4val c0 c1 c2 c3) ->
      lenv = (if swapped then bswap32 (le4val n0 n1 n2 n3) else le4val n0 n1 n2 n3) ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (npeek usegs)
        (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK
           (mkFound (if swapped then bswap16 (i0 + 256 * i1) else i0 + 256 * i1)%Z
                    ((if swapped then bswap32 (le4val h0 h1 h2 h3) else le4val h0 h1 h2 h3) * 2 ^ 32 + (if swapped then bswap32 (le4val l0 l1 l2 l3) else le4val l0 l1 l2 l3))
                    (if swapped then bswap32 (le4val c0 c1 c2 c3) else le4val c0 c1 c2 c3)
                    (if swapped then bswap32 (le4val n0 n1 n2 n3) else le4val n0 n1 n2 n3)
                    (mkCursor 28 (rem - 20) bt)) (pv bq alloc data eb sx ix) ps)
        (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y0 y1 y2 (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (rem + -20)) cw iw (Z_to_bv 64 (s32 bt)) a4v (Z_to_bv 64 (Bq + 28)) a6v a7v
                 y7 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 y3 y4 y5 y6) F (Z_to_bv 64 0x180e0) fc None m6 (seg_rom usegs))).
    { intros iw cw lw a4v a6v a7v y0 y1 y2 y3 y4 y5 y6 y7 m6 idv capv lenv tv MU6 WM6 MI6 ST6 HH6 FR6 HD6 Hiw Hcw Hlw -> Htv Hid Hcap Hlen Eid Etv Ecap Elen.
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5' | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LO BU R1 R2 R3; lia). }
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGP | | exact PC5']. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5' Ha). cbn [outside]. unfold rc_lo in LO. (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header ps bq Bq Ix alloc data eb sx ix hcs dw bsx' hj iw cw lw m6 a LO BU R1 G6 H0; lia). }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj iw cw lw a Hna; lia). }
      assert (HH7 : rw_cells usegs m6 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 capv); C4 (Z_to_bv 64 lenv)]).
      { eapply rw_cells_recell; [exact HH6 | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LHJ; lia) |].
        cbn [cells_bytes cbytes app]. rewrite (le4_word_mod32 cw capv Hcw), (le4_word_mod32 lw lenv Hlw). reflexivity. }
      apply evt_done. rewrite <- Eid, <- Etv, <- Ecap, <- Elen.
      replace (Z_to_bv 64 (rem + -20)) with (Z_to_bv 64 (rem - 20)) by (f_equal; lia).
      eapply (ngn_found _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iw cw _ _ m6 ps bq Bq Ix alloc 28 (rem - 20) data eb sx ix idv tv capv lenv bt _ dj);
        [exact ST6 | exact FR6 | exact MI6 | exact G6 | exact PC6 | exact AG6 | exact HH7 | exact HD6 | reflexivity
        | exact Hiw | exact Hcw | exact Htv | exact DRNG | (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj iw cw lw; lia) | reflexivity | (keep_hyps CEILV sp R P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw REM; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LEN; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj iw cw lw LEN L30; lia) | exact Hlen | exact Hbt | exact OF5]. }
    step. destruct swapped.
    - (* [comment removed for export] *)
      if_false. step. if_false.
      step. step. if_false_by (eqz_false HA ltac:(gio_ceil_fact; clear -CLO__ R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia)).
      step. step. rewrite (and7_aligned HA) by (gio_ceil_fact; clear -CLO__ AH R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
      eapply evt_cut.
      { eapply (ngn_pb_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 c0 c1 c2 c3 n0 n1 n2 n3 Bq);
          [repeat (apply Forall_cons; [(keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Ri0 Ri1 Rd0 Rd1 Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3 Rc0 Rc1 Rc2 Rc3 Rn0 Rn1 Rn2 Rn3; lia)|]); apply Forall_nil | exact BUF4 | exact FRJ | exact HHj | assumption | gio_ceil_fact; clear -CLO__ K1 K4 R1 LO BU SPM SPW W4 LEN REM; unfold rc_lo, rc_spmain in *; (keep_hyps CEILV sp R lo HA Bq alloc rem data LO BU R1 K4 W4 CLO__; lia) | exact R1 | clear -R1 R2 R3 SP47 SPM; unfold rc_spmain in *; (keep_hyps R HA DA R2 R3 SP47; lia)]. }
      cbv beta. intros ms' (a1v & a2v & a4v & a6v & a7v & lw & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & m6 & -> & MU6 & WM6 & MI6 & HH6 & Hi & Hc & Hl & Ht).
      assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      pose proof (agrees_stk _ _ _ _ _ AGP6 ST5' ltac:(intros a Ha; cbn [outside]; (keep_hyps CEILV sp R lo P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw a R1 Ha; lia))) as ST6.
      assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad])).
      { unfold S3.F_ngnextA.TwB.ngn_frame. cbn [app]. apply (agrees_rw_cells _ _ _ _ _ AGP6) in FRJ; [exact FRJ| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia]. }
      pose proof HD' as HD6. apply (agrees_rw_cells _ _ _ _ _ AGP6) in HD6; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R2; lia].
      eapply (JOIN a2v a1v lw a4v a6v a7v y0 y1 y2 y3 y4 y5 y6 y7 m6 (i1 + 256 * i0)%Z (le4val c3 c2 c1 c0) (le4val n3 n2 n1 n0) (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z);
        [exact MU6 | exact WM6 | exact MI6 | exact ST6 | exact HH6 | exact FR6 | exact HD6 | exact Hi | exact Hc | exact Hl | exact Ht
        | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Hi; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rc0 Rc1 Rc2 Rc3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj a1v a2v lw Rn0 Rn1 Rn2 Rn3; lia)
        | rewrite bswap16_2 by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Ri0 Ri1; lia); reflexivity | rewrite !bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia); reflexivity | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rc0 Rc1 Rc2 Rc3; lia); reflexivity | rewrite bswap32_le4val by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj a1v a2v lw Rn0 Rn1 Rn2 Rn3; lia); reflexivity].
    - (* [comment removed for export] *)
      if_true. step. if_false.
      step. step. if_false_by (eqz_false HA ltac:(gio_ceil_fact; clear -CLO__ R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia)).
      step. step. rewrite (and7_aligned HA) by (gio_ceil_fact; clear -CLO__ AH R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
      step. rewrite (sx32_lit c0 c1 c2 c3) by lia. step. rewrite (sx32_lit n0 n1 n2 n3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia). step. rewrite (zx16_lit (i0 + 256 * i1)) by (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1; lia). step.
      step. rewrite (sx32_lit h0 h1 h2 h3) by lia. step. rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
      hide BUF4. step. hide FRJ. step. step. step. step.
      rewrite (ts_word h0 h1 h2 h3 l0 l1 l2 l3) by (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia).
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGP6 : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]) end.
      unhide FRJ.
      assert (FR6' : forall mm, agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5' mm ->
                rw_cells usegs mm (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad])).
      { intros mm AG. unfold S3.F_ngnextA.TwB.ngn_frame. cbn [app]. apply (agrees_rw_cells _ _ _ _ _ AG) in FRJ; [exact FRJ| intros a Ha; cbn [outside cells_size csize Nat.add] in *; clear -Ha R1; lia]. }
      lazymatch goal with HX : rw_cells usegs ?mm HA [_; _; C4 ?cwv; C4 ?lwv] |- _ =>
        eapply (JOIN _ cwv lwv _ _ _ _ _ _ _ _ _ _ _ mm (i0 + 256 * i1)%Z (le4val c0 c1 c2 c3) (le4val n0 n1 n2 n3) (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3)%Z);
          [exact MU | exact WM | assumption | assumption | exact HX | exact (FR6' mm AGP6) | exact HD'
          | rewrite unsigned_lit by (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1; lia); apply Z.mod_small; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1; lia)
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Rc0 Rc1 Rc2 Rc3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rc0 Rc1 Rc2 Rc3; lia)
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; (keep_hyps CEILV R P r1 Bq alloc rem data hcs dw bsx' hj q r q1 Rn0 Rn1 Rn2 Rn3 H0 H1; lia)); apply sxv_mod32; (keep_hyps CEILV sp R P HA DA Bq alloc data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia)
          | reflexivity | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rh0 Rh1 Rh2 Rh3 Rl0 Rl1 Rl2 Rl3; lia) | (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Ri0 Ri1; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rc0 Rc1 Rc2 Rc3; lia) | unfold le4val; (keep_hyps CEILV sp R lo P HA DA Bq alloc rem data hcs dw bsx' hj Rn0 Rn1 Rn2 Rn3; lia) | reflexivity | reflexivity | reflexivity | reflexivity] end.
  Qed.
  End Sz11.
  Lemma ngn_pb : ltac:(let t := eval cbv delta [ngn_pb__stmt] in ngn_pb__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_pb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.

End WithCeil.
End TwB.
End F_ngnextD.

(* [comment removed for export] *)
Module F_ngnextE.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
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
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (F_ngnextA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (F_ngnextA.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (F_ngnextA.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (F_ngnextA.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (F_ngnextA.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (F_ngnextA.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (F_ngnextA.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (F_ngnextA.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (F_ngnextA.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (F_ngnextA.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (F_ngnextA.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (F_ngnextA.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold F_ngnextA.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold F_ngnextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ccells := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells).
  #[local] Abbreviation ngn_spb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_spb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_epb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_epb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_pb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).


  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  (* [comment removed for export] *)
  Definition ngn_KF (rp : (Z + ng_found) * pcapT) : M (PState H hptr) (Z * pkthdr * pcapT) :=
    let '(r, p) := rp in match r with inl st => mret (st, hdr0, p) | inr fd => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK fd p end.

  Definition ngn_epbK (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 20 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      mret (inr (mkFound (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) off) else get_le32 (pc_bufdata p) off)
                        ((if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 4)) else get_le32 (pc_bufdata p) (off + 4)) * 2^32
                         + (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 8)) else get_le32 (pc_bufdata p) (off + 8)))
                        (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 12)) else get_le32 (pc_bufdata p) (off + 12))
                        (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 16)) else get_le32 (pc_bufdata p) (off + 16)) c'), p)
    end.
  Definition ngn_spbK (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 4 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let len := (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) off) else get_le32 (pc_bufdata p) off) in
      let caplen := if pc_snapshot p <? len then pc_snapshot p else len in
      mret (inr (mkFound 0 0 caplen len c'), p)
    end.
  Definition ngn_pbK (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 20 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      mret (inr (mkFound (if pc_swapped p then bswap16 (get_le16 (pc_bufdata p) off) else get_le16 (pc_bufdata p) off)
                        ((if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 4)) else get_le32 (pc_bufdata p) (off + 4)) * 2^32
                         + (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 8)) else get_le32 (pc_bufdata p) (off + 8)))
                        (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 12)) else get_le32 (pc_bufdata p) (off + 12))
                        (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 16)) else get_le32 (pc_bufdata p) (off + 16)) c'), p)
    end.
  Definition ngn_idbK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 8 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let p' := if pc_swapped p then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p else p in
      let lt := get_le16 (pc_bufdata p') off in
      let sl := get_le32 (pc_bufdata p') (off + 4) in
      if negb (pc_linktype p' =? lt) then mret (inl (-1)%Z, set_errbuf (Msg.iface_type_differs lt) p')
      else if negb (pc_snapshot p' =? pcapint_adjust_snapshot (pc_linktype p') sl) then mret (inl (-1)%Z, set_errbuf (Msg.iface_snaplen_differs sl) p')
      else mbind (add_interface MOps (prims HO fo_nop sites) p' off c') (fun r => let '(ok, c, p, m) := r in
             if ok then LOOP p else mret (inl (-1)%Z, set_errbuf m p))
    end.
  Definition ngn_shbK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 16 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let p' := if pc_swapped p then set_bufdata (swap_field 2 (off + 4) (swap_field 4 off (pc_bufdata p))) p else p in
      let bom := get_le32 (pc_bufdata p') off in
      if bom =? BYTE_ORDER_MAGIC then
        let major := get_le16 (pc_bufdata p') (off + 4) in
        if negb (major =? 1) then mret (inl (-1)%Z, set_errbuf (Msg.unknown_major major) p')
        else LOOP (set_ng (mkNg (ng_user_tsresol (ng_of p')) (ng_max_blocksize (ng_of p')) 0 (ng_ifaces_size (ng_of p')) []) (ng_ifaces_ptr_of p') p')
      else if bom =? BYTE_ORDER_MAGIC_SWAPPED then mret (inl (-1)%Z, set_errbuf Msg.sections_byte_order p')
      else mret (inl (-1)%Z, set_errbuf Msg.bad_byte_order_magic p')
    end.
  Definition ngn_blkK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    if cur_block_type c =? BT_EPB then ngn_epbK c p
    else if cur_block_type c =? BT_SPB then ngn_spbK c p
    else if cur_block_type c =? BT_PB then ngn_pbK c p
    else if cur_block_type c =? BT_IDB then ngn_idbK LOOP c p
    else if cur_block_type c =? BT_SHB then ngn_shbK LOOP c p
    else LOOP p.
  Definition ngn_body (LOOP : pcapT -> MR) (rb : block_result) : MR :=
    match rb with
    | RB_Eof p => mret (inl 0%Z, p)
    | RB_Err m p => mret (inl (-1)%Z, set_errbuf m p)
    | RB_Ok c p => ngn_blkK LOOP c p
    end.

  Lemma ng_scan_blocks_S : forall fuel (p : pcapT),
    ng_scan_blocks MOps (prims HO fo_nop sites) (S fuel) p
    = mbind (read_block MOps (prims HO fo_nop sites) (DStack SiteBhdrNextPacket 0) p) (ngn_body (ng_scan_blocks MOps (prims HO fo_nop sites) fuel)).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma pcap_ng_next_packet_KF : forall fuel (p : pcapT),
    pcap_ng_next_packet MOps (prims HO fo_nop sites) fuel p = mbind (ng_scan_blocks MOps (prims HO fo_nop sites) fuel p) ngn_KF.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngn_head (Q : pcapT -> PState H hptr -> machine_state -> Prop) : Prop :=
    forall (ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat -> ps_outfile ps = o ->
      Q (pv bq alloc data eb sx ix) ps
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 (Z_to_bv 64 (P + 216)) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 65280) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x6 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) x10 (Z_to_bv 64 15)
                 t3' t4' t5' t6') F (Z_to_bv 64 NGN_LOOP) fc None m5 (seg_rom ssegs)).

  (* [comment removed for export] *)
  Lemma ngn_too_short :
    forall (ra' t0' t1' t2' a0' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (p' : pcapT) (PB' : list (cblock (hptr:=hptr))) (z : Z) (e : list Z) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_finalC m5 ps PB' p' hcs dw ->
      implM ssegs (mret ((-1)%Z, hdr0, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 256) (Z_to_bv 64 NGN_FMT_TOO_SHORT) (Z_to_bv 64 z) a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x176cc) fc None m5 (seg_rom ssegs)).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros until ccs. intros ST5 FR5 Hccs MI5 FIN.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    assert (MSG : fmt_at m5 NGN_FMT_TOO_SHORT "block of type %u in pcapng dump file is too short"%string)
      by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_TOO_SHORT; lia | unfold NGN_FMT_TOO_SHORT; cbn; lia]).
    pose proof FIN as (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. step. unhide FR5. unhide HH. unhide HD.
    apply evt_done. unfold NGN_FMT_TOO_SHORT in MSG |- *.
    eapply ngn_snp with (args := [AInt z]); [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_epb_full :
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (mbind (ngn_epbK (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17644) fc None m5 (seg_rom ssegs)).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros until cpad. intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold ngn_epbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. step. step.
    if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (rem <? 20) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply ngn_epb; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | lia | exact Hbt | exact OF5].
    - replace (rem <? 20) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 6);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_spb_full :
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (mbind (ngn_spbK (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17624) fc None m5 (seg_rom ssegs)).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros until cpad. intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold ngn_spbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. step. step.
    if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (rem <? 4) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply ngn_spb; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | lia | exact Hbt | exact OF5].
    - replace (rem <? 4) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 3);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_pb_full :
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (mbind (ngn_pbK (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x175e0) fc None m5 (seg_rom ssegs)).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros until cpad. intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold ngn_pbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. step. step.
    if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (rem <? 20) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply ngn_pb; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | lia | exact Hbt | exact OF5].
    - replace (rem <? 20) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 2);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  Lemma PCAPR_bufdata : forall (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data data' eb : list Z) (sx : pcap_ng_sf) (ix : option hptr)
                              (m5 m6 : mem) (Q : Z -> Prop) (BS : list byte),
    GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
    agrees_on Q m5 m6 -> (forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> Q a) ->
    rw_cells ssegs m6 Bq [CB (Z.to_nat alloc) BS] -> firstn (length data') BS = map b8 data' -> length data' = length data ->
    PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m6.
  Proof using AD AH ALN BU LO P1 P5 R1 R2 SPW. pin_using (fun (AD AH ALN BU LO P1 P5 R1 R2 SPW : unit) => tt).
    intros ps bq Bq Ix alloc data data' eb sx ix m5 m6 Q BS G PC AG HQ BUF6 PFX6 LEN.
    destruct PC as (Afx & Hin & (Bx & Ix' & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G as Ge. rewrite EPB in Ge.
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ Ge eq_refl) as [APB API].
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ Ge ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ Ge ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, APB, API, L1, L3, L4, K1, K3, K4. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB, API, L1, L3, L4, K1, K3, K4.
    assert (EBX : Bx = Bq) by congruence. subst Bx. unfold PCAP_NG_SF_TOTAL in APB, API, L3, L4.
    exists Afx. split; [exact Hin|]. exists Bq, Ix', jx, padx, BS.
    split; [exact EPB|].
    split. { eapply agrees_rw_cells; [exact AG | exact CELLS |]. intros a Ha. rewrite pcap_cells_gen_size in Ha by reflexivity. apply HQ; lia. }
    split. { eapply agrees_rw_cells; [exact AG | exact PRIV |]. intros a Ha. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ.
             unfold psize, is_ng, F_ngnextA.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha. cbn [pc_priv] in PZ, Ha. unfold PCAP_NG_SF_TOTAL in PZ. apply HQ; lia. }
    split; [exact BUF6|]. split; [exact PFX6|].
    split. { eapply ifaces_ok_agree; [exact AG | | exact IFS]. intros sg q Hq a Ha. unfold F_ngnextA.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
             destruct (API sx q eq_refl) as [X1 X2].
             pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ Ge ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
             unfold F_ngnextA.pv in X2. cbn [pc_bufalloc] in X2. clear - HQ I1 I4 X2 Ha. apply HQ; lia. }
    unfold pcap_wf in WF |- *. unfold F_ngnextA.pv in WF |- *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
    rewrite LEN. exact WF.
  Qed.

End NgnCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.

From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB.  Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
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

Local Open Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_ngnextA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (S3.F_ngnextA.TwB.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (S3.F_ngnextA.TwB.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (S3.F_ngnextA.TwB.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (S3.F_ngnextA.TwB.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (S3.F_ngnextA.TwB.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (S3.F_ngnextA.TwB.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (S3.F_ngnextA.TwB.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (S3.F_ngnextA.TwB.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (S3.F_ngnextA.TwB.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (S3.F_ngnextA.TwB.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (S3.F_ngnextA.TwB.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold S3.F_ngnextA.TwB.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold S3.F_ngnextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ccells := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells ).
  #[local] Abbreviation ngn_spb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_spb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_epb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_epb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_pb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).


  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  (* [comment removed for export] *)
  Definition ngn_KF (rp : (Z + ng_found) * pcapT) : M (PState H hptr) (Z * pkthdr * pcapT) :=
    let '(r, p) := rp in match r with inl st => mret (st, hdr0, p) | inr fd => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK fd p end.

  Definition ngn_epbK (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 20 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      mret (inr (mkFound (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) off) else get_le32 (pc_bufdata p) off)
                        ((if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 4)) else get_le32 (pc_bufdata p) (off + 4)) * 2^32
                         + (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 8)) else get_le32 (pc_bufdata p) (off + 8)))
                        (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 12)) else get_le32 (pc_bufdata p) (off + 12))
                        (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 16)) else get_le32 (pc_bufdata p) (off + 16)) c'), p)
    end.
  Definition ngn_spbK (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 4 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let len := (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) off) else get_le32 (pc_bufdata p) off) in
      let caplen := if pc_snapshot p <? len then pc_snapshot p else len in
      mret (inr (mkFound 0 0 caplen len c'), p)
    end.
  Definition ngn_pbK (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 20 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      mret (inr (mkFound (if pc_swapped p then bswap16 (get_le16 (pc_bufdata p) off) else get_le16 (pc_bufdata p) off)
                        ((if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 4)) else get_le32 (pc_bufdata p) (off + 4)) * 2^32
                         + (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 8)) else get_le32 (pc_bufdata p) (off + 8)))
                        (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 12)) else get_le32 (pc_bufdata p) (off + 12))
                        (if pc_swapped p then bswap32 (get_le32 (pc_bufdata p) (off + 16)) else get_le32 (pc_bufdata p) (off + 16)) c'), p)
    end.
  Definition ngn_idbK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 8 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let p' := if pc_swapped p then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p else p in
      let lt := get_le16 (pc_bufdata p') off in
      let sl := get_le32 (pc_bufdata p') (off + 4) in
      if negb (pc_linktype p' =? lt) then mret (inl (-1)%Z, set_errbuf (Msg.iface_type_differs lt) p')
      else if negb (pc_snapshot p' =? pcapint_adjust_snapshot (pc_linktype p') sl) then mret (inl (-1)%Z, set_errbuf (Msg.iface_snaplen_differs sl) p')
      else mbind (add_interface MOps (prims HO fo_nop sites) p' off c') (fun r => let '(ok, c, p, m) := r in
             if ok then LOOP p else mret (inl (-1)%Z, set_errbuf m p))
    end.
  Definition ngn_shbK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    match get_from_block_data c 16 with
    | inl m => mret (inl (-1)%Z, set_errbuf m p)
    | inr (off, c') =>
      let p' := if pc_swapped p then set_bufdata (swap_field 2 (off + 4) (swap_field 4 off (pc_bufdata p))) p else p in
      let bom := get_le32 (pc_bufdata p') off in
      if bom =? BYTE_ORDER_MAGIC then
        let major := get_le16 (pc_bufdata p') (off + 4) in
        if negb (major =? 1) then mret (inl (-1)%Z, set_errbuf (Msg.unknown_major major) p')
        else LOOP (set_ng (mkNg (ng_user_tsresol (ng_of p')) (ng_max_blocksize (ng_of p')) 0 (ng_ifaces_size (ng_of p')) []) (ng_ifaces_ptr_of p') p')
      else if bom =? BYTE_ORDER_MAGIC_SWAPPED then mret (inl (-1)%Z, set_errbuf Msg.sections_byte_order p')
      else mret (inl (-1)%Z, set_errbuf Msg.bad_byte_order_magic p')
    end.
  Definition ngn_blkK (LOOP : pcapT -> MR) (c : cursor) (p : pcapT) : MR :=
    if cur_block_type c =? BT_EPB then ngn_epbK c p
    else if cur_block_type c =? BT_SPB then ngn_spbK c p
    else if cur_block_type c =? BT_PB then ngn_pbK c p
    else if cur_block_type c =? BT_IDB then ngn_idbK LOOP c p
    else if cur_block_type c =? BT_SHB then ngn_shbK LOOP c p
    else LOOP p.
  Definition ngn_body (LOOP : pcapT -> MR) (rb : block_result) : MR :=
    match rb with
    | RB_Eof p => mret (inl 0%Z, p)
    | RB_Err m p => mret (inl (-1)%Z, set_errbuf m p)
    | RB_Ok c p => ngn_blkK LOOP c p
    end.

  Lemma ng_scan_blocks_S : forall fuel (p : pcapT),
    ng_scan_blocks MOps (prims HO fo_nop sites) (S fuel) p
    = mbind (read_block MOps (prims HO fo_nop sites) (DStack SiteBhdrNextPacket 0) p) (ngn_body (ng_scan_blocks MOps (prims HO fo_nop sites) fuel)).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma pcap_ng_next_packet_KF : forall fuel (p : pcapT),
    pcap_ng_next_packet MOps (prims HO fo_nop sites) fuel p = mbind (ng_scan_blocks MOps (prims HO fo_nop sites) fuel p) ngn_KF.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngn_head (Q : pcapT -> PState H hptr -> machine_state -> Prop) : Prop :=
    forall (ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat -> ps_outfile ps = o ->
      Q (pv bq alloc data eb sx ix) ps
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 (Z_to_bv 64 (P + 216)) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 65280) (Z_to_bv 64 Af) x6 x7 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 168627466)
                 t3' t4' t5' t6') F (Z_to_bv 64 NGN_LOOP) fc None m5 (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma ngn_too_short :
    forall (ra' t0' t1' t2' a0' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (p' : pcapT) (PB' : list (cblock (hptr:=hptr))) (z : Z) (e : list Z) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_finalC m5 ps PB' p' hcs dw ->
      implM usegs (mret ((-1)%Z, hdr0, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 256) (Z_to_bv 64 NGN_FMT_TOO_SHORT) (Z_to_bv 64 z) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17d28) fc None m5 (seg_rom usegs)).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros until ccs. intros ST5 FR5 Hccs MI5 FIN.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    assert (MSG : fmt_at m5 NGN_FMT_TOO_SHORT "block of type %u in pcapng dump file is too short"%string)
      by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_TOO_SHORT; lia | unfold NGN_FMT_TOO_SHORT; cbn; lia]).
    pose proof FIN as (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. step. unhide FR5. unhide HH. unhide HD.
    apply evt_done. unfold NGN_FMT_TOO_SHORT in MSG |- *.
    eapply ngn_snp with (args := [AInt z]); [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_epb_full :
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (mbind (ngn_epbK (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17c80) fc None m5 (seg_rom usegs)).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros until cpad. intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold ngn_epbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. step. step.
    if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (rem <? 20) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply ngn_epb; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | lia | exact Hbt | exact OF5].
    - replace (rem <? 20) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 6);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_spb_full :
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (mbind (ngn_spbK (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17ca0) fc None m5 (seg_rom usegs)).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros until cpad. intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold ngn_spbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. step. step.
    if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (rem <? 4) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply ngn_spb; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | lia | exact Hbt | exact OF5].
    - replace (rem <? 4) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 3);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_pb_full :
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (mbind (ngn_pbK (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17c60) fc None m5 (seg_rom usegs)).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros until cpad. intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold ngn_pbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. step. step.
    if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (rem <? 20) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply ngn_pb; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | lia | exact Hbt | exact OF5].
    - replace (rem <? 20) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 2);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  Lemma PCAPR_bufdata : forall (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data data' eb : list Z) (sx : pcap_ng_sf) (ix : option hptr)
                              (m5 m6 : mem) (Q : Z -> Prop) (BS : list byte),
    GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
    agrees_on Q m5 m6 -> (forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> Q a) ->
    rw_cells usegs m6 Bq [CB (Z.to_nat alloc) BS] -> firstn (length data') BS = map b8 data' -> length data' = length data ->
    PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m6.
  Proof using AD AH ALN BU LO P1 P5 R1 R2 SPW. pin_using (fun (AD AH ALN BU LO P1 P5 R1 R2 SPW : unit) => tt).
    intros ps bq Bq Ix alloc data data' eb sx ix m5 m6 Q BS G PC AG HQ BUF6 PFX6 LEN.
    destruct PC as (Afx & Hin & (Bx & Ix' & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G as Ge. rewrite EPB in Ge.
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ Ge eq_refl) as [APB API].
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ Ge ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ Ge ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB, API, L1, L3, L4, K1, K3, K4. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB, API, L1, L3, L4, K1, K3, K4.
    assert (EBX : Bx = Bq) by congruence. subst Bx. unfold PCAP_NG_SF_TOTAL in APB, API, L3, L4.
    exists Afx. split; [exact Hin|]. exists Bq, Ix', jx, padx, BS.
    split; [exact EPB|].
    split. { eapply agrees_rw_cells; [exact AG | exact CELLS |]. intros a Ha. rewrite pcap_cells_gen_size in Ha by reflexivity. apply HQ; lia. }
    split. { eapply agrees_rw_cells; [exact AG | exact PRIV |]. intros a Ha. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ.
             unfold psize, is_ng, S3.F_ngnextA.TwB.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha. cbn [pc_priv] in PZ, Ha. unfold PCAP_NG_SF_TOTAL in PZ. apply HQ; lia. }
    split; [exact BUF6|]. split; [exact PFX6|].
    split. { eapply ifaces_ok_agree; [exact AG | | exact IFS]. intros sg q Hq a Ha. unfold S3.F_ngnextA.TwB.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
             destruct (API sx q eq_refl) as [X1 X2].
             pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ Ge ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
             unfold S3.F_ngnextA.TwB.pv in X2. cbn [pc_bufalloc] in X2. clear - HQ I1 I4 X2 Ha. apply HQ; lia. }
    unfold pcap_wf in WF |- *. unfold S3.F_ngnextA.TwB.pv in WF |- *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
    rewrite LEN. exact WF.
  Qed.

End NgnCtx.

End WithCeil.
End TwB.
End F_ngnextE.

(* [comment removed for export] *)
Module F_ngnextS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Close Scope bv_scope.
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition str_bytes (s : string) : list byte :=
  map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string s) ++ [Z_to_bv 8 0].
Lemma str_bytes_length : forall s, length (str_bytes s) = S (String.length s).
Proof using Type. pin_using tt. intros s. unfold str_bytes. rewrite length_app, length_map, length_list_ascii. cbn [length]. lia. Qed.
Lemma str_at_intro : forall m A (s : string),
  mem_inv ssegs m -> ro_bytes_b ssegs A (str_bytes s) = true ->
  0x10000 <= A -> A + Z.of_nat (String.length s) + 1 <= 0x13000 -> bytes_at ssegs m A (str_bytes s).
Proof using Type. pin_using tt.
  intros m A s MI RO LO HI.
  pose proof (ro_cells_image ssegs m A _ MI RO ltac:(lia)) as X. rewrite str_bytes_length in X.
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

Definition splice_pfx__stmt : Prop := forall (data mid : list Z) (bs : list byte) (k : nat),
  firstn (length data) bs = map b8 data -> (k + length mid <= length data)%nat -> (length data <= length bs)%nat ->
  firstn (length (firstn k data ++ mid ++ skipn (k + length mid) data)) (firstn k bs ++ map b8 mid ++ skipn (k + length mid) bs)
  = map b8 (firstn k data ++ mid ++ skipn (k + length mid) data).
Section Sz5.
Variables data mid bs k : ltac2:(SecDiet.SzSec.tyM 'splice_pfx__stmt "vvvv" @data).
Lemma splice_pfx__body : ltac2:(SecDiet.SzSec.bodyP 'splice_pfx__stmt "vvvv").
Proof using Type. pin_using tt.
  intros PFX Hk Hl.
 rewrite splice_length by lia.
  assert (L1 : length (firstn k bs) = k) by (rewrite length_firstn; lia).
  assert (L2 : length (map b8 mid) = length mid) by apply length_map.
  rewrite firstn_app, L1, firstn_all2 by (rewrite L1; lia).
  rewrite firstn_app, L2, (firstn_all2 (map b8 mid)) by (rewrite L2; lia).
  rewrite !map_app, <- firstn_map, <- skipn_map, <- PFX.
  rewrite firstn_firstn by lia. replace (Nat.min k (length data)) with k by lia.
  f_equal. f_equal. rewrite firstn_skipn_comm. f_equal. f_equal. lia.
Qed.
End Sz5.
Lemma splice_pfx : ltac:(let t := eval cbv delta [splice_pfx__stmt] in splice_pfx__stmt in exact t).
Proof using Type. intros data mid bs k. ltac2:(SecDiet.SzSec.closeP 'splice_pfx__body "vvvv"). Qed.

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
Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (F_ngnextA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (F_ngnextA.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (F_ngnextA.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (F_ngnextA.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (F_ngnextA.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (F_ngnextA.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (F_ngnextA.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (F_ngnextA.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (F_ngnextA.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (F_ngnextA.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (F_ngnextA.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (F_ngnextA.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold F_ngnextA.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold F_ngnextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ccells := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells).
  #[local] Abbreviation ngn_spb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_spb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_epb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_epb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_pb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).


  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  #[local] Abbreviation ngn_KF := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_shbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_shbK (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_idbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_idbK HO sites).
  #[local] Abbreviation ngn_head := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_too_short := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_too_short K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation PCAPR_bufdata := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.PCAPR_bufdata K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU ALN R1 R2 AH AD SPW P1 P5).
  #[local] Abbreviation get_le16_q8' := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le16_q8').
  #[local] Abbreviation firstn2_q8 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn2_q8 sp R lo P HA DA LO BU R1 R2 SPW P1).
  #[local] Abbreviation bswap16_2 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.bswap16_2 sp P HA DA).

  Ltac name_field data off a b c d DRNG :=
    set (a := q8 data off 0%Z) in *; set (b := q8 data off 1%Z) in *; set (c := q8 data off 2%Z) in *; set (d := q8 data off 3%Z) in *;
    let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
    pose proof (q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
    pose proof (q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
    fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

  (* [comment removed for export] *)
  Definition ngn_snp90__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (p' : pcapT) (PB' : list (cblock (hptr:=hptr))) (e : list Z) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_finalC m5 ps PB' p' hcs dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -160) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implM ssegs (mret ((-1)%Z, hdr0, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x176cc) fc None m5 (seg_rom ssegs)).
  Section Sz10.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps p' PB' e hcs dw dj ccs FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'ngn_snp90__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_snp90__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_snp90__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros ST5 FR5 Hccs MI5 FIN FMT FOK LA FW.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof FIN as (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD. hide FMT. hide FW.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. step. unhide FR5. unhide HH. unhide HD. unhide FMT. unhide FW.
    apply evt_done.
    eapply ngn_snp; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact FMT | exact FOK | exact LA | exact FW].
  Qed.
  End Sz10.
  Lemma ngn_snp90 : ltac:(let t := eval cbv delta [ngn_snp90__stmt] in ngn_snp90__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps p' PB' e hcs dw dj ccs FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'ngn_snp90__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition ngn_snp8c__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (p' : pcapT) (PB' : list (cblock (hptr:=hptr))) (e : list Z) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_finalC m5 ps PB' p' hcs dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -160) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implM ssegs (mret ((-1)%Z, hdr0, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x176c8) fc None m5 (seg_rom ssegs)).
  Section Sz11.
  Variables ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps p' PB' e hcs dw dj ccs FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'ngn_snp8c__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_snp8c__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_snp8c__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros ST5 FR5 Hccs MI5 FIN FMT FOK LA FW.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof FIN as (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD. hide FMT. hide FW.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. unhide FR5. unhide HH. unhide HD. unhide FMT. unhide FW.
    apply evt_done.
    eapply ngn_snp90; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact FMT | exact FOK | exact LA | exact FW].
  Qed.
  End Sz11.
  Lemma ngn_snp8c : ltac:(let t := eval cbv delta [ngn_snp8c__stmt] in ngn_snp8c__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. intros ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps p' PB' e hcs dw dj ccs FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'ngn_snp8c__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_shb_swap__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (mx : mem)
           (g0 g1 g2 g3 j0 j1 : Z) (Bq : Z) (pre : list byte) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; j0; j1] ->
      rw_cells ssegs mx Bq ([CB 8 pre; C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C2 (Z_to_bv 64 (j0 + 256 * j1))] ++ rest) ->
      mem_inv ssegs mx -> (0 <= Bq)%Z -> (Bq + 14 <= 2^64)%Z ->
      evt ssegs (fun ms' => exists (a1v a2v a3v a4v : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 (Z_to_bv 64 (Bq + 8)) a1v a2v a3v a4v a5' a6' a7'
                       (Z_to_bv 64 65280) x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17500) fc None m' (seg_rom ssegs)
          /\ munch [(Bq + 8, Bq + 14)]%Z mx m' /\ wmono ssegs mx m' /\ mem_inv ssegs m'
          /\ rw_cells ssegs m' Bq ([CB 8 pre; C4 a1v; C2 a2v] ++ rest)
          /\ (bv_unsigned a1v mod 2^32 = le4val g3 g2 g1 g0)%Z /\ (bv_unsigned a2v = j1 + 256 * j0 + 65536 * j1)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 (Z_to_bv 64 (Bq + 8)) (Z_to_bv 64 (sxv g0 g1 g2 g3)) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 65280) x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x174c4) fc None mx (seg_rom ssegs)).
  Section Sz12.
  Variables ra' t0' t1' t2' x0 x1 a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx g0 g1 g2 g3 j0 j1 Bq pre rest : ltac2:(SecDiet.SzSec.tyM 'ngn_shb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_shb_swap__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R1 R2 SPW. pin_using (fun (BU LO P1 R1 R2 SPW : unit) => tt).
    intros GR HB MI B0 B64.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 6 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(Bq + 8, Bq + 14)]%Z mx) as MU. pose proof (wmono_refl ssegs mx) as WM.
    do 6 step.
    step. rewrite (zx16_lit (j0 + 256 * j1)) by lia.
    do 6 step.
    step. step.
    apply evt_done. cbv beta.
    lazymatch goal with HX : rw_cells ssegs ?mm Bq (CB 8 pre :: C4 ?w1 :: C2 ?w2 :: _) |- _ =>
      exists w1, w2; do 2 eexists; exists mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply swap32_sxv_mod32; assumption|].
    apply (swap16_val _ j0 j1); [assumption | assumption | apply unsigned_lit; lia].
  Qed.
  End Sz12.
  Lemma ngn_shb_swap : ltac:(let t := eval cbv delta [ngn_shb_swap__stmt] in ngn_shb_swap__stmt in exact t).
  Proof using BU LO P1 R1 R2 SPW. intros ra' t0' t1' t2' x0 x1 a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx g0 g1 g2 g3 j0 j1 Bq pre rest. ltac2:(SecDiet.SzSec.closeP 'ngn_shb_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ng_reset (sx : pcap_ng_sf) : pcap_ng_sf := mkNg (ng_user_tsresol sx) (ng_max_blocksize sx) 0 (ng_ifaces_size sx) [].

  Definition PCAPR_reset__stmt : Prop := forall (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr)
                             (m6 m7 : mem) (Afx B I : Z) (j : pcap_junk) (pad bs : list byte),
    GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6 ->
    In (f, Afx, FILE_BLOCK) FB ->
    pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix = pcap_blocks (pv bq alloc data eb sx ix) P B I ->
    rw_cells ssegs m7 P (pcap_cells (pv bq alloc data eb sx ix) P B Afx j) ->
    rw_cells ssegs m7 (P + 648) (ng_cells (ng_reset sx) I pad) ->
    rw_cells ssegs m7 B [CB (Z.to_nat alloc) bs] -> firstn (length data) bs = map b8 data ->
    ifaces_ok (pv bq alloc data eb sx ix) I m6 ->
    agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m6 m7 ->
    pcap_wf (pv bq alloc data eb sx ix) ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7.
  Section Sz13.
  Variables ps bq Bq Ix alloc data eb sx ix m6 m7 Afx B I j pad bs : ltac2:(SecDiet.SzSec.tyM 'PCAPR_reset__stmt "vvvvvvvvvvvvvvvvv" @ps).
  Lemma PCAPR_reset__body : ltac2:(SecDiet.SzSec.bodyP 'PCAPR_reset__stmt "vvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R1 R2 SPW. pin_using (fun (BU LO P1 R1 R2 SPW : unit) => tt).
    intros G Hin EPB CELLS PRIV BUF PFX IFS AG WF.
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G eq_refl) as [APB API].
    exists Afx. split; [exact Hin|]. exists B, I, j, pad, bs.
    split; [exact EPB|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [exact BUF|]. split; [exact PFX|].
    split.
    - unfold ifaces_ok in IFS |- *. unfold F_ngnextA.pv in IFS, API |- *. cbn [pc_priv] in IFS, API |- *. destruct ix as [q|].
      + destruct IFS as (js & tail & Ljs & CE & E1 & E2 & E3 & E4).
        rewrite <- (app_nil_r [CB (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx))) tail]), app_assoc in CE.
        apply (rw_cells_merge ssegs m6 I [] _ []) in CE. cbn [app] in CE. rewrite cells_size_app, ifs_cells_size in CE by (rewrite length_rev; lia).
        cbn [cells_size csize Nat.add] in CE. rewrite length_rev in CE.
        destruct (API sx q eq_refl) as [X1 X2]. unfold psize, is_ng in X1. cbn [pc_priv] in X1. unfold PCAP_NG_SF_TOTAL in X1.
        pose proof EPB as EPB'. unfold pcap_blocks, F_ngnextA.pv, psize, is_ng in EPB'. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB'.
        injection EPB' as EB EI.
        exists [], (cells_bytes (ifs_cells (rev (ng_ifaces sx)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx))) tail])).
        unfold ng_reset. cbn [ng_ifaces ng_ifcount ng_ifaces_size length rev ifs_cells app Z.of_nat].
        split; [reflexivity|]. split.
        * replace (Z.to_nat (40 * (ng_ifaces_size sx - 0))) with (40 * length (ng_ifaces sx) + (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx)) + 0))%nat by lia.
          eapply agrees_rw_cells; [exact AG | exact CE |]. intros a Ha. cbn [cells_size csize Nat.add outside] in Ha |- *. clear - Ha X1 E1 E2 E3 EI. lia.
        * split; [reflexivity|]. split; [lia|]. split; [lia| apply Forall_nil].
      + unfold ng_reset. cbn [ng_ifaces ng_ifcount ng_ifaces_size]. clear - IFS. tauto.
    - unfold pcap_wf, ng_reset, F_ngnextA.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv
           ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in WF |- *.
      clear - WF. lia.
  Qed.
  End Sz13.
  Lemma PCAPR_reset : ltac:(let t := eval cbv delta [PCAPR_reset__stmt] in PCAPR_reset__stmt in exact t).
  Proof using BU LO P1 R1 R2 SPW. intros ps bq Bq Ix alloc data eb sx ix m6 m7 Afx B I j pad bs. ltac2:(SecDiet.SzSec.closeP 'PCAPR_reset__body "vvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_shb_tail__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM ssegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' aw : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (16 <= rem)%Z ->
      ps_outfile ps = o -> (bv_unsigned aw mod 2^32 = get_le32 data 8)%Z ->
      implM ssegs (mbind (let bom := get_le32 data 8 in
                          if bom =? BYTE_ORDER_MAGIC then
                            let major := get_le16 data 12 in
                            if negb (major =? 1) then mret (inl (-1)%Z, set_errbuf (Msg.unknown_major major) (pv bq alloc data eb sx ix))
                            else LOOP (set_ng (ng_reset sx) ix (pv bq alloc data eb sx ix))
                          else if bom =? BYTE_ORDER_MAGIC_SWAPPED then mret (inl (-1)%Z, set_errbuf Msg.sections_byte_order (pv bq alloc data eb sx ix))
                          else mret (inl (-1)%Z, set_errbuf Msg.bad_byte_order_magic (pv bq alloc data eb sx ix))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (Bq + 8)) aw a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 65280) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x6 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) x10 (Z_to_bv 64 15)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17500) fc None m5 (seg_rom ssegs)).
  Section Sz14.
  Variables LOOP ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' aw m5 ps bq Bq Ix alloc rem data eb sx ix hcs dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_shb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_shb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros HLOOP ST5 FR5 Hccs MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM OF5 Haw.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
    unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnextA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold F_ngnextA.pv in Hin. cbn [pc_rfile] in Hin.
    unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    cbv zeta. rewrite (get_le32_q8 data 8) in Haw |- * by lia. rewrite (get_le16_q8' data 12) by lia.
    name_field data 8%Z b0 b1 b2 b3 DRNG.
    set (k0 := q8 data 12 0) in *. set (k1 := q8 data 12 1) in *.
    pose proof (q8_range data 12 0 DRNG ltac:(lia)) as Rk0. pose proof (q8_range data 12 1 DRNG ltac:(lia)) as Rk1. fold k0 in Rk0. fold k1 in Rk1.
    pose proof BUF as BUF0.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 2; Z.to_nat alloc - 14]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (firstn4_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
    fold b0 b1 b2 b3 k0 k1 in BUF.
    assert (BUF4 : rw_cells ssegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val b0 b1 b2 b3)); C2 (Z_to_bv 64 (k0 + 256 * k1)); CB (Z.to_nat alloc - 14) (firstn (Z.to_nat alloc - 14) (skipn 14 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit b0 b1 b2 b3), (le2_lit k0 k1) by lia. reflexivity. }
    clear BUF.
    pose proof PRIV as PRIVJ. unfold priv_cells, F_ngnextA.pv, PCAP_PRIV_OFF in PRIVJ. cbn [pc_priv] in PRIVJ. unfold ng_cells in PRIVJ.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame in FRJ. cbn [app] in FRJ.
    pose proof (sxu_range' (le4val b0 b1 b2 b3) ltac:(unfold le4val; lia)) as SR. pose proof (sxu_range (le4val b0 b1 b2 b3) ltac:(unfold le4val; lia)) as (_ & SX2 & SX3).
    hide FR5. hide CELLS. hide PRIV. hide IFS. hide HH. hide HD. hide BUF0.
    pose proof (munch_refl [(P + 660, P + 664)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. rewrite (sextw_word aw (le4val b0 b1 b2 b3) Haw).
    step. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      assert (NB : le4val b0 b1 b2 b3 <> 439041101%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR by lia; lia | lia]).
      unfold BYTE_ORDER_MAGIC. replace (le4val b0 b1 b2 b3 =? 439041101) with false by (symmetry; apply Z.eqb_neq; exact NB). cbv iota.
      step. step.
      step. if_cases BR3; zify_cond BR3; rewrite ?unsigned_lit in BR3 by lia.
      + (* [comment removed for export] *)
        assert (NS : le4val b0 b1 b2 b3 <> 1295788826%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR3 by lia; lia | lia]).
        unfold BYTE_ORDER_MAGIC_SWAPPED. replace (le4val b0 b1 b2 b3 =? 1295788826) with false by (symmetry; apply Z.eqb_neq; exact NS). cbv iota.
        step. step. step.
        unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
        assert (SRC : bytes_at ssegs m5 0x10b82 (str_bytes "the file has a section with a bad byte order magic field"))
          by (apply str_at_intro; [exact MI5 | vm_compute; reflexivity | lia | cbn; lia]).
        apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
        eapply ngn_mcp; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | | exact SRC | rewrite str_bytes_length; reflexivity | lia | lia].
        split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
        split; [exact HD|]. split; [exact Hd| exact OF5].
      + (* [comment removed for export] *)
        assert (ES : le4val b0 b1 b2 b3 = 1295788826%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR3 by lia; lia | specialize (SX3 ltac:(lia)); lia]).
        unfold BYTE_ORDER_MAGIC_SWAPPED. replace (le4val b0 b1 b2 b3 =? 1295788826) with true by (symmetry; apply Z.eqb_eq; exact ES). cbv iota.
        step. step. step. step.
        unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
        assert (SRC : bytes_at ssegs m5 0x109c7 (str_bytes "the file has sections with different byte orders"))
          by (apply str_at_intro; [exact MI5 | vm_compute; reflexivity | lia | cbn; lia]).
        apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
        eapply ngn_mcp; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | | exact SRC | rewrite str_bytes_length; reflexivity | lia | lia].
        split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
        split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      assert (EB : le4val b0 b1 b2 b3 = 439041101%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR by lia; lia | specialize (SX3 ltac:(lia)); lia]).
      unfold BYTE_ORDER_MAGIC. replace (le4val b0 b1 b2 b3 =? 439041101) with true by (symmetry; apply Z.eqb_eq; exact EB). cbv iota. cbv zeta.
      step. rewrite (zx16_lit (k0 + 256 * k1)) by lia.
      step. if_cases BR2; zify_cond BR2; rewrite ?unsigned_lit in BR2 by lia.
      + (* [comment removed for export] *)
        replace (k0 + 256 * k1 =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
        step. step.
        unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
        assert (MSG : fmt_at m5 NGN_FMT_MAJOR "unknown pcapng savefile major version number %u"%string)
          by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_MAJOR; lia | unfold NGN_FMT_MAJOR; cbn; lia]).
        unfold NGN_FMT_MAJOR in MSG.
        apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
        eapply ngn_snp8c with (args := [AInt (k0 + 256 * k1)%Z]);
          [exact ST5 | exact FR5 | exact Hccs | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
        split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
        split; [exact HD|]. split; [exact Hd| exact OF5].
      + (* [comment removed for export] *)
        replace (k0 + 256 * k1 =? 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
        step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m6 end.
        unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; unfold F_ngnextA.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 R1; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 R1 R2; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in CELLS; [| intros a Ha; rewrite pcap_cells_gen_size in Ha by reflexivity; cbn [outside]; clear - Ha; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in BUF0; [| intros a Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; clear - Ha APB W4 LEN REM; lia].
        assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil].
          right. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, F_ngnextA.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
        assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
        { lazymatch goal with PRIV7 : rw_cells ssegs m6 (P + 648) _ |- _ =>
            eapply (PCAPR_reset ps bq Bq Ix alloc data eb sx ix m5 m6 Afx Bq Ix' jx' padx bsx');
              [exact G5 | exact Hin | exact EPB | exact CELLS | exact PRIV7 | exact BUF0 | exact PFX | exact IFS | exact AGP | exact WF] end. }
        assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia|].
          destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [| exact Logic.I].
          intros Hr. apply Hnb. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, F_ngnextA.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
        assert (G6' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb (ng_reset sx) ix) P Bq Ix) FB m6) by exact G6.
        assert (PC6' : PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb (ng_reset sx) ix) P Bq Ix) FB m6) by exact PC6.
        apply evt_done.
        change (set_ng (ng_reset sx) ix (pv bq alloc data eb sx ix)) with (pv bq alloc data eb (ng_reset sx) ix).
        unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head in HLOOP. unfold NGN_LOOP in HLOOP.
        eapply HLOOP; [exact ST5 | exact FR5 | exact Hccs | assumption | exact G6' | exact PC6' | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact OF5].
  Qed.
  End Sz14.
  Lemma ngn_shb_tail : ltac:(let t := eval cbv delta [ngn_shb_tail__stmt] in ngn_shb_tail__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP. intros LOOP HLOOP ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' aw m5 ps bq Bq Ix alloc rem data eb sx ix hcs dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_shb_tail__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_shb__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM ssegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (mbind (ngn_shbK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 (Z_to_bv 64 65280) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x6 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) x10 (Z_to_bv 64 15)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17498) fc None m5 (seg_rom ssegs)).
  Section Sz15.
  Variables LOOP ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_shb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_shb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros HLOOP ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_shbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step.
    step. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 16) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 168627466);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      replace (rem <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
      pose proof G5 as G5e. rewrite EPB in G5e.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
      pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
      pose proof WF as (W1' & _ & W3 & W4 & _).
      unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
      unfold PCAP_NG_SF_TOTAL in APB.
      unfold F_ngnextA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnextA.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      name_field data 8%Z g0 g1 g2 g3 DRNG.
      set (j0 := q8 data 12 0) in *. set (j1 := q8 data 12 1) in *.
      pose proof (q8_range data 12 0 DRNG ltac:(lia)) as Rj0. pose proof (q8_range data 12 1 DRNG ltac:(lia)) as Rj1. fold j0 in Rj0. fold j1 in Rj1.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 2; Z.to_nat alloc - 14]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (firstn4_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
      fold g0 g1 g2 g3 j0 j1 in BUF.
      replace (firstn (Z.to_nat alloc - 14) (skipn 14 bsx')) with (skipn 14 bsx') in BUF by (symmetry; apply firstn_all2; rewrite length_skipn; lia).
      assert (BUF4 : rw_cells ssegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C2 (Z_to_bv 64 (j0 + 256 * j1)); CB (Z.to_nat alloc - 14) (skipn 14 bsx')]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le4_lit g0 g1 g2 g3), (le2_lit j0 j1) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS.
      (* [comment removed for export] *)
      step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        rename mm into m6 end.
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; clear - Ha R1; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R1 R2; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in PRIV; [| intros a Ha; pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ; unfold psize, is_ng, F_ngnextA.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha; cbn [pc_priv] in PZ, Ha; unfold PCAP_NG_SF_TOTAL in PZ; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha PZ LO BU SPW P4; lia].
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. clear - LO BU SPM; lia. }
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. gio_ceil_fact; clear -CLO__ H0 LO BU SPW; lia. }
      assert (IFS6 : ifaces_ok (pv bq alloc data eb sx ix) Ix' m6).
      { eapply ifaces_ok_agree; [exact AGF | | exact IFS]. intros sg q Hq a Ha. unfold F_ngnextA.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
        destruct (API sx q eq_refl) as [X1 X2].
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
        cbn [outside]. gio_ceil_fact; clear -CLO__ Ha I1 I4 LO BU SPW. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGF|]. intros a [[Ha|Ha] _]; cbn [outside]; [clear - Ha; lia|].
        destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. gio_ceil_fact; clear -CLO__ Hc LO BU SPW. lia. }
      clear MU WM AGF G5 PC5 AG5 IFS G5e.
      step. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. clear -BRZ K1 K3 K4. lia. }
      step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      step. rewrite (sx32_lit g0 g1 g2 g3) by lia.
      (* [comment removed for export] *)
      lazymatch goal with FRX : rw_cells ssegs m6 (bv_unsigned sp + -160) (_ :: _ :: _ :: _ :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: _) |- _ =>
        assert (FR6 : rw_cells ssegs m6 (bv_unsigned sp + -160) (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [c1; c2; c3; c4])) by exact FRX end.
      step. if_cases BRS; zify_cond BRS.
      + (* [comment removed for export] *)
        assert (SW : swapped = false) by (destruct swapped; [| reflexivity]; exfalso; revert BRS; rewrite ?unsigned_lit by (cbn; lia); cbn; lia).
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with Y by (rewrite SW; reflexivity) end.
        cbv zeta.
        change (ng_of (pv bq alloc data eb sx ix)) with sx. change (ng_ifaces_ptr_of (pv bq alloc data eb sx ix)) with ix.
        change (pc_bufdata (pv bq alloc data eb sx ix)) with data. fold (ng_reset sx).
        apply evt_done.
        eapply (ngn_shb_tail LOOP HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (sxv g0 g1 g2 g3)) m6 ps bq Bq Ix alloc rem data eb sx ix hcs dw dj);
          [assumption | exact FR6 | reflexivity | assumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG
          | exact LEN | exact L30 | clear - BR0; lia | exact OF5 | rewrite (get_le32_q8 data 8) by lia; fold g0 g1 g2 g3; rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply sxv_mod32; lia].
      + (* [comment removed for export] *)
        assert (SW : swapped = true) by (destruct swapped; [reflexivity|]; exfalso; revert BRS; rewrite ?unsigned_lit by (cbn; lia); cbn; lia).
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with X by (rewrite SW; reflexivity) end.
        cbv zeta.
        change (set_bufdata (swap_field 2 (8 + 4) (swap_field 4 8 data)) (pv bq alloc data eb sx ix)) with (pv bq alloc (swap_field 2 (8 + 4) (swap_field 4 8 data)) eb sx ix).
        change (8 + 4)%Z with 12%Z. rewrite (shb_swap_data' data) by lia. fold g0 g1 g2 g3 j0 j1.
        set (data' := firstn 8 data ++ [g3; g2; g1; g0; j1; j0] ++ skipn 14 data).
        change (ng_of (pv bq alloc data' eb sx ix)) with sx. change (ng_ifaces_ptr_of (pv bq alloc data' eb sx ix)) with ix.
        change (pc_bufdata (pv bq alloc data' eb sx ix)) with data'. fold (ng_reset sx).
        hide FR6. hide HH. hide HD. hide PRIV. hide CELLS.
        eapply evt_cut.
        { eapply (ngn_shb_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 g0 g1 g2 g3 j0 j1 Bq);
            [repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF4 | assumption | clear - K1; lia | clear - K4 W4 LEN REM BR0; lia]. }
        cbv beta. intros ms' (a1v & a2v & a3v & a4v & m7 & -> & MU7 & WM7 & MI7 & HB7 & E1 & E2).
        assert (AGP : agrees_on (fun a => outside [(Bq + 8, Bq + 14)]%Z a) m6 m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
        unhide FR6. unhide HH. unhide HD. unhide PRIV. unhide CELLS.
        lazymatch goal with STX : stk ssegs m6 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP STX ltac:(intros a Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia)) as ST7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold F_ngnextA.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW R1 W4 LEN REM BR0; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW R1 R2 W4 LEN REM BR0; lia].
        assert (G7 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU7 | exact WM7 |]. apply Forall_cons; [| apply Forall_nil].
          right. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnextA.pv]. clear - W4 LEN REM BR0; lia. }
        (* [comment removed for export] *)
        assert (BUF7 : rw_cells ssegs m7 Bq [CB (Z.to_nat alloc) (firstn 8 bsx' ++ [b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx')]).
        { assert (R7 : rw_cells ssegs m7 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C2 (Z_to_bv 64 (j1 + 256 * j0)); CB (Z.to_nat alloc - 14) (skipn 14 bsx')]).
          { eapply rw_cells_recell; [exact HB7 | | ].
            { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
            cbn [cells_bytes cbytes app]. rewrite (le4_word_mod32 a1v (le4val g3 g2 g1 g0) E1), (le2_of_val a2v j1 j0 j1) by lia. rewrite (le4_lit g3 g2 g1 g0), (le2_lit j1 j0) by lia. reflexivity. }
          pose proof (rw_cells_merge ssegs m7 Bq [] _ [] ltac:(rewrite app_nil_r; exact R7)) as R8.
          lazymatch type of R8 with rw_cells _ _ _ ([] ++ [CB ?n ?bs]) =>
            replace n with (Z.to_nat alloc) in R8 by (cbn [cells_size csize]; clear - W4 LEN REM BR0; lia);
            cbn [app cells_bytes cbytes] in R8 end.
          rewrite (le4_lit g3 g2 g1 g0), (le2_lit j1 j0), app_nil_r in R8 by lia. exact R8. }
        assert (LEN' : length data' = length data).
        { subst data'. change (skipn 14 data) with (skipn (8 + length [g3; g2; g1; g0; j1; j0]) data). apply splice_length. cbn [length]. clear - LEN REM BR0; lia. }
        assert (PFX7 : firstn (length data') (firstn 8 bsx' ++ [b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx') = map b8 data').
        { subst data'. change ([b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx') with (map b8 [g3; g2; g1; g0; j1; j0] ++ skipn (8 + length [g3; g2; g1; g0; j1; j0]) bsx').
          change ([g3; g2; g1; g0; j1; j0] ++ skipn 14 data) with ([g3; g2; g1; g0; j1; j0] ++ skipn (8 + length [g3; g2; g1; g0; j1; j0]) data).
          apply splice_pfx; [exact PFX | cbn [length]; clear - LEN REM BR0; lia | clear - LBS W4; lia]. }
        assert (HQ7 : forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> outside [(Bq + 8, Bq + 14)]%Z a) by (intros a _ Hn; cbn [outside]; clear - Hn W4 LEN REM BR0; lia).
        pose proof (PCAPR_bufdata ps bq Bq Ix alloc data data' eb sx ix m6 m7 _ _ G6 PC6 AGP HQ7 BUF7 PFX7 LEN') as PC7.
        assert (G7' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m7) by exact G7.
        assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia|].
          destruct (ngn_CLc_facts _ _ _ _ G6 Ha) as [Hc Hnb]. split; [| exact Logic.I].
          intros Hr. apply Hnb. unfold pcap_blocks, in_block. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnextA.pv]. clear - Hr W4 LEN REM BR0; lia. }
        assert (DRNG' : Forall (fun x => 0 <= x < 256)%Z data').
        { subst data'. change (skipn 14 data) with (skipn (8 + length [g3; g2; g1; g0; j1; j0]) data). apply splice_Forall; [exact DRNG|].
          repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
        apply evt_done.
        eapply (ngn_shb_tail LOOP HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1v m7 ps bq Bq Ix alloc rem data' eb sx ix hcs dw dj);
          [exact ST7 | exact FR6 | reflexivity | exact MI7 | exact G7' | exact PC7 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG'
          | rewrite LEN'; exact LEN | exact L30 | clear - BR0; lia | exact OF5 | rewrite E1; subst data'; symmetry; apply shb_splice_le32; clear - LEN REM BR0; lia].
  Qed.
  End Sz15.
  Lemma ngn_shb : ltac:(let t := eval cbv delta [ngn_shb__stmt] in ngn_shb__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP. intros LOOP HLOOP ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_shb__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require NgnPure.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.NgnPure. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
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

Local Close Scope bv_scope.
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma str_at_intro : forall m A (s : string),
  mem_inv usegs m -> ro_bytes_b usegs A (str_bytes s) = true ->
  0x10000 <= A -> A + Z.of_nat (String.length s) + 1 <= 0x13000 -> bytes_at usegs m A (str_bytes s).
Proof using Type. pin_using tt.
  intros m A s MI RO LO HI.
  pose proof (ro_cells_image usegs m A _ MI RO ltac:(lia)) as X. rewrite str_bytes_length in X.
  pose proof (ro_cells_bytes_at _ _ _ _ (X ltac:(lia))) as Y. cbn [cells_bytes cbytes] in Y. rewrite app_nil_r in Y. exact Y.
Qed.
End WithCeil.


Local Open Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_ngnextA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (S3.F_ngnextA.TwB.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (S3.F_ngnextA.TwB.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (S3.F_ngnextA.TwB.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (S3.F_ngnextA.TwB.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (S3.F_ngnextA.TwB.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (S3.F_ngnextA.TwB.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (S3.F_ngnextA.TwB.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (S3.F_ngnextA.TwB.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (S3.F_ngnextA.TwB.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (S3.F_ngnextA.TwB.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (S3.F_ngnextA.TwB.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold S3.F_ngnextA.TwB.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold S3.F_ngnextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ccells := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells ).
  #[local] Abbreviation ngn_spb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_spb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_epb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_epb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_pb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).


  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  #[local] Abbreviation ngn_KF := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_shbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_shbK (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_idbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_idbK HO sites).
  #[local] Abbreviation ngn_head := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_too_short := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_too_short K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation PCAPR_bufdata := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.PCAPR_bufdata K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU ALN R1 R2 AH AD SPW P1 P5).
  #[local] Abbreviation get_le16_q8' := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.get_le16_q8' ).
  #[local] Abbreviation firstn2_q8 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.firstn2_q8 sp R lo P HA DA LO BU R1 R2 SPW P1).
  #[local] Abbreviation bswap16_2 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.bswap16_2 sp P HA DA).

  Ltac name_field data off a b c d DRNG :=
    set (a := q8 data off 0%Z) in *; set (b := q8 data off 1%Z) in *; set (c := q8 data off 2%Z) in *; set (d := q8 data off 3%Z) in *;
    let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
    pose proof (q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
    pose proof (q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
    fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

  (* [comment removed for export] *)
  Definition ngn_snp90__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (p' : pcapT) (PB' : list (cblock (hptr:=hptr))) (e : list Z) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_finalC m5 ps PB' p' hcs dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -160) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implM usegs (mret ((-1)%Z, hdr0, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17d28) fc None m5 (seg_rom usegs)).
  Section Sz2.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps p' PB' e hcs dw dj ccs FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'ngn_snp90__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_snp90__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_snp90__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
 intros ST5 FR5 Hccs MI5 FIN FMT FOK LA FW.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof FIN as (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD. hide FMT. hide FW.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. step. unhide FR5. unhide HH. unhide HD. unhide FMT. unhide FW.
    apply evt_done.
    eapply ngn_snp; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact FMT | exact FOK | exact LA | exact FW].
  Qed.
  End Sz2.
  Lemma ngn_snp90 : ltac:(let t := eval cbv delta [ngn_snp90__stmt] in ngn_snp90__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps p' PB' e hcs dw dj ccs FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'ngn_snp90__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition ngn_snp8c__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (p' : pcapT) (PB' : list (cblock (hptr:=hptr))) (e : list Z) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_finalC m5 ps PB' p' hcs dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -160) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implM usegs (mret ((-1)%Z, hdr0, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17d24) fc None m5 (seg_rom usegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps p' PB' e hcs dw dj ccs FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'ngn_snp8c__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_snp8c__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_snp8c__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
 intros ST5 FR5 Hccs MI5 FIN FMT FOK LA FW.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof FIN as (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD. hide FMT. hide FW.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. unhide FR5. unhide HH. unhide HD. unhide FMT. unhide FW.
    apply evt_done.
    eapply ngn_snp90; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact FMT | exact FOK | exact LA | exact FW].
  Qed.
  End Sz3.
  Lemma ngn_snp8c : ltac:(let t := eval cbv delta [ngn_snp8c__stmt] in ngn_snp8c__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. intros ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps p' PB' e hcs dw dj ccs FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'ngn_snp8c__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_shb_swap__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a1' a2' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (mx : mem)
           (g0 g1 g2 g3 j0 j1 : Z) (Bq : Z) (pre : list byte) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; j0; j1] ->
      rw_cells usegs mx Bq ([CB 8 pre; C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C2 (Z_to_bv 64 (j0 + 256 * j1))] ++ rest) ->
      mem_inv usegs mx -> (0 <= Bq)%Z -> (Bq + 14 <= 2^64)%Z ->
      evt usegs (fun ms' => exists (a1v a2v a3v a4v : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 (Z_to_bv 64 (Bq + 8)) a1v a2v a3v a4v a5' a6' a7'
                       x2 x3 (Z_to_bv 64 65280) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17c1c) fc None m' (seg_rom usegs)
          /\ munch [(Bq + 8, Bq + 14)]%Z mx m' /\ wmono usegs mx m' /\ mem_inv usegs m'
          /\ rw_cells usegs m' Bq ([CB 8 pre; C4 a1v; C2 a2v] ++ rest)
          /\ (bv_unsigned a1v mod 2^32 = le4val g3 g2 g1 g0)%Z /\ (bv_unsigned a2v = j1 + 256 * j0 + 65536 * j1)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 (Z_to_bv 64 (Bq + 8)) a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 65280) x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17b00) fc None mx (seg_rom usegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' x0 x1 a1' a2' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx g0 g1 g2 g3 j0 j1 Bq pre rest : ltac2:(SecDiet.SzSec.tyM 'ngn_shb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_shb_swap__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R1 R2 SPW. pin_using (fun (BU LO P1 R1 R2 SPW : unit) => tt).
 intros GR HB MI B0 B64.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 6 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(Bq + 8, Bq + 14)]%Z mx) as MU. pose proof (wmono_refl usegs mx) as WM.
    step. rewrite (sx32_lit g0 g1 g2 g3) by lia.
    step. rewrite (zx16_lit (j0 + 256 * j1)) by lia.
    do 12 step.
    step. step. step.
    apply evt_done. cbv beta.
    lazymatch goal with HX : rw_cells usegs ?mm Bq (CB 8 pre :: C4 ?w1 :: C2 ?w2 :: _) |- _ =>
      exists w1, w2; do 2 eexists; exists mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply swap32_sxv_mod32; assumption|].
    apply (swap16_val _ j0 j1); [assumption | assumption | apply unsigned_lit; lia].
  Qed.
  End Sz4.
  Lemma ngn_shb_swap : ltac:(let t := eval cbv delta [ngn_shb_swap__stmt] in ngn_shb_swap__stmt in exact t).
  Proof using BU LO P1 R1 R2 SPW. intros ra' t0' t1' t2' x0 x1 a1' a2' a3' a4' a5' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx g0 g1 g2 g3 j0 j1 Bq pre rest. ltac2:(SecDiet.SzSec.closeP 'ngn_shb_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ng_reset (sx : pcap_ng_sf) : pcap_ng_sf := mkNg (ng_user_tsresol sx) (ng_max_blocksize sx) 0 (ng_ifaces_size sx) [].

  Definition PCAPR_reset__stmt : Prop := forall (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr)
                             (m6 m7 : mem) (Afx B I : Z) (j : pcap_junk) (pad bs : list byte),
    GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6 ->
    In (f, Afx, FILE_BLOCK) FB ->
    pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix = pcap_blocks (pv bq alloc data eb sx ix) P B I ->
    rw_cells usegs m7 P (pcap_cells (pv bq alloc data eb sx ix) P B Afx j) ->
    rw_cells usegs m7 (P + 648) (ng_cells (ng_reset sx) I pad) ->
    rw_cells usegs m7 B [CB (Z.to_nat alloc) bs] -> firstn (length data) bs = map b8 data ->
    ifaces_ok (pv bq alloc data eb sx ix) I m6 ->
    agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m6 m7 ->
    pcap_wf (pv bq alloc data eb sx ix) ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7.
  Section Sz5.
  Variables ps bq Bq Ix alloc data eb sx ix m6 m7 Afx B I j pad bs : ltac2:(SecDiet.SzSec.tyM 'PCAPR_reset__stmt "vvvvvvvvvvvvvvvvv" @ps).
  Lemma PCAPR_reset__body : ltac2:(SecDiet.SzSec.bodyP 'PCAPR_reset__stmt "vvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R1 R2 SPW. pin_using (fun (BU LO P1 R1 R2 SPW : unit) => tt).
    intros G Hin EPB CELLS PRIV BUF PFX IFS AG WF.
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G eq_refl) as [APB API].
    exists Afx. split; [exact Hin|]. exists B, I, j, pad, bs.
    split; [exact EPB|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [exact BUF|]. split; [exact PFX|].
    split.
    - unfold ifaces_ok in IFS |- *. unfold S3.F_ngnextA.TwB.pv in IFS, API |- *. cbn [pc_priv] in IFS, API |- *. destruct ix as [q|].
      + destruct IFS as (js & tail & Ljs & CE & E1 & E2 & E3 & E4).
        rewrite <- (app_nil_r [CB (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx))) tail]), app_assoc in CE.
        apply (rw_cells_merge usegs m6 I [] _ []) in CE. cbn [app] in CE. rewrite cells_size_app, ifs_cells_size in CE by (rewrite length_rev; lia).
        cbn [cells_size csize Nat.add] in CE. rewrite length_rev in CE.
        destruct (API sx q eq_refl) as [X1 X2]. unfold psize, is_ng in X1. cbn [pc_priv] in X1. unfold PCAP_NG_SF_TOTAL in X1.
        pose proof EPB as EPB'. unfold pcap_blocks, S3.F_ngnextA.TwB.pv, psize, is_ng in EPB'. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB'.
        injection EPB' as EB EI.
        exists [], (cells_bytes (ifs_cells (rev (ng_ifaces sx)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx))) tail])).
        unfold ng_reset. cbn [ng_ifaces ng_ifcount ng_ifaces_size length rev ifs_cells app Z.of_nat].
        split; [reflexivity|]. split.
        * replace (Z.to_nat (40 * (ng_ifaces_size sx - 0))) with (40 * length (ng_ifaces sx) + (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx)) + 0))%nat by lia.
          eapply agrees_rw_cells; [exact AG | exact CE |]. intros a Ha. cbn [cells_size csize Nat.add outside] in Ha |- *. clear - Ha X1 E1 E2 E3 EI. lia.
        * split; [reflexivity|]. split; [lia|]. split; [lia| apply Forall_nil].
      + unfold ng_reset. cbn [ng_ifaces ng_ifcount ng_ifaces_size]. clear - IFS. tauto.
    - unfold pcap_wf, ng_reset, S3.F_ngnextA.TwB.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv
           ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in WF |- *.
      clear - WF. lia.
  Qed.
  End Sz5.
  Lemma PCAPR_reset : ltac:(let t := eval cbv delta [PCAPR_reset__stmt] in PCAPR_reset__stmt in exact t).
  Proof using BU LO P1 R1 R2 SPW. intros ps bq Bq Ix alloc data eb sx ix m6 m7 Afx B I j pad bs. ltac2:(SecDiet.SzSec.closeP 'PCAPR_reset__body "vvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_shb_tail__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM usegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (hcs : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (16 <= rem)%Z ->
      ps_outfile ps = o ->
      implM usegs (mbind (let bom := get_le32 data 8 in
                          if bom =? BYTE_ORDER_MAGIC then
                            let major := get_le16 data 12 in
                            if negb (major =? 1) then mret (inl (-1)%Z, set_errbuf (Msg.unknown_major major) (pv bq alloc data eb sx ix))
                            else LOOP (set_ng (ng_reset sx) ix (pv bq alloc data eb sx ix))
                          else if bom =? BYTE_ORDER_MAGIC_SWAPPED then mret (inl (-1)%Z, set_errbuf Msg.sections_byte_order (pv bq alloc data eb sx ix))
                          else mret (inl (-1)%Z, set_errbuf Msg.bad_byte_order_magic (pv bq alloc data eb sx ix))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (Bq + 8)) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 65280) (Z_to_bv 64 Af) x6 x7 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 168627466)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17c1c) fc None m5 (seg_rom usegs)).
  Section Sz6.
  Variables LOOP ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix hcs dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_shb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_shb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros HLOOP.
 intros ST5 FR5 Hccs MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
    unfold PCAP_NG_SF_TOTAL in APB.
    unfold S3.F_ngnextA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold S3.F_ngnextA.TwB.pv in Hin. cbn [pc_rfile] in Hin.
    unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    cbv zeta. rewrite (get_le32_q8 data 8) by lia. rewrite (get_le16_q8' data 12) by lia.
    name_field data 8%Z b0 b1 b2 b3 DRNG.
    set (k0 := q8 data 12 0) in *. set (k1 := q8 data 12 1) in *.
    pose proof (q8_range data 12 0 DRNG ltac:(lia)) as Rk0. pose proof (q8_range data 12 1 DRNG ltac:(lia)) as Rk1. fold k0 in Rk0. fold k1 in Rk1.
    pose proof BUF as BUF0.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 2; Z.to_nat alloc - 14]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (firstn4_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
    fold b0 b1 b2 b3 k0 k1 in BUF.
    assert (BUF4 : rw_cells usegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val b0 b1 b2 b3)); C2 (Z_to_bv 64 (k0 + 256 * k1)); CB (Z.to_nat alloc - 14) (firstn (Z.to_nat alloc - 14) (skipn 14 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit b0 b1 b2 b3), (le2_lit k0 k1) by lia. reflexivity. }
    clear BUF.
    pose proof PRIV as PRIVJ. unfold priv_cells, S3.F_ngnextA.TwB.pv, PCAP_PRIV_OFF in PRIVJ. cbn [pc_priv] in PRIVJ. unfold ng_cells in PRIVJ.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ. cbn [app] in FRJ.
    pose proof (sxu_range' (le4val b0 b1 b2 b3) ltac:(unfold le4val; lia)) as SR. pose proof (sxu_range (le4val b0 b1 b2 b3) ltac:(unfold le4val; lia)) as (_ & SX2 & SX3).
    hide FR5. hide CELLS. hide PRIV. hide IFS. hide HH. hide HD. hide BUF0.
    pose proof (munch_refl [(P + 660, P + 664)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. rewrite (sx32_lit b0 b1 b2 b3) by lia. rewrite (sxv_sxu b0 b1 b2 b3) by lia.
    step. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      assert (NB : le4val b0 b1 b2 b3 <> 439041101%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR by lia; lia | lia]).
      unfold BYTE_ORDER_MAGIC. replace (le4val b0 b1 b2 b3 =? 439041101) with false by (symmetry; apply Z.eqb_neq; exact NB). cbv iota.
      step. step.
      step. if_cases BR3; zify_cond BR3; rewrite ?unsigned_lit in BR3 by lia.
      + (* [comment removed for export] *)
        assert (NS : le4val b0 b1 b2 b3 <> 1295788826%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR3 by lia; lia | lia]).
        unfold BYTE_ORDER_MAGIC_SWAPPED. replace (le4val b0 b1 b2 b3 =? 1295788826) with false by (symmetry; apply Z.eqb_neq; exact NS). cbv iota.
        step. step. step.
        unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
        assert (SRC : bytes_at usegs m5 0x10b82 (str_bytes "the file has a section with a bad byte order magic field"))
          by (apply str_at_intro; [exact MI5 | vm_compute; reflexivity | lia | cbn; lia]).
        apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF.
        eapply ngn_mcp; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | | exact SRC | rewrite str_bytes_length; reflexivity | lia | lia].
        split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
        split; [exact HD|]. split; [exact Hd| exact OF5].
      + (* [comment removed for export] *)
        assert (ES : le4val b0 b1 b2 b3 = 1295788826%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR3 by lia; lia | specialize (SX3 ltac:(lia)); lia]).
        unfold BYTE_ORDER_MAGIC_SWAPPED. replace (le4val b0 b1 b2 b3 =? 1295788826) with true by (symmetry; apply Z.eqb_eq; exact ES). cbv iota.
        step. step. step. step.
        unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
        assert (SRC : bytes_at usegs m5 0x109c7 (str_bytes "the file has sections with different byte orders"))
          by (apply str_at_intro; [exact MI5 | vm_compute; reflexivity | lia | cbn; lia]).
        apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF.
        eapply ngn_mcp; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | | exact SRC | rewrite str_bytes_length; reflexivity | lia | lia].
        split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
        split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      assert (EB : le4val b0 b1 b2 b3 = 439041101%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR by lia; lia | specialize (SX3 ltac:(lia)); lia]).
      unfold BYTE_ORDER_MAGIC. replace (le4val b0 b1 b2 b3 =? 439041101) with true by (symmetry; apply Z.eqb_eq; exact EB). cbv iota. cbv zeta.
      step. rewrite (zx16_lit (k0 + 256 * k1)) by lia.
      step. if_cases BR2; zify_cond BR2; rewrite ?unsigned_lit in BR2 by lia.
      + (* [comment removed for export] *)
        replace (k0 + 256 * k1 =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
        step. step.
        unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
        assert (MSG : fmt_at m5 NGN_FMT_MAJOR "unknown pcapng savefile major version number %u"%string)
          by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_MAJOR; lia | unfold NGN_FMT_MAJOR; cbn; lia]).
        unfold NGN_FMT_MAJOR in MSG.
        apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF.
        eapply ngn_snp8c with (args := [AInt (k0 + 256 * k1)%Z]);
          [exact ST5 | exact FR5 | exact Hccs | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
        split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
        split; [exact HD|]. split; [exact Hd| exact OF5].
      + (* [comment removed for export] *)
        replace (k0 + 256 * k1 =? 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
        step. if_false. step. pstep. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m6 end.
        unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; unfold S3.F_ngnextA.TwB.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 R1; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 R1 R2; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in CELLS; [| intros a Ha; rewrite pcap_cells_gen_size in Ha by reflexivity; cbn [outside]; clear - Ha; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in BUF0; [| intros a Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; clear - Ha APB W4 LEN REM; lia].
        assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil].
          right. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, S3.F_ngnextA.TwB.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
        assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
        { lazymatch goal with PRIV7 : rw_cells usegs m6 (P + 648) _ |- _ =>
            eapply (PCAPR_reset ps bq Bq Ix alloc data eb sx ix m5 m6 Afx Bq Ix' jx' padx bsx');
              [exact G5 | exact Hin | exact EPB | exact CELLS | exact PRIV7 | exact BUF0 | exact PFX | exact IFS | exact AGP | exact WF] end. }
        assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia|].
          destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [| exact Logic.I].
          intros Hr. apply Hnb. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, S3.F_ngnextA.TwB.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
        assert (G6' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb (ng_reset sx) ix) P Bq Ix) FB m6) by exact G6.
        assert (PC6' : PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb (ng_reset sx) ix) P Bq Ix) FB m6) by exact PC6.
        apply evt_done.
        change (set_ng (ng_reset sx) ix (pv bq alloc data eb sx ix)) with (pv bq alloc data eb (ng_reset sx) ix).
        unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head in HLOOP. unfold NGN_LOOP in HLOOP.
        eapply HLOOP; [exact ST5 | exact FR5 | exact Hccs | assumption | exact G6' | exact PC6' | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact OF5].
  Qed.
  End Sz6.
  Lemma ngn_shb_tail : ltac:(let t := eval cbv delta [ngn_shb_tail__stmt] in ngn_shb_tail__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP. intros LOOP HLOOP ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix hcs dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_shb_tail__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_shb__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM usegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (mbind (ngn_shbK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 65280) (Z_to_bv 64 Af) x6 x7 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 168627466)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17ac4) fc None m5 (seg_rom usegs)).
  Section Sz7.
  Variables LOOP ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_shb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_shb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_shb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros HLOOP.
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_shbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. step.
    step. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 16) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 168627466);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      replace (rem <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
      pose proof G5 as G5e. rewrite EPB in G5e.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
      pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
      pose proof WF as (W1' & _ & W3 & W4 & _).
      unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
      unfold PCAP_NG_SF_TOTAL in APB.
      unfold S3.F_ngnextA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, S3.F_ngnextA.TwB.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      name_field data 8%Z g0 g1 g2 g3 DRNG.
      set (j0 := q8 data 12 0) in *. set (j1 := q8 data 12 1) in *.
      pose proof (q8_range data 12 0 DRNG ltac:(lia)) as Rj0. pose proof (q8_range data 12 1 DRNG ltac:(lia)) as Rj1. fold j0 in Rj0. fold j1 in Rj1.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 2; Z.to_nat alloc - 14]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (firstn4_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
      fold g0 g1 g2 g3 j0 j1 in BUF.
      replace (firstn (Z.to_nat alloc - 14) (skipn 14 bsx')) with (skipn 14 bsx') in BUF by (symmetry; apply firstn_all2; rewrite length_skipn; lia).
      assert (BUF4 : rw_cells usegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C2 (Z_to_bv 64 (j0 + 256 * j1)); CB (Z.to_nat alloc - 14) (skipn 14 bsx')]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le4_lit g0 g1 g2 g3), (le2_lit j0 j1) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS.
      (* [comment removed for export] *)
      step. step. if_false_by (eqz_false (Bq + 8) ltac:(clear -K1 K3 K4; lia)).
      step. step. if_false_by (geu_neg_false (Bq + 8) 16 ltac:(lia) ltac:(clear -K1 K3 K4 W4 LEN REM BR0; lia)).
      step. step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      step. pstep. step.
      step. rewrite (and7_aligned (Bq + 8)) by (clear -K1 K2 K3 K4; try lia; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        rename mm into m6 end.
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; clear - Ha R1; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R1 R2; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in PRIV; [| intros a Ha; pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ; unfold psize, is_ng, S3.F_ngnextA.TwB.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha; cbn [pc_priv] in PZ, Ha; unfold PCAP_NG_SF_TOTAL in PZ; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha PZ LO BU SPW P4; lia].
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. clear - LO BU SPM; lia. }
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. gio_ceil_fact; clear -CLO__ H0 LO BU SPW; lia. }
      assert (IFS6 : ifaces_ok (pv bq alloc data eb sx ix) Ix' m6).
      { eapply ifaces_ok_agree; [exact AGF | | exact IFS]. intros sg q Hq a Ha. unfold S3.F_ngnextA.TwB.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
        destruct (API sx q eq_refl) as [X1 X2].
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
        cbn [outside]. gio_ceil_fact; clear -CLO__ Ha I1 I4 LO BU SPW. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGF|]. intros a [[Ha|Ha] _]; cbn [outside]; [clear - Ha; lia|].
        destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. gio_ceil_fact; clear -CLO__ Hc LO BU SPW. lia. }
      clear MU WM AGF G5 PC5 AG5 IFS G5e.
      (* [comment removed for export] *)
      lazymatch goal with FRX : rw_cells usegs m6 (bv_unsigned sp + -160) (_ :: _ :: _ :: _ :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: _) |- _ =>
        assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [c1; c2; c3; c4])) by exact FRX end.
      step. if_cases BRS; zify_cond BRS.
      + (* [comment removed for export] *)
        assert (SW : swapped = false) by (destruct swapped; [| reflexivity]; exfalso; revert BRS; rewrite ?unsigned_lit by (cbn; lia); cbn; lia).
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with Y by (rewrite SW; reflexivity) end.
        cbv zeta.
        change (ng_of (pv bq alloc data eb sx ix)) with sx. change (ng_ifaces_ptr_of (pv bq alloc data eb sx ix)) with ix.
        change (pc_bufdata (pv bq alloc data eb sx ix)) with data. fold (ng_reset sx).
        hide FR6. hide HH. hide HD. hide PRIV. step. if_false. unhide FR6. unhide HH. unhide HD. unhide PRIV.
        apply evt_done.
        eapply (ngn_shb_tail LOOP HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps bq Bq Ix alloc rem data eb sx ix hcs dw dj);
          [assumption | exact FR6 | reflexivity | assumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG
          | exact LEN | exact L30 | clear - BR0; lia | exact OF5].
      + (* [comment removed for export] *)
        assert (SW : swapped = true) by (destruct swapped; [reflexivity|]; exfalso; revert BRS; rewrite ?unsigned_lit by (cbn; lia); cbn; lia).
        hide FR6. hide HH. hide HD. hide PRIV. step. if_false. unhide FR6. unhide HH. unhide HD. unhide PRIV.
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with X by (rewrite SW; reflexivity) end.
        cbv zeta.
        change (set_bufdata (swap_field 2 (8 + 4) (swap_field 4 8 data)) (pv bq alloc data eb sx ix)) with (pv bq alloc (swap_field 2 (8 + 4) (swap_field 4 8 data)) eb sx ix).
        change (8 + 4)%Z with 12%Z. rewrite (shb_swap_data' data) by lia. fold g0 g1 g2 g3 j0 j1.
        set (data' := firstn 8 data ++ [g3; g2; g1; g0; j1; j0] ++ skipn 14 data).
        change (ng_of (pv bq alloc data' eb sx ix)) with sx. change (ng_ifaces_ptr_of (pv bq alloc data' eb sx ix)) with ix.
        change (pc_bufdata (pv bq alloc data' eb sx ix)) with data'. fold (ng_reset sx).
        hide FR6. hide HH. hide HD. hide PRIV. hide CELLS.
        eapply evt_cut.
        { eapply (ngn_shb_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 g0 g1 g2 g3 j0 j1 Bq);
            [repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF4 | assumption | clear - K1; lia | clear - K4 W4 LEN REM BR0; lia]. }
        cbv beta. intros ms' (a1v & a2v & a3v & a4v & m7 & -> & MU7 & WM7 & MI7 & HB7 & E1 & E2).
        assert (AGP : agrees_on (fun a => outside [(Bq + 8, Bq + 14)]%Z a) m6 m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
        unhide FR6. unhide HH. unhide HD. unhide PRIV. unhide CELLS.
        lazymatch goal with STX : stk usegs m6 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP STX ltac:(intros a Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia)) as ST7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold S3.F_ngnextA.TwB.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW R1 W4 LEN REM BR0; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW R1 R2 W4 LEN REM BR0; lia].
        assert (G7 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU7 | exact WM7 |]. apply Forall_cons; [| apply Forall_nil].
          right. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc S3.F_ngnextA.TwB.pv]. clear - W4 LEN REM BR0; lia. }
        (* [comment removed for export] *)
        assert (BUF7 : rw_cells usegs m7 Bq [CB (Z.to_nat alloc) (firstn 8 bsx' ++ [b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx')]).
        { assert (R7 : rw_cells usegs m7 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C2 (Z_to_bv 64 (j1 + 256 * j0)); CB (Z.to_nat alloc - 14) (skipn 14 bsx')]).
          { eapply rw_cells_recell; [exact HB7 | | ].
            { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
            cbn [cells_bytes cbytes app]. rewrite (le4_word_mod32 a1v (le4val g3 g2 g1 g0) E1), (le2_of_val a2v j1 j0 j1) by lia. rewrite (le4_lit g3 g2 g1 g0), (le2_lit j1 j0) by lia. reflexivity. }
          pose proof (rw_cells_merge usegs m7 Bq [] _ [] ltac:(rewrite app_nil_r; exact R7)) as R8.
          lazymatch type of R8 with rw_cells _ _ _ ([] ++ [CB ?n ?bs]) =>
            replace n with (Z.to_nat alloc) in R8 by (cbn [cells_size csize]; clear - W4 LEN REM BR0; lia);
            cbn [app cells_bytes cbytes] in R8 end.
          rewrite (le4_lit g3 g2 g1 g0), (le2_lit j1 j0), app_nil_r in R8 by lia. exact R8. }
        assert (LEN' : length data' = length data).
        { subst data'. change (skipn 14 data) with (skipn (8 + length [g3; g2; g1; g0; j1; j0]) data). apply splice_length. cbn [length]. clear - LEN REM BR0; lia. }
        assert (PFX7 : firstn (length data') (firstn 8 bsx' ++ [b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx') = map b8 data').
        { subst data'. change ([b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx') with (map b8 [g3; g2; g1; g0; j1; j0] ++ skipn (8 + length [g3; g2; g1; g0; j1; j0]) bsx').
          change ([g3; g2; g1; g0; j1; j0] ++ skipn 14 data) with ([g3; g2; g1; g0; j1; j0] ++ skipn (8 + length [g3; g2; g1; g0; j1; j0]) data).
          apply splice_pfx; [exact PFX | cbn [length]; clear - LEN REM BR0; lia | clear - LBS W4; lia]. }
        assert (HQ7 : forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> outside [(Bq + 8, Bq + 14)]%Z a) by (intros a _ Hn; cbn [outside]; clear - Hn W4 LEN REM BR0; lia).
        pose proof (PCAPR_bufdata ps bq Bq Ix alloc data data' eb sx ix m6 m7 _ _ G6 PC6 AGP HQ7 BUF7 PFX7 LEN') as PC7.
        assert (G7' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m7) by exact G7.
        assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia|].
          destruct (ngn_CLc_facts _ _ _ _ G6 Ha) as [Hc Hnb]. split; [| exact Logic.I].
          intros Hr. apply Hnb. unfold pcap_blocks, in_block. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc S3.F_ngnextA.TwB.pv]. clear - Hr W4 LEN REM BR0; lia. }
        assert (DRNG' : Forall (fun x => 0 <= x < 256)%Z data').
        { subst data'. change (skipn 14 data) with (skipn (8 + length [g3; g2; g1; g0; j1; j0]) data). apply splice_Forall; [exact DRNG|].
          repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
        apply evt_done.
        eapply (ngn_shb_tail LOOP HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 ps bq Bq Ix alloc rem data' eb sx ix hcs dw dj);
          [exact ST7 | exact FR6 | reflexivity | exact MI7 | exact G7' | exact PC7 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG'
          | rewrite LEN'; exact LEN | exact L30 | clear - BR0; lia | exact OF5].
  Qed.
  End Sz7.
  Lemma ngn_shb : ltac:(let t := eval cbv delta [ngn_shb__stmt] in ngn_shb__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP. intros LOOP HLOOP ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_shb__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.

End WithCeil.
End TwB.
End F_ngnextS.
