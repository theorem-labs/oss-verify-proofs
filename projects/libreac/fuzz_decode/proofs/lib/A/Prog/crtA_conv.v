(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/FP.v; 609 of its 651 lines of code are new or changed and 349 lines of the source are left out. *)
(* crtA_conv: the convert loop of check_round_trip in image A (fuzz_decode.asan) as an Exec.v evt walk --- the
   shadow checks of its four loads and two stores, the loop invariant crt_inv and its transport lemmas, and the
   exact float conversion each iteration makes.  It feeds the footprint twin lib/A/Prog/crtA_loop.v and, through
   it, the cgif-form walk of lib/A/Prog/check_round_trip_cg.v.

   PORT of the record of the same function,
   a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_convert.v:1-701.
   Every lemma name, every proof and every comment is the record's.  Five things are not:
     - the ASan address predicates (ASAN_K, app_mem, shadow_addr, addressable, addr_one, ...) come from
       lib/A/AsanCells.v.  The record's lib/A/AsanRT.v is not on this branch; AsanCells.v is the verbatim split of
       that file's constants and address predicates, so the names and the bodies are the same.
     - no image address is spelled out.  Every program address is a name of lib/A/Prog/crtA_iface.v:
       CRT_AT off = CRT_ENTRY + off, and CRT_ENTRY = decode_sigma DS_check_round_trip = decode_text +
       AF_check_round_trip of the listing lib/A/Prog/DecodeList.v.  CRT_ENTRY is the entry the record walks from,
       so the record's convert loop is CRT_AT 0xd4 .. CRT_AT 0x1f0 here, and each comment below names an interior
       point by its offset from CRT_ENTRY (+0x10c, +0x120, ...) instead of by the record's absolute address.
       Inside the proofs, step first computes each CRT_AT o to its value (crt_lits below), so no numeral is
       written anywhere and the walk still runs on numeral pcs as the record's did.
     - s24 (record :11-13) and byte_range (record :58-59) are not defined here: they come, with the record's
       text, from lib/Lib/CrtS24.v, so that the image-free encode lemmas (lib/Lib/CrtEnc.v) and this file share
       one constant s24.  CrtS24.v loads no lib/Prog file: lib/Prog/RcBraidLib.v redefines Step.v's exec_pre and
       post_step globally (post_step := idtac), and with that the FP steps of crt_body below find no frm0.
     - in Section Loops the register words ra .. s11 and the postcondition G are declared after the memory-side
       lemmas instead of first, and those lemmas (crt_nn .. crt_sh_store8) are closed with `Proof using All`.
       The record left their section arguments to whatever its lia certificates used, and crt_loopF.v passed a
       hand-made argument list per lemma; on this branch the certificates use other hypotheses (crt_inv_pcm took
       HP2 where the record's took HP1), so the lists no longer matched.  Now every one of them takes exactly
       m0 pb P Q pcm nch ns HN .. DQC.  No proof step is changed.
     - step is redefined locally as crt_lits followed by lib/Lib/Step.v's step (see the comment at crt_lits),
       and lia / nia are restored locally to the Stdlib definitions (see the comment after the imports). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import CrtS24.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof ReacDecodeLib check_braid
  crtA_iface.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact.
Import ListNotations.
Open Scope Z_scope.

(* Not in the record.  Requiring crtA_iface.v loads lib/A/Prog/DecodeAddr.v -> PaTable.v -> lib/Reusable/YM03.v,
   whose global `Ltac Lia.lia ::=` / `Ltac Lia.nia ::=` (YM03.v:182-189) replace the lia and nia the record was
   built under; under them this file compiled 50-80 times slower than the record's crt_convert.v (crtA_conv.vo
   2395-2419 s against 28-56 s) and its lia certificates used other hypotheses.  So this file restores, for itself
   only, the record's tactics: lia as lib/Lib/LiaTwx2.v:187-190 defines it (LiaTwx2 is loaded through PropExec, in
   the record's closure too) and nia as Stdlib defines it (YM03.v:180 keeps it as lf_nia_orig). *)
Local Ltac Lia.lia ::=
  first [ LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

Definition cv (pb : Z -> byte) (j : Z) : Z :=
  f32 (s24 (pb (3 * j)) (pb (3 * j + 1)) (pb (3 * j + 2))) (-23).

Lemma unbox_nan_box : forall v : bv 32, unbox_s (nan_box v) = v.
Proof.
  intros v. unfold unbox_s, nan_box, low32.
  pose proof (bv_unsigned_in_range 32 v) as Hv. unfold bv_modulus in Hv.
  assert (E : bv_unsigned (bv_concat 64 (Z_to_bv 32 (-1)) v) = (Z.lor (Z.shiftl (2^32 - 1) 32) (bv_unsigned v))%Z).
  { rewrite bv_concat_unsigned by reflexivity. reflexivity. }
  assert (Hhi : bv_unsigned (bv_extract 32 32 (bv_concat 64 (Z_to_bv 32 (-1)) v)) = Z.ones 32).
  { rewrite bv_extract_unsigned, E. apply Z.bits_inj'. intros i Hi.
    change (bv_wrap 32 ?x) with (x mod 2^32)%Z. change (Z.of_N 32) with 32%Z.
    destruct (Z.lt_ge_cases i 32).
    - rewrite testbit_mod_pow2_low, Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec, Z.ones_spec_low by lia.
      replace (i + 32 - 32)%Z with i by lia. change (2^32 - 1)%Z with (Z.ones 32). rewrite Z.ones_spec_low by lia. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high by lia. apply andb_false_r. }
  rewrite Hhi, Z.eqb_refl.
  apply bv_eq. rewrite bv_extract_unsigned, E, Z.shiftr_0_r. change (bv_wrap 32 ?x) with (x mod 2^32)%Z.
  apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
  - rewrite testbit_mod_pow2_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
  - rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high, andb_false_r by lia.
    symmetry. destruct (Z.eq_dec (bv_unsigned v) 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma low32_nan_box : forall v : bv 32, low32 (nan_box v) = v.
Proof.
  intros v. unfold nan_box, low32. apply bv_eq. rewrite bv_extract_unsigned, bv_concat_unsigned, Z.shiftr_0_r by reflexivity.
  change (bv_wrap 32 ?x) with (x mod 2^32)%Z. pose proof (bv_unsigned_in_range 32 v) as Hv. unfold bv_modulus in Hv.
  change (Z.of_N 32) with 32%Z in *.
  apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
  - rewrite testbit_mod_pow2_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
  - rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high, andb_false_r by lia.
    symmetry. destruct (Z.eq_dec (bv_unsigned v) 0) as [E|E]; [rewrite E; apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32%Z; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma le4_nan_box : forall x : bv 32, le4 (nan_box x) = Z_to_le_bytes 4 (bv_unsigned x).
Proof. intros x. rewrite <- store_bytes_4', low32_nan_box. reflexivity. Qed.

Lemma u32_small : forall z, 0 <= z < 2^32 -> bv_unsigned (Z_to_bv 32 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 32) with (2^32). exact Hz. Qed.

Lemma s24_range : forall b0 b1 b2, -8388608 <= s24 b0 b1 b2 < 8388608.
Proof.
  intros b0 b1 b2. unfold s24. pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
  destruct (Z.leb_spec 128 (bv_unsigned b2)); lia.
Qed.

Lemma conv_bytes : forall md (w y : word) b0 b1 b2,
  unbox_s y = Z_to_bv 32 F2M23 ->
  bv_unsigned w mod 2^32 = s24 b0 b1 b2 mod 2^32 ->
  le4 (fmul_s md (fcvt_s_w md w) y) = Z_to_le_bytes 4 (f32 (s24 b0 b1 b2) (-23)).
Proof.
  intros md w y b0 b1 b2 Hy Hw. pose proof (s24_range b0 b1 b2) as R.
  unfold fmul_s, fcvt_s_w.
  rewrite (f32_of_int md (s24 b0 b1 b2) (bv_unsigned w) R Hw). cbn [fst].
  rewrite unbox_nan_box, Hy.
  rewrite (u32_small (f32 (s24 b0 b1 b2) 0)) by (apply f32_range; lia).
  rewrite (u32_small F2M23) by (unfold F2M23; lia).
  rewrite (f32_mul_m23 md _ R). cbn [fst].
  rewrite le4_nan_box, u32_small by (apply f32_range; lia). reflexivity.
Qed.

Lemma lor_low : forall a b n, 0 <= a -> 0 <= b < 2^n -> 0 <= n -> Z.lor (a * 2^n) b = a * 2^n + b.
Proof.
  intros a b n Ha Hb Hn.
  assert (L : Z.land (a * 2^n) b = 0).
  { rewrite <- Z.shiftl_mul_pow2 by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.bits_0. destruct (Z.ltb_spec i n).
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 b i); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite (Z.add_nocarry_lxor _ _ L). apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, Z.lxor_spec.
  pose proof (f_equal (fun z => Z.testbit z i) L) as Li. cbv beta in Li.
  rewrite Z.land_spec, Z.bits_0 in Li.
  destruct (Z.testbit (a * 2 ^ n) i), (Z.testbit b i); cbn in *; congruence.
Qed.

Lemma sxb_unsigned : forall b : byte,
  bv_unsigned (sxb b) = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b + 18446744073709551360.
Proof.
  intros b. pose proof (byte_range b) as R. unfold sxb. rewrite unsigned_lit_wrap.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  change (2^64) with 18446744073709551616.
  destruct (Z.ltb_spec (bv_unsigned b) 128); cbv iota.
  - rewrite (Z.mod_small (bv_unsigned b + 128) 256) by lia.
    replace (bv_unsigned b + 128 - 128) with (bv_unsigned b) by lia. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_unique (bv_unsigned b + 128) 256 1 (bv_unsigned b - 128)) by lia.
    symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

Lemma land_hi24 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073692774400 = 2^24 * (x / 2^24).
Proof. intros x Hx. exact (land_hi x 24 Hx ltac:(lia)). Qed.

Lemma comb : forall (b0 b1 b2 : byte) (a2 : word), bv_unsigned a2 = 18446744073692774400 ->
  bv_unsigned (Z_to_bv 64
    (Z.lor
      (bv_unsigned (Z_to_bv 64
        (Z.lor
          (bv_unsigned (Z_to_bv 64
            (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8))) (bv_unsigned (zxb b0)))))
          (bv_unsigned (Z_to_bv 64
            (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb b2)) 255))) 16))))))
      (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb b2)) (bv_unsigned a2)))))) mod 2^32
  = s24 b0 b1 b2 mod 2^32.
Proof.
  intros b0 b1 b2 a2 Ha2.
  pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1. pose proof (byte_range b2) as R2.
  assert (P8 : 2^8 = 256) by reflexivity. assert (P16 : 2^16 = 65536) by reflexivity.
  assert (P24 : 2^24 = 16777216) by reflexivity. assert (P32 : 2^32 = 4294967296) by reflexivity.
  assert (P64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (U0 : bv_unsigned (zxb b0) = bv_unsigned b0) by (unfold zxb; apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (zxb b1) = bv_unsigned b1) by (unfold zxb; apply unsigned_lit; lia).
  rewrite U0, U1, Ha2, sxb_unsigned.
  rewrite (Z.shiftl_mul_pow2 (bv_unsigned b1) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2^8)) by lia.
  rewrite (lor_low (bv_unsigned b1) (bv_unsigned b0) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2^8 + bv_unsigned b0)) by lia.
  unfold s24.
  destruct (Z.ltb_spec (bv_unsigned b2) 128) as [L|L]; cbv iota.
  - replace (Z.land (bv_unsigned b2) 255) with (bv_unsigned b2)
      by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    rewrite (unsigned_lit (bv_unsigned b2)) by lia.
    rewrite (Z.shiftl_mul_pow2 (bv_unsigned b2) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned b2 * 2^16)) by lia.
    rewrite (Z.lor_comm (bv_unsigned b1 * 2^8 + bv_unsigned b0) (bv_unsigned b2 * 2^16)).
    rewrite (lor_low (bv_unsigned b2) (bv_unsigned b1 * 2^8 + bv_unsigned b0) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned b2 * 2^16 + (bv_unsigned b1 * 2^8 + bv_unsigned b0))) by lia.
    rewrite land_hi24 by lia. rewrite (Z.div_small (bv_unsigned b2) (2^24)) by lia. rewrite Z.mul_0_r.
    rewrite (unsigned_lit 0) by lia. rewrite Z.lor_0_r.
    rewrite unsigned_lit by lia.
    rewrite (proj2 (Z.leb_gt 128 (bv_unsigned b2))) by lia. cbv iota.
    rewrite ?P8, ?P16, ?P24, ?P32. Z.div_mod_to_equations. lia.
  - assert (E255 : Z.land (bv_unsigned b2 + 18446744073709551360) 255 = bv_unsigned b2).
    { change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite P8.
      symmetry. apply (Z.mod_unique _ _ 72057594037927935); lia. }
    rewrite E255.
    rewrite (unsigned_lit (bv_unsigned b2)) by lia.
    rewrite (Z.shiftl_mul_pow2 (bv_unsigned b2) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned b2 * 2^16)) by lia.
    rewrite (Z.lor_comm (bv_unsigned b1 * 2^8 + bv_unsigned b0) (bv_unsigned b2 * 2^16)).
    rewrite (lor_low (bv_unsigned b2) (bv_unsigned b1 * 2^8 + bv_unsigned b0) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned b2 * 2^16 + (bv_unsigned b1 * 2^8 + bv_unsigned b0))) by lia.
    assert (D : (bv_unsigned b2 + 18446744073709551360) / 2^24 = 1099511627775).
    { rewrite P24. symmetry.
      apply (Z.div_unique _ _ _ (bv_unsigned b2 + 18446744073709551360 - 1099511627775 * 16777216)); lia. }
    rewrite land_hi24 by lia. rewrite D. clear D.
    rewrite (unsigned_lit (2^24 * 1099511627775)) by lia.
    rewrite (Z.mul_comm (2^24) 1099511627775).
    rewrite (Z.lor_comm _ (1099511627775 * 2^24)).
    rewrite (lor_low 1099511627775 _ 24) by lia.
    rewrite unsigned_lit by lia.
    rewrite (proj2 (Z.leb_le 128 (bv_unsigned b2))) by lia. cbv iota.
    rewrite ?P8, ?P16, ?P24, ?P32. Z.div_mod_to_equations. lia.
Qed.

Local Ltac fct := try unfold wa; norm;
  first [ reflexivity | rng | (rewrite ?unsigned_lit_wrap; zb_fold_lits; Z.div_mod_to_equations; lia) ].
Local Ltac word_eq_tac ::= first [ exact eq_refl | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
  | (norm; first [ reflexivity | f_equal; lia | lia ]) ].

(* Not in the record: the statements of this file name every pc as CRT_AT off, where the record wrote the
   numeral.  Inside the proofs only, each step first replaces every CRT_AT o of the goal and of the hypotheses by
   its value, computed by vm_compute (no numeral is written here), so the walk runs on numeral pcs exactly as the
   record's did (image B's crtB_loop.v does the same with its crt_pc).  The step body after crt_lits is
   lib/Lib/Step.v's step. *)
Local Ltac crt_lits :=
  repeat match goal with
  | |- context [CRT_AT ?o] => let v := eval vm_compute in (CRT_AT o) in change (CRT_AT o) with v
  | H : context [CRT_AT ?o] |- _ => let v := eval vm_compute in (CRT_AT o) in change (CRT_AT o) with v in H
  end.
Local Ltac step ::= crt_lits;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Lemma land_sxb_255 : forall b : byte, Z.land (bv_unsigned (sxb b)) 255 = bv_unsigned b.
Proof.
  intros b. pose proof (byte_range b). change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256. rewrite sxb_unsigned. destruct (Z.ltb_spec (bv_unsigned b) 128).
  - apply Z.mod_small; lia.
  - replace (bv_unsigned b + 18446744073709551360) with (bv_unsigned b + 72057594037927935 * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma land_mask32 : forall v, 0 <= v < 2 ^ 64 -> Z.land v 4278190080 = (2 ^ 24 * (v / 2 ^ 24)) mod 2 ^ 32.
Proof.
  intros v Hv. replace 4278190080 with (Z.land (2 ^ 64 - 2 ^ 24) (Z.ones 32)) by (vm_compute; reflexivity).
  rewrite Z.land_assoc, (land_hi v 24 Hv ltac:(lia)), Z.land_ones by lia. reflexivity.
Qed.

Lemma comb_asan : forall (b0 b1 b2 : byte) (a2 : word), bv_unsigned a2 = 4278190080 ->
  bv_unsigned (Z_to_bv 64
    (Z.lor
      (bv_unsigned (Z_to_bv 64
        (Z.lor
          (bv_unsigned (Z_to_bv 64
            (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8))) (bv_unsigned (zxb b0)))))
          (bv_unsigned (Z_to_bv 64
            (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb b2)) 255))) 16))))))
      (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb b2)) (bv_unsigned a2)))))) mod 2^32
  = s24 b0 b1 b2 mod 2^32.
Proof.
  intros b0 b1 b2 a2 Ha2.
  pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1. pose proof (byte_range b2) as R2.
  assert (P8 : 2^8 = 256) by reflexivity. assert (P16 : 2^16 = 65536) by reflexivity.
  assert (P24 : 2^24 = 16777216) by reflexivity. assert (P32 : 2^32 = 4294967296) by reflexivity.
  assert (P64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (U0 : bv_unsigned (zxb b0) = bv_unsigned b0) by (unfold zxb; apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (zxb b1) = bv_unsigned b1) by (unfold zxb; apply unsigned_lit; lia).
  rewrite U0, U1, Ha2.
  rewrite (land_sxb_255 b2).
  rewrite (Z.shiftl_mul_pow2 (bv_unsigned b1) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2^8)) by lia.
  rewrite (lor_low (bv_unsigned b1) (bv_unsigned b0) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2^8 + bv_unsigned b0)) by lia.
  rewrite (unsigned_lit (bv_unsigned b2)) by lia.
  rewrite (Z.shiftl_mul_pow2 (bv_unsigned b2) 16) by lia.
  rewrite (unsigned_lit (bv_unsigned b2 * 2^16)) by lia.
  rewrite (Z.lor_comm (bv_unsigned b1 * 2^8 + bv_unsigned b0) (bv_unsigned b2 * 2^16)).
  rewrite (lor_low (bv_unsigned b2) (bv_unsigned b1 * 2^8 + bv_unsigned b0) 16) by lia.
  rewrite (unsigned_lit (bv_unsigned b2 * 2^16 + (bv_unsigned b1 * 2^8 + bv_unsigned b0))) by lia.
  rewrite (land_mask32 (bv_unsigned (sxb b2)) (u64_range (sxb b2))).
  rewrite sxb_unsigned. unfold s24.
  destruct (Z.ltb_spec (bv_unsigned b2) 128) as [L|L].
  - rewrite (Z.div_small (bv_unsigned b2) (2^24)) by lia. rewrite Z.mul_0_r.
    change (0 mod 2^32) with 0. rewrite (unsigned_lit 0) by lia. rewrite Z.lor_0_r.
    rewrite unsigned_lit by lia.
    rewrite (proj2 (Z.leb_gt 128 (bv_unsigned b2))) by lia. cbv iota.
    rewrite ?P8, ?P16, ?P24, ?P32. Z.div_mod_to_equations. lia.
  - assert (HD : (bv_unsigned b2 + 18446744073709551360) / 2 ^ 24 = 1099511627775).
    { change (2 ^ 24) with 16777216. Z.div_mod_to_equations. lia. }
    rewrite HD.
    replace ((2 ^ 24 * 1099511627775) mod 2 ^ 32) with 4278190080 by (vm_compute; reflexivity).
    rewrite (unsigned_lit 4278190080) by lia.
    rewrite (Z.lor_comm (bv_unsigned b2 * 2^16 + (bv_unsigned b1 * 2^8 + bv_unsigned b0)) 4278190080).
    replace 4278190080 with (255 * 2^24) by (vm_compute; reflexivity).
    rewrite (lor_low 255 (bv_unsigned b2 * 2^16 + (bv_unsigned b1 * 2^8 + bv_unsigned b0)) 24) by lia.
    rewrite unsigned_lit by lia.
    rewrite (proj2 (Z.leb_le 128 (bv_unsigned b2))) by lia. cbv iota.
    rewrite ?P8, ?P16, ?P24, ?P32. Z.div_mod_to_equations. lia.
Qed.

(* =========================================================================
   Convert-loop shadow checks (+0x10c..+0x164), modelled on reac_decode rc_c*.
   ========================================================================= *)

(* CL1 @+0x10c -> +0x120 : addr a1 := t0 + t3, shadow/lb into a2, handler andi t5 *)
Lemma cl1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x5 + bv_unsigned x28 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y11 y12 y30 : word, bv_unsigned y11 = A ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 y30 x31) F (Z_to_bv 64 (CRT_AT 0x120)) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x10c)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x5) as R5. pose proof (u64_range x28) as R28. unfold ASAN_K in M.
  step. gen_add x5 x28 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* CL2 @+0x120 -> +0x13c : t6 := s6+t3 ; shadow of a1+1 (lb s9) ; data b0 := [t6] (lbu t5) ; handler andi s10 *)
Lemma cl2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b0 : byte) (A Dd : Z),
  bv_unsigned x11 = A -> A + 1 < 2^64 ->
  mrd rsegs mm (wa ((A + 1) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (A + 1) mod 8 < bv_signed k) ->
  bv_unsigned x22 + bv_unsigned x28 = Dd -> Dd + 2 < 2^64 -> mrd rsegs mm (wa Dd) = Some b0 ->
  (forall y12 y25 y26 y31 : word, bv_unsigned y31 = Dd ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) y25 y26 x27 x28 x29 (zxb b0) y31) F (Z_to_bv 64 (CRT_AT 0x13c)) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x120)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E11 RA M SK Ed DB MD CONT.
  pose proof (u64_range x11) as R11. pose proof (u64_range x22) as R22. pose proof (u64_range x28) as R28.
  unfold ASAN_K in M.
  step. gen_add x22 x28 wt6 Ut6. rewrite Ed in Ut6.
  step. gen_addi x11 wa2 Ua2. rewrite E11 in Ua2.
  step. gen_shr wa2 g G. rewrite Ua2 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm wt6 _ _ MD Ut6) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound (A + 1) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact Ut6.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, Ua2, (lts_low ((A + 1) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact Ut6.
Qed.

(* CL3 @+0x13c -> +0x154 : a1 := a1+2 ; shadow of a1 (lb s9) ; data b1 := [t6+1] (lbu a2) ; handler andi s10 *)
Lemma cl3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b1 : byte) (A Dd : Z),
  bv_unsigned x11 = A -> A + 2 < 2^64 ->
  mrd rsegs mm (wa ((A + 2) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (A + 2) mod 8 < bv_signed k) ->
  bv_unsigned x31 = Dd -> mrd rsegs mm (wa (Dd + 1)) = Some b1 ->
  (forall y11 y25 y26 : word, bv_unsigned y11 = A + 2 ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 (zxb b1) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) y25 y26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x154)) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x13c)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E11 RA M SK Ed MD CONT.
  pose proof (u64_range x11) as R11. pose proof (u64_range x31) as R31. unfold ASAN_K in M.
  step. gen_addi x11 wa1 Ua1. rewrite E11 in Ua1.
  step. gen_shr wa1 g G. rewrite Ua1 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x31 1 _ _ MD ltac:(lia)) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound (A + 2) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact Ua1.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, Ua1, (lts_low ((A + 2) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact Ua1.
Qed.

(* CLS4 @+0x154 -> +0x168 : shadow of a0 (store4; lb s9) ; data b2 := [t6+2] (lb a1, signed) ; handler andi t6 + addi 3 *)
Lemma cls4 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b2 : byte) (A Dd : Z),
  bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  bv_unsigned x31 = Dd -> mrd rsegs mm (wa (Dd + 2)) = Some b2 ->
  (forall y25 y31 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (sxb b2) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) y25 x26 x27 x28 x29 x30 y31) F (Z_to_bv 64 (CRT_AT 0x168)) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x154)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E10 RA M SK Ed MD CONT.
  pose proof (u64_range x10) as R10. pose proof (u64_range x31) as R31. unfold ASAN_K in M.
  step. gen_shr x10 g G. rewrite E10 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x31 2 _ _ MD ltac:(lia)) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step. rewrite land7, E10, (lts_sm (A mod 8 + 3) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* CSH_Q8 @+0xdc -> +0xec : 8-byte store shadow of a0 (lbu a1) ; shadow byte must be 0 *)
Lemma csh_q8 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k -> bv_unsigned k = 0 ->
  (forall y11 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0xec)) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0xdc)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M HK CONT.
  pose proof (u64_range x10) as R10. unfold ASAN_K in M.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  replace (zxb k) with (Z_to_bv 64 0) by (unfold zxb; rewrite HK; reflexivity).
  step. apply CONT.
Qed.

Lemma byte_signed0 : forall b : byte, bv_signed b = 0 -> bv_unsigned b = 0.
Proof.
  intros b H. pose proof (byte_range b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (Z.of_N 8) with 8 in H. Z.div_mod_to_equations; lia.
Qed.

(* =========================================================================
   Convert loop (+0xd4..+0x1f0), asan.  Invariant lemmas (crt_inv, crt_inv_P,
   ...) are build-independent and taken verbatim from the plain model.
   ========================================================================= *)
Section Loops.
Variables (m0 : word -> option byte) (pb : Z -> byte) (P Q pcm nch ns : Z).
Hypothesis HN : 2 <= nch <= 127.
Hypothesis HNS : 1 <= ns <= 12.
Hypothesis HB : 3 * nch * ns <= 1440.
Hypothesis HP0 : 0 < P.
Hypothesis HP1 : P + 4 * nch * ns < 2^63.
Hypothesis HP2 : P mod 16 = 0.
Hypothesis HQ0 : 0 < Q.
Hypothesis HQ1 : Q + 8 * nch < 2^63.
Hypothesis HQ2 : Q mod 16 = 0.
Hypothesis HC0 : 0 < pcm.
Hypothesis HC1 : pcm + 3 * nch * ns < 2^63.
Hypothesis PB : forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m0 (wa (pcm + i)) = Some (pb i).
Hypothesis WP : wr_at rsegs m0 P (4 * nch * ns).
Hypothesis WQ : wr_at rsegs m0 Q (8 * nch).
Hypothesis ADP : addressable m0 P (4 * nch * ns).
Hypothesis ADQ : addressable m0 Q (8 * nch).
Hypothesis ADC : addressable m0 pcm (3 * nch * ns).
Hypothesis DPQ : P + 4 * nch * ns <= Q \/ Q + 8 * nch <= P.
Hypothesis DPC : P + 4 * nch * ns <= pcm \/ pcm + 3 * nch * ns <= P.
Hypothesis DQC : Q + 8 * nch <= pcm \/ pcm + 3 * nch * ns <= Q.

Definition crt_W : list ivl := [(P, P + 4 * nch * ns); (Q, Q + 8 * nch)].

Definition crt_inv (m : word -> option byte) (kp kq : Z) : Prop :=
  munch crt_W m0 m /\ wmono rsegs m0 m /\
  (forall j, 0 <= j < kp -> bytes_at rsegs m (P + 4 * j) (Z_to_le_bytes 4 (cv pb j))) /\
  (forall c, 0 <= c < kq -> bytes_at rsegs m (Q + 8 * c) (le8 (Z_to_bv 64 (P + 4 * (c * ns))))).

Lemma crt_nn : 0 < nch * ns <= 480.
Proof using All. split; [apply Z.mul_pos_pos; lia | lia]. Qed.

Lemma crt_inv_init : crt_inv m0 0 0.
Proof using All.
  split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; intros; exfalso; lia.
Qed.

Lemma crt_inv_pcm : forall m kp kq i, crt_inv m kp kq -> 0 <= i < 3 * nch * ns -> mrd rsegs m (wa (pcm + i)) = Some (pb i).
Proof using All.
  intros m kp kq i (MU & _) Hi. pose proof crt_nn. pose proof (PB i Hi) as E. unfold munch in MU. unfold mrd in *.
  rewrite MU; [exact E|]. unfold crt_W. rewrite wa_unsigned by lia. cbn [outside].
  split; [lia | split; [lia | exact I]].
Qed.

Lemma crt_stP : forall m k kq (t0 : word), crt_inv m k kq -> 0 <= k < nch * ns -> bv_unsigned t0 = P + 4 * k ->
  store_ok rsegs m t0 4 = true.
Proof using All.
  intros m k kq t0 (_ & WM & _) Hk Ht. pose proof crt_nn.
  pose proof (wr_at_transport rsegs m0 m P (4 * nch * ns) WP WM) as W1.
  rewrite <- (wa_of_var t0 (P + 4 * k) Ht).
  apply (wr_at_store_ok rsegs m P (4 * nch * ns) (4 * k) 4 W1); lia.
Qed.

Lemma crt_stQ : forall m kp c, crt_inv m kp c -> 0 <= c < nch -> store_ok rsegs m (wa (Q + 8 * c)) 8 = true.
Proof using All.
  intros m kp c (_ & WM & _) Hc.
  pose proof (wr_at_transport rsegs m0 m Q (8 * nch) WQ WM) as W1.
  apply (wr_at_store_ok rsegs m Q (8 * nch) (8 * c) 8 W1); lia.
Qed.

Lemma crt_inv_P : forall m k kq (a : word) bs, crt_inv m k kq -> 0 <= k < nch * ns -> 0 <= kq <= nch ->
  bv_unsigned a = P + 4 * k -> bs = Z_to_le_bytes 4 (cv pb k) -> crt_inv (write_to_mem m a bs) (k + 1) kq.
Proof using All.
  intros m k kq a bs (MU & WM & HPd & HQd) Hk Hkq Ha ->. pose proof crt_nn.
  rewrite <- (wa_of_var a (P + 4 * k) Ha).
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | rewrite length_Z_to_le_bytes; lia |].
    unfold crt_W. cbn [inside]. rewrite length_Z_to_le_bytes. lia.
  - apply wmono_write. exact WM.
  - intros j Hj. destruct (Z.eq_dec j k) as [->|Hne].
    + apply bytes_at_write_same; [lia | rewrite length_Z_to_le_bytes; lia].
    + apply bytes_at_write_other; [apply HPd; lia | lia | rewrite length_Z_to_le_bytes; lia |].
      rewrite !length_Z_to_le_bytes. lia.
  - intros c Hc. apply bytes_at_write_other; [apply HQd; lia | lia | rewrite length_Z_to_le_bytes; lia |].
    rewrite length_Z_to_le_bytes, length_le8. lia.
Qed.

Lemma crt_inv_Q : forall m kp c (a v : word), crt_inv m kp c -> 0 <= c < nch -> 0 <= kp <= nch * ns ->
  bv_unsigned a = Q + 8 * c -> bv_unsigned v = P + 4 * (c * ns) -> crt_inv (write_to_mem m a (le8 v)) kp (c + 1).
Proof using All.
  intros m kp c a v (MU & WM & HPd & HQd) Hc Hkp Ha Hv. pose proof crt_nn.
  rewrite <- (wa_of_var a (Q + 8 * c) Ha), <- (wa_of_var v (P + 4 * (c * ns)) Hv).
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | rewrite length_le8; lia |].
    unfold crt_W. cbn [inside]. rewrite length_le8. lia.
  - apply wmono_write. exact WM.
  - intros j Hj. apply bytes_at_write_other; [apply HPd; lia | lia | rewrite length_le8; lia |].
    rewrite length_le8, length_Z_to_le_bytes. lia.
  - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
    + apply bytes_at_write_same; [lia | rewrite length_le8; lia].
    + apply bytes_at_write_other; [apply HQd; lia | lia | rewrite length_le8; lia |].
      rewrite !length_le8. lia.
Qed.

(* ---- addressability transport through the loop's writes (crt_W) ---- *)
Lemma crt_app0 : forall X n i, addressable m0 X n -> 0 <= i < n -> app_mem (X + i).
Proof. intros X n i A Hi. destruct (addr_one m0 X n i A Hi) as (Ha & _). exact Ha. Qed.

Lemma crt_shadow_out : forall a, app_mem a -> outside crt_W (shadow_addr a).
Proof.
  intros a Ha. unfold crt_W. cbn [outside]. pose proof (shadow_not_app a Ha) as NA.
  unfold shadow_addr in *.
  split; [|split; [|exact I]].
  - intros W. apply NA. replace (a / 8 + ASAN_K) with (P + (a / 8 + ASAN_K - P)) by ring.
    apply (crt_app0 P (4 * nch * ns)); [exact ADP | lia].
  - intros W. apply NA. replace (a / 8 + ASAN_K) with (Q + (a / 8 + ASAN_K - Q)) by ring.
    apply (crt_app0 Q (8 * nch)); [exact ADQ | lia].
Qed.

Lemma crt_addr_keep : forall m kp kq X n, crt_inv m kp kq -> addressable m0 X n -> addressable m X n.
Proof.
  intros m kp kq X n (MU & _) A. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct (addr_one m0 X n i A Hi) as (Ha & _). apply crt_shadow_out. exact Ha.
Qed.

Lemma crt_sh_pcm : forall m kp kq i, crt_inv m kp kq -> 0 <= i < 3 * nch * ns ->
  exists kb, mrd rsegs m (wa ((pcm + i) / 8 + ASAN_K)) = Some kb /\ (bv_signed kb = 0 \/ (pcm + i) mod 8 < bv_signed kb).
Proof using All.
  intros m kp kq i Hinv Hi.
  destruct (addr_one m pcm (3 * nch * ns) i (crt_addr_keep m kp kq pcm (3 * nch * ns) Hinv ADC) Hi)
    as (_ & kb & Mk & Sk). exists kb. split; [exact Mk | exact Sk].
Qed.

Lemma crt_sh_store4 : forall m kp kq k, crt_inv m kp kq -> 0 <= k < nch * ns ->
  exists kb, mrd rsegs m (wa ((P + 4 * k) / 8 + ASAN_K)) = Some kb /\ (bv_signed kb = 0 \/ (P + 4 * k) mod 8 + 3 < bv_signed kb).
Proof using All.
  intros m kp kq k Hinv Hk. pose proof crt_nn.
  assert (Hi3 : 0 <= 4 * k + 3 < 4 * nch * ns) by lia.
  destruct (addr_one m P (4 * nch * ns) (4 * k + 3) (crt_addr_keep m kp kq P (4 * nch * ns) Hinv ADP) Hi3)
    as (_ & kb & Mk & Sk).
  assert (P8 : P mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (M4 : (P + 4 * k) mod 8 = 0 \/ (P + 4 * k) mod 8 = 4).
  { assert (E : (P + 4 * k) mod 8 = (4 * k) mod 8)
      by (rewrite Zplus_mod, P8, Z.add_0_l, Zmod_mod; reflexivity).
    rewrite E. replace 8 with (4 * 2) by lia. rewrite Z.mul_mod_distr_l by lia.
    pose proof (Z.mod_pos_bound k 2 ltac:(lia)). lia. }
  assert (E8 : (P + (4 * k + 3)) / 8 = (P + 4 * k) / 8) by (Z.div_mod_to_equations; lia).
  assert (Em : (P + (4 * k + 3)) mod 8 = (P + 4 * k) mod 8 + 3) by (Z.div_mod_to_equations; lia).
  rewrite E8 in Mk. exists kb. split; [exact Mk|].
  destruct Sk as [Hs|Hs]; [left; exact Hs | right; rewrite Em in Hs; exact Hs].
Qed.
Lemma crt_sh_store8 : forall m kp kq ch, crt_inv m kp kq -> 0 <= ch < nch ->
  exists kb, mrd rsegs m (wa ((Q + 8 * ch) / 8 + ASAN_K)) = Some kb /\ bv_unsigned kb = 0.
Proof using All.
  intros m kp kq ch Hinv Hch.
  pose proof (crt_addr_keep m kp kq Q (8 * nch) Hinv ADQ) as ADQm.
  destruct ADQm as (_ & _ & _ & HA).
  assert (Hi : 0 <= 8 * ch + 7 < 8 * nch) by lia.
  destruct (HA (8 * ch + 7) Hi) as (_ & kb & Mk & Sk).
  assert (Q8 : Q mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Em : (Q + (8 * ch + 7)) mod 8 = 7) by (Z.div_mod_to_equations; nia).
  assert (E8 : (Q + (8 * ch + 7)) / 8 = (Q + 8 * ch) / 8) by (Z.div_mod_to_equations; nia).
  assert (HK : bv_signed kb = 0).
  { unfold shadow_ok in Sk. destruct Sk as [H|[H1 H2]]; [exact H | rewrite Em in H1; lia]. }
  exists kb. unfold shadow_addr in Mk. rewrite E8 in Mk.
  split; [exact Mk | exact (byte_signed0 kb HK)].
Qed.

(* The register words of the walk and its postcondition.  They are declared here, after the memory-side lemmas
   above, so that each of those lemmas (all closed with `Proof using All`) is generalised over exactly
   m0 pb P Q pcm nch ns and the twenty hypotheses HN .. DQC, in that order, whatever the lia certificates of its
   proof happen to use.  lib/A/Prog/crtA_loop.v passes that argument list to them. *)
Variables (ra sp gp tp s1 s4 s7 s11 : word).
Variable G : machine_state -> Prop.

Local Notation CST pc t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 (Z_to_bv 64 (4 * ns)) (Z_to_bv 64 18446744073692774400)
           (Z_to_bv 64 (3 * ns)) (Z_to_bv 64 (3 * ns)) (Z_to_bv 64 ns) (Z_to_bv 64 nch) s4 (Z_to_bv 64 Q) s6 s7
           (Z_to_bv 64 2147450880) s9 s10 s11 t3 t4 t5 t6)
      Fh (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma crt_body : forall ch s (t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  0 <= ch < nch -> 0 <= s < ns ->
  bv_unsigned t0 = pcm + 3 * ns * ch -> bv_unsigned s6 = pcm + 3 * ns * ch -> bv_unsigned a3 = ch ->
  bv_unsigned a0 = P + 4 * (ch * ns + s) -> bv_unsigned t4 = P + 4 * (ch * ns + s) -> bv_unsigned t3 = 3 * s ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc -> crt_inv m (ch * ns + s) (ch + 1) ->
  (forall (a0' a1' a2' s9' s10' t3' t4' t5' t6' v : word) (fc' : bv 32) m',
     bv_unsigned a0' = P + 4 * (ch * ns + s + 1) -> bv_unsigned t3' = 3 * (s + 1) ->
     bv_unsigned t4' = P + 4 * (ch * ns + s + 1) -> frm0 fc' -> crt_inv m' (ch * ns + s + 1) (ch + 1) ->
     evt rsegs G (CST (CRT_AT 0x19c) t0 t1 t2 a0' a1' a2' a3 s6 s9' s10' t3' t4' t5' t6' (bvmap_set (Z_to_bv 5 14) v Fh) fc' m')) ->
  evt rsegs G (CST (CRT_AT 0x10c) t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m).
Proof.
  intros ch s t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m
    Hch Hs Ht0 Hs6 Ha3 Ha0 Ht4 Ht3 H15 Hfc Hinv K.
  pose proof crt_nn as NN.
  assert (B1 : ch * ns <= (nch - 1) * ns) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (B1' : (nch - 1) * ns = nch * ns - ns) by ring.
  assert (Hmc : 0 <= ch * ns) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hk : 0 <= ch * ns + s < nch * ns) by lia.
  assert (Bn : 0 <= 3 * (ch * ns + s) + 2 < 3 * nch * ns)
    by (replace (3 * nch * ns) with (3 * (nch * ns)) by ring; lia).
  pose proof (crt_inv_pcm m _ _ (3 * (ch * ns + s)) Hinv ltac:(lia)) as M0.
  pose proof (crt_inv_pcm m _ _ (3 * (ch * ns + s) + 1) Hinv ltac:(lia)) as M1.
  pose proof (crt_inv_pcm m _ _ (3 * (ch * ns + s) + 2) Hinv ltac:(lia)) as M2.
  destruct (crt_sh_pcm m _ _ (3 * (ch * ns + s)) Hinv ltac:(lia)) as (kp0 & Mp0 & Sp0).
  destruct (crt_sh_pcm m _ _ (3 * (ch * ns + s) + 1) Hinv ltac:(lia)) as (kp1 & Mp1 & Sp1).
  destruct (crt_sh_pcm m _ _ (3 * (ch * ns + s) + 2) Hinv ltac:(lia)) as (kp2 & Mp2 & Sp2).
  destruct (crt_sh_store4 m _ _ (ch * ns + s) Hinv Hk) as (ks & Ms & Ss).
  pose proof (crt_stP m (ch * ns + s) (ch + 1) t4 Hinv Hk Ht4) as HSt.
  (* cl1 : shadow pcm + 3k, addr t0+t3 *)
  eapply cl1 with (A := pcm + 3 * (ch * ns + s)) (k := kp0);
    [ rewrite Ht0, Ht3; ring | lia | exact Mp0 | exact Sp0 |].
  intros wa1 wa12 w30 Ea1.
  (* cl2 : shadow pcm + 3k + 1, data b0 at pcm+3k *)
  eapply cl2 with (A := pcm + 3 * (ch * ns + s)) (Dd := pcm + 3 * (ch * ns + s)) (k := kp1) (b0 := pb (3 * (ch * ns + s)));
    [ exact Ea1 | lia | replace (pcm + 3 * (ch * ns + s) + 1) with (pcm + (3 * (ch * ns + s) + 1)) by ring; exact Mp1
    | replace (pcm + 3 * (ch * ns + s) + 1) with (pcm + (3 * (ch * ns + s) + 1)) by ring; exact Sp1
    | rewrite Hs6, Ht3; ring | lia | exact M0 |].
  intros w12 w25 w26 w31 Et6.
  (* cl3 : shadow pcm + 3k + 2, data b1 at pcm+3k+1 *)
  eapply cl3 with (A := pcm + 3 * (ch * ns + s)) (Dd := pcm + 3 * (ch * ns + s)) (k := kp2) (b1 := pb (3 * (ch * ns + s) + 1));
    [ exact Ea1 | lia | replace (pcm + 3 * (ch * ns + s) + 2) with (pcm + (3 * (ch * ns + s) + 2)) by ring; exact Mp2
    | replace (pcm + 3 * (ch * ns + s) + 2) with (pcm + (3 * (ch * ns + s) + 2)) by ring; exact Sp2
    | exact Et6 | replace (pcm + 3 * (ch * ns + s) + 1) with (pcm + (3 * (ch * ns + s) + 1)) by ring; exact M1 |].
  intros wa1b w25b w26b Ea1b.
  (* cls4 : shadow store target P+4k, data b2 at pcm+3k+2 *)
  eapply cls4 with (A := P + 4 * (ch * ns + s)) (Dd := pcm + 3 * (ch * ns + s)) (k := ks) (b2 := pb (3 * (ch * ns + s) + 2));
    [ exact Ha0 | lia | exact Ms | exact Ss | exact Et6
    | replace (pcm + 3 * (ch * ns + s) + 2) with (pcm + (3 * (ch * ns + s) + 2)) by ring; exact M2 |].
  intros w25c w31c.
  (* assemble (9 int ops), then abstract the fcvt input before the FP store to keep it symbolic *)
  clear M0 M1 M2 Mp0 Mp1 Mp2 Sp0 Sp1 Sp2 Ms Ss NN B1 B1' Hmc Bn.
  do 10 step.
  match goal with |- context [fcvt_s_w ?md ?w] => remember w as W eqn:EW end.
  do 3 step.
  apply K; [ fct | fct | fct | assumption |].
  eapply crt_inv_P; [ exact Hinv | lia | lia | exact Ht4 |].
  unfold cv. apply conv_bytes;
    [ exact H15
    | rewrite EW; apply (comb _ _ _ (Z_to_bv 64 18446744073692774400)); apply unsigned_lit; lia ].
Qed.
Lemma crt_inner : forall ch (t0 t1 t2 a3 s6 : word),
  0 <= ch < nch ->
  bv_unsigned t0 = pcm + 3 * ns * ch -> bv_unsigned s6 = pcm + 3 * ns * ch -> bv_unsigned a3 = ch ->
  (forall (a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
     unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc -> crt_inv m ((ch + 1) * ns) (ch + 1) ->
     evt rsegs G (CST (CRT_AT 0x1d8) t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m)) ->
  forall n s (a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  0 <= s -> s + Z.of_nat (S n) = ns ->
  bv_unsigned a0 = P + 4 * (ch * ns + s) -> bv_unsigned t4 = P + 4 * (ch * ns + s) -> bv_unsigned t3 = 3 * s ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc -> crt_inv m (ch * ns + s) (ch + 1) ->
  evt rsegs G (CST (CRT_AT 0x10c) t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m).
Proof.
  intros ch t0 t1 t2 a3 s6 Hch Ht0 Hs6 Ha3 K n.
  pose proof crt_nn as NN.
  assert (SB : 0 <= ch * ns) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SB2 : (ch + 1) * ns = ch * ns + ns) by ring.
  induction n as [|n IH];
    intros s a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m Hs0 Hsn Ha0 Ht4 Ht3 H15 Hfc Hinv.
  - apply (crt_body ch s t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m);
      try assumption; [lia |].
    intros a0' a1' a2' s9' s10' t3' t4' t5' t6' v fc' m' Ha0' Ht3' Ht4' Hfc' Hinv'.
    step. take false. step.
    apply K; [rewrite freg_get_other by reflexivity; exact H15 | exact Hfc' | replace ((ch + 1) * ns) with (ch * ns + s + 1) by lia; exact Hinv'].
  - apply (crt_body ch s t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m);
      try assumption; [lia |].
    intros a0' a1' a2' s9' s10' t3' t4' t5' t6' v fc' m' Ha0' Ht3' Ht4' Hfc' Hinv'.
    step. take true.
    apply (IH (s + 1) a0' a1' a2' s9' s10' t3' t4' t5' t6' (bvmap_set (Z_to_bv 5 14) v Fh) fc' m');
      [lia | lia | rewrite Ha0'; lia | rewrite Ht4'; lia | rewrite Ht3'; lia | rewrite freg_get_other by reflexivity; exact H15
      | exact Hfc' | replace (ch * ns + (s + 1)) with (ch * ns + s + 1) by lia; exact Hinv'].
Qed.

Lemma crt_outer : forall n ch (t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  0 <= ch -> ch + Z.of_nat (S n) = nch ->
  bv_unsigned t0 = pcm + 3 * ns * ch -> bv_unsigned s6 = pcm + 3 * ns * ch -> bv_unsigned a3 = ch ->
  bv_unsigned t1 = P + 4 * ns * ch -> bv_unsigned t2 = P + 4 * ns * ch ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc -> crt_inv m (ch * ns) ch ->
  (forall (a0' a1' a2' a3' s6' t0' t1' t2' s9' s10' t3' t4' t5' t6' : word) (Fh' : bvmap 5 word) (fc' : bv 32) m',
     bv_unsigned a3' = nch -> frm0 fc' -> crt_inv m' (nch * ns) nch ->
     evt rsegs G (CST (CRT_AT 0x1f0) t0' t1' t2' a0' a1' a2' a3' s6' s9' s10' t3' t4' t5' t6' Fh' fc' m')) ->
  evt rsegs G (CST (CRT_AT 0xd4) t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m).
Proof.
  intros n. induction n as [|n IH];
    intros ch t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m
      Hc0 Hcn Ht0 Hs6 Ha3 Ht1 Ht2 H15 Hfc Hinv K;
    pose proof crt_nn as NN;
    assert (Hch : 0 <= ch < nch) by lia;
    assert (B0 : 0 <= ch * ns) by (apply Z.mul_nonneg_nonneg; lia);
    assert (Bcns : ch * ns <= (nch - 1) * ns) by (apply Z.mul_le_mono_nonneg_r; lia);
    assert (Bcns' : (nch - 1) * ns = nch * ns - ns) by ring;
    destruct (crt_sh_store8 m (ch * ns) ch ch Hinv Hch) as (kq0 & Mq & Sq);
    pose proof (crt_stQ m (ch * ns) ch Hinv Hch) as HSq;
    do 2 step;
    (eapply csh_q8 with (A := Q + 8 * ch) (k := kq0);
       [ rewrite Ha3; repeat first [ rewrite Z.shiftl_mul_pow2 by lia | match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end ]; lia | lia | exact Mq | exact Sq | ]);
    intros wq;
    do 3 step; step; step; take false; do 3 step;
    (eapply crt_inner with (ch := ch) (n := Z.to_nat (ns - 1)) (s := 0);
       [ exact Hch | exact Ht0 | exact Hs6 | exact Ha3
       | | lia | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
       | rewrite Ht2; f_equal; ring
       | rewrite Ht1; f_equal; ring | reflexivity | exact H15 | exact Hfc
       | replace (ch * ns + 0) with (ch * ns) by lia; eapply crt_inv_Q;
           [ exact Hinv | lia | lia
           | unfold wa; apply unsigned_lit; lia
           | rewrite Ha3; repeat first [ rewrite Z.shiftl_mul_pow2 by lia | match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end ]; lia ] ]);
    intros a0' a1' a2' s9' s10' t3' t4' t5' t6' Fh' fc' m' Hunbox' Hfc' Hinv';
    do 5 step; step.
  - take false.
    apply K; [ rewrite (unsigned_lit (bv_unsigned a3 + 1)) by lia; rewrite Ha3; lia | exact Hfc' | replace nch with (ch + 1) by lia; exact Hinv' ].
  - take true.
    apply (IH (ch + 1));
      [ lia
      | rewrite Nat2Z.inj_succ in Hcn |- *; lia
      | rewrite Ht0; rewrite unsigned_lit by nia; nia
      | rewrite Hs6; rewrite unsigned_lit by nia; nia
      | rewrite (unsigned_lit (bv_unsigned a3 + 1)) by lia; lia
      | rewrite Ht1; rewrite unsigned_lit by nia; nia
      | rewrite Ht2; rewrite unsigned_lit by nia; nia
      | exact Hunbox' | exact Hfc'
      | exact Hinv' | exact K ].
Qed.

End Loops.

