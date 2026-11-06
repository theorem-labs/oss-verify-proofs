(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bndiv/lib/A/R_m2s.v, with its module paths and addresses changed; 2 of its 134 lines of code are new or changed and 1 line of the source is left out. *)
(* Modified by Theorem Labs, 2026-10: moved from image B (fuzz_preset.asan-ubsan f8f98a95), commit 3244f5c71f6, to the #102 pin B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5): 10 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-B-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan-ubsan (image B, f8f98a95) from commit 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/R_m2s.v: module paths (lib/A/Bz -> lib/AU/PSnpBz), the image binding Asan -> AsanUbsan, and 10 address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97, --build asan-ubsan --from-build asan), each by symbol + offset in both images (per-numeral report: the relocation record, reloc-B). *)
(* Ported by the runtime port from commit affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/R_m2s.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A Require Import Shadow R_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition kLowMemEnd : Z := 0x7fff7fff.
Definition kHighShadowEnd : Z := 0x10007fff7fff.
Definition kHighMemEnd : Z := 0x7fffffffffff.

(* [comment removed for export] *)
Definition m2s_cells (m : mem) : Prop :=
  rw_cells asegs m 0xa2850 [C8 (Z_to_bv 64 0xab6f8); C8 (Z_to_bv 64 0xac3e8); C8 (Z_to_bv 64 0xac3f0); C8 (Z_to_bv 64 0xac3e0)]
  /\ rw_cells asegs m 0xab6f8 [C8 (Z_to_bv 64 SHB)]
  /\ rw_cells asegs m 0xac3e0 [C8 (Z_to_bv 64 kHighMemEnd); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition addr_in_mem (p : Z) : Prop := (0 <= p <= kLowMemEnd)%Z \/ (kHighShadowEnd < p <= kHighMemEnd)%Z.

Definition m2s_stmt (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p : Z),
  a0 = Z_to_bv 64 p -> addr_in_mem p ->
  m2s_cells m -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (shad p) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma m2s_54d48_spec : m2s_stmt 0x54f08.
Proof.
  unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
  do 8 zstep.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 3 zstep.
    replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
      by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
    finish.
  - (* [comment removed for export] *)
    assert (HH : (17594333495295 < p <= 140737488355327)%Z).
    { assert (E : (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879 = 2147450879)%Z)
        by reflexivity.
      rewrite E in K. destruct HP as [HP|HP]; [lia|exact HP]. }
    clear HP K.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 p)) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit p) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 6 zstep.
    assert (C2 : bv_ltu (Z_to_bv 64 140737488355327) (Z_to_bv 64 p) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. }
    rewrite C2; cbv iota.
    do 1 zstep.
    assert (C3 : negb (bv_ltu (Z_to_bv 64 17594333495295) (Z_to_bv 64 p)) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply negb_false_iff, Z.ltb_lt. lia. }
    rewrite C3; cbv iota.
    do 3 zstep.
    replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
      by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
    finish.
Qed.

(* [comment removed for export] *)

Lemma m2s_53700_spec : m2s_stmt 0x53578.
Proof.
  unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
  do 8 zstep.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 3 zstep.
    replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
      by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
    finish.
  - (* [comment removed for export] *)
    assert (HH : (17594333495295 < p <= 140737488355327)%Z).
    { assert (E : (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879 = 2147450879)%Z)
        by reflexivity.
      rewrite E in K. destruct HP as [HP|HP]; [lia|exact HP]. }
    clear HP K.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 p)) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit p) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 6 zstep.
    assert (C2 : bv_ltu (Z_to_bv 64 140737488355327) (Z_to_bv 64 p) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. }
    rewrite C2; cbv iota.
    do 1 zstep.
    assert (C3 : negb (bv_ltu (Z_to_bv 64 17594333495295) (Z_to_bv 64 p)) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply negb_false_iff, Z.ltb_lt. lia. }
    rewrite C3; cbv iota.
    do 3 zstep.
    replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
      by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
    finish.
Qed.

Lemma m2s_5dc34_spec : m2s_stmt 0x5ddf4.
Proof.
  unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
  do 8 zstep.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 3 zstep.
    replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
      by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
    finish.
  - (* [comment removed for export] *)
    assert (HH : (17594333495295 < p <= 140737488355327)%Z).
    { assert (E : (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879 = 2147450879)%Z)
        by reflexivity.
      rewrite E in K. destruct HP as [HP|HP]; [lia|exact HP]. }
    clear HP K.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 p)) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit p) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 6 zstep.
    assert (C2 : bv_ltu (Z_to_bv 64 140737488355327) (Z_to_bv 64 p) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. }
    rewrite C2; cbv iota.
    do 1 zstep.
    assert (C3 : negb (bv_ltu (Z_to_bv 64 17594333495295) (Z_to_bv 64 p)) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply negb_false_iff, Z.ltb_lt. lia. }
    rewrite C3; cbv iota.
    do 3 zstep.
    replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
      by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
    finish.
Qed.
