(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition kLowMemEnd : Z := 0x7fff7fff.
Definition kHighShadowEnd : Z := 0x10007fff7fff.
Definition kHighMemEnd : Z := 0x7fffffffffff.

Definition m2s_cells (m : mem) : Prop :=
rw_cells bsegs m 0xfc118 [C8 (Z_to_bv 64 0x105ab8); C8 (Z_to_bv 64 0x1067a8); C8 (Z_to_bv 64 0x1067b0); C8 (Z_to_bv 64 0x1067a0)]
/\ rw_cells bsegs m 0x105ab8 [C8 (Z_to_bv 64 SHB)]
/\ rw_cells bsegs m 0x1067a0 [C8 (Z_to_bv 64 kHighMemEnd); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition addr_in_mem (p : Z) : Prop := (0 <= p <= kLowMemEnd)%Z \/ (kHighShadowEnd < p <= kHighMemEnd)%Z.

Definition m2s_stmt (entry : Z) : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p : Z),
a0 = Z_to_bv 64 p -> addr_in_mem p ->
m2s_cells m -> mem_inv bsegs m ->
evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (shad p) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Lemma m2s_54d48_spec : m2s_stmt 0x699dc.
Proof.
unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
do 8 zstep.
if_cases K; zify_cond K.
-
do 3 zstep.
replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
finish.
-
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

Lemma m2s_3d1d8_spec : m2s_stmt 0x51fac.
Proof.
unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
do 8 zstep.
if_cases K; zify_cond K.
-
do 3 zstep.
replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
finish.
-
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

Lemma m2s_53700_spec : m2s_stmt 0x67cd8.
Proof.
unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
do 8 zstep.
if_cases K; zify_cond K.
-
do 3 zstep.
replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
finish.
-
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

Lemma m2s_5dc34_spec : m2s_stmt 0x72d68.
Proof.
unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
do 8 zstep.
if_cases K; zify_cond K.
-
do 3 zstep.
replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
finish.
-
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
End B_TWIN.

Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition kLowMemEnd : Z := 0x7fff7fff.
Definition kHighShadowEnd : Z := 0x10007fff7fff.
Definition kHighMemEnd : Z := 0x7fffffffffff.

Definition m2s_cells (m : mem) : Prop :=
rw_cells asegs m 0xf3898 [C8 (Z_to_bv 64 0xfd278); C8 (Z_to_bv 64 0xfdf68); C8 (Z_to_bv 64 0xfdf70); C8 (Z_to_bv 64 0xfdf60)]
/\ rw_cells asegs m 0xfd278 [C8 (Z_to_bv 64 SHB)]
/\ rw_cells asegs m 0xfdf60 [C8 (Z_to_bv 64 kHighMemEnd); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition addr_in_mem (p : Z) : Prop := (0 <= p <= kLowMemEnd)%Z \/ (kHighShadowEnd < p <= kHighMemEnd)%Z.

Definition m2s_stmt (entry : Z) : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p : Z),
a0 = Z_to_bv 64 p -> addr_in_mem p ->
m2s_cells m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (shad p) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma m2s_54d48_spec : m2s_stmt 0x698f0.
Proof.
unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
do 8 zstep.
if_cases K; zify_cond K.
-
do 3 zstep.
replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
finish.
-
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

Lemma m2s_3d1d8_spec : m2s_stmt 0x51ec0.
Proof.
unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
do 8 zstep.
if_cases K; zify_cond K.
-
do 3 zstep.
replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
finish.
-
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

Lemma m2s_53700_spec : m2s_stmt 0x67bec.
Proof.
unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
do 8 zstep.
if_cases K; zify_cond K.
-
do 3 zstep.
replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
finish.
-
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

Lemma m2s_5dc34_spec : m2s_stmt 0x72c7c.
Proof.
unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
do 8 zstep.
if_cases K; zify_cond K.
-
do 3 zstep.
replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
finish.
-
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
