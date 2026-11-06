(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YCct YC4z YCcq YCcp YCcv YCcw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rf_byte_rng : forall z, 0 <= z mod 256 < 256.
Proof. intros z. apply Z.mod_pos_bound. lia. Qed.
Lemma rf_obj_of_region : forall E m b cs lo hi wlo whi e0 e8 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 v0 v8,
region_ok trasegs E m (YQ0b.mkRegion (Some 11%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 11) = b ->
In (YQ0b.mkChunk 0 (CVal 8 e0)) cs -> In (YQ0b.mkChunk 8 (CVal 4 e8)) cs ->
In (YQ0b.mkChunk 12 (CVal 1 e12)) cs -> In (YQ0b.mkChunk 13 (CVal 1 e13)) cs -> In (YQ0b.mkChunk 14 (CVal 1 e14)) cs -> In (YQ0b.mkChunk 15 (CVal 1 e15)) cs ->
In (YQ0b.mkChunk 16 (CVal 1 e16)) cs -> In (YQ0b.mkChunk 17 (CVal 1 e17)) cs -> In (YQ0b.mkChunk 18 (CVal 1 e18)) cs -> In (YQ0b.mkChunk 19 (CVal 1 e19)) cs ->
In (YQ0b.mkChunk 20 (CVal 1 e20)) cs -> In (YQ0b.mkChunk 21 (CVal 1 e21)) cs ->
sv_denot E e0 = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> sv_denot E e8 = Z_to_bv 64 v8 -> 0 <= v8 < 2 ^ 32 ->
exists fattr fgen delay, obj_at trasegs m b LAY_RgbFrameConfig [v0; v8; fattr; fgen; delay].
Proof.
intros E m b cs lo hi wlo whi e0 e8 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 v0 v8 HR Hb I0 I8 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 D0 R0 D8 R8.
pose proof (field_of_region E m 11 b cs lo hi wlo whi 0 8%N e0 v0 HR Hb I0 D0 ltac:(exact R0) ltac:(cbn; lia)) as V0.
pose proof (field_of_region E m 11 b cs lo hi wlo whi 8 4%N e8 v8 HR Hb I8 D8 ltac:(exact R8) ltac:(cbn; lia)) as V8.
pose proof (byte_of_region E m 11 b cs lo hi wlo whi 12 e12 HR Hb I12) as V12. pose proof (byte_of_region E m 11 b cs lo hi wlo whi 13 e13 HR Hb I13) as V13.
pose proof (byte_of_region E m 11 b cs lo hi wlo whi 14 e14 HR Hb I14) as V14. pose proof (byte_of_region E m 11 b cs lo hi wlo whi 15 e15 HR Hb I15) as V15.
pose proof (byte_of_region E m 11 b cs lo hi wlo whi 16 e16 HR Hb I16) as V16. pose proof (byte_of_region E m 11 b cs lo hi wlo whi 17 e17 HR Hb I17) as V17.
pose proof (byte_of_region E m 11 b cs lo hi wlo whi 18 e18 HR Hb I18) as V18. pose proof (byte_of_region E m 11 b cs lo hi wlo whi 19 e19 HR Hb I19) as V19.
pose proof (byte_of_region E m 11 b cs lo hi wlo whi 20 e20 HR Hb I20) as V20. pose proof (byte_of_region E m 11 b cs lo hi wlo whi 21 e21 HR Hb I21) as V21.
set (b12 := bv_unsigned (sv_denot E e12) mod 256) in *. set (b13 := bv_unsigned (sv_denot E e13) mod 256) in *.
set (b14 := bv_unsigned (sv_denot E e14) mod 256) in *. set (b15 := bv_unsigned (sv_denot E e15) mod 256) in *.
set (b16 := bv_unsigned (sv_denot E e16) mod 256) in *. set (b17 := bv_unsigned (sv_denot E e17) mod 256) in *.
set (b18 := bv_unsigned (sv_denot E e18) mod 256) in *. set (b19 := bv_unsigned (sv_denot E e19) mod 256) in *.
set (b20 := bv_unsigned (sv_denot E e20) mod 256) in *. set (b21 := bv_unsigned (sv_denot E e21) mod 256) in *.
pose proof (rf_byte_rng (bv_unsigned (sv_denot E e12))) as Q12. pose proof (rf_byte_rng (bv_unsigned (sv_denot E e13))) as Q13.
pose proof (rf_byte_rng (bv_unsigned (sv_denot E e14))) as Q14. pose proof (rf_byte_rng (bv_unsigned (sv_denot E e15))) as Q15.
pose proof (rf_byte_rng (bv_unsigned (sv_denot E e16))) as Q16. pose proof (rf_byte_rng (bv_unsigned (sv_denot E e17))) as Q17.
pose proof (rf_byte_rng (bv_unsigned (sv_denot E e18))) as Q18. pose proof (rf_byte_rng (bv_unsigned (sv_denot E e19))) as Q19.
pose proof (rf_byte_rng (bv_unsigned (sv_denot E e20))) as Q20. pose proof (rf_byte_rng (bv_unsigned (sv_denot E e21))) as Q21.
fold b12 in Q12. fold b13 in Q13. fold b14 in Q14. fold b15 in Q15. fold b16 in Q16. fold b17 in Q17. fold b18 in Q18. fold b19 in Q19. fold b20 in Q20. fold b21 in Q21.
replace (b + 13) with (b + 12 + 1) in V13 by lia. replace (b + 15) with (b + 14 + 1) in V15 by lia.
replace (b + 17) with (b + 16 + 1) in V17 by lia. replace (b + 19) with (b + 18 + 1) in V19 by lia. replace (b + 21) with (b + 20 + 1) in V21 by lia.
pose proof (val_mem_bytes2 m (b + 12) b12 b13 V12 V13 Q12 Q13) as H12. pose proof (val_mem_bytes2 m (b + 14) b14 b15 V14 V15 Q14 Q15) as H14.
pose proof (val_mem_bytes2 m (b + 16) b16 b17 V16 V17 Q16 Q17) as H16. pose proof (val_mem_bytes2 m (b + 18) b18 b19 V18 V19 Q18 Q19) as H18.
pose proof (val_mem_bytes2 m (b + 20) b20 b21 V20 V21 Q20 Q21) as H20.
replace (b + 14) with (b + 12 + 2) in H14 by lia. replace (b + 18) with (b + 16 + 2) in H18 by lia.
pose proof (val_mem_half2 m (b + 12) _ _ H12 H14 ltac:(lia) ltac:(lia)) as F12.
pose proof (val_mem_half2 m (b + 16) _ _ H16 H18 ltac:(lia) ltac:(lia)) as F16.
exists (b12 + 256 * b13 + 65536 * (b14 + 256 * b15)), (b16 + 256 * b17 + 65536 * (b18 + 256 * b19)), (b20 + 256 * b21).
unfold LAY_RgbFrameConfig. cbn [obj_at]. unfold field_ok. cbn [fst snd]. change (N.to_nat 8) with 8%nat in *. change (N.to_nat 4) with 4%nat in *. change (N.to_nat 2) with 2%nat.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with 4294967296. change (2 ^ (8 * Z.of_N 2)) with 65536. change (2 ^ 32) with 4294967296 in R8.
repeat split; try assumption; try lia.
Qed.
End a.
Ltac rf_chunk_e cs od :=
lazymatch eval cbv in (find (fun c => Z.eqb (YQ0b.c_off c) od) cs) with
| Some (YQ0b.mkChunk _ (CVal _ ?e)) => e
end.
Ltac rf_obj_at HS B11 v0 tac0 v8 tac8 OBJ :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hx ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baseA rs 11%nat in
let r := eval vm_compute in (nth i rs got_region) in
let HRd := fresh "HRd" in
pose proof (st_ok_region_nth Ex ssx (restrict Hx msX) i r HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
lazymatch type of HRd with region_ok _ _ _ (YQ0b.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let e0 := rf_chunk_e cs 0 in let e8 := rf_chunk_e cs 8 in
let e12 := rf_chunk_e cs 12 in let e13 := rf_chunk_e cs 13 in let e14 := rf_chunk_e cs 14 in let e15 := rf_chunk_e cs 15 in
let e16 := rf_chunk_e cs 16 in let e17 := rf_chunk_e cs 17 in let e18 := rf_chunk_e cs 18 in let e19 := rf_chunk_e cs 19 in
let e20 := rf_chunk_e cs 20 in let e21 := rf_chunk_e cs 21 in
pose proof (rf_obj_of_region Ex _ _ cs lo hi wlo whi e0 e8 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 v0 v8 HRd B11
ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto)
ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto)
ltac:(tac0) ltac:(lia) ltac:(tac8) ltac:(lia)) as OBJ end;
clear HRd end.
Ltac rf_stream_words HS B10 E33 E34 cur2 dtac Vp Vn Vc :=
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baseA rs 10%nat in let i := eval vm_compute in i in
lazymatch eval vm_compute in (nth i rs got_region) with YQ0b.mkRegion _ _ _ _ _ ?cs =>
let e16 := rf_chunk_e cs 16 in
lazymatch type of B10 with _ = ?st =>
lazymatch type of E33 with _ = Z_to_bv 64 ?pd => lazymatch type of E34 with _ = Z_to_bv 64 ?nbv =>
field_atD HS i 10%nat st B10 0 8%N (SOff 33 0) pd ltac:(rewrite sv_denot_SOff0; exact E33) Vp;
field_atD HS i 10%nat st B10 8 8%N (SOff 34 0) nbv ltac:(rewrite sv_denot_SOff0; exact E34) Vn;
field_atD HS i 10%nat st B10 16 8%N e16 cur2 dtac Vc end end end end end.
