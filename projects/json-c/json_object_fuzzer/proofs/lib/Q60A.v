(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7b.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AKeyStr.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Lemma key_stringA : forall A LB LM FRS B m md kp kn ks,
HEAPAx A LB LM FRS B m md -> In (kp, kn) LB -> cstr asegs m kp kn ks ->
exists slack, bytes_at asegs m kp (ks ++ Z_to_bv 8 0 :: slack) /\
(- (kp + Z.of_nat (length ks) + 1)) mod 8 <= Z.of_nat (length slack) /\
~ In (Z_to_bv 8 0) ks /\ kp mod 16 = 0 /\ Z.of_nat (length ks) + 1 <= kn /\ 0 < kp /\ kp + kn <= alloc_ceiling /\
kp + Z.of_nat (length ks) + 1 + Z.of_nat (length slack) <= alloc_ceiling.
Proof.
intros A LB LM FRS B m md kp kn ks HP Hin (CL & CNZ & junk & CB).
assert (HinX : In (kp, kn) (LB ++ LM)) by (apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ kp kn HP HinX) as (Hn0 & Hal & Hlo & Hhi & _).
destruct (heapA_blk_slack A4L HIx _ _ _ _ _ _ _ kp kn HP HinX) as [g [G Lg]]. cbn [hl_segs hla_base A4L A4H] in G.
assert (NN : ~ In (Z_to_bv 8 0) ks).
{ intros X. rewrite Forall_forall in CNZ. apply (CNZ _ X). reflexivity. }
assert (LENB : length (ks ++ [Z_to_bv 8 0] ++ junk) = Z.to_nat kn) by (destruct CB as [[[Hwf _] _] _]; exact Hwf).
rewrite !length_app in LENB. cbn [length] in LENB.
assert (BB : bytes_at asegs m kp (ks ++ [Z_to_bv 8 0] ++ junk)).
{ destruct CB as [[[_ _] HB] _]. cbn in HB. rewrite app_nil_r in HB. exact HB. }
exists (junk ++ g).
assert (B2 : bytes_at asegs m kp ((ks ++ [Z_to_bv 8 0] ++ junk) ++ g)).
{ apply bytes_at_app. split; [exact BB|]. rewrite !length_app. cbn [length].
replace (kp + Z.of_nat (length ks + (1 + length junk))) with (kp + kn) by lia. exact G. }
replace ((ks ++ [Z_to_bv 8 0] ++ junk) ++ g) with (ks ++ Z_to_bv 8 0 :: junk ++ g) in B2 by (rewrite <- !app_assoc; reflexivity).
pose proof alloc_ceiling_al16 as C16.
split; [exact B2|]. split; [| split; [exact NN | split; [exact Hal | split; [exact CL | split; [exact Hlo | split; [exact Hhi|]]]]]].
- rewrite length_app.
replace (Z.of_nat (length junk + length g)) with ((kn - Z.of_nat (length ks) - 1) + Z.of_nat (length g)) by lia.
rewrite Lg.
set (x := kp + Z.of_nat (length ks) + 1) in *.
pose proof (Z.div_mod kn 16 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound kn 16 ltac:(lia)) as B1.
pose proof (Z.div_mod kp 16 ltac:(lia)) as E2. rewrite Hal in E2.
pose proof (Z.div_mod (16 - kn mod 16) 16 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (16 - kn mod 16) 16 ltac:(lia)) as B3.
pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E4. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B4.
set (rn := kn mod 16) in *. set (r8 := (- x) mod 8) in *.
set (qn := kn / 16) in *. set (qb := kp / 16) in *. set (q3 := (16 - rn) / 16) in *. set (q8 := - x / 8) in *.
nia.
- rewrite length_app. rewrite Nat2Z.inj_add, Lg.
pose proof (Z.div_mod kn 16 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound kn 16 ltac:(lia)) as B1.
pose proof (Z.div_mod kp 16 ltac:(lia)) as E2. rewrite Hal in E2.
pose proof (Z.div_mod (16 - kn mod 16) 16 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (16 - kn mod 16) 16 ltac:(lia)) as B3.
unfold alloc_ceiling in *. pose proof (Z.div_mod rc_ceil 16 ltac:(lia)) as E5.
set (rn := kn mod 16) in *. set (qn := kn / 16) in *. set (qb := kp / 16) in *. set (q3 := (16 - rn) / 16) in *. set (qc := rc_ceil / 16) in *.
nia.
Qed.
End AKeyStr.
End RC__1.
