(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz QO3A Q7m0 QSpR QuJV QCPB QH7x QXup UEQM Lib.GwApply QWxq Qfw3 QRjH QHnV QCcH QfLs Q0Ek QjDH UC8c Qsw7 QJjn UBpZ UT7i Uv6q U7zy UD4E UzWc Qio9 QHXC Qfe5 QId5 Uuoa UfJh QBGG ULch UrM1 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0 Qfw3.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UBpZ UT7i Uv6q U7zy UD4E.
Import UzWc.
Import Qio9 QHXC Qfe5 QId5.
Import Uuoa UfJh.
Import QBGG.
Import Uuoa.Mq0 ULch.Mq0 UrM1.
Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma neg_lit64 : forall z, Z_to_bv 64 (18446744073709551615 * bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite Z.mul_mod_idemp_r by lia. replace (18446744073709551615 * z) with (- z + z * 18446744073709551616) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
#[using="Type"] Lemma mul_m1_lit : forall z, mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 z) = Z_to_bv 64 (- z).
Proof.
intros z. change (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 z)) with (bv_mul (Z_to_bv 64 (-1)) (Z_to_bv 64 z)).
apply bv_eq. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite <- Z.mul_mod by lia. f_equal; ring.
Qed.
#[using="Type"] Lemma neg_chk_ok : forall len, -2^31 < len < 0 ->
negb (bv_eqb (alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 len)) (alu64 ALU_SLT (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 len)) (Z_to_bv 64 0))) = false.
Proof.
intros len H. rewrite mul_m1_lit.
assert (EA : alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 len) = Z_to_bv 64 0).
{ rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite !signed_lit by lia. replace (0 <? len) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
assert (EB : alu64 ALU_SLT (Z_to_bv 64 (- len)) (Z_to_bv 64 0) = Z_to_bv 64 0).
{ rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite !signed_lit by lia. replace (- len <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite EA, EB. reflexivity.
Qed.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (Z_to_bv 64 JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (Z_to_bv 64 JHEX_SLOT)).

#[using="MEMMOVE HEXP HT63 HGOT"] Lemma ser_str_inline : ser_spec HIx SER_STR (Sstr false).
Proof.
unfold ser_spec. intros until errv. intros HP PB JN INCL LBS FL Hlv Hlvd ST LO LOS SPA HT ERR TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (len & str & junk & EREST & Hlen0 & SRCL & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp. unfold TP, SER_STR, Uuoa.Mq0.ERRNO in *. unfold ser_budget in LOS. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INpL : In (p, str_objsize len) LB) by (apply INCL; rewrite EREST; left; reflexivity).
assert (INp : In (p, str_objsize len) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INpL).
pose proof (heap_blk S4L HIx _ _ _ _ p _ HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold str_objsize in Hphi, INp, INpL, NODE.
assert (Rlen : 0 <= len < 2147483648) by lia.
unfold_consts.
destruct FL as [Rfl FL56]. destruct (land56_bits fl FL56) as (FL32 & FL16 & FL8).
assert (Rfl64 : 0 <= fl < 2^64) by lia.
destruct PB as (Hbp & Hcap & Hln & PBS & PBUF).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
assert (NODE0 : True -> rw_cells rsegs m p
[C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string S4F)); C8 (Z_to_bv 64 pb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 len); CB (Z.to_nat (49 + Z.max len 8 - 48)) (str ++ [Z_to_bv 8 0] ++ junk)]) by (intros _; exact NODE).
apply rz_evt; [exact MOK|].
carve_frame 48%nat ST.
symb_run 40%nat [MEMAPPEND] [false; false; true].
2,3: sc_cbn; first [ apply br_and_zero; [exact Rfl64 | lia | exact FL32] | apply brne_and_zero; [lia | lia | exact (land7_of_mod16 p Hpal)] ].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
lazymatch type of FR with rw_cells _ _ _ ?cs => assert (INV1 : ser_mem HIx sp m md LB pb lo (bv_unsigned sp + -48) cs m1 md) end.
{ exists A, buf, cap, bpos, content, errv.
split; [exact HP1|]. split; [split; [lia|]; split; [lia|]; split; [exact Hln|]; split; [exact PBS|exact PBUF]|].
split; [exact FR|]. split; [exact ERR|]. split; [exact ST|]. split; [exact HPR1 | apply model_vm_only_refl]. }
clear HP1 HPR1 MU WM.
destruct (ro_src m1 0x1239c [Z_to_bv 8 34] LB 1 (bv_unsigned sp + -48) MI1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m md LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 34]);
[ exact INV1 | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
pose proof INV2 as INV2'. destruct INV2 as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FR2c & ERR2 & ST2 & HPR2 & VM2).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2. unfold Uuoa.Mq0.ERRNO in ERR2.
assert (NODE2 : rw_cells rsegs m2 p
[C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string S4F)); C8 (Z_to_bv 64 pb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 len); CB (Z.to_nat (49 + Z.max len 8 - 48)) (str ++ [Z_to_bv 8 0] ++ junk)]).
{ eapply (heap_pres_rw_cells S4L); [exact HPR2 | exact (NODE0 I) |]. right; right. exists (p, 49 + Z.max len 8). split; [exact INpL|]. cbn. lia. }
apply rz_evt; [exact MOK2|].
symb_run 40%nat [ESCAPE] (@nil bool).

assert (SRC2 : bytes_at rsegs m2 (p + 48) str).
{ lazymatch type of NODE2 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
pose proof (proj1 (rw_cells_app rsegs m2 p [c1; c2; c3; c4; c5; c6; c7] rest) NODE2) as [_ ND] end.
cbn [cells_size csize Nat.add] in ND. change (Z.of_nat 48) with 48 in ND.
pose proof (rw_cells_bytes_at rsegs m2 _ _ ND) as BY. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY.
exact (proj1 (proj1 (bytes_at_app rsegs m2 _ _ _) BY)). }
apply evt_RZ_done.
eapply (ser_escape HIx MEMMOVE HEXP HT63 HGOT sp gp m md LB pb lo LO HT) with (F := F) (src := str);
[ exact INV2' | exact SRC2 | exact SRCL | lia | lia | lia
| left; right; right; exists (p, 49 + Z.max len 8); split; [exact INpL | cbn; lia]
| lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | rewrite unsigned_lit by lia; exact FL16 | ].
intros m3 md3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 INV3 FS3 FR3 _.
pose proof (ser_mem_model_ok _ _ _ _ _ _ _ _ _ _ _ INV3) as MOK3. pose proof (ser_mem_mem_inv _ _ _ _ _ _ _ _ _ _ _ INV3) as MI3.
apply rz_evt; [exact MOK3|].
symb_run 40%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m3 0x1239c [Z_to_bv 8 34] LB 1 (bv_unsigned sp + -48) MI3 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBr SBCr].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m md LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 34]);
[ exact INV3 | exact SBr | reflexivity | lia | lia | lia | exact SBCr | left; lia | lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FR3 | ].
intros m4 md4 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F4 fc4 INV4 FS4 FR4 _.
destruct INV4 as (A4 & buf4 & cap4 & bpos4 & content4 & errv4 & HP4 & PB4 & FR4c & ERR4 & ST4 & HPR4 & VM4).
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4. unfold Uuoa.Mq0.ERRNO in ERR4.
apply rz_evt; [exact MOK4|].
symb_run 40%nat (@nil Z) [true].
step.
apply evt_RZ_done. apply K. unfold ser_post.
exists m4, A4. eexists. exists errv4, buf4, cap4, bpos4, content4.
split; [| split; [exact VM4 | split; [| split; [exact HPR4 | split; [exact ERR4 | split; [exact HP4 | exact PB4]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -48 + 48)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
apply ret_statew_intro; [exact FS4 | intros _; exact FR4].
- release_frame FR4c ST4 (bv_unsigned sp). exact ST4.
Qed.

#[using="MEMMOVE HEXP HT63 HGOT"] Lemma ser_str_heap : ser_spec HIx SER_STR (Sstr true).
Proof.
unfold ser_spec. intros until errv. intros HP PB JN INCL LBS FL Hlv Hlvd ST LO LOS SPA HT ERR TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (len & pd & pdn & str & junk2 & EREST & Hlen0 & SRCL & Hpdn & NODE & DATA). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp. unfold TP, SER_STR, Uuoa.Mq0.ERRNO in *. unfold ser_budget in LOS. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INpL : In (p, 56) LB) by (apply INCL; rewrite EREST; left; reflexivity).
assert (INdL : In (pd, pdn) LB) by (apply INCL; rewrite EREST; right; left; reflexivity).
assert (INd : In (pd, pdn) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INdL).
pose proof (heap_blk S4L HIx _ _ _ _ pd _ HP INd) as (_ & Hdal & Hdlo & Hdhi & _).
assert (INp : In (p, 56) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INpL).
pose proof (heap_blk S4L HIx _ _ _ _ p _ HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
assert (Rlen : -2147483648 < len < 0) by lia. assert (Rpd : 1 <= pd < 140737488355328) by (unfold_consts; lia).
unfold_consts.
destruct FL as [Rfl FL56]. destruct (land56_bits fl FL56) as (FL32 & FL16 & FL8).
assert (Rfl64 : 0 <= fl < 2^64) by lia.
destruct PB as (Hbp & Hcap & Hln & PBS & PBUF).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
assert (NODE0 : True -> rw_cells rsegs m p
[C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string S4F)); C8 (Z_to_bv 64 pb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd)]) by (intros _; exact NODE).
assert (DATA0 : True -> rw_cells rsegs m pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]) by (intros _; exact DATA). clear DATA.
apply rz_evt; [exact MOK|].
carve_frame 48%nat ST.
symb_run 40%nat [MEMAPPEND] [false; false; true].
2,3: sc_cbn; first [ apply br_and_zero; [exact Rfl64 | lia | exact FL32] | apply brne_and_zero; [lia | lia | exact (land7_of_mod16 p Hpal)] ].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
lazymatch type of FR with rw_cells _ _ _ ?cs => assert (INV1 : ser_mem HIx sp m md LB pb lo (bv_unsigned sp + -48) cs m1 md) end.
{ exists A, buf, cap, bpos, content, errv.
split; [exact HP1|]. split; [split; [lia|]; split; [lia|]; split; [exact Hln|]; split; [exact PBS|exact PBUF]|].
split; [exact FR|]. split; [exact ERR|]. split; [exact ST|]. split; [exact HPR1 | apply model_vm_only_refl]. }
clear HP1 HPR1 MU WM.
destruct (ro_src m1 0x1239c [Z_to_bv 8 34] LB 1 (bv_unsigned sp + -48) MI1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m md LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 34]);
[ exact INV1 | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
pose proof INV2 as INV2'. destruct INV2 as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FR2c & ERR2 & ST2 & HPR2 & VM2).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2. unfold Uuoa.Mq0.ERRNO in ERR2.
assert (NODE2 : rw_cells rsegs m2 p
[C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string S4F)); C8 (Z_to_bv 64 pb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd)]).
{ eapply (heap_pres_rw_cells S4L); [exact HPR2 | exact (NODE0 I) |]. right; right. exists (p, 56). split; [exact INpL|]. cbn. lia. }
assert (DATA2 : rw_cells rsegs m2 pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]).
{ eapply (heap_pres_rw_cells S4L); [exact HPR2 | exact (DATA0 I) |]. right; right. exists (pd, pdn). split; [exact INdL|]. cbn.
destruct (DATA0 I) as [[Hwf _] _]. cbn in Hwf. lia. }
apply rz_evt; [exact MOK2|].
symb_run 40%nat [ESCAPE] [true; false; false].
2: sc_cbn; exact (neg_chk_ok len ltac:(lia)).
rewrite neg_lit64.

assert (SRC2 : bytes_at rsegs m2 pd str).
{ pose proof (rw_cells_bytes_at rsegs m2 _ _ DATA2) as BY. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY.
exact (proj1 (proj1 (bytes_at_app rsegs m2 _ _ _) BY)). }
apply evt_RZ_done.
eapply (ser_escape HIx MEMMOVE HEXP HT63 HGOT sp gp m md LB pb lo LO HT) with (F := F) (src := str);
[ exact INV2' | exact SRC2 | lia | lia | lia | lia
| left; right; right; exists (pd, pdn); split; [exact INdL | cbn; lia]
| lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | rewrite unsigned_lit by lia; exact FL16 | ].
intros m3 md3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 INV3 FS3 FR3 _.
pose proof (ser_mem_model_ok _ _ _ _ _ _ _ _ _ _ _ INV3) as MOK3. pose proof (ser_mem_mem_inv _ _ _ _ _ _ _ _ _ _ _ INV3) as MI3.
apply rz_evt; [exact MOK3|].
symb_run 40%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m3 0x1239c [Z_to_bv 8 34] LB 1 (bv_unsigned sp + -48) MI3 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBr SBCr].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m md LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 34]);
[ exact INV3 | exact SBr | reflexivity | lia | lia | lia | exact SBCr | left; lia | lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FR3 | ].
intros m4 md4 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F4 fc4 INV4 FS4 FR4 _.
destruct INV4 as (A4 & buf4 & cap4 & bpos4 & content4 & errv4 & HP4 & PB4 & FR4c & ERR4 & ST4 & HPR4 & VM4).
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4. unfold Uuoa.Mq0.ERRNO in ERR4.
apply rz_evt; [exact MOK4|].
symb_run 40%nat (@nil Z) [true].
step.
apply evt_RZ_done. apply K. unfold ser_post.
exists m4, A4. eexists. exists errv4, buf4, cap4, bpos4, content4.
split; [| split; [exact VM4 | split; [| split; [exact HPR4 | split; [exact ERR4 | split; [exact HP4 | exact PB4]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -48 + 48)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
apply ret_statew_intro; [exact FS4 | intros _; exact FR4].
- release_frame FR4c ST4 (bv_unsigned sp). exact ST4.
Qed.
End Ser.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7zy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7zy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UD4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UD4E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UgLo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UgLo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qio9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qio9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHXC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHXC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfe5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfe5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QId5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QId5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfJh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfJh.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UUr4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULch.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrM1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwKH.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma land7_m8 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.
#[using="Type"] Lemma slt_succ_lit : forall x, 0 <= x < 2^31 -> v_slt (Z_to_bv 64 (x + 1)) (Z_to_bv 64 x) = Z_to_bv 64 0.
Proof.
intros x H. unfold v_slt, c_lts, bv_lts. rewrite !signed_lit by lia.
replace (x + 1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (wz JHEX_SLOT)).

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (pb lo p rc pb0 lv fl t : Z).
Variables (TBS : list blk) (es : list oent) (KBS : list (list blk)) (kids : list (option jshape)) (T : TSet).
Let usp := bv_unsigned sp.
Hypothesis KIDS : forall s', In (Some s') kids -> ser_spec HIx (fn_of s') s'.
Hypothesis LBS : lb_small LB.
Hypothesis FL : flags_ok fl.
Hypothesis Hlv : 0 <= lv.
Hypothesis Hlvd : lv + sdepth (Sobj kids) <= 1000.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ser_budget (Sobj kids).
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.
Hypothesis INCL : incl ((p, 48) :: TBS ++ concat KBS) LB.
Hypothesis NODE0 : rw_cells rsegs m0 p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string S4F) pb0 0 0 ++ [C8 (Z_to_bv 64 t)]).
Hypothesis OT0 : otab rsegs m0 TBS t es.
Hypothesis LK : length KBS = length kids.
Hypothesis LE : length es = length kids.
Hypothesis KOK : kids_okv rsegs S4F m0 kids (map (fun e => (oe_k e, oe_v e)) es) KBS.
Hypothesis K : forall ms' md', ser_post HIx ra sp gp (Z_to_bv 64 TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb lo ms' md' ->
realizes rsegs (mkCfg ms' md') T.

Variables (f1 f2 : Z).
Hypothesis Hf1 : Z.land fl 1 = f1.
Hypothesis Hf2 : Z.land fl 2 = f2.

Notation ser_memx := (ser_mem HIx sp m0 md0 LB pb lo).
Let LEN := Z.of_nat (length es).
Definition osavedR : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition objLoc (j0 : list byte) : list cell :=
[CB 8 j0; C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0x13204); C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0x105a2);
C8 (Z_to_bv 64 0x126d7); C8 (Z_to_bv 64 0x12e84); C8 (Z_to_bv 64 0x11ca0); C8 (Z_to_bv 64 0x1120c); C8 (Z_to_bv 64 0x122e0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x10eb1)].
Definition objFR (j0 : list byte) : list cell := objLoc j0 ++ osavedR.

#[using="RC__ ra TBS KBS LBS FL LOS INCL LK LE"] Lemma facts :
0 <= usp < 2^64 /\ In (p, 48) LB /\
Z.land fl 32 = 0 /\ Z.land fl 16 = 0 /\ Z.land fl 8 = 0 /\ 0 <= fl < 2^31 /\
0 <= kdepth kids /\ lo <= usp - 208 - 208 * kdepth kids - 8560 /\ LEN = Z.of_nat (length kids).
Proof.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (INp : In (p, 48) LB) by (apply INCL; left; reflexivity).
destruct FL as [Rfl FL56]. destruct (land56_bits fl FL56) as (FL32 & FL16 & FL8).
pose proof (kdepth_nonneg kids) as KD. unfold ser_budget in LOS. rewrite sdepth_obj in LOS.
repeat split; try assumption; unfold LEN, usp in *; lia.
Qed.

#[using="ra fl usp LBS FL LOS INCL NODE0 OT0 LK LE KOK LEN"] Lemma factsM : forall FA FR m md, ser_memx FA FR m md ->
mem_inv rsegs m /\ model_ok md /\ 0 < p /\ p + 48 <= alloc_ceiling /\ p mod 16 = 0 /\
rw_cells rsegs m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string S4F) pb0 0 0 ++ [C8 (Z_to_bv 64 t)]) /\
otab rsegs m TBS t es /\
(forall j e k, nth_error kids j = Some k -> nth_error es j = Some e ->
match k with
| None => oe_v e = 0
| Some s' => exists bs, nth_error KBS j = Some bs /\ jval rsegs S4F s' m bs (oe_v e) 1 /\ incl bs LB /\
0 < oe_v e /\ oe_v e + 48 <= alloc_ceiling /\ oe_v e mod 16 = 0 /\ sdepth s' <= kdepth kids
end).
Proof.
intros FA FR m md (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
pose proof facts as (SPR & INp & _).
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INp' : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp') as (_ & Hpal & Hplo & Hphi & _).
assert (AG : agree_on rsegs LB m0 m) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR | reflexivity | apply incl_refl]).
split; [exact MI|]. split; [exact (heap_model_ok _ _ _ _ _ _ HP)|]. split; [exact Hplo|]. split; [exact Hphi|]. split; [exact Hpal|].
split. { eapply (heap_pres_rw_cells S4L); [exact HPR | exact NODE0 |]. right; right. exists (p, 48). split; [exact INp | cbn; lia]. }
split. { eapply otab_agree; [exact OT0 | exact AG |]. intros b Hb. apply INCL. right. apply in_or_app. left. exact Hb. }
intros j e k Hk He.
destruct (kids_okv_nth _ _ _ _ _ _ j k KOK Hk) as (kk & v & bs & Hkv & Hb & KD).
rewrite nth_error_map, He in Hkv. cbn in Hkv. injection Hkv as _ <-.
destruct k as [s'|]; [| exact (proj1 KD)]. destruct KD as [Hv0 J].
assert (IB : incl bs LB).
{ intros b Hbb. apply INCL. right. apply in_or_app. right. apply in_concat. exists bs. split; [| exact Hbb]. eapply nth_error_In. exact Hb. }
assert (J' : jval rsegs S4F s' m bs (oe_v e) 1) by (eapply (jval_agree rsegs S4F); [exact J | exact AG | exact IB]).
exists bs. split; [exact Hb|]. split; [exact J'|]. split; [exact IB|].
destruct (proj1 (jval_split rsegs S4F s' m bs (oe_v e) 1) J') as (pbc & PBSc & RESTc & Ebs & _ & JN).
destruct (jnode_hdr rsegs S4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
assert (INv : In (oe_v e, n) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply IB; rewrite Ebs, ER; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ (oe_v e) n HP INv) as (_ & Hval & Hvlo & Hvhi & _).
split; [exact Hvlo|]. split; [lia|]. split; [exact Hval|].
apply kdepth_in. eapply nth_error_In. exact Hk.
Qed.

#[using="RC__ ra sp LB lo p fl TBS es KBS kids usp LBS FL LOS INCL LK LE Hf1 LEN"] Lemma FC1 : f1 = 0 \/ f1 = 1. Proof. rewrite <- Hf1. apply land1_cases. pose proof facts as (_ & _ & _ & _ & _ & R & _). lia. Qed.
#[using="RC__ ra sp LB lo p fl TBS es KBS kids usp LBS FL LOS INCL LK LE Hf2 LEN"] Lemma FC2 : f2 = 0 \/ f2 = 2. Proof. rewrite <- Hf2. apply land2_cases. pose proof facts as (_ & _ & _ & _ & _ & R & _). lia. Qed.

#[using="ra LBS LO HT"] Lemma oser_mem_frame : forall FA FR FR' m md x,
ser_memx FA FR m md -> munch [(FA, FA + Z.of_nat (cells_size FR))] m x -> wmono rsegs m x -> mem_inv rsegs x ->
rw_cells rsegs x FA FR' -> lo <= FA -> FA + Z.of_nat (cells_size FR) <= usp ->
ser_memx FA FR' x md.
Proof. intros. eapply (ser_mem_frame HIx ra sp m0 md0 LB pb lo [] LBS LO HT); eassumption. Qed.

#[using="MEMMOVE fc p fl TBS es KBS kids LBS FL LO LOS SPA HT RA INCL LK LE K LEN"] Lemma obj_tailcall :
forall (x2 x3 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md FR (lit k : Z) (bs : list byte),
x2 = sp -> x3 = gp ->
ser_memx (usp + -208) FR m md -> cells_size FR = 208%nat ->
ro_bytes_b rsegs lit bs = true -> Z.of_nat (length bs) = k -> 0 < k < 2^31 -> 0 <= lit -> lit + k < 2^64 ->
fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR ra x2 x3 (Z_to_bv 64 TP) t0 t1 t2 s0 s1 (Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 MEMAPPEND) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until bs. intros -> -> INV HFR RB BL Hk Hl Hlk FS' FR'.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & _).
destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (stk_release rsegs _ _ _ _ ST FRc ltac:(lia)) as ST'. rewrite HFR in ST'.
replace (usp + -208 + Z.of_nat 208) with usp in ST' by lia.
destruct (ro_src m lit bs LB k usp MI RB BL Hl ltac:(lia)) as [SB SBC].
eapply (memappend_cps HIx MEMMOVE) with (A := A) (LB := LB) (buf := buf) (bpos := bpos) (cap := cap) (b := lit) (n := k)
(lo := lo) (content := content) (src := bs) (errv := errv).
- exact HP.
- exact PB.
- lia.
- exact SB.
- exact BL.
- exact SBC.
- lia.
- lia.
- destruct (ser_src_sep_buf HIx _ _ _ _ _ _ _ _ _ _ _ HP SBC BL Hl ltac:(lia) ltac:(unfold usp; unfold_consts; lia)) as [?|SEP]; [lia | exact SEP].
- exact ST'.
- exact LO.
- unfold ser_budget in LOS. unfold usp in *. lia.
- exact SPA.
- exact HT.
- unfold ERRNO in ERR. exact ERR.
- unfold TP. reflexivity.
- exact RA.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' POST.
destruct POST as (m' & A' & r & errv' & buf' & cap' & RS & VM' & ST2 & HPR' & ERR' & HP' & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F'' & fc'' & -> & FS'' & FR'').
apply K. unfold ser_post.
assert (PB' : exists bpos' content', pbuf_core rsegs m' pb buf' bpos' cap' content').
{ destruct OUT as [[_ PBF] | (_ & -> & -> & PBC)].
- destruct PBF as (bufq & bposq & sizeq & pre & post & E & L & C). injection E as <- <-. eauto.
- eauto. }
destruct PB' as (bpos' & content' & PB').
exists m', A', (Z_to_bv 64 r), errv', buf', cap', bpos', content'.
split; [| split; [eapply model_vm_only_trans; [exact VM | exact VM'] | split; [exact ST2 | split; [| split; [unfold ERRNO; exact ERR' | split; [exact HP' | exact PB']]]]]].
+ unfold TP. apply ret_statew_intro; [eapply fsaved_trans; [exact FS' | exact FS''] | intros _; exact (FR'' FR')].
+ eapply heap_pres_trans; [exact HPR | exact HPR'].
Qed.

#[using="MEMMOVE fc p rc pb0 t TBS es KBS kids LBS FL LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K f1 f2 Hf1 Hf2 LEN"] Lemma obj_close :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md (pre : list cell),
ser_memx (usp + -208) (pre ++ osavedR) m md -> cells_size pre = 104%nat ->
fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP) t0 t1 t2 (Z_to_bv 64 pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 fl) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (Z_to_bv 64 0x24dd8) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until pre. intros INV Hpre FS' FR'. pose proof FC1 as C1. pose proof FC2 as C2.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & _).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
destruct PB as (Hbp & Hcap & Hln & PBS & PBUF). unfold ERRNO in ERR. unfold TP.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc as [FRp FRs]. rewrite Hpre in FRs. change (Z.of_nat 104) with 104 in FRs.
replace (usp + -208 + 104) with (usp + -104) in FRs by lia. unfold osavedR in FRs. unfold usp in *. unfold_consts.
assert (Rfl64 : 0 <= fl < 2^64) by lia.
apply rz_evt; [exact MOK|].
destruct (Z.eq_dec (Z.lor f1 f2) 1) as [E1|NE1].
-
symb_run 30%nat [MEMAPPEND] [false].
2:{ sc_cbn. rewrite alu_and3 by lia. rewrite land3_lor, Hf1, Hf2.
destruct C1 as [E|E]; rewrite E in *; destruct C2 as [E'|E']; rewrite E' in *; compute in E1; try lia; vm_compute; reflexivity. }
apply evt_RZ_done. eapply (obj_tailcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' _ md (pre ++ osavedR) 0x12ff7 2 [Z_to_bv 8 32; Z_to_bv 8 125]);
[ first [reflexivity | apply bv_eq; rewrite unsigned_lit by lia; lia] | reflexivity | exact INV' | rewrite cells_size_app, Hpre; reflexivity
| vm_compute; reflexivity | reflexivity | lia | lia | lia | exact FS' | exact FR' ].
- symb_run 30%nat [MEMAPPEND] [true].
2:{ sc_cbn. rewrite alu_and3 by lia. rewrite land3_lor, Hf1, Hf2.
destruct C1 as [E|E]; rewrite E in *; destruct C2 as [E'|E']; rewrite E' in *; compute in NE1; try congruence; vm_compute; reflexivity. }
apply evt_RZ_done. eapply (obj_tailcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' _ md (pre ++ osavedR) 0x104fd 1 [Z_to_bv 8 125]);
[ first [reflexivity | apply bv_eq; rewrite unsigned_lit by lia; lia] | reflexivity | exact INV' | rewrite cells_size_app, Hpre; reflexivity
| vm_compute; reflexivity | reflexivity | lia | lia | lia | exact FS' | exact FR' ].
Qed.

#[using="fc p rc pb0 fl t TBS es KBS kids LBS FL LO LOS INCL NODE0 OT0 LK LE KOK K LEN"] Lemma obj_fail :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md (pre : list cell),
ser_memx (usp + -208) (pre ++ osavedR) m md -> cells_size pre = 104%nat ->
fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (Z_to_bv 64 0x24cd8) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until pre. intros INV Hpre FS' FR'.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & _).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR. unfold TP.
pose proof FRc as FRj.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc as [FRp FRs]. rewrite Hpre in FRs. change (Z.of_nat 104) with 104 in FRs.
replace (usp + -208 + 104) with (usp + -104) in FRs by lia. unfold osavedR in FRs. unfold usp in *. unfold_consts.
apply rz_evt; [exact MOK|].
symb_run 20%nat (@nil Z) (@nil bool).
step.
apply evt_RZ_done. apply K. unfold ser_post.
exists m, A. eexists. exists errv, buf, cap, bpos, content.
split; [| split; [exact VM | split; [| split; [exact HPR | split; [exact ERR | split; [exact HP | exact PB]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -208 + 208)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
unfold TP. apply ret_statew_intro; [exact FS' | intros _; exact FR'].
- pose proof (stk_release rsegs _ _ _ _ ST FRj ltac:(lia)) as ST'.
rewrite cells_size_app, Hpre in ST'. cbn [cells_size csize Nat.add osavedR length] in ST'.
replace (bv_unsigned sp + -208 + Z.of_nat 208) with (bv_unsigned sp) in ST' by lia. exact ST'.
Qed.

Ltac oopen_frame FRc FR0 FRs :=
unfold objFR, objLoc in FRc;
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc as [FR0 FRs]; cbn [cells_size csize Nat.add] in FRs; change (Z.of_nat 104) with 104 in FRs;
replace (bv_unsigned sp + -208 + 104) with (bv_unsigned sp + -104) in FRs by lia; unfold osavedR in FRs.
Ltac chk_side := sc_cbn; first
[ apply brne_and_zero; [lia | lia | first [apply land7_of_mod16; assumption | apply land7_m8; assumption]]
| apply br_and_zero; [lia | lia | first [apply land7_of_mod16; assumption | apply land7_m8; assumption]] ].

#[using="MEMMOVE fc p rc pb0 t TBS es KBS kids LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K f1 Hf1 Hf2 LEN"] Lemma obj_end :
forall (j0 : list byte) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP) t0 t1 t2 (Z_to_bv 64 pb) (Z_to_bv 64 f2) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 fl) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (Z_to_bv 64 0x24dd0) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until md. intros INV FS' FR'. pose proof FC2 as C2.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & _).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
oopen_frame FRc FR0 FRs.
unfold TP. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
destruct C2 as [E2|E2].
- symb_run 2%nat [0x24dd8]%Z [false].
apply evt_RZ_done.
eapply obj_close with (pre := objLoc j0);
[ eapply (ser_mem_pure HIx); [exact INV' | exact MU | exact WM | assumption] | reflexivity | exact FS' | exact FR' ].
-
symb_run 7%nat [MEMAPPEND] [true].
destruct (ro_src m 0x122e0 [Z_to_bv 8 10] LB 1 (bv_unsigned sp + -208) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBr SBCr].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 10]);
[ exact INV' | exact SBr | reflexivity | lia | lia | lia | exact SBCr | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m. intros m2 md2 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F2 fc2 INV2 FS2 FR2 _.
destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _).
pose proof INV2 as INV2'. destruct INV2' as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FRc2 & _).
oopen_frame FRc2 FR02 FRs2.
apply rz_evt; [exact MOK2|].
symb_run 11%nat [PBMEMSET] [false].
change (1 mod 32) with 1. rewrite (Z.shiftl_mul_pow2 lv 1) by lia. change (2 ^ 1) with 2. rewrite (swrap32_id (lv * 2)) by lia.
apply evt_RZ_done.
eapply (ser_memset HIx sp gp m0 md0 LB pb lo LO HT) with (F := F);
[ exact INV2 | lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
clear dependent m2. intros m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
destruct (factsM _ _ _ _ INV3) as (MI3 & MOK3 & _).
pose proof INV3 as INV3'. destruct INV3' as (A3 & buf3 & cap3 & bpos3 & content3 & errv3 & HP3 & PB3 & FRc3 & _).
oopen_frame FRc3 FR03 FRs3.
apply rz_evt; [exact MOK3|].
symb_run 19%nat [MEMAPPEND] (@nil bool).
apply evt_RZ_done. eapply (obj_tailcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 _ md3 (objFR j0) 0x104fd 1 [Z_to_bv 8 125]);
[ first [reflexivity | apply bv_eq; rewrite unsigned_lit by lia; lia] | reflexivity | exact INV3 | reflexivity
| vm_compute; reflexivity | reflexivity | lia | lia | lia | exact FS3 | exact FR3 ].
Qed.

#[using="ra p rc pb0 fl t TBS KBS kids usp LBS FL LOS INCL NODE0 OT0 LK LE KOK LEN"] Lemma factsE : forall FA FR m md j e, ser_memx FA FR m md -> nth_error es j = Some e ->
0 < oe_a e /\ oe_a e + 32 <= alloc_ceiling /\
(exists pad : word, rw_cells rsegs m (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) es)))]) /\
cstr rsegs m (oe_k e) (oe_kn e) (oe_ks e) /\ In (oe_k e, oe_kn e) LB /\
0 < oe_k e /\ oe_k e + oe_kn e <= alloc_ceiling /\ oe_kn e <= 2^31.
Proof.
intros FA FR m md j e INV Hj.
destruct (factsM _ _ _ _ INV) as (_ & _ & _ & _ & _ & _ & OT & _).
destruct INV as (A & buf & cap & bpos & content & errv & HP & _).
destruct OT as (_ & _ & ENT). destruct (ENT j e Hj) as (A0 & AL8 & (ba & bn & Hb & Hlo & Hhi) & RW & CS & INk & Hkn).
assert (HbL : In (ba, bn) LB) by (apply INCL; right; apply in_or_app; left; exact Hb).
assert (HkL : In (oe_k e, oe_kn e) LB) by (apply INCL; right; apply in_or_app; left; exact INk).
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP ltac:(right; right; exact HbL)) as (_ & _ & Hblo & Hbhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ (oe_k e) (oe_kn e) HP ltac:(right; right; exact HkL)) as (_ & _ & Hklo & Hkhi & _).
split; [exact A0|]. split; [lia|]. split; [exact RW|]. split; [exact CS|]. split; [exact HkL|]. lia.
Qed.

#[using="OT0"] Lemma ealign : forall j e, nth_error es j = Some e -> oe_a e mod 8 = 0.
Proof. intros j e Hj. destruct OT0 as (_ & _ & ENT). exact (proj1 (proj2 (ENT j e Hj))). Qed.

Definition st_o (pc ea : Z) (sv5 sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP) t0 t1 t2 (Z_to_bv 64 pb) (Z_to_bv 64 f2) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 fl) (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 0) sv5 (Z_to_bv 64 0x1239c) sv7 (Z_to_bv 64 0) (Z_to_bv 64 f1) (Z_to_bv 64 0x127bc)
(Z_to_bv 64 ea) t3 t4 t5 t6) F' (Z_to_bv 64 pc) fc' None m (seg_rom rsegs).
Definition oloopK (bound : Z) : Prop :=
forall j0 j e hs sv5 sv7 x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> (hs = 0 \/ hs = 1) -> LEN - Z.of_nat j <= bound ->
realizes rsegs (mkCfg (st_o 0x24c20 (oe_a e) sv5 sv7 x1 t0 t1 t2 (Z_to_bv 64 hs) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.

#[using="MEMMOVE fc p rc pb0 t TBS KBS kids LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_604 :
forall j0 j e sv5 sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24c0c (oe_a e) sv5 sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj IH.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
destruct (factsE _ _ _ _ j e INV Hj) as (Hea & Hea2 & (pad & ENT) & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
oopen_frame FRc FR0 FRs.
unfold st_o, TP. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
destruct (nth_error es (S j)) as [e'|] eqn:Hj'.
-
destruct (factsE _ _ _ _ (S j) e' INV' Hj') as (Hea' & Hea2' & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hea2'.
pose proof (ealign (S j) e' Hj') as Hal'.
rewrite (ohd_skipn es (S j)), Hj' in ENT.
symb_run 5%nat [0x24c20]%Z [false; false]; [ idtac | chk_side .. ].
apply evt_RZ_done. unfold oloopK in IH. eapply (IH j0 (S j) e' 0); [| exact FS' | exact FR' | exact Hj' | left; reflexivity | lia].
eapply (ser_mem_pure HIx); [exact INV' | exact MU | exact WM | assumption].
-
rewrite (ohd_skipn es (S j)), Hj' in ENT.
symb_run 3%nat [0x24dd0]%Z [true].
apply evt_RZ_done. eapply obj_end; [| exact FS' | exact FR'].
eapply (ser_mem_pure HIx); [exact INV' | exact MU | exact WM | assumption].
Qed.

#[using="MEMMOVE fc p rc pb0 t TBS KBS kids LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_6a0 :
forall j0 j e sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24da0 (oe_a e) (Z_to_bv 64 0) sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj IH.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
destruct (factsE _ _ _ _ j e INV Hj) as (Hea & Hea2 & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
oopen_frame FRc FR0 FRs.
unfold st_o, TP. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia).
apply rz_evt; [exact MOK|].
symb_run 5%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m 0x10eb1 (map (Z_to_bv 8) [110; 117; 108; 108]) LB 4 (bv_unsigned sp + -208) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := map (Z_to_bv 8) [110; 117; 108; 108]);
[ exact INV' | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
eapply (obj_604 j0 j e (Z_to_bv 64 0)); [exact INV2 | exact FS2 | exact FR2 | exact Hj | exact IH].
Qed.

#[using="MEMMOVE fc p rc pb0 t TBS KBS KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_788 :
forall j0 j e s' sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> nth_error kids j = Some (Some s') ->
oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24cb4 (oe_a e) (Z_to_bv 64 (oe_v e)) sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj Hk IH.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _ & _ & _ & _ & _ & KF).
destruct (KF j e (Some s') Hk Hj) as (bs & Hbs & J & IB & Hvlo & Hvhi & Hval & Hsd).
destruct (proj1 (jval_split rsegs S4F s' m bs (oe_v e) 1) J) as (pbc & PBSc & RESTc & Ebs & OPB & JN).
destruct (jnode_hdr rsegs S4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
rewrite (fn_of_S4F s') in HDR. apply (proj1 (rw_cells_app rsegs _ _ _ _)) in HDR as [HDR _].
pose proof (fn_of_range s') as FR_. pose proof (fn_of_even s') as FE_.
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
oopen_frame FRc FR0 FRs.
unfold st_o, TP. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia). assert (Rv : 1 <= oe_v e < 140737488355328) by lia.
apply rz_evt; [exact MOK|].
symb_run 7%nat (@nil Z) [false]; [ idtac | chk_side .. ].
step. replace (ret_pc (Z_to_bv 64 (fn_of s'))) with (Z_to_bv 64 (fn_of s')) by (symmetry; apply ret_pc_even; [lia | exact FE_]).
fold_mkR. apply evt_RZ_done.
assert (Hin : In (Some s') kids) by (eapply nth_error_In; exact Hk).
pose proof (sdepth_obj kids) as SDA.
eapply (ser_child HIx sp gp m0 md0 LB pb lo LO HT _ _ (KIDS s' Hin)) with (F := F) (RESTc := RESTc) (rc' := 1) (pbc := pbc);
[ exact INV' | exact JN | intros b Hb; apply IB; rewrite Ebs; apply in_or_app; left; exact Hb | exact LBS | exact FL | lia | lia
| unfold ser_budget; lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2.
destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _).
apply rz_evt; [exact MOK2|].
step. if_cases Kge; fold_mkR.
- apply evt_RZ_done. eapply (obj_604 j0 j e (Z_to_bv 64 (oe_v e))); [exact INV2 | exact FS2 | exact FR2 | exact Hj | exact IH].
- apply evt_RZ_done. eapply obj_fail with (pre := objLoc j0); [ exact INV2 | reflexivity | exact FS2 | exact FR2 ].
Qed.

#[using="ra p rc pb0 fl t TBS KBS usp LBS FL LOS INCL NODE0 OT0 LK LE KOK LEN"] Lemma obj_val : forall FA FR m md j e k,
ser_memx FA FR m md -> nth_error es j = Some e -> nth_error kids j = Some k ->
match k with None => oe_v e = 0 | Some s' => 1 <= oe_v e < 2^47 end.
Proof.
intros FA FR m md j e k INV Hj Hk.
destruct (factsM _ _ _ _ INV) as (_ & _ & _ & _ & _ & _ & _ & KF).
pose proof (KF j e k Hk Hj) as H. destruct k as [s'|]; [| exact H].
destruct H as (bs & _ & _ & _ & Hvlo & Hvhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi. lia.
Qed.

#[using="MEMMOVE fc p rc pb0 t TBS KBS KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_69c :
forall j0 j e k sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> nth_error kids j = Some k ->
oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24cb0 (oe_a e) (Z_to_bv 64 (oe_v e)) sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj Hk IH.
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
pose proof (obj_val _ _ _ _ j e k INV Hj Hk) as HV.
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & _).
pose proof facts as (SPR & _).
unfold st_o, TP. unfold usp in *. unfold_consts.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
destruct k as [s'|].
- symb_run 1%nat [0x24cb4]%Z [false].
apply evt_RZ_done. eapply obj_788; [exact INV' | exact FS' | exact FR' | exact Hj | exact Hk | exact IH].
- rewrite HV. symb_run 1%nat [0x24da0]%Z (@nil bool).
apply evt_RZ_done. eapply obj_6a0; [exact INV' | exact FS' | exact FR' | exact Hj | exact IH].
Qed.
#[using="MEMMOVE fc p rc pb0 t TBS KBS KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_784 :
forall j0 j e k sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> nth_error kids j = Some k ->
oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24d9c (oe_a e) (Z_to_bv 64 (oe_v e)) sv7 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj Hk IH.
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
pose proof (obj_val _ _ _ _ j e k INV Hj Hk) as HV.
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & _).
pose proof facts as (SPR & _).
unfold st_o, TP. unfold usp in *. unfold_consts.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
destruct k as [s'|].
- symb_run 1%nat [0x24cb4]%Z [true].
apply evt_RZ_done. eapply obj_788; [exact INV' | exact FS' | exact FR' | exact Hj | exact Hk | exact IH].
- rewrite HV. symb_run 1%nat [0x24da0]%Z (@nil bool).
apply evt_RZ_done. eapply obj_6a0; [exact INV' | exact FS' | exact FR' | exact Hj | exact IH].
Qed.

#[using="MEMMOVE fc p rc pb0 t TBS KBS KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_688 :
forall j0 j e k x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> nth_error kids j = Some k ->
oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24c9c (oe_a e) (Z_to_bv 64 (oe_v e)) (Z_to_bv 64 (oe_k e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj Hk IH. pose proof FC1 as C1.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
destruct (factsE _ _ _ _ j e INV Hj) as (Hea & Hea2 & _ & _ & _ & Hk0 & Hk2 & _).
pose proof (obj_val _ _ _ _ j e k INV Hj Hk) as HV. assert (Rv : 0 <= oe_v e < 2^47) by (destruct k; lia). clear HV.
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
oopen_frame FRc FR0 FRs.
unfold st_o, TP. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia).
apply rz_evt; [exact MOK|].
destruct C1 as [E1|E1].
-
symb_run 5%nat [MEMAPPEND] [true].
destruct (ro_src m 0x11ca0 [Z_to_bv 8 58] LB 1 (bv_unsigned sp + -208) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 58]);
[ exact INV' | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
eapply (obj_784 j0 j e k (Z_to_bv 64 (oe_k e))); [exact INV2 | exact FS2 | exact FR2 | exact Hj | exact Hk | exact IH].
-
symb_run 5%nat [MEMAPPEND] [false].
destruct (ro_src m 0x12e84 [Z_to_bv 8 58; Z_to_bv 8 32] LB 2 (bv_unsigned sp + -208) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 58; Z_to_bv 8 32]);
[ exact INV' | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
eapply (obj_69c j0 j e k (Z_to_bv 64 (oe_k e))); [exact INV2 | exact FS2 | exact FR2 | exact Hj | exact Hk | exact IH].
Qed.

#[using="MEMMOVE HEXP HT63 HGOT fc p rc pb0 t TBS KBS KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_64c :
forall j0 j e k x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> nth_error kids j = Some k ->
oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24c60 (oe_a e) (Z_to_bv 64 (oe_v e)) (Z_to_bv 64 (oe_k e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj Hk IH.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
destruct (factsE _ _ _ _ j e INV Hj) as (Hea & Hea2 & _ & _ & INk & Hk0 & Hk2 & Hkn).
pose proof (obj_val _ _ _ _ j e k INV Hj Hk) as HV. assert (Rv : 0 <= oe_v e < 2^47) by (destruct k; lia). clear HV.
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
oopen_frame FRc FR0 FRs.
unfold st_o, TP. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia).
apply rz_evt; [exact MOK|].

symb_run 4%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m 0x1239c [Z_to_bv 8 34] LB 1 (bv_unsigned sp + -208) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 34]);
[ exact INV' | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.

destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _).
destruct (factsE _ _ _ _ j e INV2 Hj) as (_ & _ & _ & CS2 & _).
pose proof INV2 as INV2'. destruct INV2' as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FRc2 & _).
destruct (cstr_slack HIx _ _ _ _ _ _ _ HP2 ltac:(right; right; exact INk) CS2) as (slack & SBY & SLK & NONUL).
destruct CS2 as (Hlen1 & _ & _).
assert (LENsb : Z.of_nat (length slack) <= oe_kn e - Z.of_nat (length (oe_ks e)) - 1 + 15) by lia.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
oopen_frame FRc2 FR02 FRs2.
apply rz_evt; [exact MOK2|].
symb_run 2%nat [STRLEN] (@nil bool).
call (strlen_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (oe_k e)));
[ rewrite unsigned_lit by lia; exact SBY | exact NONUL | rewrite unsigned_lit by lia; clear -SLK Hk0 Hk2 Hlen1 LENsb Hkn; lia | exact MI2 | ].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
assert (INV3 : ser_memx (bv_unsigned sp + -208) (objFR j0) m3 md2) by (eapply (ser_mem_pure HIx); [exact INV2 | exact MU | exact WM | exact MI3]).
assert (SB3 : bytes_at rsegs m3 (oe_k e) (oe_ks e)) by (exact (proj1 (proj1 (bytes_at_app rsegs m3 (oe_k e) _ _) SBY))).
assert (Hlen31 : 0 <= Z.of_nat (length (oe_ks e)) < 2^31) by lia.
symb_run 5%nat [ESCAPE] (@nil bool).
apply evt_RZ_done.
eapply (ser_escape HIx MEMMOVE HEXP HT63 HGOT sp gp m0 md0 LB pb lo LO HT) with (F := F) (src := oe_ks e);
[ exact INV3 | exact SB3 | reflexivity | lia | lia | lia
| left; right; right; exists (oe_k e, oe_kn e); split; [exact INk | cbn; lia]
| lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | rewrite unsigned_lit by lia; exact FL16 | ].
clear dependent m2. clear dependent m3.
intros m4 md4 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F4 fc4 INV4 FS4 FR4 _.

destruct (factsM _ _ _ _ INV4) as (MI4 & MOK4 & _).
pose proof INV4 as INV4'. destruct INV4' as (A4 & buf4 & cap4 & bpos4 & content4 & errv4 & HP4 & PB4 & FRc4 & _).
oopen_frame FRc4 FR04 FRs4.
apply rz_evt; [exact MOK4|].
symb_run 4%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m4 0x1239c [Z_to_bv 8 34] LB 1 (bv_unsigned sp + -208) MI4 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq' SBCq'].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 34]);
[ exact INV4 | exact SBq' | reflexivity | lia | lia | lia | exact SBCq' | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS4 | exact FR4 | ].
clear dependent m4.
intros m5 md5 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F5 fc5 INV5 FS5 FR5 _.
eapply (obj_688 j0 j e k); [exact INV5 | exact FS5 | exact FR5 | exact Hj | exact Hk | exact IH].
Qed.

#[using="MEMMOVE HEXP HT63 HGOT fc p rc pb0 t TBS KBS KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_630 :
forall j0 j e k x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> nth_error kids j = Some k ->
oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24c40 (oe_a e) (Z_to_bv 64 (oe_v e)) (Z_to_bv 64 (oe_k e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj Hk IH. pose proof FC1 as C1. pose proof FC2 as C2.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
destruct (factsE _ _ _ _ j e INV Hj) as (Hea & Hea2 & _ & _ & INk & Hk0 & Hk2 & Hkn).
pose proof (obj_val _ _ _ _ j e k INV Hj Hk) as HV. assert (Rv : 0 <= oe_v e < 2^47) by (destruct k; lia). clear HV.
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
oopen_frame FRc FR0 FRs.
unfold st_o, TP. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
destruct C2 as [E2|E2].
- destruct C1 as [E1|E1].
+
symb_run 4%nat [0x24c60]%Z [false; true].
apply evt_RZ_done. eapply (obj_64c j0 j e k); [| exact FS' | exact FR' | exact Hj | exact Hk | exact IH].
eapply (ser_mem_pure HIx); [exact INV' | exact MU | exact WM | assumption].
+
symb_run 6%nat [MEMAPPEND] [false; false].
destruct (ro_src m 0x105a2 [Z_to_bv 8 32] LB 1 (bv_unsigned sp + -208) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 32]);
[ exact INV' | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _).
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
apply rz_evt; [exact MOK2|].
symb_run 2%nat [0x24c60]%Z (@nil bool).
apply evt_RZ_done. eapply (obj_64c j0 j e k); [| exact FS2 | exact FR2 | exact Hj | exact Hk | exact IH].
eapply (ser_mem_pure HIx); [exact INV2 | exact MU | exact WM | assumption].
-
symb_run 5%nat [MEMAPPEND] [true].
destruct (ro_src m 0x122e0 [Z_to_bv 8 10] LB 1 (bv_unsigned sp + -208) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 10]);
[ exact INV' | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _).
pose proof INV2 as INV2'. destruct INV2' as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FRc2 & _).
oopen_frame FRc2 FR02 FRs2.
apply rz_evt; [exact MOK2|].
symb_run 11%nat [PBMEMSET] [false].
apply evt_RZ_done.
eapply (ser_memset HIx sp gp m0 md0 LB pb lo LO HT) with (F := F);
[ exact INV2 | lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
clear dependent m2.
intros m3 md3 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F3 fc3 INV3 FS3 FR3.
destruct (factsM _ _ _ _ INV3) as (MI3 & MOK3 & _).
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
apply rz_evt; [exact MOK3|].
symb_run 1%nat [0x24c60]%Z (@nil bool).
apply evt_RZ_done. eapply (obj_64c j0 j e k); [| exact FS3 | exact FR3 | exact Hj | exact Hk | exact IH].
eapply (ser_mem_pure HIx); [exact INV3 | exact MU | exact WM | assumption].
Qed.

#[using="MEMMOVE HEXP HT63 HGOT fc p rc pb0 t TBS KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_610 :
forall j0 j e hs sv5 sv7 x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -208) (objFR j0) m md -> fsaved F F' -> frm0 fc' -> nth_error es j = Some e -> (hs = 0 \/ hs = 1) ->
oloopK (LEN - Z.of_nat j - 1) ->
realizes rsegs (mkCfg (st_o 0x24c20 (oe_a e) sv5 sv7 x1 t0 t1 t2 (Z_to_bv 64 hs) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hj Hhs IH.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk).
destruct (nth_error kids j) as [k|] eqn:Hk.
2:{ exfalso. apply nth_error_None in Hk. pose proof (nth_error_lt _ _ _ Hj). rewrite <- LE in Hk. lia. }
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
destruct (factsE _ _ _ _ j e INV Hj) as (Hea & Hea2 & (pad & ENT) & _ & INk & Hk0 & Hk2 & Hkn).
pose proof (obj_val _ _ _ _ j e k INV Hj Hk) as HV. assert (Rv : 0 <= oe_v e < 2^47) by (destruct k; lia). clear HV.
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
oopen_frame FRc FR0 FRs.
unfold st_o, TP. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia).
assert (Rnx : 0 <= ohd (skipn (S j) es) < 2^47).
{ rewrite ohd_skipn. destruct (nth_error es (S j)) as [e'|] eqn:Hj'; [| lia].
destruct (factsE _ _ _ _ (S j) e' INV' Hj') as (Hea' & Hea2' & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hea2'. lia. }
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
destruct Hhs as [-> | ->].
-
symb_run 8%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m 0x1120c [Z_to_bv 8 44] LB 1 (bv_unsigned sp + -208) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 44]);
[ exact INV' | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
eapply (obj_630 j0 j e k); [exact INV2 | exact FS2 | exact FR2 | exact Hj | exact Hk | exact IH].
- symb_run 4%nat [0x24c40]%Z (@nil bool).
apply evt_RZ_done. eapply (obj_630 j0 j e k); [| exact FS' | exact FR' | exact Hj | exact Hk | exact IH].
eapply (ser_mem_pure HIx); [exact INV' | exact MU | exact WM | assumption].
Qed.

#[using="MEMMOVE HEXP HT63 HGOT fc p rc pb0 t TBS KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 OT0 LK LE KOK K Hf1 Hf2"] Lemma obj_loop : forall n, oloopK (Z.of_nat n).
Proof.
induction n as [|n IHn]; unfold oloopK; intros until md; intros INV FS' FR' Hj Hhs Hb.
- exfalso. pose proof (nth_error_lt _ _ _ Hj). unfold LEN in Hb. lia.
- eapply obj_610; [exact INV | exact FS' | exact FR' | exact Hj | exact Hhs |].
unfold oloopK in *. intros. eapply IHn; try eassumption. lia.
Qed.

#[using="MEMMOVE HEXP HT63 HGOT rc pb0 t TBS es KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA FRM INCL NODE0 OT0 LK LE KOK K f1 f2 Hf1 Hf2 LEN"] Lemma obj_entry :
forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m md A buf cap bpos content errv,
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core rsegs m pb buf bpos cap content ->
stk rsegs m lo usp ->
rw_cells rsegs m ERRNO [C4 errv] ->
heap_pres S4L LB usp m0 m -> model_vm_only md0 md -> t mod 16 = 0 ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 pb) (Z_to_bv 64 lv) (Z_to_bv 64 fl) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SER_OBJ) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP PB ST ERR HPR0 VM0 TAL.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INp' : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp') as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
assert (NODE : rw_cells rsegs m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string S4F) pb0 0 0 ++ [C8 (Z_to_bv 64 t)])).
{ eapply (heap_pres_rw_cells S4L); [exact HPR0 | exact NODE0 |]. right; right. exists (p, 48). split; [exact INp | cbn; lia]. }
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold TP, ERRNO in *. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_obj kids); lia). assert (Rfl64 : 0 <= fl < 2^64) by lia.
destruct PB as (Hbp & Hcap & Hln & PBS & PBUF).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
carve_frame 208%nat ST.
symb_run 23%nat [MEMAPPEND] (@nil bool).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m0 m1).
{ eapply heap_pres_trans; [exact HPR0|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
lazymatch type of FR with rw_cells _ _ _ ?cs => assert (INV1 : ser_memx (bv_unsigned sp + -208) cs m1 md) end.
{ exists A, buf, cap, bpos, content, errv.
split; [exact HP1|]. split; [split; [lia|]; split; [lia|]; split; [exact Hln|]; split; [exact PBS|exact PBUF]|].
split; [exact FR|]. split; [exact ERR|]. split; [exact ST|]. split; [exact HPR1 | exact VM0]. }
clear HP1 HPR1 MU WM.
destruct (ro_src m1 0x1304f [Z_to_bv 8 123] LB 1 (bv_unsigned sp + -208) MI1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 123]);
[ exact INV1 | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -208) with (bv_unsigned sp - 16 * 13) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
clear dependent m1.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _ & _ & _ & NODE2 & OT2 & _).
pose proof INV2 as INV2'. destruct INV2' as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FRc & ERR2 & ST2 & HPR2 & VM2).
unfold jhdr_cells in NODE2. cbn [app] in NODE2.
destruct OT2 as ((ta & tk & Htin & Ht1 & Ht2) & HD & _).
assert (HtL : In (ta, tk) LB) by (apply INCL; right; apply in_or_app; left; exact Htin).
pose proof (heap_blk S4L HIx _ _ _ _ ta tk HP2 ltac:(right; right; exact HtL)) as (_ & _ & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
assert (Rt : 1 <= t < 140737488355328) by lia.
assert (EHD : ohd es = match nth_error es 0 with Some x => oe_a x | None => 0 end) by (generalize es; intros [|x l]; reflexivity).
rewrite EHD in HD.
pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp + -208 + 208)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
apply rz_evt; [exact MOK2|].
destruct (nth_error es 0) as [e0|] eqn:He0.
2:{
symb_run 12%nat [0x24dd8]%Z [false; false; false; false]; [ idtac | chk_side .. ].
apply evt_RZ_done.
eapply obj_close with (pre := [CB 104 _]); [ | reflexivity | exact FS2 | exact FR2 ].
eapply oser_mem_frame; [exact INV2 | exact MU | exact WM | assumption | exact FRc | lia | cbn; lia]. }
destruct (factsE _ _ _ _ 0%nat e0 INV2 He0) as (Hea & Hea2 & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hea2.
pose proof (ealign 0%nat e0 He0) as Hal0.
symb_run 59%nat [0x24c20]%Z [false; false; false; false; false; false]; [ idtac | chk_side .. ].
rewrite (swrap32_id (lv + 1073741825)) in FRc by lia. rewrite (slt_succ_lit lv) by lia.
rewrite (u64_of_Z (lv + 1)) in FRc by lia. change (1 mod 32) with 1 in FRc. rewrite (Z.shiftl_mul_pow2 (lv + 1) 1) in FRc by lia.
change (2 ^ 1) with 2 in FRc. rewrite (swrap32_id ((lv + 1) * 2)) in FRc by lia.
replace ((lv + 1) * 2) with (2 * lv + 2) in FRc by lia.
rewrite FL8 in FRc. rewrite FL32, Hf1, Hf2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
assert (INV3 : exists j0, ser_memx (bv_unsigned sp + -208) (objFR j0) m3 md2).
{ eexists. eapply oser_mem_frame; [exact INV2 | exact MU | exact WM | exact MI3 | unfold objFR, objLoc; cbn [app]; unfold osavedR; exact FRc | lia | cbn; lia]. }
destruct INV3 as [j0 INV3].
apply evt_RZ_done.
pose proof (obj_loop (length es)) as OLK. unfold oloopK in OLK.
eapply (OLK j0 0%nat e0 1); [exact INV3 | exact FS2 | exact FR2 | exact He0 | right; reflexivity | unfold LEN; lia].
Qed.
End Ser.

Section SerObjMain.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (wz JHEX_SLOT)).

#[using="MEMMOVE HEXP HT63 HGOT"] Lemma ser_obj : forall kids,
(forall s', In (Some s') kids -> ser_spec HIx (fn_of s') s') ->
ser_spec HIx SER_OBJ (Sobj kids).
Proof.
intros kids KIDS. unfold ser_spec. intros until errv. intros HP PB JN INCL LBS FL Hlv Hlvd ST LO LOS SPA HT ERR TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (t & TBS & kvs & KBS & EREST & NODE & LH & Lkv & LK & KOK).
subst a0 a1 a2 a3 tp. rewrite EREST in INCL.
assert (POS : forall a n, In (a, n) TBS -> 0 < a /\ a mod 16 = 0).
{ intros a n Hin. assert (HinL : In (a, n) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; apply in_or_app; left; exact Hin).
pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (_ & Hal & Hlo & _). split; [exact Hlo | exact Hal]. }
destruct (lhtab_otab rsegs S4F _ _ _ _ LH POS) as (es & OT & Ekvs).
assert (TAL : t mod 16 = 0).
{ destruct LH as (tbl & size & es0 & svs & Hkvs & E & _). apply (POS t 56). rewrite E. left. reflexivity. }
rewrite Ekvs in KOK, Lkv. rewrite length_map in Lkv.
eapply (obj_entry HIx MEMMOVE HEXP HT63 HGOT) with (f1 := Z.land fl 1) (f2 := Z.land fl 2);
first [ exact KIDS | exact HP | exact PB | exact NODE | exact OT | exact TAL | exact KOK | exact INCL | exact K | eassumption | reflexivity
| apply heap_pres_refl | apply model_vm_only_refl ].
Qed.
End SerObjMain.

End RC__1.
