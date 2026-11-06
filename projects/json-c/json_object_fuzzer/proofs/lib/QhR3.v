(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE QWxq_c1 Qsn5 QJFf QWTC QgpE Q85Z QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QyaF QXVi QQjP QJQc QKY2 QvSK QXDj Q45h QOTx Q25t QNDM Q7DP QlHe QZxC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5 QJFf.Mq1.
Import QWTC QgpE Q85Z.Mq1 QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QvSK.Mq0 QXDj Q45h QOTx Q25t QNDM Q7DP QlHe QZxC.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition pres_at (kn : list kentry) (b : expr) (off : Z) : bool :=
existsb (fun K => match K with
| KWord (SA b' k) w _ => expr_eqb b b' && Z.leb k off && Z.ltb off (k + Z.of_nat w)
| KBlob (SA b' k) (ELit n) _ => expr_eqb b b' && Z.leb k off && Z.ltb off (k + n) && Z.leb 0 n && Z.ltb n (2^64)
| _ => false end) kn.
Fixpoint pres_ok (kn : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
match n with O => true | S n' => pres_at kn b off && pres_ok kn b (off + 1) n' end.

Section Pres.
Variable segs : list Segment.
Variables (E : env) (base : word -> option byte) (kn : list kentry).
Hypothesis KN : know_ok segs E base kn.

Lemma pres_at_sound : forall b off, pres_at kn b off = true ->
exists x, QZDE.mrd segs base (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) = Some x.
Proof.
intros b off H. unfold pres_at in H. apply existsb_exists in H as (K & HIn & HK).
pose proof (proj1 (Forall_forall _ _) KN K HIn) as OK.
destruct K as [a w v| | a n kb | | | | | | |]; try discriminate.
- destruct a as [b' k]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
cbn [kentry_ok] in OK. destruct OK as (_ & FL & RD).
pose proof (flat_u E _ _ FL) as FU. unfold estart in FU. cbn [a_base a_off] in FU.
destruct FL as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
pose proof (rdn_mrd_c segs base w _ _ (Z.to_nat (off - k)) RD ltac:(lia) ltac:(rewrite FU; exact F4)) as Rd. rewrite FU in Rd.
rewrite Z2Nat.id in Rd by lia. replace (bv_unsigned (edenot E b) + k + (off - k)) with (bv_unsigned (edenot E b) + off) in Rd by lia.
rewrite Rd. destruct (nth_error (word_to_le_bytes w (edenot E v)) (Z.to_nat (off - k))) as [x|] eqn:En; [exists x; reflexivity|].
apply nth_error_None in En. rewrite length_N_to_le_bytes in En. lia.
- destruct a as [b' k]. destruct n as [nn| | | | | | |]; try discriminate.
apply andb_prop in HK as [HK H5]. apply andb_prop in HK as [HK H4]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
cbn [kentry_ok] in OK. destruct OK as (_ & _ & OK). unfold elenZ, estart in OK. cbn [edenot a_base a_off] in OK.
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small in OK by lia.
specialize (OK (off - k) ltac:(lia)). replace (bv_unsigned (edenot E b) + k + (off - k)) with (bv_unsigned (edenot E b) + off) in OK by lia.
eexists. apply mrd_some. exact OK.
Qed.

Lemma pres_ok_sound : forall n b off, pres_ok kn b off n = true -> forall i, 0 <= i < Z.of_nat n ->
exists x, QZDE.mrd segs base (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some x.
Proof.
induction n as [|n IH]; intros b off H i Hi; [lia|]. cbn [pres_ok] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec i 0) as [->|NZ]; [rewrite Z.add_0_r; exact (pres_at_sound b off H1)|].
replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E b) + (off + 1) + (i - 1)) by lia.
apply (IH b (off + 1) H2). lia.
Qed.
End Pres.

Definition E_RND : expr :=
EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
(EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2))
(EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))).
Lemma split_rnd : split_lit e_atrandom = (E_RND, 184).  Proof. vm_compute. reflexivity. Qed.

Definition stk_checks (k : list kentry) : bool := pres_ok k ESP0 0 24 && pres_ok k E_AUXV 24 160 && pres_ok k E_RND 184 16.
Lemma STK_CHECKS : forall w ch, HSCLASS_S w ch -> stk_checks (kn_view ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section Stk.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
#[local] Notation EI := (E0 JOB6PH sp rdraw brk0 argv envp uid hw).
#[local] Notation bsb := (build_stack_bytes JOB6PH sp argv envp uid hw rdraw).
#[local] Notation PTOP := (entry_page_top sp bsb).

Lemma u_rnd : bv_unsigned (edenot E E_RND) + 184 = usp + Z.of_nat (length bsb) - 16.
Proof.
pose proof (proj1 (P co_sinv)) as Senv.
rewrite (edenot_ev_agree NX0 E EI E_RND Senv eq_refl eq_refl).
pose proof (QpvH.u_e_atrandom JOB6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U.
pose proof (split_lit_denot EI e_atrandom E_RND 184 split_rnd) as S.
unfold uE in U. rewrite S, u_lit64a in U.
pose proof (u64_range (edenot EI E_RND)). pose proof (u64_range sp).
pose proof (QpvH.usp_fit JOB6PH sp rdraw argv envp uid hw Hfit) as Ufit.
pose proof (QpvH.bsb_ge JOB6PH sp rdraw argv envp uid hw) as [G _].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma ptop_facts : usp + Z.of_nat (length bsb) <= PTOP /\ PTOP <= 2^47 /\ TOPP usp <= PTOP
/\ usp + Z.of_nat (length (entry_stack_image JOB6PH sp argv envp uid hw rdraw)) = PTOP.
Proof.
pose proof (entry_page_top_within_window JOB6PH sp argv envp uid hw rdraw Hfit) as T. unfold sp_window_hi in T.
pose proof (entry_stack_image_top JOB6PH sp argv envp uid hw rdraw) as IT.
pose proof (QpvH.bsb_ge JOB6PH sp rdraw argv envp uid hw) as [G _]. destruct (MV4 len_bounds) as [LA LE].
pose proof Hsp as (S1 & S2 & S3). unfold sp_window_lo, sp_window_hi in S1, S2.
unfold entry_page_top, entry_block_top, page_round_up_Z, page_size in *. unfold TOPP.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
repeat split; try lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma hidden_present : forall a, usp <= a < PTOP -> argH0 JOB6PH sp rdraw argv envp uid hw E (QZDE.wa a) = true -> exists b, m (QZDE.wa a) = Some b.
Proof.
intros a Ha Hh. destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3).
rewrite (MV4 view_stack) by lia. rewrite (proj2 (P co_sinv) (QZDE.wa a) Hh).
rewrite wrap_above_sp by (rewrite QZDE.wa_unsigned by lia; lia).
unfold stack_to_mem. rewrite QZDE.wa_unsigned by lia.
replace (usp <=? a) with true by (symmetry; apply Z.leb_le; lia).
replace (a - usp <? Z.of_nat (length (entry_stack_image JOB6PH sp argv envp uid hw rdraw))) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (nth_error (entry_stack_image JOB6PH sp argv envp uid hw rdraw) (Z.to_nat (a - usp))) as [b|] eqn:En; [exists b; reflexivity|].
apply nth_error_None in En. lia.
Qed.

Lemma known_present : forall b off n a, pres_ok (kn_view ch) b off n = true ->
bv_unsigned (edenot E b) + off <= a < bv_unsigned (edenot E b) + off + Z.of_nat n -> 0x7fff80000000 <= a < 2^64 ->
exists x, m (QZDE.wa a) = Some x.
Proof.
intros b off n a C Ha Hr.
destruct (pres_ok_sound JOB6SEGS E m (kn_view ch) KV n b off C (a - (bv_unsigned (edenot E b) + off)) ltac:(lia)) as (x & Hx).
replace (bv_unsigned (edenot E b) + off + (a - (bv_unsigned (edenot E b) + off))) with a in Hx by lia.
change (Z_to_bv 64 a) with (QZDE.wa a) in Hx.
destruct (m (QZDE.wa a)) as [y|] eqn:Em; [exists y; reflexivity|]. exfalso. unfold QZDE.mrd in Hx. rewrite Em in Hx.
unfold QsjA.seg_rom, memory_read in Hx. cbn [Z.of_N] in Hx.
rewrite (JOB6SEGS_low (QZDE.wa a)) in Hx; [discriminate|]. rewrite QZDE.wa_unsigned by lia. unfold QzgH.kLowEnd. lia.
Qed.

Theorem img_present : forall a, usp <= a < PTOP -> exists x, m (QZDE.wa a) = Some x.
Proof.
intros a Ha. destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3). destruct (MV4 len_bounds) as [LA LE].
destruct (QpvH.W_range JOB6PH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & _).
pose proof (STK_CHECKS w ch HCL) as C. unfold stk_checks in C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
pose proof (MV4 u_esp0) as UE. pose proof (MV4 u_auxv) as UA. pose proof u_rnd as UR.
assert (HID : forall z, (usp + 24 <= z < usp + 8 * argc + 8 * envc + 24) \/ (usp + 8 * argc + 8 * envc + 184 <= z < usp + Z.of_nat (length bsb) - 16)
\/ (usp + Z.of_nat (length bsb) <= z < PTOP) -> 0 <= z < 2^64 -> argH0 JOB6PH sp rdraw argv envp uid hw E (QZDE.wa z) = true).
{ intros z Hz Hr. unfold argH0. rewrite QZDE.wa_unsigned by lia. destruct Hz as [Hz|[Hz|Hz]].
- apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
destruct (Z.lt_ge_cases a (usp + 24)) as [A1|A1]; [exact (known_present ESP0 0 24 a C1 ltac:(change (Z.of_nat 24) with 24; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a (usp + 8 * argc + 8 * envc + 24)) as [A2|A2]; [exact (hidden_present a Ha (HID a ltac:(lia) ltac:(lia)))|].
destruct (Z.lt_ge_cases a (usp + 8 * argc + 8 * envc + 184)) as [A3|A3]; [exact (known_present E_AUXV 24 160 a C2 ltac:(change (Z.of_nat 160) with 160; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a (usp + Z.of_nat (length bsb) - 16)) as [A4|A4]; [exact (hidden_present a Ha (HID a ltac:(lia) ltac:(lia)))|].
destruct (Z.lt_ge_cases a (usp + Z.of_nat (length bsb))) as [A5|A5]; [exact (known_present E_RND 184 16 a C3 ltac:(change (Z.of_nat 16) with 16; lia) ltac:(lia))|].
exact (hidden_present a Ha (HID a ltac:(lia) ltac:(lia))).
Qed.

Theorem stk_main : QWxq_c1.stk JOB6SEGS m (usp - 8388608) (TOPP usp).
Proof.
destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3).
pose proof (MV4 drv_stk) as (S1 & S2 & S3).
split; [lia|]. split; [lia|]. intros a Ha.
destruct (Z.lt_ge_cases a usp) as [LT|GE]; [apply S3; lia|].
destruct (img_present a ltac:(lia)) as (x & Hx).
split; [unfold wview; rewrite Hx; discriminate | exists x; unfold QZDE.mrd; rewrite Hx; reflexivity].
Qed.
End Stk.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5o6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qxua.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qxua. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZxC.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition pres_at (kn : list kentry) (b : expr) (off : Z) : bool :=
existsb (fun K => match K with
| KWord (SA b' k) w _ => expr_eqb b b' && Z.leb k off && Z.ltb off (k + Z.of_nat w)
| KBlob (SA b' k) (ELit n) _ => expr_eqb b b' && Z.leb k off && Z.ltb off (k + n) && Z.leb 0 n && Z.ltb n (2^64)
| _ => false end) kn.
Fixpoint pres_ok (kn : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
match n with O => true | S n' => pres_at kn b off && pres_ok kn b (off + 1) n' end.

Section Pres.
Variable segs : list Segment.
Variables (E : env) (base : word -> option byte) (kn : list kentry).
Hypothesis KN : know_ok segs E base kn.

Lemma pres_at_sound : forall b off, pres_at kn b off = true ->
exists x, QZDE.mrd segs base (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) = Some x.
Proof.
intros b off H. unfold pres_at in H. apply existsb_exists in H as (K & HIn & HK).
pose proof (proj1 (Forall_forall _ _) KN K HIn) as OK.
destruct K as [a w v| | a n kb | | | | | | |]; try discriminate.
- destruct a as [b' k]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
cbn [kentry_ok] in OK. destruct OK as (_ & FL & RD).
pose proof (flat_u E _ _ FL) as FU. unfold estart in FU. cbn [a_base a_off] in FU.
destruct FL as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
pose proof (rdn_mrd_c segs base w _ _ (Z.to_nat (off - k)) RD ltac:(lia) ltac:(rewrite FU; exact F4)) as Rd. rewrite FU in Rd.
rewrite Z2Nat.id in Rd by lia. replace (bv_unsigned (edenot E b) + k + (off - k)) with (bv_unsigned (edenot E b) + off) in Rd by lia.
rewrite Rd. destruct (nth_error (word_to_le_bytes w (edenot E v)) (Z.to_nat (off - k))) as [x|] eqn:En; [exists x; reflexivity|].
apply nth_error_None in En. rewrite length_N_to_le_bytes in En. lia.
- destruct a as [b' k]. destruct n as [nn| | | | | | |]; try discriminate.
apply andb_prop in HK as [HK H5]. apply andb_prop in HK as [HK H4]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
cbn [kentry_ok] in OK. destruct OK as (_ & _ & OK). unfold elenZ, estart in OK. cbn [edenot a_base a_off] in OK.
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small in OK by lia.
specialize (OK (off - k) ltac:(lia)). replace (bv_unsigned (edenot E b) + k + (off - k)) with (bv_unsigned (edenot E b) + off) in OK by lia.
eexists. apply mrd_some. exact OK.
Qed.

Lemma pres_ok_sound : forall n b off, pres_ok kn b off n = true -> forall i, 0 <= i < Z.of_nat n ->
exists x, QZDE.mrd segs base (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some x.
Proof.
induction n as [|n IH]; intros b off H i Hi; [lia|]. cbn [pres_ok] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec i 0) as [->|NZ]; [rewrite Z.add_0_r; exact (pres_at_sound b off H1)|].
replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E b) + (off + 1) + (i - 1)) by lia.
apply (IH b (off + 1) H2). lia.
Qed.
End Pres.

Definition E_RND : expr :=
EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
(EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2))
(EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))).
Lemma split_rnd : split_lit e_atrandom = (E_RND, 184).  Proof. vm_compute. reflexivity. Qed.

Definition stk_checks (k : list kentry) : bool := pres_ok k ESP0 0 24 && pres_ok k E_AUXV 24 160 && pres_ok k E_RND 184 16.
Lemma STK_CHECKS : forall w ch, HSCLASS_S w ch -> stk_checks (kn_view ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section Stk.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
#[local] Notation EI := (E0 JO6PH sp rdraw brk0 argv envp uid hw).
#[local] Notation bsb := (build_stack_bytes JO6PH sp argv envp uid hw rdraw).
#[local] Notation PTOP := (entry_page_top sp bsb).

Lemma u_rnd : bv_unsigned (edenot E E_RND) + 184 = usp + Z.of_nat (length bsb) - 16.
Proof.
pose proof (proj1 (P co_sinv)) as Senv.
rewrite (edenot_ev_agree NX0 E EI E_RND Senv eq_refl eq_refl).
pose proof (QpvH.u_e_atrandom JO6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U.
pose proof (split_lit_denot EI e_atrandom E_RND 184 split_rnd) as S.
unfold uE in U. rewrite S, u_lit64a in U.
pose proof (u64_range (edenot EI E_RND)). pose proof (u64_range sp).
pose proof (QpvH.usp_fit JO6PH sp rdraw argv envp uid hw Hfit) as Ufit.
pose proof (QpvH.bsb_ge JO6PH sp rdraw argv envp uid hw) as [G _].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma ptop_facts : usp + Z.of_nat (length bsb) <= PTOP /\ PTOP <= 2^47 /\ TOPP usp <= PTOP
/\ usp + Z.of_nat (length (entry_stack_image JO6PH sp argv envp uid hw rdraw)) = PTOP.
Proof.
pose proof (entry_page_top_within_window JO6PH sp argv envp uid hw rdraw Hfit) as T. unfold sp_window_hi in T.
pose proof (entry_stack_image_top JO6PH sp argv envp uid hw rdraw) as IT.
pose proof (QpvH.bsb_ge JO6PH sp rdraw argv envp uid hw) as [G _]. destruct (MV4 len_bounds) as [LA LE].
pose proof Hsp as (S1 & S2 & S3). unfold sp_window_lo, sp_window_hi in S1, S2.
unfold entry_page_top, entry_block_top, page_round_up_Z, page_size in *. unfold TOPP.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
repeat split; try lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma hidden_present : forall a, usp <= a < PTOP -> argH0 JO6PH sp rdraw argv envp uid hw E (QZDE.wa a) = true -> exists b, m (QZDE.wa a) = Some b.
Proof.
intros a Ha Hh. destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3).
rewrite (MV4 view_stack) by lia. rewrite (proj2 (P co_sinv) (QZDE.wa a) Hh).
rewrite wrap_above_sp by (rewrite QZDE.wa_unsigned by lia; lia).
unfold stack_to_mem. rewrite QZDE.wa_unsigned by lia.
replace (usp <=? a) with true by (symmetry; apply Z.leb_le; lia).
replace (a - usp <? Z.of_nat (length (entry_stack_image JO6PH sp argv envp uid hw rdraw))) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (nth_error (entry_stack_image JO6PH sp argv envp uid hw rdraw) (Z.to_nat (a - usp))) as [b|] eqn:En; [exists b; reflexivity|].
apply nth_error_None in En. lia.
Qed.

Lemma known_present : forall b off n a, pres_ok (kn_view ch) b off n = true ->
bv_unsigned (edenot E b) + off <= a < bv_unsigned (edenot E b) + off + Z.of_nat n -> 0x7fff80000000 <= a < 2^64 ->
exists x, m (QZDE.wa a) = Some x.
Proof.
intros b off n a C Ha Hr.
destruct (pres_ok_sound JO6SEGS E m (kn_view ch) KV n b off C (a - (bv_unsigned (edenot E b) + off)) ltac:(lia)) as (x & Hx).
replace (bv_unsigned (edenot E b) + off + (a - (bv_unsigned (edenot E b) + off))) with a in Hx by lia.
change (Z_to_bv 64 a) with (QZDE.wa a) in Hx.
destruct (m (QZDE.wa a)) as [y|] eqn:Em; [exists y; reflexivity|]. exfalso. unfold QZDE.mrd in Hx. rewrite Em in Hx.
unfold QsjA.seg_rom, memory_read in Hx. cbn [Z.of_N] in Hx.
rewrite (JO6SEGS_low (QZDE.wa a)) in Hx; [discriminate|]. rewrite QZDE.wa_unsigned by lia. unfold QzgH.kLowEnd. lia.
Qed.

Theorem img_present : forall a, usp <= a < PTOP -> exists x, m (QZDE.wa a) = Some x.
Proof.
intros a Ha. destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3). destruct (MV4 len_bounds) as [LA LE].
destruct (QpvH.W_range JO6PH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & _).
pose proof (STK_CHECKS w ch HCL) as C. unfold stk_checks in C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
pose proof (MV4 u_esp0) as UE. pose proof (MV4 u_auxv) as UA. pose proof u_rnd as UR.
assert (HID : forall z, (usp + 24 <= z < usp + 8 * argc + 8 * envc + 24) \/ (usp + 8 * argc + 8 * envc + 184 <= z < usp + Z.of_nat (length bsb) - 16)
\/ (usp + Z.of_nat (length bsb) <= z < PTOP) -> 0 <= z < 2^64 -> argH0 JO6PH sp rdraw argv envp uid hw E (QZDE.wa z) = true).
{ intros z Hz Hr. unfold argH0. rewrite QZDE.wa_unsigned by lia. destruct Hz as [Hz|[Hz|Hz]].
- apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
destruct (Z.lt_ge_cases a (usp + 24)) as [A1|A1]; [exact (known_present ESP0 0 24 a C1 ltac:(change (Z.of_nat 24) with 24; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a (usp + 8 * argc + 8 * envc + 24)) as [A2|A2]; [exact (hidden_present a Ha (HID a ltac:(lia) ltac:(lia)))|].
destruct (Z.lt_ge_cases a (usp + 8 * argc + 8 * envc + 184)) as [A3|A3]; [exact (known_present E_AUXV 24 160 a C2 ltac:(change (Z.of_nat 160) with 160; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a (usp + Z.of_nat (length bsb) - 16)) as [A4|A4]; [exact (hidden_present a Ha (HID a ltac:(lia) ltac:(lia)))|].
destruct (Z.lt_ge_cases a (usp + Z.of_nat (length bsb))) as [A5|A5]; [exact (known_present E_RND 184 16 a C3 ltac:(change (Z.of_nat 16) with 16; lia) ltac:(lia))|].
exact (hidden_present a Ha (HID a ltac:(lia) ltac:(lia))).
Qed.

Theorem stk_main : QWxq_c1.stk JO6SEGS m (usp - 8388608) (TOPP usp).
Proof.
destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3).
pose proof (MV4 drv_stk) as (S1 & S2 & S3).
split; [lia|]. split; [lia|]. intros a Ha.
destruct (Z.lt_ge_cases a usp) as [LT|GE]; [apply S3; lia|].
destruct (img_present a ltac:(lia)) as (x & Hx).
split; [unfold wview; rewrite Hx; discriminate | exists x; unfold QZDE.mrd; rewrite Hx; reflexivity].
Qed.
End Stk.
