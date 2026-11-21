(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: both sections take its fields with QpvH.launch_ok and HSCLASS_R at kb_rseq; the CONFIG_RSEQ flag of the start-up layer: E_RND, the auxv size and stk_checks per value; the entry stack layout: the head, the pad and the strings up to ed_top in ptop_facts and img_present, with ed_top's page alignment and bound read from entry_launch_ok_va; pres_at reads KUnk entries; the stack window from stack_window_depth in stk_main). *)

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
| KUnk (SA b' k) (ELit n) => expr_eqb b b' && Z.leb k off && Z.ltb off (k + n) && Z.leb 0 n && Z.ltb n (2^64)
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
destruct K as [a w v| | a n kb | | | | | | | a n]; try discriminate.
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
- destruct a as [b' k]. destruct n as [nn| | | | | | |]; try discriminate.
apply andb_prop in HK as [HK H5]. apply andb_prop in HK as [HK H4]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
cbn [kentry_ok] in OK. destruct OK as (_ & OK). unfold elenZ, estart in OK. cbn [edenot a_base a_off] in OK.
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small in OK by lia.
specialize (OK (off - k) ltac:(lia)).
replace (bv_unsigned (edenot E b) + k + (off - k)) with (bv_unsigned (edenot E b) + off) in OK by lia.
destruct (base (Z_to_bv 64 (bv_unsigned (edenot E b) + off))) as [x|] eqn:Hx; [exists x; apply mrd_some; exact Hx | exfalso; congruence].
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

Definition E_RND (r : Z) : expr := fst (e_atrb r).
Lemma split_rnd : forall r, split_lit (e_atrandom (rseq_z r)) = (E_RND (rseq_z r), 24 + AUXSZ (rseq_z r)).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition stk_checks (r : bool) (k : list kentry) : bool :=
pres_ok k ESP0 0 24 && pres_ok k E_AUXV 24 (Z.to_nat (AUXSZ (rseq_z r)))
&& pres_ok k (E_RND (rseq_z r)) (24 + AUXSZ (rseq_z r)) 16.
Lemma STK_CHECKS : forall r w ch, HSCLASS_R r w ch -> stk_checks r (kn_view ch) = true.
Proof. intros [|] [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section Stk.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Variable apc : N.
Variable mbase : word.
Variable ifs : Fs.Fs.
Variable stdin : InputStream.
Variable gid : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abort_terminal : bool.
Variable urnd : InputStream.
Variable tmp : Fs.Fs.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variables rdr sgd sgt : bool.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : QpvH.launch_ok sp brk0 mbase rdraw (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt).
Let Hfes := proj1 Hfit.
Let Hkernel := proj1 (proj2 Hfit).
Let Hlaunch := proj1 (proj2 (proj2 Hfit)).
Let Hlau := proj2 (proj2 (proj2 Hfit)).
#[local] Ltac qpv X := first [ solve [eapply (X JOB6PH apc); eassumption] | solve [eapply (X JOB6PH); eassumption] | solve [eapply X; eassumption] ].
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
(* the state is one of the main-entry states of the run's own CONFIG_RSEQ value *)
Hypothesis HCLR : HSCLASS_R (kb_rseq kb) w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH apc sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) (argH0 sp rdraw argv envp kb execfn) fs E ch R FULL mo.
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw apc mbase ifs stdin gid groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw apc mbase ifs stdin gid groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
#[local] Notation EI := (E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
#[local] Notation RSEQ := (kb_rseq kb).
#[local] Notation RZ := (rseq_z RSEQ).
#[local] Notation CHEAD := (Z.of_nat (block_head_size RSEQ argv envp)).
#[local] Notation W := (Z.of_nat (block_pad_len RSEQ sp (ed_top rdraw) argv envp execfn)).
#[local] Notation STR0 := (usp + CHEAD + W).
#[local] Notation bsb := (entry_stack_image (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) mbase JOB6PH (Z_to_bv 64 (Z.of_N apc)) sp rdraw).
#[local] Notation PTOP := (bv_unsigned (ed_top rdraw)).

Lemma u_rnd : bv_unsigned (edenot E (E_RND RZ)) + 24 + AUXSZ RZ = usp + CHEAD - 16.
Proof.
pose proof (proj1 (P co_sinv)) as Senv.
rewrite (edenot_ev_agree NX0 E EI (E_RND RZ) Senv ltac:(destruct RSEQ; reflexivity) ltac:(destruct RSEQ; reflexivity)).
assert (U : uE EI (e_atrandom RZ) = usp + CHEAD - 16) by qpv QpvH.u_e_atrandom.
pose proof (split_lit_denot EI (e_atrandom RZ) (E_RND RZ) (24 + AUXSZ RZ) (split_rnd RSEQ)) as S.
unfold uE in U. rewrite S, u_lit64a in U.
pose proof (u64_range (edenot EI (E_RND RZ))). pose proof (u64_range sp).
destruct (MV4 usp_bounds) as (U1 & _ & _). assert (RR : 0 <= RZ <= 1) by qpv QpvH.RZ_range. unfold AUXSZ in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma ptop_facts : usp + Z.of_nat (length bsb) <= PTOP /\ PTOP <= 2^47 /\ TOPP usp <= PTOP
/\ usp + Z.of_nat (length bsb) = PTOP.
Proof.
assert (LB : Z.of_nat (length bsb) = stack_image_size sp (ed_top rdraw)) by qpv QpvH.length_bsb_eq.
assert (G : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb)) by qpv QpvH.bsb_ge.
pose proof (entry_page_top_within_window Sv48 (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) mbase sp brk0 rdraw Hlau) as T.
pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (T1 & T2 & T3 & T4).
unfold stack_image_size, entry_page_top, va_stack_top in LB, T. unfold TOPP.
(* LPS 727298f3: the stack top ed_top is page aligned (Run.valid_stack_top_va, entry_launch_ok_va's first conjunct) and below sp_window_hi = 2^47 *)
assert (TA : PTOP mod 4096 = 0) by (pose proof Hlau as ((TA0 & _ & _) & _ & _); exact TA0).
assert (TH : PTOP <= 2^47) by (unfold sp_window_hi in T; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
repeat split; try lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma hidden_present : forall a, usp <= a < PTOP -> argH0 sp rdraw argv envp kb execfn E (QZDE.wa a) = true -> exists b, m (QZDE.wa a) = Some b.
Proof.
intros a Ha Hh. destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3).
rewrite (MV4 view_stack) by lia. rewrite (proj2 (P co_sinv) (QZDE.wa a) Hh).
rewrite wrap_above_sp by (rewrite QZDE.wa_unsigned by lia; lia).
unfold stack_to_mem. rewrite QZDE.wa_unsigned by lia.
replace (usp <=? a) with true by (symmetry; apply Z.leb_le; lia).
replace (a - usp <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (nth_error bsb (Z.to_nat (a - usp))) as [b|] eqn:En; [exists b; reflexivity|].
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
assert (CH : CHEAD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * Z.of_nat (block_items argv envp mod 2)) by qpv QpvH.chead_eq.
assert (WR : 0 <= W <= 4110) by qpv QpvH.pad_range.
assert (RR : 0 <= RZ <= 1) by qpv QpvH.RZ_range.
pose proof (STK_CHECKS RSEQ w ch HCLR) as C. unfold stk_checks in C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
pose proof (MV4 u_esp0) as UE. pose proof (MV4 u_auxv) as UA. pose proof u_rnd as UR.
assert (HID : forall z,
(usp + 24 <= z < usp + 8 * argc + 8 * envc + 24) \/
(usp + 8 * argc + 8 * envc + 456 + 32 * RZ <= z < usp + CHEAD - 16) \/
(usp + CHEAD <= z < STR0) \/ (STR0 <= z < PTOP) ->
0 <= z < 2^64 -> argH0 sp rdraw argv envp kb execfn E (QZDE.wa z) = true).
{ intros z Hz Hr. unfold argH0. rewrite QZDE.wa_unsigned by lia. destruct Hz as [Hz|[Hz|[Hz|Hz]]].
- apply orb_true_iff. left. apply orb_true_iff. left. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. left. apply orb_true_iff. left. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. left. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
destruct (Z.lt_ge_cases a (usp + 24)) as [A1|A1]; [exact (known_present ESP0 0 24 a C1 ltac:(change (Z.of_nat 24) with 24; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a (usp + 8 * argc + 8 * envc + 24)) as [A2|A2]; [exact (hidden_present a Ha (HID a ltac:(left; lia) ltac:(lia)))|].
destruct (Z.lt_ge_cases a (usp + 8 * argc + 8 * envc + 456 + 32 * RZ)) as [A3|A3];
[exact (known_present E_AUXV 24 (Z.to_nat (AUXSZ RZ)) a C2 ltac:(unfold AUXSZ in *; rewrite Z2Nat.id by lia; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a (usp + CHEAD - 16)) as [A4|A4]; [exact (hidden_present a Ha (HID a ltac:(right; left; lia) ltac:(lia)))|].
destruct (Z.lt_ge_cases a (usp + CHEAD)) as [A5|A5];
[exact (known_present (E_RND RZ) (24 + AUXSZ RZ) 16 a C3 ltac:(change (Z.of_nat 16) with 16; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a STR0) as [A6|A6]; [exact (hidden_present a Ha (HID a ltac:(right; right; left; lia) ltac:(lia)))|].
exact (hidden_present a Ha (HID a ltac:(right; right; right; lia) ltac:(lia))).
Qed.

Theorem stk_main : QWxq_c1.stk JOB6SEGS m (usp - 6144513) (TOPP usp).
Proof.
destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3).
pose proof (MV4 drv_stk HCLR) as (S1 & S2 & S3).
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
| KUnk (SA b' k) (ELit n) => expr_eqb b b' && Z.leb k off && Z.ltb off (k + n) && Z.leb 0 n && Z.ltb n (2^64)
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
destruct K as [a w v| | a n kb | | | | | | | a n]; try discriminate.
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
- destruct a as [b' k]. destruct n as [nn| | | | | | |]; try discriminate.
apply andb_prop in HK as [HK H5]. apply andb_prop in HK as [HK H4]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
cbn [kentry_ok] in OK. destruct OK as (_ & OK). unfold elenZ, estart in OK. cbn [edenot a_base a_off] in OK.
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small in OK by lia.
specialize (OK (off - k) ltac:(lia)).
replace (bv_unsigned (edenot E b) + k + (off - k)) with (bv_unsigned (edenot E b) + off) in OK by lia.
destruct (base (Z_to_bv 64 (bv_unsigned (edenot E b) + off))) as [x|] eqn:Hx; [exists x; apply mrd_some; exact Hx | exfalso; congruence].
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

Definition E_RND (r : Z) : expr := fst (e_atrb r).
Lemma split_rnd : forall r, split_lit (e_atrandom (rseq_z r)) = (E_RND (rseq_z r), 24 + AUXSZ (rseq_z r)).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition stk_checks (r : bool) (k : list kentry) : bool :=
pres_ok k ESP0 0 24 && pres_ok k E_AUXV 24 (Z.to_nat (AUXSZ (rseq_z r)))
&& pres_ok k (E_RND (rseq_z r)) (24 + AUXSZ (rseq_z r)) 16.
Lemma STK_CHECKS : forall r w ch, HSCLASS_R r w ch -> stk_checks r (kn_view ch) = true.
Proof. intros [|] [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section Stk.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Variable apc : N.
Variable mbase : word.
Variable ifs : Fs.Fs.
Variable stdin : InputStream.
Variable gid : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abort_terminal : bool.
Variable urnd : InputStream.
Variable tmp : Fs.Fs.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variables rdr sgd sgt : bool.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : QpvH.launch_ok sp brk0 mbase rdraw (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt).
Let Hfes := proj1 Hfit.
Let Hkernel := proj1 (proj2 Hfit).
Let Hlaunch := proj1 (proj2 (proj2 Hfit)).
Let Hlau := proj2 (proj2 (proj2 Hfit)).
#[local] Ltac qpv X := first [ solve [eapply (X JO6PH apc); eassumption] | solve [eapply (X JO6PH); eassumption] | solve [eapply X; eassumption] ].
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
(* the state is one of the main-entry states of the run's own CONFIG_RSEQ value *)
Hypothesis HCLR : HSCLASS_R (kb_rseq kb) w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH apc sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) (argH0 sp rdraw argv envp kb execfn) fs E ch R FULL mo.
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw apc mbase ifs stdin gid groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw apc mbase ifs stdin gid groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
#[local] Notation EI := (E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
#[local] Notation RSEQ := (kb_rseq kb).
#[local] Notation RZ := (rseq_z RSEQ).
#[local] Notation CHEAD := (Z.of_nat (block_head_size RSEQ argv envp)).
#[local] Notation W := (Z.of_nat (block_pad_len RSEQ sp (ed_top rdraw) argv envp execfn)).
#[local] Notation STR0 := (usp + CHEAD + W).
#[local] Notation bsb := (entry_stack_image (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) mbase JO6PH (Z_to_bv 64 (Z.of_N apc)) sp rdraw).
#[local] Notation PTOP := (bv_unsigned (ed_top rdraw)).

Lemma u_rnd : bv_unsigned (edenot E (E_RND RZ)) + 24 + AUXSZ RZ = usp + CHEAD - 16.
Proof.
pose proof (proj1 (P co_sinv)) as Senv.
rewrite (edenot_ev_agree NX0 E EI (E_RND RZ) Senv ltac:(destruct RSEQ; reflexivity) ltac:(destruct RSEQ; reflexivity)).
assert (U : uE EI (e_atrandom RZ) = usp + CHEAD - 16) by qpv QpvH.u_e_atrandom.
pose proof (split_lit_denot EI (e_atrandom RZ) (E_RND RZ) (24 + AUXSZ RZ) (split_rnd RSEQ)) as S.
unfold uE in U. rewrite S, u_lit64a in U.
pose proof (u64_range (edenot EI (E_RND RZ))). pose proof (u64_range sp).
destruct (MV4 usp_bounds) as (U1 & _ & _). assert (RR : 0 <= RZ <= 1) by qpv QpvH.RZ_range. unfold AUXSZ in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma ptop_facts : usp + Z.of_nat (length bsb) <= PTOP /\ PTOP <= 2^47 /\ TOPP usp <= PTOP
/\ usp + Z.of_nat (length bsb) = PTOP.
Proof.
assert (LB : Z.of_nat (length bsb) = stack_image_size sp (ed_top rdraw)) by qpv QpvH.length_bsb_eq.
assert (G : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb)) by qpv QpvH.bsb_ge.
pose proof (entry_page_top_within_window Sv48 (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) mbase sp brk0 rdraw Hlau) as T.
pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (T1 & T2 & T3 & T4).
unfold stack_image_size, entry_page_top, va_stack_top in LB, T. unfold TOPP.
(* LPS 727298f3: the stack top ed_top is page aligned (Run.valid_stack_top_va, entry_launch_ok_va's first conjunct) and below sp_window_hi = 2^47 *)
assert (TA : PTOP mod 4096 = 0) by (pose proof Hlau as ((TA0 & _ & _) & _ & _); exact TA0).
assert (TH : PTOP <= 2^47) by (unfold sp_window_hi in T; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
repeat split; try lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma hidden_present : forall a, usp <= a < PTOP -> argH0 sp rdraw argv envp kb execfn E (QZDE.wa a) = true -> exists b, m (QZDE.wa a) = Some b.
Proof.
intros a Ha Hh. destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3).
rewrite (MV4 view_stack) by lia. rewrite (proj2 (P co_sinv) (QZDE.wa a) Hh).
rewrite wrap_above_sp by (rewrite QZDE.wa_unsigned by lia; lia).
unfold stack_to_mem. rewrite QZDE.wa_unsigned by lia.
replace (usp <=? a) with true by (symmetry; apply Z.leb_le; lia).
replace (a - usp <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (nth_error bsb (Z.to_nat (a - usp))) as [b|] eqn:En; [exists b; reflexivity|].
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
assert (CH : CHEAD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * Z.of_nat (block_items argv envp mod 2)) by qpv QpvH.chead_eq.
assert (WR : 0 <= W <= 4110) by qpv QpvH.pad_range.
assert (RR : 0 <= RZ <= 1) by qpv QpvH.RZ_range.
pose proof (STK_CHECKS RSEQ w ch HCLR) as C. unfold stk_checks in C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
pose proof (MV4 u_esp0) as UE. pose proof (MV4 u_auxv) as UA. pose proof u_rnd as UR.
assert (HID : forall z,
(usp + 24 <= z < usp + 8 * argc + 8 * envc + 24) \/
(usp + 8 * argc + 8 * envc + 456 + 32 * RZ <= z < usp + CHEAD - 16) \/
(usp + CHEAD <= z < STR0) \/ (STR0 <= z < PTOP) ->
0 <= z < 2^64 -> argH0 sp rdraw argv envp kb execfn E (QZDE.wa z) = true).
{ intros z Hz Hr. unfold argH0. rewrite QZDE.wa_unsigned by lia. destruct Hz as [Hz|[Hz|[Hz|Hz]]].
- apply orb_true_iff. left. apply orb_true_iff. left. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. left. apply orb_true_iff. left. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. left. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
destruct (Z.lt_ge_cases a (usp + 24)) as [A1|A1]; [exact (known_present ESP0 0 24 a C1 ltac:(change (Z.of_nat 24) with 24; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a (usp + 8 * argc + 8 * envc + 24)) as [A2|A2]; [exact (hidden_present a Ha (HID a ltac:(left; lia) ltac:(lia)))|].
destruct (Z.lt_ge_cases a (usp + 8 * argc + 8 * envc + 456 + 32 * RZ)) as [A3|A3];
[exact (known_present E_AUXV 24 (Z.to_nat (AUXSZ RZ)) a C2 ltac:(unfold AUXSZ in *; rewrite Z2Nat.id by lia; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a (usp + CHEAD - 16)) as [A4|A4]; [exact (hidden_present a Ha (HID a ltac:(right; left; lia) ltac:(lia)))|].
destruct (Z.lt_ge_cases a (usp + CHEAD)) as [A5|A5];
[exact (known_present (E_RND RZ) (24 + AUXSZ RZ) 16 a C3 ltac:(change (Z.of_nat 16) with 16; lia) ltac:(lia))|].
destruct (Z.lt_ge_cases a STR0) as [A6|A6]; [exact (hidden_present a Ha (HID a ltac:(right; right; left; lia) ltac:(lia)))|].
exact (hidden_present a Ha (HID a ltac:(right; right; right; lia) ltac:(lia))).
Qed.

Theorem stk_main : QWxq_c1.stk JO6SEGS m (usp - 6144513) (TOPP usp).
Proof.
destruct ptop_facts as (T1 & T2 & T3 & T4). destruct (MV4 usp_bounds) as (U1 & U2 & U3).
pose proof (MV4 drv_stk HCLR) as (S1 & S2 & S3).
split; [lia|]. split; [lia|]. intros a Ha.
destruct (Z.lt_ge_cases a usp) as [LT|GE]; [apply S3; lia|].
destruct (img_present a ltac:(lia)) as (x & Hx).
split; [unfold wview; rewrite Hx; discriminate | exists x; unfold QZDE.mrd; rewrite Hx; reflexivity].
Qed.
End Stk.
