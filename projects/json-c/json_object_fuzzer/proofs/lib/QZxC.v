(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5 QJFf QWxq_c1 Q6q3 Qwm6 QupI Qirj QJ4Q QWTC QgpE QG64 QND5 QsSk Qt8n QWtD QEdo QDlz QOTP Q1LT QpvH QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QNDM Q7DP QvSK QvQl Qn7S QlHe Qvjf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import Qsn5 QJFf.Mq1.

Import QWTC QgpE QG64 QND5 QsSk Qt8n QWtD QEdo.Mq0 QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QvSK.Mq0 QvQl.Mq0 QvQl Qn7S QlHe Qvjf.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma ARG_CHECKS : forall w ch, HSCLASS_S w ch -> arg_pieces_check (kn_view ch) = true.
Proof. intros [|] ch [-> | ->]; [exact ARGPIECES_HS2sA_1_ok | exact ARGPIECES_HS2sA_2_ok | exact ARGPIECES_HS2sB_3_ok | exact ARGPIECES_HS2sB_4_ok]. Qed.

Lemma ESP0_eq : ESP0 = e_sp0.  Proof. reflexivity. Qed.
Lemma EARGV0_eq : EARGV0 = e_str0.  Proof. reflexivity. Qed.
Lemma EARGV1_eq : EARGV1 = e_argv1w.  Proof. reflexivity. Qed.

Lemma total_firstn_succ : forall (av : list (list byte)) k, (k < length av)%nat ->
(total_arg_bytes_nat (firstn k av) + length (nth k av []) + 1 <= total_arg_bytes_nat av)%nat.
Proof.
induction av as [|a r IH]; intros k Hk; [cbn in Hk; lia|]. destruct k as [|k].
- cbn [firstn nth total_arg_bytes_nat fold_right]. unfold total_arg_bytes_nat. cbn [fold_right]. lia.
- cbn [firstn nth]. unfold total_arg_bytes_nat in *. cbn [fold_right]. cbn [length] in Hk. specialize (IH k ltac:(lia)). lia.
Qed.

Section DrvPre2.
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
#[local] Notation STR0 := (usp + 8 * argc + 8 * envc + 184).

Lemma Senv : forall n, (n < NX0)%nat -> ev E n = ev EI n.
Proof. exact (proj1 (P co_sinv)). Qed.
Lemma u_esp0 : bv_unsigned (edenot E ESP0) = usp.
Proof. rewrite ESP0_eq, (MA main_sp0). reflexivity. Qed.

Lemma len_bounds : 1 <= argc <= 1024 /\ 0 <= envc <= 256.
Proof. destruct Hva as [A _]. destruct Hve as [B _]. lia. Qed.
Lemma usp_bounds : 0x7fff80000000 <= usp /\ usp mod 16 = 0 /\ usp + Z.of_nat (length (build_stack_bytes JOB6PH sp argv envp uid hw rdraw)) <= 2^47.
Proof.
destruct Hsp as (H1 & _ & H3). unfold sp_window_lo in H1. split; [exact H1|]. split; [exact H3|].
exact (QpvH.usp_fit JOB6PH sp rdraw argv envp uid hw Hfit).
Qed.

Lemma ed_argv0 : edenot E EARGV0 = Z_to_bv 64 STR0.
Proof.
rewrite EARGV0_eq, (edenot_ev_agree NX0 E EI e_str0 Senv eq_refl eq_refl).
pose proof (QpvH.u_e_str0 JOB6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U. unfold uE in U.
apply bv_eq. rewrite U. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
pose proof (u64_range (edenot EI e_str0)) as RG. rewrite U in RG. rewrite Z.mod_small by lia. reflexivity.
Qed.
#[local] Notation L0 := (Z.of_nat (length (nth 0 argv []))).
Lemma ed_argv1 : 2 <= argc -> edenot E EARGV1 = Z_to_bv 64 (STR0 + L0 + 1).
Proof.
intros H2. rewrite EARGV1_eq, (edenot_ev_agree NX0 E EI e_argv1w Senv eq_refl eq_refl).
pose proof (QpvH.u_e_str1 JOB6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U. unfold uE in U.
destruct (QpvH.uE0 JOB6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
pose proof (u64_range (edenot EI e_str1)) as RG.
unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
destruct (Z.ltb_spec 1 argc) as [_|X]; [|lia]. rewrite Z.mul_1_l, Z.mod_small by lia. rewrite U.
rewrite U in RG. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma arg_checks : cells_check JOB6SEGS (kn_view ch) ESP0 0 DARGC = true /\ cells_check JOB6SEGS (kn_view ch) ESP0 8 DARGV0 = true
/\ cells_check JOB6SEGS (kn_view ch) ESP0 16 DARGV1 = true /\ wr_check (kn_view ch) ESP0 (-8388608) 8388608 = true.
Proof.
pose proof (ARG_CHECKS w ch HCL) as C. unfold arg_pieces_check in C.
apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. tauto.
Qed.

Theorem drv_argv0_cell : QlEo_c1.ro_cells JOB6SEGS m (usp + 8) [QbVh.C8 (Z_to_bv 64 STR0)].
Proof.
destruct arg_checks as (_ & C & _). destruct usp_bounds as (U1 & U2 & U3).
pose proof (check_cells_at JOB6SEGS E m (kn_view ch) KV DARGV0 ESP0 8 [QbVh.C8 (Z_to_bv 64 STR0)] C) as X. cbv zeta in X. rewrite u_esp0 in X.
refine (proj1 (X _ _ _ _)); [lia | cbn; lia | | cbn; tauto].
cbn [sc_match DARGV0]. split; [| exact I]. rewrite ed_argv0. reflexivity.
Qed.
Theorem drv_argv1_cell : 2 <= argc -> QlEo_c1.ro_cells JOB6SEGS m (usp + 16) [QbVh.C8 (Z_to_bv 64 (STR0 + L0 + 1))].
Proof.
intros H2. destruct arg_checks as (_ & _ & C & _). destruct usp_bounds as (U1 & U2 & U3).
pose proof (check_cells_at JOB6SEGS E m (kn_view ch) KV DARGV1 ESP0 16 [QbVh.C8 (Z_to_bv 64 (STR0 + L0 + 1))] C) as X. cbv zeta in X. rewrite u_esp0 in X.
refine (proj1 (X _ _ _ _)); [lia | cbn; lia | | cbn; tauto].
cbn [sc_match DARGV1]. split; [| exact I]. rewrite (ed_argv1 H2). reflexivity.
Qed.

Theorem drv_stk : QWxq_c1.stk JOB6SEGS m (usp - 8388608) usp.
Proof.
destruct arg_checks as (_ & _ & _ & C). destruct usp_bounds as (U1 & U2 & U3).
pose proof (wr_check_sound JOB6SEGS E m (kn_view ch) KV ESP0 (-8388608) 8388608 C ltac:(lia)) as (W0 & W1 & W). rewrite u_esp0 in *.
split; [lia|]. split; [lia|]. intros a Ha. specialize (W (a - (usp + -8388608)) ltac:(lia)).
replace (usp + -8388608 + (a - (usp + -8388608))) with a in W by lia. split; [exact W|].
unfold wview in W. unfold QZDE.mrd. destruct (m (QZDE.wa a)) as [b|] eqn:Em; [exists b; reflexivity|].
exfalso. apply W. rewrite (JOB6SEGS_low (QZDE.wa a)); [reflexivity|].
unfold QZDE.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
unfold QzgH.kLowEnd. lia.
Qed.

#[local] Notation bsb := (build_stack_bytes JOB6PH sp argv envp uid hw rdraw).
#[local] Notation CSS := (cat_struct_size argv envp).
Lemma css_val : Z.of_nat CSS = 8 * argc + 8 * envc + 184.
Proof. unfold cat_struct_size, auxv_size. lia. Qed.

Lemma view_stack : forall x, usp - 8388608 <= x < 2^47 -> m (QZDE.wa x) = FULL (QZDE.wa x).
Proof.
intros x Hx. destruct usp_bounds as (U1 & U2 & U3). unfold view, QQIi.mrestrict, hidden.
rewrite QZDE.wa_unsigned by lia. rewrite (MV4 allowed_base x) by (right; rewrite (MV4 atop_val); lia). reflexivity.
Qed.

Lemma arg_block_byte : forall (i : nat) b, (CSS <= i)%nat -> Z.of_nat i < Z.of_nat (length bsb) - 16 -> nth_error bsb i = Some b ->
m (QZDE.wa (usp + Z.of_nat i)) = Some b.
Proof.
intros i b Hlo Hhi Hn. destruct usp_bounds as (U1 & U2 & U3). pose proof css_val as CV. destruct len_bounds as [LA LE].
destruct (QpvH.W_range JOB6PH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & _).
rewrite view_stack by lia.
rewrite (proj2 (P co_sinv) (QZDE.wa (usp + Z.of_nat i))).
2:{ unfold argH0. rewrite QZDE.wa_unsigned by lia. apply orb_true_iff. right. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite wrap_above_sp by (rewrite QZDE.wa_unsigned by lia; lia).
unfold stack_to_mem. rewrite QZDE.wa_unsigned by lia. unfold entry_stack_image. cbv zeta. rewrite length_app.
replace (usp <=? usp + Z.of_nat i) with true by (symmetry; apply Z.leb_le; lia).
replace (usp + Z.of_nat i - usp) with (Z.of_nat i) by lia.
replace (Z.of_nat i <? Z.of_nat (length bsb + length (entry_slack sp bsb (ed_slack rdraw)))) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite Nat2Z.id. rewrite nth_error_app1 by lia. exact Hn.
Qed.

Lemma arg_block_bytes : forall off n : nat, (CSS <= off)%nat -> Z.of_nat (off + n) <= Z.of_nat (length bsb) - 16 ->
QZDE.bytes_at JOB6SEGS m (usp + Z.of_nat off) (firstn n (skipn off bsb)) /\ length (firstn n (skipn off bsb)) = n.
Proof.
intros off n Hlo Hhi. destruct usp_bounds as (U1 & U2 & U3).
assert (LEN : length (firstn n (skipn off bsb)) = n) by (rewrite length_firstn, length_skipn; lia).
split; [|exact LEN]. split; [lia|]. rewrite LEN. split; [lia|]. intros i Hi.
assert (Hn : nth_error (firstn n (skipn off bsb)) i = nth_error bsb (off + i)).
{ rewrite nth_error_firstn. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_error_skipn. reflexivity. }
rewrite Hn. destruct (nth_error bsb (off + i)) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
unfold QZDE.mrd. replace (usp + Z.of_nat off + Z.of_nat i) with (usp + Z.of_nat (off + i)) by lia.
rewrite (arg_block_byte (off + i) b ltac:(lia) ltac:(lia) Eb). reflexivity.
Qed.

Definition arg_ptr (k : nat) : Z := usp + Z.of_nat (CSS + total_arg_bytes_nat (firstn k argv)).
Theorem arg_string : forall k, (k < length argv)%nat ->
let p := arg_ptr k in let s := nth k argv [] in
QZDE.bytes_at JOB6SEGS m p (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
/\ usp + 24 <= p /\ (p + Z.of_nat (length s) + 1 + 8 <= usp + 2^22 - 4096 /\ (Z.of_nat (length s) < 2^17 /\ p + Z.of_nat (length s) + 1 + 8 <= 2^47))
/\ (exists t, QZDE.bytes_at JOB6SEGS m (p + Z.of_nat (length s) + 1) t /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length t)).
Proof.
intros k Hk p s. destruct usp_bounds as (U1 & U2 & U3). pose proof css_val as CV. destruct len_bounds as [LA LE].
pose proof (QpvH.length_bsb_eq JOB6PH sp rdraw argv envp uid hw) as LB. unfold stack_image_size in LB. cbv zeta in LB.
destruct (QpvH.bsb_ge JOB6PH sp rdraw argv envp uid hw) as [_ M8].
pose proof (total_firstn_succ argv k Hk) as TF. fold s in TF.
pose proof (total_arg_bytes_Z argv) as TA. pose proof (total_arg_bytes_Z envp) as TE.
pose proof (valid_argv_str_len argv k Hva Hk) as SL. fold s in SL.
pose proof (QEiB.Mq0.bsb_bound JOB6PH sp argv envp uid hw rdraw Hva Hve) as BB.
set (off := (CSS + total_arg_bytes_nat (firstn k argv))%nat) in *.
match type of LB with context [((8 - ?l mod 8) mod 8)] => assert (PD : 0 <= (8 - l mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia) end.
assert (IN : Z.of_nat (off + (length s + 1)) <= Z.of_nat (length bsb) - 16) by (unfold off; lia).
destruct (bsb_byte_k JOB6PH sp argv envp k uid hw rdraw Hk) as (pre & post & EQ & LP). fold s in EQ. fold off in LP.
split; [|split; [exact (valid_argv_str_nz argv k Hva Hk)|split; [unfold p, arg_ptr; fold off; unfold off; lia|split; [unfold p, arg_ptr; fold off; lia|]]]].
- destruct (arg_block_bytes off (length s + 1) ltac:(unfold off; lia) IN) as [B _].
replace (firstn (length s + 1) (skipn off bsb)) with (s ++ [Z_to_bv 8 0]) in B; [exact B|].
rewrite EQ, (skipn_app_exact pre _ off LP), (firstn_app_exact (s ++ [Z_to_bv 8 0]) post); [reflexivity|]. rewrite length_app. cbn [length]. lia.
-
set (q := p + Z.of_nat (length s) + 1). set (n := Z.to_nat ((- q) mod 8)).
assert (QN : 0 <= (- q) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (QE : q = usp + Z.of_nat (off + (length s + 1))) by (unfold q, p, arg_ptr; fold off; lia).
assert (Hend : Z.of_nat (off + (length s + 1) + n) <= Z.of_nat (length bsb) - 16).
{
assert (E8 : (usp + (Z.of_nat (length bsb) - 16)) mod 8 = 0).
{ replace (usp + (Z.of_nat (length bsb) - 16)) with (usp + (8 * argc + 8 * envc + 184) + (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184))) by lia.
rewrite Z.add_mod, M8, Z.add_0_r, Z.mod_mod by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
unfold n. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
destruct (arg_block_bytes (off + (length s + 1)) n ltac:(unfold off; lia) Hend) as [B LEN].
exists (firstn n (skipn (off + (length s + 1)) bsb)). split; [rewrite QE; exact B|]. rewrite LEN. unfold n. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma arg_ptr_0 : arg_ptr 0 = STR0.
Proof. unfold arg_ptr. rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat. pose proof css_val. lia. Qed.
Lemma arg_ptr_1 : (2 <= length argv)%nat -> arg_ptr 1 = STR0 + L0 + 1.
Proof.
intros H2. unfold arg_ptr. pose proof css_val as CV. destruct argv as [|a0 r]; [cbn in H2; lia|].
change (firstn 1 (a0 :: r)) with [a0]. cbn [nth]. unfold total_arg_bytes_nat. cbn [fold_right]. lia.
Qed.

Theorem drv_mem : QupI.drvA_mem argv usp m.
Proof.
destruct (MV4 drv_pristine) as [PA _].
refine (QupI.DMA argv usp m (MV4 drv_mem_inv) (proj1 len_bounds) _ _ PA (MV4 drv_tid) (MV4 drv_loc) (MV4 drv_atexit)).
- exists (arg_ptr 0). split; [rewrite arg_ptr_0; exact drv_argv0_cell|].
exact (arg_string 0%nat ltac:(destruct len_bounds; lia)).
- intros H2. exists (arg_ptr 1). split; [rewrite (arg_ptr_1 H2); exact (drv_argv1_cell ltac:(lia))|].
exact (arg_string 1%nat ltac:(lia)).
Qed.

Section Pre.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Theorem drv_pre : QupI.drvA_pre argv usp (usp - 8388608) m mo.
Proof.
destruct usp_bounds as (U1 & U2 & U3). destruct (MV4 drv_fds) as (F1 & F2 & F3).
constructor.
- split; [exact U2|]. split; lia.
- unfold Q6q3.alloc_ceiling. rewrite HCEIL, (MV4 atop_val). lia.
- exact (proj1 (QWxq_c1.stk_split JOB6SEGS m (usp - 8388608) (usp - 48) usp drv_stk ltac:(lia))).
- exact F1.
- exact F2.
- exact F3.
- exact drv_mem.
- exact (proj2 (MV4 drv_pristine)).
Qed.
End Pre.
End DrvPre2.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ4Q.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG64. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5o6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvQl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvQl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn7S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn7S. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qxua.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qxua. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvjf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvjf.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma ARG_CHECKS : forall w ch, HSCLASS_S w ch -> arg_pieces_check (kn_view ch) = true.
Proof. intros [|] ch [-> | ->]; [exact ARGPIECES_HS2sA_1_ok | exact ARGPIECES_HS2sA_2_ok | exact ARGPIECES_HS2sB_3_ok | exact ARGPIECES_HS2sB_4_ok]. Qed.

Lemma ESP0_eq : ESP0 = e_sp0.  Proof. reflexivity. Qed.
Lemma EARGV0_eq : EARGV0 = e_str0.  Proof. reflexivity. Qed.
Lemma EARGV1_eq : EARGV1 = e_argv1w.  Proof. reflexivity. Qed.

Lemma total_firstn_succ : forall (av : list (list byte)) k, (k < length av)%nat ->
(total_arg_bytes_nat (firstn k av) + length (nth k av []) + 1 <= total_arg_bytes_nat av)%nat.
Proof.
induction av as [|a r IH]; intros k Hk; [cbn in Hk; lia|]. destruct k as [|k].
- cbn [firstn nth total_arg_bytes_nat fold_right]. unfold total_arg_bytes_nat. cbn [fold_right]. lia.
- cbn [firstn nth]. unfold total_arg_bytes_nat in *. cbn [fold_right]. cbn [length] in Hk. specialize (IH k ltac:(lia)). lia.
Qed.

Section DrvPre2.
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
#[local] Notation STR0 := (usp + 8 * argc + 8 * envc + 184).

Lemma Senv : forall n, (n < NX0)%nat -> ev E n = ev EI n.
Proof. exact (proj1 (P co_sinv)). Qed.
Lemma u_esp0 : bv_unsigned (edenot E ESP0) = usp.
Proof. rewrite ESP0_eq, (MA main_sp0). reflexivity. Qed.

Lemma len_bounds : 1 <= argc <= 1024 /\ 0 <= envc <= 256.
Proof. destruct Hva as [A _]. destruct Hve as [B _]. lia. Qed.
Lemma usp_bounds : 0x7fff80000000 <= usp /\ usp mod 16 = 0 /\ usp + Z.of_nat (length (build_stack_bytes JO6PH sp argv envp uid hw rdraw)) <= 2^47.
Proof.
destruct Hsp as (H1 & _ & H3). unfold sp_window_lo in H1. split; [exact H1|]. split; [exact H3|].
exact (QpvH.usp_fit JO6PH sp rdraw argv envp uid hw Hfit).
Qed.

Lemma ed_argv0 : edenot E EARGV0 = Z_to_bv 64 STR0.
Proof.
rewrite EARGV0_eq, (edenot_ev_agree NX0 E EI e_str0 Senv eq_refl eq_refl).
pose proof (QpvH.u_e_str0 JO6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U. unfold uE in U.
apply bv_eq. rewrite U. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
pose proof (u64_range (edenot EI e_str0)) as RG. rewrite U in RG. rewrite Z.mod_small by lia. reflexivity.
Qed.
#[local] Notation L0 := (Z.of_nat (length (nth 0 argv []))).
Lemma ed_argv1 : 2 <= argc -> edenot E EARGV1 = Z_to_bv 64 (STR0 + L0 + 1).
Proof.
intros H2. rewrite EARGV1_eq, (edenot_ev_agree NX0 E EI e_argv1w Senv eq_refl eq_refl).
pose proof (QpvH.u_e_str1 JO6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U. unfold uE in U.
destruct (QpvH.uE0 JO6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
pose proof (u64_range (edenot EI e_str1)) as RG.
unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
destruct (Z.ltb_spec 1 argc) as [_|X]; [|lia]. rewrite Z.mul_1_l, Z.mod_small by lia. rewrite U.
rewrite U in RG. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma arg_checks : cells_check JO6SEGS (kn_view ch) ESP0 0 DARGC = true /\ cells_check JO6SEGS (kn_view ch) ESP0 8 DARGV0 = true
/\ cells_check JO6SEGS (kn_view ch) ESP0 16 DARGV1 = true /\ wr_check (kn_view ch) ESP0 (-8388608) 8388608 = true.
Proof.
pose proof (ARG_CHECKS w ch HCL) as C. unfold arg_pieces_check in C.
apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. tauto.
Qed.

Theorem drv_argv0_cell : QlEo_c1.ro_cells JO6SEGS m (usp + 8) [QbVh.C8 (Z_to_bv 64 STR0)].
Proof.
destruct arg_checks as (_ & C & _). destruct usp_bounds as (U1 & U2 & U3).
pose proof (check_cells_at JO6SEGS E m (kn_view ch) KV DARGV0 ESP0 8 [QbVh.C8 (Z_to_bv 64 STR0)] C) as X. cbv zeta in X. rewrite u_esp0 in X.
refine (proj1 (X _ _ _ _)); [lia | cbn; lia | | cbn; tauto].
cbn [sc_match DARGV0]. split; [| exact I]. rewrite ed_argv0. reflexivity.
Qed.
Theorem drv_argv1_cell : 2 <= argc -> QlEo_c1.ro_cells JO6SEGS m (usp + 16) [QbVh.C8 (Z_to_bv 64 (STR0 + L0 + 1))].
Proof.
intros H2. destruct arg_checks as (_ & _ & C & _). destruct usp_bounds as (U1 & U2 & U3).
pose proof (check_cells_at JO6SEGS E m (kn_view ch) KV DARGV1 ESP0 16 [QbVh.C8 (Z_to_bv 64 (STR0 + L0 + 1))] C) as X. cbv zeta in X. rewrite u_esp0 in X.
refine (proj1 (X _ _ _ _)); [lia | cbn; lia | | cbn; tauto].
cbn [sc_match DARGV1]. split; [| exact I]. rewrite (ed_argv1 H2). reflexivity.
Qed.

Theorem drv_stk : QWxq_c1.stk JO6SEGS m (usp - 8388608) usp.
Proof.
destruct arg_checks as (_ & _ & _ & C). destruct usp_bounds as (U1 & U2 & U3).
pose proof (wr_check_sound JO6SEGS E m (kn_view ch) KV ESP0 (-8388608) 8388608 C ltac:(lia)) as (W0 & W1 & W). rewrite u_esp0 in *.
split; [lia|]. split; [lia|]. intros a Ha. specialize (W (a - (usp + -8388608)) ltac:(lia)).
replace (usp + -8388608 + (a - (usp + -8388608))) with a in W by lia. split; [exact W|].
unfold wview in W. unfold QZDE.mrd. destruct (m (QZDE.wa a)) as [b|] eqn:Em; [exists b; reflexivity|].
exfalso. apply W. rewrite (JO6SEGS_low (QZDE.wa a)); [reflexivity|].
unfold QZDE.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
unfold QzgH.kLowEnd. lia.
Qed.

#[local] Notation bsb := (build_stack_bytes JO6PH sp argv envp uid hw rdraw).
#[local] Notation CSS := (cat_struct_size argv envp).
Lemma css_val : Z.of_nat CSS = 8 * argc + 8 * envc + 184.
Proof. unfold cat_struct_size, auxv_size. lia. Qed.

Lemma view_stack : forall x, usp - 8388608 <= x < 2^47 -> m (QZDE.wa x) = FULL (QZDE.wa x).
Proof.
intros x Hx. destruct usp_bounds as (U1 & U2 & U3). unfold view, QQIi.mrestrict, hidden.
rewrite QZDE.wa_unsigned by lia. rewrite (MV4 allowed_base x) by (right; rewrite (MV4 atop_val); lia). reflexivity.
Qed.

Lemma arg_block_byte : forall (i : nat) b, (CSS <= i)%nat -> Z.of_nat i < Z.of_nat (length bsb) - 16 -> nth_error bsb i = Some b ->
m (QZDE.wa (usp + Z.of_nat i)) = Some b.
Proof.
intros i b Hlo Hhi Hn. destruct usp_bounds as (U1 & U2 & U3). pose proof css_val as CV. destruct len_bounds as [LA LE].
destruct (QpvH.W_range JO6PH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & _).
rewrite view_stack by lia.
rewrite (proj2 (P co_sinv) (QZDE.wa (usp + Z.of_nat i))).
2:{ unfold argH0. rewrite QZDE.wa_unsigned by lia. apply orb_true_iff. right. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite wrap_above_sp by (rewrite QZDE.wa_unsigned by lia; lia).
unfold stack_to_mem. rewrite QZDE.wa_unsigned by lia. unfold entry_stack_image. cbv zeta. rewrite length_app.
replace (usp <=? usp + Z.of_nat i) with true by (symmetry; apply Z.leb_le; lia).
replace (usp + Z.of_nat i - usp) with (Z.of_nat i) by lia.
replace (Z.of_nat i <? Z.of_nat (length bsb + length (entry_slack sp bsb (ed_slack rdraw)))) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite Nat2Z.id. rewrite nth_error_app1 by lia. exact Hn.
Qed.

Lemma arg_block_bytes : forall off n : nat, (CSS <= off)%nat -> Z.of_nat (off + n) <= Z.of_nat (length bsb) - 16 ->
QZDE.bytes_at JO6SEGS m (usp + Z.of_nat off) (firstn n (skipn off bsb)) /\ length (firstn n (skipn off bsb)) = n.
Proof.
intros off n Hlo Hhi. destruct usp_bounds as (U1 & U2 & U3).
assert (LEN : length (firstn n (skipn off bsb)) = n) by (rewrite length_firstn, length_skipn; lia).
split; [|exact LEN]. split; [lia|]. rewrite LEN. split; [lia|]. intros i Hi.
assert (Hn : nth_error (firstn n (skipn off bsb)) i = nth_error bsb (off + i)).
{ rewrite nth_error_firstn. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_error_skipn. reflexivity. }
rewrite Hn. destruct (nth_error bsb (off + i)) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
unfold QZDE.mrd. replace (usp + Z.of_nat off + Z.of_nat i) with (usp + Z.of_nat (off + i)) by lia.
rewrite (arg_block_byte (off + i) b ltac:(lia) ltac:(lia) Eb). reflexivity.
Qed.

Definition arg_ptr (k : nat) : Z := usp + Z.of_nat (CSS + total_arg_bytes_nat (firstn k argv)).
Theorem arg_string : forall k, (k < length argv)%nat ->
let p := arg_ptr k in let s := nth k argv [] in
QZDE.bytes_at JO6SEGS m p (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
/\ usp + 24 <= p /\ (p + Z.of_nat (length s) + 1 + 8 <= usp + 2^22 - 4096 /\ (Z.of_nat (length s) < 2^17 /\ p + Z.of_nat (length s) + 1 + 8 <= 2^47))
/\ (exists t, QZDE.bytes_at JO6SEGS m (p + Z.of_nat (length s) + 1) t /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length t)).
Proof.
intros k Hk p s. destruct usp_bounds as (U1 & U2 & U3). pose proof css_val as CV. destruct len_bounds as [LA LE].
pose proof (QpvH.length_bsb_eq JO6PH sp rdraw argv envp uid hw) as LB. unfold stack_image_size in LB. cbv zeta in LB.
destruct (QpvH.bsb_ge JO6PH sp rdraw argv envp uid hw) as [_ M8].
pose proof (total_firstn_succ argv k Hk) as TF. fold s in TF.
pose proof (total_arg_bytes_Z argv) as TA. pose proof (total_arg_bytes_Z envp) as TE.
pose proof (valid_argv_str_len argv k Hva Hk) as SL. fold s in SL.
pose proof (QEiB.Mq0.bsb_bound JO6PH sp argv envp uid hw rdraw Hva Hve) as BB.
set (off := (CSS + total_arg_bytes_nat (firstn k argv))%nat) in *.
match type of LB with context [((8 - ?l mod 8) mod 8)] => assert (PD : 0 <= (8 - l mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia) end.
assert (IN : Z.of_nat (off + (length s + 1)) <= Z.of_nat (length bsb) - 16) by (unfold off; lia).
destruct (bsb_byte_k JO6PH sp argv envp k uid hw rdraw Hk) as (pre & post & EQ & LP). fold s in EQ. fold off in LP.
split; [|split; [exact (valid_argv_str_nz argv k Hva Hk)|split; [unfold p, arg_ptr; fold off; unfold off; lia|split; [unfold p, arg_ptr; fold off; lia|]]]].
- destruct (arg_block_bytes off (length s + 1) ltac:(unfold off; lia) IN) as [B _].
replace (firstn (length s + 1) (skipn off bsb)) with (s ++ [Z_to_bv 8 0]) in B; [exact B|].
rewrite EQ, (skipn_app_exact pre _ off LP), (firstn_app_exact (s ++ [Z_to_bv 8 0]) post); [reflexivity|]. rewrite length_app. cbn [length]. lia.
-
set (q := p + Z.of_nat (length s) + 1). set (n := Z.to_nat ((- q) mod 8)).
assert (QN : 0 <= (- q) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (QE : q = usp + Z.of_nat (off + (length s + 1))) by (unfold q, p, arg_ptr; fold off; lia).
assert (Hend : Z.of_nat (off + (length s + 1) + n) <= Z.of_nat (length bsb) - 16).
{
assert (E8 : (usp + (Z.of_nat (length bsb) - 16)) mod 8 = 0).
{ replace (usp + (Z.of_nat (length bsb) - 16)) with (usp + (8 * argc + 8 * envc + 184) + (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184))) by lia.
rewrite Z.add_mod, M8, Z.add_0_r, Z.mod_mod by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
unfold n. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
destruct (arg_block_bytes (off + (length s + 1)) n ltac:(unfold off; lia) Hend) as [B LEN].
exists (firstn n (skipn (off + (length s + 1)) bsb)). split; [rewrite QE; exact B|]. rewrite LEN. unfold n. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma arg_ptr_0 : arg_ptr 0 = STR0.
Proof. unfold arg_ptr. rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat. pose proof css_val. lia. Qed.
Lemma arg_ptr_1 : (2 <= length argv)%nat -> arg_ptr 1 = STR0 + L0 + 1.
Proof.
intros H2. unfold arg_ptr. pose proof css_val as CV. destruct argv as [|a0 r]; [cbn in H2; lia|].
change (firstn 1 (a0 :: r)) with [a0]. cbn [nth]. unfold total_arg_bytes_nat. cbn [fold_right]. lia.
Qed.

Theorem drv_mem : Q2y2.drvA_mem argv usp m.
Proof.
destruct (MV4 drv_pristine) as [PA _].
refine (Q2y2.DMA argv usp m (MV4 drv_mem_inv) (proj1 len_bounds) _ _ PA (MV4 drv_tid) (MV4 drv_loc) (MV4 drv_atexit)).
- exists (arg_ptr 0). split; [rewrite arg_ptr_0; exact drv_argv0_cell|].
exact (arg_string 0%nat ltac:(destruct len_bounds; lia)).
- intros H2. exists (arg_ptr 1). split; [rewrite (arg_ptr_1 H2); exact (drv_argv1_cell ltac:(lia))|].
exact (arg_string 1%nat ltac:(lia)).
Qed.

Section Pre.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Theorem drv_pre : Q2y2.drvA_pre argv usp (usp - 8388608) m mo.
Proof.
destruct usp_bounds as (U1 & U2 & U3). destruct (MV4 drv_fds) as (F1 & F2 & F3).
constructor.
- split; [exact U2|]. split; lia.
- unfold Q6q3.alloc_ceiling. rewrite HCEIL, (MV4 atop_val). lia.
- exact (proj1 (QWxq_c1.stk_split JO6SEGS m (usp - 8388608) (usp - 48) usp drv_stk ltac:(lia))).
- exact F1.
- exact F2.
- exact F3.
- exact drv_mem.
- exact (proj2 (MV4 drv_pristine)).
Qed.
End Pre.
End DrvPre2.
