(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: the sections take apc, mbase, kb, execfn and the other QpvH.inp fields, with the launch premise QpvH.launch_ok; the CONFIG_RSEQ flag of the start-up layer: ARG_CHECKS per value over HSCLASS_R, checked conjunct by conjunct, and the HCLR premise on the driver lemmas, and the argv expressions' variable checks per value; the entry stack layout: the argv strings after the block head and the pad, up to ed_top (cat_string_off); the stack window from the model's stack_window_depth in place of the 8 MiB bound). *)

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

Lemma ARG_CHECKS : forall r w ch, HSCLASS_R r w ch ->
cells_check JOB6SEGS (kn_view ch) ESP0 0 DARGC = true /\
cells_check JOB6SEGS (kn_view ch) ESP0 8 [SCw 8 (e_str0 (rseq_z r))] = true /\
cells_check JOB6SEGS (kn_view ch) ESP0 16 [SCw 8 (e_argv1w (rseq_z r))] = true /\
wr_check (kn_view ch) ESP0 (-6144513) 6144513 = true.
Proof. intros [|] [|] ch [-> | ->]; refine (conj _ (conj _ (conj _ _))); vm_compute; reflexivity. Qed.

Lemma ESP0_eq : ESP0 = e_sp0.  Proof. reflexivity. Qed.

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
#[local] Notation SOFF := (cat_string_off RSEQ sp (ed_top rdraw) argv envp execfn).
#[local] Notation bsb := (entry_stack_image (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) mbase JOB6PH (Z_to_bv 64 (Z.of_N apc)) sp rdraw).

Lemma Senv : forall n, (n < NX0)%nat -> ev E n = ev EI n.
Proof. exact (proj1 (P co_sinv)). Qed.
Lemma u_esp0 : bv_unsigned (edenot E ESP0) = usp.
Proof. rewrite ESP0_eq, (MA main_sp0). reflexivity. Qed.

Lemma len_bounds : 1 <= argc <= 1024 /\ 0 <= envc <= 256.
Proof. destruct Hva as [A _]. destruct Hve as [B _]. lia. Qed.
Lemma usp_bounds : 0x7fff80000000 <= usp /\ usp mod 16 = 0 /\ usp + Z.of_nat (length bsb) <= 2^47.
Proof.
destruct Hsp as (H1 & _ & H3). unfold sp_window_lo in H1. split; [exact H1|]. split; [exact H3|].
qpv QpvH.usp_fit.
Qed.

Lemma ed_argv0 : edenot E (e_str0 RZ) = Z_to_bv 64 STR0.
Proof.
rewrite (edenot_ev_agree NX0 E EI (e_str0 RZ) Senv ltac:(destruct RSEQ; reflexivity) ltac:(destruct RSEQ; reflexivity)).
assert (U : uE EI (e_str0 RZ) = STR0) by qpv QpvH.u_e_str0. unfold uE in U.
apply bv_eq. rewrite U. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
pose proof (u64_range (edenot EI (e_str0 RZ))) as RG. rewrite U in RG. rewrite Z.mod_small by lia. reflexivity.
Qed.
#[local] Notation L0 := (Z.of_nat (length (nth 0 argv []))).
Lemma ed_argv1 : 2 <= argc -> edenot E (e_argv1w RZ) = Z_to_bv 64 (STR0 + L0 + 1).
Proof.
intros H2. rewrite (edenot_ev_agree NX0 E EI (e_argv1w RZ) Senv ltac:(destruct RSEQ; reflexivity) ltac:(destruct RSEQ; reflexivity)).
assert (U : uE EI (e_str1 RZ) = STR0 + L0 + 1) by qpv QpvH.u_e_str1. unfold uE in U.
assert (U0 : uE EI (EVar V_S1) = usp / 32768 /\ uE EI (EVar V_S2) = (usp mod 32768) / 16
/\ uE EI (EVar V_ARGC) = argc /\ uE EI (EVar V_ENVC) = envc /\ uE EI (EVar V_L0) = L0
/\ uE EI (EVar V_W) = W /\ uE EI (EVar V_BRK) = bv_unsigned brk0 / 4096
/\ uE EI (EVar V_G) = Z.of_nat (block_items argv envp mod 2)) by qpv QpvH.uE0.
destruct U0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
pose proof (u64_range (edenot EI (e_str1 RZ))) as RG.
unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
destruct (Z.ltb_spec 1 argc) as [_|X]; [|lia]. rewrite Z.mul_1_l, Z.mod_small by lia. rewrite U.
rewrite U in RG. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. reflexivity.
Qed.

(* the argv cells are those of the run's own CONFIG_RSEQ value: [HCLR] says the state is one of its main-entry states *)
Lemma arg_checks (HCLR : HSCLASS_R RSEQ w ch) : cells_check JOB6SEGS (kn_view ch) ESP0 0 DARGC = true /\
cells_check JOB6SEGS (kn_view ch) ESP0 8 [SCw 8 (e_str0 RZ)] = true /\
cells_check JOB6SEGS (kn_view ch) ESP0 16 [SCw 8 (e_argv1w RZ)] = true /\
wr_check (kn_view ch) ESP0 (-6144513) 6144513 = true.
Proof. exact (ARG_CHECKS RSEQ w ch HCLR). Qed.

Theorem drv_argv0_cell (HCLR : HSCLASS_R RSEQ w ch) : QlEo_c1.ro_cells JOB6SEGS m (usp + 8) [QbVh.C8 (Z_to_bv 64 STR0)].
Proof.
destruct (arg_checks HCLR) as (_ & C & _). destruct usp_bounds as (U1 & U2 & U3).
pose proof (check_cells_at JOB6SEGS E m (kn_view ch) KV [SCw 8 (e_str0 RZ)] ESP0 8 [QbVh.C8 (Z_to_bv 64 STR0)] C) as X. cbv zeta in X. rewrite u_esp0 in X.
refine (proj1 (X _ _ _ _)); [lia | cbn; lia | | cbn; tauto].
cbn [sc_match]. split; [| exact I]. rewrite ed_argv0. reflexivity.
Qed.
Theorem drv_argv1_cell (HCLR : HSCLASS_R RSEQ w ch) : 2 <= argc -> QlEo_c1.ro_cells JOB6SEGS m (usp + 16) [QbVh.C8 (Z_to_bv 64 (STR0 + L0 + 1))].
Proof.
intros H2. destruct (arg_checks HCLR) as (_ & _ & C & _). destruct usp_bounds as (U1 & U2 & U3).
pose proof (check_cells_at JOB6SEGS E m (kn_view ch) KV [SCw 8 (e_argv1w RZ)] ESP0 16 [QbVh.C8 (Z_to_bv 64 (STR0 + L0 + 1))] C) as X. cbv zeta in X. rewrite u_esp0 in X.
refine (proj1 (X _ _ _ _)); [lia | cbn; lia | | cbn; tauto].
cbn [sc_match]. split; [| exact I]. rewrite (ed_argv1 H2). reflexivity.
Qed.

Theorem drv_stk (HCLR : HSCLASS_R RSEQ w ch) : QWxq_c1.stk JOB6SEGS m (usp - 6144513) usp.
Proof.
destruct (arg_checks HCLR) as (_ & _ & _ & C). destruct usp_bounds as (U1 & U2 & U3).
pose proof (wr_check_sound JOB6SEGS E m (kn_view ch) KV ESP0 (-6144513) 6144513 C ltac:(lia)) as (W0 & W1 & W). rewrite u_esp0 in *.
split; [lia|]. split; [lia|]. intros a Ha. specialize (W (a - (usp + -6144513)) ltac:(lia)).
replace (usp + -6144513 + (a - (usp + -6144513))) with a in W by lia. split; [exact W|].
unfold wview in W. unfold QZDE.mrd. destruct (m (QZDE.wa a)) as [b|] eqn:Em; [exists b; reflexivity|].
exfalso. apply W. rewrite (JOB6SEGS_low (QZDE.wa a)); [reflexivity|].
unfold QZDE.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
unfold QzgH.kLowEnd. lia.
Qed.

Lemma soff_val : Z.of_nat SOFF = CHEAD + W.
Proof. unfold cat_string_off. apply Nat2Z.inj_add. Qed.

Lemma view_stack : forall x, usp - 6144513 <= x < 2^47 -> m (QZDE.wa x) = FULL (QZDE.wa x).
Proof.
intros x Hx. destruct usp_bounds as (U1 & U2 & U3). unfold view, QQIi.mrestrict, hidden.
rewrite QZDE.wa_unsigned by lia. rewrite (MV4 allowed_base x) by (right; rewrite (MV4 atop_val); lia). reflexivity.
Qed.

Lemma arg_block_byte : forall (i : nat) b, (SOFF <= i)%nat -> Z.of_nat i < Z.of_nat (length bsb) -> nth_error bsb i = Some b ->
m (QZDE.wa (usp + Z.of_nat i)) = Some b.
Proof.
intros i b Hlo Hhi Hn. destruct usp_bounds as (U1 & U2 & U3). pose proof soff_val as CV. destruct len_bounds as [LA LE].
assert (LB : Z.of_nat (length bsb) = stack_image_size sp (ed_top rdraw)) by qpv QpvH.length_bsb_eq.
unfold stack_image_size in LB.
rewrite view_stack by lia.
rewrite (proj2 (P co_sinv) (QZDE.wa (usp + Z.of_nat i))).
2:{ unfold argH0. rewrite QZDE.wa_unsigned by lia. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite wrap_above_sp by (rewrite QZDE.wa_unsigned by lia; lia).
unfold stack_to_mem. rewrite QZDE.wa_unsigned by lia.
replace (usp <=? usp + Z.of_nat i) with true by (symmetry; apply Z.leb_le; lia).
replace (usp + Z.of_nat i - usp) with (Z.of_nat i) by lia.
replace (Z.of_nat i <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite Nat2Z.id. exact Hn.
Qed.

Lemma arg_block_bytes : forall off n : nat, (SOFF <= off)%nat -> Z.of_nat (off + n) <= Z.of_nat (length bsb) ->
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

Definition arg_ptr (k : nat) : Z := usp + Z.of_nat (SOFF + total_arg_bytes_nat (firstn k argv)).
Theorem arg_string : forall k, (k < length argv)%nat ->
let p := arg_ptr k in let s := nth k argv [] in
QZDE.bytes_at JOB6SEGS m p (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
/\ usp + 24 <= p /\ (p + Z.of_nat (length s) + 1 + 8 <= usp + 2^22 - 4096 /\ (Z.of_nat (length s) < 2^17 /\ p + Z.of_nat (length s) + 1 + 8 <= 2^47))
/\ (exists t, QZDE.bytes_at JOB6SEGS m (p + Z.of_nat (length s) + 1) t /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length t)).
Proof.
intros k Hk p s. destruct usp_bounds as (U1 & U2 & U3). pose proof soff_val as CV. destruct len_bounds as [LA LE].
assert (LB : Z.of_nat (length bsb) = CHEAD + W + Z.of_nat (launch_string_bytes argv envp execfn) + 8) by qpv QpvH.length_bsb_sum.
assert (BB : Z.of_nat (length bsb) <= 2101782) by qpv QpvH.bsb_len_hi.
pose proof (total_firstn_succ argv k Hk) as TF. fold s in TF.
pose proof (total_arg_bytes_Z argv) as TA. pose proof (total_arg_bytes_Z envp) as TE.
pose proof (valid_argv_str_len argv k Hva Hk) as SL. fold s in SL.
pose proof (launch_string_bytes_ge argv envp execfn) as LSG. pose proof (block_head_size_bounds RSEQ argv envp) as HCH.
set (off := (SOFF + total_arg_bytes_nat (firstn k argv))%nat) in *.
assert (IN : Z.of_nat (off + (length s + 1)) <= Z.of_nat (length bsb)) by (unfold off; lia).
assert (END : Z.of_nat (off + (length s + 1 + 8)) <= Z.of_nat (length bsb)) by (unfold off; lia).
destruct (bsb_byte_k (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) mbase JOB6PH (Z_to_bv 64 (Z.of_N apc)) sp rdraw k Hk) as (pre & post & EQ & LP). fold s in EQ. fold off in LP.
split; [|split; [exact (valid_argv_str_nz argv k Hva Hk)|split; [unfold p, arg_ptr; fold off; unfold off; lia|split; [unfold p, arg_ptr; fold off; lia|]]]].
- destruct (arg_block_bytes off (length s + 1) ltac:(unfold off; lia) IN) as [B _].
replace (firstn (length s + 1) (skipn off bsb)) with (s ++ [Z_to_bv 8 0]) in B; [exact B|].
rewrite EQ, (skipn_app_exact pre _ off LP), (firstn_app_exact (s ++ [Z_to_bv 8 0]) post); [reflexivity|]. rewrite length_app. cbn [length]. lia.
-
set (q := p + Z.of_nat (length s) + 1). set (n := Z.to_nat ((- q) mod 8)).
assert (QN : 0 <= (- q) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (QE : q = usp + Z.of_nat (off + (length s + 1))) by (unfold q, p, arg_ptr; fold off; lia).
assert (Hend : Z.of_nat (off + (length s + 1) + n) <= Z.of_nat (length bsb)).
{ unfold n. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
destruct (arg_block_bytes (off + (length s + 1)) n ltac:(unfold off; lia) Hend) as [B LEN].
exists (firstn n (skipn (off + (length s + 1)) bsb)). split; [rewrite QE; exact B|]. rewrite LEN. unfold n. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma arg_ptr_0 : arg_ptr 0 = STR0.
Proof. unfold arg_ptr. rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat. pose proof soff_val. lia. Qed.
Lemma arg_ptr_1 : (2 <= length argv)%nat -> arg_ptr 1 = STR0 + L0 + 1.
Proof.
intros H2. unfold arg_ptr. pose proof soff_val as CV. destruct argv as [|a0 r]; [cbn in H2; lia|].
change (firstn 1 (a0 :: r)) with [a0]. cbn [nth]. unfold total_arg_bytes_nat. cbn [fold_right]. lia.
Qed.

Theorem drv_mem (HCLR : HSCLASS_R RSEQ w ch) : QupI.drvA_mem argv usp m.
Proof.
destruct (MV4 drv_pristine) as [PA _].
refine (QupI.DMA argv usp m (MV4 drv_mem_inv) (proj1 len_bounds) _ _ PA (MV4 drv_tid) (MV4 drv_loc) (MV4 drv_atexit)).
- exists (arg_ptr 0). split; [rewrite arg_ptr_0; exact (drv_argv0_cell HCLR)|].
exact (arg_string 0%nat ltac:(destruct len_bounds; lia)).
- intros H2. exists (arg_ptr 1). split; [rewrite (arg_ptr_1 H2); exact (drv_argv1_cell HCLR ltac:(lia))|].
exact (arg_string 1%nat ltac:(lia)).
Qed.

Section Pre.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Theorem drv_pre (HCLR : HSCLASS_R RSEQ w ch) : QupI.drvA_pre argv usp (usp - 6144513) m mo.
Proof.
destruct usp_bounds as (U1 & U2 & U3). destruct (MV4 drv_fds) as (F1 & F2 & F3).
constructor.
- split; [exact U2|]. split; lia.
- unfold Q6q3.alloc_ceiling. rewrite HCEIL, (MV4 atop_val). lia.
- exact (proj1 (QWxq_c1.stk_split JOB6SEGS m (usp - 6144513) (usp - 48) usp (drv_stk HCLR) ltac:(lia))).
- exact F1.
- exact F2.
- exact F3.
- exact (drv_mem HCLR).
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

Lemma ARG_CHECKS : forall r w ch, HSCLASS_R r w ch ->
cells_check JO6SEGS (kn_view ch) ESP0 0 DARGC = true /\
cells_check JO6SEGS (kn_view ch) ESP0 8 [SCw 8 (e_str0 (rseq_z r))] = true /\
cells_check JO6SEGS (kn_view ch) ESP0 16 [SCw 8 (e_argv1w (rseq_z r))] = true /\
wr_check (kn_view ch) ESP0 (-6144513) 6144513 = true.
Proof. intros [|] [|] ch [-> | ->]; refine (conj _ (conj _ (conj _ _))); vm_compute; reflexivity. Qed.

Lemma ESP0_eq : ESP0 = e_sp0.  Proof. reflexivity. Qed.

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
#[local] Notation SOFF := (cat_string_off RSEQ sp (ed_top rdraw) argv envp execfn).
#[local] Notation bsb := (entry_stack_image (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) mbase JO6PH (Z_to_bv 64 (Z.of_N apc)) sp rdraw).

Lemma Senv : forall n, (n < NX0)%nat -> ev E n = ev EI n.
Proof. exact (proj1 (P co_sinv)). Qed.
Lemma u_esp0 : bv_unsigned (edenot E ESP0) = usp.
Proof. rewrite ESP0_eq, (MA main_sp0). reflexivity. Qed.

Lemma len_bounds : 1 <= argc <= 1024 /\ 0 <= envc <= 256.
Proof. destruct Hva as [A _]. destruct Hve as [B _]. lia. Qed.
Lemma usp_bounds : 0x7fff80000000 <= usp /\ usp mod 16 = 0 /\ usp + Z.of_nat (length bsb) <= 2^47.
Proof.
destruct Hsp as (H1 & _ & H3). unfold sp_window_lo in H1. split; [exact H1|]. split; [exact H3|].
qpv QpvH.usp_fit.
Qed.

Lemma ed_argv0 : edenot E (e_str0 RZ) = Z_to_bv 64 STR0.
Proof.
rewrite (edenot_ev_agree NX0 E EI (e_str0 RZ) Senv ltac:(destruct RSEQ; reflexivity) ltac:(destruct RSEQ; reflexivity)).
assert (U : uE EI (e_str0 RZ) = STR0) by qpv QpvH.u_e_str0. unfold uE in U.
apply bv_eq. rewrite U. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
pose proof (u64_range (edenot EI (e_str0 RZ))) as RG. rewrite U in RG. rewrite Z.mod_small by lia. reflexivity.
Qed.
#[local] Notation L0 := (Z.of_nat (length (nth 0 argv []))).
Lemma ed_argv1 : 2 <= argc -> edenot E (e_argv1w RZ) = Z_to_bv 64 (STR0 + L0 + 1).
Proof.
intros H2. rewrite (edenot_ev_agree NX0 E EI (e_argv1w RZ) Senv ltac:(destruct RSEQ; reflexivity) ltac:(destruct RSEQ; reflexivity)).
assert (U : uE EI (e_str1 RZ) = STR0 + L0 + 1) by qpv QpvH.u_e_str1. unfold uE in U.
assert (U0 : uE EI (EVar V_S1) = usp / 32768 /\ uE EI (EVar V_S2) = (usp mod 32768) / 16
/\ uE EI (EVar V_ARGC) = argc /\ uE EI (EVar V_ENVC) = envc /\ uE EI (EVar V_L0) = L0
/\ uE EI (EVar V_W) = W /\ uE EI (EVar V_BRK) = bv_unsigned brk0 / 4096
/\ uE EI (EVar V_G) = Z.of_nat (block_items argv envp mod 2)) by qpv QpvH.uE0.
destruct U0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
pose proof (u64_range (edenot EI (e_str1 RZ))) as RG.
unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
destruct (Z.ltb_spec 1 argc) as [_|X]; [|lia]. rewrite Z.mul_1_l, Z.mod_small by lia. rewrite U.
rewrite U in RG. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. reflexivity.
Qed.

(* the argv cells are those of the run's own CONFIG_RSEQ value: [HCLR] says the state is one of its main-entry states *)
Lemma arg_checks (HCLR : HSCLASS_R RSEQ w ch) : cells_check JO6SEGS (kn_view ch) ESP0 0 DARGC = true /\
cells_check JO6SEGS (kn_view ch) ESP0 8 [SCw 8 (e_str0 RZ)] = true /\
cells_check JO6SEGS (kn_view ch) ESP0 16 [SCw 8 (e_argv1w RZ)] = true /\
wr_check (kn_view ch) ESP0 (-6144513) 6144513 = true.
Proof. exact (ARG_CHECKS RSEQ w ch HCLR). Qed.

Theorem drv_argv0_cell (HCLR : HSCLASS_R RSEQ w ch) : QlEo_c1.ro_cells JO6SEGS m (usp + 8) [QbVh.C8 (Z_to_bv 64 STR0)].
Proof.
destruct (arg_checks HCLR) as (_ & C & _). destruct usp_bounds as (U1 & U2 & U3).
pose proof (check_cells_at JO6SEGS E m (kn_view ch) KV [SCw 8 (e_str0 RZ)] ESP0 8 [QbVh.C8 (Z_to_bv 64 STR0)] C) as X. cbv zeta in X. rewrite u_esp0 in X.
refine (proj1 (X _ _ _ _)); [lia | cbn; lia | | cbn; tauto].
cbn [sc_match]. split; [| exact I]. rewrite ed_argv0. reflexivity.
Qed.
Theorem drv_argv1_cell (HCLR : HSCLASS_R RSEQ w ch) : 2 <= argc -> QlEo_c1.ro_cells JO6SEGS m (usp + 16) [QbVh.C8 (Z_to_bv 64 (STR0 + L0 + 1))].
Proof.
intros H2. destruct (arg_checks HCLR) as (_ & _ & C & _). destruct usp_bounds as (U1 & U2 & U3).
pose proof (check_cells_at JO6SEGS E m (kn_view ch) KV [SCw 8 (e_argv1w RZ)] ESP0 16 [QbVh.C8 (Z_to_bv 64 (STR0 + L0 + 1))] C) as X. cbv zeta in X. rewrite u_esp0 in X.
refine (proj1 (X _ _ _ _)); [lia | cbn; lia | | cbn; tauto].
cbn [sc_match]. split; [| exact I]. rewrite (ed_argv1 H2). reflexivity.
Qed.

Theorem drv_stk (HCLR : HSCLASS_R RSEQ w ch) : QWxq_c1.stk JO6SEGS m (usp - 6144513) usp.
Proof.
destruct (arg_checks HCLR) as (_ & _ & _ & C). destruct usp_bounds as (U1 & U2 & U3).
pose proof (wr_check_sound JO6SEGS E m (kn_view ch) KV ESP0 (-6144513) 6144513 C ltac:(lia)) as (W0 & W1 & W). rewrite u_esp0 in *.
split; [lia|]. split; [lia|]. intros a Ha. specialize (W (a - (usp + -6144513)) ltac:(lia)).
replace (usp + -6144513 + (a - (usp + -6144513))) with a in W by lia. split; [exact W|].
unfold wview in W. unfold QZDE.mrd. destruct (m (QZDE.wa a)) as [b|] eqn:Em; [exists b; reflexivity|].
exfalso. apply W. rewrite (JO6SEGS_low (QZDE.wa a)); [reflexivity|].
unfold QZDE.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
unfold QzgH.kLowEnd. lia.
Qed.

Lemma soff_val : Z.of_nat SOFF = CHEAD + W.
Proof. unfold cat_string_off. apply Nat2Z.inj_add. Qed.

Lemma view_stack : forall x, usp - 6144513 <= x < 2^47 -> m (QZDE.wa x) = FULL (QZDE.wa x).
Proof.
intros x Hx. destruct usp_bounds as (U1 & U2 & U3). unfold view, QQIi.mrestrict, hidden.
rewrite QZDE.wa_unsigned by lia. rewrite (MV4 allowed_base x) by (right; rewrite (MV4 atop_val); lia). reflexivity.
Qed.

Lemma arg_block_byte : forall (i : nat) b, (SOFF <= i)%nat -> Z.of_nat i < Z.of_nat (length bsb) -> nth_error bsb i = Some b ->
m (QZDE.wa (usp + Z.of_nat i)) = Some b.
Proof.
intros i b Hlo Hhi Hn. destruct usp_bounds as (U1 & U2 & U3). pose proof soff_val as CV. destruct len_bounds as [LA LE].
assert (LB : Z.of_nat (length bsb) = stack_image_size sp (ed_top rdraw)) by qpv QpvH.length_bsb_eq.
unfold stack_image_size in LB.
rewrite view_stack by lia.
rewrite (proj2 (P co_sinv) (QZDE.wa (usp + Z.of_nat i))).
2:{ unfold argH0. rewrite QZDE.wa_unsigned by lia. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite wrap_above_sp by (rewrite QZDE.wa_unsigned by lia; lia).
unfold stack_to_mem. rewrite QZDE.wa_unsigned by lia.
replace (usp <=? usp + Z.of_nat i) with true by (symmetry; apply Z.leb_le; lia).
replace (usp + Z.of_nat i - usp) with (Z.of_nat i) by lia.
replace (Z.of_nat i <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite Nat2Z.id. exact Hn.
Qed.

Lemma arg_block_bytes : forall off n : nat, (SOFF <= off)%nat -> Z.of_nat (off + n) <= Z.of_nat (length bsb) ->
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

Definition arg_ptr (k : nat) : Z := usp + Z.of_nat (SOFF + total_arg_bytes_nat (firstn k argv)).
Theorem arg_string : forall k, (k < length argv)%nat ->
let p := arg_ptr k in let s := nth k argv [] in
QZDE.bytes_at JO6SEGS m p (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
/\ usp + 24 <= p /\ (p + Z.of_nat (length s) + 1 + 8 <= usp + 2^22 - 4096 /\ (Z.of_nat (length s) < 2^17 /\ p + Z.of_nat (length s) + 1 + 8 <= 2^47))
/\ (exists t, QZDE.bytes_at JO6SEGS m (p + Z.of_nat (length s) + 1) t /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length t)).
Proof.
intros k Hk p s. destruct usp_bounds as (U1 & U2 & U3). pose proof soff_val as CV. destruct len_bounds as [LA LE].
assert (LB : Z.of_nat (length bsb) = CHEAD + W + Z.of_nat (launch_string_bytes argv envp execfn) + 8) by qpv QpvH.length_bsb_sum.
assert (BB : Z.of_nat (length bsb) <= 2101782) by qpv QpvH.bsb_len_hi.
pose proof (total_firstn_succ argv k Hk) as TF. fold s in TF.
pose proof (total_arg_bytes_Z argv) as TA. pose proof (total_arg_bytes_Z envp) as TE.
pose proof (valid_argv_str_len argv k Hva Hk) as SL. fold s in SL.
pose proof (launch_string_bytes_ge argv envp execfn) as LSG. pose proof (block_head_size_bounds RSEQ argv envp) as HCH.
set (off := (SOFF + total_arg_bytes_nat (firstn k argv))%nat) in *.
assert (IN : Z.of_nat (off + (length s + 1)) <= Z.of_nat (length bsb)) by (unfold off; lia).
assert (END : Z.of_nat (off + (length s + 1 + 8)) <= Z.of_nat (length bsb)) by (unfold off; lia).
destruct (bsb_byte_k (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) mbase JO6PH (Z_to_bv 64 (Z.of_N apc)) sp rdraw k Hk) as (pre & post & EQ & LP). fold s in EQ. fold off in LP.
split; [|split; [exact (valid_argv_str_nz argv k Hva Hk)|split; [unfold p, arg_ptr; fold off; unfold off; lia|split; [unfold p, arg_ptr; fold off; lia|]]]].
- destruct (arg_block_bytes off (length s + 1) ltac:(unfold off; lia) IN) as [B _].
replace (firstn (length s + 1) (skipn off bsb)) with (s ++ [Z_to_bv 8 0]) in B; [exact B|].
rewrite EQ, (skipn_app_exact pre _ off LP), (firstn_app_exact (s ++ [Z_to_bv 8 0]) post); [reflexivity|]. rewrite length_app. cbn [length]. lia.
-
set (q := p + Z.of_nat (length s) + 1). set (n := Z.to_nat ((- q) mod 8)).
assert (QN : 0 <= (- q) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (QE : q = usp + Z.of_nat (off + (length s + 1))) by (unfold q, p, arg_ptr; fold off; lia).
assert (Hend : Z.of_nat (off + (length s + 1) + n) <= Z.of_nat (length bsb)).
{ unfold n. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
destruct (arg_block_bytes (off + (length s + 1)) n ltac:(unfold off; lia) Hend) as [B LEN].
exists (firstn n (skipn (off + (length s + 1)) bsb)). split; [rewrite QE; exact B|]. rewrite LEN. unfold n. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma arg_ptr_0 : arg_ptr 0 = STR0.
Proof. unfold arg_ptr. rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat. pose proof soff_val. lia. Qed.
Lemma arg_ptr_1 : (2 <= length argv)%nat -> arg_ptr 1 = STR0 + L0 + 1.
Proof.
intros H2. unfold arg_ptr. pose proof soff_val as CV. destruct argv as [|a0 r]; [cbn in H2; lia|].
change (firstn 1 (a0 :: r)) with [a0]. cbn [nth]. unfold total_arg_bytes_nat. cbn [fold_right]. lia.
Qed.

Theorem drv_mem (HCLR : HSCLASS_R RSEQ w ch) : Q2y2.drvA_mem argv usp m.
Proof.
destruct (MV4 drv_pristine) as [PA _].
refine (Q2y2.DMA argv usp m (MV4 drv_mem_inv) (proj1 len_bounds) _ _ PA (MV4 drv_tid) (MV4 drv_loc) (MV4 drv_atexit)).
- exists (arg_ptr 0). split; [rewrite arg_ptr_0; exact (drv_argv0_cell HCLR)|].
exact (arg_string 0%nat ltac:(destruct len_bounds; lia)).
- intros H2. exists (arg_ptr 1). split; [rewrite (arg_ptr_1 H2); exact (drv_argv1_cell HCLR ltac:(lia))|].
exact (arg_string 1%nat ltac:(lia)).
Qed.

Section Pre.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Theorem drv_pre (HCLR : HSCLASS_R RSEQ w ch) : Q2y2.drvA_pre argv usp (usp - 6144513) m mo.
Proof.
destruct usp_bounds as (U1 & U2 & U3). destruct (MV4 drv_fds) as (F1 & F2 & F3).
constructor.
- split; [exact U2|]. split; lia.
- unfold Q6q3.alloc_ceiling. rewrite HCEIL, (MV4 atop_val). lia.
- exact (proj1 (QWxq_c1.stk_split JO6SEGS m (usp - 6144513) (usp - 48) usp (drv_stk HCLR) ltac:(lia))).
- exact F1.
- exact F2.
- exact F3.
- exact (drv_mem HCLR).
- exact (proj2 (MV4 drv_pristine)).
Qed.
End Pre.
End DrvPre2.
