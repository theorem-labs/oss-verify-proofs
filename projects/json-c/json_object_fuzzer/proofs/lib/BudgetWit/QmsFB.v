(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QmsF.v: section Usage (ref_usage and ref_usage_w), over BudgetWit.QRjHB.realizes. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: main_entry over the launch's input, mmap base and entry point; the channel-reader premise a_channel_reader = true for model0; the entry stack layout: argv[0]'s pointer from ed_top and the AT_EXECFN string, and its end bound from main_strN's Sv48 bound in place of the entry_stack_fits arithmetic; valsN_length applied at its section's full argument list; a0s_fits declares Hargc and Hfit, which its case split on av generalizes). *)

From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Plain.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Qnhz Qrxj QRjH Qpox QsV0 QBxa QSjk QMz4 QO3A Q7m0 QSpR QuJV QCPB QH7x QqES Q1oC Q9ox QFeQ Qm90 QWQV QUeZ QJvR QG24 Q9ch QleT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB QleTB.

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqES.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFeQ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1oC.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMOs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMOs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqHD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqHD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFeQ.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdbv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFOH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFOH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWQV.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUeZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUeZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJvR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJvR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG24. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ch.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1oC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG24.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QleT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QleT.Mq2.
Import QRjHB QleTB.Mq2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Section Usage.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av envv : list (list byte).
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable brk : word.
Variable mbase : word.
Variable fs0 : Fs.
Variable stdin0 : InputStream.

Variable lim : Z.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
(* LPS 727298f3: [main_entry] takes the launch's input, the mmap base and the entry point. *)
Variable inp : ProcInput.
Variable entry : word.
Hypothesis ME : main_entry inp mbase entry sp0 av envv tid regs0 mem0.
Hypothesis Hargc : length av <> 2%nat.

Hypothesis Hfit : entry_stack_fits sp0 av envv.
(* LPS 727298f3: the far end of fd 2 has a reader; the launch seeds [State.m_channel_reader] from
   [in_channel_reader], which [Run.valid_input] pins to true *)
Hypothesis Hrdr : a_channel_reader = true.

Definition model0 : Model :=
with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC av envv fs0 stdin0)).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

#[using="Type"] Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
#[using="Type"] Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
#[using="Type"] Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
#[using="Hrdr"] Lemma model0_rdr : m_channel_reader model0 = true. Proof. exact Hrdr. Qed.
#[using="Type"] Lemma model0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.

#[using="AMB sp0 envv tid regs0 mem0 Hva ME Hargc Hfit"] Lemma a0s_nonul : ~ In (Z_to_bv 8 0) (hd [] av).
Proof.
destruct Hva as ([H1 _] & _ & _ & Hn & _). destruct av as [|a0s rest]; [cbn in H1; lia|].
inversion Hn; subst. assumption.
Qed.

#[using="Hva Hve Hvsp Htid ME Hargc Hfit"] Lemma a0s_fits : (bv_unsigned (p0N av envv inp) + Z.of_nat (length (hd [] av)) + 1 <= 0x800000000000)%Z.
Proof.
assert (Hlen : (1 <= length av)%nat) by (destruct Hva as [[H1 _] _]; lia).
(* LPS 727298f3: the string end bound of [Q1oC.Mq1.main_strN] (the strings end below the Sv48 stack top) *)
destruct (main_strN sp0 av envv tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME 0%nat ltac:(lia))
as (_ & _ & _ & _ & _ & Send).
destruct av as [|a0 rest]; [cbn in Hlen; lia|].
cbn [hd nth] in *. unfold p0N. change (2 ^ 47)%Z with 0x800000000000%Z in Send. lia.
Qed.

#[using="AMB sp0 envv tid regs0 mem0 Hva ME Hargc Hfit"] Lemma hd_nth : hd [] av = nth 0 av [].
Proof. destruct av; reflexivity. Qed.

#[using="Hvsp SPlo SPhi"] Lemma umemcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
mem_denot (ENV vals) M u_logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE7.
Proof.
intros vals M P0. pose proof SPlo. pose proof SPhi.
rewrite <- PRE7_word. cbn [mem_denot u_logM1].
unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
f_equal; f_equal; lia.
Qed.

#[using="Hva Hve Hvsp Htid ME Hargc Hfit Hrdr SPlo SPhi"] Theorem ref_usage :
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x209c0) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_usage (hd [] av)) fs0).
Proof.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
assert (HR : regs_ok (EN sp0 av envv tid regs0 inp) sr_mainN regs0)
by exact (main_regs_okN sp0 av envv tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME).
assert (HK : know_ok RSEGS (EN sp0 av envv tid regs0 inp) mem0 kn_mainN)
by exact (main_know_okN sp0 av envv tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME).
assert (Hac : ev (EN sp0 av envv tid regs0 inp) 16 = len_word av)
by exact (evN_argc sp0 av envv tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME).
change (EN sp0 av envv tid regs0 inp) with (ENV (valsN sp0 av envv tid regs0 inp)) in HR, HK, Hac.
set (vals := valsN sp0 av envv tid regs0 inp) in *.
assert (HL : length vals = 39%nat)
by (subst vals; first [ exact (valsN_length sp0 av envv tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) | apply valsN_length ]).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P1 : vals_ev vals 1 = p0N av envv inp) by reflexivity.
cbn [ev ENV] in Hac.
destruct (main_strN sp0 av envv tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME 0%nat ltac:(lia))
as (Sr & Slo & Shi & Slen & (t8 & Ht8) & _).
rewrite <- hd_nth in Sr, Slen, Ht8. set (a0s := hd [] av) in *.
pose proof (u64_range (cat_argv_ptr (ed_top a_rnd) av envv (in_execfn inp) 0)) as Hppr.
clearbody vals.
pose proof model0_halted as Hh.

run_blk_keep_b u_scrA 39%nat.
{ unfold sc_denot. cbn [branch_taken edenot ev ENV]. rewrite Hac.
unfold bv_eqb, len_word. rewrite u_small by lia. change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
{ intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x97000);
[vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
clear EQM.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x110b8) 7 = Some PRE7).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x110b8 7) in exact i)
_ _ 0x110b8 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
assert (Hdst : store_ok RSEGS M dst 7 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
_ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH M dst (Z_to_bv 64 0x110b8) 7 PRE7).
{ constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x5329c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x110b8) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M dst (Z_to_bv 64 0x110b8) 7 _ (seg_rom RSEGS) MC Rc (0x5329c : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 382640) with (0x5d6b0 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact model0_lazy | exact Hms |]. clear Hms.
replace (0x5329c : word) with (Z_to_bv 64 0x5329c) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M dst PRE7) u_knB0).
{ subst dst. rewrite <- (umemcpy1_denot vals M P0).
eapply (carry_after RSEGS (ENV vals) M u_logM1 u_knA [] u_knB0 [] []);
[vm_compute; reflexivity | | exact HK | constructor].
cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) (wbytes M dst PRE7) u_knB0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q1 : vals_ev vals1 1 = p0N av envv inp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
rewrite <- model0_fs.
eapply (us_tail sp0 model0 Hvsp model0_halted model0_lazy model0_fd2 model0_rdr a0s (p0N av envv inp) t8 vals1); try eassumption.
- apply a0s_nonul.
- unfold p0N. lia.
- pose proof a0s_fits as HFp. fold a0s in HFp. unfold p0N in HFp |- *. clearbody a0s. lia.
- unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
Qed.

#[using="Hva Hve Hvsp Htid ME Hargc Hfit Hrdr SPlo SPhi"] Corollary ref_usage_w :
realizes RSEGS (mkCfg (mkst regs0 (0x209c0 : word) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_usage (hd [] av)) fs0).
Proof.
replace (0x209c0 : word) with (Z_to_bv 64 0x209c0) by (apply bv_eq; reflexivity). apply ref_usage.
Qed.

End Usage.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
