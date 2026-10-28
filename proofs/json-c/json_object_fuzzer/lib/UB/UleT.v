(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Qnhz Qrxj QRjH Qpox QsV0 QBxa QSjk QMz4 QO3A Q7m0 QSpR QuJV QCPB QH7x QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ Um90 UWQV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUeZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJvR UG24 U9ch U1zM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qpox QsV0 QRjH QBxa.Mq4 QSjk.Mq0 QBxa.Mq1 QMz4 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES.Mq0 QqES.
Import U1oC.
Import QBxa.Mq5 Q9ox.Mq2 QSpR.Mq0.
Import UFeQ.Mq0 Um90 U1oC.Mq0 UWQV.Mq0.
Import QUeZ.
Import Um90.Mq0 UJvR.Mq1 UG24.Mq1 U9ch.Mq0.

Import UG24.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition KEPT_OOM : list nat := [2; 3; 4]%nat.
Definition srOOM0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_OOM 6.

Definition ssA0 : sym_state := SS 0x20dec srOOM0 [] knRE0 39.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA knRE0.
Definition ssA0' : sym_state := SS 0x20e2c srOOM0 [] knRE0 39.
Definition rA' := Eval vm_compute in run scr0 ssA0'.

Definition resB : stdio_res :=
Eval vm_compute in match stdio_call 39 srA knA with Some r => r
| None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
#[using="Type"] Lemma resB_eq : stdio_call 39 srA knA = Some resB.
Proof. vm_compute. reflexivity. Qed.

Definition srB0 : list expr := Eval vm_compute in sc_sr resB.
Definition knB0 : list kentry := Eval vm_compute in sc_kn resB.
Definition ssB0 : sym_state := SS 0x550e0 srB0 [] knB0 71.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.

End FPGEN1.

Section OomTail.
Context {fF : FPF} {fC : FPC}.
Variable sp0 : word.
Variable BL : list (list byte).
Variable model : Model.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma oom_sym : forall (pc : Z) vals R M,
(pc = 0x20dec \/ pc = 0x20e2c)%Z ->
length vals = 39%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srOOM0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model)
(t_die msg_oom (m_fs model)).
Proof.
intros pc vals R M Hpc HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

assert (STEP : forall T,
(forall R' M', regs_ok (ENV BL vals) srA R' -> know_ok RSEGS (ENV BL vals) M' knA ->
realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x551dc) M' (seg_rom RSEGS)) model) T) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model) T).
{ intros T HT. destruct Hpc as [-> | ->].
- run_blk scr0 39%nat. apply HT; assumption.
- run_blk scr0 39%nat. apply HT; assumption. }
apply STEP. clear STEP HR HK R M. intros R M HR HK.

oom_stdio_exit HL P0 resB_eq Hfd2 (@eq_refl _ (m_fs model)).
Qed.

Variables (tid : Z) (c : Z) (R : bvmap 5 word) (M : word -> option byte).
Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x77c00.
Hypothesis Mstack : stack_writable M sp0.
Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Hypothesis Mtid : cell M 0x77b58 4 tid.
Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
Hypothesis Mself : cell M 0x77b38 8 0x77b38.
Hypothesis Mcanary : cell M 0x97e70 8 c.
Hypothesis Mpagesz : cell M 0x97ec0 8 4096.

Definition valsOOM : list word := valsRE sp0 sp0 tid c R.
Let E : env := ENV BL valsOOM.

#[using="Type"] Lemma valsOOM_len : length valsOOM = 39%nat.
Proof. apply valsRE_len. Qed.

#[using="Type"] Lemma evOOM_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid c R i Hi). Qed.

Ltac reg_caseOOM :=
cbn [nth srOOM0 all_regs];
first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
change (edenot E (EVar n)) with (ev E n);
first [ rewrite (evOOM_junk (n - 6)) by lia; reflexivity | idtac ]
| |- _ => cbn [edenot] end ];
first [ reflexivity
| exact Rgp | exact Rtp
| rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
| idtac ].

#[using="Hvsp SPlo SPhi Rsp Rgp Rtp"] Lemma regs_okOOM : regs_ok E srOOM0 R.
Proof.
pose proof SPlo. pose proof SPhi.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseOOM.
Qed.

#[using="Hvsp SPlo SPhi Mstack Mimg Mtid Htid Mself Mcanary Mpagesz"] Lemma know_okOOM : know_ok RSEGS E M knRE0.
Proof.
pose proof SPlo. pose proof SPhi.
apply (know_okRE sp0 BL Hvsp sp0 tid c R M Mstack Mimg Mtid Htid Mself Mcanary Mpagesz); lia.
Qed.

#[using="sp0 BL Hvsp Hh Hlazy Hfd2 SPlo SPhi tid c Rsp Rgp Rtp Mstack Mimg Mtid Htid Mself Mcanary Mpagesz E"] Theorem ref_oom_tail : forall pc : Z, (pc = 0x20dec \/ pc = 0x20e2c)%Z ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model)
(t_die msg_oom (m_fs model)).
Proof.
intros pc Hpc.
eapply (oom_sym pc valsOOM R M Hpc valsOOM_len eq_refl regs_okOOM know_okOOM).
Qed.
End OomTail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e QiVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN UMOs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 QRjH QBxa.Mq4 QSjk.Mq0 QBxa.Mq1 QMz4 Qn1e.Mq1 QiVh Qn1e QBxa.Mq0 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES.Mq0 QBxa.Mq5 Q9ox.Mq2 QSpR.Mq0.
Import UFeQ.Mq0 Um90 U1oC.Mq0 U1oC.
Import QBxa.Mq3.
Import UeDN UMOs UWQV.Mq0.
Import QUeZ.
Import Um90.Mq0 UJvR.Mq1 UG24.Mq1 U9ch.Mq0.
Import UG24.Mq2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition PRE14 : list byte := s2b "cli: input >= "%string.
Definition DIG8 : list byte := s2b "67108864"%string.
Definition SUF16 : list byte := s2b " bytes, refused"%string ++ [Z_to_bv 8 10].

#[using="Type"] Lemma msg_refused_split : msg_refused = PRE14 ++ DIG8 ++ SUF16.
Proof. reflexivity. Qed.

#[using="Type"] Lemma PRE14_words :
word_to_le_bytes 8 (Z_to_bv 64 8101528366825958499) ++ word_to_le_bytes 4 (Z_to_bv 64 1042314357)
++ word_to_le_bytes 2 (Z_to_bv 64 8253) = PRE14.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
#[using="Type"] Lemma DIG8_word : word_to_le_bytes 8 (Z_to_bv 64 3762256352692483894) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
#[using="Type"] Lemma DIG8_bytes :
word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 55) ++ word_to_le_bytes 1 (Z_to_bv 64 49)
++ word_to_le_bytes 1 (Z_to_bv 64 48) ++ word_to_le_bytes 1 (Z_to_bv 64 56) ++ word_to_le_bytes 1 (Z_to_bv 64 56)
++ word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 52) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
#[using="Type"] Lemma SUF16_words :
word_to_le_bytes 8 (Z_to_bv 64 2318354787771965984) ++ word_to_le_bytes 8 (Z_to_bv 64 748834984615634290) = SUF16.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
#[using="Type"] Lemma pre14_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11e58) 14 = Some PRE14.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma suf16_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11e68) 16 = Some SUF16.
Proof. vm_compute. reflexivity. Qed.

End FPGEN1.

Section Refused.
Context {fF : FPF} {fC : FPC}.
Variable sp0 : word.
Ltac at_addr k H :=
lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (bv_unsigned sp0 + k)%Z by lia; exact H end.
Variable BL : list (list byte).
Variable model : Model.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Let T : TSet := t_emit (W 2 msg_refused) (t_exit (exit_code 2) (m_fs model)).

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma rf_segH : forall vals R M,
length vals = 231%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srH0 R -> know_ok RSEGS (ENV BL vals) M knH0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5559c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 231%nat.
apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
2:{ cbn [W map].
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
apply t_eq_sym. apply t_emit_nil_exit. }
apply ref_exit_Z.
pose proof (know_nth RSEGS _ _ knH ltac:(let i := kidx knH (is_krange (EVar 5)) in exact i) _ HK eq_refl)
as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x77c00), (bv_unsigned (vals_ev vals 5)),
(Z_to_bv 64 0), (Z_to_bv 64 0).
split; [|split; [exact Hh|split; [exact Hlazy|]]].
+ constructor.
* regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
rewrite P0. f_equal; lia.
* regv HR (4 : reg). reflexivity.
* regv HR (10 : reg). reflexivity.
* rewrite u_small by lia. lia.
* rewrite u_small by lia. lia.
* rewrite u_small by lia.
pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knH ltac:(let i := kidx knH (is_kwr_cov (EVar 0) (-272) 144) in exact i)
_ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
* lit_u. lia.
* lit_u. lia.
* lia.
* lit_u. change (490496 - 168)%Z with 0x77b58%Z.
krd HK 0x77b58%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
rewrite Z_to_bv_bv_unsigned. reflexivity.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* repeat split; krd_solve HK.
* repeat split; krd_solve HK.
* krd_solve HK.
* exists false. split; krd_solve HK.
+ left. split; [reflexivity|].
exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segG : forall vals R M,
length vals = 199%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srG0 R -> know_ok RSEGS (ENV BL vals) M knG0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 199%nat.

krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-552)%Z 4%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-548)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-546)%Z 8%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-538)%Z 8%nat Hw4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-530)%Z 8%nat Hw5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
rewrite P0 in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
assert (MSG : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + -560)) ((8 + (4 + 2)) + (8 + (8 + 8)))
= Some msg_refused).
{ rewrite msg_refused_split, <- PRE14_words, <- DIG8_word, <- SUF16_words.
apply rdn_app_Z; [ | | lia | lia].
- apply rdn_app_Z; [exact Hw0 | | lia | lia].
apply rdn_app_Z; [at_addr (-552)%Z Hw1 | at_addr (-548)%Z Hw2 | lia | lia].
- apply rdn_app_Z; [at_addr (-546)%Z Hw3 | | lia | lia].
apply rdn_app_Z; [at_addr (-538)%Z Hw4 | at_addr (-530)%Z Hw5 | lia | lia]. }

unfold T.
replace (W 2 msg_refused) with (map (WriteEv (Z_to_bv 64 2)) (msg_refused ++ []))
by (unfold W; rewrite app_nil_r; reflexivity).
pose proof itinerary_rf as (_ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev BL) srG knG Rc Mc model scRF msg_refused []
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG knG) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRF];
change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot]. reflexivity.
- lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot]. unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
change 38%nat with ((8 + (4 + 2)) + (8 + (8 + 8)))%nat. exact MSG.
- reflexivity.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_exit_has_nil.
-
clear HR HK. intros R2 M2 HR HK.
eapply (rf_segH (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Hvsp SPlo SPhi"] Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
mem_denot (ENV BL vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE14.
Proof.
intros vals M P0. pose proof SPlo. pose proof SPhi.
rewrite <- PRE14_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
repeat (f_equal; try (f_equal; lia)).
Qed.
#[using="Hvsp SPlo SPhi"] Lemma memcpy4_denot : forall vals M, vals_ev vals 0 = sp0 ->
mem_denot (ENV BL vals) M logM4 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 546)) DIG8.
Proof.
intros vals M P0. pose proof SPlo. pose proof SPhi.
rewrite <- DIG8_word. cbn [mem_denot logM4].
unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
repeat (f_equal; try (f_equal; lia)).
Qed.
#[using="Hvsp SPlo SPhi"] Lemma memcpy5_denot : forall vals M, vals_ev vals 0 = sp0 ->
mem_denot (ENV BL vals) M logM5 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 538)) SUF16.
Proof.
intros vals M P0. pose proof SPlo. pose proof SPhi.
rewrite <- SUF16_words. cbn [mem_denot logM5]. rewrite !wbytes_app.
unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
repeat (f_equal; try (f_equal; lia)).
Qed.

Ltac after_memcpy HL Hms Hkeep :=
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity);
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]; clear Hms;
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity);
lazymatch goal with H : regs_ok ?E ?sr ?Rc |- realizes _ (mkCfg (mkst ?R2 _ _ _) _) _ =>
pose proof (regs_after_keeps _ (blobs_ev BL) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) H Hkeep callee_kept_no0) as HR2;
rewrite HL in HR2; clear H Hkeep; rename HR2 into HR
end.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segF : forall vals R M,
length vals = 167%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knF0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 167%nat.
set (dst := Z_to_bv 64 (bv_unsigned sp0 - 538)).
assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x11e68) 16 = Some SUF16).
{ rewrite (kimg_rdn RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x11e68 16) in exact i)
_ _ 0x11e68 16 HK eq_refl) by (cbn; lia). apply suf16_img. }
assert (Hdst : store_ok RSEGS M dst 16 = true).
{ pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-538) 16) in exact i)
_ _ _ (-538) 16 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 538)%Z with (bv_unsigned sp0 + -538)%Z by lia. exact Hst. }
assert (MC : mcH M dst (Z_to_bv 64 0x11e68) 16 SUF16).
{ constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x11e68) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 16) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M dst (Z_to_bv 64 0x11e68) 16 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
after_memcpy HL Hms Hkeep.
assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst SUF16) knG0).
{ subst dst. rewrite <- (memcpy5_denot vals M P0).
eapply (carry_after RSEGS (ENV BL vals) M logM5 knF [] knG0 [] []);
[vm_compute; reflexivity | | exact HK | constructor].
cbn [log_flat logM5].
repeat match goal with
| |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
| |- (_ <= _)%nat => lia
| |- True => exact I
| |- _ /\ _ => split
end. }
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst SUF16) knG0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
eapply (rf_segG vals1); eassumption.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segE : forall vals R M,
length vals = 135%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srE0 R -> know_ok RSEGS (ENV BL vals) M knD ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 135%nat.
set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546)).
set (src := Z_to_bv 64 (bv_unsigned sp0 - 952)).

krdv HK 0%nat (-952)%Z 1%nat Hd0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-951)%Z 1%nat Hd1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-950)%Z 1%nat Hd2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-949)%Z 1%nat Hd3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-948)%Z 1%nat Hd4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-947)%Z 1%nat Hd5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-946)%Z 1%nat Hd6. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-945)%Z 1%nat Hd7. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
unfold adenot, v_addi in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
cbn [a_base a_off edenot ev ENV] in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
rewrite P0 in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
assert (Hsrc : rdn RSEGS M src (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) = Some DIG8).
{ subst src. replace (bv_unsigned sp0 - 952)%Z with (bv_unsigned sp0 + -952)%Z by lia. rewrite <- DIG8_bytes.
apply rdn_app_Z; [exact Hd0 | | lia | lia].
apply rdn_app_Z; [at_addr (-951)%Z Hd1 | | lia | lia].
apply rdn_app_Z; [at_addr (-950)%Z Hd2 | | lia | lia].
apply rdn_app_Z; [at_addr (-949)%Z Hd3 | | lia | lia].
apply rdn_app_Z; [at_addr (-948)%Z Hd4 | | lia | lia].
apply rdn_app_Z; [at_addr (-947)%Z Hd5 | | lia | lia].
apply rdn_app_Z; [at_addr (-946)%Z Hd6 | at_addr (-945)%Z Hd7 | lia | lia]. }
assert (Hdst : store_ok RSEGS M dst 8 = true).
{ pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knE ltac:(let i := kidx knE (is_kwr_cov (EVar 0) (-546) 8) in exact i)
_ _ _ (-546) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 546)%Z with (bv_unsigned sp0 + -546)%Z by lia. exact Hst. }
assert (MC : mcH M dst src 8 DIG8).
{ constructor; subst dst src; rewrite ?u_small by lia; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = src)
by (regv HR (11 : reg); subst src; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A12 : getr Rc 12 = Z_to_bv 64 8) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
after_memcpy HL Hms Hkeep.
assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst DIG8) knF0).
{ subst dst. rewrite <- (memcpy4_denot vals M P0).
eapply (carry_after RSEGS (ENV BL vals) M logM4 knE [] knF0 [] []);
[vm_compute; reflexivity | | exact HK | constructor].
cbn [log_flat logM4].
repeat match goal with
| |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
| |- (_ <= _)%nat => lia
| |- True => exact I
| |- _ /\ _ => split
end. }
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst DIG8) knF0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 167%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
eapply (rf_segF vals1); eassumption.
Qed.

Ltac memcpy0_step HL P0 srcZ :=
let dst := fresh "dst" in
set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546));
lazymatch goal with HR : regs_ok _ _ ?Rc |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
assert (MC : mcH Mc dst (Z_to_bv 64 srcZ) 0 [])
by (constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity);
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 srcZ) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy Mc dst (Z_to_bv 64 srcZ) 0 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12 MC;
after_memcpy HL Hms Hkeep;
change (wbytes Mc dst []) with Mc
end.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segD : forall vals R M,
length vals = 103%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srD0 R -> know_ok RSEGS (ENV BL vals) M knC ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 103%nat.
memcpy0_step HL P0 0x104f3%Z.
lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knD ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
clear HK; rename HK2 into HK;
set (vals1 := vals ++ junk_vals R2) in *
end.
assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
eapply (rf_segE vals1); eassumption.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segC : forall vals R M,
length vals = 71%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srC0 R -> know_ok RSEGS (ENV BL vals) M knC0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 71%nat.
memcpy0_step HL P0 0x11e66%Z.
lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knC ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
clear HK; rename HK2 into HK;
set (vals1 := vals ++ junk_vals R2) in *
end.
assert (HL1 : length vals1 = 103%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
eapply (rf_segD vals1); eassumption.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segB : forall vals R M,
length vals = 39%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srRF0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20dcc) M (seg_rom RSEGS)) model) T.
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 39%nat.
set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x11e58) 14 = Some PRE14).
{ rewrite (kimg_rdn RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x11e58 14) in exact i)
_ _ 0x11e58 14 HK eq_refl) by (cbn; lia). apply pre14_img. }
assert (Hdst : store_ok RSEGS M dst 14 = true).
{ pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 14) in exact i)
_ _ _ (-560) 14 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH M dst (Z_to_bv 64 0x11e58) 14 PRE14).
{ constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x11e58) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 14) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M dst (Z_to_bv 64 0x11e58) 14 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
after_memcpy HL Hms Hkeep.
assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst PRE14) knC0).
{ subst dst. rewrite <- (memcpy1_denot vals M P0).
eapply (carry_after RSEGS (ENV BL vals) M logM1 knB [] knC0 [] []);
[vm_compute; reflexivity | | exact HK | constructor].
cbn [log_flat logM1].
repeat match goal with
| |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
| |- (_ <= _)%nat => lia
| |- True => exact I
| |- _ /\ _ => split
end. }
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst PRE14) knC0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
eapply (rf_segC vals1); eassumption.
Qed.

Variables (tid : Z) (c : Z) (R : bvmap 5 word) (M : word -> option byte).
Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x77c00.
Hypothesis Mstack : stack_writable M sp0.
Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Hypothesis Mtid : cell M 0x77b58 4 tid.
Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
Hypothesis Mself : cell M 0x77b38 8 0x77b38.
Hypothesis Mcanary : cell M 0x97e70 8 c.
Hypothesis Mpagesz : cell M 0x97ec0 8 4096.

Let E : env := ENV BL (valsRE sp0 sp0 tid c R).

#[using="Type"] Lemma evRF_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid c R i Hi). Qed.

Ltac reg_caseRF :=
cbn [nth srRF0 all_regs];
first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
change (edenot E (EVar n)) with (ev E n);
first [ rewrite (evRF_junk (n - 6)) by lia; reflexivity | idtac ]
| |- _ => cbn [edenot] end ];
first [ reflexivity
| exact Rgp | exact Rtp
| rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
| idtac ].

#[using="Hvsp SPlo SPhi Rsp Rgp Rtp"] Lemma regs_okRF : regs_ok E srRF0 R.
Proof.
pose proof SPlo. pose proof SPhi.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRF.
Qed.

#[using="sp0 BL Hvsp Hh Hlazy Hfd2 SPlo SPhi T tid c Rsp Rgp Rtp Mstack Mimg Mtid Htid Mself Mcanary Mpagesz E"] Theorem ref_refused_tail :
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20dcc) M (seg_rom RSEGS)) model)
(t_die msg_refused (m_fs model)).
Proof.
pose proof SPlo. pose proof SPhi.
unfold t_die.
eapply (rf_segB (valsRE sp0 sp0 tid c R) R M (valsRE_len sp0 sp0 tid c R) eq_refl regs_okRF).
apply (know_okRE sp0 BL Hvsp sp0 tid c R M Mstack Mimg Mtid Htid Mself Mcanary Mpagesz); lia.
Qed.
End Refused.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqHD Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 QRjH QBxa.Mq4 QSjk.Mq0 QBxa.Mq1 Q9ox.Mq2 QMz4 Qn1e.Mq1 QiVh Qn1e QBxa.Mq0 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES.Mq0 QqES QBxa.Mq5 QSpR.Mq0.
Import UFeQ.Mq0 Um90 U1oC.Mq0 U1oC.
Import QBxa.Mq3.
Import UeDN UMOs UqHD UFeQ.Mq4 Udbv UWQV.Mq0.
Import QUeZ.
Import UJvR.Mq0 UG24 U9ch.
Import U1oC.Mq1 UG24.Mq3.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition PRE7 : list byte := s2b "usage: "%string.
Definition SUF7 : list byte := s2b " INPUT"%string ++ [Z_to_bv 8 10].

#[using="Type"] Lemma PRE7_word : word_to_le_bytes 7 (Z_to_bv 64 9071406455288693) = PRE7.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
#[using="Type"] Lemma SUF7_word : word_to_le_bytes 7 (Z_to_bv 64 2907475163367712) = SUF7.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
#[using="Type"] Lemma pre7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x110af) 7 = Some PRE7.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma suf7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x110b8) 7 = Some SUF7.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma PRE7_len : length PRE7 = 7%nat. Proof. reflexivity. Qed.
#[using="Type"] Lemma SUF7_len : length SUF7 = 7%nat. Proof. reflexivity. Qed.
#[using="Type"] Lemma msg_usage_eq : forall a0s, msg_usage a0s = PRE7 ++ a0s ++ SUF7.
Proof. intros. unfold msg_usage, PRE7, SUF7. reflexivity. Qed.
End FPGEN1.

Section UTail.
Context {fF : FPF} {fC : FPC}.
Variable sp0 : word.
Variable model : Model.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

Ltac close_exit_at HR HK P0 Hh Hlazy sp0 OFF WLO :=
lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
[ | cbn [W map];
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
apply t_eq_sym; apply t_emit_nil_exit ];
apply ref_exit_Z;
let Ktid := fresh "Ktid" in
pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
as Ktid; cbn [kentry_ok edenot ev ENV EN] in Ktid;
lazymatch type of HR with regs_ok _ _ ?Rc =>
exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x77c00), (bv_unsigned (ev E 5)),
(Z_to_bv 64 0), (Z_to_bv 64 0);
split; [|split; [exact Hh|split; [exact Hlazy|]]];
[ constructor;
[ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV EN];
rewrite P0; f_equal; lia
| regv HR (4 : reg); reflexivity
| regv HR (10 : reg); reflexivity
| rewrite u_small by lia; lia
| rewrite u_small by lia; lia
| rewrite u_small by lia;
let Hst := fresh "Hst" in
pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
_ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV EN] in Hst; rewrite P0 in Hst;
replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
| lit_u; cbn [ev ENV EN] in Ktid |- *; lia
| lit_u; cbn [ev ENV EN] in Ktid |- *; lia
| cbn [ev ENV EN] in Ktid |- *; lia
| lit_u; change (490496 - 168)%Z with 0x77b58%Z;
let Htc := fresh "Htc" in
krd HK 0x77b58%Z 4%nat Htc; rewrite Htc; cbn [ev ENV EN] in Ktid |- *;
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
rewrite Z_to_bv_bv_unsigned; reflexivity
| krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
| repeat split; krd_solve HK
| repeat split; krd_solve HK
| krd_solve HK
| exists false; split; krd_solve HK ]
| left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
end end end.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma us_segH : forall vals R M,
length vals = 263%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV vals) u_srH0 R -> know_ok RSEGS (ENV vals) M u_knH0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5559c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 263%nat.
close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma us_segG : forall (a0s : list byte) (L : Z) vals R M,
Z.of_nat (length a0s) = L -> (0 <= L <= 66)%Z ->
length vals = 231%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 L ->
regs_ok (ENV vals) u_srG0 R -> know_ok RSEGS (ENV vals) M u_knG0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553 + L)) 7%nat = Some SUF7 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros a0s L vals R M HP HPr HL P0 P112 HR HK SBp SBn.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk_keep scr0 231%nat.
assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
{ unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553 + L)) 7 = Some SUF7).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
clear EQM SBp SBn. rename M0 into M'.
krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (7 + (length a0s + 7))
= Some (msg_usage a0s)).
{ rewrite msg_usage_eq.
apply rdn_app_Z; [exact Hw0 | | lia | lia].
apply rdn_app_Z; [| | lia | lia].
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 7)%Z with (bv_unsigned sp0 - 553)%Z by lia. exact SBp'.
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 7 + Z.of_nat (length a0s))%Z
with (bv_unsigned sp0 - 553 + L)%Z by lia. exact SBn'. }
replace (W 2 (msg_usage a0s)) with (map (WriteEv (Z_to_bv 64 2)) (msg_usage a0s ++ []))
by (unfold W; rewrite app_nil_r; reflexivity).
assert (LEN : length (msg_usage a0s) = (7 + (length a0s + 7))%nat)
by (rewrite msg_usage_eq, !length_app, PRE7_len, SUF7_len; reflexivity).
pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev []) u_srG u_knG Rc Mc model u_scG (msg_usage a0s) []
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG u_knG) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG]; rewrite ?LEN end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- cbn [edenot length]. reflexivity.
- cbn [length Z.of_nat]. lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- cbn [edenot]. unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm.
replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact MSG.
- reflexivity.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_exit_has_nil.
-
clear HR HK. intros R2 M2 HR HK.
eapply (us_segH (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

Definition atUF0 (a0s : list byte) (L : Z) (T : TSet) : Prop :=
forall vals R M,
length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 L ->
regs_ok (ENV vals) u_srF0 R -> know_ok RSEGS (ENV vals) M u_knF0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma us_segF : forall (a0s : list byte) (L : Z), Z.of_nat (length a0s) = L -> (0 <= L <= 66)%Z ->
atUF0 a0s L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros a0s L HP HPr vals R M HL P0 P112 HR HK SBp.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk_keep u_scrF 199%nat.
{
unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112).
replace (-1 * L + 73)%Z with (73 - L)%Z by lia.
rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
{ unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
clear EQM SBp. rename M0 into M'.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553 + L)).
assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x110b8) 7 = Some SUF7).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ u_knF ltac:(let i := kidx u_knF (is_kimg_cov 0x110b8 7) in exact i)
_ _ 0x110b8 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
assert (Hdst : store_ok RSEGS M' dst 7 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knF ltac:(let i := kidx u_knF (is_kwr_cov (EVar 0) (-553) 73) in exact i)
_ _ _ (-553 + L) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 553 + L)%Z with (bv_unsigned sp0 + (-553 + L))%Z by lia. exact Hst. }
assert (MC : mcH M' dst (Z_to_bv 64 0x110b8) 7 SUF7).
{ constructor; subst dst; rewrite ?u_small by lia; rewrite ?SUF7_len; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x110b8) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M' dst (Z_to_bv 64 0x110b8) 7 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst SUF7) 0 (-553) BUF_HI IHI u_knF
ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(apply (wbytes_agree_out M' dst SUF7 (ENV vals) 0 (-553) BUF_HI);
cbn [ev ENV]; rewrite P0, ?SUF7_len; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
(wbytes_grows _ _ _) HK) as HK2.
clear HK. change (kn_cut 0 (-553) BUF_HI IHI u_knF) with u_knG0 in HK2.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) (wbytes M' dst SUF7) u_knG0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q112 : vals_ev vals1 113 = Z_to_bv 64 L) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P112).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
eapply (us_segG a0s L vals1); try eassumption.
- rewrite rdn_wbytes_out; [exact SBp' | | |]; rewrite ?SUF7_len; subst dst; rewrite ?u_small by lia; lia.
- subst dst. rewrite <- SUF7_len.
apply (rdn_wbytes_hit RSEGS SUF7 M'). rewrite SUF7_len, u_small by lia. lia.
Qed.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma us_segE_gen : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) vals R M,
Z.of_nat (length a0s) = L -> (0 <= L <= 73)%Z ->
length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp -> vals_ev vals 113 = Z_to_bv 64 L ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) u_srE0 R -> know_ok RSEGS (ENV vals) M u_knD ->
rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
atUF0 a0s L T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros a0s pp L T vals R M HP HPr HL P0 P1 P112 Hpp1 Hpp2 HR HK Hstr HF0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 113)) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV]. rewrite P112, u_small by lia. lia. }
run_blk_keep u_scrE 167%nat.
{ unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P112).
rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
{ unfold sc_denot. cbn [branch_taken].
rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
| cbn [ev ENV]; rewrite P0; lia]. }
clear EQM Hstr. rename M0 into M'.
set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
assert (Hsrc : rdn RSEGS M' pp (length a0s) = Some a0s).
{ replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
eapply rdn_firstn; [exact Hstr' | lia]. }
assert (Hdst : store_ok RSEGS M' dst (length a0s) = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knE ltac:(let i := kidx u_knE (is_kwr_cov (EVar 0) (-553) 73) in exact i)
_ _ _ (-553) (length a0s) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 553)%Z with (bv_unsigned sp0 + -553)%Z by lia. exact Hst. }
assert (MC : mcH M' dst pp L a0s).
{ constructor; subst dst; rewrite ?u_small by lia; try lia.
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P1);
assert (A12 : getr Rc 12 = Z_to_bv 64 L) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P112);
destruct (ref_memcpy M' dst pp L _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst a0s) 0 (-553) BUF_HI IHI u_knE
ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(apply (wbytes_agree_out M' dst a0s (ENV vals) 0 (-553) BUF_HI);
cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
(wbytes_grows _ _ _) HK) as HK2.
clear HK. change (kn_cut 0 (-553) BUF_HI IHI u_knE) with u_knF0 in HK2.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) (wbytes M' dst a0s) u_knF0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q112 : vals_ev vals1 113 = Z_to_bv 64 L) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P112).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
eapply (HF0 vals1); try eassumption.
subst dst. rewrite <- HP at 1 || idtac.
pose proof (rdn_wbytes_hit RSEGS a0s M' (Z_to_bv 64 (bv_unsigned sp0 - 553))) as Hc.
apply Hc. rewrite u_small by lia. lia.
Qed.

Definition atUE0 (a0s : list byte) (pp : word) (L : Z) (T : TSet) : Prop :=
forall vals R M,
length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp -> vals_ev vals 113 = Z_to_bv 64 L ->
regs_ok (ENV vals) u_srE0 R -> know_ok RSEGS (ENV vals) M u_knD ->
rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma us_segCD : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) (t8 : list byte) vals R M,
Z.of_nat (length a0s) = L -> (0 <= L <= 131071)%Z -> ~ In (Z_to_bv 8 0) a0s ->
length vals = 103%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) u_srC0 R -> know_ok RSEGS (ENV vals) M u_knB ->
rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8 ->
atUE0 a0s pp L T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros a0s pp L T t8 vals R M HP HPr Hnonul HL P0 P1 Hpp1 Hpp2 HR HK Hstr Ht8 HE0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }

run_blk_keep scr0 103%nat.
assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
| cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
clear EQM Hstr Ht8. rename M0 into M'.
set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
assert (Hbuf : rdn RSEGS M' pp (length (a0s ++ t8)) = Some (a0s ++ t8)).
{ rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
- rewrite <- (word_Z pp). replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
eapply rdn_firstn; [exact Hstr' | lia].
- pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
assert (Hz : nth (length a0s) (a0s ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
{ pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
rewrite app_nth2, Nat.sub_diag by lia.
pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length a0s + 1) _ (length a0s)
ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + L) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
replace (bv_unsigned pp + Z.of_nat (length a0s))%Z with (bv_unsigned pp + L)%Z in B1 by lia.
replace (bv_unsigned pp + L + Z.of_nat 0)%Z with (bv_unsigned pp + L)%Z in B2 by lia.
rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
assert (MC : mchrH M' pp (a0s ++ t8) L 0x7fffffff).
{ pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
constructor.
- exact Hbuf.
- rewrite length_app, L8.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
- rewrite length_app, L8. lia.
- lia.
- rewrite <- HP, Nat2Z.id, Hz. reflexivity.
- intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
intros E. apply (In_nth_neq a0s (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
- lia.
- lia.
- intros i Hi.
pose proof (know_nth RSEGS _ _ u_knC ltac:(let k := kidx u_knC (is_kimg_cov 0x13410 24) in exact k) _ HK eq_refl)
as (_ & _ & Hnone). apply Hnone. lia. }
assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knC ltac:(let i := kidx u_knC (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
_ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst spS. rewrite u_small by lia.
replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55c3c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A2 : getr Rc 2 = spS)
by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P1);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
destruct (ref_strnlen M' pp spS (a0s ++ t8) L 0x7fffffff (seg_rom RSEGS) Rc (0x55c3c : word) MC
ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
ltac:(right; subst spS; rewrite u_small by lia; lia)
ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
clear A1 A2 A10 A11
end.
replace (Z_to_bv 64 392740) with (0x5fe24 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55c3c : word) with (Z_to_bv 64 0x55c3c) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R2 callee_saved
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
destruct Hfr as [Hagree Hgrow].
pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI u_knC
ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
unfold in_rng; subst spS; unorm;
cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
Hgrow HK) as HK2.
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) M2 (kn_cut 0 (-1152) (-1120) IHI u_knC)
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q1 : vals_ev vals1 1 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
assert (Q112 : vals_ev vals1 113 = Z_to_bv 64 L).
{ subst vals1. change 113%nat with (103 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK3.
assert (HK : know_ok RSEGS (ENV vals1) M2 u_knD0).
{ unfold u_knD0. apply know_ok_cons; [|exact HK3].
apply krange_intro. cbn [edenot ev ENV LX]. rewrite Q112, u_small by lia. lia. }
clear HK3.
assert (Hstr2 : rdn RSEGS M2 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
{ rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 113)) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV]. rewrite Q112, u_small by lia. lia. }

run_blk_keep u_scrD 135%nat.
{ unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
{ unfold sc_denot. exists [Z_to_bv 8 0]. split.
- unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
ed_lin ltac:(cbn [ev ENV]; rewrite ?Q1, ?Q112). rewrite <- HP.
pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length a0s + 1) _ (length a0s)
ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
- reflexivity. }
assert (Hstr3 : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
[exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
| cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
clear EQM Hstr2. rename M0 into M3.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
assert (MC : mcH M3 dst (Z_to_bv 64 0x104f3) 0 []).
{ constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x104f3) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M3 dst (Z_to_bv 64 0x104f3) 0 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
change (wbytes M3 dst []) with M3.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals1 (blobs_ev []) sr Rc R4 callee_kept
ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev []) M3 u_knD ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
clear HK. rename HK2 into HK.
set (vals2 := vals1 ++ junk_vals R4) in *.
assert (HL2 : length vals2 = 167%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
assert (W1 : vals_ev vals2 1 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q1).
assert (W112 : vals_ev vals2 113 = Z_to_bv 64 L) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q112).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev [])) with (ENV vals2) in HR, HK.
eapply (HE0 vals2); eassumption.
Qed.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma us_segB : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) (t8 : list byte) vals R M,
Z.of_nat (length a0s) = L -> (0 <= L <= 131071)%Z -> ~ In (Z_to_bv 8 0) a0s ->
length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) u_srB0 R -> know_ok RSEGS (ENV vals) M u_knB0 ->
rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8 ->
atUE0 a0s pp L T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros a0s pp L T t8 vals R M HP HPr Hnonul HL P0 P1 Hpp1 Hpp2 HR HK Hstr Ht8 HE0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
run_blk_keep scr0 71%nat.
assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
| cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
clear EQM Hstr Ht8. rename M0 into M3.
set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
assert (MC : mcH M3 dst (Z_to_bv 64 0x110b6) 0 []).
{ constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x110b6) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M3 dst (Z_to_bv 64 0x110b6) 0 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
change (wbytes M3 dst []) with M3.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R4 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (env_app_know RSEGS vals (junk_vals R4) (blobs_ev []) M3 u_knB ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
clear HK. rename HK2 into HK.
set (vals2 := vals ++ junk_vals R4) in *.
assert (HL2 : length vals2 = 103%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (W1 : vals_ev vals2 1 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev [])) with (ENV vals2) in HR, HK.
eapply (us_segCD a0s pp L T t8 vals2); eassumption.
Qed.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma us_segH3 : forall vals R M,
length vals = 263%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV vals) u_srH30 R -> know_ok RSEGS (ENV vals) M u_knH30 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5559c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 263%nat.
close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma us_segG3 : forall vals R M,
length vals = 231%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV vals) u_srG30 R -> know_ok RSEGS (ENV vals) M u_knG30 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5576c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk scr0 231%nat.
apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev []) u_srG3 u_knG3 Rc Mc model u_scG3 [] []
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG3 u_knG3) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG3 length Z.of_nat] end.
- lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- lia.
- cbn [edenot]. apply u_small. lia.
- lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot]. unorm. lia.
- reflexivity.
- reflexivity.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_exit_has_nil.
- clear HR HK. intros R2 M2 HR HK.
eapply (us_segH3 (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma us_segF3 : forall (a0s : list byte) (L : Z), Z.of_nat (length a0s) = L -> (67 <= L <= 73)%Z ->
atUF0 a0s L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros a0s L HP HPr vals R M HL P0 P112 HR HK SBp.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk_keep u_scrF3 199%nat.
{ unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite <- (zbv_mod (-1 * L + 73)%Z).
rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
{ unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
clear EQM SBp. rename M0 into M'.
krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (7 + length a0s) = Some (PRE7 ++ a0s)).
{ apply rdn_app_Z; [exact Hw0 | | lia | lia].
replace (bv_unsigned sp0 + -560 + Z.of_nat 7)%Z with (bv_unsigned sp0 - 553)%Z by lia. exact SBp'. }
assert (Hsuf : rdn RSEGS M' (Z_to_bv 64 0x110b8) 7 = Some SUF7).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ u_knF3 ltac:(let i := kidx u_knF3 (is_kimg_cov 0x110b8 7) in exact i)
_ _ 0x110b8 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
rewrite msg_usage_eq, app_assoc. unfold W.
pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev []) u_srF3 u_knF3 Rc Mc model u_scF3 (PRE7 ++ a0s) SUF7
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srF3 u_knF3) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scF3];
rewrite ?length_app, ?PRE7_len, ?SUF7_len end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- cbn [edenot]. apply u_small. lia.
- cbn [length Z.of_nat]. lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
- left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot]. unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm.
replace (7 + length a0s)%nat with (7 + length a0s)%nat by lia. exact B80.
- cbn [edenot]. exact Hsuf.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_exit_has_nil.
-
clear HR HK. intros R2 M2 HR HK.
eapply (us_segG3 (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma us_segH4 : forall vals R M,
length vals = 263%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV vals) u_srH40 R -> know_ok RSEGS (ENV vals) M u_knH40 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5559c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 263%nat.
close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma us_segG4 : forall vals R M,
length vals = 231%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV vals) u_srG40 R -> know_ok RSEGS (ENV vals) M u_knG40 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk scr0 231%nat.
krdv HK 0%nat (-560)%Z 7%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
rewrite SUF7_word in Hb.
unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
replace (W 2 SUF7) with (map (WriteEv (Z_to_bv 64 2)) (SUF7 ++ [])) by (unfold W; rewrite app_nil_r; reflexivity).
pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev []) u_srG4 u_knG4 Rc Mc model u_scG4 SUF7 []
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG4 u_knG4) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG4];
rewrite ?SUF7_len end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot length Z.of_nat]. apply u_small. lia.
- cbn [length Z.of_nat]. lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot]. unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
- reflexivity.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_exit_has_nil.
- clear HR HK. intros R2 M2 HR HK.
eapply (us_segH4 (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma us_segEF4 : forall (a0s : list byte) (pp : word) (L : Z), Z.of_nat (length a0s) = L -> (74 <= L <= 131071)%Z ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
(bv_unsigned pp + L <= 0x800000000000)%Z ->
atUE0 a0s pp L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros a0s pp L HP HPr Hpp1 Hpp2 HppT vals R M HL P0 P1 P112 HR HK Hstr.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 113)) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV]. rewrite P112, u_small by lia. lia. }
run_blk_keep u_scrE4 167%nat.
{ unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P112).
rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
{ unfold sc_denot. cbn [branch_taken].
rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
clear EQM Hstr. rename M0 into M'.
assert (Hsrc : rdn RSEGS M' pp (length a0s) = Some a0s).
{ replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
eapply rdn_firstn; [exact Hstr' | lia]. }
krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE7 ++ a0s)) (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))))).
2:{ rewrite msg_usage_eq, app_assoc. unfold W. rewrite (map_app _ (PRE7 ++ a0s)).
apply t_eq_sym. apply t_emit_app. }
unfold W at 1.
pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev []) u_srE4 u_knE4 Rc Mc model u_scE4 PRE7 a0s
(t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))) HR HK
(eq_trans (f_equal (fun n => stdio_call n u_srE4 u_knE4) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scE4];
rewrite ?PRE7_len end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot ev ENV LX]. rewrite P112. rewrite u_small by lia. lia.
- cbn [length Z.of_nat]. lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- right. cbn [edenot ev ENV LX]. rewrite P1. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot ev ENV LX]. rewrite P1, P112. rewrite u_small by lia. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hw0.
- cbn [edenot ev ENV LX]. rewrite P1. exact Hsrc.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_emit_has_nil.
-
clear HR HK. intros R1 M1 HR HK.
clear Hstr' Hsrc Hw0 Psmall.
lazymatch type of HK with know_ok _ _ _ ?k => change k with u_knF40 in HK end.
lazymatch type of HR with regs_ok _ ?sr _ => change sr with u_srF40 in HR end.
set (vals0 := vals) in P1, P112.
set (vals1 := vals ++ junk_vals R1) in *.
assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
run_blk scr0 199%nat.
lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
assert (Hsuf : rdn RSEGS MG (Z_to_bv 64 0x110b8) 7 = Some SUF7).
{ rewrite (kimg_rdn RSEGS (ENV vals1) _ u_knF4 ltac:(let i := kidx u_knF4 (is_kimg_cov 0x110b8 7) in exact i)
_ _ 0x110b8 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
assert (Hdst : store_ok RSEGS MG dst 7 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals1) _ u_knF4 ltac:(let i := kidx u_knF4 (is_kwr_cov (EVar 0) (-560) 7) in exact i)
_ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH MG dst (Z_to_bv 64 0x110b8) 7 SUF7).
{ constructor; subst dst; rewrite ?u_small by lia; rewrite ?SUF7_len; try (cbn; lia).
- exact Hsuf.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x110b8) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy MG dst (Z_to_bv 64 0x110b8) 7 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals1 (blobs_ev []) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (know_after_store RSEGS (ENV vals1) MG u_knF4 (SA (EVar 0) (-560)) 7 (ELit 2907475163367712) SUF7
u_knG40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
ltac:(cbn [edenot]; symmetry; apply SUF7_word)) as HK2.
clear HK.
assert (Edst : adenot (ENV vals1) (SA (EVar 0) (-560)) = dst).
{ unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
rewrite Edst in HK2.
pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev []) (wbytes MG dst SUF7) u_knG40
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals2 := vals1 ++ junk_vals R2) in *.
assert (HL2 : length vals2 = 231%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev [])) with (ENV vals2) in HR, HK.
eapply (us_segG4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Theorem us_tail : forall (a0s : list byte) (pp : word) (t8 : list byte) vals R M,
~ In (Z_to_bv 8 0) a0s -> (Z.of_nat (length a0s) <= 131071)%Z ->
length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z ->
(bv_unsigned pp + Z.of_nat (length a0s) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
(bv_unsigned pp + Z.of_nat (length a0s) <= 0x800000000000)%Z ->
regs_ok (ENV vals) u_srB0 R -> know_ok RSEGS (ENV vals) M u_knB0 ->
rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length a0s))) 8 = Some t8 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_die (msg_usage a0s) (m_fs model)).
Proof.
intros a0s pp t8 vals R M Hnonul HPl HL P0 P1 Hpp1 Hpp2 HppT HR HK Hstr Ht8.
unfold t_die.
eapply (us_segB a0s pp (Z.of_nat (length a0s)) _ t8 vals); try eassumption; try lia.
intros vals' R' M' HL' Q0 Q1 Q112 HR' HK' Hstr'.
destruct (Z.le_gt_cases (Z.of_nat (length a0s)) 73) as [Hle | Hgt].
- eapply (us_segE_gen a0s pp _ _ vals'); try eassumption; try lia.
destruct (Z.le_gt_cases (Z.of_nat (length a0s)) 66) as [Hle2 | Hgt2].
+ apply us_segF; [reflexivity | lia].
+ apply us_segF3; [reflexivity | lia].
- eapply (us_segEF4 a0s pp _ eq_refl); try eassumption; try lia.
Qed.

End UTail.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqES.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeDN. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMOs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMOs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqHD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqHD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udbv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFOH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFOH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWQV.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUeZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUeZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJvR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJvR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG24. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U9ch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U9ch.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
(2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
Proof. intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
replace ((- e) mod 2 ^ 64)%Z with (2 ^ 64 - e)%Z; [lia|].
apply Z.mod_unique with (q := (-1)%Z); lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="Type"] Lemma In_firstn : forall {A} (l : list A) n x, In x (firstn n l) -> In x l.
Proof.
intros A l n x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H.
Qed.

#[using="Type"] Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
intros e He. unfold openat_errnos in He. cbn in He.
unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.

Section OpenFail.
Context {AMB : Amb}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable brk : word.
Variable mbase : word.
Variable fs0 : Fs.
Variable stdin0 : InputStream.

Variable lim : Z.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.

Hypothesis Hfit : entry_stack_fits sp0 [a0s; path] envv.

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).
Definition model0 : Model :=
with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0)).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

#[using="Type"] Lemma model0_halted : m_halted model0 = None.
Proof. reflexivity. Qed.
#[using="Type"] Lemma model0_lazy : m_vm_lazy model0 = [].
Proof. reflexivity. Qed.
#[using="Type"] Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma model0_fs : m_fs model0 = fs0.
Proof. reflexivity. Qed.

#[using="a0s Hva"] Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
Proof.
destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
Qed.
#[using="a0s Hva"] Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
Proof.
destruct Hva as (_ & _ & Hl & _ & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
Qed.

#[using="a0s tid Hva Htid"] Lemma path_noslash : path_has_slash path = false.
Proof. destruct Hva as (_ & _ & _ & _ & Ht). cbn [tl] in Ht. inversion Ht; subst. tauto. Qed.
#[using="a0s tid Hva Htid"] Lemma path_notdotdot : path_eqb path dotdot_path = false.
Proof. destruct Hva as (_ & _ & _ & _ & Ht). cbn [tl] in Ht. inversion Ht; subst. tauto. Qed.
#[using="a0s tid Hva Htid"] Lemma path_not_dirref : path <> dot_path -> Open.path_is_dirref path = false.
Proof.
intros Hnd. unfold Open.path_is_dirref.
replace (path_eqb path Namei.dotdot_path) with false by (symmetry; exact path_notdotdot).
rewrite Bool.orb_false_r.
destruct (path_eqb path Uapi.dot_path) eqn:E; [| reflexivity]. exfalso. apply Hnd. apply path_eqb_eq. exact E.
Qed.

#[using="AMB tid regs0 Hva Hve Hvsp ME SPlo SPhi"] Lemma path_facts :
rdn RSEGS mem0 (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
/\ (bv_unsigned sp0 <= bv_unsigned (p1 sp0 a0s path envv))%Z
/\ (bv_unsigned (p1 sp0 a0s path envv) <= bv_unsigned sp0 + 2107576)%Z
/\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (p1 sp0 a0s path envv) + Z.of_nat (length path))) 8 = Some t8.
Proof.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct (main_str sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
cbn [nth] in Sr, Slo, Shi, Slen. unfold p1.
split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|].
pose proof (lay_bsb_nw RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
destruct (read_word_stack RPH RSEGS sp0 [a0s; path] envv 1 (length path) a_uid a_hwcap a_rnd ltac:(cbn; lia) ltac:(cbn; lia) Hnw)
as (t8 & Hl8 & Hr8).
exists t8. rewrite w_add_nat in Hr8.
pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)).
rewrite (main_entry_rdn_above sp0 [a0s; path] envv tid regs0 mem0 ME) by (rewrite u_small by lia; lia).
pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv a_uid a_hwcap a_rnd) as Hw. unfold wmem in Hw.
rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
Qed.

#[using="Hva Hve Hvsp Hfit SPlo SPhi"] Lemma path_fits : (bv_unsigned (p1 sp0 a0s path envv) + Z.of_nat (length path) + 1 <= 0x800000000000)%Z.
Proof.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
unfold p1. rewrite (u_cat_argv_ptr sp0 [a0s; path] envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(cbn; lia)).
pose proof Hfit as HF. unfold entry_stack_fits, entry_stack_span, sp_window_hi in HF.
pose proof (total_arg_bytes_nonneg envv) as He.
cbn [firstn]. rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat.
unfold cat_struct_size, auxv_size. cbn [length total_arg_bytes fold_right] in HF. unfold auxv_size in HF. cbn [length]. lia.
Qed.

#[using="regs0 Hva Hve Hvsp ME Hfit SPlo SPhi"] Theorem ref_open_fail_errno : forall e vals R M,
(1 <= e <= 4095)%Z ->
length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 39 = errno_ret e ->
vals_ev vals 2 = p1 sp0 a0s path envv ->
regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 39)) R -> know_ok RSEGS (ENV vals) M knA ->
(forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x6086c) M (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros e vals R M He HL P0 P38 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
destruct path_facts as (Sr & Slo & Shi & t8 & Ht8).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
rewrite <- model0_fs.
eapply (of_tail sp0 (blobs0 a0s path) model0 Hvsp model0_halted model0_lazy model0_fd2 path (p1 sp0 a0s path envv) t8 vals);
try eassumption.
- apply path_nonul.
- rewrite P38. apply errno_ret_range. exact He.
- lia.
- pose proof path_fits. lia.
- rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
Qed.

#[using="Hva Hve Hvsp Htid ME SPlo SPhi"] Lemma of_blockA : forall T,
(forall vals R M,
length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
(forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x60868) M (seg_rom RSEGS)) model0) T) ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x20b84) mem0 (seg_rom RSEGS)) model0) T.
Proof.
intros T HA.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
pose proof (main_regs_ok sp0 a0s path envv tid regs0 mem0 Hvsp Htid ME) as HR.
pose proof (main_know_ok sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
change (E0 sp0 a0s path envv tid regs0) with (ENV (vals0 sp0 a0s path envv tid regs0)) in HR, HK.
set (vals := vals0 sp0 a0s path envv tid regs0) in *.
assert (HL : length vals = 39%nat) by (subst vals; unfold vals0; rewrite !length_app, junk_vals_length; reflexivity).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
clearbody vals.
pose proof model0_halted as Hh.
run_blk_keep scr0 39%nat.
apply (HA vals); try assumption.
intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x99000);
[vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
Qed.

#[using="Type"] Lemma openat_regs : forall vals R,
vals_ev vals 2 = p1 sp0 a0s path envv -> regs_ok (ENV vals) srA R ->
getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 sp0 a0s path envv
/\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
Proof.
intros vals R P2 HR. repeat split.
- regv HR (17 : reg). reflexivity.
- regv HR (10 : reg). apply bv_eq. reflexivity.
- regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
- regv HR (12 : reg). vm_compute. reflexivity.
Qed.

#[using="regs0 Hva Hve Hvsp ME Hfit SPlo SPhi"] Lemma after_openat_fail : forall e vals R M,
(1 <= e <= 4095)%Z ->
length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
(forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x60868) 4) M (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros e vals R M He HL P0 P2 HR HK Habove.
rewrite v_addi_pc4 by lia. change (0x60868 + 4)%Z with 0x6086c%Z.
lazymatch type of HR with regs_ok _ ?sr ?Rc =>
pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
eapply (ref_open_fail_errno e (vals ++ [errno_ret e])); try eassumption.
- rewrite length_app, HL. reflexivity.
- rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
- rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
- rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
- apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
Qed.

#[using="Hva Hve Hvsp Htid ME Hfit SPlo SPhi"] Theorem ref_open_fail_toolong :
(4096 <= length path)%nat ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x20b84) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & _).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0x60868) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_toolong RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
- rewrite A11. rewrite <- (firstn_app_l 4096 path [Z_to_bv 8 0]) at 1 || idtac.
replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
- apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
Qed.

#[using="Hva Hve Hvsp Htid ME Hfit SPlo SPhi"] Theorem ref_open_fail_empty :
path = [] ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x20b84) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & _).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0x60868) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_empty RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12).
- split; [cbn; lia|]. split; [intros [] |]. rewrite A11.
replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
cbn [length Nat.add app].
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
Qed.

#[using="Hva Hve Hvsp Htid ME Hfit SPlo SPhi"] Theorem ref_open_fail_absent :
(length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x20b84) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros Hlen Hne Hnd Hfs. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & _).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0x60868) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_absent RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12 path).
- split; [exact Hlen|]. split; [apply path_nonul|]. rewrite A11.
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- exact Hne.
- exact path_noslash.
- apply path_not_dirref. exact Hnd.
- exact Hfs.
- apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
Qed.

#[using="Hva Hve Hvsp Htid ME Hfit SPlo SPhi"] Corollary ref_open_fail_toolong_w :
(4096 <= length path)%nat ->
realizes RSEGS (mkCfg (mkst regs0 (0x20b84 : word) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros H. replace (0x20b84 : word) with (Z_to_bv 64 0x20b84) by (apply bv_eq; reflexivity).
apply ref_open_fail_toolong. exact H.
Qed.

#[using="Hva Hve Hvsp Htid ME Hfit SPlo SPhi"] Corollary ref_open_fail_empty_w :
path = [] ->
realizes RSEGS (mkCfg (mkst regs0 (0x20b84 : word) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros H. replace (0x20b84 : word) with (Z_to_bv 64 0x20b84) by (apply bv_eq; reflexivity).
apply ref_open_fail_empty. exact H.
Qed.

#[using="Hva Hve Hvsp Htid ME Hfit SPlo SPhi"] Corollary ref_open_fail_absent_w :
(length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
realizes RSEGS (mkCfg (mkst regs0 (0x20b84 : word) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros H1 H2 H3 H4. replace (0x20b84 : word) with (Z_to_bv 64 0x20b84) by (apply bv_eq; reflexivity).
apply ref_open_fail_absent; assumption.
Qed.

End OpenFail.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
