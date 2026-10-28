(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Qnhz Qrxj QRjH QBxa QSjk QO3A Q7m0 QSpR QuJV QCPB QH7x QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ UWQV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUeZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90 UJvR UG24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 QRjH QBxa.Mq4 QSjk.Mq0 QBxa.Mq1 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES.Mq0 QBxa.Mq5.
Import UFeQ.Mq0 UWQV.Mq0.
Import QUeZ.
Import Um90.Mq0.
Import UJvR.Mq1 UG24.Mq1.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition re_ivs : list (Z * Z) :=
[(0x10000,0x66f30); (0x66f31,0x66f79); (0x76f79,0x77b30); (0x97c08,0x97c18); (0x77b64,0x77bb0); (0x77bb8,0x77bd0);
(0x77bd8,0x77bf0); (0x77c00,0x77c10); (0x77c20,0x97c08); (0x97c40,0x97e70); (0x97e78,0x97e80); (0x97e91,0x97e98);
(0x97ec8,0x97ef8); (0x97f00,0x97f78); (0x98320,0x99000)]%Z.

End FPGEN1.

Section ReadErr.
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

#[using="Hvsp Hh Hlazy Hfd2"] Theorem re_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z ->
(bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV BL vals) srRE0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20db0) M (seg_rom RSEGS)) model)
(t_die (msg_read_error path) (m_fs model)).
Proof.
intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
unfold t_die.
eapply (re_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
try eassumption; try lia.
intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
eapply (re_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
Qed.

Variables (pp : word) (tid : Z) (c : Z) (R : bvmap 5 word) (M : word -> option byte).

Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x77c00.
Hypothesis Rs2 : getr R 18 = pp.

Hypothesis Mstack : stack_writable M sp0.
Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Hypothesis Mtid : cell M 0x77b58 4 tid.
Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
Hypothesis Mself : cell M 0x77b38 8 0x77b38.
Hypothesis Mcanary : cell M 0x97e70 8 c.
Hypothesis Mpagesz : cell M 0x97ec0 8 4096.

Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.

Definition valsRE : list word :=
[sp0; pp; pp; pp; pp; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 c].
Let E : env := ENV BL valsRE.

#[using="Type"] Lemma valsRE_len : length valsRE = 39%nat.
Proof. unfold valsRE. rewrite !length_app, junk_vals_length. reflexivity. Qed.

#[using="Type"] Lemma evRE_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRE.
change (6 + i)%nat with (length [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] + i)%nat.
unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.

#[using="Type"] Lemma spxRE_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

Ltac reg_caseRE :=
cbn [nth srRE0 all_regs];
first [ rewrite spxRE_val
| lazymatch goal with |- _ = edenot _ (EVar ?n) =>
change (edenot E (EVar n)) with (ev E n);
first [ rewrite (evRE_junk (n - 6)) by lia; reflexivity | idtac ]
| |- _ => cbn [edenot] end ];
first [ reflexivity
| exact Rgp | exact Rtp | exact Rs2
| rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
| idtac ].

#[using="Hvsp SPlo SPhi Rsp Rgp Rtp Rs2"] Lemma regs_okRE : regs_ok E srRE0 R.
Proof.
pose proof SPlo. pose proof SPhi.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRE.
Qed.

#[using="Mimg"] Lemma img_clear_of : forall lo hi, In (lo, hi) re_ivs -> img_clear M lo hi.
Proof. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.

Ltac kimg := split; [lia|]; split; [lia|]; apply img_clear_of; cbn; tauto.
Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
rewrite adenot_lit0; cbn [edenot];
first [exact H | rewrite H; reflexivity | idtac].

#[using="Hvsp SPlo SPhi SPal Mstack Mimg Mtid Htid Mself Mcanary Mpagesz Hpp1"] Lemma know_okRE : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knRE0.
Proof.
intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
unfold know_ok, knRE0.
repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
-  split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
- change (edenot E (EVar 0)) with sp0. lia.
-  split; [apply flat_intro; cbn; lia|].
intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia.
apply Mstack; lia.
- change (edenot E (EVar 2)) with pp. lia.
-  split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
apply store_ok_data; rewrite u_small by lia; lia.
- kimg. - kimg. - kimg. - kimg.
- kcell Mself.
- kcell Mtid.
- kimg. - kimg. - kimg. - kimg. - kimg. - kimg.
- kcell Mcanary.
- kimg. - kimg.
- kcell Mpagesz.
- kimg.
- kimg. - kimg.
- change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
Qed.

#[using="BL Hvsp Hh Hlazy Hfd2 SPlo SPhi SPal tid c Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htid Mself Mcanary Mpagesz Hpp1 E"] Theorem ref_read_error : forall (path : list byte) (t8 : list byte),
~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
(bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20db0) M (seg_rom RSEGS)) model)
(t_die (msg_read_error path) (m_fs model)).
Proof.
intros path t8 Hnonul HPl Hpp2 Hstr Ht8.
eapply (re_tail path pp t8 valsRE R M); try eassumption.
- apply valsRE_len.
- reflexivity.
- reflexivity.
- apply regs_okRE.
- apply know_okRE. lia.
Qed.

#[using="BL Hvsp Hh Hlazy Hfd2 SPlo SPhi SPal tid c Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htid Mself Mcanary Mpagesz Hpp1 E"] Corollary ref_read_error_dot : forall (t8 : list byte),
(bv_unsigned pp + 9 <= bv_unsigned sp0 + 4194304)%Z ->
rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0] ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20db0) M (seg_rom RSEGS)) model)
(t_die (msg_read_error dot_path) (m_fs model)).
Proof.
intros t8 Hpp2 Hstr Ht8.
apply (ref_read_error dot_path t8).
- cbn. intros [E0|[]]. apply (f_equal bv_unsigned) in E0. vm_compute in E0. lia.
- cbn. lia.
- cbn [length dot_path Z.of_nat Pos.of_succ_nat]. lia.
- exact Hstr.
- exact Ht8.
Qed.
End ReadErr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqES.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeDN. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMOs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMOs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqHD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqHD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udbv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWQV.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUeZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUeZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJvR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJvR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG24.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac close_exit HR HK P0 Hh Hlazy sp0 :=
lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
[ | cbn [W map];
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
apply t_eq_sym; apply t_emit_nil_exit ];
apply ref_exit_Z;
let Ktid := fresh "Ktid" in
pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
lazymatch type of HR with regs_ok _ _ ?Rc =>
exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x77c00), (bv_unsigned (ev E 5)),
(Z_to_bv 64 0), (Z_to_bv 64 0);
split; [|split; [exact Hh|split; [exact Hlazy|]]];
[ constructor;
[ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV];
rewrite P0; f_equal; lia
| regv HR (4 : reg); reflexivity
| regv HR (10 : reg); reflexivity
| rewrite u_small by lia; lia
| rewrite u_small by lia; lia
| rewrite u_small by lia;
let Hst := fresh "Hst" in
pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
_ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
| lit_u; cbn [ev ENV] in Ktid |- *; lia
| lit_u; cbn [ev ENV] in Ktid |- *; lia
| cbn [ev ENV] in Ktid |- *; lia
| lit_u; change (490496 - 168)%Z with 0x77b58%Z;
let Htc := fresh "Htc" in
krd HK 0x77b58%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
rewrite Z_to_bv_bv_unsigned; reflexivity
| krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
| repeat split; krd_solve HK
| repeat split; krd_solve HK
| krd_solve HK
| exists false; split; krd_solve HK ]
| left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
end end end.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Section Tail2.
Variable sp0 : word.
Variable BL : list (list byte).
Variable model : Model.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segI3 : forall vals R M,
length vals = 264%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srI30 R -> know_ok RSEGS (ENV BL vals) M knI30 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5559c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 264%nat.
close_exit HR HK P0 Hh Hlazy sp0.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segH3 : forall vals R M,
length vals = 232%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srH30 R -> know_ok RSEGS (ENV BL vals) M knH30 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5576c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk scr0 232%nat.
apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev BL) srH3 knH3 Rc Mc model scH3 [] []
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH3 knH3) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH3 length Z.of_nat] end.
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
eapply (of_segI3 (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segG3 : forall (path : list byte), Z.of_nat (length path) = 63%Z ->
atG0 sp0 BL model path 63 (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros path HP vals R M HL P0 P113 HR HK SBp.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk_keep scrG3 200%nat.
{
unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
replace (-1 * 63 + 63)%Z with 0%Z by lia.
rewrite ltu_ZZ by lia. reflexivity. }
assert (WOK : win_ok (ENV BL vals) 0 BUF_LO BUF_HI IHI).
{ unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
clear EQM SBp. rename M0 into M'.
krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
rewrite P0 in Hw0, Hw1, Hw2.
assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
{ rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
apply rdn_app_Z; [exact Hw0 | | lia | lia].
apply rdn_app_Z; [ | | lia | lia].
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + length path) = Some (PRE17 ++ path)).
{ apply rdn_app_Z; [exact H17 | | lia | lia].
replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'. }
assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x12981) 1 = Some [Z_to_bv 8 10]).
{ rewrite (kimg_rdn RSEGS (ENV BL vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x12981 1) in exact i)
_ _ 0x12981 1 HK eq_refl) by (cbn; lia). apply nl_img. }

unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
pose proof itinerary_63_64 as (_ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev BL) srG3 knG3 Rc Mc model scG3 (PRE17 ++ path) [Z_to_bv 8 10]
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG3 knG3) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scG3];
rewrite ?length_app, ?PRE17_len end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- cbn [edenot length]. apply u_small. lia.
- cbn [length Z.of_nat]. lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot]. unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
replace (17 + length path)%nat with (17 + length path)%nat by lia. exact B80.
- cbn [edenot]. exact Hnl.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_exit_has_nil.
-
clear HR HK. intros R2 M2 HR HK.
eapply (of_segH3 (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Type"] Lemma NL_word : word_to_le_bytes 1 (Z_to_bv 64 10) = [Z_to_bv 8 10].
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segI4 : forall vals R M,
length vals = 264%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srI40 R -> know_ok RSEGS (ENV BL vals) M knI40 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5559c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 264%nat.
close_exit HR HK P0 Hh Hlazy sp0.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segH4 : forall vals R M,
length vals = 232%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srH40 R -> know_ok RSEGS (ENV BL vals) M knH40 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk scr0 232%nat.
krdv HK 0%nat (-560)%Z 1%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
rewrite NL_word in Hb.
unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev BL) srH4 knH4 Rc Mc model scH4 [Z_to_bv 8 10] []
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH4 knH4) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH4 length Z.of_nat] end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot]. apply u_small. lia.
- lia.
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
eapply (of_segI4 (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segFG4 : forall (path : list byte) (pp : word) (P : Z) vals R M,
Z.of_nat (length path) = P -> (64 <= P <= 131071)%Z ->
length vals = 168%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 114 = Z_to_bv 64 P ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
(bv_unsigned pp + P <= 0x800000000000)%Z ->
regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knE ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HppT HR HK Hstr.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
assert (Psmall : (bv_unsigned (edenot (ENV BL vals) (EVar 114)) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV]. rewrite P113, u_small by lia. lia. }

run_blk_keep scrF4 168%nat.
{
unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
{
unfold sc_denot. cbn [branch_taken].
rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
assert (WOKS : win_ok (ENV BL vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
clear EQM Hstr. rename M0 into M'.
assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
{ replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
eapply rdn_firstn; [exact Hstr' | lia]. }
krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
rewrite P0 in Hw0, Hw1, Hw2.
assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
{ rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
apply rdn_app_Z; [exact Hw0 | | lia | lia].
apply rdn_app_Z; [ | | lia | lia].
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }

apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))))).
2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
apply t_eq_sym. apply t_emit_app. }
unfold W at 1.
pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev BL) srF4 knF4 Rc Mc model scF4 PRE17 path
(t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))) HR HK
(eq_trans (f_equal (fun n => stdio_call n srF4 knF4) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scF4];
rewrite ?PRE17_len end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot ev ENV PX]. rewrite P113. rewrite u_small by lia. lia.
- cbn [length Z.of_nat]. lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- right. cbn [edenot ev ENV PX]. rewrite P2. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
- cbn [edenot ev ENV PX]. rewrite P2, P113. rewrite u_small by lia. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact H17.
- cbn [edenot ev ENV PX]. rewrite P2. exact Hsrc.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_emit_has_nil.
-
clear HR HK. intros R1 M1 HR HK.
clear Hstr' Hsrc Hw0 Hw1 Hw2 H17 Psmall.
lazymatch type of HK with know_ok _ _ _ ?k => change k with knG40 in HK end.
lazymatch type of HR with regs_ok _ ?sr _ => change sr with srG40 in HR end.
set (vals0 := vals) in P2, P113.
set (vals1 := vals ++ junk_vals R1) in *.
assert (HL1 : length vals1 = 200%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
run_blk scr0 200%nat.
lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x12981) 1 = Some [Z_to_bv 8 10]).
{ rewrite (kimg_rdn RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x12981 1) in exact i)
_ _ 0x12981 1 HK eq_refl) by (cbn; lia). apply nl_img. }
assert (Hdst : store_ok RSEGS MG dst 1 = true).
{ pose proof (kwr_store_ok RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-560) 1) in exact i)
_ _ _ (-560) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH MG dst (Z_to_bv 64 0x12981) 1 [Z_to_bv 8 10]).
{ constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
- exact Hnl.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12981) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy MG dst (Z_to_bv 64 0x12981) 1 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

pose proof (know_after_store RSEGS (ENV BL vals1) MG knG4 (SA (EVar 0) (-560)) 1 (ELit 10) [Z_to_bv 8 10]
knH40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
ltac:(cbn [edenot]; symmetry; apply NL_word)) as HK2.
clear HK.
assert (Edst : adenot (ENV BL vals1) (SA (EVar 0) (-560)) = dst).
{ unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
rewrite Edst in HK2.
pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst [Z_to_bv 8 10]) knH40
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals2 := vals1 ++ junk_vals R2) in *.
assert (HL2 : length vals2 = 232%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR, HK.
eapply (of_segH4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Theorem of_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 131071)%Z ->
length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
(2 ^ 64 - 4095 <= bv_unsigned (vals_ev vals 39))%Z ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z ->
(bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
(bv_unsigned pp + Z.of_nat (length path) <= 0x800000000000)%Z ->
regs_ok (ENV BL vals) (sr_upd srA (ridx 10) (EVar 39)) R -> know_ok RSEGS (ENV BL vals) M knA ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x6086c) M (seg_rom RSEGS)) model)
(t_die (msg_cannot_open path) (m_fs model)).
Proof.
intros path pp t8 vals R M Hnonul HPl HL P0 P2 P38 Hpp1 Hpp2 HppT HR HK Hstr Ht8.
unfold t_die.
eapply (of_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
try eassumption; try lia.
intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
destruct (Z.le_gt_cases (Z.of_nat (length path)) 62) as [Hle | Hgt].
- eapply (of_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
- destruct (Z.le_gt_cases (Z.of_nat (length path)) 63) as [Hle2 | Hgt2].
+ assert (E63 : Z.of_nat (length path) = 63%Z) by lia. rewrite E63 in Q113.
eapply (of_segF_gen sp0 BL model Hvsp Hh Hlazy path pp 63 _ vals'); try eassumption; try lia.
apply of_segG3. exact E63.
+ eapply (of_segFG4 path pp _ vals'); try eassumption; lia.
Qed.

End Tail2.
End FPGEN1.

