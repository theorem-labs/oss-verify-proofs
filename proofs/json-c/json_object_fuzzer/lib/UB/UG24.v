(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Qnhz Qrxj QRjH Qpox QsV0 Q9ox QBxa Qn1e QiVh QMz4 QO3A Q7m0 QSpR QuJV QCPB QH7x QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC UFeQ Um90 Udbv UWQV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1zM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qpox QsV0 QRjH Q9ox.Mq2 QBxa.Mq4 Qn1e.Mq1 QiVh Qn1e QBxa.Mq0 QMz4 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES.
Import U1oC.
Import QBxa.Mq5 QSpR.Mq0 QSpR.Mq2.
Import UFeQ.Mq0 Um90 U1oC.Mq0.
Import QBxa.Mq3.
Import Udbv UWQV.Mq0.
Import QSjk.Mq0 QBxa.Mq1.
Import U1oC.Mq2 U1zM.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac oom_exit_pre HL P0 MFS :=
lazymatch goal with
| HR : regs_ok ?E ?sr ?R, HK : know_ok _ _ ?M ?kn |- realizes _ (mkCfg _ ?model) _ =>
apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
[ | try rewrite MFS; apply exit_leaf_eq; lia ];
apply ref_exit_Z;
let Ktid := fresh "Ktid" in let Hst := fresh "Hst" in let Htc := fresh "Htc" in
pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
as Ktid; cbn [kentry_ok edenot ev] in Ktid;
lazymatch type of P0 with vals_ev _ 0 = ?sp0 =>
exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x77c00), (bv_unsigned (ev E 5)),
(Z_to_bv 64 0x98348), (Z_to_bv 64 0);
split; [|split; [first [reflexivity | assumption] | split; [first [reflexivity | assumption] |]]];
[ constructor;
[ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
rewrite P0; f_equal; lia
| regv HR (4 : reg); reflexivity
| regv HR (10 : reg); reflexivity
| rewrite u_small by lia; lia
| rewrite u_small by lia; lia
| rewrite u_small by lia;
pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
_ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev] in Hst; rewrite P0 in Hst;
replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
| lit_u; lia
| lit_u; lia
| cbn [ev]; cbn [ev] in Ktid; lia
| lit_u; change (490496 - 168)%Z with 0x77b58%Z;
krd HK 0x77b58%Z 4%nat Htc; rewrite Htc; cbn [ev];
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; cbn [ev] in Ktid; lia);
rewrite Z_to_bv_bv_unsigned; reflexivity
| krd_solve HK
| krd_solve HK
| krd_solve HK
| krd_solve HK
| krd_solve HK
| krd_solve HK
| krd_solve HK
| repeat split; krd_solve HK
| repeat split; krd_solve HK
| krd_solve HK
| exists false; split; krd_solve HK ]
| left; split; [reflexivity|];
exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
end
end.

Ltac oom_stdio_exit HL P0 RES_EQ FD2 MFS :=

lazymatch goal with
| HR : regs_ok ?E _ _, HK : know_ok _ _ _ _ |- _ =>
let En := eval hnf in E in change E with En in HR; change E with En in HK end;
lazymatch goal with
| HR : regs_ok ?E ?sr ?R, HK : know_ok _ _ ?M ?kn |- realizes _ (mkCfg _ ?model) (t_die msg_oom ?fs) =>
lazymatch type of HL with length ?vals = ?nv =>
lazymatch type of P0 with vals_ev _ 0 = ?sp0 =>
lazymatch type of RES_EQ with stdio_call _ _ _ = Some ?res =>
lazymatch E with Env _ ?ebs =>
unfold t_die, W;
apply (stdio_call_sound vals ebs sr kn R M model res [] msg_oom
(t_exit (exit_code 2) fs) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) RES_EQ));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res];
change (Z.of_nat (length msg_oom)) with 19%Z; change (Z.of_nat (@length byte [])) with 0%Z;
[ cbn [edenot]; lia
|
first [ cbn [edenot]; lit_u; lia
| rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia ]
| cbn [edenot]; lia
| cbn [edenot]; lit_u; reflexivity
| lia
| left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
| left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
| cbn [edenot]; lit_u; lia
| reflexivity
| cbn [edenot]; change (length msg_oom) with 19%nat;
rewrite (kimg_rdn RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10d1d 19) in exact i)
_ _ 0x10d1d 19 HK eq_refl) by (cbn; lia);
apply msg_oom_img
| apply FD2
| first [reflexivity | assumption]
| first [reflexivity | assumption]
| apply t_exit_has_nil
| clear HR HK; try clear R M;
let R2 := fresh "R" in let M2 := fresh "M" in
intros R2 M2 HR HK;
let srX := eval vm_compute in (sc_sr res) in change (sc_sr res) with srX in HR;
let knX := eval vm_compute in (sc_kn res) in change (sc_kn res) with knX in HK;
let ret := eval vm_compute in (sc_ret res) in change (sc_ret res) with ret;
let vals2 := fresh "vals" in let HL2 := fresh "HL" in let Q0 := fresh "P0" in
set (vals2 := vals ++ junk_vals R2) in *;
assert (HL2 : length vals2 = (nv + 32)%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity);
cbn [Nat.add] in HL2;
assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
clearbody vals2; clear HL P0;
let NX := eval vm_compute in (nv + 32)%nat in
run_block_gen FUEL STOPS scr0 NX false;
oom_exit_pre HL2 Q0 MFS
] end end end end
end.

End Mq0.
From Stdlib Require String.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN UMOs UqHD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUeZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJvR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 QRjH QBxa.Mq4 QSjk.Mq0 QBxa.Mq1 Q9ox.Mq2 QMz4 Qn1e.Mq1 QiVh Qn1e QBxa.Mq0 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES.Mq0 QBxa.Mq5 QSpR.Mq0.
Import UFeQ.Mq0 Um90 U1oC.Mq0 U1oC.
Import QBxa.Mq3.
Import UeDN UMOs UqHD UFeQ.Mq4 Udbv UWQV.Mq0.
Import QUeZ.
Import UJvR.Mq1.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section Tail.
Context {fF : FPF} {fC : FPC}.
Variable sp0 : word.
Variable BL : list (list byte).
Variable model : Model.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma re_segI : forall vals R M,
length vals = 263%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5559c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 263%nat.

apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
2:{ cbn [W map].
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
apply t_eq_sym. apply t_emit_nil_exit. }
apply ref_exit_Z.
pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
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
pose proof (kwr_store_ok RSEGS (ENV vals) _ knI ltac:(let i := kidx knI (is_kwr_cov (EVar 0) (-272) 144) in exact i)
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

Definition PRE19 : list byte := s2b "cli: read error on "%string.

#[using="Type"] Lemma PRE19_words :
word_to_le_bytes 8 (Z_to_bv 64 7018141077071293539)
++ word_to_le_bytes 8 (Z_to_bv 64 2338053693894893668)
++ word_to_le_bytes 2 (Z_to_bv 64 28271)
++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE19.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma re_segH : forall (path : list byte) (P : Z) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
length vals = 231%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1%nat = Some [Z_to_bv 8 10] ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk_keep scr0 231%nat.

assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
{ unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1 = Some [Z_to_bv 8 10]).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
clear EQM SBp SBn. rename M0 into M'.

krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-544)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
krdv HK 0%nat (-542)%Z 1%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3.
rewrite P0 in Hw0, Hw1, Hw2, Hw3.
assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 19 = Some PRE19).
{ rewrite <- PRE19_words. change 19%nat with (8 + (8 + (2 + 1)))%nat.
apply rdn_app_Z; [exact Hw0 | | lia | lia].
apply rdn_app_Z; [ | | lia | lia].
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
+ apply rdn_app_Z; [ | | lia | lia].
* replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2.
* replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2)%Z with (bv_unsigned sp0 + -542)%Z by lia.
exact Hw3. }
assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (19 + (length path + 1))
= Some (msg_read_error path)).
{ unfold msg_read_error. change (s2b _) with PRE19.
apply rdn_app_Z; [exact H17 | | lia | lia].
apply rdn_app_Z; [| | lia | lia].
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 19)%Z with (bv_unsigned sp0 - 541)%Z by lia. exact SBp'.
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 19 + Z.of_nat (length path))%Z
with (bv_unsigned sp0 - 541 + P)%Z by lia. exact SBn'. }

assert (LEN : length (msg_read_error path) = (19 + (length path + 1))%nat)
by (unfold msg_read_error; rewrite !length_app; reflexivity).
replace (W 2 (msg_read_error path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_read_error path ++ []))
by (unfold W; rewrite app_nil_r; reflexivity).
pose proof itinerary_re as (_ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scRE (msg_read_error path) []
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRE]; rewrite ?LEN end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- cbn [edenot length]. reflexivity.
- cbn [length Z.of_nat]. lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- cbn [edenot]. unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
- reflexivity.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_exit_has_nil.
-
clear HR HK. intros R2 M2 HR HK.
eapply (re_segI (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Type"] Lemma re_nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x12998) 1 = Some [Z_to_bv 8 10].
Proof. vm_compute. reflexivity. Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma re_segG : forall (path : list byte) (P : Z) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk_keep scrG 199%nat.
{
unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
replace (-1 * P + 61)%Z with (61 - P)%Z by lia.
rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
{ unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
clear EQM SBp. rename M0 into M'.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541 + P)).
assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x12998) 1 = Some [Z_to_bv 8 10]).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x12998 1) in exact i)
_ _ 0x12998 1 HK eq_refl) by (cbn; lia). apply re_nl_img. }
assert (Hdst : store_ok RSEGS M' dst 1 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-541) 64) in exact i)
_ _ _ (-541 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 541 + P)%Z with (bv_unsigned sp0 + (-541 + P))%Z by lia. exact Hst. }
assert (MC : mcH M' dst (Z_to_bv 64 0x12998) 1 [Z_to_bv 8 10]).
{ constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12998) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M' dst (Z_to_bv 64 0x12998) 1 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).

lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-541) BUF_HI IHI knG
ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-541) BUF_HI);
cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
(wbytes_grows _ _ _) HK) as HK2.
clear HK. change (kn_cut 0 (-541) BUF_HI IHI knG) with knH0 in HK2.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
eapply (re_segH path P vals1); try eassumption.
-
rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
-
subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 541 + P))) as Hn.
cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
Qed.

Definition reG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
forall vals R M,
length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma re_segF_gen : forall (path : list byte) (pp : word) (P : Z) (T : TSet) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 61)%Z ->
length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
reG0 path P T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros path pp P T vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr HG0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
assert (Psmall : (bv_unsigned (edenot (ENV vals) PX) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV PX]. rewrite P113, u_small by lia. lia. }
unfold PX in Psmall.

run_blk_keep scrF 167%nat.
{
unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
{
unfold sc_denot. cbn [branch_taken].
rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
| cbn [ev ENV]; rewrite P0; lia]. }
clear EQM Hstr. rename M0 into M'.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
{ rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
eapply rdn_firstn; [exact Hstr' | lia]. }
assert (Hdst : store_ok RSEGS M' dst (length path) = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-541) 63) in exact i)
_ _ _ (-541) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 541)%Z with (bv_unsigned sp0 + -541)%Z by lia. exact Hst. }
assert (MC : mcH M' dst pp P path).
{ constructor; subst dst; rewrite ?u_small by lia; try lia.
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).

lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-541) BUF_HI IHI knF
ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-541) BUF_HI);
cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
(wbytes_grows _ _ _) HK) as HK2.
clear HK. change (kn_cut 0 (-541) BUF_HI IHI knF) with knG0 in HK2.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
eapply (HG0 vals1); try eassumption.

subst dst. rewrite <- HP at 1 || idtac.
pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 541))) as Hc.
apply Hc. rewrite u_small by lia. lia.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma re_segF : forall (path : list byte) (pp : word) (P : Z) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr.
eapply (re_segF_gen path pp P _ vals); try eassumption; [lia|].
intros vals' R' M' HL' Q0 Q113 HR' HK' SB. eapply (re_segG path P vals'); eassumption.
Qed.

Definition reF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop :=
forall vals R M,
length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma re_segDE : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
length vals = 103%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
reF0 path pp P T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }

run_blk_keep scr0 103%nat.
assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
| cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
clear EQM Hstr Ht8. rename M0 into M'.

set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
{ rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
- rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
eapply rdn_firstn; [exact Hstr' | lia].
- pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
{ pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
rewrite app_nth2, Nat.sub_diag by lia.
pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
replace (bv_unsigned pp + Z.of_nat (length path))%Z with (bv_unsigned pp + P)%Z in B1 by lia.
replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
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
intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
- lia.
- lia.
- intros i Hi.
pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x13410 24) in exact k) _ HK eq_refl)
as (_ & _ & Hnone). apply Hnone. lia. }
assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
_ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst spS. rewrite u_small by lia.
replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55c3c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A2 : getr Rc 2 = spS)
by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x55c3c : word) MC
ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
ltac:(right; subst spS; rewrite u_small by lia; lia)
ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
clear A1 A2 A10 A11
end.
replace (Z_to_bv 64 392740) with (0x5fe24 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55c3c : word) with (Z_to_bv 64 0x55c3c) by (apply bv_eq; reflexivity).

lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

destruct Hfr as [Hagree Hgrow].
pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI knD
ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
unfold in_rng; subst spS; unorm;
cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
Hgrow HK) as HK2.
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI knD)
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P).
{ subst vals1. change 113%nat with (103 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
assert (HK : know_ok RSEGS (ENV vals1) M2 knE0).
{ unfold knE0. apply know_ok_cons; [|exact HK3].
apply krange_intro. cbn [edenot ev ENV PX]. rewrite Q113, u_small by lia. lia. }
clear HK3.

assert (Hstr2 : rdn RSEGS M2 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 113)) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV]. rewrite Q113, u_small by lia. lia. }

run_blk_keep scrE 135%nat.
{
unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
{
unfold sc_denot. exists [Z_to_bv 8 0]. split.
- unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
ed_lin ltac:(cbn [ev ENV]; rewrite ?Q2, ?Q113). rewrite <- HP.
pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
- reflexivity. }
assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
[exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
| cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
clear EQM Hstr2. rename M0 into M3.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
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
pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knE ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
clear HK. rename HK2 into HK.
set (vals2 := vals1 ++ junk_vals R4) in *.
assert (HL2 : length vals2 = 167%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
assert (W113 : vals_ev vals2 113 = Z_to_bv 64 P) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q113).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
eapply (HF0 vals2); eassumption.
Qed.

#[using="Type"] Lemma pre19_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x12983) 19 = Some PRE19.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma PRE19_len : length PRE19 = 19%nat.
Proof. reflexivity. Qed.

#[using="Hvsp SPlo SPhi"] Lemma re_memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE19.
Proof.
intros vals M P0. pose proof SPlo. pose proof SPhi.
rewrite <- PRE19_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
repeat (f_equal; try (f_equal; lia)).
Qed.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma re_segBC : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) srRE0 R -> know_ok RSEGS (ENV vals) M knRE0 ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
reF0 path pp P T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20db0) M (seg_rom RSEGS)) model) T.
Proof.
intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }

run_blk_keep scr0 39%nat.
assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
| cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
clear EQM Hstr Ht8. rename M0 into M'.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x12983) 19 = Some PRE19).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x12983 19) in exact i)
_ _ 0x12983 19 HK eq_refl) by (cbn; lia). apply pre19_img. }
assert (Hdst : store_ok RSEGS M' dst 19 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 19) in exact i)
_ _ _ (-560) 19 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH M' dst (Z_to_bv 64 0x12983) 19 PRE19).
{ constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12983) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 19) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M' dst (Z_to_bv 64 0x12983) 19 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE19) knC0).
{ subst dst. rewrite <- (re_memcpy1_denot vals M' P0).
eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
[vm_compute; reflexivity | | exact HK | constructor].
cbn [log_flat logM1].
repeat match goal with
| |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
| |- (_ <= _)%nat => lia
| |- True => exact I
| |- _ /\ _ => split
end. }
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE19) knC0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.

assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE19) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
assert (Ht82 : rdn RSEGS (wbytes M' dst PRE19) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
{ rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
set (M1 := wbytes M' dst PRE19) in *. clearbody M1. clear M' dst.
assert (WOKS1 : win_ok (ENV vals1) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite Q0. lia. }

run_blk_keep scr0 71%nat.
assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
[exact Hstr2 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
assert (Ht83 : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
[exact Ht82 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0, u_small by lia; lia
| cbn [ev ENV]; rewrite Q0, u_small by lia; lia]. }
clear EQM Hstr2 Ht82. rename M0 into M3.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
assert (MC : mcH M3 dst (Z_to_bv 64 0x12996) 0 []).
{ constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12996) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M3 dst (Z_to_bv 64 0x12996) 0 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
change (wbytes M3 dst []) with M3.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knC ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
clear HK. rename HK2 into HK.
set (vals2 := vals1 ++ junk_vals R4) in *.
assert (HL2 : length vals2 = 103%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
eapply (re_segDE path pp P T t8 vals2); eassumption.
Qed.

End Tail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QBxa.Mq3.
Import UWQV.Mq0.
Import QqES.Mq0.
Import U1oC UJvR.Mq1.
Import ListNotations. Import SX2. Import SX2S.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

Definition ssB0 : sym_state := SS 0x20dcc srRF0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.

Definition logM1 : list sentry :=
[SE (SA (EVar 0) (-548)) 2 (ELit 8253);
SE (SA (EVar 0) (-552)) 4 (ELit 1042314357);
SE (SA (EVar 0) (-560)) 8 (ELit 8101528366825958499)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

Definition ssC0 : sym_state := SS 0x55024 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

Definition ssD0 : sym_state := SS 0x55024 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

Definition ssE0 : sym_state := SS 0x55024 srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.

Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

Definition ssF0 : sym_state := SS 0x55024 srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
[SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

Definition ssG0 : sym_state := SS 0x55024 srG0 [] knG0 199.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := Eval vm_compute in
match stdio_call 199 srG knG with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

Definition ssH0 : sym_state := SS (sc_ret scRF) srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

#[using="Type"] Lemma itinerary_rf :
(s_pc (fst (fst rB)), snd (fst rB)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x551dc%Z, [])
/\ stdio_call 199 srG knG = Some scRF
/\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0x5559c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
/\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x50e6c%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPGEN1.

End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QBxa.Mq3.
Import UWQV.Mq0.
Import QqES.Mq0.
Import U1oC UJvR.Mq0.
Import U1oC.Mq1.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition u_ssA0 : sym_state := SS 0x20b84 sr_mainN [] kn_mainN 39.
Definition u_scrA : scripts := SCR [true] [] [].
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.

Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 39.

Definition u_ssB0 : sym_state := SS 0x55024 u_srB0 [] u_knB0 71.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 71.

Definition u_ssC0 : sym_state := SS 0x55024 u_srC0 [] u_knB 103.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 113.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 103.

Definition u_ssD0 : sym_state := SS 0x55c3c u_srD0 [] u_knD0 135.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 135.

Definition u_ssE0 : sym_state := SS 0x55024 u_srE0 [] u_knD 167.
Definition u_scrE : scripts := SCR [true; true] [] [].
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 167.

Definition u_ssF0 : sym_state := SS 0x55024 u_srF0 [] u_knF0 199.
Definition u_scrF : scripts := SCR [true] [] [].
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 199.

Definition u_ssG0 : sym_state := SS 0x55024 u_srG0 [] u_knG0 231.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 231 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.

Definition u_ssH0 : sym_state := SS 0x5559c u_srH0 [] u_knH0 263.
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.
Definition u_srH : list expr := Eval vm_compute in s_regs (fst (fst u_rH)).
Definition u_knH : list kentry := Eval vm_compute in kn_after u_rH u_knH0.

Definition u_scrF3 : scripts := SCR [false] [] [].
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 199 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.

Definition u_ssG30 : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 231.
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 231 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.

Definition u_ssH30 : sym_state := SS 0x5559c u_srH30 [] u_knH30 263.
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.
Definition u_srH3 : list expr := Eval vm_compute in s_regs (fst (fst u_rH3)).
Definition u_knH3 : list kentry := Eval vm_compute in kn_after u_rH3 u_knH30.

Definition u_scrE4 : scripts := SCR [true; false] [] [].
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 167 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.

Definition u_ssF40 : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 199.
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.

Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 199.

Definition u_ssG40 : sym_state := SS 0x55024 u_srG40 [] u_knG40 231.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 231 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.

Definition u_ssH40 : sym_state := SS 0x5559c u_srH40 [] u_knH40 263.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

#[using="Type"] Lemma u_itinerary :
(s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0x5f438%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
/\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0x5fe24%Z, [])
/\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
= (0x5f438%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
/\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
= (0x5f438%Z, [SCBr true BC_GEU (ELit 73) LX;
SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
/\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
= (0x5f438%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
/\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0x551dc%Z, [])
/\ stdio_call 231 u_srG u_knG = Some u_scG
/\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0x5559c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
/\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0x50e6c%Z, [])
/\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
= (0x551dc%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
/\ stdio_call 199 u_srF3 u_knF3 = Some u_scF3
/\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0x5576c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x110b8, ELit 7)
/\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0x551dc%Z, [])
/\ stdio_call 231 u_srG3 u_knG3 = Some u_scG3
/\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0x5559c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
/\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0x50e6c%Z, [])
/\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
= (0x551dc%Z, [SCBr false BC_GEU (ELit 73) LX;
SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
/\ stdio_call 167 u_srE4 u_knE4 = Some u_scE4
/\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0x5618c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
/\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0x551dc%Z, [])
/\ stdio_call 231 u_srG4 u_knG4 = Some u_scG4
/\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0x5559c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
/\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0x50e6c%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPGEN1.

End Mq3.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJvR.Mq0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section Tail.
Context {fF : FPF} {fC : FPC}.
Variable sp0 : word.
Variable BL : list (list byte).
Variable model : Model.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segI : forall vals R M,
length vals = 264%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x5559c) M (seg_rom RSEGS)) model)
(t_exit (exit_code 2) (m_fs model)).
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 264%nat.

apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
2:{ cbn [W map].
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
apply t_eq_sym. apply t_emit_nil_exit. }
apply ref_exit_Z.
pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
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
pose proof (kwr_store_ok RSEGS (ENV vals) _ knI ltac:(let i := kidx knI (is_kwr_cov (EVar 0) (-272) 144) in exact i)
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

Definition PRE17 : list byte := s2b "cli: cannot open "%string.

#[using="Type"] Lemma PRE17_words :
word_to_le_bytes 8 (Z_to_bv 64 7953747406983097443)
++ word_to_le_bytes 8 (Z_to_bv 64 7954887939408031598)
++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE17.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segH : forall (path : list byte) (P : Z) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
length vals = 232%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 114 = Z_to_bv 64 P ->
regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543 + P)) 1%nat = Some [Z_to_bv 8 10] ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk_keep scr0 232%nat.

assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
{ unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543 + P)) 1 = Some [Z_to_bv 8 10]).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
clear EQM SBp SBn. rename M0 into M'.

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
assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + (length path + 1))
= Some (msg_cannot_open path)).
{ unfold msg_cannot_open. change (s2b _) with PRE17.
apply rdn_app_Z; [exact H17 | | lia | lia].
apply rdn_app_Z; [| | lia | lia].
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'.
+ replace (bv_unsigned sp0 + -560 + Z.of_nat 17 + Z.of_nat (length path))%Z
with (bv_unsigned sp0 - 543 + P)%Z by lia. exact SBn'. }

assert (LEN : length (msg_cannot_open path) = (17 + (length path + 1))%nat)
by (unfold msg_cannot_open; rewrite !length_app; reflexivity).
replace (W 2 (msg_cannot_open path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_cannot_open path ++ []))
by (unfold W; rewrite app_nil_r; reflexivity).
pose proof itinerary_le62 as (_ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scOF (msg_cannot_open path) []
(t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scOF]; rewrite ?LEN end.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- cbn [edenot length]. reflexivity.
- cbn [length Z.of_nat]. lia.
- right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
- cbn [edenot]. unorm. lia.
- ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
- reflexivity.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- apply t_exit_has_nil.
-
clear HR HK. intros R2 M2 HR HK.
eapply (of_segI (vals ++ junk_vals R2));
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| exact HR | exact HK ].
Qed.

#[using="Type"] Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x12981) 1 = Some [Z_to_bv 8 10].
Proof. vm_compute. reflexivity. Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segG : forall (path : list byte) (P : Z) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
length vals = 200%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 114 = Z_to_bv 64 P ->
regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

run_blk_keep scrG 200%nat.
{
unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
replace (-1 * P + 63)%Z with (63 - P)%Z by lia.
rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
{ unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
[exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
| cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
clear EQM SBp. rename M0 into M'.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543 + P)).
assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x12981) 1 = Some [Z_to_bv 8 10]).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x12981 1) in exact i)
_ _ 0x12981 1 HK eq_refl) by (cbn; lia). apply nl_img. }
assert (Hdst : store_ok RSEGS M' dst 1 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-543) 64) in exact i)
_ _ _ (-543 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 543 + P)%Z with (bv_unsigned sp0 + (-543 + P))%Z by lia. exact Hst. }
assert (MC : mcH M' dst (Z_to_bv 64 0x12981) 1 [Z_to_bv 8 10]).
{ constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12981) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M' dst (Z_to_bv 64 0x12981) 1 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).

lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-543) BUF_HI IHI knG
ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-543) BUF_HI);
cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
(wbytes_grows _ _ _) HK) as HK2.
clear HK. change (kn_cut 0 (-543) BUF_HI IHI knG) with knH0 in HK2.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 232%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q113 : vals_ev vals1 114 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
eapply (of_segH path P vals1); try eassumption.
-
rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
-
subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 543 + P))) as Hn.
cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
Qed.

Definition atG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
forall vals R M,
length vals = 200%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 114 = Z_to_bv 64 P ->
regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segF_gen : forall (path : list byte) (pp : word) (P : Z) (T : TSet) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 63)%Z ->
length vals = 168%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 114 = Z_to_bv 64 P ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
atG0 path P T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros path pp P T vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr HG0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
assert (Psmall : (bv_unsigned (edenot (ENV vals) PX) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV PX]. rewrite P113, u_small by lia. lia. }
unfold PX in Psmall.

run_blk_keep scrF 168%nat.
{
unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
{
unfold sc_denot. cbn [branch_taken].
rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
| cbn [ev ENV]; rewrite P0; lia]. }
clear EQM Hstr. rename M0 into M'.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
{ rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
eapply rdn_firstn; [exact Hstr' | lia]. }
assert (Hdst : store_ok RSEGS M' dst (length path) = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-543) 63) in exact i)
_ _ _ (-543) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 543)%Z with (bv_unsigned sp0 + -543)%Z by lia. exact Hst. }
assert (MC : mcH M' dst pp P path).
{ constructor; subst dst; rewrite ?u_small by lia; try lia.
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).

lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-543) BUF_HI IHI knF
ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-543) BUF_HI);
cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
(wbytes_grows _ _ _) HK) as HK2.
clear HK. change (kn_cut 0 (-543) BUF_HI IHI knF) with knG0 in HK2.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 200%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q113 : vals_ev vals1 114 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
eapply (HG0 vals1); try eassumption.

subst dst. rewrite <- HP at 1 || idtac.
pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 543))) as Hc.
apply Hc. rewrite u_small by lia. lia.
Qed.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segF : forall (path : list byte) (pp : word) (P : Z) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
length vals = 168%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 114 = Z_to_bv 64 P ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model)
(t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr.
eapply (of_segF_gen path pp P _ vals); try eassumption; [lia|].
intros vals' R' M' HL' Q0 Q113 HR' HK' SB. eapply (of_segG path P vals'); eassumption.
Qed.

Definition atF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop :=
forall vals R M,
length vals = 168%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 114 = Z_to_bv 64 P ->
regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segDE : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
length vals = 104%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
atF0 path pp P T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x55024) M (seg_rom RSEGS)) model) T.
Proof.
intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }

run_blk_keep scr0 104%nat.
assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
| cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
clear EQM Hstr Ht8. rename M0 into M'.

set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
{ rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
- rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
eapply rdn_firstn; [exact Hstr' | lia].
- pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
{ pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
rewrite app_nth2, Nat.sub_diag by lia.
pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
replace (bv_unsigned pp + Z.of_nat (length path))%Z with (bv_unsigned pp + P)%Z in B1 by lia.
replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
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
intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
- lia.
- lia.
- intros i Hi.
pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x13410 24) in exact k) _ HK eq_refl)
as (_ & _ & Hnone). apply Hnone. lia. }
assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
_ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst spS. rewrite u_small by lia.
replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55c3c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A2 : getr Rc 2 = spS)
by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x55c3c : word) MC
ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
ltac:(right; subst spS; rewrite u_small by lia; lia)
ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
clear A1 A2 A10 A11
end.
replace (Z_to_bv 64 392740) with (0x5fe24 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55c3c : word) with (Z_to_bv 64 0x55c3c) by (apply bv_eq; reflexivity).

lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

destruct Hfr as [Hagree Hgrow].
pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI knD
ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
unfold in_rng; subst spS; unorm;
cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
Hgrow HK) as HK2.
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI knD)
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 136%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
assert (Q113 : vals_ev vals1 114 = Z_to_bv 64 P).
{ subst vals1. change 114%nat with (104 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
assert (HK : know_ok RSEGS (ENV vals1) M2 knE0).
{ unfold knE0. apply know_ok_cons; [|exact HK3].
apply krange_intro. cbn [edenot ev ENV PX]. rewrite Q113, u_small by lia. lia. }
clear HK3.

assert (Hstr2 : rdn RSEGS M2 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 114)) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV]. rewrite Q113, u_small by lia. lia. }

run_blk_keep scrE 136%nat.
{
unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
{
unfold sc_denot. exists [Z_to_bv 8 0]. split.
- unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
ed_lin ltac:(cbn [ev ENV]; rewrite ?Q2, ?Q113). rewrite <- HP.
pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
- reflexivity. }
assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
[exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
| cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
clear EQM Hstr2. rename M0 into M3.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
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
pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knE ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
clear HK. rename HK2 into HK.
set (vals2 := vals1 ++ junk_vals R4) in *.
assert (HL2 : length vals2 = 168%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
assert (W113 : vals_ev vals2 114 = Z_to_bv 64 P) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q113).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
eapply (HF0 vals2); eassumption.
Qed.

#[using="Type"] Lemma pre17_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1296e) 17 = Some PRE17.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma PRE17_len : length PRE17 = 17%nat.
Proof. reflexivity. Qed.

#[using="Hvsp SPlo SPhi"] Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE17.
Proof.
intros vals M P0. pose proof SPlo. pose proof SPhi.
rewrite <- PRE17_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
repeat (f_equal; try (f_equal; lia)).
Qed.

#[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segBC : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
(2 ^ 64 - 4095 <= bv_unsigned (vals_ev vals 39))%Z ->
(bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 39)) R -> know_ok RSEGS (ENV vals) M knA ->
rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
atF0 path pp P T ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x6086c) M (seg_rom RSEGS)) model) T.
Proof.
intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 P38 Hpp1 Hpp2 HR HK0 Hstr Ht8 HF0.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
pose proof (u64_range (vals_ev vals 39)) as H38r.
assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
assert (HK : know_ok RSEGS (ENV vals) M knB0).
{ unfold knB0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK0]].
- apply krange_intro. cbn [edenot ev ENV]. rewrite P2. lia.
- apply krange_intro. cbn [edenot ev ENV]. lia. }
clear HK0. change (sr_upd srA (ridx 10) (EVar 39)) with srB0 in HR.

run_blk_keep scrB 40%nat.
{
unfold sc_denot. cbn [branch_taken]. rewrite edenot_addw0_errno by (cbn [edenot ev ENV]; lia).
cbn [edenot ev ENV]. unfold bv_ltu. rewrite (u_small 18446744073709547521) by lia.
apply (proj2 (Z.ltb_ge _ _)). lia. }
assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
[exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
| cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
clear EQM Hstr Ht8. rename M0 into M'.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x1296e) 17 = Some PRE17).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x1296e 17) in exact i)
_ _ 0x1296e 17 HK eq_refl) by (cbn; lia). apply pre17_img. }
assert (Hdst : store_ok RSEGS M' dst 17 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 17) in exact i)
_ _ _ (-560) 17 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH M' dst (Z_to_bv 64 0x1296e) 17 PRE17).
{ constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x1296e) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 17) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M' dst (Z_to_bv 64 0x1296e) 17 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.

assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE17) knC0).
{ subst dst. rewrite <- (memcpy1_denot vals M' P0).
eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
[vm_compute; reflexivity | | exact HK | constructor].
cbn [log_flat logM1].
repeat match goal with
| |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
| |- (_ <= _)%nat => lia
| |- True => exact I
| |- _ /\ _ => split
end. }
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE17) knC0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 72%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.

assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE17) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE17_len; unorm; lia. }
assert (Ht82 : rdn RSEGS (wbytes M' dst PRE17) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
{ rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE17_len; unorm; lia. }
clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
set (M1 := wbytes M' dst PRE17) in *. clearbody M1. clear M' dst.
assert (WOKS1 : win_ok (ENV vals1) 0 0 4194304 IHI).
{ unfold win_ok, IHI. cbn [ev ENV]. rewrite Q0. lia. }

run_blk_keep scr0 72%nat.
assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
[exact Hstr2 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
assert (Ht83 : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
{ rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
[exact Ht82 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0, u_small by lia; lia
| cbn [ev ENV]; rewrite Q0, u_small by lia; lia]. }
clear EQM Hstr2 Ht82. rename M0 into M3.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
assert (MC : mcH M3 dst (Z_to_bv 64 0x1297f) 0 []).
{ constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x1297f) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1297f) 0 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
change (wbytes M3 dst []) with M3.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knC ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
clear HK. rename HK2 into HK.
set (vals2 := vals1 ++ junk_vals R4) in *.
assert (HL2 : length vals2 = 104%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
eapply (of_segDE path pp P T t8 vals2); eassumption.
Qed.

End Tail.
