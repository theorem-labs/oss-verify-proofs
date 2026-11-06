(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Hoare Frame ShapeLaws SpecConsts
MmapSim AllocSim FileSim AgentLib
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
Spec LibWritev Js0ExitBase Js0StdioDefs Js0Exit Js0LibStdioCall RefMemcpyLib Js0MemcpyBase Js0Memcpy Js0Memchr Js0Strnlen
Js0Startup Js0MainEntry LibTail.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0OpenFail_defs Js0OpenFail_tail.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0OpenFail_tail2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0OpenFail_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0OpenFail_tail."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BL"; "1O"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2not"; "3add"; "4Z"]; ["5word_to_le_bytes"; "6mkCfg"; "7m_fs"; "8bvmap"; "0M"; "0P"; "0R"; "9knA"; "9knE"; "9knH30"; "9knH40"; "9knI30"; "9knI40"; "9srA"; "9srF0"; "9srH30"]; ["9srH40"; "9srI30"; "9srI40"; ":ENV"; ":atG0"; ";mkst"; ";rdn"; ";seg_rom"; "<t_emit"; "<t_exit"; "=W"; "=exit_code"; "=msg_cannot_open"; "=t_die"; ">srealizes"; "?EVar"]; ["?ridx"; "?sr_upd"; "@know_ok"; "@regs_ok"; "Avals_ev"; "Bloaded_segments"; "CIn"; "Dadd"; "Dle"; "Dof_nat"; "Dpow"; "Dsub"; "0fx"; "0model"; "0path"; "0pp"]; ["0scfg"; "0sp0"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0t8"; "0vals"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac close_exit HR HK P0 Hh Hlazy sp0 :=
lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
lazymatch goal with |- srealizes _ ?scfg (mkCfg _ ?model) _ =>
apply (srz_conseq segs scfg _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
[ | cbn [W map];
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
apply t_eq_sym; apply t_emit_nil_exit ];
apply ref_exit_Z;
let Ktid := fresh "Ktid" in
pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
lazymatch type of HR with regs_ok _ _ ?Rc =>
exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0xc7c60), (bv_unsigned (ev E 5)),
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
| lit_u; change (818272 - 168)%Z with 0xc7bb8%Z;
let Htc := fresh "Htc" in
krd HK 0xc7bb8%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
rewrite Z_to_bv_bv_unsigned; reflexivity
| krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | (exists 0%nat; split; krd_solve HK) | krd_solve HK
| repeat split; krd_solve HK
| repeat split; krd_solve HK ]
| left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
end end end.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Tail2.
Context {RE : RunEnv}.
Variable sp0 : word.
Variable BL : list (list byte).
Variable model : Model.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Section SE.
Local Abbreviation SEC_T_of_segI3 := (ltac2:(TCodec.tc2 tcn__Js0OpenFail_tail2 "R3'6'R4yR0%211%411&Cy5%2214'9y8%911%311p091'<'7&5r3%22>1uX7%63521&QDr4(1%3221vR1%<3F21&QC&Q3v0r5%3221&Q1%6321;&QB&QEr6%9281&K%5442A1'Q>vR0(A&Q5vQL&R3+cjW4%22Q<1&Q7%11>%756>3D1vQM%:221&Q9&Q;+2%211&B%117%6231%D4IC81p0F1p0M1p0Q51p0Q<1pQ:QD1pQ>QJ1pT@QN1")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_of_segI3) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_of_segI3) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_of_segI3) 2%nat 0%nat).
Lemma of_segI3 : ltac:(sec_stmt2 constr:(SEC_T_of_segI3) 3%nat 0%nat).
Proof.
intros HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 263%nat.
close_exit HR HK P0 Hh Hlazy sp0.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_of_segH3 := (ltac2:(TCodec.tc2 tcn__Js0OpenFail_tail2 "R3'6'R4yR0%211%411&Cy5%2214'9y8%911%311p091'<'7&5r3%22>1uW7%63521&QDr4(1%3221vR1%<3F21&QC&Q3v0r5%3221&O%6321;&QB&QEr6%9281&I%5442A1'Q>vR0(A&Q5vQL&R3+cjeD%22Q<1&Q7%11>%756>3D1vQM%:221&Q9&Q;+2%211&B%117%6231%D4IC81p0F1p0M1p0Q51p0Q<1pQ:QD1pQ>QJ1pT@QN1")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_of_segH3) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_of_segH3) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_of_segH3) 2%nat 0%nat).
Lemma of_segH3 : ltac:(sec_stmt2 constr:(SEC_T_of_segH3) 3%nat 0%nat).
Proof.
intros HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 231%nat.
apply (srz_conseq RSEGS scfg _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound scfg vals (blobs_ev BL) srH3 knH3 Rc Mc model scH3 [] []
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
End SE.
Section SE.
Variables (path : list byte).
Lemma of_segG3 : Z.of_nat (length path) = 63%Z ->
atG0 scfg sp0 BL model path 63 (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
Proof.
intros HP vals R M HL P0 P113 HR HK SBp.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk_keep scrG3 199%nat.
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
assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x12b3e) 1 = Some [Z_to_bv 8 10]).
{ rewrite (kimg_rdn RSEGS (ENV BL vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x12b3e 1) in exact i)
_ _ 0x12b3e 1 HK eq_refl) by (cbn; lia). apply nl_img. }
unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
pose proof itinerary_63_64 as (_ & SC & _).
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound scfg vals (blobs_ev BL) srG3 knG3 Rc Mc model scG3 (PRE17 ++ path) [Z_to_bv 8 10]
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
End SE.
Lemma NL_word : ltac2:(TCodec.tc2 tcn__Js0OpenFail_tail2 "C'<'6'R4y8%211%411&@u1&R3yR0+:%3221%6251(4%62;4(8%11<%43=31%B3=61").
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma of_segI4 : ltac2:(TCodec.tc2 tcn__Js0OpenFail_tail2 "R3'6'R4yR0%211%411&Cy5%2214'9y8%911%311p091'<'7&5r3%22>1uX7%63521&QDr4(1%3221vR1%<3F21&QC&Q3v0r5%3221&Q2%6321;&QB&QEr6%9281&L%5442A1'Q>vR0(A&Q5vQL&R3+cjW4%22Q<1&Q7%11>%756>3D1vQM%:221&Q9&Q;+2%211&B%117%6231%D4IC81p0F1p0M1p0Q51p0Q<1pQ:QD1pQ>QJ1pT@QN1").
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 263%nat.
close_exit HR HK P0 Hh Hlazy sp0.
Qed.
Lemma of_segH4 : ltac2:(TCodec.tc2 tcn__Js0OpenFail_tail2 "R='6'R4yR0%211%411&Cy5%2214'9y8%911%311p091'<'7&5r3%22>1uW7%63521&QDr4(1%3221vR1%<3F21&QC&Q3v0r5%3221&Q0%6321;&QB&QEr6%9281&J%5442A1'Q>vR0(A&Q5vQL&R3+ciPD%22Q<1&Q7%11>%756>3D1vQM%:221&Q8&Q:+2(4+:%=2Q@1(8%11QA%53QB31%8271&Q9&Q;%11:&B%11@%5231%@271%N4Q3MB1p0Q01p0Q71p0Q?1p0QF1pQ:QN1pQ>R41pT@R81").
Proof.
intros vals R M HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 231%nat.
krdv HK 0%nat (-560)%Z 1%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
rewrite NL_word in Hb.
unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound scfg vals (blobs_ev BL) srH4 knH4 Rc Mc model scH4 [Z_to_bv 8 10] []
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
Section SE.
Local Abbreviation SEC_T_of_segFG4 := (ltac2:(TCodec.tc2 tcn__Js0OpenFail_tail2 "TD'6'R4y8%211%411yR0%511'?%812&Cy5%2215'9%11:p081'<&QI&5r6%22@1%411r4%73?21';&QH+R0r5%3221+SooO%5231%7231'7%?2J6uU7%C3321&QD(1%22C1vR1%H3Q121r7u2%7221r9%M3Q621r8uSA%<221&R3%12Q<6%Q33Q<31&R5%12Q?>r;%32QA1%O231&QGr<%72QE1%3216+8%5221+TPPP0%72;1%Q8231r=%?2QM1%;21:%<218+TPPPPPPPP0%Q>221&QC&Q3v0%221A&N%5321G&QB&QE%726>&H%4432L1%R61R>&Q6r@&>rA%R62RD1u1%4221%74<Q161(2&3(4z%Q?2RM1(8%11RN%53RO31%73S0=1%92S01%RF3C;1'Q>vR0(A&Q5vQLr>+ciPD%QM2S81&Q7%11Q1%75653Q?1vQM%:221&Q8&Q:+2&Q<rB%211%5241&Q9&Q;%117&B%11=%5231%=271%K4QCJ?1p0M1p0QB1p0QH1p0QO1p0R61p0R@1p0RF1p0RM1p0S31p0S91p0S>1p0SG1pQ:T01pQ>T41pT@T81pQ<T:1pT0T<1pSNT?1")) (only parsing).
Variable path : ltac:(sec_ty2 constr:(SEC_T_of_segFG4) 0%nat 0%nat).
Variable pp : ltac:(sec_ty2 constr:(SEC_T_of_segFG4) 1%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_of_segFG4) 2%nat 0%nat).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_of_segFG4) 3%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_of_segFG4) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_of_segFG4) 5%nat 0%nat).
Lemma of_segFG4 : ltac:(sec_stmt2 constr:(SEC_T_of_segFG4) 6%nat 0%nat).
Proof.
intros HP HPr HL P0 P2 P113 Hpp1 Hpp2 Hpp3 HR HK Hstr.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
assert (Psmall : (bv_unsigned (edenot (ENV BL vals) (EVar 113)) < 2 ^ 31)%Z).
{ cbn [edenot ev ENV]. rewrite P113, u_small by lia. lia. }
run_blk_keep scrF4 167%nat.
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
apply (srz_conseq RSEGS scfg _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))))).
2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
apply t_eq_sym. apply t_emit_app. }
unfold W at 1.
pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound scfg vals (blobs_ev BL) srF4 knF4 Rc Mc model scF4 PRE17 path
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
assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
run_blk scr0 199%nat.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x12b3e) 1 = Some [Z_to_bv 8 10]).
{ rewrite (kimg_rdn RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x12b3e 1) in exact i)
_ _ 0x12b3e 1 HK eq_refl) by (cbn; lia). apply nl_img. }
assert (Hdst : store_ok RSEGS MG dst 1 = true).
{ pose proof (kwr_store_ok RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-560) 1) in exact i)
_ _ _ (-560) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH MG dst (Z_to_bv 64 0x12b3e) 1 [Z_to_bv 8 10]).
{ constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
- exact Hnl.
- exact Hdst. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x9e414 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12b3e) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy MG dst (Z_to_bv 64 0x12b3e) 1 _ (seg_rom RSEGS) MC Rc (0x9e414 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 692576) with (0xa9160 : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x9e414 : word) with (Z_to_bv 64 0x9e414) by (apply bv_eq; reflexivity).
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
assert (HL2 : length vals2 = 231%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
clearbody vals2.
change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR, HK.
eapply (of_segH4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
Qed.
End SE.
Theorem of_tail : ltac2:(TCodec.tc2 tcn__Js0OpenFail_tail2 "U;'6'R4y8%211%411yR0%511%711&Cy5%2214'9%119p071&=&QF&R3z%22@1r6%53A21%711&QH&QI&5r7%22G1%411+SooO%7221'<'7r5%92K1uQ7%53421&QD(1%22C1vR1%:3Q221u2%62A1r9%>3Q621&QK&QJ+2+R0%3221+SoO%6221&R5r8uQ6%C221%42QC1%Q3261%62QECr;%82QG1%Q7231&QGr<%<2QK1r=%Q:2QO1%Q<11%6241+8%8221+TPPP0%:2>1%QC231%F2R59r>%QD2R91%QF11%@241%A21:+TPPPPPPPP0%QK221&QC&Q3v0%221F&QA&M&Q@(R2+:(:%33RC21%511(Q?%11Q9%:3931%?3<1Q6&QB&QE%A2@Q3&G%4432Q;1%RL1S3&Q6r@&>rA%RD2S91u1%4221%74<Q@61(2&3(4(8%11SA%33SBS31%53SC;1%72SC1%RJ3A91%R52SD>rB%S32SH1%S511%QO241%S>2SI1u8%H4MQO21%A2SMH%S43K21'Q>vR0(A&Q5vQLr?+eXX<%SJ2T51&Q7%11Q9%75653R21vQM%:221&Q=&Q<rC%211&B%117%6231%D4QDC81p0F1p0Q11p0QD1p0QJ1p0R;1p0RD1p0S11p0S61p0SD1p0SI1p0SO1p0T61p0T?1pQ:TH1pQ>TL1pT@U01pT>U41pT0U31pSNU61").
Proof.
intros path pp t8 vals R M Hnonul HPl HL P0 P2 P38 Hpp1 Hpp2 Hpp3 HR HK Hstr Ht8.
unfold t_die.
eapply (of_segBC scfg sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
try eassumption; try lia.
intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
destruct (Z.le_gt_cases (Z.of_nat (length path)) 62) as [Hle | Hgt].
- eapply (of_segF scfg sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
- destruct (Z.le_gt_cases (Z.of_nat (length path)) 63) as [Hle2 | Hgt2].
+ assert (E63 : Z.of_nat (length path) = 63%Z) by lia. rewrite E63 in Q113.
eapply (of_segF_gen scfg sp0 BL model Hvsp Hh Hlazy path pp 63 _ vals'); try eassumption; try lia.
apply of_segG3. exact E63.
+ eapply (of_segFG4 path pp _ vals'); try eassumption; lia.
Qed.
End Tail2.
End FPX_1.
