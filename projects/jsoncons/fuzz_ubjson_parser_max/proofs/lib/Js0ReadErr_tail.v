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
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
Spec LibWritev Js0ExitBase Js0StdioDefs Js0Exit Js0LibStdioCall RefMemcpyLib Js0MemcpyBase Js0Memcpy Js0Memchr Js0Strnlen
Js0Startup Js0MainEntry LibTail.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0ReadErr_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0ReadErr_tail () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0ReadErr_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0ReadErr_tail.FPX_1.Tail."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2not"; "3add"; "4Z"; "5word_to_le_bytes"]; ["6mkCfg"; "7m_fs"; "8bvmap"; "0M"; "0P"; "0R"; "9wbytes"; ":knC"; ":knE"; ":knG0"; ":knH0"; ":knI0"; ":knRE0"; ":logM1"; ":srD0"; ":srF0"]; [":srG0"; ":srH0"; ":srI0"; ":srRE0"; ";ENV"; ";PRE19"; ";reF0"; ";reG0"; "<mkst"; "<rdn"; "<seg_rom"; "=TSet"; "=t_emit"; "=t_exit"; ">W"; ">exit_code"]; [">msg_read_error"; "?srealizes"; "@know_ok"; "@mem_denot"; "@regs_ok"; "Avals_ev"; "Bloaded_segments"; "CIn"; "Dadd"; "Dle"; "Dof_nat"; "Dsub"; "0T"; "0fx"; "0model"; "0path"]; ["0pp"; "0scfg"; "0sp0"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0t8"; "0vals"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Tail.
Context {RE : RunEnv}.
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
Section SE.
Local Abbreviation SEC_T_re_segI := (ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "R2'6'R4yR0%211%411&By5%2214'9y8%911%311p091';'7&5r3%22>1uX7%63521&QEr4(1%3221vR2%<3F21&QD&Q4r5%211&Q2%5321:&QB&QFr6%811&K%5442@1'QAvR1(@&Q8vQM&R3+cjW4%22Q;1&Q:%11>%756>3D1vQN%:221&Q=&Q?+2%211&A%117%6231%D4IC81p0F1p0M1p0Q41p0Q;1pQ8QC1pQ<QI1pT@QM1")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_re_segI) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_re_segI) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_re_segI) 2%nat 0%nat).
Lemma re_segI : ltac:(sec_stmt2 constr:(SEC_T_re_segI) 3%nat 0%nat).
Proof.
intros HL P0 HR HK.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
run_blk scr0 263%nat.
apply (srz_conseq RSEGS scfg _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
2:{ cbn [W map].
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
apply t_eq_sym. apply t_emit_nil_exit. }
apply ref_exit_Z.
pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0xc7c60), (bv_unsigned (vals_ev vals 5)),
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
* lit_u. change (818272 - 168)%Z with 0xc7bb8%Z.
krd HK 0xc7bb8%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
rewrite Z_to_bv_bv_unsigned. reflexivity.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* krd_solve HK.
* exists 0%nat; split; krd_solve HK.
* krd_solve HK.
* repeat split; krd_solve HK.
* repeat split; krd_solve HK.
+ left. split; [reflexivity|].
exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
Qed.
End SE.
Definition PRE19 : list byte := s2b "cli: read error on "%string.
Lemma PRE19_words : ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "N';'6'R4y8%211%411&3&?u8&R3yR0+VRi[bTPmVbkS3%3221%6251+RPlc_^YiVZXS4%6251%9281u2+kc?%:291%=231u1+Q0%>2=1%A231%C3E51%D3F:1%E3G>1&Q5%M3H21").
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_re_segH := (ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "T0'6'R4y8%211%411'>yR0%611%811&By5%2214'9%11:p071';&QJ&5r5%22@1%411r4%73A21':&QIz%2218+QL%42:1%6231'7%>2H=uW7%B3321&QEr6(1%3221vR2%H3Q021r7uSA%8221&R3r8%22Q71%O3Q741&QD&Q4%115&Q1%4321;&QB&QFr9%711&J%5442A1%Q>1QF&Q9&QK&R5%12QHH+`M%4221%F2QK1r<%QB2R01%94?H31(2%12R24%QH3=31&QH%1297%O2R41u1%A4GF21(4+:%Q42R=1(8%11R>%53R?31%>2R?1%R53J81'QAvR1(@&Q8vQMr;+ciPD%QA2RF1r:&Q:%11Q:%8576431vQN%;221&Q<&Q>+2&Q@r>%211%5241&Q=&Q?%117&A%11=%5231%=271%L4QLK?1p0N1p0Q<1p0QK1p0R21p0R81p0R@1p0RG1p0RL1p0S41pQ8S=1pQ<SA1pT@SE1pQ:SI1pT0SK1")) (only parsing).
Variable path : ltac:(sec_ty2 constr:(SEC_T_re_segH) 0%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_re_segH) 1%nat 0%nat).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_re_segH) 2%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_re_segH) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_re_segH) 4%nat 0%nat).
Lemma re_segH : ltac:(sec_stmt2 constr:(SEC_T_re_segH) 5%nat 0%nat).
Proof.
intros HP HPr HL P0 P113 HR HK SBp SBn.
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
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
apply (stdio_call_sound scfg vals (blobs_ev BL) srH knH Rc Mc model scRE (msg_read_error path) []
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
End SE.
Lemma re_nl_img : ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "M';'9'6'R4y8%211%411%611&Q9&QFyR0%811(0%118q031&R3+RZjE%2271u1%;4:521(2(4+:%82C1(8%11D%53E31%72E1%L3E91").
Proof. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_re_segG := (ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "SA'6'R4y8%211%411'>yR0%611%811&By5%2214'9%11:p071';&QJ&5r5%22@1%411r4%73A21':&QIz%2218+QL%42:1%6231'7%>2H=uV7%B3321&QEr6(1%3221vR2%H3Q021r7uSA%8221&R3r8%22Q71%O3Q741&QD&Q4%115&Q0%4321;&QB&QFr9%711&I%5442A1%Q>1QF&Q9&QK&R5%12QHH+`M%4221%F2QK1r<%QB2R01%94?H31(2%12R24%QH3=31'QAvR1(@&Q8vQMr:+ciPD%Q42R91&Q:%11L%75653L1vQN%:221&Q<&Q>+2&Q@r=%211%5241&Q=&Q?%117&A%11=%5231%=271%K4Q>J?1p0M1p0Q<1p0QC1p0QI1p0R11p0R81p0R=1p0RE1pQ8RN1pQ<S21pT@S61pQ:S:1pT0S<1")) (only parsing).
Variable path : ltac:(sec_ty2 constr:(SEC_T_re_segG) 0%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_re_segG) 1%nat 0%nat).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_re_segG) 2%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_re_segG) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_re_segG) 4%nat 0%nat).
Lemma re_segG : ltac:(sec_stmt2 constr:(SEC_T_re_segG) 5%nat 0%nat).
Proof.
intros HP HPr HL P0 P113 HR HK SBp.
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
assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x12b55) 1 = Some [Z_to_bv 8 10]).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x12b55 1) in exact i)
_ _ 0x12b55 1 HK eq_refl) by (cbn; lia). apply re_nl_img. }
assert (Hdst : store_ok RSEGS M' dst 1 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-541) 64) in exact i)
_ _ _ (-541 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 541 + P)%Z with (bv_unsigned sp0 + (-541 + P))%Z by lia. exact Hst. }
assert (MC : mcH M' dst (Z_to_bv 64 0x12b55) 1 [Z_to_bv 8 10]).
{ constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x9e414 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12b55) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M' dst (Z_to_bv 64 0x12b55) 1 _ (seg_rom RSEGS) MC Rc (0x9e414 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 692576) with (0xa9160 : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x9e414 : word) with (Z_to_bv 64 0x9e414) by (apply bv_eq; reflexivity).
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
End SE.
Definition reG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
forall vals R M,
length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x9e414) M (seg_rom RSEGS)) model) T.
Lemma re_segF_gen : ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "T4'6'R4y8%211%411yR0%511'>&Q;%913&By5%2216'9%11;p091';&QJ&5r7%22A1%411r5%73@21':&QIzr6%3221+QM%5231%7231'7%?2K;uU7%C3321&QE(1%22;1vR2%H3Q221u2%62G1r:%L3Q621r8uSA%;221&R3%12Q<6%Q23Q<31&R5%12Q?=r<%32QA1%N231&QHr=%72QE1%3216+8%5221+TPPP0%72;1%Q7231&QD&Q4r;%211&O%5321K&QB&QF%71D&H%4432Q01%QO1R8&Q9r@&=rA%QO2R>1u1%4221%74<A61(2&3(4%Q82RFQN(8%11RG%43RH31%63RI<1%82RI1%R>3B:1&Q7rBr?%332D1'QAvR1(@&Q8vQMr>+ciPD%QJ2S51&Q:%11Q4%75653QD1vQN%:221%=4Q8<1Q2p0?1p0D1p0Q81p0Q>1p0QE1p0QO1p0R51p0R<1p0RA1p0RG1p0RL1p0S51pQ8S>1pQ<SB1pT@SF1pSJSH1pQ:SJ1pT2SL1pT0SO1").
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
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x9e414 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x9e414 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 692576) with (0xa9160 : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x9e414 : word) with (Z_to_bv 64 0x9e414) by (apply bv_eq; reflexivity).
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
Lemma re_segF : ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "T<'6'R4y8%211%411yR0%511'>%812&By5%2215'9%11:p081';&QJ&5r6%22@1%411r4%73?21':&QIzr5%3221+QL%5231%7231'7%?2J6uU7%C3321&QE(1%22C1vR2%H3Q121r7u2%7221r9%M3Q621r8uSA%<221&R3%12Q<6%Q33Q<31&R5%12Q?>r;%32QA1%O231&QHr<%72QE1%3216+8%5221+TPPP0%72;1%Q8231&QD&Q4%11>&Or:%53321&QB&QF%71@&H%443261%R01R8&Q9r?&=r@%R02R>1u1%4221%74<O61(2&3(4%Q82RFQO(8%11RG%43RH31%63RI<1%82RI1%R?3B:1'QAvR1(@&Q8vQMr=+ciPD%QF2S11&Q:%11Q0%75653Q@1vQN%:221&Q<&Q>+2&Q@rA%211%5241&Q=&Q?%117&A%11=%5231%=271%K4QBJ?1p0M1p0QA1p0QG1p0QN1p0R81p0R>1p0RE1p0RK1p0S11p0S61p0S?1pQ8SH1pQ<SL1pT@T01pQ:T21pT2T41pT0T71").
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
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x9e414) M (seg_rom RSEGS)) model) T.
Section SE.
Local Abbreviation SEC_T_re_segDE := (ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "T='6'R4y8%211%411yR0%511'>&Q;%913&By5%2216'9%11;p091';&QJ&5r8%22A1%411r6%73@21':&QIzr7%3221+SooO%5231%7231&<&QG&R3%12Q19r:%43Q221%611'7%F2Q2BuS7%J3321&QE(1%22B1vR2%O3Q921u2%62N1r<%Q33Q=21&R5%12Q@7r=%32QB1%O231&QHr>%72QF1%3216+8%5221+TPPP0%72;1%Q8231&QD&Q4r;%211&N%5321Q3&QB&QF%71H&G%4432Q81%R01R9&Q9rA&=rB%R02R?1u1%4221%74<A61(2&3(4(8%11RG%33RHQH1%53RI;1%72RI1%R>3A91%Q;2RJ>%Q721A%QO2RL1u8%E4JQA21r?%?2S11%RF3I31&Q6rDrC%3421IK'QAvR1(@&Q8vQM+ciPD%R?2S<1&Q:%11Q:%655@3QJ1vQN%9221%<4Q>;1Q6p0>1p0C1p0L1p0Q?1p0QE1p0QL1p0R61p0R<1p0RA1p0RG1p0RL1p0S41p0S=1pQ8SF1pQ<SJ1pT@SN1pT>T41pSJT11pQ:T31pT2T51pT0T81")) (only parsing).
Variable path : ltac:(sec_ty2 constr:(SEC_T_re_segDE) 0%nat 0%nat).
Variable pp : ltac:(sec_ty2 constr:(SEC_T_re_segDE) 1%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_re_segDE) 2%nat 0%nat).
Variable T : ltac:(sec_ty2 constr:(SEC_T_re_segDE) 3%nat 0%nat).
Variable t8 : ltac:(sec_ty2 constr:(SEC_T_re_segDE) 4%nat 0%nat).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_re_segDE) 5%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_re_segDE) 6%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_re_segDE) 7%nat 0%nat).
Lemma re_segDE : ltac:(sec_stmt2 constr:(SEC_T_re_segDE) 8%nat 0%nat).
Proof.
intros HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
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
pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x13a98 24) in exact k) _ HK eq_refl)
as (_ & _ & Hnone). apply Hnone. lia. }
assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
_ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst spS. rewrite u_small by lia.
replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x9ef84 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A2 : getr Rc 2 = spS)
by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x9ef84 : word) MC
ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
ltac:(right; subst spS; rewrite u_small by lia; lia)
ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
clear A1 A2 A10 A11
end.
replace (Z_to_bv 64 695380) with (0xa9c54 : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x9ef84 : word) with (Z_to_bv 64 0x9ef84) by (apply bv_eq; reflexivity).
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
assert (MC : mcH M3 dst (Z_to_bv 64 0x104cb) 0 []).
{ constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x9e414 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x104cb) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M3 dst (Z_to_bv 64 0x104cb) 0 _ (seg_rom RSEGS) MC Rc (0x9e414 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 692576) with (0xa9160 : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
change (wbytes M3 dst []) with M3.
replace (0x9e414 : word) with (Z_to_bv 64 0x9e414) by (apply bv_eq; reflexivity).
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
End SE.
Lemma pre19_img : ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "H';'9'6'R4y8%211%411%611&Q9&QFyR0%811(0%118q031&R3+RZj0%2271uC%;4:521(2&Q5%22@1%G3@41").
Proof. vm_compute. reflexivity. Qed.
Lemma PRE19_len : ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail ":';'7&5'R4y8%211&Q5%5221uC%93821").
Proof. reflexivity. Qed.
Lemma re_memcpy1_denot : ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "Q5'6'R4yR0%211%411'9y8%611%311p061';&QEr2(1%3221vR2%63=21&QC&Q4r3%211&M%532:1&F&R3&QK&R5%12I<+a@%4221%62L1&Q5%93D21%G3H;1p0B1pQ8J1pT@Q01").
Proof.
intros vals M P0. pose proof SPlo. pose proof SPhi.
rewrite <- PRE19_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
repeat (f_equal; try (f_equal; lia)).
Qed.
Lemma re_segBC : ltac2:(TCodec.tc2 tcn__Js0ReadErr_tail "T='6'R4y8%211%411yR0%511'>&Q;%913&By5%2216'9%11;p091';&QJ&5r8%22A1%411r6%73@21':&QIzr7%3221+SooO%5231%7231&<&QG&R3%12Q19r:%43Q221%611'7%F2Q2BuQ7%J3321&QE(1%22B1vR2%O3Q921u2%62N1r<%Q33Q=21&R5%12Q@7r=%32QB1%O231&QHr>%72QF1%3216+8%5221+TPPP0%72;1%Q8231&QD&Q4r;%211&Q3%5321Q3&QB&QF%71H&L%4432Q81%R01R9&Q9rA&=rB%R02R?1u1%4221%74<A61(2&3(4(8%11RG%33RHQH1%53RI;1%72RI1%R>3A91%Q;2RJ>%Q721A%QO2RL1u8%E4JQA21r?%?2S11%RF3I31&Q6rDrC%3421IK'QAvR1(@&Q8vQM+V_^H%R?2S<1&Q:%11Q:%655@3QJ1vQN%9221%<4Q>;1Q6p0>1p0C1p0L1p0Q?1p0QE1p0QL1p0R61p0R<1p0RA1p0RG1p0RL1p0S41p0S=1pQ8SF1pQ<SJ1pT@SN1pT>T41pSJT11pQ:T31pT2T51pT0T81").
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
assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x12b40) 19 = Some PRE19).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x12b40 19) in exact i)
_ _ 0x12b40 19 HK eq_refl) by (cbn; lia). apply pre19_img. }
assert (Hdst : store_ok RSEGS M' dst 19 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 19) in exact i)
_ _ _ (-560) 19 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH M' dst (Z_to_bv 64 0x12b40) 19 PRE19).
{ constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x9e414 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12b40) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 19) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M' dst (Z_to_bv 64 0x12b40) 19 _ (seg_rom RSEGS) MC Rc (0x9e414 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 692576) with (0xa9160 : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
replace (0x9e414 : word) with (Z_to_bv 64 0x9e414) by (apply bv_eq; reflexivity).
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
assert (MC : mcH M3 dst (Z_to_bv 64 0x12b53) 0 []).
{ constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x9e414 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x12b53) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M3 dst (Z_to_bv 64 0x12b53) 0 _ (seg_rom RSEGS) MC Rc (0x9e414 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 692576) with (0xa9160 : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
change (wbytes M3 dst []) with M3.
replace (0x9e414 : word) with (Z_to_bv 64 0x9e414) by (apply bv_eq; reflexivity).
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
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
