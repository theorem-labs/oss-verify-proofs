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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Hoare Frame
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
Spec Ju0ExitBase Ju0MainEntry LibTail.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ju0ReadErr_defs Ju0ReadErr_tail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0ReadErr () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0ReadErr.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0ReadErr.FPX_1.ReadErr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0ReadErr_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0ReadErr_tail."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BL"; "1O"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2eq"; "2not"; "3add"; "4lt"]; ["5Z"; "0E"; "6mkCfg"; "7m_fs"; "8bvmap"; "0M"; "0R"; ":valsRE"; "9img_clear"; "9re_ivs"; ";knRE0"; ";spx"; ";srRE0"; "<ENV"; "=getr"; "=mkst"]; ["=rdn"; "=seg_rom"; ">dot_path"; ">msg_read_error"; ">t_die"; "?srealizes"; "@edenot"; "@ev"; "Aknow_ok"; "Aregs_ok"; "Bvals_ev"; "Cloaded_segments"; "DIn"; "Eadd"; "Ele"; "Eof_nat"]; ["0fx"; "0hi"; "0i"; "0k"; "0lo"; "0model"; "0path"; "0pp"; "0scfg"; "0sp0"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "0t8"; "0vals"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Definition re_ivs : list (Z * Z) :=
[(0x10000,0xb7230); (0xb7231,0xb7279); (0xc7279,0xc8be0); (0xe8cb8,0xe8cd8); (0xc8c14,0xc8c60); (0xc8c68,0xc8c80);
(0xc8c88,0xc8ca0); (0xc8cb0,0xc8cc0); (0xc8cc8,0xe8cb8); (0xe8cf0,0xe8f20); (0xe8f28,0xe8f30); (0xe8f41,0xe8f48);
(0xe8f50,0xe8f58); (0xe8f68,0xe8f70); (0xe8f78,0xe8fa8);
(0xe9478,0xea000)]%Z.
Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.
Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
forall i, (lo <= i < hi)%Z -> M (Z_to_bv 64 i) = None.
Section ReadErr.
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
Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Theorem re_tail : ltac2:(TCodec.tc2 tcn__Ju0ReadErr "T;'6'QKy8%211%411yR0%511%711&Dy5%2214'9%119p071&=&Q<&QJz%22@1r6%53A21%711&Q>&Q?&5r7%22G1%411+QL%7221'<'7r5%92K1uQ7%53421&Q:(1%22C1vQI%:3Q221u2%62A1r9%>3Q621&QL%12Q97r:%32Q;1%K231&Q=r;%72Q?1r<%N2QC1%Q011%6241+8%8221+TPPP0%:2>1%Q7231&Q9&Mv0%221B&L%5321H&Q8&Q;%726C&J%4432M1%QN1R5&Q0r>&>r?%QF2R;1u1%4221%74<Q261(2&3(4(8%11RC%33RDR51%53RE;1%72RE1%QL3A91%Q>2RF>r@%R52RJ1%R711%Q=241%R@2RK1u8%H4MQ?21%A2ROH%R63K21'Q5vQH(B&OvQ@r=+V`R8%RL2S71&Q1%11Q9%75653QJ1vQE%:221&Q4&Q3rA%211&C%117%6231%D4QDC81p0F1p0Q11p0QD1p0QJ1p0R11p0R>1p0RD1p0RI1p0RO1p0S61p0S?1pQ<SH1pQ>SL1pSNT01pSLT41pS@T31pS>T61").
Proof.
intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
unfold t_die.
eapply (re_segBC scfg sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
try eassumption; try lia.
intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
eapply (re_segF scfg sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
Qed.
Variables (pp : word) (tid : Z) (R : bvmap 5 word) (M : word -> option byte).
Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
Hypothesis Rtp : getr R 4 = Z_to_bv 64 0xc8cb0.
Hypothesis Rs2 : getr R 18 = pp.
Hypothesis Mstack : stack_writable M sp0.
Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Hypothesis Mtid : cell M 0xc8c08 4 tid.
Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
Hypothesis Mself : cell M 0xc8be8 8 0xc8be8.
Hypothesis Mcanary : forall i, (0 <= i < 8)%Z -> M (Z_to_bv 64 (0xe8f20 + i)) = Some (nth (Z.to_nat i) (nth 2 BL []) (Z_to_bv 8 0)).
Hypothesis Lcanary : length (nth 2 BL []) = 8%nat.
Hypothesis Mpagesz : cell M 0xe8f70 8 4096.
Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.
Definition valsRE : list word :=
[sp0; pp; pp; pp; pp; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 0].
Let E : env := ENV BL valsRE.
Lemma valsRE_len : ltac2:(TCodec.tc2 tcn__Ju0ReadErr ":'<'7&5'QKyR0%211&G%5221uQ7%93821").
Proof. unfold valsRE. rewrite !length_app, junk_vals_length. reflexivity. Qed.
Lemma evRE_junk : ltac2:(TCodec.tc2 tcn__Ju0ReadErr "K'7&?r1uQ0%3221'<'QKyR0%211&Q7vA&>u6r2%3221%6251&NvF&QJy5&Q?%118%4231%7261%C3@91p0E1pS6J1").
Proof.
intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRE.
change (6 + i)%nat with (length [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] + i)%nat.
unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.
Lemma spxRE_val : ltac2:(TCodec.tc2 tcn__Ju0ReadErr "D'@'<'QKyR0%211&Q6vA&Kr1%211%5241&QJ&Q=&QLvQI%22<1%4218%62>1%A3>81pS8C1").
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
Lemma regs_okRE : ltac2:(TCodec.tc2 tcn__Ju0ReadErr "5&Q9vA&LvF%43321").
Proof.
pose proof SPlo. pose proof SPhi.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRE.
Qed.
Lemma img_clear_of : ltac2:(TCodec.tc2 tcn__Ju0ReadErr "A'@&Q<';%1233(:r2r1%347721&I%83621&HvEr3%33218p051pS4?1pS:@1").
Proof. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.
Ltac kimg := split; [lia|]; split; [lia|]; apply img_clear_of; cbn; tauto.
Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
rewrite adenot_lit0; cbn [edenot];
first [exact H | rewrite H; reflexivity | idtac].
Lemma know_okRE : ltac2:(TCodec.tc2 tcn__Ju0ReadErr "D&Q>&Q=&QLyR0vQG%3221+8%6221vQI%7261+TPPP0%:221%<251&Q8&Q;vAvE&J%544321p071").
Proof.
intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
unfold know_ok, knRE0.
repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
- split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
- change (edenot E (EVar 0)) with sp0. lia.
- split; [apply flat_intro; cbn; lia|].
intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia.
apply Mstack; lia.
- change (edenot E (EVar 2)) with pp. lia.
- split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
apply store_ok_data; rewrite u_small by lia; lia.
- kimg. - kimg. - kimg. - kimg.
- kcell Mself.
- kcell Mtid.
- kimg. - kimg. - kimg. - kimg. - kimg. - kimg.
-
unfold elenZ, estart. cbn [edenot a_base a_off eb E ENV blobs_ev]. rewrite ?(u_small 8), ?(u_small 0) by lia.
split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?(u_small 0) by lia; lia|].
split; [unfold blobs_ev; rewrite Lcanary; reflexivity|].
intros i Hi. replace (0 + 954144 + i)%Z with (954144 + i)%Z by lia. unfold blobs_ev. apply Mcanary. lia.
- kimg. - kimg. - kimg. - kimg.
- kcell Mpagesz.
- kimg.
- kimg.
- change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
Qed.
Theorem ref_read_error : ltac2:(TCodec.tc2 tcn__Ju0ReadErr "RO'6'QKy8%211%411&=&Q<&QJz%2271r2%53821%711&Q>&Q?&5r3%22>1%411+QL%7221&Q=&QLyR0vQG%3221r4%<2H1%>11%8241+8%:221vQI%;2:1+TPPP0%>221%G251'<'9%11Q3&Q0&Q;vE&>r5%N2Q:1u1%4221%8476H1(2&3(4(8%11QB%33QCQ=1%53QD;1%72QD1%D3B91r6%Q<2QH1%Q>11%Q82Q41%QG2Q71u8%H4GF21%@2QME%M3K21'Q5vQH(B&OvQ@vF+V`R8%R32QC1&Q1%11Q3%75653Q31vQE%:221&Q4&Q3r7%211&C%117%6231%D4Q>C81p0F1p0Q01p0QF1p0R71p0R@1pSLRI1pS>RJ1").
Proof.
intros path t8 Hnonul HPl Hpp2 Hstr Ht8.
eapply (re_tail path pp t8 valsRE R M); try eassumption.
- apply valsRE_len.
- reflexivity.
- reflexivity.
- apply regs_okRE.
- apply know_okRE. lia.
Qed.
Corollary ref_read_error_dot : ltac2:(TCodec.tc2 tcn__Ju0ReadErr "R8'6'QKy8%211%411&Q>&Q=&QLyR0vQG%3221+9%6221vQI%7261+TPPP0%:221%<251'<'9%11@&Q0&Q;vEu2%4432@1(2(4&QJ+Q>%22L1z%42N1(8%11O%83Q031%93Q161%;2Q11%D3B=1+1%Q22N1%=2Q11u8%F4ED21r3%C2Q91%L3J31'Q5vQH(B&OvQ@vF+V`R8%J2Q>1&Q1%11Q2%75653Q21vQE%:221&Q4&Q3&Q2%211&C%117%6231%D4Q=C81p0F1p0O1p0QE1pSLR31").
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
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
