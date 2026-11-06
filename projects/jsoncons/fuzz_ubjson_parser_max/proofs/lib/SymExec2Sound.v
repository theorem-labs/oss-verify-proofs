(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SymExec2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SymExec2Sound () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.FPX_1.LinDenot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.FPX_2.CarrySound."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.FPX_2.StepSound."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1andb"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"]; ["1true"; "2I"; "2True"; "2and"; "2eq"; "2ex"; "2iff"; "2or"; "3add"; "3sub"; "4le"; "4lt"; "5firstn"; "5map"; "5nth"; "5repeat"]; ["5skipn"; "6N"; "6Z"; "0E"; "7Z_to_le_bytes"; "7bytes_le_to_Z"; "7nat_to_word"; "8Segment"; "9MachineOk"; "9fetch_word"; "9is_ecall"; "9machine_result"; "9machine_state"; "9step"; "9store_ok"; "9word_to_le_bytes"]; [":decode_any"; ";ALU_ADD"; ";ALU_AND"; ";ALU_OR"; ";ALU_SLL"; ";ALU_SRA"; ";ALU_SRL"; ";ALU_SUB"; ";ALU_XOR"; ";Fence"; ";FenceI"; ";Load"; ";M_DIVU"; ";M_MUL"; ";M_MULHU"; ";M_REMU"]; [";Store"; ";aluop"; ";branch_cond"; ";instr"; ";msize"; ";mulop"; "<bvmap"; "<sext"; "<zext"; "=alu32"; "=alu64"; "=branch_taken"; "=low32"; "=mul_div"; "0M"; "0M0"]; ["0R"; ">wbytes"; "?msteps"; "@getr"; "@mkst"; "@rdn"; "@v_addi"; "Amem_grows"; "BELit"; "BEnv"; "BKImg"; "BKZero"; "BRDisjoint"; "BRInside"; "BSA"; "BSOk"]; ["Badenot"; "Ball_eval_to"; "Baluop_eqb"; "Bbase_range"; "Bblob_val"; "Bcarry"; "Bclampi"; "Bcoeffs_div"; "Bconc_expr"; "Bconc_try"; "Bconcretize"; "Bcond_on_eq"; "Bctz64"; "Bctz_fuel"; "Bdecide_branch"; "Bealign"]; ["Bedenot"; "Belen"; "Benv"; "Berange"; "Berange_f"; "Besubst"; "Beval_closed"; "Bexpr"; "Bexpr_eqb"; "Bext_Z"; "Bext_val"; "Bfind_align"; "Bfind_range"; "Bflat_sc"; "Bimg_bytes"; "Bis_lit"]; ["Bitv_lts"; "Bitv_ltu"; "Bkdisj_apart"; "Bkentry"; "Bladd"; "Bldiv_terms"; "Blin"; "Blin_lowbits"; "Blin_nowrap"; "Blin_of"; "Blin_range"; "Blins"; "Blit_shamt"; "Blscale"; "Blscale_terms"; "Blterm"]; ["Blterms"; "Bmask_cover"; "BmkAlu"; "BmkAluK"; "BmkAluw"; "BmkAnd"; "BmkExt"; "BmkMd"; "BmkMdw"; "BmkOr"; "BmkSrl"; "Bmsize_bytes"; "Bmulop_eqb"; "Bor_disjoint"; "Bprune"; "Brange_branch"]; ["Brangerel"; "Branges_apart"; "Brel_lit"; "Bridx"; "Bs_know"; "Bs_log"; "Bs_pc"; "Bs_regs"; "Bsaddr"; "Bsaddr_eqb"; "Bsc_add"; "Bsc_mem"; "Bscripts"; "Bsentry"; "Bshamt_of"; "Bsidecond"]; ["Bsidecond_eqb"; "Bsnorm"; "Bsr_id"; "Bsr_upd"; "Bstepres"; "Bsub_itv"; "Bsym_exec"; "Bsym_state"; "Bsym_step"; "Bto_saddr"; "Bto_saddrK"; "Btwo64"; "Btwo64z"; "Bunlin"; "Bzbytes_le_to_Z"; "Elden"]; ["Etden"; "EuE"; "Deff_sx"; "DelenZ"; "Deqm"; "Destart"; "Dextz"; "Dflat"; "Dknow_ok"; "Dload_result"; "Dmem_denot"; "Dreg_ev"; "Dregs_ok"; "Dsc_denot"; "Dscs_denot"; "Dtden"]; ["Gkn_words_le8"; "Hst_ok"; "Fst_ok"; "CelenZ"; "Cestart"; "Cextz"; "Cflat"; "Ckentry_ok"; "Cknow_ok"; "Clog_flat"; "Cmem_denot"; "Cregs_ok"; "Cscs_denot"; "Ctden"; "IIn"; "Jle"]; ["Kadd"; "Kdiv"; "Kdivide"; "Kland"; "Kle"; "Kleb"; "Klog2_up"; "Klor"; "Klt"; "Kltb"; "Klxor"; "Kmodulo"; "Kmul"; "Kof_N"; "Kof_nat"; "Kopp"]; ["Kpow"; "Ksub"; "Ktestbit"; "Kto_nat"; "0V"; "0a"; "0acc"; "0ah"; "0al"; "0allkn"; "0anybase"; "0b"; "0b1"; "0b2"; "0base"; "0bh"]; ["0bits"; "0bl"; "0bs"; "0c"; "0cands"; "0cnt"; "0d"; "0e"; "0ebs"; "0f"; "0first"; "0fuel"; "0fx"; "0h"; "0hi"; "0hi'"]; ["0hints"; "0hs'"; "0i"; "0i0"; "0imm"; "0j"; "0k"; "0k1"; "0k2"; "0ka"; "0kb"; "0kk"; "0kn"; "0kn'"; "0l"; "0l0"]; ["0l1"; "0l2"; "0len"; "0lo"; "0lo'"; "0log"; "0m"; "0mem"; "0ms"; "0ms'"; "0n"; "0n'"; "0n1"; "0n2"; "0news"; "0nk"]; ["0nr"; "0op"; "0pc"; "0q"; "0r"; "0r'"; "0ra"; "0rb"; "0rd"; "0regs"; "0rest"; "0rhi"; "0rk"; "0rlo"; "0rn"; "0rng"]; ["0rom"; "0rs"; "0rs1"; "0rs2"; "0s"; "0scr"; "0scr'"; "0scs"; "0segs"; "0sh"; "0sr"; "0ss"; "0ss'"; "LBV"; "LZ_to_bv"; "Lbv"]; ["Lbv_add"; "Lbv_extract"; "Lbv_signed"; "Lbv_swrap"; "Lbv_unsigned"; "0stops"; "0sx"; "0sz"; "0t"; "0ts"; "0u"; "0v"; "0w"; "0wa"; "0wb"; "0wk"]; ["0x"; "0y"; "0y'"; "0z"; "0zs"]]).
Local Ltac lia := L5FastLia.plia.
Import ListNotations.
Open Scope bv_scope.
Module SX2S.
Import SX2.
Export SX2.
Section FPX_1. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma aluop_eqb_eq : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'R1'D'5&S2r2r1%3221(@%73621r3%93:16p031p_H<1p_<=1").
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
#[using="Type"] Lemma mulop_eqb_eq : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'R5'D'5&TLr2r1%3221(@%73621r3%93:16p031p_H<1p_<=1").
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
#[using="Type"] Lemma expr_eqb_eq : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'SG'D'5&SHr2r1%3221(@%73621r3%93:16p031pf4<1pf2=1").
Proof.
induction x; destruct y; cbn; intros H; try discriminate;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
| H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
| H : aluop_eqb _ _ = true |- _ => apply aluop_eqb_eq in H
| H : mulop_eqb _ _ = true |- _ => apply mulop_eqb_eq in H
| H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
end; subst; reflexivity.
Qed.
#[using="Type"] Lemma saddr_eqb_eq : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'U8'D'5&U9r2r1%3221(@%73621r3%93:16p031p_H<1p_<=1").
Proof.
intros [ab ak] [bb bk] H. unfold saddr_eqb in H. cbn [a_base a_off] in H.
apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2.
subst. reflexivity.
Qed.
#[using="Type"] Lemma edenot_lit : ltac2:(TCodec.tc2 tcn__SymExec2Sound "A'SB'Q2'D'Z?yR0%211&S@r2(RHr1%211%5241&Z>%1294%<3931pf8>1pR8@1").
Proof. reflexivity. Qed.
#[using="Type"] Lemma alu64_add_0_r : ltac2:(TCodec.tc2 tcn__SymExec2Sound "='Z?yR0%211'D&R:(QAr1&Z>z%2281%63541%83915peH:1").
Proof.
intro v. rewrite alu_add. unfold v_add. apply bv_eq.
rewrite !Z_to_bv_unsigned. change (bv_wrap 64 0) with 0%Z.
rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.
#[using="Type"] Lemma alu64_add_comm : ltac2:(TCodec.tc2 tcn__SymExec2Sound "='Z?yR0%211'D&R:(QAr2r1%43321%53423%73821p_H91p_<:1").
Proof. intros. rewrite !alu_add. apply v_add_comm. Qed.
#[using="Type"] Lemma alu64_sub_as_add : ltac2:(TCodec.tc2 tcn__SymExec2Sound "D'Z?yR0%211'Q2'D&R:(QGr2&Z>r1%2291%63541(QA&W?%115%72>1%;3491%=3?61pf4?1peHA1").
Proof.
intros v y. rewrite alu_sub, alu_add, v_sub_lit, v_add_lit. f_equal.
Qed.
Definition eqm (a b : Z) : Prop := exists q, (a = b + q * 2 ^ 64)%Z.
#[using="Type"] Lemma eqm_refl : ltac2:(TCodec.tc2 tcn__SymExec2Sound "5'Q2&V4r1%2211p_<41"). Proof. intros; exists 0%Z; lia. Qed.
#[using="Type"] Lemma eqm_sym : ltac2:(TCodec.tc2 tcn__SymExec2Sound ":'Q2&V4r2r1%3221r3%5241p031p_H81p_<91"). Proof. intros a b [q H]; exists (-q)%Z; lia. Qed.
#[using="Type"] Lemma eqm_trans : ltac2:(TCodec.tc2 tcn__SymExec2Sound "<'Q2&V4r3r2%3221r5%5214p031p041p`891p_H:1p_<;1").
Proof. intros a b c [q H] [r H']; exists (q + r)%Z; lia. Qed.
#[using="Type"] Lemma eqm_add : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Q2&V4r4r3%3221r2%5231&W0r6%2217r5%4218%;231p071p0:1p`>?1p`8@1p_HA1p_<B1").
Proof. intros a b c d [q H] [r H']; exists (q + r)%Z; lia. Qed.
#[using="Type"] Lemma eqm_mul_l : ltac2:(TCodec.tc2 tcn__SymExec2Sound "?'Q2&V4r2r1%3221&W<r4r3%3221%4237%9221p071p_H<1p_<=1pa>>1").
Proof. intros k a b [q H]; exists (k * q)%Z. subst a. ring. Qed.
#[using="Type"] Lemma eqm_mul_r : ltac2:(TCodec.tc2 tcn__SymExec2Sound "?'Q2&V4r2r1%3221&W<r3r4%3221%4272%9221p071p_H<1p_<=1pa>>1").
Proof. intros k a b [q H]; exists (q * k)%Z. subst a. ring. Qed.
#[using="Type"] Lemma eqm_mod : ltac2:(TCodec.tc2 tcn__SymExec2Sound ";'Q2&V4&W;r1&W@+2+R0%3221%6251%8216p_<:1").
Proof. intros a. exists (- (a / 2 ^ 64))%Z. pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)). lia. Qed.
#[using="Type"] Lemma two64z_eq : ltac2:(TCodec.tc2 tcn__SymExec2Sound "8'D'Q2&UL&W@+2+R0%3221%73651"). Proof. reflexivity. Qed.
#[using="Type"] Lemma eqm_snorm : ltac2:(TCodec.tc2 tcn__SymExec2Sound "7'Q2&V4&UAr1%211%4212pa>61").
Proof.
intros k. unfold snorm. rewrite two64z_eq. pose proof (Z.div_mod k (2 ^ 64) ltac:(lia)).
destruct (Z.leb (2 ^ 63) (k mod 2 ^ 64)).
- exists (- (k / 2 ^ 64) - 1)%Z. lia.
- exists (- (k / 2 ^ 64))%Z. lia.
Qed.
#[using="Type"] Lemma eqm_Z_to_bv : ltac2:(TCodec.tc2 tcn__SymExec2Sound "A'Q2&V4r2r1%3221'D'Z?yR0%211&Z>r3%2241%325:%83521p0:1p_H?1p_<@1").
Proof.
intros a b [q H]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. subst a. apply Z.mod_add. lia.
Qed.
#[using="Type"] Lemma u_lit64a : ltac2:(TCodec.tc2 tcn__SymExec2Sound "@'Q2'D&ZDyR0&Z>r1%2231%5241&W;&W@+2+R0%3221%5281%=3>71pf8?1").
Proof. intros. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.
#[using="Type"] Lemma eqm_u_lit : ltac2:(TCodec.tc2 tcn__SymExec2Sound ":'Q2&V4&ZDyR0&Z>r1%2231%5241%7213pf891").
Proof. intros. rewrite u_lit64a. apply eqm_mod. Qed.
Section LinDenot.
Variable E : env.
Definition uE (e : expr) : Z := bv_unsigned (edenot E e).
Fixpoint tden (ts : list (Z * expr)) : Z :=
match ts with [] => 0 | (k, a) :: rest => k * uE a + tden rest end.
Definition lden (x : lin) : Z := (fst x + tden (snd x))%Z.
#[using="Type"] Lemma lins_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Q2'SG':'>%1243%311&V4&V0&T;r3r2r1%43321%611&W0&W<&V1%117%3291%<18%6221%?281peDA1p_<F1pa>H1").
Proof.
intros k a ts. induction ts as [|[k' a'] rest IH]; cbn [lins tden].
- pose proof (eqm_snorm k) as [q Hq].
destruct (Z.eqb (snorm k) 0) eqn:Hz; cbn [tden].
+ apply Z.eqb_eq in Hz. exists (q * uE a)%Z. nia.
+ exists (q * uE a)%Z. nia.
- destruct (expr_eqb a a') eqn:Heq.
+ apply expr_eqb_eq in Heq. subst a'. pose proof (eqm_snorm (k + k')) as [q Hq].
destruct (Z.eqb (snorm (k + k')) 0) eqn:Hz.
* apply Z.eqb_eq in Hz. exists (q * uE a)%Z. nia.
* cbn [tden]. exists (q * uE a)%Z. nia.
+ pose proof (eqm_snorm k) as [q Hq].
destruct (expr_cmp a a'); cbn [tden].
* destruct IH as [r Hr]. exists r. lia.
* destruct (Z.eqb (snorm k) 0) eqn:Hz; cbn [tden].
-- apply Z.eqb_eq in Hz. exists (q * uE a)%Z. nia.
-- exists (q * uE a)%Z. nia.
* destruct IH as [r Hr]. exists r. lia.
Qed.
#[using="Type"] Lemma ladd_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "?&T6&V4&UO&T4r2r1%3221%511&W0%715%815%3221%;251pf4=1pf2>1").
Proof.
intros [c ts] [d us]. unfold ladd, lden. cbn [fst snd].
assert (Hf : forall l acc, eqm (tden (fold_right (fun t acc => lins (fst t) (snd t) acc) acc l)) (tden l + tden acc)).
{ induction l as [|[k a] l IH]; intros acc; cbn [fold_right tden].
- exists 0%Z. lia.
- eapply eqm_trans; [apply lins_sound|]. cbn [fst snd].
destruct (IH acc) as [r Hr]. exists r. lia. }
pose proof (eqm_snorm (c + d)) as [q Hq]. destruct (Hf ts us) as [r Hr]. exists (q + r)%Z. lia.
Qed.
#[using="Type"] Lemma lscale_terms_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Q2':'>'SG%2241%411&V4&V0&T>r2r1%3221%511&W<%714%2261%:241peD<1pb>B1").
Proof.
intros m ts. induction ts as [|[k a] rest IH]; cbn [lscale_terms tden].
- exists 0%Z. lia.
- pose proof (eqm_snorm (m * k)) as [q Hq]. destruct IH as [r Hr].
destruct (Z.eqb (snorm (m * k)) 0) eqn:Hz; cbn [tden].
+ apply Z.eqb_eq in Hz. exists (r + q * uE a)%Z. nia.
+ exists (r + q * uE a)%Z. nia.
Qed.
#[using="Type"] Lemma lscale_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "?'Q2&T6&V4&UO&T=r2r1%3221%511&W<%714%2261%:241pf2<1pb>>1").
Proof.
intros m [c ts]. unfold lscale, lden. cbn [fst snd].
pose proof (eqm_snorm (m * c)) as [q Hq]. destruct (lscale_terms_sound m ts) as [r Hr].
exists (q + r)%Z. nia.
Qed.
#[using="Type"] Lemma u_add_eqm : ltac2:(TCodec.tc2 tcn__SymExec2Sound "B'Z?yR0%211&V4&ZD&R:(QAr2r1%43321%6291&W0%82;5%92<5%3221%<251pf4>1pf2?1").
Proof. intros. rewrite alu_add. unfold v_add. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_sub_eqm : ltac2:(TCodec.tc2 tcn__SymExec2Sound "B'Z?yR0%211&V4&ZD&R:(QGr2r1%43321%6291&WA%82;5%92<5%3221%<251pf4>1pf2?1").
Proof. intros. rewrite alu_sub. unfold v_sub. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_mul_eqm : ltac2:(TCodec.tc2 tcn__SymExec2Sound "B'Z?yR0%211&V4&ZD&R=(QMr2r1%448321%6291&W<%82;5%92<5%3221%<251pf4>1pf2?1").
Proof. intros. rewrite m_mul. unfold v_mul. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_sll_eqm : ltac2:(TCodec.tc2 tcn__SymExec2Sound "J'Z?yR0%211'Q2&V4&ZD&R:(QDr2&Z>r1%22:1%63541%82<1&W<&W@+2&W;+R0%2291%5241%@2D=%8221%C2:1pd:E1pf2G1").
Proof.
intros. rewrite alu_sll. unfold v_sll. rewrite (u_lit64a s).
replace ((s mod 2 ^ 64) mod 64)%Z with (s mod 64)%Z by (symmetry; apply Z.mod_mod_divide; exists (2^58)%Z; reflexivity).
rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). rewrite Z.mul_comm. apply eqm_u_lit.
Qed.
#[using="Type"] Lemma lin_of_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound ";'SG&V4&UO&T9r1%211%411&V1%114%8231p`@:1").
Proof.
induction e; cbn [lin_of]; try (unfold lden; cbn [fst snd tden]; exists 0%Z; lia).
- unfold lden; cbn [fst snd tden]. pose proof (eqm_snorm z) as [q Hq]. unfold uE. cbn [edenot].
pose proof (eqm_u_lit z) as [r Hr]. exists (q - r)%Z. lia.
- destruct op; try (unfold lden; cbn [fst snd tden]; exists 0%Z; lia).
+ eapply eqm_trans; [apply ladd_sound|]. unfold uE. cbn [edenot].
eapply eqm_trans; [| apply eqm_sym; apply u_add_eqm]. apply eqm_add; assumption.
+ eapply eqm_trans; [apply ladd_sound|]. unfold uE. cbn [edenot].
eapply eqm_trans; [| apply eqm_sym; apply u_sub_eqm].
replace (bv_unsigned (edenot E e1) - bv_unsigned (edenot E e2))%Z
with (bv_unsigned (edenot E e1) + (-1) * bv_unsigned (edenot E e2))%Z by lia.
apply eqm_add; [assumption|]. eapply eqm_trans; [apply lscale_sound|]. apply eqm_mul_l. assumption.
+ destruct e2; try (unfold lden; cbn [fst snd tden]; exists 0%Z; lia).
eapply eqm_trans; [apply lscale_sound|]. unfold uE. cbn [edenot].
eapply eqm_trans; [| apply eqm_sym; apply u_sll_eqm]. apply eqm_mul_l. assumption.
- destruct op; try (unfold lden; cbn [fst snd tden]; exists 0%Z; lia).
destruct e1;
[ eapply eqm_trans; [apply lscale_sound|]; unfold uE; cbn [edenot];
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]; cbn [edenot];
eapply eqm_trans; [apply eqm_mul_l; exact IHe2|]; apply eqm_mul_r; apply eqm_sym; apply eqm_u_lit | ..];
(destruct e2;
[ eapply eqm_trans; [apply lscale_sound|]; unfold uE; cbn [edenot];
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]; cbn [edenot]; rewrite Z.mul_comm;
eapply eqm_trans; [apply eqm_mul_r; exact IHe1|]; apply eqm_mul_l; apply eqm_sym; apply eqm_u_lit
| unfold lden; cbn [fst snd tden]; exists 0%Z; lia .. ]).
Qed.
#[using="Type"] Lemma lterm_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'>'Q2'SG%3221&V4&V1&T?r1%211%411&W<&8%13;:5&?%13=<7%:11%6241%=281peB?1").
Proof.
intros [k a]. unfold lterm. cbn [fst snd]. destruct (Z.eqb k 1) eqn:Hk.
- apply Z.eqb_eq in Hk. subst. exists 0%Z. lia.
- unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_mul_eqm|]. cbn [edenot].
apply eqm_mul_r. apply eqm_u_lit.
Qed.
#[using="Type"] Lemma lterms_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "@':'>'Q2'SG%3221%511&V4&V1&T@r1%211%411&V0%114%8231peD:1").
Proof.
induction ts as [|t rest IH]; cbn [lterms tden].
- unfold uE. cbn [edenot]. rewrite u_lit64a. exists 0%Z. reflexivity.
- destruct rest as [|t' rest'].
+ destruct t as [k a]. cbn [tden]. rewrite Z.add_0_r. apply lterm_sound.
+ destruct t as [k a]. unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_add_eqm|].
apply eqm_add; [apply (lterm_sound (k, a)) | exact IH].
Qed.
#[using="Type"] Lemma unlin_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound ";&T6&V4&V1&UMr1%211%411&UO%114%8231pf2:1").
Proof.
intros [c ts]. unfold unlin, lden. cbn [fst snd].
destruct ts as [|t rest].
- cbn [tden]. unfold uE. cbn [edenot]. rewrite Z.add_0_r. apply eqm_u_lit.
- destruct (Z.eqb c 0) eqn:Hc.
+ apply Z.eqb_eq in Hc. subst c. rewrite Z.add_0_l. apply lterms_sound.
+ unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_add_eqm|]. rewrite Z.add_comm.
apply eqm_add; [cbn [edenot]; apply eqm_u_lit | apply lterms_sound].
Qed.
#[using="Type"] Lemma unlin_ladd : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'SG'D'Z?yR0%211&S@vQ3&UM&T4&T9r2%211r1%411%6231%811%;2:1&R:(QA%>2=9%?2>8%43321%E3B61p_HG1p_<H1").
Proof.
intros a b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply ladd_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_add_eqm]. apply eqm_add; apply lin_of_sound.
Qed.
#[using="Type"] Lemma unlin_lsub : ltac2:(TCodec.tc2 tcn__SymExec2Sound "L'SG'D'Z?yR0%211&S@vQ3&UM&T4&T9r2%211&T=-1r1%611%4231%9261%;11%>2=1&R:(QG%A2@<%B2A9%43321%H3E61p_HJ1p_<K1").
Proof.
intros a b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply ladd_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_sub_eqm].
replace (bv_unsigned (edenot E a) - bv_unsigned (edenot E b))%Z
with (bv_unsigned (edenot E a) + (-1) * bv_unsigned (edenot E b))%Z by lia.
apply eqm_add; [apply lin_of_sound|]. eapply eqm_trans; [apply lscale_sound|]. apply eqm_mul_l. apply lin_of_sound.
Qed.
#[using="Type"] Lemma unlin_lsll : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q0'SG'Q2'D'Z?yR0%211&S@vQ3&UM&T=&W@+2&W;r1+R0%3221%6251&T9r2%211%;241%=11%@2?1&R:(QD%C2B7&Z>%12G>%53431%K3H71pd:M1p_<O1").
Proof.
intros a s. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_sll_eqm]. apply eqm_mul_l. apply lin_of_sound.
Qed.
#[using="Type"] Lemma unlin_lmul_l : ltac2:(TCodec.tc2 tcn__SymExec2Sound "J'Q2'SG'D'Z?yR0%211&S@vQ3&UM&T=r2&T9r1%211%5241%711%:291&R=(QM&Z>%12@:%?2>9%54B421%E3B71p_HG1pf2I1").
Proof.
intros x b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (mul_div _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]. rewrite u_lit64a.
eapply eqm_trans; [apply eqm_mul_l; apply lin_of_sound|]. apply eqm_mul_r. apply eqm_sym. apply eqm_mod.
Qed.
#[using="Type"] Lemma unlin_lmul_r : ltac2:(TCodec.tc2 tcn__SymExec2Sound "J'SG'Q2'D'Z?yR0%211&S@vQ3&UM&T=r1&T9r2%211%5241%711%:291&R=(QM%=2<7&Z>%12A;%54B431%E3B71pf4G1p_<I1").
Proof.
intros a y. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (mul_div _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]. rewrite u_lit64a. rewrite (Z.mul_comm (bv_unsigned _)).
eapply eqm_trans; [apply eqm_mul_l; apply lin_of_sound|]. apply eqm_mul_r. apply eqm_sym. apply eqm_mod.
Qed.
End LinDenot.
#[using="Type"] Lemma coeffs_div_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "N'SB'Q2':'>'SG%2241%411&W8zr2%3221'D'5&S7r3%2216(@%63521&W;&V?r5%2217r4%5221%=3G1@p081p0@1peDE1pb>K1pR8M1").
Proof.
intros E m ts Hm. induction ts as [|[k a] rest IH]; cbn [coeffs_div tden]; intros H.
- apply Z.mod_0_l. lia.
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. specialize (IH H2).
rewrite Z.add_mod, Z.mul_mod, H1, Z.mul_0_l, Z.mod_0_l, Z.add_0_l, IH by lia. apply Z.mod_0_l. lia.
Qed.
#[using="Type"] Lemma pow2_div_64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "B'Q2'C&W4zr1%3221+R0%5231%7231&W2&W@+2r2%3221%4238%6221p081pa>A1").
Proof. intros k Hk. exists (2 ^ (64 - k))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
#[using="Type"] Lemma eqm_mod_pow2 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "K'Q2'C&W4zr1%3221+R0%5231%7231&V4r4r3%3221'D&W;r5&W@+2%2217%5241%62:2%83E21p0:1p0?1pa>H1p_HI1p_<J1").
Proof.
intros a b k Hk [q Hq]. subst a. destruct (pow2_div_64 k Hk) as [r Hr]. rewrite Hr.
replace (b + q * (r * 2 ^ k))%Z with (b + (q * r) * 2 ^ k)%Z by ring. apply Z.mod_add.
assert (0 < 2 ^ k)%Z by (apply Z.pow_pos_nonneg; lia). lia.
Qed.
#[using="Type"] Lemma lin_lowbits_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q='SB'SG'Q2'C&W4zr2%3221+R0%5231%7231'D'<%11;&T7r4r3%3221(2%12A=%93731&W;&ZDyR0&S@r6r5%3221%6251&W@+2%221@%;241%F3O1A%N2MB&W8%12D5%Q2231%Q3251p0C1p0N1peHQ71pa>Q81p`@Q:1pR8Q<1").
Proof.
intros E e k v Hk H. unfold lin_lowbits in H.
assert (Hp : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
destruct (lin_of e) as [c ts] eqn:Hl. cbn [fst snd] in H.
destruct (coeffs_div (2 ^ k) ts) eqn:Hd; [|discriminate]. injection H as <-.
pose proof (lin_of_sound E e) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs. unfold uE in Hs.
split; [|apply Z.mod_pos_bound; lia].
rewrite <- (eqm_mod_pow2 _ _ k Hk Hs). rewrite Z.add_mod, (coeffs_div_sound E _ ts Hp Hd), Z.add_0_r, Z.mod_mod by lia.
reflexivity.
Qed.
#[using="Type"] Lemma shamt_of_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q='SB'SG'Q2'C&W4zr2%3221+R0%5231%7231'D'<%11;&U>r4r3%3221(2%12A=%93731&W;&ZDyR0&S@r6r5%3221%6251&W@+2%221@%;241%F3O1A%N2MB&W8%12D5%Q2231%Q3251p0C1p0N1pd:Q71p`2Q81p`@Q:1pR8Q<1").
Proof.
intros E e bits s Hb H. assert (Hp : (0 < 2 ^ bits)%Z) by (apply Z.pow_pos_nonneg; lia).
unfold shamt_of in H. destruct e; try (apply lin_lowbits_sound; assumption).
injection H as <-. cbn [edenot]. rewrite u_lit64a. split; [|apply Z.mod_pos_bound; lia].
apply Z.mod_mod_divide. apply pow2_div_64. lia.
Qed.
#[using="Type"] Lemma alu_sll_amt : ltac2:(TCodec.tc2 tcn__SymExec2Sound "O'Z?yR0%211'Q2'D&W;&ZDr2%2271+R0%5221r1%83921&R:(QDr4r3%43321&Z>&W<%>2C5&W@+2%221@%5241%72H1%F3H91p0?1pd:I1pf4K1pf2L1").
Proof.
intros x y s Hs. rewrite alu_sll. unfold v_sll.
pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as Hr. rewrite Hs in Hr. rewrite Hs.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
#[using="Type"] Lemma alu_srl_amt : ltac2:(TCodec.tc2 tcn__SymExec2Sound "J'Z?yR0%211'D'Q2&W;&ZDr2%2271+R0%5221r1%62;1%8214%;3:41&R:(QFr4r3%43321%5343=%B3C21p081pf6E1pf4F1pf2G1").
Proof. intros x y y' H. rewrite !alu_srl. unfold v_srl. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma alu_sra_amt : ltac2:(TCodec.tc2 tcn__SymExec2Sound "J'Z?yR0%211'D'Q2&W;&ZDr2%2271+R0%5221r1%62;1%8214%;3:41&R:(QEr4r3%43321%5343=%B3C21p081pf6E1pf4F1pf2G1").
Proof. intros x y y' H. rewrite !alu_sra. unfold v_sra. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma w_shift_amt : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q?'R1'Z?yR0%211'G'Dr4(QD%33821(QF%53:41(QE%73<61%9231%:261'Q2&W;&ZDr3%22A1+Q0%5221r2%62E1%8214%D3:41&R7yQ0&R9r6&R<r5%211%31K%63521%938Q11/01Q1%71C%:3961%=3<Q51%Q33Q541p0@1p0L1pf6Q81pf4Q91pf2Q:1pc4Q>1").
Proof.
intros op x y y' Hop H. destruct Hop as [-> | [-> | ->]].
- rewrite !w_sllw. unfold v_sllw. rewrite H. reflexivity.
- rewrite !w_srlw. unfold v_srlw. rewrite H. reflexivity.
- rewrite !w_sraw. unfold v_sraw. rewrite H. reflexivity.
Qed.
#[using="Type"] Lemma u_lit_mod : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q5'Q2'C&W4zr2%3221&W8&W@+2+6%3221%5271%;271'G'D+R0%23@<1+Q0%43B>1%6231r4r3%@221&W;&ZDyR0&Z>r5%2231%5241%721:%A3O14p0:1p0>1p0F1pb>Q31pd:Q41").
Proof. intros s m Hs Hm Hsm. rewrite u_lit64a. rewrite (Z.mod_small s (2 ^ 64)) by lia. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma unlin_lsll_amt : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q7'SB'SG'Z?yR0%211'Q2'D&W;&ZDr2%2271+R0%5221r1%83921&S@r5&UM&T=&W@+2%221<&T9r4%211%7241%911%<2;1&R:(QD%?2>7r3%43321%K3M61p0D1pd:N1pf4Q01p_<Q41pR8Q61").
Proof.
intros E a y s Hs. rewrite (alu_sll_amt _ _ s Hs).
rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
rewrite Z.mul_comm. apply eqm_mul_r. apply lin_of_sound.
Qed.
#[using="Type"] Lemma and_lowmask_val : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q3'Z?yR0%211'Q2&W4zr1%3221r2+R0%6221'D&R:(QBr4&Z>&WA&W@+2r3%3221+1%6221%82F1%<3;:1&W;&ZD%12J=%3218%>2L1%C3L61p0E1p0I1pa<N1peHQ01").
Proof.
intros v j Hj Hj64. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j <= 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
rewrite (Z.mod_small (2 ^ j - 1)) by lia.
replace (2 ^ j - 1)%Z with (Z.ones j) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
rewrite Z.land_ones by lia. reflexivity.
Qed.
#[using="Type"] Lemma is_lit_some : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'SG'Q2'D'<%113&SOr2%211(2r1%2291%93741r3(RH%118%=3?31p051pf8@1p`@B1").
Proof. intros e w H; destruct e; cbn in H; try discriminate. congruence. Qed.
#[using="Type"] Lemma mkAlu_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "H'SB'R1'SG'D'Z?yR0%211&S@r4&TBr3r2r1%43321%7261&R:%9285%:295%33821%@3=51p_HB1p_<C1pc4E1pR8G1").
Proof.
intros E op a b. unfold mkAlu.
assert (Hsll : edenot E (match shamt_of b 6 with
| Some s => unlin (lscale (2 ^ s) (lin_of a))
| None => EAlu ALU_SLL a b
end) = alu64 ALU_SLL (edenot E a) (edenot E b)).
{ destruct (shamt_of b 6) as [s|] eqn:Hs; [|reflexivity].
destruct (shamt_of_sound E b 6 s ltac:(lia) Hs) as [Hm Hr].
apply unlin_lsll_amt. change (2 ^ 6)%Z with 64%Z in Hm. exact Hm. }
assert (Hsr : forall op', (op' = ALU_SRL \/ op' = ALU_SRA) ->
edenot E (match is_lit b with
| Some _ => EAlu op' a b
| None => match shamt_of b 6 with
| Some s => EAlu op' a (ELit s)
| None => EAlu op' a b
end
end) = alu64 op' (edenot E a) (edenot E b)).
{ intros op' Hop. destruct (is_lit b); [reflexivity|]. destruct (shamt_of b 6) as [s|] eqn:Hs; [|reflexivity].
destruct (shamt_of_sound E b 6 s ltac:(lia) Hs) as [Hm Hr]. change (2 ^ 6)%Z with 64%Z in Hm, Hr.
cbn [edenot].
destruct Hop as [-> | ->];
[ apply alu_srl_amt | apply alu_sra_amt ]; rewrite (u_lit_mod s 64) by lia; symmetry; exact Hm. }
destruct (is_lit a) as [x|] eqn:Ha.
- apply is_lit_some in Ha. subst a.
destruct (is_lit b) as [y|] eqn:Hb.
+ apply is_lit_some in Hb. subst b. cbn [edenot]. unfold zalu. apply Z_to_bv_bv_unsigned.
+ destruct op; try reflexivity.
* apply unlin_ladd.
* apply unlin_lsub.
* apply Hsll.
* apply Hsr. left; reflexivity.
* apply Hsr. right; reflexivity.
- destruct op; try (destruct (is_lit b); reflexivity).
+ destruct (is_lit b); apply unlin_ladd.
+ destruct (is_lit b); apply unlin_lsub.
+ destruct (is_lit b); apply Hsll.
+ destruct (is_lit b); apply Hsr; left; reflexivity.
+ destruct (is_lit b); apply Hsr; right; reflexivity.
Qed.
#[using="Type"] Lemma mkAluw_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "N'SB'R1'SG'D'Z?yR0%211&S@r4&TDr3r2r1%43321%7261&R7yQ0&R9&R<%<2;8%211%>2=9%411%63=31%938C1%F3C;1p_HH1p_<I1pc4K1pR8M1").
Proof.
intros E op a b. unfold mkAluw.
assert (Hsh : (op = ALU_SLL \/ op = ALU_SRL \/ op = ALU_SRA) ->
edenot E (match is_lit b with
| Some _ => EAluw op a b
| None => match shamt_of b 5 with
| Some s => match is_lit a with
| Some x => ELit (zaluw op x s)
| None => EAluw op a (ELit s)
end
| None => EAluw op a b
end
end) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))).
{ intros Hop. destruct (is_lit b); [reflexivity|]. destruct (shamt_of b 5) as [s|] eqn:Hs; [|reflexivity].
destruct (shamt_of_sound E b 5 s ltac:(lia) Hs) as [Hm Hr]. change (2 ^ 5)%Z with 32%Z in Hm, Hr.
assert (Heq : forall x : word, (sext 64 (alu32 op (low32 x) (low32 (Z_to_bv 64 s))) : word)
= sext 64 (alu32 op (low32 x) (low32 (edenot E b)))).
{ intros x. apply w_shift_amt; [exact Hop|]. rewrite (u_lit_mod s 32) by lia. symmetry. exact Hm. }
destruct (is_lit a) as [x|] eqn:Ha;
[ apply is_lit_some in Ha; subst a; cbn [edenot]; unfold zaluw; rewrite Z_to_bv_bv_unsigned; apply Heq
| cbn [edenot]; apply Heq ]. }
destruct (is_lit a) as [x|] eqn:Ha.
- destruct (is_lit b) as [y|] eqn:Hb.
+ apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. unfold zaluw.
apply Z_to_bv_bv_unsigned.
+ destruct op; try reflexivity; apply Hsh; tauto.
- destruct (is_lit b); (destruct op; try reflexivity; apply Hsh; tauto).
Qed.
#[using="Type"] Lemma mkMd_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "H'SB'R5'SG'D'Z?yR0%211&S@r4&TGr3r2r1%43321%7261&R=%9285%:295%34=821%@3=51p_HB1p_<C1pc4E1pR8G1").
Proof.
intros E op a b. unfold mkMd.
destruct (is_lit a) as [x|] eqn:Ha; [apply is_lit_some in Ha; subst a|];
(destruct (is_lit b) as [y|] eqn:Hb; [apply is_lit_some in Hb; subst b|]).
- cbn [edenot]. unfold zmd. apply Z_to_bv_bv_unsigned.
- destruct op; try reflexivity. cbn [edenot]. apply unlin_lmul_l.
- destruct op; try reflexivity. cbn [edenot]. apply unlin_lmul_r.
- reflexivity.
Qed.
#[using="Type"] Lemma mkMdw_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "N'SB'R5'SG'D'Z?yR0%211&S@r4&THr3r2r1%43321%7261&R7yQ0&R=&R<%<2;8%211%>2=9%411%647=31%938C1%F3C;1p_HH1p_<I1pc4K1pR8M1").
Proof.
intros E op a b. unfold mkMdw.
destruct (is_lit a) as [x|] eqn:Ha; [|reflexivity].
destruct (is_lit b) as [y|] eqn:Hb; [|reflexivity].
apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. unfold zmdw.
apply Z_to_bv_bv_unsigned.
Qed.
#[using="Type"] Lemma slice_mod : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q2'Q2&W4zr2%3221&W0r4r3%3221r5%9221'D&W;&W1r7&W@+2r6%3221%7251%524;%8221%726@%;221%;2:4%=213%?3J31p0A1p0H1p0I1pa<N1pa>O1pb>Q01p_<Q11").
Proof.
intros a m k j Hk Hj Hm. apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia.
rewrite !Z.div_pow2_bits by lia.
rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
#[using="Type"] Lemma Z_to_bv64_swrap64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "='Q2'D'Z?yR0%211&Z>&ZCr1%2251%4261%5273%:3721peF<1").
Proof.
intro u. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_swrap.
unfold bv_wrap. change (bv_half_modulus 64) with (2^63)%Z.
change (bv_modulus 64) with (2^64)%Z.
rewrite <- Zminus_mod_idemp_l.
rewrite Z.mod_mod by lia.
rewrite Zminus_mod_idemp_l.
f_equal. lia.
Qed.
#[using="Type"] Lemma ext_val_full : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'5'Z?yR0%211'D&SJr2(1u8r1%544321%73812peH91pe>=1").
Proof.
intros sx v. unfold ext_val, ext_Z.
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
change (8 * Z.of_nat 8)%Z with 64%Z. change (8 * N.of_nat 8)%N with 64%N.
pose proof (bv_unsigned_in_range 64 v) as Hr. change (bv_modulus 64) with (2^64)%Z in Hr.
rewrite Z.mod_small by lia.
destruct sx; [rewrite Z_to_bv64_swrap64|]; apply Z_to_bv_bv_unsigned.
Qed.
#[using="Type"] Lemma ext_Z_range : ltac2:(TCodec.tc2 tcn__SymExec2Sound "J';'Q2'Jr2u8%3221'C&W4z&SI(7r4r3%44321:%7261&W8&W@+2+R0%3221%5271%?271p0A1pf8F1pbFH1pb8I1").
Proof.
intros lo n z Hn. unfold ext_Z.
pose proof (Z.mod_pos_bound (z / 2 ^ (8 * Z.of_nat lo)) (2 ^ (8 * Z.of_nat n)) ltac:(apply Z.pow_pos_nonneg; lia)) as H.
assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
lia.
Qed.
#[using="Type"] Lemma ext_val_compose : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q2'5';'Z?yR0%211'J&Hr5r4%3221r2%6221r3u8%9221'D&SJr8r7r6(7%541>=9%645431%A2@5%84715<%:3E31p0<1p0@1peHH1pbHL1pb:M1pbFN1pb8O1pe>Q11").
Proof.
intros sx lo n lo' n' v Hle Hn'. unfold ext_val.
f_equal.
rewrite Z_to_bv_unsigned.
rewrite (bv_wrap_small 64) by
(pose proof (ext_Z_range lo' n' (bv_unsigned v) Hn'); change (bv_modulus 64) with (2^64)%Z; lia).
unfold ext_Z. cbv beta iota.
assert (Hs : (((bv_unsigned v / 2 ^ (8 * Z.of_nat lo')) mod 2 ^ (8 * Z.of_nat n') /
2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n) =
(bv_unsigned v / 2 ^ (8 * Z.of_nat (lo' + lo))) mod 2 ^ (8 * Z.of_nat n))%Z).
{ rewrite slice_mod by lia.
rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
rewrite <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. lia. }
rewrite Hs. reflexivity.
Qed.
#[using="Type"] Lemma mkExt_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "N'SB'5';'SG'Jr2u8%3221'D'Z?yR0%211&S@r6&TFr5r4r3%44321=%7261&SJ%928@%247651%?3<41p0A1p`@F1pbFH1pb8I1pe>K1pR8M1").
Proof.
intros E sx lo n e Hn. unfold mkExt.
destruct e as [x|v|op a b|op a b|op a b|op a b|sx' lo' n' e'|sx' k i n'].
1: { cbn [edenot]. unfold zext_lit. apply Z_to_bv_bv_unsigned. }
all: destruct (Nat.eqb lo 0 && Nat.eqb n 8)%bool eqn:Hfull;
[ apply andb_prop in Hfull as [H0 H8]; apply Nat.eqb_eq in H0; apply Nat.eqb_eq in H8;
subst; symmetry; apply ext_val_full
| ]; try reflexivity.
destruct sx'; [reflexivity|].
destruct (Nat.leb (lo + n) n' && Nat.leb n' 8)%bool eqn:Hc; [|reflexivity].
apply andb_prop in Hc as [Hc1 Hc2]. apply Nat.leb_le in Hc1. apply Nat.leb_le in Hc2.
cbn [edenot]. symmetry. apply ext_val_compose; assumption.
Qed.
#[using="Type"] Lemma ridx_inj : ltac2:(TCodec.tc2 tcn__SymExec2Sound "@'Z?y5%211'D';&U3r2%211r1%411%73631r3%93:16p031pc<<1pc:=1").
Proof.
intros r r' H. apply bv_eq. unfold ridx in H.
pose proof (u5_range r). pose proof (u5_range r'). lia.
Qed.
#[using="Type"] Lemma nth_sr_upd : forall n sr e i,
nth i (sr_upd sr n e) (ELit 0) = if Nat.eqb i n then e else nth i sr (ELit 0).
Proof.
induction n as [|n IH]; intros sr e i.
- destruct sr; destruct i; cbn; try reflexivity; destruct i; reflexivity.
- destruct sr as [|h t]; destruct i as [|i]; cbn; try reflexivity.
+ rewrite IH. destruct (Nat.eqb i n); [reflexivity|]. destruct i; reflexivity.
+ apply IH.
Qed.
Definition regs_ok (E : env) (sr : list expr) (regs : bvmap 5 word) : Prop :=
forall r : reg, getr regs r = edenot E (sr_get sr r).
#[using="Type"] Lemma regs_ok_upd : forall E sr regs rd v e,
regs_ok E sr regs -> edenot E e = v ->
regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
(if bv_eqb rd 0 then regs else regupd regs rd v).
Proof.
intros E sr regs rd v e Hr Hv.
destruct (bv_eqb rd 0) eqn:Hrd; [exact Hr|].
assert (Hne : rd <> 0).
{ intro Hc. subst rd. rewrite bv_eqb_refl in Hrd. discriminate. }
intro r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r. unfold getr. rewrite Hr0. reflexivity.
- rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r.
rewrite getr_same by exact Hne. exact (eq_sym Hv).
+ assert (Hrr : r <> rd).
{ intro Hc. subst r. rewrite Nat.eqb_refl in Hi. discriminate. }
rewrite getr_other by exact Hrr.
specialize (Hr r). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.
#[using="Type"] Lemma regs_ok_pin : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q5'SB':'SG%211&R6y5'Z?yR0%211%5241%415&V<r5r4r3%43321'D&RC%1254&S@r6r2%3221%73?51r7&UC&U3%11>%3381>%B351Ap071p0@1p`@N1pc:G1pcDI1pdFQ01pR8Q41").
Proof.
intros E sr regs r e Hr Hv r'. unfold sr_get.
destruct (bv_eqb r' 0) eqn:Hr0.
- assert (r' = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r'. unfold getr. rewrite Hr0. reflexivity.
- rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
+ specialize (Hr r'). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.
#[using="Type"] Lemma ridx_range : ltac2:(TCodec.tc2 tcn__SymExec2Sound ":'Z?y5%211&K&U3r1%211uQ0%5221pc:71").
Proof. intro r. unfold ridx. pose proof (u5_range r). lia. Qed.
#[using="Type"] Lemma ridx_roundtrip : ltac2:(TCodec.tc2 tcn__SymExec2Sound "='Z?y5%211'D&Z>&W>&U3r1%211%411%6291%83914pc::1").
Proof.
intro r. apply bv_eq. unfold ridx. rewrite Z_to_bv_unsigned.
pose proof (u5_range r). rewrite Z2Nat.id by lia.
apply bv_wrap_bv_unsigned.
Qed.
Definition reg_ev (regs : bvmap 5 word) (rest : nat -> word) : nat -> word :=
fun n => if Nat.ltb n 32 then getr regs (Z_to_bv 5 (Z.of_nat n)) else rest n.
#[using="Type"] Lemma regs_ok_id : ltac2:(TCodec.tc2 tcn__SymExec2Sound "J&R6y5'Z?yR0%211%5241';p013':y8%811%311p061&V<(RI&V;r3r2%3221r1%6221&UB%93216p`B;1pcFA1pcDD1").
Proof.
intros regs rest ebs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r. unfold getr. rewrite Hr0. reflexivity.
- unfold reg_ev. cbn [ev]. rewrite <- (ridx_roundtrip r) at 1.
pose proof (ridx_range r) as Hlt.
set (n := ridx r) in *. clearbody n.
cbn [edenot ev].
do 32 (destruct n as [|n]; [reflexivity|]).
exfalso. lia.
Qed.
Fixpoint mem_denot (E : env) (base : word -> option byte) (log : list sentry)
: word -> option byte :=
match log with
| [] => base
| SE a w v :: rest =>
wbytes (mem_denot E base rest) (adenot E a) (word_to_le_bytes w (edenot E v))
end.
#[using="Type"] Lemma mem_denot_grows : ltac2:(TCodec.tc2 tcn__SymExec2Sound "F'SB'Z?yR0%211'<y8%511%311p051':'U=%211&RGr2&V:r3r1%33241%6251pb<81p_N<1pR8E1").
Proof.
intros E base log. induction log as [|[a w v] rest IH]; cbn [mem_denot].
- apply mem_grows_refl.
- eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.
Definition estart (E : env) (a : saddr) : Z := (bv_unsigned (edenot E (a_base a)) + a_off a)%Z.
Definition elenZ (E : env) (n : expr) : Z := bv_unsigned (edenot E n).
Definition flat (E : env) (a : saddr) (n : Z) : Prop :=
(0 <= estart E a)%Z /\ (estart E a < 2^64)%Z /\ (0 <= n)%Z /\ (estart E a + n <= 2^64)%Z.
#[using="Type"] Lemma flat_u : ltac2:(TCodec.tc2 tcn__SymExec2Sound "F'SB'U8'Q2&V7r3r2r1%43321'D&ZDyR0&S0r4%2219%5241&V5%124<%93?31p0;1pbFA1p_<C1pR8E1").
Proof.
intros E a n (H1 & H2 & H3 & H4). unfold adenot, v_addi, estart in *.
rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma flat_mono : ltac2:(TCodec.tc2 tcn__SymExec2Sound "G'SB'U8'Q2&V7r4r3r2%43321'C&W4z%2215%3267%5221r6r5%=321;p041p0;1pb>A1pbFB1p_<D1pR8F1").
Proof. intros E a n m (H1 & H2 & H3 & H4) Hm. unfold flat. lia. Qed.
Fixpoint log_flat (E : env) (log : list sentry) : Prop :=
match log with
| [] => True
| SE a w _ :: rest => (w <= 8)%nat /\ flat E a (Z.of_nat w) /\ log_flat E rest
end.
Definition extz (sx : bool) (n : nat) (u : Z) : Z :=
if sx then bv_swrap (8 * N.of_nat n) u else u.
Definition kentry_ok (segs : list Segment) (E : env) (base : word -> option byte) (K : kentry) : Prop :=
match K with
| KWord a w v =>
(w <= 8)%nat /\ flat E a (Z.of_nat w)
/\ rdn segs base (adenot E a) w = Some (word_to_le_bytes w (edenot E v))
| KZero a n =>
flat E a (elenZ E n)
/\ forall i, (0 <= i < elenZ E n)%Z -> base (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 0)
| KBlob a n k =>
flat E a (elenZ E n)
/\ Z.of_nat (length (eb E k)) = elenZ E n
/\ forall i, (0 <= i < elenZ E n)%Z ->
base (Z_to_bv 64 (estart E a + i)) = Some (nth (Z.to_nat i) (eb E k) (Z_to_bv 8 0))
| KImg lo hi =>
(0 <= lo)%Z /\ (hi <= 2^64)%Z /\ forall i, (lo <= i < hi)%Z -> base (Z_to_bv 64 i) = None
| KAlign e m => (0 < m)%Z /\ (bv_unsigned (edenot E e) mod m = 0)%Z
| KRange e lo hi => (lo <= bv_unsigned (edenot E e))%Z /\ (bv_unsigned (edenot E e) <= hi)%Z
| KWr a n => flat E a n /\ forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= n)%Z ->
RiscvSemantics.store_ok segs base (Z_to_bv 64 (estart E a + d)) m = true
| KDisj a1 n1 a2 n2 => (estart E a1 + n1 <= estart E a2)%Z \/ (estart E a2 + n2 <= estart E a1)%Z
end.
Definition know_ok (segs : list Segment) (E : env) (base : word -> option byte) (kn : list kentry) : Prop :=
Forall (kentry_ok segs E base) kn.
Definition sc_denot (segs : list Segment) (base : word -> option byte) (E : env) (s : sidecond) : Prop :=
match s with
| SCBr t c a b => branch_taken c (edenot E a) (edenot E b) = t
| SCFlat a n => flat E a (elenZ E n)
| SCDisj a1 n1 a2 n2 =>
flat E a1 (elenZ E n1) /\ flat E a2 (elenZ E n2)
/\ ((estart E a1 + elenZ E n1 <= estart E a2)%Z \/ (estart E a2 + elenZ E n2 <= estart E a1)%Z)
| SCInside a1 n1 a2 n2 =>
flat E a2 (elenZ E n2) /\ (0 <= elenZ E n1)%Z
/\ (estart E a2 <= estart E a1)%Z /\ (estart E a1 + elenZ E n1 <= estart E a2 + elenZ E n2)%Z
| SCStoreOk a n => RiscvSemantics.store_ok segs base (adenot E a) n = true
| SCReadBase a n sx e =>
exists bs, rdn segs base (adenot E a) n = Some bs
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E e
| SCEq a b => edenot E a = edenot E b
end.
Definition scs_denot (segs : list Segment) (base : word -> option byte) (E : env) (l : list sidecond) : Prop :=
Forall (sc_denot segs base E) l.
#[using="Type"] Lemma w_add_nat : ltac2:(TCodec.tc2 tcn__SymExec2Sound "F'Z?yR0%211';'D&Z@r2&Q6r1%211%53941&Z>&W0&ZD%12=8&W>%118%5231%72A1%?3A91pbFA1p_<C1").
Proof.
intros a n. apply bv_eq. unfold nat_to_word.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. apply bv_wrap_add_idemp_r.
Qed.
#[using="Type"] Lemma w_add_1 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Z?yR0%211'D&Z@r1(Z=+1(A%33821%63951&Z>&W0&ZD%12=9%3218%52?1%>3?71p_<@1").
Proof.
intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
change (bv_unsigned (1 : word)) with 1%Z. reflexivity.
Qed.
#[using="Type"] Lemma u_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "G'Q2'C&W4zr1%3221&W8&W@+2+R0%3221%5271%;271'D&ZDyR0&Z>r2%2231%5241%73D13p091pf8F1").
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z. lia.
Qed.
#[using="Type"] Lemma elenZ_elen : ltac2:(TCodec.tc2 tcn__SymExec2Sound "D'SB';'Jr1u8%3221'D'Q2&V3r3&SAr2%211%5241&W>%114%:3931p0<1pbFA1pR8C1").
Proof.
intros E n Hn. unfold elenZ, elen. cbn [edenot]. apply u_small. lia.
Qed.
#[using="Type"] Lemma rdn_skipn : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q@':'Q7%211'Z?yR0%211'<y8%511%311p051';%<14'D%812&REr6r5r3r4%544321(2r2%22;1%;3:41'J%1249r8r7&Z@&Q6%11=%33L?1&I%12B@%D48731&Q0%13MCB%A2J1%J3I41p0>1p0A1pa>O1p`6O1p_<Q71pbFQ21pb@Q41pdBQ=1").
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
- assert (k = 0)%nat by lia. subst k. rewrite word_add_0. cbn in H |- *. exact H.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct k as [|k].
+ rewrite word_add_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
+ cbn [skipn]. replace (S n - S k)%nat with (n - k)%nat by lia.
replace (a + nat_to_word (S k)) with (a + 1 + nat_to_word k)
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply (IH (a+1) rest k Er). lia.
Qed.
#[using="Type"] Lemma rdn_slice : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QD':'Q7%211'Z?yR0%211'<y8%511%311p051';%<14'D%812&REr7r6r4r5%544321(2r3%22;1%;3:41'J&Hr2%2261%421<r9r8&Z@&Q6%11@%33OB1%E4651>&L&Q0%13OED%33Q0B1%D2M1%M3L61p0>1p0D1pa>Q21p`>Q31p`6Q31p_<Q;1pbFQ61pb@Q81pdBQA1").
Proof.
intros segs mem n a bs d k H Hdk.
eapply rdn_firstn; [eapply rdn_skipn; [exact H | lia] | lia].
Qed.
#[using="Type"] Lemma skipn_Z_to_le_bytes : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q3';'Q2'Jr2r3%3221'D':'Z?y8%211%411&Q0&Q4r4%221<%436<1&I%124>&W1&W@+2&W<+8&W>%11E%4231%7261%92I1%@2;1%H3C>1p0J1pf8O1p`>Q11peJQ21").
Proof.
induction w as [|w IH]; intros d z Hd.
- assert (d = 0)%nat by lia. subst. cbn. reflexivity.
- destruct d as [|d].
+ cbn [skipn Nat.sub]. change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r. reflexivity.
+ cbn [Z_to_le_bytes skipn Nat.sub]. rewrite IH by lia.
rewrite Z.shiftr_div_pow2 by lia.
rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
rewrite <- Z.pow_add_r by lia.
replace (8 + 8 * Z.of_nat d)%Z with (8 * Z.of_nat (S d))%Z by lia. reflexivity.
Qed.
#[using="Type"] Lemma firstn_Z_to_le_bytes : ltac2:(TCodec.tc2 tcn__SymExec2Sound "G';'Q2'Jr2r3%3221'D':'Z?y8%211%411&L&Q4r4%221<%436<1%42=>%<3721p0>1pf8C1pbFE1pb>F1").
Proof.
induction m as [|m IH]; intros n z Hn.
- assert (n = 0)%nat by lia. subst. reflexivity.
- destruct n as [|n]; [reflexivity|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.
#[using="Type"] Lemma slice_word_bytes : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q?';'Z?yR0%211'J&Hr3r2%3221r4%6221'D'Q2&Q5&Ly8%?11&Q0&Q?r5%221=%435<1%836@1%:11&W;&W1&ZD%12ID&W@+2&W<+8&W>%11H%4231%7261%;291%51O%8271%;2:1%@241%N3MB1p0Q01peHQ81pbFQ<1p`>Q=1peJQ>1").
Proof.
intros w d n v H. unfold word_to_le_bytes.
rewrite skipn_Z_to_le_bytes by lia. rewrite firstn_Z_to_le_bytes by lia.
apply bytes_le_Z_to_le. apply Z.div_pos; [apply u64_range | apply Z.pow_pos_nonneg; lia].
Qed.
#[using="Type"] Lemma length_firstn_skipn : forall {A} (l : list A) d n,
(d + n <= length l)%nat -> length (firstn n (skipn d l)) = n.
Proof. intros A l d n H. rewrite length_firstn, length_skipn. lia. Qed.
#[using="Type"] Lemma bytes_le_to_Z_bound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "J':'Z?y8%211%411'C&W4z&Q5r1%211%5241&W8&W@+2&W<+8&W>&9%12@:%311%6251%9281%;2=1%C2=1p`6E1").
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length].
- change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. lia.
- pose proof (u8_range b) as Hb.
replace (8 * Z.of_nat (S (length bs)))%Z with (8 * Z.of_nat (length bs) + 8)%Z by lia.
rewrite Z.pow_add_r by lia.
assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)
= (bv_unsigned b + bytes_le_to_Z bs * 2 ^ 8)%Z).
{ rewrite Z.shiftl_mul_pow2 by lia.
rewrite <- Z.lxor_lor by
(apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8];
[ rewrite (Z.mul_pow2_bits_low) by lia; apply andb_false_r
| rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia; reflexivity ]).
rewrite Z.add_nocarry_lxor by
(apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8];
[ rewrite (Z.mul_pow2_bits_low) by lia; apply andb_false_r
| rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia; reflexivity ]).
reflexivity. }
rewrite Hlor. change (2^8)%Z with 256%Z. nia.
Qed.
#[using="Type"] Lemma Z_to_bv_u_plus0 : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'Z?yR0%211'D&Z>&W0&ZDr1%2271z%5221%72:1%93:15p_<;1").
Proof. intro a. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
#[using="Type"] Lemma rdn_pointwise : ltac2:(TCodec.tc2 tcn__SymExec2Sound "R3':'Q7%211'Z?yR0%211'<y8%511%311pf251';%<14'D&9r1%2281r3%53721&W4&W0&ZD%12B5&W>r4%211%6241&W@+2+R0%3221%<251&Kr6%22C1r8&Z>%@2Q14r2%@11%D231%52Q51%711(2&Nr5z%;2Q81%44Q8:31%62Q91%Q53Q981p0A1pa<Q91%Q?1Q9&REr7%24E1;G%>2Q=Q1%Q=3521p071p0M1p0Q;1p`6QB1p_<QJ1pbFQE1pb@QG1pdBR01").
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
- destruct bs; [reflexivity | cbn in Hlen; lia].
- destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
cbn [rdn].
pose proof (Hpt 0%nat ltac:(lia)) as H0. cbn [nth Z.of_nat] in H0.
rewrite Z_to_bv_u_plus0 in H0. rewrite H0.
destruct n as [|n'].
+ destruct bs'; [reflexivity | cbn in Hlen; lia].
+ assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH (a + 1) bs'); [reflexivity | lia | lia |].
intros j Hj. rewrite Hu1.
replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
rewrite (Hpt (S j)) by lia. reflexivity.
Qed.
#[using="Type"] Lemma rdn_img : ltac2:(TCodec.tc2 tcn__SymExec2Sound "R?':'Q7%211'Z?yR0%211'<y8%511%311pf251';'Q2%=11&W4&W0&ZDr2%22>1&W>r3%211%7241&W@+2+R0%3221%=251&Kr1r5%3221'Dr7&Z>%C2O5%A1C%F221%42Q21%611(0%11Q1%:3Q131p0<1pa<Q11%Q71Q0&SNr4%Q02Q<1%33@1C(2%12Q6O%D3731'E%QF1Q>'C%QB12&REr9r8r6%44321L%<28Q1%O3721&M%QA1QJ%24QJQF1Q5%Q33QF1Q5%=251q`6?1%A2@1p0C1p0L1p0Q>1pf:QM1p_<R61pbFR11pb@R31pdBR<1").
Proof.
intros segs mem n. induction n as [|n IH]; intros a zs Hnw Hpt Himg.
- cbn in Himg. injection Himg as <-. exists []. split; reflexivity.
- cbn [img_bytes] in Himg. rewrite Z_to_bv_bv_unsigned in Himg.
destruct (seg_rom segs a) as [b|] eqn:Hrom; [|discriminate].
destruct (img_bytes segs (bv_unsigned a + 1) n) as [zr|] eqn:Hrest; [|discriminate].
injection Himg as <-.
pose proof (Hpt 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z_to_bv_u_plus0 in H0.
cbn [rdn]. rewrite H0, Hrom.
destruct n as [|n'].
+ cbn in Hrest. injection Hrest as <-. cbn. exists [b]. split; reflexivity.
+ assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
destruct (IH (a + 1) zr) as (bs & Hbs & Hmap); [lia | | rewrite Hu1; exact Hrest |].
{ intros j Hj. rewrite Hu1.
replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
apply Hpt. lia. }
rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; rewrite Hmap; reflexivity].
Qed.
#[using="Type"] Lemma zbytes_map : ltac2:(TCodec.tc2 tcn__SymExec2Sound "B':'Z?y8%211%411'D'Q2&UN&M&ZD%118r1%449621%611&Q5%114%;3:31p`6=1").
Proof. induction bs as [|b bs IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
#[using="Type"] Lemma bytes_le_to_Z_repeat0 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "@';'D'Q2&Q5&O'Z?y8%211&Z>z%2241r1%83521%:11%=3<15pbF?1").
Proof.
induction n as [|n IH]; cbn [repeat bytes_le_to_Z]; [reflexivity|].
rewrite IH. reflexivity.
Qed.
#[using="Type"] Lemma extz_0 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "<'5';'D'Q2&V6r2r1z%43321%73612pbF91pe>;1").
Proof.
intros sx n. unfold extz. destruct sx; [|reflexivity].
unfold bv_swrap, bv_wrap. rewrite Z.add_0_l.
rewrite Z.mod_small; [lia|].
unfold bv_half_modulus. split.
- apply Z.div_pos; [apply Z.lt_le_incl, bv_modulus_pos | lia].
- apply Z.div_lt_upper_bound; [lia|]. pose proof (bv_modulus_pos (8 * N.of_nat n)). lia.
Qed.
Definition load_result (sz : msize) (sx : bool) (bs : list byte) : word :=
match sz with
| SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
| SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
| SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
| SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
end.
Definition eff_sx (sz : msize) (sx : bool) : bool :=
match sz with SZ8 => false | _ => sx end.
#[using="Type"] Lemma step_load : forall segs regs pc mem rom w sz sx rd rs (imm : bv 12) bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w sz sx rd rs imm bs Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4;
destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
#[using="Type"] Lemma bv_extract0_lit : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Q1'Q2'D'Z?r2%211&ZAyR0w&Z>r1%2241%645481%4293%<3921'Bp021peF@1pb>B1").
Proof. auto. Qed.
#[using="Type"] Lemma extract0_Z_to_bv64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "D'Q1'Q2&VOr2yR0%3221'D'Z?r3%211&ZAw&Z>%129:%44:361%327<%:3721p0<1peFA1pb>C1").
Proof.
intros m u Hm. apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned.
rewrite Z.shiftr_0_r. unfold bv_wrap.
unfold bv_modulus.
rewrite <- Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
- reflexivity.
- exists (2 ^ (Z.of_N 64 - Z.of_N m))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
#[using="Type"] Lemma zext64_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q1'Q1'Q2&VOr2yR0%3221'C&W4z%2216&W8&W@+2&W=r3%211%5241%72>1%<291'D'Z?%11A&R8r4&Z>%122;%433F1%32G=%93721p0;1p0I1peFN1pb>Q01").
Proof.
intros m u Hm Hu. rewrite zext64_lit. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus. lia.
Qed.
#[using="Type"] Lemma sext64_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q3'Q1'Q2&VOr2yR0%3221'C&W4z%2216&W8&W@+2&W=r3%211%5241%72>1%<291'D'Z?%11A&R7r4&Z>%122;%433F1&ZC%125>%52I1%;3941p0=1p0K1peFQ01pb>Q21").
Proof.
intros m u Hm Hu. rewrite sext64_lit. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned.
rewrite bv_wrap_small; [reflexivity | unfold bv_modulus; lia].
Qed.
#[using="Type"] Lemma load_result_val : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q4'R4'5':'Z?y8%211%411'D';&9r1%2261&TKr3%211%83741yR0%>11&V9r4r2%33281&Z>&V6&V2%126<%>17&Q5%118%63431%82>1%H3>:1p0A1p`6K1pe>Q11pe@Q31").
Proof.
intros sz sx bs Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
unfold load_result, le_bytes_to_word, extz, eff_sx.
destruct sz; cbn [msize_bytes] in *.
- rewrite extract0_Z_to_bv64 by lia. destruct sx.
+ rewrite sext64_small by (cbn; lia). reflexivity.
+ rewrite zext64_small by (cbn; lia). reflexivity.
- rewrite extract0_Z_to_bv64 by lia. destruct sx.
+ rewrite sext64_small by (cbn; lia). reflexivity.
+ rewrite zext64_small by (cbn; lia). reflexivity.
- rewrite extract0_Z_to_bv64 by lia. destruct sx.
+ rewrite sext64_small by (cbn; lia). reflexivity.
+ rewrite zext64_small by (cbn; lia). reflexivity.
- rewrite extract0_Z_to_bv64 by lia. reflexivity.
Qed.
#[using="Type"] Lemma step_store : ltac2:(TCodec.tc2 tcn__SymExec2Sound "S9':'Q7%211&R6y5'Z?yR0%211%5241'<y8%611%311p061yQ0%:11'R4%<1=y<%>11'D%<16&Q9r:r8%3221(2r5%22=1%93841'5&Q:r6%211(7%?3521'>'R3'Q2%3221%O11&Q@r7%211(=(R0r4r3%34@E21+4%64=<21%I2<1%Q03<91&Q>r=&RF&RCr<%221J&ZB%12Q:>%6231&TK%11E%;4:Q931(@%Q>3Q421'Q;'Q<%211&Q=r>&RDvX<r;%352EB1QD%6251(Q8%G2EM&RA%H2JQ6%F2QOQF%K221&Q?%F1QL%M2OQE%3221%83=51%@5?Q2:1R1%<2E1%R63E>1p0I1p0Q81p0QJ1p0R11pa:R<1pd8R?1pd6R@1pe@RB1peJRD1pd2RG1pb@RH1pc6RO1pcDRO1pdBS61").
Proof.
intros segs regs pc mem rom w sz rs1 rs2 imm Hf He Hd Hok.
destruct sz; cbn [msize_bytes] in *.
- eapply step_sb; eassumption.
- eapply step_sh_val; eassumption.
- eapply SeqExec.step_sw_val; eassumption.
- eapply step_sd_val; eassumption.
Qed.
#[using="Type"] Lemma scs_denot_cons : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q3':'Q7%211'Z?yR0%211'<y8%511%311p051'SB'U?%=11&F&V>r5r4r3(6r2r1%33:21%847651'C&V=%14:986%<4;:96%4221%?261paNA1pd:C1pR8E1p_NG1pdBQ01").
Proof.
intros. unfold scs_denot. split.
- intros H. inversion H; auto.
- intros [A B]. constructor; auto.
Qed.
#[using="Type"] Lemma scs_denot_app : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q2':'Q7%211'Z?yR0%211'<y8%511%311p051'SB'U?%=11&F&V>r5r4r3&4r2r1%33:21%847651'C%:49875%;4:985%3221%>251pb4@1pb2A1pR8D1p_NF1pdBO1").
Proof. intros. unfold scs_denot. apply Forall_app. Qed.
#[using="Type"] Lemma log_lookup_acc : forall kn log rb rk n sx hints acc,
match log_lookup kn log rb rk n sx hints acc with
| LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
| LStuck => True
end.
Proof.
intros kn. induction log as [|[[kb kk] w v] rest IH]; intros rb rk n sx hints acc; cbn [log_lookup].
- exists []. reflexivity.
- destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) as [d| | |].
+ exists []. reflexivity.
+ apply IH.
+ exact I.
+ destruct (ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH|].
destruct hints as [|[|] hs].
* specialize (IH rb rk n sx (tl (@nil bool)) (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)).
destruct (log_lookup kn rest rb rk n sx (tl []) _) as [v0 scs h|scs h|]; try exact I;
destruct IH as [pre ->]; exists (pre ++ [SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w)]);
rewrite <- app_assoc; reflexivity.
* specialize (IH rb rk n sx (tl (true :: hs)) (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)).
destruct (log_lookup kn rest rb rk n sx (tl (true :: hs)) _) as [v0 scs h|scs h|]; try exact I;
destruct IH as [pre ->]; exists (pre ++ [SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w)]);
rewrite <- app_assoc; reflexivity.
* exact I.
Qed.
#[using="Type"] Lemma find_range_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QF':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&V8r7r6r5r4%544321'D'>%1299%B11&SL%1287(2(=r3r2%34AA21%5291%<3971'C&W4&ZD&S@r8%221E%42Q41%62F1%722=%9221p0;1p0I1p`NQ01pb8Q11p`@Q31paJQ51pTNQ81pR8QA1pdBQC1").
Proof.
intros segs E M kn e lo hi Hkn. induction kn as [|K rest IH]; cbn [find_range]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | | |e' lo' hi'| |]; try (apply IH; assumption).
destruct (expr_eqb e e') eqn:Heq.
- injection H as <- <-. apply expr_eqb_eq in Heq. subst e'. exact HK.
- apply IH; assumption.
Qed.
#[using="Type"] Lemma u_lit64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "='Q2'D&ZDyR0&Z>r1%2231%5241&W;&UK%2251%:3;41pf8<1").
Proof. intros. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.
#[using="Type"] Lemma two64_eq : ltac2:(TCodec.tc2 tcn__SymExec2Sound "8'D'Q2&UK&W@+2+R0%3221%73651").
Proof. reflexivity. Qed.
#[using="Type"] Lemma u_add64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Z?yR0%211'D'Q2&ZD&R:(QAr2r1%43321%62:1&W;&W0%92=6%:2>6%3221&W@+2+R0%3221%9251%C3B;1pf4E1pf2F1").
Proof. intros. rewrite alu_add. unfold v_add. apply u_lit64. Qed.
#[using="Type"] Lemma u_sub64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Z?yR0%211'D'Q2&ZD&R:(QGr2r1%43321%62:1&W;&WA%92=6%:2>6%3221&W@+2+R0%3221%9251%C3B;1pf4E1pf2F1").
Proof. intros. rewrite alu_sub. unfold v_sub. apply u_lit64. Qed.
#[using="Type"] Lemma u_and64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Z?yR0%211'D'Q2&ZD&R:(QBr2r1%43321%62:1&W3%82<5%92=5%3221%=3<51pf4?1pf2@1").
Proof.
intros. rewrite alu_and. unfold v_and. rewrite u_lit64, two64_eq. apply Z.mod_small.
pose proof (u64_range x). pose proof (u64_range y). apply Z_land_range; lia.
Qed.
#[using="Type"] Lemma u_or64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Z?yR0%211'D'Q2&ZD&R:(QCr2r1%43321%62:1&W7%82<5%92=5%3221%=3<51pf4?1pf2@1").
Proof.
intros. rewrite alu_or. unfold v_or. rewrite u_lit64, two64_eq. apply Z.mod_small.
pose proof (u64_range x). pose proof (u64_range y). apply Z_lor_range; lia.
Qed.
#[using="Type"] Lemma u_xor64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Z?yR0%211'D'Q2&ZD&R:(QHr2r1%43321%62:1&W:%82<5%92=5%3221%=3<51pf4?1pf2@1").
Proof.
intros. rewrite alu_xor. unfold v_xor. rewrite u_lit64, two64_eq. apply Z.mod_small.
pose proof (u64_range x). pose proof (u64_range y). apply Z_lxor_range; lia.
Qed.
#[using="Type"] Lemma u_sltu64 : forall x y : word,
bv_unsigned (alu64 ALU_SLTU x y) = (if (bv_unsigned x <? bv_unsigned y)%Z then 1 else 0)%Z.
Proof.
intros. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu.
destruct (bv_unsigned x <? bv_unsigned y)%Z; reflexivity.
Qed.
#[using="Type"] Lemma u_slt64 : forall x y : word,
bv_unsigned (alu64 ALU_SLT x y) = (if (bv_signed x <? bv_signed y)%Z then 1 else 0)%Z.
Proof.
intros. rewrite alu_slt. unfold v_slt, c_lts, bv_lts.
destruct (bv_signed x <? bv_signed y)%Z; reflexivity.
Qed.
#[using="Type"] Lemma lit_shamt_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q4'SB'SG'Q2'D'<%113&T<r2%211(2r1%2291%93741'C&W;&ZDyR0&S@r4r3%3221%6251+R0%9221%E3F1A&W4z%221D&W8%12F7%A231%B271p0D1pd:O1p_HQ11pR8Q31").
Proof.
intros E b s H. destruct b; cbn [lit_shamt] in H; try discriminate. injection H as <-.
cbn [edenot]. rewrite u_lit64, two64_eq. split; [|apply Z.mod_pos_bound; lia].
apply Z.mod_mod_divide. exists (2 ^ 58)%Z. reflexivity.
Qed.
#[using="Type"] Lemma u_srl64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Z?yR0%211'D'Q2&ZD&R:(QFr2r1%43321%62:1&W1%82<5&W@+2&W;%<2@8+R0%3221%6251%9281%C3B;1pf4E1pf2F1").
Proof.
intros. rewrite alu_srl. unfold v_srl. rewrite u_lit64, two64_eq, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
pose proof (u64_range x). apply Z.mod_small.
assert (0 < 2 ^ (bv_unsigned y mod 64))%Z by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned x); [|lia].
apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
#[using="Type"] Lemma u_sll64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "K'Z?yR0%211'D'Q2&ZD&R:(QDr2r1%43321%62:1&W;&W<%92=6&W@+2%<2@8+R0%7221%5241%8271%7264%;221%E3D=1pf4G1pf2H1").
Proof.
intros. rewrite alu_sll. unfold v_sll. rewrite u_lit64, two64_eq, Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
reflexivity.
Qed.
#[using="Type"] Lemma u_sra64_nonneg : ltac2:(TCodec.tc2 tcn__SymExec2Sound "N'Z?yR0%211&W8&ZDr2%2251&W@+2+QO%3221%8251'D'Q2&R:(QEr3%3321<%>2A1&W1%@2C4&W;+R0%22A1%A2@1%6251%>3=81p0@1pf4J1pf2K1").
Proof.
intros x y Hx. rewrite alu_sra. unfold v_sra. rewrite bv_signed_small by exact Hx.
rewrite u_lit64, two64_eq, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
pose proof (u64_range x). apply Z.mod_small.
assert (0 < 2 ^ (bv_unsigned y mod 64))%Z by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned x); [|lia].
apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
#[using="Type"] Lemma swrap32_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "E'Q2'C&W4zr1%3221&W8&W@+2+O%3221%5271%;271'D&ZCyQ0r2%3221%53B12p071peBD1").
Proof.
intros t Ht. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. lia.
Qed.
#[using="Type"] Lemma swrap32_shift : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Q2'D&ZCyQ0&W0r2&W<r1&W@+2+Q0%3221%6251%9281%<2;1%=2<:%?3@21pa>A1peBB1").
Proof.
intros t k. unfold bv_swrap. f_equal. unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32)%Z.
replace (t + k * 2 ^ 32 + bv_half_modulus 32)%Z with (t + bv_half_modulus 32 + k * 2 ^ 32)%Z by lia.
apply Z.mod_add. lia.
Qed.
#[using="Type"] Lemma u_small_id : ltac2:(TCodec.tc2 tcn__SymExec2Sound "E'Q2'C&W4zr1%3221&W8&W@+2+R0%3221%5271%;271'D&W;r2&UK%3221%53B13p071peBD1").
Proof. intros. rewrite two64_eq. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma u_addw_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QC'Z?yR0%211'Q2'C&W4zr1%3221&W8&W@+2+O%3221%5271%;271'E'D&W0&ZDr5%22D1r4%42F1%6231r3&W<+Q0%B2A1%32F1%<251%>3L71qa>M1%A2N1&R7yQ0&R9(QA&R<%11C%21B%53421%837Q91/01Q9%I2Q;1%L3Q:1Dp0=1p0Q01peBQ=1pf4Q?1pf2Q@1").
Proof.
intros x y t Ht [k Hk]. rewrite w_addw. unfold v_addw. rewrite u_lit64, Hk, swrap32_shift, swrap32_small by lia.
apply u_small_id. lia.
Qed.
#[using="Type"] Lemma u_subw_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q<'Z?yR0%211'Q2'C&W4zr1%3221&W8&W@+2+O%3221%5271%;271'D&WA&ZDr4%22C1r3%42E1%6231r2%93F21&R7yQ0&R9(QG&R<r5%211%31>%63521%938Q21/01Q2%C2Q41%F3Q31Ap0>1p0I1peBQ61pf4Q81pf2Q91").
Proof.
intros x y t Ht Hk. rewrite w_subw. unfold v_subw. rewrite u_lit64, Hk, swrap32_small by lia.
apply u_small_id. lia.
Qed.
#[using="Type"] Lemma mod32_of_mod64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound ";'Q2'D&W;r1+R0%3221+Q0%5221%6252%83921pf8:1").
Proof. intros. apply Z.mod_mod_divide. exists 2%Z. reflexivity. Qed.
#[using="Type"] Lemma u_sllw_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QA'Z?yR0%211'Q2'D&W;&ZDr2%2271+R0%5221r1%83921&W8&W<r4%:2?1&W@+2+Q0%?2=1%4231%8261+O%7261%<231&R7yQ0&R9(QD&R<r5%211%31B%63521%938Q21/01Q2%O2Q41%Q02Q57r3%Q321E%H2G1%L241%Q73Q861p0C1p0Q11pd:Q;1pf4Q=1pf2Q>1").
Proof.
intros x y s Hs Hb. rewrite w_sllw. unfold v_sllw. pose proof (u64_range x).
assert (Hs' : (bv_unsigned y mod 32 = s mod 32)%Z) by (rewrite <- Hs; symmetry; apply mod32_of_mod64).
rewrite Hs', Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
assert (0 <= bv_unsigned x * 2 ^ (s mod 32))%Z by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
rewrite u_lit64, swrap32_small by lia. apply u_small_id. lia.
Qed.
#[using="Type"] Lemma u_srlw_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QF'Z?yR0%211'Q2'D&W;&ZDr2%2271+R0%5221r1%83921&W8r4%92>1&W@+2+Q0%3221%7251&W1r5%A2F1r3%D217%:291%6241+O%=2<1%A231&R7yQ0&R9(QF&R<r6%211%31@%63521%938Q71/01Q7%Q42Q91%Q52Q:7%Q72NJ%M2L1%I231%Q;3Q<51p0B1p0M1p0Q61pd:Q@1pf4QB1pf2QC1").
Proof.
intros x y s Hs Hx Hb. rewrite w_srlw. unfold v_srlw. pose proof (u64_range x).
assert (Hs' : (bv_unsigned y mod 32 = s mod 32)%Z) by (rewrite <- Hs; symmetry; apply mod32_of_mod64).
rewrite Hs', Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
rewrite bv_wrap32_mod, (Z.mod_small (bv_unsigned x)) by lia.
assert (0 <= bv_unsigned x / 2 ^ (s mod 32))%Z by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]]).
rewrite u_lit64, swrap32_small by lia. apply u_small_id. lia.
Qed.
#[using="Type"] Lemma u_sraw_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q>'Z?yR0%211'Q2'D&W;&ZDr2%2271+R0%5221r1%83921&W8r4%92>1&W@+2+O%3221%7251&R7yQ0&R9(QE&R<r5%211%31>%63521%938M1/01M%J2O1&W1%L2Q18r3+Q0%Q0221%F2E1%6251%Q43Q581p0E1p0N1pd:Q81pf4Q:1pf2Q;1").
Proof.
intros x y s Hs Hx. rewrite w_sraw. unfold v_sraw. pose proof (u64_range x).
assert (Hs' : (bv_unsigned y mod 32 = s mod 32)%Z) by (rewrite <- Hs; symmetry; apply mod32_of_mod64).
rewrite Hs', Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
rewrite (swrap32_small (bv_unsigned x)) by lia.
assert (Hp : (0 < 2 ^ (s mod 32))%Z) by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
assert (0 <= bv_unsigned x / 2 ^ (s mod 32))%Z by (apply Z.div_pos; lia).
assert (bv_unsigned x / 2 ^ (s mod 32) <= bv_unsigned x)%Z by (apply Z.div_le_upper_bound; [lia|nia]).
rewrite u_lit64, swrap32_small by lia. apply u_small_id. lia.
Qed.
#[using="Type"] Lemma u_mul64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Z?yR0%211'D'Q2&ZD&R=(QMr2r1%449321%62:1&W;&W<%92=6%:2>6%3221&W@+2+R0%3221%9251%C3B;1pf4E1pf2F1").
Proof. intros. rewrite m_mul. unfold v_mul. apply u_lit64. Qed.
#[using="Type"] Lemma u_mulhu64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Z?yR0%211'D'Q2&ZD&R=(QNr2r1%449321%62:1&W1&W<%92=6%:2>6%3221&W@+2+R0%3221%9251%C3B;1pf4E1pf2F1").
Proof.
intros. rewrite m_mulhu. unfold v_mulhu. rewrite u_lit64, Z.shiftr_div_pow2 by lia.
pose proof (u64_range x). pose proof (u64_range y). apply u_small_id.
split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
#[using="Type"] Lemma u_divu64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Z?yR0%211&W8z&ZDr1%2261%5241'D'Q2&R=(QLr3r2%44>321%;2?1&W1%=2A5%>2B5%3221%<3;51p0>1pf4E1pf2F1").
Proof.
intros x y Hy. unfold mul_div. replace (bv_unsigned y =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_divu_unsigned.
Qed.
#[using="Type"] Lemma u_remu64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Z?yR0%211&W8z&ZDr1%2261%5241'D'Q2&R=(QOr3r2%44>321%;2?1&W;%=2A5%>2B5%3221%<3;51p0>1pf4E1pf2F1").
Proof.
intros x y Hy. unfold mul_div. replace (bv_unsigned y =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_modu_unsigned.
Qed.
#[using="Type"] Lemma u_ext_zx : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q=';'Z?yR0%211'C'D'Q2&ZD&SJ(7r3r2r1%544321%72<1&W;&W1%:2?5&W@+2&W<+8&W>%11=%4231%7261%:291%51@%8271%;2:1%?241%J3IA1&W4&WA+1%2261%42F1&UK%5214%72I1%Q4241%Q52:1peHQ71pbFQ;1pb8Q<1").
Proof.
intros lo n v. unfold ext_val, ext_Z. pose proof (u64_range v) as Hv.
set (q := (bv_unsigned v / 2 ^ (8 * Z.of_nat lo))%Z).
assert (Hw : (0 < 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.mod_pos_bound q _ Hw) as Hm.
assert (Hq : (0 <= q)%Z) by (subst q; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
assert (Hle : (q mod 2 ^ (8 * Z.of_nat n) <= bv_unsigned v)%Z).
{ apply Z.le_trans with q; [apply Z.mod_le; lia|]. subst q. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
rewrite <- (Z.mul_1_l (bv_unsigned v)) at 1. apply Z.mul_le_mono_nonneg_r; [lia|].
assert (0 < 2 ^ (8 * Z.of_nat lo))%Z by (apply Z.pow_pos_nonneg; lia). lia. }
rewrite u_lit64. rewrite u_small_id by lia. rewrite two64_eq. lia.
Qed.
#[using="Type"] Lemma u_ext_zx0_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "O';'Z?yR0%211&W8&ZDr1%2251&W@+2&W<+8&W>r2%211%5241%8271%=2:1'D'Q2&SJ(7(1r3%44321;%D2G1%E2H=%93821p0;1peHJ1pbFN1").
Proof.
intros n v Hv. destruct (u_ext_zx 0 n v) as (H & _ & _). rewrite H.
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r. apply Z.mod_small. pose proof (u64_range v). lia.
Qed.
#[using="Type"] Lemma u_ext_sx0_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q1';'Z?yR0%211&W8&ZDr1%2251&W1&W@+2&W<+8&W>r2%211%5241%8271%:218%?2<1'D'Q2&SJ(@(1r3%44321<%F2I1%G2J>%93821p0;1peHL1pbFQ01").
Proof.
intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
assert (Hw : (0 < 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hhalf : (2 ^ (8 * Z.of_nat n) / 2 <= 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.div_le_upper_bound; lia).
rewrite (Z.mod_small (bv_unsigned v)) by lia.
rewrite bv_swrap_small.
- rewrite u_lit64. apply u_small_id. lia.
- unfold bv_half_modulus, bv_modulus. replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia. lia.
Qed.
#[using="Type"] Lemma u_blob_zx : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q5':'Z?y8%211%411'Q2';'C&W4&ZDyR0&S4(7r3r2r1%544321%8271&WA&W@+2&W<+8&W>%119%4231%7261+1%:221%E2<1&UK%=214%H2?1%J241pbFL1pa6N1p`6Q01").
Proof.
intros bs i n. unfold blob_val. pose proof (bytes_le_to_Z_bound (blob_bytes bs i n)) as Hb.
assert (Hlen : (length (blob_bytes bs i n) <= n)%nat) by (unfold blob_bytes; rewrite firstn_length; apply Nat.le_min_l).
assert (Hp : (2 ^ (8 * Z.of_nat (length (blob_bytes bs i n))) <= 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.pow_le_mono_r; lia).
rewrite u_lit64. pose proof (Z.mod_pos_bound (bytes_le_to_Z (blob_bytes bs i n)) two64 ltac:(rewrite two64_eq; lia)).
pose proof (Z.mod_le (bytes_le_to_Z (blob_bytes bs i n)) two64 ltac:(lia) ltac:(rewrite two64_eq; lia)). lia.
Qed.
#[using="Type"] Lemma clampi_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q4'Z?yR0%211'Q2'C&W4r4&ZDr5%2281%5241r3%7231%9231'D'>%12==&S6(=%14@@;=%311r2%44CC;1%93731r7%B2H1%E2D1%F22@%H221p061p0A1pa0L1pb:M1p`NN1pb8O1peHQ11").
Proof.
intros v lo hi lo' hi' H Hc. unfold clampi in Hc. injection Hc as <- <-. pose proof (u64_range v). rewrite two64_eq. lia.
Qed.
#[using="Type"] Lemma mod_wrap_hi : ltac2:(TCodec.tc2 tcn__SymExec2Sound "G'Q2'C&W4&W@+2+R0%3221r1%6221&W8&W0%1255%3251%<251'D&W;r2%221;&WA%123=%63D31p081peBF1").
Proof. intros t Ht. symmetry. apply (Z.mod_unique_pos t (2 ^ 64) 1); lia. Qed.
#[using="Type"] Lemma mod_wrap_neg : ltac2:(TCodec.tc2 tcn__SymExec2Sound "H'Q2'C&W4&W?&W@+2+R0%3221%511r1%8221&W8z%2241%=241'D&W;r2%221;&W0%123=%63E31p081peBG1").
Proof. intros t Ht. symmetry. apply (Z.mod_unique_pos t (2 ^ 64) (-1)); lia. Qed.
#[using="Type"] Lemma mask_cover_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "@'Q2'C&W4zr1%3221r2%5231%7231&TAr3%211%:261p051pf2>1p`L?1").
Proof.
intros h x Hx. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eq_dec h 0) as [->|Hne].
- replace (2 ^ Z.log2_up (0 + 1) - 1)%Z with 0%Z by reflexivity. lia.
- pose proof (Z.log2_up_spec (h + 1) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma pow_cover : ltac2:(TCodec.tc2 tcn__SymExec2Sound "D'Q2&W4zr1%3221'C&W0r2+1%3221&W@+2&W6%114%4231%>261%?2>3%<221p0>1p`LC1").
Proof.
intros h Hh. split; [|apply Z.log2_up_nonneg].
destruct (Z.eq_dec h 0) as [->|Hne].
- replace (2 ^ Z.log2_up (0 + 1))%Z with 1%Z by reflexivity. lia.
- pose proof (Z.log2_up_spec (h + 1) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma lor_cover : ltac2:(TCodec.tc2 tcn__SymExec2Sound "G'Q2'C&W4zr2%3221r3%5231%7231r4%8261%:261&W7%1247&TAr5%211%?241p071p0;1pf4D1pf2E1p`LF1").
Proof.
intros h x y Hx Hy. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (pow_cover h ltac:(lia)) as [Hh Hk]. set (k := Z.log2_up (h + 1)) in *.
enough (Z.lor x y < 2 ^ k)%Z by lia.
apply (Z_bounded_by_bits k); [lia | apply Z.lor_nonneg; lia |].
intros i Hi. rewrite Z.lor_spec.
rewrite (Z_testbit_high k x i) by lia. rewrite (Z_testbit_high k y i) by lia. reflexivity.
Qed.
#[using="Type"] Lemma lxor_cover : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Q2'C&W4zr2%3221r3%5231%7231r4%8261%:261&W:%1247%<2;1&TAr5%211%@251%B251p091p0=1pf4F1pf2G1p`LH1").
Proof.
intros h x y Hx Hy. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (pow_cover h ltac:(lia)) as [Hh Hk]. set (k := Z.log2_up (h + 1)) in *.
assert (Hnn : (0 <= Z.lxor x y)%Z) by (apply Z.lxor_nonneg; lia).
enough (Z.lxor x y < 2 ^ k)%Z by lia.
apply (Z_bounded_by_bits k); [lia | exact Hnn |].
intros i Hi. rewrite Z.lxor_spec.
rewrite (Z_testbit_high k x i) by lia. rewrite (Z_testbit_high k y i) by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_le_l : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'Q2&W4zr2%3221&W3r4r3%3221%8213p061p071p_H<1p_<=1").
Proof.
intros a b Ha Hb.
pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as Hal.
rewrite Z.lor_ldiff_and in Hal.
assert (Hand : Z.land (Z.ldiff a b) (Z.land a b) = 0%Z).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
rewrite Hand in Hal.
assert (0 <= Z.ldiff a b)%Z by (apply Z.ldiff_nonneg; lia). lia.
Qed.
#[using="Type"] Lemma land_le_r : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'Q2&W4zr2%3221&W3r4r3%3221%8212p061p071p_H<1p_<=1").
Proof. intros. rewrite Z.land_comm. apply land_le_l; assumption. Qed.
#[using="Type"] Lemma lor_ge_l : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'Q2&W4zr2%3221r4&W7r3%2231%8241p061p071pf4<1pf2=1").
Proof. intros. pose proof (Z.add_lor_land x y). pose proof (land_le_r x y H H0). lia. Qed.
#[using="Type"] Lemma lor_ge_r : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'Q2&W4zr2%3221r3&W7r4%2213%8241p061p071pf4<1pf2=1").
Proof. intros. rewrite Z.lor_comm. apply lor_ge_l; assumption. Qed.
End FPX_1.
Ltac fr_case Hkn H :=
lazymatch type of H with
| match find_range ?kn ?e with _ => _ end = _ =>
destruct (find_range kn e) as [[flo fhi]|] eqn:Hfr;
[ pose proof (find_range_sound _ _ _ _ _ _ _ Hkn Hfr) as Hb; unfold clampi in H;
injection H as <- <-; lazymatch goal with |- context [bv_unsigned ?v] => pose proof (u64_range v) end; unfold two64 in *; lia
| clear Hfr ]
end.
Ltac er_both IHe1 IHe2 Hkn H :=
destruct (erange _ _) as [[al ah]|] eqn:He1 in H; [|try discriminate];
destruct (erange _ _) as [[bl bh]|] eqn:He2 in H; [|try discriminate];
try (specialize (IHe1 al ah Hkn eq_refl)); try (specialize (IHe2 bl bh Hkn eq_refl)).
Section FPX_2. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma lin_range_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QI'SB'SG'<'>'Q2%2211%411pf261'Dr4r3%211(2(=r2r1%34<<21%52<1%:3<71'C&W4&ZDyR0&S@r6%221@%5241%72A1%822>%:221p0<1p`NK1pb8L1p_<Q01':%Q02OQ2%211&T:%13>ML%O3Q11F&W0r5&VMr8%221Q3%5241%J2Q41%K22Q1%M221p0:1p`NQ>1pb8Q?1peD@1p`8QA1p0E1pd0Q@1pR8QH1").
Proof.
intros E rng Hrng c ts. induction ts as [|[k a] rest IHts]; intros lo hi H; cbn [lin_range tden] in H |- *.
- injection H as <- <-. lia.
- destruct (rng a) as [[al ah]|] eqn:Ha; [|discriminate].
destruct (lin_range rng c rest) as [[lo' hi']|] eqn:Hr; [|discriminate].
pose proof (Hrng a al ah Ha) as Hb. pose proof (IHts lo' hi' eq_refl) as Hrest. unfold uE.
destruct (Z.leb 0 k) eqn:Hk; injection H as <- <-.
+ apply Z.leb_le in Hk. nia.
+ apply Z.leb_gt in Hk. nia.
Qed.
#[using="Type"] Lemma erange_f_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QI':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11';'SG'Q2&VHr8r7r6r5%544321'D'>%1299%C11&SDr4%23891(2(=r3r2%34BB21%52:1%=3:71'C&W4&ZD&S@r9%221E%42Q61%62@1%722=%9221p0;1p0J1pcHQ11pcLQ21p`@Q41p`HQ61paJQ81pTNQ;1pR8QD1pdBQF1").
Proof.
intros segs E M kn fuel. induction fuel as [|fuel IH]; intros e rlo rhi Hkn H; [discriminate|].
cbn [erange_f] in H. fr_case Hkn H.
lazymatch type of H with
| match ?X with _ => _ end = _ =>
destruct X as [[llo lhi]|] eqn:Hlin;
[ injection H as <- <-;
destruct (lin_trivial (lin_of e)) eqn:Htriv; [discriminate|];
destruct (lin_range (erange_f fuel kn) (fst (lin_of e)) (snd (lin_of e))) as [[lo1 hi1]|] eqn:Hlr; [|discriminate];
destruct (Z.leb 0 lo1 && Z.ltb hi1 two64)%bool eqn:Hc; [|discriminate];
injection Hlin as <- <-; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2;
unfold two64 in Hc2;
pose proof (lin_range_sound E (erange_f fuel kn) (fun a lo hi Ha => IH a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb;
pose proof (lin_of_sound E e) as [q Hq]; unfold lden in Hq;
destruct (lin_of e) as [c ts]; cbn [fst snd] in *; unfold uE in Hq;
pose proof (u64_range (edenot E e)); nia
| clear Hlin ]
end.
pose proof (fun a => IH a) as IHe1. pose proof (fun a => IH a) as IHe2. pose proof (fun a => IH a) as IHe.
destruct e; cbn [edenot]; unfold two64 in *.
- injection H as <- <-. rewrite u_lit64. unfold two64. lia.
- discriminate.
-
pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
destruct op.
+ rewrite u_add64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
destruct (ah + bh <? 2 ^ 64)%Z eqn:C1.
* injection H as <- <-. rewrite Z.mod_small by lia. lia.
* destruct (2 ^ 64 <=? al + bl)%Z eqn:C2; [|discriminate]. injection H as <- <-.
rewrite mod_wrap_hi by lia. lia.
+ rewrite u_sub64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
destruct (bh <=? al)%Z eqn:C1.
* injection H as <- <-. rewrite Z.mod_small by lia. lia.
* destruct (ah <? bl)%Z eqn:C2; [|discriminate]. injection H as <- <-.
rewrite mod_wrap_neg by lia. lia.
+ rewrite u_sll64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr]. rewrite Hsv.
destruct (ah * 2 ^ s <? 2 ^ 64)%Z eqn:C1; [|discriminate]. injection H as <- <-.
assert (Hp : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
rewrite Z.mod_small by nia. nia.
+ rewrite u_slt64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1;
[destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2|];
[ specialize (IHe1 e1 al ah Hkn He1); specialize (IHe2 e2 bl bh Hkn He2)
| injection H as <- <-; destruct (bv_signed (edenot E e1) <? bv_signed (edenot E e2))%Z; lia
| injection H as <- <-; destruct (bv_signed (edenot E e1) <? bv_signed (edenot E e2))%Z; lia ].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C0 end.
* apply andb_prop in C0 as [Ca Cb].
rewrite (bv_signed_small (edenot E e1)) by lia. rewrite (bv_signed_small (edenot E e2)) by lia.
set (x := bv_unsigned (edenot E e1)) in *. set (y := bv_unsigned (edenot E e2)) in *.
destruct (ah <? bl)%Z eqn:C1; [injection H as <- <-; destruct (x <? y)%Z eqn:C; lia|].
destruct (bh <=? al)%Z eqn:C2; injection H as <- <-; destruct (x <? y)%Z eqn:C; lia.
* injection H as <- <-. destruct (bv_signed (edenot E e1) <? bv_signed (edenot E e2))%Z; lia.
+ rewrite u_sltu64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1;
[destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2|];
[ specialize (IHe1 e1 al ah Hkn He1); specialize (IHe2 e2 bl bh Hkn He2)
| injection H as <- <-; destruct (bv_unsigned (edenot E e1) <? bv_unsigned (edenot E e2))%Z; lia
| injection H as <- <-; destruct (bv_unsigned (edenot E e1) <? bv_unsigned (edenot E e2))%Z; lia ].
set (x := bv_unsigned (edenot E e1)) in *. set (y := bv_unsigned (edenot E e2)) in *.
destruct (ah <? bl)%Z eqn:C1; [injection H as <- <-; destruct (x <? y)%Z eqn:C; lia|].
destruct (bh <=? al)%Z eqn:C2; injection H as <- <-; destruct (x <? y)%Z eqn:C; lia.
+ rewrite u_xor64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
injection H as <- <-. apply lxor_cover; lia.
+ rewrite u_srl64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr]. rewrite Hsv.
injection H as <- <-.
assert (Hp : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
split; apply Z.div_le_mono; lia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr].
destruct (ah <? 2 ^ 63)%Z eqn:C1; [|discriminate]. injection H as <- <-.
rewrite u_sra64_nonneg by lia. rewrite Hsv.
assert (Hp : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
split; apply Z.div_le_mono; lia.
+ rewrite u_or64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
injection H as <- <-. split.
* apply Z.max_lub; [eapply Z.le_trans; [|apply lor_ge_l; lia] | eapply Z.le_trans; [|apply lor_ge_r; lia]]; lia.
* apply lor_cover; lia.
+ rewrite u_and64.
pose proof (Z.land_nonneg (bv_unsigned (edenot E e1)) (bv_unsigned (edenot E e2))) as Hnn.
pose proof (land_le_l _ _ (proj1 R1) (proj1 R2)) as Hl1.
pose proof (land_le_r _ _ (proj1 R1) (proj1 R2)) as Hl2.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1;
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; try discriminate;
try specialize (IHe1 e1 al ah Hkn He1); try specialize (IHe2 e2 bl bh Hkn He2);
injection H as <- <-; lia.
-
pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
destruct op; try discriminate.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
revert H. unfold zsigned64, two64.
destruct (bl =? bh)%Z eqn:Ceq;
[destruct (2 ^ 63 <=? bl)%Z eqn:Chi; destruct (2 ^ 63 <=? bh)%Z eqn:Chi2|]; intros H;
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end;
injection H as <- <-; apply andb_prop in C1 as [Ca Cb];
first
[ rewrite (u_addw_small _ _ (bv_unsigned (edenot E e1) + (bv_unsigned (edenot E e2) - 2 ^ 64))%Z);
[lia | lia | exists (2 ^ 32)%Z; lia]
| rewrite (u_addw_small _ _ (bv_unsigned (edenot E e1) + bv_unsigned (edenot E e2))%Z);
[lia | lia | exists 0%Z; lia]
| exfalso; lia ].
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
rewrite (u_subw_small _ _ (bv_unsigned (edenot E e1) - bv_unsigned (edenot E e2))%Z); lia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-.
assert (Hp : (0 < 2 ^ (s mod 32))%Z) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
rewrite (u_sllw_small _ _ s Hsv) by nia. nia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
assert (Hp : (0 < 2 ^ (s mod 32))%Z) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
assert (Hsm : (bv_unsigned (edenot E e1) / 2 ^ (s mod 32) < 2 ^ 31)%Z).
{ apply orb_prop in Cb as [Cb|Cb].
- apply Z.div_lt_upper_bound; [lia|].
assert (2 <= 2 ^ (s mod 32))%Z.
{ replace 2%Z with (2 ^ 1)%Z at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
nia.
- apply Z.le_lt_trans with (bv_unsigned (edenot E e1)); [|lia].
apply Z.div_le_upper_bound; [lia|]. nia. }
rewrite (u_srlw_small _ _ s Hsv) by lia.
split; apply Z.div_le_mono; lia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-.
assert (Hp : (0 < 2 ^ (s mod 32))%Z) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
rewrite (u_sraw_small _ _ s Hsv) by lia.
split; apply Z.div_le_mono; lia.
-
pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
destruct op; try discriminate.
+ rewrite u_mul64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [C1 Cc]. apply andb_prop in C1 as [Ca Cb].
assert (bv_unsigned (edenot E e1) * bv_unsigned (edenot E e2) <= ah * bh)%Z by nia.
rewrite Z.mod_small by nia. nia.
+ rewrite u_mulhu64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
split; apply Z.div_le_mono; nia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct e2; try discriminate. cbn [edenot] in *.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. rewrite u_lit64 in *. unfold two64 in *.
rewrite u_divu64 by (rewrite u_lit64; unfold two64; lia). rewrite u_lit64. unfold two64.
split; apply Z.div_le_mono; lia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct e2; try discriminate. cbn [edenot] in *.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-.
rewrite u_remu64 by (rewrite u_lit64; unfold two64; lia). rewrite u_lit64. unfold two64.
pose proof (Z.mod_pos_bound (bv_unsigned (edenot E e1)) (z mod 2 ^ 64) ltac:(lia)).
pose proof (Z.mod_le (bv_unsigned (edenot E e1)) (z mod 2 ^ 64) ltac:(lia) ltac:(lia)). lia.
- discriminate.
-
pose proof (u64_range (edenot E e)) as R1.
destruct sx.
+ destruct lo; [|discriminate].
destruct (erange_f fuel kn e) as [[al ah]|] eqn:He1; [|discriminate].
specialize (IHe e al ah Hkn He1).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
rewrite u_ext_sx0_small by lia. lia.
+ destruct (u_ext_zx lo n (edenot E e)) as (_ & Hb1 & Hb2). unfold two64 in Hb2.
pose proof (u64_range (ext_val false lo n (edenot E e))) as R0.
destruct lo.
* destruct (erange_f fuel kn e) as [[al ah]|] eqn:He1.
-- specialize (IHe e al ah Hkn He1).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
++ injection H as <- <-. apply andb_prop in C1 as [Ca Cb]. rewrite u_ext_zx0_small by lia. lia.
++ injection H as <- <-. lia.
-- injection H as <- <-. lia.
* injection H as <- <-. lia.
-
destruct sx; [discriminate|]. injection H as <- <-.
destruct (u_blob_zx (eb E k) i n) as [Hb1 Hb2]. unfold two64 in Hb2.
pose proof (u64_range (blob_val false (eb E k) i n)). lia.
Qed.
#[using="Type"] Lemma erange_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QF':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&VHr7r6r5r4%544321'D'>%1299%B11&SC%1287(2(=r3r2%34AA21%5291%<3971'C&W4&ZD&S@r8%221E%42Q41%62F1%722=%9221p0;1p0I1pcHQ01pcLQ11p`@Q31paJQ51pTNQ81pR8QA1pdBQC1").
Proof. intros. eapply erange_f_sound; eassumption. Qed.
#[using="Type"] Lemma base_range_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QF':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&VHr7r6r5r4%544321'D'>%1299%B11&S3%1287(2(=r3r2%34AA21%5291%<3971'C&W4&ZD&S@r8%221E%42Q41%62F1%722=%9221p0;1p0I1p`NQ01pb8Q11p`@Q31paJQ51pTNQ81pR8QA1pdBQC1").
Proof.
intros segs E M kn e lo hi Hkn H. unfold base_range in H.
exact (erange_sound segs E M kn e lo hi Hkn H).
Qed.
#[using="Type"] Lemma sub_itv_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q5'SB'SG'Q2'U8'D'5&UEr5r4r3r2r1%6554321(@%:3921'C&W4&VDr7%221:(RNr6%221?%6251%8251&W0%123B%228A%<221%>251p0@1pb>M1p`8M1pbFO1pa>Q01p_HQ21pR8Q41").
Proof.
intros E b k n [cb ck] m H. unfold sub_itv in H. cbn [a_base a_off] in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply expr_eqb_eq in H1. subst cb. apply Z.leb_le in H2. apply Z.leb_le in H3.
unfold estart. cbn [a_base a_off]. lia.
Qed.
#[using="Type"] Lemma kdisj_apart_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QL':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&VHr:r9r8r7%544321'D'5&T2r6r5r4r3r2%67;:54321(@%:3921'G&W4&W0&VDr;(RN%12DC%4231%621@%42@?%7261%:231%:22A%<216%>231p0@1p0L1pbLQ31paBQ41p_LQ61pbJQ61pa@Q71p_JQ91paJQ;1pTNQ>1pR8QG1pdBQI1").
Proof.
intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn. induction kn as [|K rest IH]; cbn [kdisj_apart]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | | | | |c1 m1 c2 m2]; try (apply IH; assumption).
apply orb_prop in H as [H|H]; [|apply IH; assumption].
cbn [kentry_ok] in HK.
apply orb_prop in H as [H|H]; apply andb_prop in H as [Ha Hb];
apply (sub_itv_sound E) in Ha as [Ha1 Ha2]; apply (sub_itv_sound E) in Hb as [Hb1 Hb2]; lia.
Qed.
#[using="Type"] Lemma ranges_apart_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QL':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&VHr:r9r8r7%544321'D'5&U1r6r5r4r3r2%67;:54321(@%:3921'G&W4&W0&VDr;(RN%12DC%4231%621@%42@?%7261%:231%:22A%<216%>231p0@1p0L1pbLQ31paBQ41p_LQ61pbJQ61pa@Q71p_JQ91paJQ;1pTNQ>1pR8QG1pdBQI1").
Proof.
intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold ranges_apart in H.
apply orb_prop in H as [H|H]; [|eapply kdisj_apart_sound; eassumption].
destruct (base_range kn b1) as [[lo1 hi1]|] eqn:H1; [|discriminate].
destruct (base_range kn b2) as [[lo2 hi2]|] eqn:H2; [|discriminate].
pose proof (base_range_sound segs E M kn b1 lo1 hi1 Hkn H1) as [A1 B1].
pose proof (base_range_sound segs E M kn b2 lo2 hi2 Hkn H2) as [A2 B2].
unfold estart. cbn [a_base a_off].
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
#[using="Type"] Lemma know_lookup_acc : forall segs kn rb rk n sx hints acc,
match know_lookup segs kn rb rk n sx hints acc with
| LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
| LStuck => True
end.
Proof.
induction kn as [|K rest IH]; intros rb rk n sx hints acc; cbn [know_lookup].
- exists []. reflexivity.
- assert (Hnil : exists pre : list sidecond, acc = pre ++ acc) by (exists []; reflexivity).
assert (Hone : forall s, exists pre : list sidecond, s :: acc = pre ++ acc)
by (intros s; exists [s]; reflexivity).
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2]; [ | | | | apply IH | apply IH | apply IH | apply IH].
+ destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); first [exact I | apply IH | apply Hnil | apply Hone].
+ destruct len; first [ destruct (rel_lit rb rk (Z.of_nat n) kb kk (z mod 2^64)%Z); first [exact I | apply IH | apply Hnil | apply Hone | destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone]]
| destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone] ].
+ destruct (expr_eqb rb kb); [|apply IH].
destruct (Z.leb kk rk); [|apply IH].
destruct len; first [ destruct (Z.leb (rk + Z.of_nat n) (kk + (z mod 2^64)%Z)); [apply Hnil|]; destruct (Z.leb (kk + (z mod 2^64)%Z) rk); [apply IH | exact I]
| destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone] ].
+ destruct rb; try apply IH. destruct z; try apply IH.
destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool; [|apply IH].
destruct (img_bytes segs rk n); [apply Hnil | exact I].
Qed.
#[using="Type"] Lemma rel_lit_inside : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QC'SB'SG'Q2'D'U0&U2r7r6r5r4r3r2%76654321(RMr1%211%=3<41'Cr8%@3B1;&WA%12?<%C3D;1&W4%12?B&W0%12DC%22BA%5221&VDr9(RN%12>J%4231%32JI%6251%;21I%Q23Q341%E2:1%F2?1%G2B1%H2F1p0J1p`>Q91paJQ:1paHQ;1paFQ=1pcNQ=1pcJQ>1pc@Q@1pR8QB1").
Proof.
intros E rb rk rn kb kk kn d H. unfold rel_lit in H.
destruct (expr_eqb rb kb) eqn:Heq; [|discriminate].
apply expr_eqb_eq in Heq. subst kb.
destruct (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool eqn:Hin.
- injection H as <-. apply andb_prop in Hin as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold estart. cbn [a_base a_off]. repeat split; lia.
- destruct (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool; discriminate.
Qed.
#[using="Type"] Lemma rel_lit_disjoint : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q:'SB'SG'Q2'D'U0&U2r6r5r4r3r2r1%76654321(RL%;3:21'Cr7%>3@19'G&W4&W0&VDr8(RN%128B%4231%621C%42CB%7261%:231%:22D%<216%>231%B2@1p0D1paJQ11paHQ21paFQ41pcNQ41pcJQ51pc@Q71pR8Q91").
Proof.
intros E rb rk rn kb kk kn H. unfold rel_lit in H.
destruct (expr_eqb rb kb) eqn:Heq; [|discriminate].
apply expr_eqb_eq in Heq. subst kb.
destruct (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool; [discriminate|].
destruct (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool eqn:Hd; [|discriminate].
split; [reflexivity|]. unfold estart. cbn [a_base a_off].
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.
#[using="Type"] Lemma rdn_inside_wbytes : ltac2:(TCodec.tc2 tcn__SymExec2Sound "RA':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'U8';'Q2&VFr8r6&W>r5%211%63541r9r4r3%711%;3431'D&VDr:%221;&W0%423@%2219%73D41&W4z%221>%D1E%82D1%F1B%6221%Q:1Q1%Q411&REr>&RAr<&S0r=r;%3221&Q?%12HO%83731%726Q7r7%=4<321(2&L&Q0&WC%11Q=%33QF1:%53QG81%72G1%Q73G91p0J1p0O1p0Q31p0Q<1p0QB1p`>QJ1pbFQL1pc>QN1p_:R51peJQO1paDR11pTNR31pR8R<1pdBR>1").
Proof.
intros segs E M ka w V ra n d Hfk Hfr Hst Hd Hdn.
pose proof (flat_u E ka _ Hfk) as Huk. pose proof (flat_u E ra _ Hfr) as Hur.
assert (Haddr : adenot E ra = adenot E ka + nat_to_word (Z.to_nat d)).
{ rewrite w_add_nat. apply bv_eq. rewrite Hur, u_small; [lia|].
destruct Hfk as (?&?&?&?). destruct Hfr as (?&?&?&?). rewrite Huk. lia. }
rewrite Haddr.
eapply rdn_slice.
- apply rdn_wbytes_hit. rewrite length_N_to_le_bytes. rewrite Huk.
destruct Hfk as (?&?&?&?). lia.
- rewrite length_N_to_le_bytes. lia.
Qed.
#[using="Type"] Lemma ext_hit_value : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QB'5'Q2';'Z?yR0%211&W4zr4%3221'J&H&WCr5%211%4217r3%7221u8%9261'D&Z>&VEr8r6&Q5&Ly8%I11&Q0r7%C11&Q?%12DI%53631%937;1%;11%?3>=1%A2Q21&SJ%14A9@Q0%E3Q431p0G1p0J1p0Q31p_:Q81peJQ<1pbFQ=1p`>Q?1pe>QA1").
Proof.
intros sx d n w V Hd Hdn Hn.
rewrite slice_word_bytes by lia. unfold ext_val, ext_Z, extz. reflexivity.
Qed.
Section Lookups.
Variable segs : list Segment.
#[using="Type"] Lemma log_lookup_sound : forall E base kn log rb rk n sx hints acc,
know_ok segs E base kn ->
log_flat E log -> (1 <= n)%nat -> (n <= 8)%nat ->
match log_lookup kn log rb rk n sx hints acc with
| LHit v scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n = Some bs
/\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
| LMiss scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n
= rdn segs base (adenot E (SA rb rk)) n
| LStuck => True
end.
Proof.
intros E base kn log. induction log as [|[[kb kk] w v] rest IH]; intros rb rk n sx hints acc Hkn Hlf Hn1 Hn8.
{ cbn. intros _ _. reflexivity. }
cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfk & Hlf').
cbn [log_lookup mem_denot].
destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel.
-
intros Hscs Hfr.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
exists (firstn n (skipn (Z.to_nat d) (word_to_le_bytes w (edenot E v)))).
split; [|split].
+ apply rdn_inside_wbytes; auto; lia.
+ apply length_firstn_skipn. rewrite length_N_to_le_bytes. lia.
+ rewrite mkExt_denot by exact Hn8. apply ext_hit_value; lia.
-
destruct (rel_lit_disjoint E _ _ _ _ _ _ Hrel) as [<- Hdis].
specialize (IH rb rk n sx hints acc Hkn Hlf' Hn1 Hn8).
destruct (log_lookup kn rest rb rk n sx hints acc) as [v' scs h|scs h|]; [ | | exact I];
intros Hscs Hfr;
(rewrite rdn_wbytes_out;
[ exact (IH Hscs Hfr)
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk), (flat_u E _ _ Hfr); exact Hdis
| rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk); destruct Hfk as (?&?&?&?); lia ]).
- exact I.
-
destruct (ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)) eqn:Hap.
{ pose proof (ranges_apart_sound segs E base kn _ _ _ _ _ _ Hkn Hap) as Hdis.
specialize (IH rb rk n sx hints acc Hkn Hlf' Hn1 Hn8).
destruct (log_lookup kn rest rb rk n sx hints acc) as [v' scs h|scs h|]; [ | | exact I];
intros Hscs Hfr;
(rewrite rdn_wbytes_out;
[ exact (IH Hscs Hfr)
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk), (flat_u E _ _ Hfr); exact Hdis
| rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk); destruct Hfk as (?&?&?&?); lia ]). }
assert (Hgen : forall hs,
match log_lookup kn rest rb rk n sx hs (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) with
| LHit v0 scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs (wbytes (mem_denot E base rest) (adenot E (SA kb kk)) (word_to_le_bytes w (edenot E v)))
(adenot E (SA rb rk)) n = Some bs
/\ length bs = n /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v0
| LMiss scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
rdn segs (wbytes (mem_denot E base rest) (adenot E (SA kb kk)) (word_to_le_bytes w (edenot E v)))
(adenot E (SA rb rk)) n = rdn segs base (adenot E (SA rb rk)) n
| LStuck => True
end).
{ intros hs.
specialize (IH rb rk n sx hs (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) Hkn Hlf' Hn1 Hn8).
pose proof (log_lookup_acc kn rest rb rk n sx hs (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)) as Hacc.
destruct (log_lookup kn rest rb rk n sx hs _) as [v' scs h|scs h|]; [ | | exact I];
intros Hscs Hfr; destruct Hacc as [pre ->];
(assert (Hd : sc_denot segs base E (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w)))
by (apply scs_denot_app in Hscs as [_ Hscs]; apply scs_denot_cons in Hscs as [Hd _]; exact Hd));
cbn [sc_denot] in Hd; destruct Hd as (Hf1 & Hf2 & Hdis);
rewrite (elenZ_elen E n) in Hf1, Hdis by lia; rewrite (elenZ_elen E w) in Hf2, Hdis by lia;
(rewrite rdn_wbytes_out;
[ exact (IH Hscs Hfr)
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk), (flat_u E _ _ Hfr); exact Hdis
| rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk); destruct Hfk as (?&?&?&?); lia ]). }
destruct hints as [|[|] hs0]; [apply Hgen | apply Hgen | exact I].
Qed.
End Lookups.
#[using="Type"] Lemma u_lit0 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "9'D'Q2&ZDyR0&Z>z%2231%5241%83713").
Proof. reflexivity. Qed.
#[using="Type"] Lemma estart_lit0 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "?'SB'Q2'D&VDr2(RN(RHz%211r1%5221%8271%:3;13pcJ<1pR8>1").
Proof. intros E rk. unfold estart. cbn [a_base a_off edenot]. rewrite u_lit0. lia. Qed.
#[using="Type"] Lemma adenot_shift : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q?'SB'U8'Q2&VFr6r5r3%43321r7%63143'D&VDr8%2219&W0%4237%221:%73?41&W4zr4%3221'Z?yR0%211&S0r:%221?&Z@r9%5241&Q6&WC%11L%311%73<51%J3<91p0@1p0E1p0N1p0Q11p`>Q71pc2Q81pc0Q91pc>Q;1paDQ<1pR8Q>1").
Proof.
intros E ka ra nk nr d Hfk Hfr Hst Hd.
rewrite w_add_nat. rewrite Z2Nat.id by exact Hd. apply bv_eq. rewrite (flat_u E _ _ Hfr).
rewrite (flat_u E _ _ Hfk).
destruct Hfk as (?&?&?&?). destruct Hfr as (?&?&?&?).
rewrite u_small by lia. exact Hst.
Qed.
#[using="Type"] Lemma elenZ_lit : ltac2:(TCodec.tc2 tcn__SymExec2Sound "B'SB'Q2'D&VCr2(RHr1%211%5241&W;&W@+2+R0%3221%5281%=3>71pb0?1pR8A1").
Proof. intros E l0. unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Section KLookup.
Variable segs : list Segment.
#[using="Type"] Lemma know_lookup_sound : forall E base kn rb rk n sx hints acc,
know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
match know_lookup segs kn rb rk n sx hints acc with
| LHit v scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs
/\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
| _ => True
end.
Proof.
intros E base kn. induction kn as [|K rest IH]; intros rb rk n sx hints acc Hkn Hn1 Hn8.
{ cbn. exact I. }
apply Forall_cons_iff in Hkn as [HK Hrest].
cbn [know_lookup].
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2].
5: { apply IH; assumption. }
5: { apply IH; assumption. }
5: { apply IH; assumption. }
5: { apply IH; assumption. }
-
cbn [kentry_ok] in HK. destruct HK as (Hkw8 & Hfk & Hrd).
destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel;
try (apply IH; assumption).
intros Hscs Hfr.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
exists (firstn n (skipn (Z.to_nat d) (word_to_le_bytes w (edenot E v)))).
split; [|split].
+ rewrite (adenot_shift E (SA rb kk) (SA rb rk) _ _ d Hfk Hfr Hst ltac:(lia)).
eapply rdn_slice; [exact Hrd | lia].
+ apply length_firstn_skipn. rewrite length_N_to_le_bytes. lia.
+ rewrite mkExt_denot by exact Hn8. apply ext_hit_value; lia.
-
cbn [kentry_ok] in HK. destruct HK as [Hfk Hz].
assert (Hin : flat E (SA rb rk) (Z.of_nat n) ->
(estart E (SA kb kk) <= estart E (SA rb rk))%Z ->
(estart E (SA rb rk) + Z.of_nat n <= estart E (SA kb kk) + elenZ E len)%Z ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (ELit 0)).
{ intros Hfr Hlo Hhi. exists (repeat (Z_to_bv 8 0) n). split; [|split].
- apply rdn_pointwise; [apply repeat_length | rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia |].
intros j Hj. rewrite (flat_u E _ _ Hfr). rewrite nth_repeat.
replace (estart E (SA rb rk) + Z.of_nat j)%Z
with (estart E (SA kb kk) + (estart E (SA rb rk) - estart E (SA kb kk) + Z.of_nat j))%Z by lia.
apply Hz. lia.
- apply repeat_length.
- cbn [edenot]. rewrite bytes_le_to_Z_repeat0, extz_0. reflexivity. }
destruct len as [l0| | | | | | |];
first
[ destruct (rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)) as [d| | |] eqn:Hrel;
[ intros Hscs Hfr; destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (Heqb & Hd & Hkk & Hrn & Hst);
apply Hin; [exact Hfr | lia | rewrite elenZ_lit; unfold estart in *; cbn [a_base a_off] in *; subst; lia]
| apply IH; assumption
| apply IH; assumption
| destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin; assumption
| apply IH; assumption ] ]
| destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin; assumption
| apply IH; assumption ] ].
-
cbn [kentry_ok] in HK. destruct HK as (Hfk & Hlen & Hb).
destruct (expr_eqb rb kb) eqn:Heqb; [|apply IH; assumption].
apply expr_eqb_eq in Heqb. subst kb.
destruct (Z.leb kk rk) eqn:Hkk; [|apply IH; assumption].
apply Z.leb_le in Hkk.
assert (Hst : estart E (SA rb rk) = (estart E (SA rb kk) + (rk - kk))%Z).
{ unfold estart. cbn [a_base a_off]. lia. }
assert (Hin : flat E (SA rb rk) (Z.of_nat n) ->
(rk - kk + Z.of_nat n <= elenZ E len)%Z ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (EBlob sx k (rk - kk) n)).
{ intros Hfr Hhi. exists (firstn n (skipn (Z.to_nat (rk - kk)) (eb E k))). split; [|split].
- apply rdn_pointwise.
+ apply length_firstn_skipn. lia.
+ rewrite (flat_u E _ _ Hfr). destruct Hfr as (?&?&?&?). lia.
+ intros j Hj. rewrite (flat_u E _ _ Hfr), Hst.
replace (estart E (SA rb kk) + (rk - kk) + Z.of_nat j)%Z
with (estart E (SA rb kk) + (rk - kk + Z.of_nat j))%Z by lia.
rewrite Hb by lia.
rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn. f_equal. f_equal. lia.
- apply length_firstn_skipn. lia.
- cbn [edenot]. unfold blob_val, blob_bytes, extz. reflexivity. }
destruct len as [l0| | | | | | |];
first
[ destruct (Z.leb (rk + Z.of_nat n) (kk + l0 mod 2 ^ 64)) eqn:Hle;
[ intros Hscs Hfr; apply Hin; [exact Hfr | apply Z.leb_le in Hle; rewrite elenZ_lit; lia]
| destruct (Z.leb (kk + l0 mod 2 ^ 64) rk); [apply IH; assumption | exact I] ]
| destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin;
[assumption | unfold estart in Hhi, Hlo |- *; cbn [a_base a_off] in Hhi, Hlo |- *; lia]
| apply IH; assumption ] ].
-
cbn [kentry_ok] in HK. destruct HK as (Hlo0 & Hhi64 & Hnone).
destruct rb as [z| | | | | | |]; try (apply IH; assumption).
destruct z; try (apply IH; assumption).
destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool eqn:Hr; [|apply IH; assumption].
apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
destruct (img_bytes segs rk n) as [zs|] eqn:Himg; [|exact I].
intros Hscs Hfr.
pose proof (flat_u E _ _ Hfr) as Hu. rewrite estart_lit0 in Hu.
destruct (rdn_img segs base n (adenot E (SA (ELit 0) rk)) zs) as (bs & Hbs & Hmap).
+ rewrite Hu. destruct Hfr as (?&?&?&?). rewrite estart_lit0 in *. lia.
+ intros j Hj. rewrite Hu. apply Hnone. lia.
+ rewrite Hu. exact Himg.
+ exists bs. split; [exact Hbs | split].
* exact (rdn_length _ _ _ _ _ Hbs).
* cbn [edenot]. unfold lit_of_bytes. rewrite <- Hmap, zbytes_map. unfold extz. reflexivity.
Qed.
End KLookup.
#[using="Type"] Lemma Z_to_bv64_u : ltac2:(TCodec.tc2 tcn__SymExec2Sound "='Q2'D'Z?yR0%211&Z>&ZDr1%3251%3261%5271%:3713pf8<1").
Proof. intros z. apply Z_to_bv_bv_unsigned. Qed.
#[using="Type"] Lemma Z_to_bv64_mod : ltac2:(TCodec.tc2 tcn__SymExec2Sound "A'Q2'D'Z?yR0%211&Z>&W;r1&W@+2+R0%3221%6251%82:1%92;7%>3;21pf8@1").
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia.
Qed.
#[using="Type"] Lemma to_saddr_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "F'SB'SG'Q2'D'Z?yR0%211&S0r3&UIr2r1%3221%6251&RF&S@%1286%3216%?3<51pa:A1p`@C1pR8E1").
Proof.
intros E e imm. unfold to_saddr.
assert (Hgen : forall b k, split_lit e = (b, k) ->
adenot E (SA b (k + imm)) = v_addi (edenot E e) imm).
{ intros b k Hs. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
destruct e as [z|v|op a1 a2|op a1 a2|op a1 a2|op a1 a2|sx lo n a1|sx kk i n]; cbn [split_lit] in Hs;
try (injection Hs as <- <-; f_equal; lia).
- injection Hs as <- <-. cbn [edenot]. rewrite u_lit0, Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Z.add_0_l, Zplus_mod_idemp_l. reflexivity.
- destruct op; try (injection Hs as <- <-; f_equal; lia).
destruct a2 as [z| | | | | | |]; try (injection Hs as <- <-; f_equal; lia).
injection Hs as <- <-. cbn [edenot]. rewrite alu_add, v_add_lit, Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Zplus_mod_idemp_l. f_equal. lia. }
destruct (split_lit e) as [b k]. apply Hgen. reflexivity.
Qed.
#[using="Type"] Lemma step_fence : ltac2:(TCodec.tc2 tcn__SymExec2Sound "RE':'Q7%211&R6y5'Z?yR0%211%5241'<y8%611%311p061yQ0%:11y4%<11%=1>'D%;15&Q9r;r9%3221(2r6%22<1%93841'5&Q:r7%211(7%?3521'>'R3'Q2%3221%N11&Q@r8%211(=(QIr5r4r3%45AF321+4%74>=21%J2=1%Q13=:1'Q;'Q<%211&Q=r>&RDvX<r=r<r:%55432Q91%8271(Q8&RF%126B%:5981Q>6%42?1%QC3?61p0C1p0Q61p0Q=1p`@QH1p`>QI1p`8QK1p_HQL1p_<QM1peJR01pd2R31pb@R41pc6R;1pcDR;1pdBRB1").
Proof.
intros segs regs pc mem rom w a b c d e Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.
#[using="Type"] Lemma step_fencei : ltac2:(TCodec.tc2 tcn__SymExec2Sound "RA':'Q7%211&R6y5'Z?yR0%211%5241'<y8%611%311p061yQ0%:11%;1<y<%=11'D%;15&Q9r9r7%3221(2r4%22<1%93841'5&Q:r5%211(7%?3521'>'R3'Q2%3221%N11&Q@r6%211(=(QJr3%23?D1+4%54<;21%H2;1%O3;81'Q;'Q<%211&Q=r<&RDvX<r;r:r8%55432Q71%8271(Q8&RF%126B%:5981Q<6%42?1%QA3?61p0C1p0Q41p0Q;1p`8QF1p_HQI1p_<QJ1peJQL1pd2QO1pb@R01pc6R71pcDR71pdBR>1").
Proof.
intros segs regs pc mem rom w a b c Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.
#[using="Type"] Lemma testbit_mask : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q2'Q2&W4zr2%3221&W8r3+R0%3221%8273'D'5&WB&WA&W@+2%2219r5%4231%6231r4%9221&3&W5%1274&W9%126C%5231%B3A71p0D1p0F1p0K1pa6Q01pa<Q11").
Proof.
intros j i Hj Hj64 Hi.
assert (Heq : (2 ^ 64 - 2 ^ j)%Z = Z.shiftl (Z.ones (64 - j)) j).
{ rewrite Z.shiftl_mul_pow2 by lia. unfold Z.ones. rewrite Z.shiftl_1_l.
rewrite <- Z.sub_1_r, Z.mul_sub_distr_r, <- Z.pow_add_r by lia.
replace (64 - j + j)%Z with 64%Z by lia. lia. }
rewrite Heq.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite Z.shiftl_spec_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
- rewrite Z.shiftl_spec_high by lia. rewrite Z.testbit_ones by lia.
destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
+ replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
replace (i <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia).
apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
+ replace (i <? 64)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
apply andb_false_intro2. apply Z.ltb_ge. lia.
Qed.
#[using="Type"] Lemma land_align_mask : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q4'Q2&W4zr1%3221&W8r2+R0%3221'Cr4%:291&W@+2%2217%:251%7251'D&W;r5%827:%3221%53F1D&W3r6&WA%>2=7%22=1%5241%<3M15p081p0?1p0H1p0M1pa<Q21pf2Q31").
Proof.
intros x j Hj Hj64 Hx Hmod.
assert (Hx' : x = ((x / 2 ^ j) * 2 ^ j)%Z).
{ pose proof (Z.div_mod x (2 ^ j) ltac:(apply Z.pow_nonzero; lia)) as Hdm. lia. }
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask by lia.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- replace (j <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia).
rewrite andb_false_r. rewrite Hx'. symmetry. apply Z.mul_pow2_bits_low. lia.
- replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
+ replace (i <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). apply andb_true_r.
+ replace (i <? 64)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
symmetry. apply (Z_testbit_high 64 x i); lia.
Qed.
Section ZBits.
Local Open Scope Z_scope.
#[using="Type"] Lemma testbit_drop_low : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q5'Q2&W4zr2%3221'Cr4%6251&W8&W@+2r3%3221%5271%9271%>294'D'5&WB&W0&W<r7r5%>2=1%4231r6%7221%921E%:24F%=3<21p0?1p0A1p0L1pa6Q11pa<Q21pc:Q31pc8Q41").
Proof.
intros q r j i Hj Hr Hi.
replace i with ((i - j) + j) by lia.
rewrite <- !Z.div_pow2_bits by lia.
f_equal. rewrite Z.div_add_l by lia. rewrite (Z.div_small r) by lia.
rewrite Z_div_mult by lia. lia.
Qed.
#[using="Type"] Lemma land_highmask : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q0'Q2'C&W4zr1%3221&W8+R0%2241%8241r3%9281&W@+2%2217%9251%?251'D&W3r4&WA%928;%2281%5241&W;%1264%6271%:3K41p0<1p0D1pa<N1pf2O1").
Proof.
intros x j Hj Hx.
assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hmb.
set (q := x / 2 ^ j) in *. set (r := x mod 2 ^ j) in *.
replace (x - r) with (q * 2 ^ j) by lia. rewrite Hdm.
replace (2 ^ j * q + r) with (q * 2 ^ j + r) by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
pose proof (testbit_mask j i ltac:(lia) ltac:(lia) ltac:(lia)) as Hmask.
rewrite Hmask. destruct (Z.lt_ge_cases i j) as [Hij|Hij].
- replace (j <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r.
symmetry. apply Z.mul_pow2_bits_low. lia.
- replace (j <=? i) with true by (symmetry; apply Z.leb_le; lia).
destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
+ replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r.
apply testbit_drop_low; lia.
+ replace (i <? 64) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
assert (0 <= q) by (subst q; apply Z.div_pos; lia).
assert (0 <= q * 2 ^ j < 2 ^ 64) by nia.
destruct (Z.testbit (q * 2 ^ j) i) eqn:Ht; [|reflexivity]. exfalso.
assert (Hb : forall n a, 0 <= n -> 0 <= a < 2 ^ n -> forall k, n <= k -> Z.testbit a k = false).
{ intros n a Hn Ha k Hk. destruct (Z.testbit a k) eqn:E; [|reflexivity]. exfalso.
apply Z.testbit_true in E; [|lia].
assert (Hpk : 2 ^ n <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
assert (Hsmall : a / 2 ^ k = 0) by (apply Z.div_small; lia). rewrite Hsmall in E. cbn in E. lia. }
rewrite (Hb 64 (q * 2 ^ j)) in Ht by lia. discriminate.
Qed.
End ZBits.
#[using="Type"] Lemma and_highmask_val : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q5'Z?yR0%211'Q2&W4zr1%3221&W8r2+R0%3221'D&R:(QBr4&Z>&W?&W@+2r3%3221%511%72F1%;3:91&WA&ZD%12J<&W;%1228%5231%?2N1%D3N81p0F1p0K1pa<Q01peHQ21").
Proof.
intros v j Hj Hj64. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j < 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
assert (Hm : ((- 2 ^ j) mod 2 ^ 64 = 2 ^ 64 - 2 ^ j)%Z).
{ rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
rewrite Hm. f_equal. apply land_highmask; lia.
Qed.
#[using="Type"] Lemma and_mask_id : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q6'Z?yR0%211'Q2&W4zr1%3221&W8r2+R0%3221'D&W;&ZDr4%22?1&W@+2r3%3221%8251%:3C1A&R:(QBr5&Z>&W?%;2:=%211%42M1%83761%D3N17p0;1p0G1p0L1pa<Q11peHQ31").
Proof.
intros v j Hj Hj64 Hmod. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
pose proof (u64_range v) as Hv.
assert (Hm : ((- 2 ^ j) mod 2 ^ 64 = 2 ^ 64 - 2 ^ j)%Z).
{ assert (0 < 2 ^ j <= 2 ^ 64)%Z.
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
rewrite Hm, land_align_mask by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma find_align_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QC':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&VHr6r5r4r3%544321'D%@18&SK%1265(2r2%22=1%73641'C&W8z%221=&W;&ZD&S@r7%221C%42Q21%621D%C3J19%<291p0>1p0G1pb>N1p_<Q01paJQ21p_NQ51pR8Q>1pdBQ@1").
Proof.
intros segs E base kn a m Hkn. induction kn as [|K rest IH]; cbn [find_align]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | |e' m'| | |]; try (apply IH; assumption).
destruct (expr_eqb a e') eqn:Heq.
- injection H as <-. apply expr_eqb_eq in Heq. subst e'. exact HK.
- apply IH; assumption.
Qed.
#[using="Type"] Lemma ctz_fuel_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "F';'Q2'C&W4z&S=r2r1%3221%6251&W2&W@+2%2215%4217&W>%11:%>291%@241%A2:1pf8C1p`DE1").
Proof.
induction f as [|f IH]; intros z; cbn [ctz_fuel].
- split; [lia|]. split; [exists z; lia | lia].
- destruct (z mod 2 =? 0)%Z eqn:E.
+ destruct (IH (z / 2)%Z) as (A & [q Hq] & C). split; [lia|]. split; [|lia].
exists q. rewrite Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z.
apply Z.eqb_eq in E. pose proof (Z.div_mod z 2 ltac:(lia)). lia.
+ split; [lia|]. split; [exists z; rewrite Z.pow_0_r; lia | lia].
Qed.
#[using="Type"] Lemma ctz64_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "B'Q2'C&W4z&S<r1%211%5241+R0%7231%9231&W2&W@+2%2218%421:%?261pf8A1").
Proof. intros z. unfold ctz64. destruct (ctz_fuel_sound 64 z) as (A & B & C). cbn [Z.of_nat] in C. split; [lia | exact B]. Qed.
#[using="Type"] Lemma pow2_divide_le : ltac2:(TCodec.tc2 tcn__SymExec2Sound "C'Q2'C&W4zr2%3221r1%5231%7231&W2&W@+2r3%3221%423:%6221p081p_HA1p_<B1").
Proof. intros a b H. exists (2 ^ (b - a))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
#[using="Type"] Lemma divide_mod64 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "I'Q2'C&W4zr2%3221+R0%5231%7231&W2&W@+2r3%3221%521:r4%6251&W;%827<%2271%;241p071p0>1peBG1pa>H1").
Proof.
intros k t Hk Hd. rewrite Z.mod_eq by lia.
apply Z.divide_sub_r; [exact Hd|]. apply Z.divide_mul_l. apply pow2_divide_le. lia.
Qed.
#[using="Type"] Lemma ealign_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q>':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG&VHr5r4r3r2%544321'C&W4z&S?%1276%4231+R0%6231%8231&W2&W@+2%2218&ZD&S@%12DA%32Q01%8251%B2:1p0D1p`@K1paJM1pTNQ01pR8Q91pdBQ;1").
Proof.
intros segs E M kn e Hkn. induction e; cbn [ealign];
lazymatch goal with
| |- context [find_align kn ?e0] =>
destruct (find_align kn e0) as [m|] eqn:Hfa;
[ destruct (find_align_sound segs E M kn e0 m Hkn Hfa) as [Hm0 Hmod];
destruct (0 <? m)%Z eqn:Hp; [|split; [lia | apply Z.divide_1_l]];
destruct (ctz64_sound m) as [A B]; split; [exact A|];
eapply Z.divide_trans; [exact B|]; apply Z.mod_divide; [lia | exact Hmod]
| clear Hfa ]
end; cbn [edenot].
- destruct (ctz64_sound (z mod two64)) as [A B]. split; [exact A|]. rewrite u_lit64. exact B.
- split; [lia | apply Z.divide_1_l].
- destruct IHe1 as [A1 B1], IHe2 as [A2 B2].
pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
destruct op; try (split; [lia | apply Z.divide_1_l]).
+ split; [lia|]. rewrite u_add64. apply divide_mod64; [lia|].
apply Z.divide_add_r; (eapply Z.divide_trans; [apply pow2_divide_le|]; [|eassumption]; lia).
+ split; [lia|]. rewrite u_sub64. apply divide_mod64; [lia|].
apply Z.divide_sub_r; (eapply Z.divide_trans; [apply pow2_divide_le|]; [|eassumption]; lia).
+ destruct (lit_shamt e2) as [s|] eqn:Hs; [|split; [lia | apply Z.divide_1_l]].
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr]. split; [lia|].
rewrite u_sll64, Hsv. apply divide_mod64; [lia|].
eapply Z.divide_trans; [apply (pow2_divide_le _ (ealign kn e1 + s)); lia|].
rewrite Z.pow_add_r by lia. apply Z.mul_divide_mono_r. exact B1.
+ split; [lia|]. rewrite u_or64.
set (k := Z.min (ealign kn e1) (ealign kn e2)).
assert (D1 : (2 ^ k | bv_unsigned (edenot E e1))%Z) by (eapply Z.divide_trans; [apply pow2_divide_le|exact B1]; lia).
assert (D2 : (2 ^ k | bv_unsigned (edenot E e2))%Z) by (eapply Z.divide_trans; [apply pow2_divide_le|exact B2]; lia).
destruct D1 as [q1 Hq1], D2 as [q2 Hq2]. exists (Z.lor q1 q2).
rewrite Hq1, Hq2. rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lor. reflexivity.
+ split; [lia|]. rewrite u_and64.
set (k := Z.max (ealign kn e1) (ealign kn e2)).
assert (Hk : (0 <= k)%Z) by lia.
assert (Hlow : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (2 ^ k | x)%Z -> (2 ^ k | Z.land x y)%Z).
{ intros x y Hx Hy [q Hq]. exists (Z.land q (Z.shiftr y k)).
rewrite Hq. rewrite <- !Z.shiftl_mul_pow2 by lia.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec.
destruct (Z.lt_ge_cases i k) as [Hik|Hik].
- rewrite !Z.shiftl_spec_low by lia. reflexivity.
- rewrite !Z.shiftl_spec_high by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
f_equal. f_equal. lia. }
destruct (Z.le_ge_cases (ealign kn e2) (ealign kn e1)) as [Hc|Hc].
* replace k with (ealign kn e1) in * by lia. apply Hlow; [lia | lia | exact B1].
* replace k with (ealign kn e2) in * by lia. rewrite Z.land_comm. apply Hlow; [lia | lia | exact B2].
- split; [lia | apply Z.divide_1_l].
- destruct IHe1 as [A1 B1], IHe2 as [A2 B2].
destruct op; try (split; [lia | apply Z.divide_1_l]).
split; [lia|]. rewrite u_mul64. apply divide_mod64; [lia|].
eapply Z.divide_trans; [apply (pow2_divide_le _ (ealign kn e1 + ealign kn e2)); lia|].
rewrite Z.pow_add_r by lia. destruct B1 as [p1 Hp1], B2 as [p2 Hp2]. exists (p1 * p2)%Z. rewrite Hp1, Hp2. ring.
- split; [lia | apply Z.divide_1_l].
- split; [lia | apply Z.divide_1_l].
- split; [lia | apply Z.divide_1_l].
Qed.
#[using="Type"] Lemma and_lowmask_zero : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q6'Z?yR0%211'Q2&W4zr1%3221r2+R0%6221&W2&W@+2r3%3221&ZDr4%22A1%8241'D&R:(QBr5&Z>&WA%>2=9+1%3221%52L1%93871%72NJ%<3N21p0>1p0H1p0L1pa<Q11peHQ31").
Proof.
intros v j Hj Hj64 Hd. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j <= 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
rewrite (Z.mod_small (2 ^ j - 1)) by lia.
replace (2 ^ j - 1)%Z with (Z.ones j) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
rewrite Z.land_ones by lia. rewrite (Znumtheory.Zdivide_mod _ _ Hd). reflexivity.
Qed.
#[using="Type"] Lemma mkAnd_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q8':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG&VHr6r5r4r3%544321'D&S@&TEr2%23761%42:1&R:(QB%72=:%82>6%43321%;3J61p0=1p_HD1p_<E1paJG1p_NJ1pR8Q31pdBQ51").
Proof.
intros segs E base kn a b Hkn. unfold mkAnd.
destruct b as [k| | | | | | |]; try apply mkAlu_denot.
destruct (ealign_sound segs E base kn a Hkn) as [Hal Hdiv].
set (k' := (k mod two64)%Z). set (j := Z.log2 (two64 - k')).
assert (Hk' : (0 <= k' < 2 ^ 64)%Z) by (subst k'; unfold two64; apply Z.mod_pos_bound; lia).
assert (Hbk : Z_to_bv 64 k = Z_to_bv 64 k').
{ apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. subst k'. unfold two64. rewrite Z.mod_mod by lia. reflexivity. }
pose proof (u64_range (edenot E a)) as Hua.
destruct (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool eqn:Hc.
- apply andb_prop in Hc as [Hpow Hj64]. apply Z.eqb_eq in Hpow. apply Z.ltb_lt in Hj64.
assert (Hj0 : (0 <= j)%Z) by (subst j; apply Z.log2_nonneg).
cbn [edenot]. rewrite Hbk. replace k' with (2 ^ 64 - 2 ^ j)%Z by (unfold two64 in Hpow; lia).
assert (Hneg : Z_to_bv 64 (2 ^ 64 - 2 ^ j) = Z_to_bv 64 (- 2 ^ j)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- (Z.mod_add (- 2 ^ j) 1) by lia. f_equal. lia. }
rewrite Hneg.
destruct (Z.leb j (ealign kn a)) eqn:Hle.
+ apply Z.leb_le in Hle. symmetry. apply and_mask_id; [lia | lia |].
apply Znumtheory.Zdivide_mod. eapply Z.divide_trans; [apply pow2_divide_le | exact Hdiv]. lia.
+ destruct (lin_of a) as [c ts] eqn:Hl. cbn [fst snd].
destruct (coeffs_div (2 ^ j) ts) eqn:Hcd; [| rewrite <- Hneg; replace (2 ^ 64 - 2 ^ j)%Z with k' by (unfold two64 in Hpow; lia); rewrite <- Hbk; apply mkAlu_denot].
rewrite and_highmask_val by lia.
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (lin_of_sound E a) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs. unfold uE in Hs.
assert (Hmod : (bv_unsigned (edenot E a) mod 2 ^ j = c mod 2 ^ j)%Z).
{ rewrite <- (eqm_mod_pow2 _ _ j ltac:(lia) Hs). rewrite Z.add_mod, (coeffs_div_sound E _ ts Hp Hcd), Z.add_0_r, Z.mod_mod by lia. reflexivity. }
rewrite Hmod. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd].
destruct Hs as [q Hq]. exists q. lia.
- set (j2 := Z.log2 (k' + 1)).
destruct (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool eqn:Hc2; [|apply mkAlu_denot].
apply andb_prop in Hc2 as [Hpow Hj64]. apply Z.eqb_eq in Hpow. apply Z.ltb_lt in Hj64.
assert (Hj0 : (0 <= j2)%Z) by (subst j2; apply Z.log2_nonneg).
cbn [edenot]. rewrite Hbk. replace k' with (2 ^ j2 - 1)%Z by lia.
destruct (Z.leb j2 (ealign kn a)) eqn:Hle.
+ apply Z.leb_le in Hle. symmetry. apply and_lowmask_zero; [lia | lia |].
eapply Z.divide_trans; [apply pow2_divide_le | exact Hdiv]. lia.
+ destruct (lin_lowbits a j2) as [v|] eqn:Hlb;
[| replace (2 ^ j2 - 1)%Z with k' by lia; rewrite <- Hbk; apply mkAlu_denot].
destruct (lin_lowbits_sound E a j2 v ltac:(lia) Hlb) as [Hv Hvr].
rewrite and_lowmask_val by lia. cbn [edenot]. rewrite Hv. reflexivity.
Qed.
#[using="Type"] Lemma itv_ltu_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q6'Q2'5'C&W4r7r3%3221r6%5231%7231%7235r5%9271%;231'D'<%11?&T1r9r8%3421@=(2%12EA%93731&W9%12B>r4%=3J21p051p0@1p0E1peBN1pf4Q01pf2Q11p`0Q21p`4Q31p_@Q41p_BQ51").
Proof.
intros al ah bl bh x y t Hx Hy H. unfold itv_ltu in H.
destruct (ah <? bl)%Z eqn:C1; [injection H as <-; apply Z.ltb_lt; lia|].
destruct (bh <=? al)%Z eqn:C2; [injection H as <-; apply Z.ltb_ge; lia| discriminate].
Qed.
#[using="Type"] Lemma itv_lts_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q>'Q2'Z?yR0%211'5'C&W4r7&ZDr3%2281%5241r6%7231%9231%9235r5%;271%=231'D'<%11A&T0r9r8%3421B=(2%12GB%93731&W9&ZB%12MC%22N@%4221r4%@3O21p081p0C1p0H1peBQ31pf4Q51pf2Q61p`0Q:1p`4Q;1p_@Q<1p_BQ=1").
Proof.
intros al ah bl bh x y t Hx Hy H. unfold itv_lts in H.
pose proof (u64_range x) as Rx. pose proof (u64_range y) as Ry.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
- apply orb_prop in C1 as [C1|C1]; apply andb_prop in C1 as [Ca Cb].
+ rewrite (bv_signed_small x) by lia. rewrite (bv_signed_small y) by lia.
eapply itv_ltu_sound; [exact Hx | exact Hy | exact H].
+ rewrite (bv_signed_hi x) by lia. rewrite (bv_signed_hi y) by lia.
pose proof (itv_ltu_sound al ah bl bh (bv_unsigned x) (bv_unsigned y) t Hx Hy H) as Hl.
destruct t; [apply Z.ltb_lt in Hl; apply Z.ltb_lt | apply Z.ltb_ge in Hl; apply Z.ltb_ge]; lia.
- match type of H with (if ?c then _ else _) = _ => destruct c eqn:C2 end.
+ injection H as <-. apply andb_prop in C2 as [Ca Cb].
rewrite (bv_signed_hi x) by lia. rewrite (bv_signed_small y) by lia. apply Z.ltb_lt. lia.
+ match type of H with (if ?c then _ else _) = _ => destruct c eqn:C3 end; [|discriminate].
injection H as <-. apply andb_prop in C3 as [Ca Cb].
rewrite (bv_signed_small x) by lia. rewrite (bv_signed_hi y) by lia. apply Z.ltb_ge. lia.
Qed.
#[using="Type"] Lemma range_branch_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q?'R2'Q2'Z?yR0%211'5'C&W4r7&ZDr3%2281%5241r6%7231%9231%9235r5%;271%=231'D'<%11A&TOr:r9r8%45321C>(2%12HC%:3831&R;r;%231D@r4%?3N21p061p0B1p0G1peBQ21pf4Q41pf2Q51p`0Q91p`4Q:1p_@Q;1p_BQ<1p`8Q>1").
Proof.
intros c al ah bl bh x y t Hx Hy H. destruct c; cbn [range_branch branch_taken] in *;
unfold bv_eqb, bv_ltu, bv_lts.
- match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
+ injection H as <-. apply Z.eqb_neq. apply orb_prop in C1 as [C1|C1]; apply Z.ltb_lt in C1; lia.
+ match type of H with (if ?c then _ else _) = _ => destruct c eqn:C2 end; [|discriminate].
injection H as <-. apply Z.eqb_eq. apply andb_prop in C2 as [C2 C4]. apply andb_prop in C2 as [C2 C3]. lia.
- match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
+ injection H as <-. apply Bool.negb_true_iff. apply Z.eqb_neq. apply orb_prop in C1 as [C1|C1]; apply Z.ltb_lt in C1; lia.
+ match type of H with (if ?c then _ else _) = _ => destruct c eqn:C2 end; [|discriminate].
injection H as <-. apply Bool.negb_false_iff. apply Z.eqb_eq. apply andb_prop in C2 as [C2 C4]. apply andb_prop in C2 as [C2 C3]. lia.
- eapply itv_lts_sound; eassumption.
- destruct (itv_lts al ah bl bh) as [t'|] eqn:Hi; [|discriminate]. cbn [option_map] in H. injection H as <-.
f_equal. eapply itv_lts_sound; eassumption.
- eapply itv_ltu_sound; eassumption.
- destruct (itv_ltu al ah bl bh) as [t'|] eqn:Hi; [|discriminate]. cbn [option_map] in H. injection H as <-.
f_equal. eapply itv_ltu_sound; eassumption.
Qed.
#[using="Type"] Lemma cond_on_eq_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "?'R2'Z?yR0%211'D'5&R;r2r1%33211&S;%114%83731peH:1p`8>1").
Proof.
intros c v. destruct c; cbn [branch_taken cond_on_eq]; unfold bv_eqb, bv_lts, bv_ltu;
rewrite ?Z.eqb_refl, ?Z.ltb_irrefl; reflexivity.
Qed.
#[using="Type"] Lemma decide_branch_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QB':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'R2'SG'5&VHr8r7r6r5%544321'D%A18&S>r4r3%348721(2r2%22?1%93841&R;&S@r9%221?%322;%53B21%@3G1<p081p0C1peBJ1p_HL1p_<M1p`8O1paJQ11pTNQ41pR8Q=1pdBQ?1").
Proof.
intros segs E M kn c a b t Hkn H.
assert (Hrest : (if expr_eqb a b then Some (cond_on_eq c)
else match erange kn a, erange kn b with
| Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
| _, _ => None
end) = Some t ->
branch_taken c (edenot E a) (edenot E b) = t).
{ clear H. intros H. destruct (expr_eqb a b) eqn:Heq.
- apply expr_eqb_eq in Heq. subst b. injection H as <-. apply cond_on_eq_sound.
- destruct (erange kn a) as [[al ah]|] eqn:Ha; [|discriminate].
destruct (erange kn b) as [[bl bh]|] eqn:Hb; [|discriminate].
eapply range_branch_sound; [eapply erange_sound; [exact Hkn | exact Ha] | eapply erange_sound; [exact Hkn | exact Hb] | exact H]. }
unfold decide_branch in H.
destruct a; try exact (Hrest H). destruct b; try exact (Hrest H).
injection H as <-. reflexivity.
Qed.
#[using="Type"] Lemma lin_nowrap_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QF':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG&VHr5r4r3r2%544321'D'5&T8%1265(@%53421'Q2&ZD&S@r6%221=%42K1&W0&8'>%129F%Q511&T9%11E%63=31&VM&?%13@64%32>1%<251%I3C>1p0E1p0L1p`@Q31paJQ51pTNQ81pR8QA1pdBQC1").
Proof.
intros segs E M kn e Hkn H. unfold lin_nowrap in H.
destruct (lin_range (erange kn) (fst (lin_of e)) (snd (lin_of e))) as [[lo hi]|] eqn:Hlr; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
pose proof (u64_range (edenot E e)). nia.
Qed.
#[using="Type"] Lemma ldiv_terms_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q1'SB'Q2':'>'SG%2241%411&W8zr2%3221'D'5&S7r3%2216(@%63521&VMr5%2216&W<r4&T5%122:%7261%5241%@3J71p0;1p0C1peDH1pb>N1pR8Q01").
Proof.
intros E m ts Hm. induction ts as [|[k a] rest IH]; cbn [coeffs_div ldiv_terms tden]; intros H.
- lia.
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH H2).
pose proof (Z.div_mod k m ltac:(lia)). nia.
Qed.
#[using="Type"] Lemma mkSrl_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QB':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&VHr7r6r5r4%544321'D&W;&ZDr2%22E1+R0%5221r3%83?21&S@r8&TJ%13@?>%4231&R:(QF%726C%3321:%B3Q251p0;1p0E1pf4Q51pdDM1p_<O1paJQ11pTNQ41pR8Q=1pdBQ?1").
Proof.
intros segs E M kn a sh y Hkn Hy. unfold mkSrl.
pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as Hsr. rewrite Hy in Hsr.
assert (Hlit : edenot E (mkAlu ALU_SRL a (ELit sh)) = alu64 ALU_SRL (edenot E a) y).
{ rewrite mkAlu_denot. cbn [edenot]. apply alu_srl_amt. rewrite (u_lit_mod sh 64) by lia. symmetry; exact Hy. }
match goal with |- edenot E (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|exact Hlit].
apply andb_prop in Hc as [Hc Hnw]. apply andb_prop in Hc as [Hc Hc3]. apply andb_prop in Hc as [Hc Hc2].
apply andb_prop in Hc as [Htriv Hdiv]. apply Z.leb_le in Hc2. apply Z.ltb_lt in Hc3.
assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (lin_nowrap_sound segs E M kn a Hkn Hnw) as Hval.
destruct (lin_of a) as [c ts] eqn:Hl. cbn [fst snd] in *.
rewrite (ldiv_terms_sound E (2 ^ sh) ts Hp Hdiv) in Hval.
rewrite alu_srl. unfold v_srl. rewrite Hy, Z.shiftr_div_pow2, Hval by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd].
exists 0%Z.
replace (c + 2 ^ sh * tden E (ldiv_terms (2 ^ sh) ts))%Z
with (tden E (ldiv_terms (2 ^ sh) ts) * 2 ^ sh + c)%Z by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small c) by lia. lia.
Qed.
#[using="Type"] Lemma land_aligned_small : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q1'Q2&W4zr1%3221r4%5241&W2&W@+2r3%3221r5%6221'C%>2=3&W8%928<%2261%5241'D&W3r7r6%3221%53I1Gp071p0>1p0F1p0I1pa>N1p_HO1pf2Q01").
Proof.
intros x b k Hk Hx [q Hq] Hb. subst x.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hik|Hik].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z_testbit_high k b i) by lia. apply andb_false_r.
Qed.
#[using="Type"] Lemma or_disjoint_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QA':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG&VHr6r5r4r3%544321'D'5&TMr2%23761(@%63521'Q2&W7&ZD&S@r7%221?%42M1%423@%62O1%8231&W0%1253%C3<31p0>1p0F1p_HM1p_<N1paJQ01pTNQ31pR8Q<1pdBQ>1").
Proof.
intros segs E M kn a b Hkn H. unfold or_disjoint in H.
destruct (erange kn b) as [[lo hi]|] eqn:Hr; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (erange_sound segs E M kn b lo hi Hkn Hr) as Hb.
destruct (ealign_sound segs E M kn a Hkn) as [Hk Hdiv].
pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)).
pose proof (Z.add_lor_land (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))) as Hal.
rewrite (land_aligned_small _ _ (ealign kn a)) in Hal by (try lia; exact Hdiv). lia.
Qed.
#[using="Type"] Lemma mkOr_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q8':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG&VHr6r5r4r3%544321'D&S@&TIr2%23761%42:1&R:(QC%72=:%82>6%43321%;3J61p0=1p_HD1p_<E1paJG1pTNJ1pR8Q31pdBQ51").
Proof.
intros segs E M kn a b Hkn. unfold mkOr.
destruct (is_lit a) as [x|] eqn:Ha; [destruct (is_lit b) as [y|] eqn:Hb|].
- apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. unfold zalu. apply Z_to_bv_bv_unsigned.
- destruct (or_disjoint kn a b) eqn:H1; [|destruct (or_disjoint kn b a) eqn:H2; [|reflexivity]];
rewrite mkAlu_denot, alu_add, alu_or; unfold v_add, v_or; f_equal; symmetry.
+ eapply or_disjoint_sound; eassumption.
+ rewrite Z.lor_comm, Z.add_comm. eapply or_disjoint_sound; eassumption.
- destruct (or_disjoint kn a b) eqn:H1; [|destruct (or_disjoint kn b a) eqn:H2; [|reflexivity]];
rewrite mkAlu_denot, alu_add, alu_or; unfold v_add, v_or; f_equal; symmetry.
+ eapply or_disjoint_sound; eassumption.
+ rewrite Z.lor_comm, Z.add_comm. eapply or_disjoint_sound; eassumption.
Qed.
#[using="Type"] Lemma mkAluK_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q:':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'R1'SG&VHr7r6r5r4%544321'D&S@&TCr3r2%348721%52;1&R:%72=5%82>5%33<21%;3K51p0=1p_HD1p_<E1pc4G1paJI1p_NL1pR8Q51pdBQ71").
Proof.
intros segs E base kn op a b Hkn. unfold mkAluK. destruct op; try apply mkAlu_denot.
- destruct (is_lit a); [apply mkAlu_denot|].
destruct (shamt_of b 6) as [sh|] eqn:Hs; [|apply mkAlu_denot].
destruct (shamt_of_sound E b 6 sh ltac:(lia) Hs) as [Hm Hr]. change (2 ^ 6)%Z with 64%Z in Hm.
eapply mkSrl_denot; [exact Hkn | exact Hm].
- eapply mkOr_denot. exact Hkn.
-
assert (Hcomm : alu64 ALU_AND (edenot E b) (edenot E a) = alu64 ALU_AND (edenot E a) (edenot E b)).
{ rewrite !alu_and. unfold v_and. rewrite Z.land_comm. reflexivity. }
destruct a; destruct b; try (eapply mkAnd_denot; exact Hkn);
rewrite <- Hcomm; eapply mkAnd_denot; exact Hkn.
Qed.
#[using="Type"] Lemma flat_sc_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QJ':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'U8';'U?%A11&VHr7r6r5r4%544321'Ju1r3%3221u8%5271&VLr:r8r9&4&SM%13A@?%33E1?%847651'C&VF&W>%11F%33<H1r;%?41<>H%7231p091p0C1p0F1p0K1pcFQ21pbFQ51p_<Q71paJQ91p_NQ<1pR8QE1pdBQG1").
Proof.
intros segs E base kn a n rest Hkn Hn1 Hn8 H. unfold flat_sc in H.
destruct (base_range kn (a_base a)) as [[lo hi]|] eqn:Hb.
- destruct (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool eqn:Hc.
+ split; [|exact H]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (base_range_sound segs E base kn _ _ _ Hkn Hb) as [A B].
unfold flat, estart. lia.
+ apply scs_denot_cons in H as [Hf Hr]. cbn [sc_denot] in Hf. rewrite elenZ_elen in Hf by exact Hn8. auto.
- apply scs_denot_cons in H as [Hf Hr]. cbn [sc_denot] in Hf. rewrite elenZ_elen in Hf by exact Hn8. auto.
Qed.
#[using="Type"] Lemma eval_closed_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "K'SB'SG'Q2'D'<%113&SFr2%211(2r1%2291%93741'Z?yR0%211&S@r4r3%3221&Z>%127>%C3731p0;1peHF1p`@H1pR8J1").
Proof.
intros E e. induction e; intros v H; cbn [eval_closed] in H; cbn [edenot]; try discriminate.
- injection H as <-. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64. rewrite Z.mod_mod by lia. reflexivity.
- destruct (eval_closed e1) as [x|] eqn:H1; [|discriminate]. destruct (eval_closed e2) as [y|] eqn:H2; [|discriminate].
injection H as <-. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl). unfold zalu. symmetry. apply Z_to_bv_bv_unsigned.
- destruct (eval_closed e1) as [x|] eqn:H1; [|discriminate]. destruct (eval_closed e2) as [y|] eqn:H2; [|discriminate].
injection H as <-. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl). unfold zaluw. symmetry. apply Z_to_bv_bv_unsigned.
- destruct (eval_closed e1) as [x|] eqn:H1; [|discriminate]. destruct (eval_closed e2) as [y|] eqn:H2; [|discriminate].
injection H as <-. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl). unfold zmd. symmetry. apply Z_to_bv_bv_unsigned.
- destruct (eval_closed e1) as [x|] eqn:H1; [|discriminate]. destruct (eval_closed e2) as [y|] eqn:H2; [|discriminate].
injection H as <-. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl). unfold zmdw. symmetry. apply Z_to_bv_bv_unsigned.
- destruct (eval_closed e) as [x|] eqn:H1; [|discriminate].
injection H as <-. rewrite (IHe x eq_refl). unfold zext_lit. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
#[using="Type"] Lemma esubst_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "H'SB'SG'D'Z?yR0%211&S@r4r2%3221r3%5241%:3731r5&SE%13857%:231%;249%@3=21p071p`@C1pc:D1pd:E1pR8G1").
Proof.
intros E s r e Hr. induction e; cbn [esubst];
(destruct (expr_eqb _ s) eqn:Heq;
[ apply expr_eqb_eq in Heq; rewrite Hr, <- Heq; reflexivity
| cbn [edenot]; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity ]).
Qed.
#[using="Type"] Lemma all_eval_to_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q>'SG'Q2';'D'5&S1r5r4r3r2r1%6554321(@%:3921'C&W4%1296&W8&W0&W>%11<%32>1%52<1%9271'<%11H&SF&SEr8(RH%11Er7%53421%711(2r6%22Q31%Q23<41p0?1pf8Q61p0K1p`<Q71pb8Q91peHQ:1p`@Q<1pd:Q=1").
Proof.
intros s e v lo cnt. revert lo. induction cnt as [|c IH]; intros lo H z Hz; [lia|].
cbn [all_eval_to] in H. destruct (eval_closed (esubst s (ELit lo) e)) as [w|] eqn:Hw; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst w.
destruct (Z.eq_dec z lo) as [->|Hne]; [exact Hw|].
apply (IH (lo + 1)%Z H2). lia.
Qed.
#[using="Type"] Lemma conc_try_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q?':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG%?11'Q2&VHr7r6r5r4%544321'D%A18&S9r3%23761(2r2%22>1%83741&S@r8%221>&Z>%12O:%>3O31p071p0A1peHH1p`:J1p`@L1paJN1pTNQ11pR8Q:1pdBQ<1").
Proof.
intros segs E M kn e cands v Hkn. induction cands as [|c rest IH]; cbn [conc_try]; intros H; [discriminate|].
destruct (closedb c); [apply IH; exact H|].
destruct (erange kn c) as [[lo hi]|] eqn:Hr; [|apply IH; exact H].
destruct (Z.leb (hi - lo) conc_limit); [|apply IH; exact H].
destruct (eval_closed (esubst c (ELit lo) e)) as [v0|] eqn:Hv0; [|apply IH; exact H].
destruct (all_eval_to c e v0 lo (Z.to_nat (hi - lo + 1))) eqn:Hall; [|apply IH; exact H].
injection H as <-.
pose proof (erange_sound segs E M kn c lo hi Hkn Hr) as Hb.
pose proof (all_eval_to_sound c e v0 lo _ Hall (bv_unsigned (edenot E c)) ltac:(rewrite Z2Nat.id by lia; lia)) as He.
rewrite <- (esubst_sound E c (ELit (bv_unsigned (edenot E c))) e) by (cbn [edenot]; apply Z_to_bv_bv_unsigned).
apply eval_closed_sound. exact He.
Qed.
#[using="Type"] Lemma concretize_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q<':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&VHr6r5r4r3%544321'D%@18&S:%1265(2r2%22=1%73641&S@r7%221=&Z>%12M>%=3M31p071p0@1peHG1p`@I1paJK1pTNN1pR8Q71pdBQ91").
Proof.
intros segs E M kn e v Hkn H. unfold concretize in H.
destruct (closedb e); [apply eval_closed_sound; exact H | eapply conc_try_sound; eassumption].
Qed.
#[using="Type"] Lemma conc_expr_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q2':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG&VHr5r4r3r2%544321'D&S@&S8%1265%3291%42:7%63E21p081p`@?1paJA1pTND1pR8M1pdBO1").
Proof.
intros segs E M kn e Hkn. unfold conc_expr.
assert (Hg : forall e', edenot E (match concretize kn e' with Some v => ELit v | None => e' end) = edenot E e').
{ intros e'. destruct (concretize kn e') as [v|] eqn:Hc; [|reflexivity].
symmetry. exact (concretize_sound segs E M kn e' v Hkn Hc). }
destruct e; try reflexivity; apply Hg.
Qed.
#[using="Type"] Lemma to_saddrK_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q8':'Q7%211'SB'Z?yR0%211'<y8%511%311p051'T3%=11'SG'Q2&VHr6r5r4r3%544321'D&S0&UJr2%23761%42:1&RF&S@%12=:%3216%:3J51p0<1pa:C1p`@E1paJG1pTNJ1pR8Q31pdBQ51").
Proof.
intros segs E M kn e imm Hkn. unfold to_saddrK.
destruct (split_lit e) as [b k] eqn:Hs.
destruct b; try (destruct (concretize kn (mkAlu ALU_ADD e (ELit imm))) as [v|] eqn:Hc;
[ unfold adenot; cbn [a_base a_off edenot];
pose proof (concretize_sound segs E M kn _ v Hkn Hc) as Hv; rewrite mkAlu_denot in Hv; cbn [edenot] in Hv;
unfold v_addi; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; rewrite Z.mod_0_l by lia; rewrite Z.add_0_l;
apply (f_equal bv_unsigned) in Hv; rewrite Z_to_bv_unsigned, bv_wrap64_mod in Hv; rewrite <- Hv;
rewrite alu_add; unfold v_add; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod;
rewrite Zplus_mod_idemp_r; reflexivity
| apply to_saddr_denot ]).
apply to_saddr_denot.
Qed.
Section StepSound.
Variable segs : list Segment.
Definition st_ok (E : env) (base rom : word -> option byte)
(ss : sym_state) (ms : machine_state) : Prop :=
exists regs, ms = mkst regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
/\ regs_ok E (s_regs ss) regs
/\ log_flat E (s_log ss)
/\ know_ok segs E base (s_know ss).
#[using="Type"] Lemma msize_bytes_range : ltac2:(TCodec.tc2 tcn__SymExec2Sound "<'R4'C'Ju1&TKr1%211%5241u8%7231%9231pe@;1").
Proof. destruct sz; cbn; lia. Qed.
#[using="Type"] Lemma sym_step_sound_load : ltac2:(TCodec.tc2 tcn__SymExec2Sound "T@'SB'Z?yR0%211'<y8%511%311p051'UG&R6y5%2219'R4'5%>14y<%@11':'U?%211'U<yQ0%F11'D%E12&Q9vZ8&Z>&U6r<%211%42N1%7261(2r1%22=1%=3<41&Q:r2%211(7%B3L21'>'R3'Q2%3221%Q;11&Q@r3%211(=(QKr;r:r9r8%55K4321+4%84?>21%J2>1%Q53>;1'UD&UHr=%=51Q3<;:r?r6%54Q9321(ROr7r5%33@21%QA3;51&VLrBrC%34QB21E&VKrD&U7rA%211r@%63521&VIrE&U5%11=%4231&VHrF&U4%11A%44R3381'E'Q<'C'Q;%113&Q=&RDvX<%R:1A%R<2S61&VJrHrG%E1F%43321%958O61C%;2RD1(Q8%12AR>%RJ3?31&VAr>%25;:J1RB%E241qbDG1%I2H1p0K1p0Q11p0Q71p0Q?1p0QD1p0R11p0RE1p0RK1peJS:1pd>S=1pd<S>1pd@S@1pdJSL1pa:SE1pd4SH1pcBSI1pe>SK1pe@SM1pcDSO1pdHT31pd2T51p_NT61pR8T?1").
Proof.
intros E base rom ss regs sz sx rd rs imm ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
set (n := msize_bytes sz) in Hs.
set (sx' := match sz with SZ8 => false | _ => sx end) in Hs.
set (a := to_saddrK (s_know ss) (sr_get (s_regs ss) rs) (bv_signed imm)) in Hs.
pose proof (msize_bytes_range sz) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = v_addi (getr regs rs) (bv_signed imm)).
{ subst a. rewrite (to_saddrK_denot segs E base _ _ _ Hkn), Hregs. reflexivity. }
assert (Hsx : sx' = eff_sx sz sx) by (subst sx'; destruct sz; reflexivity).
assert (Hfin : forall v bs,
rdn segs mem (adenot E a) n = Some bs -> length bs = n ->
Z_to_bv 64 (extz sx' n (bytes_le_to_Z bs)) = edenot E v ->
exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (s_pc ss)) mem rom) = MachineOk ms'
/\ st_ok E base rom (sset ss rd v (s_pc ss + 4)) ms').
{ intros v bs Hrd Hlen Hval.
rewrite Hadr in Hrd.
eexists; split; [exact (step_load segs regs _ mem rom w sz sx rd rs imm bs Hf He Hd Hrd)|].
eexists; split; [f_equal; cbn [s_pc sset]; apply v_addi_lit|].
cbn [s_regs s_log s_know sset]. split; [|split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|].
rewrite load_result_val by (subst n; exact Hlen). rewrite <- Hsx. fold n. symmetry. exact Hval. }
destruct (log_lookup (s_know ss) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) as [v lscs lh|lscs lh|] eqn:Hll;
[ | | discriminate].
-
injection Hs as <- <- <-.
apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc].
pose proof (log_lookup_sound segs E base (s_know ss) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] Hkn Hlf Hn1 Hn8) as HL.
rewrite Hll in HL.
destruct (HL Hsc ltac:(destruct a; exact Hfl)) as (bs & Hrd & Hlen & Hval).
apply (Hfin v bs); [destruct a; exact Hrd | exact Hlen | exact Hval].
-
pose proof (log_lookup_sound segs E base (s_know ss) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] Hkn Hlf Hn1 Hn8) as HL.
rewrite Hll in HL.
pose proof (know_lookup_sound segs E base (s_know ss) (a_base a) (a_off a) n sx' lh lscs Hkn Hn1 Hn8) as HK.
pose proof (know_lookup_acc segs (s_know ss) (a_base a) (a_off a) n sx' lh lscs) as HKacc.
destruct (know_lookup segs (s_know ss) (a_base a) (a_off a) n sx' lh lscs) as [v kscs kh|kscs kh|] eqn:Hkl;
[ | | discriminate].
+
injection Hs as <- <- <-.
apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc].
destruct HKacc as [pre ->].
assert (Hlscs : scs_denot segs base E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
destruct (HK Hsc ltac:(destruct a; exact Hfl)) as (bs & Hrd & Hlen & Hval).
apply (Hfin v bs); [| exact Hlen | exact Hval].
destruct a; cbn [a_base a_off] in *. unfold mem. rewrite (HL Hlscs Hfl). exact Hrd.
+
injection Hs as <- <- <-.
apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc].
apply scs_denot_cons in Hsc as [Hrb Hsc]. cbn [sc_denot] in Hrb.
destruct Hrb as (bs & Hrd & Hval).
destruct HKacc as [pre ->].
assert (Hlscs : scs_denot segs base E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
assert (Hrd' : rdn segs mem (adenot E a) n = Some bs).
{ destruct a; cbn [a_base a_off] in *. unfold mem. rewrite (HL Hlscs Hfl). exact Hrd. }
pose proof (rdn_length _ _ _ _ _ Hrd') as Hlen.
rewrite Hadr in Hrd'.
eexists; split; [exact (step_load segs regs _ mem rom w sz sx rd rs imm bs Hf He Hd Hrd')|].
eexists; split; [f_equal; cbn [s_pc]; apply v_addi_lit|].
cbn [s_regs s_log s_know]. split; [|split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|].
rewrite load_result_val by (subst n; exact Hlen). rewrite <- Hsx. fold n. symmetry. exact Hval.
Qed.
#[using="Type"] Lemma sym_step_sound_store : ltac2:(TCodec.tc2 tcn__SymExec2Sound "T='SB'Z?yR0%211'<y8%511%311p051'UG&R6y5%2219'R4%=13y<%?11':'U?%211'U<yQ0%E11'D%D12&Q9vZ8&Z>&U6r;%211%42M1%7261(2r1%22=1%=3<41'5&Q:r2%211(7%C3521'>'R3'Q2%3221%Q;11&Q@r3%211(=(R0r:r9r8%44K321+4%74>=21%J2=1%Q53=:1'UD&UHr<%<41Q3;:r>r6%54Q9321(ROr7r5%33@21%QA3;51&VLrArB%34QB21E&VKrC&U7r@%211r?%63521&VIrD&U5%11=%4231&VHrE&U4%11A%44R3381'E'Q<'C'Q;%113&Q=&RDvX<%R:1A%R<2S51&VJrGrF%E1F%43321%958O61C%;2RD1(Q8%12AR>%RJ3?31&VA%15:9IQBRA%D231qbDF1%H2G1p0J1p0Q01p0Q61p0Q>1p0QC1p0R01p0RC1p0RJ1peJS91pd>S<1pd<S=1pd@S?1pdJSJ1pa:SD1pd8SG1pd6SH1pe@SJ1pcDSL1pdHT01pd2T21p_NT31pR8T<1").
Proof.
intros E base rom ss regs sz rs1 rs2 imm ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
injection Hs as <- <- <-.
set (n := msize_bytes sz) in *.
set (a := to_saddrK (s_know ss) (sr_get (s_regs ss) rs1) (bv_signed imm)) in *.
pose proof (msize_bytes_range sz) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm)).
{ subst a. rewrite (to_saddrK_denot segs E base _ _ _ Hkn), Hregs. reflexivity. }
apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc].
assert (Hok : RiscvSemantics.store_ok segs base (adenot E a) n = true).
{ unfold storeok_sc in Hsc.
destruct (wr_covered (s_know ss) a n) eqn:Hw.
- clear Hsc. revert Hw. generalize Hkn. generalize (s_know ss) as kn. intros kn Hkn0 Hw.
induction kn as [|K rest IH]; cbn [wr_covered] in Hw; [discriminate|].
apply Forall_cons_iff in Hkn0 as [HK Hrest].
destruct K as [| | | | | |[kb kk] len|]; try (apply IH; assumption).
destruct (expr_eqb (a_base a) kb && Z.leb kk (a_off a) && Z.leb (a_off a + Z.of_nat n) (kk + len))%bool eqn:Hc;
[|apply IH; assumption].
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
cbn [kentry_ok] in HK. destruct HK as [Hfk Hs0].
replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (a_off a - kk))).
+ apply Hs0; lia.
+ apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite <- H1.
destruct Hfl as (?&?&?&?). unfold estart in *. rewrite u_small by lia. lia.
- apply scs_denot_cons in Hsc as [Hok _]. cbn [sc_denot] in Hok. exact Hok. }
assert (Hok' : RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) n = true).
{ rewrite <- Hadr. unfold mem. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
eexists; split; [exact (step_store segs regs _ mem rom w sz rs1 rs2 imm Hf He Hd Hok')|].
eexists; split.
- f_equal; [cbn [s_pc]; apply v_addi_lit|].
cbn [s_log mem_denot]. fold n. rewrite Hadr, (Hregs rs2). reflexivity.
- cbn [s_regs s_log s_know]. split; [exact Hregs|]. split; [|exact Hkn].
cbn [log_flat]. split; [exact Hn8|]. split; [exact Hfl | exact Hlf].
Qed.
Ltac alu_case STEP DEN :=
match goal with
| Hs : SOk _ _ _ = SOk _ _ _ |- _ =>
injection Hs as <- <- <-;
eexists; split; [ STEP |];
eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |];
cbn [s_regs s_log s_know sset];
match goal with
| Hregs : regs_ok _ _ _, Hlf : log_flat _ _, Hkn : know_ok _ _ _ _ |- _ =>
split; [ apply regs_ok_upd; [exact Hregs|]; DEN | split; [exact Hlf | exact Hkn] ]
end
end.
#[using="Type"] Lemma sym_step_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "S6'SB'Z?yR0%211'<y8%511%311p051'UG'Q<'R3':'U?%211'U<yQ0%@11'D%?12&Q9vZ8&Z>&U6r8%211%42H1%7261(2r1%22=1%=3<41'5&Q:r2%211(7%C3521'>'Q2%22M1%Q511&Q@r3%211(=+4%24Q48G1%D281%O3851'UD&UHr9r;r6%44Q2321(ROr7r5%33Q321%Q:3:51&VLr>r?%34Q;21Q8&VAr@r=r<%4536721'E'C'Q;%11QO&Q=%12QF=(Q8%12R3Q@%QL3531rBrA%@521?=QD%;241qbDR91%>2R:1p0@1p0F1p0K1p0Q71p0QD1p0QK1peJR:1pd>R=1pd<R>1pd@R@1pdJRF1pa6RE1pbBRG1pdHRI1pd2RK1p_NRL1pR8S51").
Proof.
intros E base rom ss ms i ss' scs scr scr' w Hf He Hd Hs Hsc (regs & -> & Hregs & Hlf & Hkn).
destruct i;
try (eapply sym_step_sound_load; eassumption);
try (eapply sym_step_sound_store; eassumption);
set (mem := mem_denot E base (s_log ss)) in *;
cbn [sym_step] in Hs; try discriminate.
-
alu_case ltac:(exact (step_lui segs regs _ mem rom w rd imm Hf He Hd))
ltac:(cbn [edenot]; unfold v_lui; apply Z_to_bv64_u).
-
alu_case ltac:(exact (step_auipc segs regs _ mem rom w rd imm Hf He Hd))
ltac:(cbn [edenot]; rewrite Z_to_bv64_u; symmetry; apply v_auipc_lit).
-
injection Hs as <- <- <-.
eexists; split; [ exact (step_jal_link segs regs _ mem rom w rd imm Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sset]; rewrite btgt_lit; symmetry; apply Z_to_bv64_u |].
cbn [s_regs s_log s_know sset]. split; [| split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|]. cbn [edenot]. symmetry. apply v_addi_lit.
-
pose proof (conc_expr_sound segs E base (s_know ss) (sr_get (s_regs ss) rs1) Hkn) as Hce.
destruct (conc_expr (s_know ss) (sr_get (s_regs ss) rs1)) as [z| | | | | | |] eqn:Hg; try discriminate.
injection Hs as <- <- <-.
eexists; split; [ exact (step_jalr segs regs _ mem rom w rd rs1 imm Hf He Hd) |].
eexists; split.
+ f_equal. cbn [s_pc sset]. unfold v_jalr.
specialize (Hregs rs1) as Hg1. rewrite <- Hce in Hg1. cbn [edenot] in Hg1.
rewrite Hg1. rewrite Z_to_bv64_mod. exact (jalr_tgt_lit z (bv_signed imm)).
+ cbn [s_regs s_log s_know sset]. split; [| split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|]. cbn [edenot]. symmetry. apply v_addi_lit.
-
set (tk := bv_unsigned (Z_to_bv 64 (s_pc ss + bv_signed imm))) in Hs.
assert (Hcond : forall t, branch_taken c (getr regs rs1) (getr regs rs2) = t ->
exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (s_pc ss)) mem rom) = MachineOk ms'
/\ st_ok E base rom (sjump ss (if t then tk else (s_pc ss + 4)%Z)) ms').
{ intros t Ht. destruct t.
- eexists; split; [exact (step_branch_tk_gen segs regs _ mem rom w c rs1 rs2 imm Hf He Hd Ht)|].
eexists; split; [| split; [exact Hregs | split; [exact Hlf | exact Hkn]]].
f_equal. cbn [s_pc sjump]. rewrite btgt_lit. subst tk. symmetry. apply Z_to_bv64_u.
- eexists; split; [exact (step_branch_ft_gen segs regs _ mem rom w c rs1 rs2 imm Hf He Hd Ht)|].
eexists; split; [| split; [exact Hregs | split; [exact Hlf | exact Hkn]]].
f_equal. cbn [s_pc sjump]. apply v_addi_lit. }
destruct (decide_branch (s_know ss) c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) as [t|] eqn:Hdb.
+
injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
eapply decide_branch_sound; [exact Hkn | exact Hdb].
+ destruct (decide_branch (s_know ss) c (conc_expr (s_know ss) (sr_get (s_regs ss) rs1))
(conc_expr (s_know ss) (sr_get (s_regs ss) rs2))) as [t|] eqn:Hdb2.
*
injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
rewrite <- (conc_expr_sound segs E base (s_know ss) (sr_get (s_regs ss) rs1) Hkn).
rewrite <- (conc_expr_sound segs E base (s_know ss) (sr_get (s_regs ss) rs2) Hkn).
eapply decide_branch_sound; [exact Hkn | exact Hdb2].
*
destruct (sc_dirs scr) as [|t dirs'] eqn:Hdirs; [discriminate|].
injection Hs as <- <- <-. apply Hcond.
apply scs_denot_cons in Hsc as [Hbr _]. cbn [sc_denot] in Hbr.
rewrite (Hregs rs1), (Hregs rs2). exact Hbr.
-
alu_case ltac:(exact (step_opimm_gen segs regs _ mem rom w op rd rs1 imm Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hkn); cbn [edenot]; rewrite <- Hregs, sext64_lit; reflexivity).
-
alu_case ltac:(exact (step_shiftimm_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hkn); cbn [edenot]; rewrite <- Hregs, zext64_lit; reflexivity).
-
alu_case ltac:(exact (step_op_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hkn); rewrite <- !Hregs; reflexivity).
-
alu_case ltac:(exact (step_opimm32_gen segs regs _ mem rom w rd rs1 imm Hf He Hd))
ltac:(rewrite mkAluw_denot; cbn [edenot]; rewrite <- Hregs, sext32_low32; reflexivity).
-
alu_case ltac:(exact (step_shiftimm32_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd))
ltac:(rewrite mkAluw_denot; cbn [edenot]; rewrite <- Hregs, zext32_low32; reflexivity).
-
alu_case ltac:(exact (step_op32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite mkAluw_denot; rewrite <- !Hregs; reflexivity).
-
injection Hs as <- <- <-.
eexists; split; [ exact (step_fence segs regs _ mem rom w _ _ _ _ _ Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sjump]; apply v_addi_lit |].
cbn [s_regs s_log s_know sjump]. split; [exact Hregs | split; [exact Hlf | exact Hkn]].
-
injection Hs as <- <- <-.
eexists; split; [ exact (step_fencei segs regs _ mem rom w _ _ _ Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sjump]; apply v_addi_lit |].
cbn [s_regs s_log s_know sjump]. split; [exact Hregs | split; [exact Hlf | exact Hkn]].
-
alu_case ltac:(exact (step_mul_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite mkMd_denot; rewrite <- !Hregs; reflexivity).
-
alu_case ltac:(exact (step_mul32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite mkMdw_denot; rewrite <- !Hregs; reflexivity).
Qed.
End StepSound.
#[using="Type"] Lemma sidecond_eqb_eq : ltac2:(TCodec.tc2 tcn__SymExec2Sound ">'U?'D'5&U@r2r1%3221(@%73621r3%93:16p031pf4<1pf2=1").
Proof.
intros x y H. destruct x, y; cbn [sidecond_eqb] in H; try discriminate;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
| H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
end; subst; reflexivity.
Qed.
#[using="Type"] Lemma sc_mem_In : ltac2:(TCodec.tc2 tcn__SymExec2Sound "A'U?':%112'D'5&U;r2r1%3221(@%73621&VNr3%23=17p041paN=1pf2@1").
Proof.
induction l as [|y t IH]; cbn [sc_mem]; intros H; [discriminate|].
apply orb_prop in H as [H|H].
- left. symmetry. apply sidecond_eqb_eq. exact H.
- right. apply IH. exact H.
Qed.
#[using="Type"] Lemma sc_add_denot : ltac2:(TCodec.tc2 tcn__SymExec2Sound "Q2':'Q7%211'Z?yR0%211'<y8%511%311p051'SB'U?%=11&VLr5r4r3&U:r2r1%3221%847651'Cr6%;41:98%<42;:7%4221p061p_>@1pbNA1pR8D1p_NF1pdBO1").
Proof.
intros segs base E news. induction news as [|x t IH]; intros acc H; cbn [sc_add] in H.
- split; [constructor | exact H].
- destruct (sc_mem x acc) eqn:Hm.
+ destruct (IH acc H) as [Ht Hacc]. split; [|exact Hacc].
constructor; [|exact Ht].
apply sc_mem_In in Hm. unfold scs_denot in Hacc. rewrite Forall_forall in Hacc. apply Hacc. exact Hm.
+ destruct (IH (x :: acc) H) as [Ht Hxa]. apply scs_denot_cons in Hxa as [Hx Hacc].
split; [constructor; assumption | exact Hacc].
Qed.
Section ExecSound.
Variable segs : list Segment.
#[using="Type"] Lemma sym_exec_acc : forall fuel first stops scr ss acc E base,
match sym_exec segs fuel first stops scr ss acc with
| (ss', scs, scr') => scs_denot segs base E scs -> scs_denot segs base E acc
end.
Proof.
induction fuel as [|f IH]; intros first stops scr ss acc E base; cbn [sym_exec].
- intros H; exact H.
- destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [intros H; exact H|].
destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|intros H; exact H].
destruct (is_ecall w); [intros H; exact H|].
destruct (decode_any w) as [[i sz]|]; [|intros H; exact H].
destruct (negb (Z.eqb sz 4)); [intros H; exact H|].
destruct (sym_step segs i ss scr) as [ss2 scs2 scr2|]; [|intros H; exact H].
specialize (IH false stops scr2 ss2 (sc_add scs2 acc) E base).
destruct (sym_exec segs f false stops scr2 ss2 (sc_add scs2 acc)) as [[ss' scs] scr'].
intros H. apply IH in H. apply sc_add_denot in H as [_ H]. exact H.
Qed.
#[using="Type"] Theorem sym_exec_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "R6';'5':'Q2%211'U<'UG'U?%611'SB'Z?yR0%211'<y8%511%311p051'Q<'D'>%12?=%221A&UFvZ8r=r<r;r:r9r8%877654321(=r7r6%34MK21r5%54@Q021%C3@71&VLr4%24A158&VBr3%26D:84A1'E'C'RBr1%23I=1%86JDA@G2%5221qbDQ21%82Q31p0:1p0>1p0B1pbBQ71pd2Q91p_NQ:1pR8QC1pd>QH1pd@QF1pdJQI1p_>QH1pdHQK1pd<QM1pe<QO1p`FR31p`HR51").
Proof.
induction fuel as [|f IH]; intros first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
{ cbn in Hex. injection Hex as <- <- <-. exists ms. split; [apply mst_refl | exact Hst]. }
assert (Hstop : (ss, acc, scr) = (ss', scs, scr') ->
exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms').
{ intro HX. injection HX as <- <- <-. exists ms. split; [apply mst_refl | exact Hst]. }
cbn [sym_exec] in Hex.
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact (Hstop Hex)|].
destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact (Hstop Hex)].
destruct (is_ecall w) eqn:He; [exact (Hstop Hex)|].
destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hstop Hex)].
destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in Hex; [|exact (Hstop Hex)].
apply Z.eqb_eq in Hsz. subst sz.
destruct (sym_step segs i ss scr) as [ss2 scs2 scr2|] eqn:Hstep; [|exact (Hstop Hex)].
pose proof (sym_exec_acc f false stops scr2 ss2 (sc_add scs2 acc) E base) as Hacc.
rewrite Hex in Hacc. specialize (Hacc Hsc). apply sc_add_denot in Hacc as [Hsc2 _].
destruct (sym_step_sound segs E base rom ss ms i ss2 scs2 scr scr2 w Hf He Hd Hstep Hsc2 Hst)
as (msA & HstepA & HstA).
destruct (IH false stops scr2 ss2 (sc_add scs2 acc) ss' scs scr' E base rom msA Hex Hsc HstA)
as (msB & HmsB & HstB).
exists msB. split; [|exact HstB].
eapply mst_step; [ destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact HmsB ].
Qed.
#[using="Type"] Theorem sym_exec_ex : ltac2:(TCodec.tc2 tcn__SymExec2Sound "RJ';'5':'Q2%211'U<'UG'U?%611'SB'Z?yR0%211'<y8%511%311p051'Q<'D'>%12?=%221A&UFvZ8r=r<r;r:r9r8%877654321(=r7r6%34MK21r5%54@Q021%C3@71&VLr4%24A158&VBr3%26D:84A1'E&R6y5%221Q4'C&VK&U7%11Ir1%43H21&VI&U5%11N%32L1'RB&RDvX<&Z>&U6%11Q5%32QF1&VJ%13Q5Q2:%857?31Q2%:3Q=Q11%E2<1%F2A1qU2H1%L2I1p0N1p0Q21p0Q61pbBQK1pd2QM1p_NQN1pR8R71pd>R<1pd@R:1pdJR=1p_>R<1pdHR?1pd<RA1pe<RC1p`FRG1p`HRI1").
Proof.
intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
destruct (sym_exec_sound fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst)
as (ms' & Hms & (R & Heq & Hregs & Hlf & _)).
exists R. split; [exact Hregs|]. split; [exact Hlf|]. rewrite <- Heq. exact Hms.
Qed.
End ExecSound.
#[using="Type"] Lemma wbytes_out : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QA':'Z?y8%211%411yR0%511'<%115p031&W4&W0&ZDr2%2291&W>&9r4%22?1%411%9261&W@+2+R0%3221%?251'G&W8r3%A2H1%32@1r5%@2M1%B11%G251%I21E%:261'D&RAr6%249G1<%:1=%53Q221p071p0C1pf2Q71p_<Q81pb>Q61p`6Q<1").
Proof.
intros bs m a x Hnw [H|H].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.
Section CarrySound.
Variable segs : list Segment.
#[using="Type"] Lemma kentry_ok_frame : forall E M (wa : saddr) w (V : word) K (ka : saddr) (kl : expr),
flat E wa (Z.of_nat w) ->
kentry_ok segs E M K ->
match K with
| KWord a w' _ => ka = a /\ kl = elen w' /\ (w' <= 8)%nat
| KZero a n => ka = a /\ kl = n
| KBlob a n _ => ka = a /\ kl = n
| KImg lo hi => ka = SA (ELit 0) lo /\ kl = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)%Z
| KAlign _ _ => True
| KRange _ _ _ => True
| KWr _ _ => True
| KDisj _ _ _ _ => True
end ->
((estart E wa + Z.of_nat w <= estart E ka)%Z \/ (estart E ka + elenZ E kl <= estart E wa)%Z) ->
kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) K.
Proof.
intros E M wa w V K ka kl Hfw HK Hshape Hdis.
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
destruct K as [[kb kk] w' v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2]; cbn [kentry_ok] in *;
[ | | | | exact HK | exact HK
| destruct HK as [Hf0 Hs0]; split; [exact Hf0|]; intros d m Hd Hm;
eapply store_ok_mono; [apply wbytes_grows | apply Hs0; assumption]
| exact HK ].
- destruct Hshape as (-> & -> & Hw8). destruct HK as (Hkw8 & Hfk & Hrd). split; [exact Hkw8|]. split; [exact Hfk|].
rewrite elenZ_elen in Hdis by exact Hw8.
rewrite rdn_wbytes_out; [exact Hrd | | |].
+ rewrite length_N_to_le_bytes, Huw, (flat_u E _ _ Hfk). lia.
+ rewrite (flat_u E _ _ Hfk). destruct Hfk as (?&?&?&?). lia.
+ rewrite length_N_to_le_bytes, Huw. lia.
- destruct Hshape as (-> & ->). destruct HK as [Hfk Hz]. split; [exact Hfk|].
intros i Hi. rewrite wbytes_out; [apply Hz; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia.
- destruct Hshape as (-> & ->). destruct HK as (Hfk & Hlen & Hb). split; [exact Hfk|]. split; [exact Hlen|].
intros i Hi. rewrite wbytes_out; [apply Hb; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia.
- destruct Hshape as (-> & -> & Hsz). destruct HK as (Hlo & Hhi & Hnone). split; [exact Hlo|]. split; [exact Hhi|].
intros i Hi. rewrite estart_lit0, elenZ_lit in Hdis.
rewrite wbytes_out; [apply Hnone; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. rewrite u_small by lia.
assert ((hi - lo) mod 2 ^ 64 = hi - lo)%Z by (apply Z.mod_small; lia). lia.
Qed.
#[using="Type"] Lemma Forall_app_intro : forall {A} (P : A -> Prop) l1 l2,
Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof. intros. apply Forall_app. auto. Qed.
#[using="Type"] Lemma kzero_piece : ltac2:(TCodec.tc2 tcn__SymExec2Sound "RI'SB'Z?yR0%211'<y8%511%311p051'SG'Q2';&VFr:(RNr8r7%3221&W>r6%211%93841&VGvZ8r;(RKr9r5%>221(RHr4%211%7241%;4:9D1&W4z%2216&W8%1238&W0%12E=&W;&W@+2+R0%3221%52N1%=271'G%:2GQ1%;21Or<%B221%Q31M%?231%E216%8241r@&RAr?&S0r>r=%QA221%4271&Q?%12?Q:%93831%M2QGQE%QG281%Q91QF%Q>221%QB4QA?51p0A1p0K1p0Q51p0Q81p0Q<1p0QI1pb6R51pa8R61pb0R71paHR81p_:R@1peJR91pf0R;1peNR=1pTNR?1pR8RH1").
Proof.
intros E M wb wk w V kk l0 i0 len Hfw [Hfk Hz] Hi0 Hlen Hil Hdis.
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
rewrite elenZ_lit in Hfk, Hz. cbn [kentry_ok]. rewrite elenZ_lit.
unfold flat, estart in *; cbn [a_base a_off] in *.
destruct Hfk as (Hk1 & Hk2 & Hk3 & Hk4).
pose proof (Z.mod_pos_bound l0 (2 ^ 64) ltac:(lia)) as Hl.
rewrite (Z.mod_small len) by lia.
split; [lia|].
intros i Hi.
rewrite wbytes_out.
- replace (bv_unsigned (edenot E wb) + (kk + i0) + i)%Z
with (bv_unsigned (edenot E wb) + kk + (i0 + i))%Z by lia.
apply Hz. lia.
- rewrite length_N_to_le_bytes, Huw. lia.
- rewrite length_N_to_le_bytes, Huw. rewrite u_small by lia. lia.
Qed.
#[using="Type"] Lemma kimg_piece : ltac2:(TCodec.tc2 tcn__SymExec2Sound "R1'SB'Z?yR0%211'<y8%511%311p051'U8';'Q2&VFr9r7&W>r6%211%63541&VGvZ8r:(RJr5r4%3221%7465=1&W4%12<4%225='G&VDr=r;%3221%82<1&W0%F1@%2241%<21G%:251r>&RA&S0r<%2241&Q?%12>J%63@31%K2Q3Q1%O4N921p0;1p0G1p0I1p0L1p0Q51pa0Q=1pb:Q>1p`NQ?1pb8Q@1p_:QI1peJQC1peLQE1pTNQG1pR8R01").
Proof.
intros E M wa w V lo hi lo' hi' Hfw (Hlo & Hhi & Hnone) H1 H2 Hdis.
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
cbn [kentry_ok]. split; [lia|]. split; [lia|].
intros i Hi. rewrite wbytes_out.
- apply Hnone. lia.
- rewrite length_N_to_le_bytes, Huw. lia.
- rewrite length_N_to_le_bytes, Huw. rewrite u_small by lia. lia.
Qed.
#[using="Type"] Lemma Forall_one : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. intros. constructor; [assumption | constructor]. Qed.
#[using="Type"] Lemma prune1_sound : forall E (anybase : word -> option byte) M0 allkn M wa w V K hints kept scs hs',
prune1 allkn wa w K hints = (kept, scs, hs') ->
know_ok segs E M0 allkn ->
(w <= 8)%nat ->
flat E wa (Z.of_nat w) ->
kentry_ok segs E M K ->
match K with KWord _ w' _ => (w' <= 8)%nat | _ => True end ->
scs_denot segs anybase E scs ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept.
Proof.
intros E anyb M0 allkn M wa w V K hints kept scs hs' Hp Hall Hw8 Hfw HK Hkw Hscs.
pose proof (flat_u E _ _ Hfw) as Huw.
assert (Hfw' := Hfw). destruct Hfw' as (Hw1 & Hw2 & Hw3 & Hw4).
unfold prune1 in Hp.
assert (Hdiff : forall ka kl,
(let apart := match kl with
| ELit l => ranges_apart allkn (a_base wa) (a_off wa) (Z.of_nat w) (a_base ka) (a_off ka) (l mod 2 ^ 64)%Z
| _ => false
end in
if apart then ([K], [], hints) else
match hints with
| true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end) = (kept, scs, hs') ->
match K with
| KWord a w' _ => ka = a /\ kl = elen w' /\ (w' <= 8)%nat
| KZero a n => ka = a /\ kl = n
| KBlob a n _ => ka = a /\ kl = n
| KImg lo hi => ka = SA (ELit 0) lo /\ kl = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)%Z
| KAlign _ _ => True
| KRange _ _ _ => True
| KWr _ _ => True
| KDisj _ _ _ _ => True
end ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept).
{ intros ka kl Hm Hshape. cbv zeta in Hm.
assert (Hkl : forall l, kl = ELit l ->
ranges_apart allkn (a_base wa) (a_off wa) (Z.of_nat w) (a_base ka) (a_off ka) (l mod 2 ^ 64) = true ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) [K]).
{ intros l -> Hap. apply Forall_one.
pose proof (ranges_apart_sound segs E M0 allkn _ _ _ _ _ _ Hall Hap) as Hdis.
eapply kentry_ok_frame; eauto;
rewrite elenZ_lit; destruct wa, ka; cbn [a_base a_off] in *; exact Hdis. }
destruct kl as [l| | | | | | |];
[ destruct (ranges_apart allkn (a_base wa) (a_off wa) (Z.of_nat w) (a_base ka) (a_off ka) (l mod 2 ^ 64)) eqn:Hap;
[ injection Hm as <- <- <-; apply (Hkl l eq_refl Hap) | ]
| .. ];
(destruct hints as [|[|] hs]; try (injection Hm as <- <- <-);
[ constructor | | constructor ];
(apply scs_denot_cons in Hscs as [Hd _]; cbn [sc_denot] in Hd;
destruct Hd as (_ & _ & Hd); rewrite elenZ_elen in Hd by exact Hw8;
constructor; [ eapply kentry_ok_frame; eauto | constructor ])). }
destruct K as [[kb kk] w' v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2].
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
5: { injection Hp as <- <- <-. apply Forall_one. cbn [kentry_ok] in HK |- *.
destruct HK as [Hf0 Hs0]. split; [exact Hf0|]. intros d m Hd Hm.
eapply store_ok_mono; [apply wbytes_grows | apply Hs0; assumption]. }
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
-
destruct (expr_eqb kb (a_base wa)) eqn:Heqb; [|eapply Hdiff; [exact Hp | cbn; auto]].
apply expr_eqb_eq in Heqb.
destruct (Z.leb (kk + Z.of_nat w') (a_off wa) || Z.leb (a_off wa + Z.of_nat w) kk)%bool eqn:Hd;
injection Hp as <- <- <-; [|constructor].
apply Forall_one.
eapply (kentry_ok_frame E M wa w V _ (SA kb kk) (elen w') Hfw HK); [cbn; auto|].
rewrite elenZ_elen by exact Hkw. unfold estart. cbn [a_base a_off]. subst kb.
destruct wa as [wb wk]; cbn [a_base a_off] in *.
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
-
destruct (expr_eqb kb (a_base wa)) eqn:Heqb; [|eapply Hdiff; [exact Hp | cbn; auto]].
apply expr_eqb_eq in Heqb.
destruct wa as [wb wk]; cbn [a_base a_off] in *. subst kb.
destruct n as [l0| | | | | | |];
[
injection Hp as <- <- <-;
assert (HK' := HK); destruct HK' as [Hfk _]; rewrite elenZ_lit in Hfk;
destruct Hfk as (Hk1 & Hk2 & Hk3 & Hk4); unfold estart in Hk1, Hk2, Hk4; cbn [a_base a_off] in Hk1, Hk2, Hk4;
lazymatch goal with |- Forall ?P (?A ++ ?B) =>
assert (H1 : Forall P A);
[ destruct (Z.ltb kk (Z.min wk (kk + l0 mod 2 ^ 64))) eqn:Hlt; [|constructor];
apply Z.ltb_lt in Hlt; apply Forall_one;
replace kk with (kk + 0)%Z at 1 by lia;
eapply kzero_piece; [exact Hfw | exact HK | lia | lia | lia | lia]
| assert (H2 : Forall P B);
[ destruct (Z.ltb (Z.max kk (wk + Z.of_nat w)) (kk + l0 mod 2 ^ 64)) eqn:Hlt; [|constructor];
apply Z.ltb_lt in Hlt; apply Forall_one;
replace (Z.max kk (wk + Z.of_nat w)) with (kk + (Z.max kk (wk + Z.of_nat w) - kk))%Z at 1 by lia;
eapply kzero_piece; [exact Hfw | exact HK | lia | lia | lia | lia]
| exact (Forall_app_intro _ _ _ H1 H2) ] ]
end
| .. ];
(destruct (Z.leb (wk + Z.of_nat w) kk) eqn:Hle; injection Hp as <- <- <-; [|constructor];
apply Z.leb_le in Hle; apply Forall_one;
eapply (kentry_ok_frame E M (SA wb wk) w V _ (SA wb kk) _ Hfw HK); [cbn; auto|];
unfold estart; cbn [a_base a_off]; lia).
-
destruct (expr_eqb kb (a_base wa)) eqn:Heqb; [|eapply Hdiff; [exact Hp | cbn; auto]].
apply expr_eqb_eq in Heqb.
destruct wa as [wb wk]; cbn [a_base a_off] in *. subst kb.
destruct n as [l0| | | | | | |];
[ destruct (Z.leb (kk + l0 mod 2 ^ 64) wk || Z.leb (wk + Z.of_nat w) kk)%bool eqn:Hd;
injection Hp as <- <- <-; [|constructor];
apply Forall_one;
eapply (kentry_ok_frame E M (SA wb wk) w V _ (SA wb kk) (ELit l0) Hfw HK); [cbn; auto|];
rewrite elenZ_lit; unfold estart; cbn [a_base a_off];
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia
| .. ];
(destruct (Z.leb (wk + Z.of_nat w) kk) eqn:Hle; injection Hp as <- <- <-; [|constructor];
apply Z.leb_le in Hle; apply Forall_one;
eapply (kentry_ok_frame E M (SA wb wk) w V _ (SA wb kk) _ Hfw HK); [cbn; auto|];
unfold estart; cbn [a_base a_off]; lia).
-
assert (Hdb : (if (hi - lo <? 2 ^ 64)%Z
then (if ranges_apart allkn (a_base wa) (a_off wa) (Z.of_nat w) (ELit 0) lo ((hi - lo) mod 2 ^ 64)%Z
then ([KImg lo hi], [], hints) else
match hints with
| true :: hs => ([KImg lo hi], [SCDisj wa (elen w) (SA (ELit 0) lo) (ELit (hi - lo))], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end)
else ([], [], hints)) = (kept, scs, hs') ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept).
{ intros Hq. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt.
- apply Z.ltb_lt in Hlt. eapply Hdiff; [exact Hq | cbn; auto].
- injection Hq as <- <- <-. constructor. }
destruct (a_base wa) as [z| | | | | | |] eqn:Hwb; try (apply Hdb; exact Hp).
destruct z; try (apply Hdb; exact Hp).
injection Hp as <- <- <-.
assert (Hws : estart E wa = a_off wa).
{ unfold estart. rewrite Hwb. cbn [edenot]. rewrite u_lit0. lia. }
assert (HK' := HK). destruct HK' as (Hlo & Hhi & _).
lazymatch goal with |- Forall ?P (?A ++ ?B) =>
assert (H1 : Forall P A);
[ destruct (Z.ltb lo (Z.min (a_off wa) hi)) eqn:Hlt; [|constructor]; apply Z.ltb_lt in Hlt;
apply Forall_one; eapply kimg_piece; [exact Hfw | exact HK | lia | lia | lia]
| assert (H2 : Forall P B);
[ destruct (Z.ltb (Z.max lo (a_off wa + Z.of_nat w)) hi) eqn:Hlt; [|constructor]; apply Z.ltb_lt in Hlt;
apply Forall_one; eapply kimg_piece; [exact Hfw | exact HK | lia | lia | lia]
| exact (Forall_app_intro _ _ _ H1 H2) ] ]
end.
Qed.
Fixpoint kn_words_le8 (kn : list kentry) : Prop :=
match kn with
| [] => True
| KWord _ w' _ :: r => (w' <= 8)%nat /\ kn_words_le8 r
| _ :: r => kn_words_le8 r
end.
#[using="Type"] Lemma know_ok_words_le8 : ltac2:(TCodec.tc2 tcn__SymExec2Sound "H'SB'Z?yR0%211'<y8%511%311p051':'T3%211&VHvZ8r3r2r1%544321&V@%114p031paJ:1pTN>1pR8G1").
Proof.
intros E M kn H. induction kn as [|K r IH]; [exact I|].
apply Forall_cons_iff in H as [HK Hr].
destruct K as [a w' v| | | | | | |]; cbn [kn_words_le8]; auto.
cbn [kentry_ok] in HK. split; [exact (proj1 HK) | apply IH; exact Hr].
Qed.
#[using="Type"] Lemma prune_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "RE'SB'Z?yR0%211'<y8%511%311p051':'T3%211'U8';'5%611'U?%811'D'>%1293%2216&TNr:r8r7r5r4%6554321(=r3r2%34E?21r1%54>C21%A3>71&VHvZ8r>r<r;%544321'Jr9u8%3221&VFr@&W>%11J%433:1rAr=%A4@21:&VLrB%24C51OrC&RAr?&S0%124G&Q?%12;H%63531%M4L81Fp0:1p0>1p0B1p0H1p0M1p0Q41pa4QI1pd@QH1paLQO1pa2QL1paJR11p_:R:1peJR11peLR31pTNR81p_DR61pU0R:1p_FR;1pR8RD1").
Proof.
intros E anyb M0 allkn M wa w V kn. induction kn as [|K rest IH]; intros hints kn' scs hs' Hp Hall Hw8 Hfw Hkn Hscs.
- cbn in Hp. injection Hp as <- <- <-. constructor.
- cbn [prune] in Hp.
destruct (prune1 allkn wa w K hints) as [[kept scs1] hs1] eqn:Hp1.
destruct (prune allkn wa w rest hs1) as [[r scs2] hs2] eqn:Hpr.
injection Hp as <- <- <-.
apply Forall_cons_iff in Hkn as [HK Hrest].
apply scs_denot_app in Hscs as [Hs1 Hs2].
apply Forall_app. split.
+ eapply prune1_sound; eauto.
destruct K as [a w' v| | | | | | |]; try exact I. exact (proj1 HK).
+ eapply IH; eauto.
Qed.
#[using="Type"] Lemma carry_sound : ltac2:(TCodec.tc2 tcn__SymExec2Sound "QO'SB'Z?yR0%211'<y8%511%311p051':'U=%211'T3%411'5%611'U?%811'D'>%1273%2216&S5r6r5r4%43321(=r3r2%34A=21r1%54<A21%?3<71&VIr:r7%3221&VHvZ8r;r9%443216&VLr<%24651Er=&VJ%1328=%;4:31=p051p091p0?1p0D1pa4Q71pd@Q61paLQ;1pa2Q:1paJQ=1pb<Q@1p_NQD1p_FQE1pR8QN1").
Proof.
intros E anyb base log. induction log as [|[a w v] older IH]; intros kn hints kn' scs hs' Hc Hlf Hkn Hscs.
- cbn in Hc. injection Hc as <- <- <-. exact Hkn.
- cbn [carry] in Hc. cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf').
destruct (carry older kn hints) as [[kn1 scs1] hs1] eqn:Hco.
destruct (prune kn1 a w kn1 hs1) as [[kn2 scs2] hs2] eqn:Hpr.
injection Hc as <- <- <-.
apply scs_denot_app in Hscs as [Hs1 Hs2].
cbn [mem_denot].
constructor.
+ cbn [kentry_ok]. split; [exact Hw8|]. split; [exact Hfa|].
pose proof (rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v)) (mem_denot E base older) (adenot E a)) as Hh.
rewrite length_N_to_le_bytes in Hh. apply Hh. rewrite (flat_u E _ _ Hfa).
destruct Hfa as (?&?&?&?). lia.
+ eapply prune_sound; eauto.
Qed.
End CarrySound.
End FPX_2.
End SX2S.
