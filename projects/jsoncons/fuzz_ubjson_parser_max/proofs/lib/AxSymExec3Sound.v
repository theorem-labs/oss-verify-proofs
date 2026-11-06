(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SymStepR AxSymExec3.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AxSymExec3Sound () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S.FPX_1.LinDenot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S.FPX_2.CarrySound."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S.FPX_2.StepSound."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S.FPX_2.XSound."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymStepR."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1S"; "1Some"; "1andb"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1orb"]; ["1pair"; "1prod"; "1snd"; "1true"; "1tt"; "1unit"; "2I"; "2True"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3add"; "3sub"]; ["4le"; "4lt"; "5Forall"; "5firstn"; "5map"; "5nth"; "5repeat"; "5skipn"; "6N"; "6Z"; "0E"; "0E'"; "0E''"; "0E0"; "0E1"; "0E2"]; ["0E3"; "0K"; "0L"; "7Z_to_le_bytes"; "7bytes_le_to_Z"; "7nat_to_word"; "8Segment"; "8seg_base"; "8seg_size"; "9MachineOk"; "9fetch_word"; "9find_segment"; "9is_ecall"; "9machine_result"; "9machine_state"; "9ms_mem"]; ["9ms_regs"; "9step"; "9store_ok"; "9word_to_le_bytes"; ":decode_any"; ";ALU_ADD"; ";ALU_AND"; ";ALU_OR"; ";ALU_SLL"; ";ALU_SRA"; ";ALU_SRL"; ";ALU_SUB"; ";ALU_XOR"; ";Amo"; ";Load"; ";Lr"]; [";M_DIVU"; ";M_MUL"; ";M_MULHU"; ";M_REMU"; ";Sc"; ";Store"; ";aluop"; ";amoop"; ";awidth"; ";branch_cond"; ";instr"; ";msize"; ";mulop"; "<bvmap"; "<sext"; "<zext"]; ["=alu32"; "=alu64"; "=amo_bytes"; "=amo_val"; "=branch_taken"; "=low32"; "=mul_div"; "0M"; "0M'"; "0M0"; "0R"; ">EAlu"; ">EExt"; ">ELit"; ">EVar"; ">Env"]; [">KBlob"; ">KFill"; ">KImg"; ">KUnk"; ">KWord"; ">KZero"; ">RDisjoint"; ">RInside"; ">SA"; ">SCReadBase"; ">SOk"; ">a_base"; ">a_off"; ">adenot"; ">all_eval_to"; ">all_eval_toS"]; [">aluop_eqb"; ">amo_alignedb"; ">amo_aluop"; ">amo_newval"; ">amo_sz"; ">and_high_split"; ">and_low_split"; ">base_range"; ">blob_val"; ">br_lookup"; ">cap_rd"; ">carry"; ">clampi"; ">clr"; ">coeffs_div"; ">coeffs_divk"]; [">conc_expr"; ">conc_try"; ">concretize"; ">cond_on_eq"; ">ctz64"; ">ctz_fuel"; ">deand"; ">decide_branch"; ">disj_sides"; ">disj_sides_x"; ">ealign"; ">ealign0"; ">edenot"; ">elen"; ">end_hi"; ">enum_branch"]; [">env"; ">erange"; ">erange0"; ">erange_f"; ">esubst"; ">ev"; ">evalS"; ">eval_closed"; ">evars_lt"; ">expr"; ">expr_eqb"; ">extK"; ">extK0"; ">ext_Z"; ">ext_merge_step"; ">ext_partner"]; [">ext_slice"; ">ext_val"; ">fact_nowrap"; ">facts_of"; ">fill_lit"; ">find_align"; ">find_and_atom"; ">find_and_atom_k"; ">find_range"; ">find_readbase"; ">flat_sc"; ">foldK"; ">img_bytes"; ">in_sides"; ">in_sides_x"; ">is_lit"]; [">itab"; ">itab_sound"; ">itv_lts"; ">itv_ltu"; ">kcut"; ">kdisj_apart"; ">kdisj_apart_x"; ">kentry"; ">kentry_overlay"; ">kentry_readable"; ">kfill_cut"; ">kn_overlay"; ">kn_readable"; ">know_byte_lit"; ">know_bytes_lit"; ">ktrim"]; [">kunk_cut"; ">kword_cut"; ">kwr_offimage"; ">kzero_cut"; ">ladd"; ">land32"; ">land64"; ">ldiv_terms"; ">lin"; ">lin_apart"; ">lin_branch"; ">lin_brange"; ">lin_ge0"; ">lin_ge0_scaled"; ">lin_lowbits"; ">lin_lowbits_kn"]; [">lin_nowrap"; ">lin_nowrapR"; ">lin_of"; ">lin_range"; ">lin_srange"; ">lin_test"; ">lin_test_rel"; ">lins"; ">lins_e"; ">lit_shamt"; ">lit_strip"; ">lmerge"; ">lmerge_f"; ">log_byte_lit"; ">log_bytes_lit"; ">lowbits"]; [">lscale"; ">lscale_terms"; ">lsplit_div"; ">lsub_e"; ">lterm"; ">lterms"; ">mask_cover"; ">mkAlu"; ">mkAluK"; ">mkAluK0"; ">mkAluw"; ">mkAluwK"; ">mkAluwK0"; ">mkAnd"; ">mkAnd0"; ">mkAndK"]; [">mkExt"; ">mkMd"; ">mkMdK"; ">mkMdw"; ">mkOr"; ">mkSrl"; ">mk_sprep"; ">msize_bytes"; ">mulop_eqb"; ">or_disjoint"; ">pageup_align"; ">pageup_low"; ">pageup_low_k"; ">pow2_log"; ">prune"; ">prune1"]; [">prune1p"; ">prune_zf"; ">prunep"; ">prunepc"; ">range_branch"; ">rangerel"; ">ranges_apart"; ">ranges_apart_p"; ">ranges_apart_pc"; ">ranges_apart_x"; ">rel_lit"; ">resv_inval"; ">ridx"; ">s_clean"; ">s_know"; ">s_log"]; [">s_next"; ">s_pc"; ">s_regs"; ">s_resv"; ">saddr"; ">saddr_eqb"; ">sc_add"; ">sc_mem"; ">scr_nil"; ">scripts"; ">sentry"; ">sfact"; ">shamt_of"; ">sidecond"; ">sidecond_eqb"; ">snorm"]; [">sprep"; ">sr_id"; ">sr_upd"; ">srl_expand"; ">srl_rem"; ">stepres"; ">storeok_sc"; ">sub_fact"; ">sub_itv"; ">sub_itv_x"; ">sum_fact_x"; ">sum_facts"; ">sum_subst"; ">sx32"; ">sym_exec"; ">sym_execS"]; [">sym_execSX"; ">sym_execSX_go"; ">sym_execS_go"; ">sym_execT"; ">sym_execTX"; ">sym_execTX_go"; ">sym_execT_go"; ">sym_read"; ">sym_state"; ">sym_step"; ">sym_stepX"; ">to_saddr"; ">to_saddrK"; ">two64"; ">two64z"; ">unlin"]; [">wrap64"; ">x_dischargeable"; ">x_filter"; ">xhi"; ">xinside"; ">xlo"; ">xt_const"; ">xt_lin"; ">xt_nowrap"; ">xterms"; ">zalu"; ">zalu_l"; ">zaluw"; ">zaluw_l"; ">zbytes_le_to_Z"; ">zext_fast"]; [">zext_lit"; ">zf_covers"; ">zfast"; ">zfastm"; ">zfastw"; ">zlit64"; ">zmd"; ">zmd_l"; "Alden"; "Atden"; "AuE"; "@elenZ"; "@eqm"; "@estart"; "@extz"; "@flat"]; ["@know_ok"; "@mem_denot"; "@reg_ev"; "@regs_ok"; "@sc_denot"; "@scs_denot"; "@tden"; "Cbr_cache_ok"; "Ckn_words_le8"; "Czf_kind"; "Dresv_denot"; "Dst_ok"; "Dst_okR"; "Eeagree"; "Eeupd"; "Erd1"]; ["Est_okX"; "Bresv_denot"; "Bsfact_ok"; "Bst_ok"; "Bst_okR"; "Bxt_den"; "?elenZ"; "?eqm"; "?estart"; "?extz"; "?flat"; "?kentry_ok"; "?know_ok"; "?log_flat"; "?mem_denot"; "?regs_ok"]; ["?sc_denot"; "?scs_denot"; "?tden"; "?uE"; "Fwbytes"; "Gmsteps"; "Hgetr"; "Hmkst"; "Hrdn"; "Hv_addi"; "Imem_grows"; "Jamo_msize"; "Jamo_nbytes"; "Jamo_store_bytes"; "Jeff_sx"; "Jload_result"]; ["JmkstR"; "Jmsize_bytes"; "Jresv_inval_w"; "0SA"; "KIn"; "Kfold_right"; "Kforallb"; "Lle"; "Madd"; "Mdiv"; "Mdivide"; "Mland"; "Mle"; "Mleb"; "Mlnot"; "Mlog2_up"]; ["Mlor"; "Mlt"; "Mltb"; "Mlxor"; "Mmodulo"; "Mmul"; "Mof_N"; "Mof_nat"; "Mopp"; "Mpow"; "Msub"; "Mtestbit"; "Mto_nat"; "0V"; "0a"; "0a0"]; ["0acc"; "0ah"; "0al"; "0allkn"; "0anybase"; "0aop"; "0apart"; "0aq"; "0b"; "0b'"; "0b1"; "0b2"; "0base"; "0bh"; "0bits"; "0bk"]; ["0bl"; "0bs"; "0byteof"; "0c"; "0c'"; "0cache"; "0cands"; "0ck"; "0cnt"; "0d"; "0diffbase"; "0dts"; "0e"; "0e'"; "0ebs"; "0f"]; ["0first"; "0fk"; "0fs"; "0fts"; "0fuel"; "0fx"; "0h"; "0h1"; "0hi"; "0hi'"; "0hi1"; "0hints"; "0hit"; "0hit'"; "0hs'"; "0i"]; ["0i0"; "0imm"; "0j"; "0k"; "0k1"; "0k2"; "0ka"; "0kb"; "0kept"; "0kk"; "0kn"; "0kn'"; "0l"; "0l0"; "0l1"; "0l2"]; ["0len"; "0lo"; "0lo'"; "0lo1"; "0log"; "0m"; "0mem"; "0mk"; "0mm"; "0mr"; "0ms"; "0ms'"; "0n"; "0n'"; "0n1"; "0n2"]; ["0ne"; "0neg"; "0news"; "0nk"; "0nr"; "0nx'"; "0o"; "0op"; "0others"; "0pos"; "0pre"; "0q"; "0r"; "0r'"; "0ra"; "0rb"]; ["0rd"; "0regs"; "0rest"; "0rhi"; "0rho"; "0rk"; "0rl"; "0rlo"; "0rn"; "0rng"; "0rom"; "0rs"; "0rs1"; "0rs2"; "0rts"; "0s"]; ["0sc"; "0scr"; "0scr'"; "0scs"; "0segs"; "0sg"; "0sh"; "0sp"; "0sr"; "0src"; "0ss"; "0ss'"; "0ssx"; "NBV"; "NZ_to_bv"; "Nbv"]; ["Nbv_add"; "Nbv_extract"; "Nbv_signed"; "Nbv_swrap"; "Nbv_unsigned"; "Nbv_wrap"; "0stops"; "0sx"; "0sx'"; "0sz"; "0t"; "0test"; "0ts"; "0ts'"; "0ts1"; "0ts2"]; ["0u"; "0ua"; "0ur"; "0v"; "0vold"; "0w"; "0w'"; "0wa"; "0wb"; "0wd"; "0wk"; "0wn"; "0wv"; "0x"; "0y"; "0y'"]; ["0z"; "0zs"]]).
Module AX2S.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Export AX2.
Section FPX_1. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma aluop_eqb_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'RF'I'6&T0r2r1%3221(C%73621r3%93:16p031plB<1pkN=1").
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
#[using="Type"] Lemma mulop_eqb_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'RL'I'6&X8r2r1%3221(C%73621r3%93:16p031plB<1pkN=1").
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
#[using="Type"] Lemma expr_eqb_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'U9'I'6&U:r2r1%3221(C%73621r3%93:16p031pQUN<1pQUL=1").
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
#[using="Type"] Lemma saddr_eqb_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'Y4'I'6&Y5r2r1%3221(C%73621r3%93:16p031plB<1pkN=1").
Proof.
intros [ab ak] [bb bk] H. unfold saddr_eqb in H. cbn [a_base a_off] in H.
apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2.
subst. reflexivity.
Qed.
#[using="Type"] Lemma edenot_lit : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "A'U0'Q9'I'aOyR0%211&TLr2(S=r1%211%5241&aN%1294%<3931pQV2>1pRF@1").
Proof. reflexivity. Qed.
#[using="Type"] Lemma alu64_add_0_r : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='aOyR0%211'I&S1(R5r1&aNz%2281%63541%83915pQU8:1").
Proof.
intro v. rewrite alu_add. unfold v_add. apply bv_eq.
rewrite !Z_to_bv_unsigned. change (bv_wrap 64 0) with 0%Z.
rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.
#[using="Type"] Lemma alu64_add_comm : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='aOyR0%211'I&S1(R5r2r1%43321%53423%73821plB91pkN:1").
Proof. intros. rewrite !alu_add. apply v_add_comm. Qed.
#[using="Type"] Lemma alu64_sub_as_add : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "D'aOyR0%211'Q9'I&S1(R;r2&aNr1%2291%63541(R5&]H%115%72>1%;3491%=3?61pQUN?1pQU8A1").
Proof.
intros v y. rewrite alu_sub, alu_add, v_sub_lit, v_add_lit. f_equal.
Qed.
Definition eqm (a b : Z) : Prop := exists q, (a = b + q * 2 ^ 64)%Z.
#[using="Type"] Lemma eqm_refl : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "5'Q9&[<r1%2211pkN41"). Proof. intros; exists 0%Z; lia. Qed.
#[using="Type"] Lemma eqm_sym : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'Q9&[<r2r1%3221r3%5241p031plB81pkN91"). Proof. intros a b [q H]; exists (-q)%Z; lia. Qed.
#[using="Type"] Lemma eqm_trans : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "<'Q9&[<r3r2%3221r5%5214p031p041pm891plB:1pkN;1").
Proof. intros a b c [q H] [r H']; exists (q + r)%Z; lia. Qed.
#[using="Type"] Lemma eqm_add : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'Q9&[<r4r3%3221r2%5231&]8r6%2217r5%4218%;231p071p0:1pmD?1pm8@1plBA1pkNB1").
Proof. intros a b c d [q H] [r H']; exists (q + r)%Z; lia. Qed.
#[using="Type"] Lemma eqm_mul_l : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "?'Q9&[<r2r1%3221&]Er4r3%3221%4237%9221p071plB<1pkN=1po8>1").
Proof. intros k a b [q H]; exists (k * q)%Z. subst a. ring. Qed.
#[using="Type"] Lemma eqm_mul_r : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "?'Q9&[<r2r1%3221&]Er3r4%3221%4272%9221p071plB<1pkN=1po8>1").
Proof. intros k a b [q H]; exists (q * k)%Z. subst a. ring. Qed.
#[using="Type"] Lemma eqm_mod : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ";'Q9&[<&]Dr1&]I+2+R0%3221%6251%8216pkN:1").
Proof. intros a. exists (- (a / 2 ^ 64))%Z. pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)). lia. Qed.
#[using="Type"] Lemma two64z_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "8'I'Q9&Z>&]I+2+R0%3221%73651"). Proof. reflexivity. Qed.
#[using="Type"] Lemma eqm_snorm : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "7'Q9&[<&Y?r1%211%4212po861").
Proof.
intros k. rewrite snorm_eq. unfold snorm_ref. rewrite two64z_eq. pose proof (Z.div_mod k (2 ^ 64) ltac:(lia)).
destruct (Z.leb (2 ^ 63) (k mod 2 ^ 64)).
- exists (- (k / 2 ^ 64) - 1)%Z. lia.
- exists (- (k / 2 ^ 64))%Z. lia.
Qed.
#[using="Type"] Lemma eqm_Z_to_bv : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "A'Q9&[<r2r1%3221'I'aOyR0%211&aNr3%2241%325:%83521p0:1plB?1pkN@1").
Proof.
intros a b [q H]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. subst a. apply Z.mod_add. lia.
Qed.
#[using="Type"] Lemma u_lit64a : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "@'Q9'I&b4yR0&aNr1%2231%5241&]D&]I+2+R0%3221%5281%=3>71pQV2?1").
Proof. intros. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.
#[using="Type"] Lemma eqm_u_lit : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'Q9&[<&b4yR0&aNr1%2231%5241%7213pQV291").
Proof. intros. rewrite u_lit64a. apply eqm_mod. Qed.
Section LinDenot.
Variable E : env.
Definition uE (e : expr) : Z := bv_unsigned (edenot E e).
Fixpoint tden (ts : list (Z * expr)) : Z :=
match ts with [] => 0 | (k, a) :: rest => k * uE a + tden rest end.
Definition lden (x : lin) : Z := (fst x + tden (snd x))%Z.
#[using="Type"] Lemma lins_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'Q9'U9';'A%1243%311&[<&[9&W7r3r2r1%43321%611&]8&]E&[:%117%3291%<18%6221%?281pQTJA1pkNF1po8H1").
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
#[using="Type"] Lemma ladd_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "?&VH&[<&[8&VDr2r1%3221%511&]8%715%815%3221%;251pQUN=1pQUL>1").
Proof.
intros [c ts] [d us]. unfold ladd, lden. cbn [fst snd].
assert (Hf : forall l acc, eqm (tden (fold_right (fun t acc => lins (fst t) (snd t) acc) acc l)) (tden l + tden acc)).
{ induction l as [|[k a] l IH]; intros acc; cbn [fold_right tden].
- exists 0%Z. lia.
- eapply eqm_trans; [apply lins_sound|]. cbn [fst snd].
destruct (IH acc) as [r Hr]. exists r. lia. }
pose proof (eqm_snorm (c + d)) as [q Hq]. destruct (Hf ts us) as [r Hr]. exists (q + r)%Z. lia.
Qed.
#[using="Type"] Lemma lscale_terms_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'Q9';'A'U9%2241%411&[<&[9&WAr2r1%3221%511&]E%714%2261%:241pQTJ<1pQP<B1").
Proof.
intros m ts. induction ts as [|[k a] rest IH]; cbn [lscale_terms tden].
- exists 0%Z. lia.
- pose proof (eqm_snorm (m * k)) as [q Hq]. destruct IH as [r Hr].
destruct (Z.eqb (snorm (m * k)) 0) eqn:Hz; cbn [tden].
+ apply Z.eqb_eq in Hz. exists (r + q * uE a)%Z. nia.
+ exists (r + q * uE a)%Z. nia.
Qed.
#[using="Type"] Lemma lscale_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "?'Q9&VH&[<&[8&W@r2r1%3221%511&]E%714%2261%:241pQUL<1pQP<>1").
Proof.
intros m [c ts]. unfold lscale, lden. cbn [fst snd].
pose proof (eqm_snorm (m * c)) as [q Hq]. destruct (lscale_terms_sound m ts) as [r Hr].
exists (q + r)%Z. nia.
Qed.
#[using="Type"] Lemma u_add_eqm : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "B'aOyR0%211&[<&b4&S1(R5r2r1%43321%6291&]8%82;5%92<5%3221%<251pQUN>1pQUL?1").
Proof. intros. rewrite alu_add. unfold v_add. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_sub_eqm : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "B'aOyR0%211&[<&b4&S1(R;r2r1%43321%6291&]J%82;5%92<5%3221%<251pQUN>1pQUL?1").
Proof. intros. rewrite alu_sub. unfold v_sub. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_mul_eqm : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "B'aOyR0%211&[<&b4&S6(RAr2r1%448321%6291&]E%82;5%92<5%3221%<251pQUN>1pQUL?1").
Proof. intros. rewrite m_mul. unfold v_mul. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_sll_eqm : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'aOyR0%211'Q9&[<&b4&S1(R8r2&aNr1%22:1%63541%82<1&]E&]I+2&]D+R0%2291%5241%@2D=%8221%C2:1pQS0E1pQULG1").
Proof.
intros. rewrite alu_sll. unfold v_sll. rewrite (u_lit64a s).
replace ((s mod 2 ^ 64) mod 64)%Z with (s mod 64)%Z by (symmetry; apply Z.mod_mod_divide; exists (2^58)%Z; reflexivity).
rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). rewrite Z.mul_comm. apply eqm_u_lit.
Qed.
#[using="Type"] Lemma lin_of_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ";'U9&[<&[8&W2r1%211%411&[:%114%8231pmJ:1").
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
#[using="Type"] Lemma lterm_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'A'Q9'U9%3221&[<&[:&WDr1%211%411&]E&9%13;:5&B%13=<7%:11%6241%=281pQTF?1").
Proof.
intros [k a]. unfold lterm. cbn [fst snd]. destruct (Z.eqb k 1) eqn:Hk.
- apply Z.eqb_eq in Hk. subst. exists 0%Z. lia.
- unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_mul_eqm|]. cbn [edenot].
apply eqm_mul_r. apply eqm_u_lit.
Qed.
#[using="Type"] Lemma lterms_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "@';'A'Q9'U9%3221%511&[<&[:&WEr1%211%411&[9%114%8231pQTJ:1").
Proof.
induction ts as [|t rest IH]; cbn [lterms tden].
- unfold uE. cbn [edenot]. rewrite u_lit64a. exists 0%Z. reflexivity.
- destruct rest as [|t' rest'].
+ destruct t as [k a]. cbn [tden]. rewrite Z.add_0_r. apply lterm_sound.
+ destruct t as [k a]. unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_add_eqm|].
apply eqm_add; [apply (lterm_sound (k, a)) | exact IH].
Qed.
#[using="Type"] Lemma unlin_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ";&VH&[<&[:&Z?r1%211%411&[8%114%8231pQUL:1").
Proof.
intros [c ts]. unfold unlin, lden. cbn [fst snd].
destruct ts as [|t rest].
- cbn [tden]. unfold uE. cbn [edenot]. rewrite Z.add_0_r. apply eqm_u_lit.
- destruct (Z.eqb c 0) eqn:Hc.
+ apply Z.eqb_eq in Hc. subst c. rewrite Z.add_0_l. apply lterms_sound.
+ unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_add_eqm|]. rewrite Z.add_comm.
apply eqm_add; [cbn [edenot]; apply eqm_u_lit | apply lterms_sound].
Qed.
#[using="Type"] Lemma tden_app : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "D';'A'Q9'U9%3221%511'I&[9&5r2r1%33721%511&]8%715%815%3221%;3?51pQP0=1poN>1").
Proof. induction l1 as [|[k a] l1 IH]; intros l2; cbn [tden app]; [lia|]. rewrite IH. lia. Qed.
#[using="Type"] Lemma ext_Z_u : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'<'Q9'Q0r2u8%3221'H&]<z&U=(8r4r3%44321:%7261&]A&]I+2+R0%3221%5271%?271p0A1pQV2F1pQPJH1pQP4I1").
Proof.
intros lo n z Hn. unfold ext_Z.
pose proof (Z.mod_pos_bound (z / 2 ^ (8 * Z.of_nat lo)) (2 ^ (8 * Z.of_nat n)) ltac:(apply Z.pow_pos_nonneg; lia)) as H.
assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.
#[using="Type"] Lemma uE_ext : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "G'<'U9'Q0r2u8%3221'I'Q9&[:(S<(8r4r3%44321:%611&U=%81=%247651%<3;41p0>1pQU8C1pQPJE1pQP4F1").
Proof.
intros lo n v Hn. unfold uE. cbn [edenot]. unfold ext_val. rewrite Z_to_bv_unsigned.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. apply ext_Z_u. exact Hn.
Qed.
#[using="Type"] Lemma ext_Z_split : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "O'<'Q9'I&U=(8r4&Nr3r2%3221r1%847621&]8%:49863&]E&]I+2+8&]G%11<%6231%6251%@2A?%D4C1?=%:231%=2<1%H3I?1pQV2J1pQPLL1pQPJM1pQP4N1").
Proof.
intros lo n n' z. unfold ext_Z.
set (p := (2 ^ (8 * Z.of_nat n))%Z). set (q := (2 ^ (8 * Z.of_nat n'))%Z). set (a := (z / 2 ^ (8 * Z.of_nat lo))%Z).
assert (Hp : (0 < p)%Z) by (subst p; apply Z.pow_pos_nonneg; lia).
assert (Hq : (0 < q)%Z) by (subst q; apply Z.pow_pos_nonneg; lia).
replace (2 ^ (8 * Z.of_nat (n + n')))%Z with (p * q)%Z
by (subst p q; rewrite <- Z.pow_add_r by lia; f_equal; lia).
replace (z / 2 ^ (8 * Z.of_nat (lo + n)))%Z with (a / p)%Z
by (subst a p; rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia); f_equal; rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.rem_mul_r by lia. lia.
Qed.
#[using="Type"] Lemma uE_ext_slice : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'<'U9'Q0&Nr3r2%3221u8%6221'I'Q9&[:&U@r4%231:9%411&U=(8%71=%3426?1%;3:51p0=1pQU8E1pQPJG1pQP4H1").
Proof.
intros lo n v H. unfold ext_slice.
destruct (Nat.eqb lo 0 && Nat.eqb n 8)%bool eqn:Hb.
- apply andb_true_iff in Hb as [H0 H8]. apply Nat.eqb_eq in H0. apply Nat.eqb_eq in H8. subst lo n.
unfold ext_Z. change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r. change (8 * Z.of_nat 8)%Z with 64%Z.
symmetry. apply Z.mod_small. unfold uE. pose proof (bv_unsigned_in_range 64 (edenot E v)) as Hr.
change (bv_modulus 64) with (2^64)%Z in Hr. lia.
- apply uE_ext. lia.
Qed.
#[using="Type"] Lemma ext_partner_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R0'Q9'<'U9';'A%1253%311'I'>%5283%211&U?r7r6r5r4r3%6554321(3(@r2r1%34E@21%52>1%A3>71'H'Q0&N%12@?%221=u8%5221&[<&[9%11C&]8&]Er8&]I+2+8&]G%11M%7231%6251%9281&[:(S<(8%241EQ1Q3%411%?261%C1Q0%B221%F2D1%N2H1p0Q01pQQJQC1pQPLQI1pQTJQE1pQU8QJ1pQPJQL1pQP4QM1pm8QO1").
Proof.
intros c lo n v ts. induction ts as [|[c' a'] rest IH]; intros n' r H; [discriminate|].
cbn [ext_partner] in H.
assert (REC : match ext_partner c lo n v rest with Some (m, r0) => Some (m, (c', a') :: r0) | None => None end = Some (n', r) ->
(lo + n + n' <= 8)%nat /\ eqm (tden ((c', a') :: rest)) (c * 2 ^ (8 * Z.of_nat n) * uE (EExt false (lo + n) n' v) + tden r)).
{ intros HR. destruct (ext_partner c lo n v rest) as [[m r0]|] eqn:Hp; [|discriminate].
injection HR as <- <-. destruct (IH m r0 eq_refl) as [A [q Hq]]. split; [exact A|].
exists q. cbn [tden]. lia. }
destruct a' as [| | | | | |sx lo' m w|]; try exact (REC H).
destruct sx; [exact (REC H)|].
destruct (Nat.eqb lo' (lo + n) && Nat.leb (lo + n + m) 8 && Nat.ltb 0 m && expr_eqb w v
&& Z.eqb (snorm c') (snorm (c * 2 ^ (8 * Z.of_nat n))))%bool eqn:Hc; [|exact (REC H)].
injection H as <- <-. clear REC IH.
apply andb_true_iff in Hc as [Hc Hs]. apply andb_true_iff in Hc as [Hc Hw]. apply andb_true_iff in Hc as [Hc _].
apply andb_true_iff in Hc as [Hl Hle]. apply Nat.eqb_eq in Hl. apply Nat.leb_le in Hle. apply expr_eqb_eq in Hw. apply Z.eqb_eq in Hs.
subst lo' w. split; [exact Hle|].
cbn [tden]. pose proof (eqm_snorm c') as [q1 H1]. pose proof (eqm_snorm (c * 2 ^ (8 * Z.of_nat n))) as [q2 H2].
exists ((q2 - q1) * uE (EExt false (lo + n) m v))%Z. nia.
Qed.
#[using="Type"] Lemma ext_merge_step_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q;';'A'Q9'U9%3221%511'I'>%7243%211&U>r5r4%3221(3(@r3r2%34@?21r1%54@?21%72=1%@3=91&[<&]8&[9r6%211%31A%5221&]E&[:%11@%32E1%91A%;221%=271p0?1pQQBQ11pkNQ41pm8Q61pQTJQ41pQQFQ51").
Proof.
intros pre ts. revert pre. induction ts as [|[c0 a0] rest IH]; intros pre c a others H; [discriminate|].
cbn [ext_merge_step] in H.
assert (REC : ext_merge_step (pre ++ [(c0, a0)]) rest = Some (c, a, others) -> eqm (tden pre + tden ((c0, a0) :: rest)) (c * uE a + tden others)).
{ intros HR. pose proof (IH _ _ _ _ HR) as [q Hq]. exists q. rewrite tden_app in Hq. cbn [tden] in *. lia. }
destruct a0 as [| | | | | |sx lo n v|]; try exact (REC H).
destruct sx; [exact (REC H)|].
destruct (Nat.ltb 0 n) eqn:Hn; [|exact (REC H)].
destruct (ext_partner c0 lo n v rest) as [[n' rest']|] eqn:Hp; [|exact (REC H)].
injection H as <- <- <-. clear REC IH.
destruct (ext_partner_sound _ _ _ _ _ _ _ Hp) as [Hle [q Hq]].
exists q. rewrite tden_app. cbn [tden]. rewrite Hq.
rewrite uE_ext_slice by lia. rewrite ext_Z_split. rewrite (uE_ext lo n v) by lia. rewrite (uE_ext (lo + n) n' v) by lia. lia.
Qed.
#[using="Type"] Lemma lmerge_f_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='<&VH&[<&[8&W<r2r1%3221%511%613%8221pQUL:1pn:<1").
Proof.
induction fuel as [|f IH]; intros x; cbn [lmerge_f]; [apply eqm_refl|].
destruct (ext_merge_step [] (snd x)) as [[[c a] others]|] eqn:Hs; [|apply eqm_refl].
eapply eqm_trans; [apply IH|].
pose proof (ext_merge_step_sound _ _ _ _ _ Hs) as Hm. cbn [tden] in Hm.
eapply eqm_trans; [apply ladd_sound|].
destruct x as [k ts]. unfold lden in *. cbn [fst snd] in *.
pose proof (lscale_sound c (lin_of a)) as Hsc. pose proof (lin_of_sound a) as Hlo. unfold lden in Hsc, Hlo.
destruct Hm as [q Hq]. destruct Hsc as [r Hr]. destruct Hlo as [t Ht].
exists (r + c * t - q)%Z. nia.
Qed.
#[using="Type"] Lemma lmerge_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":&VH&[<&[8&W;r1%211%411%513%7221pQUL91").
Proof. intros x. apply lmerge_f_sound. Qed.
#[using="Type"] Lemma unlin_ladd : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "K'U9'I'aOyR0%211&TLvQ:&Z?&W;&VD&W2r2%211r1%411%6231%811%:11%=2<1&S1(R5%@2?:%A2@9%43321%G3D61plBI1pkNJ1").
Proof.
intros a b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lmerge_sound|]. eapply eqm_trans; [apply ladd_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_add_eqm]. apply eqm_add; apply lin_of_sound.
Qed.
#[using="Type"] Lemma unlin_lsub : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "L'U9'I'aOyR0%211&TLvQ:&Z?&VD&W2r2%211&W@-1r1%611%4231%9261%;11%>2=1&S1(R;%A2@<%B2A9%43321%H3E61plBJ1pkNK1").
Proof.
intros a b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply ladd_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_sub_eqm].
replace (bv_unsigned (edenot E a) - bv_unsigned (edenot E b))%Z
with (bv_unsigned (edenot E a) + (-1) * bv_unsigned (edenot E b))%Z by lia.
apply eqm_add; [apply lin_of_sound|]. eapply eqm_trans; [apply lscale_sound|]. apply eqm_mul_l. apply lin_of_sound.
Qed.
#[using="Type"] Lemma unlin_lsll : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q0'U9'Q9'I'aOyR0%211&TLvQ:&Z?&W@&]I+2&]Dr1+R0%3221%6251&W2r2%211%;241%=11%@2?1&S1(R8%C2B7&aN%12G>%53431%K3H71pQS0M1pkNO1").
Proof.
intros a s. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_sll_eqm]. apply eqm_mul_l. apply lin_of_sound.
Qed.
#[using="Type"] Lemma unlin_lmul_l : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'Q9'U9'I'aOyR0%211&TLvQ:&Z?&W@r2&W2r1%211%5241%711%:291&S6(RA&aN%12@:%?2>9%54B421%E3B71plBG1pQULI1").
Proof.
intros x b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (mul_div _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]. rewrite u_lit64a.
eapply eqm_trans; [apply eqm_mul_l; apply lin_of_sound|]. apply eqm_mul_r. apply eqm_sym. apply eqm_mod.
Qed.
#[using="Type"] Lemma unlin_lmul_r : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'U9'Q9'I'aOyR0%211&TLvQ:&Z?&W@r1&W2r2%211%5241%711%:291&S6(RA%=2<7&aN%12A;%54B431%E3B71pQUNG1pkNI1").
Proof.
intros a y. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (mul_div _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]. rewrite u_lit64a. rewrite (Z.mul_comm (bv_unsigned _)).
eapply eqm_trans; [apply eqm_mul_l; apply lin_of_sound|]. apply eqm_mul_r. apply eqm_sym. apply eqm_mod.
Qed.
End LinDenot.
#[using="Type"] Lemma coeffs_div_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N'U0'Q9';'A'U9%2241%411&]Azr2%3221'I'6&T>r3%2216(C%63521&]D&[Fr5%2217r4%5221%=3G1@p081p0@1pQTJE1pQP<K1pRFM1").
Proof.
intros E m ts Hm. induction ts as [|[k a] rest IH]; cbn [coeffs_div tden]; intros H.
- apply Z.mod_0_l. lia.
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. specialize (IH H2).
rewrite Z.add_mod, Z.mul_mod, H1, Z.mul_0_l, Z.mod_0_l, Z.add_0_l, IH by lia. apply Z.mod_0_l. lia.
Qed.
#[using="Type"] Lemma pow2_div_64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "B'Q9'H&]<zr1%3221+R0%5231%7231&]:&]I+2r2%3221%4238%6221p081po8A1").
Proof. intros k Hk. exists (2 ^ (64 - k))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
#[using="Type"] Lemma eqm_mod_pow2 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "K'Q9'H&]<zr1%3221+R0%5231%7231&[<r4r3%3221'I&]Dr5&]I+2%2217%5241%62:2%83E21p0:1p0?1po8H1plBI1pkNJ1").
Proof.
intros a b k Hk [q Hq]. subst a. destruct (pow2_div_64 k Hk) as [r Hr]. rewrite Hr.
replace (b + q * (r * 2 ^ k))%Z with (b + (q * r) * 2 ^ k)%Z by ring. apply Z.mod_add.
assert (0 < 2 ^ k)%Z by (apply Z.pow_pos_nonneg; lia). lia.
Qed.
#[using="Type"] Lemma lin_lowbits_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q='U0'U9'Q9'H&]<zr2%3221+R0%5231%7231'I'>%11;&VNr4r3%3221(3%12A=%93731&]D&b4yR0&TLr6r5%3221%6251&]I+2%221@%;241%F3O1A%N2MB&]A%12D5%Q2231%Q3251p0C1p0N1pQU8Q71po8Q81pmJQ:1pRFQ<1").
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
#[using="Type"] Lemma shamt_of_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q='U0'U9'Q9'H&]<zr2%3221+R0%5231%7231'I'>%11;&Y<r4r3%3221(3%12A=%93731&]D&b4yR0&TLr6r5%3221%6251&]I+2%221@%;241%F3O1A%N2MB&]A%12D5%Q2231%Q3251p0C1p0N1pQS0Q71plNQ81pmJQ:1pRFQ<1").
Proof.
intros E e bits s Hb H. assert (Hp : (0 < 2 ^ bits)%Z) by (apply Z.pow_pos_nonneg; lia).
unfold shamt_of in H. destruct e; try (apply lin_lowbits_sound; assumption).
injection H as <-. cbn [edenot]. rewrite u_lit64a. split; [|apply Z.mod_pos_bound; lia].
apply Z.mod_mod_divide. apply pow2_div_64. lia.
Qed.
#[using="Type"] Lemma alu_sll_amt : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "O'aOyR0%211'Q9'I&]D&b4r2%2271+R0%5221r1%83921&S1(R8r4r3%43321&aN&]E%>2C5&]I+2%221@%5241%72H1%F3H91p0?1pQS0I1pQUNK1pQULL1").
Proof.
intros x y s Hs. rewrite alu_sll. unfold v_sll.
pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as Hr. rewrite Hs in Hr. rewrite Hs.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
#[using="Type"] Lemma alu_srl_amt : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'aOyR0%211'I'Q9&]D&b4r2%2271+R0%5221r1%62;1%8214%;3:41&S1(R:r4r3%43321%5343=%B3C21p081pQV0E1pQUNF1pQULG1").
Proof. intros x y y' H. rewrite !alu_srl. unfold v_srl. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma alu_sra_amt : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'aOyR0%211'I'Q9&]D&b4r2%2271+R0%5221r1%62;1%8214%;3:41&S1(R9r4r3%43321%5343=%B3C21p081pQV0E1pQUNF1pQULG1").
Proof. intros x y y' H. rewrite !alu_sra. unfold v_sra. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma w_shift_amt : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q?'RF'aOyR0%211'M'Ir4(R8%33821(R:%53:41(R9%73<61%9231%:261'Q9&]D&b4r3%22A1+Q0%5221r2%62E1%8214%D3:41&RNyQ0&S0r6&S5r5%211%31K%63521%938Q11/01Q1%71C%:3961%=3<Q51%Q33Q541p0@1p0L1pQV0Q81pQUNQ91pQULQ:1pQQ@Q>1").
Proof.
intros op x y y' Hop H. destruct Hop as [-> | [-> | ->]].
- rewrite !w_sllw. unfold v_sllw. rewrite H. reflexivity.
- rewrite !w_srlw. unfold v_srlw. rewrite H. reflexivity.
- rewrite !w_sraw. unfold v_sraw. rewrite H. reflexivity.
Qed.
#[using="Type"] Lemma u_lit_mod : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'Q9'H&]<zr2%3221&]A&]I+2+6%3221%5271%;271'M'I+R0%23@<1+Q0%43B>1%6231r4r3%@221&]D&b4yR0&aNr5%2231%5241%721:%A3O14p0:1p0>1p0F1pQP<Q31pQS0Q41").
Proof. intros s m Hs Hm Hsm. rewrite u_lit64a. rewrite (Z.mod_small s (2 ^ 64)) by lia. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma unlin_lsll_amt : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q7'U0'U9'aOyR0%211'Q9'I&]D&b4r2%2271+R0%5221r1%83921&TLr5&Z?&W@&]I+2%221<&W2r4%211%7241%911%<2;1&S1(R8%?2>7r3%43321%K3M61p0D1pQS0N1pQUNQ01pkNQ41pRFQ61").
Proof.
intros E a y s Hs. rewrite (alu_sll_amt _ _ s Hs).
rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
rewrite Z.mul_comm. apply eqm_mul_r. apply lin_of_sound.
Qed.
#[using="Type"] Lemma and_lowmask_val : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q3'aOyR0%211'Q9&]<zr1%3221r2+R0%6221'I&S1(R6r4&aN&]J&]I+2r3%3221+1%6221%82F1%<3;:1&]D&b4%12J=%3218%>2L1%C3L61p0E1p0I1po6N1pQU8Q01").
Proof.
intros v j Hj Hj64. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j <= 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
rewrite (Z.mod_small (2 ^ j - 1)) by lia.
replace (2 ^ j - 1)%Z with (Z.ones j) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
rewrite Z.land_ones by lia. reflexivity.
Qed.
#[using="Type"] Lemma is_lit_some : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'U9'Q9'I'>%113&UOr2%211(3r1%2291%93741r3(S=%118%=3?31p051pQV2@1pmJB1").
Proof. intros e w H; destruct e; cbn in H; try discriminate. congruence. Qed.
#[using="Type"] Lemma slice_mod : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2'Q9&]<zr2%3221&]8r4r3%3221r5%9221'I&]D&]9r7&]I+2r6%3221%7251%524;%8221%726@%;221%;2:4%=213%?3J31p0A1p0H1p0I1po6N1po8O1pQP<Q01pkNQ11").
Proof.
intros a m k j Hk Hj Hm. apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia.
rewrite !Z.div_pow2_bits by lia.
rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
#[using="Type"] Lemma Z_to_bv64_swrap64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='Q9'I'aOyR0%211&aN&b3r1%2251%4261%5273%:3721pQU2<1").
Proof.
intro u. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_swrap.
unfold bv_wrap. change (bv_half_modulus 64) with (2^63)%Z.
change (bv_modulus 64) with (2^64)%Z.
rewrite <- Zminus_mod_idemp_l.
rewrite Z.mod_mod by lia.
rewrite Zminus_mod_idemp_l.
f_equal. lia.
Qed.
#[using="Type"] Lemma ext_val_full : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'6'aOyR0%211'I&UAr2(1u8r1%544321%73812pQU891pQT@=1").
Proof.
intros sx v. unfold ext_val, ext_Z.
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
change (8 * Z.of_nat 8)%Z with 64%Z. change (8 * N.of_nat 8)%N with 64%N.
pose proof (bv_unsigned_in_range 64 v) as Hr. change (bv_modulus 64) with (2^64)%Z in Hr.
rewrite Z.mod_small by lia.
destruct sx; [rewrite Z_to_bv64_swrap64|]; apply Z_to_bv_bv_unsigned.
Qed.
#[using="Type"] Lemma ext_Z_range : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'<'Q9'Q0r2u8%3221'H&]<z&U=(8r4r3%44321:%7261&]A&]I+2+R0%3221%5271%?271p0A1pQV2F1pQPJH1pQP4I1").
Proof.
intros lo n z Hn. unfold ext_Z.
pose proof (Z.mod_pos_bound (z / 2 ^ (8 * Z.of_nat lo)) (2 ^ (8 * Z.of_nat n)) ltac:(apply Z.pow_pos_nonneg; lia)) as H.
assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
lia.
Qed.
#[using="Type"] Lemma ext_val_compose : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2'6'<'aOyR0%211'Q0&Nr5r4%3221r2%6221r3u8%9221'I&UAr8r7r6(8%541>=9%645431%A2@5%84715<%:3E31p0<1p0@1pQU8H1pQPLL1pQP6M1pQPJN1pQP4O1pQT@Q11").
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
#[using="Type"] Lemma wrap64_mod : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='Q9'I&Z@r1%211&]D&]I+2+R0%3221%5271%:3;71pQV2<1").
Proof.
intros z. unfold wrap64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:H; [|reflexivity].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2. symmetry. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma land64_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'Q9'I&VFr1%211&]D&Z=%2241%73841pQV291").
Proof.
intros z. unfold land64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:H.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. symmetry. apply Z.mod_small. lia.
- unfold ones64z, two64. rewrite Z.land_ones by lia. reflexivity.
Qed.
#[using="Type"] Lemma land32_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'Q9'I&VEr1%211&]D+TPPPPP0%2241%73841pQV291").
Proof.
intros z. unfold land32. destruct (Z.leb 0 z && Z.ltb z two32z)%bool eqn:H.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two32z in H2. symmetry. apply Z.mod_small. lia.
- unfold ones32z. rewrite Z.land_ones by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_63 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ";'Q9'I&];r1+QO%3221&]D+R0%2251%83941pQUN:1").
Proof. intros y. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
#[using="Type"] Lemma land_31 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ";'Q9'I&];r1+O%3221&]D+Q0%2251%83941pQUN:1").
Proof. intros y. change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
#[using="Type"] Lemma zext_fast_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N'6'<'Q9'H&]<zr1%3221&]A&]I+2+R0%3221%5271%;271'I&ZOr5r4r3r2%544321&[0%146543%93F31p0;1pQULH1pQPJJ1pQP4K1pQT@M1").
Proof.
intros sx lo n x Hx. unfold zext_fast, zext_lit, ext_val, ext_Z.
rewrite !u_lit64a. rewrite (Z.mod_small x) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.land_ones by lia.
set (k := (8 * Z.of_nat n)%Z). set (u := ((x / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ k)%Z).
assert (Hk2 : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hu : (0 <= u < 2 ^ k)%Z) by (apply Z.mod_pos_bound; lia).
destruct sx; [|rewrite wrap64_mod; reflexivity].
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
replace (Z.of_N (8 * N.of_nat n)) with k by lia.
destruct n as [|n'].
- subst k. cbn in Hu |- *. rewrite wrap64_mod. f_equal. assert (H0 : u = 0%Z) by lia. rewrite H0. reflexivity.
- assert (Hk : (8 <= k)%Z) by lia.
assert (Hh : (2 ^ k = 2 * 2 ^ (k - 1))%Z) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
replace (2 ^ k `div` 2)%Z with (2 ^ (k - 1))%Z by lia.
rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mul_1_l.
destruct (Z.ltb_spec u (2 ^ (k - 1))) as [Hl|Hge]; rewrite wrap64_mod.
+ f_equal. rewrite Z.mod_small by lia. lia.
+ replace (u + 2 ^ (k - 1))%Z with (u + 2 ^ (k - 1) - 2 ^ k + 1 * 2 ^ k)%Z by lia.
rewrite (Z.mod_add (u + 2 ^ (k - 1) - 2 ^ k) 1 (2 ^ k)) by lia.
rewrite (Z.mod_small (u + 2 ^ (k - 1) - 2 ^ k)) by lia.
replace (u - 2 ^ k + two64)%Z with ((u + 2 ^ (k - 1) - 2 ^ k - 2 ^ (k - 1)) + 1 * 2 ^ 64)%Z by (unfold two64; lia).
rewrite (Z.mod_add _ 1 (2 ^ 64)) by lia. reflexivity.
Qed.
#[using="Type"] Lemma mkExt_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N'U0'6'<'U9'Q0r2u8%3221'I'aOyR0%211&TLr6&X0r5r4r3%44321=%7261&UA%928@%247651%?3<41p0A1pmJF1pQPJH1pQP4I1pQT@K1pRFM1").
Proof.
intros E sx lo n e Hn. unfold mkExt.
destruct e as [x|v|op a b|op a b|op a b|op a b|sx' lo' n' e'|sx' k i n'].
1: { cbn [edenot]. rewrite zext_fast_eq by (rewrite wrap64_mod; apply Z.mod_pos_bound; lia).
unfold zext_lit. rewrite Z_to_bv_bv_unsigned. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite wrap64_mod. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_mod by lia. reflexivity. }
all: destruct (Nat.eqb lo 0 && Nat.eqb n 8)%bool eqn:Hfull;
[ apply andb_prop in Hfull as [H0 H8]; apply Nat.eqb_eq in H0; apply Nat.eqb_eq in H8;
subst; symmetry; apply ext_val_full
| ]; try reflexivity.
destruct sx'; [reflexivity|].
destruct (Nat.leb (lo + n) n' && Nat.leb n' 8)%bool eqn:Hc; [|reflexivity].
apply andb_prop in Hc as [Hc1 Hc2]. apply Nat.leb_le in Hc1. apply Nat.leb_le in Hc2.
cbn [edenot]. symmetry. apply ext_val_compose; assumption.
Qed.
#[using="Type"] Lemma ridx_inj : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "@'aOy5%211'I'<&XLr2%211r1%411%73631r3%93:16p031pQQL<1pQQJ=1").
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
#[using="Type"] Lemma regs_ok_pin : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'U0';'U9%211&RMy5'aOyR0%211%5241%415&[Cr5r4r3%43321'I&\F%1254&TLr6r2%3221%73?51r7&YB&XL%11>%3381>%B351Ap071p0@1pmJN1pQQJG1pQR4I1pQSBQ01pRFQ41").
Proof.
intros E sr regs r e Hr Hv r'. unfold sr_get.
destruct (bv_eqb r' 0) eqn:Hr0.
- assert (r' = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r'. unfold getr. rewrite Hr0. reflexivity.
- rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
+ specialize (Hr r'). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.
#[using="Type"] Lemma ridx_range : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'aOy5%211&Q1&XLr1%211uQ0%5221pQQJ71").
Proof. intro r. unfold ridx. pose proof (u5_range r). lia. Qed.
#[using="Type"] Lemma ridx_roundtrip : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='aOy5%211'I&aN&]G&XLr1%211%411%6291%83914pQQJ:1").
Proof.
intro r. apply bv_eq. unfold ridx. rewrite Z_to_bv_unsigned.
pose proof (u5_range r). rewrite Z2Nat.id by lia.
apply bv_wrap_bv_unsigned.
Qed.
Definition reg_ev (regs : bvmap 5 word) (rest : nat -> word) : nat -> word :=
fun n => if Nat.ltb n 32 then getr regs (Z_to_bv 5 (Z.of_nat n)) else rest n.
#[using="Type"] Lemma regs_ok_id : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J&RMy5'aOyR0%211%5241'<p013';y8%811%311p061&[C(S?&[Br3r2%3221r1%6221&YA%93216pmN;1pQR6A1pQR4D1").
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
#[using="Type"] Lemma mem_denot_grows : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "F'U0'aOyR0%211'>y8%511%311p051';'Y:%211&\Jr2&[Ar3r1%33241%6251pQP:81plJ<1pRFE1").
Proof.
intros E base log. induction log as [|[a w v] rest IH]; cbn [mem_denot].
- apply mem_grows_refl.
- eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.
Definition estart (E : env) (a : saddr) : Z := (bv_unsigned (edenot E (a_base a)) + a_off a)%Z.
Definition elenZ (E : env) (n : expr) : Z := bv_unsigned (edenot E n).
Definition flat (E : env) (a : saddr) (n : Z) : Prop :=
(0 <= estart E a)%Z /\ (estart E a < 2^64)%Z /\ (0 <= n)%Z /\ (estart E a + n <= 2^64)%Z.
#[using="Type"] Lemma flat_u : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "F'U0'Y4'Q9&[?r3r2r1%43321'I&b4yR0&SMr4%2219%5241&[=%124<%93?31p0;1pQPJA1pkNC1pRFE1").
Proof.
intros E a n (H1 & H2 & H3 & H4). unfold adenot, v_addi, estart in *.
rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma flat_mono : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "G'U0'Y4'Q9&[?r4r3r2%43321'H&]<z%2215%3267%5221r6r5%=321;p041p0;1pQP<A1pQPJB1pkND1pRFF1").
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
| KWr a n => flat E a (elenZ E n) /\ forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= elenZ E n)%Z ->
RiscvSemantics.store_ok segs base (Z_to_bv 64 (estart E a + d)) m = true
| KDisj a1 n1 a2 n2 => (estart E a1 + elenZ E n1 <= estart E a2)%Z \/ (estart E a2 + elenZ E n2 <= estart E a1)%Z
| KFill a n c =>
flat E a (elenZ E n)
/\ forall i, (0 <= i < elenZ E n)%Z -> base (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 c)
| KUnk a n =>
flat E a (elenZ E n)
/\ forall i, (0 <= i < elenZ E n)%Z -> base (Z_to_bv 64 (estart E a + i)) <> None
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
#[using="Type"] Lemma w_add_nat : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "F'aOyR0%211'<'I&b0r2&QEr1%211%53941&aN&]8&b4%12=8&]G%118%5231%72A1%?3A91pQPJA1pkNC1").
Proof.
intros a n. apply bv_eq. unfold nat_to_word.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. apply bv_wrap_add_idemp_r.
Qed.
#[using="Type"] Lemma w_add_1 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'aOyR0%211'I&b0r1(aM+1(F%33821%63951&aN&]8&b4%12=9%3218%52?1%>3?71pkN@1").
Proof.
intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
change (bv_unsigned (1 : word)) with 1%Z. reflexivity.
Qed.
#[using="Type"] Lemma u_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "G'Q9'H&]<zr1%3221&]A&]I+2+R0%3221%5271%;271'I&b4yR0&aNr2%2231%5241%73D13p091pQV2F1").
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z. lia.
Qed.
#[using="Type"] Lemma elenZ_elen : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "D'U0'<'Q0r1u8%3221'I'Q9&[;r3&TMr2%211%5241&]G%114%:3931p0<1pQPJA1pRFC1").
Proof.
intros E n Hn. unfold elenZ, elen. cbn [edenot]. apply u_small. lia.
Qed.
#[using="Type"] Lemma rdn_skipn : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q@';'QF%211'aOyR0%211'>y8%511%311p051'<%<14'I%812&\Hr6r5r3r4%544321(3r2%22;1%;3:41'Q0%1249r8r7&b0&QE%11=%33L?1&O%12B@%D48731&Q7%13MCB%A2J1%J3I41p0>1p0A1po8O1pm4O1pkNQ71pQPJQ21pQP>Q41pQS:Q=1").
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
#[using="Type"] Lemma rdn_slice : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QD';'QF%211'aOyR0%211'>y8%511%311p051'<%<14'I%812&\Hr7r6r4r5%544321(3r3%22;1%;3:41'Q0&Nr2%2261%421<r9r8&b0&QE%11@%33OB1%E4651>&Q3&Q7%13OED%33Q0B1%D2M1%M3L61p0>1p0D1po8Q21pmDQ31pm4Q31pkNQ;1pQPJQ61pQP>Q81pQS:QA1").
Proof.
intros segs mem n a bs d k H Hdk.
eapply rdn_firstn; [eapply rdn_skipn; [exact H | lia] | lia].
Qed.
#[using="Type"] Lemma skipn_Z_to_le_bytes : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q3'<'Q9'Q0r2r3%3221'I';'aOy8%211%411&Q7&QCr4%221<%436<1&O%124>&]9&]I+2&]E+8&]G%11E%4231%7261%92I1%@2;1%H3C>1p0J1pQV2O1pmDQ11pQU<Q21").
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
#[using="Type"] Lemma firstn_Z_to_le_bytes : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "G'<'Q9'Q0r2r3%3221'I';'aOy8%211%411&Q3&QCr4%221<%436<1%42=>%<3721p0>1pQV2C1pQPJE1pQP<F1").
Proof.
induction m as [|m IH]; intros n z Hn.
- assert (n = 0)%nat by lia. subst. reflexivity.
- destruct n as [|n]; [reflexivity|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.
#[using="Type"] Lemma slice_word_bytes : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q?'<'aOyR0%211'Q0&Nr3r2%3221r4%6221'I'Q9&QD&Q3y8%?11&Q7&R3r5%221=%435<1%836@1%:11&]D&]9&b4%12ID&]I+2&]E+8&]G%11H%4231%7261%;291%51O%8271%;2:1%@241%N3MB1p0Q01pQU8Q81pQPJQ<1pmDQ=1pQU<Q>1").
Proof.
intros w d n v H. unfold word_to_le_bytes.
rewrite skipn_Z_to_le_bytes by lia. rewrite firstn_Z_to_le_bytes by lia.
apply bytes_le_Z_to_le. apply Z.div_pos; [apply u64_range | apply Z.pow_pos_nonneg; lia].
Qed.
#[using="Type"] Lemma length_firstn_skipn : forall {A} (l : list A) d n,
(d + n <= length l)%nat -> length (firstn n (skipn d l)) = n.
Proof. intros A l d n H. rewrite length_firstn, length_skipn. lia. Qed.
#[using="Type"] Lemma bytes_le_to_Z_bound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J';'aOy8%211%411'H&]<z&QDr1%211%5241&]A&]I+2&]E+8&]G&:%12@:%311%6251%9281%;2=1%C2=1pm4E1").
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
#[using="Type"] Lemma Z_to_bv_u_plus0 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'aOyR0%211'I&aN&]8&b4r1%2271z%5221%72:1%93:15pkN;1").
Proof. intro a. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
#[using="Type"] Lemma rdn_pointwise : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R3';'QF%211'aOyR0%211'>y8%511%311pQUL51'<%<14'I&:r1%2281r3%53721&]<&]8&b4%12B5&]Gr4%211%6241&]I+2+R0%3221%<251&Q1r6%22C1r8&aN%@2Q14r2%@11%D231%52Q51%711(3&Q5r5z%;2Q81%44Q8:31%62Q91%Q53Q981p0A1po6Q91%Q?1Q9&\Hr7%24E1;G%>2Q=Q1%Q=3521p071p0M1p0Q;1pm4QB1pkNQJ1pQPJQE1pQP>QG1pQS:R01").
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
#[using="Type"] Lemma rdn_img : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R?';'QF%211'aOyR0%211'>y8%511%311pQUL51'<'Q9%=11&]<&]8&b4r2%22>1&]Gr3%211%7241&]I+2+R0%3221%=251&Q1r1r5%3221'Ir7&aN%C2O5%A1C%F221%42Q21%611(0%11Q1%:3Q131p0<1po6Q11%Q71Q0&ULr4%Q02Q<1%33@1C(3%12Q6O%D3731'J%QF1Q>'H%QB12&\Hr9r8r6%44321L%<28Q1%O3721&Q4%QA1QJ%24QJQF1Q5%Q33QF1Q5%=251qm4?1%A2@1p0C1p0L1p0Q>1pQV4QM1pkNR61pQPJR11pQP>R31pQS:R<1").
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
#[using="Type"] Lemma zbytes_map : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "B';'aOy8%211%411'I'Q9&ZN&Q4&b4%118r1%449621%611&QD%114%;3:31pm4=1").
Proof. induction bs as [|b bs IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
#[using="Type"] Lemma bytes_le_to_Z_repeat0 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "@'<'I'Q9&QD&Q6'aOy8%211&aNz%2241r1%83521%:11%=3<15pQPJ?1").
Proof.
induction n as [|n IH]; cbn [repeat bytes_le_to_Z]; [reflexivity|].
rewrite IH. reflexivity.
Qed.
#[using="Type"] Lemma extz_0 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "<'6'<'I'Q9&[>r2r1z%43321%73612pQPJ91pQT@;1").
Proof.
intros sx n. unfold extz. destruct sx; [|reflexivity].
unfold bv_swrap, bv_wrap. rewrite Z.add_0_l.
rewrite Z.mod_small; [lia|].
unfold bv_half_modulus. split.
- apply Z.div_pos; [apply Z.lt_le_incl, bv_modulus_pos | lia].
- apply Z.div_lt_upper_bound; [lia|]. pose proof (bv_modulus_pos (8 * N.of_nat n)). lia.
Qed.
#[using="Type"] Lemma bv_extract0_lit : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'Q8'Q9'I'aOr2%211&b1yR0w&aNr1%2241%645481%4293%<3921'Gp021pQU2@1pQP<B1").
Proof. auto. Qed.
#[using="Type"] Lemma extract0_Z_to_bv64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "D'Q8'Q9&]7r2yR0%3221'I'aOr3%211&b1w&aN%129:%44:361%327<%:3721p0<1pQU2A1pQP<C1").
Proof.
intros m u Hm. apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned.
rewrite Z.shiftr_0_r. unfold bv_wrap.
unfold bv_modulus.
rewrite <- Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
- reflexivity.
- exists (2 ^ (Z.of_N 64 - Z.of_N m))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
#[using="Type"] Lemma zext64_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'Q8'Q9&]7r2yR0%3221'H&]<z%2216&]A&]I+2&]Fr3%211%5241%72>1%<291'I'aO%11A&ROr4&aN%122;%433F1%32G=%93721p0;1p0I1pQU2N1pQP<Q01").
Proof.
intros m u Hm Hu. rewrite zext64_lit. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus. lia.
Qed.
#[using="Type"] Lemma sext64_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q3'Q8'Q9&]7r2yR0%3221'H&]<z%2216&]A&]I+2&]Fr3%211%5241%72>1%<291'I'aO%11A&RNr4&aN%122;%433F1&b3%125>%52I1%;3941p0=1p0K1pQU2Q01pQP<Q21").
Proof.
intros m u Hm Hu. rewrite sext64_lit. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned.
rewrite bv_wrap_small; [reflexivity | unfold bv_modulus; lia].
Qed.
#[using="Type"] Lemma load_result_val : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q4'RK'6';'aOy8%211%411'I'<&:r1%2261&X7r3%211%83741yR0%>11&\Or4r2%33281&aN&[>&\N%126<%>17&QD%118%63431%82>1%H3>:1p0A1pm4K1pQT@Q11pQTDQ31").
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
#[using="Type"] Lemma scs_denot_cons : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q3';'QF%211'aOyR0%211'>y8%511%311p051'U0'Y=%=11&K&[Er5r4r3(7r2r1%33:21%847651'H&[D%14:986%<4;:96%4221%?261poJA1pQS0C1pRFE1plJG1pQS:Q01").
Proof.
intros. unfold scs_denot. split.
- intros H. inversion H; auto.
- intros [A B]. constructor; auto.
Qed.
#[using="Type"] Lemma scs_denot_app : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2';'QF%211'aOyR0%211'>y8%511%311p051'U0'Y=%=11&K&[Er5r4r3&5r2r1%33:21%847651'H%:49875%;4:985%3221%>251pQP0@1poNA1pRFD1plJF1pQS:O1").
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
+ match goal with |- match (match ?lb with _ => _ end) with _ => _ end => destruct lb; [exists []; reflexivity | exact I] end.
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
#[using="Type"] Lemma lit_strip_val : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'U0'U9'Q9'I'A%1243&W:r3%211(@r2r1%34;:21%:3851&b4yR0&TLr5r4%3221%6251&]D&]8%726@%:291%321?&]I+2+R0%3221%9251%L3M;1p0C1pm8O1pQU8Q11pmJQ21pRFQ41").
Proof.
intros E e v c H.
assert (D : (v = e /\ c = 0%Z) \/ e = EAlu ALU_ADD v (ELit c)).
{ destruct e as [z|n|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; cbn [lit_strip] in H;
try (injection H as <- <-; left; split; reflexivity).
destruct op; try (injection H as <- <-; left; split; reflexivity).
destruct b as [z|n'|op' a' b'|op' a' b'|op' a' b'|op' a' b'|sx lo n' a'|sx k i n'];
try (injection H as <- <-; left; split; reflexivity).
injection H as <- <-. right. reflexivity. }
destruct D as [[-> ->]| ->].
- rewrite Z.add_0_r. symmetry. apply Z.mod_small. pose proof (u64_range (edenot E e)). lia.
- cbn [edenot]. rewrite alu_add. unfold v_add. rewrite !u_lit64a.
rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
#[using="Type"] Lemma shifted_bound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QK'Q9'H&]<zr5%3221&]A&]I+2+R0%3221%5271%;271r3&]D&]8r6r4%3221%5219%B271r2%D231%F231%F2E7%G2E8r7&]Jr9r8%3221%@251%N2M1r:%7216%D291%N21Jr;%;215%H2;1r<%J214%L21Q0%Q9241%M2?6%Q;231%Q=231p0;1p0@1p0Q61p0I1p0K1p0M1p0Q91pnBQF1pQP4QG1pm:QH1pm8QI1pQULQJ1").
Proof.
intros x c c' lo hi Hx H L0 LH H64 D0 D64.
assert (E2 : ((x + c) mod 2 ^ 64 = (x + c') mod 2 ^ 64 + (c - c'))%Z).
{ replace (x + c)%Z with ((x + c') + (c - c'))%Z by lia.
rewrite <- (Zplus_mod_idemp_l (x + c')).
apply Z.mod_small. lia. }
lia.
Qed.
#[using="Type"] Lemma find_range_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&[@r7r6r5r4%544321'I'A%1299%B11&UH%1287(3(@r3r2%34AA21%5291%<3971'H&]<&b4&TLr8%221E%42Q41%62F1%722=%9221p0;1p0I1pnBQ01pQP4Q11pmJQ31poFQ51pV@Q81pRFQA1pQS:QC1").
Proof.
intros segs E M kn e lo hi Hkn. induction kn as [|K rest IH]; cbn [find_range]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | | |e' lo' hi'| | | |]; try (apply IH; assumption).
destruct (expr_eqb e e') eqn:Heq.
- injection H as <- <-. apply expr_eqb_eq in Heq. subst e'. exact HK.
- assert (SH : forall v c v' c', lit_strip e = (v, c) -> lit_strip e' = (v', c') ->
(if expr_eqb v v' then
let d := (c - c')%Z in
if (Z.leb 0 lo' && Z.leb lo' hi' && Z.ltb hi' (2 ^ 64) && Z.leb 0 (lo' + d) && Z.ltb (hi' + d) (2 ^ 64))%bool
then Some ((lo' + d)%Z, (hi' + d)%Z) else find_range rest e
else find_range rest e) = Some (lo, hi) ->
(lo <= bv_unsigned (edenot E e))%Z /\ (bv_unsigned (edenot E e) <= hi)%Z).
{ intros v c v' c' Hs Hs' H0.
destruct (expr_eqb v v') eqn:Hv; [|apply IH; assumption]. cbv zeta in H0.
match type of H0 with context [if ?b then Some _ else _] => destruct b eqn:Hb end; [|apply IH; assumption].
injection H0 as <- <-. apply expr_eqb_eq in Hv. subst v'.
pose proof (lit_strip_val E e v c Hs) as V1. pose proof (lit_strip_val E e' v c' Hs') as V2.
cbn [kentry_ok] in HK. destruct HK as [HK1 HK2].
apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3].
apply andb_prop in Hb as [B1 B2].
apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.ltb_lt in B3. apply Z.leb_le in B4. apply Z.ltb_lt in B5.
rewrite V1. rewrite V2 in HK1, HK2.
apply (shifted_bound (bv_unsigned (edenot E v)) c c' lo' hi' (u64_range _)); try assumption. split; assumption. }
destruct (lit_strip e) as [v c] eqn:Hs. destruct (lit_strip e') as [v' c'] eqn:Hs'.
destruct e; first [apply IH; assumption | exact (SH v c v' c' eq_refl eq_refl H)].
Qed.
#[using="Type"] Lemma u_lit64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='Q9'I&b4yR0&aNr1%2231%5241&]D&Z=%2251%:3;41pQV2<1").
Proof. intros. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.
#[using="Type"] Lemma two64_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "8'I'Q9&Z=&]I+2+R0%3221%73651").
Proof. reflexivity. Qed.
#[using="Type"] Lemma u_add64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'aOyR0%211'I'Q9&b4&S1(R5r2r1%43321%62:1&]D&]8%92=6%:2>6%3221&]I+2+R0%3221%9251%C3B;1pQUNE1pQULF1").
Proof. intros. rewrite alu_add. unfold v_add. apply u_lit64. Qed.
#[using="Type"] Lemma u_sub64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'aOyR0%211'I'Q9&b4&S1(R;r2r1%43321%62:1&]D&]J%92=6%:2>6%3221&]I+2+R0%3221%9251%C3B;1pQUNE1pQULF1").
Proof. intros. rewrite alu_sub. unfold v_sub. apply u_lit64. Qed.
#[using="Type"] Lemma u_and64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'aOyR0%211'I'Q9&b4&S1(R6r2r1%43321%62:1&];%82<5%92=5%3221%=3<51pQUN?1pQUL@1").
Proof.
intros. rewrite alu_and. unfold v_and. rewrite u_lit64, two64_eq. apply Z.mod_small.
pose proof (u64_range x). pose proof (u64_range y). apply Z_land_range; lia.
Qed.
#[using="Type"] Lemma u_or64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'aOyR0%211'I'Q9&b4&S1(R7r2r1%43321%62:1&]@%82<5%92=5%3221%=3<51pQUN?1pQUL@1").
Proof.
intros. rewrite alu_or. unfold v_or. rewrite u_lit64, two64_eq. apply Z.mod_small.
pose proof (u64_range x). pose proof (u64_range y). apply Z_lor_range; lia.
Qed.
#[using="Type"] Lemma u_xor64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'aOyR0%211'I'Q9&b4&S1(R<r2r1%43321%62:1&]C%82<5%92=5%3221%=3<51pQUN?1pQUL@1").
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
#[using="Type"] Lemma lit_shamt_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q4'U0'U9'Q9'I'>%113&W9r2%211(3r1%2291%93741'H&]D&b4yR0&TLr4r3%3221%6251+R0%9221%E3F1A&]<z%221D&]A%12F7%A231%B271p0D1pQS0O1plBQ11pRFQ31").
Proof.
intros E b s H. destruct b; cbn [lit_shamt] in H; try discriminate. injection H as <-.
cbn [edenot]. rewrite u_lit64, two64_eq. split; [|apply Z.mod_pos_bound; lia].
apply Z.mod_mod_divide. exists (2 ^ 58)%Z. reflexivity.
Qed.
#[using="Type"] Lemma u_srl64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'aOyR0%211'I'Q9&b4&S1(R:r2r1%43321%62:1&]9%82<5&]I+2&]D%<2@8+R0%3221%6251%9281%C3B;1pQUNE1pQULF1").
Proof.
intros. rewrite alu_srl. unfold v_srl. rewrite u_lit64, two64_eq, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
pose proof (u64_range x). apply Z.mod_small.
assert (0 < 2 ^ (bv_unsigned y mod 64))%Z by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned x); [|lia].
apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
#[using="Type"] Lemma u_sll64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "K'aOyR0%211'I'Q9&b4&S1(R8r2r1%43321%62:1&]D&]E%92=6&]I+2%<2@8+R0%7221%5241%8271%7264%;221%E3D=1pQUNG1pQULH1").
Proof.
intros. rewrite alu_sll. unfold v_sll. rewrite u_lit64, two64_eq, Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
reflexivity.
Qed.
#[using="Type"] Lemma u_sra64_nonneg : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N'aOyR0%211&]A&b4r2%2251&]I+2+QO%3221%8251'I'Q9&S1(R9r3%3321<%>2A1&]9%@2C4&]D+R0%22A1%A2@1%6251%>3=81p0@1pQUNJ1pQULK1").
Proof.
intros x y Hx. rewrite alu_sra. unfold v_sra. rewrite bv_signed_small by exact Hx.
rewrite u_lit64, two64_eq, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
pose proof (u64_range x). apply Z.mod_small.
assert (0 < 2 ^ (bv_unsigned y mod 64))%Z by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned x); [|lia].
apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
#[using="Type"] Lemma swrap32_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "E'Q9'H&]<zr1%3221&]A&]I+2+O%3221%5271%;271'I&b3yQ0r2%3221%53B12p071pQTFD1").
Proof.
intros t Ht. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. lia.
Qed.
#[using="Type"] Lemma swrap32_shift : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'Q9'I&b3yQ0&]8r2&]Er1&]I+2+Q0%3221%6251%9281%<2;1%=2<:%?3@21po8A1pQTFB1").
Proof.
intros t k. unfold bv_swrap. f_equal. unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32)%Z.
replace (t + k * 2 ^ 32 + bv_half_modulus 32)%Z with (t + bv_half_modulus 32 + k * 2 ^ 32)%Z by lia.
apply Z.mod_add. lia.
Qed.
#[using="Type"] Lemma u_small_id : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "E'Q9'H&]<zr1%3221&]A&]I+2+R0%3221%5271%;271'I&]Dr2&Z=%3221%53B13p071pQTFD1").
Proof. intros. rewrite two64_eq. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma u_addw_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QC'aOyR0%211'Q9'H&]<zr1%3221&]A&]I+2+O%3221%5271%;271'J'I&]8&b4r5%22D1r4%42F1%6231r3&]E+Q0%B2A1%32F1%<251%>3L71qo8M1%A2N1&RNyQ0&S0(R5&S5%11C%21B%53421%837Q91/01Q9%I2Q;1%L3Q:1Dp0=1p0Q01pQTFQ=1pQUNQ?1pQULQ@1").
Proof.
intros x y t Ht [k Hk]. rewrite w_addw. unfold v_addw. rewrite u_lit64, Hk, swrap32_shift, swrap32_small by lia.
apply u_small_id. lia.
Qed.
#[using="Type"] Lemma u_subw_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q<'aOyR0%211'Q9'H&]<zr1%3221&]A&]I+2+O%3221%5271%;271'I&]J&b4r4%22C1r3%42E1%6231r2%93F21&RNyQ0&S0(R;&S5r5%211%31>%63521%938Q21/01Q2%C2Q41%F3Q31Ap0>1p0I1pQTFQ61pQUNQ81pQULQ91").
Proof.
intros x y t Ht Hk. rewrite w_subw. unfold v_subw. rewrite u_lit64, Hk, swrap32_small by lia.
apply u_small_id. lia.
Qed.
#[using="Type"] Lemma mod32_of_mod64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ";'Q9'I&]Dr1+R0%3221+Q0%5221%6252%83921pQV2:1").
Proof. intros. apply Z.mod_mod_divide. exists 2%Z. reflexivity. Qed.
#[using="Type"] Lemma u_sllw_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QA'aOyR0%211'Q9'I&]D&b4r2%2271+R0%5221r1%83921&]A&]Er4%:2?1&]I+2+Q0%?2=1%4231%8261+O%7261%<231&RNyQ0&S0(R8&S5r5%211%31B%63521%938Q21/01Q2%O2Q41%Q02Q57r3%Q321E%H2G1%L241%Q73Q861p0C1p0Q11pQS0Q;1pQUNQ=1pQULQ>1").
Proof.
intros x y s Hs Hb. rewrite w_sllw. unfold v_sllw. pose proof (u64_range x).
assert (Hs' : (bv_unsigned y mod 32 = s mod 32)%Z) by (rewrite <- Hs; symmetry; apply mod32_of_mod64).
rewrite Hs', Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
assert (0 <= bv_unsigned x * 2 ^ (s mod 32))%Z by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
rewrite u_lit64, swrap32_small by lia. apply u_small_id. lia.
Qed.
#[using="Type"] Lemma u_srlw_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF'aOyR0%211'Q9'I&]D&b4r2%2271+R0%5221r1%83921&]Ar4%92>1&]I+2+Q0%3221%7251&]9r5%A2F1r3%D217%:291%6241+O%=2<1%A231&RNyQ0&S0(R:&S5r6%211%31@%63521%938Q71/01Q7%Q42Q91%Q52Q:7%Q72NJ%M2L1%I231%Q;3Q<51p0B1p0M1p0Q61pQS0Q@1pQUNQB1pQULQC1").
Proof.
intros x y s Hs Hx Hb. rewrite w_srlw. unfold v_srlw. pose proof (u64_range x).
assert (Hs' : (bv_unsigned y mod 32 = s mod 32)%Z) by (rewrite <- Hs; symmetry; apply mod32_of_mod64).
rewrite Hs', Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
rewrite bv_wrap32_mod, (Z.mod_small (bv_unsigned x)) by lia.
assert (0 <= bv_unsigned x / 2 ^ (s mod 32))%Z by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]]).
rewrite u_lit64, swrap32_small by lia. apply u_small_id. lia.
Qed.
#[using="Type"] Lemma u_sraw_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q>'aOyR0%211'Q9'I&]D&b4r2%2271+R0%5221r1%83921&]Ar4%92>1&]I+2+O%3221%7251&RNyQ0&S0(R9&S5r5%211%31>%63521%938M1/01M%J2O1&]9%L2Q18r3+Q0%Q0221%F2E1%6251%Q43Q581p0E1p0N1pQS0Q81pQUNQ:1pQULQ;1").
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
#[using="Type"] Lemma u_mul64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'aOyR0%211'I'Q9&b4&S6(RAr2r1%449321%62:1&]D&]E%92=6%:2>6%3221&]I+2+R0%3221%9251%C3B;1pQUNE1pQULF1").
Proof. intros. rewrite m_mul. unfold v_mul. apply u_lit64. Qed.
#[using="Type"] Lemma u_mulhu64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'aOyR0%211'I'Q9&b4&S6(RBr2r1%449321%62:1&]9&]E%92=6%:2>6%3221&]I+2+R0%3221%9251%C3B;1pQUNE1pQULF1").
Proof.
intros. rewrite m_mulhu. unfold v_mulhu. rewrite u_lit64, Z.shiftr_div_pow2 by lia.
pose proof (u64_range x). pose proof (u64_range y). apply u_small_id.
split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
#[using="Type"] Lemma u_divu64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'aOyR0%211&]Az&b4r1%2261%5241'I'Q9&S6(R@r3r2%44>321%;2?1&]9%=2A5%>2B5%3221%<3;51p0>1pQUNE1pQULF1").
Proof.
intros x y Hy. unfold mul_div. replace (bv_unsigned y =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_divu_unsigned.
Qed.
#[using="Type"] Lemma u_remu64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'aOyR0%211&]Az&b4r1%2261%5241'I'Q9&S6(RCr3r2%44>321%;2?1&]D%=2A5%>2B5%3221%<3;51p0>1pQUNE1pQULF1").
Proof.
intros x y Hy. unfold mul_div. replace (bv_unsigned y =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_modu_unsigned.
Qed.
#[using="Type"] Lemma u_ext_zx : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q='<'aOyR0%211'H'I'Q9&b4&UA(8r3r2r1%544321%72<1&]D&]9%:2?5&]I+2&]E+8&]G%11=%4231%7261%:291%51@%8271%;2:1%?241%J3IA1&]<&]J+1%2261%42F1&Z=%5214%72I1%Q4241%Q52:1pQU8Q71pQPJQ;1pQP4Q<1").
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
#[using="Type"] Lemma u_ext_zx0_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "O'<'aOyR0%211&]A&b4r1%2251&]I+2&]E+8&]Gr2%211%5241%8271%=2:1'I'Q9&UA(8(1r3%44321;%D2G1%E2H=%93821p0;1pQU8J1pQPJN1").
Proof.
intros n v Hv. destruct (u_ext_zx 0 n v) as (H & _ & _). rewrite H.
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r. apply Z.mod_small. pose proof (u64_range v). lia.
Qed.
#[using="Type"] Lemma u_ext_sx0_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'<'aOyR0%211&]A&b4r1%2251&]9&]I+2&]E+8&]Gr2%211%5241%8271%:218%?2<1'I'Q9&UA(C(1r3%44321<%F2I1%G2J>%93821p0;1pQU8L1pQPJQ01").
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
#[using="Type"] Lemma u_ext_sx0_high : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF'<'aOyR0%211'H&]<&]9&]I+2&]E+8&]Gr2%211%5241%8271%:218&b4r1%22A1%?241&]A%1237%C231'Q0u1r3%3221u8%5231%J231'I'Q9&UA(C(1r4%44321;%E2Q41&]8&]J+R0%Q32Q21%Q017%Q32Q21%Q62Q51%6241%N2Q=E%9221%B3A;1p0D1p0L1pQU8QA1pQPJQE1").
Proof.
intros n v Hv Hn. unfold ext_val, ext_Z. pose proof (u64_range v).
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
assert (Hw : (0 < 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hw64 : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
rewrite (Z.mod_small (bv_unsigned v)) by lia.
cbv zeta. cbn [negb].
rewrite bv_swrap_hi.
- rewrite u_lit64. unfold two64, bv_modulus.
replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
- lia.
- unfold bv_half_modulus, bv_modulus. replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia. lia.
- unfold bv_modulus. replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia. lia.
Qed.
#[using="Type"] Lemma u_blob_zx : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5';'aOy8%211%411'Q9'<'H&]<&b4yR0&T8(8r3r2r1%544321%8271&]J&]I+2&]E+8&]G%119%4231%7261+1%:221%E2<1&Z=%=214%H2?1%J241pQPJL1po0N1pm4Q01").
Proof.
intros bs i n. unfold blob_val. pose proof (bytes_le_to_Z_bound (blob_bytes bs i n)) as Hb.
assert (Hlen : (length (blob_bytes bs i n) <= n)%nat) by (unfold blob_bytes; rewrite firstn_length; apply Nat.le_min_l).
assert (Hp : (2 ^ (8 * Z.of_nat (length (blob_bytes bs i n))) <= 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.pow_le_mono_r; lia).
rewrite u_lit64. pose proof (Z.mod_pos_bound (bytes_le_to_Z (blob_bytes bs i n)) two64 ltac:(rewrite two64_eq; lia)).
pose proof (Z.mod_le (bytes_le_to_Z (blob_bytes bs i n)) two64 ltac:(lia) ltac:(rewrite two64_eq; lia)). lia.
Qed.
#[using="Type"] Lemma clampi_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q4'aOyR0%211'Q9'H&]<r4&b4r5%2281%5241r3%7231%9231'I'A%12==&T<(@%14@@;=%311r2%44CC;1%93731r7%B2H1%E2D1%F22@%H221p061p0A1pnDL1pQP6M1pnBN1pQP4O1pQU8Q11").
Proof.
intros v lo hi lo' hi' H Hc. unfold clampi, two64m1 in Hc. injection Hc as <- <-. pose proof (u64_range v). rewrite two64_eq. lia.
Qed.
#[using="Type"] Lemma mod_wrap_hi : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "G'Q9'H&]<&]I+2+R0%3221r1%6221&]A&]8%1255%3251%<251'I&]Dr2%221;&]J%123=%63D31p081pQTFF1").
Proof. intros t Ht. symmetry. apply (Z.mod_unique_pos t (2 ^ 64) 1); lia. Qed.
#[using="Type"] Lemma mod_wrap_neg : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'Q9'H&]<&]H&]I+2+R0%3221%511r1%8221&]Az%2241%=241'I&]Dr2%221;&]8%123=%63E31p081pQTFG1").
Proof. intros t Ht. symmetry. apply (Z.mod_unique_pos t (2 ^ 64) (-1)); lia. Qed.
#[using="Type"] Lemma mask_cover_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "@'Q9'H&]<zr1%3221r2%5231%7231&WFr3%211%:261p051pQUL>1pn>?1").
Proof.
intros h x Hx. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eq_dec h 0) as [->|Hne].
- replace (2 ^ Z.log2_up (0 + 1) - 1)%Z with 0%Z by reflexivity. lia.
- pose proof (Z.log2_up_spec (h + 1) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma pow_cover : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "D'Q9&]<zr1%3221'H&]8r2+1%3221&]I+2&]?%114%4231%>261%?2>3%<221p0>1pn>C1").
Proof.
intros h Hh. split; [|apply Z.log2_up_nonneg].
destruct (Z.eq_dec h 0) as [->|Hne].
- replace (2 ^ Z.log2_up (0 + 1))%Z with 1%Z by reflexivity. lia.
- pose proof (Z.log2_up_spec (h + 1) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma lor_cover : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "G'Q9'H&]<zr2%3221r3%5231%7231r4%8261%:261&]@%1247&WFr5%211%?241p071p0;1pQUND1pQULE1pn>F1").
Proof.
intros h x y Hx Hy. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (pow_cover h ltac:(lia)) as [Hh Hk]. set (k := Z.log2_up (h + 1)) in *.
enough (Z.lor x y < 2 ^ k)%Z by lia.
apply (Z_bounded_by_bits k); [lia | apply Z.lor_nonneg; lia |].
intros i Hi. rewrite Z.lor_spec.
rewrite (Z_testbit_high k x i) by lia. rewrite (Z_testbit_high k y i) by lia. reflexivity.
Qed.
#[using="Type"] Lemma lxor_cover : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'Q9'H&]<zr2%3221r3%5231%7231r4%8261%:261&]C%1247%<2;1&WFr5%211%@251%B251p091p0=1pQUNF1pQULG1pn>H1").
Proof.
intros h x y Hx Hy. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (pow_cover h ltac:(lia)) as [Hh Hk]. set (k := Z.log2_up (h + 1)) in *.
assert (Hnn : (0 <= Z.lxor x y)%Z) by (apply Z.lxor_nonneg; lia).
enough (Z.lxor x y < 2 ^ k)%Z by lia.
apply (Z_bounded_by_bits k); [lia | exact Hnn |].
intros i Hi. rewrite Z.lxor_spec.
rewrite (Z_testbit_high k x i) by lia. rewrite (Z_testbit_high k y i) by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_le_l : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'Q9&]<zr2%3221&];r4r3%3221%8213p061p071plB<1pkN=1").
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
#[using="Type"] Lemma land_le_r : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'Q9&]<zr2%3221&];r4r3%3221%8212p061p071plB<1pkN=1").
Proof. intros. rewrite Z.land_comm. apply land_le_l; assumption. Qed.
#[using="Type"] Lemma lor_ge_l : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'Q9&]<zr2%3221r4&]@r3%2231%8241p061p071pQUN<1pQUL=1").
Proof. intros. pose proof (Z.add_lor_land x y). pose proof (land_le_r x y H H0). lia. Qed.
#[using="Type"] Lemma lor_ge_r : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'Q9&]<zr2%3221r3&]@r4%2213%8241p061p071pQUN<1pQUL=1").
Proof. intros. rewrite Z.lor_comm. apply lor_ge_l; assumption. Qed.
End FPX_1.
Ltac fr_case Hkn H :=
lazymatch type of H with
| match find_range ?kn ?e with _ => _ end = _ =>
destruct (find_range kn e) as [[flo fhi]|] eqn:Hfr;
[ pose proof (find_range_sound _ _ _ _ _ _ _ Hkn Hfr) as Hb; unfold clampi, two64m1 in H;
injection H as <- <-; lazymatch goal with |- context [bv_unsigned ?v] => pose proof (u64_range v) end; unfold two64 in *; lia
| clear Hfr ]
end.
Ltac er_both IHe1 IHe2 Hkn H :=
destruct (erange _ _) as [[al ah]|] eqn:He1 in H; [|try discriminate];
destruct (erange _ _) as [[bl bh]|] eqn:He2 in H; [|try discriminate];
try (specialize (IHe1 al ah Hkn eq_refl)); try (specialize (IHe2 bl bh Hkn eq_refl)).
Section FPX_2. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma lin_range_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QI'U0'U9'>'A'Q9%2211%411pQUL61'Ir4r3%211(3(@r2r1%34<<21%52<1%:3<71'H&]<&b4yR0&TLr6%221@%5241%72A1%822>%:221p0<1pnBK1pQP4L1pkNQ01';%Q02OQ2%211&W3%13>ML%O3Q11F&]8r5&\Br8%221Q3%5241%J2Q41%K22Q1%M221p0:1pnBQ>1pQP4Q?1pQTJ@1pm8QA1p0E1pQRDQ@1pRFQH1").
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
#[using="Type"] Lemma testbit_mask : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2'Q9&]<zr2%3221&]Ar3+R0%3221%8273'I'6&]K&]J&]I+2%2219r5%4231%6231r4%9221&4&]=%1274&]B%126C%5231%B3A71p0D1p0F1p0K1po0Q01po6Q11").
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
#[using="Type"] Lemma land_align_mask : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q4'Q9&]<zr1%3221&]Ar2+R0%3221'Hr4%:291&]I+2%2217%:251%7251'I&]Dr5%827:%3221%53F1D&];r6&]J%>2=7%22=1%5241%<3M15p081p0?1p0H1p0M1po6Q21pQULQ31").
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
#[using="Type"] Lemma testbit_drop_low : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'Q9&]<zr2%3221'Hr4%6251&]A&]I+2r3%3221%5271%9271%>294'I'6&]K&]8&]Er7r5%>2=1%4231r6%7221%921E%:24F%=3<21p0?1p0A1p0L1po0Q11po6Q21pQQJQ31pQQHQ41").
Proof.
intros q r j i Hj Hr Hi.
replace i with ((i - j) + j) by lia.
rewrite <- !Z.div_pow2_bits by lia.
f_equal. rewrite Z.div_add_l by lia. rewrite (Z.div_small r) by lia.
rewrite Z_div_mult by lia. lia.
Qed.
#[using="Type"] Lemma land_highmask : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q0'Q9'H&]<zr1%3221&]A+R0%2241%8241r3%9281&]I+2%2217%9251%?251'I&];r4&]J%928;%2281%5241&]D%1264%6271%:3K41p0<1p0D1po6N1pQULO1").
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
#[using="Type"] Lemma erange_f_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QI';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'<'U9'Q9&\<r8r7r6r5%544321'I'A%1299%C11&U3r4%23891(3(@r3r2%34BB21%52:1%=3:71'H&]<&b4&TLr9%221E%42Q61%62@1%722=%9221p0;1p0J1pQR8Q11pQR@Q21pmJQ41pn:Q61poFQ81pV@Q;1pRFQD1pQS:QF1").
Proof.
intros segs E M kn fuel. induction fuel as [|fuel IH]; intros e rlo rhi Hkn H; [discriminate|].
cbn [erange_f] in H. fr_case Hkn H.
lazymatch type of H with
| match ?X with _ => _ end = _ =>
destruct X as [[llo lhi]|] eqn:Hlin;
[ injection H as <- <-;
destruct (lin_trivial (lin_of e)) eqn:Htriv; [discriminate|];
destruct (lin_range (erange_f fuel kn) (fst (lin_of e)) (snd (lin_of e))) as [[lo1 hi1]|] eqn:Hlr; [|discriminate];
rewrite ?zdiv64_eq2 in Hlin;
destruct (Z.eqb (lo1 / two64) (hi1 / two64)) eqn:Hc; [|discriminate];
injection Hlin as <- <-; apply Z.eqb_eq in Hc;
pose proof (lin_range_sound E (erange_f fuel kn) (fun a lo hi Ha => IH a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb;
pose proof (lin_of_sound E e) as [q Hq]; unfold lden in Hq;
destruct (lin_of e) as [c ts]; cbn [fst snd] in *; unfold uE in Hq;
pose proof (u64_range (edenot E e)) as Hu; unfold two64 in *;
set (v := bv_unsigned (edenot E e)) in *;
set (p1 := (lo1 / 2 ^ 64)%Z) in *;
pose proof (Z.div_mod lo1 (2 ^ 64) ltac:(lia)) as D1;
pose proof (Z.div_mod hi1 (2 ^ 64) ltac:(lia)) as D2;
pose proof (Z.mod_pos_bound lo1 (2 ^ 64) ltac:(lia)) as B1;
pose proof (Z.mod_pos_bound hi1 (2 ^ 64) ltac:(lia)) as B2;
rewrite <- Hc in D2;
assert (q = p1) by nia; subst q; nia
| clear Hlin ]
end.
pose proof (fun a => IH a) as IHe1. pose proof (fun a => IH a) as IHe2. pose proof (fun a => IH a) as IHe.
destruct e; cbn [edenot]; unfold two64 in *.
- injection H as <- <-. rewrite ?zmod64_eq, u_lit64. unfold two64. lia.
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
lazymatch type of H with (match ?pre with Some r => Some r | None => _ end = _) =>
destruct pre as [r18|] eqn:H18 end.
{ injection H as E18. subst r18.
destruct e2 as [m| | | | | | |]; try discriminate.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
unfold two64 in H18.
set (m' := (m mod 2 ^ 64)%Z) in H18. set (j := Z.log2 (m' + 1)) in H18.
lazymatch type of H18 with ((if ?c then _ else _) = _) => destruct c eqn:Hc end.
2: {
set (jh := Z.log2 (2 ^ 64 - m')) in H18.
lazymatch type of H18 with ((if ?c then _ else _) = _) => destruct c eqn:Hch; [|discriminate] end.
injection H18 as <- <-. apply andb_prop in Hch as [Hpow Hj64]. apply Z.eqb_eq in Hpow. apply Z.ltb_lt in Hj64.
assert (Hj0 : (0 <= jh)%Z) by (subst jh; apply Z.log2_nonneg).
assert (Hp : (0 < 2 ^ jh)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hm' : (0 <= m' < 2 ^ 64)%Z) by (subst m'; apply Z.mod_pos_bound; lia).
cbn [edenot] in *. rewrite u_lit64 in *. unfold two64 in *. fold m' in Hl2 |- *.
set (x := bv_unsigned (edenot E e1)) in *.
replace m' with (2 ^ 64 - 2 ^ jh)%Z by lia. rewrite land_highmask by lia.
pose proof (Z.div_mod x (2 ^ jh) ltac:(lia)) as Dx.
pose proof (Z.div_mod al (2 ^ jh) ltac:(lia)) as Da.
pose proof (Z.div_mod ah (2 ^ jh) ltac:(lia)) as Dh.
pose proof (Z.mod_pos_bound x (2 ^ jh) Hp). pose proof (Z.mod_pos_bound al (2 ^ jh) Hp). pose proof (Z.mod_pos_bound ah (2 ^ jh) Hp).
assert (Hqa : (al / 2 ^ jh <= x / 2 ^ jh)%Z) by (apply Z.div_le_mono; lia).
assert (Hqh : (x / 2 ^ jh <= ah / 2 ^ jh)%Z) by (apply Z.div_le_mono; lia).
set (xq := (x / 2 ^ jh)%Z) in *; set (aq := (al / 2 ^ jh)%Z) in *; set (hq := (ah / 2 ^ jh)%Z) in *.
set (P := (2 ^ jh)%Z) in *. clearbody xq aq hq P. clearbody x. clear - Dx Da Dh Hqa Hqh Hp H H0 H1.
replace (al - al mod P)%Z with (P * aq)%Z by lia. replace (x - x mod P)%Z with (P * xq)%Z by lia. replace (ah - ah mod P)%Z with (P * hq)%Z by lia.
split; apply Z.mul_le_mono_nonneg_l; lia. }
injection H18 as <- <-. apply andb_prop in Hc as [Hc Hq]. apply andb_prop in Hc as [Hpow _].
apply Z.eqb_eq in Hpow. apply Z.eqb_eq in Hq.
assert (Hj0 : (0 <= j)%Z) by (subst j; apply Z.log2_nonneg).
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hm' : (0 <= m' < 2 ^ 64)%Z) by (subst m'; apply Z.mod_pos_bound; lia).
cbn [edenot] in *. rewrite u_lit64 in *. unfold two64 in *. fold m' in Hl2 |- *.
set (x := bv_unsigned (edenot E e1)) in *.
assert (Hx : Z.land x m' = (x mod 2 ^ j)%Z).
{ replace m' with (Z.pred (2 ^ j)) by lia. rewrite <- Z.ones_equiv. apply Z.land_ones. lia. }
rewrite Hx.
pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Dx.
pose proof (Z.div_mod al (2 ^ j) ltac:(lia)) as Da.
pose proof (Z.div_mod ah (2 ^ j) ltac:(lia)) as Dh.
pose proof (Z.mod_pos_bound x (2 ^ j) Hp). pose proof (Z.mod_pos_bound al (2 ^ j) Hp). pose proof (Z.mod_pos_bound ah (2 ^ j) Hp).
assert (Hqa : (al / 2 ^ j <= x / 2 ^ j)%Z) by (apply Z.div_le_mono; lia).
assert (Hqh : (x / 2 ^ j <= ah / 2 ^ j)%Z) by (apply Z.div_le_mono; lia).
set (xq := (x / 2 ^ j)%Z) in *; set (aq := (al / 2 ^ j)%Z) in *; set (hq := (ah / 2 ^ j)%Z) in *.
set (xm := (x mod 2 ^ j)%Z) in *; set (am' := (al mod 2 ^ j)%Z) in *; set (hm := (ah mod 2 ^ j)%Z) in *.
clearbody xq aq hq xm am' hm.
assert (Ex : xq = aq) by (clear - Hqa Hqh Hq; lia).
subst xq. rewrite <- Hq in Dh.
set (PQ := (2 ^ j * aq)%Z) in *. clearbody PQ.
clearbody x. clear - Dx Da Dh IHe1. lia. }
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
revert H. unfold zsigned64, two63z, two64.
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
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
* injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
rewrite u_ext_sx0_small by lia. lia.
* match type of H with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
injection H as <- <-. apply andb_prop in C2 as [C2 Cd]. apply andb_prop in C2 as [C2 Cc].
apply andb_prop in C2 as [Cn1 Cn8]. apply Nat.leb_le in Cn1. apply Nat.leb_le in Cn8.
apply Z.leb_le in Cc. apply Z.ltb_lt in Cd.
rewrite u_ext_sx0_high by lia. unfold two64. lia.
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
destruct sx.
+ injection H as <- <-. unfold two64m1, two64. cbn [edenot]. pose proof (u64_range (blob_val true (eb E k) i n)). lia.
+ injection H as <- <-.
destruct (u_blob_zx (eb E k) i n) as [Hb1 Hb2]. unfold two64 in Hb2.
pose proof (u64_range (blob_val false (eb E k) i n)). lia.
Qed.
#[using="Type"] Lemma facts_of_ok : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "M';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11&\<r4r3r2r1%544321r5&UC%115%943871p051poF<1pV@?1pRFH1pQS:J1").
Proof. intros segs E M kn H. rewrite facts_of_filter. apply Forall_forall. intros K HK.
apply filter_In in HK as [HK _]. exact (proj1 (Forall_forall _ _) H K HK). Qed.
#[using="Type"] Lemma erange0_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'I'A%1299%B11&U2%1287(3(@r3r2%34AA21%5291%<3971'H&]<&b4&TLr8%221E%42Q41%62F1%722=%9221p0;1p0I1pQR8Q01pQR@Q11pmJQ31poFQ51pV@Q81pRFQA1pQS:QC1").
Proof. intros. eapply erange_f_sound; [eapply facts_of_ok|]; eassumption. Qed.
#[using="Type"] Lemma deand_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q='U0'U9'Q9'I'A%1243&TFr3%211(@r2r1%34;:21%:3851'H&]<z%2217'J%4238%529=%7221&\7&b4yR0&TLr6r5%3221%6251&]Jr4%7261%:291%421G%=261%F2?1qQR:Q31%D2Q41%I2F1p0K1pQS0Q71pmLQ91pmJQ:1pRFQ<1").
Proof.
intros E e. induction e; intros e' s H; cbn [deand] in H;
try (injection H as <- <-; split; [lia|]; exists 0%Z; split; [lia|]; exists 0%Z; lia).
destruct op; try (injection H as <- <-; split; [lia|]; exists 0%Z; split; [lia|]; exists 0%Z; lia).
-
destruct (deand e1) as [a' s1] eqn:H1. destruct (deand e2) as [b' s2] eqn:H2. injection H as <- <-.
destruct (IHe1 a' s1 eq_refl) as (Hs1 & r1 & Hr1 & [q1 Hq1]). destruct (IHe2 b' s2 eq_refl) as (Hs2 & r2 & Hr2 & [q2 Hq2]).
split; [lia|]. exists (r1 + r2)%Z. split; [lia|].
cbn [edenot]. pose proof (u_add_eqm (edenot E e1) (edenot E e2)) as [q3 Hq3].
pose proof (u_add_eqm (edenot E a') (edenot E b')) as [q4 Hq4].
exists (q3 + q1 + q2 - q4)%Z. lia.
-
destruct e2 as [m| | | | | | |]; try (injection H as <- <-; split; [lia|]; exists 0%Z; split; [lia|]; exists 0%Z; lia).
set (m' := (m mod two64)%Z) in H. set (j := Z.log2 (two64 - m')) in H.
destruct (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool eqn:Hc;
[|injection H as <- <-; split; [lia|]; exists 0%Z; split; [lia|]; exists 0%Z; lia].
apply andb_prop in Hc as [Hpow Hj]. apply Z.eqb_eq in Hpow. apply Z.leb_le in Hj.
destruct (deand e1) as [x' s1] eqn:H1. injection H as <- <-.
destruct (IHe1 x' s1 eq_refl) as (Hs1 & r1 & Hr1 & [q1 Hq1]).
assert (Hj0 : (0 <= j)%Z) by (subst j; apply Z.log2_nonneg).
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
split; [lia|].
assert (Hm' : (0 <= m' < 2 ^ 64)%Z) by (subst m'; unfold two64; apply Z.mod_pos_bound; lia).
cbn [edenot]. rewrite u_and64, u_lit64. fold two64. fold m'. unfold two64 in Hpow.
replace m' with (2 ^ 64 - 2 ^ j)%Z by lia.
pose proof (u64_range (edenot E e1)) as Hx. set (x := bv_unsigned (edenot E e1)) in *.
rewrite land_highmask by lia.
pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hmod.
exists (r1 + x mod 2 ^ j)%Z. split; [lia|]. exists q1. lia.
Qed.
#[using="Type"] Lemma erange_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'I'A%1299%B11&U1%1287(3(@r3r2%34AA21%5291%<3971'H&]<&b4&TLr8%221E%42Q41%62F1%722=%9221p0;1p0I1pQR8Q01pQR@Q11pmJQ31poFQ51pV@Q81pRFQA1pQS:QC1").
Proof.
intros segs E M kn e rlo rhi Hkn H. unfold erange in H.
pose proof (fun lo hi (He : erange0 kn e = Some (lo, hi)) => erange0_sound segs E M kn e lo hi Hkn He) as H0.
destruct (deand e) as [e' s] eqn:Hd.
destruct (Z.eqb s 0); [exact (H0 _ _ H)|].
destruct (erange0 kn (unlin (lin_of e'))) as [[lo' hi']|] eqn:He'; [|exact (H0 _ _ H)].
destruct (Z.leb s lo') eqn:Hs; [|exact (H0 _ _ H)]. apply Z.leb_le in Hs.
pose proof (erange0_sound segs E M kn _ lo' hi' Hkn He') as Hb'.
assert (Hn : edenot E (unlin (lin_of e')) = edenot E e').
{ rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (edenot E e')).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound | apply lin_of_sound]. }
rewrite Hn in Hb'.
destruct (deand_sound E e e' s Hd) as (Hs0 & rho & Hrho & [q Hq]).
pose proof (u64_range (edenot E e)) as Hu. pose proof (u64_range (edenot E e')) as Hu'.
assert (q = 0%Z) by nia. subst q.
destruct (erange0 kn e) as [[lo hi]|] eqn:He.
- pose proof (H0 lo hi eq_refl) as Hb. injection H as <- <-. lia.
- injection H as <- <-. lia.
Qed.
#[using="Type"] Lemma base_range_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'I'A%1299%B11&T7%1287(3(@r3r2%34AA21%5291%<3971'H&]<&b4&TLr8%221E%42Q41%62F1%722=%9221p0;1p0I1pnBQ01pQP4Q11pmJQ31poFQ51pV@Q81pRFQA1pQS:QC1").
Proof.
intros segs E M kn e lo hi Hkn H. unfold base_range in H.
destruct e; try exact (erange_sound segs E M kn _ lo hi Hkn H).
injection H as <- <-. cbn [edenot]. rewrite u_lit64. unfold two64. lia.
Qed.
#[using="Type"] Lemma zlit64_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'Q9'I&[5r1%211&]D&Z=%2241%73841pQV291").
Proof.
intros z. unfold zlit64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:H; [|reflexivity].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. symmetry. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma lin_nowrap_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r5r4r3r2%544321'I'6&W0%1265(C%53421'Q9&b4&TLr6%221=%42K1&]8&9'A%129F%Q511&W2%11E%63=31&\B&B%13@64%32>1%<251%I3C>1p0E1p0L1pmJQ31poFQ51pV@Q81pRFQA1pQS:QC1").
Proof.
intros segs E M kn e Hkn H. unfold lin_nowrap in H.
destruct (lin_range (erange kn) (fst (lin_of e)) (snd (lin_of e))) as [[lo hi]|] eqn:Hlr; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
pose proof (u64_range (edenot E e)). nia.
Qed.
#[using="Type"] Lemma lins_e_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "L'U0'Q9'U9';'A%1243%311'I&\Br4&W8r3r2r1%43321%7261&]8&]E&\C%12:7%3291%=2<8%6221%@3F81pQTJB1pkNG1po8I1pRFK1").
Proof.
intros E k a ts. induction ts as [|[k' a'] rest IH]; cbn [lins_e tden].
- destruct (Z.eqb k 0) eqn:Hz; cbn [tden]; [apply Z.eqb_eq in Hz; subst; lia | lia].
- destruct (expr_eqb a a') eqn:Heq.
+ apply expr_eqb_eq in Heq. subst a'. destruct (Z.eqb (k + k') 0) eqn:Hz; cbn [tden]; [apply Z.eqb_eq in Hz; nia | nia].
+ cbn [tden]. rewrite IH. lia.
Qed.
#[using="Type"] Lemma lsub_e_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "G'U0';'A'Q9'U9%3221%511'I&\Br3&WCr2r1%3221%6251&]J%8275%9285%3221%<3@51pQTN>1pQU0?1pRFF1").
Proof.
intros E ts2 ts1. unfold lsub_e. induction ts1 as [|[k a] rest IH]; cbn [fold_right tden]; [lia|].
rewrite lins_e_sound. cbn [fst snd]. rewrite IH. lia.
Qed.
#[using="Type"] Lemma find_align_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QC';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r6r5r4r3%544321'I%@18&UE%1265(3r2%22=1%73641'H&]Az%221=&]D&b4&TLr7%221C%42Q21%621D%C3J19%<291p0>1p0G1pQP<N1pkNQ01poFQ21plJQ51pRFQ>1pQS:Q@1").
Proof.
intros segs E base kn a m Hkn. induction kn as [|K rest IH]; cbn [find_align]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | |e' m'| | | | |]; try (apply IH; assumption).
destruct (expr_eqb a e') eqn:Heq.
- injection H as <-. apply expr_eqb_eq in Heq. subst e'. exact HK.
- apply IH; assumption.
Qed.
#[using="Type"] Lemma ctz_fuel_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "F'<'Q9'H&]<z&TEr2r1%3221%6251&]:&]I+2%2215%4217&]G%11:%>291%@241%A2:1pQV2C1pn0E1").
Proof.
induction f as [|f IH]; intros z; cbn [ctz_fuel].
- split; [lia|]. split; [exists z; lia | lia].
- destruct (z mod 2 =? 0)%Z eqn:E.
+ destruct (IH (z / 2)%Z) as (A & [q Hq] & C). split; [lia|]. split; [|lia].
exists q. rewrite Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z.
apply Z.eqb_eq in E. pose proof (Z.div_mod z 2 ltac:(lia)). lia.
+ split; [lia|]. split; [exists z; rewrite Z.pow_0_r; lia | lia].
Qed.
#[using="Type"] Lemma ctz64_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "B'Q9'H&]<z&TDr1%211%5241+R0%7231%9231&]:&]I+2%2218%421:%?261pQV2A1").
Proof. intros z. unfold ctz64. destruct (ctz_fuel_sound 64 z) as (A & B & C). cbn [Z.of_nat] in C. split; [lia | exact B]. Qed.
#[using="Type"] Lemma pow2_divide_le : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'Q9'H&]<zr2%3221r1%5231%7231&]:&]I+2r3%3221%423:%6221p081plBA1pkNB1").
Proof. intros a b H. exists (2 ^ (b - a))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
#[using="Type"] Lemma divide_mod64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'Q9'H&]<zr2%3221+R0%5231%7231&]:&]I+2r3%3221%521:r4%6251&]D%827<%2271%;241p071p0>1pQTFG1po8H1").
Proof.
intros k t Hk Hd. rewrite Z.mod_eq by lia.
apply Z.divide_sub_r; [exact Hd|]. apply Z.divide_mul_l. apply pow2_divide_le. lia.
Qed.
#[using="Type"] Lemma ealign0_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q>';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r5r4r3r2%544321'H&]<z&TK%1276%4231+R0%6231%8231&]:&]I+2%2218&b4&TL%12DA%32Q01%8251%B2:1p0D1pmJK1poFM1pV@Q01pRFQ91pQS:Q;1").
Proof.
intros segs E M kn e Hkn. induction e; cbn [ealign0];
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
eapply Z.divide_trans; [apply (pow2_divide_le _ (ealign0 kn e1 + s)); lia|].
rewrite Z.pow_add_r by lia. apply Z.mul_divide_mono_r. exact B1.
+ split; [lia|]. rewrite u_or64.
set (k := Z.min (ealign0 kn e1) (ealign0 kn e2)).
assert (D1 : (2 ^ k | bv_unsigned (edenot E e1))%Z) by (eapply Z.divide_trans; [apply pow2_divide_le|exact B1]; lia).
assert (D2 : (2 ^ k | bv_unsigned (edenot E e2))%Z) by (eapply Z.divide_trans; [apply pow2_divide_le|exact B2]; lia).
destruct D1 as [q1 Hq1], D2 as [q2 Hq2]. exists (Z.lor q1 q2).
rewrite Hq1, Hq2. rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lor. reflexivity.
+ split; [lia|]. rewrite u_and64.
set (k := Z.max (ealign0 kn e1) (ealign0 kn e2)).
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
destruct (Z.le_ge_cases (ealign0 kn e2) (ealign0 kn e1)) as [Hc|Hc].
* replace k with (ealign0 kn e1) in * by lia. apply Hlow; [lia | lia | exact B1].
* replace k with (ealign0 kn e2) in * by lia. rewrite Z.land_comm. apply Hlow; [lia | lia | exact B2].
- split; [lia | apply Z.divide_1_l].
- destruct IHe1 as [A1 B1], IHe2 as [A2 B2].
destruct op; try (split; [lia | apply Z.divide_1_l]).
split; [lia|]. rewrite u_mul64. apply divide_mod64; [lia|].
eapply Z.divide_trans; [apply (pow2_divide_le _ (ealign0 kn e1 + ealign0 kn e2)); lia|].
rewrite Z.pow_add_r by lia. destruct B1 as [p1 Hp1], B2 as [p2 Hp2]. exists (p1 * p2)%Z. rewrite Hp1, Hp2. ring.
- split; [lia | apply Z.divide_1_l].
- split; [lia | apply Z.divide_1_l].
- split; [lia | apply Z.divide_1_l].
Qed.
#[using="Type"] Lemma find_and_atom_k_some : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'Q9';'A'U9%2241%411'I'>%6258%211&UGr4r3%3221(3(@r2r1%34?B21%52;1%>3;71'H&]Az%2218&];&]8+1%22<1%421=%H3N17%:271p0<1pQPBQ11pQUNO1pQTJN1pQS<Q41").
Proof.
intros sg. induction ts as [|[k a] r IH]; intros y mm H; [discriminate|].
assert (DFL : find_and_atom_k sg r = Some (y, mm) -> (0 < mm)%Z /\ Z.land (mm + 1) mm = 0%Z) by (intros H'; exact (IH y mm H')).
destruct a as [z1|v1|op b1 b2|op b1 b2|op b1 b2|op b1 b2|sx lo n b1|sx kk i n]; cbn [find_and_atom_k] in H; try (apply DFL; exact H).
destruct op; try (apply DFL; exact H). destruct b2 as [z| | | | | | |]; try (apply DFL; exact H).
destruct (Z.eqb k sg && Z.ltb 0 z && Z.eqb (Z.land (z + 1) z) 0)%bool eqn:Hc; [|apply DFL; exact H].
injection H as <- <-. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. auto.
Qed.
#[using="Type"] Lemma find_and_atom_some : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q3';'A'Q9'U9%3221%511'I'>%7256%211&UFr3%211(3(@r2r1%34>?21%52:1%=3:71'H&]Az%2218&];&]8+1%22<1%421=%G3K17%:271p0<1pQPBN1pQUNN1pQTJM1").
Proof. intros ts y mm H. exact (find_and_atom_k_some 1 ts y mm H). Qed.
#[using="Type"] Lemma u_and_mask : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q>'U0'U9'Q9'H&]<zr1%3221+R0%5231%7231'I&]8r3+1%3221&]I+2r2%3221%93B51&b4yR0&TLr6(S;(R6r5(S=r4%211%63541%9281%<2;1&]D%<2;8%?2>1%E2DH%4221%L3Q561p0D1p0O1po8Q81pQPBQ91pQUNQ;1pRFQ=1").
Proof.
intros E y mm k Hk Hm. cbn [edenot]. rewrite alu_and. unfold v_and.
pose proof (u64_range (edenot E y)) as Hr.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as Hp.
pose proof (Z.pow_le_mono_r 2 k 64 ltac:(lia) ltac:(lia)) as Hp64.
assert (Hones : bv_unsigned (Z_to_bv 64 mm) = Z.ones k).
{ rewrite u_lit64. unfold two64. rewrite Z.ones_equiv. rewrite Z.mod_small by lia. lia. }
rewrite Hones, Z.land_ones by lia.
pose proof (Z.mod_pos_bound (bv_unsigned (edenot E y)) (2 ^ k) ltac:(lia)).
rewrite u_small by lia. reflexivity.
Qed.
#[using="Type"] Lemma fold_lins_e_sg_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'U0'Q9';'A'U9%2241%411'I&\Br4&]5&W8&]Er5&9r2%23?<1%5241&B%13B?4r1%:3421qkN@1qQTFB1%>5BC149%A2@1&]8r3%D2C=%A221%F2E:%5221%I3O71pl2K1pQTJL1pQS<Q21pRFQ41").
Proof.
intros E sg ts acc. induction ts as [|[k a] rest IH]; cbn [fold_right tden]; [lia|].
rewrite lins_e_sound. cbn [fst snd]. rewrite IH. lia.
Qed.
#[using="Type"] Lemma fold_lins_e1_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2'U0';'A'Q9'U9%3221%511'I&\Br3&]5&W8&]E+1&9r2%23=<1%5241&B%13@?4r1%:3421qkN@1qQTFB1%>5BC149%A2@1&]8%C2B<%D2C8%3221%G3K51pl2I1pQTJJ1pRFQ11").
Proof. intros E ts acc. rewrite (fold_lins_e_sg_sound E 1 ts acc). lia. Qed.
#[using="Type"] Lemma pageup_low_k_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QJ'Q9'U0'U9'M'Ir6+1%33721-1%53941%7231'H&]<zr3%3221+R0%5231%7231r5&]I+2r4%3221%D3H51'>%11J&X<r9r7%3321I(3%12Q0:%M3731&]D&b4yR0&TLr8%22;1%5241%721<%Q63Q:1G%O2NH&]A%12J@%Q3231%Q4251p0?1p0I1p0Q01p0Q91pQQJQD1po6QE1pQP<QF1pmJQE1pRFQG1pQS<QI1").
Proof.
intros sg E e m j r Hsg Hj Hm H. unfold pageup_low_k in H.
destruct (lin_of e) as [c ts] eqn:Hle. cbn [fst snd] in H.
destruct (find_and_atom_k sg ts) as [[y mm]|] eqn:Hfa; [|discriminate].
destruct (find_and_atom_k_some sg ts y mm Hfa) as [Hmm Hland].
destruct (Z.ltb 0 m && Z.eqb ((mm + 1) mod m) 0 && Z.leb (mm + 1) two64)%bool eqn:Hc; [|discriminate].
apply andb_prop in Hc as [Hc Hle64]. apply andb_prop in Hc as [Hm0 Hdm].
apply Z.ltb_lt in Hm0. apply Z.eqb_eq in Hdm. apply Z.leb_le in Hle64. unfold two64 in Hle64.
destruct (lin_of y) as [cy tsy] eqn:Hly. cbn [fst snd] in H.
set (rest := lins_e (- sg) (EAlu ALU_AND y (ELit mm)) ts) in H.
destruct (fold_right (fun t acc => lins_e (sg * fst t) (snd t) acc) tsy rest) as [|t0 r0] eqn:Hfold; [|discriminate].
injection H as <-.
assert (Hp : (0 < m)%Z) by lia.
split; [|apply Z.mod_pos_bound; lia].
assert (HK : exists K, (0 <= K <= 64)%Z /\ (mm + 1 = 2 ^ K)%Z).
{ exists (Z.log2 (mm + 1)).
pose proof (Z.log2_nonneg (mm + 1)) as HK0.
destruct (Z.log2_spec (mm + 1) ltac:(lia)) as [HKle HKlt].
assert (E2 : (mm + 1 = 2 ^ Z.log2 (mm + 1))%Z).
{ destruct (Z.eq_dec (mm + 1) (2 ^ Z.log2 (mm + 1))) as [Heq|Hne]; [exact Heq|]. exfalso.
assert (Ht1 : Z.testbit (mm + 1) (Z.log2 (mm + 1)) = true) by (apply Z.bit_log2; lia).
assert (HL : Z.log2 mm = Z.log2 (mm + 1)).
{ apply Z.log2_unique; [lia|]. split; lia. }
assert (Ht2 : Z.testbit mm (Z.log2 (mm + 1)) = true) by (rewrite <- HL; apply Z.bit_log2; lia).
pose proof (Z.land_spec (mm + 1) mm (Z.log2 (mm + 1))) as Hls. rewrite Hland, Z.bits_0, Ht1, Ht2 in Hls. discriminate. }
split; [|exact E2]. split; [lia|].
destruct (Z.le_gt_cases (Z.log2 (mm + 1)) 64) as [Hok|Hbig]; [exact Hok|]. exfalso.
rewrite E2 in Hle64. pose proof (Z.pow_lt_mono_r 2 64 (Z.log2 (mm + 1)) ltac:(lia) ltac:(lia)). lia. }
destruct HK as (K & HKr & HKe).
pose proof (lin_of_sound E e) as [q1 H1]. unfold lden, uE in H1. rewrite Hle in H1. cbn [fst snd] in H1.
pose proof (lin_of_sound E y) as [q2 H2]. unfold lden, uE in H2. rewrite Hly in H2. cbn [fst snd] in H2.
pose proof (lins_e_sound E (- sg) (EAlu ALU_AND y (ELit mm)) ts) as Hrest. fold rest in Hrest. unfold uE in Hrest.
pose proof (fold_lins_e_sg_sound E sg rest tsy) as Hf. rewrite Hfold in Hf. cbn [tden] in Hf.
rewrite (u_and_mask E y mm K HKr HKe) in Hrest.
set (x := bv_unsigned (edenot E y)) in *. set (v := bv_unsigned (edenot E e)) in *.
rewrite HKe in Hdm. apply Z.mod_divide in Hdm; [|lia]. destruct Hdm as [w1 Hw1].
destruct (pow2_divide_le K 64 ltac:(lia)) as [w2 Hw2].
pose proof (Z.div_mod x (2 ^ K) ltac:(lia)) as Hx.
set (xq := (x / 2 ^ K)%Z) in *. set (xr := (x mod 2 ^ K)%Z) in *.
assert (E1 : tden E ts = (sg * xr - sg * tden E tsy)%Z) by (clearbody xq xr; destruct Hsg as [-> | ->]; lia).
assert (E2 : v = (c + sg * cy - sg * (2 ^ K * xq) - (q1 + sg * q2) * 2 ^ 64)%Z) by (clearbody xq xr; destruct Hsg as [-> | ->]; lia).
rewrite E2. rewrite Hw2, Hw1.
replace (c + sg * cy - sg * (w1 * m * xq) - (q1 + sg * q2) * (w2 * (w1 * m)))%Z
with (c + sg * cy + (- sg * w1 * xq - (q1 + sg * q2) * w2 * w1) * m)%Z by ring.
apply Z.mod_add. lia.
Qed.
#[using="Type"] Lemma pageup_low_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QB'U0'U9'Q9'H&]<zr2%3221+R0%5231%7231'Ir4&]I+2r3%3221%63?51'>%11A&X;r6r5%3221(3%12G:%?3731&]D&b4yR0&TLr8r7%3221%6251%821>%I3Q21H%Q12Q0I&]A%12KB%Q5231%Q6251p0@1p0J1p0Q21pQQJQ;1po6Q<1pQP<Q=1pmJQ?1pRFQA1").
Proof.
intros E e m j r Hj Hm H. unfold pageup_low in H.
destruct (pageup_low_k 1 e m) as [r1|] eqn:H1.
- injection H as <-. eapply (pageup_low_k_sound 1); eauto.
- eapply (pageup_low_k_sound (-1)); eauto.
Qed.
#[using="Type"] Lemma pageup_align_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'U0'U9'H&]<z&X:r1%211%5241+R0%7231%9231&]:&]I+2%2218&b4yR0&TLr2%221>%5241%:271%E2<1pmJG1pRFI1").
Proof.
intros E e. unfold pageup_align.
destruct (match find_and_atom_k 1 (snd (lin_of e)) with Some p => Some p | None => find_and_atom_k (-1) (snd (lin_of e)) end)
as [[y mm]|] eqn:Hfa; [|split; [lia | apply Z.divide_1_l]].
set (k := ctz64 (mm + 1)).
destruct (Z.eqb (mm + 1) (2 ^ k) && Z.leb k 64)%bool eqn:Hc; cbv iota beta; [|split; [lia | apply Z.divide_1_l]].
apply andb_prop in Hc as [Hm Hk64]. apply Z.eqb_eq in Hm. apply Z.leb_le in Hk64.
pose proof (ctz64_sound (mm + 1)) as [Hk0 _]. fold k in Hk0.
destruct (pageup_low e (mm + 1)) as [r|] eqn:Hpl; [|split; [lia | apply Z.divide_1_l]].
destruct r as [|rp|rn]; try (split; [lia | apply Z.divide_1_l]).
destruct (pageup_low_sound E e (mm + 1) k 0 ltac:(lia) Hm Hpl) as [Hmod _].
split; [lia|]. rewrite <- Hm. apply Z.mod_divide; [lia | exact Hmod].
Qed.
#[using="Type"] Lemma ealign_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q>';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r5r4r3r2%544321'H&]<z&TJ%1276%4231+R0%6231%8231&]:&]I+2%2218&b4&TL%12DA%32Q01%8251%B2:1p0D1pmJK1poFM1pV@Q01pRFQ91pQS:Q;1").
Proof.
intros segs E M kn e Hkn. unfold ealign.
pose proof (ealign0_sound segs E M (facts_of kn) e ltac:(eapply facts_of_ok; exact Hkn)) as [A1 B1].
pose proof (pageup_align_sound E e) as [A2 B2].
destruct (Z.max_spec (ealign0 (facts_of kn) e) (pageup_align e)) as [[_ ->]|[_ ->]]; split; try lia; assumption.
Qed.
#[using="Type"] Lemma u_srl_lit : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'U0'U9'Q9'I&b4yR0&TLr3(S;(R:r2(S=r1%211%63541%9281%<2;1&]9%<2;8%?2>1&]I+2&]D&Z=%22<1+R0%4221%7261%;291%J3K=1pQS0L1pmJN1pRFQ01").
Proof.
intros E e s. cbn [edenot]. rewrite alu_srl. unfold v_srl. rewrite (u_lit64 s).
pose proof (u64_range (edenot E e)) as Hr.
pose proof (Z.mod_pos_bound (s mod two64) 64 ltac:(lia)) as Hm.
rewrite Z.shiftr_div_pow2 by lia.
assert (Hp : (0 < 2 ^ ((s mod two64) mod 64))%Z) by (apply Z.pow_pos_nonneg; lia).
set (m := (2 ^ ((s mod two64) mod 64))%Z) in *.
assert (bv_unsigned (edenot E e) / m <= bv_unsigned (edenot E e))%Z.
{ apply Z.div_le_upper_bound; [exact Hp|]. nia. }
pose proof (Z.div_pos (bv_unsigned (edenot E e)) m ltac:(lia) ltac:(lia)).
rewrite u_small by lia. reflexivity.
Qed.
#[using="Type"] Lemma fold_lins_e_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'U0'Q9';'A'U9%2241%411'I&\Br4&]5&W8&]Er5&9r2%23?<1%5241&B%13B?4r1%:3421qkN@1qQTFB1%>5BC149%A2@1&]8r3%D2C=%A221%F2E:%5221%I3O71pl2K1pQTJL1pQQHQ21pRFQ41").
Proof.
intros E q ts acc. induction ts as [|[k a] rest IH]; cbn [fold_right tden]; [lia|].
rewrite lins_e_sound. cbn [fst snd]. rewrite IH. lia.
Qed.
#[using="Type"] Lemma u_srl_rem : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q3'U0'U9'Q9'H&]<zr1%3221&]A+R0%2241%8241'I&b4yR0&TLr4&YDr3&]I+2r2%3221%6251%9281%<2;1&]D%<2;9%?2>1%3217%B3L51p0D1pQS0N1pmJQ01pRFQ21").
Proof.
intros E e s Hs. unfold srl_rem. cbn [edenot]. rewrite alu_and. unfold v_and.
pose proof (u64_range (edenot E e)) as Hr.
pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)) as Hp.
pose proof (Z.pow_le_mono_r 2 s 63 ltac:(lia) ltac:(lia)) as Hp63.
assert (Hones : bv_unsigned (Z_to_bv 64 (2 ^ s - 1)) = Z.ones s).
{ rewrite u_lit64. unfold two64. rewrite Z.ones_equiv. change (2 ^ 63)%Z with 9223372036854775808%Z in Hp63.
rewrite Z.mod_small by lia. reflexivity. }
rewrite Hones, Z.land_ones by lia.
pose proof (Z.mod_pos_bound (bv_unsigned (edenot E e)) (2 ^ s) ltac:(lia)).
rewrite u_small by lia. reflexivity.
Qed.
#[using="Type"] Lemma srl_expand_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QB';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'A'Q9'U9%3221%B11&\<r7r6r5r4%544321'I%<2;8&YC%1265(@r3r2%34A>21%83751&\Br8%221>&]8%4238%22@1%?3I41p081p0B1pQTLI1pm8M1pQTJK1poFQ11pV@Q41pRFQ=1pQS:Q?1").
Proof.
intros segs E M kn ts. induction ts as [|[k a] rest IH]; intros c ts' Hkn H; cbn [srl_expand] in H.
- injection H as <- <-. cbn [tden]. lia.
- destruct (srl_expand kn rest) as [c0 t0] eqn:Hr.
specialize (IH c0 t0 Hkn eq_refl).
assert (KEEP : (c, ts') = (c0, lins_e k a t0) -> tden E ((k, a) :: rest) = (c + tden E ts')%Z).
{ intros HK. injection HK as -> ->. cbn [tden]. rewrite lins_e_sound. unfold uE. lia. }
destruct a as [| |op e b| | | | |]; try (apply KEEP; congruence).
destruct op; try (apply KEEP; congruence).
2: {
destruct b as [mk| | | | | | |]; try (apply KEEP; congruence).
destruct (highmask_s mk) as [s|] eqn:Hhm; [|apply KEEP; congruence].
destruct (lin_nowrap kn e) eqn:Hnw; [|apply KEEP; congruence].
injection H as <- <-.
unfold highmask_s in Hhm.
set (m' := (mk mod two64)%Z) in Hhm.
destruct (Z.eqb (two64 - m') (2 ^ Z.log2 (two64 - m')) && Z.ltb 0 (Z.log2 (two64 - m')) && Z.ltb (Z.log2 (two64 - m')) 64)%bool eqn:Hc; [|discriminate].
injection Hhm as Hs. rewrite Hs in Hc.
apply andb_prop in Hc as [Hc Hs64]. apply andb_prop in Hc as [Hm Hs0].
apply Z.eqb_eq in Hm. apply Z.ltb_lt in Hs0. apply Z.ltb_lt in Hs64.
pose proof (lin_nowrap_sound segs E M kn e Hkn Hnw) as He.
set (x := bv_unsigned (edenot E e)) in *.
pose proof (u64_range (edenot E e)) as Hxr. fold x in Hxr.
assert (Hp : (0 < 2 ^ s < 2 ^ 64)%Z) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
assert (Hand : bv_unsigned (edenot E (EAlu ALU_AND e (ELit mk))) = (x - x mod 2 ^ s)%Z).
{ cbn [edenot]. fold x.
rewrite alu_and. unfold v_and. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold x.
assert (Hmm : (mk mod 2 ^ 64 = 2 ^ 64 - 2 ^ s)%Z).
{ subst m'. unfold two64 in Hm. clear - Hm. lia. }
rewrite Hmm. rewrite land_highmask by lia.
pose proof (Z.mod_pos_bound x (2 ^ s) ltac:(lia)) as Hxs. unfold two64 in Hxr. pose proof (Z.mod_le x (2 ^ s) ltac:(lia) ltac:(lia)) as Hxl. apply Z.mod_small. clear - Hxs Hxr Hp Hxl. lia. }
assert (Hrem : uE E (srl_rem e (2 ^ s)) = (x mod 2 ^ s)%Z).
{ unfold uE. subst x. apply u_srl_rem. lia. }
cbn [tden]. rewrite lins_e_sound, fold_lins_e_sound.
unfold uE in Hrem |- *. rewrite Hand, Hrem.
destruct (lin_of e) as [ce te] eqn:Hle. cbn [fst snd] in *.
assert (QX : (k * x = k * ce + k * tden E te)%Z) by (rewrite He; ring).
clearbody x. clear - IH QX. lia. }
destruct b as [s| | | | | | |]; try (apply KEEP; congruence).
destruct (Z.eqb (k mod 2 ^ ((s mod two64) mod 64)) 0 && lin_nowrap kn e)%bool eqn:Hc; [|apply KEEP; congruence].
apply andb_prop in Hc as [Hdiv Hnw]. apply Z.eqb_eq in Hdiv.
pose proof (Z.mod_pos_bound (s mod two64) 64 ltac:(lia)) as Hs64.
set (m := (2 ^ ((s mod two64) mod 64))%Z) in *.
assert (Hm : (0 < m)%Z) by (subst m; apply Z.pow_pos_nonneg; lia).
pose proof (lin_nowrap_sound segs E M kn e Hkn Hnw) as He.
pose proof (u_srl_lit E e s) as Hsv. fold m in Hsv.
set (q := (k / m)%Z) in *.
assert (Hk : k = (q * m)%Z) by (subst q; rewrite Z.mul_comm; apply Z_div_exact_2; lia).
set (x := bv_unsigned (edenot E e)) in *.
pose proof (Z.div_mod x m ltac:(lia)) as Hxm. pose proof (Z.mod_pos_bound x m ltac:(lia)) as Hrm.
set (r := (x mod m)%Z) in *. set (d := (x / m)%Z) in *.
assert (Hrem : uE E (srl_rem e m) = r).
{ unfold uE. subst r x m. apply u_srl_rem. lia. }
destruct (Z.leb ((s mod two64) mod 64) (ealign kn e)) eqn:Hal.
+
injection H as <- <-.
apply Z.leb_le in Hal.
destruct (ealign_sound segs E M kn e Hkn) as [Hab Hdv]. fold x in Hdv.
assert (Hr0 : r = 0%Z).
{ subst r. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdv]. subst m. apply pow2_divide_le. lia. }
cbn [tden]. rewrite fold_lins_e_sound.
unfold uE in *. rewrite Hsv. fold d.
assert (Hkd : (k * d = q * x - q * r)%Z) by (rewrite Hk, Hxm; ring).
destruct (lin_of e) as [ce te] eqn:Hle. cbn [fst snd] in *.
assert (QX : (q * x = q * ce + q * tden E te)%Z) by (rewrite He; ring).
rewrite Hr0, Z.mul_0_r, Z.sub_0_r in Hkd. clearbody m q x d r. clear - Hkd IH QX. lia.
+ injection H as <- <-.
cbn [tden]. rewrite lins_e_sound, fold_lins_e_sound.
unfold uE in Hrem |- *. rewrite Hsv, Hrem. fold d.
assert (Hkd : (k * d = q * x - q * r)%Z) by (rewrite Hk, Hxm; ring).
destruct (lin_of e) as [ce te] eqn:Hle. cbn [fst snd] in *.
assert (QX : (q * x = q * ce + q * tden E te)%Z) by (rewrite He; ring).
clearbody m q x d r. clear - Hkd IH QX. lia.
Qed.
Definition sfact_ok (E : env) (f : sfact) : Prop :=
(fst (snd f) <= tden E (fst f) <= snd (snd f))%Z.
#[using="Type"] Lemma sum_fact_x_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QC';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'A'Q9'U9%3221%B11&\<r7r6r5r4%544321'H&]<r3&\B%1296%4231r2%6231%8231'Q2&Y;&\2r8%211&YJ%14CBA=%73631p091p0C1pnBM1pQP4N1pQTJL1pl8Q21pV@Q51pRFQ>1pQS:Q@1").
Proof.
intros segs E M allkn ts lo hi Hall Hb. unfold sum_fact_x.
destruct (srl_expand allkn ts) as [c2 ts2] eqn:Hx.
pose proof (srl_expand_sound segs E M allkn ts c2 ts2 Hall Hx) as S1.
destruct ts2 as [|t r]; [constructor|]. destruct (Z.eqb c2 0); [constructor|].
constructor; [|constructor]. unfold sfact_ok. cbn [fst snd]. lia.
Qed.
#[using="Type"] Lemma fact_nowrap_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R3';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'I'6&UBr2%23761(C%63521'H&]<&b4&TLr8%221?%42N1%62@1r3%8231%:231r9%921G%;2Q51&]8&9'A%12OQ0%Q?11&W2%11O%63Q331&\B&B%13Q664%32>1%<251%Q23Q9>1p0B1p0N1p0Q61pnBQ=1pQP4Q>1pmJQ@1pl8QB1pV@QE1pRFQN1pQS:R01").
Proof.
intros segs E M allkn e lo hi Hall H Hb. unfold fact_nowrap in H.
destruct (lin_range (erange allkn) (fst (lin_of e)) (snd (lin_of e))) as [[a b]|] eqn:Hlr; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. unfold two64 in H1, H2.
pose proof (lin_range_sound E (erange allkn) (fun a lo hi Ha => erange_sound segs E M allkn a lo hi Hall Ha) _ _ _ _ Hlr) as Hr.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
pose proof (u64_range (edenot E e)). nia.
Qed.
#[using="Type"] Lemma sum_facts_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q4';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11&\<r5r4r3r2%544321r6%741653'Q2&Y;&\2%115&YK%12;:%63531p081p0;1poFB1pl8C1pV@F1pRFO1pQS:Q11").
Proof.
intros segs E M allkn kn Hall Hkn. induction kn as [|K rest IH]; cbn [sum_facts]; [constructor|].
apply Forall_cons_iff in Hkn as [HK Hrest]. specialize (IH Hrest).
destruct K as [| | | | |e lo hi| | | |]; try exact IH.
assert (GEN : forall c ts, lin_of e = (c, ts) -> fact_nowrap allkn e hi = true ->
Forall (sfact_ok E) ((ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_x allkn ts (lo - c)%Z (hi - c)%Z ++ sum_facts allkn rest)).
{ intros c ts Hle Hnw. cbn [kentry_ok] in HK.
pose proof (fact_nowrap_sound segs E M allkn e lo hi Hall Hnw HK) as He. rewrite Hle in He. cbn [fst snd] in He.
constructor.
- unfold sfact_ok. cbn [fst snd]. lia.
- apply Forall_app. split; [|exact IH]. eapply sum_fact_x_sound; [exact Hall | lia]. }
destruct e; try exact IH;
(destruct (lin_of _) as [c [|t1 [|t2 ts]]] eqn:Hle; try exact IH;
pose proof (GEN _ _ eq_refl) as GEN';
destruct (fact_nowrap allkn _ hi) eqn:Hnw; [exact (GEN' eq_refl) | exact IH]).
Qed.
#[using="Type"] Lemma sub_fact_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "K'U0'Q9';'A'U9%2241%411'I&\Br4&YGr3r2r1%43321%7261&]J%9284&]E%;2:7%2291%5241%?3E71pQTJA1pn8B1pQQHH1pRFJ1").
Proof.
intros E q fts ts. unfold sub_fact. induction fts as [|[k a] r IH]; cbn [fold_right tden]; [lia|].
rewrite lins_e_sound. cbn [fst snd]. rewrite IH. lia.
Qed.
#[using="Type"] Lemma sum_subst_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QL'U0';&Y;%211'A'Q9'U9%3221%711'6'Q2&\2r:%211r9%53=21'I%=2<<%>2:1%?21:&YLr8r7r6%45<:321(@r5r4r3%44HH21%54F=41r2%74>G21%A3>91'H&]<&]8&\Br<%221@%421>%423M%621L%8231%823G%926B%;221%=241p0?1p0Q21pnLQ91pnDQ>1pQP6Q?1pQTLQ=1pnJQ=1pnBQB1pQP4QC1pQTJQA1pn6QG1pRFQK1").
Proof.
intros E fs. induction fs as [|[fts [flo fhi]] r IH]; intros ts lo hi hit ts' lo' hi' hit' Hfs H; cbn [sum_subst] in H.
- injection H as <- <- <- <-. lia.
- apply Forall_cons_iff in Hfs as [Hf Hr]. unfold sfact_ok in Hf. cbn [fst snd] in Hf.
destruct (fact_quot fts ts None) as [q|]; [|exact (IH _ _ _ _ _ _ _ _ Hr H)].
pose proof (sub_fact_sound E q fts ts) as Hs.
destruct (Z.leb 0 q) eqn:Hq.
+ apply Z.leb_le in Hq. pose proof (IH _ _ _ _ _ _ _ _ Hr H) as [A B]. rewrite Hs in A, B. nia.
+ apply Z.leb_gt in Hq. pose proof (IH _ _ _ _ _ _ _ _ Hr H) as [A B]. rewrite Hs in A, B. nia.
Qed.
#[using="Type"] Lemma lin_test_rel_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QO';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'Q9'A'U9%2231%B11'6p061p071&\<r7r6r5r4%544321'I&W6r3r2%347621(C%63?21'J'Hr1%=271%;3D16&]<&]8&\Br:%221D%42F1%62?1%722:%<221%=2:1qnBQ41%@2Q51qQP4Q61%B2Q71p0D1p0L1pQTHQ31pQTJQ71pm8Q<1poFQ>1pV@QA1pRFQJ1pQS:QL1").
Proof.
intros segs E M kn c ts test Hkn H. unfold lin_test_rel in H.
pose proof (sum_facts_sound segs E M kn kn Hkn Hkn) as Hfs.
destruct (sum_facts kn kn) as [|f fs] eqn:Hsf; [discriminate|].
destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] hit] eqn:Hss.
destruct hit; [|discriminate].
pose proof (sum_subst_sound E _ _ _ _ _ _ _ _ _ Hfs Hss) as [A B].
destruct (lin_range (erange kn) c ts') as [[lo hi]|] eqn:Hlr; [|discriminate].
pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
exists (lo + lo0)%Z, (hi + hi0)%Z. split; [exact H|]. lia.
Qed.
#[using="Type"] Lemma lin_test_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QO';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'Q9'A'U9%2231%B11'6p061p071&\<r7r6r5r4%544321'I&W5r3r2%347621(C%63?21'J'Hr1%=271%;3D16&]<&]8&\Br:%221D%42F1%62?1%722:%<221%=2:1qnBQ41%@2Q51qQP4Q61%B2Q71p0D1p0L1pQTHQ31pQTJQ71pm8Q<1poFQ>1pV@QA1pRFQJ1pQS:QL1").
Proof.
intros segs E M kn c ts test Hkn H. unfold lin_test in H.
destruct (lin_range (erange kn) c ts) as [[lo hi]|] eqn:Hlr; [|exact (lin_test_rel_sound segs E M kn c ts test Hkn H)].
destruct (test lo hi) eqn:Ht; [|exact (lin_test_rel_sound segs E M kn c ts test Hkn H)].
pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
exists lo, hi. split; [exact Ht | exact Hb].
Qed.
#[using="Type"] Lemma lin_brange_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'I'A%1299%B11&VK%1287(3(@r3r2%34AA21%5291%<3971'H&]<&b4&TLr8%221E%42Q41%62F1%722=%9221p0;1p0I1pnBQ01pQP4Q11pmJQ31poFQ51pV@Q81pRFQA1pQS:QC1").
Proof.
intros segs E M kn e lo hi Hkn H. unfold lin_brange in H.
pose proof (sum_facts_sound segs E M kn kn Hkn Hkn) as Hfs.
destruct (sum_facts kn kn) as [|f fs] eqn:Hsf; [discriminate|].
destruct (sum_subst (f :: fs) (snd (lin_of e)) 0 0 false) as [[ts' [lo0 hi0]] hit] eqn:Hss.
destruct hit; [|discriminate].
pose proof (sum_subst_sound E _ _ _ _ _ _ _ _ _ Hfs Hss) as [A B].
destruct (lin_range (erange kn) (fst (lin_of e)) ts') as [[l h]|] eqn:Hlr; [|discriminate].
destruct (Z.leb 0 (l + lo0) && Z.ltb (h + hi0) two64)%bool eqn:Hc; [|discriminate]. injection H as <- <-.
apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
pose proof (u64_range (edenot E e)). nia.
Qed.
#[using="Type"] Lemma tden_map_scale : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N'U0'Q9';'A'U9%2241%411'I&\Br3&Q4(@&]E&9r1%23>;1%4271&B%13A>4%84B?31qQTF?1%;4@@17%>2=1r2%@2?:%=221%C3I41pQTJE1pQS2K1pRFM1").
Proof. intros E sc ts. induction ts as [|[k a] rest IH]; cbn [List.map tden fst snd]; [lia|]. rewrite IH. lia. Qed.
#[using="Type"] Lemma lin_srange_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'I'A%1299%B11&W4%1287(3(@r3r2%34AA21%5291%<3971'H&]<&b4&TLr8%221E%42Q41%62F1%722=%9221p0;1p0I1pnBQ01pQP4Q11pmJQ31poFQ51pV@Q81pRFQA1pQS:QC1").
Proof.
intros segs E M kn e lo hi Hkn H. unfold lin_srange in H.
set (j := srl_scale_need (snd (lin_of e))) in H.
destruct (if Z.leb 0 j then Z.leb j 24 else false) eqn:Hj; [|discriminate].
assert (Hj0 : (0 <= j)%Z) by (destruct (Z.leb_spec 0 j); [assumption|discriminate]).
assert (Hsc : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
destruct (srl_expand kn (List.map (fun t => ((2 ^ j * fst t)%Z, snd t)) (snd (lin_of e)))) as [c2 t2] eqn:Hx2.
pose proof (srl_expand_sound segs E M kn _ _ _ Hkn Hx2) as S2. rewrite tden_map_scale in S2.
destruct (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) as [c3 t3] eqn:Hx3.
assert (S3 : tden E t2 = (c3 + tden E t3)%Z).
{ destruct (has_srl t2); [exact (srl_expand_sound segs E M kn _ _ _ Hkn Hx3) | injection Hx3 as <- <-; lia]. }
destruct (lin_range (erange kn) (2 ^ j * fst (lin_of e) + c2 + c3)%Z t3) as [[lo' hi']|] eqn:Hlr; [|discriminate].
pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
destruct (Z.leb_spec 0 (zcdiv lo' (2 ^ j))) as [Hlo0|Hlo0]; [|discriminate].
destruct (Z.leb_spec (zcdiv lo' (2 ^ j)) (hi' / 2 ^ j)) as [Hlohi|Hlohi]; [|discriminate].
destruct (Z.ltb_spec (hi' / 2 ^ j) two64) as [Hhi|Hhi]; [|discriminate]. injection H as <- <-.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
pose proof (u64_range (edenot E e)) as Ru. unfold two64 in *.
set (L := (fst (lin_of e) + tden E (snd (lin_of e)))%Z) in *.
assert (HL : (lo' <= 2 ^ j * L <= hi')%Z) by (unfold L; lia).
assert (Hfl : (L <= hi' / 2 ^ j)%Z) by (apply Z.div_le_lower_bound; lia).
assert (Hce : (zcdiv lo' (2 ^ j) <= L)%Z).
{ unfold zcdiv. assert ((- L) <= (- lo') / 2 ^ j)%Z by (apply Z.div_le_lower_bound; lia). lia. }
assert (q = 0%Z) by nia. subst q. lia.
Qed.
#[using="Type"] Lemma lin_srange_exact : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QN';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'I'A%1299%B11&W4%1287(3(@r3r2%34AA21%5291%<3971&b4&TLr8%221C%42Q21&]8&9%C2KL%Q;11&W2%11J%53O31&\B&B%13Q264%32=1%;251%N3Q5=1p0C1p0Q11pnBQ81pQP4Q91pmJQ;1poFQ=1pV@Q@1pRFQI1pQS:QK1").
Proof.
intros segs E M kn e lo hi Hkn H. unfold lin_srange in H.
set (j := srl_scale_need (snd (lin_of e))) in H.
destruct (if Z.leb 0 j then Z.leb j 24 else false) eqn:Hj; [|discriminate].
assert (Hj0 : (0 <= j)%Z) by (destruct (Z.leb_spec 0 j); [assumption|discriminate]).
assert (Hsc : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
destruct (srl_expand kn (List.map (fun t => ((2 ^ j * fst t)%Z, snd t)) (snd (lin_of e)))) as [c2 t2] eqn:Hx2.
pose proof (srl_expand_sound segs E M kn _ _ _ Hkn Hx2) as S2. rewrite tden_map_scale in S2.
destruct (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) as [c3 t3] eqn:Hx3.
assert (S3 : tden E t2 = (c3 + tden E t3)%Z).
{ destruct (has_srl t2); [exact (srl_expand_sound segs E M kn _ _ _ Hkn Hx3) | injection Hx3 as <- <-; lia]. }
destruct (lin_range (erange kn) (2 ^ j * fst (lin_of e) + c2 + c3)%Z t3) as [[lo' hi']|] eqn:Hlr; [|discriminate].
pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
destruct (Z.leb_spec 0 (zcdiv lo' (2 ^ j))) as [Hlo0|Hlo0]; [|discriminate].
destruct (Z.leb_spec (zcdiv lo' (2 ^ j)) (hi' / 2 ^ j)) as [Hlohi|Hlohi]; [|discriminate].
destruct (Z.ltb_spec (hi' / 2 ^ j) two64) as [Hhi|Hhi]; [|discriminate]. injection H as <- <-.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
pose proof (u64_range (edenot E e)) as Ru. unfold two64 in *.
set (L := (fst (lin_of e) + tden E (snd (lin_of e)))%Z) in *.
assert (HL : (lo' <= 2 ^ j * L <= hi')%Z) by (unfold L; lia).
assert (Hfl : (L <= hi' / 2 ^ j)%Z) by (apply Z.div_le_lower_bound; lia).
assert (Hce : (zcdiv lo' (2 ^ j) <= L)%Z).
{ unfold zcdiv. assert ((- L) <= (- lo') / 2 ^ j)%Z by (apply Z.div_le_lower_bound; lia). lia. }
assert (q = 0%Z) by nia. subst q. lia.
Qed.
#[using="Type"] Lemma xlo_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q=';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r6r5r4r3%544321'I%@18&ZE%1265(3r2%22=1%73641&]<&b4&TLr7%221?%42N1%62@1p081p0A1pQP4H1pmJJ1poFL1pV@O1pRFQ81pQS:Q:1").
Proof.
intros segs E M kn e lo Hkn H. unfold xlo in H.
destruct e; try (destruct (erange kn _) as [[l h]|] eqn:Her;
[ injection H as <-; exact (proj1 (erange_sound segs E M kn _ l h Hkn Her))
| destruct (lin_brange kn _) as [[l h]|] eqn:Hbr;
[ injection H as <-; exact (proj1 (lin_brange_sound segs E M kn _ l h Hkn Hbr))
| destruct (lin_srange kn _) as [[l h]|] eqn:Hsr; [|discriminate]; injection H as <-;
exact (proj1 (lin_srange_sound segs E M kn _ l h Hkn Hsr)) ] ]).
injection H as <-. cbn [edenot]. rewrite u_lit64, zlit64_eq. lia.
Qed.
#[using="Type"] Lemma xhi_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q=';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r6r5r4r3%544321'I%@18&ZC%1265(3r2%22=1%73641&]<&b4&TLr7%221?%42N1%621@p081p0A1pnBH1pmJJ1poFL1pV@O1pRFQ81pQS:Q:1").
Proof.
intros segs E M kn e hi Hkn H. unfold xhi in H.
destruct e; try (destruct (erange kn _) as [[l h]|] eqn:Her;
[ injection H as <-; exact (proj2 (erange_sound segs E M kn _ l h Hkn Her))
| destruct (lin_brange kn _) as [[l h]|] eqn:Hbr;
[ injection H as <-; exact (proj2 (lin_brange_sound segs E M kn _ l h Hkn Hbr))
| destruct (lin_srange kn _) as [[l h]|] eqn:Hsr; [|discriminate]; injection H as <-;
exact (proj2 (lin_srange_sound segs E M kn _ l h Hkn Hsr)) ] ]).
injection H as <-. cbn [edenot]. rewrite u_lit64, zlit64_eq. lia.
Qed.
#[using="Type"] Lemma lin_nowrapR_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r5r4r3r2%544321'I'6&W1%1265(C%53421'Q9&b4&TLr6%221=%42K1&]8&9'A%129F%Q511&W2%11E%63=31&\B&B%13@64%32>1%<251%I3C>1p0E1p0L1pmJQ31poFQ51pV@Q81pRFQA1pQS:QC1").
Proof.
intros segs E M kn e Hkn H. unfold lin_nowrapR in H.
destruct (srl_expand kn (snd (lin_of e))) as [c2 t2] eqn:Hx.
lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Ht0 end.
2: {
destruct (lin_srange kn e) as [[slo shi]|] eqn:Hs; [|discriminate]. exact (lin_srange_exact segs E M kn e slo shi Hkn Hs). }
clear H. rename Ht0 into H.
apply (lin_test_sound segs E M kn) in H as (lo & hi & Ht & Hb); [|exact Hkn].
pose proof (srl_expand_sound segs E M kn _ _ _ Hkn Hx) as S1.
apply andb_prop in Ht as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
pose proof (u64_range (edenot E e)). nia.
Qed.
#[using="Type"] Lemma lin_apart_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QL';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r:r9r8r7%544321'I'6&VIr6r5r4r3r2%67;:54321(C%:3921'M&]<&]8&\8r;(SH%12DC%4231%621@%42@?%7261%:231%:22A%<216%>231p0@1p0L1pQQ0Q31po<Q41plHQ61pQPNQ61po:Q71plFQ91poFQ;1pV@Q>1pRFQG1pQS:QI1").
Proof.
intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold lin_apart in H.
destruct (shares_var b1 b2); [|discriminate]. unfold lin_apart0 in H.
apply andb_prop in H as [H Hm]. apply andb_prop in H as [Hw1 Hw2].
pose proof (lin_nowrapR_sound segs E M kn b1 Hkn Hw1) as E1.
pose proof (lin_nowrapR_sound segs E M kn b2 Hkn Hw2) as E2.
destruct (lin_of b1) as [c1 ts1] eqn:Hl1. destruct (lin_of b2) as [c2 ts2] eqn:Hl2. cbn [fst snd] in *.
apply (lin_test_sound segs E M kn) in Hm as (lo & hi & Hm & Hb); [|exact Hkn].
rewrite lsub_e_sound in Hb. unfold estart. cbn [a_base a_off]. rewrite E1, E2.
apply orb_prop in Hm as [Hm|Hm]; apply Z.leb_le in Hm; lia.
Qed.
Fixpoint xt_den (E : env) (ts : xterms) : Z :=
match ts with [] => 0 | (e, k) :: r => (bv_unsigned (edenot E e) + k + xt_den E r)%Z end.
#[using="Type"] Lemma xt_lin_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q?';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11&ZI&\<r5r4r3r2%544321'I'6&ZH%1265(C%53421'Q9&]8&ZF%11<&\Br6&ZG%11@%4231%8261&\5%126D%B3<31p0>1p0E1pQTJL1poFN1pV@Q11pRFQ:1pQS:Q<1").
Proof.
intros segs E M kn ts Hkn. induction ts as [|[e k] r IH]; cbn [xt_nowrap xt_const xt_lin xt_den]; intros H.
- cbn [tden]. lia.
- apply andb_prop in H as [H1 H2].
pose proof (lin_nowrapR_sound segs E M kn e Hkn H1) as He.
specialize (IH H2).
assert (FR : forall ts acc, tden E (fold_right (fun t a => lins_e (fst t) (snd t) a) acc ts) = (tden E ts + tden E acc)%Z).
{ intros ts0 acc. induction ts0 as [|[k' a'] rest IH0]; cbn [fold_right tden]; [lia|].
rewrite lins_e_sound. cbn [fst snd]. rewrite IH0. lia. }
rewrite FR. rewrite He. lia.
Qed.
#[using="Type"] Lemma lin_ge0_scaled_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q@';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'Q9'A'U9%2231%B11&\<r6r5r4r3%544321'I'6&VMr2%23761(C%63521&]<z&]8&\Br7%221>%42@1%7261p091p0A1pQTJH1pm8M1poFO1pV@Q21pRFQ;1pQS:Q=1").
Proof.
intros segs E M kn c ts Hkn H. unfold lin_ge0_scaled in H.
set (j := srl_scale_need ts) in H.
destruct (if Z.ltb 0 j then Z.leb j 24 else false) eqn:Hj; [|discriminate].
assert (Hj0 : (0 < j)%Z) by (destruct (Z.ltb_spec 0 j); [assumption|discriminate]).
assert (Hsc : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
destruct (srl_expand kn (List.map (fun t => ((2 ^ j * fst t)%Z, snd t)) ts)) as [c2 t2] eqn:Hx2.
pose proof (srl_expand_sound segs E M kn _ _ _ Hkn Hx2) as S2. rewrite tden_map_scale in S2.
destruct (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) as [c3 t3] eqn:Hx3.
assert (S3 : tden E t2 = (c3 + tden E t3)%Z).
{ destruct (has_srl t2); [exact (srl_expand_sound segs E M kn _ _ _ Hkn Hx3) | injection Hx3 as <- <-; lia]. }
apply (lin_test_sound segs E M kn) in H as (lo & hi & Hr & Hb); [|exact Hkn]. apply Z.leb_le in Hr.
assert (G : (0 <= 2 ^ j * (c + tden E ts))%Z) by lia.
nia.
Qed.
#[using="Type"] Lemma lin_ge0_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q:';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11&ZI&\<r6r5r4r3%544321'I'6&VLr2%23761(C%63521&]<&\5r7%221<%322>%5221p071p0?1pQQ4F1pQQDG1poFI1pV@L1pRFQ51pQS:Q71").
Proof.
intros segs E M kn pos neg Hkn H. unfold lin_ge0 in H.
apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hp Hn].
pose proof (xt_lin_sound segs E M kn pos Hkn Hp) as XP. pose proof (xt_lin_sound segs E M kn neg Hkn Hn) as XN.
destruct (lin_test kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo)) eqn:Hplain.
{ apply (lin_test_sound segs E M kn) in Hplain as (lo & hi & Hr0 & Hb0); [|exact Hkn].
apply Z.leb_le in Hr0. rewrite lsub_e_sound in Hb0. lia. }
destruct (srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg))) as [c2 t2] eqn:Hx.
pose proof (srl_expand_sound segs E M kn _ _ _ Hkn Hx) as S1.
rewrite lsub_e_sound in S1.
destruct (lin_test kn (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo)) eqn:H2.
{ apply (lin_test_sound segs E M kn) in H2 as (lo & hi & Hr2 & Hb2); [|exact Hkn]. apply Z.leb_le in Hr2. lia. }
lazymatch type of Hr with (if ?c then _ else _) = _ => destruct c eqn:H3 end.
{ clear Hr. destruct (has_srl t2); [|discriminate].
destruct (srl_expand kn t2) as [c3 t3] eqn:Hx3.
pose proof (srl_expand_sound segs E M kn _ _ _ Hkn Hx3) as S2.
apply (lin_test_sound segs E M kn) in H3 as (lo & hi & H3 & Hb); [|exact Hkn].
apply Z.leb_le in H3. lia. }
pose proof (lin_ge0_scaled_sound segs E M kn _ _ Hkn Hr) as SC. rewrite lsub_e_sound in SC. lia.
Qed.
#[using="Type"] Lemma xinside_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QO';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r:r9r8r7%544321'I'6&ZDr6r5r4r3r2%67;:54321(C%:3921'H&]<&\8r;(SH%12<;%4231%32ED%6251%8231&]8&\6%129D%3251%32;C%5291%?231%A281p0C1p0O1pQQ0Q71po<Q71plHQ91pQPNQ:1po:Q:1plFQ<1poFQ>1pV@QA1pRFQJ1pQS:QL1").
Proof.
intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold xinside in H.
destruct (shares_var b1 b2).
2: { destruct (novars b2); [|discriminate]. unfold xinside_num in H.
destruct (xlo kn b2) as [lo2|] eqn:Xl2; [|discriminate].
destruct (xhi kn b2) as [hi2|] eqn:Xh2; [|discriminate].
destruct (Z.eqb lo2 hi2) eqn:Heq; [|discriminate]. apply Z.eqb_eq in Heq. subst hi2.
destruct (base_range kn b1) as [[lo1 hi1]|] eqn:Hb1; [|discriminate].
destruct (xhi kn n1) as [h1|] eqn:Xh1; [|discriminate].
destruct (xlo kn n2) as [l2|] eqn:Xl2n; [|discriminate].
apply andb_prop in H as [Ha Hb]. apply Z.leb_le in Ha. apply Z.leb_le in Hb.
pose proof (xlo_sound segs E M kn b2 lo2 Hkn Xl2). pose proof (xhi_sound segs E M kn b2 lo2 Hkn Xh2).
pose proof (base_range_sound segs E M kn b1 lo1 hi1 Hkn Hb1) as [A1 B1].
pose proof (xhi_sound segs E M kn n1 h1 Hkn Xh1). pose proof (xlo_sound segs E M kn n2 l2 Hkn Xl2n).
unfold estart, elenZ. cbn [a_base a_off]. lia. }
unfold xinside0 in H.
lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:H1; [|discriminate] end. rename H into H2.
pose proof (lin_ge0_sound segs E M kn _ _ Hkn H1) as A. pose proof (lin_ge0_sound segs E M kn _ _ Hkn H2) as B.
cbn [xt_den] in A, B. unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.
#[using="Type"] Lemma sub_itv_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QL';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9'Y4&\<r9r8r7r6%544321'I'6&YHr5r4r3r2%56:94321(C%93821'H&]<&\8r:%221:(SH%12CB%5241%7241&]8%123A&\6%129A%4291%=241%?271p0A1p0L1pQP<Q51pm8Q41pQPJQ61po8Q71plBQ91pl8Q;1pV@Q>1pRFQG1pQS:QI1").
Proof.
intros segs E M allkn b k n [cb ck] m Hkn H. unfold sub_itv in H. cbn [a_base a_off] in H.
lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hlit end.
- destruct (expr_eqb b cb && Z.leb ck k)%bool eqn:H12; [|discriminate].
apply andb_prop in H12 as [H1 H2].
apply expr_eqb_eq in H1. subst cb. apply Z.leb_le in H2.
destruct (xlo allkn m) as [ml|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hlit.
pose proof (xlo_sound segs E M allkn m ml Hkn Hx). unfold elenZ.
unfold estart. cbn [a_base a_off]. lia.
- destruct (Z.leb 0 n && Z.ltb n two64)%bool eqn:Hn; [|discriminate].
apply andb_prop in Hn as [Hn0 Hn1]. apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
pose proof (xinside_sound segs E M allkn b k (ELit n) cb ck m Hkn H) as [A B].
unfold elenZ in B at 1. cbn [edenot] in B. rewrite u_lit64 in B. unfold two64 in B. rewrite Z.mod_small in B by lia.
split; [exact A | exact B].
Qed.
#[using="Type"] Lemma if3_cases : forall (a b c d e : bool),
(if (if a then b else false) then true else if (if c then d else false) then true else e) = true ->
(a = true /\ b = true) \/ (c = true /\ d = true) \/ e = true.
Proof. intros [|] [|] [|] [|] [|]; cbn; intros H; try discriminate; auto. Qed.
#[using="Type"] Lemma kdisj_apart_sound_gen : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R0';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r;r:r9r8%544321r<%741653'I'6&V5r7r6r5r4r3%68>=<54321(C%:3921'M&]<&]8&\8r=(SH%12FE%4231%621@%42@?%7261%:231%:22A%<216%>231p0@1p0L1p0O1pQQ0Q61po<Q71plHQ91pQPNQ91po:Q:1plFQ<1poFQ>1pl8Q?1pV@QB1pRFQK1pQS:QM1").
Proof.
intros segs E M allkn kn b1 k1 n1 b2 k2 n2 Hall Hkn. induction kn as [|K rest IH]; cbn [kdisj_apart]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | | | | |c1 m1 c2 m2| |]; try (apply IH; assumption).
apply if3_cases in H as [[Ha Hb]|[[Ha Hb]|H]]; [| |apply IH; assumption];
cbn [kentry_ok] in HK;
apply (sub_itv_sound segs E M allkn) in Ha as [Ha1 Ha2]; try exact Hall;
apply (sub_itv_sound segs E M allkn) in Hb as [Hb1 Hb2]; try exact Hall; lia.
Qed.
#[using="Type"] Lemma kdisj_apart_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QL';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r:r9r8r7%544321'I'6&V5r6r5r4r3r2%68;;:54321(C%:3921'M&]<&]8&\8r;(SH%12DC%4231%621@%42@?%7261%:231%:22A%<216%>231p0@1p0L1pQQ0Q31po<Q41plHQ61pQPNQ61po:Q71plFQ91poFQ;1pV@Q>1pRFQG1pQS:QI1").
Proof. intros. eapply kdisj_apart_sound_gen; eassumption. Qed.
#[using="Type"] Lemma ranges_apart_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QL';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r:r9r8r7%544321'I'6&XFr6r5r4r3r2%67;:54321(C%:3921'M&]<&]8&\8r;(SH%12DC%4231%621@%42@?%7261%:231%:22A%<216%>231p0@1p0L1pQQ0Q31po<Q41plHQ61pQPNQ61po:Q71plFQ91poFQ;1pV@Q>1pRFQG1pQS:QI1").
Proof.
intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold ranges_apart in H.
lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hbr end.
2: { lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkd end.
- eapply kdisj_apart_sound; eassumption.
- eapply lin_apart_sound; eassumption. }
clear H. rename Hbr into H.
destruct (base_range kn b1) as [[lo1 hi1]|] eqn:H1; [|discriminate].
destruct (base_range kn b2) as [[lo2 hi2]|] eqn:H2; [|discriminate].
pose proof (base_range_sound segs E M kn b1 lo1 hi1 Hkn H1) as [A1 B1].
pose proof (base_range_sound segs E M kn b2 lo2 hi2 Hkn H2) as [A2 B2].
unfold estart. cbn [a_base a_off].
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
#[using="Type"] Lemma sub_itv_x_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QM';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9'Y4&\<r9r8r7r6%544321'I'6&YIr5r4r3r2%56:94321(C%93821'H&]<&\8r:%221:(SH%12CB%5241%7241&]8&\6%128B%3251%32:B%52:1%>231%@281p0B1p0M1pQP<Q61pm8Q51pQPJQ81po8Q81plBQ:1poFQ<1pV@Q?1pRFQH1pQS:QJ1").
Proof.
intros segs E M kn b k n [cb ck] m Hkn H. unfold sub_itv_x in H. cbn [a_base a_off] in H.
pose proof (xinside_sound segs E M kn b k n cb ck m Hkn H) as [A B]. unfold estart in *. cbn [a_base a_off] in *. lia.
Qed.
#[using="Type"] Lemma kdisj_apart_x_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R3';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r;r:r9r8%544321r<%741653'I'6&V6r7r6r5r4r3%68>=<54321(C%:3921'M&]<&]8&\8r=(SH%12FE%4231&\6%125A%8231%62BA%9281%<231%62:C%=231%?219%A241p0C1p0O1p0Q21pQQ0Q:1po<Q:1plHQ<1pQPNQ=1po:Q=1plFQ?1poFQA1pl8QB1pV@QE1pRFQN1pQS:R01").
Proof.
intros segs E M allkn kn b1 k1 n1 b2 k2 n2 Hall Hkn. induction kn as [|K rest IH]; cbn [kdisj_apart_x]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | | | | |c1 m1 c2 m2| |]; try (apply IH; assumption).
apply if3_cases in H as [[Ha Hb]|[[Ha Hb]|H]]; [| |apply IH; assumption];
cbn [kentry_ok] in HK;
apply (sub_itv_x_sound segs E M allkn) in Ha as [Ha1 Ha2]; try exact Hall;
apply (sub_itv_x_sound segs E M allkn) in Hb as [Hb1 Hb2]; try exact Hall; lia.
Qed.
#[using="Type"] Lemma know_lookupA0_acc : forall allkn segs kn rb rk n sx hints acc,
match know_lookupA0 allkn segs kn rb rk n sx hints acc with
| LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
| LStuck => True
end.
Proof.
intros allkn segs kn.
induction kn as [|K rest IH]; intros rb rk n sx hints acc; cbn [know_lookupA0].
- exists []. reflexivity.
- assert (Hnil : exists pre : list sidecond, acc = pre ++ acc) by (exists []; reflexivity).
assert (Hone : forall s, exists pre : list sidecond, s :: acc = pre ++ acc)
by (intros s; exists [s]; reflexivity).
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] ulen];
[ | | | | apply IH | apply IH | apply IH | apply IH | | apply IH].
5: { cbv zeta.
destruct len; first [ destruct (rel_lit rb rk (Z.of_nat n) kb kk (z mod 2^64)%Z); first [exact I | apply IH | apply Hnil | apply Hone | destruct (xinside allkn _ _ _ _ _ _); [apply Hnil|]; destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone]]
| destruct (xinside allkn _ _ _ _ _ _); [apply Hnil|]; destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone] ]. }
+ destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); first [exact I | apply IH | apply Hnil | apply Hone].
+ destruct len; first [ destruct (rel_lit rb rk (Z.of_nat n) kb kk (z mod 2^64)%Z); first [exact I | apply IH | apply Hnil | apply Hone | destruct (xinside allkn _ _ _ _ _ _); [apply Hnil|]; destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone]]
| destruct (xinside allkn _ _ _ _ _ _); [apply Hnil|]; destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone] ].
+ destruct (expr_eqb rb kb); [|apply IH].
destruct (Z.leb kk rk); [|apply IH].
destruct len; first [ destruct (Z.leb (rk + Z.of_nat n) (kk + (z mod 2^64)%Z)); [apply Hnil|]; destruct (Z.leb (kk + (z mod 2^64)%Z) rk); [apply IH | exact I]
| lazymatch goal with |- match (if ?c then _ else _) with _ => _ end => destruct c; [apply Hnil|] end;
destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone] ].
+ destruct rb; try apply IH. destruct z; try apply IH.
destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool; [|apply IH].
destruct (img_bytes segs rk n); [apply Hnil | exact I].
Qed.
#[using="Type"] Lemma know_lookupA_acc : forall allkn segs kn rb rk n sx hints acc,
match know_lookupA allkn segs kn rb rk n sx hints acc with
| LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
| LStuck => True
end.
Proof.
intros allkn segs kn rb rk n sx hints acc. unfold know_lookupA.
pose proof (know_lookupA0_acc allkn segs kn rb rk n sx hints acc) as H.
destruct (know_lookupA0 allkn segs kn rb rk n sx hints acc) as [v scs h|scs h|]; try exact H.
destruct (know_bytes_lit segs kn rb rk n); exact H.
Qed.
#[using="Type"] Lemma know_lookup_acc : forall segs kn rb rk n sx hints acc,
match know_lookup segs kn rb rk n sx hints acc with
| LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
| LStuck => True
end.
Proof. intros. unfold know_lookup. apply know_lookupA_acc. Qed.
#[using="Type"] Lemma rel_lit_inside : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QC'U0'U9'Q9'I'XE&XJr7r6r5r4r3r2%76654321(SGr1%211%=3<41'Hr8%@3B1;&]J%12?<%C3D;1&]<%12?B&]8%12DC%22BA%5221&\8r9(SH%12>J%4231%32JI%6251%;21I%Q23Q341%E2:1%F2?1%G2B1%H2F1p0J1pmDQ91poFQ:1poDQ;1po@Q=1pQRBQ=1pQR<Q>1pQR0Q@1pRFQB1").
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
#[using="Type"] Lemma rel_lit_disjoint : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q:'U0'U9'Q9'I'XE&XJr6r5r4r3r2r1%76654321(SF%;3:21'Hr7%>3@19'M&]<&]8&\8r8(SH%128B%4231%621C%42CB%7261%:231%:22D%<216%>231%B2@1p0D1poFQ11poDQ21po@Q41pQRBQ41pQR<Q51pQR0Q71pRFQ91").
Proof.
intros E rb rk rn kb kk kn H. unfold rel_lit in H.
destruct (expr_eqb rb kb) eqn:Heq; [|discriminate].
apply expr_eqb_eq in Heq. subst kb.
destruct (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool; [discriminate|].
destruct (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool eqn:Hd; [|discriminate].
split; [reflexivity|]. unfold estart. cbn [a_base a_off].
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.
#[using="Type"] Lemma rdn_inside_wbytes : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RA';'QF%211'U0'aOyR0%211'>y8%511%311p051'Y4'<'Q9&\:r8r6&]Gr5%211%63541r9r4r3%711%;3431'I&\8r:%221;&]8%423@%2219%73D41&]<z%221>%D1E%82D1%F1B%6221%Q:1Q1%Q411&\Hr>&\Dr<&SMr=r;%3221&R3%12HO%83731%726Q7r7%=4<321(3&Q3&Q7&]L%11Q=%33QF1:%53QG81%72G1%Q73G91p0J1p0O1p0Q31p0Q<1p0QB1pmDQJ1pQPJQL1pQQNQN1pkLR51pQU<QO1po>R11pV@R31pRFR<1pQS:R>1").
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
#[using="Type"] Lemma ext_hit_value : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QB'6'Q9'<'aOyR0%211&]<zr4%3221'Q0&N&]Lr5%211%4217r3%7221u8%9261'I&aN&\9r8r6&QD&Q3y8%I11&Q7r7%C11&R3%12DI%53631%937;1%;11%?3>=1%A2Q21&UA%14A9@Q0%E3Q431p0G1p0J1p0Q31pkLQ81pQU<Q<1pQPJQ=1pmDQ?1pQT@QA1").
Proof.
intros sx d n w V Hd Hdn Hn.
rewrite slice_word_bytes by lia. unfold ext_val, ext_Z, extz. reflexivity.
Qed.
Section Lookups.
Variable segs : list Segment.
#[using="Type"] Lemma rdn_cons1 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QD'aOyR0%211'>y8%511%311p051'<';%115'I%912&\HvaDr5r4u1%544321(3(7r2(=%11B%43C31%62?1%?3>81r6&b0(aM+1(F%33O21%53Q0B1%E4D71B%@2I>%I3H21r7(2%11H%K4J3=1r3%F3Q5J1%H2Q11%Q13Q041p091p0D1pm4Q51plBQ;1pQPJQ91pkNQ@1pQP>Q<1").
Proof.
intros mem a n b bs H1 Hn.
change (rdn segs mem a (S n)) with
(match (match mem a with Some b0 => Some b0 | None => seg_rom segs a end) with
| Some b0 => match rdn segs mem (a + 1) n with Some rest => Some (b0 :: rest) | None => None end
| None => None end).
change (rdn segs mem a 1) with
(match (match mem a with Some b0 => Some b0 | None => seg_rom segs a end) with
| Some b0 => match rdn segs mem (a + 1) 0 with Some rest => Some (b0 :: rest) | None => None end
| None => None end) in H1.
cbn [rdn] in H1.
destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end) as [x|]; [|discriminate].
injection H1 as ->. rewrite Hn. reflexivity.
Qed.
#[using="Type"] Lemma word_byte_at : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QH'<'Q9'aOyR0%211'Q0&N&]Lr2%211u1%5221r3%8221&]<z%2214'I';y8%B11%311&Q3&Q7r4%B11&R3r5%221@%63941%83:D1(7&aN&]D&]9&b4%12Q1H&]I+2&]E+8%221A%5241%9271+X0%<221%>2K1(=%11L%B3M31%Q13MD1p0Q31p0Q71pkLQA1pmDQE1pQU<QG1").
Proof.
intros w d V Hw Hd. unfold word_to_le_bytes.
rewrite skipn_Z_to_le_bytes by lia. rewrite firstn_Z_to_le_bytes by lia.
cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
rewrite Z2Nat.id by lia. change (bv_wrap 8 ?x) with (x mod 256)%Z. cbn [bv_wrap bv_modulus].
change (bv_modulus 8) with 256%Z. rewrite Z.mod_mod by lia. reflexivity.
Qed.
#[using="Type"] Lemma log_byte_lit_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R9'U0'aOyR0%211'>y8%511%311p051';'Y:%211'U9'Q9&\=r6r4%3221'I%?16&W=r5r3%33271(3r2%22=1%93841&\:r8(SH%12:?+1%53421'H%J1M%Q011&\HvaD&\>r9r7%332=1&SM%>2MG%2251u1%:49521(7&aN%12Q=Q2(=%11Q>%53Q?31%N2C1%Q53C81&]<z%221Q:&]A+X0%22Q=1%L241%M281p0O1p0Q61p0QA1plBQF1pQR<QG1pQR0QI1pQP:QK1plJQO1pRFR81").
Proof.
intros E base log. induction log as [|[[kb kk] w v] rest IH]; intros rb rk b Hlf H Hfr; [discriminate|].
cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfk & Hlf').
cbn [log_byte_lit] in H. cbn [mem_denot].
destruct (rel_lit rb rk 1 kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel; try discriminate.
- destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
destruct v as [z| | | | | | |]; try discriminate. injection H as <-.
split; [|apply Z.mod_pos_bound; lia].
rewrite (rdn_inside_wbytes segs E _ (SA rb kk) w (edenot E (ELit z)) (SA rb rk) 1 d Hfk Hfr Hst) by lia.
rewrite word_byte_at by lia. cbn [edenot]. rewrite u_lit64. reflexivity.
- destruct (rel_lit_disjoint E _ _ _ _ _ _ Hrel) as [<- Hdis].
destruct (IH rb rk b Hlf' H Hfr) as [IH1 IH2]. split; [|exact IH2].
rewrite rdn_wbytes_out;
[ exact IH1
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk), (flat_u E _ _ Hfr); exact Hdis
| rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); cbn [Z.of_nat]; lia
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk); destruct Hfk as (?&?&?&?); lia ].
Qed.
#[using="Type"] Lemma log_bytes_lit_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R:'U0'aOyR0%211'>y8%511%311p051';'Y:%211'U9'<'Q9%611&\=r7r5%3221'I%A16&W>r6r3r4%443821(3r2%22>1%:3941&\:r9(SH%12;9&]G%11B%63531'J%N1Q1'H%Q512&\HvaD&\>r;r:%3321?&SMr8%A21K%3261%:4951Q3r1%K2?1%Q33>31&Q4&b4%11QE%34QEQ=16%Q83Q=1Q:%E261qm4G1%I2H1p0K1p0Q31p0Q?1pQV4QD1pQR<QF1pQPJQH1pQR0QJ1pQP:QL1plJR01pRFR91").
Proof.
intros E base log rb n. induction n as [|n IH]; intros rk zs Hlf H Hfr.
- cbn in H. injection H as <-. exists []. split; reflexivity.
- cbn [log_bytes_lit] in H.
destruct (log_byte_lit log rb rk) as [b|] eqn:Hb; [|discriminate].
destruct (log_bytes_lit log rb (rk + 1) n) as [r|] eqn:Hr; [|discriminate].
injection H as <-.
assert (Hf1 : flat E (SA rb rk) 1) by (unfold flat, estart in *; cbn [a_base a_off] in *; lia).
destruct (log_byte_lit_sound E base log rb rk b Hlf Hb Hf1) as [H1 Hb8].
assert (Hb8' : map bv_unsigned [Z_to_bv 8 b] = [b]).
{ cbn [map]. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia. }
destruct n as [|n'].
{ cbn in Hr. injection Hr as <-. exists [Z_to_bv 8 b]. split; [exact H1 | exact Hb8']. }
assert (Hfn : flat E (SA rb (rk + 1)) (Z.of_nat (S n'))) by (unfold flat, estart in *; cbn [a_base a_off] in *; lia).
destruct (IH (rk + 1)%Z r Hlf Hr Hfn) as (bs' & Hn & Hmap).
exists (Z_to_bv 8 b :: bs'). split.
+ apply rdn_cons1; [exact H1|].
replace (adenot E (SA rb rk) + 1) with (adenot E (SA rb (rk + 1))); [exact Hn|].
unfold adenot, v_addi. cbn [a_base a_off]. rewrite w_add_1, Z_to_bv_unsigned, Z_to_bv64_wrap_l. f_equal. lia.
+ cbn [map]. rewrite Hmap. cbn [map] in Hb8'. injection Hb8' as Hb8''. rewrite Hb8''. reflexivity.
Qed.
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
-
match goal with |- match (match ?lb with _ => _ end) with _ => _ end => destruct lb as [zs|] eqn:Hbl; [|exact I] end.
intros Hscs Hfr.
destruct (log_bytes_lit_sound E base (SE (SA kb kk) w v :: rest) rb n rk zs
ltac:(cbn [log_flat]; split; [exact Hw8 | split; [exact Hfk | exact Hlf']]) Hbl Hfr) as (bs & Hbs & Hmap).
cbn [mem_denot] in Hbs.
exists bs. split; [exact Hbs | split].
+ exact (rdn_length _ _ _ _ _ Hbs).
+ cbn [edenot]. unfold lit_of_bytes. rewrite <- Hmap, zbytes_map. unfold extz. reflexivity.
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
#[using="Type"] Lemma u_lit0 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "9'I'Q9&b4yR0&aNz%2231%5241%83713").
Proof. reflexivity. Qed.
#[using="Type"] Lemma estart_lit0 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "?'U0'Q9'I&\8r2(SH(S=z%211r1%5221%8271%:3;13pQR<<1pRF>1").
Proof. intros E rk. unfold estart. cbn [a_base a_off edenot]. rewrite u_lit0. lia. Qed.
#[using="Type"] Lemma adenot_shift : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q?'U0'Y4'Q9&\:r6r5r3%43321r7%63143'I&\8r8%2219&]8%4237%221:%73?41&]<zr4%3221'aOyR0%211&SMr:%221?&b0r9%5241&QE&]L%11L%311%73<51%J3<91p0@1p0E1p0N1p0Q11pmDQ71pQQ:Q81pQQ8Q91pQQNQ;1po>Q<1pRFQ>1").
Proof.
intros E ka ra nk nr d Hfk Hfr Hst Hd.
rewrite w_add_nat. rewrite Z2Nat.id by exact Hd. apply bv_eq. rewrite (flat_u E _ _ Hfr).
rewrite (flat_u E _ _ Hfk).
destruct Hfk as (?&?&?&?). destruct Hfr as (?&?&?&?).
rewrite u_small by lia. exact Hst.
Qed.
#[using="Type"] Lemma elenZ_lit : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "B'U0'Q9'I&\6r2(S=r1%211%5241&]D&]I+2+R0%3221%5281%=3>71poL?1pRFA1").
Proof. intros E l0. unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Section KLookup.
Variable segs : list Segment.
#[using="Type"] Lemma u8_lit : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='Q9'I&b4y8&aNr1%2231%5241&]D+X0%2251%:3;41pm8<1").
Proof. intros c. rewrite Z_to_bv_unsigned. reflexivity. Qed.
#[using="Type"] Lemma map_unsigned_repeat8 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'Q9'<'I';%114&Q4'aOy8%211&b4%113&Q6&aNr2%2271r1%53821%<49A71&]D+X0%2271%:3E16%D3B51pQPJF1pm8H1").
Proof. intros c n. rewrite map_repeat, u8_lit. reflexivity. Qed.
#[using="Type"] Lemma fill_lit_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q0'U0'6'<'Q9'I'aOyR0%211&TLr4&UDr3r2r1%43321%7261&aN&\9&QD&Q6y8%@11%6229%4321;%611%83>=1%:2D1%G3D<1pm8I1pQPJK1pQT@M1pRFO1").
Proof.
intros E sx n c. unfold fill_lit, lit_of_bytes. cbn [edenot].
rewrite <- map_unsigned_repeat8, zbytes_map. unfold extz. reflexivity.
Qed.
#[using="Type"] Lemma fill_read : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "S2'U0'aOyR0%211'>y8%511%311pQUL51'Y4'<'6'Q9'H&]<zr1%3221&]Ar2%2241%8241'Ir9&aN&]8&\8r:r8%3221%521;%72M1%911(3r4%;2N1%32N1%?3N51p0A1po0K1&\:r6&]Gr5%211%53F41r7%E2D1%Q22C1r;%H21F%915%K221%K24N%M21D%Q9231'J';%11QD%QG11&\HvaDr<&SMr=%221Q6%64541Q;%Q229QC%Q>3921&:%12R0QF%QA3QM1Q@&\9&QD%11QJ%33Q?QD1%QD2R:1&TL&UD%13QCQHQ1%32@1%QK3R>51%R52;1%R62?1qm4J1%M2K1p0O1p0Q71p0Q;1p0QB1pS6R>1pm8R?1pQT@RA1pQPJRC1pQQNRE1po>RF1plJRH1pRFS11").
Proof.
intros E base ka ra n sx c L Hc Hfr Hlo Hhi. exists (repeat (Z_to_bv 8 c) n). split; [|split].
- apply rdn_pointwise; [apply repeat_length | rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia |].
intros j Hj. rewrite (flat_u E _ _ Hfr).
rewrite (nth_indep _ (Z_to_bv 8 0) (Z_to_bv 8 c)) by (rewrite repeat_length; exact Hj).
rewrite nth_repeat.
replace (estart E ra + Z.of_nat j)%Z with (estart E ka + (estart E ra - estart E ka + Z.of_nat j))%Z by lia.
apply Hc. lia.
- apply repeat_length.
- rewrite fill_lit_denot. reflexivity.
Qed.
#[using="Type"] Lemma know_lookupA0_sound : forall E M0 allkn base kn rb rk n sx hints acc,
know_ok segs E M0 allkn ->
know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
match know_lookupA0 allkn segs kn rb rk n sx hints acc with
| LHit v scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs
/\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
| _ => True
end.
Proof.
intros E M0 allkn base kn. induction kn as [|K rest IH]; intros rb rk n sx hints acc Hall Hkn Hn1 Hn8.
{ cbn. exact I. }
apply Forall_cons_iff in Hkn as [HK Hrest].
cbn [know_lookupA0].
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] ulen].
10: { apply IH; assumption. }
5: { apply IH; assumption. }
5: { apply IH; assumption. }
5: { apply IH; assumption. }
5: { apply IH; assumption. }
5: {
cbv zeta. cbn [kentry_ok] in HK. destruct HK as [Hfk Hz].
assert (Hin : flat E (SA rb rk) (Z.of_nat n) ->
(estart E (SA kb kk) <= estart E (SA rb rk))%Z ->
(estart E (SA rb rk) + Z.of_nat n <= estart E (SA kb kk) + elenZ E len)%Z ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (fill_lit sx n fc)).
{ intros Hfr Hlo Hhi. eapply fill_read; eauto. }
assert (Hx : xinside allkn rb rk (elen n) kb kk len = true ->
scs_denot segs base E acc -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (fill_lit sx n fc)).
{ intros Hxi _ Hfr. pose proof (xinside_sound segs E M0 allkn _ _ _ _ _ _ Hall Hxi) as [Hlo Hhi].
rewrite elenZ_elen in Hhi by lia. apply Hin; assumption. }
destruct len as [l0| | | | | | |];
first
[ destruct (rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)) as [d| | |] eqn:Hrel;
[ intros Hscs Hfr; destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (Heqb & Hd & Hkk & Hrn & Hst);
apply Hin; [exact Hfr | lia | rewrite elenZ_lit; unfold estart in *; cbn [a_base a_off] in *; subst; lia]
| apply IH; assumption
| apply IH; assumption
| destruct (xinside allkn rb rk (elen n) kb kk (ELit l0)) eqn:Hxi; [exact (Hx eq_refl)|];
destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin; assumption
| apply IH; assumption ] ]
| destruct (xinside allkn rb rk (elen n) kb kk _) eqn:Hxi; [exact (Hx eq_refl)|];
destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin; assumption
| apply IH; assumption ] ]. }
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
assert (Hx : xinside allkn rb rk (elen n) kb kk len = true ->
scs_denot segs base E acc -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (ELit 0)).
{ intros Hxi _ Hfr. pose proof (xinside_sound segs E M0 allkn _ _ _ _ _ _ Hall Hxi) as [Hlo Hhi].
rewrite elenZ_elen in Hhi by lia. apply Hin; assumption. }
destruct len as [l0| | | | | | |];
first
[ destruct (rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)) as [d| | |] eqn:Hrel;
[ intros Hscs Hfr; destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (Heqb & Hd & Hkk & Hrn & Hst);
apply Hin; [exact Hfr | lia | rewrite elenZ_lit; unfold estart in *; cbn [a_base a_off] in *; subst; lia]
| apply IH; assumption
| apply IH; assumption
| destruct (xinside allkn rb rk (elen n) kb kk (ELit l0)) eqn:Hxi; [exact (Hx eq_refl)|];
destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin; assumption
| apply IH; assumption ] ]
| destruct (xinside allkn rb rk (elen n) kb kk _) eqn:Hxi; [exact (Hx eq_refl)|];
destruct hints as [|[|] hs];
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
| lazymatch goal with |- match (if ?c then _ else _) with _ => _ end =>
destruct c eqn:Hrg;
[ intros Hscs Hfr; apply Hin; [exact Hfr|];
lazymatch type of Hrg with (match erange allkn ?ln with _ => _ end) = true =>
destruct (erange allkn ln) as [[rlo rhi]|] eqn:Her; [|discriminate];
apply Z.leb_le in Hrg;
pose proof (erange_sound segs E M0 allkn ln rlo rhi ltac:(assumption) Her) as Hrb;
unfold elenZ; lia
end
| destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin;
[assumption | unfold estart in Hhi, Hlo |- *; cbn [a_base a_off] in Hhi, Hlo |- *; lia]
| apply IH; assumption ] ]
end ].
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
#[using="Type"] Lemma rdn_one : forall mem (a : word) b,
match mem a with Some b0 => Some b0 | None => seg_rom segs a end = Some b ->
rdn segs mem a 1 = Some [b].
Proof.
intros mem a b H.
change (rdn segs mem a 1) with
(match (match mem a with Some b0 => Some b0 | None => seg_rom segs a end) with
| Some b0 => match rdn segs mem (a + 1) 0 with Some rest => Some (b0 :: rest) | None => None end
| None => None end).
rewrite H. reflexivity.
Qed.
#[using="Type"] Lemma Z_to_bv8_mod : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'Q9'I'aOy8%211&aN&]Dr1+X0%3221%5271%6284%;3821pm8=1").
Proof.
intros c. apply bv_eq. rewrite !u8_lit. apply Z.mod_mod. lia.
Qed.
#[using="Type"] Lemma know_byte_lit_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R6'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'Q9&\<vaDr6r5r4%544321'I%A18&V=r3%249761(3r2%22>1%83741&\:r8(SH%12?>+1%53421'H%K1N%Q111&\H&SMr9%:2IH%3221u1%64M>21(7&aN%12Q:M(=%11Q;%53Q<31%J2?1%Q03?81&]<z%221Q5&]A+X0%22Q81%H241%I281p0K1p0Q21p0Q<1plBQC1pQR<QD1pQR0QF1poFQH1plJQL1pRFR51").
Proof.
intros E base kn. induction kn as [|K rest IH]; intros rb rk b Hkn H Hfr; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
cbn [know_byte_lit] in H.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] ulen];
try exact (IH rb rk b Hrest H Hfr).
-
destruct v as [z| | | | | | |]; try exact (IH rb rk b Hrest H Hfr).
destruct (rel_lit rb rk 1 kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel; try exact (IH rb rk b Hrest H Hfr).
injection H as <-.
cbn [kentry_ok] in HK. destruct HK as (Hkw8 & Hfk & Hrd).
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
split; [|apply Z.mod_pos_bound; lia].
rewrite (adenot_shift E (SA rb kk) (SA rb rk) _ _ d Hfk Hfr Hst ltac:(lia)).
rewrite (rdn_slice segs base w _ _ (Z.to_nat d) 1 Hrd) by lia.
rewrite word_byte_at by lia. cbn [edenot]. rewrite u_lit64. reflexivity.
-
destruct len as [l0| | | | | | |]; try exact (IH rb rk b Hrest H Hfr).
destruct (rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)) as [d| | |] eqn:Hrel; try exact (IH rb rk b Hrest H Hfr).
injection H as <-. split; [|lia].
cbn [kentry_ok] in HK. destruct HK as [Hfk Hz]. rewrite elenZ_lit in Hz.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
apply rdn_one. rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (SA rb rk))), (flat_u E _ _ Hfr), Hst.
rewrite (Hz d) by lia. reflexivity.
-
destruct rb as [z| | | | | | |]; try exact (IH _ rk b Hrest H Hfr).
destruct z; try exact (IH _ rk b Hrest H Hfr).
destruct (Z.leb lo rk && Z.ltb rk hi)%bool eqn:Hr; [|exact (IH _ rk b Hrest H Hfr)].
apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2.
destruct (seg_rom segs (Z_to_bv 64 rk)) as [bb|] eqn:Hrom; [|discriminate]. injection H as <-.
cbn [kentry_ok] in HK. destruct HK as (Hlo0 & Hhi64 & Hnone).
split; [|apply (u8_range bb)].
assert (Ha : adenot E (SA (ELit 0) rk) = Z_to_bv 64 rk).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (SA (ELit 0) rk))), (flat_u E _ _ Hfr), estart_lit0. reflexivity. }
rewrite Ha. rewrite Z_to_bv_bv_unsigned. apply rdn_one. rewrite (Hnone rk) by lia. exact Hrom.
-
destruct len as [l0| | | | | | |]; try exact (IH rb rk b Hrest H Hfr).
destruct (rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)) as [d| | |] eqn:Hrel; try exact (IH rb rk b Hrest H Hfr).
injection H as <-. split; [|apply Z.mod_pos_bound; lia].
cbn [kentry_ok] in HK. destruct HK as [Hfk Hz]. rewrite elenZ_lit in Hz.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
rewrite Z_to_bv8_mod.
apply rdn_one. rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (SA rb rk))), (flat_u E _ _ Hfr), Hst.
rewrite (Hz d) by lia. reflexivity.
Qed.
#[using="Type"] Lemma know_bytes_lit_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R8'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'<'Q9%611&\<vaDr7r6r5%544321'I%C18&V>r3r4%35:8721(3r2%22?1%93841&\:r9(SH%12@9&]G%11A%63531'J%O1Q2'H%Q612&\Hr:&SMr;r8%>21M%4231%74Q161Q0r1%H2<1%O3;31&Q4&b4%11QC%34QCQ;16%Q43Q;1Q6%B261qm4D1%F2E1p0H1p0Q01p0Q;1pQV4QB1pQR<QD1pQPJQF1pQR0QH1poFQJ1plJQN1pRFR71").
Proof.
intros E base kn rb n. induction n as [|n IH]; intros rk zs Hkn H Hfr.
- cbn in H. injection H as <-. exists []. split; reflexivity.
- cbn [know_bytes_lit] in H.
destruct (know_byte_lit segs kn rb rk) as [b|] eqn:Hb; [|discriminate].
destruct (know_bytes_lit segs kn rb (rk + 1) n) as [r|] eqn:Hr; [|discriminate].
injection H as <-.
assert (Hf1 : flat E (SA rb rk) 1) by (unfold flat, estart in *; cbn [a_base a_off] in *; lia).
destruct (know_byte_lit_sound E base kn rb rk b Hkn Hb Hf1) as [H1 Hb8].
assert (Hb8' : map bv_unsigned [Z_to_bv 8 b] = [b]).
{ cbn [map]. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia. }
destruct n as [|n'].
{ cbn in Hr. injection Hr as <-. exists [Z_to_bv 8 b]. split; [exact H1 | exact Hb8']. }
assert (Hfn : flat E (SA rb (rk + 1)) (Z.of_nat (S n'))) by (unfold flat, estart in *; cbn [a_base a_off] in *; lia).
destruct (IH (rk + 1)%Z r Hkn Hr Hfn) as (bs' & Hn & Hmap).
exists (Z_to_bv 8 b :: bs'). split.
+ apply rdn_cons1; [exact H1|].
replace (adenot E (SA rb rk) + 1) with (adenot E (SA rb (rk + 1))); [exact Hn|].
unfold adenot, v_addi. cbn [a_base a_off]. rewrite w_add_1, Z_to_bv_unsigned, Z_to_bv64_wrap_l. f_equal. lia.
+ cbn [map]. rewrite Hmap. cbn [map] in Hb8'. injection Hb8' as Hb8''. rewrite Hb8''. reflexivity.
Qed.
#[using="Type"] Lemma know_lookupA_sound : forall E M0 allkn base kn rb rk n sx hints acc,
know_ok segs E M0 allkn ->
know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
match know_lookupA allkn segs kn rb rk n sx hints acc with
| LHit v scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs
/\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
| _ => True
end.
Proof.
intros E M0 allkn base kn rb rk n sx hints acc Hall Hkn Hn1 Hn8. unfold know_lookupA.
pose proof (know_lookupA0_sound E M0 allkn base kn rb rk n sx hints acc Hall Hkn Hn1 Hn8) as H0.
destruct (know_lookupA0 allkn segs kn rb rk n sx hints acc) as [v scs h|scs h|]; [exact H0 | | exact I].
destruct (know_bytes_lit segs kn rb rk n) as [zs|] eqn:Hbl; [|exact I].
intros Hscs Hfr.
destruct (know_bytes_lit_sound E base kn rb n rk zs Hkn Hbl Hfr) as (bs & Hbs & Hmap).
exists bs. split; [exact Hbs | split].
- exact (rdn_length _ _ _ _ _ Hbs).
- cbn [edenot]. unfold lit_of_bytes. rewrite <- Hmap, zbytes_map. unfold extz. reflexivity.
Qed.
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
intros E base kn rb rk n sx hints acc Hkn Hn1 Hn8. unfold know_lookup.
apply (know_lookupA_sound E base kn base kn); assumption.
Qed.
End KLookup.
#[using="Type"] Lemma Z_to_bv64_u : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='Q9'I'aOyR0%211&aN&b4r1%3251%3261%5271%:3713pQV2<1").
Proof. intros z. apply Z_to_bv_bv_unsigned. Qed.
#[using="Type"] Lemma Z_to_bv64_mod : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "A'Q9'I'aOyR0%211&aN&]Dr1&]I+2+R0%3221%6251%82:1%92;7%>3;21pQV2@1").
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia.
Qed.
#[using="Type"] Lemma to_saddr_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "F'U0'U9'Q9'I'aOyR0%211&SMr3&Z;r2r1%3221%6251&\I&TL%1286%3216%?3<51po4A1pmJC1pRFE1").
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
#[using="Type"] Lemma and_highmask_val : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'aOyR0%211'Q9&]<zr1%3221&]Ar2+R0%3221'I&S1(R6r4&aN&]H&]I+2r3%3221%511%72F1%;3:91&]J&b4%12J<&]D%1228%5231%?2N1%D3N81p0F1p0K1po6Q01pQU8Q21").
Proof.
intros v j Hj Hj64. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j < 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
assert (Hm : ((- 2 ^ j) mod 2 ^ 64 = 2 ^ 64 - 2 ^ j)%Z).
{ rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
rewrite Hm. f_equal. apply land_highmask; lia.
Qed.
#[using="Type"] Lemma and_mask_id : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q6'aOyR0%211'Q9&]<zr1%3221&]Ar2+R0%3221'I&]D&b4r4%22?1&]I+2r3%3221%8251%:3C1A&S1(R6r5&aN&]H%;2:=%211%42M1%83761%D3N17p0;1p0G1p0L1po6Q11pQU8Q31").
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
#[using="Type"] Lemma and_lowmask_zero : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q6'aOyR0%211'Q9&]<zr1%3221r2+R0%6221&]:&]I+2r3%3221&b4r4%22A1%8241'I&S1(R6r5&aN&]J%>2=9+1%3221%52L1%93871%72NJ%<3N21p0>1p0H1p0L1po6Q11pQU8Q31").
Proof.
intros v j Hj Hj64 Hd. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j <= 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
rewrite (Z.mod_small (2 ^ j - 1)) by lia.
replace (2 ^ j - 1)%Z with (Z.ones j) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
rewrite Z.land_ones by lia. rewrite (Znumtheory.Zdivide_mod _ _ Hd). reflexivity.
Qed.
#[using="Type"] Lemma coeffs_divk_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QA';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'Q9'A'U9%2231%B11&\<r6r5r4r3%544321&]Az%2214'I'6&T?%13:98(C%53421&]D&\Br8%221?%421A%;3I1=p071p0>1p0B1pQTJI1pQP<N1poFQ01pV@Q31pRFQ<1pQS:Q>1").
Proof.
intros segs E M kn m ts Hkn Hm. induction ts as [|[k a] rest IH]; cbn [coeffs_divk tden]; intros H.
- apply Z.mod_0_l. lia.
- apply andb_prop in H as [H1 H2]. specialize (IH H2).
assert (Hka : ((k * uE E a) mod m = 0)%Z).
{ apply orb_prop in H1 as [H1|H1]; apply Z.eqb_eq in H1.
- rewrite Z.mul_mod, H1, Z.mul_0_l, Z.mod_0_l by lia. reflexivity.
- destruct (ealign_sound segs E M kn a Hkn) as [Hr [q Hq]]. unfold uE. rewrite Hq.
replace (k * (q * 2 ^ ealign kn a))%Z with (q * (k * 2 ^ ealign kn a))%Z by ring.
rewrite Z.mul_mod, H1, Z.mul_0_r, Z.mod_0_l by lia. reflexivity. }
rewrite Z.add_mod, Hka, IH, Z.add_0_l, Z.mod_0_l by lia. reflexivity.
Qed.
#[using="Type"] Lemma lin_lowbits_kn_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QO';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'H&]<zr3%3221+R0%5231%7231'I%H1@&VO%13?>=(3%12D:%63531&]D&b4&TLr9%221G%42Q51&]I+2%221J%9241%A3Q01K%I2HL&]A%12N5%M231%N251p0A1p0I1p0Q21pQU8Q91po8Q:1pmJQ<1poFQ>1pV@QA1pRFQJ1pQS:QL1").
Proof.
intros segs E M kn e k v Hkn Hk H. unfold lin_lowbits_kn in H.
assert (Hp : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
destruct (lin_of e) as [c ts] eqn:Hl. cbn [fst snd] in H.
destruct (coeffs_divk kn (2 ^ k) ts) eqn:Hd.
2:{
exact (pageup_low_sound E e (2 ^ k) k v Hk eq_refl H). }
injection H as <-.
pose proof (lin_of_sound E e) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs. unfold uE in Hs.
split; [|apply Z.mod_pos_bound; lia].
rewrite <- (eqm_mod_pow2 _ _ k Hk Hs). rewrite Z.add_mod, (coeffs_divk_sound segs E M kn _ ts Hkn Hp Hd), Z.add_0_r, Z.mod_mod by lia.
reflexivity.
Qed.
#[using="Type"] Lemma ldiv_terms_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'U0'Q9';'A'U9%2241%411&]Azr2%3221'I'6&T>r3%2216(C%63521&\Br5%2216&]Er4&VG%122:%7261%5241%@3J71p0;1p0C1pQTJH1pQP<N1pRFQ01").
Proof.
intros E m ts Hm. induction ts as [|[k a] rest IH]; cbn [coeffs_div ldiv_terms tden]; intros H.
- lia.
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH H2).
pose proof (Z.div_mod k m ltac:(lia)). nia.
Qed.
#[using="Type"] Lemma wrap64_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'Q9'I&Z@r1%211&]D&Z=%2241%73841pQV291").
Proof.
intros z. unfold wrap64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:H; [|reflexivity].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. symmetry. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma u_swrap32 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "B'Q9'I&b4yR0&aN&b3yQ0r1%3221%5261%8271&YM&]D+TPPPPP0%2271%411%?3@61pQTFA1").
Proof.
intros t. rewrite u_lit64. unfold bv_swrap, bv_wrap, sx32.
change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z. unfold two64.
pose proof (Z.mod_pos_bound t 4294967296 ltac:(lia)) as Hr.
set (r := (t mod 4294967296)%Z) in *.
assert (E : ((t + 2147483648) mod 4294967296 = (r + 2147483648) mod 4294967296)%Z).
{ subst r. rewrite <- Zplus_mod_idemp_l. reflexivity. }
rewrite E. destruct (Z.ltb_spec r 2147483648).
- rewrite (Z.mod_small (r + 2147483648)) by lia. rewrite Z.add_simpl_r. apply Z.mod_small. lia.
- replace (r + 2147483648)%Z with (r - 2147483648 + 1 * 4294967296)%Z by lia.
rewrite Z.mod_add by lia. rewrite (Z.mod_small (r - 2147483648)) by lia.
replace (r - 2147483648 - 2147483648)%Z with (r + 18446744069414584320 + (-1) * 18446744073709551616)%Z by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma zfast_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'RF'Q9'H&]<zr2%3221&]A&Z=%2241%8241'I&[2r5r4r3%43321&ZJ%13543%83B31p0:1p0;1pQUNE1pQULF1pQQ@H1").
Proof.
intros op x y Hx Hy. unfold two64 in Hx, Hy.
pose proof (u_small x Hx) as Ux. pose proof (u_small y Hy) as Uy.
destruct op; cbn [zfast]; try reflexivity; unfold zalu.
- rewrite u_add64, Ux, Uy. unfold two64. destruct (Z.ltb_spec (x + y) (2 ^ 64)).
+ symmetry. apply Z.mod_small. lia.
+ replace (x + y)%Z with ((x + y - 2 ^ 64) + 1 * 2 ^ 64)%Z at 2 by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
- rewrite u_sub64, Ux, Uy. unfold two64. destruct (Z.leb_spec 0 (x - y)).
+ symmetry. apply Z.mod_small. lia.
+ replace (x - y)%Z with ((x - y + 2 ^ 64) + (-1) * 2 ^ 64)%Z at 2 by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
- rewrite land64_eq, land_63, u_sll64, Ux, Uy, Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
- rewrite u_sltu64, Ux, Uy. reflexivity.
- rewrite u_xor64, Ux, Uy. reflexivity.
- rewrite land_63, u_srl64, Ux, Uy, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
- rewrite u_or64, Ux, Uy. reflexivity.
- rewrite u_and64, Ux, Uy. reflexivity.
Qed.
#[using="Type"] Lemma zfastw_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'RF'Q9'H&]<zr2%3221&]A&Z=%2241%8241'I&[4r5r4r3%43321&ZL%13543%83B31p0:1p0;1pQUNE1pQULF1pQQ@H1").
Proof.
intros op x y Hx Hy. unfold two64 in Hx, Hy.
pose proof (u_small x Hx) as Ux. pose proof (u_small y Hy) as Uy.
destruct op; cbn [zfastw]; try reflexivity; unfold zaluw; rewrite ?land32_eq, ?land_31.
- rewrite w_addw. unfold v_addw. rewrite u_swrap32, Ux, Uy. reflexivity.
- rewrite w_subw. unfold v_subw. rewrite u_swrap32, Ux, Uy. reflexivity.
- rewrite w_sllw. unfold v_sllw. rewrite u_swrap32, Ux, Uy. f_equal.
rewrite !Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
rewrite Zmult_mod_idemp_l. reflexivity.
- rewrite w_srlw. unfold v_srlw. rewrite u_swrap32, Ux, Uy, bv_wrap32_mod. f_equal.
change (2 ^ 32)%Z with 4294967296%Z.
symmetry. apply Z.mod_small. rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)).
assert (0 < 2 ^ (y mod 32))%Z by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
#[using="Type"] Lemma zfastm_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'RL'Q9'H&]<zr2%3221&]A&Z=%2241%8241'I&[3r5r4r3%43321&[6%13543%83B31p0:1p0;1pQUNE1pQULF1pQQ@H1").
Proof.
intros op x y Hx Hy. unfold two64 in Hx, Hy.
destruct op; cbn [zfastm]; try reflexivity. rewrite land64_eq. unfold zmd. rewrite u_mul64, !u_small by lia. reflexivity.
Qed.
#[using="Type"] Lemma wrap64_range : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='Q9'H&]<z&Z@r1%211%5241&]A&Z=%2241%:241pQV2<1").
Proof. intros z. rewrite wrap64_eq. unfold two64. apply Z.mod_pos_bound. lia. Qed.
#[using="Type"] Lemma Z_to_bv_wrap64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='Q9'I'aOyR0%211&aN&Z@r1%211%4261%5273%:3721pQV2<1").
Proof.
intros z. apply bv_eq. rewrite !u_lit64, wrap64_eq. unfold two64. rewrite Z.mod_mod by lia. reflexivity.
Qed.
#[using="Type"] Lemma zalu_l_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'RF'Q9'I&ZKr3r2r1%43321&ZJ%13543%83931pQUN:1pQUL;1pQQ@=1").
Proof. intros. unfold zalu_l. rewrite zfast_eq by apply wrap64_range. unfold zalu. rewrite !Z_to_bv_wrap64. reflexivity. Qed.
#[using="Type"] Lemma zaluw_l_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'RF'Q9'I&ZMr3r2r1%43321&ZL%13543%83931pQUN:1pQUL;1pQQ@=1").
Proof. intros. unfold zaluw_l. rewrite zfastw_eq by apply wrap64_range. unfold zaluw. rewrite !Z_to_bv_wrap64. reflexivity. Qed.
#[using="Type"] Lemma zmd_l_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'RL'Q9'I&[7r3r2r1%43321&[6%13543%83931pQUN:1pQUL;1pQQ@=1").
Proof. intros. unfold zmd_l. rewrite zfastm_eq by apply wrap64_range. unfold zmd. rewrite !Z_to_bv_wrap64. reflexivity. Qed.
#[using="Type"] Lemma mkAlu_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'U0'RF'U9'I'aOyR0%211&TLr4&WGr3r2r1%43321%7261&S1%9285%:295%33821%@3=51plBB1pkNC1pQQ@E1pRFG1").
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
+ apply is_lit_some in Hb. subst b. cbn [edenot]. rewrite zalu_l_eq. unfold zalu. apply Z_to_bv_bv_unsigned.
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
#[using="Type"] Lemma end_hi_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R7';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r;r:r9r8%544321'I'A%1299%B11&T7%1287(3(@r5r4%34AA21%5291%<3971%L1D&ZCr7%22D1%;2H8%B3521&TNr6%27JIHG61=%F3915&]<&]8&\8r>(SH%12Q1Q0%4231&\6%125Q2%8231%:21Ip0<1p0A1p0H1p0Q61pmJQ=1pn@Q>1pnFQ?1pQP8Q@1pQPJQB1po8QB1plBQD1poFQF1pV@QI1pRFR21pQS:R41").
Proof.
intros segs E M kn b k n lo1 hi1 h1 e Hkn Hb Hx H. unfold end_hi in H.
assert (GEN : (if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
then match find_range (facts_of kn) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
| Some (_, ehi) => Some ehi
| None => None
end
else None) = Some e -> (estart E (SA b k) + elenZ E n <= e)%Z).
2: { destruct n; [discriminate | apply GEN; exact H ..]. }
clear H. intros H.
destruct (Z.leb_spec 0 (lo1 + k)) as [Hlo|Hlo]; [|discriminate].
destruct (Z.ltb_spec (hi1 + k + h1) two64) as [Hhi|Hhi]; [|discriminate].
destruct (find_range (facts_of kn) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n)) as [[elo ehi]|] eqn:Hf; [|discriminate].
injection H as <-.
pose proof (find_range_sound segs E M (facts_of kn) _ elo ehi (facts_of_ok segs E M kn Hkn) Hf) as [_ B].
rewrite !mkAlu_denot in B. cbn [alu64 alu edenot] in B. rewrite !bv_add_unsigned, u_lit64 in B.
pose proof (base_range_sound segs E M kn b lo1 hi1 Hkn Hb) as [A1 B1].
pose proof (xhi_sound segs E M kn n h1 Hkn Hx) as Xn.
pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn.
unfold estart, elenZ. cbn [a_base a_off]. unfold bv_wrap in B. change (bv_modulus 64) with two64 in B. unfold two64 in *.
rewrite (Zplus_mod_idemp_r k (bv_unsigned (edenot E b)) (2 ^ 64)) in B.
rewrite (Z.mod_small (bv_unsigned (edenot E b) + k) (2 ^ 64)) in B by lia.
rewrite Z.mod_small in B by lia. lia.
Qed.
#[using="Type"] Lemma ranges_apart_x_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QO';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r:r9r8r7%544321'I'6&XIr6r5r4r3r2%67;:54321(C%:3921'M&]<&]8&\8r;(SH%12DC%4231&\6%125A%8231%62BA%9281%<231%62:C%=231%?219%A241p0C1p0O1pQQ0Q71po<Q71plHQ91pQPNQ:1po:Q:1plFQ<1poFQ>1pV@QA1pRFQJ1pQS:QL1").
Proof.
intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold ranges_apart_x in H.
assert (LIT : forall z1 z2, n1 = ELit z1 -> n2 = ELit z2 ->
ranges_apart kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2) = true ->
((estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2))%Z
\/ (estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1))%Z)).
{ intros z1 z2 -> -> HL. pose proof (ranges_apart_sound segs E M kn b1 k1 _ b2 k2 _ Hkn HL) as A.
rewrite !zlit64_eq in A. unfold elenZ. cbn [edenot]. rewrite !u_lit64. exact A. }
assert (GEN :
(if match base_range kn b1, base_range kn b2, xhi kn n1, xhi kn n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else
if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end then true
else if kdisj_apart_x kn kn b1 k1 n1 b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]) = true ->
((estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2))%Z
\/ (estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1))%Z)).
2:{ destruct n1; [destruct n2; [eapply LIT; [reflexivity | reflexivity | exact H] | ..] |..]; apply GEN; exact H. }
clear H. intros H.
lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc1 end.
2: { lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc2 end.
{ eapply kdisj_apart_x_sound; eassumption. }
destruct (negb (shares_var b1 b2)); [discriminate|].
lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc3 end.
{ pose proof (lin_ge0_sound segs E M kn _ _ Hkn Hc3) as A. cbn [xt_den] in A.
unfold estart, elenZ. cbn [a_base a_off]. lia. }
pose proof (lin_ge0_sound segs E M kn _ _ Hkn H) as A. cbn [xt_den] in A.
unfold estart, elenZ. cbn [a_base a_off]. lia. }
clear H. rename Hc1 into H.
- destruct (base_range kn b1) as [[lo1 hi1]|] eqn:H1; [|discriminate].
destruct (base_range kn b2) as [[lo2 hi2]|] eqn:H2; [|discriminate].
destruct (xhi kn n1) as [h1|] eqn:X1; [|discriminate].
destruct (xhi kn n2) as [h2|] eqn:X2; [|discriminate].
pose proof (base_range_sound segs E M kn b1 lo1 hi1 Hkn H1) as [A1 B1].
pose proof (base_range_sound segs E M kn b2 lo2 hi2 Hkn H2) as [A2 B2].
pose proof (xhi_sound segs E M kn n1 h1 Hkn X1). pose proof (xhi_sound segs E M kn n2 h2 Hkn X2).
lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hnum end.
{ unfold estart, elenZ. cbn [a_base a_off]. apply orb_prop in Hnum as [Hn|Hn]; apply Z.leb_le in Hn; lia. }
lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:He1 end.
{ destruct (end_hi kn b1 k1 n1 lo1 hi1 h1) as [e1|] eqn:E1; [|discriminate]. apply Z.leb_le in He1.
pose proof (end_hi_sound segs E M kn b1 k1 n1 lo1 hi1 h1 e1 Hkn H1 X1 E1) as HE. left.
unfold estart, elenZ in *. cbn [a_base a_off] in *. lia. }
destruct (end_hi kn b2 k2 n2 lo2 hi2 h2) as [e2|] eqn:E2; [|discriminate]. apply Z.leb_le in H.
pose proof (end_hi_sound segs E M kn b2 k2 n2 lo2 hi2 h2 e2 Hkn H2 X2 E2) as HE. right.
unfold estart, elenZ in *. cbn [a_base a_off] in *. lia.
Qed.
#[using="Type"] Lemma mkAluw_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N'U0'RF'U9'I'aOyR0%211&TLr4&WJr3r2r1%43321%7261&RNyQ0&S0&S5%<2;8%211%>2=9%411%63=31%938C1%F3C;1plBH1pkNI1pQQ@K1pRFM1").
Proof.
intros E op a b. unfold mkAluw.
assert (Hsh : (op = ALU_SLL \/ op = ALU_SRL \/ op = ALU_SRA) ->
edenot E (match is_lit b with
| Some _ => EAluw op a b
| None => match shamt_of b 5 with
| Some s => match is_lit a with
| Some x => ELit (zaluw_l op x s)
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
[ apply is_lit_some in Ha; subst a; cbn [edenot]; rewrite zaluw_l_eq; unfold zaluw; rewrite Z_to_bv_bv_unsigned; apply Heq
| cbn [edenot]; apply Heq ]. }
destruct (is_lit a) as [x|] eqn:Ha.
- destruct (is_lit b) as [y|] eqn:Hb.
+ apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. rewrite zaluw_l_eq. unfold zaluw.
apply Z_to_bv_bv_unsigned.
+ destruct op; try reflexivity; apply Hsh; tauto.
- destruct (is_lit b); (destruct op; try reflexivity; apply Hsh; tauto).
Qed.
#[using="Type"] Lemma mkMd_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'U0'RL'U9'I'aOyR0%211&TLr4&X1r3r2r1%43321%7261&S6%9285%:295%34=821%@3=51plBB1pkNC1pQQ@E1pRFG1").
Proof.
intros E op a b. unfold mkMd.
destruct (is_lit a) as [x|] eqn:Ha; [apply is_lit_some in Ha; subst a|];
(destruct (is_lit b) as [y|] eqn:Hb; [apply is_lit_some in Hb; subst b|]).
- cbn [edenot]. rewrite zmd_l_eq. unfold zmd. apply Z_to_bv_bv_unsigned.
- destruct op; try reflexivity. cbn [edenot]. apply unlin_lmul_l.
- destruct op; try reflexivity. cbn [edenot]. apply unlin_lmul_r.
- reflexivity.
Qed.
#[using="Type"] Lemma mkMdw_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N'U0'RL'U9'I'aOyR0%211&TLr4&X3r3r2r1%43321%7261&RNyQ0&S6&S5%<2;8%211%>2=9%411%647=31%938C1%F3C;1plBH1pkNI1pQQ@K1pRFM1").
Proof.
intros E op a b. unfold mkMdw.
destruct (is_lit a) as [x|] eqn:Ha; [|reflexivity].
destruct (is_lit b) as [y|] eqn:Hb; [|reflexivity].
apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. unfold zmdw.
apply Z_to_bv_bv_unsigned.
Qed.
#[using="Type"] Lemma mkSrl_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QB';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'I&]D&b4r2%22E1+R0%5221r3%83?21&TLr8&X5%13@?>%4231&S1(R:%726C%3321:%B3Q251p0;1p0E1pQUNQ51pQS>M1pkNO1poFQ11pV@Q41pRFQ=1pQS:Q?1").
Proof.
intros segs E M kn a sh y Hkn Hy. unfold mkSrl.
pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as Hsr. rewrite Hy in Hsr.
assert (Hlit : edenot E (mkAlu ALU_SRL a (ELit sh)) = alu64 ALU_SRL (edenot E a) y).
{ rewrite mkAlu_denot. cbn [edenot]. apply alu_srl_amt. rewrite (u_lit_mod sh 64) by lia. symmetry; exact Hy. }
match goal with |- edenot E (if ?c then _ else _) = _ => destruct c eqn:Hc end.
2: {
destruct (if (negb (lin_trivial (lin_of a)) && lin_nowrap kn a)%bool then lsplit_divc (2 ^ sh) (snd (lin_of a)) else ([], []))
as [dts rts] eqn:Hsp.
destruct dts as [|d1 dts']; [exact Hlit|]. destruct rts as [|r1 rts']; [exact Hlit|].
destruct (negb (lin_trivial (lin_of a)) && lin_nowrap kn a)%bool eqn:Hnw; [|discriminate].
apply andb_prop in Hnw as [_ Hnw].
destruct (if lin_nowrap_l kn (fst (lin_of a)) (r1 :: rts') then erange kn (unlin (fst (lin_of a), r1 :: rts')) else None)
as [[lo hi]|] eqn:Her; [|exact Hlit].
destruct (lin_nowrap_l kn (fst (lin_of a)) (r1 :: rts')) eqn:Hnr; [|discriminate].
destruct (Z.eqb (lo / 2 ^ sh) (hi / 2 ^ sh)) eqn:Hq; [|exact Hlit]. apply Z.eqb_eq in Hq.
assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (SPLIT : forall m ts d r, lsplit_divc m ts = (d, r) ->
coeffs_div m d = true /\ forall E0, tden E0 ts = (tden E0 d + tden E0 r)%Z).
{ intros m ts. induction ts as [|[k a0] rest IH]; intros d r H.
- cbn in H. injection H as <- <-. split; [reflexivity | intros; cbn; lia].
- cbn [lsplit_divc] in H. destruct (lsplit_divc m rest) as [d0 r0] eqn:Hs0.
destruct (IH d0 r0 eq_refl) as [Hd Hsum].
destruct (Z.eqb (k mod m) 0) eqn:Hk; injection H as <- <-.
+ split; [cbn [coeffs_div]; rewrite Hk, Hd; reflexivity|]. intros E0. cbn [tden]. rewrite Hsum. lia.
+ split; [exact Hd|]. intros E0. cbn [tden]. rewrite Hsum. lia. }
destruct (SPLIT _ _ _ _ Hsp) as [Hdiv Hsum].
pose proof (lin_nowrap_sound segs E M kn a Hkn Hnw) as Hval. rewrite (Hsum E) in Hval.
set (c := fst (lin_of a)) in *.
unfold lin_nowrap_l in Hnr.
destruct (lin_range (erange kn) c (r1 :: rts')) as [[lo2 hi2]|] eqn:Hlr; [|discriminate].
apply andb_prop in Hnr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
pose proof (lin_range_sound E (erange kn) (fun a0 lo0 hi0 Ha => erange_sound segs E M kn a0 lo0 hi0 Hkn Ha) _ _ _ _ Hlr) as HR.
assert (HuR : bv_unsigned (edenot E (unlin (c, r1 :: rts'))) = (c + tden E (r1 :: rts'))%Z).
{ pose proof (unlin_sound E (c, r1 :: rts')) as [q Hq']. unfold lden, uE in Hq'. cbn [fst snd] in Hq'.
pose proof (u64_range (edenot E (unlin (c, r1 :: rts')))). nia. }
pose proof (erange_sound segs E M kn _ lo hi Hkn Her) as HRr. rewrite HuR in HRr.
rewrite (ldiv_terms_sound E (2 ^ sh) (d1 :: dts') Hp Hdiv) in Hval.
set (A := tden E (ldiv_terms (2 ^ sh) (d1 :: dts'))) in *. set (T := tden E (r1 :: rts')) in *.
pose proof (Z.div_le_mono lo (c + T) (2 ^ sh) Hp ltac:(lia)) as D1.
pose proof (Z.div_le_mono (c + T) hi (2 ^ sh) Hp ltac:(lia)) as D2.
rewrite alu_srl. unfold v_srl. rewrite Hy, Z.shiftr_div_pow2, Hval by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd]. fold A.
replace (c + (2 ^ sh * A + T))%Z with (A * 2 ^ sh + (c + T))%Z by lia. rewrite Z.div_add_l by lia.
exists 0%Z. lia. }
apply andb_prop in Hc as [Hc Hnw].
apply andb_prop in Hc as [Htriv Hdiv].
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
rewrite Z.div_add_l by lia. lia.
Qed.
#[using="Type"] Lemma and_highmask_srl : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QN';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r6r5r4r3%544321&]<zr2%3221&]A+R0%2281'I&TLr8&X1(RA(S=&]I+2%221B%411&X5%13GFE%93831%<2;1&aN&]J&b4%@2?L%22Q:1&]D%122<%6231%82Q>1%G3Q>:1p0I1p0M1p0Q21po6Q91pkNQ;1poFQ=1pV@Q@1pRFQI1pQS:QK1").
Proof.
intros segs E M kn a j Hkn Hj Hj64. rewrite mkMd_denot. cbn [edenot].
rewrite (mkSrl_denot segs E M kn a j (Z_to_bv 64 j) Hkn) by (rewrite u_small by lia; apply Z.mod_small; lia).
rewrite m_mul, alu_srl. unfold v_mul, v_srl.
rewrite (u_small j) by lia. rewrite (Z.mod_small j 64) by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
pose proof (u64_range (edenot E a)) as Ha. set (x := bv_unsigned (edenot E a)) in *.
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hp64 : (2 ^ j < 2 ^ 64)%Z) by (apply Z.pow_lt_mono_r; lia).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hmb.
assert (Hq : (0 <= x / 2 ^ j <= x)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
rewrite (Z.mod_small (2 ^ j)) by lia. rewrite (Z.mod_small (x / 2 ^ j)) by lia.
f_equal. lia.
Qed.
#[using="Type"] Lemma land_mod_pow2 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'Q9&]<zr1%3221'I&]D&];r4r3%3221&]I+2r2%3221%9251%:282%;283%;221%>3C41p0@1po6E1pQUNF1pQULG1").
Proof.
intros x y j Hj. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. apply Z.land_spec.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
#[using="Type"] Lemma lor_mod_pow2 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'Q9&]<zr1%3221'I&]D&]@r4r3%3221&]I+2r2%3221%9251%:282%;283%;221%>3C41p0@1po6E1pQUNF1pQULG1").
Proof.
intros x y j Hj. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. apply Z.lor_spec.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
#[using="Type"] Lemma lxor_mod_pow2 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'Q9&]<zr1%3221'I&]D&]Cr4r3%3221&]I+2r2%3221%9251%:282%;283%;221%>3C41p0@1po6E1pQUNF1pQULG1").
Proof.
intros x y j Hj. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. apply Z.lxor_spec.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
#[using="Type"] Lemma mod_pow2_mod_pow2 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'Q9'H&]<zr2%3221r1%5231%7231'I&]Dr4&]I+2%221:%5241r3%5241%8231%9282%;3D21p0=1po8F1po6G1pQULH1").
Proof.
intros x j k H. rewrite <- Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
- reflexivity.
- exists (2 ^ (k - j))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
#[using="Type"] Lemma lowbits_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QJ';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r7r6r5r4%544321'H&]<zr3%3221+R0%5231%7231'I%H1@&W?%13?>=(3%12D:%63531&]D&b4&TLr9%221G%42Q51&]I+2%221J%9241%A3Q01Kp0<1p0D1p0M1pQU8Q41po6Q51pmJQ71poFQ91pV@Q<1pRFQE1pQS:QG1").
Proof.
intros segs E M kn e j. intros v Hkn Hj. revert v.
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hdflt : forall e' v,
(if Z.leb j (ealign kn e') then Some 0%Z else lin_lowbits_kn kn e' j) = Some v ->
(bv_unsigned (edenot E e') mod 2 ^ j = v)%Z).
{ intros e' v H. destruct (Z.leb j (ealign kn e')) eqn:Hle.
- injection H as <-. apply Z.leb_le in Hle.
destruct (ealign_sound segs E M kn e' Hkn) as [Hr Hdv].
apply Znumtheory.Zdivide_mod. eapply Z.divide_trans; [apply pow2_divide_le | exact Hdv]. lia.
- exact (proj1 (lin_lowbits_kn_sound segs E M kn e' j v Hkn Hj H)). }
assert (Hlit : forall c, ((bv_unsigned (edenot E (ELit c))) mod 2 ^ j = (c mod two64) mod 2 ^ j)%Z).
{ intros c. cbn [edenot]. rewrite u_lit64. reflexivity. }
assert (M64 : forall x, ((x mod 2 ^ 64) mod 2 ^ j = x mod 2 ^ j)%Z) by (intros x; apply mod_pow2_mod_pow2; lia).
induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
intros v H; cbn [lowbits] in H; try exact (Hdflt _ _ H).
- injection H as <-. apply Hlit.
-
destruct op; try exact (Hdflt _ _ H).
+
destruct (lowbits kn a j) as [x|] eqn:Ha; [|exact (Hdflt _ _ H)].
destruct (lowbits kn b j) as [y|] eqn:Hb; [|exact (Hdflt _ _ H)].
injection H as <-. cbn [edenot]. rewrite u_add64, M64.
rewrite Z.add_mod by lia. rewrite (IHa x eq_refl), (IHb y eq_refl). reflexivity.
+
destruct (lowbits kn a j) as [x|] eqn:Ha; [|exact (Hdflt _ _ H)].
destruct (lowbits kn b j) as [y|] eqn:Hb; [|exact (Hdflt _ _ H)].
injection H as <-. cbn [edenot]. rewrite u_sub64, M64.
rewrite Zminus_mod. rewrite (IHa x eq_refl), (IHb y eq_refl). reflexivity.
+
destruct b as [c| | | | | | |]; try exact (Hdflt _ _ H).
destruct (lowbits kn a j) as [x|] eqn:Ha; [|exact (Hdflt _ _ H)].
injection H as <-. cbn [edenot]. rewrite u_xor64, lxor_mod_pow2 by lia.
rewrite (IHa x eq_refl). cbn [edenot] in Hlit. rewrite <- (Hlit c). cbn [edenot]. reflexivity.
+
destruct b as [c| | | | | | |]; try exact (Hdflt _ _ H).
destruct (lowbits kn a j) as [x|] eqn:Ha; [|exact (Hdflt _ _ H)].
injection H as <-. cbn [edenot]. rewrite u_or64, lor_mod_pow2 by lia.
rewrite (IHa x eq_refl). rewrite <- (Hlit c). cbn [edenot]. reflexivity.
+
destruct b as [c| | | | | | |]; try exact (Hdflt _ _ H).
destruct (Z.eqb ((c mod two64) mod 2 ^ j) 0) eqn:Hz.
{ injection H as <-. apply Z.eqb_eq in Hz. cbn [edenot]. rewrite u_and64, land_mod_pow2 by lia.
rewrite u_lit64, Hz. apply Z.land_0_r. }
destruct (lowbits kn a j) as [x|] eqn:Ha; [|exact (Hdflt _ _ H)].
injection H as <-. cbn [edenot]. rewrite u_and64, land_mod_pow2 by lia.
rewrite (IHa x eq_refl). rewrite <- (Hlit c). cbn [edenot]. reflexivity.
-
destruct op; try exact (Hdflt _ _ H).
destruct a as [c| | | | | | |]; try exact (Hdflt _ _ H).
destruct (Z.eqb ((c mod two64) mod 2 ^ j) 0) eqn:Hz.
{ injection H as <-. apply Z.eqb_eq in Hz. cbn [edenot].
rewrite (eqm_mod_pow2 _ _ j Hj (u_mul_eqm _ _)). rewrite u_lit64.
rewrite Z.mul_mod, Hz, Z.mul_0_l, Z.mod_0_l by lia. reflexivity. }
destruct (lowbits kn b j) as [y|] eqn:Hb; [|exact (Hdflt _ _ H)].
injection H as <-. cbn [edenot].
rewrite (eqm_mod_pow2 _ _ j Hj (u_mul_eqm _ _)). rewrite u_lit64.
rewrite Z.mul_mod, (IHb y eq_refl) by lia.
unfold two64. rewrite M64. apply Z.mul_mod_idemp_l. lia.
Qed.
#[using="Type"] Lemma lsplit_div_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q;';'V7%211'Q9'A'U9%2231%711'I%5222&WBr5r4r3%43321(@r2r1%34;;21%;3:51'H'6&T?r6%231=;(C%B3521'U0&\B%12<B&]8%32>C%42?C%3221%J3O51pRF81%@2:1p0B1pQRNO1pmHQ01pQTJQ11pQP<Q61poFQ81").
Proof.
intros kn m ts. induction ts as [|[k a] rest IH]; intros dts rts H.
- cbn in H. injection H as <- <-. split; [reflexivity | intros; cbn; lia].
- cbn [lsplit_div] in H. destruct (lsplit_div kn m rest) as [d r] eqn:Hs.
destruct (IH d r eq_refl) as [Hd Hsum].
destruct (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0)%bool eqn:Hc; injection H as <- <-.
+ split; [cbn [coeffs_divk]; rewrite Hc, Hd; reflexivity|]. intros E. cbn [tden]. rewrite Hsum. lia.
+ split; [exact Hd|]. intros E. cbn [tden]. rewrite Hsum. lia.
Qed.
#[using="Type"] Lemma split_mod_core : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'Q9'H&]<zr1%3221+R0%5231%7231'I&]Dr3&]I+2r2%3221%6251%83A1>&\7r6&]8r4r5%3221%6251r7%>2=5%A221%B292%D3M21p061p0>1p0H1po6Q11pj8Q21pQU6Q31pQU4Q41").
Proof.
intros ua ur SA j Hj HSA Heq.
rewrite (eqm_mod_pow2 _ _ j Hj Heq). rewrite Z.add_mod, HSA, Z.add_0_l, Z.mod_mod by lia. reflexivity.
Qed.
#[using="Type"] Lemma and_high_split_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RK';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9'A%1223%B11&\<r:r9r8r7%544321&]<zr6%3221&]A+R0%2281'I&TLr<%221>&aN&]H&]I+2%221B%411%62Q51%;3Q581'6&T?r;%928J%3321I(C%B3621&\7&\Cr>%221K&]8&\B%124Q3%32Q51%326Q4%5221%:271r?&T5r=%261OCQ=Q<Q;%Q1241&S1(R6%Q427Q>%Q02OH%Q211%Q42R31%63541%Q:3R481p0>1p0J1p0Q21p0Q?1p0QC1p0QH1pkNR31pQRNR01pmHR11pm8R51po6R61pm0R81poFR:1plJR=1pRFRF1pQS:RH1").
Proof.
intros segs E base kn bk j c dts rts a Hkn Hj0 Hj64 Hbk Hdiv Ha. unfold and_high_split.
rewrite and_highmask_val by lia.
set (m := (2 ^ j)%Z).
assert (Hp : (0 < m)%Z) by (subst m; apply Z.pow_pos_nonneg; lia).
set (cA := (c - c mod m)%Z). set (r := unlin ((c mod m)%Z, rts)).
set (SA := (cA + tden E dts)%Z).
assert (HSA : (SA mod m = 0)%Z).
{ subst SA cA m. rewrite Z.add_mod, (coeffs_divk_sound segs E base kn _ dts Hkn Hp Hdiv), Z.add_0_r, Z.mod_mod by lia.
rewrite Zminus_mod_idemp_r. rewrite Z.sub_diag. reflexivity. }
assert (Hr : eqm (uE E r) (c mod m + tden E rts)%Z).
{ subst r. eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd]. apply eqm_refl. }
assert (Har : eqm (uE E a) (SA + uE E r)).
{ eapply eqm_trans; [exact Ha|]. apply eqm_sym in Hr.
eapply eqm_trans; [|apply eqm_add; [apply eqm_refl | exact Hr]]. exists 0%Z. subst SA cA.
pose proof (Z.div_mod c m ltac:(lia)). lia. }
pose proof (split_mod_core (uE E a) (uE E r) SA j ltac:(lia) HSA Har) as Hmod. fold m in Hmod.
unfold uE in *.
assert (GOAL : forall res, eqm (bv_unsigned (edenot E res)) (SA + (bv_unsigned (edenot E r) - bv_unsigned (edenot E r) mod m))%Z ->
edenot E res = Z_to_bv 64 (bv_unsigned (edenot E a) - bv_unsigned (edenot E a) mod m)).
{ intros res Hres. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E res)). apply eqm_Z_to_bv.
eapply eqm_trans; [exact Hres|]. rewrite Hmod. destruct Har as [q Hq]. exists (-q)%Z. lia. }
assert (RES : edenot E (mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk))
= Z_to_bv 64 (bv_unsigned (edenot E a) - bv_unsigned (edenot E a) mod m)).
{ apply GOAL. rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add.
- eapply eqm_trans; [apply unlin_sound|]. unfold lden; cbn [fst snd]. apply eqm_refl.
- rewrite mkAlu_denot, Hbk, and_highmask_val by lia. fold m. apply eqm_u_lit. }
destruct (erange kn r) as [[lo hi]|] eqn:Her; [|exact RES].
destruct (Z.eqb (lo / m) (hi / m)) eqn:Hq; [|exact RES].
apply Z.eqb_eq in Hq. apply GOAL.
pose proof (erange_sound segs E base kn r lo hi Hkn Her) as [Hlo Hhi].
eapply eqm_trans; [apply unlin_sound|]. unfold lden; cbn [fst snd].
set (x := bv_unsigned (edenot E r)) in *.
pose proof (Z.div_mod x m ltac:(lia)) as Dx.
assert (Hqa : (lo / m <= x / m)%Z) by (apply Z.div_le_mono; lia).
assert (Hqh : (x / m <= hi / m)%Z) by (apply Z.div_le_mono; lia).
assert (Ex : (x / m = lo / m)%Z) by lia.
exists 0%Z. subst SA. rewrite <- Ex. lia.
Qed.
#[using="Type"] Lemma and_low_split_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RL';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9'A%1223%B11&\<r:r9r8r7%544321&]<zr6%3221&]A+R0%2281'I&TLr<%221>&aN&]J&]I+2%221B+1%5221%72Q61%<3Q691'6&T?r;%:29K%3321J(C%C3621&\7&\Cr>%221L&]8&\B%124Q4%32Q61%326Q5%5221%:271r?&T6r=%251Q0CQ>Q<%Q2241&S1(R6%Q527Q?%Q12Q0H%Q321O%Q52R41%63541%Q;3R581p0>1p0J1p0Q21p0Q@1p0QD1p0QI1pkNR41pQRNR11pmHR21pm8R61po6R71pm0R91poFR;1plJR>1pRFRG1pQS:RI1").
Proof.
intros segs E base kn bk j c dts rts a Hkn Hj0 Hj64 Hbk Hdiv Ha. unfold and_low_split.
rewrite and_lowmask_val by lia.
set (m := (2 ^ j)%Z).
assert (Hp : (0 < m)%Z) by (subst m; apply Z.pow_pos_nonneg; lia).
set (r := unlin ((c mod m)%Z, rts)).
set (SA := (c - c mod m + tden E dts)%Z).
assert (HSA : (SA mod m = 0)%Z).
{ subst SA m. rewrite Z.add_mod, (coeffs_divk_sound segs E base kn _ dts Hkn Hp Hdiv), Z.add_0_r, Z.mod_mod by lia.
rewrite Zminus_mod_idemp_r. rewrite Z.sub_diag. reflexivity. }
assert (Hr : eqm (uE E r) (c mod m + tden E rts)%Z).
{ subst r. eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd]. apply eqm_refl. }
assert (Har : eqm (uE E a) (SA + uE E r)).
{ eapply eqm_trans; [exact Ha|]. apply eqm_sym in Hr.
eapply eqm_trans; [|apply eqm_add; [apply eqm_refl | exact Hr]]. exists 0%Z. subst SA.
pose proof (Z.div_mod c m ltac:(lia)). lia. }
pose proof (split_mod_core (uE E a) (uE E r) SA j ltac:(lia) HSA Har) as Hmod. fold m in Hmod.
unfold uE in *. rewrite Hmod.
assert (RES : edenot E (mkAlu ALU_AND r bk) = Z_to_bv 64 (bv_unsigned (edenot E r) mod m)).
{ rewrite mkAlu_denot, Hbk, and_lowmask_val by lia. reflexivity. }
destruct (erange kn r) as [[lo hi]|] eqn:Her; [|exact RES].
destruct (Z.eqb (lo / m) (hi / m)) eqn:Hq; [|exact RES].
apply Z.eqb_eq in Hq.
pose proof (erange_sound segs E base kn r lo hi Hkn Her) as [Hlo Hhi].
rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
eapply eqm_trans; [apply unlin_sound|]. unfold lden; cbn [fst snd].
set (x := bv_unsigned (edenot E r)) in *.
pose proof (Z.div_mod x m ltac:(lia)) as Dx.
assert (Hqa : (lo / m <= x / m)%Z) by (apply Z.div_le_mono; lia).
assert (Hqh : (x / m <= hi / m)%Z) by (apply Z.div_le_mono; lia).
assert (Ex : (x / m = lo / m)%Z) by lia.
apply eqm_sym in Hr. destruct Hr as [q Hq']. exists q. rewrite <- Ex. unfold uE in Hq'. fold x in Hq'. lia.
Qed.
#[using="Type"] Lemma mkAnd0_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q8';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r6r5r4r3%544321'I&TL&WNr2%23761%42:1&S1(R6%72=:%82>6%43321%;3J61p0=1plBD1pkNE1poFG1plJJ1pRFQ31pQS:Q51").
Proof.
intros segs E base kn a b Hkn. unfold mkAnd0.
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
destruct (negb (lin_trivial (c, ts)) && coeffs_divk kn (2 ^ j) ts)%bool eqn:Hcd0.
2: {
destruct (if lin_trivial (c, ts) then ([], ts) else lsplit_div kn (2 ^ j) ts) as [dts rts] eqn:Hsp.
assert (R6 : edenot E (mkMd M_MUL (ELit (2 ^ j)) (mkSrl kn a j)) = alu64 ALU_AND (edenot E a) (Z_to_bv 64 (- 2 ^ j)))
by (rewrite and_highmask_val by lia; eapply and_highmask_srl; [exact Hkn | lia | lia]).
destruct dts as [|d1 dts']; [exact R6|]. destruct rts as [|r1 rts']; [exact R6|].
destruct (lin_trivial (c, ts)) eqn:Htr; [discriminate|].
destruct (lsplit_div_sound kn (2 ^ j) ts _ _ Hsp) as [Hdts Hsum].
assert (Hbk2 : edenot E (ELit k) = Z_to_bv 64 (- 2 ^ j)).
{ cbn [edenot]. rewrite Hbk, <- Hneg. f_equal. unfold two64 in Hpow. lia. }
eapply (and_high_split_denot segs E base kn (ELit k) j c (d1 :: dts') (r1 :: rts') a Hkn ltac:(lia) ltac:(lia) Hbk2 Hdts).
apply eqm_sym. pose proof (lin_of_sound E a) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs.
rewrite (Hsum E), Z.add_assoc in Hs. exact Hs. }
apply andb_prop in Hcd0 as [_ Hcd].
rewrite and_highmask_val by lia.
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (lin_of_sound E a) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs. unfold uE in Hs.
assert (Hmod : (bv_unsigned (edenot E a) mod 2 ^ j = c mod 2 ^ j)%Z).
{ rewrite <- (eqm_mod_pow2 _ _ j ltac:(lia) Hs). rewrite Z.add_mod, (coeffs_divk_sound segs E base kn _ ts Hkn Hp Hcd), Z.add_0_r, Z.mod_mod by lia. reflexivity. }
rewrite Hmod. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd].
destruct Hs as [q Hq]. exists q. lia.
- set (j2 := Z.log2 (k' + 1)).
destruct (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool eqn:Hc2.
2:{
set (j3 := (Z.log2 k' + 1)%Z).
destruct (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool eqn:Hc3; [|apply mkAlu_denot].
apply andb_prop in Hc3 as [Hc3 _]. apply andb_prop in Hc3 as [Hk0 Hj3]. apply Z.ltb_lt in Hk0. apply Z.leb_le in Hj3.
assert (Hj30 : (0 <= Z.log2 k')%Z) by apply Z.log2_nonneg.
destruct (lin_lowbits_kn kn a j3) as [v|] eqn:Hlb; [|apply mkAlu_denot].
destruct (lin_lowbits_kn_sound segs E base kn a j3 v Hkn ltac:(lia) Hlb) as [Hv Hvr].
cbn [edenot]. rewrite Hbk. apply bv_eq. rewrite u_and64, !u_lit64. fold two64. unfold two64.
rewrite (Z.mod_small k') by lia.
assert (Hkj : (k' < 2 ^ j3)%Z) by (subst j3; destruct (Z.log2_spec k' Hk0) as [_ B]; rewrite Z.add_1_r; exact B).
assert (LOW : Z.land (bv_unsigned (edenot E a)) k' = Z.land v k').
{ rewrite <- Hv. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i j3) as [Hlt|Hge].
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit k' i) with false; [rewrite !andb_false_r; reflexivity|].
symmetry. apply Z.bits_above_log2;
[clearbody k'; clear - Hk0; lia | unfold j3 in Hge; clear - Hge; lia]. }
rewrite LOW. apply Z.mod_small.
assert (Hln : (0 <= Z.land v k')%Z) by (apply Z.land_nonneg; lia).
destruct (Z.eq_dec (Z.land v k') 0) as [Hz|Hnz]; [rewrite Hz; lia|].
pose proof (Z.log2_land v k' ltac:(lia) ltac:(lia)) as Hll.
destruct (Z.log2_spec (Z.land v k') ltac:(lia)) as [_ B].
assert (Hpw : (2 ^ Z.succ (Z.log2 (Z.land v k')) <= 2 ^ 64)%Z).
{ apply Z.pow_le_mono_r; [clear; lia | unfold j3 in Hj3; clear - Hll Hj3; lia]. }
clearbody k'. clear - Hln B Hpw. lia. }
apply andb_prop in Hc2 as [Hpow Hj64]. apply Z.eqb_eq in Hpow. apply Z.ltb_lt in Hj64.
assert (Hj0 : (0 <= j2)%Z) by (subst j2; apply Z.log2_nonneg).
cbn [edenot]. rewrite Hbk. replace k' with (2 ^ j2 - 1)%Z by lia.
destruct (Z.leb j2 (ealign kn a)) eqn:Hle.
+ apply Z.leb_le in Hle. symmetry. apply and_lowmask_zero; [lia | lia |].
eapply Z.divide_trans; [apply pow2_divide_le | exact Hdiv]. lia.
+ destruct (lowbits kn a j2) as [v0|] eqn:Hlow.
{ pose proof (lowbits_sound segs E base kn a j2 v0 Hkn ltac:(lia) Hlow) as Hv0.
rewrite and_lowmask_val by lia. cbn [edenot]. rewrite Hv0. reflexivity. }
destruct (lin_trivial (lin_of a)); [replace (2 ^ j2 - 1)%Z with k' by lia; rewrite <- Hbk; apply mkAlu_denot|].
destruct (lin_lowbits_kn kn a j2) as [v|] eqn:Hlb.
2: {
destruct (lsplit_div kn (2 ^ j2) (snd (lin_of a))) as [dts rts] eqn:Hsp.
assert (DF : edenot E (mkAlu ALU_AND a (ELit k)) = alu64 ALU_AND (edenot E a) (Z_to_bv 64 (2 ^ j2 - 1)))
by (replace (2 ^ j2 - 1)%Z with k' by lia; rewrite <- Hbk; apply mkAlu_denot).
destruct dts as [|d1 dts']; [exact DF|]. destruct rts as [|r1 rts']; [exact DF|].
destruct (lsplit_div_sound kn (2 ^ j2) _ _ _ Hsp) as [Hdts Hsum].
assert (Hbk2 : edenot E (ELit k) = Z_to_bv 64 (2 ^ j2 - 1)) by (cbn [edenot]; rewrite Hbk; f_equal; lia).
eapply (and_low_split_denot segs E base kn (ELit k) j2 _ (d1 :: dts') (r1 :: rts') a Hkn ltac:(lia) ltac:(lia) Hbk2 Hdts).
apply eqm_sym. pose proof (lin_of_sound E a) as Hs. destruct (lin_of a) as [c ts]. unfold lden in Hs. cbn [fst snd] in Hs, Hsum |- *.
rewrite (Hsum E), Z.add_assoc in Hs. exact Hs. }
destruct (lin_lowbits_kn_sound segs E base kn a j2 v Hkn ltac:(lia) Hlb) as [Hv Hvr].
rewrite and_lowmask_val by lia. cbn [edenot]. rewrite Hv. reflexivity.
Qed.
#[using="Type"] Lemma testbit_pow_sub : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'Q9'H&]<zr2%3221r3%5231%7231'I'6&]K&]J&]I+2r5%3221r4%5241%7231%921>&4&]=%126A&]B%12C:%5231%B3A71p0G1p0E1pQPJN1po0O1pkNQ01").
Proof.
intros a i n Hi Hn.
replace (2 ^ a - 2 ^ i)%Z with (Z.shiftl (Z.ones (a - i)) i).
2:{ rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv.
replace (2 ^ a)%Z with (2 ^ (a - i) * 2 ^ i)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
rewrite Z.shiftl_spec by lia.
destruct (Z.leb_spec i n).
- rewrite Z.testbit_ones by lia. cbn [andb]. apply Bool.eq_true_iff_eq. rewrite Z.ltb_lt. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. lia.
- rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_mask_narrow : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q7'Q9'H&]<zr2%3221r1%5231%7231+R0%8261r5%:291&]A&]I+2r3%3221%5271%B271'I&];r6&]Jr4%;2:1%<2;?%4221%7261%?2>D%7214%:291%<3Q041p0>1p0H1p0K1po6Q41po0Q51pQULQ61").
Proof.
intros x i j Hij Hj Hx. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
rewrite !testbit_pow_sub by lia.
destruct (Z.ltb_spec n j).
- replace (n <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- replace (Z.testbit x n) with false; [destruct (i <=? n)%Z; reflexivity|]. symmetry.
destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|].
assert (Z.log2 x < j)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.
#[using="Type"] Lemma mkAnd_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q8';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r6r5r4r3%544321'I&TL&WMr2%23761%42:1&S1(R6%72=:%82>6%43321%;3J61p0=1plBD1pkNE1poFG1plJJ1pRFQ31pQS:Q51").
Proof.
intros segs E base kn a b Hkn. unfold mkAnd.
destruct b as [k| | | | | | |]; try (eapply mkAnd0_denot; exact Hkn).
destruct (narrow_mask kn a (k mod two64)) as [m|] eqn:Hm; [|eapply mkAnd0_denot; exact Hkn].
rewrite (mkAnd0_denot segs E base kn) by exact Hkn. cbn [edenot].
unfold narrow_mask in Hm.
pose proof (ctz64_sound (k mod two64)) as [Hi _].
set (i := ctz64 (k mod two64)) in *. set (j := Z.log2 (k mod two64 + 2 ^ i)) in *.
destruct (Z.ltb 0 (k mod two64) && Z.eqb (k mod two64 + 2 ^ i) (2 ^ j) && Z.ltb j 64)%bool eqn:Hc; [|discriminate].
apply andb_prop in Hc as [Hc Hj64]. apply andb_prop in Hc as [Hk0 Hpow].
apply Z.ltb_lt in Hk0. apply Z.eqb_eq in Hpow. apply Z.ltb_lt in Hj64.
destruct (xhi kn a) as [h|] eqn:Hx; [|discriminate].
destruct (Z.ltb h (2 ^ j)) eqn:Hh; [|discriminate]. apply Z.ltb_lt in Hh. injection Hm as <-.
pose proof (xhi_sound segs E base kn a h Hkn Hx) as Hua. pose proof (u64_range (edenot E a)) as Hr.
assert (Hj0 : (0 <= j)%Z) by (subst j; apply Z.log2_nonneg).
assert (Hp : (0 < 2 ^ i)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hij : (i < j)%Z) by (apply (Z.pow_lt_mono_r_iff 2); lia).
assert (Hpi : (2 ^ i <= 2 ^ 63)%Z) by (apply Z.pow_le_mono_r; lia).
apply bv_eq. rewrite !u_and64, !u_lit64. unfold two64 in *.
rewrite (Z.mod_small (2 ^ 64 - 2 ^ i)) by lia.
replace (k mod 2 ^ 64)%Z with (2 ^ j - 2 ^ i)%Z by lia.
symmetry. apply land_mask_narrow; lia.
Qed.
#[using="Type"] Lemma mkAndK_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q8';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r6r5r4r3%544321'I&TL&WOr2%23761%42:1&S1(R6%72=:%82>6%43321%;3J61p0=1plBD1pkNE1poFG1plJJ1pRFQ31pQS:Q51").
Proof.
intros segs E base kn a b Hkn. unfold mkAndK.
assert (MERGE : forall x (M1 k : Z), (0 <= M1 < two64)%Z ->
bv_unsigned (edenot E a) = Z.land (bv_unsigned (edenot E x)) M1 ->
edenot E (mkAnd kn x (ELit (Z.land M1 (k mod two64)))) = alu64 ALU_AND (edenot E a) (edenot E (ELit k))).
{ intros x M1 k HM1 Ha. rewrite (mkAnd_denot segs E base kn) by exact Hkn. cbn [edenot].
apply bv_eq. rewrite !u_and64, !u_lit64, Ha.
pose proof (u64_range (edenot E x)) as Hx.
pose proof (Z.mod_pos_bound k two64 ltac:(unfold two64; lia)) as H2.
rewrite (Z.mod_small (Z.land M1 (k mod two64))).
- rewrite Z.land_assoc. reflexivity.
- split; [apply Z.land_nonneg; lia|].
eapply Z.le_lt_trans; [apply land_le_l; lia | lia]. }
destruct a as [|i|op x m| |mo ma mb| | |]; try (eapply mkAnd_denot; exact Hkn).
- destruct op; try (eapply mkAnd_denot; exact Hkn).
destruct m as [m1| | | | | | |]; try (eapply mkAnd_denot; exact Hkn).
destruct b as [k| | | | | | |]; try (eapply mkAnd_denot; exact Hkn).
apply MERGE; [apply Z.mod_pos_bound; unfold two64; lia|].
cbn [edenot]. rewrite u_and64, u_lit64. reflexivity.
- destruct mo; try (eapply mkAnd_denot; exact Hkn).
destruct ma as [m| | | | | | |]; try (eapply mkAnd_denot; exact Hkn).
destruct mb as [| |op2 x si| | | | |]; try (eapply mkAnd_denot; exact Hkn).
destruct op2; try (eapply mkAnd_denot; exact Hkn).
destruct si as [i| | | | | | |]; try (eapply mkAnd_denot; exact Hkn).
destruct b as [k| | | | | | |]; try (eapply mkAnd_denot; exact Hkn).
cbv zeta. set (i' := ((i mod two64) mod 64)%Z).
destruct (Z.eqb (m mod two64) (2 ^ i')) eqn:Hm; [|eapply mkAnd_denot; exact Hkn].
apply Z.eqb_eq in Hm.
assert (Hi' : (0 <= i' < 64)%Z) by (subst i'; apply Z.mod_pos_bound; lia).
assert (Hp : (0 < 2 ^ i')%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hp64 : (2 ^ i' < 2 ^ 64)%Z) by (apply Z.pow_lt_mono_r; lia).
apply MERGE; [unfold two64 in *; lia|].
cbn [edenot]. rewrite m_mul, alu_srl. unfold v_mul, v_srl. rewrite !u_lit64, Hm.
replace (bv_unsigned (Z_to_bv 64 i) mod 64)%Z with i' by (subst i'; rewrite u_lit64; reflexivity).
pose proof (u64_range (edenot E x)) as Hx. set (ux := bv_unsigned (edenot E x)) in *.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.div_mod ux (2 ^ i') ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound ux (2 ^ i') Hp) as Hmb.
assert (Hq : (0 <= ux / 2 ^ i' <= ux)%Z)
by (clearbody ux i'; clear - Hp Hx; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
unfold two64. rewrite (Z.mod_small (ux / 2 ^ i')) by lia. rewrite (Z.mod_small (2 ^ i' * _)) by lia.
pose proof (and_highmask_val (edenot E x) i' ltac:(lia) ltac:(lia)) as Hh.
apply (f_equal bv_unsigned) in Hh. rewrite u_and64 in Hh. fold ux in Hh.
rewrite (u_small (ux - ux mod 2 ^ i')) in Hh by lia.
replace (2 ^ 64 - 2 ^ i')%Z with (bv_unsigned (Z_to_bv 64 (- 2 ^ i'))).
+ rewrite Hh. lia.
+ rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite <- (Z.mod_add _ 1) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
#[using="Type"] Lemma itv_ltu_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q6'Q9'6'H&]<r7r3%3221r6%5231%7231%7235r5%9271%;231'I'>%11?&V3r9r8%3421@=(3%12EA%93731&]B%12B>r4%=3J21p051p0@1p0E1pQTFN1pQUNQ01pQULQ11plLQ21pm2Q31pl4Q41pl6Q51").
Proof.
intros al ah bl bh x y t Hx Hy H. unfold itv_ltu in H.
destruct (ah <? bl)%Z eqn:C1; [injection H as <-; apply Z.ltb_lt; lia|].
destruct (bh <=? al)%Z eqn:C2; [injection H as <-; apply Z.ltb_ge; lia| discriminate].
Qed.
#[using="Type"] Lemma itv_lts_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q>'Q9'aOyR0%211'6'H&]<r7&b4r3%2281%5241r6%7231%9231%9235r5%;271%=231'I'>%11A&V2r9r8%3421B=(3%12GB%93731&]B&b2%12MC%22N@%4221r4%@3O21p081p0C1p0H1pQTFQ31pQUNQ51pQULQ61plLQ:1pm2Q;1pl4Q<1pl6Q=1").
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
#[using="Type"] Lemma range_branch_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q?'RI'Q9'aOyR0%211'6'H&]<r7&b4r3%2281%5241r6%7231%9231%9235r5%;271%=231'I'>%11A&XDr:r9r8%45321C>(3%12HC%:3831&S4r;%231D@r4%?3N21p061p0B1p0G1pQTFQ21pQUNQ41pQULQ51plLQ91pm2Q:1pl4Q;1pl6Q<1pm8Q>1").
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
#[using="Type"] Lemma cond_on_eq_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "?'RI'aOyR0%211'I'6&S4r2r1%33211&TC%114%83731pQU8:1pm8>1").
Proof.
intros c v. destruct c; cbn [branch_taken cond_on_eq]; unfold bv_eqb, bv_lts, bv_ltu;
rewrite ?Z.eqb_refl, ?Z.ltb_irrefl; reflexivity.
Qed.
#[using="Type"] Lemma lin_branch_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QB';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'RI'U9'6&\<r8r7r6r5%544321'I%A18&VJr4r3%348721(3r2%22?1%93841&S4&TLr9%221?%322;%53B21%@3G1<p081p0C1pQTFJ1plBL1pkNM1pm8O1poFQ11pV@Q41pRFQ=1pQS:Q?1").
Proof.
intros segs E M kn c a b t Hkn H. unfold lin_branch in H.
set (ltu := if lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] then Some true
else if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then Some false else None) in H.
assert (Hltu : forall t', ltu = Some t' -> bv_ltu (edenot E a) (edenot E b) = t').
{ intros t' Ht. subst ltu. unfold bv_ltu.
destruct (lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)]) eqn:G1.
- injection Ht as <-. pose proof (lin_ge0_sound segs E M kn _ _ Hkn G1) as L. cbn [xt_den] in L.
apply Z.ltb_lt. lia.
- destruct (lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)]) eqn:G2; [|discriminate].
injection Ht as <-. pose proof (lin_ge0_sound segs E M kn _ _ Hkn G2) as L. cbn [xt_den] in L.
apply Z.ltb_ge. lia. }
assert (Hsgn : forall ah bh, erange kn a = Some (fst ah, snd ah) -> erange kn b = Some (fst bh, snd bh) ->
(Z.ltb (snd ah) (2 ^ 63) && Z.ltb (snd bh) (2 ^ 63))%bool = true ->
bv_lts (edenot E a) (edenot E b) = bv_ltu (edenot E a) (edenot E b)).
{ intros [al ah] [bl bh] Ha Hb Hc. cbn [fst snd] in *.
apply andb_prop in Hc as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
pose proof (erange_sound segs E M kn a _ _ Hkn Ha) as Ra. pose proof (erange_sound segs E M kn b _ _ Hkn Hb) as Rb.
unfold bv_lts, bv_ltu. rewrite (bv_signed_small (edenot E a)) by lia. rewrite (bv_signed_small (edenot E b)) by lia.
reflexivity. }
assert (Hne : (lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0 kn [(a, (-1)%Z)] [(b, 0%Z)])%bool = true ->
bv_eqb (edenot E a) (edenot E b) = false).
{ intros Hor. unfold bv_eqb. apply Z.eqb_neq.
apply orb_prop in Hor as [G|G]; pose proof (lin_ge0_sound segs E M kn _ _ Hkn G) as L; cbn [xt_den] in L; lia. }
assert (Heq : (if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 kn [(b, 0%Z)] [(a, 0%Z)] else false) = true ->
bv_eqb (edenot E a) (edenot E b) = true).
{ intros Hab. destruct (lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)]) eqn:G1; [|discriminate].
pose proof (lin_ge0_sound segs E M kn _ _ Hkn G1) as L1. pose proof (lin_ge0_sound segs E M kn _ _ Hkn Hab) as L2.
cbn [xt_den] in L1, L2. unfold bv_eqb. apply Z.eqb_eq. lia. }
destruct c; cbn [branch_taken].
1: { destruct (lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0 kn [(a, (-1)%Z)] [(b, 0%Z)])%bool.
- injection H as <-. exact (Hne eq_refl).
- destruct (if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 kn [(b, 0%Z)] [(a, 0%Z)] else false) eqn:G; [|discriminate].
injection H as <-. exact (Heq eq_refl). }
1: { destruct (lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0 kn [(a, (-1)%Z)] [(b, 0%Z)])%bool.
- injection H as <-. rewrite (Hne eq_refl). reflexivity.
- destruct (if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 kn [(b, 0%Z)] [(a, 0%Z)] else false) eqn:G; [|discriminate].
injection H as <-. rewrite (Heq eq_refl). reflexivity. }
-
destruct (erange kn a) as [[al ah]|] eqn:Ha; [|discriminate].
destruct (erange kn b) as [[bl bh]|] eqn:Hb; [|discriminate].
destruct (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool eqn:Hc; [|discriminate].
rewrite (Hsgn (al, ah) (bl, bh) eq_refl eq_refl Hc). exact (Hltu t H).
-
destruct (erange kn a) as [[al ah]|] eqn:Ha; [|discriminate].
destruct (erange kn b) as [[bl bh]|] eqn:Hb; [|discriminate].
destruct (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool eqn:Hc; [|discriminate].
rewrite (Hsgn (al, ah) (bl, bh) eq_refl eq_refl Hc).
destruct ltu as [t'|]; [|discriminate]. cbn [option_map] in H. injection H as <-.
f_equal. exact (Hltu t' eq_refl).
- exact (Hltu t H).
-
destruct ltu as [t'|]; [|discriminate]. cbn [option_map] in H. injection H as <-.
f_equal. exact (Hltu t' eq_refl).
Qed.
#[using="Type"] Lemma decide_branch_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QB';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'RI'U9'6&\<r8r7r6r5%544321'I%A18&TGr4r3%348721(3r2%22?1%93841&S4&TLr9%221?%322;%53B21%@3G1<p081p0C1pQTFJ1plBL1pkNM1pm8O1poFQ11pV@Q41pRFQ=1pQS:Q?1").
Proof.
intros segs E M kn c a b t Hkn H.
assert (Hdiff : forall t', diff_branch c a b = Some t' -> branch_taken c (edenot E a) (edenot E b) = t').
{ intros t' Hd. unfold diff_branch in Hd.
assert (Hsub : forall z, is_lit (mkAlu ALU_SUB a b) = Some z ->
(bv_eqb (edenot E a) (edenot E b) = Z.eqb (z mod two64) 0)).
{ intros z Hz. apply is_lit_some in Hz.
pose proof (mkAlu_denot E ALU_SUB a b) as Hm. rewrite Hz in Hm. cbn [edenot] in Hm.
pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E b)) as Rb.
assert (Hu : (z mod two64 = (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) mod 2 ^ 64)%Z).
{ rewrite <- u_lit64, Hm, u_sub64. reflexivity. }
rewrite Hu. unfold bv_eqb.
destruct (Z.eqb_spec (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))) as [E1|E1].
- rewrite E1, Z.sub_diag, Z.mod_0_l by lia. reflexivity.
- symmetry. apply Z.eqb_neq. intros Hz0.
apply E1. destruct (Z_lt_le_dec (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))).
+ rewrite <- (Z.mod_add _ 1) in Hz0 by lia. rewrite Z.mod_small in Hz0 by lia. lia.
+ rewrite Z.mod_small in Hz0 by lia. lia. }
destruct c; try discriminate;
destruct (is_lit (mkAlu ALU_SUB a b)) as [z|] eqn:Hz; try discriminate;
injection Hd as <-; cbn [branch_taken]; rewrite (Hsub z eq_refl); reflexivity. }
assert (Hrange : forall t',
match erange kn a, erange kn b with
| Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
| _, _ => None
end = Some t' -> branch_taken c (edenot E a) (edenot E b) = t').
{ intros t' Hr.
destruct (erange kn a) as [[al ah]|] eqn:Ha; [|discriminate].
destruct (erange kn b) as [[bl bh]|] eqn:Hb; [|discriminate].
eapply range_branch_sound; [eapply erange_sound; [exact Hkn | exact Ha] | eapply erange_sound; [exact Hkn | exact Hb] | exact Hr]. }
assert (Hrest : (if expr_eqb a b then Some (cond_on_eq c)
else match diff_branch c a b with
| Some t => Some t
| None =>
match (match erange kn a, erange kn b with
| Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
| _, _ => None
end) with
| Some t => Some t
| None => lin_branch kn c a b
end
end) = Some t ->
branch_taken c (edenot E a) (edenot E b) = t).
{ clear H. intros H. destruct (expr_eqb a b) eqn:Heq.
- apply expr_eqb_eq in Heq. subst b. injection H as <-. apply cond_on_eq_sound.
- destruct (diff_branch c a b) as [t'|] eqn:Hd.
{ injection H as Ht. rewrite <- Ht. first [exact (Hdiff _ eq_refl) | exact (Hdiff _ Hd)]. }
match type of H with match ?m with _ => _ end = _ => destruct m as [t'|] eqn:Hr end.
{ injection H as Ht. rewrite <- Ht. first [exact (Hrange _ eq_refl) | exact (Hrange _ Hr)]. }
eapply lin_branch_sound; [exact Hkn | exact H]. }
unfold decide_branch in H.
destruct a; try exact (Hrest H). destruct b; try exact (Hrest H).
injection H as <-. reflexivity.
Qed.
#[using="Type"] Lemma land_aligned_small : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'Q9&]<zr1%3221r4%5241&]:&]I+2r3%3221r5%6221'H%>2=3&]A%928<%2261%5241'I&];r7r6%3221%53I1Gp071p0>1p0F1p0I1po8N1plBO1pQULQ01").
Proof.
intros x b k Hk Hx [q Hq] Hb. subst x.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hik|Hik].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z_testbit_high k b i) by lia. apply andb_false_r.
Qed.
#[using="Type"] Lemma or_disjoint_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QA';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r6r5r4r3%544321'I'6&X9r2%23761(C%63521'Q9&]@&b4&TLr7%221?%42M1%423@%62O1%8231&]8%1253%C3<31p0>1p0F1plBM1pkNN1poFQ01pV@Q31pRFQ<1pQS:Q>1").
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
#[using="Type"] Lemma or_as_and_not_plus : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "E'Q9&]<zr2%3221'I&]@r4r3%3221&]8&];&]>%115%3271%5217%;3@71p0=1p0>1pm8C1pQULD1").
Proof.
intros x c Hx Hc.
assert (Hd : Z.land (Z.land x (Z.lnot c)) c = 0%Z).
{ rewrite <- Z.land_assoc. rewrite (Z.land_comm (Z.lnot c) c). rewrite Z.land_lnot_diag. apply Z.land_0_r. }
rewrite (Z.add_nocarry_lxor _ _ Hd).
apply Z.bits_inj'. intros n Hn.
rewrite Z.lxor_spec, Z.lor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.testbit x n), (Z.testbit c n); reflexivity.
Qed.
#[using="Type"] Lemma or_R1 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QD';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r6r5r4r3%544321'I&TL&WG(R5&WO(S=&]>&]Dr2&Z=%3221%511%711%93@?1%916%=3<21%?2E1&S1(R7%B2HE%C2I6%43321%F3Q661p0H1pm8O1pl0Q11poFQ31pV@Q61pRFQ?1pQS:QA1").
Proof.
intros segs E M kn a0 c Hkn. rewrite mkAlu_denot, (mkAndK_denot segs E M kn) by exact Hkn. cbn [edenot].
apply bv_eq. rewrite u_add64, u_and64, u_or64, !u_lit64.
pose proof (u64_range (edenot E a0)) as Hx. set (x := bv_unsigned (edenot E a0)) in *.
pose proof (Z.mod_pos_bound c two64 ltac:(unfold two64; lia)) as Hc. set (c' := (c mod two64)%Z) in *.
assert (Hln : (Z.lnot c' mod two64 = Z.land (Z.lnot c') (Z.ones 64))%Z).
{ unfold two64. rewrite Z.land_ones by lia. reflexivity. }
rewrite Hln.
replace (Z.land x (Z.land (Z.lnot c') (Z.ones 64))) with (Z.land x (Z.lnot c')).
2: { rewrite (Z.land_comm (Z.lnot c')), Z.land_assoc. rewrite (Z.land_ones x 64) by lia.
unfold two64 in Hx. rewrite (Z.mod_small x) by lia. reflexivity. }
rewrite (or_as_and_not_plus x c') by lia.
apply Z.mod_small. rewrite <- (or_as_and_not_plus x c') by lia. unfold two64.
apply Z_lor_range; unfold two64 in *; lia.
Qed.
#[using="Type"] Lemma mkOr_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q8';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r6r5r4r3%544321'I&TL&X4r2%23761%42:1&S1(R7%72=:%82>6%43321%;3J61p0=1plBD1pkNE1poFG1pV@J1pRFQ31pQS:Q51").
Proof.
intros segs E M kn a b Hkn. unfold mkOr.
assert (Hcomm : forall u v : word, alu64 ALU_OR u v = alu64 ALU_OR v u).
{ intros u v. rewrite !alu_or. unfold v_or. rewrite Z.lor_comm. reflexivity. }
destruct (is_lit a) as [x|] eqn:Ha; [destruct (is_lit b) as [y|] eqn:Hb|].
- apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. unfold zalu. apply Z_to_bv_bv_unsigned.
- destruct (or_disjoint kn a b) eqn:H1; [|destruct (or_disjoint kn b a) eqn:H2];
[ rewrite mkAlu_denot, alu_add, alu_or; unfold v_add, v_or; f_equal; symmetry; eapply or_disjoint_sound; eassumption
| rewrite mkAlu_denot, alu_add, alu_or; unfold v_add, v_or; f_equal; symmetry;
rewrite Z.lor_comm, Z.add_comm; eapply or_disjoint_sound; eassumption | ].
apply is_lit_some in Ha. subst a.
destruct b; try discriminate; rewrite Hcomm; eapply or_R1; exact Hkn.
- destruct (or_disjoint kn a b) eqn:H1; [|destruct (or_disjoint kn b a) eqn:H2];
[ rewrite mkAlu_denot, alu_add, alu_or; unfold v_add, v_or; f_equal; symmetry; eapply or_disjoint_sound; eassumption
| rewrite mkAlu_denot, alu_add, alu_or; unfold v_add, v_or; f_equal; symmetry;
rewrite Z.lor_comm, Z.add_comm; eapply or_disjoint_sound; eassumption | ].
destruct b; try (eapply or_R1; exact Hkn).
all: destruct a; try reflexivity; try discriminate.
Qed.
#[using="Type"] Lemma lxor_ones64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'Q9'H&]<zr1%3221&]A&]I+2+R0%3221%5271%;271'I&]Cr2&]J+1%2281%5241%4225%83E21p0:1pQULG1").
Proof.
intros x Hx.
pose proof (Z.sub_lxor_2rlandn (2^64-1) x) as H.
assert (Z.land (Z.lnot (2^64-1)) x = 0)%Z.
{ replace (Z.lnot (2^64-1)) with (-(2^64))%Z by reflexivity.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_dec n 64).
- replace (-(2^64))%Z with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r| lia |].
destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia| lia]. }
rewrite Z.lxor_comm. lia.
Qed.
#[using="Type"] Lemma eval_closed_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "K'U0'U9'Q9'I'>%113&U7r2%211(3r1%2291%93741'aOyR0%211&TLr4r3%3221&aN%127>%C3731p0;1pQU8F1pmJH1pRFJ1").
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
#[using="Type"] Lemma esubst_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'U0'U9'I'aOyR0%211&TLr4r2%3221r3%5241%:3731r5&U4%13857%:231%;249%@3=21p071pmJC1pQQJD1pQS0E1pRFG1").
Proof.
intros E s r e Hr. induction e; cbn [esubst];
(destruct (expr_eqb _ s) eqn:Heq;
[ apply expr_eqb_eq in Heq; rewrite Hr, <- Heq; reflexivity
| cbn [edenot]; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity ]).
Qed.
#[using="Type"] Lemma all_eval_to_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q>'U9'Q9'<'I'6&SNr5r4r3r2r1%6554321(C%:3921'H&]<%1296&]A&]8&]G%11<%32>1%52<1%9271'>%11H&U7&U4r8(S=%11Er7%53421%711(3r6%22Q31%Q23<41p0?1pQV2Q61p0K1pmBQ71pQP4Q91pQU8Q:1pmJQ<1pQS0Q=1").
Proof.
intros s e v lo cnt. revert lo. induction cnt as [|c IH]; intros lo H z Hz; [lia|].
cbn [all_eval_to] in H. destruct (eval_closed (esubst s (ELit lo) e)) as [w|] eqn:Hw; [|discriminate].
destruct (Z.eqb w v) eqn:H1; [|discriminate]. rename H into H2. apply Z.eqb_eq in H1. subst w.
destruct (Z.eq_dec z lo) as [->|Hne]; [exact Hw|].
apply (IH (lo + 1)%Z H2). lia.
Qed.
#[using="Type"] Lemma eval_closed_range : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "G'U9'Q9'I'>%113&U7r2%211(3r1%2291%93741'H&]<z%2219&]A&Z=%22<1%7241p091pQU8D1pmJF1").
Proof.
intros e. unfold two64. induction e; intros v H; cbn [eval_closed] in H; try discriminate.
- injection H as <-. apply Z.mod_pos_bound. reflexivity.
- destruct (eval_closed e1) as [x|]; [|discriminate]. destruct (eval_closed e2) as [y|]; [|discriminate].
injection H as <-. unfold zalu. apply u64_range.
- destruct (eval_closed e1) as [x|]; [|discriminate]. destruct (eval_closed e2) as [y|]; [|discriminate].
injection H as <-. unfold zaluw. apply u64_range.
- destruct (eval_closed e1) as [x|]; [|discriminate]. destruct (eval_closed e2) as [y|]; [|discriminate].
injection H as <-. unfold zmd. apply u64_range.
- destruct (eval_closed e1) as [x|]; [|discriminate]. destruct (eval_closed e2) as [y|]; [|discriminate].
injection H as <-. unfold zmdw. apply u64_range.
- destruct (eval_closed e) as [x|]; [|discriminate].
injection H as <-. unfold zext_lit. apply u64_range.
Qed.
#[using="Type"] Lemma evalS_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "F'U9'Q9'I'>%113&U6r3&Z@r2%211r1%63521&U7&U4(S=%117%33:16%511%@3>71pmJC1pQV2C1pQS0E1").
Proof.
intros s z e. induction e; cbn [evalS esubst]; destruct (expr_eqb _ s);
cbn [eval_closed]; try (rewrite (wrap64_eq z); reflexivity); try reflexivity.
- rewrite wrap64_eq. reflexivity.
- rewrite IHe1, IHe2. destruct (eval_closed (esubst s (ELit z) e1)) as [x|] eqn:C1; [|reflexivity].
destruct (eval_closed (esubst s (ELit z) e2)) as [y|] eqn:C2; [|reflexivity].
apply eval_closed_range in C1. apply eval_closed_range in C2. rewrite zfast_eq by assumption. reflexivity.
- rewrite IHe1, IHe2. destruct (eval_closed (esubst s (ELit z) e1)) as [x|] eqn:C1; [|reflexivity].
destruct (eval_closed (esubst s (ELit z) e2)) as [y|] eqn:C2; [|reflexivity].
apply eval_closed_range in C1. apply eval_closed_range in C2. rewrite zfastw_eq by assumption. reflexivity.
- rewrite IHe1, IHe2. destruct (eval_closed (esubst s (ELit z) e1)) as [x|] eqn:C1; [|reflexivity].
destruct (eval_closed (esubst s (ELit z) e2)) as [y|] eqn:C2; [|reflexivity].
apply eval_closed_range in C1. apply eval_closed_range in C2. rewrite zfastm_eq by assumption. reflexivity.
- rewrite IHe1, IHe2. destruct (eval_closed (esubst s (ELit z) e1)) as [x|]; [|reflexivity].
destruct (eval_closed (esubst s (ELit z) e2)) as [y|]; reflexivity.
- rewrite IHe. destruct (eval_closed (esubst s (ELit z) e)) as [x|] eqn:C1; [|reflexivity].
apply eval_closed_range in C1. rewrite zext_fast_eq by (unfold two64 in C1; lia). reflexivity.
Qed.
#[using="Type"] Lemma all_eval_toS_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "D'U9'Q9'<'I'6&SOr5r4r3r2r1%6554321&SN%1576543%;3:31pmB=1pQP4?1pQU8@1pmJB1pQS0C1").
Proof.
intros s e v lo cnt. revert lo. induction cnt as [|c IH]; intros lo; cbn [all_eval_toS all_eval_to]; [reflexivity|].
rewrite evalS_eq. destruct (eval_closed (esubst s (ELit lo) e)) as [w|]; [|reflexivity].
destruct (Z.eqb w v); [apply IH | reflexivity].
Qed.
#[using="Type"] Lemma probeS_eq : forall s e v z,
probeS s e v z = match eval_closed (esubst s (ELit z) e) with Some w => Z.eqb w v | None => false end.
Proof. intros. unfold probeS. rewrite evalS_eq. reflexivity. Qed.
#[using="Type"] Lemma conc_try_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q?';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9%?11'Q9&\<r7r6r5r4%544321'I%A18&TAr3%23761(3r2%22>1%83741&TLr8%221>&aN%12O:%>3O31p071p0A1pQU8H1pm>J1pmJL1poFN1pV@Q11pRFQ:1pQS:Q<1").
Proof.
intros segs E M kn e cands v Hkn. induction cands as [|c rest IH]; cbn [conc_try]; intros H; [discriminate|].
destruct (closedb c); [apply IH; exact H|].
destruct (negb (evalS_def c e)); [apply IH; exact H|].
destruct (erange kn c) as [[lo hi]|] eqn:Hr; [|apply IH; exact H].
destruct (Z.leb (hi - lo) conc_limit); [|apply IH; exact H].
rewrite evalS_eq in H.
destruct (eval_closed (esubst c (ELit lo) e)) as [v0|] eqn:Hv0; [|apply IH; exact H].
destruct (if Z.ltb hi lo then true else if probeS c e v0 hi then probeS c e v0 (lo + (hi - lo) / 2)%Z else false);
[|apply IH; exact H].
rewrite all_eval_toS_eq in H.
destruct (all_eval_to c e v0 lo (Z.to_nat (hi - lo + 1))) eqn:Hall; [|apply IH; exact H].
injection H as <-.
pose proof (erange_sound segs E M kn c lo hi Hkn Hr) as Hb.
pose proof (all_eval_to_sound c e v0 lo _ Hall (bv_unsigned (edenot E c)) ltac:(rewrite Z2Nat.id by lia; lia)) as He.
rewrite <- (esubst_sound E c (ELit (bv_unsigned (edenot E c))) e) by (cbn [edenot]; apply Z_to_bv_bv_unsigned).
apply eval_closed_sound. exact He.
Qed.
#[using="Type"] Lemma concretize_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q<';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r6r5r4r3%544321'I%@18&TB%1265(3r2%22=1%73641&TLr7%221=&aN%12M>%=3M31p071p0@1pQU8G1pmJI1poFK1pV@N1pRFQ71pQS:Q91").
Proof.
intros segs E M kn e v Hkn H. unfold concretize in H.
destruct (closedb e); [apply eval_closed_sound; exact H | eapply conc_try_sound; eassumption].
Qed.
#[using="Type"] Lemma foldK_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r5r4r3r2%544321'I&TL&UK%1265%3291%42:7%63E21p081pmJ?1poFA1plJD1pRFM1pQS:O1").
Proof.
intros segs E base kn e Hkn. unfold foldK.
assert (CC : edenot E (match concretize kn e with Some v => ELit v | None => e end) = edenot E e).
{ destruct (concretize kn e) as [v|] eqn:Hc; [|reflexivity].
cbn [edenot]. symmetry. eapply concretize_sound; eassumption. }
destruct e as [x|i|op a b|op a b|op a b|op a b|sx lo n e1|sx k i n]; try reflexivity;
lazymatch goal with |- edenot E (match erange kn ?e0 with _ => _ end) = _ =>
destruct (erange kn e0) as [[lo' hi']|] eqn:Hr; [|exact CC];
destruct (Z.eqb lo' hi') eqn:Hq; [|exact CC];
apply Z.eqb_eq in Hq; subst hi';
pose proof (erange_sound segs E base kn e0 lo' lo' Hkn Hr) as Hb;
pose proof (u64_range (edenot E e0)) as Hu;
set (v := edenot E e0) in *;
cbn [edenot]; apply bv_eq; rewrite Z_to_bv_unsigned;
rewrite bv_wrap64_mod, Z.mod_small by lia; lia
end.
Qed.
#[using="Type"] Lemma mkSlt_denot : forall segs E base kn c op a b,
know_ok segs E base kn ->
(forall x y, alu64 op x y = if branch_taken c x y then Z_to_bv 64 1 else Z_to_bv 64 0) ->
edenot E (mkSlt kn c op a b) = alu64 op (edenot E a) (edenot E b).
Proof.
intros segs E base kn c op a b Hkn Hop. unfold mkSlt.
assert (Hd : forall t, decide_branch kn c a b = Some t ->
edenot E (if t then ELit 1 else ELit 0) = alu64 op (edenot E a) (edenot E b)).
{ intros t Ht. rewrite Hop. rewrite (decide_branch_sound segs E base kn c a b t Hkn Ht). destruct t; reflexivity. }
destruct a; destruct b; try apply mkAlu_denot;
(destruct (decide_branch kn c _ _) as [[|]|]; [exact (Hd true eq_refl) | exact (Hd false eq_refl) | apply mkAlu_denot]).
Qed.
#[using="Type"] Lemma mkAluK0_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q:';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'RF'U9&\<r7r6r5r4%544321'I&TL&WIr3r2%348721%52;1&S1%72=5%82>5%33<21%;3K51p0=1plBD1pkNE1pQQ@G1poFI1plJL1pRFQ51pQS:Q71").
Proof.
intros segs E base kn op a b Hkn. unfold mkAluK0. destruct op; try apply mkAlu_denot.
1: { eapply mkSlt_denot; [exact Hkn|]. intros x y. rewrite alu_slt. reflexivity. }
1: { eapply mkSlt_denot; [exact Hkn|]. intros x y. rewrite alu_sltu. reflexivity. }
- destruct (expr_eqb a b) eqn:Heq.
{ apply expr_eqb_eq in Heq. subst b. cbn [edenot]. rewrite alu_xor. unfold v_xor. rewrite Z.lxor_nilpotent. reflexivity. }
destruct (is_lit a); [apply mkAlu_denot|]. destruct b as [k| | | | | | |]; try apply mkAlu_denot.
destruct (Z.eqb (k mod two64) (two64 - 1)) eqn:Hk; [|apply mkAlu_denot].
apply Z.eqb_eq in Hk. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_sub, alu_xor. unfold v_sub, v_xor.
pose proof (u64_range (edenot E a)) as Hr.
assert (Hb : bv_unsigned (Z_to_bv 64 k) = (2 ^ 64 - 1)%Z).
{ rewrite Z_to_bv_unsigned, bv_wrap64_mod. unfold two64 in Hk. exact Hk. }
rewrite Hb, u_small by (unfold two64; lia). f_equal. symmetry. apply lxor_ones64. exact Hr.
- destruct (is_lit a); [apply mkAlu_denot|].
destruct (shamt_of b 6) as [sh|] eqn:Hs; [|apply mkAlu_denot].
destruct (shamt_of_sound E b 6 sh ltac:(lia) Hs) as [Hm Hr]. change (2 ^ 6)%Z with 64%Z in Hm.
eapply mkSrl_denot; [exact Hkn | exact Hm].
- destruct (expr_eqb a b) eqn:Heq; [|eapply mkOr_denot; exact Hkn].
apply expr_eqb_eq in Heq. subst b. rewrite alu_or. unfold v_or. rewrite Z.lor_diag. symmetry. apply Z_to_bv_bv_unsigned.
-
assert (Hcomm : alu64 ALU_AND (edenot E b) (edenot E a) = alu64 ALU_AND (edenot E a) (edenot E b)).
{ rewrite !alu_and. unfold v_and. rewrite Z.land_comm. reflexivity. }
destruct a; destruct b; try (eapply mkAnd_denot; exact Hkn); try (eapply mkAndK_denot; exact Hkn);
rewrite <- Hcomm; first [eapply mkAndK_denot; exact Hkn | eapply mkAnd_denot; exact Hkn].
Qed.
#[using="Type"] Lemma mkAluK_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q:';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'RF'U9&\<r7r6r5r4%544321'I&TL&WHr3r2%348721%52;1&S1%72=5%82>5%33<21%;3K51p0=1plBD1pkNE1pQQ@G1poFI1plJL1pRFQ51pQS:Q71").
Proof.
intros segs E base kn op a b Hkn. unfold mkAluK.
rewrite (foldK_denot segs E base kn _ Hkn). eapply mkAluK0_denot. exact Hkn.
Qed.
#[using="Type"] Lemma pow2_log_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "O'Q9'I'>%113&X=r2%211(3r1%2291%93741'H&]<z%2219&]A+R0%22<1%7241&]Dr3&Z=%3221&]I+2%221D%I3J41%@291p0B1po8M1pQP<N1").
Proof.
intros m k H. unfold pow2_log in H.
destruct (Z.ltb 0 (m mod two64) && Z.eqb (m mod two64) (2 ^ Z.log2 (m mod two64)) && Z.ltb (Z.log2 (m mod two64)) 64)%bool eqn:Hb;
[|discriminate].
injection H as <-.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.ltb_lt in H3.
split; [split; [apply Z.log2_nonneg | exact H3] | exact H2].
Qed.
#[using="Type"] Lemma mkMdK_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q:';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'RL'U9&\<r7r6r5r4%544321'I&TL&X2r3r2%348721%52;1&S6%72=5%82>5%34K<21%;3K51p0=1plBD1pkNE1pQQ@G1poFI1plJL1pRFQ51pQS:Q71").
Proof.
intros segs E base kn op a b Hkn. unfold mkMdK.
destruct (is_lit a) as [x|] eqn:Ha; [apply mkMd_denot|].
destruct op; try apply mkMd_denot; destruct b as [m| | | | | | |]; try apply mkMd_denot;
destruct (pow2_log m) as [k|] eqn:Hp; try apply mkMd_denot;
destruct (pow2_log_sound m k Hp) as [Hk Hm];
rewrite (mkAluK_denot segs E base kn _ _ _ Hkn); cbn [edenot mul_div];
assert (Hb : bv_unsigned (Z_to_bv 64 m) = (2 ^ k)%Z)
by (rewrite Z_to_bv_unsigned, bv_wrap64_mod; unfold two64 in Hm; exact Hm);
rewrite Hb; (replace (Z.eqb (2 ^ k) 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 k); lia));
apply bv_eq.
- rewrite alu_srl. unfold v_srl. rewrite bv_divu_unsigned, Hb.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
assert (Hk' : (bv_unsigned (Z_to_bv 64 k) mod 64 = k)%Z).
{ rewrite Z_to_bv_unsigned, bv_wrap64_mod. unfold two64. rewrite (Z.mod_small k (2^64)) by lia. apply Z.mod_small. lia. }
rewrite Hk'. rewrite Z.shiftr_div_pow2 by lia.
pose proof (u64_range (edenot E a)) as Hr.
pose proof (Z.div_pos (bv_unsigned (edenot E a)) (2 ^ k) ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (bv_unsigned (edenot E a)) (2 ^ k) (2 ^ 64)) as Hu.
rewrite Z.mod_small; [reflexivity|]. split; [lia|].
apply Hu; [lia|]. pose proof (Z.pow_pos_nonneg 2 k). nia.
- rewrite alu_and. unfold v_and. rewrite bv_modu_unsigned, Hb.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
assert (Hm1 : bv_unsigned (Z_to_bv 64 (2 ^ k - 1)) = (2 ^ k - 1)%Z).
{ rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. unfold two64.
split; [pose proof (Z.pow_pos_nonneg 2 k); lia|]. apply Z.lt_le_trans with (m := (2 ^ k)%Z); [lia|].
apply Z.pow_le_mono_r; lia. }
rewrite Hm1. change (2 ^ k - 1)%Z with (Z.pred (2 ^ k)). rewrite <- Z.ones_equiv. rewrite Z.land_ones by lia.
pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a)) (2 ^ k) ltac:(lia)) as Hr.
rewrite Z.mod_small; [reflexivity|]. unfold two64. split; [lia|].
apply Z.lt_le_trans with (m := (2 ^ k)%Z); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
#[using="Type"] Lemma swrap32_neg : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N'Q9'H&]<&]J&]I+2+R0%3221+O%5241%7231r1%:221&]A%1237%>231'I'aOyR0%211&aN&b3yQ0r2%3221%5271%6283%;3821p0=1pQU8M1").
Proof.
intros v Hv. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
replace ((v + 2 ^ 31) mod 2 ^ 32)%Z with (v + 2 ^ 31 - 2 ^ 64)%Z.
- replace (v + 2 ^ 31 - 2 ^ 64 - 2 ^ 31)%Z with (v + (-1) * 2 ^ 64)%Z by lia.
rewrite Z.mod_add by lia. reflexivity.
- symmetry. rewrite <- (Z.mod_add _ (- 2 ^ 32) _) by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma mkAluwK0_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q@';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'RF'U9&\<r7r6r5r4%544321'I&TL&WLr3r2%348721%52;1&RNyQ0&S0&S5%:2@8%211%<2B9%411%63A31%938Q11%A3Q1;1p0C1plBJ1pkNK1pQQ@M1poFO1plJQ21pRFQ;1pQS:Q=1").
Proof.
intros segs E base kn op a b Hkn. unfold mkAluwK0.
assert (Hgen : forall (f : Z -> Z -> Z),
(forall x y : word, (sext 64 (alu32 op (low32 x) (low32 y)) : word) = Z_to_bv 64 (bv_swrap 32 (f (bv_unsigned x) (bv_unsigned y)))) ->
(forall x y : word, bv_unsigned (alu64 op x y) = ((f (bv_unsigned x) (bv_unsigned y)) mod 2 ^ 64)%Z) ->
edenot E (let d := mkAlu op a b in
match is_lit d with
| Some v => ELit (zsx32 v)
| None => match erange kn d with
| Some (lo, hi) => if sx32_stable lo hi then d else if zband32 kn d then d else mkAluw op a b
| None => if zband32 kn d then d else mkAluw op a b
end
end) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))).
{ intros f Hw Hu. cbn zeta.
pose proof (mkAlu_denot E op a b) as Hm.
assert (Hcongr : bv_swrap 32 (f (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)))
= bv_swrap 32 (bv_unsigned (edenot E (mkAlu op a b)))).
{ rewrite Hm, Hu. symmetry.
pose proof (Z.div_mod (f (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))) (2 ^ 64) ltac:(lia)) as D.
set (t := f _ _) in *. set (q := (t / 2 ^ 64)%Z) in *.
replace (t mod 2 ^ 64)%Z with (t + (- q * 2 ^ 32) * 2 ^ 32)%Z by lia.
apply swrap32_shift. }
destruct (is_lit (mkAlu op a b)) as [v|] eqn:Hl.
- apply is_lit_some in Hl. rewrite Hw, Hcongr, Hl. cbn [edenot]. unfold zsx32.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64. rewrite Z.mod_mod by lia.
f_equal. apply bv_swrap_congr. unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32)%Z.
symmetry. apply Z.mod_mod_divide. exists (2 ^ 32)%Z. reflexivity.
- assert (ZB : zband32 kn (mkAlu op a b) = true ->
edenot E (mkAlu op a b) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))).
{ intros Hz. unfold zband32 in Hz.
destruct (lin_range (erange kn) (fst (lin_of (mkAlu op a b))) (snd (lin_of (mkAlu op a b)))) as [[zlo zhi]|] eqn:Hlr;
[|discriminate].
apply andb_prop in Hz as [Hz1 Hz2]. apply Z.ltb_lt in Hz1. apply Z.ltb_lt in Hz2.
pose proof (lin_range_sound E (erange kn) (fun a0 lo0 hi0 Ha0 => erange_sound segs E base kn a0 lo0 hi0 Hkn Ha0) _ _ _ _ Hlr) as HL.
pose proof (lin_of_sound E (mkAlu op a b)) as [q Hq]. unfold lden, uE in Hq.
set (L := (fst (lin_of (mkAlu op a b)) + tden E (snd (lin_of (mkAlu op a b))))%Z) in *.
rewrite Hw, Hcongr.
set (u := bv_unsigned (edenot E (mkAlu op a b))) in *.
replace u with (L + (- q * 2 ^ 32) * 2 ^ 32)%Z by lia. rewrite swrap32_shift.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (mkAlu op a b))). fold u.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Hq. symmetry. apply Z.mod_add. lia. }
destruct (erange kn (mkAlu op a b)) as [[lo hi]|] eqn:Hr; [|destruct (zband32 kn (mkAlu op a b)) eqn:Hz; [exact (ZB eq_refl)|apply mkAluw_denot]].
destruct (sx32_stable lo hi) eqn:Hhi; [|destruct (zband32 kn (mkAlu op a b)) eqn:Hz; [exact (ZB eq_refl)|apply mkAluw_denot]].
unfold sx32_stable in Hhi. pose proof (erange_sound segs E base kn _ lo hi Hkn Hr) as Hb.
pose proof (u64_range (edenot E (mkAlu op a b))) as Hr2.
rewrite Hw, Hcongr. apply orb_prop in Hhi as [Hhi|Hlo].
+ apply Z.ltb_lt in Hhi. rewrite swrap32_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
+ apply Z.leb_le in Hlo. unfold two64 in Hlo. rewrite swrap32_neg by lia. symmetry. apply Z_to_bv_bv_unsigned. }
destruct op; try apply mkAluw_denot.
- apply (Hgen (fun x y => (x + y)%Z)); [intros; rewrite w_addw; reflexivity | intros; apply u_add64].
- apply (Hgen (fun x y => (x - y)%Z)); [intros; rewrite w_subw; reflexivity | intros; apply u_sub64].
Qed.
#[using="Type"] Lemma mkAluwK_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q@';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'RF'U9&\<r7r6r5r4%544321'I&TL&WKr3r2%348721%52;1&RNyQ0&S0&S5%:2@8%211%<2B9%411%63A31%938Q11%A3Q1;1p0C1plBJ1pkNK1pQQ@M1poFO1plJQ21pRFQ;1pQS:Q=1").
Proof.
intros segs E base kn op a b Hkn. unfold mkAluwK.
rewrite (foldK_denot segs E base kn _ Hkn). eapply mkAluwK0_denot. exact Hkn.
Qed.
#[using="Type"] Lemma extK0_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r5r4r3r2%544321'I&TL&U<%1265%3291%42:7%63E21p081pQU8?1poFA1plJD1pRFM1pQS:O1").
Proof.
intros segs E base kn v Hkn. unfold extK0.
destruct v as [x|i|op a b|op a b|op a b|op a b|sx lo n e|sx k i n]; try reflexivity.
destruct lo; [|reflexivity].
destruct (Nat.leb n 7) eqn:Hn7; [|reflexivity].
destruct (erange kn e) as [[lo hi]|] eqn:Hr; [|reflexivity].
destruct (Z.ltb hi _) eqn:Hhi; [|reflexivity]. apply Z.ltb_lt in Hhi.
pose proof (erange_sound segs E base kn e lo hi Hkn Hr) as Hb.
cbn [edenot]. symmetry. apply bv_eq. destruct sx.
- apply u_ext_sx0_small. lia.
- apply u_ext_zx0_small. lia.
Qed.
#[using="Type"] Lemma extK_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r5r4r3r2%544321'I&TL&U;%1265%3291%42:7%63E21p081pQU8?1poFA1plJD1pRFM1pQS:O1").
Proof.
intros segs E base kn v Hkn. unfold extK.
rewrite (foldK_denot segs E base kn _ Hkn). eapply extK0_denot. exact Hkn.
Qed.
#[using="Type"] Lemma flat_sc_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QJ';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'Y4'<'Y=%A11&\<r7r6r5r4%544321'Q0u1r3%3221u8%5271&\Ar:r8r9&5&UJ%13A@?%33E1?%847651'H&\:&]G%11F%33<H1r;%?41<>H%7231p091p0C1p0F1p0K1pQR6Q21pQPJQ51pkNQ71poFQ91plJQ<1pRFQE1pQS:QG1").
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
#[using="Type"] Lemma conc_expr_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9&\<r5r4r3r2%544321'I&TL&T@%1265%3291%42:7%63E21p081pmJ?1poFA1pV@D1pRFM1pQS:O1").
Proof.
intros segs E M kn e Hkn. unfold conc_expr.
assert (Hg : forall e', edenot E (match concretize kn e' with Some v => ELit v | None => e' end) = edenot E e').
{ intros e'. destruct (concretize kn e') as [v|] eqn:Hc; [|reflexivity].
symmetry. exact (concretize_sound segs E M kn e' v Hkn Hc). }
destruct e; try reflexivity; apply Hg.
Qed.
#[using="Type"] Lemma enum_branch_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QB';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'RI'U9'6&\<r8r7r6r5%544321'I%A18&TOr4r3%348721(3r2%22?1%93841&S4&TLr9%221?%322;%53B21%@3G1<p081p0C1pQTFJ1plBL1pkNM1pm8O1poFQ11pV@Q41pRFQ=1pQS:Q?1").
Proof.
intros segs E M kn c a b t Hkn H. unfold enum_branch in H.
destruct (cond_probe c a b) as [e pos] eqn:Hp.
destruct (concretize kn e) as [v|] eqn:Hc; [|discriminate]. injection H as <-.
pose proof (concretize_sound segs E M kn e v Hkn Hc) as Hv.
assert (Huv : bv_unsigned (edenot E e) = (v mod two64)%Z) by (rewrite Hv; apply u_lit64).
set (x := edenot E a) in *. set (y := edenot E b) in *.
pose proof (u64_range x) as Rx. pose proof (u64_range y) as Ry.
assert (SUB : e = EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z) -> (Z.eqb (v mod two64) 0 = negb (bv_eqb x y))).
{ intros ->. cbn [edenot] in Huv. fold x y in Huv. rewrite alu_sltu in Huv. unfold v_sltu, c_ltu, bv_ltu in Huv.
rewrite u_sub64, (u_small 1) in Huv by lia. unfold bv_eqb.
assert (D : ((bv_unsigned x - bv_unsigned y) mod 2 ^ 64 = 0)%Z <-> bv_unsigned x = bv_unsigned y).
{ split.
- intros Hz. destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned y)).
+ rewrite <- (Z.mod_add _ 1) in Hz by lia. rewrite Z.mod_small in Hz by lia. lia.
+ rewrite Z.mod_small in Hz by lia. lia.
- intros ->. rewrite Z.sub_diag. apply Z.mod_0_l. lia. }
pose proof (Z.mod_pos_bound (bv_unsigned x - bv_unsigned y) (2 ^ 64) ltac:(lia)) as Hm.
destruct (Z.ltb_spec ((bv_unsigned x - bv_unsigned y) mod 2 ^ 64) 1) as [Hl|Hl];
rewrite u_lit64 in Huv; unfold two64 in *; rewrite <- Huv; cbn.
+ destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E1|N1]; [reflexivity|]. exfalso. apply N1, D. lia.
+ destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E1|N1]; [|reflexivity]. exfalso. apply D in E1. lia. }
assert (SLTU : e = EAlu ALU_SLTU a b -> (Z.eqb (v mod two64) 0 = negb (bv_ltu x y))).
{ intros ->. cbn [edenot] in Huv. fold x y in Huv. rewrite alu_sltu in Huv. unfold v_sltu, c_ltu in Huv.
destruct (bv_ltu x y); rewrite u_lit64 in Huv; unfold two64 in *; rewrite <- Huv; reflexivity. }
assert (SLT : e = EAlu ALU_SLT a b -> (Z.eqb (v mod two64) 0 = negb (bv_lts x y))).
{ intros ->. cbn [edenot] in Huv. fold x y in Huv. rewrite alu_slt in Huv. unfold v_slt, c_lts in Huv.
destruct (bv_lts x y); rewrite u_lit64 in Huv; unfold two64 in *; rewrite <- Huv; reflexivity. }
destruct c; cbn [cond_probe] in Hp; injection Hp as <- <-; cbn [branch_taken];
first [ rewrite (SUB eq_refl) | rewrite (SLTU eq_refl) | rewrite (SLT eq_refl) ];
try reflexivity;
first [ destruct (bv_eqb x y); reflexivity
| destruct (bv_lts x y); reflexivity
| destruct (bv_ltu x y); reflexivity ].
Qed.
#[using="Type"] Lemma to_saddrK_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q8';'QF%211'U0'aOyR0%211'>y8%511%311p051'V7%=11'U9'Q9&\<r6r5r4r3%544321'I&SM&Z<r2%23761%42:1&\I&TL%12=:%3216%:3J51p0<1po4C1pmJE1poFG1pV@J1pRFQ31pQS:Q51").
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
Definition resv_denot (E : env) (r : option saddr) : option word :=
match r with Some a => Some (adenot E a) | None => None end.
Definition st_okR (E : env) (base rom : word -> option byte)
(ss : sym_state) (ms : machine_state) : Prop :=
exists regs, ms = mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
(resv_denot E (s_resv ss))
/\ regs_ok E (s_regs ss) regs
/\ log_flat E (s_log ss)
/\ know_ok segs E base (s_know ss).
#[using="Type"] Lemma st_ok_R : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "M'U0'aOyR0%211'>y8%511%311p051'Z8'QN&[Kr5r4r3r2r1%6554321&[Lr6&T=%117%453:917p061pQPF>1pQSF@1pQRFB1plJC1pRFL1").
Proof.
intros E base rom ss ms (regs & -> & HR & HL & HK). exists regs.
split; [reflexivity|]. split; [exact HR|]. split; [exact HL|exact HK].
Qed.
#[using="Type"] Lemma st_okR_ok : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'U0'aOyR0%211'>y8%511%311p051'Z8'QN&[Lr5r4r3r2r1%6554321'I'Y4%@11&Y3%118(0%115%73531&[Kr7r6%3521A@?p051p0>1pQPFF1pQSFH1pQRFJ1plJK1pRFQ41").
Proof.
intros E base rom ss ms (regs & -> & HR & HL & HK) Hr. exists regs. rewrite Hr.
split; [reflexivity|]. split; [exact HR|]. split; [exact HL|exact HK].
Qed.
#[using="Type"] Lemma s_clean_None : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'Z8&K'I'6&XMr1%211(C%63521'>'Y4%211&Y3%118(0%115%>3531%@291pQSFB1").
Proof. intros ss. unfold s_clean. destruct (s_resv ss); split; intros H; congruence. Qed.
#[using="Type"] Lemma s_resv_clr : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'Z8'I'>'Y4%211&Y3&T=r1%211%411(0%118%;3831pQSF=1").
Proof. reflexivity. Qed.
#[using="Type"] Lemma msize_bytes_range : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "<'RK'H'Q0u1&X7r1%211%5241u8%7231%9231pQTD;1").
Proof. destruct sz; cbn; lia. Qed.
#[using="Type"] Lemma msize_bytes_R : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'RK'I'<&]1r1%211&X7%113%73631pQTD91").
Proof. destruct sz; reflexivity. Qed.
#[using="Type"] Lemma amo_nbytes_sz : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "<'RH'I'<&\Lr1%211&X7&T4%114%311%93851pQUD;1").
Proof. destruct wd; reflexivity. Qed.
#[using="Type"] Lemma amo_msize_sz : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'RH'I'RK&\Kr1%211&T4%113%73631pQUD91").
Proof. destruct wd; reflexivity. Qed.
#[using="Type"] Lemma v_addi_0 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ":'aOyR0%211'I&\Ir1z%3221%53613pQUL71").
Proof. intros x. unfold v_addi. apply Z_to_bv_u_plus0. Qed.
#[using="Type"] Lemma wrap_swrap : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='Q8'Q9'I&b5r2&b3r1%2231%5241%6253%83921pQV2:1pQPJ<1").
Proof. intros n z. unfold bv_swrap, bv_wrap. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.
#[using="Type"] Lemma low32_sext64_32 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "<'aOyQ0%211'I&S5&RNyR0r1%33721%511%73813pQU891").
Proof.
intros v. apply bv_eq. rewrite low32_unsigned, sext32_unsigned.
rewrite bv_wrap_bv_wrap by lia. rewrite wrap_swrap. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
#[using="Type"] Lemma sym_read_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "SH'U0'aOyR0%211'>y8%511%311p051'Z8'Y9'Y4'<'6'U9';'Y=%211'I'A%1263%221;%321:%C11&Z7vaDr9&UC&XN%113%311r8r7r6r5%;7:954321(3(@r4r3%34JG21r2%54FQ021r1%74GQ021%92G1%L3G;1&\Ar;r<%34I21<&\=r=&XO%116%4231&\<r>%N19%34Q2271'Q0u1r:%3221u8%52A1'H&\:rA&]G%11E%433C1'J%QJ1R3%R611&\H&\>rBr@%J11%433<1&SM%125I%84QJ31O%Q@2;Q9%R33;21&:%12RAQ<%R63R<1Q4&aN&\9&QD%11QA%33Q<Q91%52RL1&TL%12CQ@%R?3RN31%Q02:1%Q12>1qm4K1%M2L1%Q42O1p0Q61p0Q91p0Q>1p0QC1p0QI1p0QN1pQQ<S11pQS6S41pQS8RN1pQU8S21pQTBS41pQPJS61pkNS81pQS4S:1pQSFS<1plJS>1pRFSG1").
Proof.
intros E base ss scr a n sx' v scs scr' nx' Hs Hsc Hlf Hkn Hn1 Hn8.
set (mem := mem_denot E base (s_log ss)) in *.
pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
unfold sym_read in Hs.
pose proof (log_lookup_sound segs E base fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] Hfk Hlf Hn1 Hn8) as HL.
destruct (log_lookup fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) as [v0 lscs lh|lscs lh|] eqn:Hll;
[ | | discriminate].
-
injection Hs as <- <- <- <-.
apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
split; [exact Hfl|].
destruct (HL Hsc ltac:(destruct a; exact Hfl)) as (bs & Hrd & Hlen & Hval).
exists bs. split; [destruct a; exact Hrd|]. split; [exact Hlen|].
rewrite (extK_denot segs E base fk v0 Hfk). exact Hval.
-
pose proof (know_lookupA_sound segs E base fk base (s_know ss) (a_base a) (a_off a) n sx' lh lscs Hfk Hkn Hn1 Hn8) as HK.
pose proof (know_lookupA_acc fk segs (s_know ss) (a_base a) (a_off a) n sx' lh lscs) as HKacc.
destruct (know_lookupA fk segs (s_know ss) (a_base a) (a_off a) n sx' lh lscs) as [v0 kscs kh|kscs kh|] eqn:Hkl;
[ | | discriminate].
+
injection Hs as <- <- <- <-.
apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
split; [exact Hfl|].
destruct HKacc as [pre ->].
assert (Hlscs : scs_denot segs base E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
destruct (HK Hsc ltac:(destruct a; exact Hfl)) as (bs & Hrd & Hlen & Hval).
exists bs. split.
* destruct a; cbn [a_base a_off] in *. unfold mem. rewrite (HL Hlscs Hfl). exact Hrd.
* split; [exact Hlen|]. rewrite (extK_denot segs E base fk v0 Hfk). exact Hval.
+
injection Hs as <- <- <- <-.
apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
split; [exact Hfl|].
apply scs_denot_cons in Hsc as [Hrb Hsc]. cbn [sc_denot] in Hrb.
destruct Hrb as (bs & Hrd & Hval).
destruct HKacc as [pre ->].
assert (Hlscs : scs_denot segs base E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
assert (Hrd' : rdn segs mem (adenot E a) n = Some bs).
{ destruct a; cbn [a_base a_off] in *. unfold mem. rewrite (HL Hlscs Hfl). exact Hrd. }
exists bs. split; [exact Hrd'|]. split; [exact (rdn_length _ _ _ _ _ Hrd')|]. exact Hval.
Qed.
#[using="Type"] Lemma storeok_sc_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QI'U0'aOyR0%211'>y8%511%311p051';'V7%211'Y4'<&\<vaDr5r4r3%544321&\:r6&]Gr2%211%53471'Q0u1%221:u8%42=1&\Ar8r9&YFr7%231?D%64F541'I'6&R2&SMr:%2218%44M;1G(C%83721p0:1p0B1p0E1p0I1p0Q01pQPJQ71pkNQ91pn4Q;1plJQ?1pRFQH1").
Proof.
intros E base fk a n Hfk Hfl Hn1 Hn8 Hsc.
unfold storeok_sc in Hsc.
destruct (wr_covered fk fk a n) eqn:Hw.
- clear Hsc. revert Hw. pose proof Hfk as Hall. generalize Hfk. generalize fk at 1 3 as kn. intros kn Hkn0 Hw.
induction kn as [|K rest IH]; cbn [wr_covered] in Hw; [discriminate|].
apply Forall_cons_iff in Hkn0 as [HK Hrest].
destruct K as [| | | | | |[kb kk] len| | |]; try (apply IH; assumption).
cbn [kentry_ok] in HK. destruct HK as [Hflk Hs0]. unfold elenZ in Hflk, Hs0.
match type of Hw with (if ?c then _ else _) = _ => destruct c eqn:Hc end.
{ destruct (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool eqn:H12; [|discriminate].
apply andb_prop in H12 as [H1 H2].
apply expr_eqb_eq in H1. apply Z.leb_le in H2.
destruct (xlo fk len) as [l|] eqn:Hxl; [|discriminate]. apply Z.leb_le in Hc. rename Hc into H3.
pose proof (xlo_sound segs E base fk len l Hall Hxl) as Hl.
replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (a_off a - kk))).
+ apply Hs0; lia.
+ apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite <- H1.
destruct Hfl as (?&?&?&?). unfold estart in *. rewrite u_small by lia. lia. }
match type of Hw with (if ?c then _ else _) = _ => destruct c eqn:Hxi; [|apply IH; assumption] end.
destruct (xinside_sound segs E base fk _ _ _ _ _ _ Hall Hxi) as [I1 I2].
replace (SA (a_base a) (a_off a)) with a in I1, I2 by (destruct a; reflexivity).
unfold elenZ in I2. cbn [edenot] in I2. rewrite u_lit64 in I2. unfold two64 in I2. rewrite Z.mod_small in I2 by lia.
replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (estart E a - estart E (SA kb kk)))).
+ apply Hs0; lia.
+ apply bv_eq. rewrite (flat_u E _ _ Hfl).
destruct Hfl as (?&?&?&?). rewrite u_small by lia. lia.
- apply scs_denot_cons in Hsc as [Hok _]. cbn [sc_denot] in Hok. exact Hok.
Qed.
#[using="Type"] Lemma resv_inval_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'U0'>'Y4%211'I%412&XKr3r2%3221(3r1%2291%93841'aOyR0%211%@11&]2&[Jr5r4%3221&SM%124A%7231%726B%G3:21p0?1pQQLJ1pkNL1pQQJL1pRFQ01").
Proof.
intros E r a r' H. unfold resv_inval in H. destruct r as [ra|].
- destruct (saddr_eqb ra a) eqn:Heq.
+ injection H as <-. apply saddr_eqb_eq in Heq. subst ra. cbn. rewrite Z.eqb_refl. reflexivity.
+ destruct (expr_eqb (a_base ra) (a_base a) && negb (Z.eqb ((a_off ra - a_off a) mod two64) 0))%bool eqn:Hc;
[|discriminate].
injection H as <-. apply andb_prop in Hc as [Hb Hne]. apply expr_eqb_eq in Hb.
apply negb_true_iff in Hne. apply Z.eqb_neq in Hne.
cbn [resv_denot resv_inval_w].
destruct (Z.eqb (bv_unsigned (adenot E ra)) (bv_unsigned (adenot E a))) eqn:Hz; [|reflexivity].
exfalso. apply Z.eqb_eq in Hz. apply Hne.
unfold adenot, v_addi in Hz. rewrite Hb in Hz. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hz.
unfold two64.
set (u := bv_unsigned (edenot E (a_base a))) in *.
replace (a_off ra - a_off a)%Z with ((u + a_off ra) - (u + a_off a))%Z by lia.
rewrite Zminus_mod, Hz, Z.sub_diag. reflexivity.
- injection H as <-. reflexivity.
Qed.
#[using="Type"] Lemma amo_alignedb_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q>'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'RH&\<vaDr5r4r3%544321'I'6&T1r2%23761(C%63521'Q9&]D&b4&TLr7%221?%42O1&S2%11A%8231z%B3;21p0=1p0E1pQUDL1pmJN1poFQ01pV@Q41pRFQ=1").
Proof.
intros E M kn e wd Hkn H. unfold amo_alignedb in H.
set (k := match wd with AW => 2%Z | AD => 3%Z end) in H.
destruct (lin_lowbits_kn kn e k) as [r|] eqn:Hl; [|discriminate].
apply Z.eqb_eq in H. subst r.
assert (Hk : (0 <= k <= 64)%Z) by (subst k; destruct wd; lia).
destruct (lin_lowbits_kn_sound segs E M kn e k 0 Hkn Hk Hl) as [Hm _].
replace (amo_bytes wd) with (2 ^ k)%Z by (subst k; destruct wd; reflexivity).
exact Hm.
Qed.
#[using="Type"] Lemma amo_val_alu32 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "M'RG'RF'aOyQ0%211'I'>%116%211&T2r4%211(3r3%22=1%3281%;3851&S3r5r2%34A271&S0%13<93%B3C31p081plBE1pkNF1pQQ>J1pQQ@L1").
Proof. intros op o a b H; destruct op; cbn in H; try discriminate; injection H as <-; reflexivity. Qed.
#[using="Type"] Lemma amo_val_alu64 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "M'RG'RF'aOyR0%211'I'>%116%211&T2r4%211(3r3%22=1%3281%;3851&S3r5r2%34A271&S1%13<93%B3C31p081plBE1pkNF1pQQ>J1pQQ@L1").
Proof. intros op o a b H; destruct op; cbn in H; try discriminate; injection H as <-; reflexivity. Qed.
#[using="Type"] Lemma amo_val_swap : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "O'RG'Q8'aOr1%211r2%411'I'>'RF%211%311&T2r4%211(3(0%118%3281%<3851%B17&S3r5r3%34;21C%B351Dp071plBE1pkNH1pQPJL1pQQ@N1").
Proof. intros op n a b H; destruct op; cbn in H; try discriminate; reflexivity. Qed.
#[using="Type"] Lemma amo_store_bytes_newval : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R<'U0'aOyR0%211'>y8%511%311p051';'V7%211'RG'RF%:11'RH%71:'U9&\<vaDr9r8r7%544321'I%E1;&T2%115(3r6%22@1%73641'<&:r5%22M1&X7&T4%119%311%@3851&TLr<%2219&\O%81G(C%3321B%H3Q=51&\Mr:r=%;21B%443Q0O1&R3%B1Q2%D11&T3r;%251Q6Q7NI%C291%7251%Q63Q>91p0?1p0H1p0Q21p0Q;1pQSDQB1pQU:QC1pm4QE1pQUDQG1pl<QI1pQQ@QL1pn4QN1pV@R21pRFR;1").
Proof.
intros E M fk op aop wd bs vold src Hfk Hop Hlen Hold.
unfold amo_store_bytes, amo_newval.
destruct wd; cbn [amo_sz msize_bytes] in *.
-
destruct aop as [o|].
+ rewrite (mkAluwK_denot segs E M fk o vold src Hfk). cbn [edenot]. rewrite Hold.
unfold load_result. rewrite low32_sext64_32.
rewrite (amo_val_alu32 op o _ _ Hop).
rewrite <- store_bytes_low32, low32_sext64_32. reflexivity.
+ rewrite (amo_val_swap op 32 _ _ Hop). apply store_bytes_low32.
-
destruct aop as [o|].
+ rewrite (mkAluK_denot segs E M fk o vold src Hfk). cbn [edenot]. rewrite Hold.
unfold load_result. rewrite (amo_val_alu64 op o _ _ Hop). reflexivity.
+ rewrite (amo_val_swap op 64 _ _ Hop). reflexivity.
Qed.
#[using="Type"] Lemma sym_step_sound_load : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "TD'U0'aOyR0%211'>y8%511%311p051'Z8&RMy5%2219'RK'6%>14y<%@11';'Y=%211'Y9yQ0%F11'I%E12&QJvaD&aN&Y1r<%211%42N1%7261(3r1%22=1%=3<41&QLr2%211(8%B3L21'A'RJ'Q9%3221%Q;11&R4r3%211(@(R>r;r:r9r8%55K4321+4%84?>21%J2>1%Q53>;1'YE&Z9r=%=51Q3<;:r?r6%54Q9321(SJr7r5%33@21%QA3;51&\ArBrC%34QB21E&\?rD&Y2rA%211r@%63521&\=rE&XO%11=%4231&\<rF&XN%11A%44R3381'J'QN'H'QM%113&R1&]0v_5%R:1A%R<2S61&\>rHrG%E1F%43321&[J&Y3%11J%3271%=6<Q3:5G1%?2RH1(QI%12ERB%RN3C31&[Lr>%25?>N1RF%I241qQPHK1%M2L1p0O1p0Q51p0Q;1p0QC1p0QH1p0R51p0RI1p0RO1pQU<S>1pQS6SA1pQS4SB1pQS8SD1pQSHT01po4SI1pQRHSL1pQR2SM1pQT@SO1pQTDT11pQR4T31pQSFT71pQRFT91plJT:1pRFTC1").
Proof.
intros E base rom ss regs sz sx rd rs imm ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
set (n := msize_bytes sz) in Hs.
set (sx' := match sz with SZ8 => false | _ => sx end) in Hs.
set (a := to_saddrK fk (sr_get (s_regs ss) rs) (bv_signed imm)) in Hs.
pose proof (msize_bytes_range sz) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = v_addi (getr regs rs) (bv_signed imm)).
{ subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. reflexivity. }
assert (Hsx : sx' = eff_sx sz sx) by (subst sx'; destruct sz; reflexivity).
destruct (sym_read segs ss fk scr a n sx') as [[[[v rscs] rscr] nx']|] eqn:Hr; [|discriminate].
injection Hs as <- <- <-.
destruct (sym_read_sound E base ss scr a n sx' v rscs rscr nx' Hr Hsc Hlf Hkn Hn1 Hn8)
as [Hfl (bs & Hrd & Hlen & Hval)].
rewrite Hadr in Hrd.
eexists; split.
- apply (stepR_load segs regs _ mem rom _ w sz sx rd rs imm bs Hf He Hd). rewrite msize_bytes_R. exact Hrd.
- exists (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs)).
split; [cbn [s_pc s_log s_resv]; rewrite v_addi_lit; reflexivity|].
cbn [s_regs s_log s_know]. split; [|split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|].
rewrite load_result_val by exact Hlen. rewrite <- Hsx. fold n. symmetry. exact Hval.
Qed.
#[using="Type"] Lemma sym_step_sound_store : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "TA'U0'aOyR0%211'>y8%511%311p051'Z8&RMy5%2219'RK%=13y<%?11';'Y=%211'Y9yQ0%E11'I%D12&QJvaD&aN&Y1r;%211%42M1%7261(3r1%22=1%=3<41'6&QLr2%211(8%C3521'A'RJ'Q9%3221%Q;11&R4r3%211(@(REr:r9r8%44K321+4%74>=21%J2=1%Q53=:1'YE&Z9r<%<41Q3;:r>r6%54Q9321(SJr7r5%33@21%QA3;51&\ArArB%34QB21E&\?rC&Y2r@%211r?%63521&\=rD&XO%11=%4231&\<rE&XN%11A%44R3381'J'QN'H'QM%113&R1&]0v_5%R:1A%R<2S51&\>rGrF%E1F%43321&[J&Y3%11J%3271%=6<Q3:5G1%?2RH1(QI%12ERB%RN3C31&[L%15>=MQFRE%H231qQPHJ1%L2K1p0N1p0Q41p0Q:1p0QB1p0QG1p0R41p0RG1p0RN1pQU<S=1pQS6S@1pQS4SA1pQS8SC1pQSHSN1po4SH1pQRLSK1pQRJSL1pQTDSN1pQR4T01pQSFT41pQRFT61plJT71pRFT@1").
Proof.
intros E base rom ss regs sz rs1 rs2 imm ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
set (n := msize_bytes sz) in *.
set (a := to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm)) in *.
destruct (resv_inval (s_resv ss) a) as [r'|] eqn:Hri; [|discriminate].
injection Hs as <- <- <-.
pose proof (msize_bytes_range sz) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm)).
{ subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. reflexivity. }
apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
pose proof (storeok_sc_sound E base fk a n Hfk Hfl Hn1 Hn8 Hsc) as Hok.
assert (Hok' : RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) n = true).
{ rewrite <- Hadr. unfold mem. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
eexists; split.
- apply (stepR_store segs regs _ mem rom _ w sz rs1 rs2 imm Hf He Hd). rewrite msize_bytes_R. exact Hok'.
- exists regs. split.
+ cbn [s_pc s_log s_resv mem_denot]. rewrite v_addi_lit, msize_bytes_R. fold n.
rewrite Hadr, (Hregs rs2), <- (resv_inval_sound E _ _ _ Hri), Hadr. reflexivity.
+ cbn [s_regs s_log s_know]. split; [exact Hregs|]. split; [|exact Hkn].
cbn [log_flat]. split; [exact Hn8|]. split; [exact Hfl | exact Hlf].
Qed.
#[using="Type"] Lemma sym_step_sound_lr : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "TB'U0'aOyR0%211'>y8%511%311p051'Z8&RMy5%2219'RH'6%>14';'Y=%211'Y9yQ0%D11'I%C12&QJvaD&aN&Y1r<%211%42L1%7261(3r1%22=1%=3<41&QLr2%211(8%B3J21'A'RJ'Q9%3221%Q911&R4r3%211(@(R?r;r:r9r8%55K4321+4%84?>21%J2>1%Q53>;1'YE&Z9r=%=51Q3<;:r?r6%54Q9321(SJr7r5%33@21%QA3;51&\ArBrC%34QB21E&\?rD&Y2rA%211r@%63521&\=rE&XO%11=%4231&\<rF&XN%11A%44R3381'J'QN'H'QM%113&R1&]0v_5%R:1A%R<2S41&\>rHrG%E1F%43321&[J&Y3%11J%3271%=6<Q3:5G1%?2RH1(QI%12ERB%RN3C31&[Lr>%25?>N1RF%I241qQPHK1%M2L1p0O1p0Q51p0Q;1p0QC1p0QH1p0R51p0RI1p0RO1pQU<S>1pQS6SA1pQS4SB1pQS8SD1pQSHSN1pQRHSI1pQR2SJ1pQR>SL1pl@SM1pQUDSO1pQR4T11pQSFT51pQRFT71plJT81pRFTA1").
Proof.
intros E base rom ss regs wd aq rl rd rs ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
set (n := msize_bytes (amo_sz wd)) in Hs.
destruct (amo_alignedb fk (sr_get (s_regs ss) rs) wd) eqn:Hal; [|discriminate].
set (a := to_saddrK fk (sr_get (s_regs ss) rs) 0) in Hs.
pose proof (msize_bytes_range (amo_sz wd)) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = getr regs rs).
{ subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. apply v_addi_0. }
destruct (sym_read segs ss fk scr a n (amo_sx wd)) as [[[[v rscs] rscr] nx']|] eqn:Hr; [|discriminate].
injection Hs as <- <- <-.
destruct (sym_read_sound E base ss scr a n (amo_sx wd) v rscs rscr nx' Hr Hsc Hlf Hkn Hn1 Hn8)
as [Hfl (bs & Hrd & Hlen & Hval)].
rewrite Hadr in Hrd.
pose proof (amo_alignedb_sound E base fk _ wd Hfk Hal) as HA. rewrite <- (Hregs rs) in HA.
eexists; split.
- apply (stepR_lr segs regs _ mem rom _ w wd aq rl rd rs bs Hf He Hd HA). rewrite amo_nbytes_sz. exact Hrd.
- exists (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs)).
split; [cbn [s_pc s_log s_resv resv_denot]; rewrite v_addi_lit, Hadr; reflexivity|].
cbn [s_regs s_log s_know]. split; [|split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|].
rewrite amo_msize_sz. rewrite load_result_val by exact Hlen.
replace (eff_sx (amo_sz wd) true) with (amo_sx wd) by (destruct wd; reflexivity).
fold n. symmetry. exact Hval.
Qed.
#[using="Type"] Lemma sym_step_sound_sc : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "TC'U0'aOyR0%211'>y8%511%311p051'Z8&RMy5%2219'RH'6%>14';'Y=%211'Y9yQ0%D11'I%C12&QJvaD&aN&Y1r=%211%42L1%7261(3r1%22=1%=3<41&QLr2%211(8%B3J21'A'RJ'Q9%3221%Q911&R4r3%211(@(RDr<r;r:r9r8%66L54321+4%94@?21%K2?1%Q63?<1'YE&Z9r>%>61Q4=<;:r@r6%54Q:321(SJr7r5%33@21%QB3;51&\ArCrD%34QC21E&\?rE&Y2rB%211rA%63521&\=rF&XO%11=%4231&\<rG&XN%11A%44R4381'J'QN'H'QM%113&R1&]0v_5%R;1A%R=2S51&\>rIrH%E1F%43321&[J&Y3%11J%3271%=6<Q3:5G1%?2RI1(QI%12ERC%RO3C31&[L%15>=MQHRF%H231qQPHJ1%L2K1p0N1p0Q41p0Q:1p0QB1p0QG1p0R41p0RI1p0RO1pQU<S>1pQS6SA1pQS4SB1pQS8SD1pQSHSN1pQRLSI1pQRJSJ1pQR2SK1pQR>SM1pl@SN1pQUDT01pQR4T21pQSFT61pQRFT81plJT91pRFTB1").
Proof.
intros E base rom ss regs wd aq rl rd rs1 rs2 ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
set (n := msize_bytes (amo_sz wd)) in *.
destruct (amo_alignedb fk (sr_get (s_regs ss) rs1) wd) eqn:Hal; [|discriminate].
set (a := to_saddrK fk (sr_get (s_regs ss) rs1) 0) in *.
destruct (s_resv ss) as [r|] eqn:Hrv; [|discriminate].
destruct (saddr_eqb r a) eqn:Heq; [|discriminate].
apply saddr_eqb_eq in Heq. subst r.
injection Hs as <- <- <-.
pose proof (msize_bytes_range (amo_sz wd)) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = getr regs rs1).
{ subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. apply v_addi_0. }
apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
pose proof (storeok_sc_sound E base fk a n Hfk Hfl Hn1 Hn8 Hsc) as Hok.
assert (Hok' : RiscvSemantics.store_ok segs mem (getr regs rs1) n = true).
{ rewrite <- Hadr. unfold mem. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
pose proof (amo_alignedb_sound E base fk _ wd Hfk Hal) as HA. rewrite <- (Hregs rs1) in HA.
eexists; split.
- cbn [resv_denot]. apply (stepR_sc_ok segs regs _ mem rom w wd aq rl rd rs1 rs2 _ Hf He Hd HA Hadr).
rewrite amo_nbytes_sz. exact Hok'.
- exists (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)). split.
+ cbn [s_pc s_log s_resv resv_denot mem_denot]. rewrite v_addi_lit, amo_nbytes_sz. fold n.
rewrite Hadr, (Hregs rs2). reflexivity.
+ cbn [s_regs s_log s_know]. split; [apply regs_ok_upd; [exact Hregs|reflexivity]|]. split; [|exact Hkn].
cbn [log_flat]. split; [exact Hn8|]. split; [exact Hfl | exact Hlf].
Qed.
#[using="Type"] Lemma sym_step_sound_amo : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "TF'U0'aOyR0%211'>y8%511%311p051'Z8&RMy5%2219'RG'RH'6%?15';'Y=%211'Y9yQ0%E11'I%D12&QJvaD&aN&Y1r>%211%42M1%7261(3r1%22=1%=3<41&QLr2%211(8%B3J21'A'RJ'Q9%3221%Q:11&R4r3%211(@(R=r=r<r;r:r9r8%77M654321+4%:4A@21%L2@1%Q73@=1'YE&Z9r?%?71Q5>=<;:rAr6%54Q;321(SJr7r5%33@21%QC3;51&\ArDrE%34QD21E&\?rF&Y2rC%211rB%63521&\=rG&XO%11=%4231&\<rH&XN%11A%44R5381'J'QN'H'QM%113&R1&]0v_5%R<1A%R>2S71&\>rJrI%E1F%43321&[J&Y3%11J%3271%=6<Q3:5G1%?2RJ1(QI%12ERD%S03C31&[L%15>=MRLRG%H231qQPHJ1%L2K1p0N1p0Q41p0Q:1p0QB1p0QG1p0R41p0RJ1p0S01pQU<S?1pQS6SB1pQS4SC1pQS8SE1pQSHT01pQRLSJ1pQRJSK1pQR2SL1pQR>SN1pl@SO1pQUDT11pQQ@T31pQR4T51pQSFT91pQRFT;1plJT<1pRFTE1").
Proof.
intros E base rom ss regs op wd aq rl rd rs1 rs2 ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
destruct (amo_aluop op) as [aop|] eqn:Hop; [|discriminate].
set (n := msize_bytes (amo_sz wd)) in *.
destruct (amo_alignedb fk (sr_get (s_regs ss) rs1) wd) eqn:Hal; [|discriminate].
set (a := to_saddrK fk (sr_get (s_regs ss) rs1) 0) in *.
destruct (resv_inval (s_resv ss) a) as [r'|] eqn:Hri; [|discriminate].
destruct (sym_read segs ss fk scr a n (amo_sx wd)) as [[[[vold rscs] rscr] nx']|] eqn:Hr; [|discriminate].
injection Hs as <- <- <-.
pose proof (msize_bytes_range (amo_sz wd)) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = getr regs rs1).
{ subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. apply v_addi_0. }
apply scs_denot_app in Hsc as [Hsc Hsok].
destruct (sym_read_sound E base ss scr a n (amo_sx wd) vold rscs rscr nx' Hr Hsc Hlf Hkn Hn1 Hn8)
as [Hfl (bs & Hrd & Hlen & Hval)].
pose proof (storeok_sc_sound E base fk a n Hfk Hfl Hn1 Hn8 Hsok) as Hok.
assert (Hok' : RiscvSemantics.store_ok segs mem (getr regs rs1) n = true).
{ rewrite <- Hadr. unfold mem. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
rewrite Hadr in Hrd.
pose proof (amo_alignedb_sound E base fk _ wd Hfk Hal) as HA. rewrite <- (Hregs rs1) in HA.
assert (Hold : edenot E vold = load_result (amo_sz wd) true bs).
{ rewrite load_result_val by exact Hlen.
replace (eff_sx (amo_sz wd) true) with (amo_sx wd) by (destruct wd; reflexivity).
fold n. symmetry. exact Hval. }
eexists; split.
- apply (stepR_amo segs regs _ mem rom _ w op wd aq rl rd rs1 rs2 bs Hf He Hd HA);
rewrite amo_nbytes_sz; [exact Hrd | exact Hok'].
- exists (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs)). split.
+ cbn [s_pc s_log s_resv mem_denot]. rewrite v_addi_lit. fold n.
rewrite Hadr, <- (resv_inval_sound E _ _ _ Hri), Hadr.
rewrite (Hregs rs2), (amo_store_bytes_newval E base fk op aop wd bs vold _ Hfk Hop Hlen Hold).
reflexivity.
+ cbn [s_regs s_log s_know]. split.
* apply regs_ok_upd; [exact Hregs|]. rewrite amo_msize_sz. exact Hold.
* split; [|exact Hkn]. cbn [log_flat]. split; [exact Hn8|]. split; [exact Hfl | exact Hlf].
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
#[using="Type"] Lemma sym_step_soundR : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "S6'U0'aOyR0%211'>y8%511%311p051'Z8'QN'RJ';'Y=%211'Y9yQ0%@11'I%?12&QJvaD&aN&Y1r8%211%42H1%7261(3r1%22=1%=3<41'6&QLr2%211(8%C3521'A'Q9%22M1%Q511&R4r3%211(@+4%24Q48G1%D281%O3851'YE&Z9r9r;r6%44Q2321(SJr7r5%33Q321%Q:3:51&\Ar>r?%34Q;21Q8&[Lr@r=r<%4536721'J'H'QM%11QO&R1%12QF=(QI%12R3Q@%QL3531rBrA%@521?=QD%;241qQPHR91%>2R:1p0@1p0F1p0K1p0Q71p0QD1p0QK1pQU<R:1pQS6R=1pQS4R>1pQS8R@1pQSHRF1po0RE1pQPFRG1pQSFRI1pQRFRK1plJRL1pRFS51").
Proof.
intros E base rom ss ms i ss' scs scr scr' w Hf He Hd Hs Hsc (regs & -> & Hregs & Hlf & Hkn).
destruct i;
try (eapply sym_step_sound_load; eassumption);
try (eapply sym_step_sound_store; eassumption);
try (eapply sym_step_sound_lr; eassumption);
try (eapply sym_step_sound_sc; eassumption);
try (eapply sym_step_sound_amo; eassumption);
set (mem := mem_denot E base (s_log ss)) in *;
set (rv := resv_denot E (s_resv ss)) in *;
cbn [sym_step] in Hs; try discriminate;
pose proof (facts_of_ok segs E base _ Hkn) as Hfk; set (fk := facts_of (s_know ss)) in *.
-
alu_case ltac:(exact (stepR_lui segs regs _ mem rom rv w rd imm Hf He Hd))
ltac:(cbn [edenot]; unfold v_lui; apply Z_to_bv64_u).
-
alu_case ltac:(exact (stepR_auipc segs regs _ mem rom rv w rd imm Hf He Hd))
ltac:(cbn [edenot]; rewrite Z_to_bv64_u; symmetry; apply v_auipc_lit).
-
injection Hs as <- <- <-.
eexists; split; [ exact (stepR_jal_link segs regs _ mem rom rv w rd imm Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sset]; rewrite btgt_lit; symmetry; apply Z_to_bv64_u |].
cbn [s_regs s_log s_know sset]. split; [| split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|]. cbn [edenot]. symmetry. apply v_addi_lit.
-
pose proof (conc_expr_sound segs E base fk (sr_get (s_regs ss) rs1) Hfk) as Hce.
destruct (conc_expr fk (sr_get (s_regs ss) rs1)) as [z| | | | | | |] eqn:Hg; try discriminate.
injection Hs as <- <- <-.
eexists; split; [ exact (stepR_jalr segs regs _ mem rom rv w rd rs1 imm Hf He Hd) |].
eexists; split.
+ f_equal. cbn [s_pc sset]. unfold v_jalr.
specialize (Hregs rs1) as Hg1. rewrite <- Hce in Hg1. cbn [edenot] in Hg1.
rewrite Hg1. rewrite Z_to_bv64_mod. exact (jalr_tgt_lit z (bv_signed imm)).
+ cbn [s_regs s_log s_know sset]. split; [| split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|]. cbn [edenot]. symmetry. apply v_addi_lit.
-
set (tk := bv_unsigned (Z_to_bv 64 (s_pc ss + bv_signed imm))) in Hs.
assert (Hcond : forall t, branch_taken c (getr regs rs1) (getr regs rs2) = t ->
exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) mem rom rv) = MachineOk ms'
/\ st_okR E base rom (sjump ss (if t then tk else (s_pc ss + 4)%Z)) ms').
{ intros t Ht. destruct t.
- eexists; split; [exact (stepR_branch_tk_gen segs regs _ mem rom rv w c rs1 rs2 imm Hf He Hd Ht)|].
eexists; split; [| split; [exact Hregs | split; [exact Hlf | exact Hkn]]].
f_equal. cbn [s_pc sjump]. rewrite btgt_lit. subst tk. symmetry. apply Z_to_bv64_u.
- eexists; split; [exact (stepR_branch_ft_gen segs regs _ mem rom rv w c rs1 rs2 imm Hf He Hd Ht)|].
eexists; split; [| split; [exact Hregs | split; [exact Hlf | exact Hkn]]].
f_equal. cbn [s_pc sjump]. apply v_addi_lit. }
destruct (decide_branch fk c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) as [t|] eqn:Hdb.
+
injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
eapply decide_branch_sound; [exact Hfk | exact Hdb].
+ destruct (decide_branch fk c (conc_expr fk (sr_get (s_regs ss) rs1))
(conc_expr fk (sr_get (s_regs ss) rs2))) as [t|] eqn:Hdb2.
*
injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
rewrite <- (conc_expr_sound segs E base fk (sr_get (s_regs ss) rs1) Hfk).
rewrite <- (conc_expr_sound segs E base fk (sr_get (s_regs ss) rs2) Hfk).
eapply decide_branch_sound; [exact Hfk | exact Hdb2].
* destruct (enum_branch fk c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) as [t|] eqn:Hdb3.
{
injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
eapply enum_branch_sound; [exact Hfk | exact Hdb3]. }
destruct (sc_dirs scr) as [|t dirs'] eqn:Hdirs; [discriminate|].
injection Hs as <- <- <-. apply Hcond.
apply scs_denot_cons in Hsc as [Hbr _]. cbn [sc_denot] in Hbr.
rewrite (Hregs rs1), (Hregs rs2). exact Hbr.
-
alu_case ltac:(exact (stepR_opimm_gen segs regs _ mem rom rv w op rd rs1 imm Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hfk); cbn [edenot]; rewrite <- Hregs, sext64_lit; reflexivity).
-
alu_case ltac:(exact (stepR_shiftimm_gen segs regs _ mem rom rv w op rd rs1 shamt Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hfk); cbn [edenot]; rewrite <- Hregs, zext64_lit; reflexivity).
-
alu_case ltac:(exact (stepR_op_gen segs regs _ mem rom rv w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hfk); rewrite <- !Hregs; reflexivity).
-
alu_case ltac:(exact (stepR_opimm32_gen segs regs _ mem rom rv w rd rs1 imm Hf He Hd))
ltac:(lazymatch goal with |- _ = ?r => change (edenot E (mkAluwK fk ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm))) = r) end;
rewrite (mkAluwK_denot segs E base _ _ _ _ Hfk); cbn [edenot]; rewrite <- Hregs, sext32_low32; reflexivity).
-
alu_case ltac:(exact (stepR_shiftimm32_gen segs regs _ mem rom rv w op rd rs1 shamt Hf He Hd))
ltac:(rewrite mkAluw_denot; cbn [edenot]; rewrite <- Hregs, zext32_low32; reflexivity).
-
alu_case ltac:(exact (stepR_op32_gen segs regs _ mem rom rv w op rd rs1 rs2 Hf He Hd))
ltac:(lazymatch goal with |- _ = ?r => change (edenot E (mkAluwK fk op (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) = r) end;
rewrite (mkAluwK_denot segs E base _ _ _ _ Hfk); rewrite <- !Hregs; reflexivity).
-
injection Hs as <- <- <-.
eexists; split; [ exact (stepR_fence segs regs _ mem rom rv w _ _ _ _ _ Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sjump]; apply v_addi_lit |].
cbn [s_regs s_log s_know sjump]. split; [exact Hregs | split; [exact Hlf | exact Hkn]].
-
injection Hs as <- <- <-.
eexists; split; [ exact (stepR_fencei segs regs _ mem rom rv w _ _ _ Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sjump]; apply v_addi_lit |].
cbn [s_regs s_log s_know sjump]. split; [exact Hregs | split; [exact Hlf | exact Hkn]].
-
alu_case ltac:(exact (stepR_mul_gen segs regs _ mem rom rv w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite (mkMdK_denot segs E base _ _ _ _ Hfk); rewrite <- !Hregs; reflexivity).
-
alu_case ltac:(exact (stepR_mul32_gen segs regs _ mem rom rv w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite mkMdw_denot; rewrite <- !Hregs; reflexivity).
Qed.
#[using="Type"] Lemma sym_step_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "S9'U0'aOyR0%211'>y8%511%311p051'Z8'QN'RJ';'Y=%211'Y9yQ0%@11'I%?12&QJvaD&aN&Y1r8%211%42H1%7261(3r1%22=1%=3<41'6&QLr2%211(8%C3521'A'Q9%22M1%Q511&R4r3%211(@+4%24Q48G1%D281%O3851'YE&Z9r9&T=r;%211r6%64Q4521(SJr7r5%33Q521%Q<3<51&\Ar>r?%34Q=21Q:&[Kr@r=r<%4536721'J'H'QM%11R1&R1%12QH=(QI%12R5QB%QN3531&[LrBrA%3521@>QG%<251qQPHR<1%?2R=1p0A1p0G1p0L1p0Q:1p0QG1p0QN1pQU<R=1pQS6R@1pQS4RA1pQS8RC1pQSHRI1po0RH1pQPFRJ1pQSFRL1pQRFRN1plJRO1pRFS81").
Proof.
intros E base rom ss ms i ss' scs scr scr' w Hf He Hd Hs Hsc Hst.
exact (sym_step_soundR E base rom (clr ss) ms i ss' scs scr scr' w Hf He Hd Hs Hsc (st_ok_R E base rom ss ms Hst)).
Qed.
End StepSound.
#[using="Type"] Lemma sidecond_eqb_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound ">'Y='I'6&Y>r2r1%3221(C%73621r3%93:16p031pQUN<1pQUL=1").
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
#[using="Type"] Lemma sc_mem_In : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "A'Y=';%112'I'6&Y7r2r1%3221(C%73621&]4r3%23=17p041poJ=1pQUL@1").
Proof.
induction l as [|y t IH]; cbn [sc_mem]; intros H; [discriminate|].
apply orb_prop in H as [H|H].
- left. symmetry. apply sidecond_eqb_eq. exact H.
- right. apply IH. exact H.
Qed.
#[using="Type"] Lemma sc_add_denot : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2';'QF%211'aOyR0%211'>y8%511%311p051'U0'Y=%=11&\Ar5r4r3&Y6r2r1%3221%847651'Hr6%;41:98%<42;:7%4221p061pl2@1pQQ6A1pRFD1plJF1pQS:O1").
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
Local Ltac fetch_cases Hstop :=
lazymatch goal with
| |- context [fetch_word segs (Z_to_bv 64 (s_pc ?ss))] =>
destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact Hstop];
destruct (is_ecall w) eqn:He; [exact Hstop|];
destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact Hstop];
destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb]; [|exact Hstop];
apply Z.eqb_eq in Hsz; subst sz
end.
#[using="Type"] Lemma sym_exec_go_sound : forall fuel first stops scr ss acc ck E base rom,
sym_exec_go segs fuel first stops scr ss acc ck = ck \/
(let '(r, accr, _) := sym_exec_go segs fuel first stops scr ss acc ck in
s_resv r = None /\
(scs_denot segs base E accr -> scs_denot segs base E acc) /\
(forall ms, scs_denot segs base E accr -> st_okR segs E base rom ss ms ->
exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr)).
Proof.
induction fuel as [|f IH]; intros first stops scr ss acc ck E base rom.
- cbn [sym_exec_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|]. split; [intros H; exact H|].
intros ms _ Hst. exists ms. split; [apply mst_refl|exact Hst].
- assert (Hstop : (if s_clean ss then (ss, acc, scr) else ck) = ck \/
(let '(r, accr, _) := (if s_clean ss then (ss, acc, scr) else ck) in
s_resv r = None /\
(scs_denot segs base E accr -> scs_denot segs base E acc) /\
(forall ms, scs_denot segs base E accr -> st_okR segs E base rom ss ms ->
exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr))).
{ destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|]. split; [intros H; exact H|].
intros ms _ Hst. exists ms. split; [apply mst_refl|exact Hst]. }
cbn [sym_exec_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
fetch_cases Hstop.
destruct (sym_step segs i ss scr) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
cbv zeta.
set (ck' := if s_clean ss2 then (ss2, sc_add scs2 acc, scr2) else ck).
specialize (IH false stops scr2 ss2 (sc_add scs2 acc) ck' E base rom).
destruct (sym_exec_go segs f false stops scr2 ss2 (sc_add scs2 acc) ck') as [[r accr] scrr] eqn:Hgo.
destruct IH as [Hck|(Hr & Hacc & Hrun)].
+
subst ck'. destruct (s_clean ss2) eqn:Hc2.
* right. injection Hck as -> -> ->.
split; [apply s_clean_None; exact Hc2|].
split; [intros H; apply sc_add_denot in H as [_ H]; exact H|].
intros ms Hsc Hst. apply sc_add_denot in Hsc as [Hsc2 _].
destruct (sym_step_soundR segs E base rom ss ms i ss2 scs2 scr scr2 w Hf He Hd Hstep Hsc2 Hst)
as (msA & HstepA & HstA).
exists msA. split; [|exact HstA].
eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl].
* left. exact Hck.
+ right. split; [exact Hr|].
split; [intros H; apply Hacc in H; apply sc_add_denot in H as [_ H]; exact H|].
intros ms Hsc Hst.
pose proof (Hacc Hsc) as Hacc'. apply sc_add_denot in Hacc' as [Hsc2 _].
destruct (sym_step_soundR segs E base rom ss ms i ss2 scs2 scr scr2 w Hf He Hd Hstep Hsc2 Hst)
as (msA & HstepA & HstA).
destruct (Hrun msA Hsc HstA) as (mr & Hmr & Hstr).
exists mr. split; [|exact Hstr].
eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact Hmr].
Qed.
#[using="fx"] Lemma sym_exec_acc : forall fuel first stops scr ss acc E base,
match sym_exec segs fuel first stops scr ss acc with
| (ss', scs, scr') => scs_denot segs base E scs -> scs_denot segs base E acc
end.
Proof.
intros fuel first stops scr ss acc E base. unfold sym_exec.
destruct (sym_exec_go_sound fuel first stops scr (clr ss) acc (clr ss, acc, scr) E base (fun _ => None))
as [Hck|H].
- rewrite Hck. intros HH; exact HH.
- destruct (sym_exec_go segs fuel first stops scr (clr ss) acc (clr ss, acc, scr)) as [[r accr] scrr].
destruct H as (_ & Hacc & _). exact Hacc.
Qed.
#[using="Type"] Theorem sym_exec_soundR : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R?'<'6';'Q9%211'Y9'Z8'Y=%611'U0'aOyR0%211'>y8%511%311p051'QN'I'A%12?=%221A&YNvaDr=r<r;r:r9r8%877654321(@r7r6%34MK21r5%54@Q021%C3@71&\Ar4%24A158&\3r3%26D:84A1'H'Y4%Q211&Y3%11E(0%115%Q13531'J'\Er1%23Q0D1&\4%16Q2LIHO3%>231qQPHQ:1%82Q;1%A2:1p0C1p0G1p0K1pQPFQ@1pQRFQB1plJQC1pRFQL1pQS6R11pQS8QO1pQSHR21pl2R11pQSFR41pQS4R61pQT>R81pn2R<1pn:R>1").
Proof.
intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst. unfold sym_exec in Hex.
destruct (sym_exec_go_sound fuel first stops scr (clr ss) acc (clr ss, acc, scr) E base rom) as [Hck|H].
- rewrite Hex in Hck. injection Hck as -> -> ->. split; [reflexivity|].
exists ms. split; [apply mst_refl | apply st_ok_R; exact Hst].
- rewrite Hex in H. destruct H as (Hr & _ & Hrun). split; [exact Hr|].
apply (Hrun ms Hsc). apply st_ok_R. exact Hst.
Qed.
#[using="Type"] Theorem sym_exec_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R6'<'6';'Q9%211'Y9'Z8'Y=%611'U0'aOyR0%211'>y8%511%311p051'QN'I'A%12?=%221A&YNvaDr=r<r;r:r9r8%877654321(@r7r6%34MK21r5%54@Q021%C3@71&\Ar4%24A158&\3r3%26D:84A1'J'H'\Er1%23I=1%86JDA@G2%5221qQPHQ21%82Q31p0:1p0>1p0B1pQPFQ71pQRFQ91plJQ:1pRFQC1pQS6QH1pQS8QF1pQSHQI1pl2QH1pQSFQK1pQS4QM1pQT>QO1pn2R31pn:R51").
Proof.
intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
destruct (sym_exec_soundR fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst)
as (Hr & ms' & Hms & Hst').
exists ms'. split; [exact Hms | apply st_okR_ok; assumption].
Qed.
#[using="Type"] Theorem sym_exec_ex : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RJ'<'6';'Q9%211'Y9'Z8'Y=%611'U0'aOyR0%211'>y8%511%311p051'QN'I'A%12?=%221A&YNvaDr=r<r;r:r9r8%877654321(@r7r6%34MK21r5%54@Q021%C3@71&\Ar4%24A158&\3r3%26D:84A1'J&RMy5%221Q4'H&\?&Y2%11Ir1%43H21&\=&XO%11N%32L1'\E&\Gv_5&aN&Y1%11Q5%32QF1&\>%13Q5Q2:%857?31Q2%:3Q=Q11%E2<1%F2A1qVFH1%L2I1p0N1p0Q21p0Q61pQPFQK1pQRFQM1plJQN1pRFR71pQS6R<1pQS8R:1pQSHR=1pl2R<1pQSFR?1pQS4RA1pQT>RC1pn2RG1pn:RI1").
Proof.
intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
destruct (sym_exec_sound fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst)
as (ms' & Hms & (R & Heq & Hregs & Hlf & _)).
exists R. split; [exact Hregs|]. split; [exact Hlf|]. rewrite <- Heq. exact Hms.
Qed.
#[using="fx"] Theorem sym_exec_resv : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q6'<'6';'Q9%211'Y9'Z8'Y=%611'I'>'Y4%211&Y3&9'A%12:8&YNvaDr6r5r4r3r2r1%877654321%<3:E1%=3EC1%?11(0%11C%F3C31pl2H1pQSFK1pQS4M1pQT>O1pn2Q31pn:Q51").
Proof.
intros fuel first stops scr ss acc. unfold sym_exec.
destruct (sym_exec_go_sound fuel first stops scr (clr ss) acc (clr ss, acc, scr)
(Env (fun _ => Z_to_bv 64 0) (fun _ => [])) (fun _ => None) (fun _ => None)) as [Hck|H].
- rewrite Hck. reflexivity.
- destruct (sym_exec_go segs fuel first stops scr (clr ss) acc (clr ss, acc, scr)) as [[r accr] scrr].
destruct H as (Hr & _). exact Hr.
Qed.
#[using="Type"] Lemma sym_execS_go_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QK'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'M'I&Z2vaDr8r7r6r5r4%76654321%93D12'H'Y4%B11&Y3r1%211(0%116%B3631'QN&\4r3%26D@?1B8'J'\E%13G4;%66HFEDC<%A221qQPD91%62:1p081pQPF<1%F2>1tQQJQ<I1%Q32I1pQRFQ51plJQ61pRFQ?1pm@QA1pQSFQB1pQT>QD1pn2QH1pn:QJ1").
Proof.
induction fuel as [|f IH]; intros first stops ss ck E base rom.
- cbn [sym_execS_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|].
intros ms Hst. exists ms. split; [apply mst_refl|exact Hst].
- assert (Hstop : (if s_clean ss then ss else ck) = ck \/
(let r := (if s_clean ss then ss else ck) in
s_resv r = None /\
(forall ms, st_okR segs E base rom ss ms -> exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr))).
{ destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|].
intros ms Hst. exists ms. split; [apply mst_refl|exact Hst]. }
cbn [sym_execS_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
fetch_cases Hstop.
destruct (sym_step segs i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
destruct scs2 as [|x l]; [|exact Hstop].
set (ck' := if s_clean ss2 then ss2 else ck).
specialize (IH false stops ss2 ck' E base rom).
destruct IH as [Hck|(Hr & Hrun)].
+ subst ck'. destruct (s_clean ss2) eqn:Hc2.
* right. rewrite Hck. split; [apply s_clean_None; exact Hc2|].
intros ms Hst.
destruct (sym_step_soundR segs E base rom ss ms i ss2 [] scr_nil scr2 w Hf He Hd Hstep ltac:(constructor) Hst)
as (msA & HstepA & HstA).
exists msA. split; [|exact HstA].
eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl].
* left. exact Hck.
+ right. split; [exact Hr|].
intros ms Hst.
destruct (sym_step_soundR segs E base rom ss ms i ss2 [] scr_nil scr2 w Hf He Hd Hstep ltac:(constructor) Hst)
as (msA & HstepA & HstA).
destruct (Hrun msA HstA) as (mr & Hmr & Hstr).
exists mr. split; [|exact Hstr].
eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact Hmr].
Qed.
#[using="Type"] Theorem sym_execS_soundR : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QK'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&\3vaDr4r3r2r5r1%76654321'H'I'Y4%A11&Y3&YOr9r8r7r6%55A4321%711(0%11;%=3;31'J'\E%13HFC&\4r:%?5K1>=<%36L<HK1G%F251qQPHQ01%92Q11%I2;1p0K1pQPFQ41pQRFQ61plJQ71pRFQ@1pQSFQB1pQT>QD1pn2QH1pn:QJ1").
Proof.
intros fuel first stops ss E base rom ms Hst. unfold sym_execS.
destruct (sym_execS_go_sound fuel first stops (clr ss) (clr ss) E base rom) as [Hck|(Hr & Hrun)].
- rewrite Hck. split; [reflexivity|]. exists ms. split; [apply mst_refl | apply st_ok_R; exact Hst].
- split; [exact Hr|]. apply Hrun. apply st_ok_R. exact Hst.
Qed.
#[using="Type"] Theorem sym_execS_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q@'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&\3vaDr4r3r2r5r1%76654321'J'H'\E%13:85r6&YOr:r9r8r7%55A4321%C6B7>A1=%;291qQPHF1%>2G1p0@1pQPFI1pQRFK1plJL1pRFQ51pQSFQ71pQT>Q91pn2Q=1pn:Q?1").
Proof.
intros fuel first stops ss E base rom ms Hst.
destruct (sym_execS_soundR fuel first stops ss E base rom ms Hst) as (Hr & ms' & Hms & Hst').
exists ms'. split; [exact Hms | apply st_okR_ok; assumption].
Qed.
#[using="Type"] Theorem sym_execS_ex : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R9'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&\3vaDr4r3r2r5r1%76654321&YOr9r8r7r6%55<4321'J&RMy5%221H'H&\?&Y2%11A%33;1@&\=&XO%11E%32?1&\<&XN%11I%34MCB1'\E&\Gv_5&aN&Y1%11Q0%32Q=1&\>%13LK>%857Q231Q3%:3Q8Q71%H2<1%I2A1%J2F1qVFL1%Q02M1tQSHQJQ21p0Q91pQPFQB1pQRFQD1plJQE1pRFQN1pQSFR01pQT>R21pn2R61pn:R81").
Proof.
intros fuel first stops ss E base rom ms Hst.
destruct (sym_execS_sound fuel first stops ss E base rom ms Hst) as (ms' & Hms & (R & Heq & Hregs & Hlf & Hkn)).
exists R. split; [exact Hregs|]. split; [exact Hlf|]. split; [exact Hkn|]. rewrite <- Heq. exact Hms.
Qed.
#[using="fx"] Theorem sym_execS_resv : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "J'<'6';'Q9%211'Z8'I'>'Y4%211&Y3&YOvaDr4r3r2r1%6554321%811(0%11<%?3<31pQSFA1pQT>C1pn2G1pn:I1").
Proof.
intros fuel first stops ss. unfold sym_execS.
destruct (sym_execS_go_sound fuel first stops (clr ss) (clr ss)
(Env (fun _ => Z_to_bv 64 0) (fun _ => [])) (fun _ => None) (fun _ => None)) as [Hck|(Hr & _)].
- rewrite Hck. reflexivity.
- exact Hr.
Qed.
#[using="Type"] Lemma sym_execT_go_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R2&V0'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051&V1vaDr9%3221'M'I&Z6r:r8r7r6r5%67;5:4321%83G12'H'Y4%E11&Y3r1%211(0%116%A3631'QN&\4r4%26I@?1B8'J'\Er3%23M1<%76NGFE6=%B221qQPD:1%72;1p091pQPF=1%G2?1tQQJQ@J1%Q32J1p0Q51pQRFQ:1plJQ;1pRFQD1pm@QF1pQSFQG1pQT>QI1pn2QM1pn:QO1pQTFR11").
Proof.
intros t fuel. induction fuel as [|f IH]; intros first stops ss ck E base rom Ht.
- cbn [sym_execT_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|].
intros ms Hst. exists ms. split; [apply mst_refl|exact Hst].
- assert (Hstop : (if s_clean ss then ss else ck) = ck \/
(let r := (if s_clean ss then ss else ck) in
s_resv r = None /\
(forall ms, st_okR segs E base rom ss ms -> exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr))).
{ destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|].
intros ms Hst. exists ms. split; [apply mst_refl|exact Hst]. }
cbn [sym_execT_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
destruct (itab_lookup t (s_pc ss)) as [i|] eqn:Hl; [|exact Hstop].
pose proof (Ht _ _ Hl) as Hen. unfold itab_entry in Hen.
destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|discriminate].
destruct (is_ecall w) eqn:Hec; [discriminate|].
destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz.
injection Hen as ->.
destruct (sym_step segs i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
destruct scs2 as [|x l]; [|exact Hstop].
set (ck' := if s_clean ss2 then ss2 else ck).
specialize (IH false stops ss2 ck' E base rom Ht).
destruct IH as [Hck|(Hr & Hrun)].
+ subst ck'. destruct (s_clean ss2) eqn:Hc2.
* right. rewrite Hck. split; [apply s_clean_None; exact Hc2|].
intros ms Hst.
destruct (sym_step_soundR segs E base rom ss ms i ss2 [] scr_nil scr2 w Hf Hec Hd Hstep ltac:(constructor) Hst)
as (msA & HstepA & HstA).
exists msA. split; [|exact HstA].
eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl].
* left. exact Hck.
+ right. split; [exact Hr|].
intros ms Hst.
destruct (sym_step_soundR segs E base rom ss ms i ss2 [] scr_nil scr2 w Hf Hec Hd Hstep ltac:(constructor) Hst)
as (msA & HstepA & HstA).
destruct (Hrun msA HstA) as (mr & Hmr & Hstr).
exists mr. split; [|exact Hstr].
eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact Hmr].
Qed.
#[using="Type"] Theorem sym_execT_soundR : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R2&V0'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&V1vaDr9%3221&\3r5r4r3r6r2%66954321'H'I'Y4%D11&Y3&Z3r;r:r8r7%56D43C21%711(0%11;%=3;31'J'\Er1%23LG1&\4r<%@6O1?>N=%36Q0=IL15%G251qQPHQ41%:2Q51%J2<1p0L1p0Q41pQPFQ91pQRFQ;1plJQ<1pRFQE1pQSFQG1pQT>QI1pn2QM1pn:QO1pQTFR11").
Proof.
intros t fuel first stops ss E base rom ms Ht Hst. unfold sym_execT.
destruct (sym_execT_go_sound t fuel first stops (clr ss) (clr ss) E base rom Ht) as [Hck|(Hr & Hrun)].
- rewrite Hck. split; [reflexivity|]. exists ms. split; [apply mst_refl | apply st_ok_R; exact Hst].
- split; [exact Hr|]. apply Hrun. apply st_ok_R. exact Hst.
Qed.
#[using="Type"] Theorem sym_execT_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QG&V0'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&V1vaDr9%3221&\3r5r4r3r6r2%66954321'J'H'\Er1%23>91r7&Z3r<r;r:r8%56E432D1%C6F7?B19%<291qQPHJ1%?2K1p0A1p0I1pQPFN1pQRFQ01plJQ11pRFQ:1pQSFQ<1pQT>Q>1pn2QB1pn:QD1pQTFQF1").
Proof.
intros t fuel first stops ss E base rom ms Ht Hst.
destruct (sym_execT_soundR t fuel first stops ss E base rom ms Ht Hst) as (Hr & ms' & Hms & Hst').
exists ms'. split; [exact Hms | apply st_okR_ok; assumption].
Qed.
#[using="Type"] Theorem sym_execT_ex : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R@&V0'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&V1vaDr9%3221&\3r5r4r3r6r2%66954321&Z3r;r:r8r7%56?43>21'J&RMy5%221K'H&\?&Y2%11?r1%43<21&\=&XO%11D%32@1&\<&XN%11H%34Q1DC1'\E&\Gv_5&aN&Y1%11O%32QA1&\>%13ML>%857C31Q4%:3Q<Q81%I2<1%J2A1%K2F1qVFM1%Q12N1tQSHQNQ31p0Q:1p0QB1pQPFQG1pQRFQI1plJQJ1pRFR31pQSFR51pQT>R71pn2R;1pn:R=1pQTFR?1").
Proof.
intros t fuel first stops ss E base rom ms Ht Hst.
destruct (sym_execT_sound t fuel first stops ss E base rom ms Ht Hst) as (ms' & Hms & (R & Heq & Hregs & Hlf & Hkn)).
exists R. split; [exact Hregs|]. split; [exact Hlf|]. split; [exact Hkn|]. rewrite <- Heq. exact Hms.
Qed.
#[using="fx"] Theorem sym_execT_resv : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q0&V0'<'6';'Q9%211'Z8&V1vaDr5%3221'I'>'Y4%211&Y3&Z3r6r4r3r2%56=4<321%711(0%11;%>3;31p0@1pQSFE1pQT>G1pn2K1pn:M1pQTFO1").
Proof.
intros t fuel first stops ss Ht. unfold sym_execT.
destruct (sym_execT_go_sound t fuel first stops (clr ss) (clr ss)
(Env (fun _ => Z_to_bv 64 0) (fun _ => [])) (fun _ => None) (fun _ => None) Ht) as [Hck|(Hr & _)].
- rewrite Hck. reflexivity.
- exact Hr.
Qed.
End ExecSound.
Section XSound.
Variable segs : list Segment.
Definition eagree (b : nat) (E E' : env) : Prop :=
(forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.
Definition eupd (E : env) (i : nat) (v : word) : env :=
Env (fun n => if Nat.eqb n i then v else ev E n) (eb E).
#[using="Type"] Lemma eagree_refl : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "8'<'U0&[Mr2r1%33211pRF51plB71").
Proof. intros b E. split; [intros; reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma eagree_sym : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "='<'U0&[Mr3r2r1%43321r4%63145p031pRH91pRF:1plB<1").
Proof. intros b E E' [H1 H2]. split; [intros n Hn; symmetry; apply H1; exact Hn | symmetry; exact H2]. Qed.
#[using="Type"] Lemma eagree_trans : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "A'<'U0&[Mr4r3r2%43321r5%63143r6%83136p031p061pS2<1pS0=1pRN>1plB@1").
Proof.
intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [|congruence].
intros n Hn. rewrite (A1 n Hn). apply A2. exact Hn.
Qed.
#[using="Type"] Lemma eagree_le : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "C'<'U0&[Mr3r2r1%43321'Q0r5r4%3221r6%:3139p031p081pRH>1pRF?1plDA1plBB1").
Proof. intros b b' E E' [A B] Hle. split; [|exact B]. intros n Hn. apply A. lia. Qed.
#[using="Type"] Lemma eagree_upd : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "?'U0'<'aOyR0%211&[Mr2r3&[Nr1%23341%63541pQU881po0<1pRF>1").
Proof.
intros E i v. split; [|reflexivity]. intros n Hn. cbn [ev eupd].
destruct (Nat.eqb n i) eqn:Hni; [apply Nat.eqb_eq in Hni; lia | reflexivity].
Qed.
#[using="Type"] Lemma eupd_at : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "A'U0'<'aOyR0%211'I&U5&[Nr3r2r1%43321%6213%83913pQU8:1po0>1pRF@1").
Proof. intros E i v. cbn [ev eupd]. rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma edenot_evars_lt : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "L'<'U0'U9&[Mr4r3r2%43321'I'6&U8r5%2216(C%63521'aOyR0%211&TL%128>%22@?%=3421p081p0@1pmJF1pRHH1pRFI1plBK1").
Proof.
intros b E E' e [HA HB]. induction e; cbn [evars_lt edenot]; intros H.
- reflexivity.
- apply HA. apply Nat.ltb_lt. exact H.
- apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
- apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
- apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
- apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
- rewrite (IHe H). reflexivity.
- rewrite HB. reflexivity.
Qed.
Definition st_okX (E : env) (base rom : word -> option byte) (ss : sym_state) (ms : machine_state) : Prop :=
forall E', eagree (s_next ss) E E' -> st_okR segs E' base rom ss ms.
#[using="Type"] Lemma st_okX_R : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "L'U0'aOyR0%211'>y8%511%311p051'Z8'QN&\0r5r4r3r2r1%6554321&\4vaDr6%36219876p051pQPF=1pQSF?1pQRFA1plJB1pRFK1").
Proof. intros E base rom ss ms H. apply H. apply eagree_refl. Qed.
#[using="Type"] Lemma st_okX_agree : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'U0'aOyR0%211'>y8%511%311p051'Z8'QN&\0r6r4r3r2r1%6554321&[M&Y0%116r7%4321:r5%=53<1;:p031p091pQPFA1pQSFC1pQRFE1plJF1pRHO1pRFQ01").
Proof.
intros E E' base rom ss ms H Ha E'' Ha''. apply H. eapply eagree_trans; [exact Ha | exact Ha''].
Qed.
#[using="Type"] Lemma st_okX_clr : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q4'U0'aOyR0%211'>y8%511%311p051'Z8'QN&[M&Y0r3%211r6r1%63321&\3vaDr2r5r4%5643821:p071pRHI1&\0&T=%11?%35>8719p051pQPFE1pQSFG1pQRFI1plJJ1pRFQ31").
Proof. intros E base rom ss ms H E' Ha. apply st_ok_R. apply H. exact Ha. Qed.
#[using="Type"] Lemma st_okR_parts : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QO'U0'aOyR0%211'>y8%511%311p051'Z8'QN&\4vaDr5r4r3r2r1%76654321'H&\?r6&Y2%118&R0%119%63531'I&QO%11=&\>&XO%11A%33<D1%73J51&\=%12?4&\<&XN%11H%34LCK1&]0v_5&aN&Y1%11N%32Q<1&\1&Y3%11Q2%32M1%:69J5BQ51%I3Q:Q41%Q22=1%Q32B1%Q42E1%Q52N1p0Q71pQPFQ@1pQSFQB1pQRFQD1plJQE1pRFQN1").
Proof.
intros E base rom ss ms (regs & -> & HR & HL & HK). cbn [ms_regs ms_mem]. repeat split; assumption.
Qed.
Definition rd1 (mem : word -> option byte) (x : word) : option byte :=
match mem x with Some b => Some b | None => seg_rom segs x end.
#[using="Type"] Lemma rdn_defined : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R0'aOyR0%211'>y8%511%311p051'<&]<&]8&b4r1%22<1&]Gr2%211%7241&]I+2+R0%3221%=251&Q1r4%22=1&L'I&[Or6&aN%D2N7%F21@%32Q01%6251(0%11O%:3O31%<11p0>1po6Q01'J';%11Q6'H%Q:12&\HvaDr5%342DI1(3%128Q7%I3731&:%12QAQ:%L3Q?17%<241qm4>1%A2?1p0C1p0Q61pkNQK1pQPJQF1pQP>QH1").
Proof.
intros mem n. induction n as [|n IH]; intros a Hnw Hall.
- exists []. split; reflexivity.
- cbn [rdn].
pose proof (Hall 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
unfold rd1 in H0.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Hb; [|exfalso; exact (H0 eq_refl)].
destruct n as [|n'].
+ exists [b]. split; reflexivity.
+ assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [rewrite Hu1; lia | | ].
{ intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
apply Hall. lia. }
rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.
#[using="Type"] Lemma rdn_rd1 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q<'aOyR0%211'>y8%511%311p051'<';%115'I%912&\HvaDr5r3r4%544321(3r2%22;1%;3:41&Q1%1249&L&[Or7&b0&QE%11>%33N@1%6251(0%11M%H3M31%;11p0=1p0@1po6O1pm4N1pkNQ71pQPJQ21pQP>Q41").
Proof.
intros mem n a bs j H Hj.
pose proof (rdn_nth segs mem n a bs j H Hj) as H1.
unfold rd1. cbn [rdn] in H1.
destruct (match mem (a + nat_to_word j) with Some b => Some b | None => seg_rom segs (a + nat_to_word j) end); [discriminate|discriminate].
Qed.
#[using="Type"] Lemma zf_covers_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R1'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'Q9'<&\<vaDr9r8r7%544321'Q0r5u8%3221'I'6&[1r6r4r3%47>=<3921(C%83721'H&]<&\8r<(SH%12;A%4231%32HG%6251%8231&]8&]G%11K%3251&\6%12<D%62:1%@241%B291p0D1p0N1p0Q31pQP2Q<1poDQ<1po@Q>1pQPJQ=1pQR<Q?1pQR0QA1pl8QC1pVDQG1pRFR01").
Proof.
intros E M0 allkn rb rk n kb kk len Hall Hn8 H. unfold zf_covers in H.
apply orb_prop in H as [H|H].
- destruct len as [l0| | | | | | |]; try discriminate.
destruct (rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)) as [d| | |] eqn:Hrel; try discriminate.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (Heqb & Hd & Hkk & Hrn & Hst).
rewrite elenZ_lit. unfold estart in *; cbn [a_base a_off] in *. subst. lia.
- pose proof (xinside_sound segs E M0 allkn _ _ _ _ _ _ Hall H) as [A B].
rewrite elenZ_elen in B by exact Hn8. lia.
Qed.
#[using="Type"] Lemma kentry_overlay_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RC'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'Q9'<&\<vaDr8r7r6%544321&\;r9r2%348251'Q0u1r4%3221r5u8%6221'I'6&V8r:%251CBA7(C%63521'H&\:r=(SH%12EJ&]G%11K%63531&Q1r1%221Q0&Lr<&aN&]8&\8r?r;%?21F%4231%?1Q4%7221%92QK1%;11(0%11QJ%Q13QJ31%@11p0B1po6QF1%N2G1p0Q01p0Q81p0Q<1p0QA1p0QF1pS4R11pQPJQN1pQR<R01pQR0R21plJR71pl8R51pVDR91pRFRB1").
Proof.
intros E M0 allkn base rb rk n K Hall HK Hn1 Hn8 H.
assert (GEN : forall kb kk len (P : option byte -> Prop),
(forall x, P x -> x <> None) ->
flat E (SA kb kk) (elenZ E len) ->
(forall i, (0 <= i < elenZ E len)%Z -> P (base (Z_to_bv 64 (estart E (SA kb kk) + i)))) ->
zf_covers allkn rb rk n kb kk len = true ->
flat E (SA rb rk) (Z.of_nat n) /\ forall j, (j < n)%nat -> base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
{ intros kb kk len P HP Hfl Hz Hc.
destruct (zf_covers_sound E M0 allkn rb rk n kb kk len Hall Hn8 Hc) as [A B].
split; [unfold flat, estart in *; cbn [a_base a_off] in *; lia|].
intros j Hj.
replace (estart E (SA rb rk) + Z.of_nat j)%Z with (estart E (SA kb kk) + (estart E (SA rb rk) - estart E (SA kb kk) + Z.of_nat j))%Z by lia.
apply HP. apply Hz. lia. }
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] len];
cbn [kentry_overlay] in H; try discriminate; cbn [kentry_ok] in HK.
- destruct HK as [Hfl Hz]. apply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 0))); [intros x ->; discriminate | exact Hfl | exact Hz | exact H].
- destruct HK as (Hfl & Hlen & Hz). apply (GEN kb kk len (fun x => exists b, x = Some b)); [intros x [b ->]; discriminate | exact Hfl | | exact H].
intros i Hi. eexists. apply Hz. exact Hi.
- destruct HK as [Hfl Hz]. apply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 fc))); [intros x ->; discriminate | exact Hfl | exact Hz | exact H].
- destruct HK as [Hfl Hz]. apply (GEN kb kk len (fun x => x <> None)); [intros x Hx; exact Hx | exact Hfl | exact Hz | exact H].
Qed.
#[using="Type"] Lemma segs_avoid_find_none : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QA';'QF%211'Q9'I'6&]6&?&]=r3&]F&QGr1%211%411%7261&]8&QH%116%911%4261r4%>221%@281qQS0G1%C3H14(C%G3F21&]<r2%2291&]A%12G;'>%11Q1&QKr7+1%332A1(0%11Q7%Q53731p0:1p0=1p0A1pQULQ:1pnBQ;1pQP4Q<1poJQ>1").
Proof.
induction l as [|s l IH]; intros lo hi x Hb Hlo Hhi; [reflexivity|].
cbn [forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
cbn [find_segment].
replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
- exact (IH lo hi x Hl Hlo Hhi).
- symmetry. apply andb_false_iff. apply orb_true_iff in Hs as [Hs|Hs]; apply Z.leb_le in Hs;
[left | right]; apply Z.leb_gt; lia.
Qed.
#[using="Type"] Lemma kwr_offimage_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R1'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'Q9&\<vaDr6r5r4%544321'I'6&VBr3r2%35:8721(C%73621&]<&\8r9(SH%12@?%4231r1%7221&]A&]8r:r7%921H%<231&\6%125J%7231%92E1'QF%Q;11&QK+1%23Q3K1(0%116%Q13631p091p0D1pQULQ;1p0N1p0Q71pQP2Q?1poDQ?1po@QA1pl8QC1pVDQG1pRFR01").
Proof.
intros E M0 allkn kb kk len Hall H x Hlo Hhi. unfold kwr_offimage in H.
destruct (erange allkn kb) as [[blo bhi]|] eqn:Her; [|discriminate].
destruct len as [l0| | | | | | |]; try discriminate.
pose proof (erange_sound segs E M0 allkn kb blo bhi Hall Her) as Hr.
unfold estart, elenZ in *. cbn [a_base a_off] in *. rewrite edenot_lit, Z_to_bv_unsigned in Hhi.
change (bv_wrap 64 l0) with (l0 mod 2 ^ 64)%Z in Hhi.
eapply segs_avoid_find_none; [exact H | lia | lia].
Qed.
#[using="Type"] Lemma kentry_readable_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RD'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'Q9'<&\<vaDr8r7r6%544321&\;r9r2%348251'Q0u1r4%3221r5u8%6221'I'6&V9r:%26D1CBA7(C%63521'H&\:r=(SH%12EJ&]G%11K%63531&Q1r1%221Q0&L&[Or<&aN&]8&\8r?r;%@21G%4231%@1Q5%7221%92QL1%<2;1(0%11QK%Q23QK31%A11p0C1po6QG1%O2H1p0Q11p0Q91p0Q=1p0QB1p0QG1pS4R21pQPJQO1pQR<R11pQR0R31plJR81pl8R61pVDR:1pRFRC1").
Proof.
intros E M0 allkn base rb rk n K Hall HK Hn1 Hn8 H.
assert (WR : forall kb kk len, K = KWr (SA kb kk) len ->
flat E (SA rb rk) (Z.of_nat n) /\ forall j, (j < n)%nat -> rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
{ intros kb kk len ->. cbn [kentry_readable] in H. apply andb_true_iff in H as [Hc Ho].
cbn [kentry_ok] in HK. destruct HK as [Hfl Hst].
destruct (zf_covers_sound E M0 allkn rb rk n kb kk len Hall Hn8 Hc) as [A B].
assert (Hfr : flat E (SA rb rk) (Z.of_nat n)) by (unfold flat in *; lia).
split; [exact Hfr|]. intros j Hj.
set (x := (estart E (SA rb rk) + Z.of_nat j)%Z).
assert (Hso : store_ok segs base (Z_to_bv 64 (estart E (SA kb kk) + (x - estart E (SA kb kk)))) 1 = true)
by (apply Hst; subst x; cbn; lia).
replace (estart E (SA kb kk) + (x - estart E (SA kb kk)))%Z with x in Hso by lia.
pose proof (kwr_offimage_sound E M0 allkn kb kk len Hall Ho x ltac:(subst x; lia) ltac:(subst x; lia)) as Hnone.
cbn [store_ok] in Hso. unfold wview in Hso. unfold rd1.
destruct (base (Z_to_bv 64 x)) as [b|]; [discriminate|].
rewrite (u_small x) in Hso by (subst x; unfold flat in *; lia).
rewrite Hnone in Hso. discriminate. }
assert (OV : kentry_overlay allkn rb rk n K = true ->
flat E (SA rb rk) (Z.of_nat n) /\ forall j, (j < n)%nat -> rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
{ intros Hov. destruct (kentry_overlay_sound E M0 allkn base rb rk n K Hall HK Hn1 Hn8 Hov) as [A B].
split; [exact A|]. intros j Hj. unfold rd1. specialize (B j Hj).
destruct (base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j))); [discriminate | exfalso; exact (B eq_refl)]. }
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] len];
try exact (OV H).
2:{ destruct wa0 as [wkb wkk]. exact (WR wkb wkk wn0 eq_refl). }
cbn [kentry_readable] in H. cbn [kentry_ok] in HK. destruct HK as (Hw8 & Hfk & Hrd).
destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel; try discriminate.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
assert (Hfr : flat E (SA rb rk) (Z.of_nat n)) by (unfold flat, estart in *; cbn [a_base a_off] in *; destruct Hfk as (?&?&?&?); lia).
split; [exact Hfr|]. intros j Hj.
pose proof (rdn_rd1 base w (adenot E (SA rb kk)) _ (Z.to_nat d + j) Hrd ltac:(lia)) as X.
rewrite w_add_nat in X. rewrite (flat_u E _ _ Hfk) in X.
replace (estart E (SA rb kk) + Z.of_nat (Z.to_nat d + j))%Z with (estart E (SA rb rk) + Z.of_nat j)%Z in X by lia.
exact X.
Qed.
#[using="Type"] Lemma know_byte_cov_sound : forall img E base kn rb rk,
know_ok segs E base kn -> know_byte_cov segs img kn rb rk = true ->
flat E (SA rb rk) 1
/\ (if img then rd1 base (Z_to_bv 64 (estart E (SA rb rk))) <> None
else base (Z_to_bv 64 (estart E (SA rb rk))) <> None).
Proof.
intros img E base kn rb rk Hkn. induction kn as [|K rest IH]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
cbn [know_byte_cov] in H. apply orb_prop in H as [H|H]; [|exact (IH Hrest H)]. clear IH.
assert (LIT : forall kb kk (l : Z) (P : option byte -> Prop),
(forall x, P x -> x <> None) ->
flat E (SA kb kk) l ->
(forall i, (0 <= i < l)%Z -> P (base (Z_to_bv 64 (estart E (SA kb kk) + i)))) ->
match rel_lit rb rk 1 kb kk l with RInside _ => true | _ => false end = true ->
flat E (SA rb rk) 1 /\ (if img then rd1 base (Z_to_bv 64 (estart E (SA rb rk))) <> None
else base (Z_to_bv 64 (estart E (SA rb rk))) <> None)).
{ intros kb kk l P HP Hfl Hz Hm.
destruct (rel_lit rb rk 1 kb kk l) as [d| | |] eqn:Hrel; try discriminate.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (Heqb & Hd & Hkk & Hrn & Hst).
split; [unfold flat, estart in *; cbn [a_base a_off] in *; subst; lia|].
assert (B : base (Z_to_bv 64 (estart E (SA rb rk))) <> None).
{ rewrite Hst. apply HP. apply Hz. lia. }
destruct img; [|exact B]. unfold rd1. destruct (base (Z_to_bv 64 (estart E (SA rb rk)))); [discriminate | exfalso; exact (B eq_refl)]. }
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] len];
cbn [kentry_ok] in HK; try discriminate.
-
destruct img; [|discriminate]. cbn [andb] in H.
destruct HK as (Hw8 & Hfk & Hrd).
destruct (rel_lit rb rk 1 kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel; try discriminate.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
split; [unfold flat, estart in *; cbn [a_base a_off] in *; destruct Hfk as (?&?&?&?); lia|].
pose proof (rdn_rd1 base w (adenot E (SA rb kk)) _ (Z.to_nat d) Hrd ltac:(lia)) as X.
rewrite w_add_nat, (flat_u E _ _ Hfk) in X.
replace (estart E (SA rb kk) + Z.of_nat (Z.to_nat d))%Z with (estart E (SA rb rk)) in X by lia. exact X.
- destruct len as [l0| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. rewrite elenZ_lit in Hfl, Hz.
apply (LIT kb kk (l0 mod 2 ^ 64)%Z (fun x => x = Some (Z_to_bv 8 0))); [intros x ->; discriminate | exact Hfl | exact Hz | exact H].
- destruct len as [l0| | | | | | |]; try discriminate. destruct HK as (Hfl & Hlen & Hz). rewrite elenZ_lit in Hfl, Hz, Hlen.
apply (LIT kb kk (l0 mod 2 ^ 64)%Z (fun x => exists b, x = Some b)); [intros x [b ->]; discriminate | exact Hfl | | exact H].
intros i Hi. eexists. apply Hz. exact Hi.
-
destruct img; [|discriminate]. cbn [andb] in H.
destruct rb as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
destruct HK as (Hlo & Hhi & Hnone).
apply andb_prop in H as [H Hrom]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
rewrite estart_lit0. split; [unfold flat; rewrite estart_lit0; lia|].
unfold rd1. rewrite (Hnone rk) by lia. destruct (seg_rom segs (Z_to_bv 64 rk)); [discriminate|discriminate].
- destruct len as [l0| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. rewrite elenZ_lit in Hfl, Hz.
apply (LIT kb kk (l0 mod 2 ^ 64)%Z (fun x => x = Some (Z_to_bv 8 fc))); [intros x ->; discriminate | exact Hfl | exact Hz | exact H].
- destruct len as [l0| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. rewrite elenZ_lit in Hfl, Hz.
apply (LIT kb kk (l0 mod 2 ^ 64)%Z (fun x => x <> None)); [intros x Hx; exact Hx | exact Hfl | exact Hz | exact H].
Qed.
#[using="Type"] Lemma know_bytes_cov_sound : forall img E base kn rb n rk,
know_ok segs E base kn -> know_bytes_cov segs img kn rb rk n = true -> (1 <= n)%nat ->
flat E (SA rb rk) (Z.of_nat n)
/\ forall j, (j < n)%nat ->
if img then rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None
else base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None.
Proof.
intros img E base kn rb n. induction n as [|n IH]; intros rk Hkn H Hn1; [lia|].
cbn [know_bytes_cov] in H. apply andb_prop in H as [H1 H2].
destruct (know_byte_cov_sound img E base kn rb rk Hkn H1) as [F1 B1].
destruct n as [|n'].
- split; [exact F1|]. intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. exact B1.
- destruct (IH (rk + 1)%Z Hkn H2 ltac:(lia)) as [F2 B2].
split; [unfold flat, estart in *; cbn [a_base a_off] in *; lia|].
intros j Hj. destruct j as [|j'].
+ cbn [Z.of_nat]. rewrite Z.add_0_r. exact B1.
+ specialize (B2 j' ltac:(lia)). unfold estart in *; cbn [a_base a_off] in *.
replace (bv_unsigned (edenot E rb) + rk + Z.of_nat (S j'))%Z with (bv_unsigned (edenot E rb) + (rk + 1) + Z.of_nat j')%Z by lia.
exact B2.
Qed.
#[using="Type"] Lemma kn_readable_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R@'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'Q9'<&\<vaDr8r7r6%544321r9r5%847241'Q0u1r3%3221r4u8%6221'I'6&V<r:%26C1BA@=(C%63521'H&\:r=(SH%12IH&]G%11I%63531'J%Q61Q9%Q<11&\Hr;&SMr>%<2Q0Q4%3221%64Q751Q5(3r1%22;1%L3;41&:%12QG4%O3Q@1Q<%I241qm4A1%C2B1%L2E1p0N1p0Q61p0Q:1p0Q?1p0QC1pQPJQJ1pQR<QL1pQR0QN1poFR01plJR41pl8R21pVDR61pRFR?1").
Proof.
intros E M0 allkn base kn rb rk n Hall Hkn Hn1 Hn8 H. unfold kn_readable in H.
assert (PT : flat E (SA rb rk) (Z.of_nat n)
/\ forall j, (j < n)%nat -> rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
{ apply orb_prop in H as [H|H].
- apply existsb_exists in H as (K & Hin & HK).
eapply kentry_readable_sound; [exact Hall | exact (proj1 (Forall_forall _ _) Hkn K Hin) | exact Hn1 | exact Hn8 | exact HK].
- exact (know_bytes_cov_sound true E base kn rb n rk Hkn H Hn1). }
destruct PT as [Hfl Hpt]. split; [exact Hfl|].
apply rdn_defined; rewrite (flat_u E _ _ Hfl); [destruct Hfl as (?&?&?&?); lia | exact Hpt].
Qed.
#[using="Type"] Lemma kn_overlay_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R1'U0'aOyR0%211'>y8%511%311p051';'V7%211'U9'Q9'<&\<vaDr8r7r6%544321r9r5%847241'Q0u1r3%3221r4u8%6221'I'6&V;r:%26C1BA@=(C%63521'H&\:r=(SH%12IH&]G%11I%63531&R2&SM%1286%34Q1?1N%C3B1>%=261p0?1p0G1p0K1p0Q01p0Q41pQPJQ;1pQR<Q=1pQR0Q?1poFQA1plJQE1pl8QC1pVDQG1pRFR01").
Proof.
intros E M0 allkn base kn rb rk n Hall Hkn Hn1 Hn8 H. unfold kn_overlay in H.
assert (PT : flat E (SA rb rk) (Z.of_nat n)
/\ forall j, (j < n)%nat -> base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
{ apply orb_prop in H as [H|H].
- apply existsb_exists in H as (K & Hin & HK).
eapply kentry_overlay_sound; [exact Hall | exact (proj1 (Forall_forall _ _) Hkn K Hin) | exact Hn1 | exact Hn8 | exact HK].
- exact (know_bytes_cov_sound false E base kn rb n rk Hkn H Hn1). }
destruct PT as [Hfl Hpt]. split; [exact Hfl|].
apply store_ok_of_all; rewrite (flat_u E _ _ Hfl); [destruct Hfl as (?&?&?&?); lia|].
intros x Hx. unfold wview.
specialize (Hpt (Z.to_nat (bv_unsigned x - estart E (SA rb rk))) ltac:(lia)).
replace (estart E (SA rb rk) + Z.of_nat (Z.to_nat (bv_unsigned x - estart E (SA rb rk))))%Z with (bv_unsigned x) in Hpt by lia.
rewrite Z_to_bv_bv_unsigned in Hpt. destruct (base x); [discriminate | exfalso; exact (Hpt eq_refl)].
Qed.
#[using="Type"] Lemma find_readbase_In : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q6'<';'Y=%211'Y4'6'I'>'A%1259%2215%411&UIr5r4%3221(3(@r3r2%34@D21r1%54=A21%72=1%B3=91&]4(SI(S>r6%211%44@<;1%63M1Bp081pQT@L1pQPJQ21pkNO1pQS8Q11po0Q51").
Proof.
intros i scs a n sx. induction scs as [|sc rest IH]; cbn [find_readbase]; intros H; [discriminate|].
destruct sc as [| | | | |ra rn rsx rv|]; try (right; exact (IH H)).
destruct rv as [|j| | | | | |]; try (right; exact (IH H)).
destruct (Nat.eqb j i) eqn:Hj; [|right; exact (IH H)].
apply Nat.eqb_eq in Hj. subst j. injection H as <- <- <-. left. reflexivity.
Qed.
#[using="Type"] Lemma x_filter_nil : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'Z8';'Y=%211'I&ZBvaDr4r3r2%544321(=%11:%93:31&]4%13=67'6&ZAr6r5&UI&Y0%114%321@%75B651@(C%F3:21p0<1p0?1pQS2K1pQS8K1pQSHO1pQSFQ01").
Proof.
intros ss ss' scs sc H Hin. unfold x_filter in H.
destruct scs as [|sc0 rest] eqn:Hscs; [destruct Hin|]. rewrite <- Hscs in H, Hin |- *. clear Hscs.
assert (Hf : forall l f (x : sidecond), List.filter f l = [] -> In x l -> f x = false).
{ intros l f x. induction l as [|y l IH]; cbn; intros Hn Hx; [destruct Hx|].
destruct (f y) eqn:Hy; [discriminate|]. destruct Hx as [<-|Hx]; [exact Hy | exact (IH Hn Hx)]. }
pose proof (Hf _ _ sc H Hin) as X. cbv beta in X. destruct (x_dischargeable segs ss ss' _ sc); [reflexivity | discriminate].
Qed.
#[using="Type"] Lemma x_discharge_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RM'U0'aOyR0%211'>y8%511%311p051'Z8'A'Y4'<%3221'6%5221%<11'Y=&\<vaDr6r5&XNr4%211%746541&[M&Y0%117r8r7%53321'I&ZAr3%25@?><1(C%53G21(3(@r2%24NM71r1%44NM21%62M1%=3M@1'J';%11Q:'H%Q>12&\Hr=&SMr?%221Q2%54Q541Q1%C29?%J3821&U5r>r<%Q311%4231&aN&\9&QD%11I%33Q2Q=1%52R31%Q63R371%F2=1qm4H1%K2I1p0M1pQT@QM1pQPJR01pkNR21&\@r9r:%34QN21QLp051p0Q>1p0QE1p0QL1pQS2R51pQR0R71pQSHR?1pQSFR@1plJRB1pRFRK1pRLRL1").
Proof.
intros E0 E base ss ss' rb sc Hkn Hag Hd Hrb.
pose proof (facts_of_ok segs E base _ Hkn) as Hfk.
unfold x_dischargeable in Hd.
destruct sc as [| fa fn | | | oa on | ra rn rsx rv |]; try discriminate.
-
destruct fa as [fb fk]. destruct fn as [z| | | | | | |]; try discriminate.
apply andb_prop in Hd as [Hd Hcov]. apply andb_prop in Hd as [Hz1 Hz8]. apply Z.leb_le in Hz1. apply Z.leb_le in Hz8.
cbn [sc_denot a_base a_off] in Hcov |- *. rewrite elenZ_lit.
destruct (kn_readable_sound E _ _ base _ fb fk (Z.to_nat z) Hfk Hkn ltac:(lia) ltac:(lia) Hcov) as [Hfl _].
rewrite Z2Nat.id in Hfl by lia. rewrite Z.mod_small by lia. exact Hfl.
-
destruct oa as [ob ok]. apply andb_prop in Hd as [Hd Hcov]. apply andb_prop in Hd as [Hn1 Hn8].
apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8.
cbn [sc_denot a_base a_off] in Hcov |- *.
destruct (kn_overlay_sound E _ _ base _ ob ok on Hfk Hkn Hn1 Hn8 Hcov) as [_ Hso]. exact Hso.
-
destruct rv as [|j| | | | | |]; try discriminate.
destruct rb as [[[a' n'] sx']|]; [|discriminate].
apply andb_prop in Hd as [Hd Hcov]. apply andb_prop in Hd as [Hd Hn8]. apply andb_prop in Hd as [Hd Hn1].
apply andb_prop in Hd as [Hd Hvars]. apply andb_prop in Hd as [Hd Hlt]. apply andb_prop in Hd as [Hd Hj].
apply andb_prop in Hd as [Hd Hsx]. apply andb_prop in Hd as [Ha Hn].
apply saddr_eqb_eq in Ha. apply Nat.eqb_eq in Hn. apply Bool.eqb_prop in Hsx. subst a' n' sx'.
apply Nat.eqb_eq in Hj. subst j. apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8.
destruct (Hrb ra rn rsx eq_refl) as (bs & Hbs & Hv).
cbn [sc_denot edenot]. exists bs. split; [|symmetry; exact Hv].
replace (adenot E ra) with (adenot E0 ra); [exact Hbs|].
unfold adenot. rewrite (edenot_evars_lt (s_next ss) E0 E (a_base ra) Hag Hvars). reflexivity.
Qed.
#[using="Type"] Lemma cap_rd_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF'<'RJ'U0'aOyR0%211'>y8%511%311p051'Z8'QN&[M&Y0r3%211r6r1%63321&\4vaDr2r5r4%5643821:p071pRJI1'J'H%@16r7%C321>'Q0&T:r9r8%3321=%H11%6291&\0%15GHB4J%=231%>2;1qRHQ:1%A2Q;1p0C1pQPHQ31pQSHQ51pQRFQ71plJQ81pRNQA1po0QC1pS4QE1").
Proof.
intros K i E1 base rom ss' ms' ALL.
assert (SAME : exists E', eagree (s_next ss') E1 E' /\ (s_next ss' <= s_next ss')%nat /\ st_okX E' base rom ss' ms').
{ exists E1. split; [apply eagree_refl|]. split; [lia|]. intros E'' Ha. exact (ALL E'' Ha). }
unfold cap_rd. destruct K as [|K']; [exact SAME|].
destruct (rd_of i) as [rd|]; [|exact SAME].
destruct (bv_eqb rd 0) eqn:Hrd0; [exact SAME|].
destruct (esize_le (sr_get (s_regs ss') rd) (S K')); [exact SAME|].
set (e := sr_get (s_regs ss') rd).
exists (eupd E1 (s_next ss') (edenot E1 e)).
split; [apply eagree_upd|]. split; [cbn [s_next]; lia|].
intros E'' Ha''. cbn [s_next] in Ha''.
assert (Ha1 : eagree (s_next ss') E1 E'').
{ eapply eagree_trans; [apply eagree_upd | eapply eagree_le; [exact Ha'' | lia]]. }
destruct (st_okR_parts E'' base rom ss' ms' (ALL E'' Ha1)) as (Hregs & Hmem & Hlf & Hkn & Heq).
destruct (st_okR_parts E1 base rom ss' ms' (ALL E1 (eagree_refl _ _))) as (Hregs1 & _).
exists (ms_regs ms'). cbn [s_pc s_regs s_log s_know s_resv].
split; [exact Heq|]. split; [|split; [exact Hlf | exact Hkn]].
apply regs_ok_pin; [exact Hregs|].
cbn [edenot]. destruct Ha'' as [Hv _]. rewrite <- (Hv (s_next ss')) by lia. rewrite eupd_at.
exact (Hregs1 rd).
Qed.
#[using="Type"] Lemma sym_stepX_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "S='<'U0'aOyR0%211'>y8%511%311p051'Z8'QN'RJ'Y9yQ0%=11'I%<12&QJvaD&aN&Y1r6%211%42E1%7261(3r1%22=1%=3<41'6&QLr2%211(8%C3521'A'Q9%22J1%Q211&R4r3%211(@+4%24Q18G1%D281%O3851'YE&Z:r=r7r9&Y8%55Q34321(SJ(='Y=%211r5%53Q621%Q=3=71&\0r<r;r:%45@321>'J'H&[M&Y0%11Er@%4321Q9'Q0%51:%2251'QM%11R3&R1%12QMA(QI%12R7QG%R33531r?r>%H5QF21EQK%C241%D2<1%E2@1qQPHR?1%H2R@1qRHRK1%J2RL1p0L1p0Q21p0QA1p0QN1p0R51pQU<RD1pQS6RG1pQSJRK1po0RJ1pQPFRL1pQSFRN1pQRFS01plJS11pRFS:1pS4S<1").
Proof.
intros K E base rom ss ms i ssx scr' w Hf He Hd H HX. unfold sym_stepX in H.
destruct (sym_step segs i ss scr_nil) as [ss' scs scr2|] eqn:Hst; [|discriminate].
destruct (Nat.leb (s_next ss) (s_next ss')) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
injection H as Hss Hfil Hscr. subst ssx scr'.
set (i0 := s_next ss) in *.
pose proof (st_okX_R _ _ _ _ _ HX) as HR0.
destruct (st_okR_parts E base rom ss ms HR0) as (Hregs0 & Hmem0 & Hlf0 & Hkn0 & _).
assert (HV : exists E1, eagree i0 E E1 /\
(forall E'', eagree (s_next ss') E1 E'' -> scs_denot segs base E'' scs)).
{ destruct (find_readbase i0 scs) as [[[a n] sx]|] eqn:Hrb.
- pose proof (x_filter_nil ss ss' scs _ Hfil (find_readbase_In _ _ _ _ _ Hrb)) as Hdis.
fold i0 in Hdis. rewrite Hrb in Hdis. unfold x_dischargeable in Hdis.
apply andb_prop in Hdis as [Hdis Hcov]. apply andb_prop in Hdis as [Hdis Hn8]. apply andb_prop in Hdis as [Hdis Hn1].
apply andb_prop in Hdis as [Hdis Hvars]. apply andb_prop in Hdis as [Hdis Hlt]. clear Hdis.
apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8. apply Nat.ltb_lt in Hlt.
destruct a as [ab ak]. cbn [a_base a_off] in Hcov, Hvars.
destruct (kn_readable_sound E _ _ base _ ab ak n (facts_of_ok segs E base _ Hkn0) Hkn0 Hn1 Hn8 Hcov) as (Hfl & bs & Hbs & Hlen).
exists (eupd E i0 (Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)))).
split; [apply eagree_upd|].
intros E'' Ha''.
assert (HaE : eagree i0 E E'').
{ eapply eagree_trans; [apply eagree_upd | eapply eagree_le; [exact Ha'' | exact Hle]]. }
destruct (st_okR_parts E'' base rom ss ms (HX E'' HaE)) as (_ & _ & _ & Hkn'' & _).
unfold scs_denot. apply Forall_forall. intros sc Hin.
eapply (x_discharge_sound E E''); [exact Hkn'' | exact HaE | exact (x_filter_nil ss ss' scs sc Hfil Hin) |].
intros a' n' sx' Hrb'. fold i0 in Hrb'. rewrite Hrb in Hrb'. injection Hrb' as <- <- <-.
exists bs. split; [exact Hbs|].
destruct Ha'' as [Hv _]. subst i0. rewrite <- (Hv (s_next ss) Hlt). apply eupd_at.
- exists E. split; [apply eagree_refl|].
intros E'' Ha''.
assert (HaE : eagree i0 E E'') by (eapply eagree_le; [exact Ha'' | exact Hle]).
destruct (st_okR_parts E'' base rom ss ms (HX E'' HaE)) as (_ & _ & _ & Hkn'' & _).
unfold scs_denot. apply Forall_forall. intros sc Hin.
eapply (x_discharge_sound E E''); [exact Hkn'' | exact HaE | exact (x_filter_nil ss ss' scs sc Hfil Hin) |].
intros a' n' sx' Hrb'. fold i0 in Hrb'. rewrite Hrb in Hrb'. discriminate. }
destruct HV as (E1 & Ha1 & Hscs).
destruct (sym_step_soundR segs E1 base rom ss ms i ss' scs scr_nil scr2 w Hf He Hd Hst
(Hscs E1 (eagree_refl _ _)) (HX E1 Ha1)) as (ms' & Hstep & HR1).
assert (ALL : forall E'', eagree (s_next ss') E1 E'' -> st_okR segs E'' base rom ss' ms').
{ intros E'' Ha''.
assert (HaE : eagree i0 E E'') by (eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha'' | exact Hle]]).
destruct (sym_step_soundR segs E'' base rom ss ms i ss' scs scr_nil scr2 w Hf He Hd Hst (Hscs E'' Ha'') (HX E'' HaE))
as (ms'' & Hstep'' & HR''). rewrite Hstep in Hstep''. injection Hstep'' as <-. exact HR''. }
destruct (cap_rd_sound K i E1 base rom ss' ms' ALL) as (E' & Ha' & Hle' & HX').
exists E', ms'. split; [|split; [lia | split; [exact Hstep | exact HX']]].
eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha' | exact Hle]].
Qed.
#[using="Type"] Lemma sym_execTX_go_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R@&V0'<'6';'Q9%211'Z8'aOyR0%211'>y8%511%311p051&V1vaDr9%3221'M'I&Z5r:r8r7r6r5r4%78<6;54321%93G12'H'Y4%F11&Y3r1%211(0%116%B3631'Q0&Y0%11@%218%4221'U0'QN&\0r2%251GFI>'J&[Mr;%<11%331K6'\E%13Q7LE%:59Q7Q1OF%K221%L251qQPD>1%;2?1qRHA1%=2B1p0?1pQPFC1pRFE1%Q42G1%Q52M1tQQJQNQ81%QB2Q81p0QD1pQRFQI1plJQJ1pm@R31pQSFR41pQT>R61pn2R:1pn:R<1pS4R=1pQTFR?1").
Proof.
intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck base rom Ht.
- cbn [sym_execTX_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|]. split; [lia|].
intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst].
- assert (Hstop : (if s_clean ss then ss else ck) = ck \/
(let r := (if s_clean ss then ss else ck) in
s_resv r = None /\ (s_next ss <= s_next r)%nat /\
(forall E ms, st_okX E base rom ss ms ->
exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okX E' base rom r mr))).
{ destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|]. split; [lia|].
intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst]. }
cbn [sym_execTX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
destruct (itab_lookup t (s_pc ss)) as [i|] eqn:Hl; [|exact Hstop].
pose proof (Ht _ _ Hl) as Hen. unfold itab_entry in Hen.
destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|discriminate].
destruct (is_ecall w) eqn:Hec; [discriminate|].
destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz.
injection Hen as ->.
destruct (sym_stepX segs K i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
destruct scs2 as [|x l]; [|exact Hstop].
set (ck' := if s_clean ss2 then ss2 else ck).
specialize (IH false stops ss2 ck' base rom Ht).
assert (ONE : forall E ms, st_okX E base rom ss ms ->
exists E' msA, eagree (s_next ss) E E' /\ (s_next ss <= s_next ss2)%nat /\
msteps segs ms msA /\ st_okX E' base rom ss2 msA).
{ intros E ms Hst.
destruct (sym_stepX_sound K E base rom ss ms i ss2 scr2 w Hf Hec Hd Hstep Hst) as (E' & msA & Ha & Hle & HstepA & HstA).
exists E', msA. split; [exact Ha|]. split; [exact Hle|]. split; [|exact HstA].
eapply mst_step; [destruct (st_okX_R _ _ _ _ _ Hst) as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl]. }
destruct IH as [Hck|(Hr & Hle2 & Hrun)].
+ subst ck'. destruct (s_clean ss2) eqn:Hc2.
* right. rewrite Hck. split; [apply s_clean_None; exact Hc2|].
split.
{
unfold sym_stepX in Hstep. destruct (sym_step segs i ss scr_nil) as [ss3 scs3 scr3|]; [|discriminate].
destruct (Nat.leb (s_next ss) (s_next ss3)) eqn:Hle3; [|discriminate]. apply Nat.leb_le in Hle3.
injection Hstep as <- _ _. unfold cap_rd. destruct K; [exact Hle3|].
destruct (rd_of i); [|exact Hle3]. destruct (bv_eqb _ _); [exact Hle3|]. destruct (esize_le _ _); [exact Hle3|].
cbn [s_next]. lia. }
intros E ms Hst. destruct (ONE E ms Hst) as (E' & msA & Ha & _ & Hms & HstA).
exists E', msA. split; [exact Ha|]. split; [exact Hms | exact HstA].
* left. exact Hck.
+ right. split; [exact Hr|]. split.
{ unfold sym_stepX in Hstep. destruct (sym_step segs i ss scr_nil) as [ss3 scs3 scr3|]; [|discriminate].
destruct (Nat.leb (s_next ss) (s_next ss3)) eqn:Hle3; [|discriminate]. apply Nat.leb_le in Hle3.
assert (s_next ss <= s_next ss2)%nat; [|lia].
injection Hstep as <- _ _. unfold cap_rd. destruct K; [exact Hle3|].
destruct (rd_of i); [|exact Hle3]. destruct (bv_eqb _ _); [exact Hle3|]. destruct (esize_le _ _); [exact Hle3|].
cbn [s_next]. lia. }
intros E ms Hst.
destruct (ONE E ms Hst) as (E' & msA & Ha & Hle & HmsA & HstA).
destruct (Hrun E' msA HstA) as (E2 & mr & Ha2 & Hmr & Hstr).
exists E2, mr. split; [|split; [eapply msteps_trans; [exact HmsA | exact Hmr] | exact Hstr]].
eapply eagree_trans; [exact Ha | eapply eagree_le; [exact Ha2 | exact Hle]].
Qed.
#[using="Type"] Theorem sym_execTX_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R<&V0'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&V1vaDr:%3221&[M&Y0r7%211r6r1%63321&\3r2r5r8r4%56?48321p071pRHL1&Z4r<r;r9%47F32E19A'J'H%E1H%G315?'Q0r3%I11%3251'\E%13Q0IH%M1C%O316J%I6Q3HQ2>G7p021pRJQ@1%>261%?291%@2>1qQPHQ;1%C2Q<1qRHQF1%E2QG1tQSHQIG1p0M1p0Q=1pQPFQB1pQRFQD1plJQE1pRFQN1pQSFR01pQT>R21pn2R61pn:R81pS4R91pQTFR;1").
Proof.
intros t K fuel first stops ss E base rom ms Ht Hst. unfold sym_execTX.
assert (HX : st_okX E base rom (clr ss) ms) by (apply st_okX_clr; exact Hst).
destruct (sym_execTX_go_sound t K fuel first stops (clr ss) (clr ss) base rom Ht) as [Hck|(Hr & Hle & Hrun)].
- rewrite Hck. exists E, ms. split; [apply eagree_refl|]. split; [cbn [s_next clr]; lia|].
split; [apply mst_refl|]. intros E'' Ha. apply st_okR_ok; [apply HX; exact Ha | reflexivity].
- destruct (Hrun E ms HX) as (E' & mr & Ha & Hmr & HX').
exists E', mr. split; [exact Ha|]. split; [exact Hle|]. split; [exact Hmr|].
intros E'' Ha''. apply st_okR_ok; [apply HX'; exact Ha'' | exact Hr].
Qed.
#[using="Type"] Theorem sym_execTX_ex : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "S<&V0'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&V1vaDr:%3221&[M&Y0r7%211r6r1%63321&\3r2r5r8r4%56?48321p071pRHL1&Z4r<r;r9%47F32E19A'J&RMy5%221Q2'H%H1K%J318B'Q0r3%L11%3251&\?&Y2%115%33J1M&\=&XO%119%32N1&\<&XN%11=%34Q=Q2Q01'\E&\Gv_5&aN&Y1%11D%32QM1&\>%13Q;Q9>%857Q?31QB%:3QHQA1%QE1Q;%QG31KQB%91Q?%;2R51%F1QA%93Q@QM1%@5?Q031Q:%QF6R0QEQOQ;QD1p071pRJR=1%Q82;1%Q92G1%Q:2L1%Q;2Q11%Q<2Q61%Q=2Q;1qVFQ?1%QC2Q@1qRHRF1%QE2RG1tQSHRIQG1p0QM1p0R=1pQPFRB1pQRFRD1plJRE1pRFRN1pQSFS01pQT>S21pn2S61pn:S81pS4S91pQTFS;1").
Proof.
intros t K fuel first stops ss E base rom ms Ht Hst.
destruct (sym_execTX_sound t K fuel first stops ss E base rom ms Ht Hst) as (E' & ms' & Ha & Hle & Hms & HALL).
destruct (HALL E' (eagree_refl _ _)) as (R & Heq & Hregs & Hlf & Hkn).
exists E', R. split; [exact Ha|]. split; [exact Hle|]. split; [exact Hregs|]. split; [exact Hlf|]. split; [exact Hkn|].
rewrite <- Heq. split; [exact Hms | exact HALL].
Qed.
#[using="fx"] Theorem sym_execTX_resv : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q2&V0'<'6';'Q9%211'Z8&V1vaDr6%3221'I'>'Y4%211&Y3&Z4r7r5r4r3r2%67>5=4321%811(0%11<%?3<31p0A1pQSFF1pQT>H1pn2L1pn:N1pS4O1pQTFQ11").
Proof.
intros t K fuel first stops ss Ht. unfold sym_execTX.
destruct (sym_execTX_go_sound t K fuel first stops (clr ss) (clr ss) (fun _ => None) (fun _ => None) Ht) as [Hck|(Hr & _)].
- rewrite Hck. reflexivity.
- exact Hr.
Qed.
#[using="Type"] Lemma sym_execSX_go_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R:'<'6';'Q9%211'Z8'aOyR0%211'>y8%511%311p051'M'I&Z1vaDr8r7r6r5r4r3%877654321%:3D12'H'Y4%C11&Y3r1%211(0%116%C3631'Q0&Y0%11@%218%4221'U0'QN&\0r2%251GFI>'J&[Mr:%<11%331L6'\E%13Q2ME%:59Q2Q1Q0F%K221%L251qQPD>1%;2?1qRHA1%=2B1p0?1pQPFC1pRFE1%Q42G1%Q52M1tQQJQKQ81%QC2Q81pQRFQE1plJQF1pm@QO1pQSFR01pQT>R21pn2R61pn:R81pS4R91").
Proof.
intros K fuel. induction fuel as [|f IH]; intros first stops ss ck base rom.
- cbn [sym_execSX_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|]. split; [lia|].
intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst].
- assert (Hstop : (if s_clean ss then ss else ck) = ck \/
(let r := (if s_clean ss then ss else ck) in
s_resv r = None /\ (s_next ss <= s_next r)%nat /\
(forall E ms, st_okX E base rom ss ms ->
exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okX E' base rom r mr))).
{ destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
split; [apply s_clean_None; exact Hc|]. split; [lia|].
intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst]. }
cbn [sym_execSX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact Hstop].
destruct (is_ecall w) eqn:Hec; [exact Hstop|].
destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact Hstop].
destruct (negb (Z.eqb sz 4)) eqn:Hsz; [exact Hstop|].
assert (sz = 4%Z) as -> by (destruct (Z.eqb_spec sz 4); [assumption|discriminate]).
destruct (sym_stepX segs K i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
destruct scs2 as [|x l]; [|exact Hstop].
set (ck' := if s_clean ss2 then ss2 else ck).
specialize (IH false stops ss2 ck' base rom).
assert (LE1 : (s_next ss <= s_next ss2)%nat).
{ unfold sym_stepX in Hstep. destruct (sym_step segs i ss scr_nil) as [ss3 scs3 scr3|]; [|discriminate].
destruct (Nat.leb (s_next ss) (s_next ss3)) eqn:Hle3; [|discriminate]. apply Nat.leb_le in Hle3.
injection Hstep as <- _ _. unfold cap_rd. destruct K; [exact Hle3|].
destruct (rd_of i); [|exact Hle3]. destruct (bv_eqb _ _); [exact Hle3|]. destruct (esize_le _ _); [exact Hle3|].
cbn [s_next]. lia. }
assert (ONE : forall E ms, st_okX E base rom ss ms ->
exists E' msA, eagree (s_next ss) E E' /\ msteps segs ms msA /\ st_okX E' base rom ss2 msA).
{ intros E ms Hst.
destruct (sym_stepX_sound K E base rom ss ms i ss2 scr2 w Hf Hec Hd Hstep Hst) as (E' & msA & Ha & Hle & HstepA & HstA).
exists E', msA. split; [exact Ha|]. split; [|exact HstA].
eapply mst_step; [destruct (st_okX_R _ _ _ _ _ Hst) as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl]. }
destruct IH as [Hck|(Hr & Hle2 & Hrun)].
+ subst ck'. destruct (s_clean ss2) eqn:Hc2.
* right. rewrite Hck. split; [apply s_clean_None; exact Hc2|]. split; [exact LE1|].
intros E ms Hst. destruct (ONE E ms Hst) as (E' & msA & Ha & Hms & HstA).
exists E', msA. split; [exact Ha|]. split; [exact Hms | exact HstA].
* left. exact Hck.
+ right. split; [exact Hr|]. split; [lia|].
intros E ms Hst.
destruct (ONE E ms Hst) as (E' & msA & Ha & HmsA & HstA).
destruct (Hrun E' msA HstA) as (E2 & mr & Ha2 & Hmr & Hstr).
exists E2, mr. split; [|split; [eapply msteps_trans; [exact HmsA | exact Hmr] | exact Hstr]].
eapply eagree_trans; [exact Ha | eapply eagree_le; [exact Ha2 | exact LE1]].
Qed.
#[using="Type"] Theorem sym_execSX_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R5'<'6';'Q9%211'Z8'U0'aOyR0%211'>y8%511%311p051'QN&[M&Y0r6%211r5r1%63321&\3vaDr2r4r7r3%66549321p081pRHI1&Z0r:r9r8%46<3219B'J'H%F15%H315?'Q0%I1>%2241'\E%13EIH%M1D%O31CJ%I6HG>=LDp021pRJQ<1%=261%>291%?2=1qQPHQ71%B2Q81qRHQB1%D2QC1tQSHQEF1p0L1pQPFQ=1pQRFQ?1plJQ@1pRFQI1pQSFQK1pQT>QM1pn2R11pn:R31pS4R41").
Proof.
intros K fuel first stops ss E base rom ms Hst. unfold sym_execSX.
assert (HX : st_okX E base rom (clr ss) ms) by (apply st_okX_clr; exact Hst).
destruct (sym_execSX_go_sound K fuel first stops (clr ss) (clr ss) base rom) as [Hck|(Hr & Hle & Hrun)].
- rewrite Hck. exists E, ms. split; [apply eagree_refl|]. split; [cbn [s_next clr]; lia|].
split; [apply mst_refl|]. intros E'' Ha. apply st_okR_ok; [apply HX; exact Ha | reflexivity].
- destruct (Hrun E ms HX) as (E' & mr & Ha & Hmr & HX').
exists E', mr. split; [exact Ha|]. split; [exact Hle|]. split; [exact Hmr|].
intros E'' Ha''. apply st_okR_ok; [apply HX'; exact Ha'' | exact Hr].
Qed.
#[using="fx"] Theorem sym_execSX_resv : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "L'<'6';'Q9%211'Z8'I'>'Y4%211&Y3&Z0vaDr5r4r3r2r1%76654321%911(0%11=%@3=31pQSFB1pQT>D1pn2H1pn:J1pS4K1").
Proof.
intros K fuel first stops ss. unfold sym_execSX.
destruct (sym_execSX_go_sound K fuel first stops (clr ss) (clr ss) (fun _ => None) (fun _ => None)) as [Hck|(Hr & _)].
- rewrite Hck. reflexivity.
- exact Hr.
Qed.
End XSound.
#[using="Type"] Lemma wbytes_out : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QA';'aOy8%211%411yR0%511'>%115p031&]<&]8&b4r2%2291&]G&:r4%22?1%411%9261&]I+2+R0%3221%?251'M&]Ar3%A2H1%32@1r5%@2M1%B11%G251%I21E%:261'I&\Dr6%249G1<%:1=%53Q221p071p0C1pQULQ71pkNQ81pQP<Q61pm4Q<1").
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
| KFill a n _ => ka = a /\ kl = n
| KUnk a n => ka = a /\ kl = n
end ->
((estart E wa + Z.of_nat w <= estart E ka)%Z \/ (estart E ka + elenZ E kl <= estart E wa)%Z) ->
kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) K.
Proof.
intros E M wa w V K ka kl Hfw HK Hshape Hdis.
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
destruct K as [[kb kk] w' v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] n fc|[kb kk] n]; cbn [kentry_ok] in *;
[ | | | | exact HK | exact HK
| destruct HK as [Hf0 Hs0]; split; [exact Hf0|]; intros d m Hd Hm;
eapply store_ok_mono; [apply wbytes_grows | apply Hs0; assumption]
| exact HK | | ].
5: { destruct Hshape as (-> & ->). destruct HK as [Hfk Hz]. split; [exact Hfk|].
intros i Hi. rewrite wbytes_out; [apply Hz; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia. }
5: { destruct Hshape as (-> & ->). destruct HK as [Hfk Hz]. split; [exact Hfk|].
intros i Hi. rewrite wbytes_out; [apply Hz; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia. }
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
#[using="Type"] Lemma kzero_piece : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RI'U0'aOyR0%211'>y8%511%311p051'U9'Q9'<&\:r:(SHr8r7%3221&]Gr6%211%93841&\;vaDr;(SEr9r5%>221(S=r4%211%7241%;4:9D1&]<z%2216&]A%1238&]8%12E=&]D&]I+2+R0%3221%52N1%=271'M%:2GQ1%;21Or<%B221%Q31M%?231%E216%8241r@&\Dr?&SMr>r=%QA221%4271&R3%12?Q:%93831%M2QGQE%QG281%Q91QF%Q>221%QB4QA?51p0A1p0K1p0Q51p0Q81p0Q<1p0QI1pQP2R51po2R61poLR71poDR81pkLR@1pQU<R91pQUFR;1pQUBR=1pV@R?1pRFRH1").
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
#[using="Type"] Lemma kimg_piece : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R1'U0'aOyR0%211'>y8%511%311p051'Y4'<'Q9&\:r9r7&]Gr6%211%63541&\;vaDr:(SBr5r4%3221%7465=1&]<%12<4%225='M&\8r=r;%3221%82<1&]8%F1@%2241%<21G%:251r>&\D&SMr<%2241&R3%12>J%63@31%K2Q3Q1%O4N921p0;1p0G1p0I1p0L1p0Q51pnDQ=1pQP6Q>1pnBQ?1pQP4Q@1pkLQI1pQU<QC1pQU@QE1pV@QG1pRFR01").
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
Definition zf_kind (mk : saddr -> expr -> kentry) (byteof : option byte -> Prop) : Prop :=
forall E M a n,
kentry_ok segs E M (mk a n)
<-> (flat E a (elenZ E n)
/\ forall i, (0 <= i < elenZ E n)%Z -> byteof (M (Z_to_bv 64 (estart E a + i)))).
#[using="Type"] Lemma zf_kind_zero : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "A&[I(SE'>'aOy8%211%411'Ir1(3&aNz%2281%4281%73861qQUL91%@2?1").
Proof. intros E M a n. cbn [kentry_ok]. tauto. Qed.
#[using="Type"] Lemma zf_kind_fill : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "I'Q9&[I'Y4'U9(SAr2r1r3%43321qQPJ61qkN81'>'aOy8%211%411'I(3&aN%126>%3261%536?1qQUL71%F2=1pm8H1").
Proof. intros c E M a n. cbn [kentry_ok]. tauto. Qed.
#[using="Type"] Lemma zf_kind_unk : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "@&[I(SC'>'aOy8%211%411&L'Ir1(0%116%43631%611qQUL81%?2>1").
Proof. intros E M a n. cbn [kentry_ok]. tauto. Qed.
#[using="Type"] Lemma kcut_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RI'Y4'U9'V7p021p041'>'aOy8%211%411!p021'U0yR0%811p016pQUL27';%11@'Q9&[Ir=r<%3221&\<vaDr;r8%443621&\;r?(SHr5r4%3221r3%6221%84<@;1'M&]A&b4r1%22M1&\8r:r9%?221%42A1%9261&]<&]8&\6%12FI%3261%521<%A271'Ir2%Q511r>%113%53QD31p071pQULQA1'Q2%Q43Q8Q3Q;&V4rAr7r6%483Q<JIQ;21Q6%73R561p091p0Q41p0Q>1p0QD1pQP2R;1poDQJ1po@R=1pQUHR>1pQUFQM1pQUBR@1pl8R01pVBR31pV@R51pVDR61pRFR:1pm6R<1pQP@RD1").
Proof.
intros mk byteof E M0 M M' allkn wb wk wn kb kk len Hkind Hall HK Hout.
apply (proj1 (Hkind E M _ _)) in HK. destruct HK as [Hfl Hz].
unfold kcut.
set (ws := mkAlu ALU_ADD wb (ELit wk)). set (ks := mkAlu ALU_ADD kb (ELit kk)).
assert (Uws : eqm (bv_unsigned (edenot E ws)) (estart E (SA wb wk))).
{ subst ws. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
assert (Uks : eqm (bv_unsigned (edenot E ks)) (estart E (SA kb kk))).
{ subst ks. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
apply Forall_app; split.
-
destruct (lin_ge0 allkn [(kb, kk)] [(wb, wk)]); [constructor|].
destruct (lin_ge0 allkn [(wb, wk)] [(kb, kk)]) eqn:H1; [|constructor].
destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk)]) eqn:H2; [|constructor].
pose proof (lin_ge0_sound segs E M0 allkn _ _ Hall H1) as A. cbn [xt_den] in A.
pose proof (lin_ge0_sound segs E M0 allkn _ _ Hall H2) as B. cbn [xt_den] in B.
constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)).
assert (HL : elenZ E (mkAlu ALU_SUB ws ks) = (estart E (SA wb wk) - estart E (SA kb kk))%Z).
{ unfold elenZ. rewrite mkAlu_denot.
assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E ws) (edenot E ks))) (estart E (SA wb wk) - estart E (SA kb kk))) as [q Hq].
{ eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add; [exact Uws|]. destruct Uks as [q Hq]. exists (-q)%Z. lia. }
pose proof (u64_range (alu64 ALU_SUB (edenot E ws) (edenot E ks))) as R.
pose proof (u64_range (edenot E len)) as RL.
unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
rewrite HL. split.
+ unfold flat in *. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
+ intros i Hi. rewrite Hout; [apply Hz|]; unfold estart, elenZ in *; cbn [a_base a_off] in *; [lia|].
left. rewrite u_small; lia.
-
destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]) eqn:H1; [|constructor].
destruct (lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(kb, kk)]) eqn:H2; [|constructor].
destruct (lin_ge0 allkn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]) eqn:H3; [|constructor].
pose proof (lin_ge0_sound segs E M0 allkn _ _ Hall H1) as A. cbn [xt_den] in A.
pose proof (lin_ge0_sound segs E M0 allkn _ _ Hall H2) as B. cbn [xt_den] in B.
pose proof (lin_ge0_sound segs E M0 allkn _ _ Hall H3) as C. cbn [xt_den edenot] in C.
rewrite u_lit0 in C. unfold two64 in C.
cbv zeta.
set (we := mkAlu ALU_ADD ws wn).
assert (Uwe : eqm (bv_unsigned (edenot E we)) (estart E (SA wb wk) + elenZ E wn)).
{ subst we. rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uws|apply eqm_refl]. }
destruct (split_lit we) as [hb ho] eqn:Hsp.
lazymatch goal with |- Forall _ [mk ?ha0 _] => set (ha := ha0) end.
assert (Hst : estart E ha = (estart E (SA wb wk) + elenZ E wn)%Z).
{ subst ha.
destruct (lin_ge0 allkn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool eqn:Hh.
- apply andb_prop in Hh as [Hh1 Hh2].
pose proof (lin_ge0_sound segs E M0 allkn _ _ Hall Hh1) as C1. cbn [xt_den] in C1.
pose proof (lin_ge0_sound segs E M0 allkn _ _ Hall Hh2) as C2. cbn [xt_den] in C2.
unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
- unfold estart at 1; cbn [a_base a_off]. rewrite Z.add_0_r.
destruct Uwe as [q Hq]. pose proof (u64_range (edenot E we)).
pose proof (u64_range (edenot E len)) as RL.
unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
assert (HL : elenZ E (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)
= (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))%Z).
{ unfold elenZ at 1. rewrite mkAlu_denot.
assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we)))
(estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))) as [q Hq].
{ eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add.
- rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uks|apply eqm_refl].
- destruct Uwe as [q Hq]. exists (-q)%Z. lia. }
pose proof (u64_range (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we))) as R.
pose proof (u64_range (edenot E len)) as RL.
unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)). rewrite HL.
split.
+ unfold flat. rewrite Hst. pose proof (u64_range (edenot E len)) as RL.
unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia.
+ intros i Hi. rewrite Hst.
rewrite Hout.
* replace (estart E (SA wb wk) + elenZ E wn + i)%Z
with (estart E (SA kb kk) + (estart E (SA wb wk) + elenZ E wn - estart E (SA kb kk) + i))%Z by lia.
apply Hz. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
* right. pose proof (u64_range (edenot E len)) as RL.
rewrite u_small; unfold flat, estart, elenZ in *; cbn [a_base a_off] in *; lia.
Qed.
#[using="Type"] Lemma kzero_cut_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R>'U0'aOyR0%211'>y8%511%311p051pQUL62';'V7%211'U9'Q9&\<vaDr;r:r7%544321&\;r<(SE(SHr4r3%3221r2%6221%94>8<1'M&]A&b4r1%22Q11&\8r>r9r8%@221%5241%:271&]<&]8&\6%129K%3261%521=%B271'I%M1Gr=%11I%43Q?31p061pQULQE1'Q2%Q53Q:EQ9&VCr6r5%37Q<HGQ;21Q5%63QD51p081p0Q31p0Q>1pQP2QF1poDQF1po@QH1pQUHQI1pQUFQI1pQUBQK1pl8QM1pVBR11pV@R31pVDR41pRFR=1").
Proof. intros. eapply (kcut_sound KZero); eauto using zf_kind_zero. Qed.
#[using="Type"] Lemma kfill_cut_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R@'Q9'U0'aOyR0%211'>y8%511%311p051pQUL62';'V7%211'U9&\<vaDr;r:r7%544321&\;r<(SA(SHr4r3%3221r2r=%73321%:4?9=1'M&]A&b4r1%22Q11&\8r>r9r8%A221%5241%:271&]<&]8&\6%129L%3261%521=%B271'I%N1H%H1I%33Q>21p051pQULQD1'Q2%Q53Q:DQ9&V:r?r6r5%483Q=HGQ<21Q6%73QD61p091p0Q31p0Q?1pQP2QF1poDR51po@QH1pQUHQI1pQUFR81pQUBQK1pl8QM1pVBR11pV@R31pVDR41pRFR=1pm8R?1").
Proof. intros. eapply (kcut_sound (fun a n => KFill a n c)); eauto using zf_kind_fill. Qed.
#[using="Type"] Lemma kunk_cut_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R>'U0'aOyR0%211'>y8%511%311p051pQUL62';'V7%211'U9'Q9&\<vaDr;r:r7%544321&\;r<(SC(SHr4r3%3221r2%6221%94>8<1'M&]A&b4r1%22Q11&\8r>r9r8%@221%5241%:271&]<&]8&\6%129K%3261%521=%B271'I%M1Gr=%11I%43Q?31p061pQULQE1'Q2%Q53Q:EQ9&V@r6r5%37Q<HGQ;21Q5%63QD51p081p0Q31p0Q>1pQP2QF1poDQF1po@QH1pQUHQI1pQUFQI1pQUBQK1pl8QM1pVBR11pV@R31pVDR41pRFR=1").
Proof. intros. eapply (kcut_sound KUnk); eauto using zf_kind_unk. Qed.
#[using="Type"] Lemma kcut_store : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RD'Y4'U9'V7p021p041'>'aOy8%211%411!p021'U0yR0%811p016';%11?'<'Q9&[Ir<r;%3221&\<vaDr:r8%443621'Q0r7u8%3221&\:r=r9&]G%11:%53431&\;r>r@(SHr6%22>1r5%5221%84F7J1'Q2r?&\D&SM%123N&R3%12LC%53E31%A3O71&V4rA&SK%11Q6&SL%11Q8&TM%11Q6%887Q<531Q6Q3F%B3R0:1p0D1p0N1p0Q51p0Q:1p0Q@1pQP2R71poDQF1po@R91pkLQM1pQU<QJ1pQU@R=1pl8QM1pV@R01pVDR11pRFR51pm6R71pQP@R?1").
Proof.
intros mk byteof E M0 M allkn [wb wk] w V kb kk len Hkind Hall Hw8 Hfw HK. cbn [a_base a_off].
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
eapply kcut_sound; [exact Hkind | exact Hall | exact HK |].
intros x Hx. rewrite elenZ_elen in Hx by exact Hw8.
apply wbytes_out; rewrite length_N_to_le_bytes, Huw; lia.
Qed.
#[using="Type"] Lemma kzero_cut_store : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R:'U0'aOyR0%211'>y8%511%311p051';'V7%211'Y4'<'U9'Q9&\<vaDr:r9r7%544321'Q0r6u8%3221&\:r<r8&]G%11:%53431&\;r=r;(SE(SHr5%22?1r4%5221%94H871'Q2r>&\D&SM%123L&R3%12MD%53F31%B3Q171&VC&SK%11Q3&SL%11Q5&TM%11Q6%77H531Q6Q3E%A3QA91p0C1p0N1p0Q51p0Q:1pQP2QB1poDQB1po@QD1pkLR01pQU<QG1pQU@QI1pl8QK1pV@QO1pVDR01pRFR91").
Proof.
intros E M0 M allkn [wb wk] w V kb kk len Hall Hw8 Hfw HK. cbn [a_base a_off].
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
eapply kzero_cut_sound; [exact Hall | exact HK |].
intros x Hx. rewrite elenZ_elen in Hx by exact Hw8.
apply wbytes_out; rewrite length_N_to_le_bytes, Huw; lia.
Qed.
#[using="Type"] Lemma in_sides_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N';'V7%211'U9'Q9'I'6&UMr8&THr7r6r5r4%5564321r3r2r1%;5:4321&V5%18<:987543%@3?31pQQ0B1po<C1plHE1pQPNE1po:F1plFH1poFJ1pl8K1").
Proof.
intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides kdisj_apart]; try exact IH.
destruct (sub_itv allkn b1 k1 n1 c1 m1), (sub_itv allkn b1 k1 n1 c2 m2); cbn [in_sides];
destruct (sub_itv allkn b2 k2 n2 c2 m2) eqn:E2, (sub_itv allkn b2 k2 n2 c1 m1) eqn:E1;
rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
#[using="Type"] Lemma in_sides_x_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "N';'V7%211'U9'Q9'I'6&UNr8&TIr7r6r5r4%5564321r3r2r1%;5:4321&V6%18<:987543%@3?31pQQ0C1po<C1plHE1pQPNF1po:F1plFH1poFJ1pl8K1").
Proof.
intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides_x kdisj_apart_x]; try exact IH.
destruct (sub_itv_x allkn b1 k1 n1 c1 m1), (sub_itv_x allkn b1 k1 n1 c2 m2); cbn [in_sides_x];
destruct (sub_itv_x allkn b2 k2 n2 c2 m2) eqn:E2, (sub_itv_x allkn b2 k2 n2 c1 m1) eqn:E1;
rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
#[using="Type"] Lemma ranges_apart_p_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "L';'V7%211'U9'Q9'I'6&XGr7&X6r6r5r4%445321r3r2r1%:894765321&XI%17;987543%?3>31pQQ0B1po<B1plHD1pQPNE1po:E1plFG1poFI1").
Proof.
intros kn b1 k1 n1 b2 k2 n2. unfold ranges_apart_p, ranges_apart_x, mk_sprep. cbn [sp_rng sp_h1 sp_D sp_Dx].
destruct n1; try (rewrite in_sides_x_eq; reflexivity).
destruct n2; try (rewrite in_sides_x_eq; reflexivity).
unfold ranges_apart. rewrite in_sides_eq. reflexivity.
Qed.
#[using="Type"] Lemma prune1p_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q7';'V7%211'Y4'<'U9'6%711'I'A'Y=%;11%32:1%4216&X@r6&X6&SKr5%211&SL%113&TMr4%211%94:641r3r2r1%?7>4;6321&X?%16@=8543%H3C31pnHJ1pS4Q11pQUJN1pQU<Q01pQU@Q21pl8Q41").
Proof.
intros allkn wa w wv K hints. unfold prune1p, prune1, prune_zf.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
rewrite ?ranges_apart_p_eq; reflexivity.
Qed.
#[using="Type"] Lemma prunep_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q7';'V7%211'Y4'<'U9'6%711'I'A'Y=%;11%32:1%4216&XBr6&X6&SKr5%211&SL%113&TMr4%211%94:641r3r2r1%?7>4;6321&X>%16@=8543%H3C31pnHJ1poFQ01pQUJN1pQU<Q01pQU@Q21pl8Q41").
Proof.
intros allkn wa w wv kn. induction kn as [|K rest IH]; intros hints; [reflexivity|].
cbn [prunep prune]. rewrite prune1p_eq. destruct (prune1 allkn wa w wv K hints) as [[kept scs1] hs1].
rewrite IH. reflexivity.
Qed.
#[using="Type"] Lemma ranges_apart_pc_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "O';'V7%211'Y@'U9'Q9'I'6&XHr8r7r6r5r4&T7r3%2271r2r1%;9:98763421&XG%18<;:98643%@3?31pQQ0C1po<C1plHE1pQPNF1po:F1plFH1pQS@J1poFL1").
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma prune1pc_eq : forall allkn sp wa w wv K hints br2,
match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof.
intros allkn sp wa w wv K hints br2 Hb.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [kbase] in Hb; try reflexivity; subst br2; unfold prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
rewrite ?ranges_apart_pc_eq; destruct (expr_eqb kb (a_base wa)); reflexivity.
Qed.
Definition br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop :=
Forall (fun p => snd p = base_range allkn (fst p)) c.
#[using="Type"] Lemma br_lookup_ok : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1';'V7%211'A'U9'>'Q9%4211%311%6251%:11&[Gr4r3%3221'I%;18&T9%1265(3r2%22=1%73641&T7r6%221=%;3B=1p051p0>1pQQJE1plBJ1pm8E1pl8N1").
Proof.
intros allkn c b r Hc. induction c as [|[b' r'] rest IH]; cbn; [discriminate|].
apply Forall_cons_iff in Hc as [H1 Hc]. cbn in H1.
destruct (expr_eqb b b') eqn:E.
- intros H. injection H as <-. apply expr_eqb_eq in E. subst b'. exact H1.
- apply IH. exact Hc.
Qed.
#[using="Type"] Lemma prunepc_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q>';'V7%211'Y@'Y4'<'U9'6%811'A'>'Q9%3211%311%5281%?11&[Gr8r1%3221'I'Y=%F11%>2E1%?21@&XCr9r7r6r5r4r3r2%887@654321&XB%179B87654%@3<31p0B1pm<G1pnHO1poFQ61pQUJQ31pQU<Q51pQU@Q71pQS@Q91pl8Q;1").
Proof.
intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache Hc; [reflexivity|].
cbn [prunepc prunep].
destruct (kbase K) as [kb|] eqn:HK.
- destruct (br_lookup cache kb) as [r|] eqn:HL.
+ rewrite (prune1pc_eq allkn sp wa w wv K hints r) by (rewrite HK; exact (br_lookup_ok _ _ _ _ Hc HL)).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
+ rewrite (prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb)) by (rewrite HK; reflexivity).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1].
rewrite (IH hs1 ((kb, base_range allkn kb) :: cache)) by (constructor; [reflexivity | exact Hc]). reflexivity.
- rewrite (prune1pc_eq allkn sp wa w wv K hints None) by (rewrite HK; exact I).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
Qed.
#[using="Type"] Lemma zf_piece : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "S4'Y4'U9'V7p021p041'>'aOy8%211%411!p021'U0yR0%811p016'Q9'<&[Ir<r;%3221&\:(SHr9r8%3221&]Gr7%211%83:41&\;vaDr>r:r6%=221(S=r5%211%7241%:49FE1&]<z%2216&]A%1238&]8%12D=&]D&]I+2+R0%3221%52M1%=271'M%:2GQ0%;21Nr=%B221%Q21Q:%?231%E216%8241rA&\Dr@&SMr?%Q?21Q5%3261&R3%12>QF%83731rC%M2QHQD%QF281%Q91QE%4221%QA4Q@?61p0A1p0K1p0Q51p0Q81p0Q<1p0QH1p0R21pQP2R81po2R91poLR:1poDR;1pkLR>1pQU<R<1pQUFR>1pQUBRN1pV@RA1pRFRE1pm6RG1pQP@RO1").
Proof.
intros mk byteof E M wb wk w V kk l0 i0 len Hkind Hfw HK Hi0 Hlen Hil Hdis.
apply (proj1 (Hkind E M _ _)) in HK. destruct HK as [Hfk Hz].
apply (proj2 (Hkind E _ _ _)).
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
rewrite elenZ_lit in Hfk, Hz. rewrite elenZ_lit.
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
#[using="Type"] Lemma ktrim_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R5'Y4'U9'V7p021p041'>'aOy8%211%411!p021'U0yR0%811p016'Q9'<&[Ir:r9%3221&\:(SHr7r6%3221&]Gr5%211%83:41&\;vaDr<r8r4%=221(S=r3%211%7241%:49FE1'Q2r;&\D&SM%G2J<%2241&R3%12IH%63O31%D3C81&V?r=%261Q2JCDN%=3QE41p0?1p0K1p0Q51poLQ;1poDQ<1pkLQ?1pQU<Q=1pQUFQ?1pQUBQO1pV@QB1pRFQF1pm6QH1pQP@R01").
Proof.
intros mk byteof E M wb wk w V kk l0 Hkind Hfw HK. unfold ktrim.
pose proof HK as HK'. apply (proj1 (Hkind E M _ _)) in HK'. destruct HK' as [Hfk _]. rewrite elenZ_lit in Hfk.
destruct Hfk as (Hk1 & Hk2 & Hk3 & Hk4). unfold estart in Hk1, Hk2, Hk4; cbn [a_base a_off] in Hk1, Hk2, Hk4.
apply Forall_app_intro.
- destruct (Z.ltb kk (Z.min wk (kk + l0 mod 2 ^ 64))) eqn:Hlt; [|constructor].
apply Z.ltb_lt in Hlt. apply Forall_one.
replace kk with (kk + 0)%Z at 1 by lia.
eapply zf_piece; [exact Hkind | exact Hfw | exact HK | lia | lia | lia | lia].
- destruct (Z.ltb (Z.max kk (wk + Z.of_nat w)) (kk + l0 mod 2 ^ 64)) eqn:Hlt; [|constructor].
apply Z.ltb_lt in Hlt. apply Forall_one.
replace (Z.max kk (wk + Z.of_nat w)) with (kk + (Z.max kk (wk + Z.of_nat w) - kk))%Z at 1 by lia.
eapply zf_piece; [exact Hkind | exact Hfw | exact HK | lia | lia | lia | lia].
Qed.
#[using="Type"] Lemma zf_frame : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R?'Y4'U9'V7p021p041'>'aOy8%211%411!p021'U0yR0%811p016'<'Q9&[Ir:r9%3221&\:r7&]Gr6%211%53741&\;vaDr<(SHr5r4%3221r3%6221%948BA1'M&]<&]8&\8r;%221Gr8%E11%6231%@2F?%7261%:231&\6%129B%<241%>21:%@251&\D&SM%12KQ6&R3%12Q7?%53B31r>%O2Q7Q5%221O%Q44Q3Q241p0;1p0M1p0Q81p0Q?1pQP2R41poDQE1po@R61pkLQJ1pQU<QI1pQU@R:1pV@QL1pRFR01pm6R21pQP@R:1").
Proof.
intros mk byteof E M wa w V kb kk len Hkind Hfw HK Hdis.
apply (proj1 (Hkind E M _ _)) in HK. destruct HK as [Hfk Hz]. apply (proj2 (Hkind E _ _ _)).
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
split; [exact Hfk|].
intros i Hi. rewrite wbytes_out; [apply Hz; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia.
Qed.
#[using="Type"] Lemma prune_zf_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "TE'Y4'U9'V7p021p041'>'aOy8%211%411!p021'U0yR0%811p016';%11?'Q9'<'E'6p021%712'A'Y=%:11%32:1%4215p091&[IrDrC%3221'I&XArEr@r>r=r<(SHr:r9%3221r8%:221r7r6r5%?<>=<;:4875321(@r4r3%34Q5L21r2%54MQ121%G3M71&\<vaDrBrA%443O21'Q0u8%22K1&\:rF%K27O&]Gr?%211%63541&\;rGrI%Q32Q6Q5%221Q5%54C4Q>1(D%Q811(C%Q@3QM21'M&]<&]8&\8%Q>2QHQG%22=1%D1M%5221%QB2QFE%62A1%9231&\6%12DQI%;241%=219%?251p0A1r;%11F%QC4RER<QLQK%QD4R<R@1QJ%R63R<31&\ArJ%24Q@Q01R1'Q2rK&\D&SM%R72Q=R<%2241&R3%12RDRC%63Q:31%Q<3QJ81%:3SD1R>p0<1p0@1p012p0G1p0Q=1p0QD1p0QL1p0R01p0R61p0RO1pnNS:1pQS8S81poBSB1pmFS71pnHS>1pl>S@1pQP2T61poDSF1po@T81pkLSL1pQU<SH1pQUFSJ1pQUBT<1pV@SO1pl8SN1pVDT11pl:T21pRFT61pm6T81pQP@T@1").
Proof.
intros mk byteof E anyb M0 allkn M wb wk w V kb kk len apart hints diffbase kept scs hs'
Hkind Hp Hall Hw8 Hfw HK Hapart Hdb Hscs.
unfold prune_zf in Hp.
destruct (expr_eqb kb wb) eqn:Heqb.
- apply expr_eqb_eq in Heqb. subst kb.
destruct len as [l0| | | | | | |];
[ injection Hp as <- <- <-; eapply ktrim_sound; [exact Hkind | exact Hfw | exact HK] | .. ];
(destruct (Z.leb (wk + Z.of_nat w) kk) eqn:Hle; injection Hp as <- <- <-;
[ apply Z.leb_le in Hle; apply Forall_one;
eapply zf_frame; [exact Hkind | exact Hfw | exact HK |];
unfold estart; cbn [a_base a_off]; lia
| eapply (kcut_store mk byteof E M0 M allkn (SA wb wk)); [exact Hkind | exact Hall | exact Hw8 | exact Hfw | exact HK] ]).
- destruct (apart tt) eqn:Hap.
+ injection Hp as <- <- <-. apply Forall_one.
eapply zf_frame; [exact Hkind | exact Hfw | exact HK | exact (Hapart eq_refl)].
+ destruct (kcut mk allkn wb wk (elen w) kb kk len) as [|c1 cut] eqn:Hcut.
* exact (Hdb Hp Hscs).
* injection Hp as <- <- <-. rewrite <- Hcut.
eapply (kcut_store mk byteof E M0 M allkn (SA wb wk)); [exact Hkind | exact Hall | exact Hw8 | exact Hfw | exact HK].
Qed.
#[using="Type"] Lemma word_slice_bytes : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q5'<'aOyR0%211'Q0&Nr3r2%3221r4%6221r5u8%9221'I';y8%@11%311&R3&UA(8%241;=@%42>1&Q3&Q7r6%821E%33;A1%53<D1%@3<71p0B1p0F1pkLN1pQPJQ21pmDQ31pQU>Q41").
Proof.
intros w' d n V Hdn Hw8.
unfold word_to_le_bytes at 2. rewrite skipn_Z_to_le_bytes by lia. rewrite firstn_Z_to_le_bytes by lia.
unfold word_to_le_bytes, ext_val, ext_Z.
assert (Hb : (0 <= (bv_unsigned V / 2 ^ (8 * Z.of_nat d)) mod 2 ^ (8 * Z.of_nat n) < 2 ^ (8 * Z.of_nat n))%Z)
by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
assert (Hle : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
rewrite u_small by lia. apply Z_to_le_bytes_mod.
Qed.
#[using="Type"] Lemma kword_cut_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "R:'U0'aOyR0%211'>y8%511%311p051'U9'Q9'<&\:r9(SHr7r6%3221&]Gr5%211%93841&\;vaDr:(SDr8r4%>221r3r2%63321%:498C1'I'6&?&]=&]8%D1;%22D1%421>%G1J%52@1%721H%9241(8%=3<21'Q2'V7r<&\Dr;&SM%Q72MQ8%2251&R3%12NQ9%73631%Q43Q391&VA%16Q4Q<Q9Q1Q?Q2%>3=31p0@1p0O1p0Q;1pQU8QH1pQU>QG1poDQI1pkLR11pQU<QJ1pQUFQL1pQUBQN1pV@R01pRFR91").
Proof.
intros E M wb wk w V kk w' v Hfw HK Hov. unfold kword_cut.
destruct v as [z| | | | | | |]; try constructor.
apply orb_false_elim in Hov as [Hov1 Hov2]. apply Z.leb_gt in Hov1. apply Z.leb_gt in Hov2.
cbn [kentry_ok] in HK. destruct HK as (Hkw8 & Hfk & Hrd).
pose proof (flat_u E _ _ Hfw) as Huw. pose proof (flat_u E _ _ Hfk) as Huk.
assert (Hfw' := Hfw). destruct Hfw' as (Hw1 & Hw2 & Hw3 & Hw4).
assert (Hfk' := Hfk). destruct Hfk' as (Hk1 & Hk2 & Hk3 & Hk4).
unfold estart in Hw1, Hw2, Hw4, Hk1, Hk2, Hk4, Huw, Huk; cbn [a_base a_off] in Hw1, Hw2, Hw4, Hk1, Hk2, Hk4, Huw, Huk.
assert (PIECE : forall d n, (0 <= d)%Z -> (1 <= n)%nat -> (Z.to_nat d + n <= w')%nat ->
((kk + d + Z.of_nat n <= wk)%Z \/ (wk + Z.of_nat w <= kk + d)%Z) ->
kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))
(KWord (SA wb (kk + d)) n (mkExt false (Z.to_nat d) n (ELit z)))).
{ intros d n Hd Hn1 Hdn Hdis. cbn [kentry_ok]. split; [lia|].
assert (Hfp : flat E (SA wb (kk + d)) (Z.of_nat n)) by (unfold flat, estart; cbn [a_base a_off]; lia).
split; [exact Hfp|].
pose proof (flat_u E _ _ Hfp) as Hup. unfold estart in Hup; cbn [a_base a_off] in Hup.
rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, Huw, Hup; lia | rewrite Hup; lia
| rewrite length_N_to_le_bytes, Huw; lia ].
rewrite (adenot_shift E (SA wb kk) (SA wb (kk + d)) _ _ d Hfk Hfp) by (unfold estart; cbn [a_base a_off]; lia).
rewrite (rdn_slice segs M w' _ _ (Z.to_nat d) n Hrd) by lia.
rewrite mkExt_denot by lia. cbn [edenot].
rewrite (word_slice_bytes w' (Z.to_nat d) n) by lia. reflexivity. }
apply Forall_app_intro.
- destruct (Z.ltb 0 (wk - kk)) eqn:Hlt; [|constructor]. apply Z.ltb_lt in Hlt. apply Forall_one.
replace kk with (kk + 0)%Z at 1 by lia. change 0%nat with (Z.to_nat 0).
apply PIECE; lia.
- destruct (Z.ltb (wk + Z.of_nat w - kk) (Z.of_nat w')) eqn:Hlt; [|constructor]. apply Z.ltb_lt in Hlt. apply Forall_one.
apply PIECE; lia.
Qed.
#[using="Type"] Lemma prune1_sound : forall E (anybase : word -> option byte) M0 allkn M wa w wv K hints kept scs hs',
let V := edenot E wv in
prune1 allkn wa w wv K hints = (kept, scs, hs') ->
know_ok segs E M0 allkn ->
(w <= 8)%nat ->
flat E wa (Z.of_nat w) ->
kentry_ok segs E M K ->
match K with KWord _ w' _ => (w' <= 8)%nat | _ => True end ->
scs_denot segs anybase E scs ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept.
Proof.
intros E anyb M0 allkn M wa w wv K hints kept scs hs' V Hp Hall Hw8 Hfw HK Hkw Hscs.
pose proof (flat_u E _ _ Hfw) as Huw.
assert (Hfw' := Hfw). destruct Hfw' as (Hw1 & Hw2 & Hw3 & Hw4).
unfold prune1 in Hp.
assert (Hdiff : forall ka kl,
(let apart := ranges_apart_x allkn (a_base wa) (a_off wa) (elen w) (a_base ka) (a_off ka) kl in
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
| KFill a n _ => ka = a /\ kl = n
| KUnk a n => ka = a /\ kl = n
end ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept).
{ intros ka kl Hm Hshape. cbv zeta in Hm.
assert (Hkl : ranges_apart_x allkn (a_base wa) (a_off wa) (elen w) (a_base ka) (a_off ka) kl = true ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) [K]).
{ intros Hap. apply Forall_one.
pose proof (ranges_apart_x_sound segs E M0 allkn _ _ _ _ _ _ Hall Hap) as Hdis.
rewrite elenZ_elen in Hdis by exact Hw8.
eapply kentry_ok_frame; eauto;
destruct wa, ka; cbn [a_base a_off] in *; exact Hdis. }
destruct (ranges_apart_x allkn (a_base wa) (a_off wa) (elen w) (a_base ka) (a_off ka) kl) eqn:Hap;
[ injection Hm as <- <- <-; apply (Hkl eq_refl) | ].
destruct hints as [|[|] hs]; try (injection Hm as <- <- <-);
[ constructor | | constructor ];
(apply scs_denot_cons in Hscs as [Hd _]; cbn [sc_denot] in Hd;
destruct Hd as (_ & _ & Hd); rewrite elenZ_elen in Hd by exact Hw8;
constructor; [ eapply kentry_ok_frame; eauto | constructor ]). }
assert (Hzf : forall mk byteof kb kk len,
zf_kind mk byteof ->
kentry_ok segs E M (mk (SA kb kk) len) ->
match K with
| KWord a w' _ => SA kb kk = a /\ len = elen w' /\ (w' <= 8)%nat
| KZero a n => SA kb kk = a /\ len = n
| KBlob a n _ => SA kb kk = a /\ len = n
| KImg lo hi => SA kb kk = SA (ELit 0) lo /\ len = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)%Z
| KAlign _ _ => True
| KRange _ _ _ => True
| KWr _ _ => True
| KDisj _ _ _ _ => True
| KFill a n _ => SA kb kk = a /\ len = n
| KUnk a n => SA kb kk = a /\ len = n
end ->
prune_zf mk allkn (a_base wa) (a_off wa) w (mk (SA kb kk) len) kb kk len
(fun _ => ranges_apart_x allkn (a_base wa) (a_off wa) (elen w) kb kk len) hints
(fun _ => let apart := ranges_apart_x allkn (a_base wa) (a_off wa) (elen w) (a_base (SA kb kk)) (a_off (SA kb kk)) len in
if apart then ([K], [], hints) else
match hints with
| true :: hs => ([K], [SCDisj wa (elen w) (SA kb kk) len], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end) = (kept, scs, hs') ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept).
{ intros mk byteof kb kk len Hkind HKm Hshape Hpz.
destruct wa as [wb wk]. cbn [a_base a_off] in Hpz.
eapply (prune_zf_sound mk byteof E anyb M0 allkn M wb wk w V kb kk len); try eassumption.
- intros Hap. pose proof (ranges_apart_x_sound segs E M0 allkn _ _ _ _ _ _ Hall Hap) as Hdis.
rewrite elenZ_elen in Hdis by exact Hw8. exact Hdis.
- intros Hm _. eapply (Hdiff (SA kb kk) len); [exact Hm | exact Hshape]. }
destruct K as [[kb kk] w' v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] n fc|[kb kk] n].
10: { eapply (Hzf KUnk _ kb kk n zf_kind_unk); [exact HK | cbn; auto | exact Hp]. }
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
5: { injection Hp as <- <- <-. apply Forall_one. cbn [kentry_ok] in HK |- *.
destruct HK as [Hf0 Hs0]. split; [exact Hf0|]. intros d m Hd Hm.
eapply store_ok_mono; [apply wbytes_grows | apply Hs0; assumption]. }
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
5: { eapply (Hzf (fun a n0 => KFill a n0 fc) _ kb kk n (zf_kind_fill fc)); [exact HK | cbn; auto | exact Hp]. }
2: { eapply (Hzf KZero _ kb kk n zf_kind_zero); [exact HK | cbn; auto | exact Hp]. }
-
destruct (expr_eqb kb (a_base wa)) eqn:Heqb.
2: { destruct (ranges_apart_x allkn (a_base wa) (a_off wa) (elen w) kb kk (elen w')) eqn:Hapx.
{ injection Hp as <- <- <-. apply Forall_one.
pose proof (ranges_apart_x_sound segs E M0 allkn _ _ _ _ _ _ Hall Hapx) as Hdis.
rewrite elenZ_elen in Hdis by exact Hw8.
eapply (kentry_ok_frame E M wa w V _ (SA kb kk) (elen w') Hfw HK); [cbn; auto|].
destruct wa; cbn [a_base a_off] in *; exact Hdis. }
destruct (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool eqn:Hb;
[|eapply Hdiff; [exact Hp | cbn; auto]].
injection Hp as <- <- <-. apply Forall_one.
apply andb_prop in Hb as [Hb Hv]. apply andb_prop in Hb as [Hq1 Hq1'].
apply Nat.eqb_eq in Hq1. apply Nat.eqb_eq in Hq1'. apply expr_eqb_eq in Hv. subst w w' wv.
cbn [kentry_ok] in HK |- *. destruct HK as (Hle & Hfk & Hrd). split; [exact Hle|]. split; [exact Hfk|].
subst V.
destruct (Z.eq_dec (bv_unsigned (adenot E (SA kb kk))) (bv_unsigned (adenot E wa))) as [Heq|Hne].
+ assert (adenot E (SA kb kk) = adenot E wa) as Ea by (apply bv_eq; exact Heq).
rewrite Ea. apply (rdn_wbytes_hit segs (word_to_le_bytes 1 (edenot E v)) M (adenot E wa)).
rewrite length_N_to_le_bytes, Huw. lia.
+ rewrite rdn_wbytes_out; [exact Hrd | | |];
rewrite ?length_N_to_le_bytes, ?Huw; try lia.
all: pose proof (flat_u E _ _ Hfk) as Hku; rewrite ?Hku in *; destruct Hfk as (?&?&?&?); lia. }
apply expr_eqb_eq in Heqb.
destruct (Z.leb (kk + Z.of_nat w') (a_off wa) || Z.leb (a_off wa + Z.of_nat w) kk)%bool eqn:Hd;
injection Hp as <- <- <-.
+ apply Forall_one.
eapply (kentry_ok_frame E M wa w V _ (SA kb kk) (elen w') Hfw HK); [cbn; auto|].
rewrite elenZ_elen by exact Hkw. unfold estart. cbn [a_base a_off]. subst kb.
destruct wa as [wb wk]; cbn [a_base a_off] in *.
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
+
subst kb. destruct wa as [wb wk]; cbn [a_base a_off] in *.
eapply kword_cut_sound; [exact Hfw | exact HK | exact Hd].
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
then (if ranges_apart_x allkn (a_base wa) (a_off wa) (elen w) (ELit 0) lo (ELit (hi - lo))
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
#[using="Type"] Lemma know_ok_words_le8 : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "H'U0'aOyR0%211'>y8%511%311p051';'V7%211&\<vaDr3r2r1%544321&[H%114p031poF:1pV@>1pRFG1").
Proof.
intros E M kn H. induction kn as [|K r IH]; [exact I|].
apply Forall_cons_iff in H as [HK Hr].
destruct K as [a w' v| | | | | | | | |]; cbn [kn_words_le8]; auto.
cbn [kentry_ok] in HK. split; [exact (proj1 HK) | apply IH; exact Hr].
Qed.
#[using="Type"] Lemma prune_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "RI'U0'aOyR0%211'>y8%511%311p051';'V7%211'Y4'<'U9'6%711'Y=%911'I'A%12:3%2216&X>r:r8r7r6r5r4%76654321(@r3r2%34G@21r1%54?D21%B3?71&\<vaDr>r<r;%544321'Q0r9u8%3221&\:r@&]G%11K%433:1rAr=%A4@21:&\ArB%24C51Q0rC&\Dr?&SM%124G&R3&TL%127I%32=1%83751%O4N:1Hp0<1p0@1p0D1p0J1p0O1p0Q61pnNQL1pQS8QK1poHR31pnHQO1poFR51pQUJR31pQU<R51pQU@R71pV@R<1pl8R:1pVDR>1pl:R?1pRFRH1").
Proof.
intros E anyb M0 allkn M wa w wv kn. induction kn as [|K rest IH]; intros hints kn' scs hs' Hp Hall Hw8 Hfw Hkn Hscs.
- cbn in Hp. injection Hp as <- <- <-. constructor.
- cbn [prune] in Hp.
destruct (prune1 allkn wa w wv K hints) as [[kept scs1] hs1] eqn:Hp1.
destruct (prune allkn wa w wv rest hs1) as [[r scs2] hs2] eqn:Hpr.
injection Hp as <- <- <-.
apply Forall_cons_iff in Hkn as [HK Hrest].
apply scs_denot_app in Hscs as [Hs1 Hs2].
apply Forall_app. split.
+ eapply prune1_sound; eauto.
destruct K as [a w' v| | | | | | | | |]; try exact I. exact (proj1 HK).
+ eapply IH; eauto.
Qed.
#[using="Type"] Lemma carry_sound : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QO'U0'aOyR0%211'>y8%511%311p051';'Y:%211'V7%411'6%611'Y=%811'I'A%1273%2216&T;r6r5r4%43321(@r3r2%34A=21r1%54<A21%?3<71&\=r:r7%3221&\<vaDr;r9%443216&\Ar<%24651Er=&\>%1328=%;4:31=p051p091p0?1p0D1pnNQ71pQS8Q61poHQ;1pnHQ:1poFQ=1pQP:Q@1plJQD1pl:QE1pRFQN1").
Proof.
intros E anyb base log. induction log as [|[a w v] older IH]; intros kn hints kn' scs hs' Hc Hlf Hkn Hscs.
- cbn in Hc. injection Hc as <- <- <-. exact Hkn.
- cbn [carry] in Hc. cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf').
destruct (carry older kn hints) as [[kn1 scs1] hs1] eqn:Hco.
rewrite (prunepc_eq _ _ _ _ _ _ _ [] ltac:(constructor)) in Hc. rewrite prunep_eq in Hc.
destruct (prune (facts_of kn1) a w v kn1 hs1) as [[kn2 scs2] hs2] eqn:Hpr.
injection Hc as <- <- <-.
apply scs_denot_app in Hscs as [Hs1 Hs2].
cbn [mem_denot].
constructor.
+ cbn [kentry_ok]. split; [exact Hw8|]. split; [exact Hfa|].
pose proof (rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v)) (mem_denot E base older) (adenot E a)) as Hh.
rewrite length_N_to_le_bytes in Hh. apply Hh. rewrite (flat_u E _ _ Hfa).
destruct Hfa as (?&?&?&?). lia.
+ eapply prune_sound; eauto. eapply facts_of_ok. eauto.
Qed.
#[using="Type"] Lemma wbytes_nth : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QF';'aOy8%211%411yR0%511'>%115p031'<&]<&]8&b4r2%22:1&]G&:r4%22@1%411%9261&]I+2+R0%3221%?251&Q1r5%<2J1%32@1'I&\Dr6&aN%F2NAr3%E11%J231%52Q21%84<F71(3&Q5z%:2Q:1%34Q:9<1%52Q;1%@3Q771p0B1p0G1po6Q81pkNQ=1pQP<Q;1pm4QA1").
Proof.
induction bs as [|b rest IH]; intros m a j Hnw Hj; [cbn in Hj; lia|].
cbn [length] in Hnw, Hj. cbn [wbytes].
destruct j as [|j'].
- cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
destruct rest as [|b' rest'].
+ cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
+ cbn [length] in Hnw.
rewrite wbytes_below; [rewrite bv_eqb_refl; reflexivity | | ];
rewrite (u_add1 a) by lia; cbn [length]; lia.
- cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S j'))%Z with (bv_unsigned (a + 1) + Z.of_nat j')%Z by lia.
apply IH; lia.
Qed.
#[using="Type"] Lemma know_ok_fill_intro_pt : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QJ'U0'aOyR0%211'>y8%511%311pQUL51'Y4'U9'Q9&\:r5r3&\6r2%2241%63541'H&]<zr1%3221&]Ar7r4%<221%4261%:261'I&aN&]8&\8r8r6%3221%521E%72Q41%>11(3%:2Q4?%22Q41%=3Q441p0?1po0Q21&\;vaD(SA%13Q4GQ3%443I?1p061p0Q21pm8Q:1pQPJQ<1pkNQ>1pV@Q@1pRFQI1").
Proof. intros E M a n c Hfl Hc. cbn [kentry_ok]. auto. Qed.
#[using="Type"] Lemma know_ok_fill_intro : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QA'U0'aOyR0%211'>y8%511%311p051'Y4'<'U9'Q9&\:r6r4&]Gr3%211%63541'I&\6r7%2216%819%53=21&\;vaDr8&\D&SM%123A&Q6&aN%12MAr5%43N21%83?61(SA%13IHF%>4=<31p0@1p0G1pm8O1pQQ2Q11pQPJQ31pkNQ51pV@Q71pRFQ@1").
Proof.
intros E M a n ne c Hfl Hne. apply know_ok_fill_intro_pt; rewrite Hne; [exact Hfl|].
intros i Hi. pose proof (flat_u E _ _ Hfl) as Hu.
rewrite <- Hu. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite wbytes_nth; [| rewrite repeat_length, Hu; destruct Hfl as (?&?&?&?); lia | rewrite repeat_length; lia].
f_equal. apply nth_repeat_lt. lia.
Qed.
#[using="Type"] Lemma kentry_ok_frame_bytes : forall E M (wa : saddr) (bs : list byte) K (ka : saddr) (kl : expr),
flat E wa (Z.of_nat (length bs)) ->
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
| KFill a n _ => ka = a /\ kl = n
| KUnk a n => ka = a /\ kl = n
end ->
((estart E wa + Z.of_nat (length bs) <= estart E ka)%Z \/ (estart E ka + elenZ E kl <= estart E wa)%Z) ->
kentry_ok segs E (wbytes M (adenot E wa) bs) K.
Proof.
intros E M wa bs K ka kl Hfw HK Hshape Hdis.
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
assert (OUT : forall x : word,
(bv_unsigned x < estart E wa \/ estart E wa + Z.of_nat (length bs) <= bv_unsigned x)%Z -> wbytes M (adenot E wa) bs x = M x).
{ intros x Hx. apply wbytes_out; rewrite Huw; lia. }
assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
(bv_unsigned a + Z.of_nat k <= estart E wa \/ estart E wa + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
rdn segs (wbytes M (adenot E wa) bs) a k = rdn segs M a k).
{ intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply OUT. lia. }
destruct K as [[kb kk] w' v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] n fc|[kb kk] n]; cbn [kentry_ok] in *;
[ | | | | exact HK | exact HK
| destruct HK as [Hf0 Hs0]; split; [exact Hf0|]; intros d m Hd Hm;
eapply store_ok_mono; [apply wbytes_grows | apply Hs0; assumption]
| exact HK | | ].
6: { destruct Hshape as (-> & ->). destruct HK as [Hfk Hz]. split; [exact Hfk|].
intros i Hi. rewrite OUT; [apply Hz; exact Hi|]. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia. }
- destruct Hshape as (-> & -> & Hw8). destruct HK as (Hkw8 & Hfk & Hrd). split; [exact Hkw8|]. split; [exact Hfk|].
rewrite elenZ_elen in Hdis by exact Hw8.
rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfk); destruct Hfk as (?&?&?&?); lia | rewrite (flat_u E _ _ Hfk); lia].
- destruct Hshape as (-> & ->). destruct HK as [Hfk Hz]. split; [exact Hfk|].
intros i Hi. rewrite OUT; [apply Hz; exact Hi|]. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia.
- destruct Hshape as (-> & ->). destruct HK as (Hfk & Hlen & Hb). split; [exact Hfk|]. split; [exact Hlen|].
intros i Hi. rewrite OUT; [apply Hb; exact Hi|]. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia.
- destruct Hshape as (-> & -> & Hsz). destruct HK as (Hlo & Hhi & Hnone). split; [exact Hlo|]. split; [exact Hhi|].
intros i Hi. rewrite estart_lit0, elenZ_lit in Hdis.
assert ((hi - lo) mod 2 ^ 64 = hi - lo)%Z by (apply Z.mod_small; lia).
rewrite OUT; [apply Hnone; exact Hi|]. rewrite u_small by lia. lia.
- destruct Hshape as (-> & ->). destruct HK as [Hfk Hz]. split; [exact Hfk|].
intros i Hi. rewrite OUT; [apply Hz; exact Hi|]. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia.
Qed.
#[using="Type"] Lemma know_ok_unk_intro_pt : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QI'U0'aOyR0%211'>y8%511%311pQUL51'Y4'U9&\:r4r2&\6r1%2241%63541'Q9'H&]<z%2217&]Ar6r3%<221%42<1%9261&L'I&aN&]8&\8r7r5%3221%521H%72Q41%?11(0%11Q3%<3Q331%>11p0@1po0K1&\;vaD(SC%12Q5H%443J?1p061p0Q31pQPJQ;1pkNQ=1pV@Q?1pRFQH1").
Proof. intros E M a n Hfl H. cbn [kentry_ok]. auto. Qed.
#[using="Type"] Lemma know_ok_unk_intro : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q@'U0'aOyR0%211'>y8%511%311p051'Y4';%115'U9&\:r5r3&]G&:r2%22=1%411%83761'I'Q9&\6r6%2218%:2E<%<11%73631&\;vaDr7&\D&SM%123Er4%43<21(SC%12IH%:49831p0<1p0E1pQQ2O1pm4Q11pkNQ41pV@Q61pRFQ?1").
Proof.
intros E M a bs ne Hfl Hne. apply know_ok_unk_intro_pt; rewrite Hne; [exact Hfl|].
intros i Hi. pose proof (flat_u E _ _ Hfl) as Hu.
rewrite <- Hu. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite wbytes_nth; [discriminate | rewrite Hu; destruct Hfl as (?&?&?&?); lia | lia].
Qed.
#[using="Type"] Lemma kunk_of_zero : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "M'U0'aOyR0%211'>y8%511%311p051'Y4'U9&\;vaDr4r3(SEr2r1%3221%847651r5(SC%1286%<4;3:1p051pQPJ?1pkNA1pV@C1pRFL1").
Proof. intros E M a n [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (Hz i Hi). discriminate. Qed.
#[using="Type"] Lemma kunk_of_fill : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q0'U0'aOyR0%211'>y8%511%311p051'Y4'U9'Q9&\;vaDr5r4(SAr3r2r1%43321%948761r6(SC%1297%=4<3;1p051pm8@1pQPJB1pkND1pV@F1pRFO1").
Proof. intros E M a n c [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (Hz i Hi). discriminate. Qed.
#[using="Type"] Lemma kunk_of_blob : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q0'U0'aOyR0%211'>y8%511%311p051'Y4'U9'<&\;vaDr5r4(S@r3r2r1%43321%948761r6(SC%1297%=4<3;1p051po8@1pQPJB1pkND1pV@F1pRFO1").
Proof. intros E M a n k (Hfl & Hlen & Hz). split; [exact Hfl|]. intros i Hi. rewrite (Hz i Hi). discriminate. Qed.
#[using="Type"] Lemma kentry_ok_unk_grows : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q1'U0'aOyR0%211'>y8%511%311p051'Y4'U9&\Jr4r3%3221&\;vaDr6r5(SCr2%2281%746541r7%52<;%:49271p041p0=1pQPJB1pkND1pVBF1pV@G1pRFQ01").
Proof. intros E M M' a n Hg [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply Hg. apply Hz. exact Hi. Qed.
#[using="Type"] Lemma kentry_ok_unk_frame : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "Q4'U0'aOyR0%211'>y8%511%311p051';%114'Y4'U9&\;vaDr6r5(SCr2r1%3221%847651r7&\Dr4%23:91r3%:219%?4>631p081pQPJB1pkND1pm4F1pQU@N1pV@J1pRFQ31").
Proof. intros E M wa bs a n. apply kentry_ok_unk_grows. apply wbytes_grows. Qed.
#[using="Type"] Lemma kunk_store_ok : ltac2:(TCodec.tc2 tcn__AxSymExec3Sound "QG'U0'aOyR0%211'>y8%511%311p051'Y4'U9'Q9'<&\;vaDr6r5(SCr4r3%3221%847651&]<z%2215&]8&]G%118%32:1&\6r8%221?%:241'I'6&R2&aN&\8r9r7%3221%@21I%62Q81%84M=1I(C%<3;21p0>1p0G1p0K1pQP<Q51pmDQ71pQPJQ91pkNQ;1pV@Q=1pRFQF1").
Proof.
intros E M a n d m [Hfl Hz] Hd Hm. destruct Hfl as (F1 & F2 & F3 & F4).
destruct m as [|m']; [reflexivity|].
apply store_ok_of_all; rewrite u_small by lia; [lia|].
intros x Hx. unfold wview.
specialize (Hz (bv_unsigned x - estart E a)%Z ltac:(lia)).
replace (estart E a + (bv_unsigned x - estart E a))%Z with (bv_unsigned x) in Hz by lia.
rewrite Z_to_bv_bv_unsigned in Hz. destruct (M x); [discriminate | exfalso; exact (Hz eq_refl)].
Qed.
End CarrySound.
End FPX_2.
End AX2S.
