(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
StartupTac ArgvEnv RefLayout Js0Img Js0StartupDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Startup2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemSplit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StartupTac."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ZStores."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2not"]; ["3add"; "4le"; "4lt"; "5nth"; "5skipn"; "6Z"; "0D"; "0G"; "0J"; "0Jf"; "7Segment"; "8machine_state"; "8word_to_le_bytes"; "9entry_stack_image"; ":at_random_ptr"; ":build_stack_bytes"]; [":stack_to_mem"; ";sp_window_hi"; ";sp_window_lo"; "<bv_eqb"; "<bvmap"; "=cat_argv_ptr"; "=wbytes"; ">regs_agree"; "?D_libc"; "?J_aux"; "?after_last_slash"; "?envp_w"; "@cmem"; "@wfJ"; "Ac_eq"; "Agetr"]; ["Amkst"; "Ardn"; "Awrap_mem"; "Bauxv_words"; "Bcat_envp_ptr"; "Cbwd"; "Dzeros"; "Eloaded_segments"; "Ephdrs"; "FIn"; "Gadd"; "Gle"; "Glt"; "Gmul"; "Gof_nat"; "Gpow"]; ["Gsub"; "0a"; "0a'"; "0acc"; "0av"; "0b"; "0bs"; "0ev"; "0fx"; "0hw"; "0j"; "0k"; "0l2"; "0m"; "0n"; "0r"]; ["0rdraw"; "0regs"; "0regs'"; "0rom"; "0segs"; "0sp0"; "HBV"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0uid"; "0w"]]).
Abbreviation SEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Section FPX_1. Context {fx : PropExec.FPState}.
Section P3.
Variable sp0 : word.
Variables av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)) (only parsing).
Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).
Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
Local Notation s := (nth 0 av []) (only parsing).
Local Notation A8 := (Z_to_bv 64 0xe7ee0) (only parsing).
Lemma len_av : ltac2:(TCodec.tc2 tcn__Js0Startup2 "A'=&QK+1&QN&7'8'RHy8%211%411vR4%7221%911%<2;1+QP0%>231%@231").
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
Lemma len_ev : ltac2:(TCodec.tc2 tcn__Js0Startup2 "=&QK&QN&7'8'RHy8%211%411vR7%7221%911+X0%<221").
Proof. destruct Hve as [H1 _]. lia. Qed.
Lemma Hsp_lo' : ltac2:(TCodec.tc2 tcn__Js0Startup2 "7&QK&Q2&RIyR0vRE%3221%6251"). Proof. exact Hlo. Qed.
Lemma Hsp_hi' : ltac2:(TCodec.tc2 tcn__Js0Startup2 "7&QK&RIyR0vRE%3221&Q1%6221"). Proof. exact Hhi. Qed.
Lemma bsb_len : ltac2:(TCodec.tc2 tcn__Js0Startup2 "C&QK&QN&7'RHy8%211&O&QHvREvR4vR7vRJvR9vR@%877654321%=2:1%?11+RT[`0%B221").
Proof. exact (bsb_bound RPH sp0 av ev uid hw rdraw Hva Hve). Qed.
Lemma rd_above : ltac2:(TCodec.tc2 tcn__Js0Startup2 "R5'RHyR0%211';y8%511%311p051'E'9'8%116&QK&RIvRE%22>1r3%5221&QL&QJr4&QN%116%4231&QO+2+R0%3221%:251'>%K1C&QA&QG&Q0&M&QHvR4vR7vRJvR9vR@%776K54321%92L1&RGr5%22Q<1%?4>41J(2%12Q5Q0%D3C31&Q<&QB%17AQ6@?>=<r8r7%54Q9321r6%>2QH1%K4J31>%<2Q@Q7%O3N21p0<1p0Q21p0Q>1pT>QE1pTNQH1pT4QJ1pQ>QL1pQBQM1").
Proof.
intros J D a n bs Ha Hn H. pose proof (u64_range (Z_to_bv 64 a)).
rewrite rdn_cmem_above by (unorm; lia).
rewrite rdn_wrap_stack_above by (unorm; lia). exact H.
Qed.
Lemma rd_envp : ltac2:(TCodec.tc2 tcn__Js0Startup2 "R0'RHyR0%211';y8%511%311p051'9&Br1&7'8%118vR7%4221%7261'>%?15&QA&QG&Q<vRE&QB&QHvR4vRJvR9vR@%67574?321r4r3%;4:321&RG&QJ&RI%12Q3>+@%4221&QM+8&QN%O2MA%211%5241%;271r2%611%9281%?241%A2QA1u8%Q14Q0D21(2&L&QD%14Q2OQ::%3261%52Q=1%Q:3Q971p0Q<1pTHQE1pQ>QG1pQBQH1").
Proof.
intros J D k Hk. pose proof len_av. pose proof len_ev.
apply rd_above; [lia | lia |].
replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
exact (read_envp_ptr_k SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' k Hk).
Qed.
Lemma rd_envp_null : ltac2:(TCodec.tc2 tcn__Js0Startup2 "QI'RHyR0%211';y8%511%311p051'>'8%115%811&QA&QG&Q<vRE&QB&QHvR4vR7vRJvR9vR@%776854321r2r1%<4;321&RG&QJ&RI%12M?+@%4221&QM+8&QN&7%12KC%311%6251%<281%52OF%711%:291%@241%B2Q<1u8%Q34Q2E21(2&Lz%H2QB1%3261%52Q;1%Q>3Q;71pQ>Q@1pQBQA1").
Proof.
intros J D. pose proof len_av. pose proof len_ev.
apply rd_above; [lia | lia |].
replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
with (sp0 + nat_to_word (envp_off av + 8 * length ev))
by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
exact (read_envp_null SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi').
Qed.
Lemma rd_auxv : ltac2:(TCodec.tc2 tcn__Js0Startup2 "R>'RHyR0%211';y8%511%311p051'9&Br2uD%3221'>&Cr3&QC&QH&NvREvR4vR7%43321vRJvR9%948321&RGz%22K1%?4K>41%A3L1D'8%11K%N11&QA&QG&Q<&QBvR@%27FDCB@?1r6r5%64G321&QJ&RI%12Q<J+H%4221&QM+8&QN&7%12DQ0%311%6251%<281%52HQ3%711%:291%@241r4%;11%>2=1%D241%Q62QO1u8%Q04OH21(2&L%124QF%32Q61%QJ3Q651p0Q:1p0QM1pUHR81pTFR31pQ>R51pQBR61").
Proof.
intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
apply rd_above; [lia | lia |].
replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
rewrite <- Hw. exact (read_auxv_word SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' j Hj).
Qed.
Section SE.
Local Abbreviation SEC_T_envp_loop := (ltac2:(TCodec.tc2 tcn__Js0Startup2 "SL'K!p021&QE&QGr1%3221'9&Q4y5'RHyR0%211%5241';y8%611%311p061'>&@r5r6%3221&7'8%11:vR7%4221%:3F61&Q?(RF+9(<%33I21%52>1&RG&QJ&RIvRE%22M1+@%5221&QM+8&QNvR4%G2E1%311%6251%=281%61M%9281%@231%B2Q;1%Q43Q;D1%J2QCF%<1M%?2>1%F291%G21@%I2QB1%Q;3QB61r2+:%Q23QH1Q0%Q4231z%Q02QI1%QB3QI31&Q7%QM1QN&QI(5(:%114%335;1%436Q;1%637R91qU081r9r3%<3321r>&Q@vR8r4+cP]<%QI3R=1QG/01R=&Q<&QB&QHvRJvR9vR@%574QIQBR5321r8%84QK2B1r7%@5?>;21%B11p0D1p0Q21p0Q:1pU6RL1r;+cP]0%R=3S11R;/01S1%D4R7>RHRI%K5J<21I%611p081p0QK1p0RF1pU8S21pQ>S31pQBS41pU4S:1pTHSA1pTNSB1p0SD1pQ@SI1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_envp_loop) 0%nat 0%nat).
Lemma envp_loop : ltac:(sec_stmt2 constr:(SEC_T_envp_loop) 1%nat 0%nat).
Proof.
intros HG.
pose proof len_av as Hlen. pose proof len_ev as Hlev.
induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
-
assert (k = length ev) by lia. subst k.
eapply HG.
{ ld_step (ltac:(oF' 0x981a0%Z)) (ltac:(oD' 0x981a0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981a4%Z)) (ltac:(oD' 0x981a4%Z)) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
stepb_ft (ltac:(oF' 0x981a8%Z)) (ltac:(oD' 0x981a8%Z)) ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
- assert (Hk : (k < length ev)%nat) by lia.
pose proof (cat_envp_ptr_nz RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' k Hk) as Hnz.
eapply HG.
{ ld_step (ltac:(oF' 0x981a0%Z)) (ltac:(oD' 0x981a0%Z)) (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981a4%Z)) (ltac:(oD' 0x981a4%Z)) (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
stepb_tk (ltac:(oF' 0x981a8%Z)) (ltac:(oD' 0x981a8%Z)) ltac:(pin; apply c_eq_0_false; exact Hnz).
apply mst_refl. }
eapply (IH (S k)); [lia | gres; reflexivity |].
intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
Qed.
End SE.
Lemma pn_bounds : ltac2:(TCodec.tc2 tcn__Js0Startup2 "Q5'=&QK&RIyR0vRE%3221&Q5vR4vR7(1%446321%9281%;271&QL&QJ&QN&7'RHy8%211&C'8%113(:%115%543@B1%:271%<11%>2A1+1%@221&QO+2+R0%3221%F251%Q42H1").
Proof.
pose proof len_av.
exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hsp_hi' 0 ltac:(lia)).
Qed.
Lemma rd_argv0_byte : ltac2:(TCodec.tc2 tcn__Js0Startup2 "R6'RHyR0%211';y8%511%311p051'9'Ar2&7&C'8%119(1vR4(:%11=%745431%92?1%<2;1'>r3&3(5&RGz%22H1%43H1;%63I;1%C4J813%:3K1F%N1C&QA&QG&Q<vRE&QB&QHvR7vRJvR9vR@%6757L4321r6r5%;4:321&QJ&RI&Q5%14>Q3;Q4%32QC1&QNr4%211%8241%O2QH1u1%I4H<21(2%Q43QHQ6Q;%22Q@1%Q93N41p0Q01p0Q<1pT<QM1pTFQK1pQ>QM1pQBQN1").
Proof.
intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
apply rd_above; [lia | lia |].
replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
by (rewrite word_add_nat; reflexivity).
rewrite <- Hb.
exact (read_argv_byte_k RPH SEGS sp0 av ev 0 j uid hw rdraw ltac:(lia) Hj
(bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve Hsp_hi')).
Qed.
Lemma rdn_addr : ltac2:(TCodec.tc2 tcn__Js0Startup2 "Q5'8'J%211'RHyR0%211';y8%511%311p051'9%<14%711'>&QAr6r5r3r2%544321r1%83921r4%:3C71r8r7%<421;4%>3?1:p051p081pU0B1pTNE1pT6L1pT4M1pTLI1pU:Q21").
Proof. intros; subst; reflexivity. Qed.
Lemma c_eq_byte47 : ltac2:(TCodec.tc2 tcn__Js0Startup2 "D'RHy8%211'>'4&Q>&RGyR0&RIr1%2291%5241+Q?%7261%9231&Q3%:2?4%23@81%?3>41pT<A1").
Proof.
intros b. pose proof (u8_range b). unfold c_eq, bv_eqb.
rewrite !u_Z2bv by lia. reflexivity.
Qed.
Lemma c_eq_byte0 : ltac2:(TCodec.tc2 tcn__Js0Startup2 "H'RHy8%211&?'>r1&RGz%2271%53741%711'4&Q>yR0&RIr2%22?1%;241%<25;%7221(6%A3:21p0<1pT<E1").
Proof.
intros b Hb. pose proof (u8_range b). apply c_eq_0_false. rewrite u_Z2bv by lia.
intro Hz. apply Hb. apply bv_eq. rewrite Hz. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_prog_loop := (ltac2:(TCodec.tc2 tcn__Js0Startup2 "TK'K!p021&QE&QGr1%3221'8'RHy8%211%411'9&Q4y5yR0%811%4231';%119p041'>&Dr6&C(1vR4(:%11B%54B431%83D71r7%;3E21'A&7%12I6%3251r8%5271&Q?(RF+:(<%33M21%52=1&RG+log0%22Q01%K3Q041+;%:3Q418%<2>1&QJ&RI&Q5vREvR7%342O1Q0%52Q;1&QNr:%211%:241+1%<221%D2QB1%Q=3QB?1r9+<%M3QG1K%O231+Q?%K2QI1%QD3QI31%Q32R5H%@1Q8%H2B1%I21>%Q12QO1%QJ3QO51&Q7%R91R3&QI(5+=%Q=3R71Q;%QK15%43621%537Q61%738RD1qU091r<r2%=3321rB&Q@vR8r3+cPc@%QK3RD1QI/01RD&Q<&QB&QHvRJvR9vR@%574QDRAQC321&Q6r;&Lu8&Q:r@r?r>%43321%QJ11%R22QL1%R:2S81%:291%=3<R:1%E4R3?O1%L5KJG1QO%N11p0Q01p0Q?1pU6S>1+cPc4%RI3SB1RG/01SB%R81Q8%R@2R:1%RH2SF1%H2G1%K3R4RH1%Q34RAMR<1%Q:5Q9L71S4%I11p0<1p0R31p0R;1p0RN1p0S91p0S<1p0SA1pU8SN1pQ>SO1pQBT01pU4T41pT8T:1pTFT;1pTJT=1p0TC1pQ@TH1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_prog_loop) 0%nat 0%nat).
Lemma prog_loop : ltac:(sec_stmt2 constr:(SEC_T_prog_loop) 1%nat 0%nat).
Proof.
intros HG.
pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
-
assert (Hjl : j = length s).
{ pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
eapply HG.
{ lb_step (ltac:(oF' 0x98264%Z)) (ltac:(oD' 0x98264%Z)) (Z_to_bv 8 0)
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
stepb_ft (ltac:(oF' 0x98268%Z)) (ltac:(oD' 0x98268%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x9826c%Z)) (ltac:(oD' 0x9826c%Z)) ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk0; [gres; pin; f_equal; lia | solve_regs_agree].
- assert (Hjlt : (j < length s)%nat).
{ pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
assert (Hb : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b).
{ rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
assert (Hbnz : b <> Z_to_bv 8 0).
{ intros Hb0. apply Hnz. rewrite <- Hb0, <- Hb, app_nth1 by lia. apply nth_In. lia. }
assert (Hskip' : skipn (S j) s = l2).
{ replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
cbn [after_last_slash] in Hk0.
destruct (bv_eqb b (Z_to_bv 8 47)) eqn:Eb.
+
eapply HG.
{ lb_step (ltac:(oF' 0x98264%Z)) (ltac:(oD' 0x98264%Z)) b
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
stepb_tk (ltac:(oF' 0x98268%Z)) (ltac:(oD' 0x98268%Z)) ltac:(pin; rewrite c_eq_byte47; exact Eb).
stw (ltac:(oF' 0x9825c%Z)) (ltac:(oD' 0x9825c%Z)) (Z_to_bv 64 0xe7ee0) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data).
rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
sv (ltac:(oF' 0x98260%Z)) (ltac:(oD' 0x98260%Z)) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
apply mst_refl. }
replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
intros regs' H11' Hag. apply Hk0; [exact H11'|].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
+ eapply HG.
{ lb_step (ltac:(oF' 0x98264%Z)) (ltac:(oD' 0x98264%Z)) b
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
stepb_ft (ltac:(oF' 0x98268%Z)) (ltac:(oD' 0x98268%Z)) ltac:(pin; rewrite c_eq_byte47; exact Eb).
stepb_tk (ltac:(oF' 0x9826c%Z)) (ltac:(oD' 0x9826c%Z)) ltac:(pin; apply c_eq_byte0; exact Hbnz).
sv (ltac:(oF' 0x98260%Z)) (ltac:(oD' 0x98260%Z)) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
apply mst_refl. }
eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
intros regs' H11' Hag. apply Hk0; [exact H11'|].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
Qed.
End SE.
Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].
Section SE.
Local Abbreviation SEC_T_p3_run := (ltac2:(TCodec.tc2 tcn__Js0Startup2 "TN'K!p021&QE&QGr1%3221&Q4y5'RHyR0%211%5241';y8%611%311p061&Q=vREr2%3221'>&Q?r4(RF+2(<%33D21%6251&RG&R0&RI%12G>+]0%4221%62J1%?3J81r5+8%?3Q01=%B231&Q5vR4vR7(1%44K321%I3Q461r6+9%I3Q:1G%L231&Q;%12Q2:%Q03Q;31r7+:%Q03QA1N%Q3231+[@%M2K1%O2QC1%Q83QC41+1%Q73QH1Q5%Q:2QL1+cPcH%Q52QI1%Q>3QI31%Q>2QAQ9%Q@3QK1Q2r3%QA21?%QC3QN1<+B%QB3R31Q@%QE2QD1+log@%Q@2R41%QI3R431&Q7%R81R9&QI(5+;%QL3R=1QJ+<%QN3R?1QL+=%R03RA1QN(:%11:%93;A1%:3<41%;3=71%<3>:1%=3?Q71%>3@Q?1%?3AQ21%A3BRN1qU0C1r=%F321R0r@&Q@vR8+cQT8%RB3S11R@/01S1&Q<&QB&QHvRJvR9vR@%574S0R8R7321&Q9%16S2R:R954@&Q8%14S4R<R;6%;4S5531r<%B5AR:>21%D11p0F1p0Q>1p0QE1p0QI1p0QL1pU6SE1r;r9+cP\D%S<3SK1S:/01SK&Q6r8&QFuY@%211%534R?1(0%11SOq0T41%Q34SMM41%Q95Q8>;1RJ%@11p0B1p0RF1p0RO1p0S71p0SB1p0T31pU8T81pQDT91pU4T?1p0TF1pQ@TK1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_p3_run) 0%nat 0%nat).
Lemma p3_run : ltac:(sec_stmt2 constr:(SEC_T_p3_run) 1%nat 0%nat).
Proof.
intros HG regs Jf rom HJ H2 H8 H9 H10 Hk.
pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
unfold envp_w in H9.
eapply HG.
{ sn (ltac:(oF' 0x98194%Z)) (ltac:(oD' 0x98194%Z)).
ld_step (ltac:(oF' 0x98198%Z)) (ltac:(oD' 0x98198%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xc7b90)) (Z_to_bv 64 0xc7b90)
ltac:(rd_img img_b4ea0_8) ltac:(apply bytes_le_to_Z_8).
stw (ltac:(oF' 0x9819c%Z)) (ltac:(oD' 0x9819c%Z)) (Z_to_bv 64 0xc7b90) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
apply mst_refl. }
eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
intros regs1 H9a H10a Hag1.
carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
clear H9 H10 H8 H2.
eapply HG.
{ sn (ltac:(oF' 0x981ac%Z)) (ltac:(oD' 0x981ac%Z)).
sn (ltac:(oF' 0x981b0%Z)) (ltac:(oD' 0x981b0%Z)).
stw (ltac:(oF' 0x981b4%Z)) (ltac:(oD' 0x981b4%Z)) (Z_to_bv 64 0xe7ef8)
(Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
ld_step (ltac:(oF' 0x981b8%Z)) (ltac:(oD' 0x981b8%Z)) (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x981bc%Z)) (ltac:(oD' 0x981bc%Z)) ltac:(pin; cond_compute).
sv (ltac:(oF' 0x981c0%Z)) (ltac:(oD' 0x981c0%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
sn (ltac:(oF' 0x981c4%Z)) (ltac:(oD' 0x981c4%Z)).
sv (ltac:(oF' 0x981c8%Z)) (ltac:(oD' 0x981c8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 368)).
sn (ltac:(oF' 0x981cc%Z)) (ltac:(oD' 0x981cc%Z)).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 344)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
stepb_ft (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 336)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
stepb_ft (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 328)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
stepb_ft (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 hw) hw ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 240)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
stepb_ft (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 320)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
stepb_ft (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 uid) uid ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 280)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
stepb_ft (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 uid) uid ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 272)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
stepb_ft (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 184)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
stepb_ft (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x981dc%Z)) (ltac:(oD' 0x981dc%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981e0%Z)) (ltac:(oD' 0x981e0%Z)) (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x981e4%Z)) (ltac:(oD' 0x981e4%Z)).
sv (ltac:(oF' 0x981e8%Z)) (ltac:(oD' 0x981e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 168)).
stw (ltac:(oF' 0x981ec%Z)) (ltac:(oD' 0x981ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ).
sn (ltac:(oF' 0x981f0%Z)) (ltac:(oD' 0x981f0%Z)).
ld_step (ltac:(oF' 0x981d0%Z)) (ltac:(oD' 0x981d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x981d4%Z)) (ltac:(oD' 0x981d4%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
stepb_tk (ltac:(oF' 0x981d8%Z)) (ltac:(oD' 0x981d8%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x981f4%Z)) (ltac:(oD' 0x981f4%Z)) (word_to_le_bytes 8 hw) hw
ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x981f8%Z)) (ltac:(oD' 0x981f8%Z)) (zeros 8) (Z_to_bv 64 0)
ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
ltac:(reflexivity).
sn (ltac:(oF' 0x981fc%Z)) (ltac:(oD' 0x981fc%Z)).
stw (ltac:(oF' 0x98200%Z)) (ltac:(oD' 0x98200%Z)) (Z_to_bv 64 0xe7f58) hw ltac:(ok_data).
stepb_tk (ltac:(oF' 0x98204%Z)) (ltac:(oD' 0x98204%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x9821c%Z)) (ltac:(oD' 0x9821c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stw (ltac:(oF' 0x98220%Z)) (ltac:(oD' 0x98220%Z)) (Z_to_bv 64 0xe7f20) (Z_to_bv 64 4096) ltac:(ok_data).
stepb_tk (ltac:(oF' 0x98224%Z)) (ltac:(oD' 0x98224%Z)) ltac:(pin; apply c_eq_0_false; lia).
stepb_tk (ltac:(oF' 0x9822c%Z)) (ltac:(oD' 0x9822c%Z)) ltac:(pin; apply c_eq_0_false; lia).
sn (ltac:(oF' 0x98238%Z)) (ltac:(oD' 0x98238%Z)).
ld_step (ltac:(oF' 0x9823c%Z)) (ltac:(oD' 0x9823c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7ee8)) (Z_to_bv 64 0xe7ee8)
ltac:(rd_img img_b4ea8_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x98240%Z)) (ltac:(oD' 0x98240%Z)).
ld_step (ltac:(oF' 0x98244%Z)) (ltac:(oD' 0x98244%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0xe7ee0)) (Z_to_bv 64 0xe7ee0)
ltac:(rd_img img_b4eb0_8) ltac:(apply bytes_le_to_Z_8).
stw (ltac:(oF' 0x98248%Z)) (ltac:(oD' 0x98248%Z)) (Z_to_bv 64 0xe7ee8) (cat_argv_ptr sp0 av ev 0) ltac:(ok_data).
sv (ltac:(oF' 0x9824c%Z)) (ltac:(oD' 0x9824c%Z)) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).
stw (ltac:(oF' 0x98250%Z)) (ltac:(oD' 0x98250%Z)) (Z_to_bv 64 0xe7ee0) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
sn (ltac:(oF' 0x98254%Z)) (ltac:(oD' 0x98254%Z)).
sn (ltac:(oF' 0x98258%Z)) (ltac:(oD' 0x98258%Z)).
apply mst_refl. }
eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
intros regs2 H11b Hag2.
carry Hag2 H2a (2 : reg) H2b.
eapply HG.
{ sv (ltac:(oF' 0x98270%Z)) (ltac:(oD' 0x98270%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 368)).
sn (ltac:(oF' 0x98274%Z)) (ltac:(oD' 0x98274%Z)).
apply mst_refl. }
apply Hk.
- gres; bveq.
- gres; exact H2b.
- gres; reflexivity.
- gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
- ra_chain.
Qed.
End SE.
End P3.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
