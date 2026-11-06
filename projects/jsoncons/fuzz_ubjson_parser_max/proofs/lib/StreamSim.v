(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim CatSim WallSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__StreamSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim.Loop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.WallSim."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"]; ["2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3le"; "4map"; "5N"; "5Z"; "6equiv"; "6modeled"; "7omni_strong_equiv"; "8len_word"; "8word_to_nat"; "9check_read"]; [":CheckOk"; ":check_result"; ";Fs"; "<PhdrInfo"; "<Segment"; "<mkImage"; "=Ok"; "=Unmodeled"; "=outcome"; ">coexec"; ">never_errors"; ">omni_corun"; ">omni_cosafe"; "?machine_state"; "?ms_gpr"; "?ms_svc_pending"]; ["?ms_writable_byte"; "?set_gpr0"; "@SError"; "@SNext"; "@advance_past_svc"; "@apply_effect"; "@config"; "@init_config"; "@init_machine_state"; "@is_prefix"; "@mkCfg"; "@mkEntry"; "@obs_trace"; "@reaches_error"; "@run"; "@sstep"]; ["@star"; "@step_to"; "@sys_input"; "Asyscall_spec"; "BEntryDraw"; "CFdChannel"; "CFdEntry"; "CIEof"; "CInputStream"; "CMemCopy"; "CModel"; "CProcInput"; "CReadEv"; "CSyscallEffect"; "CWriteEv"; "Caccess_okb"]; ["Cevent"; "Cfd_lookup"; "Cin_arg"; "Cin_argv"; "Cin_envp"; "Cin_fs"; "Cin_hwcap"; "Cin_stdin"; "Cin_uid"; "Cin_wmem"; "Cinit_model"; "Cm_fds"; "Cm_fs"; "Cm_halted"; "Cm_stdin"; "Cm_vm_lazy"]; ["CmkEffectU"; "Cread_bytes_aux"; "Cread_bytes_map"; "Crw_count_clamp"; "Cstream_take"; "Cstream_take_z"; "Cwith_stdin"; "Dread_spec"; "Efd32"; "Frw_bytes_max"; "Gbuf_modeled"; "Gfd1chan"; "Gmsteps"; "IReadPend"; "IWrPend"; "Ilh_next"]; ["Isinv"; "Ito_rd"; "Ito_wr"; "HM_loop"; "Hchunks"; "Heof_tail"; "Hiter_ev"; "Hstream_traces"; "Hstream_traces_ch"; "Hto_rd"; "Hwseg_ok"; "Jto_wall_tail"; "Kflat_map"; "Lle"; "Llt"; "Lof_nat"]; ["0a"; "0aLH"; "0abrk"; "0alim"; "0amb"; "0apc"; "0aph"; "0arnd"; "0asp"; "0blocks"; "0brk0"; "0bs"; "0buf"; "0c"; "0c'"; "0c0"]; ["0cnt"; "0eff"; "0evs"; "0fs"; "0inp"; "0k"; "0l1"; "0l2"; "0len"; "0lim"; "0m"; "0mb"; "0model"; "0model'"; "0ms"; "0ms'"]; ["0msR"; "0msW"; "0n"; "0o"; "0pc"; "0ph"; "0rLH"; "0rbrk"; "0rch"; "0reserved"; "0rlim"; "0rmb"; "0rnd"; "0rpc"; "0rph"; "0rrnd"]; ["0rsp"; "0s"; "0s'"; "0s1"; "0s2"; "0segs"; "0source_segs"; "0sp"; "0st"; "MZ_to_bv"; "Mbv"; "Mbv_and"; "Mbv_unsigned"; "0target_segs"; "0tr"; "0tr'"]; ["0w"; "0w1"; "0wn"; "0x"; "0x8"]]).
Lemma in_arg1_sys_input : ltac2:(TCodec.tc2 tcn__StreamSim "F'8'Q4%211'Q='UJyR0%211'A&RB&R2r3r2r1%43321u1%7221&Q>%1263%;3<31p\:=1pYNA1p[<C1").
Proof. reflexivity. Qed.
Lemma syscall_spec_read : ltac2:(TCodec.tc2 tcn__StreamSim "Q='8'Q4%211'Q='UJyR0%211'R:'Q8'R=%211'A'I&ULr3%22:1+QO%63521&C&R3&R2r6r5r4%43321r2%732<1&S7&S8&Q>(1%2291%411u1%52<1u2%72>1%:6531=G<%D2<1p0F1pZ8N1pYJQ21p\:Q41pYNQ81p[<Q:1").
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
change (in_sysno (sys_input segs ms x8)) with x8.
rewrite Hno. reflexivity.
Qed.
Lemma in_arg2_sys_input : ltac2:(TCodec.tc2 tcn__StreamSim "F'8'Q4%211'Q='UJyR0%211'A&RB&R2r3r2r1%43321u2%7221&Q>%1263%;3<31p\:=1pYNA1p[<C1").
Proof. reflexivity. Qed.
Lemma in_wmem_sys_input : ltac2:(TCodec.tc2 tcn__StreamSim "J'8'Q4%211'Q='UJyR0%211'A';y8%611%311p061&RI&R2r3r2r1%43321%611&Q@%1265%?3:31p\:A1pYNE1p[<G1").
Proof. reflexivity. Qed.
Lemma band0_255 : ltac2:(TCodec.tc2 tcn__StreamSim "<'A'UJyR0%211&UK&UIz%2251+WO%4271%63831%;3814").
Proof.
apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.
Lemma m_fs_with_stdin : ltac2:(TCodec.tc2 tcn__StreamSim ">'R8'R:'A&Q2&RL&S6r2r1%3221%511%613%93821pYF;1p[4=1").
Proof. reflexivity. Qed.
Lemma m_halted_with_stdin : ltac2:(TCodec.tc2 tcn__StreamSim "B'R8'R:'A';'UJyR0%211%411&RM&S6r2r1%3221%511%613%=3821pYF?1p[4A1").
Proof. reflexivity. Qed.
Lemma m_fds_with_stdin : ltac2:(TCodec.tc2 tcn__StreamSim "E'R8'R:'A'8'='UJyR0%211'R6%5221%711&RK&S6r2r1%3221%511%613%@3821pYFB1p[4D1").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_stdin : ltac2:(TCodec.tc2 tcn__StreamSim "D'R8'R:'A'8'='UJyR0%211%4211%611&RO&S6r2r1%3221%511%613%?3821pYFA1p[4C1").
Proof. reflexivity. Qed.
Definition M_loop (model : Model) : Prop :=
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
m_halted model = None /\
m_vm_lazy model = [].
Lemma init_M_loop : ltac2:(TCodec.tc2 tcn__StreamSim "I'8'='UJyR0%211%4211%611'I'R;&SC&RJr6r5r4r3r2r1%76654321%911pY:;1pYD=1p[@A1pYHB1pXFC1pZDB1").
Proof. intros reserved brk0 mb sp lim inp. repeat split. Qed.
Lemma M_loop_take : ltac2:(TCodec.tc2 tcn__StreamSim "I'9'R:&SCr1%211&S6&>'8'UJy8%211%411'R8&S4&RNr2%211r3%5221%=3871%?215%C11p0B1pYJF1pY<H1").
Proof. intros k model (H0 & H1 & Hh & Hlazy). repeat split; assumption. Qed.
Lemma M_loop_fd1chan : ltac2:(TCodec.tc2 tcn__StreamSim "9'R:&SCr1%211&S;r2%211p041pYJ81").
Proof. intros model (H0 & H1 & Hh & Hlazy). exact H1. Qed.
Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
match n with
| O => true
| S n' =>
match find_segment segs (bv_unsigned a) 1 with
| Some seg =>
(seg_writable seg
&& match segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
| Some _ => true
| None => false
end
&& wseg_ok segs (a + 1) n')%bool
| None => false
end
end.
Lemma wseg_ok_read_aux : ltac2:(TCodec.tc2 tcn__StreamSim "Q8'8'Q4%211'9'UJyR0%211'Q='A'4&SJr4r2r3%43321(?%83721'By8%?11%D11';%112&S1&Q@r6%221=r5%532A1(2r1%22;1%H3:41q\2=1%A2>1p0C1pYNM1pX2O1pZ6Q31p[<Q51").
Proof.
intros segs n; induction n as [|n IH]; intros a ms H.
- exists []. reflexivity.
- cbn [wseg_ok] in H.
destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
apply andb_true_iff in H as [H Hrec].
apply andb_true_iff in H as [Hwr Hbyte].
destruct (segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
[|discriminate].
destruct (IH (a + 1) ms Hrec) as [w Hw].
cbn [read_bytes_aux].
assert (Hdef : exists b0, ms_writable_byte segs ms a = Some b0).
{ unfold ms_writable_byte, wview. destruct (ms_mem ms a) as [b'|].
- eexists; reflexivity.
- rewrite Hseg, Hwr, Hb. eexists; reflexivity. }
destruct Hdef as [b0 Hb0]. rewrite Hb0, Hw. eexists; reflexivity.
Qed.
Lemma wseg_ok_wdef : ltac2:(TCodec.tc2 tcn__StreamSim "Q9'8'Q4%211'UJyR0%211'Q='A'4&SJr4r3&Nr2%211%63541(?%:3921'By8%A11%E11';%112&S2&Q@r6%221@r5%5321C(2r1%22;1%J3:41q\2=1%A2>1p0C1pYNO1pYBQ11pX2Q21p[<Q61").
Proof.
intros segs a len ms H. rewrite read_bytes_map_eq.
apply wseg_ok_read_aux. exact H.
Qed.
Lemma read0_wmem1 : ltac2:(TCodec.tc2 tcn__StreamSim "QJ'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q=y8%C11%611'A';%113&S2&Q@r4r3%3221&Q>u1%2241r6%93521(2%12?L%?3=31'B&RI&R2r5%2391?%411%>23=&UI+1%22Q=1%G3541%K3I1=q\4M1%=2N1p0?1p\2Q01p\:QC1pYNQ51p[<Q71p0Q;1pY2QG1").
Proof.
intros cnt Hcnt segs ms x8 w Hw. rewrite in_wmem_sys_input.
eexists. apply (read_bytes_map_prefix _ _ cnt (Z_to_bv 64 1) w);
[rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; lia | exact Hw].
Qed.
Lemma read0_wmem_need : ltac2:(TCodec.tc2 tcn__StreamSim "R5'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q=y8%C11%611'R8'A';%114&S2&Q@r5r4%3221&Q>u1%2241r7%93521(2r2%22A1%@3>41'B&RI&R2r6%23:1@%411%?23>&M&6&S5r3&S3r9%211%5241%73Q2Q11%92Q41%O3<;1%F2Q5QB%Q43Q221q\6Q71%E2Q81p0G1p[4Q91p\2Q;1p\:QN1pYNQ@1p[<QB1p0QF1pY2R21").
Proof.
intros cnt Hcnt segs ms x8 w s Hw. rewrite in_wmem_sys_input.
eexists. apply (read_bytes_map_prefix _ _ cnt _ w); [|exact Hw].
rewrite stream_take_z_eq.
pose proof (stream_take_length (Z.to_nat (rw_count_clamp cnt)) s) as Hlen.
pose proof (rw_count_clamp_range cnt) as Hcl.
unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap_small;
unfold bv_modulus, MAX_RW_COUNT in *; cbn [Z.of_N] in *;
[ | pose proof (bv_unsigned_in_range 64 cnt) ]; unfold rw_count_clamp in *; lia.
Qed.
Lemma read0_check_eof : ltac2:(TCodec.tc2 tcn__StreamSim "SI'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q='R:y8%D11%711'A'Ir3%C2H1+QO%53421';'R6%211&RA&RK%119&UI%12Q2N%5231(2(R5%114%32;1%C3;51'R8&RNr4%211(R7%I3521&Q>r7(1%3221%N3QB1Ar8u2%7221r;%Q33QG21%N1Q5&S2&Q@r:r9%3221u1%A231r<%83421r6%Q02Q@1%Q@3<31'4&R?%I2<9r=%R52R:1%4231(?%QH3721'Q1&O&R2%13@JE&S8%Q42LQ2%211%Q62NF%Q72OQ1(S0(:'=%12RIR6%311%32RKRK%511'R9%711'9%82S01%:11%<6R186641%E6C@?>1Q7(Q0'R@%?11%32Q;1%RD3K51p0M1p0Q61p0QD1p0QJ1p0R01p0R71p0RF1p\2RM1pYJS11p\:SB1pYNS41p[<S61p0S:1pY2SF1").
Proof.
intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
unfold check_read.
rewrite Hg0; norm_fd32; rewrite Hfd.
cbv beta iota.
change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
rewrite Hg2, Haok.
cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
rewrite Heof. cbv beta iota.
unfold check_ret_only. rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma read0_check_bytes : ltac2:(TCodec.tc2 tcn__StreamSim "TK'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q='R:y8%D11%711'A'Ir4%C2H1+QO%53421';'R6%211&RA&RK%119&UI%12Q2N%5231(2(R5%114%32;1%C3;51&Q>r7(1%3221%H3Q<1;r8u2%7221r;%M3QA21%H1O&S2&Q@r:r9%3221u1%A231r<%83421r6%J2Q:1%Q:3<31'4&R?%I2<9r=%QO2R41%4231(?%QB3721+1&SO&7%12QHQ1%311%R4251%42QKQ0%611r?%R<2RA1%R9231&6'R8&S4&RN%11Q6%>2R5Q1%4221%73R661%R63R71Q4'Q1&O&R2r>%23@1M&S8%QI23QG%211%QK25Q;%QL26QF(S0&M%12REQB(5'=%12S:RG(<%14S<RI9QG(:%114%73531%72S@S@%411'R9%611'9%<2SE1%911%B6@86641%L6IFED1QN(Q0&S6&>%Q71R2%QD2S;R8%Q:221%43S<Q<1%621R6&G'R@(R<%11S3%44SC31R@%=261%SC3Q<?1p0Q>1p0QH1p0QN1p0R51p0R>1p0RL1p0S21p0S81p0SG1pXHSN1p\2SO1pYJT31p\:TD1pYNT61p[<T81p0T<1pY2TH1").
Proof.
intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
unfold check_read.
rewrite Hg0; norm_fd32; rewrite Hfd.
cbv beta iota.
change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
rewrite Hg2, Haok.
cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
destruct (m_stdin model) as [|b0 s0] eqn:Hs.
{ exfalso. rewrite stream_take_nil_of_eof in Hpre. subst bs. cbn in Hlo. lia. }
cbv beta iota.
rewrite Hw1. cbv beta iota.
rewrite Hwn. cbv beta iota.
rewrite !bv_eqb_refl.
rewrite (proj2 (Z.leb_le 1 (Z.of_nat (length bs))) Hlo).
rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)).
rewrite (proj2 (Z.leb_le (Z.of_nat (length bs)) (bv_unsigned cnt)) Hhi).
rewrite (proj2 (listN_eqb_eq _ _) Hpre).
rewrite <- (in_wmem_sys_input segs ms x8) in Hw.
assert (Hlek : (bv_unsigned (len_word bs) <= bv_unsigned cnt)%Z).
{ unfold len_word. pose proof (bv_unsigned_in_range 64 cnt) as Hr.
rewrite Z_to_bv_unsigned, bv_wrap_small; [exact Hhi | lia]. }
rewrite (wmem_ok_of_full _ _ _ _ _ Hw Hlek).
reflexivity.
Qed.
Lemma read0_ok_eof : ltac2:(TCodec.tc2 tcn__StreamSim "SC'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q='R:y8%D11%711'A'Ir3%C2H1+QO%53421';'R6%211&RA&RK%119&UI%12Q2N%5231(2(R5%114%32;1%C3;51'R8&RNr4%211(R7%I3521&Q>r7(1%3221%N3QB1Ar8u2%7221r;%Q33QG21%N1Q5&S2&Q@r:r9%3221u1%A231r<%83421r6%Q02Q@1%Q@3<31'4&R?%I2<9r=%R52R:1%4231(?%QH3721&R3&R2%13?ID(Q6'R=(S0(:'=%12RER2%311%32RGRG%511'R9%711'9%82RL1%:11%<6QM86641'R@%=11%A4@3Q51%E3CQ61p0G1p0Q01p0Q>1p0QD1p0QJ1p0R11p0R@1p\2RG1pYJRK1p\:S<1pYNRN1p[<S01p0S41pY2S@1").
Proof.
intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
apply check_read_sound_ok. eapply read0_check_eof; eassumption.
Qed.
Lemma read0_ok_bytes : ltac2:(TCodec.tc2 tcn__StreamSim "TF'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q='R:y8%D11%711'A'Ir4%C2H1+QO%53421';'R6%211&RA&RK%119&UI%12Q2N%5231(2(R5%114%32;1%C3;51&Q>r7(1%3221%H3Q<1;r8u2%7221r;%M3QA21%H1O&S2&Q@r:r9%3221u1%A231r<%83421r6%J2Q:1%Q:3<31'4&R?%I2<9r=%QO2R41%4231(?%QB3721+1&SO&7%12QHQ1%311%R4251%42QKQ0%611r?%R<2RA1%R9231&6'R8&S4&RN%11Q6%>2R5Q1%4221%73R661%R63R71Q4&R3&R2r>%23?1L(Q6'R=(S0&M%12RAQ>(5'=%12S6RC(<%R02;Q@%24S9RF1QD(:%115%83631%82S=S=%411'R9%611'9%=2SB1%911%C6A86641&S6&>%Q21QM%Q?2S6R3%Q5221%43S7Q71%621R1&G'R@(R<%11RN%44S>31R;%Q24Q1=61%Q73Q4R81p0Q91p0QC1p0QI1p0R01p0R91p0RG1p0RM1p0S31p0SB1pXHSI1p\2SJ1pYJSN1p\:T?1pYNT11p[<T31p0T71pY2TC1").
Proof.
intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
apply check_read_sound_ok. eapply read0_check_bytes; eassumption.
Qed.
Lemma read0_ok_inv : ltac2:(TCodec.tc2 tcn__StreamSim "U;'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q='R:y8%D11%711'R='R@%:11'A'Ir7%F2K1+QO%53421';'R6%211&RA&RK%119&UI%12Q5Q1%5231(2(R5%114%32;1%C3;51&Q>r:(1%3221%H3Q?1;r;u1%7221r8%M3QD21r<u2%<221r?%Q23QI21%M1Q7&S2&Q@r>r=%3221r@%632E1r9%M2Q@1%Q=3:31'4&R?rA%R42R91%32I1(?%QD3621&R3&R2%13>FA(Q6%14QLQ4>M%533C1'E'R8&RN%11H(R7%R03421(S0(:'=%12RKR8%311%32RMRM%511'R9%711'9%82S21%:11%<6R086641%R>3RAQE1%R?3RFQJQ9%>1RB%RA3RBQ61%S8231%S9251%S:2D1'B+1&SO&7%12RNS;%311%S:251rD%S@2SE1%S=241&6&S4%Q41R0%2219%43S7Q71%S43S81SF&M%12S;SH(5(<%14T0S=R3SK%33Q61Q5%Q:651Q4Q4Q2O%S<3S?R>1&S6&>%13SCQC=%321R?%SA3SHRH1&G(R<%11S7%34SJSG1T7%SF3SGS11%T=261%T>2<1%T?2E1%T@2L1%TA2Q01qXHT01%Q82T11%R32Q:1p0R51p0R<1p0RD1p0S01p0S61p0S<1p0SB1p0T11pY6T81pYLT?1pY4T<1p\2T>1pXJU21pYJTC1p\:U41pYNTF1p[<TH1p0TL1pY2U81").
Proof.
intros cnt Hcnt segs ms x8 model buf w eff model' evs
Hno Hfd Hg0 Hg1 Hg2 Hw Haok Hspec.
destruct (read0_wmem1 cnt Hcnt segs ms x8 w) as [w1 Hw1];
[rewrite Hg1; exact Hw|].
rewrite Hg1 in Hw1.
destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model)) as [wn Hwn];
[rewrite Hg1; exact Hw|].
rewrite Hg1 in Hwn.
pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
apply check_read_complete_ok in Hspec.
unfold check_read in Hspec.
rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
cbv beta iota in Hspec.
change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
cbv beta iota in Hspec.
rewrite Hg1, Hg2, Haok in Hspec.
cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
-
apply check_ret_only_ok_iff in Hspec.
destruct Hspec as (-> & -> & ->). left. auto.
-
rewrite Hw1 in Hspec. cbv beta iota in Hspec.
rewrite Hwn in Hspec. cbv beta iota in Hspec.
destruct eff as [ret ws zs us cs copyins].
destruct ws as [|[a bs] [|w2 ws]]; [discriminate| |discriminate].
destruct zs as [|z zs]; [|discriminate].
destruct us as [|u us]; [|discriminate].
destruct cs as [|c cs]; [|discriminate].
destruct copyins as [|copyin copyins]; [|discriminate].
destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
&& (1 <=? Z.of_nat (length bs))%Z
&& (Z.of_nat (length bs) <=? rw_count_clamp cnt)%Z
&& listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
&& wmem_ok (sys_input segs ms x8) buf (len_word bs)) eqn:Hb;
try rewrite Hb in Hspec; [|discriminate].
inversion Hspec; subst.
apply andb_true_iff in Hb as [Hb _].
apply andb_true_iff in Hb as [Hb HE].
apply andb_true_iff in Hb as [Hb HD].
apply andb_true_iff in Hb as [Hb HC].
apply andb_true_iff in Hb as [HA HB].
apply bv_eqb_eq in HA; subst a.
apply bv_eqb_eq in HB; subst ret.
apply Z.leb_le in HC. apply Z.leb_le in HD.
rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)) in HD.
apply listN_eqb_eq in HE.
right. exists bs. repeat split; try assumption; reflexivity.
Qed.
Lemma read0_no_unmodeled : ltac2:(TCodec.tc2 tcn__StreamSim "RO'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q='R:y8%D11%711'A'Ir3%C2H1+QO%53421';'R6%211&RA&RK%119&UI%12Q2N%5231(2(R5%114%32;1%C3;51&Q>r6(1%3221%H3Q<1;r7u2%7221r:%M3QA21%H1O&S2&Q@r9r8%3221u1%A231r;%83421r5%J2Q:1%Q:3<31'4&R?%I2<9r<%QO2R41%4231(?%QB3721&D&R3&R2%13@JE(Q7'R=%211%634H1%811p0:1p0C1p0Q11p0Q71p0Q=1p0QL1p\2R31pYJR71p\:RH1pYNR:1p[<R<1p0R@1pY2RL1").
Proof.
intros cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 Hw Haok Hspec.
destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
apply (check_read_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_read in Hspec.
rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
cbv beta iota in Hspec.
change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
cbv beta iota in Hspec.
rewrite Hg2, Haok in Hspec.
cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
{ now apply check_ret_only_no_unmodeled in Hspec. }
rewrite Hw1 in Hspec. cbv beta iota in Hspec.
rewrite Hwn in Hspec. cbv beta iota in Hspec. discriminate.
Qed.
Lemma sstep_read_inv : ltac2:(TCodec.tc2 tcn__StreamSim "V2'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q='R:y8%D11%711'R@%911'R1'A';%11I&RMr6%211(0%11N%83631'=%12Q1Q1%F11&ROr7%211(:%116%A3631'R6%B11&RA&RKr8%211&UI%12QAQ=%6231(2(R5%114%32<1%O3<51&Q?r:%211%82QJF%Q43Q221'I%QI2QN@+QO%Q83321&Q>r<(1%3221%Q=3R41Dr=u1%7221r;%QB3R921r>u2%<221rA%QG3R>21%QG1QL&S2&Q@r@r?%3221rB%632A1%Q52R4?%R13921'4&R?rC%RH2RM1%32C1(?%R83621'QO(QJ%12E@%34>1Q2K'E'R8&RN%11J(R7%RB3421%R41RF%RD3RFQ61(QC&QD&QA%12JQO%311%@21Q4%611%RL3RMQB1%SC291%SD2<1'B+1&SO&7%12S8SE%311%SD251rF%SJ2SO1%SG241&6&S4%L1Q=%2219%43SAO1%S>3SB1T0&G(R<%11RH%34SGSE1T4%SC3SER01&QE(S0&M%12SLT9(5%S@2T@SM(<%14TBSOR5T=%S=13%53421'R9%S@11'9%SH2TH1%SC11%>6<6SCSC41%@2R01%Q?11&S6&>%13T<QJL%321R;%R0251%QF11%T<3T=RN1%U32J1%U42Q01%U52Q71%U62Q;1qXHTE1%QC2TF1%R62QE1p0R81p0R=1p0RE1p0S01p0S61p0S<1p0SB1p0SG1p0SM1p0T<1p0TF1p[BU01pY6U21p\2U51p\:UI1pXJUJ1pYJU;1pYNU=1p[<U?1p0UC1pY2UO1").
Proof.
intros cnt Hcnt segs ms model buf x8 w evs st
Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
as [(Hs & Heff & Hm & Hevs) | (bs & Hlo & Hhi & Hpre & Heff & Hm & Hevs)];
subst eff model' evs0
end.
+ match goal with
| Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
inversion Hmat; subst model''
end.
left. rewrite apply_effect_no_write.
split; [exact Hs | split; reflexivity].
+ match goal with
| Hmat : materialize_model_accesses
(with_stdin ?s model) _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy (with_stdin s model) _)
in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy);
inversion Hmat; subst model''
end.
right. exists bs. repeat split; try assumption; reflexivity.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
subst model';
[ rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat
| rewrite (materialize_model_accesses_no_lazy
(with_stdin (snd (stream_take (m_stdin model) (length bs))) model) _)
in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy) ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
subst model'; [|rewrite m_halted_with_stdin in H6]; congruence
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
subst model';
[ rewrite (m_killed_of_m_halted_none model Hh) in H6
| rewrite (m_killed_of_m_halted_none _
(eq_trans (m_halted_with_stdin _ model) Hh)) in H6 ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (read0_no_unmodeled _ Hcnt segs ms x8 model w Hno Hfd Hg0 eq_refl Hw
Haok H3)
end.
Qed.
Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
(1 <= Z.of_nat (length bs))%Z ->
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
chunks cnt s (bs :: blocks) s''.
Lemma chunks_app : ltac2:(TCodec.tc2 tcn__StreamSim "N'UJyR0%211'R8'8y8%611%311%411'SDr6r5r4r3%544321r7r2%842541r8&3%13=:8%<43618p051p091p[:E1pY@A1p[8G1pY>C1p[4I1pY2K1").
Proof.
intros cnt s l1 s1 l2 s2 H1; revert l2 s2.
induction H1 as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
intros l2 s2 H2; cbn [app]; [exact H2|].
eapply chunks_cons; eauto.
Qed.
Lemma chunks_split : ltac2:(TCodec.tc2 tcn__StreamSim "Q1'UJyR0%211'8y8%511%311%411'R8'SDr5r2&3r4r3%33921r1%847621'B'@r7r6%=42916%>437=9%5221q[8A1%82B1p0:1p[:D1p[4E1pY@G1pY>H1pY2N1").
Proof.
intros cnt l1; induction l1 as [|bs l1 IH]; intros l2 s s2 H; cbn [app] in H.
- exists s. split; [constructor | exact H].
- inversion H as [|s0 bs0 blocks0 s3 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
destruct (IH l2 _ _ HC) as (s1 & H1 & H2).
exists s1. split; [eapply chunks_cons; eauto | exact H2].
Qed.
Lemma chunks_single_inv : ltac2:(TCodec.tc2 tcn__StreamSim "Q?'UJyR0%211'R8'8y8%611%311'SDr4r3(5r2(:%117%43831r1%948721'@&SM+1&SO&7%12A=%311%6251&ULr5%22K1%:251'A&6&S4%12H:%33KO1%53L1I&>%13NQ24%83Q3J1%E241%F2;1%G2@1p0I1p[6Q81pXHQ51p[4Q:1pY2Q<1").
Proof.
intros cnt s bs s' H.
inversion H as [|s0 bs0 blocks0 s2 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
inversion HC; subst.
repeat split; assumption || reflexivity.
Qed.
Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.
Definition iter_ev (bs : list byte) : list event :=
iter_ev_ch (Z_to_bv 64 0) bs.
Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
match s with
| IEof => [ExitEv (Z_to_bv 64 0) fs]
| ICons _ _ => []
end.
Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
(s : InputStream) (tr : list event) : Prop :=
exists blocks s',
chunks cnt s blocks s' /\
is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).
Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
(tr : list event) : Prop :=
stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.
Lemma stream_traces_ch_prefix_closed : ltac2:(TCodec.tc2 tcn__StreamSim "L'UJyR0%211&Q2'R8'8'R@%211&SHr6r5r4r3r2%6554321&QI%13:34r8r7%;521:97p041p071p\0?1p[N@1p[4D1pY8F1pY2H1pZBI1").
Proof.
intros rch cnt fs s tr tr' (blocks & s' & HC & Hp) Hp'.
exists blocks, s'. split; [exact HC | eapply is_prefix_trans; eauto].
Qed.
Lemma stream_traces_prefix_closed : ltac2:(TCodec.tc2 tcn__StreamSim "J'UJyR0%211&Q2'R8'8'R@%211&SGr5r4r3r2%544321&QI%13934r7r6%:42197p041p071p\0>1p[N?1p[4C1pY8E1pY2G1").
Proof. exact (stream_traces_ch_prefix_closed (Z_to_bv 64 0)). Qed.
Section Loop.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Definition lh_next (ms : machine_state) : Prop :=
exists ms', msteps segs ms ms' /\ LH ms'.
Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
(1 <= length bs)%nat /\
to_wall segs (Z_to_bv 64 1) ms bs lh_next.
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wr bs ms' -> to_wr bs ms.
Definition ReadPend (ms : machine_state) : Prop :=
exists buf x8,
ms_svc_pending ms = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms 0 = Z_to_bv 64 0 /\
ms_gpr ms 1 = buf /\
ms_gpr ms 2 = cnt /\
(exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\
access_okb buf (bv_unsigned cnt) = true /\
to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
(forall bs,
(1 <= Z.of_nat (length bs))%Z ->
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
to_wr bs (advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))).
Lemma msteps_to_wr : ltac2:(TCodec.tc2 tcn__StreamSim "E'8'UJy8%211%411'Q='S<vUEr2r1%43321'SBr4%2215r5%4213p031p071pZ0=1pYN>1pXH@1").
Proof.
intros bs ms ms' H; induction H; [auto|].
intro Hwr. eapply twr_step; eauto.
Qed.
Lemma to_wr_wall_tail : ltac2:(TCodec.tc2 tcn__StreamSim "F'8'UJy8%211%411'Q='SBr2r1%3221'SKvUE&UIyR0+1%3221r3&S?%8573;21p0:1pYN?1pXHA1").
Proof.
intros bs ms H; induction H as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
- destruct HWP as [Hnb Hw]. apply twt_more; assumption.
- eapply twt_step; eauto.
Qed.
Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_rd ms' -> to_rd ms.
Lemma msteps_to_rd : ltac2:(TCodec.tc2 tcn__StreamSim ">'Q='S<vUEr2r1%43321'SA%114r4%311p031p061pZ0<1pYN=1").
Proof.
intros ms ms' H; induction H; [auto|].
intro Hrd. eapply trd_step; eauto.
Qed.
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.
Lemma lh_next_to_rd : ltac2:(TCodec.tc2 tcn__StreamSim "9'Q=&S?r1%211'SAr2%211p041pYN81").
Proof.
intros ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.
Lemma to_rd_star : ltac2:(TCodec.tc2 tcn__StreamSim "QA'Q='R:'A';'UJyR0%211%411&RMr1%211(0%116%;3631'8'=%12::%311&ROr2%211(:%116%E3631'SAr4%211'B'@&S=%11E'R0vUE(QJr6r5%3221'R@%A11%62N4%948421%=2;1qZ2Q:1%@2Q;1p0B1p0F1p0Q11pYJQ>1pYNQ@1").
Proof.
intros ms model Hh Hlazy Hrd.
induction Hrd as [ms HRP | ms ms' Hsvc Hstep Hrd IH].
- exists ms. split; [exact HRP | apply star_refl].
- destruct IH as (msR & HRP & Hstar).
exists msR. split; [exact HRP|].
change ([] : list event) with (([] : list event) ++ []).
eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma to_wr_star : ltac2:(TCodec.tc2 tcn__StreamSim "QF'8'UJy8%211%411'Q='R:'A';yR0%911%311&RMr1%211(0%116%:3631'=%1299%D11&ROr2%211(:%116%C3631'SBr5r4%3221'B'@&S>r7%221F'R0vUE(QJr6%221<'R@%B11%52N?%847421%=2:1qZ4Q91%@2Q:1p0B1p0G1p0Q11pYJQ=1pYNQ?1pXHQA1").
Proof.
intros bs ms model Hh Hlazy Hwr.
induction Hwr as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
- exists ms. split; [exact HWP | apply star_refl].
- destruct IH as (msW & HWP & Hstar).
exists msW. split; [exact HWP|].
change ([] : list event) with (([] : list event) ++ []).
eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma stream_star_admits : ltac2:(TCodec.tc2 tcn__StreamSim "QI'R8'8'UJy8%211%411%511'SDvT@r3r2r1%544321'Q='R:&SC%115'A&RN%119r7%43E21'SAr4%211'B'QF'R0vUE(QJr6r5%3221&3'R@&SL&SFr9%34Q1421&SEr8&RL%11;%4231%;3:61%B4A=1Q2qXLD1%F2E1p0H1p0L1p0Q21pYJQ51pYNQ71p0Q91p[6QF1pXDQA1p[4QH1").
Proof.
intros s blocks s' HC.
induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
intros ms model HM Hst Hrd; pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
-
cbn [flat_map app].
destruct s as [|b0 s0] eqn:Hs.
+
destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & _).
destruct (to_exit_star_admits segs (Z_to_bv 64 0)
(advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model Hh Hlazy Hex)
as [c Hstar2].
exists c.
assert (HssE : sstep segs (mkCfg msR model) []
(SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
model))).
{ rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
model model []);
[exact Hh | exact Hsvc | | exact Hh |].
- rewrite <- Hg1 in Hw, Haok. eapply (read0_ok_eof cnt Hcnt); eassumption.
- rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
cbn [eof_tail].
replace [ExitEv (Z_to_bv 64 0) (m_fs model)]
with (([] : list event)
++ ([] ++ [ExitEv (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255))
(m_fs model)]))
by (rewrite band0_255; reflexivity).
eapply star_trans; [exact Hstar0|].
eapply star_step; [exact HssE | exact Hstar2].
+
cbn [eof_tail app]. exists (mkCfg ms model). apply star_refl.
-
destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
pose proof (Hbytes bs Hlo Hhi) as Hwr.
set (advB := advance_past_svc (apply_effect msR
(mkEffect (len_word bs) [(buf, bs)] []))) in *.
set (model' := with_stdin (snd (stream_take s (length bs))) model).
assert (Hh' : m_halted model' = None) by exact Hh.
assert (HM' : M_loop model')
by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
(SNext (mkCfg advB model'))).
{ apply (sstep_syscall segs msR model x8
(mkEffect (len_word bs) [(buf, bs)] []) model' model'
(map (ReadEv (Z_to_bv 64 0)) bs));
[exact Hh | exact Hsvc | | exact Hh' |].
- unfold model'. rewrite <- Hst. rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
eapply (read0_ok_bytes cnt Hcnt); try eassumption.
rewrite Hst. exact Hpre.
- rewrite (materialize_model_accesses_no_lazy model' _ (proj2 (proj2 (proj2 HM')))).
reflexivity. }
assert (Hfdc' : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model')
by (apply fd1chan_fdchan; exact Hfd1).
assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
by reflexivity.
assert (Hcont : forall ms', lh_next ms' ->
exists c, star segs (mkCfg ms' model')
(flat_map iter_ev blocks ++ eof_tail s'' (m_fs model')) c).
{ intros ms' Hlh.
apply (IH ms' model' HM' Hst' (lh_next_to_rd ms' Hlh)). }
destruct (to_wall_tail_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1)
fd32_1 advB bs lh_next (to_wr_wall_tail bs advB Hwr) Hbmbs
model' _ Hh' (proj2 (proj2 (proj2 HM'))) Hfdc' Hcont) as [c Hstar1].
exists c.
change (m_fs model') with (m_fs model) in Hstar1.
cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
rewrite <- !app_assoc.
replace (map (ReadEv (Z_to_bv 64 0)) bs
++ map (WriteEv (Z_to_bv 64 1)) bs
++ flat_map iter_ev blocks ++ eof_tail s'' (m_fs model))
with (([] : list event)
++ (map (ReadEv (Z_to_bv 64 0)) bs
++ (map (WriteEv (Z_to_bv 64 1)) bs
++ (flat_map iter_ev blocks
++ eof_tail s'' (m_fs model)))))
by reflexivity.
eapply star_trans; [exact Hstar0|].
eapply star_step; [exact HssR | exact Hstar1].
Qed.
Lemma star_loop_only : ltac2:(TCodec.tc2 tcn__StreamSim "S3'QF'8'R@%211'R0vUEr3r2r1%544321'Q='R:'Ar6(QJ%1287%43@31&SC%11;'@'SAr4%211'B'UJy8%211%J11%K11'R8'SDvT@&RN%11D%4431KJ&QIr:&3&SL&SF%24=Q61Q1&SE&RL%11N%32Q41%83Q;51%;3Q<:1%L2=1q[6C1%J2D1qXDF1%L2G1p0N1'Fu1&7%12NQ@%4231&S:%11QD'SK&UIyR0+1%3221r7&S?%75QN32QM1r9%Q511%Q84Q71QOQNr=&G(R>%11:%34QAR91QN%Q218%Q42R51%Q93R<Q61%Q:3R=41%Q=3R>91%QN2;1q[6QE1%QL2QF1qXDQH1%QN2QI1p0C1p0L1p0O1pXHQN1%R72Q61p0R91p0R<1pYJRB1pYNRD1p0RF1pXNS01p[NRN1pY0S21").
Proof.
intros c0 tr c' Hstar.
induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
intros ms model Heq HM; subst.
-
split.
+ intros _. exists [], (m_stdin model).
split; [constructor | apply is_prefix_nil].
+ intros bs _ _ _. exists [], (m_stdin model).
split; [constructor | apply is_prefix_nil].
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
by (apply fd1chan_fdchan; exact Hfd1).
split.
+
intro Hrd. destruct Hrd as [ms (buf & x8 & HRP) | ms ms' Hsvc Hstep Hrd'].
*
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (SNext c2)
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
inversion Hc2; subst.
--
destruct (to_exit_star_only segs (Z_to_bv 64 0)
(advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
Hh Hlazy Hex tr2 c3 Hstar) as [-> | ->].
++ exists [], (m_stdin model).
split; [constructor | apply is_prefix_nil].
++ exists [], (m_stdin model).
split; [constructor|].
rewrite Hs, band0_255. cbn [flat_map app eof_tail].
apply is_prefix_refl.
--
assert (Hnb : (1 <= length bs)%nat) by lia.
assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
destruct (proj2 (IH _ _ eq_refl (M_loop_take (length bs) model HM)) bs
Hnb Hbmbs (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)))
as (blocks & s' & HCb & Hp).
exists (bs :: blocks), s'.
split; [eapply chunks_cons; eassumption|].
cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
rewrite <- !app_assoc.
apply is_prefix_app_mono. exact Hp.
*
destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
inversion Hc2; subst.
exact (proj1 (IH _ model eq_refl HM) Hrd').
+
intros bs Hnb Hbm Hwt.
inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl | msS msS' restS kS HsvcS HstepS Hwt']; subst.
*
cbn in Hnb. lia.
*
destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms bs lh_next model evs (SNext c2) Hh Hlazy Hfdc Hbm Hwl Hss)
as (n & Hn1 & Hn2 & Hevs & Hc2 & Hwt2).
inversion Hc2; subst.
set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
--
rewrite skipn_all in Hwt2.
destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
as (msL & HmL & HlhL).
destruct (proj1 (IH _ model eq_refl HM)
(msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)))
as (blocks & s' & HCb & Hp).
exists blocks, s'. split; [exact HCb|].
rewrite firstn_all.
apply is_prefix_app_mono. exact Hp.
--
assert (Hnb' : (1 <= length (skipn n bs))%nat)
by (rewrite length_skipn; lia).
destruct (proj2 (IH _ model eq_refl HM) (skipn n bs) Hnb'
(buf_modeled_skipn n bs Hbm) Hwt2)
as (blocks & s' & HCb & Hp).
exists blocks, s'. split; [exact HCb|].
rewrite <- (firstn_skipn n bs) at 2.
rewrite map_app, <- app_assoc.
apply is_prefix_app_mono. exact Hp.
*
destruct (sstep_instr_inv segs ms model msS' evs (SNext c2)
Hlazy HsvcS HstepS Hss) as [Hevs Hc2].
inversion Hc2; subst.
exact (proj2 (IH _ model eq_refl HM) bs Hnb Hbm Hwt').
Qed.
Definition sinv (c : config) : Prop :=
(M_loop (cfg_model c) /\
(to_rd (cfg_ms c)
\/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
\/ on_path segs (Z_to_bv 64 0) c.
Lemma sinv_step : ltac2:(TCodec.tc2 tcn__StreamSim "C'QF'8'R@%211&S@r3%211'QOvUEr4(QCr2%211%645481p018p091pXN@1pY6>1pXLB1").
Proof.
intros [ms model] evs [ms' model'] Hinv Hss.
destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
by (apply fd1chan_fdchan; exact Hfd1).
destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
+ destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
* destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs
(SNext (mkCfg ms' model'))
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
inversion Hc2; subst.
-- right. left. cbn. split; [exact Hh|].
split; [exact Hlazy | exact Hex].
-- left. cbn. split; [apply M_loop_take; exact HM|].
right. exists bs. split; [lia|].
split; [unfold buf_modeled; lia|].
exact (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)).
* destruct (sstep_instr_inv segs ms model ms1 evs
(SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
inversion Hc2; subst.
left. cbn. split; [exact HM | left; exact Hrd'].
+ inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
| msS msS' restS kS HsvcS HstepS Hwt']; subst.
*
cbn in Hnb. lia.
*
destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms bs lh_next model evs (SNext (mkCfg ms' model'))
Hh Hlazy Hfdc Hbm Hwl Hss)
as (n & Hn1 & Hn2 & _ & Hc2 & Hwt2).
inversion Hc2; subst.
set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
--
rewrite skipn_all in Hwt2.
destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
as (msL & HmL & HlhL).
left. cbn. split; [exact HM|].
left. exact (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)).
--
left. cbn. split; [exact HM|].
right. exists (skipn n bs).
split; [rewrite length_skipn; lia|].
split; [apply buf_modeled_skipn; exact Hbm | exact Hwt2].
* destruct (sstep_instr_inv segs ms model msS' evs
(SNext (mkCfg ms' model')) Hlazy HsvcS HstepS Hss) as [_ Hc2].
inversion Hc2; subst.
left. cbn. split; [exact HM|].
right. exists bs.
split; [exact Hnb | split; [exact Hbm | exact Hwt']].
- right. eapply on_path_step; eauto.
Qed.
Lemma sinv_no_error : ltac2:(TCodec.tc2 tcn__StreamSim "A'QF'8'R@%211&S@r2%211&D'QOvUEr3(QB%443271%611p081pY6<1pXL@1").
Proof.
intros [ms model] evs Hinv Hss.
destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
by (apply fd1chan_fdchan; exact Hfd1).
destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
+ destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
* destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs SError
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
* destruct (sstep_instr_inv segs ms model ms1 evs SError
Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
+ inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
| msS msS' restS kS HsvcS HstepS Hwt']; subst.
* cbn in Hnb. lia.
* exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms bs lh_next model evs Hh Hlazy Hfdc Hbm Hwl Hss).
* destruct (sstep_instr_inv segs ms model msS' evs SError
Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
- eapply on_path_no_error; eauto.
Qed.
Lemma star_sinv : ltac2:(TCodec.tc2 tcn__StreamSim "A'QF'8'R@%211&S@r3%211'R0vUEr4r2%443261p016p071pXN>1p[N<1pXL@1").
Proof. exact (star_inv segs sinv sinv_step). Qed.
Lemma to_rd_no_error : ltac2:(TCodec.tc2 tcn__StreamSim "D'Q='R:&SCr1%211'SAr3%211&D&QMvUE(QJr4%2217%5241%711p091p0=1pYJA1pYNC1").
Proof.
intros ms model HM Hrd.
apply (inv_no_reaches_error segs sinv sinv_step sinv_no_error).
left; cbn; auto.
Qed.
Lemma stream_obs_iff : ltac2:(TCodec.tc2 tcn__StreamSim "QH'H'Q3'UJyR0%211'R4'I'R;'SA&QHvUEr8r7r6r3&RCr1%211&RD%113&RH%115&RF%117%?9>=<;:7531%A11'8'R@%211&C&QL&QGr:r9r5r4%59J43IHG21F%73K1E&SGvT@&RE%11K&RG%11M%64531L%@281p[NB1p0F1pY:Q91pYDQ;1pZJQ=1pYHQ?1pXFQ@1p[@QA1pZ<QE1pZ:QG1").
Proof.
intros pc ph sp brk0 mb rnd lim inp Hrd tr.
set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
unfold init_config.
set (ms0 := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) as HM0.
set (model0 := init_model (segments_reserved segs) brk0 mb sp lim inp) in *.
assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
destruct (proj1 (star_loop_only _ _ _ Hstar ms0 model0 eq_refl HM0) Hrd)
as (blocks & s' & HC & Hp').
rewrite Hst0 in HC. rewrite Hfs0 in Hp'.
apply (stream_traces_prefix_closed cnt fs0 stdin0 tr'); [|exact Hp].
exists blocks, s'. split; assumption.
- intros (blocks & s' & HC & Hp).
destruct (stream_star_admits stdin0 blocks s' HC ms0 model0 HM0 Hst0 Hrd)
as [c Hstar].
rewrite Hfs0 in Hstar.
exists (flat_map iter_ev blocks ++ eof_tail s' fs0), c.
split; assumption.
Qed.
Lemma stream_no_error : ltac2:(TCodec.tc2 tcn__StreamSim "Q='H'Q3'UJyR0%211'R4'I'R;'SA&QHvUEr8r7r6r3&RCr1%211&RD%113&RH%115&RF%117%?9>=<;:7531%A11&D&QM&QGr9r5r4r2%59G4FED32C1%72H1%911p0;1pY:N1pYDQ01pZJQ21pYHQ41pXFQ51p[@Q61pZ<Q:1pZ:Q<1").
Proof.
intros pc ph sp brk0 mb rnd lim inp Hrd.
apply to_rd_no_error; [apply init_M_loop | exact Hrd].
Qed.
Lemma to_rd_coexec : ltac2:(TCodec.tc2 tcn__StreamSim "C'Q='R:&SCr1%211'SAr3%211'Q9vUE(QJr4%2216&Q:%63521p081p0<1pYJ@1pYNB1").
Proof.
intros ms model HM Hrd.
apply (inv_coexec segs sinv sinv_step sinv_no_error). left; cbn; auto.
Qed.
Lemma stream_omni_corun : ltac2:(TCodec.tc2 tcn__StreamSim "Q>'H'Q3'UJyR0%211'R4'I'R;'SA&QHvUEr8r7r6r3&RCr1%211&RD%113&RH%115&RF%117%?9>=<;:7531%A11&Q;(Q5r9%23C1B(QKr5r4%34ED21r2&Q:%:57F321p0<1pY:O1pYDQ11pZJQ31pYHQ51pXFQ61p[@Q71pZ<Q;1pZ:Q=1").
Proof.
intros pc ph sp brk0 mb rnd lim inp Hrd. cbn [omni_corun]. unfold init_config.
apply to_rd_coexec; [apply init_M_loop | exact Hrd].
Qed.
Lemma stream_omni_cosafe : ltac2:(TCodec.tc2 tcn__StreamSim "QD'H'Q3'UJyR0%211'R4'I'R;'SA&QHvUEr8r7r6r3&RCr1%211&RD%113&RH%115&RF%117%?9>=<;:7531%A11&Q<(Q5r9%23C1B(QKr5r4%34ED21r2&SGvT@&RE%114&RG%116%63531%@5=L981p0B1pY:Q51pYDQ71pZJQ91pYHQ;1pXFQ<1p[@Q=1pZ<QA1pZ:QC1").
Proof.
intros pc ph sp brk0 mb rnd lim inp Hrd. cbn [omni_cosafe].
apply cosafe_obs_iff.
- intros t t' Ht Hp. eapply stream_traces_prefix_closed; eauto.
- intros tr Hobs. apply (stream_obs_iff pc ph sp brk0 mb rnd lim inp Hrd). exact Hobs.
Qed.
End Loop.
Lemma stream_omni_strong_equiv : ltac2:(TCodec.tc2 tcn__StreamSim "S5'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q=!p\821'H'Q3'R4'R;rA%11B'SIrCrBrEr2%544321p071pYN@1r:%11Lr<r;rF%=43219p051pYNH1&QHr@r?&RCr3%211&RD%113&RH%115&RF%117%<9KN;:B7531%M4LKJ1r9r8r5r4%?11%=12%<13%;14%F9LN8764321%Q74MLK1&L(Q5%13Q7Q9Q8r=%331Q1Q4(QKr>%24QANM1r7r6%54DC21%;59741Cp0=1p0H1p0Q71p0Q@1pY:QK1pX@QM1pX:RB1pX6RC1pXBRD1pX>R21pX<R41pX4R61p[LR:1p[0R51pZHRJ1pZ@RK1p[2RL1pZNR:1pZLR<1pZ>R>1p[>RB1p0RF1pY2S21").
Proof.
intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
inp HrLH HaLH Hr Ha.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[exact (stream_omni_corun source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd
source_alloc_limit inp Hr) | apply never_errors_covered]. }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr tr).
rewrite (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha tr).
reflexivity.
- exact (stream_omni_corun target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha).
Qed.
Lemma stream_strong_equiv : ltac2:(TCodec.tc2 tcn__StreamSim "S@'UJyR0%211'@&SNz&ULr1%2271%5241&SM&S9%2241%:241'8'Q4%211'Q=!p\821'H'Q3'R4'I'R;rC%11C'SIrErDrGr2%544321p071pYNA1r;%11Mr=r<rH%=43219p051pYNI1&QHrBrAr>&RCr3%211&RD%113&RH%115&RF%117%=9LO<;:7531%N4MLK1r:r9r6r4%?11%=12%<13%;14%G9MO8764321%Q84NML1&K&QN(Q5%13Q9Q;Q:r?(QKr@%24QBON1r5%846521%:11&J%:3Q2Q:Q=r8r7%:4IH21%?44H18%6281%RC281p0D1p0O1p0Q?1p0QH1pY:R31pX8R51pX@R71pX:RL1pX6RM1pXBRN1pX>R<1pX<R>1pX4R@1p[LRD1pZFR>1p[0R@1pZHS51pZ@S61p[2S71pZNRE1pZLRG1pZ>RI1p[>RM1p0S11pY2S=1").
Proof.
intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
inp HrLH HaLH Hr Ha.
split.
{ apply no_error_run_modeled.
apply (stream_no_error source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr). }
right. split.
- intro tr. cbn.
rewrite (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr tr).
rewrite (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha tr).
reflexivity.
- cbn. apply (stream_no_error target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha).
Qed.
