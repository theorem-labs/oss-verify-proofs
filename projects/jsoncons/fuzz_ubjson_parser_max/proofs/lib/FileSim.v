(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim PropExec CatSim CatExec ErrEscape SeqExec StreamExec StreamSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__FileSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FileSim.WithFP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FileSim.WithFP1.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1negb"; "1nil"; "1option"; "1pair"]; ["1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3add"; "3sub"; "4le"; "4lt"; "5firstn"; "5nth"; "6N"]; ["6Z"; "7equiv"; "7modeled"; "8omni_strong_equiv"; "9len_word"; "9word_to_nat"; ":check_syscall"; ";check_close"; ";check_open_result"; ";check_openat"; "<check_read"; "<check_write"; "=CheckOk"; "=CheckUnmodeled"; "=check_copyins_after"; "=check_result"]; ["=check_ret_only"; "=check_ret_only_copyins"; "=clear_copyins"; ">Fs"; ">file_read"; ">file_write"; ">fs_lookup"; ">fs_set"; ">path"; ">path_eqb"; ">path_ltb"; "?PhdrInfo"; "?Segment"; "?mkImage"; "@Ok"; "@Unmodeled"]; ["Aexec"; "Aomni_run"; "BBuild_machine_state"; "Bmachine_state"; "Bms_gpr"; "Bms_read_byte"; "Bms_svc_pending"; "Bms_writable_byte"; "Bwrite_to_mem"; "CSError"; "CSNext"; "Cadvance_past_svc"; "Call_traces_error"; "Capply_effect"; "Cbehavior"; "Cconfig"]; ["Centry_stack_image"; "Cinit_config"; "Cinit_machine_state"; "Cis_prefix"; "CmkCfg"; "CmkEntry"; "Cobs_trace"; "Creaches_error"; "Crun"; "Csegments_reserved"; "Csstep"; "Cstar"; "Cstep_to"; "Csys_input"; "Dsyscall_spec"; "EEntryDraw"]; ["Ebuild_stack_bytes"; "Estack_to_mem"; "FCstrOk"; "FCstrTooLong"; "FEISDIR"; "FENAMETOOLONG"; "FENOENT"; "FENOMEM"; "FFdEntry"; "FFdFile"; "FFdFileW"; "FMemCopy"; "FModel"; "FProcInput"; "FSyscallEffect"; "Faccess_okb"]; ["Faddr_is_error_b"; "Falloc_fd"; "Fcstr_result"; "Feff_copyins"; "Ferrno_ret"; "Fevent"; "Ffd_insert"; "Ffd_lookup"; "Ffd_remove"; "Fin_arg"; "Fin_argv"; "Fin_envp"; "Fin_hwcap"; "Fin_mem"; "Fin_sysno"; "Fin_uid"]; ["Fin_wmem"; "Finit_model"; "Fm_fds"; "Fm_fs"; "Fm_halted"; "Fm_vm_lazy"; "FmkEffectU"; "Fread_bytes_map"; "Fread_cstr"; "Fread_cstr_aux"; "Fsource_alloc_limit"; "Ftarget_alloc_limit"; "Ftwo_pow_64"; "Fwith_copyins"; "Fwith_fds"; "Fwith_fs"]; ["Gfs_under"; "Hmodeled_open_flags"; "Hopen_ignored_flags"; "Hopenat_errnos"; "Hopenat_plain_name"; "Hwr_create_flags"; "Imodeled_file_gap"; "Jfd32"; "Jw_is0"; "Kdelivered_writes"; "Krw_bytes_max"; "LAT_FDCWD"; "Mbv_eqb"; "Mbvmap"; "Nreg_get"; "Ocat_argv_ptr"]; ["Pmsteps"; "Qis_exit_no"; "Sfon_path"; "Sfout_post"; "Sto_fout"; "Rcheck_open_result_copyins"; "Rfout_post"; "Rfout_trace"; "Rmrb"; "Ropen_copyins"; "Rto_fout"; "Tfp_csr"; "Tfp_regs"; "Tgetr"; "Tmkst"; "Trdn"]; ["Tregupd"; "Tseg_rom"; "Tv_addi"; "Uwseg_ok"; "Vmin"; "WIn"; "Wfilter"; "Xadd"; "Xldiff"; "Xle"; "Xlt"; "Xof_nat"; "Xpow"; "Xsub"; "0Te"; "0Ts"]; ["0U"; "0U'"; "0V"; "0a"; "0abrk"; "0addr"; "0alim"; "0amb"; "0apc"; "0aph"; "0arnd"; "0asp"; "0av"; "0b"; "0brk0"; "0bs"]; ["0buf"; "0c"; "0c'"; "0cnt"; "0code"; "0copyins"; "0core"; "0count"; "0d"; "0d'"; "0data"; "0e"; "0ea"; "0eff"; "0eff2"; "0ev"]; ["0evs"; "0evs'"; "0evs2"; "0f"; "0fc"; "0fd"; "0fd'"; "0fdin"; "0fds"; "0fdv"; "0fr"; "0fs"; "0fsv"; "0fuel"; "0fx"; "0hw"]; ["0inp"; "0k"; "0lim"; "0m"; "0m'"; "0m2"; "0mb"; "0mem"; "0mk"; "0model"; "0model'"; "0ms"; "0ms'"; "0n"; "0o"; "0off"]; ["0p"; "0pc"; "0ph"; "0q"; "0r"; "0rbrk"; "0reads"; "0regs"; "0rest"; "0rlim"; "0rmb"; "0rnd"; "0rom"; "0rpc"; "0rph"; "0rrnd"]; ["0rsp"; "0rv"; "0segs"; "0source_segs"; "0sp"; "0st"; "YBV"; "YZ_to_bv"; "Ybv"; "Ybv_add"; "Ybv_and"; "Ybv_unsigned"; "0str"; "0sv"; "0target"; "0target_segs"]; ["0tr"; "0uid"; "0w"; "0x"; "0x8"; "0y"; "0z"]]).
Section WithFP1.
Context {fx : FPState}.
Lemma with_fds_fs : ltac2:(TCodec.tc2 tcn__FileSim "E':'@'XHyR0%211'S8%5221%711'S<'D&QC&T3&T>r2r1%3221%511%613%93821p_8;1p^8=1").
Proof. reflexivity. Qed.
Lemma with_fds_halted : ltac2:(TCodec.tc2 tcn__FileSim "F':'@'XHyR0%211'S8%5221%711'S<'D'>%117&T4&T>r2r1%3221%511%613%:3821p_8<1p^8>1").
Proof. reflexivity. Qed.
Lemma with_fds_fds : ltac2:(TCodec.tc2 tcn__FileSim "C':'@'XHyR0%211'S8%5221%711'S<'D&T2&T>r2r1%3221%511%73914p_891p^8;1").
Proof. reflexivity. Qed.
Lemma with_fs_fs : ltac2:(TCodec.tc2 tcn__FileSim "<&QC'S<'D&T3&T?r2r1%3221%511%73914p_891p^8;1").
Proof. reflexivity. Qed.
Lemma with_fs_halted : ltac2:(TCodec.tc2 tcn__FileSim "B&QC'S<'D'>'XHyR0%211%411&T4&T?r2r1%3221%511%613%=3821p_8?1p^8A1").
Proof. reflexivity. Qed.
Lemma with_fs_fds : ltac2:(TCodec.tc2 tcn__FileSim "E&QC'S<'D':'@'XHyR0%211'S8%5221%711&T2&T?r2r1%3221%511%613%@3821p_8B1p^8D1").
Proof. reflexivity. Qed.
Lemma adv_eff_ret : ltac2:(TCodec.tc2 tcn__FileSim "R3&TMy5'XHyR0%211%5241'>y8%611%311p061'D'R3&R;&R=(R2r6&U<vW>%211r5(3r4%22C1(0%11E&U;%119r3r2%?8>;:75321(T6r1(='@':%11L%32Q11%511%52Q3Q3%711'S;%911';%:2Q81%<11%?6>86641%Q12A1%Q311&U>&U@(XF+:(B%33QE21%53Q71G&UB+4%22Q61%:5Q941ON%QA3Q@<1p`:QI1p`JQD1p_@QE1pb:QL1p`4QM1p`@QM1").
Proof.
intros regs pc x8 mem rom r.
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros apply_writes apply_zeros].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
Lemma adv_eff_ret_copyins : ltac2:(TCodec.tc2 tcn__FileSim "R8&TMy5'XHyR0%211%5241'>y8%611%311p061':'@';%22:1%411'D'R3&R;&R=(R2r7&U<vW>%211r6(3r5%22H1(0%11J&U;%119r4r3%?8>;:75321&T=r1(T6r2(=%N1Q1%N2Q61%311%Q02Q8Q8%511'S;%711%81Q2%;6:64421%>2=1%Q02@1%Q211&U>&U@(XF+:(B%33QI21%53Q61D&UB+4%22Q51%:5Q841NM%Q@3Q?<1p]<QB1p`:QN1p`JQI1p_@QJ1pb:R11p`4R21p`@R21").
Proof.
intros regs pc x8 mem rom r copyins.
unfold with_copyins.
apply adv_eff_ret.
Qed.
Lemma in_sysno_si : ltac2:(TCodec.tc2 tcn__FileSim "C':'QL%211'R3'XHyR0%211'D&SN&RMr3r2r1%43321%611%83913pb::1p_H>1pa6@1").
Proof. reflexivity. Qed.
Lemma in_arg0_si : ltac2:(TCodec.tc2 tcn__FileSim "F':'QL%211'R3'XHyR0%211'D&SI&RMr3r2r1%43321(1%7221&R4%1263%;3<31pb:=1p_HA1pa6C1").
Proof. reflexivity. Qed.
Lemma in_arg1_si : ltac2:(TCodec.tc2 tcn__FileSim "F':'QL%211'R3'XHyR0%211'D&SI&RMr3r2r1%43321u1%7221&R4%1263%;3<31pb:=1p_HA1pa6C1").
Proof. reflexivity. Qed.
Lemma in_arg2_si : ltac2:(TCodec.tc2 tcn__FileSim "F':'QL%211'R3'XHyR0%211'D&SI&RMr3r2r1%43321u2%7221&R4%1263%;3<31pb:=1p_HA1pa6C1").
Proof. reflexivity. Qed.
Lemma in_mem_si : ltac2:(TCodec.tc2 tcn__FileSim "J':'QL%211'R3'XHyR0%211'D'>y8%611%311p061&SM&RMr3r2r1%43321%611&R5%115%?3:31pb:A1p_HE1pa6G1").
Proof. reflexivity. Qed.
Lemma in_wmem_si : ltac2:(TCodec.tc2 tcn__FileSim "J':'QL%211'R3'XHyR0%211'D'>y8%611%311p061&T0&RMr3r2r1%43321%611&R7%1265%?3:31pb:A1p_HE1pa6G1").
Proof. reflexivity. Qed.
Lemma path_eqb_neq : ltac2:(TCodec.tc2 tcn__FileSim "@&QH&G'Dr2r1%33521%511'5&QIr3%2217(7%:3521p071p`8>1p`2?1").
Proof.
intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
apply path_eqb_eq in E. congruence.
Qed.
Lemma fs_lookup_set_eq : ltac2:(TCodec.tc2 tcn__FileSim "G&QC&QH':'XHy8%211%411'D'>%113&QF&QGr3r2r1%43321%6213(3%12<4%<3:31p]B>1p`2D1p^HF1").
Proof.
induction fs as [|[q dq] fs IH]; intros p d; cbn.
- rewrite path_eqb_refl. reflexivity.
- destruct (path_ltb p q); cbn.
+ rewrite path_eqb_refl. reflexivity.
+ destruct (path_eqb p q) eqn:E; cbn.
* rewrite path_eqb_refl. reflexivity.
* rewrite E. apply IH.
Qed.
Lemma fs_lookup_set_neq : ltac2:(TCodec.tc2 tcn__FileSim "M&QC&QH':'XHy8%211%411&G'Dr1r3%33:21%511'>%118&QF&QGr5r4%33219r2%6221%7252%?3921p0<1p`8H1p]BD1p`2J1p^HL1").
Proof.
induction fs as [|[r dr] fs IH]; intros p d q Hne; cbn.
- rewrite path_eqb_neq by exact Hne. reflexivity.
- destruct (path_ltb p r); cbn.
+ rewrite path_eqb_neq by exact Hne. reflexivity.
+ destruct (path_eqb p r) eqn:E; cbn.
* apply path_eqb_eq in E. subst r.
rewrite path_eqb_neq by exact Hne. reflexivity.
* destruct (path_eqb q r); [reflexivity | apply IH; exact Hne].
Qed.
Lemma path_ltb_irrefl : ltac2:(TCodec.tc2 tcn__FileSim "9&QH'D'5&QJr1%2211(7%63521p`281").
Proof.
induction p as [|a p IH]; cbn; [reflexivity|].
unfold bv_ltu. rewrite Z.ltb_irrefl, bv_eqb_refl, IH. reflexivity.
Qed.
Lemma fs_set_set : ltac2:(TCodec.tc2 tcn__FileSim "E&QC&QH':'XHy8%211%411'D&QGr4r3r2%43321r1%63241%73652%93@21p]D;1p]B<1p`2B1p^HD1").
Proof.
induction fs as [|[q dq] fs IH]; intros p d d'; cbn.
- rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
- destruct (path_ltb p q) eqn:EL; cbn.
+ rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
+ destruct (path_eqb p q) eqn:EE; cbn.
* rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
* rewrite EL, EE, IH. reflexivity.
Qed.
Lemma fd_lookup_cons_eq : ltac2:(TCodec.tc2 tcn__FileSim "J':'@'XHyR0%211'S8%5221%711'D'>%115&SG(6(?r2r1%34<;21r3%63<21%8215(3%12@6%>3<31p]HB1p^<D1p^BB1").
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.
Lemma fd_lookup_cons_neq : ltac2:(TCodec.tc2 tcn__FileSim "Q0':'@'XHyR0%211'S8%5221%711&G'Dr3r1%33821%511'>%11:&SG(6(?r4%24@?1:r5%53@21r2%8221%9242%A3;21p0>1p^<H1p]HH1p_4J1p^BH1").
Proof.
intros fds k e fd Hne. cbn.
rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.
Lemma fd_lookup_cons_None : ltac2:(TCodec.tc2 tcn__FileSim "Q5':'@'XHyR0%211'S8%5221%711'D'>%115&SG(6(?r3r2%34<;21r4%63<21r1%9221(0%11A%?3=31'C&G%B3F9;%211r5%B21>%F3D18%7241p091p^<M1p]HM1p_4O1p^BM1").
Proof.
intros fds k e fd H. cbn in H.
destruct (bv_eqb k fd) eqn:E; [discriminate|].
split; [|exact H].
intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.
Lemma fd_filter_id : ltac2:(TCodec.tc2 tcn__FileSim "Q0':'@'XHyR0%211'S8%5221%711'D'>%115&SGr2r1%3221(0%11;%93731&UF&<&TL&8%13BA9r3%43E21%611q`2D1%93E14%D3E15p0<1p^<J1p^BH1").
Proof.
induction fds as [|[k e] fds IH]; intros fd H; [reflexivity|].
apply fd_lookup_cons_None in H. destruct H as [Hne H].
cbn [List.filter fst]. rewrite (bv_eqb_neq k fd Hne). cbn [negb].
rewrite IH by exact H. reflexivity.
Qed.
Lemma fd_insert_fresh : ltac2:(TCodec.tc2 tcn__FileSim "N':'@'XHyR0%211'S8%5221%711'D'>%115&SGr3r2%3221(0%11;%93731&SFr4%23187(6(?%14CB;:%33B15%A3B51p091p]HF1p^<H1p^BF1").
Proof.
intros fds fd e H. unfold fd_insert. rewrite fd_filter_id by exact H.
reflexivity.
Qed.
Lemma fd_lookup_filter_neq : ltac2:(TCodec.tc2 tcn__FileSim "Q2':'@'XHyR0%211'S8%5221%711&G'Dr1r2%33821%511'>%11:&SG&UF&<&TL&8%13A@;r4%43D21%611q`2C1%93D14%;21@%<26A%D3>21p0A1p^>K1p^<L1p^BJ1").
Proof.
induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
cbn [List.filter fst].
destruct (bv_eqb k fd) eqn:Hk.
- apply bv_eqb_eq in Hk. subst k.
cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
rewrite bv_eqb_neq by congruence. reflexivity.
- cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.
Lemma fd_lookup_insert_eq : ltac2:(TCodec.tc2 tcn__FileSim "H':'@'XHyR0%211'S8%5221%711'D'>%115&SG&SFr3r2r1%43321%6213(3%12>4%<3:31p]H@1p^<B1p^B@1").
Proof. intros. unfold fd_insert. apply fd_lookup_cons_eq. Qed.
Lemma fd_lookup_insert_neq : ltac2:(TCodec.tc2 tcn__FileSim "N':'@'XHyR0%211'S8%5221%711&G'Dr1r3%33821%511'>%11:&SG&SFr5r4%33219r2%6221%7252%?3921p0<1p^>F1p]HF1p^<H1p^BF1").
Proof.
intros fds fd e fd' Hne. unfold fd_insert.
rewrite fd_lookup_cons_neq by congruence.
apply fd_lookup_filter_neq. exact Hne.
Qed.
Lemma fd_lookup_remove_neq : ltac2:(TCodec.tc2 tcn__FileSim "L':'@'XHyR0%211'S8%5221%711&G'Dr1r2%33821%511'>%11:&SG&SHr4r3%3221%521:%624;%>3821p0;1p^>E1p^<F1p^BD1").
Proof. intros. unfold fd_remove. apply fd_lookup_filter_neq. assumption. Qed.
Lemma fd_lookup_some_none_neq : ltac2:(TCodec.tc2 tcn__FileSim "Q1':'@'XHyR0%211'S8%5221%711'D'>%115&SGr4r3%3221(3r1%22<1%:3841r5%9217(0%11A%?3=31&G%A3E6=%211p041p0:1p]JH1p\LJ1p\8K1p^BI1").
Proof. intros fds a b ea Ha Hb ->. congruence. Qed.
Lemma free_fd_after_open : ltac2:(TCodec.tc2 tcn__FileSim "QH'S8'XHyR0%211'E'C'D'>%118&SG&SF(6'@%12:=(?&XGz%22?1r6%54@C21+1%62C1r5%94DG21+2%:2G1r4%=4HK21(=%11@%C3A31%D3B81%E3C=1r3r2%I3321r1%L221(0%11Q7%Q23Q031&UJ&XK%12Q97&UL+O%22F1%6241%Q;281qb6Q>1%Q>2Q?1p]HQC1p^@QA1pb>QE1pb<QF1pb8QG1").
Proof.
intros x y z fdin e.
destruct (decide (fdin = Z_to_bv 64 3)) as [->|Hne].
- exists (Z_to_bv 64 4). split.
+ rewrite fd_lookup_insert_neq
by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
reflexivity.
+ change (bv_unsigned (Z_to_bv 64 4)) with 4%Z. lia.
- exists (Z_to_bv 64 3). split.
+ rewrite fd_lookup_insert_neq by congruence. reflexivity.
+ change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
Qed.
Lemma filter_fd_cons_keep : forall {B} (fds : list (word * B)) k (e : B) fd,
k <> fd ->
List.filter (fun p => negb (bv_eqb (fst p) fd)) ((k, e) :: fds)
= (k, e) :: List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
intros B fds k e fd Hne. cbn [List.filter fst].
rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.
Lemma filter_fd_cons_drop : forall {B} (fds : list (word * B)) fd (e : B),
List.filter (fun p => negb (bv_eqb (fst p) fd)) ((fd, e) :: fds)
= List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
intros B fds fd e. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma length_file_read : ltac2:(TCodec.tc2 tcn__FileSim "L':'XHy8%211%411yR0%511'D';&9&QDr3r2r1%43321%62<1&UD&Q5%115&J%;2A9%419%3221%7251%A3@91p]@C1p`0D1p]FG1").
Proof.
intros data off count. rewrite file_read_unguarded.
rewrite length_firstn, length_skipn. reflexivity.
Qed.
Lemma file_read_nil : ltac2:(TCodec.tc2 tcn__FileSim "J':'XHy8%211%411yR0%511'K&9r3%2271&Q5r2%211%7241'D&QDr4%23196(=%11A%63A31p081p]@A1p`0B1p]FE1").
Proof.
intros data off count H. rewrite file_read_unguarded.
rewrite skipn_all2 by exact H. apply firstn_nil.
Qed.
Lemma file_write_append : ltac2:(TCodec.tc2 tcn__FileSim "J':'XHy8%211%411yR0%511'D';&Q5r2%211&9r3%22;1%83741&QEr4%23158&4%13A3:%>3A31p071p]0C1p`0B1p]FE1").
Proof.
intros data off bs Hoff. unfold file_write.
destruct bs as [|b bs]; [now rewrite app_nil_r|]. cbv zeta.
rewrite Hoff, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
rewrite firstn_all.
rewrite skipn_all2 by lia.
rewrite app_nil_r. reflexivity.
Qed.
Lemma firstn_add {A} : forall (l : list A) n m,
firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
induction l as [|x l IH]; intros n m.
- rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
- destruct n as [|n]; [reflexivity|].
cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.
Lemma copy_step : ltac2:(TCodec.tc2 tcn__FileSim "Q1':'XHy8%211%411yR0%511'D&4&M&Q5r2%211r3%53;21&QDr1%23461%:3?41&I&UD%;15&J&9%12E;%321=%6251%82?1%C3I1?%F3I;1p]@H1p`0I1p]FL1").
Proof.
intros data off count. rewrite file_read_unguarded.
rewrite firstn_add. f_equal.
destruct (Nat.le_ge_cases (word_to_nat count)
(length data - word_to_nat off)) as [H|H].
- rewrite Nat.min_l by exact H. reflexivity.
- rewrite Nat.min_r by exact H.
rewrite firstn_all2 by (rewrite length_skipn; lia).
rewrite firstn_all2 by (rewrite length_skipn; lia).
reflexivity.
Qed.
Definition mrb (segs : list Segment) (mem : word -> option byte)
: word -> option byte :=
fun a => match mem a with Some b => Some b | None => seg_rom segs a end.
Lemma ms_read_byte_mrb : ltac2:(TCodec.tc2 tcn__FileSim "Q2':'QL%211&TMy5'XHyR0%211%5241'>y8%611%311p061'Dp\<83&R5&U>vW>r3r2r1&UAr4%211%8576541%:11&U8%1257%?3>31p_@A1p`4H1p`@H1pa6O1").
Proof. reflexivity. Qed.
Lemma ms_read_byte_rec_mrb : ltac2:(TCodec.tc2 tcn__FileSim "Q<':'QL%211&TMy5'XHyR0%211%5241'>%113yQ0%711y8%911%611p091'Dp\<;3&R5(R2r7r6r5r4r3r2r1&UAr8%211%;8:9876541%=11&U8%1257%B3A31p_@D1p^:I1pa4L1paLM1p`4Q11p^FQ11p`@Q21pa6Q91").
Proof. reflexivity. Qed.
Lemma mrb_first : ltac2:(TCodec.tc2 tcn__FileSim "Q:':'QL%211'XHyR0%211'>y8%511%311p051';%<14'D%812&U?r6r5r4(2r3%211%746541(3(6r2r1%33C21%52@1%@3?71&U8r7%231@?%:2I=%E3I21p061p`BH1p\LM1p_LK1p\8Q21p_@N1pa6Q71").
Proof.
intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
as [b1|]; [|discriminate].
destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
injection H; intros; subst; congruence.
Qed.
Lemma rdn_tail : ltac2:(TCodec.tc2 tcn__FileSim "Q?':'QL%211'XHyR0%211'>y8%511%311p051';%<14'D%812&U?r6r5r4(2r3%211%746541(3(6r2r1%33C21%52@1%@3?71r7&XI(XF+1(B%33O21%53Q0C1%F47E1C%?2J=%J3I21p0;1p`BM1p\LQ21p_LQ01p\8Q71p_@Q31pa6Q<1").
Proof.
intros segs mem a n b rest H. cbn [rdn] in H.
destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
as [b1|]; [|discriminate].
destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
injection H; intros; subst; reflexivity.
Qed.
Lemma read_cstr_aux_of_rdn : ltac2:(TCodec.tc2 tcn__FileSim "QO':'QL%211'XHy8%211%611';yR0%611'>%116p031&L&9r4%22;1r3%5221&G&UE&XGz%22C1r5%53D21%711'D%B1F&U?r7&Ir6%C2L1u1%4221%746EC1(3&4(6(=%11Q4%33Q5C1%53Q6;1%72Q61%B3A91'SB&T9&U8r8%221J%431Q4C(S2%11G%K3831p0:1p0N1p0Q71p\8QA1p_@Q?1p^LQE1paJQG1pa6QL1").
Proof.
intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hr.
- cbn [length] in *. destruct fuel as [|fuel]; [lia|].
assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
cbn [read_cstr_aux]. rewrite Hb0. reflexivity.
- cbn [length] in *. destruct fuel as [|fuel]; [lia|].
cbn [read_cstr_aux]. cbn [app] in Hr.
assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
assert (Hfirst : mrb segs mem a = Some b)
by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
exact Hr).
assert (Htail : rdn segs mem (a + 1) (length str + 1)
= Some (str ++ [Z_to_bv 8 0]))
by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
exact Hr).
rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
rewrite (IH fuel mem (a + 1) ltac:(lia)
ltac:(intro; apply Hnz; right; assumption) Htail).
reflexivity.
Qed.
Lemma read_cstr_of_rdn : ltac2:(TCodec.tc2 tcn__FileSim "QO':'QL%211'XHyR0%211'>y8%511%311p051%;13'K&9r1%2271uSoO%5221&G&UE&XGz%22?1r2%53@21%711'D%E1@&U?r6r5r4&Ir3%E2J1u1%4221%948761(3&4(6(=%11Q2%33Q3E1%53Q4;1%72Q21%D3C91'SB&T8&U8r7%221F%421F(S2%11G%M3831p0:1p0Q01p0Q91paJQ@1p\8QG1p_@QC1pa6QL1").
Proof.
intros segs mem a str Hlen Hnz Hr.
unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hr].
change path_max with 4096%nat. lia.
Qed.
Lemma read_cstr_aux_toolong_of_rdn : ltac2:(TCodec.tc2 tcn__FileSim "QC':'QL%211';'XHy8%211%711yR0%511'>%115p031'D&9r3%22:1r4%53?21&G&UE&XGz%22B1%43B17%611%@1C&U?r7r6%342=?1(3r5%22J1%E3841'SB&T9&U8r8%2217%431G<(S3%M3721p091p0C1p0K1p\8Q51p_@Q31p]0Q91p^LQ>1pa6Q@1").
Proof.
intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hr;
[reflexivity|].
destruct bs as [|b bs]; [cbn in Hlen; lia|].
cbn [read_cstr_aux].
assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
assert (Hfirst : mrb segs mem a = Some b)
by (apply (mrb_first segs mem a fuel b bs); exact Hr).
assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
ltac:(intro; apply Hnz; right; assumption) Htail).
reflexivity.
Qed.
Lemma read_cstr_toolong_of_rdn : ltac2:(TCodec.tc2 tcn__FileSim "QD':'QL%211'XHyR0%211'>y8%511%311p051%;13'D';&9r1%2281uTP0%63521&G&UE&XGz%22@1r2%53A21%711%E1@&U?r6r5r4%44321?(3r3%22H1%H3941'SB&T8&U8r7%221<%421<(S3%Q03721p091p0D1p0M1p]0Q51p\8Q<1p_@Q81pa6QA1").
Proof.
intros segs mem a bs Hlen Hnz Hr.
unfold read_cstr. change path_max with 4096%nat.
eapply read_cstr_aux_toolong_of_rdn; eauto.
Qed.
Lemma read_argv_cstr_k : ltac2:(TCodec.tc2 tcn__FileSim "RB'QK':'QL%211'XHyR0%211y8%411%811%911';'RO&Lr4&9r6%2281%5241&UJ&UG&XKr8%22B1&UK&S0r:r7r3r2%57483>@21%@2G1%811%=2:1&UL+2+R0%3221%C251'D'>%11Q0&U?&S1r9&R@r;r5%3724JE1Q2D%6251&TO%147MHQ3&I&N(=%11Q?%34Q?Q8Q21%Q:2QA1u1%7221%B4Q2;91(3&4(6&XGz%22QK1%43QK1<%63QL<1%82QL1%O3M:1p0Q11p0QF1p`HQM1p_0R41pb4R51p_4R11p^0R31p\JR41pa:R91pa6R=1p`6RA1").
Proof.
intros ph segs sp av ev k uid hw rnd Hk Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
pre (nth k av [] ++ [Z_to_bv 8 0]) post (length (nth k av []) + 1)) as H.
rewrite Hlen in H.
replace (cat_argv_ptr sp av ev k)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
apply H; [exact E | | exact Hnw].
rewrite length_app. cbn [length]. lia.
Qed.
Lemma read_argv_prefix_k : ltac2:(TCodec.tc2 tcn__FileSim "R@'QK':'QL%211'XHyR0%211y8%411%811%911';'RO&Lr5&9r7%2281%5241'K&Nr6r8(=%11@%54@431%;2B1%82=1&UJ&UG&XKr:%22K1&UK&S0r<r9r4r3%57483AI21%I2Q01%811%=2:1&UL+2+R0%3221%C251'D'>%11Q9&U?&S1r;&R@r=%2713IDQ3Q:C%5241&TO%146LGQ5%94I31Q<(3&M%Q;4QFQ9Q0Q7%23QHQ@1%42QH1%B3@61p0D1p0Q91p0QC1p`HQJ1p_0R11pb4R21p_LQN1p_4QO1p^0R11p\JR21pa:R71pa6R;1p`6R?1").
Proof.
intros ph segs sp av ev k n uid hw rnd Hk Hn Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
pre (firstn n (nth k av []))
((skipn n (nth k av []) ++ [Z_to_bv 8 0]) ++ post) n) as H.
rewrite Hlen in H.
replace (cat_argv_ptr sp av ev k)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
apply H; [| |exact Hnw].
- rewrite E. rewrite <- !app_assoc.
rewrite (app_assoc (firstn n (nth k av [])) (skipn n (nth k av []))).
rewrite firstn_skipn. reflexivity.
- apply firstn_length_le. exact Hn.
Qed.
Definition fout_trace (o : word * Fs.Fs) : list event := [ExitEv (fst o) (snd o)].
Section WithSegs.
Variable segs : list Segment.
Inductive to_fout : machine_state -> Model -> ((word * Fs.Fs) -> Prop) -> Prop :=
| tfo_exit : forall ms model x8 (U : (word * Fs.Fs) -> Prop),
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
(forall o, U o <-> o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) ->
to_fout ms model U
| tfo_step : forall ms ms' model U,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_fout ms' model U ->
to_fout ms model U
| tfo_sys : forall ms model x8
(T : SyscallEffect -> Model -> (word * Fs.Fs) -> Prop)
(U : (word * Fs.Fs) -> Prop),
ms_svc_pending ms = Some x8 ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) ->
(forall eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
(forall eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
to_fout (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
(forall o, U o <->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
/\ T eff model' o)) ->
to_fout ms model U.
Lemma tfo_msteps : ltac2:(TCodec.tc2 tcn__FileSim "J'R3'S<'@'XHyR0%211&QC%5221!p021'U0vXBr4r3%43321'U4r2%23541r6%43176p031p071p\2=1p_DF1p_JH1p_HI1").
Proof.
intros ms ms' model U H; induction H; [auto|].
intro Ht. eapply tfo_step; eauto.
Qed.
Lemma tfo_equiv : ltac2:(TCodec.tc2 tcn__FileSim "O'R3'S<'@'XHyR0%211&QC%5221!p021pb832'U4r4r3r2%43321&Fr1%511%712%4221p_N>1r6r5%=321;p041p0;1p\6A1p\2C1p_DL1p_HN1").
Proof.
intros ms model U V Hto; revert V.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros V HV.
- apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
intro o. rewrite (HV o). apply HU.
- eapply tfo_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
- apply (tfo_sys ms model x8 T V);
[exact Hsvc | exact Hne | exact Hrec | exact Hshape | exact Hcont |].
intro o. rewrite (HV o). apply HU.
Qed.
Lemma to_fout_nonempty : ltac2:(TCodec.tc2 tcn__FileSim "G'R3'S<'@'XHyR0%211&QC%5221!p021'U4r3r2r1%43321'E%513q_N:1%32;1p051p\2;1p_DD1p_HF1").
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ].
- exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
apply HU. reflexivity.
- exact IH.
- destruct Hrec as (eff & model' & evs & Hspec).
destruct (IH eff model' evs Hspec) as [o Ho].
exists o. apply HU. exists eff, model', evs. auto.
Qed.
Lemma sstep_fsys_inv : ltac2:(TCodec.tc2 tcn__FileSim "S8'R3'S<'XHyR0%211':'SE%211'RL'D'>%117&T4r4%211(0%11<%83631'@%12??%?11&T5r5%211(=%116%A3631&R6r7%211(3%12K9%G3E31&G&RN&RMvXBr8r6%43321(QO'S>%211%934?1%;11r<r:%<3;21r;(QNr3r2r1%44<321%D3761'C%Q01QB%Q@3QB61%Q>18%QB3Q@1Q;%Q71:%QD3Q91Q4%7231%8261p0:1p^4QJ1p_FR11p]LJ1'RJ(RDr9%22I1%44Q41Q<Q2'Er=%Q83Q71K%K4Q3IHD%Q;32Q01%R53R7Q0F(R:&R;&R=%128O%311%?21Q0%611%R=3R>@1%Q0291%Q12;1q_FRH1%A2RI1q]LQB1%C2QC1p0E1p0K1p0QC1p0R01p0R71p0RA1pa<RK1p^2RM1pb:S11p_DS51p_HS71").
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (He & _ & Hlazy');
subst evs0;
match goal with
| Hmat : materialize_model_accesses model' _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
inversion Hmat; subst model''
end;
exists eff, model'; auto
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & _ & Hlazy');
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
congruence
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
assert (Hhn : m_halted model' = None) by congruence;
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
end.
Qed.
Definition fout_post (U : (word * Fs.Fs) -> Prop) : post :=
fun tr o => exists out, U out /\ tr = fout_trace out /\ exits_with (fst out) tr o.
Lemma to_fout_exec : ltac2:(TCodec.tc2 tcn__FileSim "Q?'R3'S<'@'XHyR0%211&QC%5221!p021'U4r3r2r1%43321'D'>%11<&T4%118(0%11@%73531':%F2CC%211&T5r4%211(=%116%@3631'R0vXB(RDr6r5%3221&U3%11<%83731p0:1p0D1p0M1p\2Q31p_DQ<1p_HQ>1").
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros Hh Hlazy.
-
apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_si. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold fout_post. cbn beta.
exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
split; [apply HU; reflexivity |].
split; [unfold fout_trace; cbn [fst snd app]; reflexivity |].
cbn [exits_with cfg_model fst]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
-
apply exec_step; [exact Hh | | |].
+ destruct Hrec as (eff & model' & evs & Hspec).
destruct (Hshape eff model' evs Hspec) as (-> & Hh' & Hlazy').
eexists; eexists.
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
+ intros evs Hss.
destruct (sstep_fsys_inv ms model x8 evs SError Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & _ & _ & Habs). discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_fsys_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' Hlazy') |].
intros tr o (out & Hout & Heq & Hx). exists out.
split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
split; [cbn [app]; exact Heq | exact Hx].
Qed.
Lemma to_fout_star_only : ltac2:(TCodec.tc2 tcn__FileSim "QM'R3'S<'@'XHyR0%211&QC%5221!p021'U4r3r2r1%43321'D'>%11<&T4%118(0%11@%73531':%F2CC%211&T5r4%211(=%116%@3631'SE%:11'R?'RKvXB(RDr8r7%3221%6451ML'E'C%61O&RC&U7%11Q2%33@E1%6251q_NQ;1%92Q<1p0;1p]4C1pb2E1p0H1p0Q21p0Q;1p\2QA1p_DQJ1p_HQL1").
Proof.
intros ms model U Hto Hh Hlazy tr c Hstar.
destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_fout_exec ms model U Hto Hh Hlazy) Hstar))
as (tr' & o & _ & (out & Hout & Heq & _)).
exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.
Lemma to_fout_star_admits : ltac2:(TCodec.tc2 tcn__FileSim "QG'R3'S<'@'XHyR0%211&QC%5221!p021'U4r3r2r1%43321'D'>%11<&T4%118(0%11@%73531':%F2CC%211&T5r4%211(=%116%@3631r5%11D'E'R?'RKvXB(RDr9r8%3221&U7%11Q0%84731Oq]4:1%<2;1p0>1p_NQ91p0B1p0L1p0Q51p\2Q;1p_DQD1p_HQF1").
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros Hh Hlazy o Ho.
-
apply HU in Ho. subst o. unfold fout_trace; cbn [fst snd].
exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
apply star_one.
replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
+ exact Hh.
+ exact Hsvc.
+ apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_si. exact Hx8.
+ cbn. reflexivity.
+ apply m_killed_with_halted.
-
destruct (IH Hh Hlazy o Ho) as [c Hstar].
exists c.
replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
eapply star_step; [|exact Hstar].
apply (sstep_instr segs ms model ms' model); try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
-
apply HU in Ho.
destruct Ho as (eff & model' & evs & Hspec & Ht).
destruct (Hshape eff model' evs Hspec) as (He & Hh' & Hlazy'). subst evs.
destruct (IH eff model' [] Hspec Hh' Hlazy' o Ht) as [c Hstar].
exists c.
replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
eapply star_step; [|exact Hstar].
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
Qed.
Lemma to_fout_progress : ltac2:(TCodec.tc2 tcn__FileSim "R:'R3'S<'@'XHyR0%211&QC%5221!p021'U4r3r2r1%43321'D'>%11<&T4%118(0%11@%73531':%F2CC%211&T5r4%211(=%116%@3631'SE%:11'RL'RJvXB(RDr8r7%3221%6451ML'E'C(R:%82Q1Q0%211%Q03=D1'H&G%Q01Q5%Q43Q21N%311%K1Q8%Q73M1Hq\4Q>Q9%>2Q?1%>231%?271%;271%A2=1q_FQL1%D2QM1q_JQO1%F2R01p0H1pa<Q01p^2Q21p0Q51p0Q?1p0QH1p\2QN1p_DR71p_HR91").
Proof.
intros ms model U Hto Hh Hlazy evs st Hss.
revert evs st Hss.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros evs st Hss.
-
destruct (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss)
as [_ Hst]. subst st.
do 2 eexists. split; [reflexivity|]. left. cbn. discriminate.
-
destruct (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss)
as [_ Hst]. subst st.
do 2 eexists. split; [reflexivity|]. right.
repeat split; try assumption. exists U. exact Hto.
-
destruct (sstep_fsys_inv ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & Hspec & _ & Hst). subst st.
destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
do 2 eexists. split; [reflexivity|]. right.
repeat split; try assumption.
exists (T eff model'). exact (Hcont eff model' [] Hspec).
Qed.
Definition fon_path (c : config) : Prop :=
(m_halted (cfg_model c) = None
/\ m_vm_lazy (cfg_model c) = []
/\ exists U, to_fout (cfg_ms c) (cfg_model c) U)
\/ m_halted (cfg_model c) <> None.
Lemma fon_path_step : ltac2:(TCodec.tc2 tcn__FileSim "C'R?':'SE%211&U2r3%211'RJvXBr4(R:r2%211%645481p018p091p]6@1p^2>1p]4B1").
Proof.
intros [ms model] evs [ms' model'] Hop Hss.
unfold fon_path in *; cbn in Hop |- *.
destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
- destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
as (ms'' & model'' & Hst & Hcase).
inversion Hst; subst.
destruct Hcase as [Hhz | (Hhz & Hlazy' & U' & Hto')].
+ right. exact Hhz.
+ left. repeat split; try assumption. exists U'; exact Hto'.
- exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.
Lemma fon_path_no_error : ltac2:(TCodec.tc2 tcn__FileSim "A'R?':'SE%211&U2r2%211&G'RJvXBr3(R9%443271%611p081p^2<1p]4@1").
Proof.
intros [ms model] evs Hop Hss.
unfold fon_path in Hop; cbn in Hop.
destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
- destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
as (ms'' & model'' & Hst & _). discriminate.
- inversion Hss; subst; cbn in Hh; congruence.
Qed.
Lemma star_fon_path : ltac2:(TCodec.tc2 tcn__FileSim "A'R?':'SE%211&U2r3%211'RKvXBr4r2%443261p016p071p]6>1pb2<1p]4@1").
Proof. exact (star_inv segs fon_path fon_path_step). Qed.
Lemma to_fout_no_error : ltac2:(TCodec.tc2 tcn__FileSim "Q?'R3'S<'@'XHyR0%211&QC%5221!p021'U4r3r2r1%43321'D'>%11<&T4%118(0%11@%73531':%F2CC%211&T5r4%211(=%116%@3631&G&RGvXB(RDr6r5%3221%6251%811p0:1p0D1p0M1p\2Q31p_DQ<1p_HQ>1").
Proof.
intros ms model U Hto Hh Hlazy. apply exec_no_error.
eapply exec_conseq; [exact (to_fout_exec ms model U Hto Hh Hlazy) |].
intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma star_syscall_nil : ltac2:(TCodec.tc2 tcn__FileSim "QO'R3'S<'XHyR0%211'S>'D'>%114&T4r4%211(0%119%83631&R6r6%211(3%12?9%>3<31&RN&RMvXBr7r5%43321(QNr3(='SE%211%54KF41%<37A1':'@%12Q0Q0%311&T5%11>%;14%Q33421'RK(RDr:r9%3221&R;&R=%125I%311%821Q3%:4M6E1p0<1p0Q81p0F1p0Q41p0Q;1p_FQI1p]LQF1pb:QH1p_DQL1p_HQN1").
Proof.
intros ms model x8 eff model' Hh Hsvc Hspec Hh' Hlazy.
apply star_one.
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy). reflexivity.
Qed.
Lemma reaches_error_star : ltac2:(TCodec.tc2 tcn__FileSim "C'R?':'SE%211'RKvXBr3r2r1%544321&RG%1264r5%3281p031p061p]6@1pb2>1p]4B1").
Proof.
intros c tr c' Hstar (tr2 & c2 & evs & Hstar2 & Hss).
exists (tr ++ tr2), c2, evs. split; [eapply star_trans; eauto | exact Hss].
Qed.
Lemma spec_err_error : ltac2:(TCodec.tc2 tcn__FileSim "Q9'R3'S<'XHyR0%211'D'>%113&T4r2%211(0%118%83631&R6r4%211(3%12>9%>3<31&RN&RMvXBr5r3%43321(QO'S>%211%934>1&RG(RDr6%221:%42<1p061p0A1p0H1pb:Q21p_DQ61p_HQ81").
Proof.
intros ms model x8 Hh Hsvc Hspec.
exists [], (mkCfg ms model), []. split; [apply star_refl|].
eapply sstep_syscall_unmodeled; eassumption.
Qed.
Lemma msteps_spec_err_error : ltac2:(TCodec.tc2 tcn__FileSim "QI'R3'S<'XHyR0%211'D'>%113&T4r2%211(0%118%83631':'@%12<<%311&T5r3%211(=%116%B3631'U0vXBr6r5%43321&R6%114(3r4%22M1%M3K41&RN&RMr7%23=1;(QO'S>%211%734@1&RG(RDr9%2219%42F1p061p0?1p0F1p0L1p0Q71pb:QA1p_DQE1p_JQG1p_HQH1").
Proof.
intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
eapply reaches_error_star.
- apply msteps_star_nil; eassumption.
- eapply spec_err_error; eassumption.
Qed.
Lemma spec_err_all_traces_error : ltac2:(TCodec.tc2 tcn__FileSim "Q9'R3'S<'XHyR0%211'D'>%113&T4r2%211(0%118%83631&R6r4%211(3%12>9%>3<31&RN&RMvXBr5r3%43321(QO'S>%211%934>1'R<(RDr6%221:%42<1p061p0A1p0H1pb:Q21p_DQ61p_HQ81").
Proof.
intros ms model x8 Hh Hsvc Hspec.
assert (Hno_ok : forall eff model' events,
~ syscall_spec (sys_input segs ms x8) model
(Ok eff model' events)).
{ intros eff model' events Hok.
pose proof Hspec as Herr.
apply (check_syscall_complete_unmodeled _ _ eff) in Herr.
apply check_syscall_complete_ok in Hok.
rewrite Herr in Hok. discriminate Hok. }
constructor.
- exists [], SError. eapply sstep_syscall_unmodeled; eassumption.
- intros evs c' Hnext. inversion Hnext; subst; try congruence.
all: exfalso;
match goal with
| Hno : forall (eff0 : SyscallEffect) (model0 : Model)
(events0 : list event),
~ syscall_spec (sys_input ?segs0 ?ms0 ?expected) ?m0
(Ok eff0 model0 events0),
Hexpected : ms_svc_pending ?ms0 = Some ?expected,
Hactual : ms_svc_pending ?ms0 = Some ?actual,
Hok : syscall_spec (sys_input ?segs0 ?ms0 ?actual) ?m0
(Ok ?eff ?model' ?events) |- _ =>
assert (actual = expected) by congruence; subst actual;
exact (Hno eff model' events Hok)
end.
Qed.
Lemma msteps_spec_err_all_traces_error : ltac2:(TCodec.tc2 tcn__FileSim "QI'R3'S<'XHyR0%211'D'>%113&T4r2%211(0%118%83631':'@%12<<%311&T5r3%211(=%116%B3631'U0vXBr6r5%43321&R6%114(3r4%22M1%M3K41&RN&RMr7%23=1;(QO'S>%211%734@1'R<(RDr9%2219%42F1p061p0?1p0F1p0L1p0Q71pb:QA1p_DQE1p_JQG1p_HQH1").
Proof.
intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
eapply msteps_all_traces_error; [exact Hh | exact Hlazy | exact Hm |].
eapply spec_err_all_traces_error; eassumption.
Qed.
Lemma tfo_exit_code : ltac2:(TCodec.tc2 tcn__FileSim "QC'R3'S<'XHyR0%211'D'>%113&R6r4%211(3r2%2291%93741&U1r3%211&R4r6(1%3221%A3B16&XJ&XG+WO%22G1%43HB1%G3H1C'U4r8r7'@&QC%22N1r1(?&T3%118%34Q36D1%Q33651q_N71%=3<;1p0?1p0F1p0L1p0Q01p]:Q;1pb:Q<1p_DQ@1p_HQB1").
Proof.
intros ms model x8 code Hsvc Hx8 Hg Hland.
apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
intro o. rewrite Hg, Hland. tauto.
Qed.
Lemma tfo_sys_det : ltac2:(TCodec.tc2 tcn__FileSim "RN'R3'S<'XHyR0%211'S>'@&QC%2241!p021'D'>%119&R6r6%211(3r4%22?1%93741&RN&RMvXBr7r5%43321(QNr3(='SE%211%54K>41%<37B1':%115r;r9%@3?21r:r2r1%?4Q5>21%F3541'C%Q23Q8K8r8%Q43Q>C1%Q53=8A%5221%6251p081p^6A1p_<QD1p]NQA1&G%Q23Q1CQ0(QO%11QE%Q633=1%511&T4%11Q?(0%11QL%QF3QD31%QL2QNQN%Q111&T5%11Q=%Q914%QL3421'U4&R;&R=r<%221Q7%411%631Q0QFr=%8315Q2p031p0;1p0B1p0H1p0O1p0QE1p0R31p\2R>1p_FRH1p]LRE1pb:RG1p_DRK1p_HRM1").
Proof.
intros ms model x8 eff model' U Hsvc Hok Huniq Hne Hh' Hlazy' Hcont.
apply (tfo_sys ms model x8 (fun _ _ => U) U); [exact Hsvc | exact Hne | | | |].
- exists eff, model', []. exact Hok.
- intros eff2 m2 evs2 Hs.
destruct (Huniq eff2 m2 evs2 Hs) as (_ & -> & ->).
repeat split; assumption.
- intros eff2 m2 evs2 Hs.
destruct (Huniq eff2 m2 evs2 Hs) as (-> & -> & _). exact Hcont.
- intro o. split.
+ intro Ho. exists eff, model', []. auto.
+ intros (e2 & m2 & ev2 & _ & Ht). exact Ht.
Qed.
End WithSegs.
Lemma check_syscall_56 : ltac2:(TCodec.tc2 tcn__FileSim "Q;':'QL%211'R3'XHyR0%211'S>'S<'D'Q0&XKr3%2281+QH%63521'Q?&Q6&RMr6r5r4%43321r2%732<1&Q9&TG&R4(1%2291%411u1%52<1u2%72>1%:6=531G<%K3D<1p0F1p_8N1p]LQ01pb:Q21p_HQ61pa6Q81").
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.
Lemma check_syscall_57 : ltac2:(TCodec.tc2 tcn__FileSim "Q7':'QL%211'R3'XHyR0%211'S>'S<'D'Q0&XKr3%2281+QI%63521'Q?&Q6&RMr6r5r4%43321r2%732<1&Q7&TG&R4(1%2291%411%631C8%G3@81p0B1p_8J1p]LL1pb:N1p_HQ21pa6Q41").
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.
Lemma check_syscall_63 : ltac2:(TCodec.tc2 tcn__FileSim "Q;':'QL%211'R3'XHyR0%211'S>'S<'D'Q0&XKr3%2281+QO%63521'Q?&Q6&RMr6r5r4%43321r2%732<1&Q:&TG&R4(1%2291%411u1%52<1u2%72>1%:6=531G<%K3D<1p0F1p_8N1p]LQ01pb:Q21p_HQ61pa6Q81").
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.
Lemma check_syscall_64 : ltac2:(TCodec.tc2 tcn__FileSim "Q;':'QL%211'R3'XHyR0%211'S>'S<'D'Q0&XKr3%2281+R0%63521'Q?&Q6&RMr6r5r4%43321r2%732<1&Q;&TG&R4(1%2291%411u1%52<1u2%72>1%:6=531G<%K3D<1p0F1p_8N1p]LQ01pb:Q21p_HQ61pa6Q81").
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.
Lemma fd_not_error : ltac2:(TCodec.tc2 tcn__FileSim "E'XHyR0%211&UJ&XKr1%2251&UL+2+O%3221%8251'D'5&S@r2%211(7%63521p081p^<B1").
Proof.
intros fd H. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge. lia.
Qed.
Lemma errno_ret_recover : ltac2:(TCodec.tc2 tcn__FileSim "F'Q0&UI+1r1%3221r2+SoO%6221'D&UM&T<&XKyR0&SDr3%211%5241%8271%:3B14p0<1p0@1p]HE1").
Proof.
intros e H1 H2. rewrite (errno_ret_unsigned e H1 H2). lia.
Qed.
Lemma ENOMEM_in_openat_errnos : ltac2:(TCodec.tc2 tcn__FileSim "5&UE'Q0&S7&TC%43321").
Proof. left. reflexivity. Qed.
Lemma openat_errno_range : ltac2:(TCodec.tc2 tcn__FileSim "?'Q0&UEr1&TC%33421'C&UI+1r2%3221+SoO%5231%7231p091p]H>1").
Proof. intros e HIn. exact (errnos_ok_range openat_errnos e eq_refl HIn). Qed.
Lemma check_open_result_never_unmodeled : ltac2:(TCodec.tc2 tcn__FileSim "D'S>'S<'XHyR0%211p014&G'D'Q?&Q8r3r2r1%43321(Q=%83721%:11p_B<1p_8A1p]LC1").
Proof.
intros [ret ws zs us cs copyins] m mk.
unfold check_open_result, check_new_fd_result.
destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
destruct cs as [|? ?];
destruct copyins as [|? ?];
try discriminate.
destruct (errno_ret_in openat_errnos ret); [discriminate|].
destruct (fd_lookup (m_fds m) ret); [discriminate|].
destruct (bv_eqb ret (alloc_fd (m_fds m))); discriminate.
Qed.
Lemma check_open_result_ok_iff : ltac2:(TCodec.tc2 tcn__FileSim "RG'S>'S<'XHyR0%211p014':'SE%211&F'D'Q?&Q8r5r4r3%43321(Q<r2r1%3221%;3:51'H'E'Q0'C&UE&TC%23491r6(T6&SD%11=(='@y8%Q211%O11%42Q21%611%62Q4Q4%811'S;%:11';%;2Q91%=11%A6?86641%Q63Q@C1%Q73Q@Q2Q4%A1Q;%Q93Q;Q11%K231%L251%M2J1q]HO1%Q12Q01'>'S8%211&SG&T2%11QA%321Q<(0%117%QH3731&SA%116%QK3R1QB1%Q86QCOMMKH%QM3R7Q:1%QJ1QE%QO3R8QJ1%QA21G%QB241%QC271%QD2;1q^<R:1%QH2R;1%QJ2H1%R82QL1p^2R:1p_:RB1p_BR?1p_8RD1p]LRF1").
Proof.
intros [ret ws zs us cs copyins] m mk m' evs.
unfold check_open_result, check_new_fd_result. split.
- intro H.
destruct ws as [|? ?]; [|discriminate].
destruct zs as [|? ?]; [|discriminate].
destruct us as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct copyins as [|? ?]; [|discriminate].
destruct (errno_ret_in openat_errnos ret) eqn:Herr; try rewrite Herr in H.
+ inversion H; subst.
apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
left. exists e. auto.
+ destruct (fd_lookup (m_fds m) ret) eqn:Hlk; try rewrite Hlk in H;
[discriminate|].
destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; try rewrite Heq in H;
[|discriminate].
inversion H; subst.
right. exists ret. apply bv_eqb_eq in Heq. auto.
- intros [ (e & HIn & Heff & -> & ->)
| (fd & Hlk & Heq & Heff & -> & ->) ].
+ inversion Heff; subst.
rewrite (errno_ret_in_intro _ e HIn). reflexivity.
+ inversion Heff; subst.
rewrite errno_ret_in_alloc_fd by reflexivity.
rewrite Hlk, bv_eqb_refl. reflexivity.
Qed.
Definition open_copyins (ms : machine_state) : list (word * nat) :=
[(ms_gpr ms 1,
cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].
Definition check_open_result_copyins (reads : list (word * nat))
(eff : SyscallEffect) (m : Model) (mk : word -> Model) : check_result :=
check_copyins reads eff (check_open_result (clear_copyins eff) m mk).
Lemma effect_from_copyins_and_clear : ltac2:(TCodec.tc2 tcn__FileSim "L'S>':'@'XHyR0%211';%5221%711'D&SCr3%211r2%53621&QBr4%211%93B15r5&T=%125:%=3F31p051p0:1p]>I1p`>B1p]LK1").
Proof.
intros [ret ws zs us cs copyins] reads core Hreads Hcore.
cbn [eff_copyins] in Hreads. subst copyins.
unfold clear_copyins, with_copyins in Hcore |- *.
cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies] in Hcore |- *.
inversion Hcore. reflexivity.
Qed.
Lemma check_open_result_copyins_never_unmodeled : ltac2:(TCodec.tc2 tcn__FileSim "K':'@'XHyR0%211';%5221%711'S>'S<p061&G'D'Q?&U5r4r3r2r1%544321(Q=%93821%;11p_B=1p_8?1p]LA1p`>C1").
Proof.
intros reads eff m mk.
unfold check_open_result_copyins, check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads);
[apply check_open_result_never_unmodeled|discriminate].
Qed.
Lemma check_open_result_copyins_ok_iff : ltac2:(TCodec.tc2 tcn__FileSim "RM':'@'XHyR0%211';%5221%711'S>'S<p061'SE%<11&F'D'Q?&U5r6r5r4r3%544321(Q<r2r1%3221%<3;51'H'E'Q0'C&UE&TC%23491&T=r7(T6&SD%11>(=y8%Q711%Q:11%Q:2Q71%511%Q<2Q9Q9%711'S;%911%:1Q;%>6<64421%A2@1%Q63Q<Q31%Q73Q<Q1Q3%?1Q;%Q93Q;Q01%J231%K251%L2I1q]HN1%Q02O1'>'S8%211&SG&T2%11Q@%321Q;(0%117%QH3731&SA%116%QK3R5QA1%Q66QBNLLJI%Q92Q81%QN3R4QK1%QJ1QE%R03R5QJ1%QA21H%QB241%QC281%QD2<1q^<R?1%QH2R@1%QJ2I1%R92QL1p^2R;1p_:R?1p_BR?1p_8RA1p]LRC1p`>RE1").
Proof.
intros reads eff m mk m' evs.
unfold check_open_result_copyins, check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:Hreads.
- apply access_ranges_eqb_eq in Hreads.
rewrite check_open_result_ok_iff. split.
+ intros [(e & HIn & Hcore & -> & ->)
| (fd & Hlk & Heq & Hcore & -> & ->)].
* left. exists e. repeat split; try assumption.
eapply effect_from_copyins_and_clear; eassumption.
* right. exists fd. repeat split; try assumption.
eapply effect_from_copyins_and_clear; eassumption.
+ intros [(e & HIn & Heff & -> & ->)
| (fd & Hlk & Heq & Heff & -> & ->)].
* left. exists e. repeat split; try assumption.
rewrite Heff. reflexivity.
* right. exists fd. repeat split; try assumption.
rewrite Heff. reflexivity.
- split; [discriminate|].
intros [(e & _ & Heff & _)
| (fd & _ & _ & Heff & _)].
all: rewrite Heff in Hreads; cbn [eff_copyins with_copyins] in Hreads;
pose proof (proj2 (access_ranges_eqb_eq reads reads) eq_refl) as Htrue;
congruence.
Qed.
Lemma check_copyins_after_ret_only : ltac2:(TCodec.tc2 tcn__FileSim "Q1':'@'XHyR0%211';%5221%711'S>'S<'SE%;11'D'Q?&Q>r5r4&Q@&QB%113r3r2r1%644321%:3981&QA%15;:654%?3>31p^2A1p_8D1p`:J1p]LG1p`>I1").
Proof.
intros reads eff r m evs.
unfold Prelude.check_copyins_after, check_ret_only_copyins.
destruct (check_ret_only (clear_copyins eff) r m evs) eqn:Hresult.
- reflexivity.
- unfold check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads); reflexivity.
- exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.
Lemma openat_rd_check : ltac2:(TCodec.tc2 tcn__FileSim "S;':'QL%211'R3'XHyR0%211'S<y8%511%:11'D'Q0&XKr4%22:1+QH%63521&R4r6(1%3221&TK%<3A21'SB&T8&R5r7%211u1%<231%6231(S2%11C%G3:31'5&QIr5(=%11N%4231(7%O3721&UHr9u2%L221%Q22Q:1&TB%6221z%Q83Q721&TD%11J(A%Q<3D21'>%11Q?&QF&T3%11@r8%4221(3%12QFQ5%QF3831'S>'Q?&Q6&RMr>r=r<%43321r1r;%83321&U5&U9%118&T>&SF&T2%11;(S9&XG%12RAQ4%32<1%735>1%921Aq^<RD1%>4<A@1%RA3I@1p]LK1p0M1p0Q81p0Q=1p0QG1p0R01p0R<1p0RC1p]BRK1p`2RL1p_DS01pb:S21p_HS61pa6S81").
Proof.
intros segs ms x8 model p d Hno Hdirfd Hpath Hpe Hfl Hdot Hfs eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl, Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_read.
rewrite ?Hdot, ?Hfs.
unfold check_open_result_copyins, open_copyins.
destruct (check_open_result (clear_copyins eff) model
(fun fd : word =>
with_fds
(fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model))
eqn:Hresult.
- reflexivity.
- reflexivity.
- exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.
Lemma openat_wr_check : ltac2:(TCodec.tc2 tcn__FileSim "S<':'QL%211'R3'XHyR0%211'S<y8%511%:11'D'Q0&XKr3%22:1+QH%63521&R4r5(1%3221&TK%<3A21'SB&T8&R5r6%211u1%<231%6231(S2%11C%G3:31'5&QIr4(=%11N%4231(7%O3721&UHr8u2%L221%Q22Q:1&TB%6221&TE%Q83Q721&TD%11J(A%Q<3D21&T@&T3%11>r7%4221%QB3J1D'S>'Q?&Q6&RMr=r<r;%43321r1r:%83321&U5&U9%118&T>&SF&T2%11;(S:&XGz%22R>1%42=1%836?1&T?&QG%O1D%231BQB%421F%?261q^<RF1%D4BGF1%RC3OF1p]LQ11p0Q31p0Q:1p0Q?1p0QI1p0R21p0R>1p0RE1p`2RM1p_DS11pb:S31p_HS71pa6S91").
Proof.
intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl.
change (wr_create_flags =? 0)%Z with false. cbv beta iota.
rewrite Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_create, check_create_wronly.
rewrite Hdot, Hun. rewrite orb_false_l. cbv beta iota.
unfold check_open_result_copyins, open_copyins.
destruct (check_open_result (clear_copyins eff) model
(fun fd : word =>
with_fds
(fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model)))
eqn:Hresult.
- reflexivity.
- reflexivity.
- exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.
Lemma openat_wr_isdir_check : ltac2:(TCodec.tc2 tcn__FileSim "S0':'QL%211'R3'XHyR0%211'S<y8%511%:11'D'Q0&XKr3%22:1+QH%63521&R4r5(1%3221&TK%<3A21'SB&T8&R5r6%211u1%<231%6231(S2%11C%G3:31'5&QIr4(=%11N%4231(7%O3721&UHr8u2%L221%Q22Q:1&TB%6221&TE%Q83Q721&TD%11J(A%Q<3D21&T@&T3%11>r7%4221%QB3J17'S>'Q?&Q6&RMr=r<r;%43321r1r:%83321&QA&U9%118&SD&S4%211'SE%Q:11%856;3:1%R73C:1p]LE1p0G1p0N1p0Q31p0Q=1p0QF1p0R21p0R91p`2RA1p_DRE1pb:RG1p_HRK1pa6RM1").
Proof.
intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl.
change (wr_create_flags =? 0)%Z with false. cbv beta iota.
rewrite Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_create.
rewrite Hdot, Hun. rewrite orb_false_l. cbv beta iota.
apply check_copyins_after_ret_only.
Qed.
Lemma openat_toolong_check : ltac2:(TCodec.tc2 tcn__FileSim "QO':'QL%211'R3'XHyR0%211'S<'D'Q0&XKr2%2271+QH%63521'5&TA&R4r4u2%3221%511(A%?3821'SB&T8&R5r5%211u1%=231%6231(S3%I3921'S>'Q?&Q6&RMr8r7r6%43321r1%7321@&QA&U9%117&SD&S5%211(='SE%211%957;4J1%Q>3C;1p]LE1p0G1p0Q21p0Q<1p_DQD1pb:QF1p_HQJ1pa6QL1").
Proof.
intros segs ms x8 model Hno Hfl Hpath eff.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite Hfl. cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath.
unfold check_ret_only_copyins, open_copyins.
destruct (check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG)
model []) eqn:Hresult.
- reflexivity.
- unfold check_copyins.
destruct (access_ranges_eqb (eff_copyins eff)
[(ms_gpr ms 1,
cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]);
reflexivity.
- exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.
Section OpenNodes.
Variable segs : list Segment.
Lemma tfo_open_core : ltac2:(TCodec.tc2 tcn__FileSim "TN'R3'S<'XHyR0%211p014':'@';%2251%411'Q0&QC%6291!p021p051p0=2pb854'D'>%11A&R6r8%211(3r5%22G1%93741&T4%117(0%11L%>3<31%K2NN%M11&T5r9%211(=%116%F3631'S>'Q?&Q6&RMvXBr<%3321;r1r;%73321&U5r:%24O541%Q43<41p]L>1'C%819%N11%Q93Q71L%I13%Q;3K1F%6231p^<QL1&UE&TC%23QHB1'U:&R;&R=r?&T=(T6&SDr2%211y8%R<11%R911%R92R<1%Q:11'S;%Q<11%Q=1R;%<694Q=Q=21%>2Q41%A2@1%C11r>%Q51?%G4Q=321p0I1p]HRB1'S8%R;11&SG&T2%119%321QB%R516%RB3621&SA%61Q0%211%RF3S5N1rAr=r3%Q461LR5R5JI%Q6231%Q9251%Q;11%Q:15%R016%Q?4R5321p0;1p0@1p^<SB1&F%RC1R7'H'E%R<2R:Q@%R32QI1q]HSB1%42SC1r@%O11%Q121R@%S?3Q31N%M13%SA3T0RC1%RC2RDQJ%R=221%R>251q^<T41%?2T51%A2<1%D2C1p_NSO1%R94RO>R6S8p021p0I1p0QC1p0RA1p0RJ1p0S:1p0SC1p0SI1p\2T41p\0T61p[NT81p`>T?1pb:TF1p_BTF1p_DTK1p_HTM1").
Proof.
intros ms model mk x8 reads Te Ts U Hsvc Hh Hlazy Hchk Hmk Herr Hok HU.
apply (tfo_sys segs ms model x8
(fun eff model' =>
if addr_is_error_b (eff_ret eff)
then Te ((two_pow_64 - bv_unsigned (eff_ret eff))%Z)
else Ts (eff_ret eff)) U); [exact Hsvc | | | | |].
-
intro Hspec.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
rewrite Hchk in Hspec.
exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hspec).
-
exists (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])), model, [].
apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. left. exists ENOMEM.
repeat split; try reflexivity. apply ENOMEM_in_openat_errnos.
-
intros eff model' evs Hspec.
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & _ & -> & -> & ->)
| (fd & _ & _ & -> & -> & ->) ].
+ repeat split; assumption.
+ destruct (Hmk fd) as [Hhalt Hlazy']. repeat split; assumption.
-
intros eff model' evs Hspec.
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & HIn & -> & -> & _)
| (fd & Hlk & Heq & -> & -> & _) ].
+ destruct (openat_errno_range e HIn) as [He1 He2].
cbn [eff_ret with_copyins].
rewrite (errno_ret_error_b e He1 He2).
rewrite (errno_ret_recover e He1 He2).
apply Herr; assumption.
+ cbn [eff_ret with_copyins].
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne.
apply Hok; assumption.
-
intro o. rewrite HU. split.
+ intros [ (e & HIn & Ht) | (fd & Hlk & Heq & Ht) ].
* destruct (openat_errno_range e HIn) as [He1 He2].
exists (with_copyins reads (mkEffect (errno_ret e) [] [])), model, [].
split.
{ apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. left. exists e. auto. }
{ cbn [eff_ret with_copyins]. rewrite (errno_ret_error_b e He1 He2).
rewrite (errno_ret_recover e He1 He2). exact Ht. }
* exists (with_copyins reads (mkEffect fd [] [])), (mk fd), [].
split.
{ apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. right. exists fd. auto. }
{ cbn [eff_ret with_copyins].
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne. exact Ht. }
+ intros (eff & model' & evs & Hspec & Ht).
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & HIn & -> & -> & _)
| (fd & Hlk & Heq & -> & -> & _) ].
* destruct (openat_errno_range e HIn) as [He1 He2].
cbn [eff_ret with_copyins] in Ht.
rewrite (errno_ret_error_b e He1 He2) in Ht.
rewrite (errno_ret_recover e He1 He2) in Ht.
left. exists e. auto.
* cbn [eff_ret with_copyins] in Ht.
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne in Ht.
right. exists fd. auto.
Qed.
Lemma open_ok_fd : ltac2:(TCodec.tc2 tcn__FileSim "R>'R3'S<'XHyR0%211p014':'@';%2251%411'S>'D'Q?&Q6&RMvXBr7r4%43321r1r6%83321&U5r3r5%342651%?3>51p]LA1'>'S8%211&SG&T2%11=r2%4221(0%118%K3831&SA%81H%211%O3Q7C1&RNr9%O3N1Ir8(QN&T=(T6(=y8%QC11%Q@11%Q@2QC1%511%QB2QEQE%711'S;%911%:1QD%<6Q<64421%>2Q61%Q?1Q>'SE%?11%C4QH431%H3FE1p0J1p0O1p0Q;1p^<R41p`>QO1pb:R61p_BR61p_DR;1p_HR=1").
Proof.
intros ms model mk x8 reads fd Hchk Hlk Hlt.
apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. right. exists fd. auto.
Qed.
Lemma tfo_openat_toolong : ltac2:(TCodec.tc2 tcn__FileSim "S4'R3'S<'XHyR0%211'@&QC%2231!p021'D'>%118&R6r4%211(3r2%22>1%93741'Q0&XKr3%22D1+QH%?3521'5&TA&R4r6u2%3221%511(A%H3821'SB&T8&R5r7%211u1%=231%6231(S3%Q23921&T4%118(0%11Q<%Q73Q531':%Q>2Q?Q?%211&T5r8%211(=%116%Q@3631'U:vXB&R;&R=r:&T=&U9%113(T6&SD&S5%211y8%R611%G11%R52R61%C11'S;%E11';%R:2R;1%H11%>6;6HH41%B2@1%E2D1%G11r9%K4J21Q@r;%M4L1IQ2p031p0Q01p0Q:1p0Q@1p0QK1p0R51p0R<1p\2RG1pb:RM1p_DS11p_HS31").
Proof.
intros ms model x8 U Hsvc Hno Hfl Hpath Hh Hlazy Hcont.
pose proof (openat_toolong_check segs ms x8 model Hno Hfl Hpath) as Hchk.
apply (tfo_sys_det segs ms model x8
(with_copyins (open_copyins ms)
(mkEffect (errno_ret ENAMETOOLONG) [] [])) model U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.
Lemma tfo_openat_enoent : ltac2:(TCodec.tc2 tcn__FileSim "SM'R3'S<'XHyR0%211':y8%511%311'@&QC%2271!p021'D'>%11<&R6r5%211(3r3%22B1%93741'Q0&XKr4%22H1+QH%?3521&R4r7(1%3221&TK%E3O21'SB&T8&R5r8%211u1%<231%6231(S2%11K%Q03:31&UHr9u2%D221%J2Q@1&TB%6221z%Q93O21'5&TD%11K(A%Q>3421%Q>1QE&QF&T3r:%211%421K(0%11QL%QG3831&T4r;%211%61R5%QL3QJ21%R22R7R7%R711&T5r<%211(=%116%R43631'U:vXB&R;&R=r>&T=&U9%113(T6&SD&S6%211%RF2RKRG%@11'S;%B11';%RK2S01%E11%;686EE41%?2=1%B2A1%D11r=%H4G21Q;r?%J4I1FQ6p031p0M1p0Q61p0Q<1p0QF1p0QL1p0R61p0RB1p0RI1p0S01p\2S;1p`2SA1pb:SF1p_DSJ1p_HSL1").
Proof.
intros ms model x8 p U Hsvc Hno Hdirfd Hpath Hfl Hdot Hfs Hh Hlazy Hcont.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret ENOENT) model []).
{ intro eff. rewrite (check_syscall_56 segs ms x8 eff model Hno).
unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
destruct (path_eqb p []) eqn:Hpe; cbv beta iota.
- apply check_copyins_after_ret_only.
- rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl, Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_read. rewrite Hdot, Hfs.
apply check_copyins_after_ret_only. }
apply (tfo_sys_det segs ms model x8
(with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] []))
model U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.
Lemma tfo_read_file : ltac2:(TCodec.tc2 tcn__FileSim "TN'R3'S<'XHyR0%211&QH':y8%611%311'@&QC%2281!p021'D'>%11=&R6r8%211(3r6%22C1%93741'Q0&XKr7%22I1+QO%?3521'S8%@11&SG&T2r9%211&R4r:(1%3221%8251(S9%12@E%G2=1%N3=41&TGr;%;219%311%Q33Q>12%Q31Q:&QF&T3%117%321D%Q32Q?M%Q:3621&T7&R7vXBr=%3221u1%K231u2%M251%93531%QE3A1<&UIr>%Q2216%Q>2R51&TJ%5221&UJzr?%Q921=%QE2R<1%5241'5&S?r@%Q?21E%Q@22D%QL2RC1%5231(A%R:3821&T4%118(0%11RI%R?3R=31%RE2RKRK%RJ11&T5rA%211(=%116%RG3631'U:&R;&R=rC(T6&Q4&QD%R924Q=%23Q9Q21%42S81&TI%R=28QC%2214'S;%A11';%S=2SC1%D11%>696DD41%A2@1%C11&T>&SFrB%RM11%RK2FRI&XI%13SOQEB%RI2Q@1%73541%9217r<%Q04R;<21rD%Q24R=1OR<p031p0Q51p0Q>1p0QD1p0QN1p0R51p0R<1p0RH1p0S01p0S61p0SF1p0SM1p\2T81pb6T>1p]FT?1p`0TE1p`2TE1pb:TG1p_DTK1p_HTM1").
Proof.
intros ms model x8 p off data w U Hsvc Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok Hh Hlazy Hcont.
set (bs := file_read data off (ms_gpr ms 2)).
assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
<= bv_unsigned (ms_gpr ms 2))%Z).
{ unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (u64_range (ms_gpr ms 2)) as Hc.
rewrite length_file_read, Nat2Z.inj_min.
unfold word_to_nat.
rewrite Z.mod_small; lia. }
assert (Hchk : forall eff m' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
(eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
/\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFile p (off + len_word bs))) model
/\ evs = [])).
{ intros eff m' evs.
rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite Haok. cbn [negb]. cbv beta iota.
rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
rewrite Hfs. cbv beta iota zeta.
rewrite in_wmem_si.
rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
unfold bs.
destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
-
cbv beta iota.
rewrite check_ret_only_ok_iff. cbn [delivered_writes length].
tauto.
- destruct eff as [ret ws zs us cs copyins]. split.
+ intro H.
destruct ws as [|[a bs'] [|? ?]]; try discriminate.
destruct zs as [|? ?]; [|discriminate].
destruct us as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct copyins as [|? ?]; [|discriminate].
destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr)
&& bv_eqb ret (len_word (b :: bsr)))
eqn:Hb; try rewrite Hb in H; [|discriminate].
apply andb_true_iff in Hb as [Hb Hr].
apply andb_true_iff in Hb as [Ha Hbs].
apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
inversion H; subst. cbn [delivered_writes].
repeat split; congruence.
+ intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
inversion Heff; subst.
rewrite bv_eqb_refl.
rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
apply (tfo_sys_det segs ms model x8
(mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [])
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFile p (off + len_word bs))) model) U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. apply Hchk. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite (check_syscall_63 segs ms x8 _ model Hno) in Hs.
unfold check_read in Hs.
rewrite Hfd32, Hfd in Hs. cbv beta iota in Hs.
rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs.
rewrite Hfs in Hs. cbv beta iota zeta in Hs.
rewrite in_wmem_si in Hs.
rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs.
cbv beta iota in Hs.
revert Hs.
destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs.
+ exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
+ discriminate.
Qed.
Lemma tfo_write_file : ltac2:(TCodec.tc2 tcn__FileSim "U8'R3'S<'XHyR0%211&QH':y8%611%311'@&QC%2281!p021'D'>%11=&R6r8%211(3r6%22C1%93741'Q0&XKr7%22I1+R0%?3521'S8%@11&SG&T2r9%211&R4r:(1%3221%8251(S:%12@E%G2=1%N3=41&TGr;%;219%311%Q33Q>12%Q31Q:&T7&R5r<%211u1%D231u2%F251%83531%Q82QDQ7%Q?3;21&UIr=%L217%Q82QO1&TJ%5221&QF&T3%117%321I%QD2R0Q6%QK3G21'5&<&TF%13Q8OQ;%311(7%R23621&THr@%Q?21J%311%R73;16&T4%115(0%11RF%R<3R:31%RB2RHRH%RG11&T5rA%211(=%116%RD3631'U:vXB&R;&R=rC&T=(6';%S22S81(?%R926QF&9%12S8Q@%44S=631%A16%93721(T6%R@2=QK%S<2SBS=%F11'S;%H11%6653HH18%B281%E2D1%G11&T>&SFrB%RO11%RM2JRK&XIr?%23T21@%RL2QC1%83651&T?&QG%R41:&QEr>%2319R=%534QK1%721?%B291%Q=4Q<D1RKrD%Q?4Q>1Q;RCp031p0QB1p0QK1p0R11p0R71p0R?1p0RF1p0RM1p0S:1p0S@1p0T01p0T71p\2TB1p]0TH1p]FTI1p`0TO1p`2TO1pb:U11p_DU51p_HU71").
Proof.
intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hnz Hh Hlazy Hcont.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
{ rewrite in_mem_si. exact Hrd. }
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins [(ms_gpr ms 1, length bs)] eff (ms_gpr ms 2)
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
{ intro eff.
rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hret : len_word bs = ms_gpr ms 2).
{ unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
{ destruct (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) eqn:Hg'; [|reflexivity].
exfalso. apply andb_prop in Hg' as [Hnz' Hz].
apply Nat.eqb_eq in Hz. apply negb_true_iff in Hnz'.
rewrite Hz in Hlen. cbn in Hlen.
assert (Hzero : ms_gpr ms 2 = Z_to_bv 64 0).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (ms_gpr ms 2)). rewrite <- Hlen. reflexivity. }
unfold w_is0 in Hnz'. rewrite Hzero, bv_eqb_refl in Hnz'. discriminate. }
rewrite Hgate. cbv beta iota.
rewrite Hfs. cbv beta iota.
rewrite Hgap. cbv beta iota.
rewrite Hret.
rewrite Hnz. reflexivity. }
apply (tfo_sys_det segs ms model x8
(with_copyins [(ms_gpr ms 1, length bs)]
(mkEffect (ms_gpr ms 2) [] []))
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.
Lemma tfo_write_file_zero : ltac2:(TCodec.tc2 tcn__FileSim "U8'R3'S<'XHyR0%211&QH':y8%611%311'@&QC%2281!p021'D'>%11=&R6r8%211(3r6%22C1%93741'Q0&XKr7%22I1+R0%?3521'S8%@11&SG&T2r9%211&R4r:(1%3221%8251(S:%12@E%G2=1%N3=41&TGr;%;219%311%Q33Q>12%Q31Q:&T7&R5r<%211u1%D231u2%F251%83531%Q82QDQ7%Q?3;21&UIr=%L217%Q82QO1&TJ%5221&QF&T3%117%321I%QD2R0Q6%QK3G21'5&<&TF%13Q8OQ;%311(7%R23621&THr@%Q?21J%311(A%R83<21&S?rA%QE21Q2%QF22Q1%R22RI1%5231%R?3C18&T4%117(0%11RN%RD3RB31%RJ2S0S0%RO11&T5rB%211(=%116%RL3631'U:vXB&R;&R=rD(T6%R=22QH%S92S?S:%;11'S;%=11';%S>2SD1%@11%9686@@41%<2;1%>11&T>&SFrC%RN11%RL2ARJ&XI%13T0Q@A%RJ2Q;1%73541&T?&QG%R219&QEr?r>%332QI1%635QD1%821?%B2:1%Q44Q3D1R@rE%Q64Q51Q27p031p0Q91p0QB1p0QH1p0R01p0R71p0R?1p0RF1p0RM1p0S:1p0S@1p0T01p0T71p\2TB1p]0TH1p]FTI1p`0TO1p`2TO1pb:U11p_DU51p_HU71").
Proof.
intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hz Hok Hh Hlazy Hcont.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
{ rewrite in_mem_si. exact Hrd. }
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only eff (ms_gpr ms 2)
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
{ intro eff.
rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hret : len_word bs = ms_gpr ms 2).
{ unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
{ rewrite Hz. reflexivity. }
rewrite Hgate. cbv beta iota.
rewrite Hfs. cbv beta iota.
rewrite Hgap. cbv beta iota.
rewrite Hret.
rewrite Hz. cbv beta iota.
unfold check_access_ok_zero. rewrite Hok. reflexivity. }
apply (tfo_sys_det segs ms model x8
(mkEffect (ms_gpr ms 2) [] [])
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.
Lemma tfo_close : ltac2:(TCodec.tc2 tcn__FileSim "S6'R3'S<'XHyR0%211'S8'@&QC%2241!p021'D'>%119&R6r5%211(3r3%22?1%93741'Q0&XKr4%22E1+QI%?3521%?1F&SG&T2r6%211&R4r7(1%3221%8251%D2Q0>%K3;21&TGr8%9217%311%Q03Q712&T4%115(0%11Q;%Q53Q331':%Q<2Q>Q>%211&T5r9%211(=%116%Q>3631'U:vXB&R;&R=r;(T6&XGz%22QO1y8%R211%D11%R02R21%@11'S;%B11';%R52R71%E11%>6;6EE41%A2@1%C11&T>&SHr:%QF11%QD2FQB%4221%6214%M4L81QFr<%O4N1KQAp031p0Q21p0Q<1p0QB1p0QH1p0R51p0R<1p\2RG1p]HRM1pb:RO1p_DS31p_HS51").
Proof.
intros ms model x8 e U Hsvc Hno Hfd Hfd32 Hh Hlazy Hcont.
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only eff (Z_to_bv 64 0)
(with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) []).
{ intro eff.
rewrite (check_syscall_57 segs ms x8 eff model Hno). unfold check_close.
rewrite Hfd32, Hfd. reflexivity. }
apply (tfo_sys_det segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.
Lemma record_gpr : ltac2:(TCodec.tc2 tcn__FileSim "Q@&TMy5'XHyR0%211%5241'>%113yQ0%711y8%911%611p091';'D&R4(R2r9r8r7r6r5r4r3r2%9887654321r1%<221&TN&XG&UG+:&UK%117%4231%62Q31%82C1%G3Q2:1p_4I1p`JK1p_@L1p^:Q11pa4Q41paLQ51p`4Q91p^FQ91p`@Q:1").
Proof. reflexivity. Qed.
Lemma tfo_exit_rec : ltac2:(TCodec.tc2 tcn__FileSim "R>&TMy5'XHyR0%211%5241'>y8%611%311p061'S<&QC'D'Q0&XK&U=r7(XF+A(B%33D21%6251%82D1+RM%<3;21&TNr8+:%;3L19%4231r3%C3L21&UJr4%D2Q01+X0%4221&T3r6%211%L3M17'U:vXB(R2r;&U<vW>%211r:(3%Q326N%22Q@1(0%11QB&U;%119r9%>8=:96421O'@%12QHQ@r1(?%14QKQCQ>H%QC3431q_N51%H4G8QA1p0J1p0O1p0Q51p0Q=1p^JQK1p]:R41p_DQN1p`JR01p_@R11p`4R81p`@R81").
Proof.
intros regs pc mem rom model code fsv H17 H10 Hc Hfs.
subst fsv.
eapply (tfo_exit segs _ model (getr regs 17)).
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
- intro o. rewrite record_gpr, arg_reg_0.
rewrite H10, (land_255_small code Hc). tauto.
Qed.
Lemma tfo_read_rec : ltac2:(TCodec.tc2 tcn__FileSim "UB&TMy5'XHyR0%211%5241'>y8%611%311p061'S<&QH':%116'@&QC%22=1!p021'D'Q0&XK&U=r<(XF+A(B%33K21%6251%82K1+QO%<3;21&TNr=+:%;3Q319%4231r8%C3Q321r>+;%A3Q91?%:231r5%I3Q921r?+<%G3Q?1E%@231%N3Q>16'S8%Q>11&SG&T2%11Or;%4221(3(S9r:r9%3221%52<1%Q<3<71&TG%11Q:%Q?3QO1Q;%QN1QF&QF&T3%11O%321Q@%?2QK=%QF3621'5&UCvXB&Q5%11B%433D1(A%QN3721&UI%QN2RAH&TJ%3221&UJz%R32RFQ1%3221&S?%R62RIR4%22QK1%R:3C1=%RI1RK&T4rC%211(0%11S0%RA3631%RG2S2S2%RJ11&T5rD%211(=%116%RI3631'U:&U>vW>&U@rI&Q4&QDrArB%3321R9%52S@1%837RE1&UBrH+4%3221&R8rGr@%3321:rF%D5C:621&T>&SFrE%RA11&XI%13T6CA%R?2Q91%634Q21%8216%O4R0:1S5(R2rJ&U<%11Q1%SK23SF%RI2T?1&U;%11Q5%8875Q43QB1KG%Q94R:1ES9p0;1p0Q<1p0QE1p0QM1p0R21p0R71p0R<1p0RE1p0RM1p0S11p0S@1p0SF1p0SM1p0T51p\2TC1p]8U31p]2U41p]FTK1p`0U61p`2TO1p^DU81p_DU21p`JU41p_@U51p`4U<1p`@U<1").
Proof.
intros regs pc mem rom model fdv p off data buf cnt U
H17 H10 H11 H12 Hfd Hfd32 Hfs Hwseg Hcnt Hpos Haok Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
assert (Hg1 : ms_gpr ms 1 = buf)
by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
assert (Hg2 : ms_gpr ms 2 = cnt)
by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
destruct (wseg_ok_wdef segs buf cnt ms Hwseg) as [w Hw].
apply (tfo_read_file ms model (getr regs 17) p off data w U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- rewrite Hg0. exact Hfd.
- rewrite Hg0. exact Hfd32.
- exact Hfs.
- rewrite Hg1, Hg2. exact Hw.
- rewrite Hg2. exact Hcnt.
- rewrite Hg2. exact Hpos.
- rewrite Hg1, Hg2. exact Haok.
- exact Hh.
- exact Hlazy.
- rewrite Hg0, Hg1, Hg2. unfold ms.
rewrite adv_apply_delivered. exact Hcont.
Qed.
Lemma tfo_write_rec : ltac2:(TCodec.tc2 tcn__FileSim "UM&TMy5'XHyR0%211%5241'>y8%611%311p061'S<&QH':%116'@&QC%22=1!p021'D'Q0&XK&U=r<(XF+A(B%33K21%6251%82K1+R0%<3;21&TNr=+:%;3Q319%4231r9%C3Q321r>+;%A3Q91?%:231r5%I3Q921r?+<%G3Q?1E%@231%N3Q>16'S8%Q>11&SG&T2%11E%321Q0(3(S:r;r:%3221%52;1%Q;3;71&TG%11O%Q>3QN1Q0%QM1QE&U?vXBr@&Q5r8%211%6454Q41%B2QM?%QH3921&UI%QH2R;Q8&TJ%3221&QF&T3rA%211%421Q7%M2R8QD%R33D21'5&<&TF%13QCQ=QI%311(7%R:3621'H&S?%R;2RNR9%22R01(A%R@3<21&UJz%2216%9241%S31S5&T4rD%211(0%11S:%RK3631%S12S<S<%S411&T5rE%211(=%116%S33631'U:&U>vW>&U@rI%231RIR?&UBrH+4%3221rG&UA%11QO%<5;8431&T>&SFrF%RC11&XIrC%23T91RN%RC2Q21%735K1&T?&QG%QO19&QErB%2319R1%534Q:1%721>%A291%Q04RCC1S@(R2rJ&U<%11Q2%T623T1%S52TJ1&U;%11Q6%8875Q53QC1Q2M%Q:4RM1Q0SDp0;1p0Q=1p0QF1p0QN1p0R91p0RA1p0RI1p0RN1p0S91p0S=1p0SK1p0T11p0T81p0T@1p\2TN1p]8U>1p]2U?1p]0U61p]FU71p`0UB1p`2U;1p^DUD1p_DU>1p_@U@1p`4UG1p`@UG1").
Proof.
intros regs pc mem model fdv p off data bs buf cnt U
H17 H10 H11 H12 Hfd Hfd32 Hrd Hcnt Hfs Hgap Hok Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
assert (Hg1 : ms_gpr ms 1 = buf)
by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
assert (Hg2 : ms_gpr ms 2 = cnt)
by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
destruct (w_is0 cnt) eqn:Hz.
-
apply (tfo_write_file_zero ms model (getr regs 17) p off data bs U).
+ unfold ms. cbn [ms_svc_pending]. reflexivity.
+ exact H17.
+ rewrite Hg0. exact Hfd.
+ rewrite Hg0. exact Hfd32.
+ rewrite Hg1, Hg2.
rewrite read_bytes_map_read_byte.
rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
exact Hrd.
+ rewrite Hg2. exact Hcnt.
+ exact Hfs.
+ exact Hgap.
+ rewrite Hg2. exact Hz.
+ destruct Hok as [Hfl | Hp].
* rewrite Hg1, Hg2. exact Hfl.
*
rewrite (w_is0_pos cnt Hp) in Hz. discriminate.
+ exact Hh.
+ exact Hlazy.
+ rewrite Hg0, Hg2. unfold ms.
rewrite adv_eff_ret. exact Hcont.
-
apply (tfo_write_file ms model (getr regs 17) p off data bs U).
+ unfold ms. cbn [ms_svc_pending]. reflexivity.
+ exact H17.
+ rewrite Hg0. exact Hfd.
+ rewrite Hg0. exact Hfd32.
+ rewrite Hg1, Hg2.
rewrite read_bytes_map_read_byte.
rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
exact Hrd.
+ rewrite Hg2. exact Hcnt.
+ exact Hfs.
+ exact Hgap.
+ rewrite Hg2. exact Hz.
+ exact Hh.
+ exact Hlazy.
+ rewrite Hg0, Hg2. unfold ms.
rewrite adv_eff_ret_copyins. exact Hcont.
Qed.
Lemma tfo_close_rec : ltac2:(TCodec.tc2 tcn__FileSim "SC&TMy5'XHyR0%211%5241'>y8%611%311p061'S<'S8'@&QC%22;1!p021'D'Q0&XK&U=r8(XF+A(B%33I21%6251%82I1+QI%<3;21&TNr9+:%;3Q119%4231r4%C3Q121%Q01J&SG&T2r6%211r5%5221(3%12Q2:%M3931&TG%118%Q03Q>19%Q=1Q?&T4%11O(0%11QC%Q63531':%Q=2QFQF%211&T5%11M(=%115%Q>3531'U:vXB&U>vW>&U@r>&XGz%22R61%534Q81&UBr=+4%3221r<r;%>5=7321&T>&SHr:%Q=11%321QF%5213r7%H4G821(R2r?&U<%11I%R923R4%QB2RK1&U;%11M%8875L3Q;1FC%Q24Q11CR=p0;1p0Q51p0Q>1p0QE1p0QI1p0R41p0R<1p\2RJ1p]HS01p^DS91p_DS31p`JS51p_@S61p`4S=1p`@S=1").
Proof.
intros regs pc mem rom model fdv e U H17 H10 Hfd Hfd32 Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
apply (tfo_close ms model (getr regs 17) e U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- rewrite Hg0. exact Hfd.
- rewrite Hg0. exact Hfd32.
- exact Hh.
- exact Hlazy.
- rewrite Hg0. unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.
Lemma tfo_open_enoent_rec : ltac2:(TCodec.tc2 tcn__FileSim "T4&TMy5'XHyR0%211%5241'>y8%611%311p061'S<':%115'@&QC%22<1!p021'D'Q0&XK&U=r6(XF+A(B%33J21%6251%82J1+QH%<3;21&TNr7+:%;3Q219%4231&TK%C3Q221r8+<%A3Q81?%:231&XGz%22Q:1%K3Q:41'SB&T8&U8vXB%221Br9+;%N3QE1L%G231%8251(S2r5%211%Q93=41'5&TD%11Q8(A%Q>3421%QL1QE&QF&T3%11N%321Q5(0%11QK%QF3731%R41R6&T4%11H%61R9%QK3421%R12R;R;%R411&T5r:%211(=%116%R33631'U:&U>vW>&U@r>&SD&S6%211%534QL1&UBr=+4%3221r<&UA%11QD%?5>8431r;%B4QG21QE(R2r?&U<%11D(3%RI24RD%22S<1&U;%11I%9886H3Q61B=%M4R21@Q2p0<1p0Q01p0Q91p0Q?1p0QH1p0QN1p0R=1p0RF1p0RN1p\2S<1p`2SB1p_DSE1p_@SG1p`4SN1p`@SN1").
Proof.
intros regs pc mem model p U H17 H10 H12 Hpath Hdot Hfs Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_openat_enoent ms model (getr regs 17) p U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
- exact Hdot.
- exact Hfs.
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.
Lemma tfo_open_rd_rec : ltac2:(TCodec.tc2 tcn__FileSim "V>&TMy5'XHyR0%211%5241'>y8%611%311p061'S<':%115'Q0'@&QC%22=1!p021p061p0A2pb854'D&XK&U=r9(XF+A(B%33M21%6251%82M1+QH%;3D21&TNr:+:%;3Q519%4231&TK%B3Q521r;+<%A3Q;1?%:231&XGz%22Q=1%J3Q=41'SB&T8&U8vXB%221Br<+;%N3QH1L%G231%8251(S2r8%211%Q83=41'5&QI(=%11QK%32Q:1(7%Q?3621&TD%11Q4(A%QC3:21%R51QN&QF&T3%11G%321Q5(3%12R4Q=%QK3731%R=1R?&T4r=%211(0%11RD%R23631%R;2RFRF%R?11&T5r>%211%M15%R93521&UEr1&TC%33RF21'U:&U>vW>&U@rD&SDr2%211%534R71&UBrC+4%3221rB&UA%11QO%?5>8431rA%J1<%C4R3321p0E1p]HS<1'S8%SF11&SG&T2%119%321N%Q:16%S;3621&SA%61B%211%S?3T2K1rFr3%Q132S31rE%M21K%Q65Q531Q3H&T>&SF%A1Q0(S9%12OS1%433:1%621Q4r?%11=%QA4S1:31p0A1p0F1p^<TE1&F%R61QI'H'E'Cr@%12QNQE%32QM1q]HTD1%62TE1%Q72ER2%T>3Q91Q4%Q31G%T@3U3R51%D2R6QM%;221%<251q^<U71%?2U81%A2:1%D2C1p_NTN1(R2&U<%11R;%TJ2Q9TE%S42U@1&U;%11R?%78Q=5R>3RO1R8R3%RC4T31R6S3p0:1p0Q11p0R11p0RL1p0S41p0S<1p0SE1p0SJ1p0T21p0TA1p0TJ1p0U21p\2U?1p\0UA1p[NUC1p]BUK1p`2UL1p_DUO1p_@V11p`4V81p`@V81").
Proof.
intros regs pc mem model p d Te Ts U
H17 H10 H12 Hpath Hpe Hdot Hfs Hh Hlazy Herr Hok HU.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_open_core ms model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFile p (Z_to_bv 64 0))) model)
(getr regs 17) (open_copyins ms) Te Ts U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact Hh.
- exact Hlazy.
- intro eff. apply (openat_rd_check segs ms (getr regs 17) model p d).
+ exact H17.
+ unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
+ unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
+ exact Hpe.
+ unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
+ exact Hdot.
+ exact Hfs.
- intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
- intros e HIn.
unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
- intros fd Hlk Hlt.
unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
- exact HU.
Qed.
Lemma tfo_open_wr_rec : ltac2:(TCodec.tc2 tcn__FileSim "VB&TMy5'XHyR0%211%5241'>y8%611%311p061'S<':%115'Q0'@&QC%22=1!p021p061p0A2pb854'D&XK&U=r8(XF+A(B%33M21%6251%82M1+QH%;3D21&TNr9+:%;3Q519%4231&TK%B3Q521r:+<%A3Q;1?%:231&XG+b1%22Q=1%J3Q=41'SB&T8&U8vXB%221Br;+;%N3QH1L%G231%8251(S2r7%211%Q83=41'5&QI(=%11QK%32Q:1(7%Q?3621&TD%11Q4(A%QC3:21&T@&T3%11F%321Q4%QH3?1:%R:1R<&T4r<%211(0%11RA%QO3631%R82RCRC%R<11&T5r=%211%J15%R63521&UEr1&TC%33RC21'U:&U>vW>&U@rC&SDr2%211%534R41&UBrB+4%3221rA&UA%11QL%?5>8431r@r>%11=%D4R1431p0F1p]HS:1'S8%SD11&SG&T2%11:%321O%Q;16%S93621&SA%61C%211%S=3T0L1rEr3%Q232S11rD%N21L%Q75Q631Q4I&T>&SF%A1Q1(S:z%S22T=1%32Q21%635<1&T?&QG%R91Q9%231Q7RC%421Q;%=261r?%11D%QI4S6A31p0H1p0M1p^<TJ1&F%R61R1'H'E'C%QA2R5QL%22R41q]HTH1%52TI1%Q=2KR9%TB3Q?1Q:%Q91M%TD3U7R<1%C2R=R4%:221%;251q^<U;1%>2U<1%@2:1%C2B1p_NU21(R2&U<%11RB(3%TO2Q@TJ%22UE1&U;%11RG%88QD6RF3S71R@R;%RK4T81R>S3p0;1p0Q11p0R81p0S41p0S<1p0SD1p0SJ1p0SO1p0T71p0TF1p0TO1p0U71p\2UD1p\0UF1p[NUH1p`2V01p_DV31p_@V51p`4V<1p`@V<1").
Proof.
intros regs pc mem model p Te Ts U
H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Herr Hok HU.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_open_core ms model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model))
(getr regs 17) (open_copyins ms) Te Ts U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact Hh.
- exact Hlazy.
- intro eff. apply (openat_wr_check segs ms (getr regs 17) model p).
+ exact H17.
+ unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
+ unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
+ exact Hpe.
+ unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
+ exact Hdot.
+ exact Hun.
- intro fd. split.
+ rewrite with_fds_halted, with_fs_halted. exact Hh.
+ exact Hlazy.
- intros e HIn.
unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
- intros fd Hlk Hlt.
unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
- exact HU.
Qed.
Lemma tfo_open_wr_isdir_rec : ltac2:(TCodec.tc2 tcn__FileSim "T9&TMy5'XHyR0%211%5241'>y8%611%311p061'S<':%115'@&QC%22<1!p021'D'Q0&XK&U=r6(XF+A(B%33J21%6251%82J1+QH%<3;21&TNr7+:%;3Q219%4231&TK%C3Q221r8+<%A3Q81?%:231&XG+b1%22Q:1%K3Q:41'SB&T8&U8vXB%221Br9+;%N3QE1L%G231%8251(S2r5%211%Q93=41'5&QI(=%11QH%32Q:1(7%Q@3621&TD%11Q4(A%QD3:21&T@&T3%11F%321Q4%QI3?16%R71R9&T4r:%211(0%11R>%R03631%R62R@R@%R911&T5r;%211%J15%R73521'U:&U>vW>&U@r?&SD&S4%211%534R01&UBr>+4%3221r=&UA%11QH%?5>8431r<%B4QK21N(R2r@&U<%11D(3%RM24RH%22S@1&U;%11I%9886H3Q51B=%M4R61@Q1p0<1p0Q01p0Q81p0Q@1p0QF1p0QK1p0R31p0RB1p0RK1p0S31p\2SA1p`2SG1p_DSJ1p_@SL1p`4T31p`@T31").
Proof.
intros regs pc mem model p U H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
assert (Hchk : forall eff,
check_syscall (sys_input segs ms (getr regs 17)) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret EISDIR) model []).
{ intro eff. apply (openat_wr_isdir_check segs ms (getr regs 17) model p).
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- exact Hpe.
- unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
- exact Hdot.
- exact Hun. }
apply (tfo_sys_det segs ms model (getr regs 17)
(with_copyins (open_copyins ms)
(mkEffect (errno_ret EISDIR) [] [])) model U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.
Lemma tfo_open_toolong_rec : ltac2:(TCodec.tc2 tcn__FileSim "S<&TMy5'XHyR0%211%5241'>y8%611%311p061'S<'@&QC%22:1!p021'D'Q0&XK&U=r5(XF+A(B%33H21%6251%82H1+QH%<3;21'5&TA&TNr6+<%=3Q21;%4231%611(A%F3921'SB&T8&U8vXB%221Gr7+;%I3Q>1G%@231%8251(S3%Q23;21%Q>1Q@&T4%11Q1(0%11QD%Q83531':%Q?2QGQG%211&T5%11M(=%115%Q@3531'U:&U>vW>&U@r:+:%QB3R71Q@&SD&S5%211%73641&UBr9+4%3221r8&UA%11Q8%A5@8431%C4Q:1Q8QD(R2r;&U<%11E(3%R724R2%22RH1&U;%11J%9886I3Q71A<%N4QE1?QCp0<1p0Q11p0Q:1p0QA1p0QN1p0R91p\2RG1p_DRM1p_@RO1p`4S61p`@S61").
Proof.
intros regs pc mem model U H17 Hfl Hpath Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_openat_toolong ms model (getr regs 17) U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_2. exact Hfl.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.
End OpenNodes.
Lemma fout_omni_run : ltac2:(TCodec.tc2 tcn__FileSim "QN':'QL%211'O'QK'XHyR0%211'RO'Q0'S='@&QC%2261!p021'U:r:&RBr9r8r7r4&SJr2%211&SK%113&SO%115&SL%117%>9?=<;:7531&T1&RI%11Br6r5r3%66432B1?r1%I4H921&R1(QMr;%231LJ(RE%14KJ;:&U6%11I%855L3<1p0:1p\2Q51p_2Q;1p_6Q=1p`HQ?1p_>QA1p\NQB1pa:QC1p`6QG1p`4QI1pa6QK1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto.
cbn [omni_run]. unfold init_config.
exact (to_fout_exec segs _ _ U Hto eq_refl eq_refl).
Qed.
Lemma fout_obs_iff : ltac2:(TCodec.tc2 tcn__FileSim "R:':'QL%211'O'QK'XHyR0%211'RO'Q0'S='@&QC%2261!p021'U:r:&RBr9r8r7r4&SJr2%211&SK%113&SO%115&SL%117%>9?=<;:7531&T1&RI%11Br6r5r3%66432B1?r1%I4H921'SE%Q;11&F&RFr<&RAr;%2931Q0NML=<K%5341:'E'C%O1=&RC&U7%11@%33?Q11%6251q_NQ>1%92Q?1%A2;1pb2C1p0F1p\2QA1p_2QG1p_6QI1p`HQK1p_>QM1p\NQN1pa:QO1p`6R31p`4R51pa6R71").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
unfold init_config.
set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
by reflexivity.
assert (Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [])
by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
destruct (to_fout_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
as (o & Ho & Hp').
exists o. split; [exact Ho | eapply is_prefix_trans; eauto].
- intros (o & Ho & Hp).
destruct (to_fout_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
exists (fout_trace o), c. split; assumption.
Qed.
Lemma fout_no_error_run : ltac2:(TCodec.tc2 tcn__FileSim "QL':'QL%211'O'QK'XHyR0%211'RO'Q0'S='@&QC%2261!p021'U:r:&RBr9r8r7r4&SJr2%211&SK%113&SO%115&SL%117%>9?=<;:7531&T1&RI%11Br6r5r3%66432B1?r1%I4H921&G&RGr;&RA%192MKJI:9H8%4231%611p081p\2Q31p_2Q91p_6Q;1p`HQ=1p_>Q?1p\NQ@1pa:QA1p`6QE1p`4QG1pa6QI1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
eapply exec_conseq; [exact (fout_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma fout_omni_strong_equiv : ltac2:(TCodec.tc2 tcn__FileSim "RE':'QL%211'O'QK'XHyR0%211'RO'@&QC%2241!p021'S='U:r@&RBr?r>r=r:&SJr1%211&SK%113&SO%115&SL%117%>9?=<;:7531&T1&RI%11Br<r;&T:%66432B1?r2%I4H921r9r8r7r4%G16%E17%D18%C19%Q09L87654321%A1Mr6r5&T;%F6432;1?r3%Q94Q3721&Q3(QMrBrA%3321Q=%43JQ9E(RE%14Q>Q=Q<M%24GF>=%955421;p0;1p0L1p_2QG1p\2QI1p\FQO1p\@R11p\:R21p\HR31p\DR71p\BR91pb0R;1pa0R61p`FR81p`<R91pa2R:1p`NR>1p`LR@1pa8RB1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
Hsource Htarget.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (fout_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
intros tr o (out & _ & _ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (fout_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.
Lemma fout_strong_equiv : ltac2:(TCodec.tc2 tcn__FileSim "RO':'QL%211'O'QK'XHyR0%211'RO'Q0'@&QC%2251!p021'S='U:rB&RBrAr@r?r<&SJr1%211&SK%113&SO%115&SL%117%>9?=<;:7531&T1&RI%11Br>r=r;%66432B1?r2%I4H921r:r9r8r5%G16%E17%D18%C19%Q09<87654321%A1=r7r6r4%F6432;1?r3%Q94C721'C&Q2&RH(QMrDrC%3321Q?(RE%14Q?Q>Q=N%743N1;%911&Q1%93Q@Q0L%64LKCB%<42K1@%4261%@261p0B1p0Q31p_2QN1p\2R01p\>R61p\FR81p\@R:1p\:R;1p\HR<1p\DR@1p\BRB1pb0RD1p`DR>1pa0R@1p`FRB1p`<RC1pa2RD1p`NRH1p`LRJ1pa8RL1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp
Hsource Htarget.
split.
{ apply no_error_run_modeled.
apply (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
right. split.
- intro tr. cbn.
rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
reflexivity.
- cbn. apply (fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.
Lemma spec_err_escape_equiv : ltac2:(TCodec.tc2 tcn__FileSim "Q=':'QL%211'O'QK'XHyR0%211'RO'Q0'S='R>'R<r:&RAr9r8r7r6r5r4r3r2%99:87654321%<2;1&Q1&RH(QMr;%231@>(RE%14?>=<%643<1;%821;p0:1paNH1p_2J1p_6L1p`HN1p_>Q01p\NQ11pa:Q21p`6Q61p`4Q81pa6Q:1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target Hall.
left. exact Hall.
Qed.
End WithFP1.
